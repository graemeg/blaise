{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.sets;

{ E2E tests for Pascal `set of <enum>` operations: compile -> run, assert on
  stdout, on BOTH backends (QBE + native) via AssertRunsOnAll.  Covers the
  general set-operation semantics over NAMED set types — membership (`in`),
  Include/Exclude, union/intersection, set-valued constants, set-literal
  arguments, equality, and for-in — for both <=32-member sets and the 33..64
  ("Set64") boundary.

  Related e2e set suites:
    - cp.test.e2e.inlineset  — inline `set of TE` / `set of (a,b,c)` syntax.
    - cp.test.e2e.jumboset   — >64-member ("jumbo") byte-array-bitmap sets.
    - cp.test.e2e.tset       — the TSet<T> generic collection (unrelated). }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ESetOpsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { <= 32-member sets }
    procedure TestRun_Set_Include_Exclude;
    procedure TestRun_Set_IncludeExcludeOnField;
    procedure TestRun_Set_InOperator;
    procedure TestRun_Set_InArrayElementField;
    procedure TestRun_Set_InObjectField;
    procedure TestRun_Set_UnionIntersect;
    procedure TestRun_Set_ValuedConstant;
    procedure TestRun_Set_LiteralArgument;
    procedure TestRun_Set_LiteralArgumentToConstructor;
    procedure TestRun_Set_EqualityWithLiteral;
    procedure TestRun_Set_ForIn_PrintsMembers;
    procedure TestRun_Set_RangeLiteral_Membership;
    procedure TestRun_Set_SubsetSuperset;

    { 33..64-member sets (the QBE 'l' / 64-bit register boundary) }
    procedure TestRun_Set64_InOperator_HighBit;
    procedure TestRun_Set64_IncludeExclude;
    procedure TestRun_Set64_Union;
    procedure TestRun_Set64_ForIn;

    { set of Byte — ordinal-based sets (issue #105) }
    procedure TestRun_SetOfByte_IncludeExclude;
    procedure TestRun_SetOfByte_InOperator;
    procedure TestRun_SetOfByte_RangeLiteral;
    procedure TestRun_SetOfByte_Union;

    { const-decl set literals: integer literals + ranges (not just enum idents) }
    procedure TestRun_ConstSet_IntLiterals;
    procedure TestRun_ConstSet_IntRange;
    procedure TestRun_ConstSet_MixedRangeAndLiteral;
    procedure TestRun_ConstSet_JumboWithRange;
    procedure TestRun_ConstSet_EnumStillWorks;

    { Integer-subrange base type: set of 0..255 / set of 1..10 (issue from
      future-improvements) + set of Boolean membership }
    procedure TestRun_SetOfSubrange_0to255;
    procedure TestRun_SetOfSubrange_TypeDecl;
    procedure TestRun_SetOfSubrange_NamedConstBounds;
    procedure TestRun_SetOfBoolean_Membership;
    { BUG-20260720-set-array-elem-dest: a set literal assigned into a static-
      array element must type against the element set type and round-trip. }
    procedure TestRun_Set_LiteralIntoStaticArrayElement;
  end;

implementation

const
  LE = #10;

  SrcSetIncludeExclude = '''
    program Prg;
    type TColor = (Red, Green, Blue);
         TColors = set of TColor;
    var S: TColors;
    begin
      S := [];
      Include(S, Red);
      Include(S, Blue);
      if Red in S then WriteLn('red');
      if Green in S then WriteLn('green');
      if Blue in S then WriteLn('blue');
      Exclude(S, Red);
      if Red in S then WriteLn('red2')
    end.
    ''';

  { Regression (issue #163): Include/Exclude applied to a set-typed FIELD.  The
    native codegen hard-cast the set argument to a bare identifier and emitted an
    OR/AND against a bogus global named after the field, crashing at run time.
    Exercises a small (<=32-bit) field mutated through Self inside a method and
    through Obj.Field directly, and a 33..64-bit ("Set64") field via Self. }
  SrcSetIncExclField = '''
    program Prg;
    type
      TColor = (cRed, cGreen, cBlue);
      TColors = set of TColor;
      TBig = (
        w00, w01, w02, w03, w04, w05, w06, w07,
        w08, w09, w10, w11, w12, w13, w14, w15,
        w16, w17, w18, w19, w20, w21, w22, w23,
        w24, w25, w26, w27, w28, w29, w30, w31,
        w32, w33, w34, w35, w36, w37, w38, w39, w40);
      TBigSet = set of TBig;
      TThing = class
        Colors: TColors;
        Big: TBigSet;
        procedure Mark;
      end;
    procedure TThing.Mark;
    begin
      Include(Colors, cRed);
      Include(Colors, cBlue);
      Exclude(Colors, cRed);
      Include(Big, w40);
      Include(Big, w02);
      Exclude(Big, w02);
    end;
    var T: TThing;
    begin
      T := TThing.Create();
      T.Mark();
      if cRed  in T.Colors then WriteLn('R') else WriteLn('no-R');
      if cBlue in T.Colors then WriteLn('B') else WriteLn('no-B');
      if w40 in T.Big then WriteLn('w40') else WriteLn('no-w40');
      if w02 in T.Big then WriteLn('w02') else WriteLn('no-w02');
      Include(T.Colors, cGreen);
      if cGreen in T.Colors then WriteLn('G');
      T.Free()
    end.
    ''';

  SrcSetIn = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    var Horizontal: TDirs;
    begin
      Horizontal := [East, West];
      if North in Horizontal then WriteLn('N');
      if East  in Horizontal then WriteLn('E');
      if West  in Horizontal then WriteLn('W')
    end.
    ''';

  { Regression: `elem in <arrayElement>.<setField>`.  The native `in` codegen
    kept the tested ordinal in %ecx across the RHS set evaluation; when the RHS
    is an array-element field access its address computation clobbered %rcx, so
    the shift used a garbage count and membership was always False.  The set is
    stored correctly (a copy-out reads True) — only the direct-`in`-on-the-field
    shape was wrong, and only on native (QBE was correct). }
  SrcSetInArrayField = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
         TRec = record Events: TDirs; end;
    var A: array[0..1] of TRec;
    begin
      A[0].Events := [East];
      A[1].Events := [North, West];
      if East  in A[0].Events then WriteLn('0E');
      if North in A[0].Events then WriteLn('0N');
      if North in A[1].Events then WriteLn('1N');
      if West  in A[1].Events then WriteLn('1W');
      if South in A[1].Events then WriteLn('1S')
    end.
    ''';

  { Regression (issue #164): `elem in Obj.SetField` on a plain class field
    (distinct from the array-element-record-field shape above).  On the native
    backend the tested ordinal was kept in %ecx while the RHS field address was
    computed, which clobbered it, so membership read wrong — every test after the
    first could report the wrong answer.  Copying the field to a local read
    correctly, and QBE was correct throughout.  Both a chain and a single
    isolated test are checked. }
  SrcSetInObjectField = '''
    program Prg;
    type
      TColor = (cRed, cGreen, cBlue);
      TColors = set of TColor;
      TThing = class
        Colors: TColors;
      end;
    var T: TThing; chain, one: string;
    begin
      T := TThing.Create();
      T.Colors := [cRed];
      chain := '';
      if cRed   in T.Colors then chain := chain + 'R';
      if cGreen in T.Colors then chain := chain + 'G';
      if cBlue  in T.Colors then chain := chain + 'B';
      WriteLn('chain=[', chain, ']');
      one := '';
      if cGreen in T.Colors then one := 'in' else one := 'out';
      WriteLn('one=[', one, ']');
      T.Free()
    end.
    ''';

  SrcSetUnion = '''
    program Prg;
    type TBit = (B0, B1, B2, B3);
         TBits = set of TBit;
    var A, B, C: TBits;
    begin
      A := [B0, B1];
      B := [B1, B2];
      C := A + B;
      if B0 in C then WriteLn('0');
      if B1 in C then WriteLn('1');
      if B2 in C then WriteLn('2');
      if B3 in C then WriteLn('3');
      C := A * B;
      if B1 in C then WriteLn('inter1')
    end.
    ''';

  { Set-valued constants: an inferred-type const and an annotated empty const,
    both used as set values at runtime. }
  SrcSetConst = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    const
      Horizontal = [East, West];
      Empty: TDirs = [];
    var S: TDirs;
    begin
      S := Horizontal;
      if North in S then WriteLn('N') else WriteLn('no-N');
      if East  in S then WriteLn('E');
      if West  in S then WriteLn('W');
      S := Empty;
      if East in S then WriteLn('still-E') else WriteLn('cleared')
    end.
    ''';

  { A set literal passed directly as a `set of` argument (both non-empty and
    empty), exercising the set-param ABI (w-width spill) too. }
  SrcSetLiteralArg = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    procedure Report(D: TDirs);
    begin
      if North in D then WriteLn('N') else WriteLn('no-N');
      if East  in D then WriteLn('E') else WriteLn('no-E')
    end;
    begin
      Report([East, West]);
      Report([])
    end.
    ''';

  { Regression (issue #165): a set literal passed directly as a CONSTRUCTOR
    argument.  The free-proc / function-call paths re-type a bracket literal
    bound to a `set of` parameter to that parameter's set type, but the
    constructor path did not — so the literal kept the open-array type it was
    analysed with (no set context), and native codegen rejected it as an
    unsupported array literal.  Verifies the constructed set value round-trips
    (the constructor stores its set arg into a field we read back). }
  SrcSetLiteralCtorArg = '''
    program Prg;
    type
      TColor = (cRed, cGreen, cBlue);
      TColors = set of TColor;
      TThing = class
        FC: TColors;
        constructor Create(const S: string; C: TColors);
      end;
    constructor TThing.Create(const S: string; C: TColors);
    begin
      FC := C
    end;
    var T: TThing;
    begin
      T := TThing.Create('x', [cRed, cBlue]);
      if cRed   in T.FC then WriteLn('R') else WriteLn('no-R');
      if cGreen in T.FC then WriteLn('G') else WriteLn('no-G');
      if cBlue  in T.FC then WriteLn('B') else WriteLn('no-B');
      T.Free()
    end.
    ''';

  { Set equality: S = [] and S = [literal] comparisons. }
  SrcSetEquality = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    var S: TDirs;
    begin
      S := [];
      if S = [] then WriteLn('empty') else WriteLn('not-empty');
      S := [East, West];
      if S = [] then WriteLn('bad-empty') else WriteLn('not-empty2');
      if S = [East, West] then WriteLn('match') else WriteLn('no-match');
      if S <> [East, West] then WriteLn('bad-ne') else WriteLn('equal')
    end.
    ''';

  SrcForInSet = '''
    program Prg;
    type
      TColor = (Red, Green, Blue);
      TColorSet = set of TColor;
    var
      S: TColorSet;
      C: TColor;
    begin
      S := [Red, Blue];
      for C in S do
        WriteLn(Ord(C));
    end.
    ''';

  { Subset (<=) and superset (>=) operators. }
  SrcSetSubset = '''
    program Prg;
    type TC = (Aa, Bb, Cc, Dd);
    var s, t: set of TC;
    begin
      s := [Aa, Bb]; t := [Aa, Bb, Cc];
      WriteLn(s <= t);
      WriteLn(t <= s);
      WriteLn(s >= t);
      WriteLn(t >= s);
      WriteLn(s <= s)
    end.
    ''';

  { Set range literal (issue #105): [m1..m3] and a mixed [m0, m2..m4, m7]. }
  SrcSetRange = '''
    program Prg;
    type
      TC = (m0, m1, m2, m3, m4, m5, m6, m7);
      TCS = set of TC;
    var
      e: TCS;
    begin
      e := [m1..m3];
      if m0 in e then WriteLn('y') else WriteLn('n');
      if m2 in e then WriteLn('y') else WriteLn('n');
      if m3 in e then WriteLn('y') else WriteLn('n');
      if m4 in e then WriteLn('y') else WriteLn('n');
      e := [m0, m2..m4, m7];
      if m1 in e then WriteLn('y') else WriteLn('n');
      if m2 in e then WriteLn('y') else WriteLn('n');
      if m7 in e then WriteLn('y') else WriteLn('n');
    end.
    ''';

  BigEnum64 =
    '''
    type
      TBig = (
        X00, X01, X02, X03, X04, X05, X06, X07,
        X08, X09, X10, X11, X12, X13, X14, X15,
        X16, X17, X18, X19, X20, X21, X22, X23,
        X24, X25, X26, X27, X28, X29, X30, X31,
        X32, X33, X34, X35, X36, X37, X38, X39,
        X40, X41, X42, X43, X44, X45, X46, X47);
      TBigSet = set of TBig;
    ''';

  SrcSet64InOp =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var S: TBigSet;
    begin
      S := [X40];
      if X40 in S then WriteLn('yes40') else WriteLn('no40');
      if X00 in S then WriteLn('yes00') else WriteLn('no00');
      if X31 in S then WriteLn('yes31') else WriteLn('no31')
    end.
    ''';

  SrcSet64InclExcl =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var S: TBigSet;
    begin
      S := [];
      Include(S, X40);
      Include(S, X01);
      if X40 in S then WriteLn('got40');
      if X01 in S then WriteLn('got01');
      Exclude(S, X40);
      if X40 in S then WriteLn('still40') else WriteLn('gone40')
    end.
    ''';

  SrcSet64UnionE2E =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var A, B, C: TBigSet;
    begin
      A := [X00, X01];
      B := [X40, X47];
      C := A + B;
      if X00 in C then WriteLn('0');
      if X01 in C then WriteLn('1');
      if X40 in C then WriteLn('40');
      if X47 in C then WriteLn('47');
      if X02 in C then WriteLn('BAD')
    end.
    ''';

  SrcSet64ForIn =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var S: TBigSet; V: TBig;
    begin
      S := [X02, X40, X47];
      for V in S do
        WriteLn(Ord(V))
    end.
    ''';

procedure TE2ESetOpsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sets');
end;

procedure TE2ESetOpsTests.TestRun_Set_Include_Exclude;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetIncludeExclude, 'red' + LE + 'blue' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_IncludeExcludeOnField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetIncExclField,
    'no-R' + LE + 'B' + LE + 'w40' + LE + 'no-w02' + LE + 'G' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_InOperator;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetIn, 'E' + LE + 'W' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_InArrayElementField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetInArrayField,
    '0E' + LE + '1N' + LE + '1W' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_InObjectField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetInObjectField,
    'chain=[R]' + LE + 'one=[out]' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_UnionIntersect;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetUnion,
    '0' + LE + '1' + LE + '2' + LE + 'inter1' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_ValuedConstant;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Horizontal = [East, West]: no-N, E, W; Empty cleared the set. }
  AssertRunsOnAll(SrcSetConst,
    'no-N' + LE + 'E' + LE + 'W' + LE + 'cleared' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_LiteralArgument;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Report([East,West]): no-N, E.  Report([]): no-N, no-E. }
  AssertRunsOnAll(SrcSetLiteralArg,
    'no-N' + LE + 'E' + LE + 'no-N' + LE + 'no-E' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_LiteralArgumentToConstructor;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetLiteralCtorArg,
    'R' + LE + 'no-G' + LE + 'B' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_EqualityWithLiteral;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetEquality,
    'empty' + LE + 'not-empty2' + LE + 'match' + LE + 'equal' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_ForIn_PrintsMembers;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInSet, '0' + LE + '2' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_RangeLiteral_Membership;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { [m1..m3]: m0=n m2=y m3=y m4=n; [m0,m2..m4,m7]: m1=n m2=y m7=y }
  AssertRunsOnAll(SrcSetRange,
    'n' + LE + 'y' + LE + 'y' + LE + 'n' + LE +
    'n' + LE + 'y' + LE + 'y' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_SubsetSuperset;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { s<=t, t<=s, s>=t, t>=s, s<=s }
  AssertRunsOnAll(SrcSetSubset,
    'True' + LE + 'False' + LE + 'False' + LE + 'True' + LE + 'True' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_InOperator_HighBit;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64InOp,
    'yes40' + LE + 'no00' + LE + 'no31' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_IncludeExclude;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64InclExcl,
    'got40' + LE + 'got01' + LE + 'gone40' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_Union;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64UnionE2E,
    '0' + LE + '1' + LE + '40' + LE + '47' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_ForIn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64ForIn,
    '2' + LE + '40' + LE + '47' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ set of Byte — ordinal-based sets (issue #105)                       }
{ ------------------------------------------------------------------ }

const
  SrcSetOfByteIncExcl = '''
    program Prg;
    type TByteFlags = set of Byte;
    var F: TByteFlags;
    begin
      F := [];
      Include(F, 3);
      Include(F, 100);
      if 3 in F then WriteLn('3');
      if 100 in F then WriteLn('100');
      if 50 in F then WriteLn('50');
      Exclude(F, 3);
      if 3 in F then WriteLn('3again')
    end.
    ''';

  SrcSetOfByteIn = '''
    program Prg;
    type TByteFlags = set of Byte;
    var F: TByteFlags;
    begin
      F := [1, 5, 200];
      if 1 in F then WriteLn('1');
      if 2 in F then WriteLn('2');
      if 5 in F then WriteLn('5');
      if 200 in F then WriteLn('200')
    end.
    ''';

  SrcSetOfByteRange = '''
    program Prg;
    type TByteFlags = set of Byte;
    var F: TByteFlags;
        I: Integer;
    begin
      F := [10..15];
      for I := 8 to 17 do
        if I in F then
          WriteLn(I)
    end.
    ''';

  SrcSetOfByteUnion = '''
    program Prg;
    type TByteFlags = set of Byte;
    var A, B, C: TByteFlags;
    begin
      A := [1, 2];
      B := [2, 3];
      C := A + B;
      if 1 in C then WriteLn('1');
      if 2 in C then WriteLn('2');
      if 3 in C then WriteLn('3');
      if 4 in C then WriteLn('4')
    end.
    ''';

procedure TE2ESetOpsTests.TestRun_SetOfByte_IncludeExclude;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetOfByteIncExcl,
    '3' + LE + '100' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_SetOfByte_InOperator;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetOfByteIn,
    '1' + LE + '5' + LE + '200' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_SetOfByte_RangeLiteral;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetOfByteRange,
    '10' + LE + '11' + LE + '12' + LE + '13' + LE + '14' + LE + '15' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_SetOfByte_Union;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetOfByteUnion,
    '1' + LE + '2' + LE + '3' + LE, 0);
end;

{ ---- const-decl set literals (integer literals + ranges) ---- }

procedure TE2ESetOpsTests.TestRun_ConstSet_IntLiterals;
const Src = '''
    program P;
    type TByteSet = set of Byte;
    const C: TByteSet = [1, 2, 3];
    begin
      if 2 in C then WriteLn('y') else WriteLn('n');
      if 5 in C then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'n' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_ConstSet_IntRange;
const Src = '''
    program P;
    type TByteSet = set of Byte;
    const C: TByteSet = [1..3];
    var I: Integer;
    begin
      for I := 0 to 4 do
        if I in C then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'n' + LE + 'y' + LE + 'y' + LE + 'y' + LE + 'n' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_ConstSet_MixedRangeAndLiteral;
const Src = '''
    program P;
    type TByteSet = set of Byte;
    const C: TByteSet = [10..12, 20];
    begin
      if 11 in C then WriteLn('y') else WriteLn('n');
      if 20 in C then WriteLn('y') else WriteLn('n');
      if 15 in C then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'y' + LE + 'n' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_ConstSet_JumboWithRange;
{ Edge case: a jumbo (>64-member) Byte set built from a const with a range and
  high values — exercises the byte-bitmap const path. }
const Src = '''
    program P;
    type TByteSet = set of Byte;
    const C: TByteSet = [200, 201..205, 0];
    begin
      if 203 in C then WriteLn('y') else WriteLn('n');
      if 0 in C then WriteLn('y') else WriteLn('n');
      if 100 in C then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'y' + LE + 'n' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_ConstSet_EnumStillWorks;
{ Regression: enum-member const sets (the original supported form) still work. }
const Src = '''
    program P;
    type
      TColor = (Red, Green, Blue, Yellow);
      TColors = set of TColor;
    const Warm: TColors = [Red, Yellow];
    begin
      if Red in Warm then WriteLn('y') else WriteLn('n');
      if Green in Warm then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'n' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_SetOfSubrange_0to255;
{ Integer-subrange base type 'set of 0..255' — equivalent to set of Byte. }
const Src = '''
    program P;
    var s: set of 0..255;
    begin
      s := [10, 20, 200];
      if 20 in s then WriteLn('y') else WriteLn('n');
      if 50 in s then WriteLn('y') else WriteLn('n');
      Include(s, 50);
      if 50 in s then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'n' + LE + 'y' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_SetOfSubrange_TypeDecl;
{ 'type T = set of 0..63' (small, <=64-bit path) + range literal. }
const Src = '''
    program P;
    type TS = set of 0..63;
    var s: TS;
    begin
      s := [3..7];
      if 5 in s then WriteLn('y') else WriteLn('n');
      if 63 in s then WriteLn('y') else WriteLn('n');
      Include(s, 63);
      if 63 in s then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'n' + LE + 'y' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_SetOfSubrange_NamedConstBounds;
{ Subrange bounds may be named constants: set of Lo..Hi. }
const Src = '''
    program P;
    const Lo = 0; Hi = 100;
    var s: set of Lo..Hi;
    begin
      s := [50];
      if 50 in s then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_SetOfBoolean_Membership;
{ set of Boolean: a Boolean operand on the left of 'in' (True in s) and as the
  Include/Exclude element. }
const Src = '''
    program P;
    var s: set of Boolean; b: Boolean;
    begin
      s := [True];
      if True in s then WriteLn('y') else WriteLn('n');
      if False in s then WriteLn('y') else WriteLn('n');
      Include(s, False);
      b := False;
      if b in s then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'n' + LE + 'y' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_LiteralIntoStaticArrayElement;
const Src = '''
    program P;
    type TE = (eA, eB, eC, eD); TS = set of TE;
    var A: array[0..2] of TS;
    begin
      A[0] := [eA, eC];
      A[1] := [];
      A[2] := A[0] + [eB];
      if eC in A[0] then WriteLn('y') else WriteLn('n');
      if eB in A[0] then WriteLn('y') else WriteLn('n');
      if eA in A[1] then WriteLn('y') else WriteLn('n');
      if eB in A[2] then WriteLn('y') else WriteLn('n')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'y' + LE + 'n' + LE + 'n' + LE + 'y' + LE, 0);
end;

initialization
  RegisterTest(TE2ESetOpsTests);

end.
