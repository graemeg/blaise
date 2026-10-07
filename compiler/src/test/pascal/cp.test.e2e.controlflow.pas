{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.controlflow;

{ E2E tests for control flow: if/else, for, while, repeat, break, continue,
  and signed Integer comparisons. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EControlFlowTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ForIn_AllCollectionKinds;
    procedure TestRun_Case_SelectsBranch;
    procedure TestRun_BreakAndExit;
    procedure TestRun_Repeat_BodyRunsBeforeTest;
    procedure TestRun_For_BoundsAndDirection;
    procedure TestRun_IfElse_TakesEachBranch;
    procedure TestRun_IntegerCompare_Signed;
    procedure TestRun_For_Upward_PrintsRange;
    procedure TestRun_For_Downto_PrintsRange;
    procedure TestRun_While_PrintsRange;
    procedure TestRun_For_EmptyBody_NoCrash;
    procedure TestRun_While_EmptyBody_NoCrash;
    procedure TestRun_Repeat_PrintsRange;
    procedure TestRun_For_BreakExitsEarly;
    procedure TestRun_For_ContinueSkipsIteration;
    procedure TestRun_Nested_For_Loops;
    procedure TestRun_IncDec_CapturedVar;
    procedure TestRun_ExitValue_ReturnsEarly;
    { case-label ranges (lo..hi) and Succ/Pred ordinal builtins. }
    procedure TestRun_Case_Ranges;
    procedure TestRun_Case_RangeMixedWithSingles;
    procedure TestRun_Case_EnumRange;
    procedure TestRun_SuccPred_Integer;
    procedure TestRun_SuccPred_Enum;
  end;

implementation

procedure TE2EControlFlowTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-controlflow');
end;

const
  LE = #10;

  SrcForUp = '''
    program P;
    var I: Integer;
    begin
      for I := 1 to 3 do
        WriteLn(I)
    end.
    ''';

  { Exit(X) function-result shorthand — early returns with a value, including
    a string return (exercises ARC on the returned value), and a fall-through
    case where no Exit(X) fires. }
  SrcExitValue = '''
    program P;
    function Classify(n: Integer): Integer;
    begin
      if n < 0 then Exit(-1);
      if n = 0 then Exit(0);
      Exit(1)
    end;
    function Pick(b: Boolean): string;
    begin
      if b then Exit('yes');
      Result := 'no'
    end;
    begin
      WriteLn(Classify(-9));
      WriteLn(Classify(0));
      WriteLn(Classify(42));
      WriteLn(Pick(True));
      WriteLn(Pick(False))
    end.
    ''';

  SrcForDown = '''
    program P;
    var I: Integer;
    begin
      for I := 3 downto 1 do
        WriteLn(I)
    end.
    ''';

  SrcWhile = '''
    program P;
    var I: Integer;
    begin
      I := 1;
      while I <= 3 do
      begin
        WriteLn(I);
        I := I + 1
      end
    end.
    ''';

  { Empty loop body — `for ... do;` / `while ... do;` parse to a nil body.
    Regression for issue #150: the native backend segfaulted (nil.ClassName in
    the unsupported-statement fallback) and the QBE backend rejected it; both
    must now treat the empty body as a valid no-op. }
  SrcForEmptyBody = '''
    program P;
    var I: Integer;
    begin
      for I := 0 to 9 do;
      WriteLn('done')
    end.
    ''';

  SrcWhileEmptyBody = '''
    program P;
    var I: Integer;
    begin
      I := 0;
      while I < 0 do;
      WriteLn('done')
    end.
    ''';

  SrcRepeat = '''
    program P;
    var I: Integer;
    begin
      I := 1;
      repeat
        WriteLn(I);
        I := I + 1
      until I > 3
    end.
    ''';

  SrcForBreakE2E = '''
    program P;
    var I: Integer;
    begin
      for I := 1 to 10 do
      begin
        if I = 4 then break;
        WriteLn(I)
      end
    end.
    ''';

  SrcForContinue = '''
    program P;
    var I: Integer;
    begin
      for I := 1 to 5 do
      begin
        if I = 3 then continue;
        WriteLn(I)
      end
    end.
    ''';

  SrcNestedFor = '''
    program P;
    var I, J: Integer;
    begin
      for I := 1 to 2 do
        for J := 1 to 2 do
          WriteLn(I * 10 + J)
    end.
    ''';

  { Inc/Dec on a captured outer-scope variable: the _cap_ slot holds the
    var's address, so Inc must load/modify/store through it.  Regression for
    a codegen bug where Inc(captured) referenced a non-existent %_var_ slot
    (QBE: 'invalid type ... in loadsw'; native: 'undefined reference'). }
  SrcIncCaptured = '''
    program P;
    procedure Outer;
    var
      Counter: Integer;
      procedure Inner;
      begin
        Inc(Counter);
        Inc(Counter, 5);
      end;
    begin
      Counter := 0;
      Inner();
      WriteLn(Counter);
    end;
    begin
      Outer();
    end.
    ''';

procedure TE2EControlFlowTests.TestRun_For_Upward_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForUp, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_Downto_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForDown, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3 2 1', '3' + LE + '2' + LE + '1' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_IfElse_TakesEachBranch;
const
  { Each branch taken at least once: a compound then-branch (every
    statement runs), a single-statement else, an if without else, and the
    join point after it.  Replaces the QBE IR checks in cp.test.control. }
  Src = '''
    program P;
    procedure Check(N: Integer);
    begin
      if N > 5 then
      begin
        WriteLn('big ', N);
        WriteLn('then')
      end
      else
        WriteLn('small ', N);
      if N = 7 then
        WriteLn('seven');
      WriteLn('end ', N)
    end;
    begin
      Check(10);
      Check(3);
      Check(7)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'big 10' + LE + 'then' + LE + 'end 10' + LE +
    'small 3' + LE + 'end 3' + LE +
    'big 7' + LE + 'then' + LE + 'seven' + LE + 'end 7' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_IntegerCompare_Signed;
const
  { Integer comparisons are SIGNED: an unsigned lowering gets every
    comparison involving a negative operand wrong.  Variables, not
    literals, so nothing is folded at compile time; the while loop counts
    down through zero. }
  Src = '''
    program P;
    var A, B, N: Integer;
    procedure Show(const S: string; V: Boolean);
    begin
      if V then
        WriteLn(S, ' T')
      else
        WriteLn(S, ' F')
    end;
    begin
      A := -1;
      B := 0;
      Show('-1<0', A < B);
      Show('-1>0', A > B);
      Show('-1<=0', A <= B);
      Show('-1>=0', A >= B);
      Show('-1=0', A = B);
      Show('-1<>0', A <> B);
      A := -5;
      B := -10;
      Show('-5>-10', A > B);
      Show('-5<-10', A < B);
      N := 2;
      while N > -2 do
      begin
        Write(N, ' ');
        N := N - 1
      end;
      WriteLn('')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '-1<0 T' + LE + '-1>0 F' + LE + '-1<=0 T' + LE + '-1>=0 F' + LE +
    '-1=0 F' + LE + '-1<>0 T' + LE + '-5>-10 T' + LE + '-5<-10 F' + LE +
    '2 1 0 -1 ' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_While_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcWhile, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_EmptyBody_NoCrash;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Issue #150: an empty `for` body must compile + run as a no-op on both
    backends (native previously segfaulted the compiler). }
  AssertRunsOnAll(SrcForEmptyBody, 'done' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_While_EmptyBody_NoCrash;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWhileEmptyBody, 'done' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_Repeat_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRepeat, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_BreakExitsEarly;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForBreakE2E, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_ContinueSkipsIteration;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForContinue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 4 5', '1' + LE + '2' + LE + '4' + LE + '5' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_Nested_For_Loops;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcNestedFor, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested 2x2', '11' + LE + '12' + LE + '21' + LE + '22' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_IncDec_CapturedVar;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIncCaptured, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Inc(captured) + Inc(captured,5) = 6', '6' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_ExitValue_ReturnsEarly;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExitValue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { Classify: -1, 0, 1; Pick: yes (Exit), no (fall-through). }
  AssertEquals('exit-value returns',
    '-1' + LE + '0' + LE + '1' + LE + 'yes' + LE + 'no' + LE, Output);
end;

const
  SrcCaseRanges = '''
    program P;
    var i, r: Integer;
    begin
      for i := 0 to 6 do
      begin
        case i of
          0, 1: r := 100;
          2..4: r := 200;
        else r := 999;
        end;
        Write(r); Write(' ');
      end;
      WriteLn()
    end.
    ''';

  SrcCaseRangeMixed = '''
    program P;
    var i: Integer;
    begin
      for i := 0 to 10 do
        case i of
          0:       Write('z');
          1..3:    Write('a');
          5, 7..9: Write('b');
        else Write('.');
        end;
      WriteLn()
    end.
    ''';

  SrcCaseEnumRange = '''
    program P;
    type TColor = (Red, Orange, Yellow, Green, Blue, Violet);
    function Warm(c: TColor): Boolean;
    begin case c of Red..Yellow: Result := True else Result := False end end;
    begin
      WriteLn(Warm(Orange));
      WriteLn(Warm(Blue))
    end.
    ''';

  SrcSuccPredInt = '''
    program P;
    var i: Integer;
    begin i := 10; WriteLn(Succ(i)); WriteLn(Pred(i)); WriteLn(Succ(Succ(i))) end.
    ''';

  SrcSuccPredEnum = '''
    program P;
    type TDir = (North, East, South, West);
    function Nm(d: TDir): string;
    begin case d of North: Result:='N'; East: Result:='E'; South: Result:='S'; West: Result:='W' end end;
    var d: TDir;
    begin d := North; WriteLn(Nm(Succ(d))); d := West; WriteLn(Nm(Pred(d))) end.
    ''';

procedure TE2EControlFlowTests.TestRun_Case_Ranges;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCaseRanges, '100 100 200 200 200 999 999 ' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_Case_RangeMixedWithSingles;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCaseRangeMixed, 'zaaa.b.bbb.' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_Case_EnumRange;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCaseEnumRange, 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_SuccPred_Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSuccPredInt, '11' + LE + '9' + LE + '12' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_SuccPred_Enum;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSuccPredEnum, 'E' + LE + 'S' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_For_BoundsAndDirection;
const
  {
    for runs its body once per value from start to end INCLUSIVE, counting up
    with to and down with downto, over negative bounds (signed loop test); an
    empty range runs zero times; a compound body runs every statement.
    Replaces the QBE IR checks in cp.test.forloop. }
  Src = '''
    program P;
    var I, S, Lo, Hi: Integer;
    begin
      Lo := -2;
      Hi := 1;
      for I := Lo to Hi do
        Write(I, ' ');
      WriteLn('|');
      for I := Hi downto Lo do
        Write(I, ' ');
      WriteLn('|');
      S := 0;
      for I := 1 to 0 do
        S := S + 1;
      for I := 0 downto 1 do
        S := S + 1;
      WriteLn('empty ', S);
      S := 0;
      for I := 1 to 3 do
      begin
        S := S + I;
        S := S + 10
      end;
      WriteLn('compound ', S)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '-2 -1 0 1 |' + LE +
    '1 0 -1 -2 |' + LE +
    'empty 0' + LE +
    'compound 36' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_Repeat_BodyRunsBeforeTest;
const
  {
    repeat runs its body BEFORE the first test, so a condition already true
    still runs it once, and leaves when the condition becomes true.
    Replaces the QBE IR checks in cp.test.repeatloop. }
  Src = '''
    program P;
    var I, N: Integer;
    begin
      N := 0;
      repeat
        N := N + 1
      until True;
      WriteLn('once ', N);
      I := 0;
      repeat
        I := I + 1;
        Write(I, ' ')
      until I >= 3;
      WriteLn('|')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'once 1' + LE +
    '1 2 3 |' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_BreakAndExit;
const
  {
    break leaves the innermost for and while loop; exit leaves a function with
    the Result set so far, or the main program; Exit(value) sets Result and
    leaves.  Replaces the QBE IR checks in cp.test.flowjumps. }
  Src = '''
    program P;
    function Abs1(X: Integer): Integer;
    begin
      if X < 0 then
      begin
        Result := 0 - X;
        exit
      end;
      Result := X
    end;
    function Classify(N: Integer): Integer;
    begin
      if N < 0 then Exit(-1);
      Result := 1
    end;
    var I: Integer;
    begin
      for I := 1 to 10 do
      begin
        if I > 3 then break;
        Write(I, ' ')
      end;
      WriteLn('|');
      I := 0;
      while I < 100 do
      begin
        if I = 2 then break;
        I := I + 1
      end;
      WriteLn('while ', I);
      WriteLn(Abs1(-7), ' ', Abs1(5));
      WriteLn(Classify(-3), ' ', Classify(4));
      if I = 2 then exit;
      WriteLn('not reached')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1 2 3 |' + LE +
    'while 2' + LE +
    '7 5' + LE +
    '-1 1' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_Case_SelectsBranch;
const
  {
    case selects the matching branch or else, for Integer, enum and string
    selectors; enum ordinals honour explicit values and continue after them; a
    member name shared by two enums resolves by the target type (parameter,
    record field) or by qualification.  Replaces the QBE IR checks in
    cp.test.caseenum. }
  Src = '''
    program P;
    type
      TState = (sIdle, sRunning, sDone);
      TStatus = (Idle=10, Running=20, Done=30);
      TCode = (cA=100, cB, cC);
      TDir = (dN, dE, dS, dW);
      TColorA = (Red, Green);
      TColorB = (Amber, Red);
      TRec = record c: TColorB; end;
    procedure Pick(N: Integer);
    begin
      case N of
        1: WriteLn('one');
        2: WriteLn('two')
      else
        WriteLn('other ', N)
      end
    end;
    procedure Named(const S: string);
    begin
      case S of
        'bar': WriteLn('B');
        'foo': WriteLn('F')
      else
        WriteLn('?')
      end
    end;
    procedure TakeB(c: TColorB);
    begin
      WriteLn('takeB ', Ord(c))
    end;
    var St: TState; R: TRec;
    begin
      Pick(1);
      Pick(2);
      Pick(5);
      St := sRunning;
      case St of
        sIdle: WriteLn('idle');
        sRunning: WriteLn('running');
        sDone: WriteLn('done')
      end;
      Named('foo');
      Named('bar');
      Named('baz');
      WriteLn(Ord(Running), ' ', Ord(cB), ' ', Ord(cC), ' ', Ord(TDir.dS));
      TakeB(Red);
      R.c := Red;
      WriteLn('field ', Ord(R.c))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'one' + LE +
    'two' + LE +
    'other 5' + LE +
    'running' + LE +
    'F' + LE +
    'B' + LE +
    '?' + LE +
    '20 101 102 2' + LE +
    'takeB 1' + LE +
    'field 1' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_ForIn_AllCollectionKinds;
const
  {
    for-in over every collection kind, leak-checked: a class with
    GetEnumerator / MoveNext / Current, zero- and non-zero-based static
    arrays, a dynamic array (and an empty one), a string by Byte and by
    code point (Integer loop variable: three code points from four bytes),
    an array of records with a managed field, a set, and an enumerator whose
    Current returns a managed record (refreshed into the loop variable
    each iteration). }
  Src = '''
    program P;
    type
      TColor = (Red, Green, Blue);
      TColorSet = set of TColor;
      TRec = record Name: string; Number: Integer; end;
      TItem = record S: string; end;
      TMyEnum = class
        FI, FMax: Integer;
        function MoveNext: Boolean;
        function GetCurrent: Integer;
        property Current: Integer read GetCurrent;
      end;
      TMyCol = class
        Count: Integer;
        function GetEnumerator: TMyEnum;
      end;
      TItemEnum = class
        FI: Integer;
        function GetCurrent: TItem;
        function GetEnumerator: TItemEnum;
        function MoveNext: Boolean;
        property Current: TItem read GetCurrent;
      end;
    function TMyEnum.MoveNext: Boolean;
    begin
      FI := FI + 1;
      Result := FI <= FMax
    end;
    function TMyEnum.GetCurrent: Integer; begin Result := FI * 10 end;
    function TMyCol.GetEnumerator: TMyEnum;
    begin
      Result := TMyEnum.Create();
      Result.FMax := Count
    end;
    function TItemEnum.GetCurrent: TItem;
    begin
      Result.S := 'item-' + IntToStr(FI)
    end;
    function TItemEnum.GetEnumerator: TItemEnum; begin Result := Self end;
    function TItemEnum.MoveNext: Boolean;
    begin
      FI := FI + 1;
      Result := FI <= 3
    end;
    var
      Col: TMyCol; X, I: Integer; Arr: array[0..4] of Integer;
      NZ: array[3..7] of Integer; DA: array of Integer; S: string; B: Byte;
      Recs: array[0..2] of TRec; R: TRec; CS: TColorSet; C: TColor;
      E: TItemEnum; It: TItem;
    begin
      Col := TMyCol.Create();
      Col.Count := 3;
      for X in Col do Write(X, ' ');
      WriteLn();
      for I := 0 to 4 do Arr[I] := I * I;
      for X in Arr do Write(X, ' ');
      WriteLn();
      for I := 3 to 7 do NZ[I] := I;
      for X in NZ do Write(X, ' ');
      WriteLn();
      SetLength(DA, 3);
      DA[0] := 7; DA[1] := 8; DA[2] := 9;
      for X in DA do Write(X, ' ');
      WriteLn();
      SetLength(DA, 0);
      for X in DA do Write('never');
      S := 'Hi!';
      for B in S do Write(B, ' ');
      WriteLn();
      S := 'a' + #233 + 'z';
      for I in S do Write(I, ' ');
      Write(Length(S));
      WriteLn();
      for I := 0 to 2 do
      begin
        Recs[I].Name := 'n' + IntToStr(I);
        Recs[I].Number := I + 100
      end;
      for R in Recs do Write(R.Name, '=', R.Number, ' ');
      WriteLn();
      CS := [Red, Blue];
      for C in CS do Write(Ord(C), ' ');
      WriteLn();
      E := TItemEnum.Create();
      for It in E do Write(It.S, ' ');
      WriteLn();
      Col.Free();
      E.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '10 20 30 ' + LE +
    '0 1 4 9 16 ' + LE +
    '3 4 5 6 7 ' + LE +
    '7 8 9 ' + LE +
    '72 105 33 ' + LE +
    '97 233 122 4' + LE +
    'n0=100 n1=101 n2=102 ' + LE +
    '0 2 ' + LE +
    'item-1 item-2 item-3 ' + LE, 0);
  AssertLeakFreeOnAll(Src, 'item-3');
end;

initialization
  RegisterTest(TE2EControlFlowTests);

end.
