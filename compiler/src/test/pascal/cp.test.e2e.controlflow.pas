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
    { for-in over a collection reached through a call -- a record call's field
      (F(3).A, F(3).D), a getter's (O.R.A), a static-array call, an element
      with a call in its index (Pool[G()].A) -- runs the call ONCE.  x86-64
      ran it once per element (twice a pass for a dyn array) and crashed on
      the managed shapes; arm64 refused the record call bases.  A borrowed
      array is held for the loop, so the body may resize the original. }
    procedure TestRun_ForIn_CollectionThroughCall_EvaluatedOnce;
    procedure TestRun_ForIn_AllCollectionKinds;
    { BUG-029: the writes the for-in diagnostics call discarded leave the
      collection unchanged, and the ones they stay quiet about (through a
      dynamic-array or class link) reach it }
    procedure TestRun_ForIn_WritesThroughLoopVar_WhereTheyLand;
    { for-in over a record with a record enumerator (nested, through a
      call, empty), a class with an interface enumerator (Continue, managed
      Current), a record enumerator with a managed field reached through an
      interface collection, at program level and in a procedure; leak-free }
    procedure TestRun_ForIn_RecordAndInterfaceEnumerators;
    procedure TestRun_Case_SelectsBranch;
    procedure TestRun_BreakAndExit;
    procedure TestRun_Repeat_BodyRunsBeforeTest;
    procedure TestRun_For_BoundsAndDirection;
    { a for loop ending at its counter type's limit stops there (GH #237) }
    procedure TestRun_For_EndsAtTypeLimit_NoWrap;
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
    var I: Int;
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
    function Classify(n: Int): Int;
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
    var I: Int;
    begin
      for I := 3 downto 1 do
        WriteLn(I)
    end.
    ''';

  SrcWhile = '''
    program P;
    var I: Int;
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
    var I: Int;
    begin
      for I := 0 to 9 do;
      WriteLn('done')
    end.
    ''';

  SrcWhileEmptyBody = '''
    program P;
    var I: Int;
    begin
      I := 0;
      while I < 0 do;
      WriteLn('done')
    end.
    ''';

  SrcRepeat = '''
    program P;
    var I: Int;
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
    var I: Int;
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
    var I: Int;
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
    var I, J: Int;
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
      Counter: Int;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForUp, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_Downto_PrintsRange;
var Output: string; RCode: Int;
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
    procedure Check(N: Int);
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
    var A, B, N: Int;
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
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRepeat, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_BreakExitsEarly;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForBreakE2E, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_ContinueSkipsIteration;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForContinue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 4 5', '1' + LE + '2' + LE + '4' + LE + '5' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_Nested_For_Loops;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcNestedFor, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested 2x2', '11' + LE + '12' + LE + '21' + LE + '22' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_IncDec_CapturedVar;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIncCaptured, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Inc(captured) + Inc(captured,5) = 6', '6' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_ExitValue_ReturnsEarly;
var Output: string; RCode: Int;
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
    var i, r: Int;
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
    var i: Int;
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
    var i: Int32;
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
    var I, S, Lo, Hi: Int;
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

procedure TE2EControlFlowTests.TestRun_For_EndsAtTypeLimit_NoWrap;
const
  {
    A for loop runs once per value from start to end INCLUSIVE whatever the
    counter's type -- even when the end is the type's own limit
    (for I := Low(Int8) to High(Int8)).  Both backends incremented the counter
    and then compared it with the end, so the step past High(T) wrapped to
    Low(T) and the loop never ended (GH #237): x86-64 for every type narrower
    than 64 bits, arm64 for Int64 and for a captured counter (stored at its
    declared width).  An unsigned counter compares unsigned (a bound above
    High(Int64) ran zero times), and an Int8 global with literal bounds is
    stored at its own width on x86-64 (a 4-byte store clobbered the next
    global).  Every loop also guards against running away.
  }
  Src = '''
    program P;
    var
      i8: Int8;
      i16: Int16;
      b: Byte;
      w: UInt16;
      u32: UInt32;
      i64: Int64;
      u64: UInt64;
      gA: Int8;
      gB: Int8;
      c: Int;
      big: UInt64;

    procedure Captured;
    var
      k: Int8;
      n: Int;
      F: reference to procedure;
    begin
      n := 0;
      F := procedure
        begin
          if k = High(Int8) then
            n := n + 1000;
          n := n + 1;
        end;
      for k := 120 to High(Int8) do
      begin
        F();
        if n > 3000 then
          Break;
      end;
      WriteLn('cap ', n);
    end;

    procedure Nested;
    var
      k: Int16;
      n: Int;
      procedure Bump;
      begin
        n := n + 1;
      end;
    begin
      n := 0;
      for k := High(Int16) - 3 to High(Int16) do
      begin
        Bump();
        if n > 3000 then
          Break;
      end;
      WriteLn('nest ', n);
    end;

    procedure Locals;
    var
      k: Int8;
      q: UInt64;
      n: Int;
    begin
      n := 0;
      for k := Low(Int8) to High(Int8) do
      begin
        n := n + 1;
        if n > 3000 then
          Break;
      end;
      WriteLn('loc ', n);
      n := 0;
      for q := 2 downto 0 do
      begin
        n := n + 1;
        if n > 3000 then
          Break;
      end;
      WriteLn('locq ', n);
    end;

    begin
      c := 0;
      for i8 := Low(Int8) to High(Int8) do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('i8 ', c);
      c := 0;
      for i8 := High(Int8) downto Low(Int8) do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('i8d ', c);
      c := 0;
      for i16 := Low(Int16) to High(Int16) do
      begin
        c := c + 1;
        if c > 70000 then
          Break;
      end;
      WriteLn('i16 ', c);
      c := 0;
      for b := 0 to 255 do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('b ', c);
      c := 0;
      for b := 255 downto 0 do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('bd ', c);
      c := 0;
      for w := High(UInt16) - 2 to High(UInt16) do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('w ', c);
      c := 0;
      for u32 := High(UInt32) - 2 to High(UInt32) do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('u32 ', c);
      c := 0;
      for i64 := High(Int64) - 2 to High(Int64) do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('i64 ', c);
      c := 0;
      for i64 := Low(Int64) + 2 downto Low(Int64) do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('i64d ', c);
      c := 0;
      for u64 := High(UInt64) - 2 to High(UInt64) do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('u64 ', c);
      c := 0;
      for u64 := 2 downto 0 do
      begin
        c := c + 1;
        if c > 3000 then
          Break;
      end;
      WriteLn('u64d ', c);
      c := 0;
      for i8 := 5 to 4 do
        c := c + 1;
      for u64 := 1 to 0 do
        c := c + 1;
      for b := 0 downto 1 do
        c := c + 1;
      WriteLn('empty ', c);
      c := 0;
      for u64 := 0 to 2 do
        c := c + 1;
      WriteLn('u64s ', c);
      c := 0;
      big := High(UInt64) - 1;
      for u64 := big - 2 to big do
        c := c + 1;
      for u64 := 1 to big do
      begin
        c := c + 1;
        if c > 5 then
          Break;
      end;
      WriteLn('u64big ', c);
      gB := 7;
      for gA := 1 to 3 do
        c := c + 1;
      WriteLn('nb ', gB);
      Captured();
      Nested();
      Locals();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'i8 256' + LE +
    'i8d 256' + LE +
    'i16 65536' + LE +
    'b 256' + LE +
    'bd 256' + LE +
    'w 3' + LE +
    'u32 3' + LE +
    'i64 3' + LE +
    'i64d 3' + LE +
    'u64 3' + LE +
    'u64d 3' + LE +
    'empty 0' + LE +
    'u64s 3' + LE +
    'u64big 6' + LE +
    'nb 7' + LE +
    'cap 1008' + LE +
    'nest 4' + LE +
    'loc 256' + LE +
    'locq 3' + LE, 0);
end;

procedure TE2EControlFlowTests.TestRun_Repeat_BodyRunsBeforeTest;
const
  {
    repeat runs its body BEFORE the first test, so a condition already true
    still runs it once, and leaves when the condition becomes true.
    Replaces the QBE IR checks in cp.test.repeatloop. }
  Src = '''
    program P;
    var I, N: Int;
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
    function Abs1(X: Int): Int;
    begin
      if X < 0 then
      begin
        Result := 0 - X;
        exit
      end;
      Result := X
    end;
    function Classify(N: Int): Int;
    begin
      if N < 0 then Exit(-1);
      Result := 1
    end;
    var I: Int;
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
    procedure Pick(N: Int);
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
      TRec = record Name: string; Number: Int32; end;
      TItem = record S: string; end;
      TMyEnum = class
        FI, FMax: Int32;
        function MoveNext: Boolean;
        function GetCurrent: Int32;
        property Current: Int32 read GetCurrent;
      end;
      TMyCol = class
        Count: Int32;
        function GetEnumerator: TMyEnum;
      end;
      TItemEnum = class
        FI: Int32;
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
    function TMyEnum.GetCurrent: Int32; begin Result := FI * 10 end;
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
      Col: TMyCol; X, I: Int32; Arr: array[0..4] of Int32;
      NZ: array[3..7] of Int32; DA: array of Int32; S: string; B: Byte;
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

procedure TE2EControlFlowTests.TestRun_ForIn_WritesThroughLoopVar_WhereTheyLand;
const
  Src = '''
    program P;
    type
      TIn = record X: Int32; end;
      TC = class F: Int32; end;
      TSA = array[0..1] of Int32;
      TR = record F: Int32; Arr: array[0..1] of TIn;
        D: array of TIn; C: TC; end;
    procedure Mut(var V: Int32); begin V := 9 end;
    var A: array of TR; r: TR; S: array of string; t: string;
      SA: array of TSA; sa1: TSA;
    begin
      SetLength(A, 1);
      SetLength(A[0].D, 1);
      A[0].C := TC.Create();
      SetLength(S, 1);
      S[0] := 'ab';
      SetLength(SA, 1);
      for r in A do Mut(r.F);
      for r in A do Mut(r.Arr[0].X);
      for t in S do t[0] := 'x';
      for sa1 in SA do sa1[0] := 2;
      for sa1 in SA do Mut(sa1[1]);
      WriteLn(A[0].F, ' ', A[0].Arr[0].X, ' ', S[0], ' ', SA[0][0], ' ', SA[0][1]);
      for r in A do r.D[0].X := 5;
      for r in A do Mut(r.C.F);
      WriteLn(A[0].D[0].X, ' ', A[0].C.F)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0 0 ab 0 0' + #10 + '5 9' + #10, 0);
end;

procedure TE2EControlFlowTests.TestRun_ForIn_RecordAndInterfaceEnumerators;
const
  Src = '''
    program P;
    type
      TRangeEnum = record
        Cur, Last: Int;
        function MoveNext(): Boolean;
        function GetCurrent(): Int;
        property Current: Int read GetCurrent;
      end;
      TRange = record
        Lo, Hi: Int;
        function GetEnumerator(): TRangeEnum;
      end;
      IWordEnum = interface
        function MoveNext(): Boolean;
        function GetCurrent(): string;
        property Current: string read GetCurrent;
      end;
      TWordEnum = class(TObject, IWordEnum)
        Words: array of string;
        N: Int;
        function MoveNext(): Boolean;
        function GetCurrent(): string;
      end;
      TWords = class
        Items: array of string;
        function GetEnumerator(): IWordEnum;
      end;
      { a record enumerator carrying a managed field }
      TTagEnum = record
        Prefix: string;
        N: Int;
        function MoveNext(): Boolean;
        function GetCurrent(): string;
        property Current: string read GetCurrent;
      end;
      ITagged = interface
        function GetEnumerator(): TTagEnum;
      end;
      TTagged = class(TObject, ITagged)
        function GetEnumerator(): TTagEnum;
      end;
    var
      Calls: Int;

    function TRangeEnum.MoveNext(): Boolean; begin Cur := Cur + 1; Result := Cur <= Last end;
    function TRangeEnum.GetCurrent(): Int; begin Result := Cur end;
    function TRange.GetEnumerator(): TRangeEnum; begin Result.Cur := Lo - 1; Result.Last := Hi end;
    function TWordEnum.MoveNext(): Boolean; begin N := N + 1; Result := N <= Length(Words) end;
    function TWordEnum.GetCurrent(): string; begin Result := Words[N - 1] + '!' end;
    function TWords.GetEnumerator(): IWordEnum;
    var E: TWordEnum;
    begin
      E := TWordEnum.Create();
      E.Words := Items;
      Result := E
    end;
    function TTagEnum.MoveNext(): Boolean; begin N := N + 1; Result := N <= 3 end;
    function TTagEnum.GetCurrent(): string; begin Result := Prefix + IntToStr(N) end;
    function TTagged.GetEnumerator(): TTagEnum; begin Result.Prefix := 'tag' + '-'; Result.N := 0 end;

    function MakeRange(L, H: Int): TRange;
    begin
      Calls := Calls + 1;
      Result.Lo := L;
      Result.Hi := H
    end;

    procedure InProc(W: TWords);
    var S: string; X: Int; T: ITagged;
    begin
      for S in W do
      begin
        if S = 'b!' then Continue;
        Write(S, ' ')
      end;
      WriteLn();
      for X in MakeRange(1, 9) do
      begin
        if X > 3 then Break;
        Write(X, ' ')
      end;
      WriteLn('calls ', Calls);
      T := TTagged.Create();
      for S in T do Write(S, ' ');
      WriteLn()
    end;

    var
      R: TRange;
      X, Y: Int;
      W: TWords;
      S: string;
    begin
      R.Lo := 2;
      R.Hi := 4;
      for X in R do Write(X, ' ');
      WriteLn();
      for X in R do
        for Y in MakeRange(10, 11) do
          Write(X * 100 + Y, ' ');
      WriteLn();
      W := TWords.Create();
      SetLength(W.Items, 3);
      W.Items[0] := 'a';
      W.Items[1] := 'b';
      W.Items[2] := 'c';
      for S in W do Write(S, ' ');
      WriteLn();
      InProc(W);
      R.Hi := 1;
      for X in R do Write('never');
      WriteLn('done')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 3 4 ' + LE +
    '210 211 310 311 410 411 ' + LE +
    'a! b! c! ' + LE +
    'a! c! ' + LE +
    '1 2 3 calls 4' + LE +
    'tag-1 tag-2 tag-3 ' + LE +
    'done' + LE, 0);
  AssertLeakFreeOnAll(Src, 'done');
end;

procedure TE2EControlFlowTests.TestRun_ForIn_CollectionThroughCall_EvaluatedOnce;
const
  Src = '''
    program P;
    type
      TArr = array[0..3] of Int;
      TRec = record A: TArr; D: array of Int; end;
      TObj = class
      public
        Arr: TArr;
        D: array of string;
        function GetR: TRec;
        property R: TRec read GetR;
      end;
    var Calls: Int; Pool: array of TRec; Keep: TObj;
    function F(N: Int): TRec;
    begin
      Calls := Calls + 1;
      Result.A[1] := N; SetLength(Result.D, 2); Result.D[1] := N * 10;
    end;
    function TObj.GetR: TRec; begin Result := F(7); end;
    function MkArr: TArr; begin Calls := Calls + 1; Result[3] := 33; end;
    function G: Int; begin Calls := Calls + 1; Result := 1; end;
    function MkObj: TObj;
    begin
      Calls := Calls + 1;
      Result := TObj.Create(); Result.Arr[2] := 22;
      SetLength(Result.D, 2); Result.D[0] := 'x' + IntToStr(Calls); Result.D[1] := 'y';
    end;
    function GetKeep: TObj; begin Calls := Calls + 1; Result := Keep; end;
    procedure Report(const AWhat: string; ASum: Int);
    begin
      WriteLn(AWhat, ' sum=', ASum, ' calls=', Calls);
      Calls := 0;
    end;
    var O: TObj; X, Sum: Int; S, Acc: string;
    begin
      O := TObj.Create();
      SetLength(Pool, 2); Pool[1].A[0] := 5;
      Sum := 0; for X in F(3).A do Sum := Sum + X; Report('F(3).A', Sum);
      Sum := 0; for X in F(3).D do Sum := Sum + X; Report('F(3).D', Sum);
      Sum := 0; for X in O.R.A do Sum := Sum + X; Report('O.R.A', Sum);
      Sum := 0; for X in MkArr() do Sum := Sum + X; Report('MkArr()', Sum);
      Sum := 0; for X in Pool[G()].A do Sum := Sum + X; Report('Pool[G()].A', Sum);
      Keep := TObj.Create(); SetLength(Keep.D, 3); Keep.D[0] := 'a'; Keep.D[1] := 'b'; Keep.D[2] := 'c';
      Acc := '';
      for S in GetKeep().D do
      begin
        SetLength(Keep.D, 0);
        Acc := Acc + S;
      end;
      WriteLn(Acc, ' ', Length(Keep.D)); Report('GetKeep().D', 0);
      O.Free(); Keep.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'F(3).A sum=3 calls=1' + LineEnding +
    'F(3).D sum=30 calls=1' + LineEnding +
    'O.R.A sum=7 calls=1' + LineEnding +
    'MkArr() sum=33 calls=1' + LineEnding +
    'Pool[G()].A sum=5 calls=1' + LineEnding +
    'abc 0' + LineEnding +
    'GetKeep().D sum=0 calls=1' + LineEnding, 0);
end;

initialization
  RegisterTest(TE2EControlFlowTests);

end.
