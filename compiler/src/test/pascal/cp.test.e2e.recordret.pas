{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.recordret;

{ Behavioural coverage for QBE record-by-value return: compile + run
  programs that return records through every reg-return shape (rcInt1
  in widths 1/2/4/8 + rcInt2 16-byte aggregate) and verify the values
  arrive at the caller's destination intact.

  These tests catch bugs that pure IR-shape assertions miss — wrong
  load width, wrong store width, sign-extend confusion, padding-byte
  leakage between fields. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ERecordReturnTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { rcInt1 1B — single Byte field. }
    procedure TestRun_RcInt1_OneByte_RoundTrip;
    { rcInt1 2B — two Byte fields. }
    procedure TestRun_RcInt1_TwoByte_RoundTrip;
    { rcInt1 4B — two SmallInt fields, negative value catches
      unsigned-load sign loss. }
    procedure TestRun_RcInt1_TwoSmallInt_NegativeValue;
    { rcInt1 8B — two Integer fields, multi-field one-eightbyte. }
    procedure TestRun_RcInt1_TwoInteger_RoundTrip;
    { rcInt1 8B — single Int64, boundary value. }
    procedure TestRun_RcInt1_Int64_MaxValue;
    { rcInt2 16B — two Int64 fields. }
    procedure TestRun_RcInt2_TwoInt64_RoundTrip;
    { rcInt2 16B — Integer + Int64 with tail-pad layout. }
    procedure TestRun_RcInt2_IntegerPlusInt64;
    { rcSSE1 8B — single Double field, xmm0 round-trip. }
    procedure TestRun_RcSSE1_Double_RoundTrip;
    { rcSSE2 16B — two Doubles, xmm0:xmm1. }
    procedure TestRun_RcSSE2_TwoDoubles_RoundTrip;
    { rcIntSSE 16B — Int64 + Double via (rax, xmm0). }
    procedure TestRun_RcIntSSE_Int64Double_RoundTrip;
    { rcSSEInt 16B — Double + Int64 via (xmm0, rax). }
    procedure TestRun_RcSSEInt_DoubleInt64_RoundTrip;
    { rcSSE1 with Single — 4B record via xmm0 as `s`. }
    procedure TestRun_RcSSE1_Single_RoundTrip;
    { Nested record — inner TPoint (8 B int) embedded in 12 B outer → rcInt2. }
    procedure TestRun_RcInt2_NestedRecord_RoundTrip;
    { Two Single fields — 8 B, all-float leaves → rcSSE1. }
    procedure TestRun_RcSSE1_TwoSingle_RoundTrip;
    { Managed-field record stays on sret (string field → no register return). }
    procedure TestRun_ManagedField_StaysSret;
    { Regression: SetLength + indexed store on a dynamic-array FIELD of an
      sret-Result record.  The native backend used to leaq the address of the
      Result pointer slot and add the field offset to it, instead of loading
      the pointer first — corrupting the stack (crash).  Both backends. }
    procedure TestRun_SretResult_DynArrayField_SetLength;
    { Regression: a record-returning METHOD call result passed directly as a
      const-record argument.  EmitArgHoist materialised the sret buffer via
      EmitExprToEax, which has no sret path for method calls (only functions),
      so the argument pointer was garbage and the callee read junk (crash).
      Both backends. }
    procedure TestRun_RecordMethodResult_AsConstArg;
    { Regression: a SCALAR FIELD of a record-returning call result, read inline
      as an argument alongside a const-string argument.  Reading the field via
      EmitExprToEax left the call's sret buffer allocated on the stack, shifting
      %rsp so the already-pushed string argument was reloaded from the wrong
      slot and lost.  Both backends. }
    procedure TestRun_RecordCallFieldArg_WithStringArg;
    { Regression: a FLOAT argument to a function/method that returns a record
      with a managed (dynamic-array) field.  The native sret call path
      materialised every argument via EmitExprToEax (integer-only), so a float
      literal raised "unsupported expression form TFloatLiteral" and a float
      variable would have gone through an integer register.  The sret arg path
      now routes float args through %xmm registers per the SysV ABI.  QBE was
      always correct, so these run on both backends. }
    procedure TestRun_FloatArg_ManagedRecordReturn_Func;
    procedure TestRun_TwoFloatArgs_ManagedRecordReturn_Func;
    procedure TestRun_FloatArg_ManagedRecordReturn_Method;
    { BUG-027 class: the sret float-arg spill stored %xmm0 by PARAM width
      without matching the VALUE width first — an integer arg into a Single
      param spilled the low 32 bits of a double (0 for small ints), and a
      Single arg into a Double param spilled a garbage double.  Both the
      standalone-function and method sret paths are covered. }
    procedure TestRun_SretFloatArgs_WidthMismatch_Func;
    procedure TestRun_SretFloatArgs_WidthMismatch_Method;
    { Regression: a method call whose RECEIVER is itself a record-returning
      call — A.Plus(B).Val().  The native backend used the record VALUE (the
      reg-return payload, or the sret buffer's first bytes) as the Self POINTER,
      dereferencing garbage and crashing.  It now materialises the receiver
      result into a stack buffer and passes its address as Self.  QBE was always
      correct; both backends asserted equal. }
    procedure TestRun_ChainedRecvRegReturn_ScalarResult;
    procedure TestRun_ChainedRecvSretReturn_RecordResult;
    procedure TestRun_ChainedRecvManyArgs;
    procedure TestRun_ChainedRecvDoubleChain;
    procedure TestRun_ChainedRecvManagedRecord_TDecimalLike;
    { Regression: a record-returning method assigned back into the SAME variable
      that is its receiver (M := M.Method(...)).  The sret destination buffer
      would alias Self, so the callee wrote Result (== Self) while still reading
      Self — clobbering it mid-flight.  Fix routes the call through a fresh temp
      and moves the result into the destination only after the call returns.
      Both backends; managed (string) and scalar fields both checked. }
    procedure TestRun_SelfAssignRecordMethod_ManagedField;
    procedure TestRun_SelfAssignRecordMethod_ScalarFields;
    { Regression: a record-returning FREE FUNCTION whose result is assigned back
      over a variable that is also one of its ARGUMENTS (R := CompR(R)).  The
      caller memset the sret destination to zero BEFORE evaluating the argument
      list, so the callee received an already-cleared value and computed from
      zeroes.  Broke on BOTH backends.  The control assignment to a DISTINCT
      destination in the same program pins that the non-aliasing path (which
      must still write straight into the destination) is unaffected. }
    procedure TestRun_RecordSelfAssign_FreeFunction;
    { Same aliasing shape with the aliased variable in NON-FIRST argument
      position — argument position must not matter. }
    procedure TestRun_RecordSelfAssign_NonFirstArgPosition;
    { Same aliasing shape where the destination is also an ARGUMENT of a record
      METHOD call whose receiver is a different variable (A := Obj.Comp(A)). }
    procedure TestRun_RecordSelfAssign_MethodArgument;
    { Regression: a record-returning method that takes an INTERFACE parameter.
      An interface is a fat pointer (obj + itab) occupying TWO integer-register
      slots, but the native sret/record call paths popped one register per
      LOGICAL argument, so the interface's second slot was never loaded — the
      args landed in the wrong registers and (sret case) the stack was left
      unbalanced, crashing.  This is the root cause of the TDecimal.RoundTo /
      Divide / SetScale native crash (they take a const IRoundingStrategy and
      return a record).  Both backends. }
    procedure TestRun_InterfaceArg_SretRecordReturn;
    procedure TestRun_InterfaceArg_RegRecordReturn;
    procedure TestRun_InterfaceArg_IntPlusInterface_RegReturn;
    { Regression: a FREE FUNCTION (not a method) returning a record by value
      (sret) that takes an interface parameter.  EmitSretCall pushed one stack
      slot per logical argument, so the interface's second fat-pointer slot
      (itab) was never pushed/popped — the registers were misaligned and the
      stack unbalanced, crashing.  The method path (EmitMethodSretCall) was
      already fixed; this covers the free-function path.  Both backends. }
    procedure TestRun_InterfaceArg_FreeFunc_SretReturn;
    procedure TestRun_InterfaceArg_FreeFunc_IntThenInterface;
    { Regression: an override that returns a record with a managed (string)
      field by value, sourced from `inherited`.  The inherited call path
      dropped the hidden sret pointer and passed Self into the sret slot, so
      the base wrote its managed field over the Self object and _StringRelease
      ran on garbage → heap corruption / segfault.  Both backends.  Covers the
      assignment form (Result := inherited M()) and the implicit-Result
      statement form (inherited M;). }
    procedure TestRun_InheritedRecordReturn_ManagedField;
    procedure TestRun_InheritedRecordReturn_StatementForm;
    { Regression: reading the OFFSET-0 field of an sret function's own Result
      mid-body (read-modify) after assigning Result from a record-returning
      call.  The native offset-0 field-read shortcut loaded the Result slot
      directly — but for an sret function that slot holds a POINTER to the
      record, so the buffer pointer was read as the field value (garbage).
      Offset>0 fields were fine (they always deref). Both backends.  (The fix
      lives in the inline-asm commit; this test, from Andrew's parallel fix,
      locks it in.) }
    procedure TestRun_SretResult_ReadModifyOffsetZeroField;
    { Regression: calling a record-returning METHOD as a statement (result
      discarded) with no assignment target.  The SysV sret ABI puts the sret
      pointer in %rdi and Self in %rsi, but without a buffer the callee wrote
      the record through Self, corrupting the object.  Both backends. }
    procedure TestRun_DiscardedRecordReturn_ManagedField;
    { Same for a small record with only scalar fields (register-returned,
      not sret) — the return value goes to %rax and is harmlessly discarded,
      but we must verify codegen doesn't crash. }
    procedure TestRun_DiscardedRecordReturn_ScalarOnly;
    { Discarded record-returning call via an expression receiver
      (Obj.RecordMethod();).  Tests the ObjExpr path. }
    procedure TestRun_DiscardedRecordReturn_ObjExprReceiver;
    { Regression: reading a PROPERTY whose getter returns a record with a
      managed (string) field.  The property read was emitted as a scalar-return
      call (object pointer where the sret pointer belongs), over-releasing the
      string field -> `_StringRelease corrupted header`.  Exercises the read as
      an assignment (twice), a value argument, and a nested field access.
      Both backends. }
    procedure TestRun_RecordProperty_Read_AllContexts;
    { BUG-20260719-native-indexed-prop-record: reading an INDEXED property whose
      getter returns a record segfaulted on native (the index was mis-marshalled
      against the sret ABI).  Covers a small register-return record, a large
      sret record, and a managed-field record, plus a nested-field read. }
    procedure TestRun_IndexedRecordProperty_Read;
    { BUG-002 A-indexed via DEFAULT array property: reading a record-returning
      getter through subscript syntax (H[0], not H.Items[0]) — the record read
      lands inside a TStringSubscriptExpr the record-sret gate did not recognise,
      so QBE emitted invalid IR and native segfaulted.  Covers register-class,
      large sret, and managed records, plus a field-read off the subscript. }
    procedure TestRun_DefaultSubscriptRecordProperty_Read;
    { Regression: a for-in loop whose enumerator's Current returns a record with
      a managed (string) field.  The loop reads Enumerator.Current (a property)
      each pass; the record must sret into the loop variable rather than be
      copied via a scalar-return call.  Both backends. }
    procedure TestRun_ForIn_RecordCurrent_ManagedField;
    { A record field assigned FROM a record-returning call whose record has a
      managed (string) field — Result.Field := MakeRec().  The callee sret's
      into __rret and the +1 string ref transfers into the field.  This is the
      uToolchain 'Result.QBE := ResolveQBE()' shape that blocked the arm64
      self-cross-compile.  Both backends. }
    procedure TestRun_ManagedRecordFieldStore_FromCall;
    { Reading a record-returning indexed getter on a list held in a CLASS FIELD
      (Obj.ListField[I]) — the receiver is the field, not the outer object. }
    procedure TestRun_IndexedRecordGetter_OnClassField;
  end;

implementation

procedure TE2ERecordReturnTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-recordret');
end;

const
  LE = #10;

  SrcOneByte = '''
    program P;
    type TB = record C: Byte; end;
    function MakeIt(V: Byte): TB;
    begin
      Result.C := V
    end;
    var R: TB;
    begin
      R := MakeIt(200);
      WriteLn(R.C)
    end.
    ''';

  SrcTwoByte = '''
    program P;
    type T2B = record A, B: Byte; end;
    function MakeIt(A, B: Byte): T2B;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2B;
    begin
      R := MakeIt(7, 250);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';

  SrcTwoSmallIntNeg = '''
    program P;
    type TS = record A, B: SmallInt; end;
    function MakeIt(A, B: SmallInt): TS;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: TS;
    begin
      R := MakeIt(-1, -32000);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';

  SrcTwoInteger = '''
    program P;
    type TXY = record X, Y: Integer; end;
    function MakeIt(X, Y: Integer): TXY;
    begin
      Result.X := X;
      Result.Y := Y
    end;
    var R: TXY;
    begin
      R := MakeIt(123456, -789012);
      WriteLn(R.X, ' ', R.Y)
    end.
    ''';

  SrcInt64Max = '''
    program P;
    type TI = record V: Int64; end;
    function MakeIt(V: Int64): TI;
    begin
      Result.V := V
    end;
    var R: TI;
    begin
      R := MakeIt(9223372036854775807);
      WriteLn(R.V)
    end.
    ''';

  SrcTwoInt64 = '''
    program P;
    type T2 = record A, B: Int64; end;
    function MakeIt(A, B: Int64): T2;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2;
    begin
      R := MakeIt(111111111111, 222222222222);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';

  SrcOneDouble = '''
    program P;
    type TF = record V: Double; end;
    function MakeIt(V: Double): TF;
    begin
      Result.V := V
    end;
    var R: TF;
    begin
      R := MakeIt(3.5);
      WriteLn(R.V)
    end.
    ''';

  SrcTwoDouble = '''
    program P;
    type T2D = record A, B: Double; end;
    function MakeIt(A, B: Double): T2D;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2D;
    begin
      R := MakeIt(1.5, -2.5);
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''';

  SrcOneSingle = '''
    program P;
    type TF = record V: Single; end;
    function MakeIt(V: Single): TF;
    begin
      Result.V := V
    end;
    var R: TF;
    begin
      R := MakeIt(2.5);
      WriteLn(R.V)
    end.
    ''';

  SrcIntSSE = '''
    program P;
    type TM = record I: Int64; D: Double; end;
    function MakeIt(I: Int64; D: Double): TM;
    begin
      Result.I := I;
      Result.D := D
    end;
    var R: TM;
    begin
      R := MakeIt(42, 3.5);
      WriteLn(R.I);
      WriteLn(R.D)
    end.
    ''';

  SrcSSEInt = '''
    program P;
    type TM = record D: Double; I: Int64; end;
    function MakeIt(D: Double; I: Int64): TM;
    begin
      Result.D := D;
      Result.I := I
    end;
    var R: TM;
    begin
      R := MakeIt(-1.5, 99);
      WriteLn(R.D);
      WriteLn(R.I)
    end.
    ''';

  SrcMixIntInt64 = '''
    program P;
    type TM = record X: Integer; Y: Int64; end;
    function MakeIt(X: Integer; Y: Int64): TM;
    begin
      Result.X := X;
      Result.Y := Y
    end;
    var R: TM;
    begin
      R := MakeIt(42, 1000000000000);
      WriteLn(R.X, ' ', R.Y)
    end.
    ''';

procedure TE2ERecordReturnTests.TestRun_RcInt1_OneByte_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneByte, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('200', '200' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoByte_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoByte, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two-byte fields', '7 250' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoSmallInt_NegativeValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoSmallIntNeg, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { Negative SmallInts must survive the rcInt1 round-trip even though
    the eightbyte load is unsigned — sign restoration happens at field
    access time via LoadInstrFor on the destination buffer. }
  AssertEquals('negative SmallInts', '-1 -32000' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoInteger_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoInteger, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two integers', '123456 -789012' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_Int64_MaxValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64Max, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Int64 max', '9223372036854775807' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_TwoInt64_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoInt64, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two int64s', '111111111111 222222222222' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_IntegerPlusInt64;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMixIntInt64, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('mixed Integer+Int64', '42 1000000000000' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_Double_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneDouble, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3.5 via xmm0', '3.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE2_TwoDoubles_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoDouble, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1.5 + -2.5 via xmm0:xmm1', '1.5' + LE + '-2.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcIntSSE_Int64Double_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntSSE, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Int64+Double via (rax, xmm0)', '42' + LE + '3.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSEInt_DoubleInt64_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSSEInt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Double+Int64 via (xmm0, rax)', '-1.5' + LE + '99', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_Single_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneSingle, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('2.5 via xmm0 as s', '2.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_NestedRecord_RoundTrip;
const
  Src = '''
    program P;
    type
      TInner = record X, Y: Integer; end;
      TOuter = record A: TInner; B: Integer; end;
    function MakeIt(X, Y, B: Integer): TOuter;
    begin
      Result.A.X := X;
      Result.A.Y := Y;
      Result.B := B
    end;
    var R: TOuter;
    begin
      R := MakeIt(10, 20, 30);
      WriteLn(R.A.X, ' ', R.A.Y, ' ', R.B)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested record fields', '10 20 30' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_TwoSingle_RoundTrip;
const
  Src = '''
    program P;
    type T2S = record A, B: Single; end;
    function MakeIt(A, B: Single): T2S;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2S;
    begin
      R := MakeIt(1.5, -2.5);
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two Singles via xmm0', '1.5' + LE + '-2.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_ManagedField_StaysSret;
const
  Src = '''
    program P;
    type TS = record S: string; end;
    function MakeIt(S: string): TS;
    begin
      Result.S := S
    end;
    var R: TS;
    begin
      R := MakeIt('hello');
      WriteLn(R.S)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('managed field stays on sret', 'hello' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_SretResult_DynArrayField_SetLength;
const
  Src = '''
    program P;
    type
      TRec = record
        Name: string;
        Cands: array of string;
      end;
    function Make: TRec;
    begin
      Result.Name := 'linker';
      SetLength(Result.Cands, 2);
      Result.Cands[0] := 'cc';
      Result.Cands[1] := 'clang'
    end;
    var R: TRec;
    begin
      R := Make();
      WriteLn(R.Name);
      WriteLn(R.Cands[0]);
      WriteLn(R.Cands[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'linker' + LE + 'cc' + LE + 'clang' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordMethodResult_AsConstArg;
const
  Src = '''
    program P;
    type
      TR = record A, B: Integer; end;
      TFoo = class
        function MakeR: TR;
        procedure Run;
      end;
    function Sum(const R: TR): Integer;
    begin
      Result := R.A + R.B
    end;
    function TFoo.MakeR: TR;
    begin
      Result.A := 1;
      Result.B := 2
    end;
    procedure TFoo.Run;
    begin
      WriteLn(Sum(Self.MakeR()))
    end;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.Run();
      F.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '3' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordCallFieldArg_WithStringArg;
const
  Src = '''
    program P;
    type TR = record A, B: Integer; end;
    function MakeR: TR;
    begin
      Result.A := 1;
      Result.B := 2
    end;
    procedure Check(const Msg: string; Expected, Actual: Integer);
    begin
      WriteLn(Msg, ' ', Expected, ' ', Actual)
    end;
    begin
      Check('vals', 1, MakeR().A)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'vals 1 1' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_FloatArg_ManagedRecordReturn_Func;
const
  Src = '''
    program P;
    type TR = record X: Double; M: array of UInt32; end;
    function Make(V: Double): TR;
    begin Result.X := V end;
    var R: TR;
    begin
      R := Make(0.25);
      WriteLn(R.X)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0.25' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_TwoFloatArgs_ManagedRecordReturn_Func;
const
  Src = '''
    program P;
    type TR = record X, Y: Double; M: array of UInt32; end;
    function Make2(A, B: Double): TR;
    begin Result.X := A; Result.Y := B end;
    var R: TR;
    begin
      R := Make2(0.25, 0.75);
      WriteLn(R.X, ' ', R.Y)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0.25 0.75' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_FloatArg_ManagedRecordReturn_Method;
const
  Src = '''
    program P;
    type
      TR = record X: Double; M: array of UInt32; end;
      TMaker = class
        function Make(V: Double): TR;
      end;
    function TMaker.Make(V: Double): TR;
    begin Result.X := V end;
    var K: TMaker; R: TR;
    begin
      K := TMaker.Create;
      R := K.Make(0.25);
      WriteLn(R.X);
      K.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0.25' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Chained record-call receiver (A.Plus(B).Method())                   }
{ ------------------------------------------------------------------ }

procedure TE2ERecordReturnTests.TestRun_ChainedRecvRegReturn_ScalarResult;
const
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B: TR; N: Integer;
    begin
      A.V := 10; B.V := 5;
      N := A.Plus(B).Val();
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '15' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvSretReturn_RecordResult;
const
  { The OUTER method (Scale) itself returns a record via sret, and its receiver
    is the transient result of Plus — exercises the sret-call receiver path. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Scale(F: Integer): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Scale(F: Integer): TR; begin Result.V := Self.V * F end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B, C: TR;
    begin
      A.V := 10; B.V := 5;
      C := A.Plus(B).Scale(2);
      WriteLn(C.Val())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '30' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvManyArgs;
const
  { >5 user args forces the overflow (stack-arg) call path with a chained
    record-call receiver. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Sum6(A1,A2,A3,A4,A5,A6: Integer): Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Sum6(A1,A2,A3,A4,A5,A6: Integer): Integer;
    begin Result := Self.V + A1+A2+A3+A4+A5+A6 end;
    var A, B: TR; N: Integer;
    begin
      A.V := 10; B.V := 5;
      N := A.Plus(B).Sum6(1,2,3,4,5,6);
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '36' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvDoubleChain;
const
  { Nested chain: the receiver of .Plus(A) is itself A.Plus(B).  Catches a
    %rsp-drift bug where the forwarded sret destination was resolved after a
    push had already moved the stack. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B: TR; N: Integer;
    begin
      A.V := 10; B.V := 5;
      N := A.Plus(B).Plus(A).Val();
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '25' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvManagedRecord_TDecimalLike;
const
  { A managed-field record (dynamic array) returned by value, then chained —
    the shape TDecimal uses.  Single and double chain both checked. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        M: array of UInt32;
        function Plus(const B: TR): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR;
    begin SetLength(Result.M, 1); Result.M[0] := 0; Result.V := Self.V + B.V end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B: TR;
    begin
      A.V := 10; B.V := 5;
      WriteLn(A.Plus(B).Val());
      WriteLn(A.Plus(B).Plus(A).Val())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '15' + LE + '25' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SelfAssignRecordMethod_ManagedField;
const
  { Managed (string) field record method assigned back into its own receiver.
    The non-aliasing case (C := A.Up(B)) and the receiver staying intact after
    the self-assign are both checked as regression guards. }
  Src = '''
    program P;
    type
      TR = record
        S: string;
        function Up(const X: TR): TR;
      end;
    function TR.Up(const X: TR): TR;
    begin Result.S := Self.S + X.S end;
    var A, B, C: TR;
    begin
      A.S := 'a'; B.S := 'b';
      A := A.Up(B);
      WriteLn(A.S);
      C := A.Up(B);
      WriteLn(C.S);
      WriteLn(A.S)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'ab' + LE + 'abb' + LE + 'ab' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SelfAssignRecordMethod_ScalarFields;
const
  { Two-integer record (register-return class) self-assigned through its own
    receiver. }
  Src = '''
    program P;
    type
      TR = record
        A, B: Integer;
        function Add(const X: TR): TR;
      end;
    function TR.Add(const X: TR): TR;
    begin Result.A := Self.A + X.A; Result.B := Self.B + X.B end;
    var R, Q: TR;
    begin
      R.A := 1; R.B := 10; Q.A := 2; Q.B := 20;
      R := R.Add(Q);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '3 30' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordSelfAssign_FreeFunction;
const
  { CompR swaps its argument's two fields.  R := CompR(R) must see R's LIVE
    value (1, 2) and produce (2, 1).  The last two lines are the NON-ALIASING
    control: T := CompR(R) writes straight into T and must keep working. }
  Src = '''
    program P;
    type
      TR = record
        A, B: Integer;
      end;
      TBig = record
        A, B, C, D, E: Integer;
      end;
    function CompR(const S: TR): TR;
    begin Result.A := S.B; Result.B := S.A end;
    function CompBig(const S: TBig): TBig;
    begin
      Result.A := S.E; Result.B := S.D; Result.C := S.C;
      Result.D := S.B; Result.E := S.A
    end;
    var R, T: TR;
        G, H: TBig;
    begin
      R.A := 1; R.B := 2;
      R := CompR(R);
      WriteLn(R.A, ' ', R.B);
      G.A := 1; G.B := 2; G.C := 3; G.D := 4; G.E := 5;
      G := CompBig(G);
      WriteLn(G.A, ' ', G.B, ' ', G.C, ' ', G.D, ' ', G.E);
      R.A := 7; R.B := 8;
      T := CompR(R);
      WriteLn(T.A, ' ', T.B);
      G.A := 1; G.B := 2; G.C := 3; G.D := 4; G.E := 5;
      H := CompBig(G);
      WriteLn(H.A, ' ', H.B, ' ', H.C, ' ', H.D, ' ', H.E)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 1' + LE + '5 4 3 2 1' + LE + '8 7' + LE + '5 4 3 2 1' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordSelfAssign_NonFirstArgPosition;
const
  Src = '''
    program P;
    type
      TR = record
        A, B: Integer;
      end;
    function Pick(const N: Integer; const S: TR): TR;
    begin Result.A := S.B + N; Result.B := S.A + N end;
    var R: TR;
    begin
      R.A := 1; R.B := 2;
      R := Pick(10, R);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12 11' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordSelfAssign_MethodArgument;
const
  { The receiver (Q) is NOT the destination — the ALIAS is in the argument
    list, which the old receiver-only guard never inspected. }
  Src = '''
    program P;
    type
      TR = record
        A, B: Integer;
        function Comp(const X: TR): TR;
      end;
    function TR.Comp(const X: TR): TR;
    begin Result.A := X.B + Self.A; Result.B := X.A + Self.B end;
    var R, Q: TR;
    begin
      R.A := 1; R.B := 2; Q.A := 100; Q.B := 200;
      R := Q.Comp(R);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '102 201' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Record-returning method with an interface (fat-pointer) parameter   }
{ ------------------------------------------------------------------ }

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_SretRecordReturn;
const
  { Managed field -> sret return; the interface param must occupy two arg
    register slots (obj + itab). }
  Src = '''
    program P;
    type
      IThing = interface function Val: Integer; end;
      TThing = class(TObject, IThing) function Val: Integer; end;
      TR = record
        V: Integer;
        M: array of UInt32;
        function Scale(N: Integer; const S: IThing): TR;
      end;
    function TThing.Val: Integer; begin Result := 7 end;
    function TR.Scale(N: Integer; const S: IThing): TR;
    begin SetLength(Result.M, 1); Result.V := Self.V * N + S.Val() end;
    var A, R: TR; T: IThing;
    begin
      A.V := 10; T := TThing.Create;
      R := A.Scale(2, T);
      WriteLn(R.V)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '27' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_RegRecordReturn;
const
  { No managed field -> register-return record; same interface-slot accounting
    applies on the register-return call path. }
  Src = '''
    program P;
    type
      IThing = interface function Val: Integer; end;
      TThing = class(TObject, IThing) function Val: Integer; end;
      TR = record
        V: Integer;
        function Scale(N: Integer; const S: IThing): TR;
      end;
    function TThing.Val: Integer; begin Result := 7 end;
    function TR.Scale(N: Integer; const S: IThing): TR;
    begin Result.V := Self.V * N + S.Val() end;
    var A, R: TR; T: IThing;
    begin
      A.V := 10; T := TThing.Create;
      R := A.Scale(2, T);
      WriteLn(R.V)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '27' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_IntPlusInterface_RegReturn;
const
  { A scalar arg BEFORE the interface arg checks the register ordering:
    N -> %rdx, obj(S) -> %rcx, itab(S) -> %r8. }
  Src = '''
    program P;
    type
      IThing = interface function Tag: Integer; end;
      TThing = class(TObject, IThing)
        FT: Integer;
        function Tag: Integer;
      end;
      TR = record
        V: Integer;
        function Combine(N: Integer; const S: IThing): Integer;
      end;
    function TThing.Tag: Integer; begin Result := Self.FT end;
    function TR.Combine(N: Integer; const S: IThing): Integer;
    begin Result := Self.V + N * 100 + S.Tag() end;
    var A: TR; T: TThing; N: Integer;
    begin
      A.V := 1;
      T := TThing.Create; T.FT := 9;
      N := A.Combine(2, T);
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '210' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_FreeFunc_SretReturn;
const
  Src = '''
    program P;
    type
      IThing = interface function V: Integer; end;
      TT = class(TObject, IThing) function V: Integer; end;
      TR = record A: Integer; M: array of UInt32; end;
    function TT.V: Integer; begin Result := 7 end;
    function Mk(const S: IThing): TR;
    begin SetLength(Result.M, 1); Result.A := S.V() end;
    var R: TR; T: IThing;
    begin
      T := TT.Create;
      R := Mk(T);
      WriteLn(R.A)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_FreeFunc_IntThenInterface;
const
  { A scalar arg before the interface arg pins the register ordering for the
    free-function sret path: N -> %rsi, obj(S) -> %rdx, itab(S) -> %rcx
    (sret buffer is %rdi). }
  Src = '''
    program P;
    type
      IThing = interface function V: Integer; end;
      TT = class(TObject, IThing) function V: Integer; end;
      TR = record A: Integer; M: array of UInt32; end;
    function TT.V: Integer; begin Result := 7 end;
    function Mk(N: Integer; const S: IThing): TR;
    begin SetLength(Result.M, 1); Result.A := N + S.V() end;
    var R: TR; T: IThing;
    begin
      T := TT.Create;
      R := Mk(5, T);
      WriteLn(R.A)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InheritedRecordReturn_ManagedField;
const
  Src = '''
    program P;
    type
      TTok = record Kind: Integer; Value: string; Line: Integer; end;
      TBase = class
        function Next(N: Integer): TTok; virtual;
      end;
      TDeriv = class(TBase)
        function Next(N: Integer): TTok; override;
      end;
    function TBase.Next(N: Integer): TTok;
    begin
      Result.Kind := N;
      Result.Value := 'hello-world';
      Result.Line := 99
    end;
    function TDeriv.Next(N: Integer): TTok;
    begin
      Result := inherited Next(N)
    end;
    var D: TDeriv; T: TTok;
    begin
      D := TDeriv.Create();
      T := D.Next(7);
      WriteLn(T.Kind);
      WriteLn(T.Value);
      WriteLn(T.Line);
      D.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7' + LE + 'hello-world' + LE + '99' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InheritedRecordReturn_StatementForm;
const
  Src = '''
    program P;
    type
      TTok = record Kind: Integer; Value: string; end;
      TBase = class
        function Make(N: Integer): TTok; virtual;
      end;
      TDeriv = class(TBase)
        function Make(N: Integer): TTok; override;
      end;
    function TBase.Make(N: Integer): TTok;
    begin
      Result.Kind := N + 100;
      Result.Value := 'base'
    end;
    function TDeriv.Make(N: Integer): TTok;
    begin
      inherited Make(N)
    end;
    var D: TDeriv; T: TTok;
    begin
      D := TDeriv.Create();
      T := D.Make(5);
      WriteLn(T.Kind);
      WriteLn(T.Value);
      D.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { `inherited Make(N);` with no explicit assignment sets the override's
    Result through the sret pointer. }
  AssertRunsOnAll(Src, '105' + LE + 'base' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SretResult_ReadModifyOffsetZeroField;
const
  Src = '''
    program P;
    type TR = record A: Integer; S: string; B: Integer; end;
    function Raw(N: Integer): TR;
    begin
      Result.A := N;
      Result.S := 'hi';
      Result.B := 20
    end;
    function Make(N: Integer): TR;
    begin
      Result := Raw(N);
      Result.A := Result.A + 1
    end;
    var R: TR;
    begin
      R := Make(10);
      WriteLn(R.A, ' ', R.S, ' ', R.B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { The string field forces a genuine sret return (24 bytes); reading
    Result.A (offset 0) mid-body must deref the Result pointer. }
  AssertRunsOnAll(Src, '11 hi 20' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_DiscardedRecordReturn_ManagedField;
const
  Src = '''
    program P;
    type
      TToken = record
        Kind: Integer;
        Value: string;
      end;
      TLexer = class
        FName: string;
        function Next(): TToken;
        function GetName(): string;
      end;
    function TLexer.Next(): TToken;
    begin
      Result.Kind := 42;
      Result.Value := 'hello'
    end;
    function TLexer.GetName(): string;
    begin
      Result := FName
    end;
    var L: TLexer;
    begin
      L := TLexer.Create();
      L.FName := 'mylex';
      L.Next();
      WriteLn(L.GetName());
      L.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'mylex' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_DiscardedRecordReturn_ScalarOnly;
const
  Src = '''
    program P;
    type
      TPoint = record X, Y: Integer; end;
      TObj = class
        function Pos(): TPoint;
      end;
    function TObj.Pos(): TPoint;
    begin
      Result.X := 10;
      Result.Y := 20
    end;
    var O: TObj;
    begin
      O := TObj.Create();
      O.Pos();
      WriteLn('ok');
      O.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'ok' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_DiscardedRecordReturn_ObjExprReceiver;
const
  Src = '''
    program P;
    type
      TRec = record N: Integer; S: string; end;
      TFactory = class
        FTag: string;
        function Make(): TRec;
        function GetTag(): string;
      end;
      THolder = class
        F: TFactory;
      end;
    function TFactory.Make(): TRec;
    begin
      Result.N := 7;
      Result.S := 'test'
    end;
    function TFactory.GetTag(): string;
    begin
      Result := FTag
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.F := TFactory.Create();
      H.F.FTag := 'mytag';
      H.F.Make();
      WriteLn(H.F.GetTag());
      H.F.Free();
      H.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'mytag' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordProperty_Read_AllContexts;
const
  Src =
    '''
    program P;
    type
      TItem = record
        Name: string;
      end;
      TObj = class
        function GetCurrent: TItem;
        property Current: TItem read GetCurrent;
      end;
    function TObj.GetCurrent: TItem;
    begin
      Result.Name := 'x'
    end;
    procedure Use(A: TItem);
    begin
      WriteLn('arg ', A.Name)
    end;
    var
      O: TObj;
      R: TItem;
    begin
      O := TObj.Create();
      R := O.Current;            { assignment }
      WriteLn('one ', R.Name);
      R := O.Current;            { second read -> the corruption used to hit here }
      WriteLn('two ', R.Name);
      Use(O.Current);            { value argument }
      WriteLn('fld ', O.Current.Name);   { nested field access }
      O.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'one x' + LE + 'two x' + LE + 'arg x' + LE + 'fld x' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ForIn_RecordCurrent_ManagedField;
const
  Src =
    '''
    program P;
    type
      TItem = record
        Name: string;
        N: Integer;
      end;
      TEnum = class
        FI: Integer;
        function GetCurrent: TItem;
        function GetEnumerator: TEnum;
        function MoveNext: Boolean;
        property Current: TItem read GetCurrent;
      end;
    function TEnum.GetCurrent: TItem;
    begin
      Result.Name := 'item';
      Result.N := FI
    end;
    function TEnum.GetEnumerator: TEnum;
    begin
      Result := Self
    end;
    function TEnum.MoveNext: Boolean;
    begin
      FI := FI + 1;
      Result := FI <= 3
    end;
    var
      E: TEnum;
      It: TItem;
    begin
      E := TEnum.Create();
      for It in E do
        WriteLn(It.Name, ' ', It.N);
      E.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'item 1' + LE + 'item 2' + LE + 'item 3' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SretFloatArgs_WidthMismatch_Func;
const
  Src =
    '''
    program P;
    type
      TBig = record
        A: Double;
        B: Double;
        C: Double;
        D: Double;
      end;
    function Make(S: Single; D: Double): TBig;
    begin
      Result.A := S;
      Result.B := D;
      Result.C := 0;
      Result.D := 0
    end;
    var
      R: TBig;
      Sng: Single;
    begin
      Sng := 2.5;
      R := Make(7, Sng);
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Native previously printed 0 (int arg through a Single param) and a
    garbage double (Single arg through a Double param). }
  AssertRunsOnAll(Src, '7' + LE + '2.5' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SretFloatArgs_WidthMismatch_Method;
const
  Src =
    '''
    program P;
    type
      TBig = record
        A: Double;
        B: Double;
        C: Double;
        D: Double;
      end;
      TMaker = class
      public
        function Make(S: Single; D: Double): TBig;
      end;
    function TMaker.Make(S: Single; D: Double): TBig;
    begin
      Result.A := S;
      Result.B := D;
      Result.C := 0;
      Result.D := 0
    end;
    var
      M: TMaker;
      R: TBig;
      Sng: Single;
    begin
      M := TMaker.Create();
      Sng := 2.5;
      R := M.Make(7, Sng);
      WriteLn(R.A);
      WriteLn(R.B);
      M.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7' + LE + '2.5' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ManagedRecordFieldStore_FromCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TTool = record
        Path: string;
        Kind: Integer;
      end;
      TChain = record
        QBE: TTool;
      end;
    function MakeTool: TTool;
    begin
      Result.Path := 'qbe';
      Result.Kind := 5
    end;
    function Build: TChain;
    begin
      Result.QBE := MakeTool()
    end;
    var C: TChain;
    begin
      C := Build();
      WriteLn(C.QBE.Path);
      WriteLn(C.QBE.Kind)
    end.
    ''',
    'qbe' + LE + '5' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_IndexedRecordProperty_Read;
const
  Src =
    '''
    program P;
    type
      TQ = record Index: Integer; Other: Integer; end;
      TBig = record A, B, C, D, E: Integer; end;
      TMan = record Name: string; N: Integer; end;
      TBox = class
        FQ: TQ;
        FBig: TBig;
        FMan: TMan;
        function Get(A: Integer): TQ;
        function GetBig(A: Integer): TBig;
        function GetMan(A: Integer): TMan;
        property Items[A: Integer]: TQ read Get;
        property Bigs[A: Integer]: TBig read GetBig;
        property Mans[A: Integer]: TMan read GetMan;
      end;
    function TBox.Get(A: Integer): TQ; begin Result := FQ end;
    function TBox.GetBig(A: Integer): TBig; begin Result := FBig end;
    function TBox.GetMan(A: Integer): TMan; begin Result := FMan end;
    var B: TBox; T: TQ; Tb: TBig; Tm: TMan;
    begin
      B := TBox.Create();
      B.FQ.Index := 9; B.FQ.Other := 3;
      B.FBig.A := 100; B.FBig.E := 500;
      B.FMan.Name := 'hello'; B.FMan.N := 7;
      T := B.Items[0];
      WriteLn('small ', T.Index, ' ', T.Other);
      Tb := B.Bigs[0];
      WriteLn('big ', Tb.A, ' ', Tb.E);
      Tm := B.Mans[0];
      WriteLn('man ', Tm.Name, ' ', Tm.N);
      WriteLn('nested ', B.Items[0].Index);
      B.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'small 9 3' + LE + 'big 100 500' + LE + 'man hello 7' + LE +
    'nested 9' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_DefaultSubscriptRecordProperty_Read;
const
  Src =
    '''
    program P;
    type
      TQ = record Index: Integer; Other: Integer; end;
      TBig = record A, B, C, D, E: Integer; end;
      TMan = record Name: string; N: Integer; end;
      TBoxQ = class
        FQ: TQ;
        function Get(A: Integer): TQ;
        property Items[A: Integer]: TQ read Get; default;
      end;
      TBoxBig = class
        FBig: TBig;
        function GetBig(A: Integer): TBig;
        property Items[A: Integer]: TBig read GetBig; default;
      end;
      TBoxMan = class
        FMan: TMan;
        function GetMan(A: Integer): TMan;
        property Items[A: Integer]: TMan read GetMan; default;
      end;
    function TBoxQ.Get(A: Integer): TQ; begin Result := FQ end;
    function TBoxBig.GetBig(A: Integer): TBig; begin Result := FBig end;
    function TBoxMan.GetMan(A: Integer): TMan; begin Result := FMan end;
    var Bq: TBoxQ; Bb: TBoxBig; Bm: TBoxMan; T: TQ; Tb: TBig; Tm: TMan;
    begin
      Bq := TBoxQ.Create(); Bq.FQ.Index := 9; Bq.FQ.Other := 3;
      Bb := TBoxBig.Create(); Bb.FBig.A := 100; Bb.FBig.E := 500;
      Bm := TBoxMan.Create(); Bm.FMan.Name := 'hello'; Bm.FMan.N := 7;
      T := Bq[0];
      WriteLn('small ', T.Index, ' ', T.Other);
      Tb := Bb[0];
      WriteLn('big ', Tb.A, ' ', Tb.E);
      Tm := Bm[0];
      WriteLn('man ', Tm.Name, ' ', Tm.N);
      WriteLn('nested ', Bq[0].Index);
      Bq.Free(); Bb.Free(); Bm.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'small 9 3' + LE + 'big 100 500' + LE + 'man hello 7' + LE +
    'nested 9' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_IndexedRecordGetter_OnClassField;
const
  UnitSrc = '''
    unit tokholder;
    interface
    uses Generics.Collections;
    type
      TTok = record
        Kind: Integer;
        Value: string;      { managed field forces the sret class }
        Line: Integer;
        Col: Integer;
      end;
      THolder = class
        Toks: TList<TTok>;
        constructor Create;
        procedure Add(AKind: Integer; const AValue: string; ALine, ACol: Integer);
        function Bare: Integer;
      end;
      TWrap = class
        H: THolder;
        constructor Create;
      end;
    implementation
    constructor THolder.Create;
    begin
      Self.Toks := TList<TTok>.Create();
    end;
    procedure THolder.Add(AKind: Integer; const AValue: string; ALine, ACol: Integer);
    var T: TTok;
    begin
      T.Kind := AKind; T.Value := AValue; T.Line := ALine; T.Col := ACol;
      Self.Toks.Add(T);
    end;
    { bare FField[I] — the IMPLICIT-Self arm }
    function THolder.Bare: Integer;
    begin
      Result := Toks[0].Line;
    end;
    constructor TWrap.Create;
    begin
      Self.H := THolder.Create();
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses Generics.Collections, tokholder;
    var H: THolder; W: TWrap; L: TList<TTok>; Tmp: TTok;
    begin
      H := THolder.Create();
      H.Add(1, 'hello', 42, 7);
      H.Add(2, 'world', 99, 3);
      { LEAF: receiver is a class FIELD (H.Toks) }
      WriteLn(H.Toks[0].Line);
      WriteLn(H.Toks[1].Value);
      { chained straight into an expression }
      WriteLn(H.Toks[0].Line + H.Toks[1].Line);
      { via a temp record }
      Tmp := H.Toks[1];
      WriteLn(Tmp.Col);
      { CHAINED base (W.H.Toks[I]) — a separate semantic arm }
      W := TWrap.Create();
      W.H.Add(3, 'deep', 77, 1);
      WriteLn(W.H.Toks[0].Line);
      WriteLn(W.H.Toks[0].Value);
      { IMPLICIT Self (bare Toks[0] inside a method) — a third arm }
      WriteLn(H.Bare());
      { the form that always worked — must still work }
      L := H.Toks;
      WriteLn(L[0].Value);
    end.
    ''';
var
  Output: string;
  RCode:  Integer;
  B:      TBackend;
begin
  { Obj.ListField[I] where the element is a RECORD: semantic resolved the
    field-with-subscript shape by setting PropRead but never PropReadDecl,
    and the native record-sret gate keys on PropReadDecl.  The call was
    therefore emitted with NO hidden sret buffer, so every argument shifted
    one register: the receiver landed in %rdi (where the callee expects the
    buffer), the index in %rsi (read as Self) and %rdx was uninitialised.
    The callee dereferenced the index as an object -> segfault.

    Reading the SAME list through a local (L := Obj.ListField; L[I]) took the
    property path, which does set PropReadDecl, and always worked -- that
    asymmetry is what made this look like a heap bug rather than a codegen
    one.  Both forms are asserted here so they cannot diverge again.

    Fixing the gate then exposed a second defect: the synthesised getter call
    passed FAE.Base as the receiver, which for a field access is the OUTER
    object, so the callee read TList fields off the wrong instance and
    returned garbage instead of crashing.  The receiver must be the field.

    Found via BlaiseGuard segfaulting on any source containing a duplicated
    token window (its BL-3001 rule reads RefFile.Tokens[Ref.Start].Line). }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both backends: the defect was native-only, so a QBE-only helper would
    have passed throughout and pinned nothing. }
  for B in AllBackends do
  begin
    if not BackendRunnableOnHost(B) then Continue;
    AssertTrue(BackendName(B) + ': compile+link+run',
      CompileAndRunWithUnitOn(B, 'tokholder', UnitSrc, DrvSrc, Output, RCode));
    AssertEquals(BackendName(B) + ': exit code', 0, RCode);
    AssertEquals(BackendName(B) + ': output',
      '42' + LE + 'world' + LE + '141' + LE + '3' + LE +
      '77' + LE + 'deep' + LE + '42' + LE + 'hello' + LE, Output);
  end;
end;

initialization
  RegisterTest(TE2ERecordReturnTests);

end.
