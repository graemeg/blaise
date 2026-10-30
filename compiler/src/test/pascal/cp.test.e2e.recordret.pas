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
    { @Result inside a record-returning function or method, written through: for
      a large record (returned through the hidden result pointer) it is the
      caller's buffer.  x86-64 took the address of the Result SLOT, which holds
      that pointer, so the writes landed in the frame -- the caller read zeros
      and the program crashed. }
    procedure TestRun_AddrOfResult_InRecordFunction;
    { Record call results passed as arguments, side by side: a managed record from
      a method on Self (hoisted into its own stack buffer) and a register-returned
      one from a plain call -- Resolve(Self.MakeSpec(), Host()).  The hoist leant
      on EmitExprToEax leaving a plain call's result at %rsp; once that result got
      a frame scratch the hoist region was missized and x86-64 crashed. }
    procedure TestRun_RecordCallArgs_ManagedAndRegisterShaped;
    { Record call results consumed through their address: an open-array argument
      (ShowOpen(O.Mk(1).A)), @, Length/High, and several in one expression.  On
      x86-64 a plain call's result buffer was a mid-expression `subq` that was
      never freed, so the next pop of an operand already pushed read the buffer:
      F(1).A[1] + F(2).A[1] + F(3).A[1] gave 7, not 9. }
    procedure TestRun_RecordCallAsAddressBase_EveryConsumer;
    { A record produced by every call form -- function, method, static method,
      interface method, implicit-Self method, inherited, closure, GetFn()(X),
      getter, indexed getter, static property, record method -- used as the base
      of an element, string-char or dyn-array read (F(9).A[1], O.R.D[1]).  arm64
      refused the record call base ("record address of this expression",
      BUG-20261010-recordcall-field-address-base); x86-64 called a method,
      inherited or getter base with no result buffer and crashed. }
    procedure TestRun_RecordCallAsAddressBase_EveryCallForm;
    { Discarded results of every owned kind on every receiver form -- implicit
      Self, a named object, a call result, a field, a static method, a free
      function: each needs a result buffer when it returns through x8 / the
      hidden pointer, and what it owns released.  A static method's interface
      result wrote through a garbage pointer on both ISAs, and its string, a
      discarded closure from MkC().GetFn() and a free function's closure
      leaked or corrupted memory. }
    procedure TestRun_DiscardedResultsEveryKind;
    { Aggregate-returning calls in SCALAR contexts and through inherited:
      Assigned(GetFn()), TMethod(C.GetM()).Code, I.GetFn()(4), a discarded
      I.GetFn(), `inherited GetFn();` setting a closure Result.  arm64 refused
      them (the P6 "not yet lowered" family); x86-64 crashed. }
    procedure TestRun_AggregateCallsInScalarContexts;
    { Record, interface and closure results through the procedural value an
      EXPRESSION yields (GetB()(5).S, I := GetI()(), GetC()()(5)) -- read,
      assigned, passed, compared and discarded.  arm64 refused every form;
      x86-64 compiled some and crashed (no result buffer), segfaulted the
      compiler on GetC()()(5), and rejected the interface forms. }
    procedure TestRun_ExprCalleeAggregateResults;
    { record-returning calls with every argument shape: open arrays,
      floats, stack overflow, captures (incl. six or more), var arguments,
      interfaces, a record receiver, virtual dispatch }
    procedure TestRun_SretCall_OpenArrayAndOverflowArgs;
    { A register-returned record from a bare method call on Self, passed as
      an argument (Sum(Mk(3)) inside a method): x86-64 called Mk with an
      sret buffer it never filled, so the callee read zeros. }
    procedure TestRun_ImplicitSelfRecordCall_AsArgument;
    procedure TestRun_SretNested_CapturesWithFloatsAndOverflow;
    procedure TestRun_SretNested_SixCaptures_ResultPointerOnStack;
    procedure TestRun_SretMethod_OverflowVirtualIntfAndRecordReceiver;
    procedure TestRun_RecordReturn_RemainingShapes;
    { a record returned through a closure or a procedural variable, in every
      position: assigned, field-read, passed on, discarded }
    procedure TestRun_ClosureRecordReturn_AllPositions;
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
    procedure TestRun_SingleHfa_AndOddSizedImages;
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
    { Every other receiver form of a discarded record-returning method call:
      a named receiver, a field of Self, var params (class and record), a
      record method, a captured outer local.  The results' managed fields must be
      released, not leaked. }
    procedure TestRun_DiscardedRecordReturn_AllReceiverForms;
    { A discarded record- or interface-returning call on IMPLICIT Self
      (Next(); inside a method).  x86-64 passed Self where the sret pointer
      belongs, so the callee wrote the record over the object; arm64 rejected
      it as not yet lowered. }
    procedure TestRun_DiscardedRecordReturn_ImplicitSelf;
    { Every lowering of `inherited F(..)` returning a record or Single: the
      statement form over an already-set Result, assignment, a register-
      sized record, a field read, a float expression, and the statement
      form outside a function (discarded; a string result too). }
    procedure TestRun_InheritedRecordReturn_AllForms;
    { A record-returning method called on an owned transient receiver
      (MakeL('a').Next()): assigned, register-sized, discarded and as a
      field-read base.  Every receiver is freed exactly once. }
    procedure TestRun_RecordCall_OwnedTransientReceiver;
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
    { BUG-20260722-native-recfield-sret-alias: a record-returning call
      assigned into a record FIELD that the call itself reads -- a record
      method on that field, a getter whose body reads it, the same through a
      var parameter, and a function given the field as an argument.  x86-64
      zeroed the field before the call ran and printed zeros. }
    procedure TestRun_RecordFieldFromCall_ThatReadsTheField;
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
    type TS = record A, B: Int16; end;
    function MakeIt(A, B: Int16): TS;
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
    type TXY = record X, Y: Int; end;
    function MakeIt(X, Y: Int): TXY;
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
    type TF = record V: Float64; end;
    function MakeIt(V: Float64): TF;
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
    type T2D = record A, B: Float64; end;
    function MakeIt(A, B: Float64): T2D;
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
    type TF = record V: Float32; end;
    function MakeIt(V: Float32): TF;
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
    type TM = record I: Int64; D: Float64; end;
    function MakeIt(I: Int64; D: Float64): TM;
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
    type TM = record D: Float64; I: Int64; end;
    function MakeIt(D: Float64; I: Int64): TM;
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
    type TM = record X: Int32; Y: Int64; end;
    function MakeIt(X: Int32; Y: Int64): TM;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneByte, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('200', '200' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoByte_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoByte, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two-byte fields', '7 250' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoSmallInt_NegativeValue;
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoInteger, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two integers', '123456 -789012' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_Int64_MaxValue;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64Max, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Int64 max', '9223372036854775807' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_TwoInt64_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoInt64, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two int64s', '111111111111 222222222222' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_IntegerPlusInt64;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMixIntInt64, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('mixed Integer+Int64', '42 1000000000000' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_Double_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneDouble, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3.5 via xmm0', '3.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE2_TwoDoubles_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoDouble, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1.5 + -2.5 via xmm0:xmm1', '1.5' + LE + '-2.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcIntSSE_Int64Double_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntSSE, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Int64+Double via (rax, xmm0)', '42' + LE + '3.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSEInt_DoubleInt64_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSSEInt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Double+Int64 via (xmm0, rax)', '-1.5' + LE + '99', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_SingleHfa_AndOddSizedImages;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { All-Single records of 1..4 lanes returned and passed by value (lanes in
    s registers on arm64), mixed with Double HFAs, spilling past the eighth
    fp register, plus 3-, 7- and 12-byte integer images stored next to
    guard bytes.  Each guard (G1, G2, H.G, H.H) must survive: a register
    image stored wider than its record overwrote its neighbour. }
  AssertRunsOnAll('''
    program P;
    type
      TF1 = record A: Float32; end;
      TF2 = record A, B: Float32; end;
      TF3 = record A, B, C: Float32; end;
      TF4 = record A, B, C, D: Float32; end;
      TD2 = record A, B: Float64; end;
      TB3 = packed record A, B, C: Byte; end;
      TB7 = packed record A: Int; B: UInt16; C: Byte; end;
      T12 = record A, B, C: Int; end;
      THold = packed record X: TB3; G: Byte; Y: TB7; H: Byte; end;
    function M1(A: Float32): TF1; begin Result.A := A end;
    function M2(A, B: Float32): TF2; begin Result.A := A; Result.B := B end;
    function M3(A, B, C: Float32): TF3; begin Result.A := A; Result.B := B; Result.C := C end;
    function M4(A: Float32): TF4; begin Result.A := A; Result.B := A * 2; Result.C := A * 3; Result.D := A * 4 end;
    function Sum4(R: TF4): Float32; begin Result := R.A + R.B + R.C + R.D end;
    function Sum3(X: Float64; R: TF3; Y: Float32): Float64; begin Result := X + R.A + R.B + R.C + Y end;
    function Mix(R: TF2; D: TD2; S: TF1): Float64; begin Result := R.A + R.B + D.A + D.B + S.A end;
    function Spill(A, B, C, D, E, F, G: Float64; R: TF2): Float64;
    begin Result := A + B + C + D + E + F + G + R.A * 100 + R.B * 1000 end;
    function MB3(V: Byte): TB3; begin Result.A := V; Result.B := V + 1; Result.C := V + 2 end;
    function MB7(V: Int): TB7; begin Result.A := V; Result.B := 7; Result.C := 9 end;
    function M12(V: Int): T12; begin Result.A := V; Result.B := V; Result.C := V end;
    var
      R1: TF1; G1: Int; R2: TF2; R3: TF3; R4: TF4; G2: Int;
      H: THold; Q: T12; PD: TD2;
    begin
      G1 := 111; G2 := 222;
      R1 := M1(2.5); R2 := M2(1.5, 3.25); R3 := M3(1, 2, 3); R4 := M4(1.5);
      WriteLn(R1.A:0:2, ' ', R2.A:0:2, ' ', R2.B:0:2, ' ', R3.C:0:2, ' ', R4.D:0:2, ' ', G1, ' ', G2);
      WriteLn(Sum4(R4):0:2, ' ', Sum4(M4(1)):0:2, ' ', M3(4, 5, 6).B:0:2);
      WriteLn(Sum3(10, R3, 0.5):0:2, ' ', Sum3(1, M3(1, 1, 1), 1):0:2);
      PD.A := 100; PD.B := 200;
      WriteLn(Mix(R2, PD, R1):0:2);
      WriteLn(Spill(1, 2, 3, 4, 5, 6, 7, R2):0:2);
      H.G := 77; H.H := 88;
      H.X := MB3(10); H.Y := MB7(70000);
      WriteLn(H.X.A, ' ', H.X.C, ' ', H.G, ' ', H.Y.A, ' ', H.Y.B, ' ', H.Y.C, ' ', H.H);
      Q := M12(5); WriteLn(Q.C);
    end.
    ''',
    '2.50 1.50 3.25 3.00 6.00 111 222' + LE +
    '15.00 10.00 5.00' + LE +
    '16.50 5.00' + LE +
    '307.25' + LE +
    '3428.00' + LE +
    '10 12 77 70000 7 9 88' + LE +
    '5' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_Single_RoundTrip;
var Output: string; RCode: Int;
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
      TInner = record X, Y: Int; end;
      TOuter = record A: TInner; B: Int; end;
    function MakeIt(X, Y, B: Int): TOuter;
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
var Output: string; RCode: Int;
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
    type T2S = record A, B: Float32; end;
    function MakeIt(A, B: Float32): T2S;
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
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
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
      TR = record A, B: Int; end;
      TFoo = class
        function MakeR: TR;
        procedure Run;
      end;
    function Sum(const R: TR): Int;
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
    type TR = record A, B: Int; end;
    function MakeR: TR;
    begin
      Result.A := 1;
      Result.B := 2
    end;
    procedure Check(const Msg: string; Expected, Actual: Int);
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
    type TR = record X: Float64; M: array of UInt32; end;
    function Make(V: Float64): TR;
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
    type TR = record X, Y: Float64; M: array of UInt32; end;
    function Make2(A, B: Float64): TR;
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
      TR = record X: Float64; M: array of UInt32; end;
      TMaker = class
        function Make(V: Float64): TR;
      end;
    function TMaker.Make(V: Float64): TR;
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
        V: Int;
        function Plus(const B: TR): TR;
        function Val: Int;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Val: Int; begin Result := Self.V end;
    var A, B: TR; N: Int;
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
        V: Int;
        function Plus(const B: TR): TR;
        function Scale(F: Int): TR;
        function Val: Int;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Scale(F: Int): TR; begin Result.V := Self.V * F end;
    function TR.Val: Int; begin Result := Self.V end;
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
        V: Int;
        function Plus(const B: TR): TR;
        function Sum6(A1,A2,A3,A4,A5,A6: Int): Int;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Sum6(A1,A2,A3,A4,A5,A6: Int): Int;
    begin Result := Self.V + A1+A2+A3+A4+A5+A6 end;
    var A, B: TR; N: Int;
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
        V: Int;
        function Plus(const B: TR): TR;
        function Val: Int;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Val: Int; begin Result := Self.V end;
    var A, B: TR; N: Int;
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
        V: Int;
        M: array of UInt32;
        function Plus(const B: TR): TR;
        function Val: Int;
      end;
    function TR.Plus(const B: TR): TR;
    begin SetLength(Result.M, 1); Result.M[0] := 0; Result.V := Self.V + B.V end;
    function TR.Val: Int; begin Result := Self.V end;
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
        A, B: Int;
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
        A, B: Int;
      end;
      TBig = record
        A, B, C, D, E: Int;
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
        A, B: Int;
      end;
    function Pick(const N: Int; const S: TR): TR;
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
        A, B: Int;
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
      IThing = interface function Val: Int; end;
      TThing = class(TObject, IThing) function Val: Int; end;
      TR = record
        V: Int;
        M: array of UInt32;
        function Scale(N: Int; const S: IThing): TR;
      end;
    function TThing.Val: Int; begin Result := 7 end;
    function TR.Scale(N: Int; const S: IThing): TR;
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
      IThing = interface function Val: Int; end;
      TThing = class(TObject, IThing) function Val: Int; end;
      TR = record
        V: Int;
        function Scale(N: Int; const S: IThing): TR;
      end;
    function TThing.Val: Int; begin Result := 7 end;
    function TR.Scale(N: Int; const S: IThing): TR;
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
      IThing = interface function Tag: Int; end;
      TThing = class(TObject, IThing)
        FT: Int;
        function Tag: Int;
      end;
      TR = record
        V: Int;
        function Combine(N: Int; const S: IThing): Int;
      end;
    function TThing.Tag: Int; begin Result := Self.FT end;
    function TR.Combine(N: Int; const S: IThing): Int;
    begin Result := Self.V + N * 100 + S.Tag() end;
    var A: TR; T: TThing; N: Int;
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
      IThing = interface function V: Int; end;
      TT = class(TObject, IThing) function V: Int; end;
      TR = record A: Int; M: array of UInt32; end;
    function TT.V: Int; begin Result := 7 end;
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
      IThing = interface function V: Int; end;
      TT = class(TObject, IThing) function V: Int; end;
      TR = record A: Int; M: array of UInt32; end;
    function TT.V: Int; begin Result := 7 end;
    function Mk(N: Int; const S: IThing): TR;
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
      TTok = record Kind: Int; Value: string; Line: Int; end;
      TBase = class
        function Next(N: Int): TTok; virtual;
      end;
      TDeriv = class(TBase)
        function Next(N: Int): TTok; override;
      end;
    function TBase.Next(N: Int): TTok;
    begin
      Result.Kind := N;
      Result.Value := 'hello-world';
      Result.Line := 99
    end;
    function TDeriv.Next(N: Int): TTok;
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
      TTok = record Kind: Int; Value: string; end;
      TBase = class
        function Make(N: Int): TTok; virtual;
      end;
      TDeriv = class(TBase)
        function Make(N: Int): TTok; override;
      end;
    function TBase.Make(N: Int): TTok;
    begin
      Result.Kind := N + 100;
      Result.Value := 'base'
    end;
    function TDeriv.Make(N: Int): TTok;
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
    type TR = record A: Int; S: string; B: Int; end;
    function Raw(N: Int): TR;
    begin
      Result.A := N;
      Result.S := 'hi';
      Result.B := 20
    end;
    function Make(N: Int): TR;
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
        Kind: Int;
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
      TPoint = record X, Y: Int; end;
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
      TRec = record N: Int; S: string; end;
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

procedure TE2ERecordReturnTests.TestRun_DiscardedRecordReturn_AllReceiverForms;
const
  Src = '''
    program P;
    type
      TToken = record Kind: Int; Value: string; end;
      TBig = record A, B, C: Int64; end;
      TPt = record
        X, Y: Int;
        function Moved(D: Int): TPt;
        function Tok(): TToken;
      end;
      TLexer = class
        FName: string;
        function Next(): TToken;
        function Big(): TBig;
      end;
      TOwner = class
        FLex: TLexer;
        procedure Run();
      end;
    function TPt.Moved(D: Int): TPt;
    begin
      Result.X := X + D;
      Result.Y := Y + D
    end;
    function TPt.Tok(): TToken;
    begin
      Result.Kind := X;
      Result.Value := 'tok' + IntToStr(Y)
    end;
    function TLexer.Next(): TToken;
    begin
      Result.Kind := 42;
      Result.Value := 'hello' + FName
    end;
    function TLexer.Big(): TBig;
    begin
      Result.A := 1;
      Result.B := 2;
      Result.C := 3
    end;
    procedure TOwner.Run();
    begin
      FLex.Next();
      FLex.Big()
    end;
    procedure ByVar(var L: TLexer; var R: TPt);
    begin
      L.Next();
      R.Moved(3);
      R.Tok()
    end;
    procedure Outer();
    var L: TLexer;
      procedure Inner();
      begin
        L.Next()
      end;
    begin
      L := TLexer.Create();
      L.FName := 'in';
      Inner();
      L.Free()
    end;
    var L: TLexer; O: TOwner; R: TPt;
    begin
      L := TLexer.Create();
      L.FName := 'x';
      L.Next();
      L.Big();
      O := TOwner.Create();
      O.FLex := L;
      O.Run();
      R.X := 1;
      R.Y := 2;
      R.Moved(1);
      R.Tok();
      ByVar(L, R);
      Outer();
      WriteLn('ok ', R.X, ' ', L.FName);
      O.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'ok 1 x' + LE, 0);
  AssertLeakFreeOnAll(Src, '');
end;

procedure TE2ERecordReturnTests.TestRun_RecordCall_OwnedTransientReceiver;
const
  Src = '''
    program P;
    type
      TToken = record Kind: Int; Value: string; end;
      TPt = record X, Y: Int; end;
      TLexer = class
        FName: string;
        function Next(): TToken;
        function Pos(): TPt;
        destructor Destroy(); override;
      end;
    var Frees: Int;
    function TLexer.Next(): TToken;
    begin
      Result.Kind := 42; Result.Value := 'hello-' + FName
    end;
    function TLexer.Pos(): TPt;
    begin
      Result.X := 3; Result.Y := 4
    end;
    destructor TLexer.Destroy();
    begin
      Frees := Frees + 1;
      inherited Destroy()
    end;
    function MakeL(const N: string): TLexer;
    begin
      Result := TLexer.Create();
      Result.FName := N
    end;
    var T: TToken; Q: TPt;
    begin
      T := MakeL('a').Next();
      WriteLn(T.Value, ' ', T.Kind);
      Q := MakeL('b').Pos();
      WriteLn(Q.X + Q.Y);
      MakeL('c').Next();
      WriteLn(MakeL('d').Next().Value);
      WriteLn('frees ', Frees)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'hello-a 42' + LE + '7' + LE + 'hello-d' + LE + 'frees 4' + LE, 0);
  AssertLeakFreeOnAll(Src, '');
end;

procedure TE2ERecordReturnTests.TestRun_InheritedRecordReturn_AllForms;
const
  Src = '''
    program P;
    type
      TTok = record Kind: Int; Value: string; Line: Int; end;
      TPt = record X, Y: Int; end;
      TBase = class
        function Next(N: Int): TTok; virtual;
        function Pt(N: Int): TPt; virtual;
        function S(N: Int): Float32; virtual;
        function Tag(N: Int): string; virtual;
      end;
      TDeriv = class(TBase)
        function Next(N: Int): TTok; override;
        function Pt(N: Int): TPt; override;
        function S(N: Int): Float32; override;
        procedure Show();
      end;
    function TBase.Next(N: Int): TTok;
    begin
      Result.Kind := N;
      Result.Value := 'hello-' + IntToStr(N);
      Result.Line := 99
    end;
    function TBase.Pt(N: Int): TPt;
    begin
      Result.X := N;
      Result.Y := N * 2
    end;
    function TBase.S(N: Int): Float32;
    begin
      Result := N + 0.5
    end;
    function TBase.Tag(N: Int): string;
    begin
      Result := 'tag' + IntToStr(N)
    end;
    function TDeriv.Next(N: Int): TTok;
    begin
      Result.Value := 'old';
      inherited Next(N);
      Result.Line := Result.Line + 1
    end;
    function TDeriv.Pt(N: Int): TPt;
    begin
      Result := inherited Pt(N + 1)
    end;
    function TDeriv.S(N: Int): Float32;
    begin
      inherited S(N)
    end;
    procedure TDeriv.Show();
    var T: TTok;
    begin
      T := inherited Next(3);
      WriteLn(T.Value, ' ', (inherited Pt(4)).Y, ' ', inherited S(1) * 2:0:1);
      inherited Next(6);
      inherited Tag(9)
    end;
    var D: TDeriv; T: TTok; Q: TPt;
    begin
      D := TDeriv.Create();
      T := D.Next(7);
      WriteLn(T.Kind, ' ', T.Value, ' ', T.Line);
      Q := D.Pt(1);
      WriteLn(Q.X, ' ', Q.Y);
      WriteLn(D.S(2):0:1);
      D.Show();
      D.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '7 hello-7 100' + LE + '2 4' + LE + '2.5' + LE + 'hello-3 8 3.0' + LE, 0);
  AssertLeakFreeOnAll(Src, '');
end;

procedure TE2ERecordReturnTests.TestRun_DiscardedRecordReturn_ImplicitSelf;
const
  Src = '''
    program P;
    type
      TToken = record Kind: Int; Value: string; end;
      TPt = record X, Y: Int; end;
      TBig = record A, B, C: Int64; end;
      IGreet = interface
        function Hi(): Int;
      end;
      TG = class(TObject, IGreet)
      public
        function Hi(): Int;
      end;
      TLexer = class
        FName: string;
        FCount: Int;
        function Next(): TToken;
        function Pos(): TPt;
        function Big(N: Int): TBig; virtual;
        function Greeter(): IGreet;
        procedure Again();
      end;
    function TG.Hi(): Int;
    begin
      Result := 1
    end;
    function TLexer.Next(): TToken;
    begin
      FCount := FCount + 1;
      Result.Kind := 42;
      Result.Value := 'hello' + FName
    end;
    function TLexer.Pos(): TPt;
    begin
      FCount := FCount + 1;
      Result.X := 1;
      Result.Y := 2
    end;
    function TLexer.Big(N: Int): TBig;
    begin
      FCount := FCount + N;
      Result.A := 1;
      Result.B := 2;
      Result.C := 3
    end;
    function TLexer.Greeter(): IGreet;
    begin
      FCount := FCount + 1;
      Result := TG.Create()
    end;
    procedure TLexer.Again();
    begin
      Next();
      Pos();
      Big(10);
      Greeter()
    end;
    var L: TLexer;
    begin
      L := TLexer.Create();
      L.FName := 'abc';
      L.Again();
      WriteLn(L.FName, ' ', L.FCount);
      L.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { FName and FCount intact: no callee wrote its result over the object }
  AssertRunsOnAll(Src, 'abc 13' + LE, 0);
  AssertLeakFreeOnAll(Src, '');
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
        N: Int;
      end;
      TEnum = class
        FI: Int;
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
        A: Float64;
        B: Float64;
        C: Float64;
        D: Float64;
      end;
    function Make(S: Float32; D: Float64): TBig;
    begin
      Result.A := S;
      Result.B := D;
      Result.C := 0;
      Result.D := 0
    end;
    var
      R: TBig;
      Sng: Float32;
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
        A: Float64;
        B: Float64;
        C: Float64;
        D: Float64;
      end;
      TMaker = class
      public
        function Make(S: Float32; D: Float64): TBig;
      end;
    function TMaker.Make(S: Float32; D: Float64): TBig;
    begin
      Result.A := S;
      Result.B := D;
      Result.C := 0;
      Result.D := 0
    end;
    var
      M: TMaker;
      R: TBig;
      Sng: Float32;
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
        Kind: Int;
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
      TQ = record Index: Int; Other: Int; end;
      TBig = record A, B, C, D, E: Int; end;
      TMan = record Name: string; N: Int; end;
      TBox = class
        FQ: TQ;
        FBig: TBig;
        FMan: TMan;
        function Get(A: Int): TQ;
        function GetBig(A: Int): TBig;
        function GetMan(A: Int): TMan;
        property Items[A: Int]: TQ read Get;
        property Bigs[A: Int]: TBig read GetBig;
        property Mans[A: Int]: TMan read GetMan;
      end;
    function TBox.Get(A: Int): TQ; begin Result := FQ end;
    function TBox.GetBig(A: Int): TBig; begin Result := FBig end;
    function TBox.GetMan(A: Int): TMan; begin Result := FMan end;
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
      TQ = record Index: Int; Other: Int; end;
      TBig = record A, B, C, D, E: Int; end;
      TMan = record Name: string; N: Int; end;
      TBoxQ = class
        FQ: TQ;
        function Get(A: Int): TQ;
        property Items[A: Int]: TQ read Get; default;
      end;
      TBoxBig = class
        FBig: TBig;
        function GetBig(A: Int): TBig;
        property Items[A: Int]: TBig read GetBig; default;
      end;
      TBoxMan = class
        FMan: TMan;
        function GetMan(A: Int): TMan;
        property Items[A: Int]: TMan read GetMan; default;
      end;
    function TBoxQ.Get(A: Int): TQ; begin Result := FQ end;
    function TBoxBig.GetBig(A: Int): TBig; begin Result := FBig end;
    function TBoxMan.GetMan(A: Int): TMan; begin Result := FMan end;
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
        Kind: Int;
        Value: string;      { managed field forces the sret class }
        Line: Int;
        Col: Int;
      end;
      THolder = class
        Toks: TList<TTok>;
        constructor Create;
        procedure Add(AKind: Int; const AValue: string; ALine, ACol: Int);
        function Bare: Int;
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
    procedure THolder.Add(AKind: Int; const AValue: string; ALine, ACol: Int);
    var T: TTok;
    begin
      T.Kind := AKind; T.Value := AValue; T.Line := ALine; T.Col := ACol;
      Self.Toks.Add(T);
    end;
    { bare FField[I] — the IMPLICIT-Self arm }
    function THolder.Bare: Int;
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
  RCode:  Int;
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
    AssertTrue(BackendName(B) + ': compile+link+run',
      CompileAndRunWithUnitOn(B, 'tokholder', UnitSrc, DrvSrc, Output, RCode));
    AssertEquals(BackendName(B) + ': exit code', 0, RCode);
    AssertEquals(BackendName(B) + ': output',
      '42' + LE + 'world' + LE + '141' + LE + '3' + LE +
      '77' + LE + 'deep' + LE + '42' + LE + 'hello' + LE, Output);
  end;
end;

procedure TE2ERecordReturnTests.TestRun_RecordReturn_RemainingShapes;
const
  {
    Record returns in the shapes the round-trip tests above do not cover: a
    one-field enum record, a pointer, a class reference (managed, so returned
    through the hidden result pointer), an odd-sized three-Byte record (the
    next global must not be overwritten), Single + Double, Integer + Double
    (split across register classes on x86-64, not on arm64), and a nested
    all-POD record. }
  Src = '''
    program P;
    type
      TColor = (Red, Green, Blue);
      TE = record C: TColor; end;
      TPt = record P: Pointer; end;
      TBox = class V: Int; end;
      TCR = record B: TBox; end;
      TOdd = record A, B, C: Byte; end;
      TSD = record S: Float32; D: Float64; end;
      TID = record I: Int; D: Float64; end;
      TIn = record X, Y: Int16; end;
      TNest = record Inner: TIn; Z: Int; end;
    var G: Int;
    function MakeE: TE; begin Result.C := Blue end;
    function MakePt: TPt; begin Result.P := @G end;
    function MakeCR: TCR; begin Result.B := TBox.Create(); Result.B.V := 42 end;
    function MakeOdd: TOdd; begin Result.A := 1; Result.B := 2; Result.C := 250 end;
    function MakeSD: TSD; begin Result.S := 1.25; Result.D := -2.5 end;
    function MakeID: TID; begin Result.I := -7; Result.D := 3.75 end;
    function MakeNest: TNest;
    begin
      Result.Inner.X := -3; Result.Inner.Y := 4; Result.Z := 100000
    end;
    var
      E: TE; Pt: TPt; CR: TCR; O: TOdd; SD: TSD; ID: TID; N: TNest;
      Guard: Int64;
    begin
      Guard := 99;
      E := MakeE();
      Pt := MakePt();
      CR := MakeCR();
      O := MakeOdd();
      SD := MakeSD();
      ID := MakeID();
      N := MakeNest();
      WriteLn(Ord(E.C), ' ', Pt.P = @G, ' ', CR.B.V);
      WriteLn(O.A, ' ', O.B, ' ', O.C, ' ', Guard);
      WriteLn(SD.S:0:2, ' ', SD.D:0:1, ' ', ID.I, ' ', ID.D:0:2);
      WriteLn(N.Inner.X, ' ', N.Inner.Y, ' ', N.Z)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 True 42' + LE +
    '1 2 250 99' + LE +
    '1.25 -2.5 -7 3.75' + LE +
    '-3 4 100000' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ImplicitSelfRecordCall_AsArgument;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TPt = record X, Y: Int; end;
      TBig = record A, B, C: Int64; end;
      TC = class
        function Mk(N: Int): TPt;
        function MkV(N: Int): TPt; virtual;
        function MkB(N: Int): TBig;
        function Sum(const P: TPt): Int;
        function SumV(P: TPt): Int;
        function SumB(const P: TBig): Int64;
        procedure Run();
      end;
      TD = class(TC)
        function MkV(N: Int): TPt; override;
      end;
    function TC.Mk(N: Int): TPt; begin Result.X := N; Result.Y := N * 2; end;
    function TC.MkV(N: Int): TPt; begin Result.X := N; Result.Y := 0; end;
    function TC.MkB(N: Int): TBig; begin Result.A := N; Result.B := N; Result.C := N; end;
    function TC.Sum(const P: TPt): Int; begin Result := P.X + P.Y; end;
    function TC.SumV(P: TPt): Int; begin Result := P.X + P.Y; end;
    function TC.SumB(const P: TBig): Int64; begin Result := P.A + P.B + P.C; end;
    function TD.MkV(N: Int): TPt; begin Result.X := N; Result.Y := 100; end;
    procedure TC.Run();
    begin
      WriteLn(Sum(Mk(3)), ' ', SumV(Mk(3)), ' ', SumB(MkB(3)), ' ',
        Self.Sum(Mk(3)), ' ', Sum(MkV(1)));
    end;
    var O: TC;
    begin
      O := TC.Create();
      O.Run();
      O := TD.Create();
      O.Run();
    end.
    ''', '9 9 9 9 1' + LE + '9 9 9 9 101' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SretCall_OpenArrayAndOverflowArgs;
const
  Src = '''
    program s4;
    type TBig = record A, B, C: Int64; end;
    function OA(const V: array of Int; K: Int): TBig;
    var I: Int;
    begin Result.A := 0; for I := 0 to High(V) do Result.A := Result.A + V[I]; Result.B := High(V); Result.C := K end;
    function OA6(A, B, C, D: Int; const V: array of Int; K: Int): TBig;
    begin Result.A := A + D; Result.B := High(V) * 10 + V[0]; Result.C := K end;
    function Fl7(A, B, C, D, E, F: Int; X: Float64; G: Int): TBig;
    begin Result.A := A + F; Result.B := Trunc(X * 10); Result.C := G end;
    var R: TBig;
    begin
      R := OA([1, 2, 3], 7); WriteLn(R.A, ' ', R.B, ' ', R.C);
      R := OA6(1, 2, 3, 4, [5, 6], 7); WriteLn(R.A, ' ', R.B, ' ', R.C);
      R := Fl7(1, 2, 3, 4, 5, 6, 2.5, 8); WriteLn(R.A, ' ', R.B, ' ', R.C);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '6 2 7' + #10 + '5 15 7' + #10 + '7 25 8' + #10, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SretNested_CapturesWithFloatsAndOverflow;
const
  Src = '''
    program s3;
    uses SysUtils;
    type
      TBig = record A, B, C: Int64; end;
      TSmall = record X, Y: Int; end;
    procedure Outer;
    var A, B, C, D, E, F, G, H, I, J: Int; R: Float64;
      function Mix(X: Float64; const V: array of Int; K, L: Int; Y: Float64): Float64;
      begin Result := A + J + X * 10 + Y * 100 + V[High(V)] * 1000 + K + L * 10000 + R end;
      function MkBig(K: Int): TBig;
      begin Result.A := A + K; Result.B := J * K; Result.C := H end;
      function MkSmall(K: Int; Z: Float64): TSmall;
      begin Result.X := A + K; Result.Y := J + Trunc(Z) end;
      function BigMany(K1, K2, K3, K4, K5, K6, K7: Int): TBig;
      begin Result.A := K1 + K7; Result.B := A + J; Result.C := K4 end;
      procedure Bump(var Z: Int); begin Z := Z + I + J end;
    var Bg: TBig; Sm: TSmall; Q: Int;
    begin
      A := 1; B := 2; C := 3; D := 4; E := 5; F := 6; G := 7; H := 8; I := 9; J := 10; R := 0.5;
      WriteLn(Trunc(Mix(2.0, [3, 4], 5, 6, 7.0) * 10));
      Bg := MkBig(3); WriteLn(Bg.A, ' ', Bg.B, ' ', Bg.C);
      Sm := MkSmall(4, 2.5); WriteLn(Sm.X, ' ', Sm.Y);
      Bg := BigMany(1, 2, 3, 4, 5, 6, 7); WriteLn(Bg.A, ' ', Bg.B, ' ', Bg.C);
      Q := 1; Bump(Q); WriteLn(Q + B + C + D + E + F + G);
    end;
    begin
      Outer()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '647365' + #10 + '4 30 8' + #10 + '5 12' + #10 +
    '8 11 4' + #10 + '47' + #10, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SretNested_SixCaptures_ResultPointerOnStack;
const
  Src = '''
    program s5;
    type TBig = record A, B, C: Int64; end;
    procedure Outer;
    var A, B, C, D, E, F, G: Int;
      function SixCap(K: Int; X: Float64; const V: array of Int): TBig;
      begin Result.A := A + B + C + D + E + F + G + K; Result.B := Trunc(X * 10); Result.C := V[High(V)] end;
    var R: TBig;
    begin
      A := 1; B := 2; C := 3; D := 4; E := 5; F := 6; G := 7;
      R := SixCap(100, 1.5, [8, 9]); WriteLn(R.A, ' ', R.B, ' ', R.C)
    end;
    begin Outer() end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '128 15 9' + #10, 0);
end;

procedure TE2ERecordReturnTests.TestRun_SretMethod_OverflowVirtualIntfAndRecordReceiver;
const
  Src = '''
    program s8;
    type
      TBig = record A, B, C: Int64; end;
      IN1 = interface function Get: Int; end;
      TN = class(TObject, IN1) V: Int; function Get: Int; end;
      TBase = class
        function Calc(A, B, C, D, E: Int; var Z: Int): TBig; virtual;
        function Plain(A, B, C, D, E, F, G: Int; const S: array of Int): Int;
        function WithIntf(A, B, C, D: Int; const I: IN1; E: Int): TBig;
      end;
      TDer = class(TBase)
        function Calc(A, B, C, D, E: Int; var Z: Int): TBig; override;
      end;
      TRec = record
        K: Int;
        function Mk(A, B, C, D, E: Int; X: Float64): TBig;
      end;
    function TN.Get: Int; begin Result := V end;
    function TBase.Calc(A, B, C, D, E: Int; var Z: Int): TBig;
    begin Result.A := 1; Result.B := A + E; Z := 11 end;
    function TDer.Calc(A, B, C, D, E: Int; var Z: Int): TBig;
    begin Result.A := 2; Result.B := A + E; Result.C := D; Z := 22 end;
    function TBase.Plain(A, B, C, D, E, F, G: Int; const S: array of Int): Int;
    begin Result := A + G + S[High(S)] * 100 end;
    function TBase.WithIntf(A, B, C, D: Int; const I: IN1; E: Int): TBig;
    begin Result.A := A + D; Result.B := I.Get(); Result.C := E end;
    function TRec.Mk(A, B, C, D, E: Int; X: Float64): TBig;
    begin Result.A := K + E; Result.B := Trunc(X * 10); Result.C := A end;
    var O: TBase; R: TBig; Z: Int; N: TN; Rc: TRec;
    begin
      O := TDer.Create();
      R := O.Calc(1, 2, 3, 4, 5, Z); WriteLn(R.A, ' ', R.B, ' ', R.C, ' ', Z);
      WriteLn(O.Plain(1, 2, 3, 4, 5, 6, 7, [8, 9]));
      N := TN.Create(); N.V := 42;
      R := O.WithIntf(1, 2, 3, 4, N, 9); WriteLn(R.A, ' ', R.B, ' ', R.C);
      Rc.K := 1000;
      R := Rc.Mk(1, 2, 3, 4, 5, 1.5); WriteLn(R.A, ' ', R.B, ' ', R.C);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2 6 4 22' + #10 + '908' + #10 + '5 42 9' + #10 +
    '1005 15 1' + #10, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ClosureRecordReturn_AllPositions;
const
  Src = '''
    program P;
    type
      TSmall = record A, B: Int; end;
      TBig = record A, B, C: Int64; end;
      TFnS = reference to function(X: Int): TSmall;
      TFnB = reference to function(X: Int): TBig;
      TPlain = function(X: Int): TSmall;
    function PlainMk(X: Int): TSmall;
    begin Result.A := X; Result.B := X + 1 end;
    procedure ShowS(const R: TSmall); begin WriteLn(R.A + R.B) end;
    var GS: TFnS; GB: TFnB; PP: TPlain; S: TSmall; B: TBig; K: Int;
    begin
      K := 10;
      GS := function(X: Int): TSmall
        begin Result.A := X + K; Result.B := X * 2 end;
      GB := function(X: Int): TBig
        begin Result.A := X; Result.B := K; Result.C := X + K end;
      PP := @PlainMk;
      S := GS(1); WriteLn(S.A, ' ', S.B);
      WriteLn(GS(2).B);
      ShowS(GS(3));
      GS(4);
      B := GB(5); WriteLn(B.A, ' ', B.B, ' ', B.C);
      WriteLn(GB(6).C);
      S := PP(7); WriteLn(S.A, ' ', S.B);
      WriteLn(PP(8).B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '11 2' + #10 + '4' + #10 + '19' + #10 + '5 10 15' + #10 +
    '16' + #10 + '7 8' + #10 + '9' + #10, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ExprCalleeAggregateResults;
const
  Src = '''
    program g;
    type
      TPt = record X, Y: Int; end;
      TBig = record A, B, C: Int64; S: string; end;
      IThing = interface
        function Name(): string;
      end;
      TThing = class(TObject, IThing)
        FN: string;
        constructor Create(const N: string);
        function Name(): string;
      end;
      TBFn = reference to function(A: Int): TBig;
      TPFn = reference to function(A: Int): TPt;
      TIFn = reference to function(): IThing;
      TKFn = reference to function(A: Int): Int;
      TCFn = reference to function(): TKFn;
    constructor TThing.Create(const N: string); begin FN := N; end;
    function TThing.Name(): string; begin Result := FN; end;
    function GetB(): TBFn; begin Result := function(A: Int): TBig begin Result.A := A; Result.S := 'B' + IntToStr(A); end; end;
    function GetP(): TPFn; begin Result := function(A: Int): TPt begin Result.X := A; Result.Y := A * 2; end; end;
    function GetI(): TIFn; begin Result := function(): IThing begin Result := TThing.Create('I'); end; end;
    function GetC(): TCFn; begin Result := function(): TKFn begin Result := function(A: Int): Int begin Result := A + 1000; end; end; end;
    procedure ShowB(const B: TBig); begin WriteLn('showB ', B.S); end;
    procedure ShowBv(B: TBig); begin WriteLn('showBv ', B.S); end;
    procedure ShowP(P: TPt); begin WriteLn('showP ', P.Y); end;
    procedure ShowI(const I: IThing); begin WriteLn('showI ', I.Name()); end;
    procedure ShowK(K: TKFn); begin WriteLn('showK ', K(1)); end;
    var B: TBig; P: TPt; I: IThing; K: TKFn;
    begin
      WriteLn('1 ', GetB()(5).S);
      B := GetB()(6); WriteLn('2 ', B.S);
      ShowB(GetB()(7));
      ShowBv(GetB()(8));
      GetB()(9);
      WriteLn('3 ', GetP()(5).Y);
      P := GetP()(6); WriteLn('4 ', P.X);
      ShowP(GetP()(7));
      GetP()(9);
      WriteLn('5 ', GetI()().Name());
      I := GetI()(); WriteLn('6 ', I.Name());
      ShowI(GetI()());
      GetI()();
      WriteLn('7 ', GetC()()(5));
      K := GetC()(); WriteLn('8 ', K(6));
      ShowK(GetC()());
      GetC()();
      if GetI()() <> nil then WriteLn('9 nonnil');
      if GetP()(3).X = 3 then WriteLn('10 eq');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1 B5' + LineEnding +
    '2 B6' + LineEnding +
    'showB B7' + LineEnding +
    'showBv B8' + LineEnding +
    '3 10' + LineEnding +
    '4 6' + LineEnding +
    'showP 14' + LineEnding +
    '5 I' + LineEnding +
    '6 I' + LineEnding +
    'showI I' + LineEnding +
    '7 1005' + LineEnding +
    '8 1006' + LineEnding +
    'showK 1001' + LineEnding +
    '9 nonnil' + LineEnding +
    '10 eq' + LineEnding, 0);
end;

procedure TE2ERecordReturnTests.TestRun_AggregateCallsInScalarContexts;
const
  Src = '''
    program h;
    type
      TPt = record X, Y: Int; end;
      TBig = record A, B, C: Int64; S: string; end;
      TKFn = reference to function(A: Int): Int;
      TMFn = function(A: Int): Int of object;
      IThing = interface
        function GetFn(): TKFn;
        function GetB(): TBig;
      end;
      TC = class(TObject, IThing)
        function GetFn(): TKFn;
        function GetM(): TMFn;
        function GetB(): TBig;
        function GetP(): TPt;
        function Dbl(A: Int): Int;
        procedure Run();
      end;
      TD = class(TC)
        function GetFn(): TKFn;
        function GetB(): TBig;
        procedure Run2();
      end;
    function MkFn(): TKFn; begin Result := function(A: Int): Int begin Result := A + 1; end; end;
    function MkP(A: Int): TPt; begin Result.X := A; Result.Y := A * 10; end;
    function MkC(): TC; begin Result := TC.Create(); end;
    function TC.GetFn(): TKFn; begin Result := function(A: Int): Int begin Result := A * 2; end; end;
    function TC.GetM(): TMFn; begin Result := @Self.Dbl; end;
    function TC.GetB(): TBig; begin Result.S := 'cb'; Result.A := 1; end;
    function TC.GetP(): TPt; begin Result.X := 4; Result.Y := 9; end;
    function TC.Dbl(A: Int): Int; begin Result := A * 4; end;
    procedure TC.Run();
    var Fv: TKFn;
    begin
      if Assigned(GetFn()) then WriteLn('r1 assigned');
      WriteLn('r2 ', GetP().Y);
      WriteLn('r3 ', GetM()(5));
      Fv := GetFn();
      WriteLn('r4 ', Fv(2));
      GetFn();
      GetM();
      GetB();
    end;
    function TD.GetFn(): TKFn; begin inherited GetFn(); end;
    function TD.GetB(): TBig; begin inherited GetB(); Result.B := 5; end;
    procedure TD.Run2();
    begin
      inherited GetFn();
      inherited GetB();
      WriteLn('d1 ', GetFn()(7), ' ', GetB().S, GetB().B);
    end;
    var C: TC; I: IThing; Fv: TKFn; Mv: TMFn; D: TD;
    begin
      C := TC.Create();
      C.Run();
      if Assigned(MkFn()) then WriteLn('1 assigned');
      if Assigned(C.GetFn()) then WriteLn('2 assigned');
      WriteLn('3 ', MkP(3).Y);
      WriteLn('4 ', C.GetP().X);
      WriteLn('5 ', C.GetM()(3));
      Mv := C.GetM(); WriteLn('6 ', Mv(1));
      I := C;
      WriteLn('7 ', I.GetFn()(4));
      Fv := I.GetFn(); WriteLn('8 ', Fv(5));
      I.GetFn();
      I.GetB();
      MkC().GetFn();
      MkC().GetB();
      MkC().GetM();
      if Assigned(I.GetFn()) then WriteLn('9 assigned');
      WriteLn('10 ', TMethod(C.GetM()).Code <> nil);
      D := TD.Create();
      D.Run2();
      WriteLn('11 ', I.GetB().S);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'r1 assigned' + LineEnding +
    'r2 9' + LineEnding +
    'r3 20' + LineEnding +
    'r4 4' + LineEnding +
    '1 assigned' + LineEnding +
    '2 assigned' + LineEnding +
    '3 30' + LineEnding +
    '4 4' + LineEnding +
    '5 12' + LineEnding +
    '6 4' + LineEnding +
    '7 8' + LineEnding +
    '8 10' + LineEnding +
    '9 assigned' + LineEnding +
    '10 True' + LineEnding +
    'd1 14 cb5' + LineEnding +
    '11 cb' + LineEnding, 0);
end;

procedure TE2ERecordReturnTests.TestRun_DiscardedResultsEveryKind;
const
  Src = '''
    program j;
    type
      TBig = record A, B, C: Int64; S: string; end;
      TPt = record X, Y: Int; end;
      TKFn = reference to function(A: Int): Int;
      TArr = array of Int;
      IThing = interface
        function Name(): string;
      end;
      TC = class(TObject, IThing)
        Inner: TC;
        function Name(): string;
        function GetS(): string;
        function GetC(): TC;
        function GetA(): TArr;
        function GetI(): IThing;
        function GetFn(): TKFn;
        function GetB(): TBig;
        function GetP(): TPt;
        static function SGetS(): string;
        static function SGetI(): IThing;
        static function SGetFn(): TKFn;
        static function SGetB(): TBig;
        procedure Run();
      end;
    function TC.Name(): string; begin Result := 'n'; end;
    function TC.GetS(): string; begin Result := 'abc' + IntToStr(1); end;
    function TC.GetC(): TC; begin Result := TC.Create(); end;
    function TC.GetA(): TArr; begin SetLength(Result, 3); end;
    function TC.GetI(): IThing; begin Result := TC.Create(); end;
    function TC.GetFn(): TKFn; begin Result := function(A: Int): Int begin Result := A; end; end;
    function TC.GetB(): TBig; begin Result.S := 'x' + IntToStr(2); end;
    function TC.GetP(): TPt; begin Result.X := 1; end;
    static function TC.SGetS(): string; begin Result := 'q' + IntToStr(3); end;
    static function TC.SGetI(): IThing; begin Result := TC.Create(); end;
    static function TC.SGetFn(): TKFn; begin Result := function(A: Int): Int begin Result := A; end; end;
    static function TC.SGetB(): TBig; begin Result.S := 'y' + IntToStr(4); end;
    procedure TC.Run();
    begin
      GetS(); GetC(); GetA(); GetI(); GetFn(); GetB(); GetP();
      Inner.GetS(); Inner.GetC(); Inner.GetA(); Inner.GetI(); Inner.GetFn(); Inner.GetB(); Inner.GetP();
    end;
    function MkC(): TC; begin Result := TC.Create(); end;
    function MkFn(): TKFn; begin Result := function(A: Int): Int begin Result := A; end; end;
    function MkI(): IThing; begin Result := TC.Create(); end;
    function MkB(): TBig; begin Result.S := 'z' + IntToStr(5); end;
    function MkS(): string; begin Result := 'z' + IntToStr(6); end;
    type TSA = array[0..1] of string;
    function MkSA(): TSA; begin Result[0] := 'w' + IntToStr(7); end;
    var C: TC;
    begin
      C := TC.Create();
      C.Inner := TC.Create();
      C.Run();
      C.GetS(); C.GetC(); C.GetA(); C.GetI(); C.GetFn(); C.GetB(); C.GetP();
      MkC().GetS(); MkC().GetC(); MkC().GetA(); MkC().GetI(); MkC().GetFn(); MkC().GetB(); MkC().GetP();
      C.Inner.GetS(); C.Inner.GetC(); C.Inner.GetA(); C.Inner.GetI(); C.Inner.GetFn(); C.Inner.GetB(); C.Inner.GetP();
      TC.SGetS(); TC.SGetI(); TC.SGetFn(); TC.SGetB();
      MkFn(); MkI(); MkB(); MkS(); MkSA();
      WriteLn('done');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'done' + LineEnding, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordCallAsAddressBase_EveryCallForm;
const
  Src = '''
    program P;
    type
      TArr = array[0..3] of Int;
      TRec = record
        A: TArr; S: string; D: array of Int;
        function Clone: TRec;
      end;
      TRecFn = reference to function(N: Int): TRec;
      IMk = interface
        function Mk(N: Int): TRec;
      end;
      TBase = class(IMk)
      public
        function Mk(N: Int): TRec; virtual;
      end;
      TObj = class(TBase)
      private
        FR: TRec;
        function GetR: TRec;
        function GetRI(I: Int): TRec;
        static function GetSR: TRec;
      public
        function Mk(N: Int): TRec; override;
        procedure Run;
        static function SMk(N: Int): TRec;
        property R: TRec read GetR;
        property RI[I: Int]: TRec read GetRI;
        static property SR: TRec read GetSR;
      end;
    function F(N: Int): TRec;
    var I: Int;
    begin
      for I := 0 to 3 do Result.A[I] := N + I;
      Result.S := 's' + IntToStr(N);
      SetLength(Result.D, 3); Result.D[1] := N * 10;
    end;
    function TRec.Clone: TRec; begin Result := Self; Result.A[0] := Result.A[0] + 1000; end;
    function TBase.Mk(N: Int): TRec; begin Result := F(N); end;
    function TObj.Mk(N: Int): TRec; begin Result := F(N + 1); end;
    function TObj.GetR: TRec; begin Result := F(40); end;
    function TObj.GetRI(I: Int): TRec; begin Result := F(I); end;
    static function TObj.GetSR: TRec; begin Result := F(50); end;
    static function TObj.SMk(N: Int): TRec; begin Result := F(N); end;
    function MkFn: TRecFn; begin Result := function(N: Int): TRec begin Result := F(N * 2); end; end;
    procedure ShowOpen(const A: array of Int); var X: Int; begin for X in A do Write(X, ' '); WriteLn(); end;
    procedure TObj.Run; begin WriteLn(Mk(4).A[1], ' ', Mk(4).D[1], ' ', inherited Mk(4).A[2], ' ', Self.Mk(4).A[3]); end;
    var O: TObj; I: IMk; Fn: TRecFn; R: TRec; Pi: ^Int; X: Int;
    begin
      O := TObj.Create(); I := O; Fn := MkFn();
      WriteLn(F(1).A[1], ' ', F(1).S[1], ' ', F(1).D[1]);
      WriteLn(O.Mk(1).A[1], ' ', O.Mk(1).S[1], ' ', O.Mk(1).D[1]);
      WriteLn(TObj.SMk(2).A[1], ' ', TObj.SMk(2).D[1]);
      WriteLn(I.Mk(3).A[1], ' ', I.Mk(3).S[1], ' ', I.Mk(3).D[1]);
      O.Run();
      WriteLn(Fn(5).A[1], ' ', MkFn()(5).A[2], ' ', Fn(5).D[1]);
      WriteLn(O.R.A[1], ' ', O.R.D[1], ' ', O.RI[7].A[2], ' ', TObj.SR.A[3]);
      R := F(8); WriteLn(R.Clone().A[0], ' ', F(8).Clone().A[1], ' ', R.Clone().D[1]);
      O.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 49 10' + LineEnding +
    '3 50 20' + LineEnding +
    '3 20' + LineEnding +
    '5 52 40' + LineEnding +
    '6 50 6 8' + LineEnding +
    '11 12 100' + LineEnding +
    '41 400 9 53' + LineEnding +
    '1008 9 80' + LineEnding, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordCallAsAddressBase_EveryConsumer;
const
  Src = '''
    program P;
    type
      TArr = array[0..3] of Int;
      TRec = record
        A: TArr; S: string; D: array of Int;
        function Clone: TRec;
      end;
      TRecFn = reference to function(N: Int): TRec;
      IMk = interface
        function Mk(N: Int): TRec;
      end;
      TBase = class(IMk)
      public
        function Mk(N: Int): TRec; virtual;
      end;
      TObj = class(TBase)
      private
        FR: TRec;
        function GetR: TRec;
        function GetRI(I: Int): TRec;
        static function GetSR: TRec;
      public
        function Mk(N: Int): TRec; override;
        procedure Run;
        static function SMk(N: Int): TRec;
        property R: TRec read GetR;
        property RI[I: Int]: TRec read GetRI;
        static property SR: TRec read GetSR;
      end;
    function F(N: Int): TRec;
    var I: Int;
    begin
      for I := 0 to 3 do Result.A[I] := N + I;
      Result.S := 's' + IntToStr(N);
      SetLength(Result.D, 3); Result.D[1] := N * 10;
    end;
    function TRec.Clone: TRec; begin Result := Self; Result.A[0] := Result.A[0] + 1000; end;
    function TBase.Mk(N: Int): TRec; begin Result := F(N); end;
    function TObj.Mk(N: Int): TRec; begin Result := F(N + 1); end;
    function TObj.GetR: TRec; begin Result := F(40); end;
    function TObj.GetRI(I: Int): TRec; begin Result := F(I); end;
    static function TObj.GetSR: TRec; begin Result := F(50); end;
    static function TObj.SMk(N: Int): TRec; begin Result := F(N); end;
    function MkFn: TRecFn; begin Result := function(N: Int): TRec begin Result := F(N * 2); end; end;
    procedure ShowOpen(const A: array of Int); var X: Int; begin for X in A do Write(X, ' '); WriteLn(); end;
    procedure TObj.Run; begin end;
    var O: TObj; I: IMk; Fn: TRecFn; R: TRec; Pi: ^Int; X: Int;
    begin
      O := TObj.Create(); I := O; Fn := MkFn();
      ShowOpen(O.Mk(1).A); ShowOpen(I.Mk(1).A); ShowOpen(TObj.SMk(1).A); ShowOpen(Fn(1).A); ShowOpen(O.R.A); ShowOpen(F(1).D);
      Pi := @O.Mk(3).A[1]; WriteLn(Pi^); Pi := @I.Mk(3).A[2]; WriteLn(Pi^); Pi := @Fn(3).A[3]; WriteLn(Pi^);
      WriteLn(Length(O.Mk(4).A), ' ', Length(I.Mk(4).D), ' ', High(Fn(4).A), ' ', Length(O.Mk(4).S));
      X := O.Mk(5).A[1] + I.Mk(5).A[1] + TObj.SMk(5).A[1] + Fn(5).A[1] + F(5).A[1] + O.R.A[1]; WriteLn(X);
      X := F(1).A[1] + F(2).A[1] + F(3).A[1]; WriteLn(X);
      WriteLn(F(1).A[1] + F(2).A[1] + F(3).A[1] + F(4).A[1]);
      O.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 3 4 5 ' + LineEnding +
    '2 3 4 5 ' + LineEnding +
    '1 2 3 4 ' + LineEnding +
    '2 3 4 5 ' + LineEnding +
    '40 41 42 43 ' + LineEnding +
    '0 10 0 ' + LineEnding +
    '5' + LineEnding +
    '6' + LineEnding +
    '9' + LineEnding +
    '4 3 3 2' + LineEnding +
    '78' + LineEnding +
    '9' + LineEnding +
    '14' + LineEnding, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordCallArgs_ManagedAndRegisterShaped;
const
  Src = '''
    program TS;
    type
      TOS = (osLinux, osMac);
      TCPU = (cpuX, cpuA);
      TTarget = record OS: TOS; CPU: TCPU; end;
      TSpec = record
        Name: string; EnvVar: string; Cands: array of string; Prefix: string; HostTool: Boolean;
      end;
      TT = class
        function MakeSpec: TSpec;
        procedure Run;
      end;
    function Host: TTarget; begin Result.OS := osLinux; Result.CPU := cpuA; end;
    function Resolve(const ASpec: TSpec; const ATarget: TTarget): string;
    begin
      Result := ASpec.Name + ':' + IntToStr(Length(ASpec.Cands)) + ':' + IntToStr(Ord(ATarget.CPU));
    end;
    function TT.MakeSpec: TSpec;
    begin
      Result.Name := 'linker'; SetLength(Result.Cands, 2); Result.Cands[0] := 'cc'; Result.Cands[1] := 'clang';
    end;
    procedure TT.Run;
    var R: string;
    begin
      R := Resolve(Self.MakeSpec(), Host());
      WriteLn(R);
      R := Resolve(MakeSpec(), Host());
      WriteLn(R);
    end;
    var T: TT;
    begin
      T := TT.Create(); T.Run(); T.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'linker:2:1' + LineEnding +
    'linker:2:1' + LineEnding, 0);
end;

procedure TE2ERecordReturnTests.TestRun_AddrOfResult_InRecordFunction;
const
  Src = '''
    program AR;
    type
      TBig = record X: Int; A: array[0..3] of Int; end;
      TSmall = record X, Y: Int; end;
      TObj = class function MkBig: TBig; function MkSmall: TSmall; end;
    function MkBig: TBig; var P: ^TBig; begin P := @Result; P^.X := 4; P^.A[2] := 5; end;
    function MkSmall: TSmall; var P: ^TSmall; begin P := @Result; P^.Y := 6; end;
    function TObj.MkBig: TBig; var P: ^TBig; begin P := @Result; P^.X := 7; end;
    function TObj.MkSmall: TSmall; var P: ^TSmall; begin P := @Result; P^.Y := 8; end;
    var O: TObj;
    begin
      WriteLn(MkBig().X, ' ', MkBig().A[2], ' ', MkSmall().Y);
      O := TObj.Create();
      WriteLn(O.MkBig().X, ' ', O.MkSmall().Y);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '4 5 6' + LineEnding +
    '7 8' + LineEnding, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordFieldFromCall_ThatReadsTheField;
const
  Src = '''
    program P;
    type
      TBig = record A, B, C: Int; end;
      TH = record
        V: TBig;
        function Scaled(K: Int): TBig;
      end;
      TW = record Tag: Int; Payload: TH; end;
      TPay = record N: Int; S: string; end;
      TWrap = record Payload: TPay; end;
      TBox = class
        FWrap: TWrap;
        function GetP: TPay;
        property PayloadProp: TPay read GetP;
      end;
      TIn = record
        S: string;
        C: Int;
        function Grow(const X: string): TIn;
      end;
      TZ = record Inner: TIn; end;
    function TH.Scaled(K: Int): TBig;
    begin
      Result.A := V.A * K; Result.B := V.B * K; Result.C := V.C * K
    end;
    function TBox.GetP: TPay; begin Result := FWrap.Payload end;
    function TIn.Grow(const X: string): TIn;
    begin
      Result.S := S + X; Result.C := C + 1
    end;
    function Bump(const R: TPay): TPay;
    begin
      Result.N := R.N + 1; Result.S := R.S + '+'
    end;
    procedure Pr(var Z: TZ);
    begin
      Z.Inner := Z.Inner.Grow('!');
      Z.Inner := Z.Inner.Grow('?')
    end;
    var
      W: TW;
      B: TBox;
      Z: TZ;
    begin
      W.Payload.V.A := 3; W.Payload.V.B := 5; W.Payload.V.C := 7;
      W.Payload.V := W.Payload.Scaled(2);
      WriteLn(W.Payload.V.A, ' ', W.Payload.V.B, ' ', W.Payload.V.C);
      B := TBox.Create();
      B.FWrap.Payload.N := 42; B.FWrap.Payload.S := 'x' + IntToStr(1);
      B.FWrap.Payload := B.PayloadProp;
      WriteLn(B.FWrap.Payload.N, ' ', B.FWrap.Payload.S);
      B.FWrap.Payload := Bump(B.FWrap.Payload);
      WriteLn(B.FWrap.Payload.N, ' ', B.FWrap.Payload.S);
      Z.Inner.S := 'ab'; Z.Inner.C := 5;
      Pr(Z);
      WriteLn(Z.Inner.S, ' ', Z.Inner.C)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src,
    '6 10 14' + LineEnding + '42 x1' + LineEnding + '43 x1+' + LineEnding +
    'ab!? 7' + LineEnding);
end;

initialization
  RegisterTest(TE2ERecordReturnTests);

end.
