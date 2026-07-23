{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.records;

{ E2E tests for record types: field read/write, pass by value, pass by var,
  string fields under ARC, and nested records. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ERecordsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Record_FieldReadWrite;
    procedure TestRun_Record_PassByValue;
    procedure TestRun_Record_PassByVar;
    procedure TestRun_Record_AssignToVarParam;
    procedure TestRun_Record_StringField_ARC;
    procedure TestRun_Record_VarToVarCopy_StringField_ARC;
    procedure TestRun_Record_NestedRecord;
    procedure TestRun_Record_FourByteFields_PackedAndRoundTrip;
    procedure TestRun_Record_ByteThenInteger_RoundTrip;
    procedure TestRun_Record_NestedFieldAssign_MethodCall;
    procedure TestRun_Record_StmtMethodCall_Local;
    procedure TestRun_Record_StmtMethodCall_ImplicitSelf;
    procedure TestRun_Record_StmtMethodCall_Result;
    procedure TestRun_Record_AddrOfImplicitSelf;
    procedure TestRun_Record_PointerDerefFieldAccess;
    procedure TestRun_Record_DynArrayField_ReturnByValue_NoLeak;
    { self-cross-compile leg 11: SetLength on a dyn-array field of an explicit
      record (SetLength(Result.Cands, N)) — works through the field address;
      correct output + leak-free (the RTL moves ownership on resize). }
    procedure TestRun_Record_SetLengthOnDynArrayField;
    { self-cross-compile leg 12: assignment to an element of a dyn-array field,
      both a STRING element (ARC store) and an INTEGER element (plain store);
      correct values + leak-free. }
    procedure TestRun_Record_DynArrayFieldElementAssign;
    procedure TestRun_Class_RecordField_NestedClass_FullCleanup;
    procedure TestRun_Record_InterfaceField_AssignCallAndCopy;
    procedure TestRun_Record_ByValParam_StringField_HeapARC;
    procedure TestRun_Record_ByValArg_InlineCallResult_NestedManaged_NoLeak;
    procedure TestRun_DynArrayRecordElem_FieldAssignAndRead;
    procedure TestRun_DynArrayRecordElem_CopyNoAlias;
    procedure TestRun_StaticArrayRecordElem_FieldAssignAndRead;
    procedure TestRun_DynArrayClassElem_MethodCallStmt;
    procedure TestRun_RecordField_DynArrayElemWrite;
    procedure TestRun_ClassField_DynArrayElemWrite_AllReceiverShapes;
    procedure TestRun_NestedChain_DynArrayElemWrite;
    procedure TestRun_SubscriptChain_FieldElemWrite;
    procedure TestRun_RecordField_StaticArrayElemWrite;
    procedure TestRun_RecordField_DynArrayOfString_ElemWrite_ARC;
    procedure TestRun_RecordCallResult_IntoArrayElement;
    { Added by the hardening sweep. }
    procedure TestRun_RecordMethodMutatesSelf;
    procedure TestRun_RecordReturnFieldInline;
    procedure TestRun_RecordWithStaticArrayField_DeepCopy;
    procedure TestRun_NestedRecordMethod;
    { Regression: copying a record whose layout has a sub-word field (Boolean /
      Byte / SmallInt) immediately before a managed field.  EmitRecordCopy used
      loadw/storew unconditionally, so the 4-byte store over a 1-byte Boolean
      clobbered the low bytes of the following pointer field — a later
      _StringRelease / _DynArrayRelease then crashed on QBE.  Native was always
      width-correct.  This is the shape of TDecimal (Boolean flags before a
      string-bearing carrier), which blocked Numerics.Money on QBE. }
    procedure TestRun_RecordCopy_BooleanBeforeManagedField;
    { Regression (issue #169): for..in over an array of records must copy the
      whole record element into the loop variable by value.  The element
      assignment did a single scalar load — truncating the record to its first
      8 bytes and skipping managed-field ARC — so every field past the first
      was stale.  On BOTH backends. }
    procedure TestRun_ForInArrayOfRecords_CopiesWholeElement;
    { Instance method chained onto a record-RETURNING call
      (TVal.Make(1).GetX()): QBE typed the receiver call `l` and passed half
      the record VALUE as Self for register-class returns (SIGSEGV). }
    procedure TestRun_ChainedMethodOnRecordReturn;
    { leg 22: store a whole RECORD value into an element of a dyn-array (and
      static-array) FIELD of a class instance — ClassObj.ArrayField[I] := R.
      Clean record (plain memcpy) and managed record (retain/release, leak-free). }
    procedure TestRun_RecordIntoClassDynArrayField;
    procedure TestRun_RecordIntoClassStaticArrayField;
    procedure TestRun_RecordIntoClassDynArrayField_Managed_LeakFree;
    { leg 22 review regression: a record-RETURNING call that reallocates the
      SAME dyn-array field must be materialised before the element address is
      computed, else the store lands in the freed old block. }
    procedure TestRun_RecordIntoClassDynArrayField_ReallocatingCall;
    { leg 23: store a whole record into a var/out record parameter — the store
      must reach the CALLER's record (the dereferenced var-param address).  The
      TryGetValue out-param shape. }
    procedure TestRun_RecordStoreToVarParam;
    { leg 24: nested record-field access — scalar read/write through a
      record-typed field (Rec.RecField.Scalar), via a plain var and an sret
      Result, with a non-zero intermediate offset; plus whole-record-field
      read/store as regression guards. }
    procedure TestRun_NestedRecordFieldAccess;
    { leg 25: store a whole MANAGED record lvalue into a record-typed field of
      a record (Rec.Field := managedRecordVar) — retain source / release dest,
      leak-free, including an overwrite that must release the dest's old value. }
    procedure TestRun_ManagedRecordLvalueFieldStore_LeakFree;
    { leg 26 (BUG fix): a MANAGED record parameter — var/out and by-value —
      field read/write on arm64.  The pass-2 prologue memcpy must skip a
      var-param record (its address is the caller's, no __pptr copy). }
    procedure TestRun_ManagedRecordParam_VarAndByValue_LeakFree;
    procedure TestRun_ByValueRecordParam_FieldReadWrite;
    procedure TestRun_RecordParamOverflowToStack;
    { BUG-20260720-managed-record-self-assign: a managed-record self-assign
      (R := R, element/field self-assign) must keep the fields, not zero them. }
    procedure TestRun_ManagedRecordSelfAssign;
    { Record-property getter assigned into a record FIELD — the native
      TFieldAssignment record path had arms for method/function calls but
      none for a property-getter RHS, so it fell through and mishandled the
      sret buffer (SIGSEGV; QBE was correct)
      (BUG-20260721-native-recprop-into-recfield). }
    procedure TestRun_RecordPropGetterIntoRecordField;
    { Var-param record dest aliasing the method receiver: 'Z := Z.Grow(..)'
      inside 'procedure P(var Z: TRec)' — QBE zeroed the caller's record
      before the sret call read it as the receiver, losing the prior state
      (BUG-20260721-qbe-varparam-receiver-self-assign). }
    procedure TestRun_VarParamRecordReceiverSelfAssign;
    { Record-returning FREE-FUNCTION call assigned into a record field whose
      base record is a VAR PARAM — the native FuncCall arm lacked the
      standalone IsVarParam case (present in the method-call and prop-getter
      arms), so it leaq'd the 8-byte slot instead of loading the caller
      record's address and sprayed the sret result over the callee's stack. }
    procedure TestRun_RecordFuncCallIntoVarParamRecordField;
    { Managed-record (string field) property getter into a record field:
      release-then-sret-write must transfer the getter result's +1 and
      release the old field contents on reassignment. }
    procedure TestRun_ManagedRecordPropGetterIntoRecordField;
    { Passing a FIELD-array ELEMENT (R.Arr[I]) by var/out: the l-value
      address computation dropped the subscript and yielded the field base
      (element 0), or for a dyn-array field the data-POINTER slot, so the
      callee mutated the wrong element / corrupted memory on both backends
      (BUG-20260723-vararg-field-array-elem-subscript-drop).  Covers static
      and dyn field arrays, int / string / record element types, a non-zero
      LowBound field array, and an implicit-Self field-array element. }
    procedure TestRun_FieldArrayElem_ByVarParam;
  end;

implementation

procedure TE2ERecordsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-records');
end;

const
  LE = #10;

  SrcRecordFieldRW = '''
    program Prg;
    type TPoint = record X, Y: Integer; end;
    var P1: TPoint;
    begin
      P1.X := 3;
      P1.Y := 7;
      WriteLn(P1.X + P1.Y)
    end.
    ''';

  SrcRecordPassByValue = '''
    program Prg;
    type TPoint = record X, Y: Integer; end;
    procedure Print(Pt: TPoint);
    begin
      WriteLn(Pt.X);
      WriteLn(Pt.Y)
    end;
    var P1: TPoint;
    begin
      P1.X := 5;
      P1.Y := 9;
      Print(P1)
    end.
    ''';

  SrcRecordPassByVar = '''
    program Prg;
    type TPoint = record X, Y: Integer; end;
    procedure Scale(var Pt: TPoint);
    begin
      Pt.X := Pt.X * 2;
      Pt.Y := Pt.Y * 2
    end;
    var P1: TPoint;
    begin
      P1.X := 3;
      P1.Y := 4;
      Scale(P1);
      WriteLn(P1.X);
      WriteLn(P1.Y)
    end.
    ''';

  { Regression: whole-record assignment to a var/out record parameter.
    Previously the IsVarParam path had no tyRecord case, so `Dst := L` (or
    `Dst := Func`) fell through to a single-word store and wrote garbage back
    to the caller.  Covers both a local-record RHS (var) and a record-returning
    function RHS (out). }
  SrcRecordAssignToVarParam = '''
    program Prg;
    type TPoint = record X, Y: Integer; end;
    function Make(AX, AY: Integer): TPoint;
    begin
      Result.X := AX;
      Result.Y := AY
    end;
    procedure FillFromLocal(var Dst: TPoint);
    var L: TPoint;
    begin
      L.X := 11;
      L.Y := 22;
      Dst := L
    end;
    procedure FillFromCall(out Dst: TPoint);
    begin
      Dst := Make(33, 44)
    end;
    var A, B: TPoint;
    begin
      FillFromLocal(A);
      FillFromCall(B);
      WriteLn(A.X);
      WriteLn(A.Y);
      WriteLn(B.X);
      WriteLn(B.Y)
    end.
    ''';

  SrcRecordStringField = '''
    program Prg;
    type TName = record First, Last: string; end;
    var N: TName;
    begin
      N.First := 'Ada';
      N.Last  := 'Lovelace';
      WriteLn(N.First + ' ' + N.Last)
    end.
    ''';

  SrcRecordNested = '''
    program Prg;
    type
      TInner = record V: Integer; end;
      TOuter = record A, B: TInner; end;
    var O: TOuter;
    begin
      O.A.V := 10;
      O.B.V := 20;
      WriteLn(O.A.V + O.B.V)
    end.
    ''';

  SrcRecordFourBytes = '''
    program Prg;
    type
      TFourBytes = record
        A: Byte;
        B: Byte;
        C: Byte;
        D: Byte;
      end;
    var R: TFourBytes;
    begin
      R.A := 1;
      R.B := 2;
      R.C := 3;
      R.D := 4;
      WriteLn(SizeOf(TFourBytes));
      WriteLn(R.A);
      WriteLn(R.B);
      WriteLn(R.C);
      WriteLn(R.D)
    end.
    ''';

  SrcRecordByteThenInteger = '''
    program Prg;
    type
      TMixed = record
        Tag: Byte;
        Value: Integer;
      end;
    var R: TMixed;
    begin
      R.Tag := 7;
      R.Value := 12345;
      WriteLn(R.Tag);
      WriteLn(R.Value);
      WriteLn(SizeOf(TMixed))
    end.
    ''';

  SrcRecordStmtMethodCallLocal = '''
    program Prg;
    type
      TCounter = record
        Value: Integer;
        procedure Inc;
        function GetValue: Integer;
      end;
    procedure TCounter.Inc;
    begin
      Value := Value + 1
    end;
    function TCounter.GetValue: Integer;
    begin
      Result := Value
    end;
    var
      C: TCounter;
    begin
      C.Value := 0;
      C.Inc();
      C.Inc();
      C.Inc();
      WriteLn(C.GetValue())
    end.
    ''';

  SrcRecordStmtMethodCallImplicitSelf = '''
    program Prg;
    type
      TCounter = record
        Value: Integer;
        procedure Inc;
      end;
      TApp = class
        FC: TCounter;
        procedure Run;
      end;
    procedure TCounter.Inc;
    begin
      Value := Value + 1
    end;
    procedure TApp.Run;
    begin
      FC.Inc();
      FC.Inc();
      FC.Inc();
      WriteLn(FC.Value)
    end;
    var
      A: TApp;
    begin
      A := TApp.Create();
      A.Run()
    end.
    ''';

  SrcRecordStmtMethodCallResult = '''
    program Prg;
    type
      TPoint = record
        X, Y: Integer;
        procedure SetXY(AX, AY: Integer);
      end;
    procedure TPoint.SetXY(AX, AY: Integer);
    begin
      X := AX;
      Y := AY
    end;
    function MakePoint(AX, AY: Integer): TPoint;
    begin
      Result.SetXY(AX, AY)
    end;
    var
      P: TPoint;
    begin
      P := MakePoint(5, 8);
      WriteLn(P.X);
      WriteLn(P.Y)
    end.
    ''';

  SrcRecordAddrOfImplicitSelf = '''
    program Prg;
    type
      TPoint = record
        X, Y: Integer;
      end;
      TApp = class
        Pt: TPoint;
        procedure Run;
      end;
    procedure TApp.Run;
    var PP: ^TPoint;
    begin
      Pt.X := 10;
      Pt.Y := 20;
      PP := @Pt;
      WriteLn(PP^.X);
      WriteLn(PP^.Y)
    end;
    var
      A: TApp;
    begin
      A := TApp.Create();
      A.Run()
    end.
    ''';

  SrcRecordPointerDerefFieldAccess = '''
    program Prg;
    type
      TPoint = record X, Y: Integer; end;
    var
      Pt: TPoint;
      PP: ^TPoint;
    begin
      Pt.X := 42;
      Pt.Y := 99;
      PP := @Pt;
      WriteLn(PP^.X);
      WriteLn(PP^.Y)
    end.
    ''';

  { Regression: a record whose field is a dynamic array, returned by value
    in a loop.  Before the dyn-array ARC fix, every iteration leaked the
    array buffer because EmitRecordCopy/EmitRecordReleaseFields did not
    refcount tyDynArray fields.  After the fix, the per-iter delta is one
    AddRef + one Release on the buffer header — net zero — and the final
    assertion of the buffer contents proves the data was not freed under
    the function's feet. }
  { Regression: a class whose field is a record whose field is another class
    whose field is another record whose field is a leaf class.  Each Create
    increments a global AliveCount; each Destroy decrements it.  After the
    outermost instance is released, AliveCount must be 0 — proving that
    _FieldCleanup for a class with a record field recurses through that
    record's class sub-fields all the way down.

    Before the fix, _FieldCleanup_<T> skipped record-typed fields entirely,
    so the chain leaked TMid and TLeaf instances every iteration. }
  SrcClassRecordFieldNestedCleanup = '''
    program Prg;
    type
      TLeaf = class
        Tag: Integer;
        constructor Create();
        destructor Destroy(); override;
      end;
      TMidRec = record
        Leaf:  TLeaf;
        Extra: Integer;
      end;
      TMid = class
        Inner: TMidRec;
        constructor Create();
        destructor Destroy(); override;
      end;
      TOuterRec = record
        Mid:  TMid;
        Note: Integer;
      end;
      TOuter = class
        Wrap: TOuterRec;
        constructor Create();
        destructor Destroy(); override;
      end;
    var
      AliveCount: Integer;
    constructor TLeaf.Create();
    begin
      AliveCount := AliveCount + 1;
      Self.Tag := 1
    end;
    destructor TLeaf.Destroy();
    begin
      AliveCount := AliveCount - 1
    end;
    constructor TMid.Create();
    begin
      AliveCount := AliveCount + 1;
      Self.Inner.Leaf  := TLeaf.Create();
      Self.Inner.Extra := 7
    end;
    destructor TMid.Destroy();
    begin
      AliveCount := AliveCount - 1
    end;
    constructor TOuter.Create();
    begin
      AliveCount := AliveCount + 1;
      Self.Wrap.Mid  := TMid.Create();
      Self.Wrap.Note := 99
    end;
    destructor TOuter.Destroy();
    begin
      AliveCount := AliveCount - 1
    end;
    procedure RunOnce();
    var
      O: TOuter;
    begin
      O := TOuter.Create();
      if O.Wrap.Mid.Inner.Leaf.Tag <> 1 then
        WriteLn('chain broken')
    end;
    var
      i: Integer;
    begin
      AliveCount := 0;
      for i := 0 to 99 do
        RunOnce();
      WriteLn(AliveCount)
    end.
    ''';

  { Regression: a record with a managed (string) field passed by value
    to a callee that REASSIGNS the field used to free the caller's
    heap-allocated string and then return.  The caller's subsequent
    read of the field was a use-after-free that often crashed on exit.
    A literal-only test wouldn't trip the bug because string literals
    have a sentinel refcount of -1 (Release is a no-op); we force a
    real heap refcount via 'heap-' + 'allocated'. }
  SrcRecordByValParam_StringField_HeapARC = '''
    program Prg;
    type TR = record S: string; end;
    procedure Mutate(R: TR);
    begin R.S := 'callee-replacement' end;
    var W: TR;
    begin
      W.S := 'heap-' + 'allocated';
      WriteLn('before: ', W.S);
      Mutate(W);
      WriteLn('after:  ', W.S)
    end.
    ''';

  { Caller-side cleanup of an inline call result used as a by-value
    record arg: Consume(MakeOuter()) where TOuter has a string field
    AND a nested TInner whose own field is a string.  Before the fix
    the temporary's two heap strings leaked once per Driver call; over
    many iterations the process either OOMs or the allocator's free
    list ages noticeably.  Successful run prints both fields once and
    exits 0; we drive the pattern in a tight loop so a leak would
    show up under stress. }
  SrcRecordByValArg_InlineNestedManaged = '''
    program Prg;
    type
      TInner = record N: string; end;
      TOuter = record S: string; Inner: TInner; end;
    function MakeOuter: TOuter;
    begin
      Result.S := 'outer-' + 'heap';
      Result.Inner.N := 'inner-' + 'heap'
    end;
    procedure Consume(R: TOuter);
    begin
      WriteLn(R.S, '|', R.Inner.N)
    end;
    procedure Driver;
    begin
      Consume(MakeOuter())
    end;
    var i: Integer;
    begin
      for i := 1 to 1000 do Driver()
    end.
    ''';

  SrcRecordDynArrayReturnByValueNoLeak = '''
    program Prg;
    type
      TBuf = record
        Arr: array of Integer;
      end;
    function MakeBuf: TBuf;
    var
      tmp: TBuf;
      a:   array of Integer;
    begin
      SetLength(a, 8);
      a[0] := 1;
      a[7] := 70;
      tmp.Arr := a;
      Result := tmp
    end;
    var
      i:   Integer;
      r:   TBuf;
    begin
      for i := 0 to 4999 do
        r := MakeBuf();
      WriteLn(r.Arr[0]);
      WriteLn(r.Arr[7])
    end.
    ''';

  { Interface-typed field inside a record: exercises (1) assigning a class into
    an interface record field (r.Foo := f → obj+itab fat-pointer store with
    ARC), (2) calling a method through an interface record field
    (r.Foo.GetVal() → dispatch via the field's contiguous fat pointer), (3)
    record copy carrying the interface field (b := a) and (4) the 16-byte field
    size so Tag sits at offset 16, not 8.  Before the fix the field was sized 8
    bytes and the method dispatch emitted an undefined %_var__obj temp that QBE
    rejected. }
  SrcRecordInterfaceFieldAssignCallCopy = '''
    program Prg;
    type
      IFoo = interface
        function GetVal: Integer;
      end;
      TFoo = class(TObject, IFoo)
        V: Integer;
        function GetVal: Integer;
      end;
      TRec = record
        Foo: IFoo;
        Tag: Integer;
      end;
    function TFoo.GetVal: Integer;
    begin
      Result := Self.V
    end;
    function MakeRec(n: Integer): TRec;
    var
      r: TRec;
      f: TFoo;
    begin
      f := TFoo.Create();
      f.V := n;
      r.Foo := f;
      r.Tag := n * 10;
      Result := r
    end;
    var
      a: TRec;
      b: TRec;
    begin
      a := MakeRec(5);
      b := a;
      WriteLn(b.Foo.GetVal());
      WriteLn(a.Tag)
    end.
    ''';

  SrcRecordNestedFieldAssignMethodCall = '''
    program Prg;
    type
      TDate = record
        Year: Integer;
        Month: Integer;
        Day: Integer;
        function ToString: string;
      end;
      TDateTime = record
        Date: TDate;
        Hour: Integer;
      end;
    function TDate.ToString: string;
    begin
      Result := IntToStr(Self.Year) + '-' + IntToStr(Self.Month) + '-' + IntToStr(Self.Day)
    end;
    var
      DT: TDateTime;
      D: TDate;
    begin
      DT.Date.Year := 2026;
      DT.Date.Month := 6;
      DT.Date.Day := 5;
      DT.Hour := 14;
      D := DT.Date;
      WriteLn(D.ToString());
      WriteLn(DT.Date.ToString())
    end.
    ''';

procedure TE2ERecordsTests.TestRun_Record_FieldReadWrite;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordFieldRW, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3 + 7 = 10', '10' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_PassByValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordPassByValue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('5 then 9', '5' + LE + '9' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_PassByVar;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordPassByVar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('6 then 8', '6' + LE + '8' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_AssignToVarParam;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordAssignToVarParam, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('11 22 33 44',
    '11' + LE + '22' + LE + '33' + LE + '44' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_StringField_ARC;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordStringField, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Ada Lovelace', 'Ada Lovelace' + LE, Output);
end;

const
  { Copying a record with a managed (string) field var-to-var (B := A) must
    field-copy with ARC: AddRef the source's string so the copy owns its own
    reference, and Release the destination's prior string.  A bare memcpy left
    both records sharing one buffer at refcount 1 — mutating/churning the source
    then dropped it to 0 and freed it, so the copy held a dangling pointer
    (use-after-free → '_StringRelease double-free' abort).  This is the same
    record-copy path TList<TRec>.Get uses (Result := Src^), so it also fixes the
    generic-container crash. }
  SrcRecordVarToVarCopy = '''
    program Prg;
    type
      TPerson = record Name: string; Age: Integer; end;
    var
      A, B: TPerson;
      I: Integer;
    begin
      A.Name := 'Alice-' + IntToStr(42);
      A.Age := 30;
      B := A;
      A.Name := 'Bob';
      for I := 0 to 200 do
        A.Name := 'churn-' + IntToStr(I);
      WriteLn(B.Name, ' ', B.Age)
    end.
    ''';

procedure TE2ERecordsTests.TestRun_Record_VarToVarCopy_StringField_ARC;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcRecordVarToVarCopy, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('copy retained own string', 'Alice-42 30' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_NestedRecord;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordNested, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('10 + 20 = 30', '30' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_FourByteFields_PackedAndRoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordFourBytes, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('size 4, fields 1..4',
    '4' + LE + '1' + LE + '2' + LE + '3' + LE + '4' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_ByteThenInteger_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordByteThenInteger, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('tag=7, value=12345, size=8',
    '7' + LE + '12345' + LE + '8' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_NestedFieldAssign_MethodCall;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordNestedFieldAssignMethodCall, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested field assign + method call',
    '2026-6-5' + LE + '2026-6-5' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_Local;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordStmtMethodCallLocal, '3' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_ImplicitSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordStmtMethodCallImplicitSelf, '3' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_Result;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordStmtMethodCallResult, '5' + LE + '8' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_AddrOfImplicitSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordAddrOfImplicitSelf, '10' + LE + '20' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_PointerDerefFieldAccess;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordPointerDerefFieldAccess, '42' + LE + '99' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Class_RecordField_NestedClass_FullCleanup;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcClassRecordFieldNestedCleanup, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('all 3 layers fully released across 100 iterations',
    '0' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_DynArrayField_ReturnByValue_NoLeak;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordDynArrayReturnByValueNoLeak, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('first and last element survive 5000 iterations',
    '1' + LE + '70' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_InterfaceField_AssignCallAndCopy;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordInterfaceFieldAssignCallCopy, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('method dispatch through interface field + 16-byte field layout',
    '5' + LE + '50' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_ByValParam_StringField_HeapARC;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordByValParam_StringField_HeapARC, Output, RCode));
  AssertEquals('exit code 0 (no use-after-free crash)', 0, RCode);
  AssertEquals('caller string survives callee whole-string reassignment',
    'before: heap-allocated' + LE + 'after:  heap-allocated' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_ByValArg_InlineCallResult_NestedManaged_NoLeak;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordByValArg_InlineNestedManaged, Output, RCode));
  AssertEquals('exit code 0 over 1000 inline-temp iterations', 0, RCode);
  AssertTrue('Driver printed nested strings',
    Pos('outer-heap|inner-heap' + LE, Output) >= 0);
end;

const
  SrcDynRecElemFieldAssign = '''
    program Prg;
    type
      TInner = record N: Integer; end;
      TRec = record
        Name: String;
        Number: Integer;
        Inner: TInner;
      end;
    var
      r1, r2: TRec;
      a: array of TRec;
    begin
      SetLength(a, 2);
      r1.Name := 'First';  r1.Number := 1;
      r2.Name := 'Second'; r2.Number := 2;
      a[0] := r1;
      a[1] := r2;
      writeln(a[0].Name);
      a[0].Name := 'Patched';
      a[0].Number := 10;
      a[0].Inner.N := 7;
      writeln(a[0].Name);
      writeln(a[1].Name);
      writeln(a[0].Number);
      writeln(a[1].Number);
      writeln(a[0].Inner.N);
      writeln(r1.Name);
    end.
    ''';

  SrcDynRecElemCopyNoAlias = '''
    program Prg;
    type TRec = record Name: String; Number: Integer; end;
    var
      r: TRec;
      a: array of TRec;
    begin
      SetLength(a, 1);
      r.Name := 'one';
      r.Number := 1;
      a[0] := r;
      r.Name := 'two';
      r.Number := 2;
      writeln(a[0].Name);
      writeln(a[0].Number);
      r := a[0];
      a[0].Name := 'three';
      writeln(r.Name);
      writeln(r.Number);
      writeln(a[0].Name);
    end.
    ''';

  SrcStaticRecElemFieldAssign = '''
    program Prg;
    type TRec = record Name: String; Number: Integer; end;
    var
      r1, r2: TRec;
      sa: array[0..1] of TRec;
    begin
      r1.Name := 'First';  r1.Number := 1;
      r2.Name := 'Second'; r2.Number := 2;
      sa[0] := r1;
      sa[1] := r2;
      sa[0].Name := 'Patched';
      sa[0].Number := 10;
      writeln(sa[0].Name);
      writeln(sa[1].Name);
      writeln(sa[0].Number);
      writeln(sa[1].Number);
      writeln(r1.Name);
    end.
    ''';

  SrcDynClassElemMethodCall = '''
    program Prg;
    type
      TC = class
        V: Integer;
        procedure Bump;
      end;
    procedure TC.Bump;
    begin
      V := V + 1;
    end;
    var
      a: array of TC;
    begin
      SetLength(a, 1);
      a[0] := TC.Create();
      a[0].Bump;
      a[0].Bump();
      writeln(a[0].V);
    end.
    ''';

procedure TE2ERecordsTests.TestRun_DynArrayRecordElem_FieldAssignAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynRecElemFieldAssign,
    'First' + LE + 'Patched' + LE + 'Second' + LE + '10' + LE + '2' + LE +
    '7' + LE + 'First' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_DynArrayRecordElem_CopyNoAlias;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynRecElemCopyNoAlias,
    'one' + LE + '1' + LE + 'one' + LE + '1' + LE + 'three' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_StaticArrayRecordElem_FieldAssignAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticRecElemFieldAssign,
    'Patched' + LE + 'Second' + LE + '10' + LE + '2' + LE + 'First' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_DynArrayClassElem_MethodCallStmt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynClassElemMethodCall, '2' + LE, 0);
end;

const
  SrcRecFieldDynElemWrite = '''
    program Prg;
    type
      TIA = array of Integer;
      TR  = record A: TIA; end;
    var r: TR;
    begin
      SetLength(r.A, 3);
      r.A[0] := 10;
      r.A[1] := 20;
      r.A[2] := r.A[0] + r.A[1];
      writeln(r.A[0]);
      writeln(r.A[1]);
      writeln(r.A[2]);
    end.
    ''';

  SrcClassFieldDynElemWrite = '''
    program Prg;
    type
      TIA = array of Integer;
      TC = class
        A: TIA;
        procedure Fill;
      end;
    procedure TC.Fill;
    begin
      SetLength(A, 3);
      A[0] := 42;
      Self.A[1] := 43;
      A[2] := A[0] + Self.A[1];
    end;
    var c: TC;
    begin
      c := TC.Create();
      c.Fill();
      writeln(c.A[0]);
      writeln(c.A[1]);
      writeln(c.A[2]);
      c.A[0] := 7;
      writeln(c.A[0]);
    end.
    ''';

  SrcNestedChainDynElemWrite = '''
    program Prg;
    type
      TIA    = array of Integer;
      TInner = record A: TIA; end;
      TC     = class N: TInner; end;
    var c: TC;
    begin
      c := TC.Create();
      SetLength(c.N.A, 3);
      c.N.A[0] := 7;
      c.N.A[1] := 8;
      writeln(c.N.A[0]);
      writeln(c.N.A[1]);
    end.
    ''';

  SrcSubscriptChainFieldElemWrite = '''
    program Prg;
    type
      TIA = array of Integer;
      TR  = record A: TIA; end;
    var
      rs: array of TR;
    begin
      SetLength(rs, 2);
      SetLength(rs[1].A, 3);
      rs[1].A[2] := 99;
      writeln(rs[1].A[2]);
    end.
    ''';

  SrcRecFieldStaticElemWrite = '''
    program Prg;
    type
      TR = record S: array[0..2] of Integer; end;
    var r: TR;
    begin
      r.S[0] := 5;
      r.S[1] := 6;
      r.S[2] := r.S[0] + r.S[1];
      writeln(r.S[0]);
      writeln(r.S[1]);
      writeln(r.S[2]);
    end.
    ''';

  SrcRecFieldDynStrElemWrite = '''
    program Prg;
    type
      TSA = array of String;
      TR  = record N: TSA; end;
    var
      r: TR;
      s: String;
    begin
      SetLength(r.N, 2);
      s := 'wor';
      r.N[0] := 'hello';
      r.N[1] := s + 'ld';
      r.N[0] := 'bye';
      writeln(r.N[0]);
      writeln(r.N[1]);
    end.
    ''';

procedure TE2ERecordsTests.TestRun_RecordField_DynArrayElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecFieldDynElemWrite,
    '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_ClassField_DynArrayElemWrite_AllReceiverShapes;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassFieldDynElemWrite,
    '42' + LE + '43' + LE + '85' + LE + '7' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_NestedChain_DynArrayElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedChainDynElemWrite, '7' + LE + '8' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_SubscriptChain_FieldElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSubscriptChainFieldElemWrite, '99' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordField_StaticArrayElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecFieldStaticElemWrite,
    '5' + LE + '6' + LE + '11' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordField_DynArrayOfString_ElemWrite_ARC;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecFieldDynStrElemWrite,
    'bye' + LE + 'world' + LE, 0);
end;

const
  SrcRecordCallIntoElem = '''
    program Prg;
    type
      TTok = record
        Kind: Integer;
        Text: String;
      end;
      TLex = class
        FN: Integer;
        function Next(): TTok;
      end;
    function TLex.Next(): TTok;
    begin
      FN := FN + 1;
      Result.Kind := FN;
      Result.Text := 'tok' + IntToStr(FN);
    end;
    var
      L: TLex;
      A: array[0..2] of TTok;
      D: array of TTok;
      I: Integer;
    begin
      L := TLex.Create();
      for I := 0 to 2 do
        A[I] := L.Next();
      writeln(A[0].Kind, ' ', A[0].Text);
      writeln(A[2].Kind, ' ', A[2].Text);
      SetLength(D, 2);
      D[1] := L.Next();
      writeln(D[1].Kind, ' ', D[1].Text);
    end.
    ''';

procedure TE2ERecordsTests.TestRun_RecordCallResult_IntoArrayElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordCallIntoElem,
    '1 tok1' + LE + '3 tok3' + LE + '4 tok4' + LE, 0);
end;

const
  SrcRecMutatesSelf = '''
    program Prg;
    type TP = record X: Integer; procedure Inc; begin X := X + 1 end; end;
    var a: TP;
    begin a.X := 5; a.Inc(); a.Inc(); WriteLn(a.X) end.
    ''';

  SrcRecReturnFieldInline = '''
    program Prg;
    type TP = record X, Y: Integer; end;
    function Make(V: Integer): TP; begin Result.X := V; Result.Y := V * 2 end;
    begin WriteLn(Make(10).X + Make(10).Y) end.
    ''';

  SrcRecStaticArrDeepCopy = '''
    program Prg;
    type TP = record A: array[0..2] of Integer; end;
    var x, y: TP; i: Integer;
    begin
      for i := 0 to 2 do x.A[i] := i + 1;
      y := x;
      y.A[1] := 99;
      WriteLn(x.A[1], ',', y.A[1])
    end.
    ''';

  SrcNestedRecMethod = '''
    program Prg;
    type TInner = record V: Integer; function Get: Integer; begin Result := V end; end;
      TOuter = record I: TInner; end;
    var o: TOuter;
    begin o.I.V := 88; WriteLn(o.I.Get()) end.
    ''';

procedure TE2ERecordsTests.TestRun_RecordMethodMutatesSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecMutatesSelf, '7' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordReturnFieldInline;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecReturnFieldInline, '30' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordWithStaticArrayField_DeepCopy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecStaticArrDeepCopy, '2,99' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_NestedRecordMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedRecMethod, '88' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordCopy_BooleanBeforeManagedField;
const
  { TDec mirrors TDecimal's shape: a dynarray and Boolean flags packed before
    the outer record's managed (string) field.  Mk copies a LOCAL TDec into the
    sret Result's record field, then sets a string field — exactly the path that
    over-wrote the string pointer with a wide store. }
  Src = '''
    program P;
    type
      TDec = record FC: Int64; FM: array of UInt32; FS: Integer; FN: Boolean; FI: Boolean; end;
      TM   = record A: TDec; C: string; end;
    function MkDec: TDec;
    begin SetLength(Result.FM, 2); Result.FM[0] := 5; Result.FC := 99; Result.FI := True end;
    function Mk: TM;
    var L: TDec;
    begin
      L := MkDec();
      Result.A := L;
      Result.C := 'USD';
    end;
    var M: TM;
    begin
      M := Mk();
      WriteLn(M.C, ' ', M.A.FC, ' ', M.A.FM[0], ' ', M.A.FI)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'USD 99 5 True' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_ForInArrayOfRecords_CopiesWholeElement;
const
  { Initialise each array element through the index, then iterate with for..in
    and print all three fields of the copied loop variable.  A truncating scalar
    load would carry only the first 8 bytes (the string pointer) and leave
    Number / Initialized stale; the by-value record copy round-trips every
    field, ARC-correct for the managed string. }
  Src = '''
    program P;
    type
      TRec = record
        Name: string;
        Number: Integer;
        Initialized: Boolean;
      end;
      TArr = array[0..2] of TRec;
    var
      A: TArr;
      R: TRec;
      I: Integer;
    begin
      for I := 0 to 2 do
      begin
        A[I].Name := 'N' + IntToStr(I);
        A[I].Number := I * 10;
        A[I].Initialized := (I <> 1)
      end;
      for R in A do
        WriteLn(R.Name, '|', R.Number, '|', R.Initialized)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'N0|0|True' + LE + 'N1|10|False' + LE + 'N2|20|True' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_ChainedMethodOnRecordReturn;
const
  Src = '''
    program prg;
    type
      TVal = record
        X: Integer;
        Y: Int64;
        static function Make(A: Integer): TVal;
        function GetX: Integer;
      end;
    static function TVal.Make(A: Integer): TVal;
    begin
      Result.X := A;
      Result.Y := 7
    end;
    function TVal.GetX: Integer;
    begin
      Result := X
    end;
    begin
      WriteLn(TVal.Make(41).GetX() + 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_SetLengthOnDynArrayField;
const
  Src = '''
    program P;
    type
      TStrArr = array of string;
      TSpec = record
        Name: string;
        Cands: TStrArr;
      end;
    function MakeSpec: TSpec;
    begin
      Result.Name := 'linker';
      SetLength(Result.Cands, 2);
      Result.Cands[0] := 'cc';
      Result.Cands[1] := 'clang'
    end;
    var S: TSpec;
    begin
      S := MakeSpec();
      WriteLn(S.Name, ' ', Length(S.Cands), ' ', S.Cands[0], ' ', S.Cands[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'linker 2 cc clang' + LE, 0);
  { SetLength on a dyn-array field must be leak-free (the RTL frees the old
    block and returns a fresh rc=1 block; the field store moves ownership) }
  AssertLeakFreeOnAll(Src, 'linker 2 cc clang');
end;

procedure TE2ERecordsTests.TestRun_Record_DynArrayFieldElementAssign;
const
  Src = '''
    program P;
    type
      TStrArr = array of string;
      TIntArr = array of Integer;
      TSpec = record
        Cands: TStrArr;
        Nums: TIntArr;
      end;
    function MakeSpec: TSpec;
    begin
      SetLength(Result.Cands, 2);
      SetLength(Result.Nums, 2);
      Result.Cands[0] := 'cc';
      Result.Cands[1] := 'clang';
      Result.Nums[0] := 42;
      Result.Nums[1] := 7
    end;
    var S: TSpec;
    begin
      S := MakeSpec();
      WriteLn(S.Cands[0], ' ', S.Cands[1], ' ', S.Nums[0] + S.Nums[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'cc clang 49' + LE, 0);
  { string element writes retain/release correctly; no leak }
  AssertLeakFreeOnAll(Src, 'cc clang 49');
end;

procedure TE2ERecordsTests.TestRun_RecordIntoClassDynArrayField;
begin
  { Box.Recs[1] := R where Recs is a `array of TRec` field of the class Box.
    The whole record is copied into the element; all fields must survive. }
  AssertRunsOnAll('''
    program Prg;
    type
      TRec = record A: Integer; B: Integer; C: Int64; end;
      TBox = class Recs: array of TRec; end;
    var Box: TBox; R: TRec;
    begin
      Box := TBox.Create();
      SetLength(Box.Recs, 3);
      R.A := 10; R.B := 20; R.C := 30;
      Box.Recs[1] := R;
      WriteLn(Box.Recs[1].A);
      WriteLn(Box.Recs[1].B);
      WriteLn(Box.Recs[1].C);
      Box.Free()
    end.
    ''', '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordIntoClassStaticArrayField;
begin
  { same, but the array field is a STATIC array (inline storage, no data-ptr
    deref) — Box.Recs[2] := R. }
  AssertRunsOnAll('''
    program Prg;
    type
      TRec = record A: Integer; B: Int64; end;
      TBox = class Recs: array[0..3] of TRec; end;
    var Box: TBox; R: TRec;
    begin
      Box := TBox.Create();
      R.A := 7; R.B := 99;
      Box.Recs[2] := R;
      WriteLn(Box.Recs[2].A);
      WriteLn(Box.Recs[2].B);
      Box.Free()
    end.
    ''', '7' + LE + '99' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordIntoClassDynArrayField_Managed_LeakFree;
begin
  { a MANAGED record (string field) stored into a class dyn-array field element
    must retain the source's fields and release the dest's old fields — a
    self-ish A.Arr[I] := A.Arr[J] exercises retain-before-release.  Leak-free. }
  AssertLeakFreeOnAll('''
    program Prg;
    type
      TRec = record Name: string; N: Integer; end;
      TBox = class Recs: array of TRec; end;
    var Box: TBox; R: TRec;
    begin
      Box := TBox.Create();
      SetLength(Box.Recs, 2);
      R.Name := 'hello'; R.N := 7;
      Box.Recs[0] := R;
      Box.Recs[1] := R;
      Box.Recs[0] := Box.Recs[1];
      WriteLn(Box.Recs[0].Name);
      Box.Free()
    end.
    ''', 'hello');
end;

procedure TE2ERecordsTests.TestRun_RecordIntoClassDynArrayField_ReallocatingCall;
begin
  { Box.Recs[0] := F() where F does SetLength(Box.Recs, 8) — reallocating the
    same field the store targets.  The call must be materialised (into __rret)
    BEFORE the element address is computed, so the store lands in the fresh
    block, not the freed old one.  Expect 555 / 777 / 8. }
  AssertRunsOnAll('''
    program Prg;
    type
      TRec = record A: Integer; B: Int64; end;
      TBox = class Recs: array of TRec; end;
    var Box: TBox;
    function MakeAndGrow: TRec;
    begin
      SetLength(Box.Recs, 8);
      Result.A := 555; Result.B := 777
    end;
    begin
      Box := TBox.Create();
      SetLength(Box.Recs, 1);
      Box.Recs[0] := MakeAndGrow();
      WriteLn(Box.Recs[0].A);
      WriteLn(Box.Recs[0].B);
      WriteLn(Length(Box.Recs));
      Box.Free()
    end.
    ''', '555' + LE + '777' + LE + '8' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordStoreToVarParam;
begin
  { Get(var Outp: TRec) does Outp := Src.  The store must write to the CALLER's
    record R (through the dereferenced var-param slot), so R reads back the
    stored values.  Expect 10 / 20 / 30. }
  AssertRunsOnAll('''
    program Prg;
    type TRec = record A: Integer; B: Integer; C: Int64; end;
    procedure Get(var Outp: TRec; Src: TRec);
    begin Outp := Src end;
    var R, S: TRec;
    begin
      S.A := 10; S.B := 20; S.C := 30;
      Get(R, S);
      WriteLn(R.A); WriteLn(R.B); WriteLn(R.C)
    end.
    ''', '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_NestedRecordFieldAccess;
begin
  { Nested records with a non-zero intermediate offset (Pad before I).  Covers
    the leg-24 fix (scalar write/read through a record field, plain var + sret
    Result) plus the already-working whole-record-field read/store.  Expect
    5 / 7 / 5. }
  AssertRunsOnAll('''
    program N;
    type
      TInner = record K: Integer; end;
      TOuter = record Pad: Integer; I: TInner; end;
    function Make: TOuter;
    begin
      Result.I.K := 5;
      if Result.I.K <> 0 then Result.Pad := Result.I.K
    end;
    var O, R: TOuter; L: TInner;
    begin
      R := Make();
      O.I.K := 7;
      L := O.I;
      O.I := L;
      WriteLn(R.I.K);
      WriteLn(O.I.K);
      WriteLn(R.Pad)
    end.
    ''', '5' + LE + '7' + LE + '5' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_ManagedRecordLvalueFieldStore_LeakFree;
begin
  { L.Op := O where Op is a managed-record field and O a managed-record lvalue.
    The first store into a pre-set L.Op.S must release the old 'old' string; a
    second store must release 'hi'.  All balanced — leak-free. }
  AssertLeakFreeOnAll('''
    program Prg;
    type
      TOp = record S: string; N: Integer; end;
      TLine = record Op: TOp; end;
    var L: TLine; O: TOp;
    begin
      O.S := 'hi'; O.N := 7;
      L.Op.S := 'old';
      L.Op := O;
      WriteLn(L.Op.S); WriteLn(L.Op.N);
      O.S := 'second';
      L.Op := O;
      WriteLn(L.Op.S)
    end.
    ''', 'hi');
end;

procedure TE2ERecordsTests.TestRun_ManagedRecordParam_VarAndByValue_LeakFree;
begin
  { A var-param managed record (CBInit-style: field writes through the caller's
    address) and a by-value managed record param (field reads on the callee's
    copy).  The var-param case regressed before: the pass-2 prologue memcpy
    tried to copy it via a never-registered __pptr slot.  Leak-free. }
  AssertLeakFreeOnAll('''
    program Prg;
    type TBuf = record Data: string; Len: Integer; end;
    procedure Init(var B: TBuf);
    begin B.Data := ''; B.Len := 0 end;
    procedure Emit(var B: TBuf; C: Integer);
    begin B.Data := B.Data + Chr(C); B.Len := B.Len + 1 end;
    procedure Show(B: TBuf);
    begin WriteLn(B.Data); WriteLn(B.Len) end;
    var CB: TBuf;
    begin
      Init(CB);
      Emit(CB, 65); Emit(CB, 66);
      Show(CB)
    end.
    ''', 'AB');
end;

procedure TE2ERecordsTests.TestRun_ByValueRecordParam_FieldReadWrite;
begin
  { A BY-VALUE record param's fields must be read/written on the callee's INLINE
    copy, and mutations must NOT reach the caller.  The semantic pass marks such
    a param IsVarParam=True (records pass by reference in the ABI), so a backend
    that treats every IsVarParam base as address-in-slot double-derefs the inline
    copy on arm64.  The '__pptr_' discriminator (EmitRecordBaseAddr) keeps a
    by-value param on EmitSlotAddr.  Read C.Tag / C.Sum, mutate the copy, and
    prove the caller's record is unchanged. }
  AssertRunsOnAll('''
    program Prg;
    type TCtx = record Tag: Integer; Sum: Integer; end;
    procedure Use(C: TCtx);
    begin
      WriteLn(C.Tag);          { read inline copy }
      WriteLn(C.Sum);
      C.Tag := 999;            { mutate inline copy — caller must be isolated }
      WriteLn(C.Tag)
    end;
    var Ctx: TCtx;
    begin
      Ctx.Tag := 77; Ctx.Sum := 12;
      Use(Ctx);
      WriteLn(Ctx.Tag)         { still 77 — by-value mutation did not leak }
    end.
    ''', '77' + LE + '12' + LE + '999' + LE + '77' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordParamOverflowToStack;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A routine with 9 integer params (filling the arg registers, the 9th
    overflowing) followed by a >16B record param whose hidden pointer also
    overflows to the caller's outgoing stack area (leg 29 — the compiler's own
    EmitVexRM shape).  The overflow int and the record's fields must all arrive
    intact through the stack-passed slots. }
  AssertRunsOnAll('''
    program Prg;
    type TBig = record A, B, C: Int64; S: string; end;
    function F(a, b, c, d, e, f, g, h, i: Int64; const R: TBig): Int64;
    begin Result := i + a + R.A + R.B + R.C + Length(R.S) end;
    var R: TBig;
    begin
      R.A := 100; R.B := 200; R.C := 300; R.S := 'abcd';
      WriteLn(F(1, 2, 3, 4, 5, 6, 7, 8, 9, R))
    end.
    ''', '614' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_ManagedRecordSelfAssign;
begin
  { A managed-record self-assign (R := R) used to zero the fields on native (the
    release-dest step zeroed the shared slot before the memcpy read it, losing
    the value + leaking the +1 retain).  Cover whole-record, nested-managed,
    element, and field self-assign; assert the values SURVIVE and (via a loop of
    distinct copies) that old-field release still balances.  Heap strings so the
    native managed path is exercised. }
  AssertRunsOnAll('''
    program P;
    type
      TInner = record Name: string; end;
      TRec = record
        A, B: string;
        Inner: TInner;                     { nested-managed record field }
        ArrRec: array[0..1] of TInner;     { static-array-OF-record field }
        N: Integer;
      end;
      TBox = record Arr: array[0..1] of TRec; end;
    var R: TRec; B: TBox;
    begin
      R.A := 'a' + 'aa'; R.B := 'b' + 'bb';
      R.Inner.Name := 'i' + 'nn';
      R.ArrRec[0].Name := 'r' + '0'; R.ArrRec[1].Name := 'r' + '1';
      R.N := 7;
      R := R;                              { whole-record self-assign }
      WriteLn(R.A, ' ', R.B, ' ', R.Inner.Name, ' ',
              R.ArrRec[0].Name, ' ', R.ArrRec[1].Name, ' ', R.N);
      B.Arr[0].A := 'e' + 'lem'; B.Arr[0].B := 'x'; B.Arr[0].Inner.Name := 'y';
      B.Arr[0].ArrRec[0].Name := 'z';
      B.Arr[0] := B.Arr[0];                { element self-assign }
      WriteLn(B.Arr[0].A, ' ', B.Arr[0].ArrRec[0].Name)
    end.
    ''',
    'aaa bbb inn r0 r1 7' + LE + 'elem z' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordPropGetterIntoRecordField;
begin
  AssertRunsOnAll('''
    program P;
    type
      TBig = record A, B, C, D, E: Integer; end;
      TWrap = record Tag: Integer; Payload: TBig; end;
      TBox = class
      public
        FBig: TBig;
        FArr: array[0..1] of TBig;
        function Cur(): TBig;
        function Item(I: Integer): TBig;
        property Cur2: TBig read Cur;
        property Items[I: Integer]: TBig read Item;
      end;
    function TBox.Cur(): TBig;
    begin
      Result := FBig
    end;
    function TBox.Item(I: Integer): TBig;
    begin
      Result := FArr[I]
    end;
    var
      W: TWrap;
      B: TBox;
    begin
      B := TBox.Create();
      B.FBig.C := 7;
      B.FArr[1].E := 9;
      W.Payload := B.Cur2;             { non-indexed getter into a field }
      WriteLn(W.Payload.C);
      W.Payload := B.Items[1];         { indexed getter into a field }
      WriteLn(W.Payload.E)
    end.
    ''', '7' + LE + '9' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordFuncCallIntoVarParamRecordField;
begin
  AssertRunsOnAll('''
    program P;
    type
      TBig = record A, B, C, D, E: Integer; end;
      TWrap = record Tag: Integer; Payload: TBig; end;
    function MakeBig(V: Integer): TBig;
    begin
      Result.C := V
    end;
    procedure Fill(var W: TWrap);
    begin
      W.Payload := MakeBig(11)      { FuncCall arm, var-param dest base }
    end;
    var
      W: TWrap;
    begin
      Fill(W);
      WriteLn(W.Payload.C)
    end.
    ''', '11' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_ManagedRecordPropGetterIntoRecordField;
begin
  AssertRunsOnAll('''
    program P;
    type
      TStrRec = record S: String; N: Integer; end;
      TWrap = record Tag: Integer; Payload: TStrRec; end;
      TBox = class
      public
        FRec: TStrRec;
        function Item(I: Integer): TStrRec;
        property Items[I: Integer]: TStrRec read Item;
      end;
    function TBox.Item(I: Integer): TStrRec;
    begin
      Result := FRec;
      Result.S := Result.S + '-' + IntToStr(I);
      Result.N := Result.N + I
    end;
    var
      W: TWrap;
      B: TBox;
    begin
      B := TBox.Create();
      B.FRec.S := 'hello';
      B.FRec.N := 5;
      W.Payload := B.Items[3];
      WriteLn(W.Payload.S, ' ', W.Payload.N);
      W.Payload := B.Items[9];      { reassign: old field string released }
      WriteLn(W.Payload.S, ' ', W.Payload.N);
      WriteLn(B.FRec.S)             { source untouched }
    end.
    ''', 'hello-3 8' + LE + 'hello-9 14' + LE + 'hello' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_VarParamRecordReceiverSelfAssign;
begin
  AssertRunsOnAll('''
    program P;
    type
      TRec = record
        S: string;
        N: Integer;
        function Grow(const A: string): TRec;
      end;
    function TRec.Grow(const A: string): TRec;
    begin
      Result.S := S + A;
      Result.N := N + 1
    end;
    procedure Twice(var Z: TRec);
    begin
      Z := Z.Grow('!');
      Z := Z.Grow('?')
    end;
    function Comp(const A: TRec): TRec;
    begin
      Result.S := A.S + '.';
      Result.N := A.N
    end;
    procedure ViaArg(var Z: TRec);
    begin
      { dest is also an ARGUMENT of the call }
      Z := Comp(Z)
    end;
    var R: TRec;
    begin
      R.S := 'k';
      R.N := 1;
      Twice(R);
      WriteLn(R.S);
      WriteLn(R.N);
      ViaArg(R);
      WriteLn(R.S)
    end.
    ''', 'k!?' + LE + '3' + LE + 'k!?.' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_FieldArrayElem_ByVarParam;
begin
  AssertRunsOnAll('''
    program P;
    type
      TR = record N: Integer; end;
      THold = class
      public
        FInts: array[0..2] of Integer;
        FLow: array[2..4] of Integer;
        FDyn: array of Integer;
        FStr: array[0..2] of string;
        FRec: array[0..1] of TR;
        procedure Go();
      end;
    procedure Bump(var I: Integer); begin I := I + 100 end;
    procedure AppendX(var S: string); begin S := S + 'X' end;
    procedure SetN(out R: TR); begin R.N := 99 end;
    procedure THold.Go();
    begin
      FInts[0] := 1; FInts[1] := 2; FInts[2] := 3;
      Bump(FInts[1]);                 { implicit-Self static field-array elem }
      WriteLn(FInts[0], ' ', FInts[1], ' ', FInts[2])
    end;
    var H: THold;
    begin
      H := THold.Create();
      H.FInts[0] := 10; H.FInts[1] := 20; H.FInts[2] := 30;
      Bump(H.FInts[1]);               { static field-array elem }
      WriteLn(H.FInts[0], ' ', H.FInts[1], ' ', H.FInts[2]);
      SetLength(H.FDyn, 3);
      H.FDyn[0] := 4; H.FDyn[1] := 5; H.FDyn[2] := 6;
      Bump(H.FDyn[1]);                { dyn field-array elem }
      WriteLn(H.FDyn[0], ' ', H.FDyn[1], ' ', H.FDyn[2]);
      H.FStr[0] := 'a'; H.FStr[1] := 'b'; H.FStr[2] := 'c';
      AppendX(H.FStr[1]);             { string (managed) field-array elem }
      WriteLn(H.FStr[0], ' ', H.FStr[1], ' ', H.FStr[2]);
      H.FRec[0].N := 1; H.FRec[1].N := 2;
      SetN(H.FRec[1]);                { record field-array elem, out param }
      WriteLn(H.FRec[0].N, ' ', H.FRec[1].N);
      H.FLow[2] := 1; H.FLow[3] := 2; H.FLow[4] := 3;
      Bump(H.FLow[3]);                { non-zero LowBound field-array elem }
      WriteLn(H.FLow[2], ' ', H.FLow[3], ' ', H.FLow[4]);
      H.Go()
    end.
    ''', '10 120 30' + LE + '4 105 6' + LE + 'a bX c' + LE + '1 99' + LE +
         '1 102 3' + LE + '1 102 3' + LE, 0);
end;

initialization
  RegisterTest(TE2ERecordsTests);

end.
