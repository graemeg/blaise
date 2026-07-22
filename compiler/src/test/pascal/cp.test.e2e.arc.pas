{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.arc;

{ E2E tests for ARC (Automatic Reference Counting) — class and interface
  lifetime, weak references, and leak-freedom.  Leak-freedom is checked two
  ways: valgrind (catches native-level UAF / invalid access — but NOT ARC
  refcount leaks, since the Blaise allocator is mmap-backed and invisible to
  valgrind's malloc interception) and the --debug ARC leak tracker (reports
  Blaise objects still live at exit — the true refcount-leak signal). }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EArcTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ClassArc_NoExplicitFree_Valgrind;
    procedure TestRun_InterfaceArc_CarriesLifetime_Valgrind;
    procedure TestRun_WeakRef_BreaksCycle_Valgrind;
    procedure TestRun_ClassDestroy_FreesBuffer_Valgrind;
    procedure TestRun_TListARC_Valgrind;
    procedure TestRun_IntfValueParam_Retained_Valgrind;
    { Regression: a const string param bound to a freshly-built TEMPORARY must
      stay alive for the whole call.  Under the const-param ARC elision the
      callee skips the retain, so the call site must keep the temporary alive
      (EnsureConstStringRef).  A string LITERAL hides this (it is immortal); a
      concatenation result does not. }
    procedure TestRun_ConstStringTemp_StaysAlive_Valgrind;
    { Caller-side companion to the elision: a +0 concat transient forwarded
      through nested const-string routines and read again afterwards. }
    procedure TestRun_ConstStringParam_TransientRetained_Valgrind;
    { Three instantiations of the same generic class: verifies the Pointer→class
      ARC coercion bug is fixed (the 3rd instantiation no longer uses freed memory). }
    procedure TestRun_ThreeGenericInstances_AllWork;
    { A Pointer-returning rvalue (TObjectList.Items[K]) assigned into a TObject
      local must retain, so the local's scope-exit release only balances that
      retain and does not drop the list-held object's refcount.  Guards against
      dispatching the assignment ARC on the RHS (Pointer) type instead of the
      LHS (class) slot type. }
    procedure TestRun_PtrRvalueToClassLocal_PreservesLifetime;
    procedure TestRun_ClassVarAssignNil_Destroys;
    { A method call whose receiver is a deep field chain rooted in a
      transient function result — MakeIt().A.B.Method() — must keep the
      transient alive until the call completes.  The native backend released
      the transient after the FIRST field hop, and _ClassRelease at refcount 0
      runs _FieldCleanup, freeing the intermediate objects (A, then B) the rest
      of the chain still dereferences — a use-after-free that crashed when the
      chain had two or more hops before the call.  Guards both backends. }
    procedure TestRun_TransientDeepChainMethodCall_NoUseAfterFree;
    { Free on a method-call-result receiver (B.Grab().Free()): the getter
      hands back an owned +1 temporary, so Free is a single balanced
      release — no leak, no double-free.  Guards the arm64 general-
      expression Free branch (mirrors x86-64). }
    procedure TestRun_FreeOnCallResult_NoLeak_Valgrind;
    { A retained managed field read off an owned-transient base:
      MakeThing().Name (string field) and MakeThing().Obj (class field).
      The base is released as part of the read; the loaded value must still
      be correct.  Both backends.  (Value correctness — the leak-freedom of
      the class arm is guarded separately by the valgrind test below.) }
    procedure TestRun_RetainedFieldReadOnTransient_Correct;
    { The class-field-on-transient read must be LEAK-FREE (BUG-048): both
      backends defer the transient's release to statement end rather than
      AddRef-pinning the borrowed field value.  Uses the --debug ARC leak
      tracker (NOT valgrind — the Blaise allocator is mmap-backed, so
      valgrind sees zero malloc traffic and cannot observe an ARC leak; the
      tracker reports surviving objects at exit).  The pre-fix pin left one
      TOuter + one TInner unreleased per such read on arm64. }
    procedure TestRun_ClassFieldReadOnTransient_NoLeak_Debug;
    { A dynamic-array function return (function MakeArr: TArr): the Result's
      +1 transfers to the caller, which releases the old value and stores the
      new one with no extra retain.  Must be leak-free and double-free-free —
      the transfer has to balance exactly. }
    procedure TestRun_DynArrayFunctionReturn_NoLeak_Valgrind;
    { A record-returning call stored into an array element where the element
      is a MANAGED record (string field): Arr[I] := MakeSpec().  The dest
      element's old managed refs are released and the callee's +1 refs
      transfer in — must be leak-free and double-free-free. }
    procedure TestRun_ManagedRecordCallIntoElement_NoLeak_Valgrind;
    { A record whose ONLY managed content is a static-array-of-class field
      must keep full ARC discipline on return + copy.  RecretManagedClean
      lacked a tyStaticArray case, so such a record register-returned and
      copied by bare memcpy — shared refs then double-released at scope exit
      (BUG-20260721-recretclean-static-array-of-managed). }
    procedure TestRun_RecordStaticArrayOfClassOnly_ReturnAndCopy_NoLeak;
  end;

implementation

procedure TE2EArcTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-arc');
end;

const
  LE = #10;

  SrcClassArcNoFree = '''
    program P;
    type
      TInner = class
        V: Integer;
      end;
      TOuter = class
        Child: TInner;
      end;
    var
      A, B: TOuter;
      I:    TInner;
    begin
      A       := TOuter.Create();
      I       := TInner.Create();
      I.V     := 42;
      A.Child := I;
      B       := A;
      WriteLn(B.Child.V)
    end.
    ''';

  SrcInterfaceArcLifetime = '''
    program P;
    type
      IThing = interface
        procedure Emit;
      end;
      TThing = class(TObject, IThing)
        FValue: Integer;
        procedure Emit;
      end;
    procedure TThing.Emit;
    begin
      WriteLn(Self.FValue)
    end;
    var
      T: TThing;
      F: IThing;
    begin
      T        := TThing.Create();
      T.FValue := 17;
      F        := T;
      F.Emit()
    end.
    ''';

  SrcWeakCycle = '''
    program P;
    type
      TNode = class
        Value: Integer;
        [Weak] Other: TNode;
      end;
    var
      A, B: TNode;
    begin
      A := TNode.Create();
      B := TNode.Create();
      A.Value := 1;
      B.Value := 2;
      A.Other := B;
      B.Other := A;
      WriteLn(A.Value);
      WriteLn(B.Value)
    end.
    ''';

  SrcDestroyFreesBuffer = '''
    program P;
    type
      TBuf = class
        FData: ^Integer;
        procedure Init;
        procedure Destroy;
      end;
    procedure TBuf.Init;
    begin
      Self.FData := GetMem(4 * SizeOf(Integer))
    end;
    procedure TBuf.Destroy;
    begin
      FreeMem(Self.FData);
      Self.FData := nil
    end;
    var B: TBuf;
    begin
      B := TBuf.Create();
      B.Init();
      WriteLn('ok')
    end.
    ''';

  SrcTListARCValgrind = '''
    program P;
    type
      TList = class
        FData:     ^Integer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        procedure Add(V: Integer);
        function  Get(I: Integer): Integer;
        procedure Destroy;
        property Count: Integer read FCount;
      end;
    procedure TList.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 4
      else NewCap := Self.FCapacity * 2;
      Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Integer));
      Self.FCapacity := NewCap
    end;
    procedure TList.Add(V: Integer);
    var Dest: ^Integer;
    begin
      if Self.FCount = Self.FCapacity then Self.Grow();
      Dest  := Self.FData + Self.FCount * SizeOf(Integer);
      Dest^ := V;
      Self.FCount := Self.FCount + 1
    end;
    function TList.Get(I: Integer): Integer;
    var Src: ^Integer;
    begin
      Src    := Self.FData + I * SizeOf(Integer);
      Result := Src^
    end;
    procedure TList.Destroy;
    begin
      FreeMem(Self.FData);
      Self.FData := nil
    end;
    var L: TList;
    begin
      L := TList.Create();
      L.Add(10);
      L.Add(20);
      L.Add(30);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      WriteLn(L.Get(2));
      WriteLn(L.Count)
    end.
    ''';

  { Free on a method-call-result receiver: Grab returns a freshly-created
    (+1 owned) instance, Free balances that +1.  No leak (the instance is
    freed), no double-free (nothing else holds it). }
  SrcFreeOnCallResult = '''
    program P;
    type
      TThing = class
      public
        V: Integer;
      end;
      TBox = class
      public
        function Grab: TThing;
      end;
    function TBox.Grab: TThing;
    begin
      Result := TThing.Create();
      Result.V := 9
    end;
    var
      B: TBox;
    begin
      B := TBox.Create();
      B.Grab().Free();
      WriteLn(1);
      B.Free()
    end.
    ''';

procedure TE2EArcTests.TestRun_ClassArc_NoExplicitFree_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcClassArcNoFree, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('field reread', '42' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcClassArcNoFree, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcClassArcNoFree, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_InterfaceArc_CarriesLifetime_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcInterfaceArcLifetime, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('interface method result', '17' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcInterfaceArcLifetime, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcInterfaceArcLifetime, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_WeakRef_BreaksCycle_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcWeakCycle, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('values printed via A/B', '1' + LE + '2' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcWeakCycle, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcWeakCycle, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_ClassDestroy_FreesBuffer_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcDestroyFreesBuffer, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', 'ok' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcDestroyFreesBuffer, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcDestroyFreesBuffer, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('Destroy did not free buffer — valgrind reports:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_TListARC_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTListARCValgrind, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout',
    '10' + LE + '20' + LE + '30' + LE + '3' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcTListARCValgrind, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcTListARCValgrind, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('TList FData leaked — valgrind reports:' + LE + Log);
  end;
end;

const
  { Three instantiations of the same generic class implementing a generic
    interface.  The 3rd instantiation previously failed at link time because
    the Pointer→class coercion in FindGeneric emitted no _ClassAddRef, causing
    the template TObject to be prematurely destroyed on the 2nd call.  This
    test verifies all three compile, link, and produce correct output. }
  SrcThreeGenericInstances = '''
    program P;
    type
      IBox<T> = interface
        function  GetValue: T;
        procedure SetValue(V: T);
      end;
      TBox<T> = class(IBox<T>)
        FValue: T;
        function  GetValue: T;
        procedure SetValue(V: T);
        property Value: T read GetValue write SetValue;
      end;
    function TBox<T>.GetValue: T;
    begin
      Result := Self.FValue
    end;
    procedure TBox<T>.SetValue(V: T);
    begin
      Self.FValue := V
    end;
    var
      A: TBox<Integer>;
      B: TBox<Boolean>;
      C: TBox<Integer>;
    begin
      A := TBox<Integer>.Create();
      A.Value := 10;
      B := TBox<Boolean>.Create();
      B.Value := True;
      C := TBox<Integer>.Create();
      C.Value := 30;
      WriteLn(A.Value);
      if B.Value then WriteLn(1) else WriteLn(0);
      WriteLn(C.Value)
    end.
    ''';

const
  { By-value interface param: the callee must retain it on entry, because the
    caller's reference can be dropped during the call.  Here DoSomething nils
    the global F (the caller's sole owner) *before* using MyIntf again.  With
    the entry retain the object survives until DoSomething returns; without it
    the second MyIntf.Get would be a use-after-free.  Valgrind must report no
    error and no leak (the entry retain is balanced by the exit release). }
  SrcIntfValueParamRetained = '''
    program P;
    type
      IThing = interface
        function Get: Integer;
      end;
      TThing = class(TObject, IThing)
        FValue: Integer;
        function Get: Integer;
      end;
    function TThing.Get: Integer;
    begin
      Result := Self.FValue
    end;
    var
      F: IThing;
    procedure DoSomething(MyIntf: IThing);
    begin
      WriteLn(MyIntf.Get());
      F := nil;            { drop the caller's only other reference }
      WriteLn(MyIntf.Get())  { still valid: callee retained it on entry }
    end;
    var
      T: TThing;
    begin
      T := TThing.Create();
      T.FValue := 55;
      F := T;
      DoSomething(F)
    end.
    ''';

procedure TE2EArcTests.TestRun_IntfValueParam_Retained_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfValueParamRetained, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', '55' + LE + '55' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcIntfValueParamRetained, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcIntfValueParamRetained, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('interface value param not retained — valgrind reports:' + LE + Log);
  end;
end;

const
  { Pass a freshly-concatenated temporary as a const string param, then read
    it inside the callee.  Without the callee-side retain the temporary's
    refcount hits zero at the call site and the string is freed before Use
    reads it — a use-after-free valgrind catches.  A literal would not expose
    this (it is immortal), so the argument must be a built-at-runtime value. }
  SrcConstStringTemp = '''
    program P;
    procedure Use(const S: string);
    begin
      WriteLn(S);
      WriteLn(Length(S))
    end;
    var
      A, B: string;
    begin
      A := 'hello';
      B := 'world';
      Use(A + ' ' + B)
    end.
    ''';

procedure TE2EArcTests.TestRun_ConstStringTemp_StaysAlive_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStringTemp, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', 'hello world' + LE + '11' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcConstStringTemp, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcConstStringTemp, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('const string temp freed mid-call — valgrind reports:' + LE + Log);
  end;
end;

const
  { Caller-side companion to the const-param elision.  A string concat result
    leaves _StringConcat at rc=0 (a "+0 transient").  The callee no longer
    retains the const-string buffer, so the call site must keep it alive for
    the duration of the call.  Process forwards the borrowed buffer to a
    nested const-string routine and reads it again afterwards; without the
    caller-side retain inserted by EnsureConstStringRef the buffer is freed
    mid-call and the trailing WriteLn observes corrupted data (or aborts).

    Valgrind catches the converse regression: an over-retain that never gets
    released would leak the concat buffer. }
  SrcConstStrTransient = '''
    program P;
    procedure Inner(const T: string);
    begin
      WriteLn(T)
    end;
    procedure Process(const S: string);
    begin
      Inner(S);
      Inner(S);
      WriteLn(S)
    end;
    begin
      Process('foo' + 'bar')
    end.
    ''';

procedure TE2EArcTests.TestRun_ConstStringParam_TransientRetained_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStrTransient, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', 'foobar' + LE + 'foobar' + LE + 'foobar' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcConstStrTransient, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcConstStrTransient, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('const-string transient retain missing — valgrind reports:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_ThreeGenericInstances_AllWork;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcThreeGenericInstances, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('all three instances produce correct output',
    '10' + LE + '1' + LE + '30' + LE, Output);
end;

const
  { Regression: assigning a Pointer-returning expression (TObjectList.Items[K])
    into a TObject local must retain.  Builds the list inside the program, walks
    it with a plain TObject local in Borrow, and tracks TThing.Destroy via a
    counter.  Asserts the object survives Borrow (counter 0) and is freed only
    when L.Free runs (counter 1).  If the assignment dispatched ARC on the RHS
    Pointer type it would skip the retain, and Borrow's scope-exit release would
    drop the list-held refcount to zero and run Destroy mid-program. }
  SrcPtrRvalueClassLocal = '''
    program P;
    uses contnrs;
    type
      TThing = class
        procedure Destroy; override;
      end;
    var
      L:     TObjectList;
      Freed: Integer;
    procedure TThing.Destroy;
    begin
      Freed := Freed + 1
    end;
    procedure Borrow;
    var S: TObject;
    begin
      S := L.Items[0]
    end;
    begin
      Freed := 0;
      L := TObjectList.Create(True);
      L.Add(TThing.Create());
      Borrow();
      WriteLn(Freed);
      L.Free();
      WriteLn(Freed)
    end.
    ''';

procedure TE2EArcTests.TestRun_PtrRvalueToClassLocal_PreservesLifetime;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcPtrRvalueClassLocal, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('counter after Borrow then after L.Free()',
    '0' + LE + '1' + LE, Output);
end;

const
  SrcClassAssignNil = '''
    program P;
    type
      TThing = class
        destructor Destroy; override;
      end;
    destructor TThing.Destroy;
    begin
      WriteLn('destroyed');
      inherited Destroy()
    end;
    var O: TThing;
    begin
      O := TThing.Create();
      O := nil;
      WriteLn('done')
    end.
    ''';

procedure TE2EArcTests.TestRun_ClassVarAssignNil_Destroys;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcClassAssignNil, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('O := nil triggers destroy',
    'destroyed' + LE + 'done' + LE, Output);
end;

const
  SrcTransientDeepChain = '''
    program P;
    type
      TInner = class
        Val: Integer;
        function GetVal: Integer;
      end;
      TBlk = class
        Inner: TInner;
        constructor Create;
      end;
      TProg = class
        Blk: TBlk;
        constructor Create;
      end;
    function TInner.GetVal: Integer;
    begin
      Result := Self.Val
    end;
    constructor TBlk.Create;
    begin
      Self.Inner := TInner.Create();
      Self.Inner.Val := 7
    end;
    constructor TProg.Create;
    begin
      Self.Blk := TBlk.Create()
    end;
    function MakeProg: TProg;
    begin
      Result := TProg.Create()
    end;
    var
      V, I: Integer;
    begin
      { Two field hops (.Blk.Inner) before the method call, on a transient
        function result that is never explicitly freed.  The loop forces the
        freed-then-reused arena to surface a use-after-free deterministically. }
      V := 0;
      for I := 0 to 50 do
        V := V + MakeProg().Blk.Inner.GetVal();
      WriteLn(V)
    end.
    ''';

procedure TE2EArcTests.TestRun_TransientDeepChainMethodCall_NoUseAfterFree;
var Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 51 iterations * 7 = 357.  Both backends must agree on the value. }
  AssertRunsOnAll(SrcTransientDeepChain, '357' + LE, 0);
  { The use-after-free is non-deterministic at the stdout level (a freed-then-
    not-yet-reused read returns the old value), so the value check above can
    pass even when the bug is present.  valgrind on the NATIVE binary detects
    the invalid read deterministically — this is the real regression guard. }
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  if not RunUnderValgrindNative(SrcTransientDeepChain, Log) then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('native valgrind reported an invalid access (use-after-free):' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_FreeOnCallResult_NoLeak_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcFreeOnCallResult, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('ran', '1' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcFreeOnCallResult, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcFreeOnCallResult, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_RetainedFieldReadOnTransient_Correct;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { string field off a transient base: base released inline, string survives }
  AssertRunsOnAll(
    '''
    program P;
    type
      TThing = class
      public
        Name: string;
      end;
    function MakeThing: TThing;
    begin
      Result := TThing.Create();
      Result.Name := 'hello'
    end;
    var S: string;
    begin
      S := MakeThing().Name;
      WriteLn(S)
    end.
    ''',
    'hello' + LE, 0);
  { class field off a transient base: the base release is DEFERRED (both
    backends, BUG-048) so the loaded object outlives the transient — valid }
  AssertRunsOnAll(
    '''
    program P;
    type
      TInner = class
      public
        N: Integer;
      end;
      TThing = class
      public
        Obj: TInner;
      end;
    function MakeThing: TThing;
    begin
      Result := TThing.Create();
      Result.Obj := TInner.Create();
      Result.Obj.N := 7
    end;
    var X: TInner;
    begin
      X := MakeThing().Obj;
      WriteLn(X.N)
    end.
    ''',
    '7' + LE, 0);
end;

procedure TE2EArcTests.TestRun_DynArrayFunctionReturn_NoLeak_Valgrind;
const
  Src = '''
    program P;
    type TArr = array of Integer;
    function MakeArr(N: Integer): TArr;
    var I: Integer;
    begin
      SetLength(Result, N);
      for I := 0 to N - 1 do
        Result[I] := I * 10
    end;
    var
      A: TArr;
      I, Sum: Integer;
    begin
      A := MakeArr(4);
      Sum := 0;
      for I := 0 to 3 do
        Sum := Sum + A[I];
      WriteLn(Sum)
    end.
    ''';
var Output: string; RCode: Integer; Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(Src, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('0+10+20+30', '60' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(Src, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  if not RunUnderValgrind(Src, Log) then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_ManagedRecordCallIntoElement_NoLeak_Valgrind;
const
  Src = '''
    program P;
    type
      TSpec = record
        Name: string;
        Kind: Integer;
      end;
      TArr = array of TSpec;
    function MakeSpec(N: Integer): TSpec;
    begin
      Result.Name := 'tool';
      Result.Kind := N
    end;
    var
      Arr: TArr;
      I, Sum: Integer;
    begin
      SetLength(Arr, 3);
      for I := 0 to 2 do
        Arr[I] := MakeSpec(I * 10);
      Sum := 0;
      for I := 0 to 2 do
        Sum := Sum + Arr[I].Kind;
      WriteLn(Arr[0].Name);
      WriteLn(Sum)
    end.
    ''';
var Output: string; RCode: Integer; Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(Src, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('name + 0+10+20', 'tool' + LE + '30' + LE, Output);
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(Src, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  if not RunUnderValgrind(Src, Log) then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_RecordStaticArrayOfClassOnly_ReturnAndCopy_NoLeak;
const
  Src = '''
    program P;
    type
      TThing = class
      public
        V: Integer;
      end;
      TR = record
        Arr: array[0..1] of TThing;
      end;
    function Make(): TR;
    begin
      Result.Arr[0] := TThing.Create();
      Result.Arr[0].V := 7;
      Result.Arr[1] := TThing.Create();
      Result.Arr[1].V := 8
    end;
    var
      A, B: TR;
    begin
      A := Make();
      B := A;
      WriteLn(B.Arr[0].V + B.Arr[1].V)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(Src, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('field values survive copy', '15' + LE, Output);
  { the double-release from a bare-memcpy copy shows up here }
  AssertLeakFreeOnAll(Src, '');
end;

procedure TE2EArcTests.TestRun_ClassFieldReadOnTransient_NoLeak_Debug;
const
  Src = '''
    program P;
    type
      TInner = class
      public
        N: Integer;
      end;
      TThing = class
      public
        Obj: TInner;
      end;
    function MakeThing: TThing;
    begin
      Result := TThing.Create();
      Result.Obj := TInner.Create();
      Result.Obj.N := 7
    end;
    var X: TInner;
    begin
      X := MakeThing().Obj;
      WriteLn(X.N)
    end.
    ''';
begin
  { The transient TThing's release is deferred to the assignment's end,
    balancing its +1 — the leak tracker must report nothing on either
    backend.  Native is the arm regression path: the pre-fix AddRef-pin left
    the transient graph unreleased here. }
  AssertLeakFreeOnAll(Src, '7');
end;

initialization
  RegisterTest(TE2EArcTests);

end.
