{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nativearc;

{ Assembly-level ARC tests for the NATIVE x86-64 backend.

  These cannot live in cp.test.arc.pas: that unit's uses clause pulls in
  blaise.codegen.qbe only, and its GenIR helper drives the QBE emitter — the
  QBE backend has a single cleanup routine (EmitArcCleanup) driven by
  Block.Decls, so it cannot see a native-only gap.

  The native x86-64 backend has TWO hand-written ARC cleanup paths: the
  procedure-frame walk (driven by the method's Body.Decls) and the main-body
  walk EmitGlobalReleases (driven by FDataGlobals, since PROGRAM-level vars
  are registered as globals).  A gap in one is invisible to the other, so the
  main-body path needs its own assertions. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, cp.test.harness;

type
  TNativeArcTests = class(TTestCase)
  private
    function MainExitRegion(const AAsm: string): string;
  published
    { an owned transient base's release is deferred however many one statement
      holds: the pool grows past its reserved slots }
    procedure TestNative_OwnedTransientBases_DeferredPastEightSlots;
    { an owned class transient tested with = / <>, is or Assigned is released
      afterwards (it leaked on both backends) }
    { an owned class call result narrowed to an interface is CONSUMED by the
      store (x86-64 retained it again and leaked one object per store), and
      passed to an interface parameter as obj + itab (x86-64 hoisted it as a
      single class slot, so the callee read the obj as the itab) }
    { an owned dyn-array argument is released after the call; Length of
      one is released once read; a discarded string result is released
      (BUG-20261011-owned-dynarray-arg-leak -- the first two leaked on both
      ISAs, the discard on x86-64) }
    { P3 owned-transient corners: the object / string a call hands back is
      released after Supports and OrdAt use it; a constructor result is
      owned from its allocation (retained before the body runs); an owned
      interface stored into a [Weak] variable is registered and released }
    procedure TestOwnedTransient_SupportsReleasesObject;
    procedure TestOwnedTransient_OrdAtReleasesString;
    procedure TestCtorResult_OwnedAtAllocation;
    { raise E (a variable) retains for the in-flight exception; raise
      EFoo.Create() hands the constructor's own reference over }
    procedure TestRaise_BorrowedOperandRetained;
    procedure TestOwnedIntoWeakInterface_Released;
    { R.O := MkN() for a record VARIABLE or a var record param: the call's
      +1 moves into the field -- x86-64 retained it again (a leak per store) }
    procedure TestOwnedIntoRecordVarField_NoRetain;
    procedure TestOwnedDynArrayArg_ReleasedAfterCall;
    procedure TestOwnedDynArrayLength_Released;
    procedure TestDiscardedStringResult_Released;
    procedure TestOwnedClassToInterface_StoreConsumes;
    procedure TestOwnedClassToInterface_ArgPassesItab;
    procedure TestOwnedClassTest_ReleasedAfterCompare;
    procedure TestOwnedClassTest_ReleasedAfterIsAndAssigned;
    { x86-64 codegen fixes surfaced by the macOS bring-up's native-only
      e2e tests (asm generated in-process for linux-x86_64, so they run on
      any host). }
    procedure TestX86_SmallSetLiteral_RuntimeMemberOrredIn;
    { A call with more than eight owned transient arguments: arm64 parked
      them in a fixed pool of eight frame slots and refused the ninth. }
    procedure TestCall_TenOwnedTransientArgs_Lowered;
    { an owned class transient argument (a call result) is borrowed by the
      callee, so the caller releases it after the call: x86-64 leaked it }
    procedure TestCall_OwnedClassTransientArg_ReleasedAfterCall;
    { an [Unretained] field stored through a cast receiver takes no
      reference: no retain of the new value, no release of the old }
    procedure TestFieldStore_UnretainedThroughCast_NoArc;
    procedure TestX86_NestedJumboSetCallArg_Hoisted;
    procedure TestX86_ForIn_InterfaceCurrent_UsesSret;
    procedure TestX86_ForIn_InterfaceArrayElem_Retained;
    { A PROGRAM-level static array of managed elements is a GLOBAL, so its
      cleanup runs through EmitGlobalReleases, not the procedure-frame walk.
      That kind chain handled string/class/dyn-array/interface/record but not
      tyStaticArray, so every element leaked at program exit on native while
      QBE was correct. }
    procedure TestMain_ProgramStaticArrayOfClass_EmitsClassRelease;
    procedure TestMain_ProgramStaticArrayOfString_EmitsStringRelease;
    procedure TestMain_ProgramStaticArrayOfRecord_EmitsStringRelease;
    { An unmanaged element type must emit no release walk at all. }
    procedure TestMain_ProgramStaticArrayOfInteger_NoReleases;
    { The pre-existing scalar-global arms must keep working. }
    procedure TestMain_ProgramClassGlobal_EmitsClassRelease;
    { A record whose ONLY managed content is a static-array-of-managed field
      must take the ARC copy path on `B := A` (retain source elements before
      the memcpy).  RecretManagedClean lacked a tyStaticArray case, so such a
      record was mis-classified as managed-clean and copied by bare memcpy —
      both sides then shared the refs and the scope-exit walk double-released
      (BUG-20260721-recretclean-static-array-of-managed). }
    procedure TestMain_RecordCopy_StaticArrayOfStringOnly_EmitsRetain;
    { Discarded calls to sret-returning functions must pass a hidden result
      buffer and release the discarded result's managed content — the bug
      emitted a bare `callq F` with no %rdi buffer, so the callee wrote its
      result through a garbage register
      (BUG-20260722-discarded-sret-call-no-buffer). }
    procedure TestMain_DiscardedRecordCall_ReleasesElements;
    procedure TestMain_DiscardedInterfaceCall_ReleasesObj;
    { BUG-20261009-pendrel-stale-slot: a statement-deferred release must
      re-nil its _pendrel slot after the flush (and the frame must start the
      slots at nil), because a short-circuit `and` can skip the deferring
      operand on a later evaluation of the same statement. }
    procedure TestPendRel_SlotReNilledAfterFlush;
    { BUG-20261009-recordcall-field-read-leak: F(1).V pins the loaded string
      and then releases the call temp's fields (the pin's release is
      deferred to the statement end). }
    procedure TestRecordCallFieldRead_PinsThenReleasesTemp;
    { An owned transient method receiver (MakeL().Hello()) is released after
      the call -- x86-64 never released it. }
    procedure TestOwnedMethodReceiver_Released;
    { @MakeObj().N: the owned base outlives the address and is released at
      the statement end (x86-64 leaked it; arm64 was NotYet) }
    procedure TestAddrOfOwnedTransientField_ReleasedAtStatementEnd;
    { MakeObj().S := V: the owned receiver is released at the statement end
      (x86-64 never released it) }
    procedure TestFieldStoreOwnedReceiver_Released;
    { A by-value dyn-array parameter is a co-owning ref-counted pointer:
      the callee must retain it on entry and release it at exit
      (BUG-20260721-byval-dynarray-param-no-arc). }
    procedure TestFunc_DynArrayValueParam_RetainedAndReleased;
    { A method-backed property setter borrows its value: an owned-transient
      string value must be disposed after the setter call
      (BUG-20260721-propsetter-owned-transient-str-leak). }
    procedure TestMain_PropSetterConcatValue_DisposedAfterCall;
    { G.GetI() = nil: an interface-returning call as a scalar operand gets
      its sret buffer and its +1 obj is released at the statement end
      (x86-64 passed no buffer -- a crash; arm64 leaked the obj) }
    procedure TestIntfCallOperand_SretAndReleased;
    { L := MkObj().GetI() / MkObj().FIntf: the owned receiver is released at
      the statement end (x86-64 leaked it) }
    procedure TestIntfFromOwnedReceiver_Released;
  end;

implementation

procedure TNativeArcTests.TestX86_SmallSetLiteral_RuntimeMemberOrredIn;
var
  AsmT: string;
begin
  { [K, 40]: the constant member folds into the immediate and the runtime
    member K ORs its bit in afterwards.  The fold used to skip K silently,
    leaving bit 40 alone. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TWide = set of 0..40;
    function WideOf(K: Integer): TWide;
    begin
      Result := [K, 40];
    end;
    begin
    end.
    ''', TargetX86_64);
  AssertTrue('constant member folded', Pos('movabsq $1099511627776, %rax', AsmT) >= 0);
  AssertTrue('runtime member shifted into place', Pos(#9'shlq %cl, %rdx', AsmT) >= 0);
  AssertTrue('and ORed into the mask', Pos(#9'orq %rdx, %rax', AsmT) >= 0);
end;

procedure TNativeArcTests.TestX86_NestedJumboSetCallArg_Hoisted;
var
  AsmT, Body: string;
begin
  { Count(Fold(Fold(X))): the inner jumbo-set call is hoisted like a record
    call argument, so the outer Fold's sret destination is read from its own
    saved slot rather than from 0(%rsp), which by then is the inner result's
    bitmap.  Record-returning calls go through EmitCall's slot path, so the
    saved slot sits above the 48-byte hoist region AND the 16-byte slot
    block: 64 bytes up, copied into the block's first slot (%rdi). }
  AsmT := GenAsm(
    '''
    program P;
    type
      TCls = set of Byte;
    function Count(S: TCls): Integer;
    begin
      Result := 0;
    end;
    function Fold(const ACls: TCls): TCls;
    begin
      Result := ACls;
    end;
    var
      X: TCls;
    begin
      WriteLn(Count(Fold(Fold(X))));
    end.
    ''', TargetX86_64);
  Body := Copy(AsmT, Pos('main:', AsmT), Length(AsmT));
  AssertTrue('outer destination read past the hoisted inner buffer',
    Pos(#9'movq 64(%rsp), %rax'#10#9'movq %rax, 0(%rsp)', Body) >= 0);
end;

procedure TNativeArcTests.TestX86_ForIn_InterfaceCurrent_UsesSret;
var
  AsmT: string;
begin
  { for G in E with an interface-returning Current: the getter is called
    with the sret buffer in %rdi and the enumerator in %rsi, and the owned
    pair moves into the loop variable.  It was a scalar call with the
    enumerator in %rdi, so the getter wrote through the enumerator. }
  AsmT := GenAsm(
    '''
    program P;
    type
      IG = interface
        function Greet: Int64;
      end;
      TEnum = class
        FDone: Boolean;
        FCur: IG;
        function MoveNext: Boolean;
        function GetCurrent: IG;
        property Current: IG read GetCurrent;
      end;
      TColl = class
        function GetEnumerator: TEnum;
      end;
    function TEnum.MoveNext: Boolean;
    begin
      Result := not FDone;
      FDone := True;
    end;
    function TEnum.GetCurrent: IG;
    begin
      Result := FCur;
    end;
    function TColl.GetEnumerator: TEnum;
    begin
      Result := TEnum.Create();
    end;
    procedure Run(C: TColl);
    var
      G: IG;
    begin
      for G in C do
        WriteLn(G.Greet());
    end;
    begin
    end.
    ''', TargetX86_64);
  AssertTrue('getter called with the sret buffer in %rdi and Self in %rsi',
    Pos(#9'movq %r10, %rsi'#10#9'movq %rsp, %rdi'#10#9'callq TEnum_GetCurrent', AsmT) >= 0);
end;

procedure TNativeArcTests.TestX86_ForIn_InterfaceArrayElem_Retained;
var
  AsmT: string;
begin
  { for G in A over an array of interfaces: the loop variable co-owns the
    element's obj, so it is retained (and the old binding released) before
    the pair is copied.  A plain memcpy left the variable's scope-exit
    release to free an object the array still held. }
  AsmT := GenAsm(
    '''
    program P;
    type
      IG = interface
        function Greet: Int64;
      end;
    procedure Run;
    var
      A: array of IG;
      G: IG;
    begin
      for G in A do
        WriteLn(G.Greet());
    end;
    begin
    end.
    ''', TargetX86_64);
  AssertTrue('element obj retained, old binding released, then copied',
    Pos(#9'movq (%rbx), %rdi'#10#9'callq _ClassAddRef'#10#9'movq (%r15), %rdi'#10 +
        #9'callq _ClassRelease', AsmT) >= 0);
end;

{ Slice the main-body EPILOGUE — everything from the .Lmain_exitN label to the
  end of main.  Slicing the whole of main would be useless: the body itself
  emits _ClassRelease/_StringRelease for ordinary assignments and transients,
  so a whole-main assertion passes vacuously whether or not the exit cleanup
  exists.  The global ARC releases are emitted only after the exit label. }
function TNativeArcTests.MainExitRegion(const AAsm: string): string;
var
  StartP, EndP, MainP: Integer;
  Tail: string;
begin
  MainP := Pos('main:', AAsm);
  AssertTrue('main present in asm', MainP >= 0);
  Tail := StrCopyTail(AAsm, MainP);
  EndP := StrPos('.type main', Tail);
  AssertTrue('main closed', EndP >= 0);
  Tail := StrCopyFrom(AAsm, MainP, EndP);
  StartP := Pos('.Lmain_exit', Tail);
  AssertTrue('main exit label present', StartP >= 0);
  Result := StrCopyTail(Tail, StartP);
end;

const
  SrcProgArrayOfClass = '''
    program P;
    type
      TObjX = class
      public
        Tag: Integer;
      end;
    var
      A: array[0..2] of TObjX;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := TObjX.Create();
      WriteLn(A[2].Tag);
    end.
    ''';

  SrcProgArrayOfString = '''
    program P;
    var
      A: array[0..2] of string;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := 'x';
      WriteLn(A[2]);
    end.
    ''';

  SrcProgArrayOfRecord = '''
    program P;
    type
      TRecX = record
        Name: string;
      end;
    var
      A: array[0..2] of TRecX;
    begin
      A[0].Name := 'x';
      WriteLn(A[0].Name);
    end.
    ''';

  SrcProgArrayOfInteger = '''
    program P;
    var
      A: array[0..2] of Integer;
    begin
      A[0] := 7;
      WriteLn(A[0]);
    end.
    ''';

  SrcProgClassGlobal = '''
    program P;
    type
      TObjX = class
      public
        Tag: Integer;
      end;
    var
      G: TObjX;
    begin
      G := TObjX.Create();
      WriteLn(G.Tag);
    end.
    ''';

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfClass_EmitsClassRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(GenAsm(SrcProgArrayOfClass, TargetX86_64));
  AssertTrue('main releases the program-level array elements, got: ' + Region,
    Pos('_ClassRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfString_EmitsStringRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(GenAsm(SrcProgArrayOfString, TargetX86_64));
  AssertTrue('main releases the program-level string array elements',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfRecord_EmitsStringRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(GenAsm(SrcProgArrayOfRecord, TargetX86_64));
  AssertTrue('main recurses into record elements'' managed fields',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfInteger_NoReleases;
var
  Region: string;
begin
  Region := Self.MainExitRegion(GenAsm(SrcProgArrayOfInteger, TargetX86_64));
  AssertTrue('unmanaged element type emits no release walk',
    (Pos('_ClassRelease', Region) < 0) and (Pos('_StringRelease', Region) < 0));
end;

procedure TNativeArcTests.TestMain_ProgramClassGlobal_EmitsClassRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(GenAsm(SrcProgClassGlobal, TargetX86_64));
  AssertTrue('scalar class global still released at main exit',
    Pos('_ClassRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_RecordCopy_StaticArrayOfStringOnly_EmitsRetain;
var
  Asm_: string;
begin
  { The copy `B := A` is the only statement, so a retain anywhere in the
    output can only come from the ARC record-copy path (the scope-exit walk
    emits releases only). }
  Asm_ := GenAsm(
    '''
    program P;
    type
      TR = record
        Arr: array[0..1] of string;
      end;
    var
      A, B: TR;
    begin
      B := A;
      WriteLn(1);
    end.
    ''', TargetX86_64);
  AssertTrue('record copy retains static-array-of-string elements',
    Pos('_StringAddRef', Asm_) >= 0);
end;

procedure TNativeArcTests.TestMain_DiscardedRecordCall_ReleasesElements;
var
  Asm_, MainR: string;
  P, E: Integer;
begin
  Asm_ := GenAsm(
    '''
    program P;
    type
      TR = record
        Names: array[0..1] of string;
      end;
    function Make(): TR;
    begin
      Result.Names[0] := 'x';
    end;
    begin
      Make();
    end.
    ''', TargetX86_64);
  { Slice main only: Make's own body also emits _StringRelease (element-store
    old-value release), so a whole-asm assertion would pass vacuously. }
  P := Pos('main:', Asm_);
  AssertTrue('main present', P >= 0);
  MainR := StrCopyTail(Asm_, P);
  E := StrPos('.type main', MainR);
  AssertTrue('main closed', E >= 0);
  MainR := Copy(MainR, 0, E);
  AssertTrue('discarded record result''s elements are released in main',
    Pos('_StringRelease', MainR) >= 0);
end;

procedure TNativeArcTests.TestOwnedMethodReceiver_Released;
const
  Src = '''
    program P;
    type
      TL = class
        procedure Hello();
        function Num(): Integer;
        destructor Destroy(); override;
      end;
    var Frees: Integer;
    procedure TL.Hello(); begin WriteLn('hi') end;
    function TL.Num(): Integer; begin Result := 5 end;
    destructor TL.Destroy(); begin Frees := Frees + 1; inherited Destroy() end;
    function MakeL(): TL; begin Result := TL.Create() end;
    begin
      MakeL().Hello();
      MakeL().Num();
      WriteLn(MakeL().Num());
      WriteLn('frees ', Frees)
    end.
    ''';
begin
  AssertEquals('the owned receiver is parked for release', '',
    AsmMissing(Src, #9'movq %rax, _pendrel_0(%rip)',
      #9'bl _MakeL' + #10 + #9'str x0, [sp, #-16]!' + #10 +
        #9'str x0, [sp, #-16]!'));
end;

procedure TNativeArcTests.TestAddrOfOwnedTransientField_ReleasedAtStatementEnd;
const
  Src = '''
    program P;
    type TObj = class N: Integer; end;
    var Q: ^Integer;
    function MakeObj(): TObj; begin Result := TObj.Create() end;
    begin
      Q := @MakeObj().N;
    end.
    ''';
begin
  AssertEquals('the owned base is parked for the statement end', '',
    AsmMissing(Src, #9'callq MakeObj' + #10 + #9'movq %rax, _pendrel_0(%rip)',
      #9'bl _MakeObj' + #10 + #9'stur x0, [x29, #-'));
end;

procedure TNativeArcTests.TestFieldStoreOwnedReceiver_Released;
const
  Src = '''
    program P;
    type TObj = class N: Integer; end;
    function MakeObj(): TObj; begin Result := TObj.Create() end;
    begin
      MakeObj().N := 5;
    end.
    ''';
begin
  AssertEquals('the owned receiver is parked for the statement end', '',
    AsmMissing(Src, #9'callq MakeObj' + #10 + #9'addq $8, %rsp' + #10 +
        #9'movq %rax, _pendrel_0(%rip)',
      #9'bl _MakeObj'));
end;

procedure TNativeArcTests.TestCall_TenOwnedTransientArgs_Lowered;
const
  Src = '''
    program P;
    uses SysUtils;
    function A(I: Integer): string; begin Result := 'a' + IntToStr(I) end;
    function O(I: Integer): TObject; begin Result := TObject.Create() end;
    procedure Ten(const S0, S1, S2, S3, S4, S5, S6, S7, S8, S9: string);
    begin WriteLn(S0, S9) end;
    procedure TenO(O0, O1, O2, O3, O4, O5, O6, O7, O8, O9: TObject);
    begin WriteLn(O9 <> nil) end;
    begin
      Ten(A(0), A(1), A(2), A(3), A(4), A(5), A(6), A(7), A(8), A(9));
      TenO(O(0), O(1), O(2), O(3), O(4), O(5), O(6), O(7), O(8), O(9))
    end.
    ''';
begin
  AssertEquals('ten owned string transient args', '',
    AsmMissing(Src, #9'callq Ten'#10, #9'bl _Ten'#10));
  AssertEquals('ten owned class transient args', '',
    AsmMissing(Src, #9'callq TenO'#10, #9'bl _TenO'#10));
end;

procedure TNativeArcTests.TestCall_OwnedClassTransientArg_ReleasedAfterCall;
const
  Src = '''
    program P;
    function O(I: Integer): TObject; begin Result := TObject.Create() end;
    procedure One(O0: TObject); begin WriteLn(O0 <> nil) end;
    begin
      One(O(1))
    end.
    ''';
begin
  AssertEquals('the transient is released after the call', '',
    AsmMissing(Src,
      #9'callq One'#10#9'addq $8, %rsp'#10#9'subq $40, %rsp',
      #9'bl _One'#10#9'stp x0, x1, [sp, #-16]!'));
  AssertEquals('by _ClassRelease', '',
    AsmMissing(Src, #9'movq 40(%rsp), %rdi'#10#9'callq _ClassRelease',
      #9'bl __ClassRelease'));
end;

const
  SrcOwnedClassTests = '''
    program P;
    function MkO: TObject; begin Result := TObject.Create() end;
    begin
      WriteLn(MkO() <> nil);
      WriteLn(MkO() is TObject);
      WriteLn(Assigned(MkO()))
    end.
    ''';

procedure TNativeArcTests.TestOwnedClassTest_ReleasedAfterCompare;
begin
  AssertEquals('MkO() <> nil releases the object', '',
    AsmMissing(SrcOwnedClassTests,
      #9'cmpq 8(%rsp), %rax'#10#9'setne %al'#10#9'movzbl %al, %eax'#10 +
        #9'movq %rax, 16(%rsp)'#10#9'movq (%rsp), %rdi'#10#9'callq _ClassRelease',
      #9'cmp x0, x1'#10#9'cset x0, ne'#10#9'str x0, [sp, #-16]!'#10 +
        #9'ldr x0, [sp, #32]'#10#9'bl __ClassRelease'));
end;

procedure TNativeArcTests.TestOwnedClassTest_ReleasedAfterIsAndAssigned;
begin
  AssertEquals('MkO() is TObject releases the object', '',
    AsmMissing(SrcOwnedClassTests,
      #9'callq _IsInstance'#10#9'movq %rax, 8(%rsp)'#10#9'movq (%rsp), %rdi'#10 +
        #9'callq _ClassRelease',
      #9'bl __IsInstance'#10#9'ldr x1, [sp]'#10#9'str x0, [sp]'#10 +
        #9'mov x0, x1'#10#9'bl __ClassRelease'));
  AssertEquals('Assigned(MkO()) releases the object', '',
    AsmMissing(SrcOwnedClassTests,
      #9'testq %rax, %rax'#10#9'setne %al'#10#9'movzbl %al, %eax'#10 +
        #9'movq %rax, 8(%rsp)'#10#9'movq (%rsp), %rdi'#10#9'callq _ClassRelease',
      #9'cmp x0, #0'#10#9'cset x0, ne'#10#9'ldr x1, [sp]'#10#9'str x0, [sp]'));
end;

procedure TNativeArcTests.TestRecordCallFieldRead_PinsThenReleasesTemp;
const
  Src = '''
    program P;
    type TT = record K: Integer; V: string; end;
    function F(N: Integer): TT;
    begin
      Result.K := N;
      Result.V := 'v'
    end;
    begin
      WriteLn(F(1).V);
      WriteLn(F(2).K)
    end.
    ''';
begin
  AssertEquals('the field is pinned, then the temp dismantled', '',
    AsmMissing(Src,
      #9'callq _StringAddRef' + #10 + #9'pushq %rbx' + #10 +
        #9'leaq 24(%rsp), %rbx',
      #9'bl __StringAddRef' + #10 + #9'ldp x0, x1, [sp], #16'));
end;

procedure TNativeArcTests.TestPendRel_SlotReNilledAfterFlush;
const
  Src = '''
    program P;
    type
      TB = class V: Integer; end;
      TA = class
        B: TB;
        constructor Create();
        destructor Destroy(); override;
      end;
    var Frees: Integer;
    constructor TA.Create();
    begin
      B := TB.Create();
      B.V := 7
    end;
    destructor TA.Destroy();
    begin
      Frees := Frees + 1;
      inherited Destroy()
    end;
    function MakeA(): TA;
    begin
      Result := TA.Create()
    end;
    procedure Spoil();
    var A, B, C, D, E, F, G, H: Int64;
    begin
      A := -1; B := -1; C := -1; D := -1; E := -1; F := -1; G := -1; H := -1;
      if A + B + C + D + E + F + G + H = 0 then WriteLn('x')
    end;
    procedure Run(First: Boolean);
    var I, Hits: Integer;
    begin
      Hits := 0;
      for I := 0 to 5 do
        if ((First and (I > 2)) or (not First and (I < 3))) and
           (MakeA().B.V = 7) then
          Hits := Hits + 1;
      WriteLn(Hits, ' ', Frees)
    end;
    begin
      Spoil();
      Run(True);
      Frees := 0;
      Spoil();
      Run(False)
    end.
    ''';
begin
  AssertEquals('the flushed slot is re-nilled', '',
    AsmMissing(Src,
      #9'callq _ClassRelease' + #10 + #9'addq $8, %rsp' + #10 + #9'movq $0, -',
      #9'bl __ClassRelease' + #10 + #9'stur xzr, [x29, #-'));
end;

procedure TNativeArcTests.TestMain_DiscardedInterfaceCall_ReleasesObj;
var
  Asm_, MainR: string;
  P, E: Integer;
begin
  Asm_ := GenAsm(
    '''
    program P;
    type
      IGreet = interface
        function Hi(): Integer;
      end;
      TG = class(TObject, IGreet)
      public
        function Hi(): Integer;
      end;
    function TG.Hi(): Integer;
    begin
      Result := 1;
    end;
    function MakeI(): IGreet;
    begin
      Result := TG.Create();
    end;
    begin
      MakeI();
    end.
    ''', TargetX86_64);
  P := Pos('main:', Asm_);
  AssertTrue('main present', P >= 0);
  MainR := StrCopyTail(Asm_, P);
  E := StrPos('.type main', MainR);
  AssertTrue('main closed', E >= 0);
  MainR := Copy(MainR, 0, E);
  AssertTrue('discarded interface result''s obj half is released in main',
    Pos('_ClassRelease', MainR) >= 0);
end;

procedure TNativeArcTests.TestFunc_DynArrayValueParam_RetainedAndReleased;
var
  Asm_, FnR: string;
  P, E: Integer;
begin
  Asm_ := GenAsm(
    '''
    program P;
    type
      TA = array of Integer;
    function SumV(A: TA): Integer;
    begin
      Result := Length(A);
    end;
    var
      X: TA;
    begin
      SetLength(X, 2);
      WriteLn(SumV(X));
    end.
    ''', TargetX86_64);
  { Slice SumV only — main has its own scope-exit _DynArrayRelease for X. }
  P := Pos('SumV:', Asm_);
  AssertTrue('SumV present', P >= 0);
  FnR := StrCopyTail(Asm_, P);
  E := StrPos('.type SumV', FnR);
  AssertTrue('SumV closed', E >= 0);
  FnR := Copy(FnR, 0, E);
  AssertTrue('by-value dyn-array param retained on entry',
    Pos('_DynArrayAddRef', FnR) >= 0);
  AssertTrue('by-value dyn-array param released at exit',
    Pos('_DynArrayRelease', FnR) >= 0);
end;

procedure TNativeArcTests.TestMain_PropSetterConcatValue_DisposedAfterCall;
var
  Asm_, Tail: string;
  P, E: Integer;
begin
  Asm_ := GenAsm(
    '''
    program P;
    type
      TBox = class
      private
        FCur: string;
        procedure SetCur(AValue: string);
      public
        property Cur: string read FCur write SetCur;
      end;
    procedure TBox.SetCur(AValue: string);
    begin
      FCur := AValue;
    end;
    var
      B: TBox;
      A1, A2: string;
    begin
      B := TBox.Create();
      A1 := 'x';
      A2 := 'y';
      B.Cur := A1 + A2;
    end.
    ''', TargetX86_64);
  { The rc=0 concat transient must be pinned (AddRef) BEFORE the setter
    call — a by-value setter param's entry/exit cycle would otherwise free
    it during the call — and released after it. }
  P := Pos('main:', Asm_);
  AssertTrue('main present', P >= 0);
  Tail := StrCopyTail(Asm_, P);
  E := StrPos('.type main', Tail);
  AssertTrue('main closed', E >= 0);
  Tail := Copy(Tail, 0, E);
  P := Pos('_StringConcat', Tail);
  AssertTrue('concat present in main', P >= 0);
  Tail := StrCopyTail(Tail, P);
  E := Pos('callq TBox_SetCur', Tail);
  AssertTrue('setter call present in main', E >= 0);
  AssertTrue('rc=0 pin AddRef BEFORE the setter call',
    (Pos('_StringAddRef', Tail) >= 0) and (Pos('_StringAddRef', Tail) < E));
  Tail := StrCopyTail(Tail, E);
  AssertTrue('release after setter call',
    Pos('_StringRelease', Tail) >= 0);
end;

procedure TNativeArcTests.TestFieldStore_UnretainedThroughCast_NoArc;
const
  Src = '''
    program P;
    type
      TT = class end;
      TBase = class public [Unretained] F: TT; end;
      TSub = class(TBase) G: Integer; end;
    procedure ViaCast(AObj: TObject; V: TT);
    begin
      TSub(AObj).F := V
    end;
    begin
    end.
    ''';

  function ReleasesIn(const AAsm, ALabel: string): Integer;
  var
    P, E, Q: Integer;
  begin
    { _ClassRelease calls between the routine's label and its first ret --
      only the two by-value parameters' own releases belong there }
    Result := 0;
    P := Pos(#10 + ALabel + ':', AAsm);
    if P < 0 then Exit(-1);
    E := PosEx(#9'ret', AAsm, P);
    Q := PosEx('ClassRelease', AAsm, P);
    while (Q >= 0) and (Q < E) do
    begin
      Inc(Result);
      Q := PosEx('ClassRelease', AAsm, Q + 1);
    end;
  end;

begin
  AssertEquals('x86-64: only the parameters are released', 2,
    ReleasesIn(GenAsm(Src, TargetX86_64), 'ViaCast'));
  AssertEquals('arm64: only the parameters are released', 2,
    ReleasesIn(GenAsm(Src, TargetArm64), '_ViaCast'));
end;

const
  SrcOwnedClassToIntf = '''
    program P;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        function Val: Integer;
      end;
    function TThing.Val: Integer; begin Result := 1 end;
    function MkT: TThing; begin Result := TThing.Create() end;
    function Use(T: IThing): Integer; begin Result := T.Val() end;
    var T: IThing;
    begin
      T := MkT();
      WriteLn(Use(MkT()))
    end.
    ''';

procedure TNativeArcTests.TestOwnedClassToInterface_StoreConsumes;
begin
  AssertEquals('T := MkT() stores the +1 without a second retain', '',
    AsmMissing(SrcOwnedClassToIntf,
      #9'callq MkT'#10#9'pushq %rax'#10#9'movq T_obj(%rip), %rdi',
      #9'add x1, x1, _itab_TThing_IThing@PAGEOFF'#10 +
        #9'stp x0, x1, [sp, #-16]!'#10#9'adrp x9, _g_T@PAGE'));
end;

procedure TNativeArcTests.TestOwnedClassToInterface_ArgPassesItab;
begin
  AssertEquals('Use(MkT()) parks obj + itab for the call', '',
    AsmMissing(SrcOwnedClassToIntf,
      #9'callq MkT'#10#9'leaq itab_TThing_IThing(%rip), %rcx'#10 +
        #9'pushq %rcx'#10#9'pushq %rax',
      #9'bl _MkT'#10#9'adrp x1, _itab_TThing_IThing@PAGE'#10 +
        #9'add x1, x1, _itab_TThing_IThing@PAGEOFF'#10#9'str x1, [sp, #-16]!'));
end;

const
  SrcOwnedDynArray = '''
    program P;
    type
      TIntArr = array of Integer;
    function MakeArr: TIntArr; begin SetLength(Result, 2) end;
    function MakeStr: string; begin Result := 'ab' end;
    procedure UseConst(const A: TIntArr); begin end;
    var N: Integer;
    begin
      UseConst(MakeArr());
      N := Length(MakeArr());
      MakeStr()
    end.
    ''';

procedure TNativeArcTests.TestOwnedDynArrayArg_ReleasedAfterCall;
begin
  AssertEquals('UseConst(MakeArr()) releases the array after the call', '',
    AsmMissing(SrcOwnedDynArray,
      #9'callq _DynArrayRelease'#10#9'movq 0(%rsp), %rax'#10 +
        #9'movq 8(%rsp), %rdx',
      #9'bl __DynArrayRelease'#10#9'ldp d2, d3, [sp], #16'));
end;

procedure TNativeArcTests.TestOwnedDynArrayLength_Released;
begin
  AssertEquals('Length(MakeArr()) releases the array', '',
    AsmMissing(SrcOwnedDynArray,
      #9'callq _DynArrayLength'#10 +
        #9'movq %rax, (%rsp)'#10#9'movq 8(%rsp), %rdi'#10 +
        #9'callq _DynArrayRelease',
      #9'bl __DynArrayLength'#10#9'ldr x1, [sp]'#10 +
        #9'str x0, [sp]'#10 +
        #9'mov x0, x1'#10#9'bl __DynArrayRelease'));
end;

procedure TNativeArcTests.TestDiscardedStringResult_Released;
begin
  AssertEquals('MakeStr(); releases the discarded result', '',
    AsmMissing(SrcOwnedDynArray,
      #9'callq MakeStr'#10#9'movq %rax, %rdi'#10#9'callq _StringRelease',
      #9'bl _MakeStr'#10#9'bl __StringRelease'));
end;

const
  SrcOwnedCorners = '''
    program P;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        function Val: Integer;
        procedure Go;
      end;
    function TThing.Val: Integer; begin Result := 3 end;
    procedure TThing.Go; begin end;
    function MkObj: TObject; begin Result := TThing.Create() end;
    function MkI: IThing; begin Result := TThing.Create() end;
    function MkS: string; begin Result := 'ab' end;
    var B: Boolean; N: Integer; [Weak] WI: IThing;
    begin
      B := Supports(MkObj(), IThing);
      N := OrdAt(MkS(), 1);
      TThing.Create().Go();
      WI := MkI()
    end.
    ''';

procedure TNativeArcTests.TestOwnedTransient_SupportsReleasesObject;
begin
  AssertEquals('Supports(MkObj(), IThing) releases the object', '',
    AsmMissing(SrcOwnedCorners,
      #9'callq _ImplementsInterface'#10#9'movq %rax, (%rsp)'#10 +
        #9'movq 8(%rsp), %rdi'#10#9'callq _ClassRelease',
      #9'bl __GetItab'#10#9'cmp x0, #0'#10#9'cset x0, ne'#10 +
        #9'ldr x1, [sp]'#10#9'str x0, [sp]'#10#9'mov x0, x1'#10 +
        #9'bl __ClassRelease'));
end;

procedure TNativeArcTests.TestOwnedTransient_OrdAtReleasesString;
begin
  AssertEquals('OrdAt(MkS(), 1) releases the string', '',
    AsmMissing(SrcOwnedCorners,
      #9'callq _OrdAt'#10#9'movq %rax, (%rsp)'#10#9'movq 8(%rsp), %rdi'#10 +
        #9'callq _StringRelease',
      #9'bl __OrdAt'#10#9'ldr x1, [sp]'#10#9'str x0, [sp]'#10 +
        #9'mov x0, x1'#10#9'bl __StringRelease'));
end;

procedure TNativeArcTests.TestCtorResult_OwnedAtAllocation;
begin
  { a constructor call takes its owned reference right after allocation,
    before the body runs (BUG-20261020-thread-exit-flaky-segv); the
    receiver of TThing.Create().Go() is then an ordinary owned transient,
    with no pin of a refcount-0 instance }
  AssertEquals('the fresh instance is retained once allocated', '',
    AsmMissing(SrcOwnedCorners,
      #9'movq %rcx, (%rax)'#10#9'pushq %rax'#10#9'movq %rax, %rdi'#10 +
        #9'callq _ClassAddRef'#10#9'popq %rax',
      #9'str x9, [x0]'#10#9'str x0, [sp, #-16]!'#10#9'bl __ClassAddRef'));
end;

procedure TNativeArcTests.TestRaise_BorrowedOperandRetained;
const
  Src = '''
    program P;
    type EFoo = class end;
    var E: EFoo;
    begin
      E := EFoo.Create();
      raise E
    end.
    ''';
begin
  AssertEquals('the borrowed operand is retained before _Raise', '',
    AsmMissing(Src,
      #9'callq _ClassAddRef'#10#9'addq $8, %rsp'#10#9'popq %rax'#10 +
        #9'movq %rax, %rdi'#10#9'callq _Raise',
      #9'bl __ClassAddRef'#10#9'ldr x0, [sp], #16'#10#9'bl __Raise'));
end;

procedure TNativeArcTests.TestOwnedIntoRecordVarField_NoRetain;
const
  Src = '''
    program P;
    type
      TN = class end;
      TRec = record O: TN; end;
    function MkN(): TN; begin Result := TN.Create() end;
    procedure SetVar(var R: TRec); begin R.O := MkN() end;
    var G: TRec;
    begin
      SetVar(G)
    end.
    ''';
begin
  AssertEquals('the owned result moves straight in', '',
    AsmMissing(Src,
      #9'callq MkN'#10#9'pushq %rax'#10#9'movq -8(%rbp), %rcx'#10 +
        #9'movq 0(%rcx), %rdi'#10#9'pushq %rcx'#10#9'callq _ClassRelease',
      #9'bl _MkN'));
end;

procedure TNativeArcTests.TestOwnedIntoWeakInterface_Released;
begin
  AssertEquals('[Weak] WI := MkI() registers, then releases the +1', '',
    AsmMissing(SrcOwnedCorners,
      #9'callq _WeakAssign'#10#9'addq $8, %rsp'#10#9'popq %rdi'#10 +
        #9'callq _ClassRelease',
      #9'bl __WeakAssign'#10#9'ldp x0, x1, [sp], #16'#10#9'bl __ClassRelease'));
end;

procedure TNativeArcTests.TestIntfCallOperand_SretAndReleased;
const
  Src = '''
    program P;
    type
      IFoo = interface function Get: Integer; end;
      TObj = class
        FV: IFoo;
        function GetP(I: Integer): IFoo;
      end;
    function TObj.GetP(I: Integer): IFoo; begin Result := FV end;
    var G: TObj;
    begin
      G := TObj.Create();
      if G.GetP(0) = nil then WriteLn(0)
    end.
    ''';
begin
  AssertEquals('GetP(0) = nil: sret call, obj deferred for release', '',
    AsmMissing(Src,
      #9'movq %rsp, %rdi'#10#9'callq TObj_GetP'#10#9'movq (%rsp), %rax'#10 +
        #9'addq $16, %rsp'#10#9'movq %rax, _pendrel_0(%rip)',
      #9'bl _TObj_GetP'#10#9'sub x9, x29, #16'#10#9'ldp x0, x1, [x9]'#10 +
        #9'stur x0, [x29, #'));
end;

procedure TNativeArcTests.TestIntfFromOwnedReceiver_Released;
const
  Src = '''
    program P;
    type
      IFoo = interface function Get: Integer; end;
      TObj = class
        FV: IFoo;
        function GetP(I: Integer): IFoo;
      end;
    function TObj.GetP(I: Integer): IFoo; begin Result := FV end;
    var G: TObj; L: IFoo;
    function MkObj: TObj; begin Result := G end;
    begin
      L := MkObj().GetP(0);
      L := MkObj().FV
    end.
    ''';
begin
  AssertEquals('MkObj().GetP(0): receiver deferred for release', '',
    AsmMissing(Src,
      #9'movq %rax, _pendrel_0(%rip)'#10#9'movq %rax, %r10',
      #9'bl _MkObj'#10#9'stur x0, [x29, #'));
  AssertEquals('MkObj().FV: receiver deferred for release', '',
    AsmMissing(Src,
      #9'movq %rax, _pendrel_0(%rip)'#10#9'addq $8, %rax',
      #9'bl _MkObj'#10#9'stur x0, [x29, #'));
end;

procedure TNativeArcTests.TestNative_OwnedTransientBases_DeferredPastEightSlots;
const
  Src = '''
    program P;
    type
      TArr = array[0..3] of Integer;
      TObj = class Arr: TArr; S: string; end;
    function MkObj: TObj; begin Result := TObj.Create(); end;
    var X: Integer; S: string;
    begin
      X := MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] +
           MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1];
      S := MkObj().S;
    end.
    ''';
var
  A: string;
begin
  { ten owned transients in one statement: the deferred-release pool grows
    past its 8 reserved slots ($main's .bss block on x86-64; arm64 refused
    the ninth), and a STRING field read defers the instance's release too
    rather than releasing it under the borrowed value }
  A := GenAsm(Src, TargetX86_64);
  AssertTrue('x86-64: a tenth slot', Pos('_pendrel_9(%rip)', A) >= 0);
  AssertTrue('x86-64: no eleventh', Pos('_pendrel_10', A) < 0);
  AssertTrue('arm64 lowers it', Pos(#9'bl _MkObj', GenAsm(Src, TargetArm64)) >= 0);
end;

initialization
  RegisterTest(TNativeArcTests);

end.
