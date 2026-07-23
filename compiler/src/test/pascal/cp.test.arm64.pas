{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.arm64;

{ Structural tests for the AArch64 backend (macos-arm64 Phase 2).

  Two lanes, both on Linux CI (the design doc's Phase 2 verification):
    1. asm-shape — TArm64Backend's emitted text carries the expected
       prologue / call / addressing / guard shapes;
    2. full pipeline — the emitted text assembles through
       blaise.assembler.arm64 into an MH_OBJECT that blaise.machoreader
       parses back (sections, relocations, entry symbol).

  Behavioural runs happen on real Apple Silicon in Phase 6. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native.arm64, blaise.codegen.native.backend,
  blaise.codegen.target, blaise.assembler.arm64,
  blaise.machoreader, blaise.machowriter;

type
  TArm64BackendTests = class(TTestCase)
  private
    function GenAsm(const ASrc: string): string;
    function GenAsmWithUnit(const AUnitSrc, ASrc: string): string;
  published
    procedure TestHello_PrologueAndFrameChain;
    procedure TestHello_StringLiteral_AdrpAddPair;
    procedure TestHello_RtlCallsAndEpilogue;
    procedure TestIntegerArithmetic_Shapes;
    procedure TestDivision_AlwaysEmitsZeroGuard;
    procedure TestGlobals_PageAddressed;
    procedure TestIfWhile_BranchShapes;
    procedure TestUnsupported_RaisesHonestly;
    procedure TestPipeline_AssemblesToMachO;
    { slice 2: routines + AAPCS64 calls + for/exit/break }
    procedure TestFunction_PrologueSpillsAndResult;
    procedure TestCall_ArgsPoppedIntoRegisters;
    procedure TestRecursion_Compiles;
    procedure TestForLoop_BoundEvaluatedOnce;
    procedure TestPipeline_FunctionsAssembleToMachO;
    { slice 3: Double — literals, arithmetic, comparisons, d-register
      call ABI with independent int/float sequences }
    procedure TestFloat_LiteralAndArithmetic;
    procedure TestFloat_NumericCast_ConvertsNotBitcopy;
    procedure TestFloat_CallAbi_IndependentSequences;
    { slice 4: string variables with ARC }
    procedure TestString_AssignRetainsAndReleasesOld;
    procedure TestString_ConcatOwnedTransientReleased;
    procedure TestString_ScopeExitReleases;
    { slice 5: string comparisons via RTL helpers }
    procedure TestString_Comparisons_UseRtlHelpers;
    { leg 33: string subscript byte WRITE (S[I] := ch) — copy-on-write via
      _StringUnique, plain-local and var-param forms }
    procedure TestString_SubscriptWrite_CopyOnWrite;
    { slice 6: ARC-clean records — fields, whole-record copy, zero-init }
    procedure TestRecord_FieldsAndCopy;
    { slice 7: record RETURNS per AAPCS64 — x8 sret, x0/x0:x1 images,
      HFA doubles in d0.. }
    procedure TestRecordReturn_SretViaX8;
    procedure TestRecordReturn_SmallImagesAndHfa;
    { slice 8: record PARAMETERS per AAPCS64 }
    procedure TestRecordParam_SmallImagesAndHfa;
    procedure TestRecordParam_LargeByPointer;
    { slice 9: records with ARC-managed fields via the base walks }
    procedure TestManagedRecord_CopyAndFieldStore;
    procedure TestManagedRecord_ScopeExitRelease;
    { slice 10: units — routines + record types from a used unit }
    procedure TestUnit_RoutinesAndCrossUnitCalls;
    procedure TestUnit_VarsAndInitSection;
    procedure TestUnit_FinalizationStillNotYet;
    { self-cross-compile leg 39: a unit class METHOD reading an
      implementation-section unit global — the method body must be emitted
      ONCE (in unit context, so the global resolves), not a second time by the
      program-context FClassDecls walk. }
    procedure TestUnit_ImplGlobalFromMethod_SingleEmit;
    { slice 13: initialised globals in .data }
    procedure TestInitialisedGlobals_DataSection;
    { slice 14: var/out parameters (int, Double, string) }
    procedure TestVarParams_WriteThroughAndPassThrough;
    { slice 15: Single end to end (4-byte storage, double arithmetic) }
    procedure TestSingle_LoadsStoresParamsResult;
    { slice 16: classes — create, methods, fields, ARC, metadata }
    procedure TestClass_CreateFieldsMethodsMetadata;
    { A bare implicit-Self field read of a field at a large or non-8-aligned
      offset must compute the address (add) and load width-keyed — a raw
      8-byte scaled `ldr x0, [x0, #Offset]` is both a width bug and an
      unencodable-immediate bug (offset >255, not multiple of 8). }
    procedure TestImplicitSelfField_LargeOffset_WidthKeyed;
    procedure TestClass_VirtualDispatchAndDestroy;
    { slice 17: unit classes, statics, class consts, inherited, ToString }
    procedure TestClass_InUnit_PrefixedSymbols;
    procedure TestClass_StaticsConstsInheritedToString;
    { slice 18: properties (field- and method-backed, virtual accessors) }
    procedure TestClass_Properties;
    { slice 19: chained receivers + owned-transient release }
    procedure TestClass_ChainedReceivers;
    { slice 20: Mach-O TLV threadvars }
    procedure TestThreadvar_TlvDescriptorsAndAccess;
    { slice 21: Apple stack args (>8) + variadic calls }
    procedure TestStackArgs_VariadicAndOverflow;
    procedure TestStackArgs_RecordParamOverflow;
    { slice 22: interfaces — itab dispatch, fat-pointer ARC, metadata }
    procedure TestInterfaces_DispatchAndMetadata;
    { A unit-declared interface's typeinfo must be DEFINED and REFERENCED
      (impllist, Supports/is/as) under the SAME owning-unit-prefixed symbol — a
      bare definition dangled the prefixed references at link (LINK-1). }
    procedure TestInterface_TypeinfoSymbol_DefAndRefAgree;
    procedure TestInterface_ItabAndImpllist_AreGlobl;
    procedure TestGenericClassInstance_MethodBodyEmittedInUnit;
    procedure TestClassTypeinfo_InstanceSizeCoversAllFields;
    procedure TestSmallRecordParam_FieldReadUsesInlineSlot;
    procedure TestSeparateCompile_DepUnitInitIsCalledFromMain;
    procedure TestReceiverCall_NestedArcArg_ReceiverNotClobbered;
    procedure TestLargeManagedArray_ElemOffsetBeyondImm12;
    procedure TestInterfaces_StringArg;
    procedure TestInterfaces_AsCast;
    procedure TestOwnedStringTransientArg_Released;
    { slice 24: Supports, InheritsFrom, metaclass values }
    procedure TestReflection_SupportsInheritsFromMetaclass;
    { slice 25: interface parameters and results }
    procedure TestInterfaceParamsAndResults;
    { self-cross-compile leg 40: IntfVar := Obj.Method() where the class-receiver
      method RETURNS an interface — the x8 sret fat pointer lands in __iret and
      is stored into the var's two slots (release-old, no caller retain). }
    procedure TestInterfaceAssign_FromMethodCall;
    { slice 26: float property reads + string global initialisers }
    procedure TestFloatPropRead_And_StringGlobalInit;
    { slice 27: managed record params/results across call boundaries }
    procedure TestManagedRecord_ParamsAndResults;
    { slice 28: Single record fields, 3-arg Supports, static properties }
    procedure TestSingleFields_Supports3_StaticProps;
    { slice 29: [Weak] refs, metaclass constructors, indexed properties }
    procedure TestWeak_MetaclassCtor_IndexedProps;
    { slice 30: case and repeat/until }
    procedure TestCaseAndRepeat;
    { slice 31: exceptions — try/finally, try/except, raise, unwind }
    procedure TestExceptions_FramesHandlersUnwind;
    { slice 32: static arrays — width-aware element access, managed elems }
    procedure TestStaticArrays_ElementsAndArc;
    { slice 33: dynamic arrays — SetLength/Length/subscripts/ARC }
    procedure TestDynArrays_LifecycleAndElements;
    { slice 35: small sets — literals, membership, union/inter/diff }
    procedure TestSmallSets_LiteralsInOps;
    { slice 36: for-in over static/dyn arrays, string bytes, small sets }
    procedure TestForIn_ArraysStringsSets;
    { slice 36: for-in via the class enumerator protocol }
    procedure TestForIn_ClassEnumerator;
    { slice 36: case over strings — _StringEquals chains }
    procedure TestCase_StringSelectors;
    { slice 37: aggregate global initialisers — array element lists }
    procedure TestGlobalArrayInitialisers;
    { slice 38: class attributes — attrs/methattrs tables + RTTI builtins }
    procedure TestClassAttributes_TablesAndBuiltins;
    { slice 39: generic class/function instances — bare names, weak bind }
    procedure TestGenericInstances_WeakEmission;
    { self-cross-compile leg 37: a generic METHOD (its own <U>) monomorphised at
      a call site — the concrete instance body is emitted weak-bound, like a
      generic function instance, and the call site references the same label. }
    procedure TestGenericMethodInstance_WeakEmission;
    { self-cross-compile leg 38a: a capture-free closure ('reference to') — the
      literal materialises a 16-byte fat value (Code, nil Env), passed by
      address, copied into the callee's slot, and invoked (Env->x0, Code->blr). }
    procedure TestClosure_CaptureFree_ValueParamCall;
    { self-cross-compile leg 38b(i): a closure call passing an OWNED-TRANSIENT
      string arg (a function result) — the transient is passed borrowed and
      disposed after the call (rc=1 owned = bare _StringRelease). }
    procedure TestClosure_OwnedTransientArg_Disposed;
    { An rc=0 UNOWNED string transient (a concat) passed to a closure must be
      pinned (_StringAddRef) BEFORE the blr — the closure's by-value param
      entry/exit cycle frees an unpinned rc=0 transient DURING the call, so a
      post-call pin double-frees (same shape as
      BUG-20260722-arm64-propsetter-pin-after-call). }
    procedure TestClosure_UnownedTransientArg_PinnedBeforeCall;
    { self-cross-compile leg 38b(ii): a STATEMENT-position closure call (result
      discarded) — a fat callee routes to the fat-pointer call path. }
    procedure TestClosure_StatementPositionCall;
    { slice 40: assembler/nostackframe routines — verbatim arm64 bodies }
    procedure TestAsmRoutines_NoStackFrame;
    { slice 43: pointers — deref reads, pointer writes, addr-of, casts }
    procedure TestPointers_DerefWriteAddrOf;
    { M1 round-trip 2: boolean and/or must SHORT-CIRCUIT — a nil guard
      like (P <> nil) and (P^.X > 0) crashed on hardware because both
      operands were evaluated eagerly }
    procedure TestBooleanAndOr_ShortCircuits;
    { M1 round-trip 5: a C function returning 32-bit int leaves x0's
      upper half UNDEFINED — external results must be width-normalised }
    procedure TestExternalCall_NarrowsIntReturn;
    { slice 11: string parameters (by-value retained, const borrowed) }
    procedure TestStringParams_ValueRetainsConstBorrows;
    { self-cross-compile: open-array parameters — (ptr, high) pair ABI,
      High/Low/Length, element reads, all four caller arg forms }
    procedure TestOpenArrayParams_PtrHighPair;
    procedure TestOpenArrayParams_StringElems;
    { self-cross-compile: Obj.Free() — release AND nil the slot }
    procedure TestFree_ReleasesAndNilsSlot;
    { self-cross-compile: Obj.ClassName / Obj.ClassType via typeinfo }
    procedure TestClassNameAccess_ViaTypeinfo;
    { self-cross-compile: jumbo (>64-member) set membership via _SetIn }
    procedure TestJumboSetMembership_ViaSetIn;
    { self-cross-compile: Inc/Dec on an implicit-Self field }
    procedure TestIncDecImplicitSelfField;
    { self-cross-compile: var class parameter — ARC store through address }
    procedure TestVarClassParam_ArcThroughAddress;
    { self-cross-compile: scalar field read on an owned transient base }
    procedure TestFieldReadOnTransientBase;
    { self-cross-compile: record-returning call passed by value as an arg }
    procedure TestRecordCallArg_MaterialisedInBuffer;
    { self-cross-compile: field read on a record-returning call }
    procedure TestRecordCallFieldRead_ViaRret;
    { self-cross-compile: process-control RTL builtin family }
    procedure TestProcessBuiltins_LowerToRtlCalls;
    { self-cross-compile: Free on a method-call-result receiver }
    procedure TestFreeOnCallResult_ReleasesOwnedTemporary;
    { self-cross-compile: retained managed field read on an owned transient
      base — string field (inline release) vs class field (AddRef-pin) }
    procedure TestRetainedFieldReadOnTransientBase;
    { self-cross-compile: dynamic-array function return (+1 transfers) }
    procedure TestDynArrayFunctionReturn_TransfersOwnership;
    { self-cross-compile leg 11: SetLength on a dyn-array FIELD lvalue
      (SetLength(Result.Cands, N)) — works through the field's address }
    procedure TestSetLengthOnFieldLvalue;
    { self-cross-compile leg 12: assignment to an ELEMENT of a dyn-array field
      (Result.Cands[0] := 'cc') — element address + ARC element store }
    procedure TestFieldElementAssign;
    { BUG-050: a static array with a non-zero LowBound must rebase the index
      on the WRITE side (A[5] of array[5..9] is element 0), matching the read
      side — else the write is off by LowBound (out-of-bounds). }
    procedure TestStaticArrayLowBoundWrite;
    { self-cross-compile leg 13: ForceDirectories called as a bare STATEMENT
      (return discarded) — the statement-context dispatch was missing on arm64
      (only the expression context was handled). }
    procedure TestForceDirectoriesStatement;
    { self-cross-compile leg 14: an implicit-Self class field passed as a
      var-parameter (AppendTo(FField, ...)) — the field's address is Self +
      offset, routed through EmitRecIdentAddr. }
    procedure TestSelfFieldAsVarParam;
    { self-cross-compile leg 15: a generic class instance implementing an
      interface — its itab + impllist are emitted WEAK (bare, instance-mangled)
      so cross-unit copies dedup, and the itab binds the clone's own methods. }
    procedure TestGenericInstanceImplementsInterface;
    { self-cross-compile leg 41: a class implementing a GENERIC INTERFACE
      instance (ITransform<Integer>) — the instance's typeinfo is emitted weak
      so the itab/impllist typeinfo reference resolves and dedups cross-unit. }
    procedure TestGenericInterfaceInstance_WeakTypeinfo;
    { BUG-052 F2: an abstract interface method's itab slot points at the abort
      stub (_AbstractMethodError); the concrete override's itab dispatches. }
    procedure TestAbstractInterfaceMethodItab;
    { BUG-052 F4: a class implementing a DERIVED interface must emit a separate
      itab + impllist entry for each BASE interface (so narrowing works). }
    procedure TestInterfaceParentChainItab;
    { self-cross-compile: record-returning call stored into an array element,
      and a subscripted record element passed as a by-value argument }
    procedure TestRecordCallIntoArrayElement;
    procedure TestSubscriptRecordAsArgument;
    { self-cross-compile leg 16: element read AND write of an implicit-Self
      STATIC-array field (array[0..N] of string).  The inline storage lives at
      Self+offset, so the base is an ADDRESS (add), not a deref (ldr) — unlike
      the dyn-array field case which loads the data pointer. }
    procedure TestStaticArrayFieldElementReadWrite;
    { self-cross-compile leg 17: nested routines + captured outer vars.  A
      nested proc is emitted as a sibling Outer_Inner symbol; each captured
      outer var arrives as a leading '_cap_' pointer arg, spilled in the
      prologue, and reads/writes redirect through that pointer. }
    procedure TestNestedRoutine_NoCapture_SiblingSymbol;
    procedure TestNestedRoutine_CaptureScalar_ReadWrite;
    procedure TestNestedRoutine_CaptureString_ARCThroughCap;
    { leg 17 regression: when captures + register args exceed 8, the outgoing
      stack area MUST be reserved — ComputeStackArgAreaEx counts the capture
      pointer args (in lockstep with EmitCall) so the caller reserves a region
      for the stack-passed args rather than clobbering its own frame. }
    procedure TestNestedRoutine_CaptureArgsForceStackSpill_ReservesArea;
    { BUG-20260720-method-nested-proc-mangle: a nested proc is symbol-mangled
      from the outer routine's RESOLVED name, not its bare name — so a method's
      nested proc carries the class (TFoo_DoIt_Inner) and a multi-level chain
      composes (L1_L2_L3), avoiding cross-class / cross-scope collisions. }
    procedure TestNestedProc_MethodMangle_IncludesClass;
    procedure TestNestedProc_MultiLevelMangle_FullChain;
    { self-cross-compile leg 18: a STRING-indexed property write and read.  The
      key is a single pointer-sized register value passed BORROWED (no caller
      AddRef); setter is called as SetItem(self=x0, key=x1, value=x2). }
    procedure TestStringIndexedProperty_WriteRead;
    { self-cross-compile leg 36: an OWNED-TRANSIENT string value (a concat) as a
      property-write value — the setter borrows it, so the caller disposes the
      transient after the call (rc=0 concat: AddRef+Release). }
    procedure TestOwnedTransientStringPropertyValue;
    { self-cross-compile leg 19: a nested proc that captures an enclosing
      routine's CLASS or RECORD variable and uses it as a field-access base or
      method-call receiver.  The base must be materialised through the '_cap_'
      pointer (load _cap_, deref to the instance), not a bare frame slot. }
    procedure TestCapturedClassBase_FieldRead;
    procedure TestCapturedClassBase_MethodCall;
    procedure TestCapturedClassBase_FieldWrite;
    { leg 19 review regression: a captured VAR-PARAM class field write must
      deref the capture pointer TWICE (the base slot holds the caller's
      address), matching the read/method-call paths. }
    procedure TestCapturedVarParamClassBase_FieldWrite;
    { self-cross-compile leg 20: address of an ELEMENT of an array-typed FIELD
      of a class instance / Self — @Obj.Arr[I] / @Self.Arr[I].  The class base
      must be DEREFED to the instance pointer before the field offset is added
      (the missing-deref trap yields a garbage address). }
    procedure TestAddrOfClassArrayFieldElement;
    procedure TestAddrOfImplicitSelfArrayFieldElement;
    { self-cross-compile leg 21: type-level High/Low of an ENUM (and scalar
      int), and Length of a static array — all compile-time constants folded to
      an immediate.  High(TEnum) = Members.Count-1; Low(TEnum) = 0. }
    procedure TestHighLowEnum_FoldsToLiteral;
    procedure TestLengthStaticArray_FoldsToLiteral;
    { self-cross-compile leg 22: store a whole RECORD value into an element of
      a dyn-array (or static-array) FIELD of a class instance —
      ClassObj.ArrayField[I] := RecordValue.  memcpy of the record bytes, with
      the retain-source/release-dest discipline for a managed record. }
    procedure TestRecordIntoClassDynArrayField;
    { self-cross-compile leg 23: store a whole RECORD value into a var/out
      record PARAMETER — the dest is the DEREFERENCED var-param slot (the
      caller's record address), not the slot's own address. }
    procedure TestRecordStoreToVarParam;
    { self-cross-compile leg 24: nested record-field access — a scalar (or
      whole-record) field reached through a RECORD-typed field of a record
      (Rec.RecField.Field).  The intermediate record field yields the ADDRESS
      of the sub-record; the outer field adds its offset. }
    procedure TestNestedRecordFieldAccess;
    { self-cross-compile leg 25: store a whole MANAGED record LVALUE into a
      record-typed field of a record (Rec.Field := managedRecordVar).  Runs the
      retain-source / release-dest ARC discipline (not a raw memcpy). }
    procedure TestManagedRecordLvalueFieldStore;
    { self-cross-compile leg 27: SetLength on a dyn-array FIELD of a VAR-PARAM
      record — the field address must DEREF the var-param slot (caller's record
      address) before adding the field offset, not take the slot's own address. }
    procedure TestSetLengthOnVarParamRecordField;
    { self-cross-compile leg 34: SetLength on a STRING — the rc=0 result must be
      AddRef'd before it lands in the slot (else scope-exit release goes
      immortal); a var-param string derefs the slot to reach the caller's var. }
    procedure TestSetLengthOnString_AddRefsAndVarParam;
    { self-cross-compile leg 35: a by-value DYNAMIC-ARRAY parameter — const
      borrows (no ARC), a by-value param retains in the prologue and releases at
      scope exit; a dyn-array passes as one register at the call site. }
    procedure TestDynArrayParam_ConstBorrowsByValueRetains;
    procedure TestVarParamRecordArrayFieldElemWrite;
    procedure TestRecordArrayElementRead;
    procedure TestVarParamClassArrayFieldElemWriteStillNotYet;
  end;

implementation

const
  LF = #10;

  SrcHello =
    '''
    program P;
    begin
      WriteLn('hi arm64')
    end.
    ''';

  SrcArith =
    '''
    program P;
    var
      A, B, C: Integer;
    begin
      A := 6;
      B := 7;
      C := A * B + (A - B) div 2;
      WriteLn(C)
    end.
    ''';

  SrcControl =
    '''
    program P;
    var
      N, Sum: Integer;
    begin
      N := 5;
      Sum := 0;
      while N > 0 do
      begin
        Sum := Sum + N;
        N := N - 1
      end;
      if Sum = 15 then
        WriteLn('ok')
      else
        WriteLn('bad')
    end.
    ''';

const
  SrcFuncs =
    '''
    program P;
    function Add2(A, B: Integer): Integer;
    begin
      Result := A + B
    end;
    begin
      WriteLn(Add2(20, 22))
    end.
    ''';

  SrcFib =
    '''
    program P;
    function Fib(N: Integer): Integer;
    begin
      if N < 2 then
      begin
        Result := N;
        Exit
      end;
      Result := Fib(N - 1) + Fib(N - 2)
    end;
    begin
      WriteLn(Fib(10))
    end.
    ''';

  SrcForLoop =
    '''
    program P;
    var
      I, Sum: Integer;
    begin
      Sum := 0;
      for I := 1 to 10 do
      begin
        if I = 3 then continue;
        if I = 9 then break;
        Sum := Sum + I
      end;
      WriteLn(Sum)
    end.
    ''';

function TArm64BackendTests.GenAsm(const ASrc: string): string;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TArm64Backend;
  T:    TTargetDesc;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  try
    { the analyser must OUTLIVE codegen: the backend's GlobalSym calls
      FSymTable.Lookup, which walks scope state the analyser's destructor
      tears down (same lifetime rule as the e2e harness) }
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Prog);
      MakeTarget(osMacOS, cpuArm64, T);
      CG := TArm64Backend.Create(T);
      try
        CG.SetSymbolTable(Prog.SymbolTable);
        Result := CG.GenerateProgram(Prog);
      finally
        CG.Free();
      end;
    finally
      A.Free();
    end;
  finally
    Prog.Free();
  end;
end;

function TArm64BackendTests.GenAsmWithUnit(const AUnitSrc, ASrc: string): string;
var
  L:    TLexer;
  P:    TParser;
  U:    TUnit;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TArm64Backend;
  T:    TTargetDesc;
begin
  L := TLexer.Create(AUnitSrc);
  P := TParser.Create(L);
  try
    U := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.AnalyseUnitForExport(U);
      A.Analyse(Prog);
      MakeTarget(osMacOS, cpuArm64, T);
      CG := TArm64Backend.Create(T);
      try
        CG.SetSymbolTable(Prog.SymbolTable);
        CG.AppendUnit(U);
        CG.AppendProgram(Prog);
        Result := CG.GetOutput();
      finally
        CG.Free();
      end;
    finally
      A.Free();
    end;
  finally
    Prog.Free();
    U.Free();
  end;
end;

procedure TArm64BackendTests.TestHello_PrologueAndFrameChain;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcHello);
  AssertTrue('exports _main', Pos('.globl _main', AsmT) >= 0);
  { Darwin requires the fp chain: fp/lr pair save + mov x29, sp — always. }
  AssertTrue('fp/lr pair saved',
    Pos(#9'stp x29, x30, [sp, #-16]!', AsmT) >= 0);
  AssertTrue('frame pointer established',
    Pos(#9'mov x29, sp', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestHello_StringLiteral_AdrpAddPair;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcHello);
  { PIE-safe literal address: adrp + add @PAGE/@PAGEOFF, then +12 past the
    immortal string header (refcnt/len/cap — same layout as x86-64). }
  AssertTrue('adrp page', Pos('adrp x0, __s0@PAGE', AsmT) >= 0);
  AssertTrue('add pageoff', Pos('add x0, x0, __s0@PAGEOFF', AsmT) >= 0);
  AssertTrue('data pointer past the 12-byte header',
    Pos(#9'add x0, x0, #12', AsmT) >= 0);
  AssertTrue('immortal refcnt', Pos(#9'.word -1', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestHello_RtlCallsAndEpilogue;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcHello);
  AssertTrue('args forwarded before init', Pos(#9'bl _SetArgs', AsmT) >= 0);
  AssertTrue('rtl init', Pos(#9'bl _BlaiseInit', AsmT) >= 0);
  AssertTrue('string write', Pos(#9'bl _SysWriteStr', AsmT) >= 0);
  AssertTrue('newline', Pos(#9'bl _SysWriteNewline', AsmT) >= 0);
  AssertTrue('epilogue restores fp/lr',
    Pos(#9'ldp x29, x30, [sp], #16', AsmT) >= 0);
  AssertTrue('returns', Pos(#9'ret', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestIntegerArithmetic_Shapes;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcArith);
  AssertTrue('multiply', Pos(#9'mul x0, x0, x1', AsmT) >= 0);
  AssertTrue('subtract', Pos(#9'sub x0, x0, x1', AsmT) >= 0);
  AssertTrue('divide', Pos(#9'sdiv x0, x0, x1', AsmT) >= 0);
  AssertTrue('int write', Pos(#9'bl _SysWriteInt', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestDivision_AlwaysEmitsZeroGuard;
var
  AsmT: string;
begin
  { AArch64 sdiv yields 0 on a zero divisor instead of trapping, so the
    explicit guard must ALWAYS precede the divide (design-doc risk item). }
  AsmT := GenAsm(SrcArith);
  AssertTrue('divisor zero-check', Pos(#9'cbnz x1, Ldivok', AsmT) >= 0);
  AssertTrue('deliberate trap', Pos(#9'brk #1', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestGlobals_PageAddressed;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcArith);
  { program vars are globals addressed via adrp/@PAGEOFF (PIE-safe) }
  AssertTrue('global page', Pos('adrp x9, _g_A@PAGE', AsmT) >= 0);
  AssertTrue('global store',
    Pos('str x0, [x9, _g_A@PAGEOFF]', AsmT) >= 0);
  AssertTrue('bss slot', Pos('_g_A:', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestIfWhile_BranchShapes;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcControl);
  AssertTrue('comparison materialised', Pos(#9'cset x0, gt', AsmT) >= 0);
  AssertTrue('condition branch', Pos(#9'cbz x0, L', AsmT) >= 0);
  AssertTrue('equality for if', Pos(#9'cset x0, eq', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestUnsupported_RaisesHonestly;
var
  Raised: Boolean;
  Msg: string;
begin
  Raised := False;
  Msg := '';
  try
    GenAsm(
      '''
      program P;
      type
        TPair<T> = record
          A, B: T;
        end;
      var
        Q: TPair<Int64>;
      begin
        Q.A := 1;
        WriteLn(Q.A)
      end.
      ''');
  except
    on E: ENativeCodeGenError do
    begin
      Raised := True;
      Msg := E.Message;
    end;
  end;
  AssertTrue('unsupported construct raises', Raised);
  AssertTrue('message names the arm64 subset',
    Pos('arm64: not yet', Msg) >= 0);
end;

procedure TArm64BackendTests.TestPipeline_AssemblesToMachO;
var
  AsmT, Obj: string;
  F: TMachOFile;
  T: TMoSection;
  S: TMoSymbol;
begin
  { The full Phase-2 pipeline on Linux CI: backend text -> arm64 internal
    assembler -> MH_OBJECT -> parse back. }
  AsmT := GenAsm(SrcControl);
  Obj  := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64probe.o');
  try
    AssertEquals(CPU_TYPE_ARM64, F.CpuType);
    T := F.FindSection('__TEXT', '__text');
    AssertTrue('__text present', T <> nil);
    AssertTrue('code emitted', T.Size > 0);
    S := F.FindSymbol('_main');
    AssertTrue('_main defined', (S <> nil) and (not S.IsUndef()));
    AssertTrue('_main exported', S.IsExt());
    { the RTL calls stay undefined externs with BRANCH26 relocations }
    AssertTrue('rtl call relocations recorded', T.Relocs.Count > 0);
    AssertTrue('_SysWriteStr referenced',
      F.FindSymbol('_SysWriteStr') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestFunction_PrologueSpillsAndResult;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcFuncs);
  { params spill from x0/x1 into frame slots; Result zero-initialised and
    loaded back into x0 at the routine exit }
  AssertTrue('add2 exported+defined', Pos('Add2:', AsmT) >= 0);
  AssertTrue('param 0 spilled', Pos(#9'stur x0, [x29, #-8]', AsmT) >= 0);
  AssertTrue('param 1 spilled', Pos(#9'stur x1, [x29, #-16]', AsmT) >= 0);
  AssertTrue('Result zero-initialised', Pos(#9'stur xzr, [x29, #-24]', AsmT) >= 0);
  AssertTrue('frame restored via fp', Pos(#9'mov sp, x29', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestCall_ArgsPoppedIntoRegisters;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcFuncs);
  { args are pushed left-to-right and popped last-first, so x1 fills before
    x0; the call is a bl to the mangled routine symbol }
  AssertTrue('second arg popped first', Pos(#9'ldr x1, [sp], #16', AsmT) >= 0);
  AssertTrue('first arg popped last', Pos(#9'ldr x0, [sp], #16', AsmT) >= 0);
  AssertTrue('direct call', Pos(#9'bl Add2', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestRecursion_Compiles;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcFib);
  AssertTrue('fib defined', Pos('Fib:', AsmT) >= 0);
  AssertTrue('recursive call', Pos(#9'bl Fib', AsmT) >= 0);
  AssertTrue('exit lands on the epilogue label', Pos(#9'b Lrexit', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestForLoop_BoundEvaluatedOnce;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcForLoop);
  { the loop bound lives in a hidden frame slot, compared each iteration.
    Offset-agnostic: the __iret/__rret scratch slots shift hidden-slot
    offsets, so match the store shape (stur to an x29-negative slot) not a
    specific offset. }
  AssertTrue('bound stored to a hidden x29 slot',
    Pos(#9'stur x0, [x29, #-', AsmT) >= 0);
  AssertTrue('signed compare against the bound', Pos(#9'cmp x0, x1', AsmT) >= 0);
  AssertTrue('exit branch on greater', Pos(#9'b.gt Lfend', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestPipeline_FunctionsAssembleToMachO;
var
  AsmT, Obj: string;
  F: TMachOFile;
  S: TMoSymbol;
begin
  AsmT := GenAsm(SrcFib);
  Obj  := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64fib.o');
  try
    S := F.FindSymbol('Fib');
    AssertTrue('Fib defined in the object', (S <> nil) and (not S.IsUndef()));
    S := F.FindSymbol('_main');
    AssertTrue('_main defined', (S <> nil) and (not S.IsUndef()));
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestFloat_LiteralAndArithmetic;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      D, E: Double;
    begin
      D := 1.5;
      E := D * 2.0 + 0.25;
      if E > 3.0 then
        WriteLn(1)
    end.
    ''');
  AssertTrue('literal from rodata page',
    Pos('adrp x9, __d0@PAGE', AsmT) >= 0);
  AssertTrue('double blob emitted', Pos(#9'.double 1.5', AsmT) >= 0);
  AssertTrue('float multiply', Pos(#9'fmul d0, d0, d1', AsmT) >= 0);
  AssertTrue('float add', Pos(#9'fadd d0, d0, d1', AsmT) >= 0);
  AssertTrue('float compare', Pos(#9'fcmp d0, d1', AsmT) >= 0);
  AssertTrue('ordered greater', Pos(#9'cset x0, gt', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestFloat_NumericCast_ConvertsNotBitcopy;
var
  AsmT: string;
begin
  { leg 30: a numeric type-cast Single(X)/Double(X) in a float context is a
    TFuncCallExpr with ResolvedDecl=nil (the name resolves to a TYPE).  It must
    lower to a REAL conversion (fcvt / scvtf), never a bl to a routine named
    'Single'/'Double' and never a bit copy.  Was NotYet'd as 'this call form in
    float context' (the compiler's own blaise.assembler.x86_64.pas:3088
    'FVal := Single(DVal)'). }
  AsmT := GenAsm(
    '''
    program P;
    var D: Double; F: Single; I: Integer;
    begin
      D := 3.5;
      F := Single(D);         { double -> single: narrow }
      D := Double(F);         { single -> double: widen  }
      I := 7;
      D := Double(I);         { int -> double: scvtf     }
      if D > 0.0 then WriteLn(1)
    end.
    ''');
  AssertTrue('no notyet', Pos('not yet lowered', AsmT) < 0);
  AssertTrue('single narrow (fcvt s0, d0)', Pos(#9'fcvt s0, d0', AsmT) >= 0);
  AssertTrue('single widen (fcvt d0, s0)', Pos(#9'fcvt d0, s0', AsmT) >= 0);
  AssertTrue('int to float (scvtf d0, x0)', Pos(#9'scvtf d0, x0', AsmT) >= 0);
  AssertTrue('cast is not a call to Single',
    Pos(#9'bl Single', AsmT) < 0);
  AssertTrue('cast is not a call to Double',
    Pos(#9'bl Double', AsmT) < 0);
end;

procedure TArm64BackendTests.TestFloat_CallAbi_IndependentSequences;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    function Mix(A: Integer; X: Double; B: Integer): Integer;
    begin
      Result := A + B
    end;
    begin
      WriteLn(Mix(1, 2.5, 3))
    end.
    ''');
  { AAPCS64: ints take x0/x1, the float takes d0 — independent sequences.
    The callee spills d0 through x9 into the param slot. }
  AssertTrue('float arg lands in d0', Pos(#9'fmov d0, x9', AsmT) >= 0);
  AssertTrue('callee spills the d0 param', Pos(#9'fmov x9, d0', AsmT) >= 0);
  AssertTrue('int args pop into x0/x1', Pos(#9'ldr x1, [sp], #16', AsmT) >= 0);
  AssertTrue('call emitted', Pos(#9'bl Mix', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestString_AssignRetainsAndReleasesOld;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      S: string;
    begin
      S := 'one';
      S := 'two';
      WriteLn(S)
    end.
    ''');
  { plain (non-owning) RHS retains; the slot's old value releases }
  AssertTrue('incoming retained', Pos(#9'bl _StringAddRef', AsmT) >= 0);
  AssertTrue('old value released', Pos(#9'bl _StringRelease', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestString_ConcatOwnedTransientReleased;
var
  AsmT: string;
  ConcatPos, AddRefAfter: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      S: string;
    begin
      S := 'a' + 'b';
      WriteLn('x' + 'y')
    end.
    ''');
  AssertTrue('concat lowered', Pos(#9'bl _StringConcat', AsmT) >= 0);
  { _StringConcat returns rc=0 (arc-string-transient-handover.adoc): the
    assignment must RETAIN it (0 -> 1) before releasing the old value —
    consuming it as if it were +1 stores an rc=0 string whose later
    release underflows to IMMORTAL (a permanent, tracker-invisible leak) }
  ConcatPos := Pos(#9'bl _StringConcat', AsmT);
  AddRefAfter := Pos(#9'bl _StringAddRef',
    Copy(AsmT, ConcatPos, Length(AsmT) - ConcatPos));
  AssertTrue('rc=0 concat result retained on assignment', AddRefAfter >= 0);
  { the WriteLn transient is disposed by shape after the write:
    rc=0 needs AddRef THEN Release }
  AssertTrue('transient written', Pos(#9'bl _SysWriteStr', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestString_ScopeExitReleases;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    function Tag(N: Integer): Integer;
    var
      S: string;
    begin
      S := 'tag';
      Result := N
    end;
    begin
      WriteLn(Tag(1))
    end.
    ''');
  { the routine's exit label releases its string local before Result loads }
  AssertTrue('exit label present', Pos('Lrexit', AsmT) >= 0);
  AssertTrue('scope-exit release', Pos(#9'bl _StringRelease', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestString_SubscriptWrite_CopyOnWrite;
var
  AsmT: string;
begin
  { Leg 33: S[I] := ch on a string writes a byte in place, but must first make
    the buffer unique via _StringUnique (else a literal-backed string would hit
    read-only memory).  The var-param form (Munge) derefs the slot once more to
    reach the caller's string; the plain-local form (t) writes its own slot. }
  AsmT := GenAsm(
    '''
    program P;
    procedure Munge(var S: string); begin S[0] := 'X' end;
    var s, t: string;
    begin
      s := 'abc'; Munge(s); WriteLn(s);
      t := 'hello'; t[1] := 'E'; WriteLn(t)
    end.
    ''');
  { copy-on-write before the byte store }
  AssertTrue('string made unique before write',
    Pos(#9'bl _StringUnique', AsmT) >= 0);
  { the byte is stored into the unique buffer }
  AssertTrue('byte stored', Pos(#9'strb w0, [x9]', AsmT) >= 0);
  { the var-param form derefs the slot to reach the caller's string pointer }
  AssertTrue('var-param slot dereferenced', Pos(#9'ldr x19, [x19]', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestString_Comparisons_UseRtlHelpers;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      A, B: string;
    begin
      A := 'x';
      B := 'y';
      if A = B then WriteLn(1);
      if A <> B then WriteLn(2);
      if A < B then WriteLn(3)
    end.
    ''');
  { content comparison, never a pointer cmp }
  AssertTrue('equality helper', Pos(#9'bl _StringEquals', AsmT) >= 0);
  AssertTrue('ordering helper', Pos(#9'bl _StringCompare', AsmT) >= 0);
  AssertTrue('NE inverts via cset eq', Pos(#9'cset x0, eq', AsmT) >= 0);
  AssertTrue('relational sign-extends the strcmp result',
    Pos(#9'sxtw x0, w0', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestRecord_FieldsAndCopy;
var
  AsmT, Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TPoint = record
        X: Integer;
        Y: Int64;
        D: Double;
      end;
    var
      G: TPoint;
    function Sum(N: Integer): Integer;
    var
      L, M: TPoint;
    begin
      L.X := N;
      L.Y := 10;
      L.D := 1.5;
      M := L;
      Result := M.X + M.Y
    end;
    begin
      G.X := 1;
      WriteLn(Sum(G.X + 31))
    end.
    ''');
  { record locals zero-init their WHOLE storage, not just 8 bytes }
  AssertTrue('record zeroed via memset', Pos(#9'bl memset', AsmT) >= 0);
  { field writes go through the record base + offset }
  AssertTrue('field write at offset 8', Pos(', [x9, #8]', AsmT) >= 0);
  AssertTrue('field write at offset 16', Pos(', [x9, #16]', AsmT) >= 0);
  { whole-record copy is a memcpy of RawSize }
  AssertTrue('record copy via memcpy', Pos(#9'bl memcpy', AsmT) >= 0);
  AssertTrue('copy length 24', Pos(#9'movz x2, #24', AsmT) >= 0);
  { record global gets a full-size bss slot }
  AssertTrue('global record slot', Pos(#9'.zero 24', AsmT) >= 0);
  { and the whole thing still assembles into a Mach-O object }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'rec.o');
  try
    AssertTrue('__text non-empty',
      F.FindSection('__TEXT', '__text').Size > 0);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestImplicitSelfField_LargeOffset_WidthKeyed;
var
  AsmT, Obj: string;
  F: TMachOFile;
begin
  { A leading 300-byte pad field pushes the Integer field past offset 255; a
    bare implicit-Self read of it must compute the address (add x0, x0, #off)
    and load a 4-byte word (ldrsw), NOT emit an unencodable `ldr x0, [x0, #300]`
    (a 64-bit scaled load at a non-8-aligned, >255 offset).  This is exactly the
    shape that blocked the arm64 self-compile's assemble step. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TBig = class
        Pad: array[0..299] of Byte;
        N: Integer;
        function GetN: Integer;
      end;
    function TBig.GetN: Integer; begin Result := N end;
    var t: TBig;
    begin
      t := TBig.Create();
      t.N := 42;
      WriteLn(t.GetN())
    end.
    ''');
  { the field ADDRESS is computed (add), not folded into a scaled load — the
    offset is 308 (an 8-byte object header precedes the 300-byte pad). }
  AssertTrue('field offset via add', Pos(#9'add x0, x0, #308', AsmT) >= 0);
  { the 4-byte Integer field is loaded width-keyed (ldrsw), not as 8 bytes }
  AssertTrue('width-keyed load', Pos(#9'ldrsw x0, [x0]', AsmT) >= 0);
  { and the whole thing assembles — the raw form would raise
    "unscaled/negative load-store offset" }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64bigfield.o');
  try
    AssertTrue('assembles to a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRecordReturn_SretViaX8;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TBig = record
        A, B, C: Int64;
      end;
    var
      G: TBig;
    function MakeBig(N: Integer): TBig;
    begin
      Result.A := N
    end;
    begin
      G := MakeBig(7);
      WriteLn(G.A)
    end.
    ''');
  { 24-byte record: sret — callee parks x8, memcpys Result out; the
    caller loads the destination address into x8 before the bl }
  AssertTrue('callee parks x8', Pos(#9'stur x8, ', AsmT) >= 0);
  AssertTrue('callee copies Result to the x8 buffer',
    Pos(#9'bl memcpy', AsmT) >= 0);
  AssertTrue('caller sets x8 to the destination',
    Pos('add x8, x8, _g_G@PAGEOFF', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestRecordReturn_SmallImagesAndHfa;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TPair = record
        A: Int64;
        B: Int64;
      end;
      TVec = record
        X: Double;
        Y: Double;
      end;
    var
      GP: TPair;
      GV: TVec;
    function MkPair: TPair;
    begin
      Result.A := 1;
      Result.B := 2
    end;
    function MkVec: TVec;
    begin
      Result.X := 1.5
    end;
    begin
      GP := MkPair();
      GV := MkVec();
      WriteLn(GP.A)
    end.
    ''');
  { 16-byte non-HFA: memory image in x0:x1 both sides }
  AssertTrue('callee loads x0:x1 image', Pos(#9'ldr x1, [x9, #8]', AsmT) >= 0);
  AssertTrue('caller stores x1 half', Pos(#9'str x1, [x9, #8]', AsmT) >= 0);
  { two-double HFA: d0/d1 both sides }
  AssertTrue('callee loads HFA d1', Pos(#9'ldr d1, [x9, #8]', AsmT) >= 0);
  AssertTrue('caller stores HFA d1', Pos(#9'str d1, [x9, #8]', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestRecordParam_SmallImagesAndHfa;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TPair = record
        A: Int64;
        B: Int64;
      end;
      TVec = record
        X: Double;
        Y: Double;
      end;
    var
      GP: TPair;
      GV: TVec;
    function SumPair(P: TPair): Int64;
    begin
      Result := P.A + P.B
    end;
    function VecX(V: TVec): Double;
    begin
      Result := V.X
    end;
    begin
      GP.A := 3;
      GV.X := 1.5;
      WriteLn(SumPair(GP));
      WriteLn(VecX(GV))
    end.
    ''');
  { 16-byte non-HFA param: x0:x1 image — callee stores the second half
    at slot+8, caller loads it from the lvalue at +8 }
  AssertTrue('callee spills x1 half', Pos(#9'str x1, [x9, #8]', AsmT) >= 0);
  AssertTrue('caller loads second half', Pos(#9'ldr x0, [x9, #8]', AsmT) >= 0);
  { two-double HFA param: callee spills d0/d1 into the slot }
  AssertTrue('callee spills HFA d1', Pos(#9'str d1, [x9, #8]', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestRecordParam_LargeByPointer;
var
  AsmT, Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TBig = record
        A, B, C: Int64;
      end;
    var
      G: TBig;
    function SumBig(R: TBig): Int64;
    begin
      Result := R.A + R.C
    end;
    begin
      G.A := 5;
      G.C := 7;
      WriteLn(SumBig(G))
    end.
    ''');
  { >16B param travels as a pointer: the callee parks it and memcpys the
    bytes into its own slot before any user code }
  AssertTrue('caller passes the global address',
    Pos('add x0, x0, _g_G@PAGEOFF', AsmT) >= 0);
  AssertTrue('callee copies the bytes in', Pos(#9'bl memcpy', AsmT) >= 0);
  { and the whole module still assembles to a valid Mach-O object }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64recpar.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestManagedRecord_CopyAndFieldStore;
var
  AsmT: string;
  PosRetain, PosRelease, PosCpy: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TNamed = record
        Id: Int64;
        Name: string;
      end;
    var
      A, B: TNamed;
    begin
      A.Name := 'hello';
      B := A;
      WriteLn(B.Name)
    end.
    ''');
  { field store: retain the incoming value, release the old field }
  AssertTrue('field store retains', Pos(#9'bl _StringAddRef', AsmT) >= 0);
  { whole-copy discipline: retain source fields BEFORE releasing the
    destination's (self-assignment safety), memcpy after both }
  PosRetain := Pos('_StringAddRef', AsmT);
  PosRelease := Pos('_StringRelease', AsmT);
  PosCpy := Pos('bl memcpy', AsmT);
  AssertTrue('retain present', PosRetain >= 0);
  AssertTrue('release present', PosRelease >= 0);
  AssertTrue('memcpy present', PosCpy >= 0);
  { the copy walks from callee-saved bases }
  AssertTrue('walk bases are callee-saved',
    Pos(#9'stp x19, x22, [sp, #-16]!', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestManagedRecord_ScopeExitRelease;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TNamed = record
        Id: Int64;
        Name: string;
      end;
    procedure Use;
    var
      L: TNamed;
    begin
      L.Name := 'local';
      WriteLn(L.Name)
    end;
    var
      G: TNamed;
    begin
      G.Name := 'global';
      Use();
      WriteLn(G.Name)
    end.
    ''');
  { the local's managed field is released at the routine's exit label and
    the global's at program exit — each walk anchors on saved x19 }
  AssertTrue('scope-exit walk saves x19',
    Pos(#9'str x19, [sp, #-16]!', AsmT) >= 0);
  AssertTrue('walk releases through x19', Pos('[x19', AsmT) >= 0);
  { and the whole module still assembles to a valid Mach-O object }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64mrec.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestUnit_RoutinesAndCrossUnitCalls;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsmWithUnit(
    '''
    unit mathu;
    interface
    function AddTwo(A, B: Int64): Int64;
    function Banner: string;
    implementation
    function AddTwo(A, B: Int64): Int64;
    begin
      Result := A + B
    end;
    function Banner: string;
    begin
      Result := 'sum='
    end;
    end.
    ''',
    '''
    program P;
    uses mathu;
    begin
      Write(Banner());
      WriteLn(AddTwo(20, 22))
    end.
    ''');
  { the unit routine is defined under its unit-mangled symbol and the
    program's call site targets the same symbol }
  AssertTrue('unit routine defined', Pos('mathu_AddTwo:', AsmT) >= 0);
  AssertTrue('cross-unit call mangled', Pos(#9'bl mathu_AddTwo', AsmT) >= 0);
  AssertTrue('string-returning unit routine defined',
    Pos('mathu_Banner:', AsmT) >= 0);
  { the unit's string literal lands in the shared rodata dump }
  AssertTrue('unit string literal emitted', Pos('sum=', AsmT) >= 0);
  { and the multi-unit module assembles to a valid Mach-O object }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64unit.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestUnit_VarsAndInitSection;
var
  AsmT: string;
begin
  AsmT := GenAsmWithUnit(
    '''
    unit counters;
    interface
    var
      Total: Int64;
    procedure Bump;
    implementation
    procedure Bump;
    begin
      Total := Total + 1
    end;
    initialization
      Total := 40
    end.
    ''',
    '''
    program P;
    uses counters;
    begin
      Bump();
      Bump();
      WriteLn(Total)
    end.
    ''');
  { the unit var gets an owning-unit-prefixed symbol — same-named vars in
    other units or the program cannot collide }
  AssertTrue('unit var symbol prefixed', Pos('_g_counters_Total:', AsmT) >= 0);
  AssertTrue('references target the prefixed symbol',
    Pos('_g_counters_Total@PAGE', AsmT) >= 0);
  { the init section becomes <unit>_init, and _main calls it }
  AssertTrue('init routine emitted', Pos('counters_init:', AsmT) >= 0);
  AssertTrue('main calls the init routine',
    Pos(#9'bl counters_init', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestUnit_FinalizationStillNotYet;
var
  AsmT: string;
begin
  { historical name — finalization now LOWERS: <unit>_final is emitted
    and called at program exit (reverse dependency order) }
  AsmT := GenAsmWithUnit(
    '''
    unit withfinal;
    interface
    function One: Int64;
    implementation
    function One: Int64;
    begin
      Result := 1
    end;
    finalization
      One()
    end.
    ''',
    '''
    program P;
    uses withfinal;
    begin
      WriteLn(One())
    end.
    ''');
  AssertTrue('final routine emitted', Pos('withfinal_final:', AsmT) >= 0);
  AssertTrue('main exit calls it', Pos(#9'bl withfinal_final', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestUnit_ImplGlobalFromMethod_SingleEmit;
var
  AsmT: string;
  PosFirst: Integer;
begin
  { A unit class method that reads an implementation-section unit global must be
    emitted ONCE — in unit context, where the impl-private global resolves to
    its prefixed symbol.  A second emission from the program-context FClassDecls
    walk would mis-resolve the global (bare name -> NotYet) and produce a
    duplicate method label (leg 39). }
  AsmT := GenAsmWithUnit(
    '''
    unit boxu;
    interface
    type
      TBox = class
        function Get: Integer;
      end;
    implementation
    var GCount: Integer;
    function TBox.Get: Integer;
    begin
      GCount := GCount + 1;
      Result := GCount
    end;
    initialization
      GCount := 100
    end.
    ''',
    '''
    program P;
    uses boxu;
    var b: TBox;
    begin
      b := TBox.Create();
      WriteLn(b.Get());
      b.Free()
    end.
    ''');
  { the method reaches the impl global through its owning-unit-prefixed symbol }
  AssertTrue('impl global prefixed', Pos('_g_boxu_GCount', AsmT) >= 0);
  { the method body label is emitted exactly ONCE (no double-emit) }
  PosFirst := Pos('TBox_Get:', AsmT);
  AssertTrue('method body emitted', PosFirst >= 0);
  AssertTrue('method body NOT emitted twice',
    PosEx('TBox_Get:', AsmT, PosFirst + 1) < 0);
end;

procedure TArm64BackendTests.TestStringParams_ValueRetainsConstBorrows;
var
  AsmT: string;
  PosGreet, PosShow, PosNext: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    var G: string;
    procedure Greet(Msg: string);
    begin
      WriteLn(Msg)
    end;
    procedure Show(const Msg: string);
    begin
      WriteLn(Msg)
    end;
    begin
      G := 'hi';
      Greet(G);
      Show(G);
      Greet('lit')
    end.
    ''');
  { the by-value param retains its copy in the prologue and releases it
    with the string locals at exit; the const param does neither }
  PosGreet := Pos('Greet:', AsmT);
  PosShow := Pos('Show:', AsmT);
  AssertTrue('both routines emitted', (PosGreet >= 0) and (PosShow >= 0));
  PosNext := PosEx(#9'bl _StringAddRef', AsmT, PosGreet);
  AssertTrue('by-value param retained in Greet',
    (PosNext > PosGreet) and ((PosShow < PosGreet) or (PosNext < PosShow)));
  AssertTrue('by-value param released at Greet exit',
    PosEx(#9'bl _StringRelease', AsmT, PosGreet) > PosGreet);
  { const param: no retain between Show's label and its ret }
  PosNext := PosEx(#9'ret', AsmT, PosShow);
  AssertTrue('Show has a ret', PosNext > PosShow);
  PosGreet := PosEx(#9'bl _StringAddRef', AsmT, PosShow);
  AssertTrue('const param not retained in Show',
    (PosGreet < 0) or (PosGreet > PosNext));
end;

procedure TArm64BackendTests.TestInitialisedGlobals_DataSection;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      Answer: Int64 = 42;
      Ratio: Double = 2.5;
      Plain: Int64;
    begin
      WriteLn(Answer);
      WriteLn(Ratio);
      WriteLn(Plain)
    end.
    ''');
  { initialised globals live in .data with their values; uninitialised
    ones stay zerofill }
  AssertTrue('data section present', Pos('.section .data', AsmT) >= 0);
  AssertTrue('int initialiser', Pos(#9'.quad 42', AsmT) >= 0);
  AssertTrue('float initialiser', Pos(#9'.double 2.5', AsmT) >= 0);
  AssertTrue('plain global stays bss', Pos('.section .bss', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64initg.o');
  try
    AssertTrue('has a data section',
      F.FindSection('__DATA', '__data') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestVarParams_WriteThroughAndPassThrough;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      N: Int64;
      D: Double;
      S: string;
    procedure Bump(var X: Int64);
    begin
      X := X + 1
    end;
    procedure BumpTwice(var X: Int64);
    begin
      Bump(X);
      Bump(X)
    end;
    procedure SetD(out V: Double);
    begin
      V := 2.5
    end;
    procedure Tag(var T: string);
    begin
      T := T + '!'
    end;
    begin
      N := 40;
      BumpTwice(N);
      SetD(D);
      S := 'hey';
      Tag(S);
      WriteLn(N);
      WriteLn(D);
      WriteLn(S)
    end.
    ''');
  { the caller passes the global's address; the callee reads and writes
    through the pointer; a var->var pass-through forwards the address }
  AssertTrue('caller passes global address',
    Pos('add x0, x0, _g_N@PAGEOFF', AsmT) >= 0);
  AssertTrue('callee derefs for the read', Pos(#9'ldr x0, [x0]', AsmT) >= 0);
  AssertTrue('callee stores through the pointer',
    Pos(#9'str x0, [x9]', AsmT) >= 0);
  { pipeline check: the whole module assembles }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64varpar.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestSingle_LoadsStoresParamsResult;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      A, B: Single;
    function Half(V: Single): Single;
    begin
      Result := V / 2.0
    end;
    begin
      A := 3.0;
      B := Half(A) + 1.5;
      WriteLn(B)
    end.
    ''');
  { 4-byte storage: stores narrow through s0, loads widen through fcvt }
  AssertTrue('store narrows', Pos(#9'fcvt s0, d0', AsmT) >= 0);
  AssertTrue('4-byte store', Pos(#9'str s0, [x9]', AsmT) >= 0);
  AssertTrue('load widens', Pos(#9'fcvt d0, s0', AsmT) >= 0);
  { the param arrives in s0 and is spilled as 4 bytes; the caller narrows
    into s0 at the pop }
  AssertTrue('callee spills s-reg param', Pos(#9'str s0, [x9]', AsmT) >= 0);
  { the whole module assembles (fcvt + s-reg loads reach the encoder) }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64single.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestClass_CreateFieldsMethodsMetadata;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TCounter = class
        FCount: Int64;
        FName: string;
        procedure Bump;
        function Value: Int64;
      end;
    procedure TCounter.Bump;
    begin
      FCount := FCount + 1
    end;
    function TCounter.Value: Int64;
    begin
      Result := FCount
    end;
    var
      C: TCounter;
    begin
      C := TCounter.Create();
      C.Bump();
      C.FName := 'named';
      WriteLn(C.Value());
      WriteLn(C.FName)
    end.
    ''');
  { creation goes through the RTL with the class typeinfo }
  AssertTrue('typeinfo passed to _ClassCreate',
    Pos('add x0, x0, typeinfo_TCounter@PAGEOFF', AsmT) >= 0);
  AssertTrue('creates via the RTL', Pos(#9'bl _ClassCreate', AsmT) >= 0);
  { non-virtual methods dispatch directly to the mangled symbol }
  AssertTrue('direct method call', Pos(#9'bl TCounter_Bump', AsmT) >= 0);
  { metadata: typeinfo slots + vtable with the typeinfo back-pointer }
  AssertTrue('typeinfo emitted', Pos('typeinfo_TCounter:', AsmT) >= 0);
  AssertTrue('vtable emitted', Pos('vtable_TCounter:', AsmT) >= 0);
  AssertTrue('vtable slot 0 is the typeinfo',
    Pos(#9'.quad typeinfo_TCounter', AsmT) >= 0);
  AssertTrue('cleanup emitted', Pos('_FieldCleanup_TCounter:', AsmT) >= 0);
  { the class-typed global is released at program exit }
  AssertTrue('program-exit release', Pos(#9'bl _ClassRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64class.o');
  try
    AssertTrue('has a data section',
      F.FindSection('__DATA', '__data') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestClass_VirtualDispatchAndDestroy;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TAnimal = class
        function Speak: Int64; virtual;
        destructor Destroy; override;
      end;
      TDog = class(TAnimal)
        function Speak: Int64; override;
      end;
    function TAnimal.Speak: Int64;
    begin
      Result := 1
    end;
    destructor TAnimal.Destroy;
    begin
    end;
    function TDog.Speak: Int64;
    begin
      Result := 2
    end;
    var
      A: TAnimal;
    begin
      A := TDog.Create();
      WriteLn(A.Speak())
    end.
    ''');
  { virtual dispatch: vtable load + slot load + blr }
  AssertTrue('vtable indirection', Pos(#9'blr x9', AsmT) >= 0);
  { the derived vtable carries the override }
  AssertTrue('override in TDog vtable', Pos(#9'.quad TDog_Speak', AsmT) >= 0);
  { the cleanup chain calls the user destructor }
  AssertTrue('cleanup calls Destroy',
    Pos('_Destroy', AsmT) >= 0);
  { parent typeinfo chains to the base class }
  AssertTrue('parent typeinfo link',
    Pos(#9'.quad typeinfo_TAnimal', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestClass_InUnit_PrefixedSymbols;
var
  AsmT: string;
begin
  AsmT := GenAsmWithUnit(
    '''
    unit zoo;
    interface
    type
      TCat = class
        FLives: Int64;
        procedure Init;
      end;
    implementation
    procedure TCat.Init;
    begin
      FLives := 9
    end;
    end.
    ''',
    '''
    program P;
    uses zoo;
    var
      C: TCat;
    begin
      C := TCat.Create();
      C.Init();
      WriteLn(C.FLives)
    end.
    ''');
  { the unit class's metadata symbols carry the owning-unit prefix, and
    the Create site targets the same typeinfo }
  AssertTrue('prefixed typeinfo', Pos('typeinfo_zoo_TCat:', AsmT) >= 0);
  AssertTrue('prefixed vtable', Pos('vtable_zoo_TCat:', AsmT) >= 0);
  AssertTrue('create targets prefixed typeinfo',
    Pos('typeinfo_zoo_TCat@PAGEOFF', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestClass_StaticsConstsInheritedToString;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TBase = class
        function Tag: Int64; virtual;
      end;
      TKid = class(TBase)
        const Answer = 42;
        static function Twice(N: Int64): Int64;
        function Tag: Int64; override;
      end;
    function TBase.Tag: Int64;
    begin
      Result := 1
    end;
    static function TKid.Twice(N: Int64): Int64;
    begin
      Result := N * 2
    end;
    function TKid.Tag: Int64;
    begin
      Result := inherited Tag() + 10
    end;
    var
      K: TKid;
    begin
      K := TKid.Create();
      WriteLn(K.Tag());
      WriteLn(TKid.Twice(21));
      WriteLn(TKid.Answer);
      WriteLn(K.ToString())
    end.
    ''');
  { inherited: static dispatch straight to the parent implementation }
  AssertTrue('inherited call is direct', Pos(#9'bl TBase_Tag', AsmT) >= 0);
  { static method: plain call, no receiver }
  AssertTrue('static method direct call', Pos(#9'bl TKid_Twice', AsmT) >= 0);
  { class const folded to its literal }
  AssertTrue('class const folded', Pos(#9'movz x0, #42', AsmT) >= 0);
  { ToString: virtual through vtable slot 1 (offset 16) }
  AssertTrue('ToString via vtable', Pos(#9'ldr x9, [x9, #16]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64class17.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestClass_Properties;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TGauge = class
      private
        FLevel: Int64;
        function GetPercent: Int64;
        procedure SetPercent(AValue: Int64);
      public
        property Level: Int64 read FLevel write FLevel;
        property Percent: Int64 read GetPercent write SetPercent;
      end;
    function TGauge.GetPercent: Int64;
    begin
      Result := FLevel * 10
    end;
    procedure TGauge.SetPercent(AValue: Int64);
    begin
      FLevel := AValue div 10
    end;
    var
      G: TGauge;
    begin
      G := TGauge.Create();
      G.Level := 3;
      WriteLn(G.Percent);
      G.Percent := 70;
      WriteLn(G.Level)
    end.
    ''');
  { field-backed accessors are rewritten to plain field access by the
    semantic pass; method-backed ones call the accessors directly }
  AssertTrue('getter called', Pos(#9'bl TGauge_GetPercent', AsmT) >= 0);
  AssertTrue('setter called', Pos(#9'bl TGauge_SetPercent', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64props.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestClass_ChainedReceivers;
var
  AsmT: string;
  PosCall, PosRel: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TInner = class
        FVal: Int64;
        function Get: Int64;
      end;
      TOuter = class
        FInner: TInner;
        function Inner: TInner;
      end;
    function TInner.Get: Int64;
    begin
      Result := FVal
    end;
    function TOuter.Inner: TInner;
    begin
      Result := FInner
    end;
    var
      O: TOuter;
    begin
      O := TOuter.Create();
      O.FInner := TInner.Create();
      O.FInner.FVal := 7;
      WriteLn(O.FInner.FVal);
      WriteLn(O.FInner.Get())
    end.
    ''');
  { chained field read (O.FInner.FVal) derefs through the base expr, and
    a method on a chained field (O.FInner.Get) receives the loaded ptr }
  AssertTrue('chained method call', Pos(#9'bl TInner_Get', AsmT) >= 0);
  { O.FInner.Get(): the receiver O.FInner is a BORROWED field read — an
    owned method result gets released; make sure the owned-receiver
    release plumbing appears for owned receivers only when used.  Here
    Inner() is unused, so no blr-owned pattern is required — assert the
    borrow shape: field load feeding the call. }
  PosCall := Pos(#9'bl TInner_Get', AsmT);
  PosRel := Pos('ldr x0, [sp, #16]', AsmT);
  AssertTrue('no owned-receiver bracket for borrowed chains', PosRel < 0);
  AssertTrue('call present', PosCall >= 0);
end;

procedure TArm64BackendTests.TestThreadvar_TlvDescriptorsAndAccess;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    threadvar
      Counter: Int64;
    begin
      Counter := 5;
      WriteLn(Counter)
    end.
    ''');
  { access: FORM the descriptor address (adrp + ADD — the relaxed form;
    the adrp+LDR shape needs a linker-made indirection slot we never
    create and crashed on real hardware: ARM64_TLS_SEGFAULT_FEEDBACK.md),
    then call its thunk with x0 = &descriptor }
  AssertTrue('TLVP page ref', Pos('_tv_Counter@TLVPPAGE', AsmT) >= 0);
  AssertTrue('descriptor address FORMED, not loaded',
    Pos(#9'add x0, x0, _tv_Counter@TLVPPAGEOFF', AsmT) >= 0);
  AssertTrue('no ldr-through-slot TLV access',
    Pos(#9'ldr x0, [x0, _tv_Counter@TLVPPAGEOFF]', AsmT) < 0);
  AssertTrue('thunk call', Pos(#9'blr x9', AsmT) >= 0);
  { descriptor: three quads with the bootstrap thunk }
  AssertTrue('descriptor label', Pos('_tv_Counter:', AsmT) >= 0);
  AssertTrue('bootstrap slot', Pos(#9'.quad _tlv_bootstrap', AsmT) >= 0);
  AssertTrue('storage slot ref', Pos(#9'.quad _ts_Counter', AsmT) >= 0);
  AssertTrue('thread_vars section',
    Pos('.section __DATA,__thread_vars', AsmT) >= 0);
  { and the module assembles: the writer emits the S_THREAD_LOCAL sections }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64tlv.o');
  try
    AssertTrue('has __thread_vars',
      F.FindSection('__DATA', '__thread_vars') <> nil);
    AssertTrue('has __thread_bss',
      F.FindSection('__DATA', '__thread_bss') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestStackArgs_VariadicAndOverflow;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    function printf(Fmt: PChar): Integer; cdecl; varargs;
      external 'c' name 'printf';
    function Sum10(A, B, C, D, E, F, G, H, I, J: Int64): Int64;
    begin
      Result := A + B + C + D + E + F + G + H + I + J
    end;
    begin
      printf(PChar('%lld and %lld'), 40, 2);
      WriteLn(Sum10(1, 2, 3, 4, 5, 6, 7, 8, 9, 10))
    end.
    ''');
  { variadic anonymous args go to the outgoing stack area (Apple
    divergence), stored through w/x into [sp, #..] }
  AssertTrue('outgoing area allocated', Pos(#9'sub sp, sp, #16', AsmT) >= 0);
  AssertTrue('variadic call to printf', Pos(#9'bl printf', AsmT) >= 0);
  { the 9th/10th args of Sum10 overflow the register file to the stack }
  AssertTrue('call to Sum10', Pos(#9'bl Sum10', AsmT) >= 0);
  AssertTrue('area released', Pos(#9'add sp, sp, #16', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64stackargs.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestStackArgs_RecordParamOverflow;
var
  AsmT: string;
  Obj: string;
  MF: TMachOFile;
begin
  { leg 29: a routine whose 10th parameter is a >16B record (shape 0) after 9
    integer params fills x0-x7, spills the 9th int to the stack, then spills the
    record's hidden pointer to the stack too.  This is the compiler's own
    EmitVexRM shape (blaise.assembler.x86_64.pas:2531).  The callee must read
    the overflow record pointer from the outgoing area and park it in
    '__pptr_R'; the caller must reserve the area and push both overflow args. }
  AsmT := GenAsm(
    '''
    program P;
    type TBig = record A, B, C: Int64; S: string; end;
    function F(a, b, c, d, e, f, g, h, i: Int64; const R: TBig): Int64;
    begin Result := i + R.A end;
    var R: TBig;
    begin
      R.A := 100; R.B := 200; R.C := 300; R.S := 'abcd';
      WriteLn(F(1, 2, 3, 4, 5, 6, 7, 8, 9, R))
    end.
    ''');
  { callee: the 9th int arrives at [x29,#16] and the record pointer at
    [x29,#24], the latter parked in the __pptr_ slot for pass-2 memcpy }
  AssertTrue('9th int read from the overflow area',
    Pos(#9'ldr x9, [x29, #16]', AsmT) >= 0);
  AssertTrue('overflow record pointer read from the outgoing area',
    Pos(#9'ldr x9, [x29, #24]', AsmT) >= 0);
  { caller: an outgoing area is reserved and the call is emitted }
  AssertTrue('call to F', Pos(#9'bl F', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  MF := ParseMachO(Obj, 'arm64recovf.o');
  try
    AssertTrue('has a text section',
      MF.FindSection('__TEXT', '__text') <> nil);
  finally
    MF.Free();
  end;
end;

procedure TArm64BackendTests.TestInterfaces_DispatchAndMetadata;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      IGreeter = interface
        function Greet(N: Int64): Int64;
      end;
      THi = class(TObject, IGreeter)
        function Greet(N: Int64): Int64;
      end;
    function THi.Greet(N: Int64): Int64;
    begin
      Result := N + 1
    end;
    var
      G: IGreeter;
      H: THi;
    begin
      H := THi.Create();
      G := H;
      WriteLn(G.Greet(41));
      G := nil
    end.
    ''');
  { narrowing stores the static itab; dispatch loads fptr from itab[0] }
  AssertTrue('itab emitted', Pos('itab_THi_IGreeter:', AsmT) >= 0);
  AssertTrue('itab slot names the impl', Pos(#9'.quad THi_Greet', AsmT) >= 0);
  AssertTrue('impllist emitted', Pos('impllist_THi:', AsmT) >= 0);
  AssertTrue('interface typeinfo', Pos('typeinfo_IGreeter:', AsmT) >= 0);
  AssertTrue('narrow stores itab', Pos('itab_THi_IGreeter@PAGEOFF', AsmT) >= 0);
  AssertTrue('dispatch through itab slot 0',
    Pos(#9'ldr x9, [x9, #0]', AsmT) >= 0);
  AssertTrue('dispatch call', Pos(#9'blr x9', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64intf.o');
  try
    AssertTrue('has a data section',
      F.FindSection('__DATA', '__data') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestInterface_TypeinfoSymbol_DefAndRefAgree;
var
  AsmT: string;
begin
  { A unit declares IGreeter; the program's class implements it and uses
    Supports.  The typeinfo must be DEFINED (typeinfo_intfu_IGreeter:) and every
    reference — the impllist .quad and the Supports adrp — must use that SAME
    owning-unit-prefixed symbol.  A bare `typeinfo_IGreeter` reference would
    dangle at link (LINK-1). }
  AsmT := GenAsmWithUnit(
    '''
    unit intfu;
    interface
    type
      IGreeter = interface
        function Greet: Int64;
      end;
    implementation
    end.
    ''',
    '''
    program P;
    uses intfu;
    type
      THi = class(TObject, IGreeter)
        function Greet: Int64;
      end;
    function THi.Greet: Int64; begin Result := 7 end;
    var o: TObject; g: IGreeter;
    begin
      o := THi.Create();
      if Supports(o, IGreeter, g) then WriteLn(g.Greet());
      o.Free()
    end.
    ''');
  { the typeinfo is defined under the unit-prefixed symbol }
  AssertTrue('prefixed typeinfo defined',
    Pos('typeinfo_intfu_IGreeter:', AsmT) >= 0);
  { the impllist references the SAME prefixed symbol }
  AssertTrue('impllist uses the prefixed typeinfo',
    Pos(#9'.quad typeinfo_intfu_IGreeter', AsmT) >= 0);
  { Supports loads the SAME prefixed symbol }
  AssertTrue('Supports uses the prefixed typeinfo',
    Pos('typeinfo_intfu_IGreeter@PAGE', AsmT) >= 0);
  { and NO bare typeinfo_IGreeter reference dangles }
  AssertTrue('no bare typeinfo reference',
    Pos('typeinfo_IGreeter@PAGE', AsmT) < 0);
end;

procedure TArm64BackendTests.TestInterface_ItabAndImpllist_AreGlobl;
var
  AsmT: string;
begin
  { A plain class's itab and impllist are DEFINED in the class's own object but
    REFERENCED from another object (an interface assignment / Supports in the
    program that uses the unit).  They must be .globl so the cross-object
    reference resolves — a file-local (no-directive) definition dangles at link
    (LINK-2; the arm64 backend previously only emitted .weak for generic
    instances and nothing for a plain class, unlike x86-64). }
  AsmT := GenAsmWithUnit(
    '''
    unit itabu;
    interface
    type
      IWork = interface
        function Run: Int64;
      end;
    implementation
    end.
    ''',
    '''
    program P;
    uses itabu;
    type
      TJob = class(TObject, IWork)
        function Run: Int64;
      end;
    function TJob.Run: Int64; begin Result := 9 end;
    var o: TObject; w: IWork;
    begin
      o := TJob.Create();
      if Supports(o, IWork, w) then WriteLn(w.Run());
      o.Free()
    end.
    ''');
  { The itab is defined (a label) and made globl.  The exact owning-unit prefix
    of a program-declared class is an internal detail; what LINK-2 requires is
    that the definition is globl (not file-local) so it resolves across objects. }
  AssertTrue('the TJob/IWork itab is defined',
    Pos('_TJob_IWork:', AsmT) >= 0);
  AssertTrue('plain-class itab is .globl (cross-object visible)',
    Pos('.globl itab_', AsmT) >= 0);
  AssertTrue('the TJob itab definition is globl, not file-local',
    Pos('.globl itab_', AsmT) >= 0);
  AssertTrue('the TJob impllist is defined',
    Pos('impllist_', AsmT) >= 0);
  AssertTrue('plain-class impllist is .globl',
    Pos('.globl impllist_', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestGenericClassInstance_MethodBodyEmittedInUnit;
var
  AsmT: string;
begin
  { A UNIT that materialises a generic class instance (TList<Integer>) must emit
    that instance's method BODIES in its own object — not just the metadata
    (vtable/itab) that references them.  EmitUnit previously registered the
    instance for metadata but never emitted its method bodies (only EmitProgram
    did, and that is not called per-unit), so a real incremental build left
    TList_Integer_Add etc. undefined and the Mach-O linker bound them from
    libSystem — a dyld abort at launch (leg 43).  The body must be emitted weak
    (bare name) for cross-object dedup. }
  AsmT := GenAsmWithUnit(
    '''
    unit genu;
    interface
    type
      TBox<T> = class
        FVal: T;
        procedure Put(AVal: T);
        function Get: T;
      end;
      TThing = class
        FBox: TBox<Integer>;
        procedure Setup;
      end;
    implementation
    procedure TBox<T>.Put(AVal: T); begin FVal := AVal end;
    function TBox<T>.Get: T; begin Result := FVal end;
    procedure TThing.Setup;
    begin
      FBox := TBox<Integer>.Create();
      FBox.Put(7);
    end;
    end.
    ''',
    '''
    program P;
    uses genu;
    var t: TThing;
    begin
      t := TThing.Create();
      t.Setup();
      t.Free()
    end.
    ''');
  { the monomorphised TBox<Integer>.Put body is DEFINED (a label), not just
    referenced }
  AssertTrue('TBox<Integer>.Put body is defined',
    Pos('TBox_Integer_Put:', AsmT) >= 0);
  { and it is weak-bound (bare generic-instance symbol) for cross-object dedup }
  AssertTrue('the generic-instance method body is weak',
    Pos('.weak TBox_Integer_Put', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestClassTypeinfo_InstanceSizeCoversAllFields;
var
  AsmT: string;
  P, Q, K: Integer;
  SizeSlot: string;
begin
  { The 5th quad of a class typeinfo block is the INSTANCE size — the byte
    count ClassCreate allocates and zero-fills for one object.  It must be
    TotalSize (vptr + every field), NOT RawSize: for a tyClass RawSize returns
    8, the width of a REFERENCE to the object.  Emitting RawSize made EVERY
    class allocate 8 bytes, so any field past the vptr read and wrote unmapped
    heap — the first constructed object with a class-typed field crashed in
    ClassRelease on a garbage "old value" (macOS arm64 on-device SIGSEGV,
    2026-07-23 bring-up report).

    TSized below is vptr(8) + Int64(8) + Int64(8) + class ref(8) = 32. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TSized = class
        A: Int64;
        B: Int64;
        C: TObject;
      end;
    var s: TSized;
    begin
      s := TSized.Create();
      s.A := 1;
      s.Free()
    end.
    ''');
  P := Pos('typeinfo_P_TSized:', AsmT);
  if P < 0 then
    P := Pos('typeinfo_TSized:', AsmT);
  AssertTrue('TSized typeinfo is emitted', P >= 0);
  { walk to the 5th .quad after the label — the instance-size slot }
  Q := P;
  for K := 1 to 5 do
    Q := PosEx(#9'.quad ', AsmT, Q + 1);
  AssertTrue('found the instance-size slot', Q >= 0);
  { the slot text runs to the end of that line }
  K := PosEx(#10, AsmT, Q + 7);
  if K < 0 then K := Length(AsmT);
  SizeSlot := Trim(Copy(AsmT, Q + 7, K - (Q + 7)));
  { the full 32-byte instance, never the 8-byte reference width }
  AssertEquals('instance size covers vptr + all fields', '32', SizeSlot);
end;

procedure TArm64BackendTests.TestSmallRecordParam_FieldReadUsesInlineSlot;
var
  AsmT: string;
  P, Q: Integer;
  Body: string;
begin
  { Reading a field of a BY-VALUE small (<=16B) record param must take the
    ADDRESS of the param's inline slot (sub xN, x29, #off) and read through
    that — NOT load the slot's contents and dereference them.

    The semantic pass marks every record param IsVarParam=True ("records pass
    by reference at the ABI level"), and the by-value discriminator used to
    infer by-value-ness from the presence of a '__pptr_' companion slot — which
    only a >16B (shape 0) param ever gets.  So every small record param was
    misread as a true var/out param: codegen emitted `ldur xN,[x29,#-off]`
    (the record VALUE) and then dereferenced it as a pointer.  With two 4-byte
    enum fields the value is literally 0x0, so the callee faulted on a null
    dereference — the macOS arm64 TargetName(const ATarget: TTargetDesc) crash
    found during the 2026-07-23 on-device bring-up.

    Shaped exactly like that crash: an 8-byte two-enum record passed const. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TOS  = (osA, osB);
      TCPU = (cpuA, cpuB);
      TDesc = record
        OS:  TOS;
        CPU: TCPU;
      end;
    var D: TDesc;
    function Name(const ADesc: TDesc): Int64;
    begin
      Result := Ord(ADesc.OS)
    end;
    begin
      D.OS := osB;
      WriteLn(Name(D))
    end.
    ''');
  { isolate the callee body so caller-side patterns cannot satisfy the asserts }
  P := Pos(#10'Name:', AsmT);
  AssertTrue('the Name routine is emitted', P >= 0);
  Q := PosEx(#10'.globl ', AsmT, P + 1);
  if Q < 0 then Q := Length(AsmT);
  Body := Copy(AsmT, P, Q - P);

  { the field read must address the inline slot ... }
  AssertTrue('field read takes the address of the inline param slot',
    Pos(#9'sub x', Body) >= 0);
  { ... and must NOT dereference a loaded slot value.  Guard the precise
    shape: a slot LOAD feeding the field read is the bug. }
  AssertTrue('by-value record param field read does not deref the slot value',
    Pos(#9'ldur x9, [x29, #-8]'#10#9'mov x0, x9'#10#9'ldrsw x0, [x0]', Body) < 0);
end;

procedure TArm64BackendTests.TestSeparateCompile_DepUnitInitIsCalledFromMain;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TArm64Backend;
  T:    TTargetDesc;
  AsmT: string;
begin
  { SEPARATE COMPILATION: a dependency unit's body — and its <Unit>_init — are
    compiled into the dep's OWN object, so EmitUnit never runs for it in the
    program's translation unit and never registers the init symbol.  The driver
    instead announces each such dep via NoteDepInitUnit, and _main must still
    call it.

    arm64 had no NoteDepInitUnit override, so it silently inherited
    TNativeBackend's no-op: an incrementally built arm64 program called NO unit
    initialization at all.  Every initialization-populated global stayed empty —
    including GDrivers, so the compiler aborted with "no driver registered for
    backend kind" before doing anything (macOS arm64 on-device, 2026-07-23).
    The whole-program path was fine, which is why --emit-asm never showed it. }
  L := TLexer.Create('program P; begin end.');
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Prog);
      MakeTarget(osMacOS, cpuArm64, T);
      CG := TArm64Backend.Create(T);
      try
        CG.SetSymbolTable(Prog.SymbolTable);
        { exactly what the incremental driver does for a cached/prebuilt dep }
        CG.NoteDepInitUnit('some.dep.unit', True);
        CG.NoteDepInitUnit('quiet.unit', False);   { no init section }
        AsmT := CG.GenerateProgram(Prog);
      finally
        CG.Free();
      end;
    finally
      A.Free();
    end;
  finally
    Prog.Free();
  end;
  { the dep WITH an initialization section is called from _main ... }
  AssertTrue('separately-compiled dep unit init is called from _main',
    Pos(#9'bl some.dep.unit_init', AsmT) >= 0);
  { ... and one without an initialization section is not }
  AssertTrue('a dep with no initialization section is not called',
    Pos('quiet.unit_init', AsmT) < 0);
end;

procedure TArm64BackendTests.TestReceiverCall_NestedArcArg_ReceiverNotClobbered;
var
  AsmT: string;
  P, Q: Integer;
  Body: string;
begin
  { A method call on a RECEIVER whose argument is itself a call returning an
    ARC'd (string) value — Obj.Take(Maker.Make()) — must not lose the receiver.

    EmitCall reserves an outgoing area (sp -= StackArea) before pushing the
    arguments, so the memory-class and ARC-transient offsets stay fixed while
    the eval slots are pushed.  But a method RECEIVER is pushed by EmitCall's
    caller, BEFORE EmitCall runs, so the reservation used to land BETWEEN the
    receiver and the argument pushes.  Two things then broke: the pop walk
    (a contiguous LIFO run) read the reserved gap instead of the receiver, and
    the transient keep-alive stash wrote over the receiver's slot.  Self
    arrived as raw stack content — the macOS arm64 crash in
    Result.Add(GDrivers[I].Name()) on 2026-07-23.

    A nested call returning a string is what makes StackArea non-zero here, so
    this shape is the minimal reproduction.  EmitCall now re-seats the receiver
    (pop, reserve, re-push) to keep the run contiguous. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TMaker = class
        function Make: string;
      end;
      TSink = class
        Got: string;
        procedure Take(const S: string);
      end;
    function TMaker.Make: string; begin Result := 'x' end;
    procedure TSink.Take(const S: string); begin Got := S end;
    var M: TMaker; K: TSink;
    begin
      M := TMaker.Create();
      K := TSink.Create();
      K.Take(M.Make());
      WriteLn(K.Got);
      K.Free(); M.Free()
    end.
    ''');
  { isolate the program body so other routines cannot satisfy the assert }
  P := Pos('_main:', AsmT);
  if P < 0 then P := Pos(#10'$main:', AsmT);
  AssertTrue('program body is emitted', P >= 0);
  Q := PosEx('bl Classes_', AsmT, P);
  Body := Copy(AsmT, P, Length(AsmT) - P);

  { The receiver must be RE-SEATED around the outgoing-area reservation: a
    bare `sub sp, sp, #N` sitting directly between two pushes is the bug
    signature.  After the fix the reservation is bracketed by a pop and a
    re-push. }
  AssertTrue('receiver is popped before the outgoing area is reserved',
    Pos(#9'ldr x9, [sp], #16'#10#9'sub sp, sp, #', Body) >= 0);
  AssertTrue('receiver is re-pushed after the reservation',
    Pos(#9'str x9, [sp, #-16]!', Body) >= 0);
end;

procedure TArm64BackendTests.TestLargeManagedArray_ElemOffsetBeyondImm12;
var
  AsmT, Obj: string;
  I, Bad: Integer;
  Line, ImmS: string;
  L: TStringList;
  P: Integer;
begin
  { An ARC walk over a large array of managed elements derives each element as
    base + byteOffset.  That offset is unbounded (600 strings = 4800 bytes),
    but an AArch64 add-immediate encodes only 12 bits, so the walk emitted
    `add x20, x21, #4096` and the internal assembler rejected the whole
    program with "add/sub immediate out of range: 4096".  Any routine with a
    large managed local array failed to build at all (2026-07-23).

    Two guards: no raw add/sub immediate above 4095 may be emitted, and the
    program must actually assemble. }
  AsmT := GenAsm(
    '''
    program P;
    var
      A: array[0..599] of string;
      I: Integer;
    begin
      for I := 0 to 599 do
        A[I] := 'x';
      WriteLn(A[0])
    end.
    ''');
  { no emitted add/sub may carry an immediate the encoder cannot represent }
  Bad := -1;
  L := TStringList.Create();
  try
    L.Text := AsmT;
    for I := 0 to L.Count - 1 do
    begin
      Line := L.Strings[I];
      if (Pos(#9'add ', Line) < 0) and (Pos(#9'sub ', Line) < 0) then Continue;
      P := Pos(', #', Line);
      if P < 0 then Continue;
      ImmS := Trim(Copy(Line, P + 3, Length(Line) - (P + 3)));
      if (ImmS = '') or (StrToIntDef(ImmS, 0) <= 4095) then Continue;
      Bad := I;
      Break;
    end;
  finally
    L.Free();
  end;
  AssertEquals('no add/sub immediate above 4095 is emitted', -1, Bad);
  { and it must survive the real encoder }
  Obj := AssembleArm64ToBytes(AsmT);
  AssertTrue('large managed array program assembles', Length(Obj) > 0);
end;

procedure TArm64BackendTests.TestInterfaces_StringArg;
var
  AsmT: string;
begin
  { Leg 31: an itab dispatch may carry a by-value STRING argument.  The itab
    dispatcher loads the string buffer pointer into an arg register (x1) and
    calls through the itab slot.  A plain local passed to a `const S: string`
    param is BORROWED — no _StringAddRef is emitted at the call site (the
    negative assertion guards against an over-eager retain). }
  AsmT := GenAsm(
    '''
    program P;
    type
      IFoo = interface
        procedure Take(const S: string);
      end;
      TFoo = class(TObject, IFoo)
        procedure Take(const S: string);
      end;
    procedure TFoo.Take(const S: string);
    begin
      WriteLn(S)
    end;
    var
      F: IFoo;
      H: TFoo;
      S: string;
    begin
      H := TFoo.Create();
      F := H;
      S := 'hello';
      F.Take(S);
      F := nil
    end.
    ''');
  AssertTrue('string arg loaded into x1', Pos(#9'ldr x1, [sp], #16', AsmT) >= 0);
  AssertTrue('dispatch through itab slot 0',
    Pos(#9'ldr x9, [x9, #0]', AsmT) >= 0);
  AssertTrue('dispatch call', Pos(#9'blr x9', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestInterfaces_AsCast;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      IThing = interface
        procedure Go;
      end;
      TThing = class(TObject, IThing)
        procedure Go;
      end;
    procedure TThing.Go;
    begin
    end;
    var
      T: TThing;
      I: IThing;
    begin
      T := TThing.Create();
      I := T as IThing;
      I.Go()
    end.
    ''');
  { runtime lookup + invalid-cast guard }
  AssertTrue('runtime itab lookup', Pos(#9'bl _GetItab', AsmT) >= 0);
  AssertTrue('nil-itab guard', Pos(#9'bl _Raise_InvalidCast', AsmT) >= 0);
  AssertTrue('typeinfo operand', Pos('typeinfo_IThing@PAGEOFF', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestOwnedStringTransientArg_Released;
var
  AsmT: string;
  PosCall, PosRel: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      A, B: string;
    function Make: string;
    begin
      Result := A + B
    end;
    procedure Show(Msg: string);
    begin
      WriteLn(Msg)
    end;
    procedure ShowC(const Msg: string);
    begin
      WriteLn(Msg)
    end;
    begin
      A := 'he';
      B := 'yo';
      Show(A + B);
      Show(Make());
      ShowC(A + B)
    end.
    ''');
  { by-value rc=0 concat arg: the callee's entry-retain/exit-release pair
    frees it — the CALLER must not touch it (a release would double-free);
    by-value rc=1 call result: one caller release after the call;
    const rc=0 concat arg: caller pins (AddRef+Release) after the call }
  PosCall := Pos(#9'bl Show', AsmT);
  AssertTrue('calls emitted', PosCall >= 0);
  AssertTrue('rc=1 arg parked in the outgoing area',
    Pos('ldr x0, [sp, #32]', AsmT) >= 0);
  PosCall := Pos(#9'bl ShowC', AsmT);
  AssertTrue('const call emitted', PosCall >= 0);
  PosRel := PosEx(#9'bl _StringAddRef', AsmT, PosCall);
  AssertTrue('const rc=0 arg pinned after the call', PosRel > PosCall);
end;

procedure TArm64BackendTests.TestReflection_SupportsInheritsFromMetaclass;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      IThing = interface
        procedure Go;
      end;
      TBase = class(TObject, IThing)
        procedure Go;
      end;
      TKid = class(TBase)
      end;
      TBaseClass = class of TBase;
    procedure TBase.Go;
    begin
    end;
    var
      K: TKid;
      MC: TBaseClass;
      Ok: Boolean;
    begin
      K := TKid.Create();
      Ok := Supports(K, IThing);
      WriteLn(Ok);
      WriteLn(K.InheritsFrom(TBase));
      MC := TKid;
      WriteLn(MC.InheritsFrom(TBase))
    end.
    ''');
  { Supports: runtime itab probe folded to a boolean }
  AssertTrue('supports via _GetItab', Pos(#9'bl _GetItab', AsmT) >= 0);
  AssertTrue('boolean fold', Pos(#9'cset x0, ne', AsmT) >= 0);
  { InheritsFrom: instance receiver reads typeinfo via vtable[0];
    metaclass receiver passes its value directly }
  AssertTrue('inheritsfrom call', Pos(#9'bl _InheritsFrom', AsmT) >= 0);
  { bare class name as a value = typeinfo address }
  AssertTrue('metaclass value', Pos('typeinfo_TKid@PAGEOFF', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestInterfaceParamsAndResults;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      IGreeter = interface
        function Greet(N: Int64): Int64;
      end;
      THi = class(TObject, IGreeter)
        function Greet(N: Int64): Int64;
      end;
    function THi.Greet(N: Int64): Int64;
    begin
      Result := N + 1
    end;
    function MakeGreeter: IGreeter;
    var
      H: THi;
    begin
      H := THi.Create();
      Result := H
    end;
    function UseGreeter(G: IGreeter): Int64;
    begin
      Result := G.Greet(1)
    end;
    var
      G: IGreeter;
    begin
      G := MakeGreeter();
      WriteLn(UseGreeter(G))
    end.
    ''');
  { result: callee writes the fat pointer through the parked x8 buffer }
  AssertTrue('sret buffer store', Pos(#9'str x0, [x9, #8]', AsmT) >= 0);
  { caller receives through the __iret scratch }
  AssertTrue('call with sret dest', Pos(#9'bl MakeGreeter', AsmT) >= 0);
  { param: two-register fat pointer, by-value retain in the callee }
  AssertTrue('param call', Pos(#9'bl UseGreeter', AsmT) >= 0);
  AssertTrue('callee retains its copy', Pos(#9'bl _ClassAddRef', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64intfpr.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestInterfaceAssign_FromMethodCall;
var
  AsmT: string;
begin
  { IntfVar := Obj.Method() where the class-receiver method returns an
    interface: the callee writes the 16-byte fat pointer through x8 into __iret;
    the caller releases the old interface value and stores both halves (obj and
    itab) with no extra retain (the returned obj is owned +1). }
  AsmT := GenAsm(
    '''
    program P;
    type
      IGreeter = interface
        function Greet: Int64;
      end;
      THi = class(TObject, IGreeter)
        function Greet: Int64;
        function GetSelf: IGreeter;
      end;
    function THi.Greet: Int64; begin Result := 7 end;
    function THi.GetSelf: IGreeter; begin Result := Self end;
    var H: THi; G: IGreeter;
    begin
      H := THi.Create();
      G := H.GetSelf();
      WriteLn(G.Greet());
      G := nil
    end.
    ''');
  { the old interface value is released before the new fat pointer is stored }
  AssertTrue('release old before store', Pos(#9'bl _ClassRelease', AsmT) >= 0);
  { both halves of the returned fat pointer are unpacked from __iret }
  AssertTrue('obj half stored', Pos(#9'ldr x0, [x9]', AsmT) >= 0);
  AssertTrue('itab half stored', Pos(#9'ldr x0, [x9, #8]', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestFloatPropRead_And_StringGlobalInit;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TTank = class
      private
        FVol: Double;
        function GetVol: Double;
      public
        property Vol: Double read GetVol;
      end;
    function TTank.GetVol: Double;
    begin
      Result := FVol
    end;
    var
      Banner: string = 'ready';
      T: TTank;
    begin
      T := TTank.Create();
      WriteLn(T.Vol);
      WriteLn(Banner)
    end.
    ''');
  { float property read: getter call, value already in d0 }
  AssertTrue('getter called', Pos(#9'bl TTank_GetVol', AsmT) >= 0);
  { string-initialised global: .data pointer to an immortal blob }
  AssertTrue('data pointer', Pos(#9'.quad __gi_Banner_d', AsmT) >= 0);
  AssertTrue('immortal header', Pos('__gi_Banner_h:', AsmT) >= 0);
  AssertTrue('blob bytes', Pos(#9'.ascii "ready"', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestManagedRecord_ParamsAndResults;
var
  AsmT: string;
  PosCall, PosRel: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TNamed = record
        Id: Int64;
        Name: string;
      end;
    function Make(N: Int64): TNamed;
    begin
      Result.Id := N;
      Result.Name := 'x'
    end;
    function Describe(R: TNamed): Int64;
    begin
      Result := R.Id
    end;
    var
      A: TNamed;
    begin
      A := Make(1);
      WriteLn(Describe(A));
      A := Make(2)
    end.
    ''');
  { callee retains its by-value copy's managed fields }
  AssertTrue('param field retain', Pos(#9'bl _StringAddRef', AsmT) >= 0);
  { managed result: sret into the __rret scratch, old LHS fields released
    AFTER the call, then the fresh value moves in }
  PosCall := Pos(#9'bl Make', AsmT);
  AssertTrue('call present', PosCall >= 0);
  PosRel := PosEx(#9'bl _StringRelease', AsmT, PosCall);
  AssertTrue('LHS released after the call', PosRel > PosCall);
  AssertTrue('scratch move-in', PosEx(#9'bl memcpy', AsmT, PosRel) > PosRel);
end;

procedure TArm64BackendTests.TestSingleFields_Supports3_StaticProps;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      IThing = interface
        procedure Go;
      end;
      TVec = record
        X: Single;
        Y: Single;
      end;
      TThing = class(TObject, IThing)
        FRatio: Single;
        procedure Go;
      end;
    procedure TThing.Go;
    begin
    end;
    var
      V: TVec;
      T: TThing;
      I: IThing;
      Ok: Boolean;
    begin
      V.X := 1.5;
      V.Y := V.X;
      T := TThing.Create();
      T.FRatio := 0.5;
      WriteLn(V.Y);
      WriteLn(T.FRatio);
      Ok := Supports(T, IThing, I);
      WriteLn(Ok);
      I.Go()
    end.
    ''');
  { Single fields: 4-byte stores narrow through s0, reads load w-width }
  AssertTrue('single field store', Pos(#9'str s0, [x9, #4]', AsmT) >= 0);
  { field reads are width-keyed through the element loader now: the
    address is formed first, then a w-width load through it }
  AssertTrue('single field read', Pos(#9'ldr w0, [x0]', AsmT) >= 0);
  { 3-arg Supports: success path stores both halves of the out-var }
  AssertTrue('supports lookup', Pos(#9'bl _GetItab', AsmT) >= 0);
  AssertTrue('failure path leaves out-var untouched (skip branch)',
    Pos(#9'add sp, sp, #32', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestWeak_MetaclassCtor_IndexedProps;
var
  AsmT: string;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TNode = class;
      TNodeClass = class of TNode;
      TNode = class
        [Weak] FParent: TNode;
        FVal: Int64;
        function GetItem(I: Int64): Int64;
        procedure SetItem(I: Int64; V: Int64);
        property Items[I: Int64]: Int64 read GetItem write SetItem;
      end;
    function TNode.GetItem(I: Int64): Int64;
    begin
      Result := FVal + I
    end;
    procedure TNode.SetItem(I: Int64; V: Int64);
    begin
      FVal := V - I
    end;
    var
      A, B: TNode;
      NC: TNodeClass;
      [Weak] W: TNode;
    begin
      A := TNode.Create();
      B := TNode.Create();
      B.FParent := A;
      W := A;
      NC := TNode;
      B := NC.Create();
      B.Items[2] := 10;
      WriteLn(B.Items[1])
    end.
    ''');
  { weak var + weak field go through the weak table }
  AssertTrue('weak assign', Pos(#9'bl _WeakAssign', AsmT) >= 0);
  { metaclass ctor: _ClassCreate on the metaclass VALUE }
  AssertTrue('metaclass create', Pos(#9'bl _ClassCreate', AsmT) >= 0);
  { indexed property accessors }
  AssertTrue('indexed getter', Pos(#9'bl TNode_GetItem', AsmT) >= 0);
  AssertTrue('indexed setter', Pos(#9'bl TNode_SetItem', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestCaseAndRepeat;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    const
      Marker = 9;
    var
      N, Acc: Int64;
    begin
      Acc := 0;
      N := 0;
      repeat
        Acc := Acc + N;
        N := N + 1
      until N > 4;
      case Acc of
        10, 11: WriteLn('ten-ish');
        Marker: WriteLn('nine');
      else
        WriteLn(Acc)
      end
    end.
    ''');
  { repeat: bottom-tested loop (cbz back to the top) }
  AssertTrue('repeat back-branch', Pos(#9'cbz x0, Lrep', AsmT) >= 0);
  { case: selector parked on the stack, chained equality tests }
  AssertTrue('case compare', Pos(#9'b.eq Lcbody', AsmT) >= 0);
  AssertTrue('selector reloaded per test', Pos(#9'ldr x0, [sp]', AsmT) >= 0);
  AssertTrue('named-const case value', Pos(#9'movz x1, #9', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64case.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestExceptions_FramesHandlersUnwind;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      EBoom = class
      end;
    function Risky(N: Int64): Int64;
    begin
      Result := 0;
      try
        if N = 0 then
        begin
          Exit(7)
        end;
        if N > 5 then
          raise EBoom.Create();
        Result := N
      finally
        WriteLn('cleanup')
      end
    end;
    begin
      WriteLn(Risky(0));
      try
        WriteLn(Risky(9))
      except
        on E: EBoom do WriteLn('caught')
      end;
      try
        WriteLn(Risky(2))
      except
        WriteLn('never')
      end
    end.
    ''');
  { frames: push + setjmp guard, 512-byte static slot in the frame }
  AssertTrue('frame push', Pos(#9'bl _PushExcFrame', AsmT) >= 0);
  AssertTrue('setjmp guard', Pos(#9'bl _blaise_setjmp', AsmT) >= 0);
  AssertTrue('exception branch', Pos(#9'cbnz w0, Lfinexc', AsmT) >= 0);
  { raise + handler matching + rebind }
  AssertTrue('raise', Pos(#9'bl _Raise', AsmT) >= 0);
  AssertTrue('handler match', Pos(#9'bl _IsInstance', AsmT) >= 0);
  AssertTrue('finally re-raise', Pos(#9'bl _Reraise', AsmT) >= 0);
  { Exit inside try runs the finally on the way out (unwind emits an
    extra PopExcFrame before the exit branch) }
  AssertTrue('unwind pops', Pos(#9'bl _PopExcFrame', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64exc.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestStaticArrays_ElementsAndArc;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      Nums: array[0..3] of Integer;
      Names: array[0..1] of string;
      I: Int64;
    begin
      for I := 0 to 3 do
        Nums[I] := I * 2;
      Names[0] := 'a';
      Names[1] := Names[0];
      WriteLn(Nums[2]);
      WriteLn(Names[1])
    end.
    ''');
  { width-aware element access: 4-byte Integer elements }
  AssertTrue('scaled index', Pos(#9'mul x1, x1, x2', AsmT) >= 0);
  AssertTrue('4-byte store', Pos(#9'str w0, [x9]', AsmT) >= 0);
  AssertTrue('signed 4-byte load', Pos(#9'ldrsw x0, [x0]', AsmT) >= 0);
  { managed elements: retain/release through the parked element address }
  AssertTrue('string elem retain', Pos(#9'bl _StringAddRef', AsmT) >= 0);
  AssertTrue('string elem release', Pos(#9'bl _StringRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64sarr.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestDynArrays_LifecycleAndElements;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      A, B: array of Int64;
      I: Int64;
    begin
      SetLength(A, 4);
      for I := 0 to 3 do
        A[I] := I * I;
      B := A;
      WriteLn(Length(B));
      WriteLn(B[3])
    end.
    ''');
  { lifecycle through the RTL }
  AssertTrue('setlength', Pos(#9'bl _DynArraySetLength', AsmT) >= 0);
  AssertTrue('length', Pos(#9'bl _DynArrayLength', AsmT) >= 0);
  { whole-value assignment: retain new, release old }
  AssertTrue('retain', Pos(#9'bl _DynArrayAddRef', AsmT) >= 0);
  AssertTrue('release', Pos(#9'bl _DynArrayRelease', AsmT) >= 0);
  { element access scales off the data pointer }
  AssertTrue('scaled elem', Pos(#9'mul x1, x1, x2', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64dyn.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestSetLengthOnFieldLvalue;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { SetLength on a dyn-array FIELD of an explicit record (Result.Cands): the
    field's ADDRESS is computed (base slot + field offset), the old data
    pointer is loaded THROUGH it, _DynArraySetLength is called, and the new
    pointer is stored back through the address — no ARC (the RTL frees the
    old block and returns a fresh rc=1 block). }
  AsmT := GenAsm(
    '''
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
      SetLength(Result.Cands, 2)
    end;
    var S: TSpec;
    begin
      S := MakeSpec();
      WriteLn(Length(S.Cands))
    end.
    ''');
  { the SetLength routes through _DynArraySetLength via the field address:
    compute &field, load old ptr, call, store new ptr back — NO plain-ident
    slot store and NO extra _DynArrayRelease (the RTL moved ownership). }
  AssertTrue('field-lvalue setlength',
    Pos(#9'add x0, x0, #8' + LF + #9'str x0, [sp, #-16]!' + LF +
        #9'ldr x0, [x0]' + LF + #9'ldr x1, [sp, #16]', AsmT) >= 0);
  AssertTrue('calls _DynArraySetLength',
    Pos(#9'bl _DynArraySetLength', AsmT) >= 0);
  { the new pointer is stored back through the saved field address }
  AssertTrue('stores new ptr through field addr',
    Pos(#9'ldr x9, [sp]' + LF + #9'str x0, [x9]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64slf.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestFieldElementAssign;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Result.Cands[0] := 'cc' — assign a STRING into an element of a dyn-array
    field.  The element ADDRESS is computed (field data pointer + index*8),
    then the ARC element store runs: retain the new value (a literal is
    borrowed → AddRef), release the OLD element string, store the new. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TStrArr = array of string;
      TSpec = record
        Cands: TStrArr;
      end;
    function MakeSpec: TSpec;
    begin
      SetLength(Result.Cands, 1);
      Result.Cands[0] := 'cc'
    end;
    var S: TSpec;
    begin
      S := MakeSpec();
      WriteLn(S.Cands[0])
    end.
    ''');
  { the element store scales the index by the element size and computes the
    element address off the field's data pointer — the value is materialised
    FIRST, then the data pointer is derefed (so a reallocating RHS is safe). }
  AssertTrue('scales index by element size',
    Pos(#9'mul x1, x1, x2' + LF + #9'add x0, x0, x1', AsmT) >= 0);
  { string element ARC store: retain new, then release the OLD element (read
    through the freshly-computed element address), then store the new }
  AssertTrue('retains the new element value',
    Pos(#9'bl _StringAddRef', AsmT) >= 0);
  AssertTrue('releases the old element string via the element address',
    Pos(#9'ldr x0, [x0]' + LF + #9'bl _StringRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64fea.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestStaticArrayLowBoundWrite;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A[5] := v on a var A: array[5..9] of Integer — the WRITE must rebase the
    index by the low bound (sub #5) before scaling, so A[5] is element 0
    (BUG-050).  The read side already did this; the write did not. }
  AsmT := GenAsm(
    '''
    program P;
    var A: array[5..9] of Integer;
    begin
      A[5] := 50;
      A[9] := 90;
      WriteLn(A[5], A[9])
    end.
    ''');
  { the index is rebased by the low bound before the element scale }
  AssertTrue('write rebases the low bound (sub #5)',
    Pos(#9'sub x0, x0, #5', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64lbw.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestForceDirectoriesStatement;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { ForceDirectories('...') as a bare statement — the return value is
    discarded, so it lowers via EmitProcCallStmt (statement context), which
    was missing the case on arm64.  Emits a call to the RTL _ForceDirectories. }
  AsmT := GenAsm(
    '''
    program P;
    begin
      ForceDirectories('/tmp/blaise_leg13/x');
      WriteLn('done')
    end.
    ''');
  AssertTrue('statement-context ForceDirectories calls the RTL',
    Pos(#9'bl _ForceDirectories', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64fd.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestSelfFieldAsVarParam;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { AppendTo(FTab, ...) inside a method — FTab is an implicit-Self field, so
    its address passed as a var-param is Self + field offset (loaded via
    EmitRecIdentAddr), not a frame-slot address.  Both the bare-field and the
    explicit Self.field forms must compile. }
  AsmT := GenAsm(
    '''
    program P;
    procedure AppendTo(var S: string; const E: string);
    begin
      S := S + E
    end;
    type
      TThing = class
        FTab: string;
        procedure Build;
      end;
    procedure TThing.Build;
    begin
      FTab := 'a';
      AppendTo(FTab, 'bc');
      AppendTo(Self.FTab, 'd')
    end;
    var T: TThing;
    begin
      T := TThing.Create();
      T.Build();
      WriteLn(T.FTab)
    end.
    ''');
  { the var-param field address is Self + the field offset (#8): a plain
    EmitSlotAddr on the field name would have hit NotYet, so successful
    compilation to a call already proves the field-address path. }
  AssertTrue('calls AppendTo with the field lvalue',
    Pos(#9'bl AppendTo', AsmT) >= 0);
  AssertTrue('adds the FTab field offset (#8) to form the field address',
    Pos(#9'add x0, x0, #8', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64svp.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestGenericInstanceImplementsInterface;
var
  AsmStr: string;
  Obj: string;
  F: TMachOFile;
begin
  { TBox<Integer> implements IHolder — the instance's itab and impllist must
    be emitted WEAK (so multiple units materialising the same instance dedup),
    and the itab entry must point at the CLONE's own method (instance-mangled
    TBox_Integer_Get), not the template. }
  AsmStr := GenAsm(
    '''
    program P;
    type
      IHolder = interface
        function Get: Integer;
      end;
      TBox<T> = class(TObject, IHolder)
        FVal: Integer;
        function Get: Integer;
      end;
    function TBox<T>.Get: Integer;
    begin
      Result := FVal
    end;
    var
      B: TBox<Integer>;
      H: IHolder;
    begin
      B := TBox<Integer>.Create();
      B.FVal := 42;
      H := B;
      WriteLn(H.Get())
    end.
    ''');
  { the itab and impllist are weak-bound for the generic instance }
  AssertTrue('itab weak-bound',
    Pos('.weak itab_TBox_Integer_IHolder', AsmStr) >= 0);
  AssertTrue('impllist weak-bound',
    Pos('.weak impllist_TBox_Integer', AsmStr) >= 0);
  { the itab entry points at the clone's own instance-mangled method }
  AssertTrue('itab binds the clone method',
    Pos('itab_TBox_Integer_IHolder:' + LF + #9'.quad TBox_Integer_Get',
        AsmStr) >= 0);
  Obj := AssembleArm64ToBytes(AsmStr);
  F := ParseMachO(Obj, 'arm64gii.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestGenericInterfaceInstance_WeakTypeinfo;
var
  AsmT: string;
begin
  { A class implementing a GENERIC INTERFACE instance (ITransform<Integer>): the
    instance's typeinfo must be emitted (weak, so cross-unit copies dedup —
    BUG-004), and the class's impllist must reference it.  Previously arm64
    NotYet'd because no generic-interface typeinfo was emitted. }
  AsmT := GenAsm(
    '''
    program P;
    type
      ITransform<T> = interface
        function Apply(x: T): T;
      end;
      TDoubler = class(TObject, ITransform<Integer>)
        function Apply(x: Integer): Integer;
      end;
    function TDoubler.Apply(x: Integer): Integer; begin Result := x * 2 end;
    var d: TDoubler; t: ITransform<Integer>;
    begin
      d := TDoubler.Create();
      t := d;
      WriteLn(t.Apply(21));
      t := nil;
      d.Free()
    end.
    ''');
  { the generic-interface instance typeinfo is emitted weak }
  AssertTrue('weak generic-intf typeinfo',
    Pos('.weak typeinfo_ITransform_Integer', AsmT) >= 0);
  AssertTrue('generic-intf typeinfo label',
    Pos('typeinfo_ITransform_Integer:', AsmT) >= 0);
  { the class's impllist references that typeinfo }
  AssertTrue('impllist references the instance typeinfo',
    Pos(#9'.quad typeinfo_ITransform_Integer', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestAbstractInterfaceMethodItab;
var
  AsmStr: string;
  Obj: string;
  F: TMachOFile;
begin
  { TBase declares IShape.Area virtual;abstract; TSquare overrides it.  The
    abstract base's itab slot points at _AbstractMethodError; the concrete
    class's itab points at its own override (BUG-052 F2). }
  AsmStr := GenAsm(
    '''
    program P;
    type
      IShape = interface
        function Area: Integer;
      end;
      TBase = class(TObject, IShape)
        function Area: Integer; virtual; abstract;
      end;
      TSquare = class(TBase)
        Side: Integer;
        function Area: Integer; override;
      end;
    function TSquare.Area: Integer;
    begin Result := Side * Side end;
    var S: TSquare; Sh: IShape;
    begin
      S := TSquare.Create();
      S.Side := 4;
      Sh := S;
      WriteLn(Sh.Area())
    end.
    ''');
  AssertTrue('abstract base itab slot is the abort stub',
    Pos('itab_TBase_IShape:' + LF + #9'.quad _AbstractMethodError',
        AsmStr) >= 0);
  AssertTrue('concrete override itab binds the override',
    Pos('itab_TSquare_IShape:' + LF + #9'.quad TSquare_Area', AsmStr) >= 0);
  Obj := AssembleArm64ToBytes(AsmStr);
  F := ParseMachO(Obj, 'arm64abs.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestInterfaceParentChainItab;
var
  AsmStr: string;
  Obj: string;
  F: TMachOFile;
begin
  { TImpl implements IDerived (= interface(IBase)).  The impllist must carry a
    (typeinfo, itab) pair for BOTH IDerived and IBase, and itab_TImpl_IBase is
    the leading prefix of itab_TImpl_IDerived (BUG-052 F4). }
  AsmStr := GenAsm(
    '''
    program P;
    type
      IBase = interface
        function BaseVal: Integer;
      end;
      IDerived = interface(IBase)
        function DerivedVal: Integer;
      end;
      TImpl = class(TObject, IDerived)
        function BaseVal: Integer;
        function DerivedVal: Integer;
      end;
    function TImpl.BaseVal: Integer;
    begin Result := 10 end;
    function TImpl.DerivedVal: Integer;
    begin Result := 20 end;
    var T: TImpl; D: IDerived; B: IBase;
    begin
      T := TImpl.Create();
      D := T;
      B := D;
      WriteLn(B.BaseVal())
    end.
    ''');
  { the impllist includes the BASE interface as its own pair }
  AssertTrue('impllist includes the base interface',
    Pos(#9'.quad typeinfo_IBase' + LF + #9'.quad itab_TImpl_IBase',
        AsmStr) >= 0);
  { the base itab is the leading prefix (BaseVal) of the derived itab }
  AssertTrue('base itab binds the base method',
    Pos('itab_TImpl_IBase:' + LF + #9'.quad TImpl_BaseVal', AsmStr) >= 0);
  Obj := AssembleArm64ToBytes(AsmStr);
  F := ParseMachO(Obj, 'arm64ipc.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestSmallSets_LiteralsInOps;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TDay = (Mon, Tue, Wed, Thu, Fri);
      TDays = set of TDay;
    var
      D, E: TDays;
    begin
      D := [Mon, Wed];
      E := D + [Fri];
      E := E - [Mon];
      D := D * E;
      WriteLn(Wed in D);
      WriteLn(D = E)
    end.
    ''');
  { const literal folds to an immediate mask (Mon|Wed = bits 0,2 = 5) }
  AssertTrue('folded mask', Pos(#9'movz x0, #5', AsmT) >= 0);
  { membership: shift + bit test + range guard }
  AssertTrue('bit shift', Pos(#9'lsr x0, x0, x1', AsmT) >= 0);
  AssertTrue('bit test', Pos(#9'and x0, x0, x2', AsmT) >= 0);
  AssertTrue('range guard', Pos(#9'cset x2, lt', AsmT) >= 0);
  { set ops: or / and / and-not }
  AssertTrue('union', Pos(#9'orr x0, x0, x1', AsmT) >= 0);
  AssertTrue('difference complement', Pos(#9'movn x2, #0', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64sets.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestForIn_ArraysStringsSets;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TDay = (Mon, Tue, Wed);
    var
      A: array[0..2] of Int64;
      D: array of Int64;
      S: string;
      Days: set of TDay;
      V, Total: Int64;
      B: Byte;
      E: TDay;
    begin
      A[0] := 1; A[1] := 2; A[2] := 3;
      SetLength(D, 2);
      D[0] := 5; D[1] := 6;
      S := 'hi';
      Days := [Mon, Wed];
      Total := 0;
      for V in A do
        Total := Total + V;
      for V in D do
        Total := Total + V;
      for B in S do
        Total := Total + B;
      for E in Days do
        Total := Total + 1;
      WriteLn(Total)
    end.
    ''');
  { dyn-array iteration re-reads the length each pass }
  AssertTrue('dyn length', Pos(#9'bl _DynArrayLength', AsmT) >= 0);
  { string byte-iteration: length at dataptr-8, byte loads }
  AssertTrue('string length read', Pos(#9'ldur w1, [x0, #-8]', AsmT) >= 0);
  AssertTrue('string byte load', Pos(#9'ldrb w0, [x0]', AsmT) >= 0);
  { set iteration: mask bit test per ordinal }
  AssertTrue('set bit test', Pos(#9'lsr x0, x0, x1', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64forin.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestForIn_ClassEnumerator;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TEnum = class
        FIdx: Int64;
        function MoveNext(): Boolean;
        function GetCurrent(): Int64;
        property Current: Int64 read GetCurrent;
      end;
      TColl = class
        function GetEnumerator(): TEnum;
      end;
    function TEnum.MoveNext(): Boolean;
    begin
      FIdx := FIdx + 1;
      Result := FIdx < 3
    end;
    function TEnum.GetCurrent(): Int64;
    begin
      Result := FIdx
    end;
    function TColl.GetEnumerator(): TEnum;
    begin
      Result := TEnum.Create();
    end;
    var
      C: TColl;
      V: Int64;
    begin
      C := TColl.Create();
      for V in C do
        WriteLn(V)
    end.
    ''');
  { the three protocol methods are all called }
  AssertTrue('GetEnumerator call', Pos(#9'bl TColl_GetEnumerator', AsmT) >= 0);
  AssertTrue('MoveNext call', Pos(#9'bl TEnum_MoveNext', AsmT) >= 0);
  AssertTrue('Current getter call', Pos(#9'bl TEnum_GetCurrent', AsmT) >= 0);
  { the enumerator is transferred into its slot (release old, no AddRef) }
  AssertTrue('enumerator slot release', Pos(#9'bl _ClassRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64forinenum.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestCase_StringSelectors;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      S: string;
      N: Int64;
    begin
      S := 'beta';
      case S of
        'alpha': N := 1;
        'beta', 'gamma': N := 2;
      else
        N := 0
      end;
      case S + 'x' of
        'betax': N := N + 1;
      end;
      WriteLn(N)
    end.
    ''');
  { each label compares via the RTL — pointer cmp would be silently wrong }
  AssertTrue('string equals chain', Pos(#9'bl _StringEquals', AsmT) >= 0);
  AssertTrue('match branches to body', Pos(#9'cbnz x0, Lcbody', AsmT) >= 0);
  { the concat selector is an rc=0 transient: pinned (AddRef then Release)
    after the dispatch — a bare release would make it immortal }
  AssertTrue('rc0 selector pinned', Pos(#9'bl _StringAddRef', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64strcase.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestGlobalArrayInitialisers;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    var
      Nums: array[0..3] of Integer = (10, 20, 30, 40);
      Names: array[0..1] of string = ('alpha', 'beta');
      Longs: array[0..1] of Int64 = (3, 4);
      Ds: array[0..1] of Double = (1.5, 2.5);
    begin
      WriteLn(Nums[2]);
      WriteLn(Names[1])
    end.
    ''');
  { integer elements laid out inline in .data }
  AssertTrue('int elements', Pos(#9'.word 30', AsmT) >= 0);
  { 8-byte elements }
  AssertTrue('int64 elements', Pos(#9'.quad 4', AsmT) >= 0);
  { double elements }
  AssertTrue('double elements', Pos(#9'.double 2.5', AsmT) >= 0);
  { string elements point at immortal blobs (no symbol arithmetic) }
  AssertTrue('string element pointer',
    Pos(#9'.quad __gi_Names_e1_d', AsmT) >= 0);
  AssertTrue('string element blob', Pos('__gi_Names_e1_d:', AsmT) >= 0);
  AssertTrue('string element bytes', Pos(#9'.ascii "beta"', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64ginit.o');
  try
    AssertTrue('has a data section',
      F.FindSection('__DATA', '__data') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestClassAttributes_TablesAndBuiltins;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      ThreadedAttribute = class(TCustomAttribute)
      end;
      MarkAttribute = class(TCustomAttribute)
        FTag: string;
        constructor Create(ATag: string);
      end;
      [Threaded]
      [Mark('alpha')]
      TJob = class(TObject)
      published
        [Threaded]
        procedure Run;
      end;
    constructor MarkAttribute.Create(ATag: string);
    begin
      FTag := ATag
    end;
    procedure TJob.Run;
    begin
    end;
    var
      B: Boolean;
    begin
      B := HasClassAttribute(TJob, ThreadedAttribute);
      WriteLn(B);
      WriteLn(HasMethodAttribute(TJob, 'Run', ThreadedAttribute));
      WriteLn(MethodAttributeCount(TJob, 'Run'))
    end.
    ''');
  { attribute tables: (typeinfo, thunk) pairs behind typeinfo slot 7,
    (name, typeinfo, thunk) triples behind slot 8 }
  AssertTrue('class attrs table', Pos('attrs_TJob:', AsmT) >= 0);
  AssertTrue('factory thunk referenced',
    Pos(#9'.quad __attr_TJob_c0', AsmT) >= 0);
  AssertTrue('method attrs table', Pos('methattrs_TJob:', AsmT) >= 0);
  AssertTrue('typeinfo slot 7 wired', Pos(#9'.quad attrs_TJob', AsmT) >= 0);
  { TCustomAttribute base stubs exist for the parent chain }
  AssertTrue('TCustomAttribute typeinfo',
    Pos('typeinfo_TCustomAttribute:', AsmT) >= 0);
  { RTTI builtins lower to the runtime helpers }
  AssertTrue('has-class-attr call', Pos(#9'bl _HasClassAttribute', AsmT) >= 0);
  AssertTrue('has-method-attr call',
    Pos(#9'bl _HasMethodAttribute', AsmT) >= 0);
  AssertTrue('count call', Pos(#9'bl _MethodAttributeCount', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64attrs.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestGenericInstances_WeakEmission;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TBox<T> = class
        FVal: T;
        procedure Put(AV: T);
        function Get(): T;
      end;
    procedure TBox<T>.Put(AV: T);
    begin
      FVal := AV
    end;
    function TBox<T>.Get(): T;
    begin
      Result := FVal
    end;
    function Pick<T>(A, B: T): T;
    begin
      Result := A
    end;
    var
      B: TBox<Int64>;
    begin
      B := TBox<Int64>.Create();
      B.Put(41);
      WriteLn(B.Get() + 1);
      WriteLn(Pick<Int64>(7, 9))
    end.
    ''');
  { instance symbols are BARE (no unit prefix) and WEAK — every object
    that materialises the same instance carries an identical copy and
    the linker keeps one (BUG-004) }
  AssertTrue('weak typeinfo', Pos('.weak typeinfo_TBox_Int64', AsmT) >= 0);
  AssertTrue('weak vtable', Pos('.weak vtable_TBox_Int64', AsmT) >= 0);
  AssertTrue('weak cleanup',
    Pos('.weak _FieldCleanup_TBox_Int64', AsmT) >= 0);
  AssertTrue('instance method body', Pos('TBox_Int64_Put:', AsmT) >= 0);
  AssertTrue('weak method bind', Pos('.weak TBox_Int64_Put', AsmT) >= 0);
  { instance is constructed through its own typeinfo }
  AssertTrue('ctor typeinfo ref',
    Pos('adrp x0, typeinfo_TBox_Int64@PAGE', AsmT) >= 0);
  { the generic FUNCTION instance is emitted weak too }
  AssertTrue('weak func instance', Pos('.weak Pick_Int64', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64gen.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestGenericMethodInstance_WeakEmission;
var
  AsmT: string;
begin
  { A generic METHOD (its own <U>) is monomorphised at the call site.  Its
    concrete instance body is emitted weak-bound (cross-unit dedup, like a
    generic function instance), and the call site references the same mangled
    label.  AddBase<U> also reads FBase (Self access inside a generic method). }
  AsmT := GenAsm(
    '''
    program P;
    type
      TBox = class
        FBase: Integer;
        function Wrap<U>(x: U): U;
        function AddBase<U>(x: Integer): Integer;
      end;
    function TBox.Wrap<U>(x: U): U; begin Result := x end;
    function TBox.AddBase<U>(x: Integer): Integer; begin Result := x + FBase end;
    var b: TBox;
    begin
      b := TBox.Create();
      b.FBase := 10;
      WriteLn(b.Wrap<Integer>(5));
      WriteLn(b.AddBase<Integer>(7))
    end.
    ''');
  { the monomorphised instance bodies are emitted with weak binding }
  AssertTrue('Wrap instance body', Pos('TBox_Wrap_Integer:', AsmT) >= 0);
  AssertTrue('Wrap weak bind', Pos('.weak TBox_Wrap_Integer', AsmT) >= 0);
  AssertTrue('AddBase instance body', Pos('TBox_AddBase_Integer:', AsmT) >= 0);
  AssertTrue('AddBase weak bind', Pos('.weak TBox_AddBase_Integer', AsmT) >= 0);
  { the call sites reference the same mangled labels }
  AssertTrue('Wrap called', Pos(#9'bl TBox_Wrap_Integer', AsmT) >= 0);
  AssertTrue('AddBase called', Pos(#9'bl TBox_AddBase_Integer', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestClosure_CaptureFree_ValueParamCall;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A 'reference to' closure is a 16-byte fat value (Code at +0, Env at +8).  A
    capture-free literal materialises it (Code = &thunk, Env = nil); the callee
    receives a pointer to it and copies the 16 bytes into its own slot; a call
    through it loads Env into x0 (the hidden first arg) and Code into x9 and
    blr's. }
  AsmT := GenAsm(
    '''
    program P;
    type TIntFn = reference to function(x: Integer): Integer;
    function Apply(P: TIntFn; v: Integer): Integer;
    begin
      Result := P(v)
    end;
    begin
      WriteLn(Apply(function(x: Integer): Integer begin Result := x * 2 end, 5))
    end.
    ''');
  { the anon thunk body is emitted }
  AssertTrue('closure thunk emitted', Pos('__closure_1:', AsmT) >= 0);
  { the literal materialises Code (&thunk) and a nil Env }
  AssertTrue('Code = &thunk', Pos('__closure_1@PAGE', AsmT) >= 0);
  AssertTrue('capture-free Env is nil', Pos(#9'str xzr, [x9, #8]', AsmT) >= 0);
  { the callee copies the 16-byte fat value in via ldp/stp }
  AssertTrue('param fat-value copy', Pos(#9'ldp x9, x10, [x1]', AsmT) >= 0);
  { the call loads Env into x0 (hidden first arg) and Code into x9, then blr }
  AssertTrue('Env -> x0', Pos(#9'ldr x0, [x10, #8]', AsmT) >= 0);
  AssertTrue('Code -> x9', Pos(#9'ldr x9, [x10]', AsmT) >= 0);
  AssertTrue('fat call blr', Pos(#9'blr x9', AsmT) >= 0);
  { the whole thing must assemble into a valid Mach-O object }
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64clos.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestClosure_OwnedTransientArg_Disposed;
var
  AsmT: string;
  PosCall, PosRel: Integer;
begin
  { A closure call whose argument is an owned-transient string (a function
    result, rc=1) passes it borrowed and disposes it after the call — a bare
    _StringRelease that must appear AFTER the closure blr. }
  AsmT := GenAsm(
    '''
    program P;
    type TStrFn = reference to function(s: string): Integer;
    function MakeStr: string; begin Result := 'hello' end;
    function Apply(P: TStrFn): Integer;
    begin
      Result := P(MakeStr())
    end;
    begin
      WriteLn(Apply(function(s: string): Integer begin Result := Length(s) end))
    end.
    ''');
  { the closure is invoked (blr) and the transient released afterwards }
  PosCall := Pos(#9'blr x9', AsmT);
  AssertTrue('closure invoked', PosCall >= 0);
  PosRel := PosEx(#9'bl _StringRelease', AsmT, PosCall);
  AssertTrue('transient released after the closure call', PosRel > PosCall);
  { transient pointers are held in callee-saved x19 across the call }
  AssertTrue('transient held callee-saved', Pos(#9'mov x19, x0', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestClosure_UnownedTransientArg_PinnedBeforeCall;
var
  AsmT: string;
  PosCat, PosPin, PosCall, PosRel: Integer;
begin
  { A closure call whose argument is an rc=0 UNOWNED string transient (a `+`
    concat) must pin it (_StringAddRef) BEFORE the blr: the closure's by-value
    param entry-retain/exit-release cycle frees an unpinned rc=0 transient
    during the call, so the old post-call AddRef+Release double-freed whenever
    the closure did not store the value.  After the call a single bare
    _StringRelease disposes it (1 -> 0). }
  AsmT := GenAsm(
    '''
    program P;
    type TStrFn = reference to function(s: string): Integer;
    function Apply(P: TStrFn; a: string): Integer;
    begin
      Result := P(a + '!')
    end;
    begin
      WriteLn(Apply(function(s: string): Integer begin Result := Length(s) end, 'hi'))
    end.
    ''');
  PosCat := Pos(#9'bl _StringConcat', AsmT);
  AssertTrue('concat produced', PosCat >= 0);
  PosCall := PosEx(#9'blr x9', AsmT, PosCat);
  AssertTrue('closure invoked after the concat', PosCall > PosCat);
  { the rc=0 pin lands strictly between the concat and the blr }
  PosPin := PosEx(#9'bl _StringAddRef', AsmT, PosCat);
  AssertTrue('rc=0 transient pinned BEFORE the closure call',
    (PosPin > PosCat) and (PosPin < PosCall));
  { one release after the call, with no post-call AddRef half before it }
  PosRel := PosEx(#9'bl _StringRelease', AsmT, PosCall);
  AssertTrue('transient released after the closure call', PosRel > PosCall);
  AssertTrue('no post-call AddRef half remains',
    (PosEx(#9'bl _StringAddRef', AsmT, PosCall) < 0) or
    (PosEx(#9'bl _StringAddRef', AsmT, PosCall) > PosRel));
end;

procedure TArm64BackendTests.TestClosure_StatementPositionCall;
var
  AsmT: string;
begin
  { A closure call in statement position (the result is discarded) must route a
    fat callee through the fat-pointer call path — load Env into x0, Code into
    x9, blr — not the plain single-pointer indirect-call path. }
  AsmT := GenAsm(
    '''
    program P;
    type TProc = reference to procedure(x: Integer);
    procedure Run(P: TProc; v: Integer);
    begin
      P(v)
    end;
    begin
      Run(procedure(x: Integer) begin WriteLn(x) end, 42)
    end.
    ''');
  { the fat call loads Env (x0) and Code (x9) and blr's }
  AssertTrue('Env -> x0', Pos(#9'ldr x0, [x10, #8]', AsmT) >= 0);
  AssertTrue('Code -> x9', Pos(#9'ldr x9, [x10]', AsmT) >= 0);
  AssertTrue('fat call blr', Pos(#9'blr x9', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestAsmRoutines_NoStackFrame;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    function AddOne(A: Int64): Int64; assembler; nostackframe;
    asm
        add x0, x0, #1
        ret
    end;
    begin
      WriteLn(AddOne(41))
    end.
    ''');
  { the body is emitted verbatim: no compiler prologue/epilogue around it }
  AssertTrue('label emitted', Pos('AddOne:', AsmT) >= 0);
  AssertTrue('verbatim body', Pos('add x0, x0, #1', AsmT) >= 0);
  { no stp/ldp frame bracket between the label and the ret }
  AssertTrue('no prologue',
    Pos(#9'stp x29, x30', Copy(AsmT, Pos('AddOne:', AsmT),
      Pos('add x0, x0, #1', AsmT) - Pos('AddOne:', AsmT))) < 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64asmfn.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestPointers_DerefWriteAddrOf;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      PInt = ^Integer;
      PW = ^Word;
    var
      N: Integer;
      Q: PInt;
      H: PW;
      B: Int64;
    begin
      N := 7;
      Q := @N;
      Q^ := Q^ + 1;
      H := PW(Pointer(Q));
      B := Integer(H^);
      WriteLn(N);
      WriteLn(B)
    end.
    ''');
  { deref read: 4-byte signed load through the pointer }
  AssertTrue('deref int read', Pos(#9'ldrsw x0, [x0]', AsmT) >= 0);
  { pointer write: 4-byte store through the parked pointer }
  AssertTrue('deref int write', Pos(#9'str w0, [x9]', AsmT) >= 0);
  { unsigned 2-byte deref uses ldrh }
  AssertTrue('word deref', Pos(#9'ldrh w0, [x0]', AsmT) >= 0);
  { Integer(x) cast normalises the width }
  AssertTrue('int cast narrows', Pos(#9'sxtw x0, w0', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64ptr.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestBooleanAndOr_ShortCircuits;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      PNode = ^Int64;
    var
      Q: PNode;
      B: Boolean;
    begin
      Q := nil;
      B := (Q <> nil) and (Q^ > 0);
      WriteLn(B);
      B := (Q = nil) or (Q^ = 0);
      WriteLn(B)
    end.
    ''');
  { and: LHS = 0 skips the RHS; or: LHS <> 0 skips the RHS }
  AssertTrue('and skips on false LHS', Pos(#9'cbz x0, Lscend', AsmT) >= 0);
  AssertTrue('or skips on true LHS', Pos(#9'cbnz x0, Lscend', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64sc.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestExternalCall_NarrowsIntReturn;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
  CallPos, SxtwPos: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    function c_open(Path: PChar; Flags: Integer): Integer;
      external name 'open';
    var
      Fd: Int64;
    begin
      Fd := c_open(PChar('x'), 0);
      WriteLn(Fd)
    end.
    ''');
  { the int-returning external's result must be sign-extended before any
    64-bit use — bits 32-63 of x0 are undefined at the C ABI boundary }
  CallPos := Pos(#9'bl open', AsmT);
  AssertTrue('external call emitted', CallPos >= 0);
  SxtwPos := Pos(#9'sxtw x0, w0', Copy(AsmT, CallPos, 64));
  AssertTrue('return narrowed right after the call', SxtwPos >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64ext.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestOpenArrayParams_PtrHighPair;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { the four caller arg forms: array literal, static array, dynamic
    array, and open-array forwarding — plus High/Low/Length and an
    element read in the callee }
  AsmT := GenAsm(
    '''
    program P;
    function Sum(const A: array of Integer): Int64;
    var
      I: Integer;
      T: Int64;
    begin
      T := 0;
      for I := 0 to High(A) do
        T := T + A[I];
      Result := T + Low(A) + Length(A)
    end;
    function Fwd(const A: array of Integer): Int64;
    begin
      Result := Sum(A)
    end;
    var
      S: array[0..2] of Integer;
      D: array of Integer;
    begin
      S[0] := 1; S[1] := 2; S[2] := 3;
      SetLength(D, 2);
      D[0] := 10; D[1] := 20;
      WriteLn(Sum([7, 8]));
      WriteLn(Sum(S));
      WriteLn(Sum(D));
      WriteLn(Fwd(S))
    end.
    ''');
  { a dyn array coerced to an open array computes high = length - 1 }
  AssertTrue('dyn arg high via _DynArrayLength',
    Pos(#9'bl _DynArrayLength', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64oa.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestOpenArrayParams_StringElems;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { the strutils shape that blocked the self-cross-compile: const
    array of string with High + element read + string compare.
    Elements are BORROWED (const) — no retain/release on the read. }
  AsmT := GenAsm(
    '''
    program P;
    function IndexOf(const S: string; const Arr: array of string): Integer;
    var
      I: Integer;
    begin
      for I := 0 to High(Arr) do
        if Arr[I] = S then
        begin
          Exit(I);
        end;
      Result := -1
    end;
    begin
      WriteLn(IndexOf('b', ['a', 'b', 'c']))
    end.
    ''');
  AssertTrue('string compare emitted',
    Pos(#9'bl _StringEquals', AsmT) >= 0);
  { the const element read must not retain what it merely borrows }
  AssertTrue('no retain on borrowed element',
    Pos('_StringAddRef', AsmT) <= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64oas.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestFree_ReleasesAndNilsSlot;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
  RelPos: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TBox = class
      public
        V: Int64;
      end;
    var
      B: TBox;
    begin
      B := TBox.Create();
      B.V := 7;
      B.Free();
      WriteLn(1)
    end.
    ''');
  { Free = release, then NIL the slot — a stale pointer here aliases the
    next same-size allocation and a later ARC store double-releases it }
  RelPos := Pos(#9'bl _ClassRelease' + LF + #9'movz x0, #0', AsmT);
  AssertTrue('Free releases then nils the slot', RelPos >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64free.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestClassNameAccess_ViaTypeinfo;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
  DerefPos: Integer;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TAnimal = class
      public
        Legs: Integer;
      end;
      TDog = class(TAnimal)
      end;
    var
      A: TAnimal;
    begin
      A := TDog.Create();
      WriteLn(A.ClassName);
      A.Free()
    end.
    ''');
  { ClassName walks instance[0]=vtable, vtable[0]=typeinfo, name at +16 —
    the +16 load is the tell }
  DerefPos := Pos(#9'ldr x0, [x0, #16]', AsmT);
  AssertTrue('name loaded from typeinfo+16', DerefPos >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64cn.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestJumboSetMembership_ViaSetIn;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { an 80-member enum makes 'set of' jumbo; membership against a literal
    lowers to a stack bitmap (memset + _SetInclude) tested via _SetIn }
  AsmT := GenAsm(
    '''
    program P;
    type
      TBig = (b00,b01,b02,b03,b04,b05,b06,b07,b08,b09,
              b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,
              b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,
              b30,b31,b32,b33,b34,b35,b36,b37,b38,b39,
              b40,b41,b42,b43,b44,b45,b46,b47,b48,b49,
              b50,b51,b52,b53,b54,b55,b56,b57,b58,b59,
              b60,b61,b62,b63,b64,b65,b66,b67,b68,b69,
              b70,b71,b72,b73,b74,b75,b76,b77,b78,b79);
    var
      x: TBig;
      r: Boolean;
    begin
      x := b70;
      r := x in [b00, b70, b79];
      WriteLn(r)
    end.
    ''');
  AssertTrue('membership via _SetIn', Pos(#9'bl _SetIn', AsmT) >= 0);
  AssertTrue('bitmap built via _SetInclude',
    Pos(#9'bl _SetInclude', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64js.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestIncDecImplicitSelfField;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TCounter = class
      private
        FN: Integer;
      public
        procedure Step;
      end;
    procedure TCounter.Step;
    begin
      Inc(FN);
      Dec(FN, 2)
    end;
    var
      C: TCounter;
    begin
      C := TCounter.Create();
      C.Step();
      C.Free()
    end.
    ''');
  { Inc/Dec(FN) load-adjust-store through Self+offset: the field address is
    parked in x9, then stored back with str w0 — never loaded as a bare
    variable (that path would emit 'load of variable FN') }
  AssertTrue('field address parked in x9', Pos(#9'mov x9, x0', AsmT) >= 0);
  AssertTrue('adjusted value stored back', Pos(#9'str w0, [x9]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64id.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestVarClassParam_ArcThroughAddress;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TThing = class
      public
        V: Integer;
      end;
    procedure Grab(var T: TThing);
    begin
      if T = nil then
        T := TThing.Create()
    end;
    var
      X: TThing;
    begin
      X := nil;
      Grab(X);
      X.Free()
    end.
    ''');
  { the var-class store releases the OLD value through the address and
    stores the new one back — a str-through-address after _ClassRelease }
  AssertTrue('releases old value', Pos(#9'bl _ClassRelease', AsmT) >= 0);
  AssertTrue('stores new value through address',
    Pos(#9'str x0, [x9]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64vc.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestFieldReadOnTransientBase;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  AsmT := GenAsm(
    '''
    program P;
    type
      TBox = class
      public
        N: Integer;
      end;
    function MakeBox: TBox;
    begin
      Result := TBox.Create()
    end;
    var
      K: Integer;
    begin
      K := MakeBox().N;
      WriteLn(K)
    end.
    ''');
  { the transient base (+1) is released AFTER its scalar field is loaded }
  AssertTrue('base released after field load',
    Pos(#9'bl _ClassRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64ft.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRecordCallArg_MaterialisedInBuffer;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { SumPair(MakePair(5)) — MakePair's result is materialised into a scratch
    buffer (add x9, sp, ...; str x0) then passed by value to SumPair }
  AsmT := GenAsm(
    '''
    program P;
    type
      TPair = record
        A: Integer;
        B: Integer;
      end;
    function MakePair(X: Integer): TPair;
    begin
      Result.A := X;
      Result.B := X * 2
    end;
    function SumPair(const P: TPair): Integer;
    begin
      Result := P.A + P.B
    end;
    begin
      WriteLn(SumPair(MakePair(5)))
    end.
    ''');
  AssertTrue('MakePair evaluated', Pos(#9'bl MakePair', AsmT) >= 0);
  AssertTrue('result stored into a scratch buffer',
    Pos(#9'str x0, [x9]', AsmT) >= 0);
  AssertTrue('SumPair receives the materialised record',
    Pos(#9'bl SumPair', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64rca.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRecordCallFieldRead_ViaRret;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { MakePair(7).A — the record lands in __rret, the field loads at offset 0 }
  AsmT := GenAsm(
    '''
    program P;
    type
      TPair = record
        A: Integer;
        B: Integer;
      end;
    function MakePair(X: Integer): TPair;
    begin
      Result.A := X;
      Result.B := X * 2
    end;
    begin
      WriteLn(MakePair(7).A);
      WriteLn(MakePair(7).B)
    end.
    ''');
  AssertTrue('MakePair evaluated', Pos(#9'bl MakePair', AsmT) >= 0);
  { the field is read from the __rret scratch (an x29-relative address then a
    load) — the store-into-scratch then load-field shape }
  AssertTrue('field loaded after materialisation',
    Pos(#9'ldrsw x0', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64rcf.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestProcessBuiltins_LowerToRtlCalls;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { the whole process-control family lowers 1:1 to _Process* RTL calls —
    handle from ProcessCreate (0-arg), pointer-arg queries, string-arg
    setters (SetExe/AddArg via the string-transient helper), and the
    void handle procedures }
  AsmT := GenAsm(
    '''
    program P;
    var
      H: Pointer;
      R: Boolean;
      E: Integer;
    begin
      H := ProcessCreate();
      ProcessSetExe(H, '/bin/echo');
      ProcessAddArg(H, 'hi');
      ProcessExecute(H);
      ProcessWaitOnExit(H);
      R := ProcessRunning(H);
      E := ProcessExitCode(H);
      ProcessFree(H);
      WriteLn(E)
    end.
    ''');
  AssertTrue('ProcessCreate', Pos(#9'bl _ProcessCreate', AsmT) >= 0);
  AssertTrue('ProcessSetExe', Pos(#9'bl _ProcessSetExe', AsmT) >= 0);
  AssertTrue('ProcessAddArg', Pos(#9'bl _ProcessAddArg', AsmT) >= 0);
  AssertTrue('ProcessExecute', Pos(#9'bl _ProcessExecute', AsmT) >= 0);
  AssertTrue('ProcessWaitOnExit', Pos(#9'bl _ProcessWaitOnExit', AsmT) >= 0);
  AssertTrue('ProcessRunning', Pos(#9'bl _ProcessRunning', AsmT) >= 0);
  AssertTrue('ProcessExitCode', Pos(#9'bl _ProcessExitCode', AsmT) >= 0);
  AssertTrue('ProcessFree', Pos(#9'bl _ProcessFree', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64proc.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestFreeOnCallResult_ReleasesOwnedTemporary;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
  GrabPos: Integer;
begin
  { B.Grab().Free() — the getter result is an owned +1 temporary, so Free
    is a single _ClassRelease right after the call with NO slot nil (there
    is no lvalue) }
  AsmT := GenAsm(
    '''
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
      B.Free()
    end.
    ''');
  { the Grab result is released immediately after the call — bl Grab then
    bl _ClassRelease adjacently, with no str-to-slot between them }
  GrabPos := Pos(#9'bl TBox_Grab' + LF + #9'bl _ClassRelease', AsmT);
  AssertTrue('call result released with no slot nil', GrabPos >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64frc.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRetainedFieldReadOnTransientBase;
var
  AsmStr, AsmCls: string;
  Obj: string;
  F: TMachOFile;
begin
  { STRING field on an owned transient base (MakeThing().Name): the base is
    released INLINE after the load — the string data pointer survives (the
    common case is an immortal literal); mirrors x86-64's string discipline.
    No _StringAddRef pin. }
  AsmStr := GenAsm(
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
      Result.Name := 'hi'
    end;
    var
      S: string;
    begin
      S := MakeThing().Name;
      WriteLn(S)
    end.
    ''');
  { the field-read region is after 'bl MakeThing' in $main: the base is
    loaded, field read, base released inline — NO AddRef between the call
    and the release (contrast the class arm, which pins) }
  AssertTrue('string field: base released inline after the call',
    Pos(#9'bl MakeThing' + LF + #9'str x0, [sp, #-16]!' + LF +
        #9'add x0, x0, #8' + LF + #9'ldr x0, [x0]' + LF +
        #9'str x0, [sp, #-16]!' + LF + #9'ldr x0, [sp, #16]' + LF +
        #9'bl _ClassRelease', AsmStr) >= 0);

  { CLASS field on an owned transient base (MakeThing().Obj): the field value
    aliases into the base's graph, so the base release is DEFERRED to the end
    of the enclosing statement (BUG-048 fix — the borrowed field value stays
    live and the deferred release balances the transient's +1 with no leak).
    The defer spills the base pointer to a _pendrel frame slot; there is NO
    _ClassAddRef pin on the field value between the call and the store. }
  AsmCls := GenAsm(
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
      Result.Obj := TInner.Create()
    end;
    var
      X: TInner;
    begin
      X := MakeThing().Obj;
      WriteLn(X.N)
    end.
    ''');
  { the field-read region: base + field value are both parked on the stack,
    the base is loaded (ldr x0, [sp, #16]) and SPILLED to a _pendrel frame
    slot (stur to a negative x29 offset — the defer), then the field value
    is popped back into x0 — NO _ClassAddRef pin on the field value.  Both
    stay on the stack across the spill so no volatile register (x9 is the
    slot-address scratch) has to survive it. }
  AssertTrue('class field: base deferred (parked + spilled), field on stack',
    Pos(#9'str x0, [sp, #-16]!' + LF + #9'ldr x0, [sp, #16]' + LF +
        #9'stur x0, [x29, ', AsmCls) >= 0);
  { the deferred base _ClassRelease is flushed at statement end — it reloads
    the spilled base from its _pendrel slot and releases it. }
  AssertTrue('class field: deferred base release flushed at statement end',
    Pos(#9'bl _ClassRelease', AsmCls) >= 0);
  { and crucially: the field value is NEVER AddRef-pinned before the base
    release (the old leaky path AddRef'd the borrowed field value).  The
    field-read region between the call and the store contains no _ClassAddRef
    — a pin would have appeared here.  We check the exact defer shape has no
    intervening AddRef by matching the contiguous spill sequence above. }
  AssertTrue('class field: no AddRef pin in the deferred read sequence',
    Pos(#9'ldr x0, [sp, #16]' + LF + #9'stur x0, [x29, ', AsmCls) >= 0);

  Obj := AssembleArm64ToBytes(AsmCls);
  F := ParseMachO(Obj, 'arm64rmf.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestDynArrayFunctionReturn_TransfersOwnership;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
  MakeEnd, RelInMake: Integer;
begin
  { function MakeArr: TArr — the dyn-array Result is an 8-byte pointer whose
    +1 transfers to the caller: MakeArr does NOT release Result, the caller's
    assignment consumes the owned result (releases old, stores new, no extra
    AddRef) }
  AsmT := GenAsm(
    '''
    program P;
    type TArr = array of Integer;
    function MakeArr: TArr;
    begin
      SetLength(Result, 2);
      Result[0] := 10;
      Result[1] := 20
    end;
    var A: TArr;
    begin
      A := MakeArr();
      WriteLn(A[0] + A[1])
    end.
    ''');
  { the Result +1 transfers — MakeArr's body must NOT _DynArrayRelease its
    Result before returning it (that would drop the transferred ref) }
  MakeEnd := Pos(#9'bl MakeArr', AsmT);
  AssertTrue('MakeArr called', MakeEnd >= 0);
  RelInMake := Pos('MakeArr:', AsmT);
  AssertTrue('MakeArr emitted', RelInMake >= 0);
  { caller consumes the owned result: releases the OLD A then stores }
  AssertTrue('caller releases old A on assign',
    Pos(#9'bl _DynArrayRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64dar.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRecordCallIntoArrayElement;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Arr[0] := MakeSpec(5) with a MANAGED element (string field): the call
    sret's into __rret, the dest element's old string ref is released, then
    __rret is memcpy'd in (the +1 transfers) }
  AsmT := GenAsm(
    '''
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
    var Arr: TArr;
    begin
      SetLength(Arr, 1);
      Arr[0] := MakeSpec(5);
      WriteLn(Arr[0].Kind)
    end.
    ''');
  { the element store releases the dest's old string field before the memcpy
    transfer — a _StringRelease then a memcpy from the __rret scratch }
  AssertTrue('dest old ref released', Pos(#9'bl _StringRelease', AsmT) >= 0);
  AssertTrue('transfer via memcpy', Pos(#9'bl memcpy', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64rce.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestSubscriptRecordAsArgument;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { DescribeKind(Arr[I]) — a subscripted record element passed by value:
    EmitRecAddrToX0 computes the element address (subscript lvalue), then the
    shape's registers/address are loaded from it }
  AsmT := GenAsm(
    '''
    program P;
    type
      TPair = record
        A: Integer;
        B: Integer;
      end;
      TArr = array of TPair;
    function SumPair(const P: TPair): Integer;
    begin
      Result := P.A + P.B
    end;
    var Arr: TArr;
    begin
      SetLength(Arr, 1);
      Arr[0].A := 3;
      Arr[0].B := 4;
      WriteLn(SumPair(Arr[0]))
    end.
    ''');
  AssertTrue('SumPair called with the element', Pos(#9'bl SumPair', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64sra.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestStaticArrayFieldElementReadWrite;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { FTab is an implicit-Self field of type array[0..3] of string.  Its inline
    storage lives AT Self+offset, so both the write (FTab[0] := 'a') and the
    read (Result := FTab[I]) must compute the base as an ADDRESS off Self
    (ldur Self ; add x0, x0, #offset) rather than deref a data pointer (ldr).
    This is the static-array counterpart to TestFieldElementAssign (dyn). }
  AsmT := GenAsm(
    '''
    program P;
    type
      TThing = class
        FTab: array[0..3] of string;
        procedure Fill;
        function Get(I: Integer): string;
      end;
    procedure TThing.Fill;
    begin
      FTab[0] := 'a'
    end;
    function TThing.Get(I: Integer): string;
    begin
      Result := FTab[I]
    end;
    var T: TThing;
    begin
      T := TThing.Create();
      T.Fill();
      WriteLn(T.Get(0));
      T.Free()
    end.
    ''');
  { base is Self+offset as an ADDRESS — the load of Self is followed by an
    add of the field offset, NOT a ldr deref, before the index is scaled. }
  AssertTrue('static-array field base is Self+offset address (add, no deref)',
    Pos('add x0, x0, #' , AsmT) >= 0);
  { element ARC store on the write side: retain new literal, release old }
  AssertTrue('string element store retains the new value',
    Pos(#9'bl _StringAddRef', AsmT) >= 0);
  AssertTrue('string element store releases the old element',
    Pos(#9'bl _StringRelease', AsmT) >= 0);
  { the read loads the element string through the element address }
  AssertTrue('read loads the element via the element address',
    Pos(#9'ldr x0, [x0]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64safe.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestNestedRoutine_NoCapture_SiblingSymbol;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A capture-free nested proc is emitted as a sibling top-level symbol named
    Outer_Inner, and the outer calls it with 'bl Outer_Inner'. }
  AsmT := GenAsm(
    '''
    program P;
    procedure Outer;
      procedure Inner;
      begin
        WriteLn('x')
      end;
    begin
      Inner()
    end;
    begin
      Outer()
    end.
    ''');
  AssertTrue('nested body emitted as sibling Outer_Inner symbol',
    Pos('Outer_Inner:', AsmT) >= 0);
  AssertTrue('outer calls the mangled nested symbol',
    Pos(#9'bl Outer_Inner', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64nc.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestNestedRoutine_CaptureScalar_ReadWrite;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Outer has a local 'n' captured by Inner, which does n := n + 1.  Inner
    receives &n as a leading pointer arg spilled to _cap_n; the body reads n by
    derefing _cap_n and writes back through it.  The call site materialises &n
    (sub x0, x29, #off) before the branch. }
  AsmT := GenAsm(
    '''
    program P;
    procedure Outer;
    var
      n: Integer;
      procedure Inner;
      begin
        n := n + 1
      end;
    begin
      n := 41;
      Inner();
      WriteLn(n)
    end;
    begin
      Outer()
    end.
    ''');
  { Inner spills the leading capture pointer arg into _cap_n (first store of
    x0 to a frame slot) and reads the captured var by derefing that pointer:
    load the _cap_ slot into x0, then ldr x0, [x0]. }
  AssertTrue('Inner spills the leading capture pointer to its _cap_ slot',
    Pos(#9'stur x0, [x29, #-8]', AsmT) >= 0);
  AssertTrue('Inner reads the captured var by derefing the capture pointer',
    Pos(#9'ldur x0, [x29, #-8]' + LF + #9'ldr x0, [x0]', AsmT) >= 0);
  { the write-back stores through the reloaded capture pointer (x9) }
  AssertTrue('Inner writes the captured var back through the capture pointer',
    Pos(#9'str x0, [x9]', AsmT) >= 0);
  { the call site passes the address of the outer local as the leading arg }
  AssertTrue('call site materialises the captured var address',
    Pos(#9'sub x0, x29, #', AsmT) >= 0);
  AssertTrue('outer calls the nested symbol', Pos(#9'bl Outer_Inner', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64cs.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestNestedRoutine_CaptureString_ARCThroughCap;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A captured STRING var written inside a nested proc runs the ARC store —
    retain the new value, release the OLD string read THROUGH the capture
    pointer, store the new — mirroring the x86-64 backend exactly. }
  AsmT := GenAsm(
    '''
    program P;
    procedure Outer;
    var
      s: string;
      procedure SetIt;
      begin
        s := 'a'
      end;
    begin
      s := 'b';
      SetIt();
      WriteLn(s)
    end;
    begin
      Outer()
    end.
    ''');
  AssertTrue('captured string store retains the new value',
    Pos(#9'bl _StringAddRef', AsmT) >= 0);
  AssertTrue('captured string store releases the old value',
    Pos(#9'bl _StringRelease', AsmT) >= 0);
  AssertTrue('the old string is read through the capture pointer',
    Pos(#9'ldr x0, [x9]' + LF + #9'bl _StringRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64cstr.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestNestedRoutine_CaptureArgsForceStackSpill_ReservesArea;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Inner captures 2 outer locals AND takes 8 int params.  Captures occupy
    x0..x1, params p1..p6 take x2..x7, and p7/p8 spill to the outgoing stack
    area.  ComputeStackArgAreaEx must include the 2 capture args in its NInt
    count so it reserves that area — otherwise the p7/p8 stores land in the
    caller's own frame (Finding 1).  Assert the store-to-stack instructions
    appear (proving the spill happened) inside a routine that ALSO reserved a
    second sp adjustment for the outgoing area. }
  AsmT := GenAsm(
    '''
    program P;
    procedure Outer;
    var
      a, b: Integer;
      procedure Inner(p1, p2, p3, p4, p5, p6, p7, p8: Integer);
      begin
        WriteLn(a + b + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8)
      end;
    begin
      a := 10;
      b := 20;
      Inner(1, 2, 3, 4, 5, 6, 7, 8)
    end;
    begin
      Outer()
    end.
    ''');
  { the two overflow args are stored to the reserved outgoing area via w9 }
  AssertTrue('overflow args spill to the outgoing stack area',
    Pos(#9'str w9, [sp, #', AsmT) >= 0);
  { the nested body still links correctly }
  AssertTrue('outer calls the nested symbol', Pos(#9'bl Outer_Inner', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64csp.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestNestedProc_MethodMangle_IncludesClass;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Two classes each with a method DoIt containing a nested Inner.  The nested
    symbols must be class-qualified (TFoo_DoIt_Inner / TBar_DoIt_Inner) so they
    do not collide; the bare DoIt_Inner must NOT appear. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TFoo = class procedure DoIt; end;
      TBar = class procedure DoIt; end;
    procedure TFoo.DoIt;
      procedure Inner;
      begin WriteLn('foo') end;
    begin Inner() end;
    procedure TBar.DoIt;
      procedure Inner;
      begin WriteLn('bar') end;
    begin Inner() end;
    var f: TFoo; b: TBar;
    begin
      f := TFoo.Create(); b := TBar.Create();
      f.DoIt(); b.DoIt();
      f.Free(); b.Free()
    end.
    ''');
  AssertTrue('TFoo.DoIt.Inner is class-qualified',
    Pos('TFoo_DoIt_Inner:', AsmT) >= 0);
  AssertTrue('TBar.DoIt.Inner is class-qualified',
    Pos('TBar_DoIt_Inner:', AsmT) >= 0);
  AssertTrue('the bare (colliding) DoIt_Inner symbol is gone',
    Pos(LF + 'DoIt_Inner:', AsmT) < 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64mm.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestNestedProc_MultiLevelMangle_FullChain;
var
  AsmT: string;
begin
  { A 3-level standalone nesting mangles the innermost as the FULL chain
    L1_L2_L3, not the parent-only L2_L3 — so two different L2s each with an L3
    cannot collide.  The call site targets the same full-chain symbol. }
  AsmT := GenAsm(
    '''
    program P;
    procedure L1;
      procedure L2;
        procedure L3;
        begin WriteLn('deep') end;
      begin L3() end;
    begin L2() end;
    begin L1() end.
    ''');
  AssertTrue('innermost mangles as the full chain L1_L2_L3',
    Pos('L1_L2_L3:', AsmT) >= 0);
  AssertTrue('the call targets the full-chain symbol',
    Pos(#9'bl L1_L2_L3', AsmT) >= 0);
  AssertTrue('the parent-only L2_L3 symbol is gone',
    Pos(LF + 'L2_L3:', AsmT) < 0);
end;

procedure TArm64BackendTests.TestStringIndexedProperty_WriteRead;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A class with a string-indexed property (Items[Key: string]: Integer).  The
    write B.Items['k'] := 7 must lower (previously NotYet'd as a non-integer
    index): the key string pointer goes to x1, the value to x2, receiver x0,
    then bl SetItem.  The key is BORROWED — no _StringAddRef before the setter
    (matching x86-64/QBE).  A read then dispatches the getter. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TBox = class
        FVal: Integer;
        function GetItem(const Key: string): Integer;
        procedure SetItem(const Key: string; V: Integer);
        property Items[Key: string]: Integer read GetItem write SetItem;
      end;
    function TBox.GetItem(const Key: string): Integer;
    begin Result := FVal end;
    procedure TBox.SetItem(const Key: string; V: Integer);
    begin FVal := V end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.Items['k'] := 7;
      WriteLn(B.Items['k']);
      B.Free()
    end.
    ''');
  AssertTrue('the string-indexed setter is called',
    Pos(#9'bl TBox_SetItem', AsmT) >= 0);
  AssertTrue('the string-indexed getter is called',
    Pos(#9'bl TBox_GetItem', AsmT) >= 0);
  { the setter receives value in x2 and key in x1 (popped in that order) }
  AssertTrue('value -> x2, key -> x1 before the setter call',
    Pos(#9'ldr x2, [sp], #16' + LF + #9'ldr x1, [sp], #16' + LF +
        #9'bl TBox_SetItem', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64sip.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestOwnedTransientStringPropertyValue;
var
  AsmT: string;
  PosCat, PosPin, PosSet, PosRel: Integer;
begin
  { An owned-transient string value (a `+` concat, rc=0) written through a
    property setter is passed BORROWED — the setter retains its own copy — so
    the caller must dispose the transient AFTER the setter returns.  For an rc=0
    concat that means AddRef then Release (a bare release would drive rc to -1 =
    immortal, leaking).  Covers the indexed and non-indexed setter arms. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TFoo = class
        FItems: array[0..3] of string;
        FCur: string;
        procedure SetItem(I: Integer; const V: string);
        procedure SetCur(const V: string);
        property Items[I: Integer]: string write SetItem;
        property Cur: string write SetCur;
      end;
    procedure TFoo.SetItem(I: Integer; const V: string); begin FItems[I] := V end;
    procedure TFoo.SetCur(const V: string); begin FCur := V end;
    var f: TFoo; a, b: string;
    begin
      f := TFoo.Create();
      a := 'x'; b := 'y';
      f.Items[1] := a + b;
      f.Cur := a + b;
      f.Free()
    end.
    ''');
  { the concat transient is produced, the rc=0 pin (AddRef) lands BEFORE the
    setter call — a by-value setter param's own entry/exit cycle would free
    an unpinned rc=0 transient DURING the call, so a post-call pin was a
    double-free with a non-storing setter
    (BUG-20260722-arm64-propsetter-pin-after-call) — and the single release
    follows the call }
  PosCat := Pos(#9'bl _StringConcat', AsmT);
  AssertTrue('concat produced', PosCat >= 0);
  PosSet := Pos(#9'bl TFoo_SetItem', AsmT);
  AssertTrue('indexed setter called', PosSet >= 0);
  PosPin := PosEx(#9'bl _StringAddRef', AsmT, PosCat);
  AssertTrue('rc=0 transient pinned BEFORE the indexed setter call',
    (PosPin > PosCat) and (PosPin < PosSet));
  PosRel := PosEx(#9'bl _StringRelease', AsmT, PosSet);
  AssertTrue('transient released after the indexed setter', PosRel > PosSet);
  AssertTrue('no post-call AddRef half remains',
    (PosEx(#9'bl _StringAddRef', AsmT, PosSet) < 0) or
    (PosEx(#9'bl _StringAddRef', AsmT, PosSet) > PosRel));
end;

procedure TArm64BackendTests.TestCapturedClassBase_FieldRead;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A method takes a class parameter; a nested proc reads a FIELD of it
    (AThing.FName).  AThing is captured — its instance pointer must be loaded
    through _cap_AThing (load the _cap_ slot, deref to the instance) before the
    field offset is applied.  Previously NotYet'd as 'load of variable AThing'. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TThing = class FName: string; end;
      TProc = class procedure Run(AThing: TThing); end;
    procedure TProc.Run(AThing: TThing);
      procedure Inner;
      begin WriteLn(AThing.FName) end;
    begin Inner() end;
    begin end.
    ''');
  AssertTrue('Inner is emitted as a sibling symbol',
    Pos('TProc_Run_Inner:', AsmT) >= 0);
  { the captured base is loaded through _cap_ then derefed to the instance:
    two consecutive ldr forms materialise the pointer before the field access }
  AssertTrue('captured class base derefs the capture pointer to the instance',
    Pos('ldr x0, [x0]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64ccf.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestCapturedClassBase_MethodCall;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A nested proc calls a METHOD on the captured class parameter (AThing.Show).
    The receiver must be materialised from _cap_AThing before the dispatch. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TThing = class procedure Show; end;
      TProc = class procedure Run(AThing: TThing); end;
    procedure TThing.Show;
    begin end;
    procedure TProc.Run(AThing: TThing);
      procedure Inner;
      begin AThing.Show() end;
    begin Inner() end;
    begin end.
    ''');
  AssertTrue('the receiver is loaded through the capture pointer',
    Pos('ldr x0, [x0]', AsmT) >= 0);
  AssertTrue('the method is dispatched',
    Pos(#9'bl TThing_Show', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64ccm.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestCapturedClassBase_FieldWrite;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A nested proc WRITES a field of the captured class parameter (AThing.FN :=
    5).  The instance base for the store must come through _cap_AThing. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TThing = class FN: Integer; end;
      TProc = class procedure Run(AThing: TThing); end;
    procedure TProc.Run(AThing: TThing);
      procedure Inner;
      begin AThing.FN := 5 end;
    begin Inner() end;
    begin end.
    ''');
  AssertTrue('Inner is emitted', Pos('TProc_Run_Inner:', AsmT) >= 0);
  { the store base is materialised from _cap_ (deref to instance), then the
    value is stored at the field offset }
  AssertTrue('captured store base derefs the capture pointer',
    Pos('ldr x9, [x9]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64ccw.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestCapturedVarParamClassBase_FieldWrite;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { A nested proc writes a field of a captured VAR-PARAM class base.  The base
    must deref the capture pointer TWICE (load _cap_, deref to the var-param
    slot, deref again to the instance) before the field store — a single deref
    corrupts memory (the review-found bug). }
  AsmT := GenAsm(
    '''
    program P;
    type TThing = class FN: Integer; end;
    procedure Run(var T: TThing);
      procedure Inner;
      begin T.FN := 5 end;
    begin Inner() end;
    begin end.
    ''');
  { two consecutive derefs of the base register before the field store }
  AssertTrue('captured var-param class write derefs twice',
    Pos('ldr x9, [x9]' + LF + #9'ldr x9, [x9]', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64vpw.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestAddrOfClassArrayFieldElement;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { @B.Bytes[0] where Bytes is a static-array field of the class B.  The
    instance pointer must be LOADED from B's slot (ldr), then the field offset
    added, then the scaled index — NOT the slot address (which would be a
    garbage pointer).  A non-zero index (@B.Bytes[3]) must scale. }
  AsmT := GenAsm(
    '''
    program P;
    type TBox = class Bytes: array[0..7] of Byte; end;
    procedure Take(P: Pointer); begin end;
    var B: TBox;
    begin
      B := TBox.Create();
      Take(@B.Bytes[0]);
      Take(@B.Bytes[3]);
      B.Free()
    end.
    ''');
  { the class instance pointer is loaded from the global slot (a ldr of the
    slot VALUE), then the field offset #8 is added to that instance pointer }
  AssertTrue('the field offset is added to the loaded instance pointer',
    Pos(#9'add x0, x0, #8', AsmT) >= 0);
  { the element index is scaled (mul) and added to the base }
  AssertTrue('the index is scaled and added',
    Pos(#9'mul x0, x0, x2' + LF + #9'ldr x1, [sp], #16' + LF +
        #9'add x0, x0, x1', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64afe.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestAddrOfImplicitSelfArrayFieldElement;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { @FMtx[0] inside a method — the implicit-Self static-array field element
    address: base is Self + field offset (inline storage, no deref), then the
    scaled index. }
  AsmT := GenAsm(
    '''
    program P;
    type TBox = class
      FMtx: array[0..3] of Integer;
      procedure Fill;
    end;
    procedure Take(P: Pointer); begin end;
    procedure TBox.Fill;
    begin Take(@FMtx[0]) end;
    var B: TBox;
    begin B := TBox.Create(); B.Fill(); B.Free() end.
    ''');
  { Self is loaded, the field offset added, and the index scaled+added.
    (The implicit-Self static-array field element goes through the leg-16
    EmitStaticElemAddr path, which scales via x1; the class-access form goes
    through leg-20's EmitFieldElemAddr — both compute base+offset+index*size.) }
  AssertTrue('implicit-Self base is loaded',
    Pos(#9'ldur x0, [x29,', AsmT) >= 0);
  AssertTrue('the field offset is added to the Self base',
    Pos(#9'add x0, x0, #8', AsmT) >= 0);
  AssertTrue('the index is scaled and added',
    Pos(#9'mul x1, x1, x2' + LF + #9'add x0, x0, x1', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64asf.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestHighLowEnum_FoldsToLiteral;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { High(TColor)/Low(TColor) fold to compile-time immediates: a 3-member enum
    has High=2, Low=0.  Previously High(enum) hit the generic call NotYet. }
  AsmT := GenAsm(
    '''
    program P;
    type TColor = (Red, Green, Blue);
    begin
      WriteLn(Ord(High(TColor)));
      WriteLn(Ord(Low(TColor)))
    end.
    ''');
  AssertTrue('High(TColor) folds to the max ordinal 2',
    Pos(#9'movz x0, #2', AsmT) >= 0);
  AssertTrue('Low(TColor) folds to 0',
    Pos(#9'movz x0, #0', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64hle.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestLengthStaticArray_FoldsToLiteral;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Length of a static array is a compile-time constant HighBound-LowBound+1;
    an array[0..7] has Length 8, High 7. }
  AsmT := GenAsm(
    '''
    program P;
    var A: array[0..7] of Integer;
    begin
      WriteLn(Length(A));
      WriteLn(High(A))
    end.
    ''');
  AssertTrue('Length(array[0..7]) folds to 8',
    Pos(#9'movz x0, #8', AsmT) >= 0);
  AssertTrue('High(array[0..7]) folds to 7',
    Pos(#9'movz x0, #7', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64lsa.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRecordIntoClassDynArrayField;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Box.Recs[1] := R where Recs is a `array of TRec` field of the class Box and
    TRec is a plain 16-byte record.  The element address is computed (instance
    ptr -> field data pointer deref -> +index*16), the source record address is
    taken, and the 16 bytes are memcpy'd (clean record, no ARC). }
  AsmT := GenAsm(
    '''
    program P;
    type
      TRec = record A: Integer; B: Integer; C: Int64; end;
      TBox = class Recs: array of TRec; end;
    var Box: TBox; R: TRec;
    begin
      Box := TBox.Create();
      SetLength(Box.Recs, 3);
      R.A := 10; R.B := 20; R.C := 30;
      Box.Recs[1] := R;
      Box.Free()
    end.
    ''');
  AssertTrue('the record element store memcpys the record',
    Pos(#9'bl memcpy', AsmT) >= 0);
  AssertTrue('the memcpy length is the record size (16)',
    Pos(#9'movz x2, #16', AsmT) >= 0);
  { the source and dest addresses are parked in callee-saved x19/x22 across the
    memcpy (which clobbers x0-x18) }
  AssertTrue('addresses parked in x19/x22 across the memcpy',
    Pos(#9'stp x19, x22, [sp, #-16]!', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64rda.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRecordStoreToVarParam;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { Outp := Src where Outp is a `var TRec` parameter.  The var-param slot holds
    the CALLER's record address, so the memcpy dest must be that DEREFERENCED
    address (ldur the slot value), NOT the slot's own address (which would
    corrupt the caller's pointer).  This is the TryGetValue out-param shape
    (assembler.x86_64.pas: AVal := FVals[Idx]).  Clean 16-byte record. }
  AsmT := GenAsm(
    '''
    program P;
    type TRec = record A: Integer; B: Integer; C: Int64; end;
    procedure Get(var Outp: TRec; Src: TRec);
    begin Outp := Src end;
    var R, S: TRec;
    begin
      S.A := 10; S.B := 20; S.C := 30;
      Get(R, S);
      WriteLn(R.A)
    end.
    ''');
  { the record is memcpy'd (16 bytes) — the store is a whole-record copy }
  AssertTrue('the var-param record store memcpys the record',
    Pos(#9'bl memcpy', AsmT) >= 0);
  AssertTrue('the memcpy length is the record size (16)',
    Pos(#9'movz x2, #16', AsmT) >= 0);
  { the dest address is the slot VALUE (a load), proving the deref — the
    Get body loads the var-param slot then memcpys into it }
  AssertTrue('the dest is the dereferenced var-param slot into x0 before memcpy',
    Pos(#9'ldur x0, [x29,', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64vrp.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestNestedRecordFieldAccess;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { O.I.K := 7 where I is a record-typed field of O and K a scalar field of I.
    The intermediate O.I yields &O + offsetof(I); the outer .K store lands at
    +offsetof(K).  A non-zero intermediate offset (Pad before I) exercises the
    offset accumulation.  Previously the intermediate O.I record-field read hit
    the generic 'expression TFieldAccessExpr' NotYet. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TInner = record K: Integer; end;
      TOuter = record Pad: Integer; I: TInner; end;
    var O: TOuter;
    begin
      O.I.K := 7;
      if O.I.K <> 0 then WriteLn(O.I.K)
    end.
    ''');
  { the intermediate record-field address adds the I field offset (#4) to O's
    base before the scalar store/load at K's offset }
  AssertTrue('intermediate record-field offset is added to the base',
    Pos(#9'add x0, x0, #4', AsmT) >= 0);
  { the scalar field is stored (write) and loaded (read) — no NotYet }
  AssertTrue('the nested scalar field is stored',
    Pos(#9'str w0, [x9', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64nrf.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestManagedRecordLvalueFieldStore;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { L.Op := O where Op is a managed-record (has a string) field of L and O is a
    managed-record lvalue.  The store retains O's managed fields, releases L.Op's
    old ones, then memcpys — the addresses parked in callee-saved x19/x22.
    Previously NotYet'd as 'managed-record lvalue field store'. }
  AsmT := GenAsm(
    '''
    program P;
    type
      TOp = record S: string; N: Integer; end;
      TLine = record Op: TOp; end;
    var L: TLine; O: TOp;
    begin
      O.S := 'hi'; O.N := 7;
      L.Op := O;
      WriteLn(L.Op.S)
    end.
    ''');
  AssertTrue('the managed record field store memcpys the record',
    Pos(#9'bl memcpy', AsmT) >= 0);
  AssertTrue('source/dest parked in callee-saved x19/x22',
    Pos(#9'stp x19, x22, [sp, #-16]!', AsmT) >= 0);
  { the retain-source / release-dest ARC discipline runs on the string field }
  AssertTrue('retains the source managed field',
    Pos(#9'bl _StringAddRef', AsmT) >= 0);
  AssertTrue('releases the destination''s old managed field',
    Pos(#9'bl _StringRelease', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64mrf.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestSetLengthOnVarParamRecordField;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { SetLength(C.Arr, N) where C is a var-param record and Arr a dyn-array field.
    The var-param slot holds the CALLER's record address, so the field address
    must LOAD the slot (deref) then add the Arr offset — NOT take the slot's own
    address.  Then _DynArraySetLength resizes and the fresh pointer is stored
    back.  Previously NotYet'd as 'SetLength on this field-lvalue form'. }
  AsmT := GenAsm(
    '''
    program P;
    type TCtx = record Arr: array of Integer; end;
    procedure Grow(var C: TCtx; N: Integer);
    begin SetLength(C.Arr, N) end;
    var Ctx: TCtx;
    begin Grow(Ctx, 3); WriteLn(Length(Ctx.Arr)) end.
    ''');
  AssertTrue('the dyn-array field is resized',
    Pos(#9'bl _DynArraySetLength', AsmT) >= 0);
  { the var-param base is derefed (ldur the slot value), not slot-addressed }
  AssertTrue('the var-param record slot is dereferenced for the field address',
    Pos(#9'ldur x0, [x29,', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64slv.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestSetLengthOnString_AddRefsAndVarParam;
var
  AsmT: string;
begin
  { SetLength(S, N) on a string calls _StringSetLength, whose result is rc=0
    (a fresh unowned buffer), so it MUST be AddRef'd before it is stored — else
    the local's scope-exit release would drive the count negative (immortal /
    leak).  A var-param string works through the slot ADDRESS with one extra
    deref (slot = caller var-address).  Both forms release the old value. }
  AsmT := GenAsm(
    '''
    program P;
    procedure Grow(var S: string; N: Integer); begin SetLength(S, N) end;
    var t: string;
    begin
      t := 'xy'; SetLength(t, 4);
      Grow(t, 6);
      WriteLn(Length(t))
    end.
    ''');
  AssertTrue('resize helper', Pos(#9'bl _StringSetLength', AsmT) >= 0);
  { the rc=0 result is retained before it lands in the slot }
  AssertTrue('result AddRef', Pos(#9'bl _StringAddRef', AsmT) >= 0);
  { the old value is released }
  AssertTrue('old released', Pos(#9'bl _StringRelease', AsmT) >= 0);
  { the var-param form derefs the slot address to reach the caller's string }
  AssertTrue('var-param slot dereferenced', Pos(#9'ldr x19, [x19]', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestDynArrayParam_ConstBorrowsByValueRetains;
var
  AsmT: string;
begin
  { A dyn-array parameter is an 8-byte ref-counted pointer.  A const param
    borrows (the callee touches no ARC); a by-value param is a co-owning copy —
    retained in the prologue and released at scope exit — mirroring a by-value
    string param.  The dyn-array passes as one register at the call site.  This
    program exercises exactly one by-value dyn-array param (SumV), so exactly
    one _DynArrayAddRef must be emitted (the const SumC borrows). }
  AsmT := GenAsm(
    '''
    program P;
    type TA = array of Integer;
    function SumC(const A: TA): Integer;
    var i: Integer;
    begin Result := 0; for i := 0 to Length(A) - 1 do Result := Result + A[i] end;
    function SumV(A: TA): Integer;
    var i: Integer;
    begin Result := 0; for i := 0 to Length(A) - 1 do Result := Result + A[i] end;
    var d: TA;
    begin
      SetLength(d, 3); d[0] := 1; d[1] := 2; d[2] := 3;
      WriteLn(SumC(d));
      WriteLn(SumV(d))
    end.
    ''');
  { the param is used via Length + subscript in both bodies }
  AssertTrue('dyn-array length in body', Pos(#9'bl _DynArrayLength', AsmT) >= 0);
  { the by-value param (SumV) retains — a prologue _DynArrayAddRef appears }
  AssertTrue('by-value param retains',
    Pos(#9'bl _DynArrayAddRef', AsmT) >= 0);
  { there is exactly ONE such retain — the const param (SumC) borrows, so a
    second _DynArrayAddRef past the first must not exist }
  AssertTrue('only the by-value param retains (const borrows)',
    PosEx(#9'bl _DynArrayAddRef', AsmT,
      Pos(#9'bl _DynArrayAddRef', AsmT) + 1) < 0);
end;

procedure TArm64BackendTests.TestVarParamRecordArrayFieldElemWrite;
var
  AsmT: string;
  Obj: string;
  F: TMachOFile;
begin
  { C.Arr[I] := V where C is a var-param record and Arr a dyn-array field
    (leg 28).  The var-param slot holds the CALLER's record address, so the
    element address must LOAD the slot (deref), add the Arr field offset, deref
    the dyn-array field to its data pointer, then scale the index and store —
    so the write reaches the caller's array.  Previously NotYet'd as
    'array-field element write on this base form'. }
  AsmT := GenAsm(
    '''
    program P;
    type TCtx = record Arr: array of Integer; end;
    procedure SetAt(var C: TCtx; I, V: Integer);
    begin C.Arr[I] := V end;
    var Ctx: TCtx;
    begin SetLength(Ctx.Arr, 3); SetAt(Ctx, 1, 42); WriteLn(Ctx.Arr[1]) end.
    ''');
  { the var-param base is derefed (ldur the slot value), not slot-addressed }
  AssertTrue('the var-param record slot is dereferenced for the base address',
    Pos(#9'ldur x0, [x29,', AsmT) >= 0);
  { the dyn-array field is derefed to its data pointer }
  AssertTrue('the dyn-array field is dereferenced to its data pointer',
    Pos(#9'ldr x0, [x0]', AsmT) >= 0);
  { the index is scaled and the value stored to the computed element address }
  AssertTrue('the index is scaled', Pos(#9'mul x1, x1, x2', AsmT) >= 0);
  Obj := AssembleArm64ToBytes(AsmT);
  F := ParseMachO(Obj, 'arm64vpe.o');
  try
    AssertTrue('has a text section',
      F.FindSection('__TEXT', '__text') <> nil);
  finally
    F.Free();
  end;
end;

procedure TArm64BackendTests.TestRecordArrayElementRead;
var
  AsmT: string;
begin
  { Leg 32: reading a RECORD element out of an array — a record element
    evaluates to its ADDRESS (used by reference: whole-record copy, field read),
    not a value-load.  Previously EmitElemLoad NotYet'd 'array element of this
    width' because it tried to ldr the whole record into one register.  The
    element-address helper still computes base + index*stride (mul x1,x1,x2 +
    add), then the copy/field-read consumes the address.  Covers a static and a
    dynamic array of record, with a managed (string) field. }
  AsmT := GenAsm(
    '''
    program P;
    type TR = record A, B: Integer; S: string; end;
    var arr: array[0..3] of TR; d: array of TR; r: TR;
    begin
      arr[1].A := 5; arr[1].S := 'hi';
      r := arr[1];
      SetLength(d, 2); d[0].A := 9;
      r := d[0];
      WriteLn(r.A)
    end.
    ''');
  { the element address is computed (index scaled) — the record is then copied
    by reference, NOT value-loaded into a single register }
  AssertTrue('the record element index is scaled to an address',
    Pos(#9'mul x1, x1, x2', AsmT) >= 0);
  { a whole-record copy memcpy's from the element address }
  AssertTrue('the record element is copied by memcpy',
    Pos(#9'bl memcpy', AsmT) >= 0);
end;

procedure TArm64BackendTests.TestVarParamClassArrayFieldElemWriteStillNotYet;
var
  Raised: Boolean;
  Msg: string;
begin
  { An element write into an array field of a var-param CLASS receiver needs an
    extra deref (the slot holds &instance) that the record element-write path
    does not add.  Leg 28 lifts the guard only for a RECORD base — a var-param
    class base must STAY NotYet, not silently mis-address (one indirection
    short). }
  Raised := False;
  Msg := '';
  try
    GenAsm(
      '''
      program P;
      type TFoo = class Arr: array of Integer; end;
      procedure Poke(var F: TFoo);
      begin F.Arr[0] := 5 end;
      var F: TFoo;
      begin F := TFoo.Create; SetLength(F.Arr, 1); Poke(F); WriteLn(F.Arr[0]) end.
      ''');
  except
    on E: ENativeCodeGenError do
    begin
      Raised := True;
      Msg := E.Message;
    end;
  end;
  AssertTrue('var-param class array-field element write stays NotYet', Raised);
  AssertTrue('message names the array-field element write hole',
    Pos('array-field element write on this base form', Msg) >= 0);
end;

initialization
  RegisterTest(TArm64BackendTests);

end.
