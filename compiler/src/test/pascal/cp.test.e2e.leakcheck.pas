{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.leakcheck;

{ E2E tests for the --debug leak tracker.
  Verifies that _LeakTrackerEnable is activated in debug builds,
  that leaked objects are reported on exit, and that cleanly-released
  objects produce no report. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ELeakCheckTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { A fresh constructor result as the receiver of a method returning an
      aggregate -- TT.Create().GetB() (a record), .GetI() (an interface), .GetFn()
      (a closure) -- read, assigned or discarded, frees the instance after the
      call.  It has no owner but the call, so it must be pinned and released;
      arm64 leaked it for a record result, x86-64 for an interface result. }
    procedure TestDebug_CtorResultReceiver_AggregateResults_NoLeak;
    { a managed static array from a getter passed as an open array releases its
      elements }
    procedure TestDebug_StaticArrayGetterOpenArrayArg_NoLeak;
    { captured managed variables assigned in the declaring routine and in a
      closure keep exactly one owner: nothing leaks and nothing is freed twice }
    procedure TestDebug_CapturedManagedVars_NoLeak;
    { every field kind read off an owned transient instance releases the
      instance exactly once, however many such reads one statement holds }
    procedure TestDebug_OwnedTransientBase_EveryFieldKind_NoLeak;
    { for-in over collections reached through calls releases every result and
      the reference it holds on a borrowed array }
    procedure TestDebug_ForInThroughCall_NoLeak;
    { record call results (string and dyn-array fields) as address bases in every
      call form release what they own: a getter's result (O.R.A[1]) leaked a
      string on arm64 }
    procedure TestDebug_RecordCallAddressBases_NoLeak;
    procedure TestDebug_DiscardedResultsEveryKind_NoLeak;
    procedure TestDebug_StaticAggregateMembers_NoLeak;
    procedure TestDebug_InterfaceGettersStatics_NoLeak;
    procedure TestDebug_AggregateScalarContexts_NoLeak;
    { the P6 aggregate forms above under the --debug leak tracker }
    procedure TestDebug_ExprCalleeAggregates_NoLeak;
    { owned transients only tested or passed on: an implicit-Self procedural
      FIELD call's result, and an object compared, is-tested or Assigned }
    procedure TestDebug_ImplicitSelfProcFieldResult_NoLeak;
    { owned transients written through property SETTERS -- a class, an
      interface and a class-narrowed-to-interface value, plain / indexed /
      default / bare, and an owned-transient RECEIVER (P3-1,
      BUG-20261011-intf-prop-setter): each +1 is released after the call }
    procedure TestDebug_OwnedTransientSetterValues_NoLeak;
    { a string-returning function called as a statement releases the result
      it discards (x86-64 released only a class result) }
    procedure TestDebug_DiscardedStringResult_NoLeak;
    { P3 owned-transient corners, each leaked or was NotYet:
      ClassName / ClassType / Supports / is-free `as` and hard casts of a
      call result; a constructor result as a receiver; Free of a getter read
      and through an owned base; a var argument through an owned base;
      OrdAt of a string transient; an owned value into [Weak] targets }
    procedure TestDebug_OwnedTransientCastsAndTests_NoLeak;
    procedure TestDebug_CtorResultReceiver_NoLeak;
    procedure TestDebug_FreeAndVarArgThroughOwnedBase_NoLeak;
    procedure TestDebug_OrdAtStringTransient_NoLeak;
    procedure TestDebug_OwnedIntoWeakTargets_NoLeak;
    { @MakeObj().N: the owned base is released at the statement end
      (x86-64 leaked it; arm64 was NotYet) }
    procedure TestDebug_AddrOfOwnedTransientField_NoLeak;
    { method pointers and closures copied between locals, globals, fields,
      record fields, elements, P^, captures and var params -- both halves,
      closures retaining their env (x86-64 copied the source ADDRESS or one
      half and crashed; arm64 refused most sources and every element store) }
    procedure TestDebug_MethodPtrAndClosureCopies_NoLeak;
    { MakeObj().S := V / MakeObj().P := @Hello release the owned receiver
      (x86-64 leaked it); A := G with A a static-array field of Self (x86-64
      crashed the compiler); R.F := [a, b] into a record field of Self }
    procedure TestDebug_FieldStoresThroughCallsAndSelf_NoLeak;
    { method pointers, closures (literals included), dyn arrays and floats
      stored into ARRAY-FIELD elements, through Self and through an owned
      call receiver (both ISAs refused or miscompiled most of them) }
    procedure TestDebug_ArrayFieldElementStores_NoLeak;
    { for-in over every collection form -- fields, Self fields, var params,
      captures, P^, elements, dyn-array / string / class CALL results, jumbo
      sets, float and HFA-record enumerator Currents, an empty string --
      with String, interface, closure and jumbo-set elements (arm64 refused
      most; x86-64 crashed on a global interface loop variable and on an
      empty string, read a float Current as 0.0, and leaked or re-evaluated
      call collections) }
    procedure TestDebug_ForInForms_NoLeak;
    { an interface-returning call as a scalar operand (GetI() <> nil,
      Assigned(O.GetI()), O.GetI() = L) and an interface read through an
      owned transient receiver (MkObj().GetI(), MkObj().FIntf, MkObj().P[I]):
      x86-64 crashed on the operand (no sret buffer) and leaked the
      receiver; arm64 leaked the operand's result and rejected an itab
      receiver (L.Me() <> nil); x86-64 rejected Result := G.FIntf }
    procedure TestDebug_IntfCallOperands_NoLeak;
    { an owned class call result narrowed to an interface -- into a local, a
      field, an implicit-Self field, a function Result and an interface
      argument -- is consumed, not retained a second time (x86-64 leaked one
      object per store, and passed the argument without its itab) }
    procedure TestDebug_OwnedClassToInterface_NoLeak;
    procedure TestDebug_OwnedClassTested_NoLeak;
    procedure TestDebug_NoLeak_NoReport;
    procedure TestDebug_ExceptionHandlerVar_NoLeakNoOverRelease;
    { BUG-20260720-exception-object-leak: a handler with NO bound variable (bare
      except, on-Type-no-var, else branch) left the raised exception orphaned
      (created rc=0, only borrowed, never released) — leaking Exception (rc=0). }
    { BUG-20260720-managed-record-self-assign: R := R must be leak-free (the
      native release-dest step used to zero + orphan the +1-retained field). }
    procedure TestDebug_ManagedRecordSelfAssign_NoLeak;
    procedure TestDebug_ExceptionNoVarHandler_NoLeak;
    procedure TestDebug_ExceptionNoVarHandler_NonLocalExit_NoLeak;
    procedure TestRun_BareReraise_AfterNestedHandledException;
    procedure TestDebug_ConstructorWithArgs_NoDoubleAddRef;
    procedure TestDebug_LeakedObject_ReportedOnExit;
    procedure TestDebug_MultipleLeaks_AllReported;
    procedure TestDebug_CycleRetained_Reported;
    procedure TestRelease_NoReport_WhenDebugOff;
    procedure TestDebug_LeakReport_IncludesUnitAndLine_Native;
    procedure TestDebug_StringLeak_Reported;
    procedure TestDebug_StringClean_NoReport;

    { obj.Field := MakeClass() consumes the call's +1 — no leak per store. }
    procedure TestDebug_ClassFieldFromCall_NoLeak;

    { local := MakeClass() consumes the call's +1 — no leak per assignment.
      Pins the native class-assignment AddRef elision. }
    procedure TestDebug_FuncReturnAssign_NoLeak;
    { MakeClass() called in statement position discards its +1 result — it must
      be released or one object leaks per call. }
    procedure TestDebug_DiscardedClassReturn_NoLeak;
    { X := Call().ClassField must keep the field value valid past the base
      release (a use-after-free before the deferred-base-release fix) and not
      leak.  The correct output (42) is asserted, not just the leak report. }
    procedure TestDebug_CallResultClassFieldRead_NoUseAfterFree;
    { BUG-049: a class-field read off an owned transient in an UNBRACKETED
      statement context (a call argument, an if condition, and — per iteration
      — a loop condition) must still release the transient.  Every statement is
      flush-bracketed, and loop conditions flush per iteration, so none leak. }
    procedure TestDebug_TransientFieldInCallArg_NoLeak;
    { owned string transients as call arguments: a call nested in an argument
      parks its own transients above the enclosing call's, and a call may
      take more than eight of them }
    procedure TestDebug_NestedOwnedStringTransientArgs_NoLeak;
    { owned class transients (call results) as call arguments are released
      after the call }
    procedure TestDebug_OwnedClassTransientArgs_NoLeak;
    { a record or interface result discarded through a procedural value (a
      method pointer, closure, plain pointer or procedural field) lands in a
      scratch buffer and its managed contents are released }
    procedure TestDebug_DiscardedAggregateThroughProcValue_NoLeak;
    { an interface returned through a plain procedural variable or a closure,
      assigned, passed on, used as a receiver and discarded: every position
      takes the owned (+1) reference and lets go of it }
    procedure TestDebug_InterfaceThroughProcValue_NoLeak;
    { a discarded string, object, interface or closure result of a method
      called on a NAMED receiver (C.Make();) is released -- the statement's
      return type was recorded only for a record, so every other kind leaked
      and a closure had no x8 buffer }
    procedure TestDebug_DiscardedResultOnNamedReceiver_NoLeak;
    { closures RETURNED by calls -- an implicit-Self method, a procedural
      variable, a plain function -- called, kept and discarded }
    procedure TestDebug_ClosureReturningCalls_NoLeak;
    procedure TestDebug_TransientFieldInIfCond_NoLeak;
    procedure TestDebug_TransientFieldInWhileCond_NoLeak;
    { A deep chain MakeIt().A.B.N reads a scalar off a base that is itself two
      field-reads off an owned transient.  Each intermediate owned transient's
      release must be deferred to statement end so none leak, while the value
      still survives (no UAF) (BUG-003). }
    procedure TestDebug_DeepChainFieldRead_NoLeak;
    { Multiple same-named typed handlers share one slot — no over-release. }
    procedure TestDebug_MultiHandlerVar_NoOverRelease;
    { for-in over a TList: GetEnumerator's +1 result must be transferred
      into the loop slot, not re-retained — one enumerator leaked per
      loop otherwise. }
    procedure TestDebug_ForInEnumerator_NoLeak;
    procedure TestDebug_ForInEnumerator_NoLeak_Native;
    { Objects allocated inside generic method bodies must be attributed
      to the unit that DECLARES the template (the line number already
      refers to the template source), not the instantiating unit. }
    procedure TestDebug_GenericAllocSite_ReportsDefiningUnit_Native;
    { The same for generic RECORD methods and generic FUNCTIONS
      (BUG-014) }
    procedure TestDebug_GenericRecordAndFuncAllocSite_ReportsDefiningUnit;
    { An interface-returning call passed directly as an argument — Show(Make())
      — hands the callee an owned (+1) fat pointer it borrows; the caller must
      release it after the call or one instance leaks. }
    procedure TestDebug_IntfCallResultArg_NoLeak_Native;
    { A call/getter result used as a field-access receiver must be released
      after the field load.  L[I].HitPoints — the TList<T>.Get getter returns
      +1, the field is read, then the transient base must be released. }
    procedure TestDebug_ReceiverFieldAccess_NoLeak;
    { A static array of interfaces (array[0..N] of IFoo): the elements are
      ARC-managed but the scope-exit cleanup previously skipped tyStaticArray
      locals entirely, so every stored element leaked on BOTH backends.  The
      fix releases each element at scope exit. }
    procedure TestDebug_StaticArrayOfInterface_NoLeak;
    { BUG-016 stage 2: static-array-of-CLASS/STRING/RECORD locals are
      released at scope exit (previously only interface elements were). }
    procedure TestDebug_StaticArrayOfClass_NoLeak;
    procedure TestDebug_StaticArrayOfString_NoLeak;
    procedure TestDebug_StaticArrayOfRecord_NoLeak;
    { Same, when the block is left via an exception caught in-function:
      the handler completes, the epilogue walk must still release. }
    procedure TestDebug_StaticArrayOfClass_ExceptionExit_NoLeak;
    { THE double-free guard for BUG-016: a static array whose elements are
      constructed and then MANUALLY .Free'd (the elfwriter RelaBuf shape),
      freed a second time (simulating the scope-exit release landing on top
      of a manual free), then 16 further allocations churned through the
      free list writing/reading a sentinel.  Without the allocation churn a
      double-free passes vacuously.  Requires A[I].Free() to NIL the element
      slot; must pass at EVERY stage of the BUG-016/017 work. }
    procedure TestDebug_StaticArrayManualFree_NoDoubleFree;
    { PROGRAM-LEVEL static arrays of managed elements.  Every test above
      wraps its array in a `procedure Run()`, so they all exercise the
      procedure-frame ARC walk (which drives off Body.Decls).  A
      program-level var is registered as a GLOBAL instead, and the native
      x86-64 main-body cleanup (EmitGlobalReleases) walks FDataGlobals with
      a kind chain that covered string/class/dyn-array/interface/record but
      NOT tyStaticArray — so a program-level managed array leaked every
      element on native while QBE (one shared cleanup routine) was correct.
      These pin the global-addressing arm. }
    procedure TestDebug_ProgramLevelStaticArrayOfClass_NoLeak;
    procedure TestDebug_ProgramLevelStaticArrayOfString_NoLeak;
    procedure TestDebug_ProgramLevelStaticArrayOfInterface_NoLeak;
    procedure TestDebug_ProgramLevelStaticArrayOfRecord_NoLeak;
    { The program-level twin of TestDebug_StaticArrayManualFree_NoDoubleFree,
      including the 16-allocation sentinel churn: without the churn a
      double-free at main_exit would pass vacuously. }
    procedure TestDebug_ProgramLevelStaticArrayManualFree_NoDoubleFree;
    { Program-level array live across a caught exception.  NOTE: a caught
      exception currently leaks its `Exception (rc=0)` object on BOTH
      backends (filed separately), so this test matches on the ELEMENT class
      name rather than the bare word 'leak'. }
    procedure TestDebug_ProgramLevelStaticArray_ExceptionExit_NoLeak;
    { BUG-017: static-array-of-managed FIELDS — record local, by-value
      record param (copy must retain), and class field (cleanup fn). }
    procedure TestDebug_RecordStaticArrayField_NoLeak;
    procedure TestDebug_RecordStaticArrayField_ByValueParam_NoLeak;
    procedure TestDebug_ClassStaticArrayField_NoLeak;
    { A string-returning call result passed DIRECTLY to a BY-VALUE string
      parameter — SinkVal(MakeStr(I)) — hands the callee an owned (+1) temp it
      only co-owns (entry retain / exit release nets to zero); the CALLER must
      release the temp after the call or one string leaks per call.  Covers
      plain procedure calls and method calls (the TList<string>.Add shape that
      leaked ~10 strings per directory-watcher poll in luhmann).  QBE already
      balances this via EmitOwnedArgReleases; pins the native fix. }
    procedure TestDebug_ValueStrCallResultArg_NoLeak_Native;
    { An owned (+1) string temp passed to a BUILT-IN — FileAge(PathOf()),
      Trim(Get()), Length(Make()), StrToInt(Make()), nested
      LowerCase(Trim(Make())) — the built-in emission paths call straight into
      the RTL and historically never released the argument temp (both
      backends).  One string leaked per call; the luhmann directory watcher
      hit this once per note per poll via FileAge(AbsPathOf(Id)). }
    procedure TestDebug_BuiltinOwnedStrArg_NoLeak_Native;
    { rc=0 string transients (built-in results, _StringConcat results — all
      StrAlloc buffers with RefCount = 0) leak INVISIBLY: a bare
      _StringRelease drives the count to -1 = IMMORTAL, and the leak tracker
      never saw the block (it registers on the 0 -> 1 AddRef).  Disposal must
      be AddRef + Release.  Because the tracker is blind to a regression
      here, this test pins the fix through the ALLOCATOR instead: 50k
      iterations of the shapes that used to leak one 48-byte buffer each
      (inline concat operand, user-call concat operand, nested built-in arg,
      concat-as-built-in-arg) would grow the arena count by ~150; the fixed
      compiler keeps it flat. }
    procedure TestDebug_StrTransientDispose_NoArenaGrowth_Native;
    { A string-returning call/getter used DIRECTLY as a Write/WriteLn argument
      (WriteLn(GetBar)) returns a fresh +1 string that _SysWriteStr only borrows.
      EmitWrite previously never released it, leaking one string per call.  The
      fix releases the owned string transient after the write. }
    procedure TestDebug_WriteLnCallArg_NoLeak;
    { Anonymous-method capture (Phase 2): the heap environment record must be
      allocated once and released exactly once — the enclosing frame drops its
      reference at exit and the escaped closure drops the last one when the
      closure slot is released. }
    procedure TestDebug_ClosureEnv_ReleasedExactlyOnce;
    procedure TestDebug_ClosureArgBalance_NoLeak;
    procedure TestDebug_LinqLite_ProducedLists_NoLeak;
    { Phase 3: a closure capturing Self stored in the receiver's OWN field
      forms the documented strong cycle Self -> field -> env -> Self.  It
      MUST leak (asserted) until [Weak] capture (Phase 5) provides the
      break; this pins the behaviour as intentional. }
    procedure TestDebug_ClosureSelfCycle_LeaksByDesign;
    { Phase 3: a coerced method pointer strong-retains its receiver; when
      the closure slot dies, the receiver must be released — no leak. }
    procedure TestDebug_MethodPtrCoercion_NoLeak;
    { Phase 4: every loop iteration allocates a fresh BLOCK env; each must
      be released exactly once (overwritten closure slot releases the
      previous env; the tracking slot releases the last). }
    procedure TestDebug_BlockEnvPerIteration_NoLeak;
    { Phase 5: the same self-storing closure as the leaks-by-design test,
      but with [Weak Self] — the cycle is broken, zero leaks. }
    procedure TestDebug_ClosureWeakSelfCycle_NoLeak;
    { A captured string is an ARC slot inside the env record: the env cleanup
      proc must release it, and closure-body reassignment must go through the
      string retain/release store path. }
    procedure TestDebug_ClosureCapturedString_NoLeak;

    { ---- Per-unit ARC teardown (<Unit>_fini) ----
      Managed UNIT-scope globals must be released at program exit.  These
      tests shell out to the REAL compiler binary and build with the DEFAULT
      incremental separate-compilation path (`--output`, no --no-incremental):
      that is the path where unit globals never reach the program TU's data
      globals, so main used to emit no release walk for them (and QBE emitted
      none in any mode).  The in-process harnesses (CompileAndRunWithRTLDebugOn)
      take the whole-program path, where native looked correct — verifying
      there would pass vacuously.  Allocation happens in a procedure called
      from main, never in an initialization section (_LeakTrackerEnable runs
      after unit inits, so init-time allocations are invisible to the
      tracker). }
    procedure TestDebug_UnitGlobalStaticArrayOfString_NoLeak;
    procedure TestDebug_UnitGlobalScalarString_NoLeak;
    procedure TestDebug_UnitGlobalClass_NoLeak;
    { Implementation-section private global: invisible to main's TU even in
      whole-program mode — only the unit's own <Unit>_fini can reach it.
      This is the case that justifies the per-unit fini design. }
    procedure TestDebug_UnitImplementationGlobal_NoLeak;
    { Two units, each holding a global object whose destructor prints:
      finalisation must run in REVERSE init order (last initialised, first
      finalised). }
    procedure TestDebug_TwoUnits_FiniReverseOrder;
    { A unit's user `finalization` block must run at exit — before the unit's
      globals are released, so it can still read them. }
    procedure TestDebug_FinalizationSection_RunsBeforeRelease;
    { BUG-20260720-sret-assign-old-fields-leak: repeatedly assigning a record-
      returning call into the SAME destination leaked the destination's OLD
      managed fields (one string per overwrite) on native, because the sret
      write overwrote them without releasing.  Covers the static-function,
      free-function, and method-call arms, plus the aliasing forms (dest = arg /
      dest = receiver) which must stay correct AND leak-free. }
    procedure TestDebug_SretReassign_NoLeak;
  protected
    { Compile AUnit1Src/AUnit2Src (either may be '') + AProgSrc with the real
      compiler binary on the DEFAULT incremental path (--debug --output),
      run the binary, and return its exit code (or the compiler's exit code,
      negated, on compile failure).  AOutput carries the binary's stdout
      (or the compiler diagnostics on compile failure).  ABackend is the
      --backend argument.  A fresh scratch subdirectory is
      used per call so the unit cache is always cold (avoids the separate
      warm-rebuild .bif round-trip bug for unit-interface static arrays). }
    function RunUnitFiniDebug(const ABackend, AUnit1Src, AUnit2Src,
                              AProgSrc: string;
                              out AOutput: string): Integer;
  end;

implementation

uses
  classes, sysutils, process;

procedure TE2ELeakCheckTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-leakcheck');
end;

const
  LE = #10;

  { A clean program: object is created and properly released by ARC at scope exit. }
  SrcNoLeak = '''
    program P;
    uses runtime.arc;
    type
      TBox = class
        Value: Integer;
      end;
    var
      B: TBox;
    begin
      B := TBox.Create();
      B.Value := 99;
      WriteLn(B.Value)
    end.
    ''';

  { Exception handler variable: `on E: T do` binds the caught exception to E.
    E is a class local that scope-exit ARC releases, so the handler must retain
    the exception on bind.  Without that AddRef the exception (created at rc=0
    by `raise EFoo.Create`) is over-released to a negative refcount — a
    use-after-free.  With the fix it is freed exactly once: no leak, no crash. }
  SrcExceptionHandlerVar = '''
    program P;
    uses runtime.arc;
    type
      Exception = class
        FMessage: string;
      end;
      EFoo = class(Exception) end;
    procedure DoIt;
    begin
      try
        raise EFoo.Create()
      except
        on E: EFoo do
          WriteLn('caught')
      end
    end;
    begin
      DoIt();
      WriteLn('done')
    end.
    ''';

  { Constructor with args — must not double-AddRef; object must be clean after scope. }
  SrcConstructorWithArgs = '''
    program P;
    uses runtime.arc;
    type
      TBox = class
        Value: Integer;
        constructor Create(V: Integer);
      end;
    constructor TBox.Create(V: Integer);
    begin
      Self.Value := V
    end;
    var
      B: TBox;
    begin
      B := TBox.Create(42);
      WriteLn(B.Value)
    end.
    ''';

  { Deliberately leaked: object assigned to a raw Pointer, bypassing ARC release. }
  SrcOneLeak = '''
    program P;
    uses runtime.arc;
    type
      TBox = class
        Value: Integer;
      end;
    var
      B: TBox;
    begin
      B := TBox.Create();
      B.Value := 7;
      _ClassAddRef(Pointer(B));
      { Artificial extra addref: rc=2.  Scope-exit releases B (rc=1),
        but the unbalanced addref keeps the object alive — leak. }
      WriteLn('done')
    end.
    ''';

  { Two distinct classes leaked to verify count and class-name reporting. }
  SrcTwoLeaks = '''
    program P;
    uses runtime.arc;
    type
      TAlpha = class
        X: Integer;
      end;
      TBeta = class
        Y: Integer;
      end;
    var
      A: TAlpha;
      B: TBeta;
    begin
      A := TAlpha.Create();
      B := TBeta.Create();
      _ClassAddRef(Pointer(A));
      _ClassAddRef(Pointer(B));
      { Artificial extra addref on each: scope-exit releases both
        (rc 2->1) but the unbalanced addref keeps them alive. }
      WriteLn('done')
    end.
    ''';

  { Reference cycle: each object holds the other — both leak. }
  SrcCycleLeak = '''
    program P;
    uses runtime.arc;
    type
      TNode = class
        Other: TNode;
      end;
    var
      X, Y: TNode;
    begin
      X := TNode.Create();
      Y := TNode.Create();
      X.Other := Y;
      Y.Other := X;
      { X and Y each hold refcount >= 2 due to the cycle; when the local
        vars go out of scope the refcount drops to 1, not 0 — both leak. }
      WriteLn('done')
    end.
    ''';

  { Leak with allocation-site info: the report must include the unit name and
    line number where the leaking TBox.Create() call was made. }
  SrcLeakWithSite = '''
    program LeakSite;
    uses runtime.arc;
    type
      TBox = class
        Value: Integer;
      end;
    var
      B: TBox;
    begin
      B := TBox.Create();
      _ClassAddRef(Pointer(B));
      WriteLn('done')
    end.
    ''';

  { Leaked string: concatenation produces a heap-allocated string (non-immortal).
    Extra AddRef prevents scope-exit release from freeing it. }
  SrcStringLeak = '''
    program P;
    uses runtime.arc;
    var
      S: string;
    begin
      S := 'hel' + 'lo';
      _StringAddRef(Pointer(S));
      WriteLn('done')
    end.
    ''';

  { Clean string usage: no leak expected — scope-exit ARC releases properly. }
  SrcStringClean = '''
    program P;
    uses runtime.arc;
    var
      S: string;
    begin
      S := 'hello';
      WriteLn(S)
    end.
    ''';

{ ------------------------------------------------------------------ }

const
  SrcForInEnum = '''
    program P;
    uses generics.collections;
    var
      L: TList<Integer>;
      I, Total: Integer;
    begin
      L := TList<Integer>.Create;
      L.Add(5);
      L.Add(4);
      Total := 0;
      for I in L do
        Total := Total + I;
      WriteLn(Total);
    end.
    ''';

const
  SrcNestedStrTransArgs = '''
    program NestTrans;
    uses SysUtils;
    function A(I: Integer): string; begin Result := 'a' + IntToStr(I) end;
    function G(const S: string): string; begin Result := S + '!' end;
    procedure F(const X, Y: string); begin WriteLn(X, ' ', Y) end;
    procedure Ten(const S0, S1, S2, S3, S4, S5, S6, S7, S8, S9: string);
    begin WriteLn(S0, S1, S2, S3, S4, S5, S6, S7, S8, S9) end;
    var K: Integer;
    begin
      for K := 1 to 3 do
        F(A(K), G(A(K + 10)));
      Ten(A(0), A(1), A(2), A(3), A(4), A(5), A(6), A(7), G(A(8)), G(G(A(9))))
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_NestedOwnedStringTransientArgs_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcNestedStrTransArgs, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    'a1 a11!' + LE + 'a2 a12!' + LE + 'a3 a13!' + LE +
    'a0a1a2a3a4a5a6a7a8!a9!!' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

const
  SrcClassTransArgs = '''
    program ClsTrans;
    uses generics.collections;
    type
      TFoo = class
        N: Integer;
        function Me: TFoo;
      end;
    function TFoo.Me: TFoo; begin Result := Self end;
    function O(I: Integer): TObject; begin Result := TObject.Create() end;
    function MkF(I: Integer): TFoo; begin Result := TFoo.Create(); Result.N := I end;
    procedure One(O0: TObject); begin Write(O0 <> nil, ' ') end;
    procedure OneC(const O0: TObject); begin Write(O0 <> nil, ' ') end;
    procedure ShowF(F: TFoo); begin Write(F.N, ' ') end;
    procedure TenO(O0, O1, O2, O3, O4, O5, O6, O7, O8, O9: TObject);
    begin Write(O9 <> nil, ' ') end;
    var L: TList<TFoo>; I: Integer;
    begin
      One(O(1));
      OneC(O(2));
      TenO(O(0), O(1), O(2), O(3), O(4), O(5), O(6), O(7), O(8), O(9));
      L := TList<TFoo>.Create();
      for I := 1 to 3 do L.Add(MkF(I));
      L.Add(TFoo.Create());
      ShowF(L[1]);
      for I := 0 to L.Count - 1 do ShowF(L[I].Me());
      L.Free();
      WriteLn()
    end.
    ''';

const
  SrcDiscardedAggProc = '''
    program da;
    type
      TBig = record A, B, C: Int64; end;
      TSt = record N: Integer; S: string; end;
      IFoo = interface procedure Hi; end;
      TFoo = class(TObject, IFoo) procedure Hi; end;
      TBigM = function: TBig of object;
      TStC = reference to function(X: Integer): TSt;
      TIfP = function: IFoo;
      TIfC = reference to function: IFoo;
      THost = class
        BigF: TBigM; StF: TStC;
        function Big: TBig;
        procedure Run;
      end;
    procedure TFoo.Hi; begin end;
    function THost.Big: TBig;
    begin WriteLn('big'); Result.A := 1; Result.B := 2; Result.C := 3 end;
    function MkIf: IFoo; begin Result := TFoo.Create() end;
    procedure THost.Run;
    begin
      BigF(); StF(5)
    end;
    var H: THost; M: TBigM; SC: TStC; IP: TIfP; IC: TIfC; R: TBig; K: Integer;
    begin
      H := THost.Create(); K := 40;
      M := @H.Big;
      SC := function(X: Integer): TSt
        begin Result.N := X + K; Result.S := 'str' + IntToStr(X) end;
      IP := @MkIf;
      IC := function: IFoo begin Result := TFoo.Create() end;
      M(); R := M(); WriteLn(R.C);
      SC(1); WriteLn(SC(2).S);
      IP(); IC();
      H.BigF := M; H.StF := SC;
      H.Run(); H.BigF(); H.StF(3)
    end.
    ''';

const
  SrcIntfThroughProc = '''
    program intfproc;
    type
      IFoo = interface procedure Hi; function N: Integer; end;
      TFoo = class(TObject, IFoo) V: Integer; procedure Hi; function N: Integer; end;
      TIfP = function(X: Integer): IFoo;
      TIfC = reference to function(X: Integer): IFoo;
    procedure TFoo.Hi; begin WriteLn('hi', V) end;
    function TFoo.N: Integer; begin Result := V end;
    function MkIf(X: Integer): IFoo;
    var F: TFoo;
    begin F := TFoo.Create(); F.V := X; Result := F end;
    procedure Show(const I: IFoo); begin WriteLn('show', I.N()) end;
    var IP: TIfP; IC: TIfC; I: IFoo;
    begin
      IP := @MkIf;
      IC := function(X: Integer): IFoo
        var F: TFoo;
        begin F := TFoo.Create(); F.V := X + 100; Result := F end;
      IP(1);
      WriteLn('a');
      IC(2);
      WriteLn('b');
      I := IP(3); I.Hi();
      WriteLn('c');
      I := IC(4); I.Hi();
      WriteLn('d');
      Show(IP(5));
      Show(IC(6));
      WriteLn('e');
      WriteLn(IP(7).N());
      WriteLn(IC(8).N());
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_InterfaceThroughProcValue_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcIntfThroughProc, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('output, got: ' + Output,
    Pos('a' + LE + 'b' + LE + 'hi3' + LE + 'c' + LE + 'hi104' + LE + 'd' + LE +
        'show5' + LE + 'show106' + LE + 'e' + LE + '7' + LE + '108' + LE, Output) >= 0);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

const
  SrcNamedRecvDiscard = '''
    program namedrecv;
    uses SysUtils;
    type
      IFoo = interface procedure Hi; end;
      TFoo = class(TObject, IFoo) procedure Hi; end;
      TFn = reference to function: Integer;
      TCls = class
        function MkS(X: Integer): string;
        function MkO: TObject;
        function MkI: IFoo;
        function MkFn(X: Integer): TFn;
      end;
    procedure TFoo.Hi; begin end;
    function TCls.MkS(X: Integer): string; begin Result := 'v' + IntToStr(X) end;
    function TCls.MkO: TObject; begin Result := TObject.Create() end;
    function TCls.MkI: IFoo; begin Result := TFoo.Create() end;
    function TCls.MkFn(X: Integer): TFn;
    begin Result := function: Integer begin Result := X * 2 end end;
    var C: TCls;
    begin
      C := TCls.Create();
      C.MkS(1);
      C.MkO();
      C.MkI();
      C.MkFn(1);
      WriteLn('done');
    end.
    ''';
  SrcClosureReturning = '''
    program closret;
    type
      TFn = reference to function: Integer;
      TMk = function(X: Integer): TFn;
      TCls = class
        function MkFn(X: Integer): TFn;
        procedure Go;
      end;
    function TCls.MkFn(X: Integer): TFn;
    begin
      Result := function: Integer begin Result := X * 2 end;
    end;
    procedure TCls.Go;
    begin
      MkFn(5);
      WriteLn(MkFn(6)());
    end;
    function PlainMk(X: Integer): TFn;
    begin
      Result := function: Integer begin Result := X + 1 end;
    end;
    var C: TCls; P: TMk; F: TFn;
    begin
      C := TCls.Create();
      C.MkFn(1);
      C.Go();
      P := @PlainMk;
      P(3);
      F := P(4);
      WriteLn(F());
      WriteLn(P(7)());
      PlainMk(2);
      WriteLn('done');
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_DiscardedResultOnNamedReceiver_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcNamedRecvDiscard, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('output, got: ' + Output, Pos('done' + LE, Output) >= 0);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ClosureReturningCalls_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcClosureReturning, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('output, got: ' + Output,
    Pos('12' + LE + '5' + LE + '8' + LE + 'done' + LE, Output) >= 0);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_DiscardedAggregateThroughProcValue_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcDiscardedAggProc, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'big' + LE + 'big' + LE + '3' + LE + 'str2' + LE +
    'big' + LE + 'big' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_OwnedClassTransientArgs_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcClassTransArgs, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'True True True 2 1 2 3 0 ' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

const
  SrcProcFieldResult = '''
    program pl3;
    uses SysUtils;
    type
      TC = reference to function(X: Integer): string;
      TO1 = reference to function: TObject;
      TS = function(X: Integer): string;
      THost = class
        C: TC; O: TO1; P: TS; S: string;
        procedure Take(const A: string);
        procedure Run;
      end;
    function SF(X: Integer): string; begin Result := 'p' + IntToStr(X) end;
    procedure THost.Take(const A: string); begin WriteLn('take ', A) end;
    procedure THost.Run;
    var L: string; Ob: TObject;
    begin
      WriteLn(C(2));
      L := C(3); WriteLn(L);
      S := C(4); WriteLn(S);
      Take(C(5));
      WriteLn(C(6) + C(7));
      Ob := O(); WriteLn(Ob <> nil);
      WriteLn(O() <> nil);
      WriteLn(P(8));
      L := P(9) + '!'; WriteLn(L);
    end;
    var H: THost;
    begin
      H := THost.Create();
      H.C := function(X: Integer): string begin Result := IntToStr(X) end;
      H.O := function: TObject begin Result := TObject.Create() end;
      H.P := @SF;
      H.Run();
    end.
    ''';
  SrcOwnedClassTested = '''
    program OwnTest;
    function MkO: TObject; begin Result := TObject.Create() end;
    var B: Boolean; O: TObject;
    begin
      WriteLn(MkO() <> nil);
      B := MkO() = nil; WriteLn(B);
      if MkO() <> nil then WriteLn('yes');
      WriteLn(MkO() is TObject);
      WriteLn(Assigned(MkO()));
      if Assigned(MkO()) and (MkO() is TObject) then WriteLn('ok');
      WriteLn(MkO() = MkO());
      O := MkO(); WriteLn(Assigned(O), ' ', O is TObject, ' ', O <> nil)
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_ImplicitSelfProcFieldResult_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcProcFieldResult, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '2' + LE + '3' + LE + '4' + LE + 'take 5' + LE +
    '67' + LE + 'True' + LE + 'True' + LE + 'p8' + LE + 'p9!' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_OwnedClassTested_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcOwnedClassTested, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'True' + LE + 'False' + LE + 'yes' + LE + 'True' + LE +
    'True' + LE + 'ok' + LE + 'False' + LE + 'True True True' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ForInEnumerator_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcForInEnum, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '9' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ForInEnumerator_NoLeak_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcForInEnum, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '9' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

const
  { The enumerator is allocated INSIDE TList<T>.GetEnumerator — a generic
    method body declared in generics.collections.pas.  The extra AddRef
    keeps it alive past scope exit, so the leak report must show its
    allocation site as 'generics.collections:<line>', not '<program>:<line>'. }
  SrcGenericAllocSite = '''
    program LeakGen;
    uses runtime.arc, generics.collections;
    var
      L: TList<Integer>;
      E: TListEnumerator<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(1);
      E := L.GetEnumerator();
      _ClassAddRef(Pointer(E));
      WriteLn('done')
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_GenericAllocSite_ReportsDefiningUnit_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcGenericAllocSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('enumerator class reported', Pos('TListEnumerator', Output) >= 0);
  AssertTrue('defining unit in report, got: ' + Output,
    Pos(' at Generics.Collections:', Output) >= 0);
  AssertTrue('instantiating program NOT in report, got: ' + Output,
    Pos(' at LeakGen:', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_GenericRecordAndFuncAllocSite_ReportsDefiningUnit;
const
  UnitSrc = '''
    unit gleaks;
    interface
    uses runtime.arc;
    type
      TRecLeak = class
        V: Integer;
      end;
      TFnLeak = class
        V: Integer;
      end;
      TMaker<T> = record
        X: T;
        function Make(): Integer;
      end;
    function Spawn<T>(A: T): Integer;
    implementation
    function TMaker<T>.Make(): Integer;
    var
      O: TRecLeak;
    begin
      O := TRecLeak.Create();
      _ClassAddRef(Pointer(O));
      Result := 1
    end;
    function Spawn<T>(A: T): Integer;
    var
      O: TFnLeak;
    begin
      O := TFnLeak.Create();
      _ClassAddRef(Pointer(O));
      Result := 2
    end;
    end.
    ''';
  ProgSrc = '''
    program UseGLeaks;
    uses gleaks;
    var
      M: TMaker<Integer>;
    begin
      WriteLn(M.Make() + Spawn<Integer>(5))
    end.
    ''';
var
  Output: string;
  ExitCode, P: Integer;
begin
  { Both instances are monomorphised in the program, but their bodies (and
    the line numbers in the report) are the unit's source. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  ExitCode := RunUnitFiniDebug('native', UnitSrc, '', ProgSrc, Output);
  AssertEquals('exit 0, got: ' + Output, 0, ExitCode);
  AssertTrue('leak header, got: ' + Output,
    Pos('Blaise leak report', Output) >= 0);
  AssertTrue('record-method allocation under the unit, got: ' + Output,
    Pos('TRecLeak', Output) >= 0);
  AssertTrue('function allocation reported, got: ' + Output,
    Pos('TFnLeak', Output) >= 0);
  P := Pos(' at gleaks:', Output);
  AssertTrue('first under the declaring unit, got: ' + Output, P >= 0);
  AssertTrue('second under the declaring unit, got: ' + Output,
    Pos(' at gleaks:', Copy(Output, P + 1, Length(Output))) >= 0);
  AssertTrue('instantiating program NOT in report, got: ' + Output,
    Pos(' at UseGLeaks:', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_NoLeak_NoReport;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcNoLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '99' + LE, Output);
  AssertTrue('no leak report', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ExceptionHandlerVar_NoLeakNoOverRelease;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcExceptionHandlerVar, Output, ExitCode, True));
  { Clean exit (no abort from a negative-refcount free), expected stdout, and
    no leak report (the exception is freed exactly once). }
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'caught' + LE + 'done' + LE, Output);
  AssertTrue('no leak report', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ConstructorWithArgs_NoDoubleAddRef;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcConstructorWithArgs, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '42' + LE, Output);
  AssertTrue('no leak report', Pos('Blaise leak report', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_LeakedObject_ReportedOnExit;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcOneLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 1', Pos('1 leak(s)', Output) >= 0);
  AssertTrue('class name', Pos('TBox', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_MultipleLeaks_AllReported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcTwoLeaks, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 2', Pos('2 leak(s)', Output) >= 0);
  AssertTrue('TAlpha reported', Pos('TAlpha', Output) >= 0);
  AssertTrue('TBeta reported', Pos('TBeta', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_CycleRetained_Reported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcCycleLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 2', Pos('2 leak(s)', Output) >= 0);
  AssertTrue('TNode reported', Pos('TNode', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestRelease_NoReport_WhenDebugOff;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { Same leaking source but compiled without debug mode — no report expected. }
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcOneLeak, Output, ExitCode, False));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('no leak report', Pos('Blaise leak report', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_LeakReport_IncludesUnitAndLine_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcLeakWithSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('class name', Pos('TBox', Output) >= 0);
  AssertTrue('unit name in report', Pos('LeakSite', Output) >= 0);
  AssertTrue('at separator', Pos(' at ', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StringLeak_Reported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcStringLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('string tag', Pos('string', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StringClean_NoReport;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcStringClean, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('no leak report', Pos('Blaise leak report', Output) < 0);
end;

const
  SrcClassFieldFromCall = '''
    program P;
    type
      TThing = class N: Integer; end;
      THolder = class Item: TThing; end;
    function MakeThing(): TThing;
    begin
      Result := TThing.Create();
      Result.N := 7;
    end;
    var
      H: THolder;
      I: Integer;
    begin
      H := THolder.Create();
      for I := 1 to 100 do
        H.Item := MakeThing();
      WriteLn(H.Item.N);
    end.
    ''';

  { A function returning a class leaves Result at +1 (the callee's `Result := x`
    AddRef'd and the epilogue did not release it).  Assigning that call result to
    a local consumes the transferred reference — the assignment site must NOT
    AddRef again, or one object leaks per call.  The native backend used to
    AddRef class assignments unconditionally; this pins the elision. }
  SrcFuncReturnAssign = '''
    program P;
    type
      TThing = class N: Integer; end;
    function MakeThing(): TThing;
    begin
      Result := TThing.Create();
      Result.N := 9;
    end;
    var
      T: TThing;
      I, Sum: Integer;
    begin
      Sum := 0;
      for I := 1 to 100 do
      begin
        T := MakeThing();
        Sum := Sum + T.N;
        T := nil;
      end;
      WriteLn(Sum);
    end.
    ''';

  { A class-returning function called in STATEMENT position discards its
    result.  The callee transferred a +1 reference (Result was AddRef'd on
    `Result := x` and not released at scope exit); the discard must release it
    or one object leaks per call.  This is the same transient-release rule the
    assignment path applies (SrcFuncReturnAssign above), for the discarded case.
    Regressed on BOTH backends before the discarded-class-call release landed in
    EmitProcCall (qbe) / EmitStmt's TProcCall tail (native). }
  SrcDiscardedClassReturn = '''
    program P;
    type
      TThing = class N: Integer; end;
    function MakeThing(): TThing;
    begin
      Result := TThing.Create();
      Result.N := 7;
    end;
    var
      I: Integer;
    begin
      for I := 1 to 100 do
        MakeThing();
      WriteLn(100);
    end.
    ''';

  { X := Call().ClassField — reading a managed-class field off an OWNED
    call-result base.  The loaded value aliases into the base's object graph, so
    releasing the transient base (whose Destroy nils+frees the field) must not
    happen until the field value has been stored, or the stored reference
    dangles.  On QBE this was a use-after-free (the base was released inline);
    the program must print 42, not garbage, after allocation churn that would
    reuse the freed block.  (Guards the deferred-base-release fix.) }
  SrcCallResultClassFieldRead = '''
    program P;
    type
      TInner = class N: Integer; end;
      TOuter = class
        Inner: TInner;
        destructor Destroy; override;
      end;
    destructor TOuter.Destroy;
    begin
      Inner := nil;
      inherited Destroy();
    end;
    function MakeOuter(): TOuter;
    begin
      Result := TOuter.Create();
      Result.Inner := TInner.Create();
      Result.Inner.N := 42;
    end;
    var
      X: TInner;
      I: Integer;
      Junk: TInner;
    begin
      X := MakeOuter().Inner;
      for I := 0 to 100 do
        Junk := TInner.Create();
      WriteLn(X.N);
      X := nil;
    end.
    ''';

  { BUG-049: transient-field read as a CALL ARGUMENT (Take(MakeBox().Inner)).
    A statement-level call is not one of the four leaf-assignment kinds; before
    the every-statement flush the deferred base leaked. }
  SrcTransientFieldInCallArg = '''
    program P;
    type
      TBox = class Inner: TObject; constructor Create; end;
    constructor TBox.Create;
    begin
      Inner := TObject.Create();
    end;
    function MakeBox: TBox;
    begin
      Result := TBox.Create();
    end;
    procedure Take(O: TObject);
    begin
    end;
    begin
      Take(MakeBox().Inner);
      WriteLn('done')
    end.
    ''';

  { BUG-049: transient-field read in an IF CONDITION. }
  SrcTransientFieldInIfCond = '''
    program P;
    type
      TBox = class Inner: TObject; constructor Create; end;
    constructor TBox.Create;
    begin
      Inner := TObject.Create();
    end;
    function MakeBox: TBox;
    begin
      Result := TBox.Create();
    end;
    begin
      if MakeBox().Inner <> nil then
        WriteLn('yes')
      else
        WriteLn('no')
    end.
    ''';

  { BUG-049: transient-field read in a WHILE CONDITION, evaluated per iteration.
    The loop runs several times; a single post-loop flush would release only
    the last iteration's transient — the per-iteration flush releases each. }
  SrcTransientFieldInWhileCond = '''
    program P;
    type
      TBox = class Inner: TObject; Val: Integer; constructor Create(V: Integer); end;
    constructor TBox.Create(V: Integer);
    begin
      Inner := TObject.Create();
      Val := V;
    end;
    function MakeBox(V: Integer): TBox;
    begin
      Result := TBox.Create(V);
    end;
    var I: Integer;
    begin
      I := 0;
      while (I < 5) and (MakeBox(I).Inner <> nil) do
        I := I + 1;
      WriteLn(I)
    end.
    ''';

  { A DEEP chain field read: MakeIt().A.B.N reads a scalar field off a base that
    is itself two field-reads-off-an-owned-transient.  EmitInstancePtr resolved
    each intermediate hop's owned transient (the MakeIt() result, then .A, .B)
    without releasing it, leaking every intermediate on QBE (3) and native (2).
    The value 7 must still print (no use-after-free), and — once the base
    releases are deferred to statement end — no transient should leak. }
  SrcDeepChainFieldRead = '''
    program P;
    type
      TB = class N: Integer; end;
      TA = class B: TB; destructor Destroy; override; end;
      TOuter = class A: TA; destructor Destroy; override; end;
    destructor TA.Destroy; begin B := nil; inherited Destroy(); end;
    destructor TOuter.Destroy; begin A := nil; inherited Destroy(); end;
    function MakeIt(): TOuter;
    begin
      Result := TOuter.Create();
      Result.A := TA.Create();
      Result.A.B := TB.Create();
      Result.A.B.N := 7;
    end;
    var
      V: Integer;
      I: Integer;
      Junk: TB;
    begin
      V := MakeIt().A.B.N;
      for I := 0 to 100 do
        Junk := TB.Create();
      WriteLn(V);
    end.
    ''';

  SrcMultiHandlerVar = '''
    program P;
    type
      EBase = class
        FMessage: string;
      end;
      EFoo = class(EBase) end;
    var X: Integer;
    begin
      X := 0;
      try
        raise EFoo.Create()
      except
        on E: EFoo do X := 42;
        on E: EBase do X := 1
      end;
      WriteLn(X)
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_ClassFieldFromCall_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcClassFieldFromCall, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '7' + LE, Output);
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_FuncReturnAssign_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcFuncReturnAssign, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '900' + LE, Output);
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_DiscardedClassReturn_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcDiscardedClassReturn, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '100' + LE, Output);
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_CallResultClassFieldRead_NoUseAfterFree;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { The CORRECTNESS guard: the stored field value must survive the base
    release + allocation churn and still read 42. }
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcCallResultClassFieldRead, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertTrue('field value survives base release, prints 42 (native)',
    Pos('42' + LE, Output) >= 0);
  { Native now defers the owned base release to statement end (BUG-003 native
    half), so the field value's +1 no longer leaks. }
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_TransientFieldInCallArg_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTransientFieldInCallArg, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_TransientFieldInIfCond_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTransientFieldInIfCond, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_TransientFieldInWhileCond_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { the loop runs 5 iterations; per-iteration flush releases each transient —
    a single post-loop flush would leak 4. }
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTransientFieldInWhileCond, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertTrue('loop count (native)', Pos('5' + LE, Output) >= 0);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_DeepChainFieldRead_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcDeepChainFieldRead, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertTrue('deep-chain value survives, prints 7 (native)',
    Pos('7' + LE, Output) >= 0);
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_MultiHandlerVar_NoOverRelease;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcMultiHandlerVar, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '42' + LE, Output);
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

const
  { Interface-returning call result passed positionally — Show(MakeFoo(42)).
    MakeFoo returns an owned (+1) interface; the borrowing parameter does not
    release it, so the caller must.  One TFoo leaked on native before the
    akIntfConsume hoist released it after the call. }
  SrcIntfCallResultArg = '''
    program P;
    type
      IFoo = interface
        function Val: Integer;
      end;
      TFoo = class(TObject, IFoo)
        FN: Integer;
        function Val: Integer;
      end;
    function TFoo.Val: Integer;
    begin Result := FN end;
    function MakeFoo(N: Integer): IFoo;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.FN := N;
      Result := F
    end;
    procedure Show(F: IFoo);
    begin
      WriteLn(F.Val())
    end;
    begin
      Show(MakeFoo(42))
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_IntfCallResultArg_NoLeak_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcIntfCallResultArg, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '42' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

const
  { Call result used as a field-access receiver — the getter's +1 must be
    released after the field read, otherwise one object leaks per access.
    Uses TList<T>[I].HitPoints which is the most common trigger. }
  SrcReceiverFieldAccess = '''
    program P;
    type
      TCreature = class
        HitPoints: Integer;
      end;
    function MakeCreature(): TCreature;
    begin
      Result := TCreature.Create();
      Result.HitPoints := 42;
    end;
    var
      X: Integer;
    begin
      X := MakeCreature().HitPoints;
      WriteLn(X);
    end.
    ''';

  { Static array of interfaces: three IGreet elements stored into a local
    array[0..2].  Scope-exit cleanup must release each element.  Prints the
    three greetings, then exits with no leak report. }
  SrcStaticArrayOfInterface = '''
    program P;
    type
      IGreet = interface
        function Name(): string;
      end;
      TGreet = class(IGreet)
        FName: string;
        function Name(): string;
      end;
    function TGreet.Name(): string;
    begin
      Result := Self.FName;
    end;
    procedure MakeInto(var G: IGreet; const N: string);
    var
      T: TGreet;
    begin
      T := TGreet.Create();
      T.FName := N;
      G := T;
    end;
    procedure Run();
    var
      Arr: array[0..2] of IGreet;
      I: Integer;
    begin
      MakeInto(Arr[0], 'a');
      MakeInto(Arr[1], 'b');
      MakeInto(Arr[2], 'c');
      for I := 0 to 2 do
        Write(Arr[I].Name());
      WriteLn('');
    end;
    begin
      Run();
    end.
    ''';

  { A string-returning getter used directly as a WriteLn argument.  The getter
    returns a fresh +1 string (Copy result); WriteLn only borrows it, so the
    caller must release it after the write.  Three calls => three leaks before
    the fix. }
  SrcWriteLnCallArg = '''
    program P;
    type
      TFoo = class
      private
        function GetBar: String;
      public
        property Bar: String read GetBar;
      end;
    function TFoo.GetBar: String;
    begin
      Result := Copy('abcd', 1, 3);
    end;
    var
      X: TFoo;
    begin
      X := TFoo.Create;
      WriteLn(X.Bar);
      WriteLn(X.Bar);
      WriteLn(X.Bar);
      X := nil;
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_ReceiverFieldAccess_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcReceiverFieldAccess, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '42' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StaticArrayOfInterface_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcStaticArrayOfInterface, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'abc' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

const
  SrcStaticArrayOfClass = '''
    program P;
    type
      TObjX = class
      public
        Tag: Integer;
        constructor Create(ATag: Integer);
      end;
    constructor TObjX.Create(ATag: Integer);
    begin
      Tag := ATag;
    end;
    procedure Run();
    var
      A: array[0..2] of TObjX;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := TObjX.Create(I * 10);
      WriteLn(A[2].Tag);
    end;
    begin
      Run();
    end.
    ''';

  SrcStaticArrayOfString = '''
    program P;
    procedure Run();
    var
      A: array[0..2] of string;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := 'val' + IntToStr(I);
      WriteLn(A[2]);
    end;
    begin
      Run();
    end.
    ''';

  SrcStaticArrayOfRecord = '''
    program P;
    type
      TRecX = record
        Name: string;
      end;
    procedure Run();
    var
      A: array[0..2] of TRecX;
      R: TRecX;
      I: Integer;
    begin
      for I := 0 to 2 do
      begin
        R.Name := 'val' + IntToStr(I);
        A[I] := R;
      end;
      WriteLn(A[2].Name);
    end;
    begin
      Run();
    end.
    ''';

  SrcStaticArrayOfClassExcExit = '''
    program P;
    uses SysUtils;
    type
      TObjX = class
      public
        Tag: Integer;
        constructor Create(ATag: Integer);
      end;
    constructor TObjX.Create(ATag: Integer);
    begin
      Tag := ATag;
    end;
    procedure Run();
    var
      A: array[0..2] of TObjX;
      I: Integer;
    begin
      try
        for I := 0 to 2 do
          A[I] := TObjX.Create(I);
        raise Exception.Create('boom');
      except
        on E: Exception do
          WriteLn('caught');
      end;
    end;
    begin
      Run();
    end.
    ''';

  SrcStaticArrayManualFree = '''
    program P;
    type
      TBuf = class
      public
        Tag: Integer;
        constructor Create(ATag: Integer);
      end;
    constructor TBuf.Create(ATag: Integer);
    begin
      Tag := ATag;
    end;
    procedure Run();
    var
      A: array[0..3] of TBuf;
      B: array[0..15] of TBuf;
      I: Integer;
      Bad: Boolean;
    begin
      for I := 0 to 3 do
        A[I] := TBuf.Create(100 + I);
      for I := 0 to 3 do
        A[I].Free();
      { second round simulates a scope-exit release on top of a manual
        free: it MUST be a nil no-op, not a second decrement }
      for I := 0 to 3 do
        A[I].Free();
      Bad := False;
      for I := 0 to 15 do
      begin
        B[I] := TBuf.Create(1000 + I);
        B[I].Tag := 2000 + I;
      end;
      for I := 0 to 15 do
        if B[I].Tag <> 2000 + I then
          Bad := True;
      for I := 0 to 15 do
        B[I].Free();
      if Bad then
        WriteLn('CORRUPT')
      else
        WriteLn('CLEAN');
    end;
    begin
      Run();
    end.
    ''';

  SrcRecordStaticArrayField = '''
    program P;
    type
      TRecX = record
        Names: array[0..2] of string;
      end;
    procedure Run();
    var
      R: TRecX;
      I: Integer;
    begin
      for I := 0 to 2 do
        R.Names[I] := 'val' + IntToStr(I);
      WriteLn(R.Names[2]);
    end;
    begin
      Run();
    end.
    ''';

  SrcRecordStaticArrayFieldByVal = '''
    program P;
    type
      TRecX = record
        Names: array[0..2] of string;
      end;
    procedure Show(R: TRecX);
    begin
      WriteLn(R.Names[1]);
    end;
    procedure Run();
    var
      R: TRecX;
      I: Integer;
    begin
      for I := 0 to 2 do
        R.Names[I] := 'val' + IntToStr(I);
      Show(R);
    end;
    begin
      Run();
    end.
    ''';

  SrcClassStaticArrayField = '''
    program P;
    type
      TBox = class
      public
        Names: array[0..2] of string;
      end;
    procedure Run();
    var
      B: TBox;
      I: Integer;
    begin
      B := TBox.Create();
      for I := 0 to 2 do
        B.Names[I] := 'val' + IntToStr(I);
      WriteLn(B.Names[2]);
      B.Free();
    end;
    begin
      Run();
    end.
    ''';

  { --- PROGRAM-LEVEL static arrays -------------------------------------
    Same shapes as the Src*StaticArray* consts above, but with the array
    declared in the PROGRAM var block and filled by the main body, so the
    array is a GLOBAL rather than a procedure-frame local.  That routes the
    cleanup through the native EmitGlobalReleases walk instead of the
    procedure-frame walk. }

  SrcProgStaticArrayOfClass = '''
    program P;
    type
      TObjX = class
      public
        Tag: Integer;
        constructor Create(ATag: Integer);
      end;
    constructor TObjX.Create(ATag: Integer);
    begin
      Tag := ATag;
    end;
    var
      A: array[0..2] of TObjX;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := TObjX.Create(I * 10);
      WriteLn(A[2].Tag);
    end.
    ''';

  SrcProgStaticArrayOfString = '''
    program P;
    var
      A: array[0..2] of string;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := 'val' + IntToStr(I);
      WriteLn(A[2]);
    end.
    ''';

  SrcProgStaticArrayOfInterface = '''
    program P;
    type
      IGreet = interface
        function Name(): string;
      end;
      TGreet = class(IGreet)
        FName: string;
        function Name(): string;
      end;
    function TGreet.Name(): string;
    begin
      Result := Self.FName;
    end;
    procedure MakeInto(var G: IGreet; const N: string);
    var
      T: TGreet;
    begin
      T := TGreet.Create();
      T.FName := N;
      G := T;
    end;
    var
      Arr: array[0..2] of IGreet;
      I: Integer;
    begin
      MakeInto(Arr[0], 'a');
      MakeInto(Arr[1], 'b');
      MakeInto(Arr[2], 'c');
      for I := 0 to 2 do
        Write(Arr[I].Name());
      WriteLn('');
    end.
    ''';

  SrcProgStaticArrayOfRecord = '''
    program P;
    type
      TRecX = record
        Name: string;
      end;
    var
      A: array[0..2] of TRecX;
      R: TRecX;
      I: Integer;
    begin
      for I := 0 to 2 do
      begin
        R.Name := 'val' + IntToStr(I);
        A[I] := R;
      end;
      WriteLn(A[2].Name);
    end.
    ''';

  { Program-level twin of SrcStaticArrayManualFree: manual .Free of every
    element, a second Free round that must be a nil no-op, then 16 further
    allocations churned through the free list with a sentinel check.  If the
    new main-exit release double-freed a manually-freed element, the churn
    would read back a corrupted Tag (or crash). }
  SrcProgStaticArrayManualFree = '''
    program P;
    type
      TBuf = class
      public
        Tag: Integer;
        constructor Create(ATag: Integer);
      end;
    constructor TBuf.Create(ATag: Integer);
    begin
      Tag := ATag;
    end;
    var
      A: array[0..3] of TBuf;
      B: array[0..15] of TBuf;
      I: Integer;
      Bad: Boolean;
    begin
      for I := 0 to 3 do
        A[I] := TBuf.Create(100 + I);
      for I := 0 to 3 do
        A[I].Free();
      { second round simulates the main-exit release landing on top of a
        manual free: it MUST be a nil no-op, not a second decrement }
      for I := 0 to 3 do
        A[I].Free();
      Bad := False;
      for I := 0 to 15 do
      begin
        B[I] := TBuf.Create(1000 + I);
        B[I].Tag := 2000 + I;
      end;
      for I := 0 to 15 do
        if B[I].Tag <> 2000 + I then
          Bad := True;
      for I := 0 to 15 do
        B[I].Free();
      if Bad then
        WriteLn('CORRUPT')
      else
        WriteLn('CLEAN');
    end.
    ''';

  SrcProgStaticArrayExcExit = '''
    program P;
    uses SysUtils;
    type
      TObjX = class
      public
        Tag: Integer;
        constructor Create(ATag: Integer);
      end;
    constructor TObjX.Create(ATag: Integer);
    begin
      Tag := ATag;
    end;
    var
      A: array[0..2] of TObjX;
      I: Integer;
    begin
      try
        for I := 0 to 2 do
          A[I] := TObjX.Create(I);
        raise Exception.Create('boom');
      except
        on E: Exception do
          WriteLn('caught');
      end;
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_StaticArrayOfClass_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcStaticArrayOfClass, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '20' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StaticArrayOfString_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcStaticArrayOfString, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'val2' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StaticArrayOfRecord_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcStaticArrayOfRecord, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'val2' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StaticArrayOfClass_ExceptionExit_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcStaticArrayOfClassExcExit, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'caught' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StaticArrayManualFree_NoDoubleFree;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcStaticArrayManualFree, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'CLEAN' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_RecordStaticArrayField_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcRecordStaticArrayField, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'val2' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_RecordStaticArrayField_ByValueParam_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcRecordStaticArrayFieldByVal, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'val1' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ClassStaticArrayField_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcClassStaticArrayField, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'val2' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ProgramLevelStaticArrayOfClass_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcProgStaticArrayOfClass, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '20' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ProgramLevelStaticArrayOfString_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcProgStaticArrayOfString, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'val2' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ProgramLevelStaticArrayOfInterface_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcProgStaticArrayOfInterface, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'abc' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ProgramLevelStaticArrayOfRecord_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcProgStaticArrayOfRecord, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'val2' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ProgramLevelStaticArrayManualFree_NoDoubleFree;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcProgStaticArrayManualFree, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'CLEAN' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ProgramLevelStaticArray_ExceptionExit_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { A caught exception leaks its `Exception (rc=0)` object on BOTH backends
    (pre-existing, filed separately), so assert on the ELEMENT class name
    instead of the bare word 'leak'. }
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcProgStaticArrayExcExit, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'caught' + LE, Output);
  AssertTrue('no TObjX leaked (native), got: ' + Output, Pos('TObjX', Output) < 0);
end;

const
  { Owned (+1) string temporaries passed to BY-VALUE string parameters: a
    plain procedure call, a method call, and a bare implicit-Self method-call
    ident.  The callee's entry-retain/exit-release pair nets to zero, so the
    caller must release each call-result temp after the call — 3 x 20 strings
    leak otherwise. }
  SrcValueStrCallResultArg = '''
    program P;
    type
      TSink = class
        Total: Integer;
        function Tag(): string;
        procedure Push(S: string);
        procedure PushTag();
      end;
    function TSink.Tag(): string;
    begin
      Result := 'tag-' + IntToStr(Self.Total);
    end;
    procedure TSink.Push(S: string);
    begin
      Total := Total + Length(S);
    end;
    procedure TSink.PushTag();
    begin
      Push(Tag());
    end;
    function MakeStr(I: Integer): string;
    begin
      Result := 'value-' + IntToStr(I);
    end;
    procedure SinkVal(S: string);
    begin
      if Length(S) = 0 then WriteLn('never');
    end;
    var
      K: TSink;
      I: Integer;
    begin
      K := TSink.Create();
      for I := 1 to 20 do
      begin
        SinkVal(MakeStr(I));
        K.Push(MakeStr(I));
        K.PushTag();
      end;
      if K.Total > 0 then
        WriteLn('done');
      K := nil;
    end.
    ''';

const
  { Owned (+1) string temporaries as BUILT-IN arguments.  Each shape leaked
    one string per call before the built-in arg-release fix:
      - int-returning file built-in:   FileAge(MakePath(I))
      - string-returning built-in:     Trim(MakeStr(I))  (result consumed by
                                       assignment; the ARG temp is the leak)
      - inline built-in (no RTL call): Length(MakeStr(I))
      - checked-routed built-in:       StrToInt(MakeNum(I))
      - nested built-ins:              LowerCase(Trim(MakeStr(I))) — the inner
                                       result is an owned temp of the outer. }
  SrcBuiltinOwnedStrArg = '''
    program P;
    function MakeStr(I: Integer): string;
    begin
      Result := '  v-' + IntToStr(I) + '  ';
    end;
    function MakePath(I: Integer): string;
    begin
      Result := '/nonexistent/dir/f' + IntToStr(I) + '.txt';
    end;
    function MakeNum(I: Integer): string;
    begin
      Result := IntToStr(1000 + I);
    end;
    var
      I, N: Integer;
      A: Int64;
      S: string;
    begin
      N := 0;
      for I := 1 to 20 do
      begin
        A := FileAge(MakePath(I));
        if A < -1 then WriteLn('never');
        S := Trim(MakeStr(I));
        N := N + Length(S);
        N := N + Length(MakeStr(I));
        N := N + StrToInt(MakeNum(I));
        S := LowerCase(Trim(MakeStr(I)));
        N := N + Length(S);
      end;
      if N > 0 then
        WriteLn('done');
    end.
    ''';

const
  { Every shape that used to leak an rc=0 (or unreleased rc=1) string
    transient, hammered enough that a regression visibly grows the arena
    registry.  Warm-up first so free-list steady state is reached before
    the baseline arena count is taken. }
  SrcStrTransientDispose = '''
    program P;
    uses runtime.mem;
    function MakeStr(I: Integer): string;
    begin
      Result := 'value-' + IntToStr(I);
    end;
    procedure SinkVal(S: string);
    begin
      if Length(S) = 0 then WriteLn('never');
    end;
    var
      I, A0, A1: Integer;
      S: string;
    begin
      for I := 1 to 200 do
      begin
        S := 'x' + IntToStr(I) + 'y';
        S := MakeStr(I) + 'y';
      end;
      A0 := _MemArenaCount();
      for I := 1 to 50000 do
      begin
        S := 'x' + IntToStr(I) + 'y';          { rc=0 concat operands }
        S := MakeStr(I) + 'y';                 { rc=1 user-call operand }
        S := LowerCase(Trim(MakeStr(I)));      { rc=0 built-in result as arg }
        SinkVal('v-' + IntToStr(I));           { rc=0 concat as value arg }
        if FileExists('/nonexistent/' + IntToStr(I)) then
          WriteLn('never');                    { rc=0 concat as built-in arg }
      end;
      A1 := _MemArenaCount();
      if A1 - A0 <= 2 then
        WriteLn('done')
      else
        WriteLn('arena growth: ', A1 - A0);
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_StrTransientDispose_NoArenaGrowth_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcStrTransientDispose, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'done' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_BuiltinOwnedStrArg_NoLeak_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcBuiltinOwnedStrArg, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'done' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ValueStrCallResultArg_NoLeak_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcValueStrCallResultArg, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'done' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_WriteLnCallArg_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcWriteLnCallArg, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', 'bcd' + LE + 'bcd' + LE + 'bcd' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

const
  { Phase 7 closure-argument ABI: a capturing LITERAL passed as an argument
    (by-address, borrow), stored into an object field (retain), invoked, then
    nil'd and freed.  Guards the literal-temp transient release (pending
    flush / value-slot scope release) + the field's retain/release balance —
    the exact ARC choreography behind TTaskGroup.Spawn(closure). }
  SrcClosureArgBalance = '''
    program P;
    type
      TP = reference to procedure;
      TBox = class
      public
        Proc: TP;
      end;
    procedure Stash(AProc: TP; ABox: TBox);
    begin
      ABox.Proc := AProc
    end;
    procedure Driver;
    var
      B: TBox;
      N: Integer;
    begin
      B := TBox.Create();
      N := 6;
      Stash(procedure begin WriteLn(N + 1) end, B);
      B.Proc();
      B.Proc := nil;
      B.Free()
    end;
    begin
      Driver();
      WriteLn('done')
    end.
    ''';

  { Escaping closure: env allocated in Make, last release when the global
    closure slot is released at program exit. }
  SrcClosureEnvOnce = '''
    program P;
    uses runtime.arc;
    type
      TProc = reference to procedure;
    var
      G: TProc;
    procedure Make;
    var
      Secret: Integer;
    begin
      Secret := 7;
      G := procedure
      begin
        WriteLn(Secret)
      end
    end;
    begin
      Make();
      G();
      G := nil;
      WriteLn('done')
    end.
    ''';

  { Captured string reassigned inside the closure body: the old value must be
    released on reassignment and the final value by the env cleanup proc. }
  SrcClosureCapturedString = '''
    program P;
    uses runtime.arc;
    type
      TProc = reference to procedure;
    procedure Run;
    var
      S: string;
      V: TProc;
    begin
      S := 'alpha';
      V := procedure
      begin
        S := S + '-beta';
        WriteLn(S)
      end;
      V()
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''';

const
  SrcClosureSelfCycle = '''
    program P;
    uses runtime.arc;
    type
      TProc = reference to procedure;
      TButton = class
        FOnClick: TProc;
        procedure Wire;
      end;
    procedure TButton.Wire;
    begin
      FOnClick := procedure
      begin
        Self.Wire()
      end
    end;
    procedure Make;
    var
      B: TButton;
    begin
      B := TButton.Create();
      B.Wire()
    end;
    begin
      Make();
      WriteLn('done')
    end.
    ''';

  SrcMethodPtrCoercionClean = '''
    program P;
    uses runtime.arc;
    type
      TProc = reference to procedure;
      TObj = class
        procedure Ping;
      end;
    procedure TObj.Ping;
    begin
      WriteLn('ping')
    end;
    procedure Run;
    var
      O: TObj;
      V: TProc;
    begin
      O := TObj.Create();
      V := @O.Ping;
      V()
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''';

const
  SrcBlockEnvLoop = '''
    program P;
    uses runtime.arc;
    type
      TProc = reference to procedure;
    procedure Run;
    var
      I: Integer;
      V: TProc;
    begin
      for I := 0 to 2 do
      begin
        var S: Integer := I;
        V := procedure begin WriteLn(S) end
      end;
      V();
      V := nil
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_BlockEnvPerIteration_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcBlockEnvLoop, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '2' + LE + 'done' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

const
  SrcClosureWeakSelfCycle = '''
    program P;
    uses runtime.arc;
    type
      TProc = reference to procedure;
      TButton = class
        FOnClick: TProc;
        procedure Wire;
      end;
    procedure TButton.Wire;
    begin
      FOnClick := procedure [Weak Self]
      begin
        if Self <> nil then Self.Wire()
      end
    end;
    procedure Make;
    var
      B: TButton;
    begin
      B := TButton.Create();
      B.Wire()
    end;
    begin
      Make();
      WriteLn('done')
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_ClosureWeakSelfCycle_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcClosureWeakSelfCycle, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'done' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ClosureSelfCycle_LeaksByDesign;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcClosureSelfCycle, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('strong Self-capture cycle leaks (documented until [Weak], ' +
    'got: ' + Output + ')', Pos('leak', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_MethodPtrCoercion_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcMethodPtrCoercionClean, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'ping' + LE + 'done' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ClosureEnv_ReleasedExactlyOnce;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcClosureEnvOnce, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '7' + LE + 'done' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_LinqLite_ProducedLists_NoLeak;
const
  { Phase 10: Map/Where allocate NEW lists; a string-producing Map's
    elements are ARC-managed.  Everything must balance once the produced
    lists are freed. }
  SrcLinqLeak = '''
    program P;
    uses Generics.Collections, Functional;
    var
      L: TList<Integer>;
      M: TList<string>;
      W: TList<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(1);
      L.Add(2);
      L.Add(3);
      M := L.Map<string>(N -> 'v' + IntToStr(N));
      W := L.Where(N -> N > 1);
      WriteLn(M[2], ':', W.Count);
      M.Clear();
      M.Free();
      W.Free();
      L.Free();
      WriteLn('done')
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcLinqLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'v3:2' + LE + 'done' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ClosureArgBalance_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcClosureArgBalance, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '7' + LE + 'done' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ClosureCapturedString_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcClosureCapturedString, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'alpha-beta' + LE + 'done' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

{ ---- Per-unit ARC teardown (<Unit>_fini) ---- }

{ Local copy of the base unit's implementation-private UnitNameOf: extract the
  unit name from a 'unit <name>;' header so the source can be written to the
  matching <name>.pas the unit loader expects. }
function FiniUnitNameOf(const ASrc: string): string;
var
  P, Q: Integer;
begin
  P := Pos('unit ', ASrc);
  if P < 0 then begin Result := ''; Exit; end;
  P := P + 5;
  Q := P;
  while (Q < Length(ASrc)) and (ASrc[Q] <> Ord(';')) and (ASrc[Q] <> Ord(' '))
        and (ASrc[Q] <> 10) and (ASrc[Q] <> 13) do
    Q := Q + 1;
  Result := Copy(ASrc, P, Q - P);
end;

procedure FiniWriteFile(const APath, AContent: string);
var
  SL: TStringList;
begin
  SL := TStringList.Create();
  try
    SL.Text := AContent;
    SL.SaveToFile(APath);
  finally
    SL.Free();
  end;
end;

{ Delete a stale per-unit artefact set so every compile is COLD-cache. }
procedure FiniDeleteUnitArtefacts(const ADir, AUnitName: string);
begin
  if AUnitName = '' then Exit;
  DeleteFile(ADir + '/' + LowerCase(AUnitName) + '.pas');
  DeleteFile(ADir + '/' + LowerCase(AUnitName) + '.o');
  DeleteFile(ADir + '/' + LowerCase(AUnitName) + '.bif');
end;

function FiniRunProc(const AExe: string; AArgs: TStringList;
                     out AStdout: string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    if AArgs <> nil then
      for I := 0 to AArgs.Count - 1 do
        Proc.Parameters.Add(AArgs.Strings[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TE2ELeakCheckTests.RunUnitFiniDebug(const ABackend, AUnit1Src,
  AUnit2Src, AProgSrc: string; out AOutput: string): Integer;
var
  Dir, ProgPas, BinPath, CompOut: string;
  Args: TStringList;
  Rc: Integer;
  NoArgs: TStringList;
begin
  Inc(FCounter);
  Dir := FScratch + '/unitfini' + IntToStr(FCounter) + '_' + ABackend;
  ForceDirectories(Dir);
  { Stale artefacts from a previous TestRunner invocation would warm the unit
    cache — delete them so the compile is cold and deterministic. }
  FiniDeleteUnitArtefacts(Dir, FiniUnitNameOf(AUnit1Src));
  FiniDeleteUnitArtefacts(Dir, FiniUnitNameOf(AUnit2Src));
  ProgPas := Dir + '/prog.pas';
  BinPath := Dir + '/prog';
  DeleteFile(ProgPas);
  DeleteFile(BinPath);
  if AUnit1Src <> '' then
    FiniWriteFile(Dir + '/' + LowerCase(FiniUnitNameOf(AUnit1Src)) + '.pas',
      AUnit1Src);
  if AUnit2Src <> '' then
    FiniWriteFile(Dir + '/' + LowerCase(FiniUnitNameOf(AUnit2Src)) + '.pas',
      AUnit2Src);
  FiniWriteFile(ProgPas, AProgSrc);
  Args := TStringList.Create();
  try
    Args.Add('--source');
    Args.Add(ProgPas);
    Args.Add('--unit-path');
    Args.Add(Dir);
    Args.Add('--unit-path');
    Args.Add(FRTLUnitPath);
    Args.Add('--unit-path');
    Args.Add(FStdlibUnitPath);
    Args.Add('--debug');
    Args.Add('--backend');
    Args.Add(ABackend);
    Args.Add('--output');
    Args.Add(BinPath);
    Rc := FiniRunProc(ProjectRoot() + 'compiler/target/blaise', Args, CompOut);
  finally
    Args.Free();
  end;
  if Rc <> 0 then
  begin
    AOutput := 'COMPILE FAILED (' + ABackend + '): ' + CompOut;
    Result := -Rc;
    if Result = 0 then Result := -1;
    Exit;
  end;
  NoArgs := TStringList.Create();
  try
    Result := FiniRunProc(BinPath, NoArgs, AOutput);
  finally
    NoArgs.Free();
  end;
end;

const
  SrcUnitFiniArrayUnit = '''
    unit UFinA;
    interface
    var
      UA: array[0..2] of string;
    procedure Fill();
    implementation
    procedure Fill();
    var
      I: Integer;
    begin
      for I := 0 to 2 do
        UA[I] := 'u' + IntToStr(I);
    end;
    end.
    ''';
  SrcUnitFiniArrayProg = '''
    program P;
    uses UFinA;
    begin
      Fill();
      WriteLn(UA[1]);
    end.
    ''';

  SrcUnitFiniScalarUnit = '''
    unit UFinS;
    interface
    var
      US: string;
    procedure SetIt();
    implementation
    procedure SetIt();
    begin
      US := 'sca' + 'lar';
    end;
    end.
    ''';
  SrcUnitFiniScalarProg = '''
    program P;
    uses UFinS;
    begin
      SetIt();
      WriteLn(US);
    end.
    ''';

  SrcUnitFiniClassUnit = '''
    unit UFinC;
    interface
    type
      TThing = class
        Name: string;
        destructor Destroy; override;
      end;
    var
      GT: TThing;
    procedure MakeIt();
    implementation
    destructor TThing.Destroy;
    begin
      WriteLn('down ', Name);
      inherited Destroy();
    end;
    procedure MakeIt();
    begin
      GT := TThing.Create();
      GT.Name := 'thing';
    end;
    end.
    ''';
  SrcUnitFiniClassProg = '''
    program P;
    uses UFinC;
    begin
      MakeIt();
      WriteLn('run');
    end.
    ''';

  SrcUnitFiniImplUnit = '''
    unit UFinP;
    interface
    procedure Bump();
    function Get(): string;
    implementation
    var
      Hidden: string;
    procedure Bump();
    begin
      Hidden := Hidden + 'x';
    end;
    function Get(): string;
    begin
      Result := Hidden;
    end;
    end.
    ''';
  SrcUnitFiniImplProg = '''
    program P;
    uses UFinP;
    begin
      Bump();
      Bump();
      Bump();
      WriteLn(Get());
    end.
    ''';

  SrcUnitFiniOrderUnitX = '''
    unit UFinX;
    interface
    type
      TX = class
        Tag: string;
        destructor Destroy; override;
      end;
    var
      GX: TX;
    procedure MakeX();
    implementation
    destructor TX.Destroy;
    begin
      WriteLn('down ', Tag);
      inherited Destroy();
    end;
    procedure MakeX();
    begin
      GX := TX.Create();
      GX.Tag := 'X';
    end;
    end.
    ''';
  SrcUnitFiniOrderUnitY = '''
    unit UFinY;
    interface
    type
      TY = class
        Tag: string;
        destructor Destroy; override;
      end;
    var
      GY: TY;
    procedure MakeY();
    implementation
    destructor TY.Destroy;
    begin
      WriteLn('down ', Tag);
      inherited Destroy();
    end;
    procedure MakeY();
    begin
      GY := TY.Create();
      GY.Tag := 'Y';
    end;
    end.
    ''';
  SrcUnitFiniOrderProg = '''
    program P;
    uses UFinX, UFinY;
    begin
      MakeX();
      MakeY();
      WriteLn('run');
    end.
    ''';

  SrcUnitFiniFinalUnit = '''
    unit UFinF;
    interface
    var
      FS: string;
    procedure SetF();
    implementation
    procedure SetF();
    begin
      FS := 'fin-' + 'live';
    end;
    finalization
      WriteLn('final sees ', FS);
    end.
    ''';
  SrcUnitFiniFinalProg = '''
    program P;
    uses UFinF;
    begin
      SetF();
      WriteLn('run');
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_UnitGlobalStaticArrayOfString_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  ExitCode := RunUnitFiniDebug('native', SrcUnitFiniArrayUnit, '',
    SrcUnitFiniArrayProg, Output);
  AssertEquals('exit 0 (native), got: ' + Output, 0, ExitCode);
  AssertTrue('stdout has u1 (native), got: ' + Output, Pos('u1', Output) >= 0);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_UnitGlobalScalarString_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  ExitCode := RunUnitFiniDebug('native', SrcUnitFiniScalarUnit, '',
    SrcUnitFiniScalarProg, Output);
  AssertEquals('exit 0 (native), got: ' + Output, 0, ExitCode);
  AssertTrue('stdout has scalar (native), got: ' + Output,
    Pos('scalar', Output) >= 0);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_UnitGlobalClass_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  ExitCode := RunUnitFiniDebug('native', SrcUnitFiniClassUnit, '',
    SrcUnitFiniClassProg, Output);
  AssertEquals('exit 0 (native), got: ' + Output, 0, ExitCode);
  AssertTrue('destructor ran at exit (native), got: ' + Output,
    Pos('down thing', Output) >= 0);
  AssertTrue('run before down (native), got: ' + Output,
    Pos('run', Output) < Pos('down thing', Output));
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_UnitImplementationGlobal_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  ExitCode := RunUnitFiniDebug('native', SrcUnitFiniImplUnit, '',
    SrcUnitFiniImplProg, Output);
  AssertEquals('exit 0 (native), got: ' + Output, 0, ExitCode);
  AssertTrue('stdout has xxx (native), got: ' + Output, Pos('xxx', Output) >= 0);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_TwoUnits_FiniReverseOrder;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  ExitCode := RunUnitFiniDebug('native', SrcUnitFiniOrderUnitX,
    SrcUnitFiniOrderUnitY, SrcUnitFiniOrderProg, Output);
  AssertEquals('exit 0 (native), got: ' + Output, 0, ExitCode);
  AssertTrue('Y destroyed (native), got: ' + Output, Pos('down Y', Output) >= 0);
  AssertTrue('X destroyed (native), got: ' + Output, Pos('down X', Output) >= 0);
  AssertTrue('Y down before X down (native), got: ' + Output,
    Pos('down Y', Output) < Pos('down X', Output));
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_FinalizationSection_RunsBeforeRelease;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  ExitCode := RunUnitFiniDebug('native', SrcUnitFiniFinalUnit, '',
    SrcUnitFiniFinalProg, Output);
  AssertEquals('exit 0 (native), got: ' + Output, 0, ExitCode);
  AssertTrue('finalization ran and saw the global (native), got: ' + Output,
    Pos('final sees fin-live', Output) >= 0);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_SretReassign_NoLeak;
const
  Src =
    '''
    program P;
    type
      TTag = record
        Name: string;
        static function Cat(const A, C: TTag): TTag;
        function Grow(const C: TTag): TTag;
      end;
    static function TTag.Cat(const A, C: TTag): TTag;
    begin Result.Name := A.Name + C.Name end;
    function TTag.Grow(const C: TTag): TTag;
    begin Result.Name := Self.Name + C.Name end;
    function MakeTag(const S: string): TTag;
    begin Result.Name := S end;
    var X, Y, Z, M: TTag; I: Integer;
    begin
      X.Name := 'a'; Y.Name := 'b';
      for I := 0 to 4 do Z := TTag.Cat(X, Y);   { static func, distinct dest }
      WriteLn('cat ', Z.Name);
      for I := 0 to 4 do Z := MakeTag('m');      { free func, distinct dest }
      WriteLn('make ', Z.Name);
      for I := 0 to 2 do X := TTag.Cat(X, Y);    { dest aliases ARG }
      WriteLn('alias-arg ', X.Name);
      M.Name := 'm';
      for I := 0 to 2 do M := M.Grow(Y);         { dest aliases RECEIVER }
      WriteLn('alias-recv ', M.Name)
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, Src, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)',
    'cat ab' + LE + 'make m' + LE + 'alias-arg abbb' + LE +
    'alias-recv mbbb' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ManagedRecordSelfAssign_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program P;
    uses SysUtils;
    type TRec = record A, B: string; N: Integer; end;
    var R: TRec;
    begin
      R.A := IntToStr(1) + 'x'; R.B := IntToStr(2) + 'y'; R.N := 7;
      R := R;
      WriteLn(R.A, R.B)
    end.
    ''', '1x2y');
end;

procedure TE2ELeakCheckTests.TestDebug_ExceptionNoVarHandler_NoLeak;
begin
  { Bare catch-all — no handler variable owns the exception. }
  AssertLeakFreeOnAll(
    '''
    program P;
    uses SysUtils;
    begin
      try raise Exception.Create('x') except WriteLn('caught') end
    end.
    ''', 'caught');
  { on Type do — no variable. }
  AssertLeakFreeOnAll(
    '''
    program P;
    uses SysUtils;
    begin
      try raise Exception.Create('x') except on Exception do WriteLn('caught') end
    end.
    ''', 'caught');
  { else branch handles an unmatched exception without a variable. }
  AssertLeakFreeOnAll(
    '''
    program P;
    uses SysUtils;
    type EFoo = class(Exception) end;
    begin
      try raise Exception.Create('x')
      except on E: EFoo do WriteLn('foo') else WriteLn('else') end
    end.
    ''', 'else');
  { derived class caught by a no-variable base handler (guards concrete-class
    registration/deregistration). }
  AssertLeakFreeOnAll(
    '''
    program P;
    uses SysUtils;
    type EFoo = class(Exception) end;
    begin
      try raise EFoo.Create('x') except on Exception do WriteLn('caught') end
    end.
    ''', 'caught');
end;

{ BUG-20260721-novar-handler-nonlocal-exit-leak: a handler with no
  variable whose body leaves by Exit, or by raising a NEW exception, leaked
  the caught one -- every form: bare except, on T do, else. }
procedure TE2ELeakCheckTests.TestDebug_ExceptionNoVarHandler_NonLocalExit_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program P;
    uses SysUtils;
    type
      E1 = class(Exception);
      E2 = class(Exception);
    procedure BareExit;
    begin
      try raise E1.Create('a') except Exit end;
      WriteLn('not here')
    end;
    procedure TypedExit;
    begin
      try raise E1.Create('b') except on E1 do Exit; end;
      WriteLn('not here')
    end;
    function ElseExit: Integer;
    begin
      Result := 1;
      try
        raise E2.Create('c')
      except
        on E1 do Result := 2;
      else
        begin Result := 3; Exit end;
      end;
      Result := 4
    end;
    procedure RaiseNew;
    begin
      try raise E1.Create('d') except raise E2.Create('e') end
    end;
    procedure TypedRaiseNew;
    begin
      try raise E1.Create('f') except on E1 do raise E2.Create('g'); end
    end;
    var I: Integer;
    begin
      BareExit();
      TypedExit();
      WriteLn(ElseExit());
      for I := 1 to 3 do
        try RaiseNew() except on E: E2 do WriteLn(E.Message) end;
      try TypedRaiseNew() except on E: E2 do WriteLn(E.Message) end
    end.
    ''', '3' + LineEnding + 'e' + LineEnding + 'e' + LineEnding + 'e' +
      LineEnding + 'g');
end;

{ A bare `raise;` re-raised the RTL's current exception -- the LAST one
  raised.  After a nested try/except in the handler body had handled its
  own exception, that was the inner one, already released, and the program
  aborted (rc 134), with or without a handler variable. }
procedure TE2ELeakCheckTests.TestRun_BareReraise_AfterNestedHandledException;
const
  Src = '''
    program P;
    uses SysUtils;
    type
      E1 = class(Exception);
      E2 = class(Exception);
    procedure Inner;
    begin
      try raise E2.Create('inner') except on E2 do ; end
    end;
    procedure NoVar;
    begin
      try
        raise E1.Create('no var')
      except
        on E1 do
        begin
          try raise E2.Create('x') except on E2 do WriteLn('inner handled') end;
          raise
        end;
      end
    end;
    procedure WithVar;
    begin
      try
        raise E1.Create('with var')
      except
        on X: E1 do
        begin
          Inner();
          raise
        end;
      end
    end;
    procedure CatchAll;
    begin
      try
        raise E1.Create('catch-all')
      except
        try raise E2.Create('y') except WriteLn('inner handled') end;
        raise
      end
    end;
    begin
      try NoVar() except on E: E1 do WriteLn('outer got ', E.Message) end;
      try WithVar() except on E: E1 do WriteLn('outer got ', E.Message) end;
      try CatchAll() except on E: E1 do WriteLn('outer got ', E.Message) end
    end.
    ''';
begin
  AssertLeakFreeOnAll(Src, 'outer got catch-all');
  AssertRunsOnAll(Src,
    'inner handled' + LineEnding + 'outer got no var' + LineEnding +
    'outer got with var' + LineEnding + 'inner handled' + LineEnding +
    'outer got catch-all' + LineEnding, 0);
end;

procedure TE2ELeakCheckTests.TestDebug_OwnedTransientSetterValues_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program P;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        N: Integer;
        function Val: Integer;
      end;
      TFoo = class
        N: Integer;
      end;
      THolder = class
        FFoo: TFoo;
        FArr: array[0..1] of TFoo;
        FThing: IThing;
        procedure SetFoo(V: TFoo);
        function GetItem(I: Integer): TFoo;
        procedure SetItem(I: Integer; V: TFoo);
        procedure SetThing(V: IThing);
        property Foo: TFoo read FFoo write SetFoo;
        property Items[I: Integer]: TFoo read GetItem write SetItem; default;
        property Thing: IThing read FThing write SetThing;
        procedure Fill;
      end;
    function TThing.Val: Integer; begin Result := N end;
    procedure THolder.SetFoo(V: TFoo); begin FFoo := V end;
    function THolder.GetItem(I: Integer): TFoo; begin Result := FArr[I] end;
    procedure THolder.SetItem(I: Integer; V: TFoo); begin FArr[I] := V end;
    procedure THolder.SetThing(V: IThing); begin FThing := V end;
    function MakeFoo(N: Integer): TFoo;
    begin
      Result := TFoo.Create();
      Result.N := N
    end;
    function MakeTThing(N: Integer): TThing;
    begin
      Result := TThing.Create();
      Result.N := N
    end;
    function MakeThing(N: Integer): IThing;
    begin
      Result := MakeTThing(N)
    end;
    function MakeHolder: THolder;
    begin
      Result := THolder.Create()
    end;
    procedure THolder.Fill;
    begin
      Foo := MakeFoo(9);
      Thing := MakeThing(9)
    end;
    procedure Run;
    var H: THolder;
    begin
      H := THolder.Create();
      H.Foo := MakeFoo(1);
      H.Foo := MakeFoo(2);
      H.Items[0] := MakeFoo(3);
      H[1] := MakeFoo(4);
      H[1] := MakeFoo(5);
      H.Thing := MakeThing(6);
      H.Thing := MakeTThing(7);
      H.Fill();
      MakeHolder().Foo := MakeFoo(8);
      MakeHolder().Thing := MakeThing(8);
      WriteLn(H.Foo.N, H[0].N, H[1].N, H.Thing.Val())
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''', '9359' + #10 + 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_OwnedClassToInterface_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program t4;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        N: Integer;
        function Val: Integer;
      end;
      THolder = class
        FThing: IThing;
        procedure Fill;
      end;
    function TThing.Val: Integer; begin Result := N end;
    function MakeTThing(N: Integer): TThing;
    begin
      Result := TThing.Create();
      Result.N := N
    end;
    function AsThing(N: Integer): IThing;
    begin
      Result := MakeTThing(N)
    end;
    procedure THolder.Fill;
    begin
      FThing := MakeTThing(3)
    end;
    function Use(T: IThing): Integer;
    begin
      Result := T.Val()
    end;
    procedure Run;
    var
      H: THolder;
      T: IThing;
    begin
      T := MakeTThing(1);
      H := THolder.Create();
      H.FThing := MakeTThing(2);
      H.Fill();
      WriteLn(T.Val(), H.FThing.Val(), AsThing(4).Val(), Use(MakeTThing(5)))
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''', '1345' + #10 + 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_DiscardedStringResult_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program P;
    uses SysUtils;
    function MakeStr(N: Integer): string;
    begin
      Result := 'x' + IntToStr(N)
    end;
    procedure Run;
    var I: Integer;
    begin
      for I := 1 to 3 do
        MakeStr(I)
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''', 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_OwnedTransientCastsAndTests_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program p34;
    uses SysUtils;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        function Val: Integer;
      end;
    function TThing.Val: Integer; begin Result := 3 end;
    function MakeThing: TThing; begin Result := TThing.Create() end;
    function MakeObj: TObject; begin Result := TThing.Create() end;
    procedure Run;
    var I: IThing; T: TThing;
    begin
      WriteLn(MakeThing().ClassName);
      if MakeThing().ClassType = TThing then WriteLn('type ok');
      if Supports(MakeObj(), IThing) then WriteLn('supports');
      T := MakeObj() as TThing;
      WriteLn(T.Val());
      I := MakeObj() as IThing;
      WriteLn(I.Val());
      WriteLn((MakeObj() as TThing).Val());
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', 'TThing' + #10 + 'type ok' + #10 + 'supports' + #10 + '3' + #10 + '3' + #10 + '3' + #10 + 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_CtorResultReceiver_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program q17;
    type
      TC = class
        procedure Go;
        function Val: Integer;
      end;
    procedure TC.Go;
    begin
      WriteLn('go');
    end;
    function TC.Val: Integer;
    begin
      Result := 7;
    end;
    begin
      TC.Create().Go();
      WriteLn(TC.Create().Val());
    end.
    ''', 'go' + #10 + '7');
end;

procedure TE2ELeakCheckTests.TestDebug_FreeAndVarArgThroughOwnedBase_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program p33;
    type
      TFoo = class
        N: Integer;
        destructor Destroy; override;
      end;
      THolder = class
        FFoo: TFoo;
        function GetFoo: TFoo;
        property Foo: TFoo read GetFoo;
      end;
    destructor TFoo.Destroy;
    begin
      WriteLn('destroy ', N);
      inherited Destroy();
    end;
    function THolder.GetFoo: TFoo; begin Result := FFoo end;
    function MakeFoo(N: Integer): TFoo;
    begin
      Result := TFoo.Create();
      Result.N := N;
    end;
    function MakeHolder: THolder;
    begin
      Result := THolder.Create();
      Result.FFoo := MakeFoo(9);
    end;
    var
      H: THolder;
    begin
      MakeFoo(1).Free();
      H := MakeHolder();
      H.Foo.Free();
      WriteLn('mid');
      MakeHolder().FFoo.Free();
      WriteLn('done');
    end.
    ''', 'destroy 1' + #10 + 'mid' + #10 + 'destroy 9' + #10 + 'done');
  AssertLeakFreeOnAll(
    '''
    program p38;
    type
      TPt = record
        X, Y: Integer;
        function Sum: Integer;
      end;
      THolder = class
        P: TPt;
        N: Integer;
      end;
    function TPt.Sum: Integer; begin Result := X + Y end;
    function MakeHolder: THolder;
    begin
      Result := THolder.Create();
      Result.P.X := 2;
      Result.P.Y := 5;
      Result.N := 4;
    end;
    procedure Bump(var V: Integer); begin V := V + 1 end;
    procedure Run;
    var
      Q: ^TPt;
    begin
      WriteLn(MakeHolder().P.Sum());
      Bump(MakeHolder().N);
      WriteLn('ok');
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', '7' + #10 + 'ok' + #10 + 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_OrdAtStringTransient_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program p32;
    uses SysUtils;
    function MakeStr(N: Integer): string;
    begin
      Result := 'ab' + IntToStr(N);
    end;
    procedure Run;
    var I, S: Integer;
    begin
      S := 0;
      for I := 1 to 3 do
        S := S + OrdAt(MakeStr(I), 1) + OrdAt('x' + IntToStr(I), 0);
      WriteLn(S);
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', '654' + #10 + 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_AddrOfOwnedTransientField_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program p37;
    type
      TObj = class
        N: Integer;
        destructor Destroy; override;
      end;
      PInt = ^Integer;
    destructor TObj.Destroy;
    begin
      WriteLn('destroy');
      inherited Destroy();
    end;
    function MakeObj: TObj; begin Result := TObj.Create() end;
    procedure Run;
    var P: PInt;
    begin
      P := @MakeObj().N;
      WriteLn(Assigned(P));
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', 'destroy' + #10 + 'True' + #10 + 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_OwnedIntoWeakTargets_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program p36;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        function Val: Integer;
        destructor Destroy; override;
      end;
    function TThing.Val: Integer; begin Result := 3 end;
    destructor TThing.Destroy;
    begin
      WriteLn('destroy');
      inherited Destroy();
    end;
    function MakeThing: TThing; begin Result := TThing.Create() end;
    function MakeI: IThing; begin Result := TThing.Create() end;
    procedure Run;
    var
      [Weak] W: TThing;
      [Weak] WI: IThing;
      S: TThing;
    begin
      W := MakeThing();
      WriteLn(Assigned(W));
      S := MakeThing();
      W := S;
      WriteLn(Assigned(W));
      S := nil;
      WriteLn(Assigned(W));
      WI := MakeI();
      WriteLn(Assigned(WI));
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', 'destroy' + #10 + 'False' + #10 + 'True' + #10 + 'destroy' + #10 + 'False' + #10 + 'destroy' + #10 + 'False' + #10 + 'done');
end;

procedure TE2ELeakCheckTests.TestDebug_MethodPtrAndClosureCopies_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program FatCopies;
    type
      TMeth = procedure of object;
      TClos = reference to procedure;
      THold = class N: Integer; procedure Hi; end;
      TRec = record M: TMeth; C: TClos; end;
      PRec = ^TRec;
      TObj = class M: TMeth; C: TClos; R: TRec; procedure Run; end;
    procedure THold.Hi; begin WriteLn('hi ', N) end;
    var GM: TMeth; GC: TClos; GR: TRec; AM: array[0..1] of TMeth; AC: array of TClos; PR: PRec;
    procedure TObj.Run;
    var LM: TMeth; LC: TClos;
    begin
      LM := M; LM(); LM := Self.R.M; LM();
      LC := C; LC(); LC := Self.R.C; LC();
      M := GM; M(); C := GC; C();
      R.M := LM; R.M(); R.C := LC; R.C();
    end;
    procedure VarTargets(var VM: TMeth; var VC: TClos);
    var LM: TMeth; LC: TClos;
      procedure Inner;
      begin
        LM := VM; LM(); VM := GR.M; VM();
        LC := VC; LC(); VC := GR.C; VC();
      end;
    begin
      Inner(); VM := AM[1]; VM(); VC := AC[0]; VC(); LM := PR^.M; LM(); LC := PR^.C; LC();
    end;
    procedure Run;
    var H: THold; O: TObj; LM: TMeth; LC: TClos;
    begin
      H := THold.Create(); H.N := 7;
      GM := @H.Hi; GC := procedure begin WriteLn('clos ', H.N) end;
      GR.M := GM; GR.C := GC; AM[1] := GM; SetLength(AC, 1); AC[0] := GC; PR := @GR;
      O := TObj.Create(); O.M := GM; O.C := GC; O.R.M := GM; O.R.C := GC;
      O.Run();
      LM := GM; LC := GC;
      VarTargets(LM, LC); LM(); LC();
      GC := nil; SetLength(AC, 0); GR.C := nil; LC := nil;
      O.C := nil; O.R.C := nil;
      AM[0] := LM; LM := AM[0]; LM();
      LC := procedure begin WriteLn('e ', H.N) end; SetLength(AC, 2); AC[1] := LC; LC := nil;
      LC := AC[1]; LC(); AC[1] := nil; LC := nil; SetLength(AC, 0);
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', 'hi 7' + #10 +
    'hi 7' + #10 +
    'clos 7' + #10 +
    'clos 7' + #10 +
    'hi 7' + #10 +
    'clos 7' + #10 +
    'hi 7' + #10 +
    'clos 7' + #10 +
    'hi 7' + #10 +
    'hi 7' + #10 +
    'clos 7' + #10 +
    'clos 7' + #10 +
    'hi 7' + #10 +
    'clos 7' + #10 +
    'hi 7' + #10 +
    'clos 7' + #10 +
    'hi 7' + #10 +
    'clos 7' + #10 +
    'hi 7' + #10 +
    'e 7' + #10 +
    'done');
end;

procedure TE2ELeakCheckTests.TestDebug_FieldStoresThroughCallsAndSelf_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program FieldStores;
    type
      TColor = (cRed, cGreen, cBlue);
      TSmallSet = set of TColor;
      TBig = set of 0..127;
      TSA = array[0..1] of Integer;
      TProc = procedure;
      TRec = record F: TSmallSet; B: TBig; end;
      TObj = class
        S: String; P: TProc; A: TSA; R: TRec;
        procedure Run(const G: TSA);
      end;
    var GO: TObj;
    procedure Hello; begin WriteLn('hello') end;
    function MakeObj: TObj; begin Result := GO end;
    procedure TObj.Run(const G: TSA);
    begin
      A := G; R.F := [cRed, cBlue]; R.B := [3, 100];
      WriteLn(A[0], ' ', A[1], ' ', cBlue in R.F, ' ', 100 in R.B);
    end;
    procedure Run;
    var G: TSA; I: Integer;
    begin
      GO := TObj.Create();
      for I := 1 to 3 do
      begin
        MakeObj().S := 'abc'; MakeObj().P := @Hello;
        G[0] := I; G[1] := Length(GO.S); GO.Run(G);
      end;
      GO.P(); WriteLn(GO.S);
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', '1 3 True True' + #10 +
    '2 3 True True' + #10 +
    '3 3 True True' + #10 +
    'hello' + #10 +
    'abc' + #10 +
    'done');
end;

procedure TE2ELeakCheckTests.TestDebug_ArrayFieldElementStores_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program ArrayFieldElems;
    type
      TDyn = array of Integer;
      TClos = reference to function: Integer;
      TMeth = procedure of object;
      THold = class N: Integer; procedure Hi; end;
      TObj = class
        M: array[0..1] of TMeth; C: array of TClos; D: array[0..1] of TDyn;
        F: array[0..2] of Double; S: array of Single;
        procedure Run;
      end;
    var H: THold; GO: TObj;
    procedure THold.Hi; begin WriteLn('hi ', N) end;
    function MakeObj: TObj; begin Result := GO end;
    function Mk(N: Integer): TDyn; begin SetLength(Result, 2); Result[1] := N end;
    procedure TObj.Run;
    var L: TMeth; K: TClos; X: TDyn;
    begin
      M[1] := @H.Hi; L := M[1]; L();
      C[0] := function: Integer begin Result := 77 end; K := C[0]; WriteLn(K());
      X := Mk(5); D[0] := X; SetLength(X, 0); X := Mk(9); WriteLn(D[0][1], ' ', X[1]);
      F[2] := 2.5; S[1] := F[2] / 2; WriteLn(F[2]:0:2, ' ', S[1]:0:2);
    end;
    procedure Run;
    var I: Integer; K: TClos; L: TMeth;
    begin
      H := THold.Create(); H.N := 7; GO := TObj.Create(); SetLength(GO.C, 1); SetLength(GO.S, 2);
      for I := 1 to 2 do
      begin
        GO.Run();
        MakeObj().M[0] := GO.M[1]; L := GO.M[0]; L();
        MakeObj().C[0] := nil; K := GO.C[0]; WriteLn(Assigned(K));
        MakeObj().F[0] := I * 1.5; WriteLn(GO.F[0]:0:2);
      end;
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', 'hi 7' + #10 +
    '77' + #10 +
    '5 9' + #10 +
    '2.50 1.25' + #10 +
    'hi 7' + #10 +
    'False' + #10 +
    '1.50' + #10 +
    'hi 7' + #10 +
    '77' + #10 +
    '5 9' + #10 +
    '2.50 1.25' + #10 +
    'hi 7' + #10 +
    'False' + #10 +
    '3.00' + #10 +
    'done');
end;

procedure TE2ELeakCheckTests.TestDebug_ForInForms_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program ForInForms;
    uses SysUtils, Generics.Collections;
    type
      TBig = set of 0..127;
      TClos = reference to function: Integer;
      IFoo = interface function Get: Integer; end;
      THold = class(TObject, IFoo) N: Integer; function Get: Integer; end;
      TSA = array[0..1] of String;
      TDA = array of IFoo;
      TCA = array of TClos;
      TJA = array[0..1] of TBig;
      PSA = ^TSA;
      TRec = record S: TSA; D: TDA; end;
      TObj = class S: TSA; D: TDA; C: TCA; J: TJA; R: TRec; procedure Run; end;
      TPt = record X, Y: Double; end;
      TPtEnum = class I: Integer; function MoveNext: Boolean; function GetCurrent: TPt;
        property Current: TPt read GetCurrent; end;
      TPts = class function GetEnumerator: TPtEnum; end;
      TDEnum = class I: Integer; function MoveNext: Boolean; function GetCurrent: Double;
        property Current: Double read GetCurrent; end;
      TDs = class function GetEnumerator: TDEnum; end;
    var Hold: THold; GO: TObj; PS: PSA; AR: array[0..1] of TRec;
    function THold.Get: Integer; begin Result := N end;
    function TPtEnum.MoveNext: Boolean; begin I := I + 1; Result := I <= 2 end;
    function TPtEnum.GetCurrent: TPt; begin Result.X := I; Result.Y := I * 0.5 end;
    function TPts.GetEnumerator: TPtEnum; begin Result := TPtEnum.Create() end;
    function TDEnum.MoveNext: Boolean; begin I := I + 1; Result := I <= 3 end;
    function TDEnum.GetCurrent: Double; begin Result := I * 1.25 end;
    function TDs.GetEnumerator: TDEnum; begin Result := TDEnum.Create() end;
    function MkD: TDA; begin Result := GO.D end;
    function MkObj: TObj; begin Result := GO end;
    function MkStr(N: Integer): String; begin Result := 'ab' + IntToStr(N) end;
    function MkList: TList<Integer>; begin Result := TList<Integer>.Create(); Result.Add(4); Result.Add(5) end;
    procedure TObj.Run;
    var E: String; F: IFoo; K: TClos; B: TBig; I: Integer;
    begin
      for E in S do Write(E, ' '); for F in D do Write(F.Get(), ' ');
      for K in C do Write(K(), ' '); for B in J do Write(100 in B, ' ');
      for E in Self.R.S do Write(E, ' '); WriteLn();
    end;
    procedure VarS(var A: TSA; var B: TDA);
    var E: String; F: IFoo;
    begin
      for E in A do Write(E, ' '); for F in B do Write(F.Get(), ' '); WriteLn();
    end;
    procedure Cap;
    var A: TSA; F: IFoo;
      procedure Inner; var E: String; begin for E in A do Write(E, ' '); for F in GO.D do Write(F.Get(), ' ') end;
    begin A[0] := 'c'; A[1] := 'd'; Inner(); WriteLn() end;
    procedure Run;
    var E: String; F: IFoo; C, I: Integer; P: TPt; D: Double; Pts: TPts; Ds: TDs; B: TBig;
    begin
      Hold := THold.Create(); Hold.N := 9;
      GO := TObj.Create(); GO.S[0] := 'a'; GO.S[1] := 'b'; SetLength(GO.D, 2); GO.D[0] := Hold; GO.D[1] := Hold;
      SetLength(GO.C, 1); GO.C[0] := function: Integer begin Result := 77 end;
      GO.J[1] := [100]; GO.R.S[0] := 'x'; GO.R.S[1] := 'y'; GO.R.D := GO.D; AR[1] := GO.R; PS := @GO.S;
      GO.Run(); VarS(GO.S, GO.D); Cap();
      for E in PS^ do Write(E, ' '); for E in AR[1].S do Write(E, ' ');
      for F in MkD() do Write(F.Get(), ' '); for F in MkObj().D do Write(F.Get(), ' '); WriteLn();
      for C in MkStr(7) do Write(C, ' '); WriteLn();
      B := [1, 70, 127]; for I in B do Write(I, ' '); WriteLn();
      for I in MkList() do Write(I, ' '); WriteLn();
      Pts := TPts.Create(); for P in Pts do Write(P.X:0:1, ',', P.Y:0:1, ' '); WriteLn();
      Ds := TDs.Create(); for D in Ds do Write(D:0:2, ' '); WriteLn();
      E := ''; for C in E do Write('!'); WriteLn('empty');
      GO.C[0] := nil;
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', 'a b 9 9 77 False True x y ' + #10 +
    'a b 9 9 ' + #10 +
    'c d 9 9 ' + #10 +
    'a b x y 9 9 9 9 ' + #10 +
    '97 98 55 ' + #10 +
    '1 70 127 ' + #10 +
    '4 5 ' + #10 +
    '1.0,0.5 2.0,1.0 ' + #10 +
    '1.25 2.50 3.75 ' + #10 +
    'empty' + #10 +
    'done');
end;

procedure TE2ELeakCheckTests.TestDebug_IntfCallOperands_NoLeak;
begin
  AssertLeakFreeOnAll(
    '''
    program IntfOps;
    type
      IFoo = interface
        function Get: Integer;
        function Me: IFoo;
      end;
      THold = class(TObject, IFoo)
        N: Integer;
        function Get: Integer;
        function Me: IFoo;
      end;
      TObj = class
        FV: IFoo;
        function GetP(I: Integer): IFoo;
        property P[I: Integer]: IFoo read GetP;
      end;
    var G: TObj; L: IFoo;
    function THold.Get: Integer; begin Result := N end;
    function THold.Me: IFoo; begin Result := Self end;
    function TObj.GetP(I: Integer): IFoo; begin Result := FV end;
    function MkObj: TObj; begin Result := G end;
    function MkI: IFoo; begin Result := L end;
    function MkF: IFoo; begin Result := G.FV end;
    procedure Run;
    var H: THold; K: IFoo;
    begin
      H := THold.Create();
      H.N := 7;
      G := TObj.Create();
      G.FV := H;
      L := H;
      WriteLn(MkI() <> nil, ' ', G.GetP(0) = L, ' ', Assigned(G.GetP(1)),
        ' ', L.Me() <> nil, ' ', MkF().Get());
      if G.P[0] = nil then WriteLn('nil');
      K := MkObj().GetP(0);
      Write(K.Get(), ' ');
      K := MkObj().FV;
      Write(K.Get(), ' ');
      K := MkObj().P[2];
      WriteLn(K.Get(), ' ', MkObj().GetP(0).Get(), ' ', MkObj().FV.Get());
      L := nil;
      G := nil
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''', 'True True True True 7' + #10 +
    '7 7 7 7 7' + #10 +
    'done');
end;

procedure TE2ELeakCheckTests.TestDebug_ExprCalleeAggregates_NoLeak;
const
  Src = '''
    program g;
    type
      TPt = record X, Y: Integer; end;
      TBig = record A, B, C: Int64; S: string; end;
      IThing = interface
        function Name(): string;
      end;
      TThing = class(TObject, IThing)
        FN: string;
        constructor Create(const N: string);
        function Name(): string;
      end;
      TBFn = reference to function(A: Integer): TBig;
      TPFn = reference to function(A: Integer): TPt;
      TIFn = reference to function(): IThing;
      TKFn = reference to function(A: Integer): Integer;
      TCFn = reference to function(): TKFn;
    constructor TThing.Create(const N: string); begin FN := N; end;
    function TThing.Name(): string; begin Result := FN; end;
    function GetB(): TBFn; begin Result := function(A: Integer): TBig begin Result.A := A; Result.S := 'B' + IntToStr(A); end; end;
    function GetP(): TPFn; begin Result := function(A: Integer): TPt begin Result.X := A; Result.Y := A * 2; end; end;
    function GetI(): TIFn; begin Result := function(): IThing begin Result := TThing.Create('I'); end; end;
    function GetC(): TCFn; begin Result := function(): TKFn begin Result := function(A: Integer): Integer begin Result := A + 1000; end; end; end;
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
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
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
    '10 eq' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_AggregateScalarContexts_NoLeak;
const
  Src = '''
    program h;
    type
      TPt = record X, Y: Integer; end;
      TBig = record A, B, C: Int64; S: string; end;
      TKFn = reference to function(A: Integer): Integer;
      TMFn = function(A: Integer): Integer of object;
      IThing = interface
        function GetFn(): TKFn;
        function GetB(): TBig;
      end;
      TC = class(TObject, IThing)
        function GetFn(): TKFn;
        function GetM(): TMFn;
        function GetB(): TBig;
        function GetP(): TPt;
        function Dbl(A: Integer): Integer;
        procedure Run();
      end;
      TD = class(TC)
        function GetFn(): TKFn;
        function GetB(): TBig;
        procedure Run2();
      end;
    function MkFn(): TKFn; begin Result := function(A: Integer): Integer begin Result := A + 1; end; end;
    function MkP(A: Integer): TPt; begin Result.X := A; Result.Y := A * 10; end;
    function MkC(): TC; begin Result := TC.Create(); end;
    function TC.GetFn(): TKFn; begin Result := function(A: Integer): Integer begin Result := A * 2; end; end;
    function TC.GetM(): TMFn; begin Result := @Self.Dbl; end;
    function TC.GetB(): TBig; begin Result.S := 'cb'; Result.A := 1; end;
    function TC.GetP(): TPt; begin Result.X := 4; Result.Y := 9; end;
    function TC.Dbl(A: Integer): Integer; begin Result := A * 4; end;
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
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
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
    '11 cb' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_InterfaceGettersStatics_NoLeak;
const
  Src = '''
    program f;
    type
      TPt = record X, Y: Integer; end;
      TBig = record A, B, C: Int64; S: string; end;
      TBFn = reference to function(A: Integer): Integer;
      IThing = interface
        function Name(): string;
        function GetNext(): IThing;
        function GetPos(): TPt;
        function GetBig(): TBig;
        function GetFn(): TBFn;
        property Next: IThing read GetNext;
        property Pos: TPt read GetPos;
        property Big: TBig read GetBig;
        property Fn: TBFn read GetFn;
      end;
      TThing = class(TObject, IThing)
        FN: string;
        constructor Create(const N: string);
        function Name(): string;
        function GetNext(): IThing;
        function GetPos(): TPt;
        function GetBig(): TBig;
        function GetFn(): TBFn;
      end;
      TC = class
      public static var
        SI: IThing;
      public
        T: IThing;
        function GetT(): IThing;
        static function GetST(): IThing;
        function GetFn(): TBFn;
        procedure Run();
        property PT: IThing read GetT;
        property PF: TBFn read GetFn;
        static property ST: IThing read GetST;
      end;
    constructor TThing.Create(const N: string); begin FN := N; end;
    function TThing.Name(): string; begin Result := FN; end;
    function TThing.GetNext(): IThing; begin Result := TThing.Create(FN + '+'); end;
    function TThing.GetPos(): TPt; begin Result.X := Length(FN); Result.Y := 5; end;
    function TThing.GetBig(): TBig; begin Result.C := 77; Result.S := FN + '!'; end;
    function TThing.GetFn(): TBFn; begin Result := function(A: Integer): Integer begin Result := A * 3; end; end;
    function TC.GetT(): IThing; begin Result := T; end;
    static function TC.GetST(): IThing; begin Result := TThing.Create('st'); end;
    function TC.GetFn(): TBFn; begin Result := function(A: Integer): Integer begin Result := A + 100; end; end;
    procedure TC.Run();
    var I: IThing;
    begin
      WriteLn('a ', PT.Name());
      WriteLn('b ', Self.PT.Name());
      I := PT;
      WriteLn('c ', I.Name());
      if PT <> nil then WriteLn('d nonnil');
      WriteLn('e ', GetFn()(1));
    end;
    procedure Show(const I: IThing); begin WriteLn('show ', I.Name()); end;
    var C: TC; I, J: IThing; P: TPt; B: TBig; Fv: TBFn;
    begin
      C := TC.Create();
      C.T := TThing.Create('thing');
      C.Run();
      WriteLn('f ', C.PT.Name());
      I := C.PT;
      WriteLn('g ', I.Name());
      Show(C.PT);
      WriteLn('h ', I.Next.Name());
      J := I.Next;
      WriteLn('i ', J.Next.Next.Name());
      Show(I.Next);
      WriteLn('j ', I.Pos.X, ' ', I.Pos.Y);
      P := I.Pos;
      WriteLn('k ', P.X);
      WriteLn('l ', I.Big.S, ' ', I.Big.C);
      B := I.Big;
      WriteLn('m ', B.S);
      Fv := I.Fn;
      WriteLn('o ', Fv(5));
      Fv := C.PF;
      WriteLn('p ', Fv(5));
      TC.SI := TThing.Create('si');
      WriteLn('q ', TC.SI.Name());
      I := TC.SI;
      WriteLn('r ', I.Name());
      WriteLn('s ', TC.ST.Name());
      I := TC.ST;
      WriteLn('t ', I.Name());
      Show(TC.ST);
      Show(TC.SI);
      if I.Next <> nil then WriteLn('u nonnil');
      WriteLn('v ', I.Next.Next.Name(), ' ', TC.ST.Name());
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    'a thing' + LineEnding +
    'b thing' + LineEnding +
    'c thing' + LineEnding +
    'd nonnil' + LineEnding +
    'e 101' + LineEnding +
    'f thing' + LineEnding +
    'g thing' + LineEnding +
    'show thing' + LineEnding +
    'h thing+' + LineEnding +
    'i thing+++' + LineEnding +
    'show thing+' + LineEnding +
    'j 5 5' + LineEnding +
    'k 5' + LineEnding +
    'l thing! 77' + LineEnding +
    'm thing!' + LineEnding +
    'o 15' + LineEnding +
    'p 105' + LineEnding +
    'q si' + LineEnding +
    'r si' + LineEnding +
    's st' + LineEnding +
    't st' + LineEnding +
    'show st' + LineEnding +
    'show si' + LineEnding +
    'u nonnil' + LineEnding +
    'v st++ st' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_StaticAggregateMembers_NoLeak;
const
  Src = '''
    program k;
    type
      TBig = record A, B, C: Int64; S: string; end;
      TKFn = reference to function(A: Integer): Integer;
      IThing = interface
        function Name(): string;
      end;
      TC = class(TObject, IThing)
      public static var
        SB: TBig;
      public
        FN: string;
        function Name(): string;
        function GetT(): IThing; virtual;
        procedure Touch(); virtual;
        static function GetSB(): TBig;
        static function GetSF(): TKFn;
        static property PSB: TBig read GetSB;
        static property PSF: TKFn read GetSF;
      end;
      TD = class(TC)
        function GetT(): IThing; override;
        procedure Touch(); override;
      end;
    function TC.Name(): string; begin Result := FN; end;
    function TC.GetT(): IThing; var C: TC; begin C := TC.Create(); C.FN := 'base'; Result := C; end;
    procedure TC.Touch(); begin end;
    static function TC.GetSB(): TBig; begin Result.S := 'sb' + IntToStr(1); Result.B := 9; end;
    static function TC.GetSF(): TKFn; begin Result := function(A: Integer): Integer begin Result := A * 7; end; end;
    function TD.GetT(): IThing; begin inherited GetT(); end;
    procedure TD.Touch(); begin inherited GetT(); end;
    procedure Show(const B: TBig); begin WriteLn('show ', B.S, ' ', B.B); end;
    var D: TD; I: IThing; B: TBig; F: TKFn;
    begin
      D := TD.Create();
      I := D.GetT();
      WriteLn('1 ', I.Name());
      WriteLn('2 ', D.GetT().Name());
      D.Touch();
      WriteLn('3 ', TC.PSB.S, ' ', TC.PSB.B);
      B := TC.PSB;
      WriteLn('4 ', B.S);
      Show(TC.PSB);
      F := TC.PSF;
      WriteLn('5 ', F(2), ' ', TC.GetSF()(3));
      TC.SB.S := 'svar';
      WriteLn('6 ', TC.SB.S);
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    '1 base' + LineEnding +
    '2 base' + LineEnding +
    '3 sb1 9' + LineEnding +
    '4 sb1' + LineEnding +
    'show sb1 9' + LineEnding +
    '5 14 21' + LineEnding +
    '6 svar' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_DiscardedResultsEveryKind_NoLeak;
const
  Src = '''
    program j;
    type
      TBig = record A, B, C: Int64; S: string; end;
      TPt = record X, Y: Integer; end;
      TKFn = reference to function(A: Integer): Integer;
      TArr = array of Integer;
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
    function TC.GetFn(): TKFn; begin Result := function(A: Integer): Integer begin Result := A; end; end;
    function TC.GetB(): TBig; begin Result.S := 'x' + IntToStr(2); end;
    function TC.GetP(): TPt; begin Result.X := 1; end;
    static function TC.SGetS(): string; begin Result := 'q' + IntToStr(3); end;
    static function TC.SGetI(): IThing; begin Result := TC.Create(); end;
    static function TC.SGetFn(): TKFn; begin Result := function(A: Integer): Integer begin Result := A; end; end;
    static function TC.SGetB(): TBig; begin Result.S := 'y' + IntToStr(4); end;
    procedure TC.Run();
    begin
      GetS(); GetC(); GetA(); GetI(); GetFn(); GetB(); GetP();
      Inner.GetS(); Inner.GetC(); Inner.GetA(); Inner.GetI(); Inner.GetFn(); Inner.GetB(); Inner.GetP();
    end;
    function MkC(): TC; begin Result := TC.Create(); end;
    function MkFn(): TKFn; begin Result := function(A: Integer): Integer begin Result := A; end; end;
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
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    'done' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_RecordCallAddressBases_NoLeak;
const
  Src = '''
    program P;
    type
      TArr = array[0..3] of Integer;
      TRec = record
        A: TArr; S: string; D: array of Integer;
        function Clone: TRec;
      end;
      TRecFn = reference to function(N: Integer): TRec;
      IMk = interface
        function Mk(N: Integer): TRec;
      end;
      TBase = class(IMk)
      public
        function Mk(N: Integer): TRec; virtual;
      end;
      TObj = class(TBase)
      private
        FR: TRec;
        function GetR: TRec;
        function GetRI(I: Integer): TRec;
        static function GetSR: TRec;
      public
        function Mk(N: Integer): TRec; override;
        procedure Run;
        static function SMk(N: Integer): TRec;
        property R: TRec read GetR;
        property RI[I: Integer]: TRec read GetRI;
        static property SR: TRec read GetSR;
      end;
    function F(N: Integer): TRec;
    var I: Integer;
    begin
      for I := 0 to 3 do Result.A[I] := N + I;
      Result.S := 's' + IntToStr(N);
      SetLength(Result.D, 3); Result.D[1] := N * 10;
    end;
    function TRec.Clone: TRec; begin Result := Self; Result.A[0] := Result.A[0] + 1000; end;
    function TBase.Mk(N: Integer): TRec; begin Result := F(N); end;
    function TObj.Mk(N: Integer): TRec; begin Result := F(N + 1); end;
    function TObj.GetR: TRec; begin Result := F(40); end;
    function TObj.GetRI(I: Integer): TRec; begin Result := F(I); end;
    static function TObj.GetSR: TRec; begin Result := F(50); end;
    static function TObj.SMk(N: Integer): TRec; begin Result := F(N); end;
    function MkFn: TRecFn; begin Result := function(N: Integer): TRec begin Result := F(N * 2); end; end;
    procedure ShowOpen(const A: array of Integer); var X: Integer; begin for X in A do Write(X, ' '); WriteLn(); end;
    procedure TObj.Run; begin WriteLn(Mk(4).A[1], ' ', Mk(4).D[1], ' ', inherited Mk(4).A[2], ' ', Self.Mk(4).A[3]); end;
    var O: TObj; I: IMk; Fn: TRecFn; R: TRec; Pi: ^Integer; X: Integer;
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
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    '2 49 10' + LineEnding +
    '3 50 20' + LineEnding +
    '3 20' + LineEnding +
    '5 52 40' + LineEnding +
    '6 50 6 8' + LineEnding +
    '11 12 100' + LineEnding +
    '41 400 9 53' + LineEnding +
    '1008 9 80' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_ForInThroughCall_NoLeak;
const
  Src = '''
    program P;
    type
      TArr = array[0..3] of Integer;
      TRec = record A: TArr; D: array of Integer; end;
      TObj = class
      public
        Arr: TArr;
        D: array of string;
        function GetR: TRec;
        property R: TRec read GetR;
      end;
    var Calls: Integer; Pool: array of TRec; Keep: TObj;
    function F(N: Integer): TRec;
    begin
      Calls := Calls + 1;
      Result.A[1] := N; SetLength(Result.D, 2); Result.D[1] := N * 10;
    end;
    function TObj.GetR: TRec; begin Result := F(7); end;
    function MkArr: TArr; begin Calls := Calls + 1; Result[3] := 33; end;
    function G: Integer; begin Calls := Calls + 1; Result := 1; end;
    function MkObj: TObj;
    begin
      Calls := Calls + 1;
      Result := TObj.Create(); Result.Arr[2] := 22;
      SetLength(Result.D, 2); Result.D[0] := 'x' + IntToStr(Calls); Result.D[1] := 'y';
    end;
    function GetKeep: TObj; begin Calls := Calls + 1; Result := Keep; end;
    procedure Report(const AWhat: string; ASum: Integer);
    begin
      WriteLn(AWhat, ' sum=', ASum, ' calls=', Calls);
      Calls := 0;
    end;
    var O: TObj; X, Sum: Integer; S, Acc: string;
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
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    'F(3).A sum=3 calls=1' + LineEnding +
    'F(3).D sum=30 calls=1' + LineEnding +
    'O.R.A sum=7 calls=1' + LineEnding +
    'MkArr() sum=33 calls=1' + LineEnding +
    'Pool[G()].A sum=5 calls=1' + LineEnding +
    'abc 0' + LineEnding +
    'GetKeep().D sum=0 calls=1' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_OwnedTransientBase_EveryFieldKind_NoLeak;
const
  Src = '''
    program Owned;
    type
      IGreet = interface function Hi: string; end;
      TG = class(IGreet) function Hi: string; end;
      TColour = (cRed, cGreen, cBlue);
      TArr = array[0..3] of Integer;
      TPt = record X, Y: Integer; S: string; A: TArr; end;
      TObj = class
      public
        F: Double; Sg: Single; I64: Int64; G: IGreet; C: set of TColour; P: TPt;
        N: Integer; S: string; D: array of string; Arr: TArr;
      end;
    function TG.Hi: string; begin Result := 'hi' + IntToStr(1); end;
    function MkObj: TObj;
    begin
      Result := TObj.Create(); Result.F := 2.5; Result.Sg := 1.5; Result.I64 := 40000000000;
      Result.G := TG.Create(); Result.C := [cGreen, cBlue];
      Result.P.X := 7; Result.P.S := 'p' + IntToStr(5); Result.P.A[2] := 9;
      Result.N := 3; Result.S := 's' + IntToStr(2);
      SetLength(Result.D, 2); Result.D[0] := 'a' + IntToStr(1); Result.D[1] := 'b';
      Result.Arr[1] := 77;
    end;
    procedure ShowPt(const P: TPt); begin WriteLn(P.X, ' ', P.S); end;
    var D: Double; P: TPt; S: string; Ds: array of string; X: Integer; Pi: ^Integer;
    begin
      S := MkObj().S; WriteLn(S, ' ', MkObj().S, ' ', MkObj().N);
      Ds := MkObj().D; WriteLn(Length(Ds), ' ', Ds[0], ' ', Length(MkObj().D), ' ', MkObj().D[0]);
      WriteLn(MkObj().F:0:2, ' ', MkObj().Sg:0:2, ' ', MkObj().I64);
      D := MkObj().F + MkObj().F; WriteLn(D:0:2);
      WriteLn(MkObj().G.Hi(), ' ', cBlue in MkObj().C);
      P := MkObj().P; WriteLn(P.X, ' ', P.S);
      ShowPt(MkObj().P);
      WriteLn(MkObj().P.S, ' ', MkObj().P.X, ' ', MkObj().P.A[2]);
      WriteLn(MkObj().Arr[1]);
      MkObj().Arr[2] := 5; MkObj().D[0] := 'x';
      Pi := @MkObj().Arr[1]; WriteLn(Pi <> nil);
      X := MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] + MkObj().Arr[1] +
           MkObj().P.A[2] + MkObj().P.A[2] + MkObj().P.A[2] + MkObj().P.A[2] + MkObj().P.A[2] +
           MkObj().N + MkObj().N;
      WriteLn(X);
      S := MkObj().S + MkObj().D[0] + MkObj().P.S + MkObj().S + MkObj().D[1] + MkObj().P.S +
           MkObj().S + MkObj().D[0] + MkObj().P.S + MkObj().G.Hi();
      WriteLn(S);
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    's2 s2 3' + LineEnding +
    '2 a1 2 a1' + LineEnding +
    '2.50 1.50 40000000000' + LineEnding +
    '5.00' + LineEnding +
    'hi1 True' + LineEnding +
    '7 p5' + LineEnding +
    '7 p5' + LineEnding +
    'p5 7 9' + LineEnding +
    '77' + LineEnding +
    'True' + LineEnding +
    '436' + LineEnding +
    's2a1p5s2bp5s2a1p5hi1' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_CapturedManagedVars_NoLeak;
const
  Src = '''
    program CapMgd;
    type
      IGreet = interface function Hi: string; end;
      TG = class(IGreet) FN: string; constructor Create(const N: string); function Hi: string; end;
    constructor TG.Create(const N: string); begin FN := N; end;
    function TG.Hi: string; begin Result := 'hi ' + FN; end;
    procedure Run;
    var G: IGreet; D: array of Integer; SD: array of string; S, Acc: string; X, Sum: Integer; B: Byte;
        F: reference to procedure;
    begin
      SetLength(D, 2); D[1] := 10; G := TG.Create('a'); S := 'x' + IntToStr(1);
      F := procedure begin WriteLn(Length(D), ' ', D[1], ' ', G.Hi(), ' ', S); end;
      F();
      F := procedure
           begin
             SetLength(D, 3); D[0] := 5; D[2] := 7;
             G := TG.Create('b'); S := S + 'y';
           end;
      F();
      WriteLn(Length(D), ' ', D[0], D[1], D[2], ' ', G.Hi(), ' ', S);
      D[1] := 4; G := nil;
      F := procedure begin WriteLn(D[1], ' ', G = nil); end;
      F();
      SetLength(SD, 2); SD[0] := 'p' + IntToStr(1); SD[1] := 'q';
      Sum := 0; Acc := '';
      F := procedure
           begin
             for X in D do Sum := Sum + X;
             for S in SD do Acc := Acc + S;
             for B in D do Sum := Sum + B;
           end;
      F();
      WriteLn(Sum, ' ', X, ' ', Acc, ' ', S, ' ', B);
    end;
    begin
      Run();
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    '2 10 hi a x1' + LineEnding +
    '3 5107 hi b x1y' + LineEnding +
    '4 True' + LineEnding +
    '32 7 p1q q 7' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_StaticArrayGetterOpenArrayArg_NoLeak;
const
  Src = '''
    program OA2;
    type
      TSArr = array[0..1] of string;
      TObj = class
      private
        function GetS: TSArr;
      public
        property SG: TSArr read GetS;
      end;
    function TObj.GetS: TSArr; begin Result[0] := 'a' + IntToStr(1); Result[1] := 'b' + IntToStr(2); end;
    procedure ShowOpen(const A: array of string); var X: string; begin for X in A do Write(X, ' '); WriteLn(); end;
    var O: TObj;
    begin
      O := TObj.Create();
      ShowOpen(O.SG); ShowOpen(O.GetS());
      O.Free();
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    'a1 b2 ' + LineEnding +
    'a1 b2 ' + LineEnding, Output);
end;

procedure TE2ELeakCheckTests.TestDebug_CtorResultReceiver_AggregateResults_NoLeak;
const
  Src = '''
    program CtorRecv;
    type
      IThing = interface function Name: string; end;
      TThing = class(IThing) function Name: string; end;
      TFn = reference to function(A: Integer): Integer;
      TBig = record A, B, C: Int64; S: string; end;
      TT = class
        function GetI: IThing;
        function GetFn: TFn;
        function GetB: TBig;
        function GetN: Integer;
      end;
    function TThing.Name: string; begin Result := 'thing'; end;
    function TT.GetI: IThing; begin Result := TThing.Create(); end;
    function TT.GetFn: TFn; begin Result := function(A: Integer): Integer begin Result := A * 3; end; end;
    function TT.GetB: TBig; begin Result.S := 'big' + IntToStr(1); Result.C := 7; end;
    function TT.GetN: Integer; begin Result := 3; end;
    var I: IThing; F: TFn; B: TBig;
    begin
      WriteLn(TT.Create().GetI().Name());
      I := TT.Create().GetI(); WriteLn(I.Name());
      WriteLn(TT.Create().GetFn()(4));
      F := TT.Create().GetFn(); WriteLn(F(5));
      WriteLn(TT.Create().GetB().S, ' ', TT.Create().GetB().C);
      B := TT.Create().GetB(); WriteLn(B.S);
      TT.Create().GetB();
      TT.Create().GetI();
      WriteLn(TT.Create().GetN());
    end.
    ''';
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(Src, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout',
    'thing' + LineEnding +
    'thing' + LineEnding +
    '12' + LineEnding +
    '15' + LineEnding +
    'big1 7' + LineEnding +
    'big1' + LineEnding +
    '3' + LineEnding, Output);
end;

initialization
  RegisterTest(TE2ELeakCheckTests);

end.
