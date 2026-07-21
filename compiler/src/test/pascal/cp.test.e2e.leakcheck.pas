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
    procedure TestDebug_NoLeak_NoReport;
    procedure TestDebug_ExceptionHandlerVar_NoLeakNoOverRelease;
    { BUG-20260720-exception-object-leak: a handler with NO bound variable (bare
      except, on-Type-no-var, else branch) left the raised exception orphaned
      (created rc=0, only borrowed, never released) — leaking Exception (rc=0). }
    procedure TestDebug_ExceptionNoVarHandler_NoLeak;
    procedure TestDebug_ConstructorWithArgs_NoDoubleAddRef;
    procedure TestDebug_LeakedObject_ReportedOnExit;
    procedure TestDebug_MultipleLeaks_AllReported;
    procedure TestDebug_CycleRetained_Reported;
    procedure TestRelease_NoReport_WhenDebugOff;
    procedure TestDebug_LeakReport_IncludesUnitAndLine;
    procedure TestDebug_LeakReport_IncludesUnitAndLine_Native;
    procedure TestDebug_StringLeak_Reported;
    procedure TestDebug_StringClean_NoReport;

    { obj.Field := MakeClass() consumes the call's +1 — no leak per store. }
    procedure TestDebug_ClassFieldFromCall_NoLeak;

    { local := MakeClass() consumes the call's +1 — no leak per assignment.
      Pins the native class-assignment AddRef elision against the QBE backend. }
    procedure TestDebug_FuncReturnAssign_NoLeak;
    { MakeClass() called in statement position discards its +1 result — it must
      be released or one object leaks per call.  Both backends. }
    procedure TestDebug_DiscardedClassReturn_NoLeak;
    { X := Call().ClassField must keep the field value valid past the base
      release (QBE use-after-free before the deferred-base-release fix) and not
      leak on QBE.  Correct output (42) is asserted on BOTH backends. }
    procedure TestDebug_CallResultClassFieldRead_NoUseAfterFree;
    { BUG-049: a class-field read off an owned transient in an UNBRACKETED
      statement context (a call argument, an if condition, and — per iteration
      — a loop condition) must still release the transient.  Every statement is
      flush-bracketed, and loop conditions flush per iteration, so none leak. }
    procedure TestDebug_TransientFieldInCallArg_NoLeak;
    procedure TestDebug_TransientFieldInIfCond_NoLeak;
    procedure TestDebug_TransientFieldInWhileCond_NoLeak;
    { A deep chain MakeIt().A.B.N reads a scalar off a base that is itself two
      field-reads off an owned transient.  Each intermediate owned transient's
      release must be deferred to statement end so none leak, while the value
      still survives (no UAF).  Both backends (BUG-003). }
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
    procedure TestDebug_GenericAllocSite_ReportsDefiningUnit;
    procedure TestDebug_GenericAllocSite_ReportsDefiningUnit_Native;
    { An interface-returning call passed directly as an argument — Show(Make())
      — hands the callee an owned (+1) fat pointer it borrows; the caller must
      release it after the call or one instance leaks. }
    procedure TestDebug_IntfCallResultArg_NoLeak;
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
    procedure TestDebug_ValueStrCallResultArg_NoLeak;
    procedure TestDebug_ValueStrCallResultArg_NoLeak_Native;
    { An owned (+1) string temp passed to a BUILT-IN — FileAge(PathOf()),
      Trim(Get()), Length(Make()), StrToInt(Make()), nested
      LowerCase(Trim(Make())) — the built-in emission paths call straight into
      the RTL and historically never released the argument temp (both
      backends).  One string leaked per call; the luhmann directory watcher
      hit this once per note per poll via FileAge(AbsPathOf(Id)). }
    procedure TestDebug_BuiltinOwnedStrArg_NoLeak;
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
    { QBE variant: runtime.mem (inline asm) cannot be compiled by the QBE
      backend, so no arena counting — the tracker-visible rc=1 shapes are
      asserted instead; the rc=0 disposal is pinned by the NATIVE arena
      test (the shape predicate is shared code in blaise.codegen). }
    procedure TestDebug_StrTransientDispose_TrackerClean;
    procedure TestDebug_StrTransientDispose_NoArenaGrowth_Native;
    { A string-returning call/getter used DIRECTLY as a Write/WriteLn argument
      (WriteLn(GetBar)) returns a fresh +1 string that _SysWriteStr only borrows.
      EmitWrite previously never released it, leaking one string per call.  The
      fix releases the owned string transient after the write (both backends). }
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
      --backend argument: 'qbe' or 'native'.  A fresh scratch subdirectory is
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

procedure TE2ELeakCheckTests.TestDebug_GenericAllocSite_ReportsDefiningUnit;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beQBE, SrcGenericAllocSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('enumerator class reported', Pos('TListEnumerator', Output) >= 0);
  AssertTrue('defining unit in report, got: ' + Output,
    Pos(' at Generics.Collections:', Output) >= 0);
  AssertTrue('instantiating program NOT in report, got: ' + Output,
    Pos(' at LeakGen:', Output) < 0);
end;

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

procedure TE2ELeakCheckTests.TestDebug_LeakReport_IncludesUnitAndLine;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beQBE, SrcLeakWithSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('class name', Pos('TBox', Output) >= 0);
  AssertTrue('unit name in report', Pos('LeakSite', Output) >= 0);
  AssertTrue('at separator', Pos(' at ', Output) >= 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcClassFieldFromCall, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '7' + LE, Output);
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcFuncReturnAssign, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '900' + LE, Output);
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcDiscardedClassReturn, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '100' + LE, Output);
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
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
  { The CORRECTNESS guard (both backends): the stored field value must survive
    the base release + allocation churn and still read 42.  QBE printed garbage
    here before the deferred-base-release fix. }
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcCallResultClassFieldRead, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertTrue('field value survives base release, prints 42 (qbe)',
    Pos('42' + LE, Output) >= 0);
  { QBE now releases the deferred base at statement end, so no leak. }
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTransientFieldInCallArg, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTransientFieldInIfCond, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTransientFieldInWhileCond, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertTrue('loop count (qbe)', Pos('5' + LE, Output) >= 0);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  { QBE (BUG-003 ii): the deep chain's intermediate owned transients must be
    deferred-released at statement end — value 7 survives (no UAF) AND no leak. }
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcDeepChainFieldRead, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertTrue('deep-chain value survives, prints 7 (qbe)',
    Pos('7' + LE, Output) >= 0);
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
  { Native now has a statement-scoped deferred-release list too, so the deep
    chain's intermediate owned transients are released (BUG-003 native half). }
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcMultiHandlerVar, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '42' + LE, Output);
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
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

procedure TE2ELeakCheckTests.TestDebug_IntfCallResultArg_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beQBE, SrcIntfCallResultArg, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '42' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcReceiverFieldAccess, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '42' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcStaticArrayOfInterface, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'abc' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcStaticArrayOfClass, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '20' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcStaticArrayOfString, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'val2' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcStaticArrayOfRecord, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'val2' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcStaticArrayOfClassExcExit, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'caught' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcStaticArrayManualFree, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'CLEAN' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcRecordStaticArrayField, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'val2' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcRecordStaticArrayFieldByVal, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'val1' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcClassStaticArrayField, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'val2' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcProgStaticArrayOfClass, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '20' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcProgStaticArrayOfString, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'val2' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcProgStaticArrayOfInterface, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'abc' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcProgStaticArrayOfRecord, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'val2' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcProgStaticArrayManualFree, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'CLEAN' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcProgStaticArrayExcExit, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'caught' + LE, Output);
  AssertTrue('no TObjX leaked (qbe), got: ' + Output, Pos('TObjX', Output) < 0);
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

const
  { Same transient shapes without the runtime.mem arena probe (QBE cannot
    compile inline asm).  The user-call concat operand (rc=1) is
    tracker-visible; a regression there reports leaks. }
  SrcStrTransientDisposeQbe = '''
    program P;
    function MakeStr(I: Integer): string;
    begin
      Result := 'value-' + IntToStr(I);
    end;
    procedure SinkVal(S: string);
    begin
      if Length(S) = 0 then WriteLn('never');
    end;
    var
      I: Integer;
      S: string;
    begin
      for I := 1 to 200 do
      begin
        S := 'x' + IntToStr(I) + 'y';
        S := MakeStr(I) + 'y';
        S := LowerCase(Trim(MakeStr(I)));
        SinkVal('v-' + IntToStr(I));
        if FileExists('/nonexistent/' + IntToStr(I)) then
          WriteLn('never');
      end;
      if Length(S) > 0 then
        WriteLn('done');
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_StrTransientDispose_TrackerClean;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcStrTransientDisposeQbe, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'done' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
end;

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

procedure TE2ELeakCheckTests.TestDebug_BuiltinOwnedStrArg_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcBuiltinOwnedStrArg, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'done' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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

procedure TE2ELeakCheckTests.TestDebug_ValueStrCallResultArg_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcValueStrCallResultArg, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'done' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcWriteLnCallArg, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', 'bcd' + LE + 'bcd' + LE + 'bcd' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  ExitCode := RunUnitFiniDebug('qbe', SrcUnitFiniArrayUnit, '',
    SrcUnitFiniArrayProg, Output);
  AssertEquals('exit 0 (qbe), got: ' + Output, 0, ExitCode);
  AssertTrue('stdout has u1 (qbe), got: ' + Output, Pos('u1', Output) >= 0);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  ExitCode := RunUnitFiniDebug('qbe', SrcUnitFiniScalarUnit, '',
    SrcUnitFiniScalarProg, Output);
  AssertEquals('exit 0 (qbe), got: ' + Output, 0, ExitCode);
  AssertTrue('stdout has scalar (qbe), got: ' + Output,
    Pos('scalar', Output) >= 0);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  ExitCode := RunUnitFiniDebug('qbe', SrcUnitFiniClassUnit, '',
    SrcUnitFiniClassProg, Output);
  AssertEquals('exit 0 (qbe), got: ' + Output, 0, ExitCode);
  { The destructor firing at teardown is the proof the release actually ran. }
  AssertTrue('destructor ran at exit (qbe), got: ' + Output,
    Pos('down thing', Output) >= 0);
  AssertTrue('run before down (qbe), got: ' + Output,
    Pos('run', Output) < Pos('down thing', Output));
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  ExitCode := RunUnitFiniDebug('qbe', SrcUnitFiniImplUnit, '',
    SrcUnitFiniImplProg, Output);
  AssertEquals('exit 0 (qbe), got: ' + Output, 0, ExitCode);
  AssertTrue('stdout has xxx (qbe), got: ' + Output, Pos('xxx', Output) >= 0);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  ExitCode := RunUnitFiniDebug('qbe', SrcUnitFiniOrderUnitX,
    SrcUnitFiniOrderUnitY, SrcUnitFiniOrderProg, Output);
  AssertEquals('exit 0 (qbe), got: ' + Output, 0, ExitCode);
  AssertTrue('Y destroyed (qbe), got: ' + Output, Pos('down Y', Output) >= 0);
  AssertTrue('X destroyed (qbe), got: ' + Output, Pos('down X', Output) >= 0);
  { Reverse init order: UFinY initialised last, so it finalises first. }
  AssertTrue('Y down before X down (qbe), got: ' + Output,
    Pos('down Y', Output) < Pos('down X', Output));
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  ExitCode := RunUnitFiniDebug('qbe', SrcUnitFiniFinalUnit, '',
    SrcUnitFiniFinalProg, Output);
  AssertEquals('exit 0 (qbe), got: ' + Output, 0, ExitCode);
  { The finalization block runs at exit and can still read the unit global —
    its ARC release happens only AFTER the user code. }
  AssertTrue('finalization ran and saw the global (qbe), got: ' + Output,
    Pos('final sees fin-live', Output) >= 0);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
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
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, Src, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)',
    'cat ab' + LE + 'make m' + LE + 'alias-arg abbb' + LE +
    'alias-recv mbbb' + LE, Output);
  AssertTrue('no leak report (qbe), got: ' + Output, Pos('leak', Output) < 0);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, Src, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)',
    'cat ab' + LE + 'make m' + LE + 'alias-arg abbb' + LE +
    'alias-recv mbbb' + LE, Output);
  AssertTrue('no leak report (native), got: ' + Output, Pos('leak', Output) < 0);
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

initialization
  RegisterTest(TE2ELeakCheckTests);

end.
