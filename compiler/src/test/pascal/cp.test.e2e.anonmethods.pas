{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.anonmethods;

{ E2E tests for anonymous-method capture (Phase 2 of
  docs/anonymous-methods-design.adoc): compile -> run on every backend
  (QBE + native), asserting stdout/exit code.  Covers the behaviour the
  IR-level tests in cp.test.anonmethods.pas cannot see: shared-environment
  mutation, escape past the creating frame, the by-reference loop-capture
  semantics, captured-parameter snapshots, and exception flow through a
  closure body. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EAnonMethodTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Captured dyn-array, interface and string variables are shared with the
      declaring routine in both directions, and a for-in inside a closure may use
      the enclosing routine's variables as its loop variable.  x86-64 sent an
      interface assignment and a dyn-array element store in the DECLARING routine
      to its idle frame slot (G.Hi() then dispatched on the env's nil: a crash);
      arm64 refused the captured loop variable ("store to variable 'X'"). }
    procedure TestRun_CapturedManagedVars_SharedWithDeclaringRoutine;
    { a [Weak] local (class or interface) captured by a closure or a nested
      routine stays weak: assigned in the body, in the declaring routine,
      and after the declaring routine has returned }
    procedure TestRun_CapturedWeakLocals_StayWeak;
    { A local RECORD captured by a closure is one variable, shared by the closure
      and the routine that declares it: each sees the other's field writes (plain,
      nested, array-field, string) and a whole-record assignment.  On arm64 the
      declaring routine read and wrote its own idle frame slot instead of the
      closure env, so the closure saw zeros and its writes were lost. }
    procedure TestRun_CapturedLocalRecord_SharedWithDeclaringRoutine;
    procedure TestRun_ClosureResult_FieldStoreAndImmediateCall;
    procedure TestRun_NestedSelfCapture_AndGenericClosurePerInstance;
    { moved from cp.test.anonmethods, where they ran through a private
      GenIR -> qbe -> link pipeline (QBE only) }
    procedure TestRun_CaptureFreeLiteral_AssignAndCall;
    procedure TestRun_FunctionLiteral_ReturnsValue;
    procedure TestRun_AdapterFromPlainRoutine;
    procedure TestRun_NilClosure_Assignable;
    procedure TestRun_Arrow_ExprBody_MultiParam_Captures;
    procedure TestRun_Arrow_SingleIdent_ProcedureTarget;
    procedure TestRun_Arrow_BlockBody;
    procedure TestRun_Arrow_MinusGreaterStaysDistinct;
    procedure TestRun_Arrow_ArgPosition_Standalone;
    procedure TestRun_Arrow_ArgPosition_MethodWithCapture;
    procedure TestRun_Arrow_ArgPosition_OverloadByShape;
    procedure TestRun_Arrow_ArgPosition_ProcTypeCalls;
    procedure TestRun_GenericMethodOnGenericClass_Gate;
    procedure TestRun_CaptureLocal_ReadInClosure;
    procedure TestRun_ClosureWrite_VisibleInEnclosing;
    procedure TestRun_TwoClosures_ShareOneEnv;
    procedure TestRun_Escape_GlobalClosure_OutlivesFrame;
    procedure TestRun_FunctionReturnsClosure_IndependentEnvs;
    procedure TestRun_LoopCapture_SharesEnv_ByReference;
    procedure TestRun_CapturedParam_InitialValueCopied;
    procedure TestRun_FunctionLiteral_CapturesAccumulator;
    procedure TestRun_CapturedString_Concat;
    procedure TestRun_RaiseThroughFinally_InClosureBody;
    { Phase 3 }
    procedure TestRun_MethodLiteral_CapturesLocalAndSelf;
    procedure TestRun_MethodLiteral_ExplicitSelfCall;
    procedure TestRun_MethodLiteral_EscapesMethodFrame;
    procedure TestRun_MethodPtrCoercion_DispatchesWithReceiver;
    procedure TestRun_MethodPtrCoercion_VirtualDispatch;
    { Phase 4 — block-scoped var + per-iteration capture }
    procedure TestRun_BlockVar_BasicScopeAndInit;
    procedure TestRun_BlockVar_InitRunsPerIteration;
    procedure TestRun_BlockVar_LoopSnapshotIdiom_012;
    procedure TestRun_LoopCapture_RoutineVar_Still333;
    { Phase 5 }
    procedure TestRun_WeakSelf_ReadsNilAfterReceiverDies;
    procedure TestRun_WeakSelf_WorksWhileReceiverAlive;
    { Regression: a routine RETURNING a 'reference to' value must use the
      16-byte (Code, Env) aggregate-return ABI.  AggRetRec classified
      'of object' but not 'reference to', so the QBE definition returned a
      plain 'l' while call sites read rax:rdx — the env half was garbage and
      the assignment crashed in _ClassAddRef. }
    procedure TestRun_MethodReturnsClosure_FatReturnABI;
    { BUG-008 follow-up: nested routines inside METHOD bodies — the
      self-contained and captured-local forms must compile AND run on both
      backends (they previously miscompiled on v0.12.0 and segfaulted the
      native codegen afterwards). }
    procedure TestRun_NestedRoutineInMethod_CapturesLocal;
    { BUG-008 remaining gap: Self inside a nested routine of a method —
      captured and threaded as a hidden by-pointer param like other outer
      vars.  Covers explicit Self.Field/Self.Method(), implicit member
      access, field writes, and record methods. }
    procedure TestRun_NestedRoutineInMethod_ExplicitSelf;
    procedure TestRun_NestedRoutineInMethod_ImplicitSelf;
    procedure TestRun_NestedRoutineInMethod_SelfInRecordMethod;
    procedure TestRun_NestedRoutineInMethod_SelfVirtualDispatch;
    procedure TestRun_NestedRoutineInMethod_InheritedCall;
    procedure TestRun_NestedRoutineInMethod_ExprCallCapture;
    procedure TestRun_NestedRoutineInMethod_BlockVarInitFromSelf;
    { Phase 6 — generics: reference-to aliases + closures in generic bodies }
    procedure TestRun_GenericRefAlias_ClosureAtInteger;
    procedure TestRun_GenericRefAlias_ClosureAtString;
    procedure TestRun_GenericBody_CapturesTTypedLocal;
    { arm64 leg 38a: a capture-free closure literal passed by value to a
      function that invokes it — the minimal closure param/arg/call shape. }
    procedure TestRun_CaptureFreeClosure_PassedAndCalled;
    { arm64 leg 38b(i): a closure call whose argument is an owned-transient
      string (a function result) — passed borrowed, disposed after the call. }
    procedure TestRun_Closure_OwnedTransientStringArg;
    { arm64 leg 38b(ii): a statement-position closure call (result discarded). }
    procedure TestRun_Closure_StatementPositionCall;
    { BUG-20260722-closure-record-field-direct-call: calling a closure
      stored in a RECORD field directly (R.F()) segfaulted on both
      backends.  Every record-receiver arm of the proc-field call path was
      gated on MDecl.IsRecordMethod, but a proc-field call has no method
      (ResolvedMethod is nil by design), so control fell through to the
      CLASS arm, which loaded the record's first 8 bytes as an instance
      POINTER and dispatched through it.  The workaround form
      (G := R.F; G()) always worked, which is the tell. }
    procedure TestRun_ClosureInRecordField_DirectCall;
    procedure TestRun_ClosureInRecordField_NonZeroOffset;
    procedure TestRun_ClosureInRecordField_WithArgs;
    procedure TestRun_ClosureInRecordField_VarParamReceiver;
    procedure TestRun_ClosureInRecordField_LocalRecord;
    procedure TestRun_ClosureInRecordField_NestedRecord;
    { BUG-20260922-record-closure-field-not-managed: a record whose only
      managed member is a 'reference to' field was reported "managed clean",
      so a whole-record copy shared the env with NO retain and the scope-exit
      walk was elided.  On QBE the copy was a use-after-free (segfault on the
      second invocation); on native the env simply leaked.  The leak tracker
      cannot see closure envs, so this asserts on observable behaviour: the
      env must stay alive through both copies to program exit. }
    procedure TestRun_RecordCopy_ClosureField_EnvSurvivesCopy;
    { BUG-20260923-closure-call-via-byval-record-param: a BY-VALUE record
      parameter is passed BY REFERENCE, so its slot holds the caller's record
      address.  The method-call STATEMENT sites in uSemantic used the narrow
      skVarParameter test, so the call path used the SLOT address as the
      record base: a closure call through such a param segfaulted, and a
      record METHOD call silently read adjacent stack memory and printed
      garbage with exit code 0. }
    procedure TestRun_ByValRecordParam_ClosureFieldCall;
    procedure TestRun_ByValRecordParam_RecordMethodCall;
    { BUG-20260923-qbe-implicit-self-ref-field-call: an UNQUALIFIED call to a
      'reference to' field inside a method (FRun(1)) did not pass the
      closure's env as the hidden first argument on QBE, so every real
      argument landed one slot early: an Integer printed garbage (exit 0), a
      closure argument segfaulted.  Self.FRun(1) and 'of object' fields were
      fine; native was fine. }
    procedure TestRun_ImplicitSelfRefField_Call;
    { Native x86-64: a call through a method-pointer or closure VARIABLE had
      its own integer-only argument loop -- a var param received the value
      instead of its address (segfault) and a Double went through an integer
      register (codegen error).  It now shares EmitCallIndirect's marshalling
      (found with BUG-20260923-addr-of-openarray-proc). }
    procedure TestRun_MethodPtrClosureVar_VarAndDoubleArgs;
    { a closure held in an array element, a record field, a class field or
      behind a pointer, passed on as a by-value closure argument: the
      callee's 16-byte copy read through the loaded first WORD, a crash on
      both ISAs (P4-8) }
    procedure TestRun_ClosureArg_FromElementFieldAndDeref;
    { a closure RETURNED by a call, passed straight on (Use(MakeFn()),
      Use(Obj.Mk()), mixed with float args): x86-64 passed the Code word as
      the pair's address (exit 255); arm64 refused the form }
    procedure TestRun_ClosureCallResult_AsArgument;
    { capturing a parameter wider than a word -- closure, static array
      (by value and const), jumbo set, record (by value and const),
      interface, Single, Double, plain procedural.  x86-64 copied one word
      (an interface closure dispatched through a nil itab; a captured
      closure param was 'Undeclared function'); arm64 refused them all }
    procedure TestRun_Capture_WideParameters;
    { closure stores into a var param and into a captured variable
      (F := MakeFn() inside a closure, F() outside it) }
    procedure TestRun_ClosureStore_VarParamAndCapturedTargets;
    { F := MakeFn() over a live closure releases the old Env -- x86-64
      zeroed it first, leaking its captures, and F := Wrap(F) passed Wrap
      a nil F (exit 139) }
    procedure TestRun_ClosureReassignFromCall_ReleasesOldEnv;
    { P^ := V through a ^closure (call, var, literal, self, nil) and calls
      through an element / dereference / temporary receiver in expression
      position (BUG-20261013-closure-pointer-write,
      BUG-20261013-call-through-element-expr) }
    procedure TestRun_ClosurePointerWrite_AndExprCallForms;
    { block-scoped interface / closure / managed-record variables in a
      loop: each execution releases the previous value (x86-64 leaked all
      but the last; arm64 refused the declaration) }
    procedure TestRun_BlockVar_ManagedAggregatesPerIteration;
    { A[I](args); and P^(args); as statements, over a bare procedural type,
      a 'reference to' and a method pointer; a discarded string result is
      released (BUG-20261012-call-element-statement) }
    procedure TestRun_ExprCallStmt_ElementAndDeref;
    { Cap.Free() inside a closure, Cap a captured local: the slot is freed and
      nilled through the _cap_ pointer (arm64 refused the shape: "load of
      variable 'Cap'") }
    procedure TestRun_FreeOfCapturedVariable;
    { a captured closure variable returning Double or Single, called from a
      nested routine and from an anonymous method, in float contexts --
      arm64 refused it ("float-returning call through a captured closure
      variable") }
    procedure TestRun_CapturedClosure_FloatResult;
    { a literal nested in another one that captures nothing, and a literal
      inside a static method (no Self) -- both were rejected at compile time }
    procedure TestRun_NestedNonCapturingLiteral;
    procedure TestRun_LiteralInStaticMethod;
    { a call through the procedural value a call returns, as a statement:
      GetFn()(X); and GetMaker()(X).Show(); }
    procedure TestRun_ExprCallStmt_CallResultCallee;
  end;

implementation

procedure TE2EAnonMethodTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-anonmethods')
end;

procedure TE2EAnonMethodTests.TestRun_CaptureLocal_ReadInClosure;
const Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  procedure Run;
  var
    Outer: Integer;
    V: TProc;
  begin
    Outer := 41;
    V := procedure
    begin
      WriteLn(Outer + 1)
    end;
    V()
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureWrite_VisibleInEnclosing;
const Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  procedure Run;
  var
    Total: Integer;
    V: TProc;
  begin
    Total := 10;
    V := procedure
    begin
      Total := Total + 32
    end;
    V();
    WriteLn(Total)
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_TwoClosures_ShareOneEnv;
const
  { Both literals in one frame capture the same 'Total' — by-reference
    semantics require ONE shared environment, so the second closure sees
    the first one's write. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  procedure Run;
  var
    Total: Integer;
    Inc10: TProc;
    Show: TProc;
  begin
    Total := 32;
    Inc10 := procedure
    begin
      Total := Total + 10
    end;
    Show := procedure
    begin
      WriteLn(Total)
    end;
    Inc10();
    Show()
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Escape_GlobalClosure_OutlivesFrame;
const
  { The closure is stored in a global and invoked AFTER Make has returned:
    the captured local must live on in the heap env, not the dead frame. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  var
    G: TProc;
  procedure Make;
  var
    Secret: Integer;
  begin
    Secret := 42;
    G := procedure
    begin
      WriteLn(Secret)
    end
  end;
  begin
    Make();
    G()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_FunctionReturnsClosure_IndependentEnvs;
const
  { A plain function returning a capturing closure: each call builds its own
    env, so two adders/counters must not share state.  Also a closure passed
    in and returned unchanged, and a DISCARDED closure-returning call, which
    still needs its result buffer and must drop the env it was handed.  On
    arm64 the result travels through the caller's x8 buffer. }
  Src =
  '''
  program P;
  type
    TIntFn = reference to function(A: Integer): Integer;
    TProc0 = reference to procedure;
  function MakeAdder(N: Integer): TIntFn;
  begin
    Result := function(A: Integer): Integer begin Result := A + N end
  end;
  function Counter(Start: Integer; const Tag: string): TProc0;
  var C: Integer;
  begin
    C := Start;
    Result := procedure begin C := C + 1; WriteLn(Tag, C) end
  end;
  function Pass(F: TIntFn): TIntFn;
  begin
    Result := F
  end;
  var Add3, Add10, G: TIntFn; A, B: TProc0;
  begin
    Add3 := MakeAdder(3);
    Add10 := MakeAdder(10);
    WriteLn(Add3(4), ' ', Add10(4));
    A := Counter(5, 'a='); B := Counter(100, 'b=');
    A(); A(); B();
    G := Pass(Add3);
    WriteLn(G(1));
    MakeAdder(99);
    Add3 := Add10;
    WriteLn(Add3(1))
  end.
  ''';
  Expected = '7 14' + LineEnding + 'a=6' + LineEnding + 'a=7' + LineEnding +
    'b=101' + LineEnding + '4' + LineEnding + '11' + LineEnding;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, Expected, 0);
  AssertLeakFreeOnAll(Src, 'b=101');
end;

procedure TE2EAnonMethodTests.TestRun_LoopCapture_SharesEnv_ByReference;
const
  { The documented Delphi-compatible trap: one env per FRAME, so all three
    closures share the same 'I' and print its post-loop value 3.  Phase 4
    (block-scoped environments) adds the fresh-binding idiom. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  procedure Run;
  var
    A: TProc;
    B: TProc;
    C: TProc;
    I: Integer;
  begin
    for I := 0 to 2 do
    begin
      if I = 0 then A := procedure begin WriteLn(I) end;
      if I = 1 then B := procedure begin WriteLn(I) end;
      if I = 2 then C := procedure begin WriteLn(I) end
    end;
    A();
    B();
    C()
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '3' + LineEnding + '3' + LineEnding + '3' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_CapturedParam_InitialValueCopied;
const
  { A captured VALUE parameter: its incoming value must be copied into the
    env field at frame entry before any closure runs. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  procedure Run(Base: Integer);
  var
    V: TProc;
  begin
    V := procedure
    begin
      Base := Base + 2;
      WriteLn(Base)
    end;
    V()
  end;
  begin
    Run(40)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_FunctionLiteral_CapturesAccumulator;
const Src =
  '''
  program P;
  type
    TStep = reference to function(AInc: Integer): Integer;
  procedure Run;
  var
    Acc: Integer;
    Step: TStep;
  begin
    Acc := 0;
    Step := function(AInc: Integer): Integer
    begin
      Acc := Acc + AInc;
      Result := Acc
    end;
    WriteLn(Step(20));
    WriteLn(Step(22))
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '20' + LineEnding + '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_CapturedString_Concat;
const
  { A captured ARC-managed string: env field must go through the string
    retain/release store path, and the env cleanup must release it. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  procedure Run;
  var
    Prefix: string;
    V: TProc;
  begin
    Prefix := 'item-';
    V := procedure
    begin
      Prefix := Prefix + '42';
      WriteLn(Prefix)
    end;
    V()
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'item-42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_RaiseThroughFinally_InClosureBody;
const
  { A raise inside the closure body must run the body's finally block and
    propagate to the invoker's except handler (design doc, Closures and
    exceptions). }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    Exception = class
    private
      FMessage: string;
    public
      constructor Create(AMsg: string);
      property Message: string read FMessage;
    end;
  constructor Exception.Create(AMsg: string);
  begin
    FMessage := AMsg;
  end;
  procedure Run;
  var
    Flag: Integer;
    V: TProc;
  begin
    Flag := 0;
    V := procedure
    begin
      try
        raise Exception.Create('boom')
      finally
        Flag := Flag + 1
      end
    end;
    try
      V()
    except
      on E: Exception do WriteLn('caught ', E.Message)
    end;
    WriteLn(Flag)
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'caught boom' + LineEnding + '1' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_MethodLiteral_CapturesLocalAndSelf;
const
  { A literal inside an instance method: implicit member access (FCount)
    goes through the captured Self; the method local Step is env-promoted. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    TCounter = class
      FCount: Integer;
      procedure Bump;
    end;
  procedure TCounter.Bump;
  var
    Step: Integer;
    V: TProc;
  begin
    Step := 40;
    V := procedure
    begin
      FCount := FCount + Step + 2
    end;
    V()
  end;
  var C: TCounter;
  begin
    C := TCounter.Create();
    C.Bump();
    WriteLn(C.FCount)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_MethodLiteral_ExplicitSelfCall;
const
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    TGreeter = class
      FName: string;
      procedure Say;
      procedure Run;
    end;
  procedure TGreeter.Say;
  begin
    WriteLn('hello ', FName)
  end;
  procedure TGreeter.Run;
  var
    V: TProc;
  begin
    V := procedure
    begin
      Self.Say()
    end;
    V()
  end;
  var G: TGreeter;
  begin
    G := TGreeter.Create();
    G.FName := 'world';
    G.Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'hello world' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_MethodLiteral_EscapesMethodFrame;
const
  { The closure escapes the method frame via a global; the env's strong Self
    reference keeps the receiver alive and members readable after Wire
    returned. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    TBox = class
      FValue: Integer;
      procedure Wire;
    end;
  var
    G: TProc;
  procedure TBox.Wire;
  begin
    G := procedure
    begin
      WriteLn(FValue)
    end
  end;
  var B: TBox;
  begin
    B := TBox.Create();
    B.FValue := 42;
    B.Wire();
    G()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_MethodPtrCoercion_DispatchesWithReceiver;
const
  Src =
  '''
  program P;
  type
    TShow = reference to procedure(AValue: Integer);
    TScaler = class
      FFactor: Integer;
      procedure Show(AValue: Integer);
    end;
  procedure TScaler.Show(AValue: Integer);
  begin
    WriteLn(AValue * FFactor)
  end;
  var
    S: TScaler;
    V: TShow;
  begin
    S := TScaler.Create();
    S.FFactor := 2;
    V := @S.Show;
    V(21)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_MethodPtrCoercion_VirtualDispatch;
const
  { @Obj.M on a virtual method must capture the DYNAMIC override, matching a
    direct Obj.M() call (same rule as method-pointer assignment). }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    TBase = class
      procedure Speak; virtual;
    end;
    TLoud = class(TBase)
      procedure Speak; override;
    end;
  procedure TBase.Speak;
  begin
    WriteLn('base')
  end;
  procedure TLoud.Speak;
  begin
    WriteLn('LOUD')
  end;
  var
    B: TBase;
    V: TProc;
  begin
    B := TLoud.Create();
    V := @B.Speak;
    V()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'LOUD' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_BlockVar_BasicScopeAndInit;
const
  Src =
  '''
  program P;
  procedure Run;
  begin
    begin
      var X: Integer := 40;
      X := X + 2;
      WriteLn(X)
    end
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_BlockVar_InitRunsPerIteration;
const
  { The declaration statement re-initialises on every execution — each
    iteration starts from 10, so the accumulating += prints 11 three times. }
  Src =
  '''
  program P;
  procedure Run;
  var
    I: Integer;
  begin
    for I := 0 to 2 do
    begin
      var Acc: Integer := 10;
      Acc := Acc + 1;
      WriteLn(Acc)
    end
  end;
  begin
    Run()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '11' + LineEnding + '11' + LineEnding + '11' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_BlockVar_LoopSnapshotIdiom_012;
const
  { THE Phase-4 headline (design doc, Capture): a block-scoped var inside
    the loop body is a fresh binding per iteration — each closure gets its
    own environment, so the stored closures print 0, 1, 2. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  var
    A: TProc;
    B: TProc;
    C: TProc;
  procedure Run;
  var
    I: Integer;
  begin
    for I := 0 to 2 do
    begin
      var Snapshot: Integer := I;
      if I = 0 then A := procedure begin WriteLn(Snapshot) end;
      if I = 1 then B := procedure begin WriteLn(Snapshot) end;
      if I = 2 then C := procedure begin WriteLn(Snapshot) end
    end
  end;
  begin
    Run();
    A();
    B();
    C()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '0' + LineEnding + '1' + LineEnding + '2' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_LoopCapture_RoutineVar_Still333;
const
  { Capturing the ROUTINE-level loop variable still shares one env — the
    documented Delphi-compatible behaviour is unchanged by Phase 4. }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
  var
    A: TProc;
    B: TProc;
  procedure Run;
  var
    I: Integer;
  begin
    for I := 0 to 2 do
    begin
      if I = 0 then A := procedure begin WriteLn(I) end;
      if I = 1 then B := procedure begin WriteLn(I) end
    end
  end;
  begin
    Run();
    A();
    B()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '3' + LineEnding + '3' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_WeakSelf_ReadsNilAfterReceiverDies;
const
  { [Weak Self]: the env's Self slot is registered in the weak table and
    auto-nil'd when the receiver dies — the closure observes nil instead of
    a dangling pointer (same contract as a [Weak] field). }
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    TBox = class
      FValue: Integer;
      procedure Wire;
    end;
  var
    G: TProc;
  procedure TBox.Wire;
  begin
    G := procedure [Weak Self]
    begin
      if Self = nil then
        WriteLn('gone')
      else
        WriteLn(FValue)
    end
  end;
  procedure Run;
  var
    B: TBox;
  begin
    B := TBox.Create();
    B.FValue := 42;
    B.Wire();
    G()
  end;
  begin
    Run();
    G()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding + 'gone' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_WeakSelf_WorksWhileReceiverAlive;
const
  Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    TCounter = class
      FCount: Integer;
      procedure Wire;
    end;
  var
    G: TProc;
    C: TCounter;
  procedure TCounter.Wire;
  begin
    G := procedure [Weak Self]
    begin
      FCount := FCount + 21;
      WriteLn(FCount)
    end
  end;
  begin
    C := TCounter.Create();
    C.Wire();
    G();
    G()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '21' + LineEnding + '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_CapturesLocal;
const Src =
  '''
  program P;
  type
    TC = class
      procedure M();
    end;
  procedure TC.M();
  var X: Integer;
    procedure Inner(K: Integer);
    begin
      WriteLn(X + K)
    end;
  begin
    X := 40;
    Inner(2)
  end;
  var C: TC;
  begin
    C := TC.Create();
    C.M()
  end.
  ''';
begin
  AssertRunsOnAll(Src, '42' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_ExplicitSelf;
const Src =
  '''
  program P;
  type
    TC = class
      FVal: Integer;
      procedure Bump();
      procedure M();
    end;
  procedure TC.Bump();
  begin
    FVal := FVal + 1
  end;
  procedure TC.M();
    procedure Inner();
    begin
      Self.FVal := Self.FVal + 10;
      Self.Bump()
    end;
  begin
    Inner();
    Inner();
    WriteLn(FVal)
  end;
  var C: TC;
  begin
    C := TC.Create();
    C.FVal := 5;
    C.M()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '27' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_ImplicitSelf;
const Src =
  '''
  program P;
  type
    TC = class
      FVal: Integer;
      FName: string;
      function Suffix(): string;
      procedure M();
    end;
  function TC.Suffix(): string;
  begin
    Result := '!'
  end;
  procedure TC.M();
  var K: Integer;
    procedure Inner();
    begin
      FVal := FVal + K;
      FName := FName + Suffix()
    end;
  begin
    K := 3;
    Inner();
    Inner();
    WriteLn(FName, FVal)
  end;
  var C: TC;
  begin
    C := TC.Create();
    C.FVal := 1;
    C.FName := 'ok';
    C.M()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'ok!!7' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_SelfInRecordMethod;
const Src =
  '''
  program P;
  type
    TR = record
      X: Integer;
      procedure M();
    end;
  procedure TR.M();
    procedure Inner();
    begin
      Self.X := Self.X + 20;
      X := X + 1
    end;
  begin
    Inner();
    WriteLn(X)
  end;
  var R: TR;
  begin
    R.X := 4;
    R.M();
    WriteLn(R.X)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '25' + LineEnding + '25' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_SelfVirtualDispatch;
const Src =
  '''
  program P;
  type
    TBase = class
      function Tag(): string; virtual;
      procedure M();
    end;
    TSub = class(TBase)
      function Tag(): string; override;
    end;
  function TBase.Tag(): string;
  begin
    Result := 'base'
  end;
  function TSub.Tag(): string;
  begin
    Result := 'sub'
  end;
  procedure TBase.M();
    procedure Inner();
    begin
      WriteLn(Self.Tag())
    end;
  begin
    Inner()
  end;
  var B: TBase;
  begin
    B := TSub.Create();
    B.M()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'sub' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_InheritedCall;
const Src =
  '''
  program P;
  type
    TBase = class
      FVal: Integer;
      function Tag(): string; virtual;
      procedure Bump();
    end;
    TSub = class(TBase)
      function Tag(): string; override;
      procedure M();
    end;
  function TBase.Tag(): string;
  begin
    Result := 'base' + IntToStr(FVal)
  end;
  procedure TBase.Bump();
  begin
    FVal := FVal + 1
  end;
  function TSub.Tag(): string;
  begin
    Result := 'sub'
  end;
  procedure TSub.M();
    procedure Inner();
    begin
      inherited Bump();
      WriteLn(inherited Tag())
    end;
  begin
    Inner()
  end;
  var S: TSub;
  begin
    S := TSub.Create();
    S.FVal := 4;
    S.M()
  end.
  ''';
begin
  { 'inherited' inside a nested routine dispatches on the captured Self —
    the capture walker must register it (statement AND expression forms). }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'base5' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_ExprCallCapture;
const Src =
  '''
  program P;
  type
    TC = class
      FVal: Integer;
      procedure M();
    end;
  procedure TC.M();
  var X: Integer;
    function GetVal(): Integer;
    var I: Integer;
    begin
      Result := 0;
      I := 0;
      while I < 2 do
      begin
        Result := Result + Self.FVal;
        I := I + 1
      end
    end;
  begin
    X := GetVal() + 2;
    WriteLn(X)
  end;
  var C: TC;
  begin
    C := TC.Create();
    C.FVal := 20;
    C.M()
  end.
  ''';
begin
  { Expression-position call to a NON-INLINABLE (loop body) nested function
    that captures Self — the QBE TFuncCallExpr path must prepend the hidden
    capture args just like statement calls do. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_NestedRoutineInMethod_BlockVarInitFromSelf;
const Src =
  '''
  program P;
  type
    TC = class
      FVal: Integer;
      procedure M();
    end;
  procedure TC.M();
    procedure Inner();
    begin
      var K: Integer := Self.FVal + 1;
      WriteLn(K)
    end;
  begin
    Inner()
  end;
  var C: TC;
  begin
    C := TC.Create();
    C.FVal := 8;
    C.M()
  end.
  ''';
begin
  { Block-scoped 'var K := <expr referencing Self>' inside a nested routine:
    the capture walker must descend the synthesised initialiser assignment. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '9' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_MethodReturnsClosure_FatReturnABI;
const Src =
  '''
  program P;
  type
    TGetter = reference to function(): string;
    TBox = class
      FVal: string;
      function Make(): TGetter;
      begin
        Result := function(): string
          begin
            Result := FVal
          end;
      end;
    end;
  var
    B: TBox;
    G: TGetter;
  begin
    B := TBox.Create();
    B.FVal := 'x' + 'y';
    G := B.Make();
    B := nil;
    WriteLn(G())
  end.
  ''';
begin
  AssertRunsOnAll(Src, 'xy' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_GenericRefAlias_ClosureAtInteger;
const Src =
  '''
  program P;
  type
    TGetter<T> = reference to function(): T;
    TBox<T> = class
      FVal: T;
      function Make(): TGetter<T>;
      begin
        Result := function(): T
          begin
            Result := FVal
          end;
      end;
    end;
  var
    B: TBox<Integer>;
    G: TGetter<Integer>;
  begin
    B := TBox<Integer>.Create();
    B.FVal := 41;
    G := B.Make();
    WriteLn(G() + 1)
  end.
  ''';
begin
  AssertRunsOnAll(Src, '42' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_GenericRefAlias_ClosureAtString;
const Src =
  '''
  program P;
  type
    TGetter<T> = reference to function(): T;
    TBox<T> = class
      FVal: T;
      function Make(): TGetter<T>;
      begin
        Result := function(): T
          begin
            Result := FVal
          end;
      end;
    end;
  var
    B: TBox<string>;
    G: TGetter<string>;
  begin
    B := TBox<string>.Create();
    B.FVal := 'mono' + 'morphised';
    G := B.Make();
    B := nil;
    WriteLn(G())
  end.
  ''';
begin
  { The string instance's env holds a managed T — the closure must keep the
    value alive after the box itself is released. }
  AssertRunsOnAll(Src, 'monomorphised' + LineEnding, 0)
end;

procedure TE2EAnonMethodTests.TestRun_GenericBody_CapturesTTypedLocal;
const Src =
  '''
  program P;
  type
    TGetter<T> = reference to function(): T;
    TDup<T> = class
      function Snapshot(AVal: T): TGetter<T>;
      var Copy: T;
      begin
        Copy := AVal;
        Result := function(): T
          begin
            Result := Copy
          end;
      end;
    end;
  var
    DI: TDup<Integer>;
    DS: TDup<string>;
    GI: TGetter<Integer>;
    GS: TGetter<string>;
  begin
    DI := TDup<Integer>.Create();
    DS := TDup<string>.Create();
    GI := DI.Snapshot(7);
    GS := DS.Snapshot('seven');
    WriteLn(GI());
    WriteLn(GS())
  end.
  ''';
begin
  { A T-typed LOCAL captured inside a generic method body: the env field is
    typed T and monomorphised per instantiation (value at Integer, managed
    at string). }
  AssertRunsOnAll(Src, '7' + LineEnding + 'seven' + LineEnding, 0)
end;


procedure TE2EAnonMethodTests.TestRun_CaptureFreeClosure_PassedAndCalled;
const
  Src = '''
    program P;
    type TIntFn = reference to function(x: Integer): Integer;
    function Apply(P: TIntFn; v: Integer): Integer;
    begin
      Result := P(v)
    end;
    begin
      WriteLn(Apply(function(x: Integer): Integer begin Result := x * 2 end, 5))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '10' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Closure_OwnedTransientStringArg;
const
  Src = '''
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
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '5' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Closure_StatementPositionCall;
const
  Src = '''
    program P;
    type TProc = reference to procedure(x: Integer);
    procedure Run(P: TProc; v: Integer);
    begin
      P(v)
    end;
    begin
      Run(procedure(x: Integer) begin WriteLn(x) end, 42)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureInRecordField_DirectCall;
const
  { The exact bug repro: a capturing closure in a record field, called
    directly.  The G := R.F; G() form is asserted alongside it so a
    regression that breaks only the direct form is unambiguous. }
  Src = '''
    program P;
    type
      TFn = reference to procedure;
      TR = record F: TFn; end;
    var
      S: string;
      R: TR;
      G: TFn;
    begin
      S := 'hello';
      R.F := procedure begin WriteLn(S) end;
      G := R.F;
      G();
      R.F()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'hello' + LineEnding + 'hello' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureInRecordField_NonZeroOffset;
const
  { Offset 0 is the easy case (the slot address IS the record address).
    A field behind a leading member exercises the 'add Offset' arm too. }
  Src = '''
    program P;
    type
      TFn = reference to procedure;
      TR = record
        Pad: Integer;
        F: TFn;
      end;
    var
      S: string;
      R: TR;
    begin
      S := 'world';
      R.Pad := 7;
      R.F := procedure begin WriteLn(S) end;
      R.F();
      WriteLn(R.Pad)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'world' + LineEnding + '7' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureInRecordField_WithArgs;
const
  { Arguments must still land in the right registers once the env is
    threaded as the hidden first argument. }
  Src = '''
    program P;
    type
      TFn = reference to procedure(A: Integer; B: Integer);
      TR = record F: TFn; end;
    var
      Base: Integer;
      R: TR;
    begin
      Base := 100;
      R.F := procedure(A: Integer; B: Integer)
             begin WriteLn(Base + A + B) end;
      R.F(20, 3)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '123' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureInRecordField_VarParamReceiver;
const
  { A var-param record receiver: the slot holds the caller's ADDRESS, so
    the field slot is one dereference further than a plain local. }
  Src = '''
    program P;
    type
      TFn = reference to procedure;
      TR = record F: TFn; end;
    procedure Run(var R: TR);
    begin
      R.F()
    end;
    var
      S: string;
      Rec: TR;
    begin
      S := 'viavar';
      Rec.F := procedure begin WriteLn(S) end;
      Run(Rec)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'viavar' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureInRecordField_LocalRecord;
const
  { A record LOCAL rather than a global: VarOperand addresses a frame slot,
    so the leaq/address form must be right for locals too. }
  Src = '''
    program P;
    type
      TFn = reference to procedure;
      TR = record F: TFn; end;
    procedure Run;
    var
      S: string;
      R: TR;
    begin
      S := 'localrec';
      R.F := procedure begin WriteLn(S) end;
      R.F()
    end;
    begin
      Run()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'localrec' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureInRecordField_NestedRecord;
const
  { A chained record base (Outer.Inner.F()) goes through the ObjExpr
    receiver path rather than the bare-name path. }
  Src = '''
    program P;
    type
      TFn = reference to procedure;
      TInner = record F: TFn; end;
      TOuter = record Inner: TInner; end;
    var
      S: string;
      O: TOuter;
    begin
      S := 'nested';
      O.Inner.F := procedure begin WriteLn(S) end;
      O.Inner.F()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'nested' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_RecordCopy_ClosureField_EnvSurvivesCopy;
const
  Src = '''
    program P;
    type
      TFn = reference to procedure;
      TR = record
        Tag: Integer;
        F: TFn;
      end;
    var
      S: string;
      A: TR;
      B: TR;
    function Make(const Msg: string): TR;
    begin
      Result.Tag := 7;
      Result.F := procedure begin WriteLn(Msg) end;
    end;
    begin
      S := 'env-alive';
      A := Make(S);
      WriteLn(A.Tag);
      A.F();
      B := A;
      B.F();
      A.F();
      WriteLn('done')
    end.
    ''';
begin
  { Make() returns the record (the sret/register-return path), then B := A
    copies it (the whole-record copy path).  Invoking through BOTH copies
    after the copy proves the env was retained, and reaching 'done' with exit
    0 proves it was not over-released.  Before the fix the QBE build printed
    'env-alive' once and segfaulted here. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    '7' + LineEnding +
    'env-alive' + LineEnding +
    'env-alive' + LineEnding +
    'env-alive' + LineEnding +
    'done' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ByValRecordParam_ClosureFieldCall;
const
  Src = '''
    program P;
    type
      TFn = reference to procedure;
      TR = record
        Tag: Integer;
        F: TFn;
      end;
    var
      S: string;
      A: TR;
    procedure Take(V: TR);
    begin
      WriteLn('tag=', V.Tag);
      V.F()
    end;
    begin
      S := 'env-alive';
      A.Tag := 7;
      A.F := procedure begin WriteLn(S) end;
      Take(A);
      WriteLn('done')
    end.
    ''';
begin
  { V.Tag reads correctly (the field-access path already used the full
    by-ref predicate) while V.F() segfaulted — the asymmetry inside a single
    function is the tell. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    'tag=7' + LineEnding +
    'env-alive' + LineEnding +
    'done' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ByValRecordParam_RecordMethodCall;
const
  Src = '''
    program P;
    type
      TR = record
        Tag: Integer;
        procedure Show();
      end;
    procedure TR.Show();
    begin
      WriteLn('Show tag=', Tag)
    end;
    procedure Take(V: TR);
    begin
      V.Show()
    end;
    var
      A: TR;
    begin
      A.Tag := 7;
      Take(A);
      WriteLn('done')
    end.
    ''';
begin
  { Worse than the closure crash: this exited 0 and printed a garbage Tag,
    so nothing flagged it.  Self was the parameter SLOT's address, so the
    method read adjacent stack memory. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    'Show tag=7' + LineEnding +
    'done' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ImplicitSelfRefField_Call;
const
  Src = '''
    program P;
    type
      TSel = reference to function(N: Integer): Integer;
      TRun = reference to procedure(N: Integer);
      TApply = reference to function(N: Integer; F: TSel): Integer;
      TBox = class
      public
        FBase: Integer;
        FRun: TRun;
        FApply: TApply;
        procedure Drv();
      end;
    procedure TBox.Drv();
    begin
      FRun(1);                          { stmt, value arg }
      WriteLn(FApply(2, function(X: Integer): Integer
        begin
          Result := X + FBase
        end))                           { expr, closure arg }
    end;
    var
      B: TBox;
      K: Integer;
    begin
      K := 100;
      B := TBox.Create();
      B.FBase := 40;
      B.FRun := procedure(N: Integer)
        begin
          WriteLn(N + K)
        end;
      B.FApply := function(N: Integer; F: TSel): Integer
        begin
          Result := F(N) + K
        end;
      B.Drv();
      B.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    '101' + LineEnding +
    '142' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_MethodPtrClosureVar_VarAndDoubleArgs;
const
  Src = '''
    program P;
    type
      TBump = procedure(var N: Integer) of object;
      TScale = function(X: Double; K: Integer): Double of object;
      TRefBump = reference to procedure(var N: Integer);
      TC = class
      public
        procedure Bump(var N: Integer);
        function Scale(X: Double; K: Integer): Double;
      end;
    procedure TC.Bump(var N: Integer);
    begin
      N := N + 10
    end;
    function TC.Scale(X: Double; K: Integer): Double;
    begin
      Result := X * K
    end;
    var
      O: TC;
      B: TBump;
      S: TScale;
      R: TRefBump;
      N: Integer;
    begin
      O := TC.Create();
      B := @O.Bump;
      S := @O.Scale;
      N := 1;
      B(N);                             { var through 'of object' }
      WriteLn(N);
      WriteLn(Trunc(S(1.5, 4) * 100));  { Double through 'of object' }
      R := procedure(var M: Integer)
        begin
          M := M * 3
        end;
      R(N);                             { var through 'reference to' }
      WriteLn(N);
      R := nil;
      O.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    '11' + LineEnding +
    '600' + LineEnding +
    '33' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_CaptureFreeLiteral_AssignAndCall;
const
  Src =
    '''
    program P;
    type
      TIntProc = reference to procedure(AValue: Integer);
    var
      V: TIntProc;
    begin
      V := procedure(AValue: Integer)
      begin
        WriteLn(AValue * 2)
      end;
      V(21)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_FunctionLiteral_ReturnsValue;
const
  Src =
    '''
    program P;
    type
      TAdd = reference to function(const A, B: Integer): Integer;
    var
      F: TAdd;
    begin
      F := function(const A, B: Integer): Integer
      begin
        Result := A + B
      end;
      WriteLn(F(19, 23))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_AdapterFromPlainRoutine;
const
  Src =
    '''
    program P;
    type
      TIntProc = reference to procedure(AValue: Integer);
    procedure Show(AValue: Integer);
    begin
      WriteLn(AValue + 1)
    end;
    var
      V: TIntProc;
    begin
      V := @Show;
      V(41)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_NilClosure_Assignable;
const
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    var
      V: TProc;
    begin
      V := procedure
      begin
        WriteLn('lived')
      end;
      V();
      V := nil;
      WriteLn('done')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'lived' + #10 + 'done' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_ExprBody_MultiParam_Captures;
const
  Src =
    '''
    program P;
    type
      TAdd = reference to function(A, B: Integer): Integer;
    var
      F: TAdd;
      Base: Integer;
    begin
      Base := 40;
      F := (A, B) -> A + B + Base;
      WriteLn(F(1, 1))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_SingleIdent_ProcedureTarget;
const
  Src =
    '''
    program P;
    type
      TShow = reference to procedure(N: Integer);
    var
      P1: TShow;
    begin
      P1 := N -> WriteLn(N * 2);
      P1(21)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_BlockBody;
const
  Src =
    '''
    program P;
    type
      TAdd = reference to function(A, B: Integer): Integer;
    var
      F: TAdd;
    begin
      F := (A, B) -> begin
        Result := A * B
      end;
      WriteLn(F(6, 7))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_MinusGreaterStaysDistinct;
const
  Src =
    '''
    program P;
    type
      TF = reference to function(A: Integer): Integer;
    var
      F: TF;
      X: Integer;
    begin
      F := (A) -> A - 1;
      X := F(43);
      if X > 41 then
        WriteLn(X)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_ArgPosition_Standalone;
const
  Src =
    '''
    program P;
    type
      TSel = reference to function(N: Integer): Integer;
    function Twice(N: Integer; F: TSel): Integer;
    begin
      Result := F(F(N))
    end;
    begin
      WriteLn(Twice(10, X -> X + 6))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '22' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_ArgPosition_MethodWithCapture;
const
  Src =
    '''
    program P;
    type
      TPred = reference to function(N: Integer): Boolean;
      TC = class
        function CountIf(A, B, C: Integer; P: TPred): Integer;
        begin
          Result := 0;
          if P(A) then Result := Result + 1;
          if P(B) then Result := Result + 1;
          if P(C) then Result := Result + 1
        end;
      end;
    var
      C: TC;
      Limit: Integer;
    begin
      C := TC.Create();
      Limit := 10;
      WriteLn(C.CountIf(5, 11, 20, N -> N > Limit))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_ArgPosition_OverloadByShape;
const
  Src =
    '''
    program P;
    type
      TSel = reference to function(N: Integer): Integer;
    function Pick(N: Integer; V: Integer): string; overload;
    begin
      Result := 'int:' + IntToStr(V)
    end;
    function Pick(N: Integer; F: TSel): string; overload;
    begin
      Result := 'fn:' + IntToStr(F(N))
    end;
    begin
      WriteLn(Pick(20, 7));
      WriteLn(Pick(20, X -> X * 2 + 2))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'int:7' + #10 + 'fn:42' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_Arrow_ArgPosition_ProcTypeCalls;
const
  Src =
    '''
    program P;
    type
      TSel = reference to function(N: Integer): Integer;
      TRun = reference to procedure(N: Integer; F: TSel);
      TApply = reference to function(N: Integer; F: TSel): Integer;
      TBox = class
      public
        FRun: TRun;
        FApply: TApply;
        procedure Drv();
      end;
    procedure TBox.Drv();
    begin
      FRun(1, X -> X + 10);
      WriteLn(FApply(2, X -> X * 3))
    end;
    var
      Run: TRun;
      Apply: TApply;
      B: TBox;
    begin
      Run := procedure(N: Integer; F: TSel)
        begin
          WriteLn(F(N))
        end;
      Apply := function(N: Integer; F: TSel): Integer
        begin
          Result := F(N)
        end;
      Run(4, X -> X + 1);
      WriteLn(Apply(5, X -> X * 2));
      B := TBox.Create();
      B.FRun := Run;
      B.FApply := Apply;
      B.Drv();
      B.FRun(6, X -> X - 1);
      WriteLn(B.FApply(7, X -> X + 100));
      B.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '5' + #10 + '10' + #10 + '11' + #10 + '6' + #10 + '5' + #10 + '107' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_GenericMethodOnGenericClass_Gate;
const
  Src =
    '''
    program P;
    type
      TSel<T, R> = reference to function(AVal: T): R;
      TBox<T> = class
      public
        FVal: T;
        function MapTo<R>(F: TSel<T, R>): R;
      end;
    function TBox<T>.MapTo<R>(F: TSel<T, R>): R;
    begin
      Result := F(FVal)
    end;
    var
      B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.FVal := 42;
      WriteLn(B.MapTo<string>(N -> 'v' + IntToStr(N)));
      WriteLn(B.MapTo<Integer>(N -> N + 1))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'v42' + #10 + '43' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_NestedSelfCapture_AndGenericClosurePerInstance;
const
  {
    Self reaches nested routines through the hidden _cap_Self pointer: a nested
    procedure writing Self.FVal, and a nested RECORD-returning (sret) function
    reading it (the sret call path once omitted the capture argument).  A
    closure in a generic class body is monomorphised per instance, each
    capturing its own Self. }
  Src = '''
    program NestedSelf;
    type
      TBig = record
        A, B, C, D, E: Int64;
      end;
      TC = class
        FVal: Int64;
        procedure M();
      end;
      TGetter<T> = reference to function(): T;
      TBox<T> = class
        FVal: T;
        function Make(): TGetter<T>;
        begin
          Result := function(): T
            begin
              Result := FVal
            end;
        end;
      end;
    procedure TC.M();
      procedure Inner();
      begin
        Self.FVal := 7
      end;
      function MakeBig(): TBig;
      begin
        Result.A := Self.FVal * 10;
        Result.E := Self.FVal + 1
      end;
    var B: TBig;
    begin
      Inner();
      B := MakeBig();
      WriteLn(Self.FVal, ' ', B.A, ' ', B.E)
    end;
    var
      C: TC;
      BI: TBox<Integer>;
      BS: TBox<string>;
      GI: TGetter<Integer>;
      GS: TGetter<string>;
    begin
      C := TC.Create();
      C.M();
      BI := TBox<Integer>.Create();
      BS := TBox<string>.Create();
      BI.FVal := 42;
      BS.FVal := 'forty-two';
      GI := BI.Make();
      GS := BS.Make();
      BI.FVal := 43;
      WriteLn(GI(), ' ', GS())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '7 70 8' + #10 +
    '43 forty-two' + #10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ClosureResult_FieldStoreAndImmediateCall;
const
  {
    A closure returned by a call is stored straight into a field, and a closure
    returned by a call is called on the spot -- MakeAdder(1)(41), H.Make(7)(6),
    including a Double result.  Each call hands over its Env at +1; the field
    store moves it in without a retain and the immediate call drops it after the
    call, so the program is leak-free. }
  Src = '''
    program RefClo;
    type
      TF = reference to function(X: Integer): Integer;
      TD = reference to function(X: Double): Double;
      THolder = class
        FF: TF;
        function Make(N: Integer): TF;
      end;
    function MakeAdder(N: Integer): TF;
    begin
      Result := function(X: Integer): Integer begin Result := X + N end;
    end;
    function MakeScale(K: Double): TD;
    begin
      Result := function(X: Double): Double begin Result := X * K end;
    end;
    function THolder.Make(N: Integer): TF;
    begin
      Result := function(X: Integer): Integer begin Result := X * N end;
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.FF := MakeAdder(10);
      WriteLn(H.FF(5));
      H.FF := MakeAdder(3);
      WriteLn(H.FF(5));
      WriteLn(MakeAdder(1)(41));
      WriteLn(H.Make(7)(6));
      WriteLn(MakeScale(2.5)(4.0):0:2);
      H.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '15' + #10 +
    '8' + #10 +
    '42' + #10 +
    '42' + #10 +
    '10.00' + #10, 0);
  AssertLeakFreeOnAll(Src, '10.00');
end;

procedure TE2EAnonMethodTests.TestRun_ClosureArg_FromElementFieldAndDeref;
const
  Src = '''
    program ClosArgs;
    uses SysUtils;
    type
      TF = reference to function: Integer;
      TSA = array[0..1] of TF;
      TR = record F: TF; end;
      TOb = class F: TF; end;
      PF = ^TF;
    function V(N: Integer): TF; begin Result := function: Integer begin Result := N end end;
    function Pr(E: TF): String; begin Result := 'v' + IntToStr(E()) end;
    procedure Run;
    var L: TSA; R: TR; O: TOb; P: PF; F: TF; DA: array of TF;
    begin
      L[1] := V(3);
      R.F := V(4);
      O := TOb.Create();
      O.F := V(5);
      F := V(6);
      P := @F;
      SetLength(DA, 2);
      DA[1] := V(7);
      WriteLn(Pr(L[1]), ' ', Pr(R.F), ' ', Pr(O.F), ' ', Pr(P^), ' ', Pr(F), ' ', Pr(DA[1]));
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 'v3 v4 v5 v6 v6 v7');
end;

procedure TE2EAnonMethodTests.TestRun_ClosureCallResult_AsArgument;
const
  Src = '''
    program CallArgs;
    type
      TF = reference to function: Integer;
      TOb = class
        N: Integer;
        function Mk: TF;
      end;
    function TOb.Mk: TF; begin Result := function: Integer begin Result := N end end;
    function Plain: TF; begin Result := function: Integer begin Result := 3 end end;
    function Cap(K: Integer): TF; begin Result := function: Integer begin Result := K end end;
    function Use(F: TF): Integer; begin Result := F() end;
    function Use3(A: Integer; F: TF; B: Double): Integer; begin Result := A + F() + Trunc(B) end;
    procedure Run;
    var O: TOb;
    begin
      O := TOb.Create();
      O.N := 4;
      WriteLn('arg ', Use(Plain()), ' ', Use(Cap(6)), ' ', Use(O.Mk()), ' ',
        Use3(1, Cap(6), 2.5));
      O.Free();
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 'arg 3 6 4 9');
end;

procedure TE2EAnonMethodTests.TestRun_Capture_WideParameters;
const
  Src = '''
    program WideCaps;
    uses SysUtils;
    type
      TF = reference to function: Integer;
      TA = array[0..2] of string;
      TBig = set of 0..99;
      TRec = record A, B: Integer; S: string; end;
      IThing = interface function Get: Integer; end;
      TThing = class(TObject, IThing) function Get: Integer; end;
      TPlain = function(X: Integer): Integer;
    function TThing.Get: Integer; begin Result := 42 end;
    function Dbl(X: Integer): Integer; begin Result := X * 2 end;
    function Cap(K: Integer): TF; begin Result := function: Integer begin Result := K end end;
    function CapFn(G: TF): TF; begin Result := function: Integer begin Result := G() + 100 end end;
    function CapArr(A: TA): TF; begin Result := function: Integer begin Result := Length(A[0]) + Length(A[2]) end end;
    function CapCArr(const A: TA): TF; begin Result := function: Integer begin Result := Length(A[1]) end end;
    function CapSet(S: TBig): TF; begin Result := function: Integer begin if 77 in S then Result := 1 else Result := 0 end end;
    function CapRec(R: TRec): TF; begin Result := function: Integer begin Result := R.A + R.B + Length(R.S) end end;
    function CapCRec(const R: TRec): TF; begin Result := function: Integer begin Result := R.A * 10 + Length(R.S) end end;
    function CapIntf(I: IThing): TF; begin Result := function: Integer begin Result := I.Get() end end;
    function CapSingle(S: Single): TF; begin Result := function: Integer begin Result := Trunc(S * 10) end end;
    function CapDouble(S: Double): TF; begin Result := function: Integer begin Result := Trunc(S * 10) end end;
    function CapPlain(P: TPlain): TF; begin Result := function: Integer begin Result := P(21) end end;
    procedure Run;
    var F: TF; A: TA; S: TBig; R: TRec; T: IThing; Line: string;
    begin
      F := CapFn(Cap(1)); Line := IntToStr(F());
      A[0] := 'ab'; A[1] := 'xyz'; A[2] := 'c';
      F := CapArr(A); A[0] := ''; Line := Line + ' ' + IntToStr(F());
      F := CapCArr(A); Line := Line + ' ' + IntToStr(F());
      S := [3, 77]; F := CapSet(S); S := []; Line := Line + ' ' + IntToStr(F());
      R.A := 1; R.B := 2; R.S := 'abcd'; F := CapRec(R); R.S := ''; Line := Line + ' ' + IntToStr(F());
      R.S := 'zz'; F := CapCRec(R); R.S := ''; Line := Line + ' ' + IntToStr(F());
      T := TThing.Create(); F := CapIntf(T); T := nil; Line := Line + ' ' + IntToStr(F());
      F := CapSingle(1.5); Line := Line + ' ' + IntToStr(F());
      F := CapDouble(2.5); Line := Line + ' ' + IntToStr(F());
      F := CapPlain(@Dbl); Line := Line + ' ' + IntToStr(F());
      WriteLn('caps ', Line);
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 'caps 101 3 3 1 7 12 42 15 25 42');
end;

procedure TE2EAnonMethodTests.TestRun_ClosureStore_VarParamAndCapturedTargets;
const
  Src = '''
    program Targets;
    type
      TF = reference to function: Integer;
      TPI = reference to procedure(X: Integer);
    function Cap(K: Integer): TF; begin Result := function: Integer begin Result := K end end;
    procedure SetLit(var F: TF); begin F := function: Integer begin Result := 9 end end;
    procedure SetCall(var F: TF); begin F := Cap(10) end;
    procedure SetNil(var F: TF); begin F := nil end;
    procedure Run;
    var F, G: TF; P: TPI;
    begin
      SetLit(F); Write('var ', F());
      SetCall(F); Write(' ', F());
      SetNil(F); Write(' ', Assigned(F));
      P := procedure(X: Integer) begin G := Cap(X) end;
      P(5);
      WriteLn(' captured ', G());
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 'var 9 10 False captured 5');
end;

procedure TE2EAnonMethodTests.TestRun_ClosureReassignFromCall_ReleasesOldEnv;
const
  Src = '''
    program Reassign;
    type
      TF = reference to function: Integer;
      TOb = class N: Integer; end;
    function CapO(O: TOb): TF; begin Result := function: Integer begin Result := O.N end end;
    function Wrap(G: TF): TF; begin Result := function: Integer begin Result := G() * 2 end end;
    procedure Run;
    var F: TF; O: TOb;
    begin
      O := TOb.Create(); O.N := 1;
      F := CapO(O);
      O := TOb.Create(); O.N := 2;
      F := CapO(O);
      O := nil;
      F := Wrap(F);
      WriteLn('re ', F());
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 're 4');
end;

procedure TE2EAnonMethodTests.TestRun_ClosurePointerWrite_AndExprCallForms;
const
  Src = '''
    program PtrForms;
    type
      TF = reference to function: Integer;
      PF = ^TF;
      TOb = class
        N: Integer;
        function Mk: TF;
      end;
    function TOb.Mk: TF; begin Result := function: Integer begin Result := N end end;
    function Cap(K: Integer): TF; begin Result := function: Integer begin Result := K end end;
    function CapO(O: TOb): TF; begin Result := function: Integer begin Result := O.N + 1 end end;
    function MkOb: TOb; begin Result := TOb.Create(); Result.N := 13 end;
    procedure Run;
    var F, G: TF; P: PF; L: array[0..1] of TF; D: array of TF; O: TOb;
    begin
      P := @F;
      P^ := Cap(4); Write('p ', F());
      O := TOb.Create(); O.N := 10;
      P^ := CapO(O); O := nil; Write(' ', F(), ' ', P^());
      G := Cap(9); P^ := G; Write(' ', F());
      P^ := function: Integer begin Result := 77 end; Write(' ', P^());
      P^ := P^; Write(' ', F());
      P^ := nil; Write(' ', Assigned(F));
      L[0] := CapO(TOb.Create()); Write(' e ', L[0]());
      SetLength(D, 1); D[0] := Cap(6); Write(' ', D[0]());
      F := MkOb().Mk(); WriteLn(' t ', F());
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 'p 4 11 11 9 77 77 False e 1 6 t 13');
end;

procedure TE2EAnonMethodTests.TestRun_BlockVar_ManagedAggregatesPerIteration;
const
  Src = '''
    program BlockVars;
    uses SysUtils;
    type
      TF = reference to function: Integer;
      IThing = interface function Get: Integer; end;
      TThing = class(TObject, IThing) N: Integer; function Get: Integer; end;
      TRec = record S: string; N: Integer; end;
    function TThing.Get: Integer; begin Result := N end;
    function Cap(K: Integer): TF; begin Result := function: Integer begin Result := K end end;
    procedure Run;
    var I, Sum: Integer; Fs: array[0..2] of TF;
    begin
      Sum := 0;
      for I := 0 to 2 do
      begin
        var G: TF := Cap(I * 10);
        var T: IThing := TThing.Create();
        var R: TRec;
        R.S := 'x' + IntToStr(I); R.N := I;
        Sum := Sum + G() + Length(R.S) + R.N + T.Get();
        var J: Integer := I;
        Fs[I] := function: Integer begin Result := J * 100 end;
      end;
      WriteLn('blockvars ', Sum, ' ', Fs[0](), ' ', Fs[2]());
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 'blockvars 39 0 200');
end;

procedure TE2EAnonMethodTests.TestRun_ExprCallStmt_ElementAndDeref;
const
  Src = '''
    program ExprCalls;
    uses SysUtils;
    type
      TP = procedure(X: Integer);
      TR = reference to procedure(X: Integer);
      TS = reference to function: string;
      PR = ^TR;
      TM = procedure of object;
      TOb = class N: Integer; procedure Hi; end;
    procedure TOb.Hi; begin Write(' hi', N) end;
    procedure Show(X: Integer); begin Write(' show', X) end;
    var
      A: array[0..1] of TP;
      R: array[0..1] of TR;
      S: array[0..0] of TS;
      M: array[0..0] of TM;
      P: PR;
      F: TR;
      O: TOb;
      Total: Integer;
    begin
      A[1] := @Show;
      A[1](7);
      R[0] := procedure(X: Integer) begin Total := Total + X end;
      R[0](5); R[0](6);
      Write(' total', Total);
      F := procedure(X: Integer) begin Write(' deref', X) end;
      P := @F;
      P^(9);
      S[0] := function: string begin Result := 'x' + IntToStr(Total) end;
      S[0]();
      O := TOb.Create(); O.N := 3;
      M[0] := @O.Hi;
      M[0]();
      O.Free();
      WriteLn()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, ' show7 total11 deref9 hi3');
end;

procedure TE2EAnonMethodTests.TestRun_FreeOfCapturedVariable;
const Src =
  '''
  program P;
  type
    TProc = reference to procedure;
    TN = class destructor Destroy; override; end;
  destructor TN.Destroy; begin WriteLn('freed') end;
  var Q: TProc;
  procedure Make();
  var Cap: TN;
  begin
    Cap := TN.Create();
    Q := procedure begin Cap.Free(); WriteLn(Cap = nil) end;
  end;
  begin
    Make();
    Q();
    Q := nil;
    WriteLn('done')
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'freed'#10'True'#10'done'#10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_CapturedClosure_FloatResult;
const Src =
  '''
  program P;
  type
    TRef = reference to function(X: Double): Double;
    TRefS = reference to function(X: Single): Single;
    TP = reference to procedure;
  function Sum(const A: array of Double): Double;
  var I: Integer;
  begin Result := 0; for I := 0 to High(A) do Result := Result + A[I] end;
  procedure Outer();
  var R: TRef; RS: TRefS; Q: TP;
    procedure Inner();
    begin
      WriteLn('nested ', R(1):0:2, ' ', RS(1):0:2, ' ', R(2) + 1:0:2)
    end;
  begin
    R := function(X: Double): Double begin Result := X * 3 end;
    RS := function(X: Single): Single begin Result := X * 3 end;
    Inner();
    Q := procedure
      begin
        WriteLn('anon ', R(4):0:2, ' ', RS(4):0:2, ' ', Sum([R(1), R(2)]):0:2)
      end;
    Q();
  end;
  begin
    Outer()
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'nested 3.00 3.00 7.00'#10'anon 12.00 12.00 9.00'#10, 0);
end;

procedure TE2EAnonMethodTests.TestRun_NestedNonCapturingLiteral;
const
  Src = '''
    program P;
    type
      TKFn = reference to function(A: Integer): Integer;
      TCFn = reference to function(): TKFn;
    function GetC(): TCFn;
    begin
      Result := function(): TKFn
        begin
          Result := function(A: Integer): Integer begin Result := A + 1000; end;
        end;
    end;
    var C: TCFn; K: TKFn;
    begin
      C := GetC();
      K := C();
      WriteLn(K(6), ' ', K(5));
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '1006 1005' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_LiteralInStaticMethod;
const
  Src = '''
    program P;
    type
      TKFn = reference to function(A: Integer): Integer;
      TC = class
        static function MakeFn(N: Integer): TKFn;
      end;
    static function TC.MakeFn(N: Integer): TKFn;
    begin
      Result := function(A: Integer): Integer begin Result := A * N; end;
    end;
    var K: TKFn;
    begin
      K := TC.MakeFn(3);
      WriteLn(K(7));
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '21' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_ExprCallStmt_CallResultCallee;
const
  Src = '''
    program P;
    type
      TShow = reference to procedure(N: Integer);
      TKFn = reference to function(A: Integer): Integer;
      TBox = class
        V: Integer;
        procedure Show(Tag: string);
      end;
      TMaker = reference to function(N: Integer): TBox;
    procedure TBox.Show(Tag: string); begin WriteLn(Tag, ' ', V); end;
    function GetShow(): TShow;
    begin
      Result := procedure(N: Integer) begin WriteLn('show ', N); end;
    end;
    function GetFn(): TKFn;
    begin
      Result := function(A: Integer): Integer begin WriteLn('fn ', A); Result := A; end;
    end;
    function GetMaker(): TMaker;
    begin
      Result := function(N: Integer): TBox
        begin
          Result := TBox.Create();
          Result.V := N * 10;
        end;
    end;
    begin
      GetShow()(5);
      GetFn()(6);
      GetMaker()(7).Show('box');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'show 5' + LineEnding + 'fn 6' + LineEnding +
    'box 70' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_CapturedLocalRecord_SharedWithDeclaringRoutine;
const
  Src = '''
    program CapRec;
    type
      TArr = array[0..3] of Integer;
      TInner = record A: TArr; N: Integer; end;
      TRec = record A: TArr; In1: TInner; N: Integer; S: string; end;
    procedure Run;
    var L, L2: TRec; K: Integer; F: reference to procedure;
    begin
      L.N := 3; L.S := 'outer'; L.A[2] := 20;
      F := procedure
           begin
             WriteLn('closure sees ', L.N, ' ', L.S, ' ', L.A[2]);
             L.N := L.N + 1; L.In1.N := 2; L.A[1] := 81; L.In1.A[1] := 82; L.S := L.S + '+';
             K := 5;
           end;
      F();
      WriteLn(L.N, ' ', L.In1.N, ' ', L.A[1], ' ', L.In1.A[1], ' ', L.S, ' ', K);
      L2 := L; L2.N := 99; L2.S := 'copy';
      F := procedure begin L := L2; end;
      F();
      WriteLn(L.N, ' ', L.S, ' ', L.A[1]);
    end;
    var G: TRec; F: reference to procedure;
    begin
      Run();
      F := procedure begin G.N := 1; G.In1.N := 2; G.A[1] := 81; G.In1.A[1] := 82; end;
      F();
      WriteLn(G.N, ' ', G.In1.N, ' ', G.A[1], ' ', G.In1.A[1]);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'closure sees 3 outer 20' + LineEnding +
    '4 2 81 82 outer+ 5' + LineEnding +
    '99 copy 81' + LineEnding +
    '1 2 81 82' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_CapturedManagedVars_SharedWithDeclaringRoutine;
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
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 10 hi a x1' + LineEnding +
    '3 5107 hi b x1y' + LineEnding +
    '4 True' + LineEnding +
    '32 7 p1q q 7' + LineEnding, 0);
end;

procedure TE2EAnonMethodTests.TestRun_CapturedWeakLocals_StayWeak;
const
  Src = '''
    program Q;
    type
      IThing = interface
        function N(): Integer;
      end;
      TThing = class(TObject, IThing)
        FN: Integer;
        function N(): Integer;
        destructor Destroy(); override;
      end;
      TProc = reference to procedure;
    function TThing.N(): Integer; begin Result := FN end;
    destructor TThing.Destroy(); begin WriteLn('gone ', FN); inherited Destroy() end;
    procedure WithIntf();
    var [Weak] W: IThing; S: IThing; P: TProc;
    begin
      S := TThing.Create();
      P := procedure begin W := S end;
      P();
      WriteLn('intf ', W.N());
      S := nil;
      WriteLn('intf after ', Assigned(W));
      P := nil
    end;
    procedure WithClass();
    var [Weak] W: TThing; S: TThing; P: TProc;
    begin
      S := TThing.Create(); S.FN := 2;
      P := procedure begin W := S end;
      P();
      WriteLn('class ', W.N());
      S := nil;
      WriteLn('class after ', Assigned(W));
      P := nil
    end;
    function MakeProbe(const S: IThing): TProc;
    var [Weak] W: IThing;
    begin
      W := S;
      Result := procedure begin WriteLn('probe ', Assigned(W)) end
    end;
    procedure Declaring();
    var [Weak] W: IThing; S: IThing; P: TProc;
    begin
      P := procedure begin WriteLn('decl sees ', Assigned(W)) end;
      S := TThing.Create();
      W := S;
      P();
      S := nil;
      P()
    end;
    procedure NestedClass();
    var [Weak] W: TThing; S: TThing;
      procedure Inner(); begin W := S end;
    begin
      S := TThing.Create(); S.FN := 9;
      Inner();
      WriteLn('nested class ', W.N());
      S := nil;
      WriteLn('nested class after ', Assigned(W))
    end;
    var Pr: TProc; Keep: IThing;
    begin
      Keep := TThing.Create();
      Pr := MakeProbe(Keep);
      Pr();
      Keep := nil;
      Pr();
      Pr := nil;
      Declaring();
      NestedClass();
      WithIntf();
      WriteLn('--');
      WithClass();
      WriteLn('end')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { the closure env's field for a [Weak] local was a strong field and the
    lifted body's symbol was not weak: the object never died while the
    closure lived, and the env released it at teardown }
  AssertRunsOnAll(Src,
    'probe True' + LineEnding + 'gone 0' + LineEnding + 'probe False' + LineEnding +
    'decl sees True' + LineEnding + 'gone 0' + LineEnding + 'decl sees False' + LineEnding +
    'nested class 9' + LineEnding + 'gone 9' + LineEnding + 'nested class after False' + LineEnding +
    'intf 0' + LineEnding + 'gone 0' + LineEnding + 'intf after False' + LineEnding + '--' + LineEnding +
    'class 2' + LineEnding + 'gone 2' + LineEnding + 'class after False' + LineEnding +
    'end' + LineEnding, 0);
end;

initialization
  RegisterTest(TE2EAnonMethodTests);

end.
