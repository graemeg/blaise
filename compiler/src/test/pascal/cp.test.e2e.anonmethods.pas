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
    procedure TestRun_CaptureLocal_ReadInClosure;
    procedure TestRun_ClosureWrite_VisibleInEnclosing;
    procedure TestRun_TwoClosures_ShareOneEnv;
    procedure TestRun_Escape_GlobalClosure_OutlivesFrame;
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

initialization
  RegisterTest(TE2EAnonMethodTests);

end.
