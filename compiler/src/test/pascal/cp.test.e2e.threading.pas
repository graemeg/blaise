{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.threading;

{ E2E tests for TThread and TCriticalSection from the RTL Classes unit.
  Covers: basic thread creation, WaitFor, Terminate flag,
  mutex-based synchronisation via TCriticalSection. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EThreadingTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ClassThreadVar_PerThreadAndBalanced;
    procedure TestRun_Thread_FinishesInsideConstructor_ObjectSurvives;
    procedure TestRun_Thread_BasicExecute;
    procedure TestRun_Thread_WaitForBlocksUntilDone;
    procedure TestRun_Thread_Terminate_Flag;
    procedure TestRun_Thread_FinishedAfterExecute;
    procedure TestRun_Thread_MultipleThreads;
    procedure TestRun_CriticalSection_MutexProtectsCounter;
    procedure TestRun_Thread_InheritedDestroy_CleanExit;
    procedure TestRun_ThreadVar_MainThread_ReadWrite;
    procedure TestRun_ThreadVar_MixedWithGlobalVar;
    procedure TestRun_ThreadVar_RecordField_PerThreadIsolation;
    procedure TestRun_ThreadVar_RecordMethod_PerThreadIsolation;
    procedure TestRun_ThreadVar_AddressOf_PerThreadIsolation;
    procedure TestRun_PerThreadAllocator_IndependentAllocs;
    procedure TestRun_AtomicARC_SharedObject_NoCorruption;
  end;

implementation

procedure TE2EThreadingTests.TestRun_ClassThreadVar_PerThreadAndBalanced;
const
  { A CLASS-typed threadvar (the scheduler's GTLWorker shape): each thread
    sees its own instance, and the ARC stores into the TLS slot balance --
    arm64 rejected the declaration ("threadvar of this type"). }
  Src = '''
    program tv;
    uses SysUtils, Classes;
    type
      TTag = class Name: string; constructor Create(const N: string); end;
      TW = class(TThread) procedure Execute; override; end;
    constructor TTag.Create(const N: string); begin Name := N; end;
    threadvar
      GTag: TTag;
    var Seen: string;
    procedure TW.Execute;
    begin
      GTag := TTag.Create('worker');
      Seen := GTag.Name;
      GTag := nil;
    end;
    var T: TW;
    begin
      GTag := TTag.Create('main');
      T := TW.Create(False); T.WaitFor();
      WriteLn(GTag.Name, ' ', Seen);
      GTag := nil;
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRTLRunsOnAll(Src, 'main worker' + LineEnding, 0);
  AssertLeakFreeOnAll(Src, 'main worker');
end;

procedure TE2EThreadingTests.TestRun_Thread_FinishesInsideConstructor_ObjectSurvives;
const
  { Create(False) starts the worker inside the constructor, while the new
    instance's refcount is still 0.  The worker must not take (and drop) an
    ARC reference to it: a 0 -> 1 -> 0 round trip destroyed the object under
    the constructor, and the creator's reference dangled -- releasing it
    crashed.  WaitFor inside the constructor makes the worker finish first
    every time, so the old trampoline failed deterministically. }
  Src = '''
    program tc;
    uses SysUtils, Classes;
    type
      TW = class(TThread)
        constructor Create;
        procedure Execute; override;
      end;
    var Seen: string;
    constructor TW.Create;
    begin
      inherited Create(False);
      WaitFor();
    end;
    procedure TW.Execute;
    begin
      Seen := 'worker';
    end;
    var T: TW;
    begin
      T := TW.Create;
      WriteLn('main ', Seen);
      T := nil;
      WriteLn('done');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRTLRunsOnAll(Src, 'main worker' + LineEnding + 'done' + LineEnding, 0);
end;

procedure TE2EThreadingTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-threading');
end;

const
  LE = #10;

  SrcBasicExecute =
    '''
    program P;
    uses Classes;
    type
      TMyThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TMyThread.Execute;
    begin
      WriteLn('worker')
    end;
    var T: TMyThread;
    begin
      T := TMyThread.Create(True);
      T.Start();
      T.WaitFor();
      WriteLn('main')
    end.
    ''';

  SrcWaitForBlocks =
    '''
    program P;
    uses Classes;
    type
      TSlowThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TSlowThread.Execute;
    var I, Sum: Integer;
    begin
      Sum := 0;
      for I := 0 to 999999 do
        Sum := Sum + 1;
      WriteLn('slow-done')
    end;
    var T: TSlowThread;
    begin
      T := TSlowThread.Create(True);
      T.Start();
      T.WaitFor();
      WriteLn('after-wait')
    end.
    ''';

  SrcTerminateFlag =
    '''
    program P;
    uses Classes;
    type
      TLoopThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TLoopThread.Execute;
    var I: Integer;
    begin
      { Spin until terminated.  The loop must exit *only* via the terminate
        flag so Terminated is guaranteed True when read — an early-break
        escape would let the worker finish before the main thread's Terminate
        landed, making the printed flag race between 0 and 1.  The large cap is
        only a safety net so a missed Terminate cannot hang the test forever.
        Read the public Terminated property — the backing FTerminated field is
        private to TThread and not visible to subclasses. }
      I := 0;
      while not Self.Terminated do
      begin
        I := I + 1;
        if I > 2000000000 then
          break
      end;
      WriteLn(Self.Terminated)
    end;
    var T: TLoopThread;
    begin
      T := TLoopThread.Create(True);
      T.Start();
      T.Terminate();
      T.WaitFor();
      WriteLn('ok')
    end.
    ''';

  SrcFinishedFlag =
    '''
    program P;
    uses Classes;
    type
      TQuickThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TQuickThread.Execute;
    begin
    end;
    var T: TQuickThread;
    begin
      { Read the public Finished property — the backing FFinished field is
        private to TThread and not visible outside the class. }
      T := TQuickThread.Create(True);
      WriteLn(T.Finished);
      T.Start();
      T.WaitFor();
      WriteLn(T.Finished)
    end.
    ''';

  SrcMultipleThreads =
    '''
    program P;
    uses Classes;
    type
      TNumThread = class(TThread)
      private
        FNum: Integer;
      protected
        procedure Execute; override;
      end;
    procedure TNumThread.Execute;
    begin
    end;
    var
      A, B, C: TNumThread;
    begin
      A := TNumThread.Create(True);
      B := TNumThread.Create(True);
      C := TNumThread.Create(True);
      A.FNum := 1;
      B.FNum := 2;
      C.FNum := 3;
      A.Start();
      B.Start();
      C.Start();
      A.WaitFor();
      B.WaitFor();
      C.WaitFor();
      WriteLn(A.FNum + B.FNum + C.FNum)
    end.
    ''';

  SrcCriticalSection =
    '''
    program P;
    uses Classes;
    type
      TShared = class
        CS: TCriticalSection;
        Counter: Integer;
      end;
      TIncThread = class(TThread)
        Shared: TShared;
      protected
        procedure Execute; override;
      end;
    procedure TIncThread.Execute;
    var I: Integer;
    begin
      for I := 0 to 999 do
      begin
        Self.Shared.CS.Enter;
        Self.Shared.Counter := Self.Shared.Counter + 1;
        Self.Shared.CS.Leave
      end
    end;
    var
      S: TShared;
      A, B: TIncThread;
    begin
      S := TShared.Create();
      S.Counter := 0;
      S.CS := TCriticalSection.Create();
      A := TIncThread.Create(True);
      B := TIncThread.Create(True);
      A.Shared := S;
      B.Shared := S;
      A.Start();
      B.Start();
      A.WaitFor();
      B.WaitFor();
      WriteLn(S.Counter)
    end.
    ''';

  SrcDestroyCleanExit =
    '''
    program P;
    uses Classes;
    type
      TMyThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TMyThread.Execute;
    begin
      WriteLn('ran')
    end;
    var T: TMyThread;
    begin
      T := TMyThread.Create(True);
      T.Start();
      T.WaitFor();
      WriteLn('clean')
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EThreadingTests.TestRun_Thread_BasicExecute;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcBasicExecute, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'worker' + LE + 'main' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_WaitForBlocksUntilDone;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcWaitForBlocks, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'slow-done' + LE + 'after-wait' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_Terminate_Flag;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTerminateFlag, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'True' + LE + 'ok' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_FinishedAfterExecute;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcFinishedFlag, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'False' + LE + 'True' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_MultipleThreads;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMultipleThreads, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '6' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_CriticalSection_MutexProtectsCounter;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCriticalSection, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '2000' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_InheritedDestroy_CleanExit;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDestroyCleanExit, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'ran' + LE + 'clean' + LE, Output)
end;

const
  SrcThreadVarMain =
    '''
    program P;
    threadvar
      Counter: Integer;
    begin
      Counter := 42;
      WriteLn(Counter)
    end.
    ''';

procedure TE2EThreadingTests.TestRun_ThreadVar_MainThread_ReadWrite;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcThreadVarMain, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '42' + LE, Output)
end;

const
  SrcThreadVarMixed =
    '''
    program P;
    var
      G: Integer;
    threadvar
      T: Integer;
    begin
      G := 10;
      T := 20;
      WriteLn(G + T)
    end.
    ''';

procedure TE2EThreadingTests.TestRun_ThreadVar_MixedWithGlobalVar;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcThreadVarMixed, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '30' + LE, Output)
end;

const
  { A RECORD-typed threadvar mutated and read back per-thread.  Each thread
    stamps its own id into the record-field threadvar, then spins re-reading it
    and asserting it never changes.  If the record threadvar is addressed
    statically (leaq Name(%rip)) instead of via TLS (%fs:0 + @tpoff), all
    threads share one slot and clobber each other -> 'CORRUPT'.  Scalar
    threadvars already use TLS; the bug was that record/aggregate threadvar
    field access bypassed it. }
  SrcThreadVarRecordIsolation =
    '''
    program P;
    uses Classes;
    type
      TRec = record
        Tag: Integer;
      end;
      TStampThread = class(TThread)
        MyId: Integer;
      protected
        procedure Execute; override;
      end;
    threadvar
      TVR: TRec;
    var
      Corrupt: Integer;
    procedure TStampThread.Execute;
    var I: Integer;
    begin
      TVR.Tag := Self.MyId;
      for I := 0 to 200000 do
        if TVR.Tag <> Self.MyId then
        begin
          Corrupt := 1;
          Exit
        end
    end;
    var
      A, B, C: TStampThread;
    begin
      Corrupt := 0;
      A := TStampThread.Create(True);
      B := TStampThread.Create(True);
      C := TStampThread.Create(True);
      A.MyId := 11;
      B.MyId := 22;
      C.MyId := 33;
      A.Start();
      B.Start();
      C.Start();
      A.WaitFor();
      B.WaitFor();
      C.WaitFor();
      if Corrupt = 0 then
        WriteLn('ok')
      else
        WriteLn('CORRUPT')
    end.
    ''';

procedure TE2EThreadingTests.TestRun_ThreadVar_RecordField_PerThreadIsolation;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcThreadVarRecordIsolation, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'ok' + LE, Output)
end;

const
  { Same per-thread isolation guarantee, but the record threadvar is accessed
    through METHOD CALLS (GR.Put / GR.Get) rather than direct field access.  The
    method-call receiver ladder loads the record base too, and used the same
    static `leaq Name(%rip)` for a global receiver — so this exercises the
    receiver-load path specifically. }
  SrcThreadVarRecordMethod =
    '''
    program P;
    uses Classes;
    type
      TRec = record
        N: Integer;
        procedure Put(V: Integer);
        function Get: Integer;
      end;
      TStampThread = class(TThread)
        MyId: Integer;
      protected
        procedure Execute; override;
      end;
    procedure TRec.Put(V: Integer);
    begin
      N := V
    end;
    function TRec.Get: Integer;
    begin
      Result := N
    end;
    threadvar
      GR: TRec;
    var
      Corrupt: Integer;
    procedure TStampThread.Execute;
    var I: Integer;
    begin
      GR.Put(Self.MyId);
      for I := 0 to 200000 do
        if GR.Get() <> Self.MyId then
        begin
          Corrupt := 1;
          Exit
        end
    end;
    var
      A, B, C: TStampThread;
    begin
      Corrupt := 0;
      A := TStampThread.Create(True);
      B := TStampThread.Create(True);
      C := TStampThread.Create(True);
      A.MyId := 11;
      B.MyId := 22;
      C.MyId := 33;
      A.Start();
      B.Start();
      C.Start();
      A.WaitFor();
      B.WaitFor();
      C.WaitFor();
      if Corrupt = 0 then
        WriteLn('ok')
      else
        WriteLn('CORRUPT')
    end.
    ''';

procedure TE2EThreadingTests.TestRun_ThreadVar_RecordMethod_PerThreadIsolation;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcThreadVarRecordMethod, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'ok' + LE, Output)
end;

const
  { @ThreadVar must be the PER-THREAD address.  The native backend used a
    static leaq Name(%rip) for the address-of form (value access was already
    TLS-correct), so every thread's @TV aliased one slot: a write through
    the pointer landed in the shared slot while the TLS read saw the
    thread's own zero-initialised copy -> 'CORRUPT'.  Also asserts the
    addresses observed by concurrent threads are pairwise distinct — the
    property runtime.mem's MyTid identity relies on. }
  SrcThreadVarAddressOf =
    '''
    program P;
    uses Classes;
    type
      TAddrThread = class(TThread)
        MyId: Int64;
        Slot: Integer;
      protected
        procedure Execute; override;
      end;
    threadvar
      TV: Int64;
    var
      Corrupt: Integer;
      Addrs: array[0..2] of Int64;
    procedure TAddrThread.Execute;
    var
      P: ^Int64;
      I: Integer;
    begin
      P := @TV;
      Addrs[Self.Slot] := Int64(PtrUInt(P));
      P^ := Self.MyId;
      for I := 0 to 200000 do
        if TV <> Self.MyId then
        begin
          Corrupt := 1;
          Exit
        end
    end;
    var
      A, B, C: TAddrThread;
    begin
      Corrupt := 0;
      A := TAddrThread.Create(True);
      B := TAddrThread.Create(True);
      C := TAddrThread.Create(True);
      A.MyId := 11; A.Slot := 0;
      B.MyId := 22; B.Slot := 1;
      C.MyId := 33; C.Slot := 2;
      A.Start();
      B.Start();
      C.Start();
      A.WaitFor();
      B.WaitFor();
      C.WaitFor();
      if (Addrs[0] = Addrs[1]) or (Addrs[0] = Addrs[2])
         or (Addrs[1] = Addrs[2]) then
        Corrupt := 2;
      if Corrupt = 0 then
        WriteLn('ok')
      else
        WriteLn('CORRUPT ' + IntToStr(Corrupt))
    end.
    ''';

procedure TE2EThreadingTests.TestRun_ThreadVar_AddressOf_PerThreadIsolation;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcThreadVarAddressOf, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'ok' + LE, Output)
end;

const
  SrcPerThreadAlloc =
    '''
    program P;
    uses Classes;
    type
      TAllocThread = class(TThread)
      private
        FOk: Integer;
      protected
        procedure Execute; override;
      end;
    procedure TAllocThread.Execute;
    var
      P1, P2: Pointer;
      I1, I2: ^Integer;
    begin
      P1 := GetMem(32);
      P2 := GetMem(64);
      I1 := P1;
      I2 := P2;
      I1^ := 111;
      I2^ := 222;
      if (I1^ = 111) and (I2^ = 222) then
        Self.FOk := 1
      else
        Self.FOk := 0;
      FreeMem(P2);
      FreeMem(P1)
    end;
    var
      A, B: TAllocThread;
    begin
      A := TAllocThread.Create(True);
      B := TAllocThread.Create(True);
      A.FOk := 0;
      B.FOk := 0;
      A.Start();
      B.Start();
      A.WaitFor();
      B.WaitFor();
      WriteLn(A.FOk + B.FOk)
    end.
    ''';

procedure TE2EThreadingTests.TestRun_PerThreadAllocator_IndependentAllocs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcPerThreadAlloc, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '2' + LE, Output)
end;

const
  SrcAtomicARC =
    '''
    program P;
    uses Classes;
    type
      TSharedData = class
        Value: Integer;
      end;
      TArcThread = class(TThread)
        Shared: TSharedData;
      protected
        procedure Execute; override;
      end;
    procedure TArcThread.Execute;
    var
      Local: TSharedData;
      I: Integer;
    begin
      for I := 0 to 999 do
      begin
        Local := Self.Shared;
        if Local.Value <> 42 then
        begin
          WriteLn('CORRUPT');
          Exit
        end;
        Local := nil
      end
    end;
    var
      S: TSharedData;
      A, B, C: TArcThread;
    begin
      S := TSharedData.Create();
      S.Value := 42;
      A := TArcThread.Create(True);
      B := TArcThread.Create(True);
      C := TArcThread.Create(True);
      A.Shared := S;
      B.Shared := S;
      C.Shared := S;
      A.Start();
      B.Start();
      C.Start();
      A.WaitFor();
      B.WaitFor();
      C.WaitFor();
      WriteLn('ok')
    end.
    ''';

procedure TE2EThreadingTests.TestRun_AtomicARC_SharedObject_NoCorruption;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcAtomicARC, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'ok' + LE, Output)
end;

initialization
  RegisterTest(TE2EThreadingTests);

end.
