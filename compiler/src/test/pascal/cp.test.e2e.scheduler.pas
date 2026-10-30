{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.scheduler;

{ E2E tests for L1 of the fiber runtime (docs/async-networking-design.adoc,
  [#scheduler]): the single-worker scheduler in
  stdlib/src/main/pascal/async.fibers.pas — SpawnFiber/RunScheduler/
  FiberYield/FiberSleep over the timer heap, plus the root exception frame
  and cancellation at the suspension point.

  BACKEND POSTURE: async.fibers pulls in the inline-asm context leaf, so all
  tests run on the NATIVE backend only (the QBE-rejection guard test lives in
  cp.test.e2e.fibers). }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TSchedulerE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Slice 2 — scheduler core: run queue, yield, timers, drain. }
    procedure TestScheduler_YieldRoundRobin_Deterministic;
    procedure TestScheduler_SleepOrdering_TimersFireInDeadlineOrder;
    procedure TestScheduler_FiberSpawnsFibers;
    procedure TestScheduler_Smoke10kFibers_DrainsToCompletion;

    { Slice 3 — root exception frame + cancellation. }
    procedure TestScheduler_UnhandledException_ContainedByRootFrame;
    procedure TestScheduler_CancelSleeping_RaisesAtSuspensionPoint;
    procedure TestScheduler_CancelUncaught_RunsFinally_SchedulerSurvives;

    { L1 multicore — N worker threads, work-stealing, channel hand-off. }
    procedure TestScheduler_Multicore_AllFibersCompleteAcrossWorkers;

    { Persistent worker-thread pool — two batches on ONE pool. }
    procedure TestScheduler_Pool_TwoBatchesOnOnePool;
  end;

implementation

const
  LE = #10;

  { Three fibers yield in a loop: the FIFO run queue must interleave them
    deterministically (spawn order, round-robin), RunScheduler must return
    once all are done, and the handles must read fsDone. }
  SrcYieldRoundRobin =
    '''
    program schedyield;
    uses async.fibers;
    var
      T0, T1, T2: TFiberTask;
    procedure Worker(AArg: Pointer);
    var
      I: Int;
    begin
      for I := 0 to 2 do
      begin
        WriteLn('F', Int32(AArg), ':', I);
        FiberYield();
      end;
    end;
    begin
      T0 := SpawnFiber(@Worker, Pointer(0));
      T1 := SpawnFiber(@Worker, Pointer(1));
      T2 := SpawnFiber(@Worker, Pointer(2));
      RunScheduler();
      if (T0.State = fsDone) and (T1.State = fsDone) and (T2.State = fsDone) then
        WriteLn('ALLDONE');
      WriteLn('LIVE=', SchedulerLiveCount());
    end.
    ''';

  { Three fibers sleep 30/10/20 ms: the timer heap must wake them in
    deadline order (10, 20, 30), not spawn order. }
  SrcSleepOrdering =
    '''
    program schedsleep;
    uses async.fibers;
    procedure Sleeper(AArg: Pointer);
    begin
      FiberSleep(Int64(AArg));
      WriteLn('S', Int64(AArg));
    end;
    var
      A, B, C: TFiberTask;
    begin
      A := SpawnFiber(@Sleeper, Pointer(30));
      B := SpawnFiber(@Sleeper, Pointer(10));
      C := SpawnFiber(@Sleeper, Pointer(20));
      RunScheduler();
      WriteLn('M');
    end.
    ''';

  { A running fiber spawns two children mid-run; they join the run queue
    behind it and the scheduler drains all three. }
  SrcFiberSpawnsFibers =
    '''
    program schedspawn;
    uses async.fibers;
    var
      C1, C2: TFiberTask;
    procedure Child(AArg: Pointer);
    begin
      WriteLn('C', Int32(AArg));
    end;
    procedure Parent(AArg: Pointer);
    begin
      WriteLn('P:start');
      C1 := SpawnFiber(@Child, Pointer(1));
      C2 := SpawnFiber(@Child, Pointer(2));
      FiberYield();
      WriteLn('P:end');
    end;
    var
      P: TFiberTask;
    begin
      P := SpawnFiber(@Parent, nil);
      RunScheduler();
      WriteLn('M');
    end.
    ''';

  { Bounded single-worker smoke (the design's 100k joint stress is the P2
    gate re-run; this is the L1-scoped 10k form): 10k fibers on small
    stacks each yield once and bump a counter; the scheduler must drain to
    completion and return. }
  SrcSmoke10k =
    '''
    program schedsmoke;
    uses async.fibers;
    var
      Counter: Int;
    procedure Work(AArg: Pointer);
    begin
      FiberYield();
      Counter := Counter + 1;
    end;
    var
      I: Int;
      T: TFiberTask;
    begin
      Counter := 0;
      for I := 0 to 9999 do
        T := SpawnFiber(@Work, nil, 8192);
      RunScheduler();
      WriteLn('COUNT=', Counter);
      WriteLn('LIVE=', SchedulerLiveCount());
    end.
    ''';

  { Root exception frame (design [#scheduler-cancellation] / the L0 open
    item): an exception that escapes a fiber's entry procedure must be
    contained — the fiber reads fsFailed with the message recorded, the
    OTHER fibers keep running, and RunScheduler returns normally. }
  SrcUnhandledContained =
    '''
    program schedexc;
    uses async.fibers, SysUtils;
    procedure Boomer(AArg: Pointer);
    begin
      WriteLn('B:pre');
      raise Exception.Create('boom');
    end;
    procedure Steady(AArg: Pointer);
    var
      I: Int;
    begin
      for I := 0 to 1 do
      begin
        WriteLn('S', I);
        FiberYield();
      end;
    end;
    var
      TB, TS: TFiberTask;
    begin
      TB := SpawnFiber(@Boomer, nil);
      TS := SpawnFiber(@Steady, nil);
      RunScheduler();
      if TB.State = fsFailed then
        WriteLn('FAILED:', TB.FailMessage);
      if TS.State = fsDone then
        WriteLn('STEADY:done');
      WriteLn('M');
    end.
    ''';

  { Cancelling a parked fiber wakes it from the timer heap and raises
    EFiberCancelled at the suspension point (inside FiberSleep), so the
    fiber's own except handler runs on its own stack — the long 10 s sleep
    must NOT elapse. }
  SrcCancelSleeping =
    '''
    program schedcancel;
    uses async.fibers;
    var
      TSleep: TFiberTask;
    procedure Sleepy(AArg: Pointer);
    begin
      try
        WriteLn('S:pre');
        FiberSleep(10000);
        WriteLn('S:post');
      except
        on E: EFiberCancelled do WriteLn('S:cancelled');
      end;
    end;
    procedure Canceller(AArg: Pointer);
    begin
      FiberSleep(20);
      FiberCancel(TSleep);
      WriteLn('C:cancelled-it');
    end;
    var
      TC: TFiberTask;
    begin
      TSleep := SpawnFiber(@Sleepy, nil);
      TC := SpawnFiber(@Canceller, nil);
      RunScheduler();
      if TSleep.State = fsDone then
        WriteLn('SLEEPY:done');
      WriteLn('M');
    end.
    ''';

  { An UNCAUGHT EFiberCancelled unwinds the fiber through its try/finally
    (releasing what it holds — the P1 coupling) into the root frame, which
    marks it fsCancelled; the scheduler survives and drains the rest. }
  SrcCancelUncaught =
    '''
    program schedcancel2;
    uses async.fibers;
    var
      TSleep: TFiberTask;
    procedure Sleepy(AArg: Pointer);
    begin
      try
        WriteLn('S:pre');
        FiberSleep(10000);
        WriteLn('S:post');
      finally
        WriteLn('S:fin');
      end;
    end;
    procedure Canceller(AArg: Pointer);
    begin
      FiberSleep(20);
      FiberCancel(TSleep);
      WriteLn('C:cancelled-it');
    end;
    var
      TC: TFiberTask;
    begin
      TSleep := SpawnFiber(@Sleepy, nil);
      TC := SpawnFiber(@Canceller, nil);
      RunScheduler();
      if TSleep.State = fsCancelled then
        WriteLn('SLEEPY:cancelled');
      if TC.State = fsDone then
        WriteLn('CANCELLER:done');
      WriteLn('M');
    end.
    ''';

  { L1 multicore: spawn many fibers, run them across N worker OS threads with
    work-stealing, hand every fiber's value through a bounded channel to a
    single drain fiber, and print the atomic tally + sum.  Interleaving is
    non-deterministic across workers, so the program asserts on COUNTS
    (order-independent) — the whole point of the e2e is that the native
    codegen + pthread + RTL stack produces the right totals, which the
    IR/stdlib harness cannot see. }
  SrcMulticore =
    '''
    program schedmc;
    uses async.fibers, async.sync, runtime.atomic;
    var
      GDone: Int;
      GSum: Int;
      GCh: TChannel<Int>;
    procedure Worker(AArg: Pointer);
    var
      V: Int;
    begin
      FiberYield();
      V := Int32(AArg);
      GCh.Send(V);
      _AtomicAddInt32(@GDone, 1);
    end;
    procedure Drain(AArg: Pointer);
    var
      V, Got: Int;
    begin
      Got := 0;
      while Got < 200 do
      begin
        if GCh.Recv(V) then
        begin
          _AtomicAddInt32(@GSum, V);
          Got := Got + 1;
        end
        else
          Break;
      end;
    end;
    var
      I: Int;
    begin
      GDone := 0;
      GSum := 0;
      GCh := TChannel<Int>.Create(16);
      SpawnFiber(@Drain, nil);
      for I := 0 to 199 do
        SpawnFiber(@Worker, Pointer(I + 1));
      RunSchedulerMC(4);
      GCh.Free();
      WriteLn('DONE=', GDone);
      WriteLn('SUM=', GSum);
      WriteLn('LIVE=', SchedulerLiveCount());
    end.
    ''';

  { Persistent pool: create the pool ONCE, run TWO batches on it (spawn +
    FiberPoolRun each), then shut down.  The second batch must run on the SAME
    peer threads without recreating them.  Each batch tallies via an atomic
    counter and hands values through a channel to a drain fiber; the program
    prints per-batch totals so the e2e pins that the native + pthread + RTL
    stack drives repeated batches on one pool correctly (the stdlib harness
    cannot exercise the compile->QBE-reject->native path). }
  SrcPoolTwoBatches =
    '''
    program schedpool;
    uses async.fibers, async.sync, runtime.atomic;
    var
      GDone: Int;
      GSum: Int;
      GCh: TChannel<Int>;
    procedure Worker(AArg: Pointer);
    var
      V: Int;
    begin
      FiberYield();
      V := Int32(AArg);
      GCh.Send(V);
      _AtomicAddInt32(@GDone, 1);
    end;
    procedure Drain(AArg: Pointer);
    var
      V, Got: Int;
    begin
      Got := 0;
      while Got < Int32(AArg) do
      begin
        if GCh.Recv(V) then
        begin
          _AtomicAddInt32(@GSum, V);
          Got := Got + 1;
        end
        else
          Break;
      end;
    end;
    procedure RunBatch(ACount: Int);
    var
      I: Int;
    begin
      GDone := 0;
      GSum := 0;
      GCh := TChannel<Int>.Create(16);
      SpawnFiber(@Drain, Pointer(ACount));
      for I := 0 to ACount - 1 do
        SpawnFiber(@Worker, Pointer(I + 1));
      FiberPoolRun();
      GCh.Free();
      WriteLn('BATCH DONE=', GDone, ' SUM=', GSum);
    end;
    begin
      FiberPoolStart(4);
      if FiberPoolIsActive() then
        WriteLn('POOL:active');
      RunBatch(100);
      RunBatch(50);
      FiberPoolShutdown();
      if not FiberPoolIsActive() then
        WriteLn('POOL:down');
      WriteLn('LIVE=', SchedulerLiveCount());
    end.
    ''';

procedure TSchedulerE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-scheduler')
end;

procedure TSchedulerE2ETests.TestScheduler_YieldRoundRobin_Deterministic;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'sched-yield', SrcYieldRoundRobin,
    'F0:0' + LE + 'F1:0' + LE + 'F2:0' + LE +
    'F0:1' + LE + 'F1:1' + LE + 'F2:1' + LE +
    'F0:2' + LE + 'F1:2' + LE + 'F2:2' + LE +
    'ALLDONE' + LE + 'LIVE=0' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_SleepOrdering_TimersFireInDeadlineOrder;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'sched-sleep', SrcSleepOrdering,
    'S10' + LE + 'S20' + LE + 'S30' + LE + 'M' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_FiberSpawnsFibers;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'sched-spawn', SrcFiberSpawnsFibers,
    'P:start' + LE + 'C1' + LE + 'C2' + LE + 'P:end' + LE + 'M' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_Smoke10kFibers_DrainsToCompletion;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'sched-smoke', SrcSmoke10k,
    'COUNT=10000' + LE + 'LIVE=0' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_UnhandledException_ContainedByRootFrame;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'sched-exc', SrcUnhandledContained,
    'B:pre' + LE + 'S0' + LE + 'S1' + LE +
    'FAILED:boom' + LE + 'STEADY:done' + LE + 'M' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_CancelSleeping_RaisesAtSuspensionPoint;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'sched-cancel', SrcCancelSleeping,
    'S:pre' + LE + 'C:cancelled-it' + LE + 'S:cancelled' + LE +
    'SLEEPY:done' + LE + 'M' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_CancelUncaught_RunsFinally_SchedulerSurvives;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'sched-cancel-uncaught', SrcCancelUncaught,
    'S:pre' + LE + 'C:cancelled-it' + LE + 'S:fin' + LE +
    'SLEEPY:cancelled' + LE + 'CANCELLER:done' + LE + 'M' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_Multicore_AllFibersCompleteAcrossWorkers;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 200 fibers over 4 worker threads + a channel drain: every fiber completes
    (DONE=200), every value is delivered (SUM = 1+..+200 = 20100), and the
    scheduler drains (LIVE=0).  Order-independent because interleaving across
    workers is non-deterministic. }
  AssertRTLRunsOnOne(beNative, 'sched-mc', SrcMulticore,
    'DONE=200' + LE + 'SUM=20100' + LE + 'LIVE=0' + LE, 0)
end;

procedure TSchedulerE2ETests.TestScheduler_Pool_TwoBatchesOnOnePool;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Batch 1: 100 fibers -> DONE=100, SUM=1+..+100=5050.
    Batch 2 on the SAME pool: 50 fibers -> DONE=50, SUM=1+..+50=1275.
    Pool active between start/shutdown, down after, and nothing left live. }
  AssertRTLRunsOnOne(beNative, 'sched-pool', SrcPoolTwoBatches,
    'POOL:active' + LE +
    'BATCH DONE=100 SUM=5050' + LE +
    'BATCH DONE=50 SUM=1275' + LE +
    'POOL:down' + LE + 'LIVE=0' + LE, 0)
end;

initialization
  RegisterTest(TSchedulerE2ETests);

end.
