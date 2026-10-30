{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the L1 fiber scheduler's intrinsic structures
  (docs/async-networking-design.adoc, [#scheduler]): the 4-ary timer
  min-heap keyed by absolute monotonic deadline, the intrusive FIFO run
  queue, and the monotonic clock helper (async.fibers).

  NATIVE BACKEND ONLY: async.fibers pulls in the inline-asm context leaf,
  so this suite (like the runner that hosts it) must be built with the
  native backend (the default).

  Self-registers via the initialization section. }

unit Scheduler.Tests;

interface

uses
  blaise.testing, SysUtils, async.fibers;

type
  TTimerHeapTests = class(TTestCase)
  published
    procedure TestHeap_EmptyState;
    procedure TestHeap_PopsInDeadlineOrder;
    procedure TestHeap_DuplicateDeadlines;
    procedure TestHeap_RemoveMiddleKeepsOrder;
    procedure TestHeap_RemoveMinAndLast;
    procedure TestHeap_HeapIndexClearedOnPop;
  end;

  TRunQueueTests = class(TTestCase)
  published
    procedure TestRunQueue_FifoOrder;
    procedure TestRunQueue_ReuseAfterDrain;
  end;

  TMonotonicClockTests = class(TTestCase)
  published
    procedure TestMonotonicNowNs_NonDecreasing;
  end;

  { In-process scheduler behaviour: SpawnFiber/RunScheduler/FiberYield/
    FiberSleep drive real fiber switches inside the test-runner process.
    Each test ends with ResetScheduler so suites stay independent. }
  TSchedulerTests = class(TTestCase)
  published
    procedure TestRun_YieldRoundRobin;
    procedure TestRun_SleepWakesInDeadlineOrder;
    procedure TestRun_FiberSpawnsFiber;
    procedure TestRun_ZeroSleepIsYield;
    procedure TestRun_ResetAllowsFreshRound;
  end;

  { Root exception frame + cancellation (design [#scheduler-cancellation]):
    an exception escaping a fiber's entry procedure is contained by the
    scheduler's root frame — recorded on the handle, other fibers continue —
    and FiberCancel wakes a parked fiber with EFiberCancelled raised at the
    suspension point. }
  TSchedulerFaultTests = class(TTestCase)
  published
    procedure TestRun_UnhandledException_MarksFailedAndContinues;
    procedure TestRun_CancelSleeping_RaisesAtSuspensionPoint;
    procedure TestRun_CancelUncaught_MarksCancelled_RunsFinally;
    procedure TestRun_CancelBeforeSleep_RaisesImmediately;
  end;

implementation

function MakeTask(ADeadline: Int64): TFiberTask;
var
  T: TFiberTask;
begin
  T := TFiberTask.Create();
  T.Deadline := ADeadline;
  Result := T;
end;

{ --- timer heap ----------------------------------------------------------- }

procedure TTimerHeapTests.TestHeap_EmptyState;
var
  H: TTimerHeap;
begin
  H := TTimerHeap.Create();
  AssertEquals('empty heap count', 0, H.Count);
  AssertTrue('PeekMin on empty is nil', H.PeekMin() = nil);
  AssertTrue('PopMin on empty is nil', H.PopMin() = nil);
end;

procedure TTimerHeapTests.TestHeap_PopsInDeadlineOrder;
var
  H: TTimerHeap;
  T: TFiberTask;
  Deadlines: array[0..8] of Int64;
  I: Int;
  Prev: Int64;
begin
  { Shuffled deadlines; PopMin must return them ascending. }
  Deadlines[0] := 30;
  Deadlines[1] := 10;
  Deadlines[2] := 90;
  Deadlines[3] := 20;
  Deadlines[4] := 70;
  Deadlines[5] := 50;
  Deadlines[6] := 40;
  Deadlines[7] := 80;
  Deadlines[8] := 60;
  H := TTimerHeap.Create();
  for I := 0 to 8 do
    H.Push(MakeTask(Deadlines[I]));
  AssertEquals('heap count after 9 pushes', 9, H.Count);
  AssertEquals('min is 10', 10, Int32(H.PeekMin().Deadline));
  Prev := 0;
  for I := 0 to 8 do
  begin
    T := H.PopMin();
    AssertTrue('pop yields ascending deadlines', T.Deadline > Prev);
    Prev := T.Deadline;
  end;
  AssertEquals('heap drained', 0, H.Count);
end;

procedure TTimerHeapTests.TestHeap_DuplicateDeadlines;
var
  H: TTimerHeap;
  I: Int;
begin
  H := TTimerHeap.Create();
  for I := 0 to 4 do
    H.Push(MakeTask(42));
  for I := 0 to 4 do
    AssertEquals('all duplicates pop with the same key',
      42, Int32(H.PopMin().Deadline));
  AssertEquals('heap drained', 0, H.Count);
end;

procedure TTimerHeapTests.TestHeap_RemoveMiddleKeepsOrder;
var
  H: TTimerHeap;
  Victim: TFiberTask;
  T: TFiberTask;
  I: Int;
  Prev: Int64;
begin
  H := TTimerHeap.Create();
  H.Push(MakeTask(50));
  H.Push(MakeTask(10));
  Victim := MakeTask(30);
  H.Push(Victim);
  H.Push(MakeTask(20));
  H.Push(MakeTask(40));
  H.Remove(Victim);
  AssertEquals('count after remove', 4, H.Count);
  AssertEquals('removed task heap index cleared', -1, Victim.HeapIndex);
  Prev := 0;
  for I := 0 to 3 do
  begin
    T := H.PopMin();
    AssertTrue('order intact after middle removal', T.Deadline > Prev);
    AssertTrue('victim never pops', T <> Victim);
    Prev := T.Deadline;
  end;
end;

procedure TTimerHeapTests.TestHeap_RemoveMinAndLast;
var
  H: TTimerHeap;
  First, Last: TFiberTask;
begin
  H := TTimerHeap.Create();
  First := MakeTask(1);
  Last := MakeTask(99);
  H.Push(MakeTask(5));
  H.Push(First);
  H.Push(Last);
  H.Remove(First);
  AssertEquals('new min after removing the min',
    5, Int32(H.PeekMin().Deadline));
  H.Remove(Last);
  AssertEquals('count after removing the max', 1, H.Count);
  AssertEquals('survivor is the middle key',
    5, Int32(H.PopMin().Deadline));
end;

procedure TTimerHeapTests.TestHeap_HeapIndexClearedOnPop;
var
  H: TTimerHeap;
  T: TFiberTask;
  I: Int;
begin
  { Push descending keys (each push sifts to the root) then verify every
    pop hands back a task with its heap slot cleared — the invariant
    cancellation's Remove depends on. }
  H := TTimerHeap.Create();
  for I := 9 downto 0 do
    H.Push(MakeTask(I * 10 + 5));
  for I := 0 to 9 do
  begin
    T := H.PopMin();
    AssertEquals('index cleared on pop', -1, T.HeapIndex);
  end;
end;

{ --- run queue ------------------------------------------------------------ }

procedure TRunQueueTests.TestRunQueue_FifoOrder;
var
  Q: TRunQueue;
  A, B, C: TFiberTask;
begin
  Q := TRunQueue.Create();
  AssertEquals('empty queue count', 0, Q.Count);
  AssertTrue('pop on empty is nil', Q.Pop() = nil);
  A := MakeTask(0);
  B := MakeTask(0);
  C := MakeTask(0);
  Q.Push(A);
  Q.Push(B);
  Q.Push(C);
  AssertEquals('count after three pushes', 3, Q.Count);
  AssertTrue('FIFO first', Q.Pop() = A);
  AssertTrue('FIFO second', Q.Pop() = B);
  AssertTrue('FIFO third', Q.Pop() = C);
  AssertEquals('drained', 0, Q.Count);
  AssertTrue('pop after drain is nil', Q.Pop() = nil);
end;

procedure TRunQueueTests.TestRunQueue_ReuseAfterDrain;
var
  Q: TRunQueue;
  A, B: TFiberTask;
begin
  Q := TRunQueue.Create();
  A := MakeTask(0);
  B := MakeTask(0);
  Q.Push(A);
  AssertTrue('single pop', Q.Pop() = A);
  Q.Push(B);
  Q.Push(A);
  AssertTrue('reuse first', Q.Pop() = B);
  AssertTrue('reuse second', Q.Pop() = A);
  AssertTrue('link cleared on pop', A.NextReady = nil);
end;

{ --- monotonic clock ------------------------------------------------------ }

procedure TMonotonicClockTests.TestMonotonicNowNs_NonDecreasing;
var
  T1, T2: Int64;
  I: Int;
begin
  T1 := MonotonicNowNs();
  AssertTrue('clock returns a positive value', T1 > 0);
  for I := 0 to 999 do
  begin
    T2 := MonotonicNowNs();
    AssertTrue('clock never goes backwards', T2 >= T1);
    T1 := T2;
  end;
end;

{ --- in-process scheduler runs -------------------------------------------- }

var
  GLog: string;

procedure LogYieldWorker(AArg: Pointer);
var
  I: Int;
begin
  for I := 0 to 1 do
  begin
    GLog := GLog + 'F' + IntToStr(Int32(AArg)) + IntToStr(I) + ' ';
    FiberYield();
  end;
end;

procedure LogSleepWorker(AArg: Pointer);
begin
  FiberSleep(Int64(AArg));
  GLog := GLog + 'S' + IntToStr(Int32(AArg)) + ' ';
end;

procedure LogChildWorker(AArg: Pointer);
begin
  GLog := GLog + 'C ';
end;

procedure LogParentWorker(AArg: Pointer);
var
  T: TFiberTask;
begin
  GLog := GLog + 'P1 ';
  T := SpawnFiber(@LogChildWorker, nil);
  FiberYield();
  GLog := GLog + 'P2 ';
end;

procedure LogZeroSleepWorker(AArg: Pointer);
begin
  GLog := GLog + 'A1 ';
  FiberSleep(0);          { must behave as a yield, not a timer park }
  GLog := GLog + 'A2 ';
end;

procedure TSchedulerTests.TestRun_YieldRoundRobin;
var
  T0, T1: TFiberTask;
begin
  GLog := '';
  T0 := SpawnFiber(@LogYieldWorker, Pointer(0));
  T1 := SpawnFiber(@LogYieldWorker, Pointer(1));
  RunScheduler();
  AssertEquals('deterministic FIFO interleaving',
    'F00 F10 F01 F11 ', GLog);
  AssertTrue('first fiber done', T0.State = fsDone);
  AssertTrue('second fiber done', T1.State = fsDone);
  AssertEquals('nothing live after drain', 0, SchedulerLiveCount());
  ResetScheduler();
end;

procedure TSchedulerTests.TestRun_SleepWakesInDeadlineOrder;
var
  T: TFiberTask;
begin
  GLog := '';
  T := SpawnFiber(@LogSleepWorker, Pointer(15));
  T := SpawnFiber(@LogSleepWorker, Pointer(5));
  T := SpawnFiber(@LogSleepWorker, Pointer(10));
  RunScheduler();
  AssertEquals('timers fire in deadline order, not spawn order',
    'S5 S10 S15 ', GLog);
  ResetScheduler();
end;

procedure TSchedulerTests.TestRun_FiberSpawnsFiber;
var
  T: TFiberTask;
begin
  GLog := '';
  T := SpawnFiber(@LogParentWorker, nil);
  RunScheduler();
  AssertEquals('child runs between parent yield and resume',
    'P1 C P2 ', GLog);
  ResetScheduler();
end;

procedure TSchedulerTests.TestRun_ZeroSleepIsYield;
var
  A, B: TFiberTask;
begin
  GLog := '';
  A := SpawnFiber(@LogZeroSleepWorker, nil);
  B := SpawnFiber(@LogChildWorker, nil);
  RunScheduler();
  AssertEquals('zero sleep requeues behind the other fiber',
    'A1 C A2 ', GLog);
  ResetScheduler();
end;

procedure TSchedulerTests.TestRun_ResetAllowsFreshRound;
var
  T: TFiberTask;
begin
  GLog := '';
  T := SpawnFiber(@LogChildWorker, nil);
  RunScheduler();
  ResetScheduler();
  AssertEquals('live count clean after reset', 0, SchedulerLiveCount());
  T := SpawnFiber(@LogChildWorker, nil);
  RunScheduler();
  AssertEquals('both rounds ran', 'C C ', GLog);
  AssertTrue('second round fiber done', T.State = fsDone);
  ResetScheduler();
end;

{ --- root exception frame + cancellation ----------------------------------- }

var
  GVictim: TFiberTask;

procedure BoomWorker(AArg: Pointer);
begin
  GLog := GLog + 'B1 ';
  raise Exception.Create('boom');
end;

procedure CaughtCancelWorker(AArg: Pointer);
begin
  try
    GLog := GLog + 'V1 ';
    FiberSleep(10000);
    GLog := GLog + 'V2 ';
  except
    on E: EFiberCancelled do
      GLog := GLog + 'Vcancelled ';
  end;
end;

procedure UncaughtCancelWorker(AArg: Pointer);
begin
  try
    GLog := GLog + 'V1 ';
    FiberSleep(10000);
    GLog := GLog + 'V2 ';
  finally
    GLog := GLog + 'Vfin ';
  end;
end;

procedure CancellerWorker(AArg: Pointer);
begin
  FiberSleep(5);
  FiberCancel(GVictim);
  GLog := GLog + 'K ';
end;

procedure PreCancelledWorker(AArg: Pointer);
begin
  try
    FiberYield();          { canceller runs here and flags us }
    GLog := GLog + 'P1 ';
    FiberSleep(10000);     { must raise immediately, never park }
    GLog := GLog + 'P2 ';
  except
    on E: EFiberCancelled do
      GLog := GLog + 'Pcancelled ';
  end;
end;

procedure ImmediateCancellerWorker(AArg: Pointer);
begin
  FiberCancel(GVictim);
  GLog := GLog + 'K ';
end;

procedure TSchedulerFaultTests.TestRun_UnhandledException_MarksFailedAndContinues;
var
  TB, TS: TFiberTask;
begin
  GLog := '';
  TB := SpawnFiber(@BoomWorker, nil);
  TS := SpawnFiber(@LogYieldWorker, Pointer(7));
  RunScheduler();
  AssertEquals('boomer ran, then survivor kept running',
    'B1 F70 F71 ', GLog);
  AssertTrue('raising fiber marked failed', TB.State = fsFailed);
  AssertEquals('exception message recorded', 'boom', TB.FailMessage);
  AssertTrue('other fiber unaffected', TS.State = fsDone);
  AssertEquals('scheduler drained', 0, SchedulerLiveCount());
  ResetScheduler();
end;

procedure TSchedulerFaultTests.TestRun_CancelSleeping_RaisesAtSuspensionPoint;
var
  Started: Int64;
  TK: TFiberTask;
begin
  GLog := '';
  Started := MonotonicNowNs();
  GVictim := SpawnFiber(@CaughtCancelWorker, nil);
  TK := SpawnFiber(@CancellerWorker, nil);
  RunScheduler();
  AssertEquals('handler ran at the suspension point, canceller first',
    'V1 K Vcancelled ', GLog);
  AssertTrue('caught cancellation completes the fiber normally',
    GVictim.State = fsDone);
  AssertTrue('the 10 s park did not elapse',
    MonotonicNowNs() - Started < Int64(5000000000));
  GVictim := nil;
  ResetScheduler();
end;

procedure TSchedulerFaultTests.TestRun_CancelUncaught_MarksCancelled_RunsFinally;
var
  TK: TFiberTask;
begin
  GLog := '';
  GVictim := SpawnFiber(@UncaughtCancelWorker, nil);
  TK := SpawnFiber(@CancellerWorker, nil);
  RunScheduler();
  AssertEquals('finally ran during the cancellation unwind',
    'V1 K Vfin ', GLog);
  AssertTrue('uncaught cancellation marks fsCancelled',
    GVictim.State = fsCancelled);
  GVictim := nil;
  ResetScheduler();
end;

procedure TSchedulerFaultTests.TestRun_CancelBeforeSleep_RaisesImmediately;
var
  TK: TFiberTask;
begin
  GLog := '';
  GVictim := SpawnFiber(@PreCancelledWorker, nil);
  TK := SpawnFiber(@ImmediateCancellerWorker, nil);
  RunScheduler();
  AssertEquals('pre-flagged fiber raises on its next park attempt',
    'K P1 Pcancelled ', GLog);
  AssertTrue('victim completed via its handler', GVictim.State = fsDone);
  GVictim := nil;
  ResetScheduler();
end;

initialization
  RegisterTest(TTimerHeapTests);
  RegisterTest(TRunQueueTests);
  RegisterTest(TMonotonicClockTests);
  RegisterTest(TSchedulerTests);
  RegisterTest(TSchedulerFaultTests);

end.
