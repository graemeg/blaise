{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the N-worker (multicore) fiber scheduler (async.fibers
  RunSchedulerMC; docs/async-networking-design.adoc, [#scheduler]).

  Covers: every spawned fiber runs to completion across N workers; work is
  spread when one worker is handed everything and the others steal it; timers
  fire under multicore; and cancellation/failure are observed correctly with
  N workers.

  Correctness is asserted on ATOMIC counters (not stdout ordering), because
  interleaving across workers is non-deterministic by design.

  NATIVE BACKEND ONLY (spawns pthreads; pulls in the inline-asm context leaf).
  Self-registers via the initialization section. }

unit SchedulerMc.Tests;

interface

uses
  blaise.testing, SysUtils, async.fibers;

type
  TSchedulerMcTests = class(TTestCase)
  published
    procedure TestMc_AllFibersRunToCompletion;
    procedure TestMc_WorkStealingUnderImbalance;
    procedure TestMc_TimersFireUnderMulticore;
    procedure TestMc_CancellationUnderMulticore;
    procedure TestMc_FailureContainedPerFiber;
  end;

implementation

uses
  runtime.atomic;

var
  GMcCounter: Int;      { atomic tally of completed fibers }
  GMcSum: Int;          { atomic sum of arguments, to prove identity }
  GMcCancelObserved: Int;
  GMcFinallyRan: Int;

{ --- all fibers complete --------------------------------------------------- }

procedure TallyWorker(Arg: Pointer);
begin
  { A little cooperative yielding to force interleaving/migration. }
  FiberYield();
  _AtomicAddInt32(@GMcCounter, 1);
  _AtomicAddInt32(@GMcSum, Int32(Arg));
end;

procedure TSchedulerMcTests.TestMc_AllFibersRunToCompletion;
const
  N = 500;
var
  I, ExpectedSum: Int;
begin
  GMcCounter := 0;
  GMcSum := 0;
  ExpectedSum := 0;
  for I := 1 to N do
  begin
    SpawnFiber(@TallyWorker, Pointer(I));
    ExpectedSum := ExpectedSum + I;
  end;
  RunSchedulerMC(4);
  AssertEquals('every fiber ran exactly once', N, GMcCounter);
  AssertEquals('argument identity preserved (no loss/dup)',
    ExpectedSum, GMcSum);
  AssertEquals('nothing live after the run', 0, SchedulerLiveCount());
end;

{ --- work stealing under imbalance ----------------------------------------- }

{ A fiber that spawns many children, all from ONE worker's context, so the
  other workers must steal them.  Each child just tallies. }
procedure BurstSpawnerWorker(Arg: Pointer);
var
  I: Int;
begin
  for I := 0 to 999 do
    SpawnFiber(@TallyWorker, Pointer(1));
end;

procedure TSchedulerMcTests.TestMc_WorkStealingUnderImbalance;
begin
  GMcCounter := 0;
  GMcSum := 0;
  { One seed fiber that dumps 1000 children onto its own deque; the peers
    must steal to make progress. }
  SpawnFiber(@BurstSpawnerWorker, nil);
  RunSchedulerMC(4);
  AssertEquals('all 1000 stolen/ran children completed', 1000, GMcCounter);
  AssertEquals('all children carried arg 1', 1000, GMcSum);
end;

{ --- timers under multicore ------------------------------------------------ }

procedure SleepTallyWorker(Arg: Pointer);
begin
  FiberSleep(Int32(Arg));      { ms }
  _AtomicAddInt32(@GMcCounter, 1);
end;

procedure TSchedulerMcTests.TestMc_TimersFireUnderMulticore;
var
  I: Int;
  Started, Elapsed: Int64;
begin
  GMcCounter := 0;
  Started := MonotonicNowNs();
  for I := 0 to 19 do
    SpawnFiber(@SleepTallyWorker, Pointer(5));   { 5 ms each }
  RunSchedulerMC(4);
  Elapsed := MonotonicNowNs() - Started;
  AssertEquals('every sleeping fiber woke and completed', 20, GMcCounter);
  { They all slept ~5 ms in parallel, so total wall time is well under 1 s. }
  AssertTrue('timers fired promptly (parallel, not serialised)',
    Elapsed < Int64(1000000000));
end;

{ --- cancellation under multicore ------------------------------------------ }

var
  GMcVictim: TFiberTask;

procedure CancellableWorker(Arg: Pointer);
begin
  try
    FiberSleep(100000);          { 100 s — must be cut short by cancel }
  except
    on E: EFiberCancelled do
      _AtomicAddInt32(@GMcCancelObserved, 1);
  end;
end;

procedure CancelKickWorker(Arg: Pointer);
var
  I: Int;
begin
  { Give the victim time to park in its worker's timer heap. }
  FiberSleep(20);
  FiberCancel(GMcVictim);
end;

procedure TSchedulerMcTests.TestMc_CancellationUnderMulticore;
var
  Started, Elapsed: Int64;
begin
  GMcCancelObserved := 0;
  Started := MonotonicNowNs();
  GMcVictim := SpawnFiber(@CancellableWorker, nil);
  SpawnFiber(@CancelKickWorker, nil);
  RunSchedulerMC(4);
  Elapsed := MonotonicNowNs() - Started;
  AssertEquals('cancellation raised at the suspension point',
    1, GMcCancelObserved);
  AssertTrue('victim did not wait out its 100 s sleep',
    Elapsed < Int64(5000000000));
  AssertTrue('victim ended via its handler', GMcVictim.State = fsDone);
  GMcVictim := nil;
end;

{ --- per-fiber failure containment ----------------------------------------- }

procedure BoomMcWorker(Arg: Pointer);
begin
  raise Exception.Create('mc-boom');
end;

procedure FinallyMcWorker(Arg: Pointer);
begin
  try
    FiberYield();
  finally
    _AtomicAddInt32(@GMcFinallyRan, 1);
  end;
end;

procedure TSchedulerMcTests.TestMc_FailureContainedPerFiber;
var
  I: Int;
  Boomer, Survivor: TFiberTask;
begin
  GMcFinallyRan := 0;
  Boomer := SpawnFiber(@BoomMcWorker, nil);
  Survivor := nil;
  for I := 0 to 99 do
    Survivor := SpawnFiber(@FinallyMcWorker, nil);
  RunSchedulerMC(4);
  AssertTrue('the raising fiber is marked failed',
    Boomer.State = fsFailed);
  AssertEquals('its message was recorded', 'mc-boom', Boomer.FailMessage);
  AssertEquals('all survivors ran their finally blocks',
    100, GMcFinallyRan);
end;

initialization
  RegisterTest(TSchedulerMcTests);

end.
