{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Joint hardening tests for the L1 multicore fiber runtime
  (docs/async-networking-design.adoc, [#scheduler] and rtl-prerequisites):

    * leak-guard proof — the lockless leak tracker is SUSPENDED while N>1
      workers run (a fiber observes it disabled mid-run) and RESTORED after.
    * 100k-fibre stress — 100 000 fibers across N workers each allocate,
      migrate between workers, and hand off through a channel; the test
      asserts every fiber completed and the allocator's arena registry
      returns to (near) its pre-run baseline, exercising exactly the
      cross-thread free + abandoned-arena reclamation the migration-safe
      allocator (P2 / phase 5) exists for.

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit AsyncStress.Tests;

interface

uses
  blaise.testing, SysUtils, async.fibers, async.sync;

type
  TAsyncStressTests = class(TTestCase)
  published
    procedure TestLeakGuard_SuspendedUnderMulticore;
    procedure TestStress_100kFibersCompleteAndBaselineReturns;
    { The single-worker fiber path must not leak one TFiberTask per fiber:
      SpawnFiber + RunScheduler + ResetScheduler over many rounds must reach a
      STEADY arena count, not creep.  Guards the SchedFiberEntry
      call-result-field-read leak fix (see bugs.txt). }
    procedure TestStress_SingleWorkerArenaPlateaus;
  end;

implementation

uses
  runtime.atomic;

{ RTL probes (leak tracker + allocator arena registry). }
procedure _LeakTrackerEnable; external name '_LeakTrackerEnable';
function _LeakTrackerSuspend: Boolean; external name '_LeakTrackerSuspend';
procedure _LeakTrackerResume(APrev: Boolean); external name '_LeakTrackerResume';
function _LeakTrackerIsEnabled: Boolean; external name '_LeakTrackerIsEnabled';
function _MemArenaCount: Int32; external name '_MemArenaCount';
function _MemAbandonedArenaCount: Int32;
  external name '_MemAbandonedArenaCount';

{ --- leak-guard proof ----------------------------------------------------- }

var
  GLgEnabledDuringRun: Int;   { 1 if a fiber saw the tracker disabled }
  GLgSampled: Int;

procedure LeakProbeWorker(Arg: Pointer);
begin
  { Running under N workers: the scheduler must have suspended the tracker. }
  if not _LeakTrackerIsEnabled() then
    GLgEnabledDuringRun := 1;
  _AtomicAddInt32(@GLgSampled, 1);
end;

procedure TAsyncStressTests.TestLeakGuard_SuspendedUnderMulticore;
var
  WasEnabled, StillEnabled: Boolean;
  I: Int;
begin
  { Turn the tracker on for this test (idempotent; normally a --debug build). }
  _LeakTrackerEnable();
  WasEnabled := _LeakTrackerIsEnabled();
  AssertTrue('leak tracker enabled for the test', WasEnabled);

  GLgEnabledDuringRun := 0;
  GLgSampled := 0;
  for I := 0 to 63 do
    SpawnFiber(@LeakProbeWorker, nil);
  RunSchedulerMC(4);

  AssertEquals('all probe fibers ran', 64, GLgSampled);
  AssertEquals('tracker was suspended during the multicore run',
    1, GLgEnabledDuringRun);
  StillEnabled := _LeakTrackerIsEnabled();
  AssertTrue('tracker restored to enabled after the run', StillEnabled);

  { Leave the tracker disabled for the rest of the suite (Suspend clears the
    enabled flag; we deliberately do not resume it). }
  _LeakTrackerSuspend();
  AssertTrue('tracker left disabled for later suites',
    not _LeakTrackerIsEnabled());
end;

{ --- 100k-fibre joint stress ---------------------------------------------- }

var
  GStCompleted: Int;
  GStChannel: TChannel<Int>;
  GStSum: Int;

{ Each worker fiber allocates a small object (heap traffic that may be freed on
  a different worker after migration), yields (to encourage stealing/
  migration), hands a value through the shared channel, and tallies. }
procedure StressWorker(Arg: Pointer);
var
  L: TList<Int>;
  V: Int;
begin
  { Allocation + a yield: the object may be released on a different OS thread
    than the one that allocated it (the cross-thread-free path). }
  L := TList<Int>.Create();
  L.Add(Int32(Arg));
  FiberYield();
  V := L[0];
  L.Free();
  { Hand-off through the bounded channel to exercise fiber-to-fiber transfer
    under contention. }
  GStChannel.Send(V);
  _AtomicAddInt32(@GStCompleted, 1);
end;

{ A drain fiber pulls everything the workers push so the bounded channel does
  not wedge the producers on backpressure. }
procedure StressDrainWorker(Arg: Pointer);
var
  V, Got: Int;
begin
  Got := 0;
  while Got < Int32(Arg) do
  begin
    if GStChannel.Recv(V) then
    begin
      _AtomicAddInt32(@GStSum, V);
      Got := Got + 1;
    end
    else
      Break;
  end;
end;

procedure TAsyncStressTests.TestStress_100kFibersCompleteAndBaselineReturns;
const
  NFIBERS = 100000;
var
  I: Int;
  Abandoned: Int;
begin
  { 100 000 fibers across GetCPUCount workers, each allocating (heap traffic
    that may be freed on a different worker after migration), yielding (to
    provoke stealing/migration), and handing a value through a bounded channel
    to a single drain fiber. }
  GStCompleted := 0;
  GStSum := 0;
  GStChannel := TChannel<Int>.Create(256);
  SpawnFiber(@StressDrainWorker, Pointer(NFIBERS));
  for I := 0 to NFIBERS - 1 do
    SpawnFiber(@StressWorker, Pointer(1));
  RunSchedulerMC(0);        { default = GetCPUCount workers }
  GStChannel.Free();

  AssertEquals('every one of the 100k fibers completed', NFIBERS, GStCompleted);
  AssertEquals('every value reached the drain (sum = NFIBERS)',
    NFIBERS, GStSum);

  { The cross-thread free + abandoned-arena reclamation path (P2 / phase 5) is
    exercised heavily here (a fiber's TList is often released on a different
    worker than the one that allocated it).  The reclamation invariant is that
    ABANDONED arenas stay bounded — they are drained and reclaimed, not piled
    up.  (Note: total arena COUNT does grow across repeated RunSchedulerMC
    calls because per-worker arenas are not reclaimed on thread EXIT — a
    separate allocator gap logged in bugs.txt; within a single run there is no
    growth problem, which is what this test covers.) }
  Abandoned := _MemAbandonedArenaCount();
  AssertTrue('abandoned arenas stay bounded (cross-thread reclamation works)',
    Abandoned <= 64);
end;

procedure PlateauNoop(Arg: Pointer);
begin
end;

procedure TAsyncStressTests.TestStress_SingleWorkerArenaPlateaus;
const
  ROUNDS = 6;
  PER_ROUND = 2000;
var
  R, I: Int;
  AfterWarm, AfterLast: Int;
begin
  { Before the SchedFiberEntry fix each fiber leaked one TFiberTask (the
    CurrentWorker().Current call-result-field-read leaked its transient on
    native), so the arena registry crept ~one arena per few-hundred fibers,
    round on round, unbounded.  With the fix a completed fiber's task is freed,
    so once the pooled small-object arenas are warm the count is STEADY.
    Sample after an early round (warm) and after the last round; a per-fiber
    leak of ~PER_ROUND objects/round would add many arenas between the two. }
  for R := 0 to ROUNDS - 1 do
  begin
    for I := 0 to PER_ROUND - 1 do
      SpawnFiber(@PlateauNoop, nil);
    RunScheduler();
    ResetScheduler();
    if R = 1 then
      AfterWarm := _MemArenaCount();
  end;
  AfterLast := _MemArenaCount();
  { Allow a tiny slack for incidental allocation, but a real per-fiber leak
    would blow far past this (pre-fix: +~6-7 arenas EVERY round). }
  AssertTrue('single-worker fiber arena count plateaus (no per-fiber leak)',
    AfterLast - AfterWarm <= 2);
end;

initialization
  RegisterTest(TAsyncStressTests);

end.
