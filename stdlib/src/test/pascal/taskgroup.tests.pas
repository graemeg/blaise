{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the TTaskGroup nursery (async.sync,
  docs/async-networking-design.adoc, [#scheduler-cancellation]): structured
  concurrency where child lifetimes are tied to the group's scope — Wait joins
  all children, the first failure cancels the siblings, a deadline cancels
  stragglers, and Free leaks nothing.

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit TaskGroup.Tests;

interface

uses
  blaise.testing, SysUtils, async.fibers, async.sync;

type
  TTaskGroupTests = class(TTestCase)
  published
    procedure TestGroup_AllChildrenRunAndJoin;
    procedure TestGroup_FirstFailureCancelsSiblings;
    procedure TestGroup_DeadlineCancelsStragglers;
  end;

implementation

uses
  runtime.atomic;

var
  GTgRan: Int;          { children that completed their work }
  GTgCancelled: Int;    { children that observed cancellation }
  GTgResult: Int;       { 1 if Wait returned success, 0 failure, -1 unset }

{ --- all children run and join -------------------------------------------- }

procedure TgChildWorker(Arg: Pointer);
begin
  FiberSleep((Int32(Arg) mod 4) + 1);
  _AtomicAddInt32(@GTgRan, 1);
end;

procedure TgAllRunnerWorker(Arg: Pointer);
var
  G: TTaskGroup;
  I: Int;
begin
  G := TTaskGroup.Create(0);          { no deadline }
  try
    for I := 0 to 49 do
      G.Spawn(@TgChildWorker, Pointer(I));
    if G.Wait() then
      GTgResult := 1
    else
      GTgResult := 0;
  finally
    G.Free();
  end;
end;

procedure TTaskGroupTests.TestGroup_AllChildrenRunAndJoin;
begin
  GTgRan := 0;
  GTgResult := -1;
  SpawnFiber(@TgAllRunnerWorker, nil);
  RunSchedulerMC(4);
  AssertEquals('every child ran to completion', 50, GTgRan);
  AssertEquals('Wait reported success', 1, GTgResult);
end;

{ --- first failure cancels siblings --------------------------------------- }

procedure TgFailingChild(Arg: Pointer);
begin
  FiberSleep(2);
  raise Exception.Create('child blew up');
end;

procedure TgLongChild(Arg: Pointer);
begin
  try
    FiberSleep(10000);              { would run for 10 s if not cancelled }
    _AtomicAddInt32(@GTgRan, 1);
  except
    on E: EFiberCancelled do
      _AtomicAddInt32(@GTgCancelled, 1);
  end;
end;

procedure TgFailRunnerWorker(Arg: Pointer);
var
  G: TTaskGroup;
  I: Int;
begin
  G := TTaskGroup.Create(0);
  try
    for I := 0 to 7 do
      G.Spawn(@TgLongChild, nil);
    G.Spawn(@TgFailingChild, nil);
    if G.Wait() then
      GTgResult := 1
    else
      GTgResult := 0;
  finally
    G.Free();
  end;
end;

procedure TTaskGroupTests.TestGroup_FirstFailureCancelsSiblings;
var
  Started, Elapsed: Int64;
begin
  GTgRan := 0;
  GTgCancelled := 0;
  GTgResult := -1;
  Started := MonotonicNowNs();
  SpawnFiber(@TgFailRunnerWorker, nil);
  RunSchedulerMC(4);
  Elapsed := MonotonicNowNs() - Started;
  AssertEquals('Wait reported failure', 0, GTgResult);
  AssertEquals('no long child ran to completion', 0, GTgRan);
  AssertEquals('all eight siblings were cancelled', 8, GTgCancelled);
  AssertTrue('siblings did not wait out their 10 s sleep',
    Elapsed < Int64(5000000000));
end;

{ --- deadline cancels stragglers ------------------------------------------ }

procedure TgSlowChild(Arg: Pointer);
begin
  try
    FiberSleep(10000);              { far longer than the group deadline }
    _AtomicAddInt32(@GTgRan, 1);
  except
    on E: EFiberCancelled do
      _AtomicAddInt32(@GTgCancelled, 1);
  end;
end;

procedure TgDeadlineRunnerWorker(Arg: Pointer);
var
  G: TTaskGroup;
  I: Int;
begin
  G := TTaskGroup.Create(20);         { 20 ms deadline }
  try
    for I := 0 to 5 do
      G.Spawn(@TgSlowChild, nil);
    if G.Wait() then
      GTgResult := 1
    else
      GTgResult := 0;
  finally
    G.Free();
  end;
end;

procedure TTaskGroupTests.TestGroup_DeadlineCancelsStragglers;
var
  Started, Elapsed: Int64;
begin
  GTgRan := 0;
  GTgCancelled := 0;
  GTgResult := -1;
  Started := MonotonicNowNs();
  SpawnFiber(@TgDeadlineRunnerWorker, nil);
  RunSchedulerMC(4);
  Elapsed := MonotonicNowNs() - Started;
  AssertEquals('Wait reported deadline failure', 0, GTgResult);
  AssertEquals('no slow child completed', 0, GTgRan);
  AssertEquals('all stragglers cancelled at the deadline', 6, GTgCancelled);
  AssertTrue('the deadline fired well before the 10 s sleeps',
    Elapsed < Int64(5000000000));
end;

initialization
  RegisterTest(TTaskGroupTests);

end.
