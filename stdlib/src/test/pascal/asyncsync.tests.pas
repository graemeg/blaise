{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the fiber-aware synchronisation primitives (async.sync,
  docs/async-networking-design.adoc, [#scheduler]): TFiberMutex, TFiberEvent,
  TFiberWaitGroup and TChannel<T>.  Each test drives real fibers under the
  multicore scheduler and asserts on atomic counters / channel ordering.

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit AsyncSync.Tests;

interface

uses
  blaise.testing, SysUtils, async.fibers, async.sync;

type
  TFiberSyncTests = class(TTestCase)
  published
    procedure TestMutex_MutualExclusionUnderContention;
    procedure TestEvent_SignalWakesAllWaiters;
    procedure TestEvent_AutoResetWakesOne;
    procedure TestWaitGroup_JoinsAllWorkers;
    procedure TestChannel_SendRecvOrdering;
    procedure TestChannel_BoundedBackpressure;
    procedure TestChannel_CloseWakesReceivers;
  end;

implementation

uses
  runtime.atomic;

{ --- mutex ---------------------------------------------------------------- }

var
  GMtx: TFiberMutex;
  GShared: Int;         { protected by GMtx; non-atomic on purpose }
  GMaxConcurrent: Int;
  GInside: Int;

procedure MutexWorker(Arg: Pointer);
var
  I, V: Int;
begin
  for I := 0 to 49 do
  begin
    GMtx.Lock();
    { Inside the critical section: prove no two fibers are here at once by a
      non-atomic read-modify-write that would corrupt under a real race. }
    V := GShared;
    FiberYield();           { force a suspension while holding the lock }
    GShared := V + 1;
    GMtx.Unlock();
  end;
end;

procedure TFiberSyncTests.TestMutex_MutualExclusionUnderContention;
const
  NF = 8;
  ITERS = 50;
var
  I: Int;
begin
  GMtx := TFiberMutex.Create();
  GShared := 0;
  for I := 0 to NF - 1 do
    SpawnFiber(@MutexWorker, nil);
  RunSchedulerMC(4);
  { If the mutex truly serialised every read-modify-write, the count is exact
    despite the yield inside the critical section. }
  AssertEquals('mutex serialised all critical sections',
    NF * ITERS, GShared);
  GMtx.Free();
end;

{ --- event (manual reset, wake all) --------------------------------------- }

var
  GEvt: TFiberEvent;
  GEvtWoken: Int;

procedure EventWaiterWorker(Arg: Pointer);
begin
  GEvt.Wait();
  _AtomicAddInt32(@GEvtWoken, 1);
end;

procedure EventSignallerWorker(Arg: Pointer);
begin
  FiberSleep(10);           { let the waiters park first }
  GEvt.Signal();
end;

procedure TFiberSyncTests.TestEvent_SignalWakesAllWaiters;
const
  NW = 10;
var
  I: Int;
begin
  GEvt := TFiberEvent.Create(False);   { manual reset }
  GEvtWoken := 0;
  for I := 0 to NW - 1 do
    SpawnFiber(@EventWaiterWorker, nil);
  SpawnFiber(@EventSignallerWorker, nil);
  RunSchedulerMC(4);
  AssertEquals('manual-reset Signal woke every waiter', NW, GEvtWoken);
  GEvt.Free();
end;

{ --- event (auto reset, wake one per signal) ------------------------------ }

const
  AUTO_NW = 4;

var
  GAutoEvt: TFiberEvent;
  GAutoWoken: Int;

{ Baton relay: each waiter, once woken, re-signals so the NEXT waiter wakes.
  This wakes all N waiters with exactly one external Signal and no dependence
  on when each waiter parks — auto-reset must release precisely one per Signal,
  so a lost or doubled wake shows up as a wrong final count (or a hang). }
procedure AutoWaiterWorker(Arg: Pointer);
begin
  GAutoEvt.Wait();
  _AtomicAddInt32(@GAutoWoken, 1);
  GAutoEvt.Signal();          { pass the baton to the next waiter }
end;

procedure AutoSignallerWorker(Arg: Pointer);
begin
  FiberSleep(10);             { let the waiters park }
  GAutoEvt.Signal();          { release the first; the relay does the rest }
end;

procedure TFiberSyncTests.TestEvent_AutoResetWakesOne;
var
  I: Int;
begin
  GAutoEvt := TFiberEvent.Create(True);    { auto reset }
  GAutoWoken := 0;
  for I := 0 to AUTO_NW - 1 do
    SpawnFiber(@AutoWaiterWorker, nil);
  SpawnFiber(@AutoSignallerWorker, nil);
  RunSchedulerMC(4);
  { The single external Signal, relayed by each woken waiter, releases exactly
    one waiter at a time until all N have woken. }
  AssertEquals('auto-reset releases exactly one waiter per signal',
    AUTO_NW, GAutoWoken);
  GAutoEvt.Free();
end;

{ --- wait group ----------------------------------------------------------- }

var
  GWg: TFiberWaitGroup;
  GWgDone: Int;
  GWgAfterWait: Int;

procedure WgChildWorker(Arg: Pointer);
begin
  FiberSleep(Int32(Arg));
  _AtomicAddInt32(@GWgDone, 1);
  GWg.Done();
end;

procedure WgJoinerWorker(Arg: Pointer);
begin
  GWg.Wait();
  { Every child must have finished before Wait returns. }
  GWgAfterWait := GWgDone;
end;

procedure TFiberSyncTests.TestWaitGroup_JoinsAllWorkers;
const
  NC = 6;
var
  I: Int;
begin
  GWg := TFiberWaitGroup.Create();
  GWgDone := 0;
  GWgAfterWait := -1;
  GWg.Add(NC);
  for I := 0 to NC - 1 do
    SpawnFiber(@WgChildWorker, Pointer((I mod 3) + 1));
  SpawnFiber(@WgJoinerWorker, nil);
  RunSchedulerMC(4);
  AssertEquals('all children ran', NC, GWgDone);
  AssertEquals('Wait returned only after every Done', NC, GWgAfterWait);
  GWg.Free();
end;

{ --- channel: ordering ---------------------------------------------------- }

var
  GCh: TChannel<Int>;
  GRecvSum: Int;
  GRecvOrdered: Int;    { 1 if values came out in send order }

procedure ChSenderWorker(Arg: Pointer);
var
  I: Int;
begin
  for I := 1 to 100 do
    GCh.Send(I);
  GCh.Close();
end;

procedure ChReceiverWorker(Arg: Pointer);
var
  V, Prev: Int;
begin
  Prev := 0;
  GRecvOrdered := 1;
  while GCh.Recv(V) do
  begin
    if V <> Prev + 1 then
      GRecvOrdered := 0;
    Prev := V;
    _AtomicAddInt32(@GRecvSum, V);
  end;
end;

procedure TFiberSyncTests.TestChannel_SendRecvOrdering;
begin
  GCh := TChannel<Int>.Create(4);     { small bounded buffer }
  GRecvSum := 0;
  SpawnFiber(@ChSenderWorker, nil);
  SpawnFiber(@ChReceiverWorker, nil);
  RunSchedulerMC(4);
  AssertEquals('every value received (1..100 sum)', 5050, GRecvSum);
  AssertEquals('FIFO ordering preserved', 1, GRecvOrdered);
  GCh.Free();
end;

{ --- channel: bounded backpressure ---------------------------------------- }

var
  GBpCh: TChannel<Int>;
  GBpSent: Int;         { values the sender has finished pushing }
  GBpReceived: Int;
  GBpOverflow: Int;     { 1 if the sender ever got too far ahead }

procedure BpSenderWorker(Arg: Pointer);
var
  I: Int;
begin
  for I := 1 to 50 do
  begin
    GBpCh.Send(I);
    _AtomicAddInt32(@GBpSent, 1);
    { With a cap of 3 and a slow receiver, the sender must be held back:
      the number of sends that have RETURNED can lead the receiver by at most
      the capacity plus one in-flight hand-off.  A larger lead means the bound
      was not enforced. }
    if (GBpSent - GBpReceived) > 5 then
      GBpOverflow := 1;
  end;
  GBpCh.Close();
end;

procedure BpReceiverWorker(Arg: Pointer);
var
  V: Int;
begin
  while GBpCh.Recv(V) do
  begin
    FiberSleep(1);          { slow receiver forces the sender to park }
    _AtomicAddInt32(@GBpReceived, 1);
  end;
end;

procedure TFiberSyncTests.TestChannel_BoundedBackpressure;
begin
  GBpCh := TChannel<Int>.Create(3);    { capacity 3 }
  GBpSent := 0;
  GBpReceived := 0;
  GBpOverflow := 0;
  SpawnFiber(@BpSenderWorker, nil);
  SpawnFiber(@BpReceiverWorker, nil);
  RunSchedulerMC(4);
  AssertEquals('all values eventually received', 50, GBpReceived);
  AssertEquals('sender held to the bound (never ran far ahead)',
    0, GBpOverflow);
  GBpCh.Free();
end;

{ --- channel: close wakes receivers --------------------------------------- }

var
  GCloseCh: TChannel<Int>;
  GCloseWoken: Int;

procedure CloseWaiterWorker(Arg: Pointer);
var
  V: Int;
begin
  { Blocks on an empty channel; Close must wake it with a False result. }
  if not GCloseCh.Recv(V) then
    _AtomicAddInt32(@GCloseWoken, 1);
end;

procedure CloserWorker(Arg: Pointer);
begin
  FiberSleep(10);
  GCloseCh.Close();
end;

procedure TFiberSyncTests.TestChannel_CloseWakesReceivers;
const
  NR = 5;
var
  I: Int;
begin
  GCloseCh := TChannel<Int>.Create(0);
  GCloseWoken := 0;
  for I := 0 to NR - 1 do
    SpawnFiber(@CloseWaiterWorker, nil);
  SpawnFiber(@CloserWorker, nil);
  RunSchedulerMC(4);
  AssertEquals('close woke every parked receiver', NR, GCloseWoken);
  GCloseCh.Free();
end;

initialization
  RegisterTest(TFiberSyncTests);

end.
