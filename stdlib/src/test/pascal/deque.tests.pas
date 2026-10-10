{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the Chase-Lev work-stealing deque (async.deque,
  docs/async-networking-design.adoc, [#scheduler]).

  Single-threaded tests pin the LIFO PopBottom / FIFO Steal semantics, empty
  and underflow behaviour, and growth past the initial capacity.  The final
  test is CONCURRENT: one owner pushes/pops while N thief threads steal, and
  the test asserts every distinct task is claimed exactly once — no loss, no
  duplication — the property the whole scheduler's correctness rests on.

  NATIVE BACKEND ONLY (spawns pthreads; the deque atomics are lock-prefixed).

  Self-registers via the initialization section. }

unit Deque.Tests;

interface

uses
  blaise.testing, SysUtils, async.deque;

type
  TDequeSingleTests = class(TTestCase)
  published
    procedure TestPushPop_LifoOrder;
    procedure TestPop_EmptyReturnsNil;
    procedure TestSteal_EmptyReturnsNil;
    procedure TestSteal_FifoOrder;
    procedure TestGrow_PastInitialCapacity;
    procedure TestPushPop_SingleElement;
  end;

  TDequeConcurrentTests = class(TTestCase)
  published
    procedure TestConcurrent_EveryTaskTakenExactlyOnce;
    { Grow publishes a NEW buffer while thieves are stealing.  On a weakly
      ordered CPU (arm64) the copied slots had to be visible before the new
      FBuf pointer; a plain store let a thief read a stale slot, win the top
      CAS and lose the task (intermittent macOS CI failure, 2026-10-10).
      Many rounds of a capacity-2 deque with an unpopped backlog maximise
      grow-while-stealing events. }
    procedure TestConcurrent_GrowWhileStealing_NoTaskLost;
  end;

implementation

uses
  runtime.thread, runtime.atomic;

{ --- single-threaded ------------------------------------------------------ }

procedure TDequeSingleTests.TestPushPop_LifoOrder;
var
  D: TWorkStealDeque;
  I: Integer;
begin
  D := TWorkStealDeque.Create();
  for I := 1 to 5 do
    D.PushBottom(Pointer(I));
  { PopBottom is LIFO: last pushed comes back first. }
  for I := 5 downto 1 do
    AssertTrue('LIFO pop order', D.PopBottom() = Pointer(I));
  AssertTrue('empty after draining', D.PopBottom() = nil);
  D.Free();
end;

procedure TDequeSingleTests.TestPop_EmptyReturnsNil;
var
  D: TWorkStealDeque;
begin
  D := TWorkStealDeque.Create();
  AssertTrue('pop on fresh empty is nil', D.PopBottom() = nil);
  D.PushBottom(Pointer(7));
  AssertTrue('pop the one item', D.PopBottom() = Pointer(7));
  AssertTrue('pop past drain is nil again', D.PopBottom() = nil);
  AssertTrue('and stays nil', D.PopBottom() = nil);
  D.Free();
end;

procedure TDequeSingleTests.TestSteal_EmptyReturnsNil;
var
  D: TWorkStealDeque;
begin
  D := TWorkStealDeque.Create();
  AssertTrue('steal from empty is nil', D.Steal() = nil);
  D.Free();
end;

procedure TDequeSingleTests.TestSteal_FifoOrder;
var
  D: TWorkStealDeque;
  I: Integer;
begin
  D := TWorkStealDeque.Create();
  for I := 1 to 5 do
    D.PushBottom(Pointer(I));
  { Steal takes from the TOP: FIFO relative to push order. }
  for I := 1 to 5 do
    AssertTrue('FIFO steal order', D.Steal() = Pointer(I));
  AssertTrue('empty after stealing all', D.Steal() = nil);
  D.Free();
end;

procedure TDequeSingleTests.TestGrow_PastInitialCapacity;
var
  D: TWorkStealDeque;
  I: Integer;
begin
  { Small initial capacity forces at least two growths. }
  D := TWorkStealDeque.Create(4);
  for I := 1 to 100 do
    D.PushBottom(Pointer(I));
  AssertTrue('approx count reflects all pushes', D.ApproxCount() = 100);
  for I := 100 downto 1 do
    AssertTrue('every pushed item survives growth', D.PopBottom() = Pointer(I));
  AssertTrue('empty after draining a grown deque', D.PopBottom() = nil);
  D.Free();
end;

procedure TDequeSingleTests.TestPushPop_SingleElement;
var
  D: TWorkStealDeque;
begin
  { Exercise the last-element PopBottom path (T = B) repeatedly. }
  D := TWorkStealDeque.Create();
  D.PushBottom(Pointer(1));
  AssertTrue('single pop', D.PopBottom() = Pointer(1));
  D.PushBottom(Pointer(2));
  AssertTrue('single steal', D.Steal() = Pointer(2));
  AssertTrue('empty after single steal', D.PopBottom() = nil);
  { Interleave: push, steal the only one, then pop must see empty. }
  D.PushBottom(Pointer(3));
  AssertTrue('steal only item', D.Steal() = Pointer(3));
  AssertTrue('pop sees empty (no double take)', D.PopBottom() = nil);
  D.Free();
end;

{ --- concurrent ----------------------------------------------------------- }

const
  CC_NUM_TASKS = 20000;
  CC_NUM_STEALERS = 4;

type
  { A distinct payload per task so we can index a claim-count array by Id.
    Using Id+1 as the stored pointer keeps every stored pointer non-nil
    (Pointer(0) = nil would be indistinguishable from an empty slot). }
  PClaimState = ^TClaimState;
  TClaimState = record
    Deque: TWorkStealDeque;
    Claims: Pointer;      { ^array[0..CC_NUM_TASKS-1] of Integer }
    Done: Integer;        { set to 1 by the owner when it has pushed+popped all }
  end;

  PIntArray = ^TIntArray;
  TIntArray = array[0..0] of Integer;

var
  GCC: TClaimState;

{ Record one claim of task Id (0-based).  Atomic so concurrent thieves +
  owner never lose or double-count a claim. }
procedure ClaimTask(AState: PClaimState; APtr: Pointer);
var
  Id: Integer;
  Arr: PIntArray;
  Slot: Pointer;
begin
  if APtr = nil then Exit;
  Id := Integer(APtr) - 1;      { we stored Id+1 }
  Arr := PIntArray(AState^.Claims);
  Slot := @Arr^[Id];
  _AtomicAddInt32(Slot, 1);
end;

{ Stealer thread: hammer Steal until the owner signals Done and the deque
  looks empty.  Every successful steal records a claim. }
procedure StealerEntry(Arg: Pointer);
var
  State: PClaimState;
  D: TWorkStealDeque;
  Item: Pointer;
  Idle: Integer;
begin
  State := PClaimState(Arg);
  D := State^.Deque;
  Idle := 0;
  while True do
  begin
    Item := D.Steal();
    if Item <> nil then
    begin
      ClaimTask(State, Item);
      Idle := 0;
    end
    else
    begin
      if State^.Done = 1 then
      begin
        { Drain any last stragglers, then stop once we see a run of empties. }
        Idle := Idle + 1;
        if Idle > 1000 then
          Break;
      end;
    end;
  end;
end;

procedure TDequeConcurrentTests.TestConcurrent_EveryTaskTakenExactlyOnce;
var
  Threads: array[0..CC_NUM_STEALERS - 1] of Int64;
  Claims: array[0..CC_NUM_TASKS - 1] of Integer;
  I, Taken, Missed, Doubled: Integer;
  Item: Pointer;
begin
  for I := 0 to CC_NUM_TASKS - 1 do
    Claims[I] := 0;
  GCC.Deque := TWorkStealDeque.Create(64);
  GCC.Claims := @Claims[0];
  GCC.Done := 0;

  { Launch the thieves before the owner starts producing, so stealing races
    production. }
  for I := 0 to CC_NUM_STEALERS - 1 do
  begin
    Threads[I] := 0;
    pthread_create(@Threads[I], nil, Pointer(@StealerEntry), @GCC);
  end;

  { Owner: push all tasks, popping some of its own bottom as it goes so the
    owner/thief last-element race is exercised heavily. }
  for I := 0 to CC_NUM_TASKS - 1 do
  begin
    GCC.Deque.PushBottom(Pointer(I + 1));
    if (I and 3) = 0 then
    begin
      Item := GCC.Deque.PopBottom();
      if Item <> nil then
        ClaimTask(@GCC, Item);
    end;
  end;
  { Owner drains whatever is left at the bottom. }
  Item := GCC.Deque.PopBottom();
  while Item <> nil do
  begin
    ClaimTask(@GCC, Item);
    Item := GCC.Deque.PopBottom();
  end;

  { Signal thieves that production is finished; they drain then exit. }
  GCC.Done := 1;
  for I := 0 to CC_NUM_STEALERS - 1 do
    pthread_join(Threads[I], nil);

  { Every task claimed exactly once. }
  Taken := 0;
  Missed := 0;
  Doubled := 0;
  for I := 0 to CC_NUM_TASKS - 1 do
  begin
    if Claims[I] = 1 then
      Taken := Taken + 1
    else if Claims[I] = 0 then
      Missed := Missed + 1
    else
      Doubled := Doubled + 1;
  end;
  AssertEquals('no task lost', 0, Missed);
  AssertEquals('no task duplicated', 0, Doubled);
  AssertEquals('every task taken exactly once', CC_NUM_TASKS, Taken);

  GCC.Deque.Free();
  GCC.Deque := nil;
end;

procedure TDequeConcurrentTests.TestConcurrent_GrowWhileStealing_NoTaskLost;
const
  ROUNDS = 60;
  ROUND_TASKS = 4000;
var
  Threads: array[0..CC_NUM_STEALERS - 1] of Int64;
  Claims: array[0..ROUND_TASKS - 1] of Integer;
  R, I, Missed, Doubled: Integer;
  Item: Pointer;
begin
  Missed := 0;
  Doubled := 0;
  for R := 1 to ROUNDS do
  begin
    for I := 0 to ROUND_TASKS - 1 do
      Claims[I] := 0;
    GCC.Deque := TWorkStealDeque.Create(2);
    GCC.Claims := @Claims[0];
    GCC.Done := 0;
    for I := 0 to CC_NUM_STEALERS - 1 do
    begin
      Threads[I] := 0;
      pthread_create(@Threads[I], nil, Pointer(@StealerEntry), @GCC);
    end;
    { Push without popping, so a backlog builds and the buffer keeps
      growing while the thieves steal from the top. }
    for I := 0 to ROUND_TASKS - 1 do
      GCC.Deque.PushBottom(Pointer(I + 1));
    Item := GCC.Deque.PopBottom();
    while Item <> nil do
    begin
      ClaimTask(@GCC, Item);
      Item := GCC.Deque.PopBottom();
    end;
    GCC.Done := 1;
    for I := 0 to CC_NUM_STEALERS - 1 do
      pthread_join(Threads[I], nil);
    for I := 0 to ROUND_TASKS - 1 do
      if Claims[I] = 0 then
        Missed := Missed + 1
      else if Claims[I] > 1 then
        Doubled := Doubled + 1;
    GCC.Deque.Free();
    GCC.Deque := nil;
  end;
  AssertEquals('no task lost across growth', 0, Missed);
  AssertEquals('no task duplicated across growth', 0, Doubled);
end;

initialization
  RegisterTest(TDequeSingleTests);
  RegisterTest(TDequeConcurrentTests);

end.
