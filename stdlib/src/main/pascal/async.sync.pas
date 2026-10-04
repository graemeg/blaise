{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit async.sync;

// L1 of the fiber runtime (docs/async-networking-design.adoc, [#scheduler],
// "Fiber-aware synchronisation"): primitives that PARK the fiber, not the OS
// thread.  A raw pthread_mutex held across a fiber suspension would block the
// whole worker (and every other fiber on it) — a deadlock-class bug.  These
// objects instead suspend the fiber via the scheduler's park/resume seam
// (async.fibers FiberParkCurrent / FiberResume) and never hold an OS lock
// across a suspension.
//
//   * TFiberMutex      — mutual exclusion between fibers.
//   * TFiberEvent      — a one-to-many signal (manual- or auto-reset).
//   * TFiberWaitGroup  — join on a dynamic set of fibers (Add/Done/Wait).
//   * TChannel<T>      — a Go-style bounded/unbounded hand-off channel.
//
// Each object uses a BRIEF, non-suspending pthread_mutex to protect its own
// state + waiter list; the design explicitly permits that ("brief,
// non-suspending critical sections may still use a raw pthread mutex").  The
// waiter list stores TFiberTask handles; parking a fiber records the current
// task under the lock, then releases the lock, then parks — a waker pops a
// waiter under the lock and resumes it.  The park/resume handshake in
// async.fibers closes the lost-wakeup window.
//
// NATIVE BACKEND ONLY (async.fibers pulls in the inline-asm context leaf).

interface

uses
  SysUtils, generics.collections, async.fibers;

type
  { A FIFO of parked fibers, guarded by the owning object's lock.  Backed by
    TQueue so Push/Pop are O(1) — a TList with Delete(0) is O(n) per pop and
    turns a channel with thousands of parked senders into O(n^2). }
  TWaiterQueue = class
  private
    FItems: TQueue<TFiberTask>;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Push(ATask: TFiberTask);
    function Pop: TFiberTask;      { nil when empty }
    function Count: Integer;
  end;

  { Fiber-aware mutual exclusion.  Lock parks the fiber when the mutex is held;
    Unlock resumes the next waiter.  NOT recursive. }
  TFiberMutex = class
  private
    FMtx: array[0..7] of Int64;   { pthread_mutex_t buffer (state guard) }
    FHeld: Boolean;
    FWaiters: TWaiterQueue;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Lock;
    procedure Unlock;
  end;

  { Fiber-aware event.  Wait parks until Signal.  With auto-reset, Signal wakes
    exactly one waiter and the event stays unset; otherwise Signal wakes all
    current waiters and latches set (Wait then returns immediately until
    Reset). }
  TFiberEvent = class
  private
    FMtx: array[0..7] of Int64;
    FSet: Boolean;
    FAutoReset: Boolean;
    FWaiters: TWaiterQueue;
  public
    constructor Create(AAutoReset: Boolean = False);
    destructor Destroy; override;
    procedure Wait;
    procedure Signal;
    procedure Reset;
  end;

  { Fiber-aware wait group (Go sync.WaitGroup / a latch).  Add raises the
    counter, Done lowers it, Wait parks until it reaches zero. }
  TFiberWaitGroup = class
  private
    FMtx: array[0..7] of Int64;
    FCount: Integer;
    FWaiters: TWaiterQueue;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Add(ADelta: Integer);
    procedure Done;
    procedure Wait;
  end;

  { Structured-concurrency nursery (design [#scheduler-cancellation]).  Owns a
    dynamic set of child fibers; Wait joins them all, cancelling every child on
    the first failure or when the optional deadline elapses; Free joins and
    cancels any stragglers so no fiber leaks by construction.

    Available-today API: Spawn takes a plain procedure + an untyped Pointer
    argument, exactly like SpawnFiber (no closures — anonymous methods are not
    implemented).  Intended use (30 s deadline, 0 = none):

      Group := TTaskGroup.Create(30000);
      try
        for I := 0 to N - 1 do
          Group.Spawn(AtFireOne, IntPtr I);
        Group.Wait;
      finally
        Group.Free;
      end;

    Must be driven from inside a fiber (it parks the caller in Wait). }
  { Closure-typed child entry for the anonymous-method Spawn overload
    (docs/anonymous-methods-design.adoc, Phase 7).  The closure's environment
    lives on the heap, so a loop that spawns with a BLOCK-SCOPED var captures
    a distinct per-iteration value; capturing the routine-level loop variable
    shares one env and every child observes its final value (the documented
    trap). }
  TSpawnProc = reference to procedure;

  TTaskGroup = class;   { forward — TSpawnBox back-references the group }

  { Heap box holding a closure child's fat value: the ARC-managed field keeps
    the closure's environment alive from Spawn until the group frees its box
    list (the group always outlives its children by construction). }
  TSpawnBox = class
  public
    [Unretained] Group: TTaskGroup;  { back-ref; the group owns the box }
    Proc: TSpawnProc;
  end;

  TTaskGroup = class
  private
    FMtx: array[0..7] of Int64;
    FChildren: TList<TFiberTask>;
    FBoxes: TList<TSpawnBox>;     { closure children's boxes — retained until Destroy }
    FRemaining: Integer;          { real children not yet finished }
    FWaiter: TFiberTask;          { the fiber parked in Wait, or nil }
    FDeadlineMs: Int64;           { 0 = no deadline }
    FDeadlineTask: TFiberTask;    { the deadline watchdog fiber, or nil }
    FFailed: Boolean;
    FFailMessage: string;
    FCancelling: Boolean;
    procedure ChildFinished(AFailed: Boolean; const AMsg: string);
    procedure CancelAll;
  public
    constructor Create(ADeadlineMs: Int64 = 0);
    destructor Destroy; override;
    { Spawn a child fiber running AProc(AArg) under this group. }
    function Spawn(AProc: TFiberProc; AArg: Pointer): TFiberTask; overload;
    { Spawn a child fiber running the closure AProc under this group.  The
      closure (and its captured environment) is kept alive by the group until
      the group is freed. }
    function Spawn(AProc: TSpawnProc): TFiberTask; overload;
    { Park until every child has finished, or cancel all children on the first
      failure or when the deadline elapses, then return.  Returns True if all
      children completed successfully, False if any failed or the deadline
      fired. }
    function Wait: Boolean;
    { True once a child failed (message in FailMessage) or the deadline fired. }
    property Failed: Boolean read FFailed;
    property FailMessage: string read FFailMessage;
  end;

  { Go-style channel of T.  Capacity 0 or more: Send parks when the buffer is
    full (bounded backpressure), Recv parks when it is empty.  A capacity of
    -1 means unbounded (Send never parks).  Fiber-to-fiber hand-off. }
  TChannel<T> = class
  private
    FMtx: array[0..7] of Int64;
    FBuf: TQueue<T>;
    FCap: Integer;                { >= 0 bounded, < 0 unbounded }
    FClosed: Boolean;
    FSenders: TWaiterQueue;       { parked because full }
    FReceivers: TWaiterQueue;     { parked because empty }
  public
    constructor Create(ACapacity: Integer = 0);
    destructor Destroy; override;
    { Send AValue, parking while the channel is full.  Returns False if the
      channel is closed. }
    function Send(const AValue: T): Boolean;
    { Receive into AValue, parking while empty.  Returns False if the channel
      is closed AND drained. }
    function Recv(out AValue: T): Boolean;
    { Close the channel: wakes all parked senders/receivers.  Further Sends
      fail; Recv drains the buffer then fails. }
    procedure Close;
    function Count: Integer;
  end;

implementation

uses
  runtime.thread;

{ --- TWaiterQueue --------------------------------------------------------- }

constructor TWaiterQueue.Create;
begin
  Self.FItems := TQueue<TFiberTask>.Create();
end;

destructor TWaiterQueue.Destroy;
begin
  Self.FItems.Free();
  inherited Destroy();
end;

procedure TWaiterQueue.Push(ATask: TFiberTask);
begin
  Self.FItems.Enqueue(ATask);
end;

function TWaiterQueue.Pop: TFiberTask;
begin
  if Self.FItems.Count = 0 then
    Exit(nil);
  Result := Self.FItems.Dequeue();
end;

function TWaiterQueue.Count: Integer;
begin
  Result := Self.FItems.Count;
end;

{ --- TFiberMutex ---------------------------------------------------------- }

constructor TFiberMutex.Create;
begin
  pthread_mutex_init(@Self.FMtx[0], nil);
  Self.FHeld := False;
  Self.FWaiters := TWaiterQueue.Create();
end;

destructor TFiberMutex.Destroy;
begin
  pthread_mutex_destroy(@Self.FMtx[0]);
  Self.FWaiters.Free();
  inherited Destroy();
end;

procedure TFiberMutex.Lock;
var
  T: TFiberTask;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  if not Self.FHeld then
  begin
    Self.FHeld := True;
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  { Held: park behind the current holder.  Record the task, release the guard,
    then park.  A future Unlock pops and resumes us. }
  T := CurrentFiberTask();
  if T = nil then
  begin
    { Off-scheduler: spin-yield on the guard is not possible; treat as an
      uncontended acquire (single-threaded caller).  This path is not the
      intended use — mutexes are for fiber code. }
    Self.FHeld := True;
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  Self.FWaiters.Push(T);
  pthread_mutex_unlock(@Self.FMtx[0]);
  FiberParkCurrent();
  { Resumed by Unlock, which handed the lock to us (FHeld stays True). }
end;

procedure TFiberMutex.Unlock;
var
  Next: TFiberTask;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  Next := Self.FWaiters.Pop();
  if Next = nil then
  begin
    Self.FHeld := False;
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  { Hand ownership directly to the next waiter (FHeld stays True). }
  pthread_mutex_unlock(@Self.FMtx[0]);
  FiberResume(Next);
end;

{ --- TFiberEvent ---------------------------------------------------------- }

constructor TFiberEvent.Create(AAutoReset: Boolean);
begin
  pthread_mutex_init(@Self.FMtx[0], nil);
  Self.FSet := False;
  Self.FAutoReset := AAutoReset;
  Self.FWaiters := TWaiterQueue.Create();
end;

destructor TFiberEvent.Destroy;
begin
  pthread_mutex_destroy(@Self.FMtx[0]);
  Self.FWaiters.Free();
  inherited Destroy();
end;

procedure TFiberEvent.Wait;
var
  T: TFiberTask;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  if Self.FSet then
  begin
    { Auto-reset consumes the signal; manual-reset stays latched. }
    if Self.FAutoReset then
      Self.FSet := False;
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  T := CurrentFiberTask();
  if T = nil then
  begin
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;                     { off-scheduler: nothing to park }
  end;
  Self.FWaiters.Push(T);
  pthread_mutex_unlock(@Self.FMtx[0]);
  FiberParkCurrent();
end;

procedure TFiberEvent.Signal;
var
  Next: TFiberTask;
  Woken: TList<TFiberTask>;
  I: Integer;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  if Self.FAutoReset then
  begin
    { Wake exactly one; if none waiting, latch the signal for the next Wait. }
    Next := Self.FWaiters.Pop();
    if Next = nil then
      Self.FSet := True;
    pthread_mutex_unlock(@Self.FMtx[0]);
    if Next <> nil then
      FiberResume(Next);
    Exit;
  end;
  { Manual-reset: latch set and wake every current waiter. }
  Self.FSet := True;
  Woken := TList<TFiberTask>.Create();
  try
    Next := Self.FWaiters.Pop();
    while Next <> nil do
    begin
      Woken.Add(Next);
      Next := Self.FWaiters.Pop();
    end;
    pthread_mutex_unlock(@Self.FMtx[0]);
    for I := 0 to Woken.Count - 1 do
      FiberResume(Woken[I]);
  finally
    Woken.Free();
  end;
end;

procedure TFiberEvent.Reset;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FSet := False;
  pthread_mutex_unlock(@Self.FMtx[0]);
end;

{ --- TFiberWaitGroup ------------------------------------------------------ }

constructor TFiberWaitGroup.Create;
begin
  pthread_mutex_init(@Self.FMtx[0], nil);
  Self.FCount := 0;
  Self.FWaiters := TWaiterQueue.Create();
end;

destructor TFiberWaitGroup.Destroy;
begin
  pthread_mutex_destroy(@Self.FMtx[0]);
  Self.FWaiters.Free();
  inherited Destroy();
end;

procedure TFiberWaitGroup.Add(ADelta: Integer);
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FCount := Self.FCount + ADelta;
  pthread_mutex_unlock(@Self.FMtx[0]);
end;

procedure TFiberWaitGroup.Done;
var
  Next: TFiberTask;
  Woken: TList<TFiberTask>;
  I: Integer;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FCount := Self.FCount - 1;
  if Self.FCount > 0 then
  begin
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  { Reached zero: wake all waiters. }
  Woken := TList<TFiberTask>.Create();
  try
    Next := Self.FWaiters.Pop();
    while Next <> nil do
    begin
      Woken.Add(Next);
      Next := Self.FWaiters.Pop();
    end;
    pthread_mutex_unlock(@Self.FMtx[0]);
    for I := 0 to Woken.Count - 1 do
      FiberResume(Woken[I]);
  finally
    Woken.Free();
  end;
end;

procedure TFiberWaitGroup.Wait;
var
  T: TFiberTask;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  if Self.FCount <= 0 then
  begin
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  T := CurrentFiberTask();
  if T = nil then
  begin
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  Self.FWaiters.Push(T);
  pthread_mutex_unlock(@Self.FMtx[0]);
  FiberParkCurrent();
end;

{ --- TTaskGroup ----------------------------------------------------------- }

type
  { Per-child record captured for the plain-procedure trampoline (boxes the
    group + user proc + arg on the heap). }
  PTaskGroupChild = ^TTaskGroupChild;
  TTaskGroupChild = record
    Group: TTaskGroup;
    Proc: TFiberProc;
    Arg: Pointer;
  end;

{ Forward: the group marks a deadline internally. }
procedure TaskGroupTripDeadline(AGroup: TTaskGroup); forward;

{ The deadline watchdog fiber: sleep the deadline, and if the group has not
  already finished, trip a deadline failure that cancels the remaining
  children.  Cancelled (by the group completing first) it just unwinds. }
procedure TaskGroupDeadlineEntry(AArg: Pointer);
var
  G: TTaskGroup;
begin
  G := TTaskGroup(AArg);
  try
    FiberSleep(G.FDeadlineMs);
    TaskGroupTripDeadline(G);
  except
    on E: EFiberCancelled do
      ;   { the group finished first and cancelled us }
  end;
end;

{ The fiber body a CLOSURE child runs: AArg is the TSpawnBox (borrowed — the
  group's box list holds the strong reference).  Failure reporting mirrors
  TaskGroupChildEntry. }
procedure TaskGroupClosureEntry(AArg: Pointer);
var
  Box: TSpawnBox;
  G: TTaskGroup;
  Failed: Boolean;
  Msg: string;
begin
  Box := TSpawnBox(AArg);
  G := Box.Group;
  Failed := False;
  Msg := '';
  try
    Box.Proc();
  except
    on E: EFiberCancelled do
      ;   { cancellation is a normal, non-failing end for a child }
    on E: Exception do
    begin
      Failed := True;
      Msg := E.Message;
    end;
  end;
  G.ChildFinished(Failed, Msg);
end;

{ The fiber body every child runs: invoke the user proc under a root frame,
  report success/failure to the group, and free the boxed child record.  A
  child cancelled via CancelAll unwinds through EFiberCancelled here and is
  reported as a (benign) completion, not a failure. }
procedure TaskGroupChildEntry(AArg: Pointer);
var
  C: PTaskGroupChild;
  G: TTaskGroup;
  UserProc: TFiberProc;
  UserArg: Pointer;
  Failed: Boolean;
  Msg: string;
begin
  C := PTaskGroupChild(AArg);
  G := C^.Group;
  UserProc := C^.Proc;
  UserArg := C^.Arg;
  Failed := False;
  Msg := '';
  try
    UserProc(UserArg);
  except
    on E: EFiberCancelled do
      ;   { cancellation is a normal, non-failing end for a child }
    on E: Exception do
    begin
      Failed := True;
      Msg := E.Message;
    end;
  end;
  FreeMem(C);
  G.ChildFinished(Failed, Msg);
end;

constructor TTaskGroup.Create(ADeadlineMs: Int64);
begin
  pthread_mutex_init(@Self.FMtx[0], nil);
  Self.FChildren := TList<TFiberTask>.Create();
  Self.FBoxes := TList<TSpawnBox>.Create();
  Self.FRemaining := 0;
  Self.FWaiter := nil;
  Self.FDeadlineMs := ADeadlineMs;
  Self.FDeadlineTask := nil;
  Self.FFailed := False;
  Self.FCancelling := False;
end;

destructor TTaskGroup.Destroy;
begin
  { Free joins + cancels stragglers: cancel every unfinished child so the run
    can drain, then release.  Wait (if the caller used it) has usually already
    drained them; this is the belt-and-braces path for the try/finally idiom. }
  Self.CancelAll();
  pthread_mutex_destroy(@Self.FMtx[0]);
  Self.FChildren.Free();
  Self.FBoxes.Free();
  inherited Destroy();
end;

function TTaskGroup.Spawn(AProc: TFiberProc; AArg: Pointer): TFiberTask;
var
  C: PTaskGroupChild;
  T: TFiberTask;
begin
  C := GetMem(SizeOf(TTaskGroupChild));
  C^.Group := Self;
  C^.Proc := AProc;
  C^.Arg := AArg;
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FRemaining := Self.FRemaining + 1;
  pthread_mutex_unlock(@Self.FMtx[0]);
  T := SpawnFiber(@TaskGroupChildEntry, C);
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FChildren.Add(T);
  pthread_mutex_unlock(@Self.FMtx[0]);
  Result := T;
end;

function TTaskGroup.Spawn(AProc: TSpawnProc): TFiberTask;
var
  Box: TSpawnBox;
  T: TFiberTask;
begin
  Box := TSpawnBox.Create();
  Box.Group := Self;
  Box.Proc := AProc;
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FBoxes.Add(Box);
  Self.FRemaining := Self.FRemaining + 1;
  pthread_mutex_unlock(@Self.FMtx[0]);
  T := SpawnFiber(@TaskGroupClosureEntry, Pointer(Box));
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FChildren.Add(T);
  pthread_mutex_unlock(@Self.FMtx[0]);
  Result := T;
end;

procedure TTaskGroup.CancelAll;
var
  I: Integer;
  Snapshot: TList<TFiberTask>;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  if Self.FCancelling then
  begin
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit;
  end;
  Self.FCancelling := True;
  Snapshot := TList<TFiberTask>.Create();
  try
    for I := 0 to Self.FChildren.Count - 1 do
      Snapshot.Add(Self.FChildren[I]);
    pthread_mutex_unlock(@Self.FMtx[0]);
    for I := 0 to Snapshot.Count - 1 do
      FiberCancel(Snapshot[I]);
  finally
    Snapshot.Free();
  end;
end;

{ Called by the deadline watchdog when the deadline elapses before all children
  finished: mark the failure and cancel every remaining child. }
procedure TaskGroupTripDeadline(AGroup: TTaskGroup);
var
  DoCancel: Boolean;
begin
  pthread_mutex_lock(@AGroup.FMtx[0]);
  DoCancel := False;
  if (AGroup.FRemaining > 0) and (not AGroup.FFailed) then
  begin
    AGroup.FFailed := True;
    AGroup.FFailMessage := 'task group deadline elapsed';
    DoCancel := True;
  end;
  pthread_mutex_unlock(@AGroup.FMtx[0]);
  if DoCancel then
    AGroup.CancelAll();
end;

procedure TTaskGroup.ChildFinished(AFailed: Boolean; const AMsg: string);
var
  Waiter, DeadlineTask: TFiberTask;
  DoCancel: Boolean;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FRemaining := Self.FRemaining - 1;
  DoCancel := False;
  if AFailed and (not Self.FFailed) then
  begin
    Self.FFailed := True;
    Self.FFailMessage := AMsg;
    DoCancel := True;         { first failure cancels the siblings }
  end;
  Waiter := nil;
  DeadlineTask := nil;
  if Self.FRemaining <= 0 then
  begin
    { All real children done: wake the waiter and retire the deadline
      watchdog (if any) so it does not keep the run alive. }
    Waiter := Self.FWaiter;
    Self.FWaiter := nil;
    DeadlineTask := Self.FDeadlineTask;
    Self.FDeadlineTask := nil;
  end;
  pthread_mutex_unlock(@Self.FMtx[0]);

  if DoCancel then
    Self.CancelAll();
  if DeadlineTask <> nil then
    FiberCancel(DeadlineTask);
  if Waiter <> nil then
    FiberResume(Waiter);
end;

function TTaskGroup.Wait: Boolean;
var
  T: TFiberTask;
begin
  { A deadline is enforced by a watchdog fiber (not a counted child) so a
    prompt success is not held back by the watchdog's sleep. }
  if (Self.FDeadlineMs > 0) and (Self.FDeadlineTask = nil) then
  begin
    pthread_mutex_lock(@Self.FMtx[0]);
    if Self.FRemaining > 0 then
      Self.FDeadlineTask := SpawnFiber(@TaskGroupDeadlineEntry, Pointer(Self));
    pthread_mutex_unlock(@Self.FMtx[0]);
  end;

  pthread_mutex_lock(@Self.FMtx[0]);
  if Self.FRemaining <= 0 then
  begin
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit(not Self.FFailed);
  end;
  T := CurrentFiberTask();
  if T = nil then
  begin
    { Off-scheduler: cannot park.  Nothing sensible to wait on. }
    pthread_mutex_unlock(@Self.FMtx[0]);
    Exit(not Self.FFailed);
  end;
  Self.FWaiter := T;
  pthread_mutex_unlock(@Self.FMtx[0]);
  FiberParkCurrent();
  Result := not Self.FFailed;
end;

{ --- TChannel<T> ---------------------------------------------------------- }

constructor TChannel<T>.Create(ACapacity: Integer);
begin
  pthread_mutex_init(@Self.FMtx[0], nil);
  Self.FBuf := TQueue<T>.Create();
  Self.FCap := ACapacity;
  Self.FClosed := False;
  Self.FSenders := TWaiterQueue.Create();
  Self.FReceivers := TWaiterQueue.Create();
end;

destructor TChannel<T>.Destroy;
begin
  pthread_mutex_destroy(@Self.FMtx[0]);
  Self.FBuf.Free();
  Self.FSenders.Free();
  Self.FReceivers.Free();
  inherited Destroy();
end;

function TChannel<T>.Send(const AValue: T): Boolean;
var
  T2: TFiberTask;
  Rcv: TFiberTask;
begin
  while True do
  begin
    pthread_mutex_lock(@Self.FMtx[0]);
    if Self.FClosed then
    begin
      pthread_mutex_unlock(@Self.FMtx[0]);
      Exit(False);
    end;
    { Room to buffer (unbounded when FCap < 0)? }
    if (Self.FCap < 0) or (Self.FBuf.Count < Self.FCap)
       or (Self.FReceivers.Count() > 0) then
    begin
      Self.FBuf.Enqueue(AValue);
      { A parked receiver can now make progress. }
      Rcv := Self.FReceivers.Pop();
      pthread_mutex_unlock(@Self.FMtx[0]);
      if Rcv <> nil then
        FiberResume(Rcv);
      Exit(True);
    end;
    { Full and no receiver waiting: park this sender and retry on resume. }
    T2 := CurrentFiberTask();
    if T2 = nil then
    begin
      { Off-scheduler: cannot park.  Buffer anyway (degrade to unbounded) so a
        non-fiber producer does not deadlock. }
      Self.FBuf.Enqueue(AValue);
      pthread_mutex_unlock(@Self.FMtx[0]);
      Exit(True);
    end;
    Self.FSenders.Push(T2);
    pthread_mutex_unlock(@Self.FMtx[0]);
    FiberParkCurrent();
    { Loop: re-check conditions after being resumed. }
  end;
end;

function TChannel<T>.Recv(out AValue: T): Boolean;
var
  T2: TFiberTask;
  Snd: TFiberTask;
begin
  while True do
  begin
    pthread_mutex_lock(@Self.FMtx[0]);
    if Self.FBuf.Count > 0 then
    begin
      AValue := Self.FBuf.Dequeue();
      { A parked sender now has room. }
      Snd := Self.FSenders.Pop();
      pthread_mutex_unlock(@Self.FMtx[0]);
      if Snd <> nil then
        FiberResume(Snd);
      Exit(True);
    end;
    if Self.FClosed then
    begin
      pthread_mutex_unlock(@Self.FMtx[0]);
      Exit(False);          { closed and drained }
    end;
    { Empty: park this receiver and retry on resume. }
    T2 := CurrentFiberTask();
    if T2 = nil then
    begin
      pthread_mutex_unlock(@Self.FMtx[0]);
      Exit(False);          { off-scheduler: nothing to wait on }
    end;
    Self.FReceivers.Push(T2);
    pthread_mutex_unlock(@Self.FMtx[0]);
    FiberParkCurrent();
  end;
end;

procedure TChannel<T>.Close;
var
  Woken: TList<TFiberTask>;
  Next: TFiberTask;
  I: Integer;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  Self.FClosed := True;
  Woken := TList<TFiberTask>.Create();
  try
    Next := Self.FSenders.Pop();
    while Next <> nil do
    begin
      Woken.Add(Next);
      Next := Self.FSenders.Pop();
    end;
    Next := Self.FReceivers.Pop();
    while Next <> nil do
    begin
      Woken.Add(Next);
      Next := Self.FReceivers.Pop();
    end;
    pthread_mutex_unlock(@Self.FMtx[0]);
    for I := 0 to Woken.Count - 1 do
      FiberResume(Woken[I]);
  finally
    Woken.Free();
  end;
end;

function TChannel<T>.Count: Integer;
begin
  pthread_mutex_lock(@Self.FMtx[0]);
  Result := Self.FBuf.Count;
  pthread_mutex_unlock(@Self.FMtx[0]);
end;

end.
