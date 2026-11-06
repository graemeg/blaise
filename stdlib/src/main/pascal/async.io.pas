{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit async.io;

// L3 of the fiber runtime (docs/async-networking-design.adoc, [#fiber-io]):
// "blocking that isn't".  Each primitive tries the non-blocking socket op; on a
// would-block result it registers interest with the reactor (token =
// CurrentFiberTask), parks, and retries when the reactor resumes it — but if NO
// scheduler is running (a plain program) it waits in poll(2) instead, so the
// same source works in both worlds -- and a deadline is honoured in both.  EINTR is retried transparently; a
// real error or EOF returns the RAW SIGNED count (0 = peer closed) so the caller
// can disambiguate — unlike RecvString which collapses EOF and error to ''.
//
// Deadlines (optional per call) arm a helper fiber via the L1 timer heap; when
// it fires it resumes the parked I/O fiber and the call returns ETIMEDOUT
// instead of hanging.  Cancellation observed on resume raises EFiberCancelled
// (the L1 contract).
//
// NATIVE BACKEND ONLY (depends on async.fibers).  OS divergences resolve at
// link time: the reactor via async.fibers' adapter seam (epoll/kqueue), errno
// via runtime.errno.*, and the socket/fcntl constants below via the
// rtl.platform.layout.<os> seam.

interface

uses
  Net.Sockets;

const
  { Negative sentinels the primitives return in addition to the raw kernel
    error (which is also negative in the static profile).  ETIMEDOUT is the
    deadline result; the raw signed count is returned otherwise. }
  IO_ETIMEDOUT = -2;

{ Receive up to ALen bytes from AFd into ABuf.  Returns the byte count (>0),
  0 on peer close (EOF), a negative kernel error, or IO_ETIMEDOUT.  Parks the
  fiber on readability while the socket would block. }
function FiberRecv(AFd: Int; ABuf: Pointer; ALen: Int64): Int64;
function FiberRecvT(AFd: Int; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;

{ Send up to ALen bytes from ABuf to AFd.  Returns the byte count written (>0),
  a negative kernel error, or IO_ETIMEDOUT.  Parks on writability for a short
  write. }
function FiberSend(AFd: Int; ABuf: Pointer; ALen: Int64): Int64;
function FiberSendT(AFd: Int; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;

{ Accept the next connection on a listening socket.  Returns the connected fd
  (>=0, set non-blocking), a negative kernel error, or IO_ETIMEDOUT.  Parks on
  readability. }
function FiberAccept(AListenFd: Int): Int;
function FiberAcceptT(AListenFd: Int; ADeadlineMs: Int64): Int;

{ Connect AFd (must be non-blocking) to AAddr (a struct sockaddr pointer --
  sockaddr_in or sockaddr_in6 -- AAddrLen bytes).  Returns 0 on success, a
  negative kernel error, or IO_ETIMEDOUT.  Waits for writability (parking the
  fiber, or in poll(2) with no scheduler) then checks SO_ERROR. }
function FiberConnect(AFd: Int; AAddr: Pointer; AAddrLen: Int): Int;
function FiberConnectT(AFd: Int; AAddr: Pointer; AAddrLen: Int; ADeadlineMs: Int64): Int;

{ Flip AFd to non-blocking (the fiber I/O primitives require it). }
procedure SetNonBlocking(AFd: Int);

type
  TResolveFunc = function(const AHost: string; APort: UInt16): TResolvedAddrs;

var
  { The lookup ResolveHostFiber runs.  Defaults to Net.Sockets.ResolveHost
    (getaddrinfo).  A replacement must be thread-safe, because under a
    scheduler it runs on a helper thread.  This is the seam for a pure-Pascal
    resolver (the planned Net.Dns) and for tests. }
  GResolveFunc: TResolveFunc;

{ Resolve AHost like Net.Sockets.ResolveHost, without stalling the scheduler.

  Under a fiber scheduler the lookup runs on a short-lived helper thread (one
  per call) while the calling fiber parks, so the worker keeps running every
  other fiber for as long as DNS takes.  With no scheduler it is a plain
  call to GResolveFunc on the calling thread.

  A lookup cannot be interrupted: getaddrinfo has no cancellation.  If the
  fiber is cancelled during one, the call waits (blocking its worker) for
  the lookup to finish before raising, so the helper never outlives its
  request.  Connect timeouts do not cover the lookup itself. }
function ResolveHostFiber(const AHost: string; APort: UInt16): TResolvedAddrs;

implementation

uses
  SysUtils, async.fibers, async.reactor, async.sync, runtime.atomic;

{ WouldBlock/Interrupted/FdExhausted are the P3 errno abstraction
  (runtime.errno.*), swapped per build profile at link time. }
function WouldBlock(N: Int64): Boolean; external name 'WouldBlock';
function Interrupted(N: Int64): Boolean; external name 'Interrupted';
{ True when the call failed with EMFILE/ENFILE (out of file descriptors).
  Such a call cannot succeed until an fd is freed, so retrying it in a tight
  loop just burns a core — the accept path backs off instead (GH #189). }
function FdExhausted(N: Int64): Boolean; external name 'FdExhausted';
{ True when a non-blocking connect returned "still completing" (EINPROGRESS or
  EINTR) rather than a real failure. }
function ConnectPending(N: Int64): Boolean; external name 'ConnectPending';

const
  { Back-off between accept retries when the process is out of file descriptors.
    Long enough that a spin can't peg a core, short enough that the listener
    resumes accepting promptly once in-flight connections close and free fds. }
  FD_EXHAUSTED_BACKOFF_MS = 10;

{ fcntl is C-VARIADIC: on Apple arm64 a variadic argument travels on the
  stack, so a fixed three-int declaration put the flag in a register fcntl
  never reads -- F_SETFL silently did not set O_NONBLOCK on macOS.  The
  third argument is passed through `varargs`. }
function c_fcntl3(AFd, ACmd: Int32): Int32; varargs; external name 'fcntl';
{$IFNDEF DARWIN}
function c_accept4(AFd: Int32; AAddr, AAddrLen: Pointer; AFlags: Int32): Int32;
  external name 'accept4';
{$ELSE}
function c_accept(AFd: Int32; AAddr, AAddrLen: Pointer): Int32;
  external name 'accept';
{$ENDIF}
function c_getsockopt(AFd, ALevel, AOptName: Int32; AOptVal, AOptLen: Pointer): Int32;
  external name 'getsockopt';
function c_getpeername(AFd: Int32; AAddr, AAddrLen: Pointer): Int32;
  external name 'getpeername';

const
  F_GETFL     = 3;
  F_SETFL     = 4;

{ OS-divergent socket/fcntl constants from the per-target
  rtl.platform.layout.<os> seam (Linux/FreeBSD values differ for all four). }
function O_NONBLOCK: Int32;    external name '_ONonBlock';
function SOCK_NONBLOCK: Int32; external name '_SockNonBlock';  { accept4 flag }

{$IFDEF DARWIN}
{ macOS has no accept4(2): accept, then make the new connection non-blocking
  -- unconditionally, because that is the only thing this unit ever asks
  accept4 for, and Darwin's SOCK_NONBLOCK seam value is 0 (there is no such
  flag), so AFlags cannot carry the request.  Not atomic the way accept4 is,
  but the fd is not yet visible to any other code.  The connection also gets
  SO_NOSIGPIPE, Darwin's stand-in for the MSG_NOSIGNAL its sends cannot use. }
function c_accept4(AFd: Int32; AAddr, AAddrLen: Pointer; AFlags: Int32): Int32;
begin
  Result := c_accept(AFd, AAddr, AAddrLen);
  if Result >= 0 then
  begin
    c_fcntl3(Result, F_SETFL, c_fcntl3(Result, F_GETFL, 0) or O_NONBLOCK());
    SuppressSigPipe(Result);
  end;
end;
{$ENDIF}
function SOL_SOCKET_: Int32;   external name '_SolSocket';
function SO_ERROR_: Int32;     external name '_SoError';

type
  PInteger = ^Int32;

procedure SetNonBlocking(AFd: Int);
var
  Fl: Int;
begin
  if AFd < 0 then
    Exit;
  Fl := c_fcntl3(AFd, F_GETFL, 0);
  if Fl < 0 then
    Fl := 0;
  c_fcntl3(AFd, F_SETFL, Fl or O_NONBLOCK());
end;

{ ---------------------------------------------------------------------------
  Deadline helper
  --------------------------------------------------------------------------- }

{ Shared context between an I/O fiber and its optional deadline helper.
  Heap-allocated so both fibers reference the same flags across parks. }
type
  TDeadlineCtx = class
  public
    IoTask: TFiberTask;      { the fiber doing the I/O; resumed on timeout }
    Fired: Boolean;          { the deadline elapsed }
    Cancel: Boolean;         { the I/O finished first; helper should exit }
    Millis: Int64;
  end;

{ The helper fiber: sleep the deadline, then (if not cancelled) flag Fired and
  resume the I/O fiber.  If FiberSleep raises EFiberCancelled (the I/O side
  cancelled us because the op completed), just exit. }
procedure DeadlineHelper(AArg: Pointer);
var
  Ctx: TDeadlineCtx;
begin
  Ctx := TDeadlineCtx(AArg);
  try
    FiberSleep(Ctx.Millis);
  except
    on E: EFiberCancelled do
      Exit;                  { I/O completed first; nothing to do }
  end;
  if not Ctx.Cancel then
  begin
    Ctx.Fired := True;
    FiberResume(Ctx.IoTask);
  end;
end;

{ Park the current fiber waiting for AInterest on AFd, honouring an optional
  deadline.  Returns True if the fd became ready, False if the deadline fired
  (the caller then returns IO_ETIMEDOUT).  ADeadlineMs <= 0 means no deadline.
  Assumes CurrentFiberTask <> nil (a scheduler is running). }
function ParkForIo(AFd: Int; AInterest: TIoInterests; ADeadlineMs: Int64): Boolean;
var
  R: TReactor;
  Ctx: TDeadlineCtx;
  Helper: TFiberTask;
  Me: TFiberTask;
begin
  R := GetReactor();
  Me := CurrentFiberTask();
  Ctx := nil;
  Helper := nil;
  if ADeadlineMs > 0 then
  begin
    Ctx := TDeadlineCtx.Create();
    Ctx.IoTask := Me;
    Ctx.Fired := False;
    Ctx.Cancel := False;
    Ctx.Millis := ADeadlineMs;
    Helper := SpawnFiber(@DeadlineHelper, Pointer(Ctx));
  end;
  R.Add(AFd, AInterest, Pointer(Me));
  FiberParkCurrent();          { resumed by reactor readiness or the helper }
  R.Remove(AFd);
  if Ctx <> nil then
  begin
    Result := not Ctx.Fired;
    { Whichever side we are on, retire the helper: if it already fired it is
      finishing; if the fd woke us first, cancel its sleep so it exits. }
    Ctx.Cancel := True;
    if not Ctx.Fired then
      FiberCancel(Helper);
    { Ctx is owned here; it stays referenced by the helper task until the
      helper finishes, but the helper only reads Fired/Cancel/Millis which are
      set.  ARC frees Ctx when both references drop. }
  end
  else
    Result := True;
end;

{ Wait for AInterest on AFd, honouring an optional deadline: park the fiber
  under a running scheduler, otherwise block the thread in poll(2).  Returns
  True when the fd is ready, False when the deadline passed.  ADeadlineMs <= 0
  means no deadline.  The fd stays non-blocking either way, so the same socket
  can later be used under a scheduler. }
function WaitForIo(AFd: Int; AInterest: TIoInterests; ADeadlineMs: Int64): Boolean;
begin
  if CurrentFiberTask() <> nil then
    Exit(ParkForIo(AFd, AInterest, ADeadlineMs));
  Result := WaitFd(AFd, ioWrite in AInterest, ADeadlineMs) <> 0;
end;

{ ---------------------------------------------------------------------------
  Primitives
  --------------------------------------------------------------------------- }

function FiberRecvT(AFd: Int; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;
var
  N: Int64;
  RdOnly: TIoInterests;
begin
  RdOnly := [ioRead];
  while True do
  begin
    N := Recv(AFd, ABuf, ALen, 0);
    if N >= 0 then
      Exit(N);                       { data (>0) or peer close (0) }
    if Interrupted(N) then
      Continue;                      { EINTR: retry }
    if WouldBlock(N) then
    begin
      if not WaitForIo(AFd, RdOnly, ADeadlineMs) then
        Exit(IO_ETIMEDOUT);
      Continue;                      { ready: retry the recv }
    end;
    Exit(N);                         { real error }
  end;
end;

function FiberRecv(AFd: Int; ABuf: Pointer; ALen: Int64): Int64;
begin
  Result := FiberRecvT(AFd, ABuf, ALen, 0);
end;

function FiberSendT(AFd: Int; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;
var
  N: Int64;
  WrOnly: TIoInterests;
begin
  WrOnly := [ioWrite];
  while True do
  begin
    N := Send(AFd, ABuf, ALen, MSG_NOSIGNAL());
    if N >= 0 then
      Exit(N);
    if Interrupted(N) then
      Continue;
    if WouldBlock(N) then
    begin
      if not WaitForIo(AFd, WrOnly, ADeadlineMs) then
        Exit(IO_ETIMEDOUT);
      Continue;
    end;
    Exit(N);
  end;
end;

function FiberSend(AFd: Int; ABuf: Pointer; ALen: Int64): Int64;
begin
  Result := FiberSendT(AFd, ABuf, ALen, 0);
end;

function FiberAcceptT(AListenFd: Int; ADeadlineMs: Int64): Int;
var
  Fd: Int;
  RdOnly: TIoInterests;
begin
  RdOnly := [ioRead];
  while True do
  begin
    Fd := c_accept4(AListenFd, nil, nil, SOCK_NONBLOCK());
    if Fd >= 0 then
      Exit(Fd);
    if Interrupted(Int64(Fd)) then
      Continue;
    if WouldBlock(Int64(Fd)) then
    begin
      if not WaitForIo(AListenFd, RdOnly, ADeadlineMs) then
        Exit(IO_ETIMEDOUT);
      Continue;
    end;
    if FdExhausted(Int64(Fd)) then
    begin
      { Out of file descriptors (EMFILE/ENFILE).  The pending SYN keeps the
        listener readable, so retrying immediately spins a core to no end — the
        accept cannot succeed until an in-flight connection closes and frees an
        fd.  Back off by parking on the timer heap so other fibers run and
        release their fds; then retry.  Off-scheduler (no fiber) there is no one
        to yield to, so surface the error to the blocking caller.  (GH #189) }
      if CurrentFiberTask() <> nil then
      begin
        FiberSleep(FD_EXHAUSTED_BACKOFF_MS);
        Continue;
      end;
      Exit(Fd);
    end;
    Exit(Fd);
  end;
end;

function FiberAccept(AListenFd: Int): Int;
begin
  Result := FiberAcceptT(AListenFd, 0);
end;

function FiberConnectT(AFd: Int; AAddr: Pointer; AAddrLen: Int; ADeadlineMs: Int64): Int;
var
  Rc, SoErr, OptLen: Int;
  WrOnly: TIoInterests;
  Peer: array[0..127] of Byte;
  PeerLen: Int32;
begin
  Rc := Connect(AFd, AAddr, AAddrLen);
  if Rc = 0 then
    Exit(0);                         { connected immediately (often loopback) }
  { Only a connect that is still completing is worth waiting for.  A real
    failure (ECONNREFUSED, ENETUNREACH, ...) is final: waiting on its socket
    could report it writable with SO_ERROR already cleared, and the dial would
    pass for a success. }
  if not ConnectPending(Int64(Rc)) then
    Exit(Rc);
  { Writable means the handshake finished, one way or the other.  Off a
    scheduler this waits in poll(2) -- before, a plain program gave up here on
    EINPROGRESS (BUG-20261106-http-client-plain-connect). }
  WrOnly := [ioWrite];
  if not WaitForIo(AFd, WrOnly, ADeadlineMs) then
    Exit(IO_ETIMEDOUT);
  SoErr := 0;
  OptLen := 4;
  if c_getsockopt(AFd, SOL_SOCKET_(), SO_ERROR_(), @SoErr, @OptLen) <> 0 then
    Exit(-1);
  if SoErr <> 0 then
    Exit(-SoErr);
  { SO_ERROR is 0 for a socket that connected, but also once a failure has
    been collected.  Having a peer address is the proof of a connection. }
  PeerLen := SizeOf(Peer);
  if c_getpeername(AFd, @Peer, @PeerLen) <> 0 then
    Exit(-1);
  Result := 0;
end;

function FiberConnect(AFd: Int; AAddr: Pointer; AAddrLen: Int): Int;
begin
  Result := FiberConnectT(AFd, AAddr, AAddrLen, 0);
end;

{ ---- name resolution off the worker thread ---------------------------------- }

function pthread_create(Thread: Pointer; Attr: Pointer;
  StartRoutine: Pointer; Arg: Pointer): Int32;
  external 'pthread' name 'pthread_create';
function pthread_detach(Thread: Int64): Int32;
  external 'pthread' name 'pthread_detach';
function c_pipe(AFds: Pointer): Int32; external name 'pipe';
function c_write(AFd: Int32; ABuf: Pointer; ALen: Int64): Int64;
  external name 'write';

type
  { One lookup in flight.  Shared by the parked fiber and the helper thread;
    ARC keeps it alive until both have let go.  The helper reports completion
    by writing a byte to a pipe the fiber is parked on: the same reactor path
    every other fiber wait uses, so it works under the single-worker
    scheduler (which has no cross-thread wake) as well as the multicore one. }
  TResolveJob = class
  public
    Host: string;
    Port: UInt16;
    Addrs: TResolvedAddrs;
    WriteFd: Int;
    Done: Int32;                  { set atomically once the helper is finished }
    constructor Create(const AHost: string; APort: UInt16; AWriteFd: Int);
  end;

constructor TResolveJob.Create(const AHost: string; APort: UInt16; AWriteFd: Int);
begin
  Host := AHost;
  Port := APort;
  WriteFd := AWriteFd;
  Done := 0;
end;

procedure ResolveThreadEntry(Arg: Pointer);
var
  Job: TResolveJob;
  B: Byte;
begin
  Job := TResolveJob(Arg);
  Job.Addrs := GResolveFunc(Job.Host, Job.Port);
  B := 1;
  c_write(Job.WriteFd, @B, 1);    { wakes the parked fiber; Addrs is final }
  CloseSocket(Job.WriteFd);
  _AtomicAddInt32(@Job.Done, 1);
end;

function ResolveHostFiber(const AHost: string; APort: UInt16): TResolvedAddrs;
var
  Job: TResolveJob;
  Fds: array[0..1] of Int32;
  Tid: Int64;
  Cancelled: Boolean;
begin
  if CurrentFiberTask() = nil then
    Exit(GResolveFunc(AHost, APort));
  if c_pipe(@Fds[0]) <> 0 then
    Exit(GResolveFunc(AHost, APort));      { no pipe: block rather than fail }
  SetNonBlocking(Fds[0]);
  Job := TResolveJob.Create(AHost, APort, Fds[1]);
  Tid := 0;
  if pthread_create(@Tid, nil, Pointer(@ResolveThreadEntry), Pointer(Job)) <> 0 then
  begin
    CloseSocket(Fds[0]);
    CloseSocket(Fds[1]);
    Exit(GResolveFunc(AHost, APort));      { no thread: block rather than fail }
  end;
  pthread_detach(Tid);
  Cancelled := False;
  try
    ParkForIo(Fds[0], [ioRead], 0);
  except
    Cancelled := True;
  end;
  { The helper has written (or is about to) and then closes its end; only then
    is it safe to drop ours, or its write would hit a closed pipe. }
  if Cancelled then
    while Job.Done = 0 do
      WaitFd(-1, False, 5);
  CloseSocket(Fds[0]);
  if Cancelled then
    raise EFiberCancelled.Create('fiber cancelled');
  Result := Job.Addrs;
end;

initialization
  GResolveFunc := @ResolveHost;

end.
