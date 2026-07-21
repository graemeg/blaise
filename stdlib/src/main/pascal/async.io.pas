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
// scheduler is running (a plain program) it falls back to a true blocking call,
// so the same source works in both worlds.  EINTR is retried transparently; a
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

const
  { Negative sentinels the primitives return in addition to the raw kernel
    error (which is also negative in the static profile).  ETIMEDOUT is the
    deadline result; the raw signed count is returned otherwise. }
  IO_ETIMEDOUT = -2;

{ Receive up to ALen bytes from AFd into ABuf.  Returns the byte count (>0),
  0 on peer close (EOF), a negative kernel error, or IO_ETIMEDOUT.  Parks the
  fiber on readability while the socket would block. }
function FiberRecv(AFd: Integer; ABuf: Pointer; ALen: Int64): Int64;
function FiberRecvT(AFd: Integer; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;

{ Send up to ALen bytes from ABuf to AFd.  Returns the byte count written (>0),
  a negative kernel error, or IO_ETIMEDOUT.  Parks on writability for a short
  write. }
function FiberSend(AFd: Integer; ABuf: Pointer; ALen: Int64): Int64;
function FiberSendT(AFd: Integer; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;

{ Accept the next connection on a listening socket.  Returns the connected fd
  (>=0, set non-blocking), a negative kernel error, or IO_ETIMEDOUT.  Parks on
  readability. }
function FiberAccept(AListenFd: Integer): Integer;
function FiberAcceptT(AListenFd: Integer; ADeadlineMs: Int64): Integer;

{ Connect AFd (must be non-blocking) to AAddr (a TSockAddrIn pointer, ALen
  bytes).  Returns 0 on success, a negative kernel error, or IO_ETIMEDOUT.
  Parks on writability then checks SO_ERROR. }
function FiberConnect(AFd: Integer; AAddr: Pointer; AAddrLen: Integer): Integer;
function FiberConnectT(AFd: Integer; AAddr: Pointer; AAddrLen: Integer; ADeadlineMs: Int64): Integer;

{ Flip AFd to non-blocking (the fiber I/O primitives require it). }
procedure SetNonBlocking(AFd: Integer);

implementation

uses
  SysUtils, async.fibers, async.reactor, Net.Sockets;

{ WouldBlock/Interrupted/FdExhausted are the P3 errno abstraction
  (runtime.errno.*), swapped per build profile at link time. }
function WouldBlock(N: Int64): Boolean; external name 'WouldBlock';
function Interrupted(N: Int64): Boolean; external name 'Interrupted';
{ True when the call failed with EMFILE/ENFILE (out of file descriptors).
  Such a call cannot succeed until an fd is freed, so retrying it in a tight
  loop just burns a core — the accept path backs off instead (GH #189). }
function FdExhausted(N: Int64): Boolean; external name 'FdExhausted';

const
  { Back-off between accept retries when the process is out of file descriptors.
    Long enough that a spin can't peg a core, short enough that the listener
    resumes accepting promptly once in-flight connections close and free fds. }
  FD_EXHAUSTED_BACKOFF_MS = 10;

function c_fcntl3(AFd, ACmd, AArg: Integer): Integer; external name 'fcntl';
function c_accept4(AFd: Integer; AAddr, AAddrLen: Pointer; AFlags: Integer): Integer;
  external name 'accept4';
function c_getsockopt(AFd, ALevel, AOptName: Integer; AOptVal, AOptLen: Pointer): Integer;
  external name 'getsockopt';

const
  F_GETFL     = 3;
  F_SETFL     = 4;

{ OS-divergent socket/fcntl constants from the per-target
  rtl.platform.layout.<os> seam (Linux/FreeBSD values differ for all four). }
function O_NONBLOCK: Integer;    external name '_ONonBlock';
function SOCK_NONBLOCK: Integer; external name '_SockNonBlock';  { accept4 flag }
function SOL_SOCKET_: Integer;   external name '_SolSocket';
function SO_ERROR_: Integer;     external name '_SoError';

type
  PInteger = ^Integer;

procedure SetNonBlocking(AFd: Integer);
var
  Fl: Integer;
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
function ParkForIo(AFd: Integer; AInterest: TIoInterests; ADeadlineMs: Int64): Boolean;
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

{ ---------------------------------------------------------------------------
  Primitives
  --------------------------------------------------------------------------- }

function FiberRecvT(AFd: Integer; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;
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
      if CurrentFiberTask() <> nil then
      begin
        if not ParkForIo(AFd, RdOnly, ADeadlineMs) then
          Exit(IO_ETIMEDOUT);
        Continue;                    { woken: retry the recv }
      end;
      { No scheduler: true blocking fallback via a blocking read.  Clear
        O_NONBLOCK so the kernel blocks us. }
      c_fcntl3(AFd, F_SETFL, c_fcntl3(AFd, F_GETFL, 0) and (not O_NONBLOCK()));
      Continue;
    end;
    Exit(N);                         { real error }
  end;
end;

function FiberRecv(AFd: Integer; ABuf: Pointer; ALen: Int64): Int64;
begin
  Result := FiberRecvT(AFd, ABuf, ALen, 0);
end;

function FiberSendT(AFd: Integer; ABuf: Pointer; ALen: Int64; ADeadlineMs: Int64): Int64;
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
      if CurrentFiberTask() <> nil then
      begin
        if not ParkForIo(AFd, WrOnly, ADeadlineMs) then
          Exit(IO_ETIMEDOUT);
        Continue;
      end;
      c_fcntl3(AFd, F_SETFL, c_fcntl3(AFd, F_GETFL, 0) and (not O_NONBLOCK()));
      Continue;
    end;
    Exit(N);
  end;
end;

function FiberSend(AFd: Integer; ABuf: Pointer; ALen: Int64): Int64;
begin
  Result := FiberSendT(AFd, ABuf, ALen, 0);
end;

function FiberAcceptT(AListenFd: Integer; ADeadlineMs: Int64): Integer;
var
  Fd: Integer;
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
      if CurrentFiberTask() <> nil then
      begin
        if not ParkForIo(AListenFd, RdOnly, ADeadlineMs) then
          Exit(IO_ETIMEDOUT);
        Continue;
      end;
      c_fcntl3(AListenFd, F_SETFL,
        c_fcntl3(AListenFd, F_GETFL, 0) and (not O_NONBLOCK()));
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

function FiberAccept(AListenFd: Integer): Integer;
begin
  Result := FiberAcceptT(AListenFd, 0);
end;

function FiberConnectT(AFd: Integer; AAddr: Pointer; AAddrLen: Integer; ADeadlineMs: Int64): Integer;
var
  Rc, SoErr, OptLen: Integer;
  WrOnly: TIoInterests;
begin
  Rc := Connect(AFd, AAddr, AAddrLen);
  if Rc = 0 then
    Exit(0);                         { connected immediately (loopback) }
  { EINPROGRESS surfaces as would-block on a non-blocking connect. }
  if WouldBlock(Int64(Rc)) or (Rc < 0) then
  begin
    if CurrentFiberTask() <> nil then
    begin
      WrOnly := [ioWrite];
      if not ParkForIo(AFd, WrOnly, ADeadlineMs) then
        Exit(IO_ETIMEDOUT);
      { Writable: check SO_ERROR to learn if the connect succeeded. }
      SoErr := 0;
      OptLen := 4;
      if c_getsockopt(AFd, SOL_SOCKET_(), SO_ERROR_(), @SoErr, @OptLen) <> 0 then
        Exit(-1);
      if SoErr = 0 then
        Exit(0);
      Exit(-SoErr);
    end;
    Exit(Rc);
  end;
  Result := Rc;
end;

function FiberConnect(AFd: Integer; AAddr: Pointer; AAddrLen: Integer): Integer;
begin
  Result := FiberConnectT(AFd, AAddr, AAddrLen, 0);
end;

end.
