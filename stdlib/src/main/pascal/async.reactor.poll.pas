{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit async.reactor.poll;
// L2 of the fiber runtime (docs/async-networking-design.adoc, [#reactor]):
// a readiness adapter over poll(2), selected for Windows, where poll is
// runtime.net.windows' leaf over WSAPoll.  Nothing in it is Windows-specific
// -- it uses only poll, pipe, read, write and fcntl -- so it would serve any
// POSIX target as well; epoll and kqueue serve those better.
//
// The fd set lives here, not in the kernel, so the adapter keeps a table of
// registrations under a lock and every Wait polls a snapshot of it.  Several
// workers may Wait at once.  poll is level-triggered, and the scheduler
// expects the edge-triggered contract of the epoll and kqueue adapters: one
// delivery per park (async.io adds an fd, parks, and removes it on resume).
// So a delivered registration is DISARMED until it is removed or modified,
// and a delivery is checked against the table under the lock first, so a
// registration that went (or was replaced) while the poll ran is not
// reported.  A registration made while another thread is blocked in Wait
// wakes it, so the new fd joins the next snapshot at once.
//
// Wake writes a byte to a pipe whose read end is in every snapshot; Wait
// drains it and never reports it.  On Windows the pipe is a loopback socket
// pair (runtime.net.windows), so WSAPoll can wait on it.  A registration
// wakes only when some thread is blocked in Wait.

interface

uses
  SysUtils, Classes, async.reactor;

type
  TPollEntry = record
    Fd: Int;
    Interest: TIoInterests;
    Token: Pointer;
    Armed: Boolean;
    { distinguishes this registration from a later one of the same fd }
    Serial: Int64;
  end;

  { poll(2) adapter (level-triggered poll, delivered entries disarmed; pipe
    wake). }
  TPollReactor = class(TReactor)
  private
    FLock: TCriticalSection;
    FEntries: array of TPollEntry;
    FCount: Int;
    FSerial: Int64;
    FWakeRead: Int;
    FWakeWrite: Int;
    { threads blocked in Wait now: a registration wakes them only then }
    FWaiting: Int;
    function IndexOf(AFd: Int): Int;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Add(AFd: Int; AInterest: TIoInterests; AToken: Pointer); override;
    procedure Modify(AFd: Int; AInterest: TIoInterests; AToken: Pointer); override;
    procedure Remove(AFd: Int); override;
    function Wait(ATimeoutMs: Int; var AReady: TReadyList): Int; override;
    procedure Wake; override;
    function FdCount: Int; override;
  end;

{ The factory registered in async.reactor.GReactorFactory by this unit's
  initialization -- the same shape as the epoll and kqueue siblings. }
function CreateOsReactor: TReactor;

implementation

const
  POLLIN = $0001;
  POLLOUT = $0004;
  POLLERR = $0008;
  POLLHUP = $0010;
  POLLNVAL = $0020;
  F_GETFL = 3;
  F_SETFL = 4;
  PFD_SIZE = 8;
  DRAIN_SIZE = 64;

function c_poll(AFds: Pointer; ANFds: Int64; ATimeout: Int32): Int32;
  external name 'poll';
function c_pipe(AFds: Pointer): Int32; external name 'pipe';
function c_read(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64;
  external name 'read';
function c_write(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64;
  external name 'write';
function c_close(AFd: Int32): Int32; external name 'close';
function c_fcntl(AFd, ACmd: Int32): Int32; cdecl; varargs; external name 'fcntl';
function _ONonBlock: Int32; external name '_ONonBlock';

type
  { One snapshot entry: what was polled for, and which registration. }
  TPolled = record
    Fd: Int;
    Serial: Int64;
  end;

function EventsOf(AInterest: TIoInterests): Int16;
begin
  Result := 0;
  if ioRead in AInterest then
    Result := Result or POLLIN;
  if ioWrite in AInterest then
    Result := Result or POLLOUT;
end;

{ An error or hang-up is reported as both read and write ready, as the
  epoll adapter does, so the parked fiber retries its operation and meets
  the error there. }
function InterestOf(AEvents: Int16): TIoInterests;
begin
  Result := [];
  if (AEvents and POLLIN) <> 0 then
    Include(Result, ioRead);
  if (AEvents and POLLOUT) <> 0 then
    Include(Result, ioWrite);
  if (AEvents and (POLLERR or POLLHUP or POLLNVAL)) <> 0 then
    Result := [ioRead, ioWrite];
end;

procedure MakeNonBlocking(AFd: Int);
var
  Flags: Int32;
begin
  Flags := c_fcntl(AFd, F_GETFL);
  if Flags < 0 then
    Flags := 0;
  c_fcntl(AFd, F_SETFL, Flags or _ONonBlock());
end;

constructor TPollReactor.Create;
var
  Fds: array[0..1] of Int32;
begin
  if c_pipe(@Fds[0]) <> 0 then
    raise Exception.Create('pipe failed');
  Self.FWakeRead := Fds[0];
  Self.FWakeWrite := Fds[1];
  { neither the drain nor a wake may ever block }
  MakeNonBlocking(Self.FWakeRead);
  MakeNonBlocking(Self.FWakeWrite);
  Self.FWaiting := 0;
  Self.FLock := TCriticalSection.Create();
  Self.FCount := 0;
  Self.FSerial := 0;
end;

destructor TPollReactor.Destroy;
begin
  c_close(Self.FWakeRead);
  c_close(Self.FWakeWrite);
  Self.FLock.Free();
  inherited Destroy();
end;

{ The index of AFd's registration, or -1; FLock held. }
function TPollReactor.IndexOf(AFd: Int): Int;
var
  I: Int;
begin
  for I := 0 to Self.FCount - 1 do
    if Self.FEntries[I].Fd = AFd then
      Exit(I);
  Result := -1;
end;

procedure TPollReactor.Add(AFd: Int; AInterest: TIoInterests; AToken: Pointer);
var
  I: Int;
  Waiting: Boolean;
begin
  Self.FLock.Enter();
  try
    I := Self.IndexOf(AFd);
    if I < 0 then
    begin
      if Self.FCount >= Length(Self.FEntries) then
        SetLength(Self.FEntries, Self.FCount * 2 + 16);
      I := Self.FCount;
      Self.FCount := Self.FCount + 1;
    end;
    Self.FSerial := Self.FSerial + 1;
    Self.FEntries[I].Fd := AFd;
    Self.FEntries[I].Interest := AInterest;
    Self.FEntries[I].Token := AToken;
    Self.FEntries[I].Armed := True;
    Self.FEntries[I].Serial := Self.FSerial;
    Waiting := Self.FWaiting > 0;
  finally
    Self.FLock.Leave();
  end;
  if Waiting then
    Self.Wake();
end;

procedure TPollReactor.Modify(AFd: Int; AInterest: TIoInterests; AToken: Pointer);
begin
  Self.Add(AFd, AInterest, AToken);
end;

procedure TPollReactor.Remove(AFd: Int);
var
  I: Int;
begin
  Self.FLock.Enter();
  try
    I := Self.IndexOf(AFd);
    if I >= 0 then
    begin
      Self.FCount := Self.FCount - 1;
      Self.FEntries[I] := Self.FEntries[Self.FCount];
    end;
  finally
    Self.FLock.Leave();
  end;
end;

procedure TPollReactor.Wake;
var
  B: Byte;
begin
  B := 1;
  c_write(Self.FWakeWrite, @B, 1);
end;

function TPollReactor.Wait(ATimeoutMs: Int; var AReady: TReadyList): Int;
var
  Polled: array of TPolled;
  Pfds: array of Byte;
  N, I, J, Rc: Int;
  Events: Int16;
  Drain: array[0..DRAIN_SIZE - 1] of Byte;
  Timeout: Int32;
begin
  Result := 0;
  { the snapshot: the wake pipe first, then every armed registration }
  Self.FLock.Enter();
  try
    SetLength(Polled, Self.FCount + 1);
    SetLength(Pfds, (Self.FCount + 1) * PFD_SIZE);
    PInt32(@Pfds[0])^ := Int32(Self.FWakeRead);
    PInt16(@Pfds[4])^ := POLLIN;
    PInt16(@Pfds[6])^ := 0;
    N := 1;
    for I := 0 to Self.FCount - 1 do
      if Self.FEntries[I].Armed then
      begin
        Polled[N].Fd := Self.FEntries[I].Fd;
        Polled[N].Serial := Self.FEntries[I].Serial;
        PInt32(@Pfds[N * PFD_SIZE])^ := Int32(Self.FEntries[I].Fd);
        PInt16(@Pfds[N * PFD_SIZE + 4])^ := EventsOf(Self.FEntries[I].Interest);
        PInt16(@Pfds[N * PFD_SIZE + 6])^ := 0;
        N := N + 1;
      end;
    Self.FWaiting := Self.FWaiting + 1;
  finally
    Self.FLock.Leave();
  end;
  if ATimeoutMs < 0 then
    Timeout := -1
  else if ATimeoutMs > High(Int32) then
    Timeout := High(Int32)
  else
    Timeout := Int32(ATimeoutMs);
  Rc := c_poll(@Pfds[0], N, Timeout);
  Self.FLock.Enter();
  Self.FWaiting := Self.FWaiting - 1;
  Self.FLock.Leave();
  if Rc <= 0 then
    Exit;
  if PInt16(@Pfds[6])^ <> 0 then
  begin
    { the wake: drain it, report nothing for it }
    while c_read(Self.FWakeRead, @Drain[0], DRAIN_SIZE) > 0 do
      ;
  end;
  if Length(AReady) < N then
    SetLength(AReady, N);
  Self.FLock.Enter();
  try
    for I := 1 to N - 1 do
    begin
      Events := PInt16(@Pfds[I * PFD_SIZE + 6])^;
      if Events = 0 then
        Continue;
      J := Self.IndexOf(Polled[I].Fd);
      if (J < 0) or (Self.FEntries[J].Serial <> Polled[I].Serial) or
         not Self.FEntries[J].Armed then
        Continue;
      Self.FEntries[J].Armed := False;
      AReady[Result].Token := Self.FEntries[J].Token;
      AReady[Result].Events := InterestOf(Events);
      Result := Result + 1;
    end;
  finally
    Self.FLock.Leave();
  end;
end;

function TPollReactor.FdCount: Int;
begin
  Self.FLock.Enter();
  try
    Result := Self.FCount;
  finally
    Self.FLock.Leave();
  end;
end;

function CreateOsReactor: TReactor;
begin
  Result := TPollReactor.Create();
end;

initialization
  GReactorFactory := @CreateOsReactor;

end.
