{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit async.reactor.epoll;

// L2 of the fiber runtime (docs/async-networking-design.adoc, [#reactor]):
// the Linux readiness adapter.  TEpollReactor is EDGE-TRIGGERED (EPOLLET):
// the fd stays registered across readiness and L3 drains it to EAGAIN before
// parking again.  Wake is an eventfd registered on the same epoll and drained
// inside Wait so it never spuriously delivers.  The token travels in
// epoll_event.data.ptr so Wait returns tokens with no side table.
//
// Bindings are Linux libc calls (epoll_*, eventfd, read) — the same posture
// as Net.Sockets binding socket/recv.  The static path swaps these for raw
// syscall stubs later; TReactor's surface does not change.
//
// This unit is selected by async.reactor's single target-driven seam; its
// FreeBSD sibling is async.reactor.kqueue.  Both export the same
// CreateOsReactor factory so the seam is one uses-clause choice.

interface

uses
  SysUtils, async.reactor;

type
  { Linux epoll adapter (edge-triggered, eventfd wake). }
  TEpollReactor = class(TReactor)
  private
    FEpFd: Int;        { the epoll instance }
    FWakeFd: Int;      { eventfd for cross-thread Wake, registered on FEpFd }
    FEventBuf: Pointer;    { array of epoll_event (12 bytes each, packed) }
    FEventCap: Int;    { capacity of FEventBuf in events }
    FCount: Int;       { fds registered by callers (excludes the wake fd) }
    procedure Ctl(AOp, AFd: Int; AInterest: TIoInterests; AToken: Pointer);
    procedure EnsureBuf(ACap: Int);
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

{ The per-OS factory registered in async.reactor.GReactorFactory by this
  unit's initialization — same shape in the kqueue sibling. }
function CreateOsReactor: TReactor;

implementation

const
  { epoll_create1 / epoll_ctl / epoll_event flags (Linux x86_64). }
  EPOLL_CLOEXEC = $80000;     { O_CLOEXEC }
  EPOLL_CTL_ADD = 1;
  EPOLL_CTL_DEL = 2;
  EPOLL_CTL_MOD = 3;

  EPOLLIN  = $001;
  EPOLLOUT = $004;
  EPOLLERR = $008;
  EPOLLHUP = $010;
  EPOLLRDHUP = $2000;
  EPOLLET  = Int64($80000000);   { edge-triggered; high bit of the 32-bit mask }

  EFD_CLOEXEC   = $80000;
  EFD_NONBLOCK  = $800;

  EPOLL_EVENT_SIZE = 12;         { packed: uint32 events + uint64 data }
  DEFAULT_EVENTS   = 64;

type
  PByte = ^Byte;
  PInt64 = ^Int64;
  PUInt32 = ^UInt32;

{ --- libc bindings (same pattern as Net.Sockets) --- }

function c_epoll_create1(AFlags: Int32): Int32;
  external name 'epoll_create1';
function c_epoll_ctl(AEpFd, AOp, AFd: Int32; AEvent: Pointer): Int32;
  external name 'epoll_ctl';
function c_epoll_wait(AEpFd: Int32; AEvents: Pointer; AMaxEvents, ATimeout: Int32): Int32;
  external name 'epoll_wait';
function c_eventfd(AInitVal, AFlags: Int32): Int32;
  external name 'eventfd';
function c_close(AFd: Int32): Int32;
  external name 'close';
function c_read(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64;
  external name 'read';
function c_write(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64;
  external name 'write';

{ Compose the epoll event mask from an interest set, always edge-triggered. }
function InterestToMask(AInterest: TIoInterests): UInt32;
var
  M: Int64;
begin
  M := EPOLLET;
  if ioRead in AInterest then
    M := M or EPOLLIN;
  if ioWrite in AInterest then
    M := M or EPOLLOUT;
  Result := UInt32(M);
end;

{ Decode a delivered epoll event mask into an interest set.  An error/hangup is
  reported as BOTH read and write ready so the parked fiber wakes, retries the
  real op, and sees the true error/EOF there. }
function MaskToInterest(AMask: UInt32): TIoInterests;
var
  M: Int64;
begin
  M := Int64(AMask);
  Result := [];
  if (M and EPOLLIN) <> 0 then
    Include(Result, ioRead);
  if (M and EPOLLOUT) <> 0 then
    Include(Result, ioWrite);
  if (M and (EPOLLERR or EPOLLHUP or EPOLLRDHUP)) <> 0 then
    Result := [ioRead, ioWrite];
end;

{ ---------------------------------------------------------------------------
  TEpollReactor
  --------------------------------------------------------------------------- }

constructor TEpollReactor.Create;
var
  RdOnly: TIoInterests;
begin
  Self.FEpFd := c_epoll_create1(EPOLL_CLOEXEC);
  if Self.FEpFd < 0 then
    raise Exception.Create('epoll_create1 failed');
  { A counting eventfd, non-blocking so the Wait-side drain never blocks. }
  Self.FWakeFd := c_eventfd(0, EFD_CLOEXEC or EFD_NONBLOCK);
  if Self.FWakeFd < 0 then
    raise Exception.Create('eventfd failed');
  Self.FCount := 0;
  Self.FEventBuf := nil;
  Self.FEventCap := 0;
  Self.EnsureBuf(DEFAULT_EVENTS);
  { Register the wake fd (level-triggered read; token nil marks it internal). }
  RdOnly := [ioRead];
  Self.Ctl(EPOLL_CTL_ADD, Self.FWakeFd, RdOnly, nil);
end;

destructor TEpollReactor.Destroy;
begin
  if Self.FEventBuf <> nil then
  begin
    FreeMem(Self.FEventBuf);
    Self.FEventBuf := nil;
  end;
  if Self.FWakeFd >= 0 then
    c_close(Self.FWakeFd);
  if Self.FEpFd >= 0 then
    c_close(Self.FEpFd);
  inherited Destroy();
end;

procedure TEpollReactor.EnsureBuf(ACap: Int);
begin
  if ACap <= Self.FEventCap then
    Exit;
  if Self.FEventBuf <> nil then
    FreeMem(Self.FEventBuf);
  Self.FEventBuf := GetMem(ACap * EPOLL_EVENT_SIZE);
  Self.FEventCap := ACap;
end;

{ Build one epoll_event on the stack (12 bytes, packed) and issue epoll_ctl.
  For the wake fd the mask is level-triggered EPOLLIN (no EPOLLET) so a pending
  count always re-delivers until drained. }
procedure TEpollReactor.Ctl(AOp, AFd: Int; AInterest: TIoInterests; AToken: Pointer);
var
  Ev: array[0..EPOLL_EVENT_SIZE - 1] of Byte;
  PMask: PUInt32;
  PData: PInt64;
  Mask: UInt32;
  Rc: Int;
begin
  if AFd = Self.FWakeFd then
    Mask := UInt32(EPOLLIN)         { level-triggered wake }
  else
    Mask := InterestToMask(AInterest);
  PMask := PUInt32(@Ev[0]);
  PMask^ := Mask;
  PData := PInt64(@Ev[4]);
  PData^ := Int64(UInt(AToken));
  Rc := c_epoll_ctl(Self.FEpFd, AOp, AFd, @Ev[0]);
  if (Rc <> 0) and (AOp <> EPOLL_CTL_DEL) then
    raise Exception.Create('epoll_ctl failed');
end;

procedure TEpollReactor.Add(AFd: Int; AInterest: TIoInterests; AToken: Pointer);
begin
  Self.Ctl(EPOLL_CTL_ADD, AFd, AInterest, AToken);
  Self.FCount := Self.FCount + 1;
end;

procedure TEpollReactor.Modify(AFd: Int; AInterest: TIoInterests; AToken: Pointer);
begin
  Self.Ctl(EPOLL_CTL_MOD, AFd, AInterest, AToken);
end;

procedure TEpollReactor.Remove(AFd: Int);
var
  Empty: TIoInterests;
begin
  Empty := [];
  Self.Ctl(EPOLL_CTL_DEL, AFd, Empty, nil);
  if Self.FCount > 0 then
    Self.FCount := Self.FCount - 1;
end;

procedure TEpollReactor.Wake;
var
  One: Int64;
begin
  { Post 1 to the counting eventfd; a blocked epoll_wait returns with FWakeFd
    readable.  Non-blocking write; a full counter (never realistic at 2^64-1)
    would EAGAIN and is harmless — a wake is already pending. }
  One := 1;
  c_write(Self.FWakeFd, @One, 8);
end;

function TEpollReactor.Wait(ATimeoutMs: Int; var AReady: TReadyList): Int;
var
  N, I, OutN: Int;
  PEv: PByte;
  PMask: PUInt32;
  PData: PInt64;
  Mask: UInt32;
  Token: Pointer;
  Drain: Int64;
begin
  Self.EnsureBuf(DEFAULT_EVENTS);
  N := c_epoll_wait(Self.FEpFd, Self.FEventBuf,
    Self.FEventCap, ATimeoutMs);
  if N <= 0 then
  begin
    { N < 0 is EINTR/error: report nothing ready, caller re-loops. }
    Result := 0;
    Exit;
  end;
  if Length(AReady) < N then
    SetLength(AReady, N);
  OutN := 0;
  for I := 0 to N - 1 do
  begin
    PEv := PByte(UInt(Self.FEventBuf) + UInt(I * EPOLL_EVENT_SIZE));
    PMask := PUInt32(PEv);
    PData := PInt64(PByte(UInt(PEv) + 4));
    Mask := PMask^;
    Token := Pointer(UInt(PData^));
    if Token = nil then
    begin
      { The wake eventfd: drain the counter so it does not re-deliver, and do
        NOT surface it as a ready entry. }
      Drain := 0;
      while c_read(Self.FWakeFd, @Drain, 8) = 8 do
        ;    { loop until EAGAIN on the non-blocking eventfd }
      Continue;
    end;
    AReady[OutN].Token := Token;
    AReady[OutN].Events := MaskToInterest(Mask);
    OutN := OutN + 1;
  end;
  Result := OutN;
end;

function TEpollReactor.FdCount: Int;
begin
  Result := Self.FCount;
end;

function CreateOsReactor: TReactor;
begin
  Result := TEpollReactor.Create();
end;

initialization
  GReactorFactory := @CreateOsReactor;

end.
