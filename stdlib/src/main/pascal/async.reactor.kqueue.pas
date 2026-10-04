{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit async.reactor.kqueue;

// L2 of the fiber runtime (docs/async-networking-design.adoc, [#reactor]):
// the FreeBSD and macOS readiness adapter.  TKqueueReactor uses kevent(2) with
// EVFILT_READ/EVFILT_WRITE and EV_CLEAR for edge-triggered semantics — the
// kqueue analogue of TEpollReactor's EPOLLET posture: the fd stays registered
// across readiness and L3 drains it to EAGAIN before parking again.  Wake is
// an EVFILT_USER event (no fd at all) triggered with NOTE_TRIGGER; EV_CLEAR
// auto-resets it after delivery, so there is nothing to drain.  The token
// travels in kevent.udata so Wait returns tokens with no side table.
//
// kqueue registers READ and WRITE as two separate filters where epoll uses
// one mask, so interest changes are per-filter EV_ADD/EV_DELETE pairs
// (re-adding an existing filter just updates its udata; deleting an absent
// one is ignored).  An fd ready for both may deliver two entries with the
// same token — the scheduler's resume path is idempotent.
//
// struct kevent: ident@0, filter@8 (i16), flags@10 (u16), fflags@12 (u32),
// data@16 (i64), udata@24 (ptr) on both systems.  FreeBSD 12+ appends ext[4]
// (64 bytes in all); Darwin's 64-bit struct kevent ends at udata (32 bytes).
// EVFILT_USER is -11 on FreeBSD but -10 on Darwin; every other constant used
// here is identical (verified against the macOS SDK <sys/event.h>).
// Bindings are libc calls (kqueue/kevent), the same posture as Net.Sockets
// binding socket/recv.
//
// This unit is selected by async.reactor's single target-driven seam; its
// Linux sibling is async.reactor.epoll.  Both export the same CreateOsReactor
// factory so the seam is one uses-clause choice.

interface

uses
  SysUtils, async.reactor;

type
  { FreeBSD / macOS kqueue adapter (EV_CLEAR edge semantics, EVFILT_USER
    wake). }
  TKqueueReactor = class(TReactor)
  private
    FKq: Integer;          { the kqueue instance }
    FEventBuf: Pointer;    { array of struct kevent (KEVENT_SIZE bytes each) }
    FEventCap: Integer;    { capacity of FEventBuf in events }
    FCount: Integer;       { fds registered by callers (excludes the wake event) }
    procedure EnsureBuf(ACap: Integer);
    function Change(AIdent: Int64; AFilter, AFlags: Integer; AFflags: UInt32;
      AToken: Pointer): Integer;
    procedure ApplyInterest(AFd: Integer; AInterest: TIoInterests; AToken: Pointer);
  public
    constructor Create;
    destructor Destroy; override;
    procedure Add(AFd: Integer; AInterest: TIoInterests; AToken: Pointer); override;
    procedure Modify(AFd: Integer; AInterest: TIoInterests; AToken: Pointer); override;
    procedure Remove(AFd: Integer); override;
    function Wait(ATimeoutMs: Integer; var AReady: TReadyList): Integer; override;
    procedure Wake; override;
    function FdCount: Integer; override;
  end;

{ The per-OS factory registered in async.reactor.GReactorFactory by this
  unit's initialization — same shape in the epoll sibling. }
function CreateOsReactor: TReactor;

implementation

const
  { kevent filters.  Held as their unsigned 16-bit encodings because
    filter+flags are packed into one 32-bit store/load (filter is a signed
    short at byte 8, flags a u16 at byte 10). }
  FILT_READ_U16  = $FFFF;   { EVFILT_READ  = -1 }
  FILT_WRITE_U16 = $FFFE;   { EVFILT_WRITE = -2 }
{$IFDEF DARWIN}
  FILT_USER_U16  = $FFF6;   { EVFILT_USER  = -10 on Darwin }
{$ELSE}
  FILT_USER_U16  = $FFF5;   { EVFILT_USER  = -11 on FreeBSD }
{$ENDIF}

  EV_ADD     = $0001;
  EV_DELETE  = $0002;
  EV_CLEAR   = $0020;
  EV_ERROR   = $4000;
  EV_EOF     = $8000;

  NOTE_TRIGGER = $01000000;

{$IFDEF DARWIN}
  KEVENT_SIZE    = 32;      { Darwin 64-bit struct kevent (ends at udata) }
{$ELSE}
  KEVENT_SIZE    = 64;      { FreeBSD 12+ struct kevent (with ext[4]) }
{$ENDIF}
  DEFAULT_EVENTS = 64;

type
  PByte = ^Byte;
  PInt64 = ^Int64;
  PUInt32 = ^UInt32;

  TTimeSpec = record
    Sec: Int64;
    NSec: Int64;
  end;

{ --- libc bindings (same pattern as Net.Sockets) --- }

function c_kqueue: Integer;
  external name 'kqueue';
function c_kevent(AKq: Integer; AChanges: Pointer; ANChanges: Integer;
  AEvents: Pointer; ANEvents: Integer; ATimeout: Pointer): Integer;
  external name 'kevent';
function c_close(AFd: Integer): Integer;
  external name 'close';

{ ---------------------------------------------------------------------------
  TKqueueReactor
  --------------------------------------------------------------------------- }

constructor TKqueueReactor.Create;
begin
  Self.FKq := c_kqueue();
  if Self.FKq < 0 then
    raise Exception.Create('kqueue failed');
  Self.FCount := 0;
  Self.FEventBuf := nil;
  Self.FEventCap := 0;
  Self.EnsureBuf(DEFAULT_EVENTS);
  { Register the wake event: EVFILT_USER ident 0, EV_CLEAR so a delivered wake
    auto-resets (token nil marks it internal, mirroring the eventfd posture). }
  if Self.Change(0, FILT_USER_U16, EV_ADD or EV_CLEAR, 0, nil) < 0 then
    raise Exception.Create('kevent EVFILT_USER add failed');
end;

destructor TKqueueReactor.Destroy;
begin
  if Self.FEventBuf <> nil then
  begin
    FreeMem(Self.FEventBuf);
    Self.FEventBuf := nil;
  end;
  if Self.FKq >= 0 then
    c_close(Self.FKq);
  inherited Destroy();
end;

procedure TKqueueReactor.EnsureBuf(ACap: Integer);
begin
  if ACap <= Self.FEventCap then
    Exit;
  if Self.FEventBuf <> nil then
    FreeMem(Self.FEventBuf);
  Self.FEventBuf := GetMem(ACap * KEVENT_SIZE);
  Self.FEventCap := ACap;
end;

{ Build one struct kevent on the stack and submit it as a single change with
  no event slots (errors surface as the -1 return).  filter+flags share one
  32-bit little-endian store: low 16 = filter, high 16 = flags. }
function TKqueueReactor.Change(AIdent: Int64; AFilter, AFlags: Integer;
  AFflags: UInt32; AToken: Pointer): Integer;
var
  Ev: array[0..KEVENT_SIZE - 1] of Byte;
  I: Integer;
  PIdent: PInt64;
  PFiltFlags: PUInt32;
  PFflags: PUInt32;
  PUdata: PInt64;
begin
  for I := 0 to KEVENT_SIZE - 1 do
    Ev[I] := 0;
  PIdent := PInt64(@Ev[0]);
  PIdent^ := AIdent;
  PFiltFlags := PUInt32(@Ev[8]);
  PFiltFlags^ := (UInt32(AFlags) shl 16) or (UInt32(AFilter) and $FFFF);
  PFflags := PUInt32(@Ev[12]);
  PFflags^ := AFflags;
  PUdata := PInt64(@Ev[24]);
  PUdata^ := Int64(PtrUInt(AToken));
  Result := c_kevent(Self.FKq, @Ev[0], 1, nil, 0, nil);
end;

{ Reconcile the two kqueue filters with the requested interest set: wanted
  filters are (re-)added — EV_ADD on an existing filter just updates udata —
  and unwanted ones deleted, ignoring "was not registered" failures.  This
  serves both Add (fresh fd: deletes are no-ops) and Modify. }
procedure TKqueueReactor.ApplyInterest(AFd: Integer; AInterest: TIoInterests;
  AToken: Pointer);
begin
  if ioRead in AInterest then
  begin
    if Self.Change(AFd, FILT_READ_U16, EV_ADD or EV_CLEAR, 0, AToken) < 0 then
      raise Exception.Create('kevent add (read) failed');
  end
  else
    Self.Change(AFd, FILT_READ_U16, EV_DELETE, 0, nil);
  if ioWrite in AInterest then
  begin
    if Self.Change(AFd, FILT_WRITE_U16, EV_ADD or EV_CLEAR, 0, AToken) < 0 then
      raise Exception.Create('kevent add (write) failed');
  end
  else
    Self.Change(AFd, FILT_WRITE_U16, EV_DELETE, 0, nil);
end;

procedure TKqueueReactor.Add(AFd: Integer; AInterest: TIoInterests; AToken: Pointer);
begin
  Self.ApplyInterest(AFd, AInterest, AToken);
  Self.FCount := Self.FCount + 1;
end;

procedure TKqueueReactor.Modify(AFd: Integer; AInterest: TIoInterests; AToken: Pointer);
begin
  Self.ApplyInterest(AFd, AInterest, AToken);
end;

procedure TKqueueReactor.Remove(AFd: Integer);
begin
  { Delete both filters; an fd registered for only one direction reports a
    harmless failure on the other. }
  Self.Change(AFd, FILT_READ_U16, EV_DELETE, 0, nil);
  Self.Change(AFd, FILT_WRITE_U16, EV_DELETE, 0, nil);
  if Self.FCount > 0 then
    Self.FCount := Self.FCount - 1;
end;

procedure TKqueueReactor.Wake;
begin
  { Trigger the EVFILT_USER event; a blocked kevent returns with it pending.
    Repeated triggers coalesce, so cross-thread racing wakes are harmless. }
  Self.Change(0, FILT_USER_U16, 0, NOTE_TRIGGER, nil);
end;

function TKqueueReactor.Wait(ATimeoutMs: Integer; var AReady: TReadyList): Integer;
var
  Ts: TTimeSpec;
  TsPtr: Pointer;
  N, I, OutN: Integer;
  PEv: PByte;
  PFiltFlags: PUInt32;
  PUdata: PInt64;
  FiltFlags: UInt32;
  Filt: UInt32;
  Flags: UInt32;
  Token: Pointer;
  Events: TIoInterests;
begin
  Self.EnsureBuf(DEFAULT_EVENTS);
  if ATimeoutMs < 0 then
    TsPtr := nil                    { indefinite — a Wake interrupts it }
  else
  begin
    Ts.Sec := ATimeoutMs div 1000;
    Ts.NSec := Int64(ATimeoutMs mod 1000) * Int64(1000000);
    TsPtr := @Ts;
  end;
  N := c_kevent(Self.FKq, nil, 0, Self.FEventBuf, Self.FEventCap, TsPtr);
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
    PEv := PByte(PtrUInt(Self.FEventBuf) + PtrUInt(I * KEVENT_SIZE));
    PFiltFlags := PUInt32(PByte(PtrUInt(PEv) + 8));
    PUdata := PInt64(PByte(PtrUInt(PEv) + 24));
    FiltFlags := PFiltFlags^;
    Filt := FiltFlags and $FFFF;
    Flags := FiltFlags shr 16;
    Token := Pointer(PtrUInt(PUdata^));
    if (Filt = FILT_USER_U16) or (Token = nil) then
      Continue;                     { the wake event: EV_CLEAR already reset it }
    if Filt = FILT_READ_U16 then
      Events := [ioRead]
    else if Filt = FILT_WRITE_U16 then
      Events := [ioWrite]
    else
      Events := [];
    { EOF/error: report BOTH directions ready so the parked fiber wakes,
      retries the real op, and sees the true error/EOF there — the same
      posture as the epoll adapter's EPOLLERR/EPOLLHUP decode. }
    if (Flags and (EV_ERROR or EV_EOF)) <> 0 then
      Events := [ioRead, ioWrite];
    if Events = [] then
      Continue;
    AReady[OutN].Token := Token;
    AReady[OutN].Events := Events;
    OutN := OutN + 1;
  end;
  Result := OutN;
end;

function TKqueueReactor.FdCount: Integer;
begin
  Result := Self.FCount;
end;

function CreateOsReactor: TReactor;
begin
  Result := TKqueueReactor.Create();
end;

initialization
  GReactorFactory := @CreateOsReactor;

end.
