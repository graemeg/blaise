{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit async.reactor;

// L2 of the fiber runtime (docs/async-networking-design.adoc, [#reactor]): the
// readiness reactor.  A TReactor tracks per-fd interest (read/write) and blocks
// in Wait until one or more fds are ready or a Wake interrupts it, delivering
// the opaque tokens registered with each fd.  The scheduler (async.fibers) uses
// the token — a TFiberTask — to resume the fiber parked on that fd.
//
// TReactor is abstract; the per-OS adapters live in their own units
// (async.reactor.epoll for Linux, async.reactor.kqueue for FreeBSD — the
// design's "one async.reactor.<mech>.pas per OS").  Each adapter's
// initialization block registers its factory in GReactorFactory here; the
// scheduler (async.fibers) pulls in the right adapter unit for the RESOLVED
// --target via the project's ONE target-driven conditional (OS defines
// follow --target, not the build host, so cross-compilation selects the
// right adapter in both directions).  A TIocpReactor (Windows) slots in
// later as one more unit + one more branch at that seam.

interface

uses
  SysUtils;

type
  { What a fiber is waiting for on an fd. }
  TIoInterest = (ioRead, ioWrite);
  TIoInterests = set of TIoInterest;

  { One ready fd delivered by Wait: the token registered for it and which of
    read/write became ready. }
  TReadyEntry = record
    Token: Pointer;
    Events: TIoInterests;
  end;

  { Wait fills a caller-owned dynamic array of these (grown as needed). }
  TReadyList = array of TReadyEntry;

  { The readiness reactor.  Abstract so per-OS adapters (epoll/kqueue/IOCP)
    share one interface that the scheduler and L3 fiber I/O depend on. }
  TReactor = class
  public
    { Register interest in AFd; when AFd is ready, Wait delivers AToken. }
    procedure Add(AFd: Int; AInterest: TIoInterests; AToken: Pointer); virtual; abstract;
    { Change the interest (and token) for an already-registered AFd. }
    procedure Modify(AFd: Int; AInterest: TIoInterests; AToken: Pointer); virtual; abstract;
    { Stop tracking AFd. }
    procedure Remove(AFd: Int); virtual; abstract;
    { Block up to ATimeoutMs (negative = indefinite, 0 = poll) or until a Wake,
      then fill AReady with (token, events) pairs.  Returns the count. }
    function Wait(ATimeoutMs: Int; var AReady: TReadyList): Int; virtual; abstract;
    { Interrupt a Wait blocked on another thread (or arm a pending wake so the
      next Wait returns promptly). }
    procedure Wake; virtual; abstract;
    { Number of caller fds currently registered (0 => scheduler may skip the
      reactor and use its plain idle-park). }
    function FdCount: Int; virtual; abstract;
  end;

{ The process-wide reactor, lazily created on first use (GetReactor).  Selected
  at scheduler startup, like GRtlPlatform. }
function GetReactor: TReactor;

{ Number of fds currently registered with the global reactor.  0 when the
  reactor was never created, so a purely CPU-bound workload never pays for it. }
function ReactorFdCount: Int;

type
  { Set by the per-OS adapter unit's initialization block (the registration
    the design doc calls for) — avoids a circular unit reference between the
    abstract port here and the adapter that subclasses it. }
  TReactorFactory = function: TReactor;

var
  GReactor: TReactor;
  GReactorFactory: TReactorFactory;

implementation

function GetReactor: TReactor;
begin
  if GReactor = nil then
  begin
    if GReactorFactory = nil then
      raise Exception.Create(
        'no reactor adapter registered (missing async.reactor.<os> unit)');
    GReactor := GReactorFactory();
  end;
  Result := GReactor;
end;

function ReactorFdCount: Int;
begin
  if GReactor = nil then
    Exit(0);
  Result := GReactor.FdCount();
end;

end.
