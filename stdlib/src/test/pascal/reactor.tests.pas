{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the L2 readiness reactor (docs/async-networking-design.adoc,
  [#reactor]): a real reactor round-trip (epoll on Linux, kqueue on FreeBSD)
  over a socketpair — Add read interest,
  write to the peer, assert Wait delivers the token with ioRead; Modify to
  write interest; Remove; Wake interrupts a blocked Wait; the eventfd drain
  never spuriously delivers.

  NATIVE BACKEND ONLY (async.reactor is part of the fiber runtime; the runner
  is native).  Self-registers via the initialization section. }

unit Reactor.Tests;

interface

uses
  blaise.testing, SysUtils, async.reactor,
  { the per-OS readiness reactor: kqueue on FreeBSD, epoll on Linux.  Both
    expose the same surface, so the tests are written against a TOsReactor
    alias and exercise whichever adapter the target actually uses (GH #204
    fallout: the hard epoll dependency could not compile on FreeBSD).
    NOTE: TAlias.Create() through such an alias used to silently SKIP the
    constructor body -- fixed alongside this port; see the alias-constructor
    tests in cp.test.classes. }
  {$IFDEF FREEBSD}
  async.reactor.kqueue,
  {$ELSE}
  async.reactor.epoll,
  {$ENDIF}
  async.fibers;

type
  {$IFDEF FREEBSD}
  TOsReactor = TKqueueReactor;
  {$ELSE}
  TOsReactor = TEpollReactor;
  {$ENDIF}

  TReactorTests = class(TTestCase)
  published
    procedure TestPoll_EmptyBeforeWrite;
    procedure TestWait_DeliversTokenWithRead;
    procedure TestModify_ToWritable;
    procedure TestRemove_DropsInterest;
    procedure TestWake_InterruptsBlockedWait;
    procedure TestWake_DrainNoSpuriousDelivery;
  end;

  { Increment 2: scheduler <-> reactor integration.  A fiber registers read
    interest on a socketpair fd with the GLOBAL reactor (token =
    CurrentFiberTask), parks via FiberParkCurrent, and the single-worker
    scheduler's idle-park blocks in the reactor.  When the peer end is written,
    the reactor resumes the parked fiber. }
  TReactorSchedulerTests = class(TTestCase)
  published
    procedure TestFiberParksOnFdThenResumes;
  end;

implementation

const
  AF_UNIX = 1;
  SOCK_STREAM = 1;

function c_socketpair(ADomain, AType, AProtocol: Integer; ASv: Pointer): Integer;
  external name 'socketpair';
function c_close_fd(AFd: Integer): Integer; external name 'close';
function c_write_fd(AFd: Integer; ABuf: Pointer; ACount: Int64): Int64;
  external name 'write';
function c_read_fd(AFd: Integer; ABuf: Pointer; ACount: Int64): Int64;
  external name 'read';

{ Make a connected AF_UNIX stream socketpair; returns True on success. }
function MakePair(out AFd0, AFd1: Integer): Boolean;
var
  Sv: array[0..1] of Integer;
begin
  Sv[0] := -1;
  Sv[1] := -1;
  if c_socketpair(AF_UNIX, SOCK_STREAM, 0, @Sv[0]) <> 0 then
    Exit(False);
  AFd0 := Sv[0];
  AFd1 := Sv[1];
  Result := True;
end;

{ A fresh reactor per test keeps them independent (the global GReactor is a
  process-wide singleton; the tests here exercise a private instance). }
function NewReactor: TOsReactor;
begin
  Result := TOsReactor.Create();
end;

procedure TReactorTests.TestPoll_EmptyBeforeWrite;
var
  R: TOsReactor;
  A, B: Integer;
  Ready: TReadyList;
  RdOnly: TIoInterests;
  N: Integer;
begin
  AssertTrue('socketpair', MakePair(A, B));
  R := NewReactor();
  RdOnly := [ioRead];
  R.Add(A, RdOnly, Pointer(PtrUInt(1)));
  AssertEquals('one fd registered', 1, R.FdCount());
  N := R.Wait(0, Ready);          { poll: nothing written yet }
  AssertEquals('empty poll before any write', 0, N);
  R.Free();
  c_close_fd(A);
  c_close_fd(B);
end;

procedure TReactorTests.TestWait_DeliversTokenWithRead;
var
  R: TOsReactor;
  A, B: Integer;
  Ready: TReadyList;
  RdOnly, Evs: TIoInterests;
  Tok: Pointer;
  N: Integer;
  Byte1: Byte;
begin
  AssertTrue('socketpair', MakePair(A, B));
  R := NewReactor();
  RdOnly := [ioRead];
  Tok := Pointer(PtrUInt($ABCD));
  R.Add(A, RdOnly, Tok);
  Byte1 := 88;
  AssertEquals('wrote one byte', Int64(1), c_write_fd(B, @Byte1, 1));
  N := R.Wait(200, Ready);
  AssertEquals('one fd ready', 1, N);
  AssertTrue('token round-trips', Ready[0].Token = Tok);
  Evs := Ready[0].Events;
  AssertTrue('read readiness reported', ioRead in Evs);
  R.Free();
  c_close_fd(A);
  c_close_fd(B);
end;

procedure TReactorTests.TestModify_ToWritable;
var
  R: TOsReactor;
  A, B: Integer;
  Ready: TReadyList;
  RdOnly, WrOnly, Evs: TIoInterests;
  N: Integer;
begin
  AssertTrue('socketpair', MakePair(A, B));
  R := NewReactor();
  RdOnly := [ioRead];
  WrOnly := [ioWrite];
  R.Add(A, RdOnly, Pointer(PtrUInt(7)));
  { With no data pending, a read-interest poll is empty. }
  AssertEquals('read-interest poll empty', 0, R.Wait(0, Ready));
  { A fresh socketpair endpoint is immediately writable. }
  R.Modify(A, WrOnly, Pointer(PtrUInt(7)));
  N := R.Wait(200, Ready);
  AssertEquals('writable after modify', 1, N);
  Evs := Ready[0].Events;
  AssertTrue('write readiness reported', ioWrite in Evs);
  R.Free();
  c_close_fd(A);
  c_close_fd(B);
end;

procedure TReactorTests.TestRemove_DropsInterest;
var
  R: TOsReactor;
  A, B: Integer;
  Ready: TReadyList;
  RdOnly: TIoInterests;
  Byte1: Byte;
begin
  AssertTrue('socketpair', MakePair(A, B));
  R := NewReactor();
  RdOnly := [ioRead];
  R.Add(A, RdOnly, Pointer(PtrUInt(3)));
  AssertEquals('registered', 1, R.FdCount());
  R.Remove(A);
  AssertEquals('count back to zero', 0, R.FdCount());
  { Even with data pending, a removed fd is not delivered. }
  Byte1 := 1;
  c_write_fd(B, @Byte1, 1);
  AssertEquals('removed fd never delivered', 0, R.Wait(50, Ready));
  R.Free();
  c_close_fd(A);
  c_close_fd(B);
end;

procedure TReactorTests.TestWake_InterruptsBlockedWait;
var
  R: TOsReactor;
  Ready: TReadyList;
  N: Integer;
begin
  { No fds registered.  Arm a wake, then Wait with a generous timeout: the
    eventfd makes Wait return promptly with nothing delivered (rather than
    blocking the full timeout). }
  R := NewReactor();
  R.Wake();
  N := R.Wait(2000, Ready);
  AssertEquals('wake delivers no tokens', 0, N);
  { A second Wait must NOT see the (already drained) wake — a short poll. }
  N := R.Wait(0, Ready);
  AssertEquals('wake was one-shot', 0, N);
  R.Free();
end;

procedure TReactorTests.TestWake_DrainNoSpuriousDelivery;
var
  R: TOsReactor;
  A, B: Integer;
  Ready: TReadyList;
  RdOnly, Evs: TIoInterests;
  Byte1: Byte;
  N: Integer;
begin
  { A real fd AND a wake pending together: Wait must deliver ONLY the real
    fd's token, never the internal wake fd (token nil). }
  AssertTrue('socketpair', MakePair(A, B));
  R := NewReactor();
  RdOnly := [ioRead];
  R.Add(A, RdOnly, Pointer(PtrUInt($55)));
  Byte1 := 7;
  c_write_fd(B, @Byte1, 1);
  R.Wake();
  N := R.Wait(200, Ready);
  AssertEquals('exactly one token (wake not surfaced)', 1, N);
  AssertTrue('the real token', Ready[0].Token = Pointer(PtrUInt($55)));
  Evs := Ready[0].Events;
  AssertTrue('read ready', ioRead in Evs);
  R.Free();
  c_close_fd(A);
  c_close_fd(B);
end;

{ --- Increment 2: scheduler <-> reactor integration -------------------------- }

var
  GIntLog: string;
  GRxA, GRxB: Integer;      { socketpair for the integration test }

{ Fiber: register read interest on GRxA, park; on resume, read the byte. }
procedure ReaderFiber(AArg: Pointer);
var
  R: TReactor;
  RdOnly: TIoInterests;
  B: Byte;
begin
  GIntLog := GIntLog + 'R1 ';
  R := GetReactor();
  RdOnly := [ioRead];
  R.Add(GRxA, RdOnly, Pointer(CurrentFiberTask()));
  FiberParkCurrent();             { scheduler idle-parks in the reactor }
  GIntLog := GIntLog + 'R2 ';
  R.Remove(GRxA);
  B := 0;
  if c_read_fd(GRxA, @B, 1) = 1 then
    GIntLog := GIntLog + 'got' + IntToStr(Integer(B)) + ' ';
end;

{ Fiber: sleep briefly (so the reader parks first), then write the byte that
  makes GRxA readable, waking the reader through the reactor. }
procedure WriterFiber(AArg: Pointer);
var
  B: Byte;
begin
  FiberSleep(5);
  B := 42;
  c_write_fd(GRxB, @B, 1);
  GIntLog := GIntLog + 'W ';
end;

procedure TReactorSchedulerTests.TestFiberParksOnFdThenResumes;
var
  TR, TW: TFiberTask;
begin
  AssertTrue('socketpair', MakePair(GRxA, GRxB));
  GIntLog := '';
  TR := SpawnFiber(@ReaderFiber, nil);
  TW := SpawnFiber(@WriterFiber, nil);
  RunScheduler();
  { Reader started, parked; writer wrote; reader resumed via the reactor and
    read the byte. }
  AssertEquals('reader parked on fd and resumed on readiness',
    'R1 W R2 got42 ', GIntLog);
  AssertTrue('reader fiber done', TR.State = fsDone);
  AssertTrue('writer fiber done', TW.State = fsDone);
  ResetScheduler();
  c_close_fd(GRxA);
  c_close_fd(GRxB);
end;

initialization
  RegisterTest(TReactorTests);
  RegisterTest(TReactorSchedulerTests);

end.
