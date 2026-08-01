{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for L3 fiber I/O (docs/async-networking-design.adoc, [#fiber-io]):
  FiberRecv/FiberSend over a socketpair (two fibers, bytes round-trip);
  FiberAccept + FiberConnect over a real loopback TCP listener; a deadline that
  expires returns IO_ETIMEDOUT; and the blocking-fallback path with NO scheduler
  running.

  NATIVE BACKEND ONLY (async.io depends on async.fibers).  Self-registers via
  the initialization section. }

unit AsyncIo.Tests;

interface

uses
  blaise.testing, SysUtils, async.io, async.fibers, Net.Sockets;

type
  TAsyncIoTests = class(TTestCase)
  published
    procedure TestSocketPair_SendRecvRoundTrip;
    procedure TestLoopback_AcceptConnect;
    procedure TestDeadline_Expires_ReturnsTimedOut;
    procedure TestBlockingFallback_NoScheduler;
  end;

implementation

const
  AF_UNIX = 1;
  SOCK_STREAM_ = 1;

function c_socketpair(ADomain, AType, AProtocol: Integer; ASv: Pointer): Integer;
  external name 'socketpair';
function c_close_fd(AFd: Integer): Integer; external name 'close';
function c_write_fd(AFd: Integer; ABuf: Pointer; ACount: Int64): Int64;
  external name 'write';

function MakePair(out AFd0, AFd1: Integer): Boolean;
var
  Sv: array[0..1] of Integer;
begin
  Sv[0] := -1;
  Sv[1] := -1;
  if c_socketpair(AF_UNIX, SOCK_STREAM_, 0, @Sv[0]) <> 0 then
    Exit(False);
  AFd0 := Sv[0];
  AFd1 := Sv[1];
  Result := True;
end;

function BufToStr(const ABuf: array of Byte; ALen: Integer): string;
var
  I: Integer;
begin
  Result := '';
  for I := 0 to ALen - 1 do
    Result := Result + Chr(ABuf[I]);
end;

{ --- socketpair send/recv round-trip --------------------------------------- }

var
  GPairA, GPairB: Integer;
  GIoLog: string;

procedure PairSender(AArg: Pointer);
var
  Msg: string;
  N: Int64;
begin
  Msg := 'ping';
  N := FiberSend(GPairB, PChar(Msg), 4);
  GIoLog := GIoLog + 'sent' + IntToStr(Integer(N)) + ' ';
end;

procedure PairReceiver(AArg: Pointer);
var
  Buf: array[0..15] of Byte;
  N: Int64;
begin
  N := FiberRecv(GPairA, @Buf[0], 16);
  GIoLog := GIoLog + 'recv:' + BufToStr(Buf, Integer(N)) + ' ';
end;

procedure TAsyncIoTests.TestSocketPair_SendRecvRoundTrip;
begin
  AssertTrue('socketpair', MakePair(GPairA, GPairB));
  SetNonBlocking(GPairA);
  SetNonBlocking(GPairB);
  GIoLog := '';
  { Receiver spawned first: it parks on the empty socket, the sender writes,
    the reactor resumes it. }
  SpawnFiber(@PairReceiver, nil);
  SpawnFiber(@PairSender, nil);
  RunScheduler();
  AssertEquals('bytes round-trip through the reactor',
    'sent4 recv:ping ', GIoLog);
  ResetScheduler();
  c_close_fd(GPairA);
  c_close_fd(GPairB);
end;

{ --- loopback TCP accept / connect ----------------------------------------- }

const
  TEST_PORT = 29355;

var
  GListenFd: Integer;

procedure LoopbackServer(AArg: Pointer);
var
  Conn: Integer;
  Buf: array[0..15] of Byte;
  N: Int64;
begin
  Conn := FiberAccept(GListenFd);
  if Conn < 0 then
  begin
    GIoLog := GIoLog + 'accfail ';
    Exit;
  end;
  GIoLog := GIoLog + 'accepted ';
  N := FiberRecv(Conn, @Buf[0], 16);
  GIoLog := GIoLog + 'srv:' + BufToStr(Buf, Integer(N)) + ' ';
  FiberSend(Conn, PChar('pong'), 4);
  c_close_fd(Conn);
end;

procedure LoopbackClient(AArg: Pointer);
var
  Fd, Rc: Integer;
  SA: TSockAddrIn;
  Buf: array[0..15] of Byte;
  N: Int64;
begin
  FiberSleep(3);                 { let the server accept-park first }
  Fd := Socket(AF_INET, SOCK_STREAM, 0);
  SetNonBlocking(Fd);
  FillSockAddr(SA, INADDR_LOOPBACK, TEST_PORT);
  Rc := FiberConnect(Fd, @SA, 16);
  if Rc <> 0 then
  begin
    GIoLog := GIoLog + 'connfail ';
    Exit;
  end;
  GIoLog := GIoLog + 'connected ';
  FiberSend(Fd, PChar('ping'), 4);
  N := FiberRecv(Fd, @Buf[0], 16);
  GIoLog := GIoLog + 'cli:' + BufToStr(Buf, Integer(N)) + ' ';
  c_close_fd(Fd);
end;

procedure TAsyncIoTests.TestLoopback_AcceptConnect;
begin
  GListenFd := TcpListenLocal(TEST_PORT, 8);
  AssertTrue('listen', GListenFd >= 0);
  SetNonBlocking(GListenFd);
  GIoLog := '';
  SpawnFiber(@LoopbackServer, nil);
  SpawnFiber(@LoopbackClient, nil);
  RunScheduler();
  c_close_fd(GListenFd);
  { The accept/connect pair may log in either order, and both orders are
    correct.  Both ends park: a non-blocking loopback connect(2) reports
    EINPROGRESS on FreeBSD exactly as it does on Linux — measured with a probe,
    not assumed.  Which of the two the reactor then reports ready first is
    simply the order the kernel hands readiness back, and the two kernels do
    not agree: kqueue surfaces the client's writable event ahead of the
    listener's readable one, epoll the reverse.  Neither ordering is something
    the reactor promises.  What IS contractual is that both ends complete and
    the payloads cross intact, so the two handshake tokens are matched as a set
    and the send/recv half stays exact. }
  AssertTrue('both ends handshake, then ping/pong crosses intact',
    (GIoLog = 'accepted connected srv:ping cli:pong ') or
    (GIoLog = 'connected accepted srv:ping cli:pong '));
  ResetScheduler();
end;

{ --- deadline expiry -------------------------------------------------------- }

procedure DeadlineReader(AArg: Pointer);
var
  Buf: array[0..15] of Byte;
  N: Int64;
begin
  { Nobody ever writes to GPairA: the 30 ms deadline must fire. }
  N := FiberRecvT(GPairA, @Buf[0], 16, 30);
  if N = IO_ETIMEDOUT then
    GIoLog := GIoLog + 'timedout '
  else
    GIoLog := GIoLog + 'notimeout' + IntToStr(Integer(N)) + ' ';
end;

procedure TAsyncIoTests.TestDeadline_Expires_ReturnsTimedOut;
var
  Started, Elapsed: Int64;
begin
  AssertTrue('socketpair', MakePair(GPairA, GPairB));
  SetNonBlocking(GPairA);
  SetNonBlocking(GPairB);
  GIoLog := '';
  Started := MonotonicNowNs();
  SpawnFiber(@DeadlineReader, nil);
  RunScheduler();
  Elapsed := MonotonicNowNs() - Started;
  AssertEquals('recv times out rather than hanging', 'timedout ', GIoLog);
  AssertTrue('returned near the deadline, not instantly and not forever',
    (Elapsed >= Int64(20000000)) and (Elapsed < Int64(2000000000)));
  ResetScheduler();
  c_close_fd(GPairA);
  c_close_fd(GPairB);
end;

{ --- blocking fallback (no scheduler) --------------------------------------- }

procedure TAsyncIoTests.TestBlockingFallback_NoScheduler;
var
  A, B: Integer;
  Buf: array[0..3] of Byte;
  Byte1: Byte;
  N: Int64;
begin
  { No RunScheduler on the stack: CurrentFiberTask is nil, so FiberRecv takes
    the true blocking path.  Write first so the ready data returns immediately
    (proving the plain-call path works and returns the raw count). }
  AssertTrue('socketpair', MakePair(A, B));
  Byte1 := 90;
  c_write_fd(B, @Byte1, 1);
  N := FiberRecv(A, @Buf[0], 4);
  AssertEquals('blocking-fallback recv returns the raw count', Int64(1), N);
  AssertEquals('byte value round-trips', 90, Integer(Buf[0]));
  c_close_fd(A);
  c_close_fd(B);
end;

initialization
  RegisterTest(TAsyncIoTests);

end.
