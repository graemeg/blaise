{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for THttpFiberServer (docs/async-networking-design.adoc, [#components]):
  the rewritten fiber-per-connection HTTP server on the single-worker scheduler,
  reusing the baseline ParseRequest / IRequestHandler contract.

    * TestFiberHttpGet        — one client fiber GETs and reads the body back.
    * TestFiberHttpKeepAlive  — one connection serves two sequential requests
                                (HTTP/1.1 keep-alive on the connection fiber).
    * TestFiberHttpConcurrent — N client fibers each GET and get correct bodies.

  A tiny HTTP client is built inline on Net.Tcp (no Net.Http.Client yet).

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit HttpFiber.Tests;

interface

uses
  blaise.testing, SysUtils, StrUtils, Net.Http.Server, Net.Tcp, async.fibers;

type
  THttpFiberTests = class(TTestCase)
  published
    procedure TestFiberHttpGet;
    procedure TestFiberHttpKeepAlive;
    procedure TestFiberHttpConcurrent;
    { CI-sized proxy for the C10k concurrency claim: N client fibers each open
      their own connection and GET concurrently; the fiber-per-connection server
      must serve ALL of them with zero errors on one worker.  The full numbers
      come from the standalone benchmark program (bench_async_http). }
    procedure TestFiberHttpHighConcurrency;
  end;

  { Echoes the request path in the body, so a client can verify per-request
    routing under concurrency. }
  TPathHandler = class(IRequestHandler)
    procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
  end;

implementation

{ ---- fd-limit (RLIMIT_NOFILE) probe + raise -------------------------------
  The high-concurrency test opens ~2 fds per client (a client socket + its
  server-accepted peer) plus the listener, so N concurrent clients need roughly
  2*N + slack file descriptors.  Under the common default soft limit of 1024
  that structurally cannot complete: the excess clients sit in SYN-SENT forever
  and the test deadlocks (GH #189).  Raise the soft limit toward the hard limit
  first; if it still can't cover the desired N, the caller scales N down so the
  test stays meaningful without depending on an unstated host limit. }
type
  TRLimit = record
    RlimCur: UInt64;
    RlimMax: UInt64;
  end;

function c_setrlimit(AResource: Integer; ARlim: Pointer): Integer;
  external name 'setrlimit';
function c_getrlimit(AResource: Integer; ARlim: Pointer): Integer;
  external name 'getrlimit';

const
  RLIMIT_NOFILE = 7;   { Linux x86_64 (FreeBSD = 8); this test is Linux CI }

{ Raise the soft NOFILE limit toward the hard limit (or ADesired, whichever is
  smaller) and return the resulting soft limit (0 on failure). }
function RaiseFdLimit(ADesired: UInt64): UInt64;
var
  Rl: TRLimit;
begin
  if c_getrlimit(RLIMIT_NOFILE, @Rl) <> 0 then
    Exit(0);
  if ADesired > Rl.RlimMax then
    Rl.RlimCur := Rl.RlimMax
  else
    Rl.RlimCur := ADesired;
  c_setrlimit(RLIMIT_NOFILE, @Rl);
  if c_getrlimit(RLIMIT_NOFILE, @Rl) <> 0 then
    Exit(0);
  Result := Rl.RlimCur;
end;

procedure TPathHandler.Handle(ARequest: THttpRequest; AResponse: THttpResponse);
begin
  AResponse.SetText(200, 'text/plain', 'path=' + ARequest.Path);
end;

{ --- a tiny fiber HTTP client over Net.Tcp --------------------------------- }

{ Send one GET on an already-open connection and return the response body
  (everything after the CRLFCRLF head).  Reads the head, parses Content-Length,
  then reads exactly that many body bytes. }
function HttpGetOnConn(AConn: TTcpConn; const APath: string; AKeepAlive: Boolean): string;
var
  Req, Head, Acc, Chunk, Lower, Line: string;
  ConnHdr: string;
  Sep, ClPos, Eol, CLen, HeadLen, BodyHave: Integer;
begin
  Result := '';
  if AKeepAlive then
    ConnHdr := 'keep-alive'
  else
    ConnHdr := 'close';
  Req := 'GET ' + APath + ' HTTP/1.1'#13#10 +
         'Host: localhost'#13#10 +
         'Connection: ' + ConnHdr + #13#10 +
         #13#10;
  if not AConn.Write(Req) then
    Exit;

  { Read until the head terminator. }
  Acc := '';
  Sep := -1;
  while True do
  begin
    Sep := PosEx(#13#10#13#10, Acc, 0);
    if Sep >= 0 then
      Break;
    Chunk := AConn.Read(4096);
    if Chunk = '' then
      Break;
    Acc := Acc + Chunk;
  end;
  if Sep < 0 then
    Exit;

  HeadLen := Sep + 4;
  Head := Copy(Acc, 0, Sep);

  { Find Content-Length. }
  CLen := 0;
  Lower := LowerCase(Head);
  ClPos := PosEx('content-length:', Lower, 0);
  if ClPos >= 0 then
  begin
    Eol := PosEx(#13#10, Head, ClPos);
    if Eol < 0 then
      Eol := Length(Head);
    Line := Trim(Copy(Head, ClPos + 15, Eol - (ClPos + 15)));
    if Line <> '' then
      CLen := StrToInt(Line);
  end;

  { Body bytes already read past the head. }
  BodyHave := Length(Acc) - HeadLen;
  Result := Copy(Acc, HeadLen, BodyHave);
  while Length(Result) < CLen do
  begin
    Chunk := AConn.Read(CLen - Length(Result));
    if Chunk = '' then
      Break;
    Result := Result + Chunk;
  end;
end;

{ --- fixture state (single-worker scheduler is serial) --------------------- }

var
  GHttpServer: THttpFiberServer;
  GHandler: IRequestHandler;
  GPort: UInt16;
  GResult: string;
  GDone: Integer;
  GExpected: Integer;

procedure HttpServerFiber(AArg: Pointer);
begin
  GHttpServer.Serve(GHandler);
end;

procedure OneGetClientFiber(AArg: Pointer);
var
  Cli: TTcpClient;
  Conn: TTcpConn;
  Id: Integer;
  Body: string;
begin
  Id := Integer(AArg);
  FiberSleep(2);
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('127.0.0.1', GPort);
  Cli.Free();
  if Conn = nil then
  begin
    GResult := GResult + 'connfail ';
    GDone := GDone + 1;
    if GDone >= GExpected then GHttpServer.Stop();
    Exit;
  end;
  Body := HttpGetOnConn(Conn, '/p' + IntToStr(Id), False);
  GResult := GResult + Body + ' ';
  Conn.Free();
  GDone := GDone + 1;
  if GDone >= GExpected then
    GHttpServer.Stop();
end;

{ Keep-alive client: two requests on ONE connection. }
procedure KeepAliveClientFiber(AArg: Pointer);
var
  Cli: TTcpClient;
  Conn: TTcpConn;
  B1, B2: string;
begin
  FiberSleep(2);
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('127.0.0.1', GPort);
  Cli.Free();
  if Conn = nil then
  begin
    GResult := 'connfail';
    GHttpServer.Stop();
    Exit;
  end;
  B1 := HttpGetOnConn(Conn, '/first', True);
  B2 := HttpGetOnConn(Conn, '/second', False);
  GResult := B1 + '|' + B2;
  Conn.Free();
  GHttpServer.Stop();
end;

procedure THttpFiberTests.TestFiberHttpGet;
const
  PORT = 29411;
begin
  GHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('http server start', GHttpServer.Start());
  GHandler := TPathHandler.Create();
  GPort := PORT;
  GResult := '';
  GDone := 0;
  GExpected := 1;

  SpawnFiber(@HttpServerFiber, nil);
  SpawnFiber(@OneGetClientFiber, Pointer(0));
  RunScheduler();

  AssertEquals('GET returns the routed body', 'path=/p0 ', GResult);
  ResetScheduler();
  GHttpServer.Free();
  GHandler := nil;
end;

procedure THttpFiberTests.TestFiberHttpKeepAlive;
const
  PORT = 29412;
begin
  GHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('http server start', GHttpServer.Start());
  GHandler := TPathHandler.Create();
  GPort := PORT;
  GResult := '';

  SpawnFiber(@HttpServerFiber, nil);
  SpawnFiber(@KeepAliveClientFiber, nil);
  RunScheduler();

  AssertEquals('two requests served on one keep-alive connection',
    'path=/first|path=/second', GResult);
  ResetScheduler();
  GHttpServer.Free();
  GHandler := nil;
end;

procedure THttpFiberTests.TestFiberHttpConcurrent;
const
  PORT = 29413;
  NCLIENTS = 12;
var
  I, Cnt: Integer;
begin
  GHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('http server start', GHttpServer.Start());
  GHandler := TPathHandler.Create();
  GPort := PORT;
  GResult := '';
  GDone := 0;
  GExpected := NCLIENTS;

  SpawnFiber(@HttpServerFiber, nil);
  for I := 0 to NCLIENTS - 1 do
    SpawnFiber(@OneGetClientFiber, Pointer(I));
  RunScheduler();

  for I := 0 to NCLIENTS - 1 do
    AssertTrue('client ' + IntToStr(I) + ' got its body',
      Pos('path=/p' + IntToStr(I) + ' ', GResult) >= 0);
  Cnt := 0;
  for I := 0 to Length(GResult) - 1 do
    if Byte(GResult[I]) = 32 then
      Cnt := Cnt + 1;
  AssertEquals('exactly NCLIENTS bodies returned', NCLIENTS, Cnt);
  ResetScheduler();
  GHttpServer.Free();
  GHandler := nil;
end;

{ High-concurrency client: connect, GET, verify a 200 body, tally; stop the
  server when the last of GExpected finishes.  Uses a shared success counter so
  a single mismatch fails the test. }
var
  GHcOk: Integer;

procedure HcClientFiber(AArg: Pointer);
var
  Cli: TTcpClient;
  Conn: TTcpConn;
  Body: string;
begin
  FiberSleep(2);
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('127.0.0.1', GPort);
  Cli.Free();
  if Conn <> nil then
  begin
    Body := HttpGetOnConn(Conn, '/x', False);
    if Body = 'path=/x' then
      GHcOk := GHcOk + 1;
    Conn.Free();
  end;
  GDone := GDone + 1;
  if GDone >= GExpected then
    GHttpServer.Stop();
end;

procedure THttpFiberTests.TestFiberHttpHighConcurrency;
const
  PORT = 29414;
  WANT = 2000;        { the C10k-proxy target when the fd budget allows it }
  FLOOR = 200;        { still a meaningful concurrency test below this }
  RESERVE = 40;       { listener + stdio + RTL fds held aside }
var
  I, NClients: Integer;
  SoftLimit, Budget: UInt64;
begin
  { Each client holds ~2 fds concurrently (its own socket + the server-accepted
    peer).  Raise the soft NOFILE limit toward what WANT needs, then size the
    client count to whatever the resulting limit actually permits — never demand
    more fds than exist, which would deadlock (GH #189). }
  SoftLimit := RaiseFdLimit(2 * WANT + RESERVE + 100);
  if SoftLimit = 0 then
  begin
    Ignore('getrlimit unavailable — cannot size the fd budget');
    Exit;
  end;
  Budget := 0;
  if SoftLimit > RESERVE then
    Budget := (SoftLimit - RESERVE) div 2;   { fds per client ~= 2 }
  if Budget >= WANT then
    NClients := WANT
  else
    NClients := Integer(Budget);
  if NClients < FLOOR then
  begin
    Ignore('fd limit too low for a meaningful concurrency run (soft='
      + IntToStr(Int64(SoftLimit)) + ')');
    Exit;
  end;

  GHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('http server start', GHttpServer.Start());
  GHandler := TPathHandler.Create();
  GPort := PORT;
  GDone := 0;
  GHcOk := 0;
  GExpected := NClients;

  SpawnFiber(@HttpServerFiber, nil);
  for I := 0 to NClients - 1 do
    SpawnFiber(@HcClientFiber, Pointer(I));
  RunScheduler();

  AssertEquals('every one of the concurrent client fibers got a correct 200',
    NClients, GHcOk);
  ResetScheduler();
  GHttpServer.Free();
  GHandler := nil;
end;

initialization
  RegisterTest(THttpFiberTests);

end.
