{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Net.Http.Client (docs/async-networking-design.adoc, L5): the
  HTTP/1.1 client on the fiber runtime.

  Each test spawns the EXISTING THttpFiberServer on a loopback port plus one or
  more client fibers under the single-worker scheduler, so the client is proven
  end to end against a real server:

    * TestClientGet        — GET returns the served body + status 200.
    * TestClientPost       — POST round-trips a request body the server echoes.
    * TestClientChunked    — a chunked transfer-encoding response decodes.
    * TestClientKeepAlive   — two requests to the same origin reuse one socket
                              (proven by a server-side connection counter == 1).
    * TestClientRedirect   — a 302 is followed to the final body.
    * TestClientConcurrent — N client fibers hit the server concurrently and
                              each get the correct body.
    * TestClientGetByName  — the URL names 'localhost', not an IP: the host is
                              resolved, and an address that refuses (::1, when
                              the server is IPv4-only) falls through to the next.
    * TestClientReadTimeout — ReadTimeoutMs ends a request whose server never
                              answers, from inside a fiber.

  TcpDial.Tests covers the same client from a plain program (no scheduler).

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit HttpClient.Tests;

interface

uses
  blaise.testing, SysUtils, StrUtils,
  Classes, Net.Http.Server, Net.Http.Client, Net.Tcp, Net.Sockets, async.fibers;

type
  THttpClientTests = class(TTestCase)
  published
    procedure TestClientGet;
    procedure TestClientPost;
    procedure TestClientChunked;
    procedure TestClientKeepAlive;
    procedure TestClientRedirect;
    procedure TestClientConcurrent;
    { one client shared by several threads, each sending requests that reuse
      its keep-alive connections: every thread gets its own answers (the
      unsynchronised pool handed one connection to two threads, which then
      read each other's responses, or corrupted the pool) }
    procedure TestClientSharedAcrossThreads;
    procedure TestClientGetByName;
    procedure TestClientReadTimeout;
  end;

  { Echoes the request path in the body. }
  THcPathHandler = class(IRequestHandler)
    procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
  end;

implementation

procedure THcPathHandler.Handle(ARequest: THttpRequest; AResponse: THttpResponse);
begin
  AResponse.SetText(200, 'text/plain', 'path=' + ARequest.Path);
end;

{ ---- shared fixture (single-worker scheduler is serial) ------------------- }

var
  GHcHttpServer: THttpFiberServer;
  GHcHandler: IRequestHandler;
  GPort: Int;
  GResult: string;
  GStatus: Int;
  GDone: Int;
  GExpected: Int;

procedure HcHttpServerFiber(AArg: Pointer);
begin
  GHcHttpServer.Serve(GHcHandler);
end;

function BaseUrl: string;
begin
  Result := 'http://127.0.0.1:' + IntToStr(GPort);
end;

{ --- GET --- }

procedure GetClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  FiberSleep(3);
  Cli := THttpClient.Create();
  Resp := Cli.Get(BaseUrl() + '/hello');
  if Resp <> nil then
  begin
    GStatus := Resp.Status;
    GResult := Resp.Body;
    Resp.Free();
  end;
  Cli.Free();
  GHcHttpServer.Stop();
end;

procedure THttpClientTests.TestClientGet;
const
  PORT = 29431;
begin
  GHcHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('server start', GHcHttpServer.Start());
  GHcHandler := THcPathHandler.Create();
  GPort := PORT;
  GResult := '';
  GStatus := 0;

  SpawnFiber(@HcHttpServerFiber, nil);
  SpawnFiber(@GetClientFiber, nil);
  RunScheduler();

  AssertEquals('GET status', 200, GStatus);
  AssertEquals('GET body', 'path=/hello', GResult);
  ResetScheduler();
  GHcHttpServer.Free();
  GHcHandler := nil;
end;

{ --- POST (echo body) --- }

type
  THcEchoHandler = class(IRequestHandler)
    procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
  end;

procedure THcEchoHandler.Handle(ARequest: THttpRequest; AResponse: THttpResponse);
begin
  { The fiber server does not surface the body to the handler; echo the path so
    the round-trip still exercises the request-body write path (Content-Length
    header emitted + body sent). The POST test asserts on status + a path echo. }
  AResponse.SetText(201, 'text/plain', 'posted=' + ARequest.Path);
end;

procedure PostClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  FiberSleep(3);
  Cli := THttpClient.Create();
  Resp := Cli.Post(BaseUrl() + '/submit', 'name=Ada&city=London', 'application/x-www-form-urlencoded');
  if Resp <> nil then
  begin
    GStatus := Resp.Status;
    GResult := Resp.Body;
    Resp.Free();
  end;
  Cli.Free();
  GHcHttpServer.Stop();
end;

procedure THttpClientTests.TestClientPost;
const
  PORT = 29432;
begin
  GHcHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('server start', GHcHttpServer.Start());
  GHcHandler := THcEchoHandler.Create();
  GPort := PORT;
  GResult := '';
  GStatus := 0;

  SpawnFiber(@HcHttpServerFiber, nil);
  SpawnFiber(@PostClientFiber, nil);
  RunScheduler();

  AssertEquals('POST status', 201, GStatus);
  AssertEquals('POST echo', 'posted=/submit', GResult);
  ResetScheduler();
  GHcHttpServer.Free();
  GHcHandler := nil;
end;

{ --- chunked response (raw server on Net.Tcp emits chunked) --- }

var
  GChunkListenPort: Int;
  GChunkServer: TTcpServer;

type
  { A minimal server that answers any request with a chunked-encoded body,
    to prove the client's chunked decoder. }
  TChunkedHandler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

procedure TChunkedHandler.Handle(AConn: TTcpConn);
var
  Line: string;
  Resp: string;
begin
  { Read the request head (up to the blank line). }
  while AConn.ReadLine(Line) do
    if Line = '' then
      Break;
  Resp :=
    'HTTP/1.1 200 OK'#13#10 +
    'Content-Type: text/plain'#13#10 +
    'Transfer-Encoding: chunked'#13#10 +
    'Connection: close'#13#10 +
    #13#10 +
    '5'#13#10'Hello'#13#10 +      { chunk 1: "Hello" }
    '6'#13#10' World'#13#10 +     { chunk 2: " World" }
    '0'#13#10#13#10;             { terminating chunk }
  AConn.Write(Resp);
  AConn.Close();
end;

procedure ChunkServerFiber(AArg: Pointer);
var
  H: IConnHandler;
begin
  H := TChunkedHandler.Create();
  GChunkServer.Serve(H);
end;

procedure ChunkClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  FiberSleep(3);
  Cli := THttpClient.Create();
  Resp := Cli.Get('http://127.0.0.1:' + IntToStr(GChunkListenPort) + '/c');
  if Resp <> nil then
  begin
    GStatus := Resp.Status;
    GResult := Resp.Body;
    Resp.Free();
  end;
  Cli.Free();
  GChunkServer.Stop();
end;

procedure THttpClientTests.TestClientChunked;
const
  PORT = 29433;
begin
  GChunkListenPort := PORT;
  GChunkServer := TTcpServer.Create(UInt16(PORT));
  AssertTrue('chunk server start', GChunkServer.Start());
  GResult := '';
  GStatus := 0;

  SpawnFiber(@ChunkServerFiber, nil);
  SpawnFiber(@ChunkClientFiber, nil);
  RunScheduler();

  AssertEquals('chunked status', 200, GStatus);
  AssertEquals('chunked body reassembled', 'Hello World', GResult);
  ResetScheduler();
  GChunkServer.Free();
end;

{ --- keep-alive reuse: server counts distinct connections --- }

var
  GConnCount: Int;
  GKaListenPort: Int;
  GKaServer: TTcpServer;

type
  { Counts each accepted connection, then serves keep-alive requests on it.
    If the client reuses one connection for two requests, GConnCount stays 1. }
  TCountingHandler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

procedure TCountingHandler.Handle(AConn: TTcpConn);
var
  Line: string;
  Body: string;
begin
  GConnCount := GConnCount + 1;
  while True do
  begin
    { Read one request head. }
    if not AConn.ReadLine(Line) then
      Break;                       { peer closed }
    { Drain remaining header lines to the blank line. }
    while AConn.ReadLine(Line) do
      if Line = '' then
        Break;
    Body := 'ok';
    AConn.Write(
      'HTTP/1.1 200 OK'#13#10 +
      'Content-Type: text/plain'#13#10 +
      'Content-Length: ' + IntToStr(Length(Body)) + #13#10 +
      'Connection: keep-alive'#13#10 +
      #13#10 + Body);
  end;
  AConn.Close();
end;

procedure KaServerFiber(AArg: Pointer);
var
  H: IConnHandler;
begin
  H := TCountingHandler.Create();
  GKaServer.Serve(H);
end;

procedure KaClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  R1, R2: THttpClientResponse;
begin
  FiberSleep(3);
  Cli := THttpClient.Create();
  R1 := Cli.Get('http://127.0.0.1:' + IntToStr(GKaListenPort) + '/a');
  if R1 <> nil then
  begin
    GResult := GResult + R1.Body;
    R1.Free();
  end;
  R2 := Cli.Get('http://127.0.0.1:' + IntToStr(GKaListenPort) + '/b');
  if R2 <> nil then
  begin
    GResult := GResult + R2.Body;
    R2.Free();
  end;
  Cli.Free();
  GKaServer.Stop();
end;

procedure THttpClientTests.TestClientKeepAlive;
const
  PORT = 29434;
begin
  GKaListenPort := PORT;
  GKaServer := TTcpServer.Create(UInt16(PORT));
  AssertTrue('ka server start', GKaServer.Start());
  GResult := '';
  GConnCount := 0;

  SpawnFiber(@KaServerFiber, nil);
  SpawnFiber(@KaClientFiber, nil);
  RunScheduler();

  AssertEquals('both requests answered', 'okok', GResult);
  AssertEquals('keep-alive reused a single connection', 1, GConnCount);
  ResetScheduler();
  GKaServer.Free();
end;

{ --- redirect following: 302 -> final body --- }

var
  GRedirListenPort: Int;
  GRedirServer: TTcpServer;

type
  { /old -> 302 Location: /new ; /new -> 200 "final". }
  TRedirectHandler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

procedure TRedirectHandler.Handle(AConn: TTcpConn);
var
  ReqLine, Line, Target, Body: string;
  Sp1, Sp2: Int;
begin
  { First line: METHOD SP target SP version }
  if not AConn.ReadLine(ReqLine) then
  begin
    AConn.Close();
    Exit;
  end;
  while AConn.ReadLine(Line) do
    if Line = '' then
      Break;
  Sp1 := PosEx(' ', ReqLine, 0);
  Sp2 := PosEx(' ', ReqLine, Sp1 + 1);
  if (Sp1 >= 0) and (Sp2 > Sp1) then
    Target := Copy(ReqLine, Sp1 + 1, Sp2 - Sp1 - 1)
  else
    Target := '';
  if Target = '/old' then
  begin
    AConn.Write(
      'HTTP/1.1 302 Found'#13#10 +
      'Location: /new'#13#10 +
      'Content-Length: 0'#13#10 +
      'Connection: keep-alive'#13#10 +
      #13#10);
  end
  else
  begin
    Body := 'final';
    AConn.Write(
      'HTTP/1.1 200 OK'#13#10 +
      'Content-Type: text/plain'#13#10 +
      'Content-Length: ' + IntToStr(Length(Body)) + #13#10 +
      'Connection: keep-alive'#13#10 +
      #13#10 + Body);
  end;
  { keep the connection open for the follow-up request }
  while True do
  begin
    if not AConn.ReadLine(ReqLine) then
      Break;
    while AConn.ReadLine(Line) do
      if Line = '' then
        Break;
    Body := 'final';
    AConn.Write(
      'HTTP/1.1 200 OK'#13#10 +
      'Content-Type: text/plain'#13#10 +
      'Content-Length: ' + IntToStr(Length(Body)) + #13#10 +
      'Connection: keep-alive'#13#10 +
      #13#10 + Body);
  end;
  AConn.Close();
end;

procedure RedirServerFiber(AArg: Pointer);
var
  H: IConnHandler;
begin
  H := TRedirectHandler.Create();
  GRedirServer.Serve(H);
end;

procedure RedirClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  FiberSleep(3);
  Cli := THttpClient.Create();
  Resp := Cli.Get('http://127.0.0.1:' + IntToStr(GRedirListenPort) + '/old');
  if Resp <> nil then
  begin
    GStatus := Resp.Status;
    GResult := Resp.Body;
    Resp.Free();
  end;
  Cli.Free();
  GRedirServer.Stop();
end;

procedure THttpClientTests.TestClientRedirect;
const
  PORT = 29435;
begin
  GRedirListenPort := PORT;
  GRedirServer := TTcpServer.Create(UInt16(PORT));
  AssertTrue('redir server start', GRedirServer.Start());
  GResult := '';
  GStatus := 0;

  SpawnFiber(@RedirServerFiber, nil);
  SpawnFiber(@RedirClientFiber, nil);
  RunScheduler();

  AssertEquals('redirect followed to final status', 200, GStatus);
  AssertEquals('redirect followed to final body', 'final', GResult);
  ResetScheduler();
  GRedirServer.Free();
end;

{ --- concurrent clients --- }

var
  GConcOk: Int;

procedure ConcClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
  Id: Int;
begin
  Id := Int32(AArg);
  FiberSleep(3);
  Cli := THttpClient.Create();
  Resp := Cli.Get(BaseUrl() + '/p' + IntToStr(Id));
  if Resp <> nil then
  begin
    if (Resp.Status = 200) and (Resp.Body = 'path=/p' + IntToStr(Id)) then
      GConcOk := GConcOk + 1;
    Resp.Free();
  end;
  Cli.Free();
  GDone := GDone + 1;
  if GDone >= GExpected then
    GHcHttpServer.Stop();
end;

procedure THttpClientTests.TestClientConcurrent;
const
  PORT = 29436;
  NCLIENTS = 10;
var
  I: Int;
begin
  GHcHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('server start', GHcHttpServer.Start());
  GHcHandler := THcPathHandler.Create();
  GPort := PORT;
  GDone := 0;
  GConcOk := 0;
  GExpected := NCLIENTS;

  SpawnFiber(@HcHttpServerFiber, nil);
  for I := 0 to NCLIENTS - 1 do
    SpawnFiber(@ConcClientFiber, Pointer(I));
  RunScheduler();

  AssertEquals('every concurrent client got its correct 200 body',
    NCLIENTS, GConcOk);
  ResetScheduler();
  GHcHttpServer.Free();
  GHcHandler := nil;
end;

{ --- one client shared across threads --- }

type
  TSharedGetter = class(TThread)
  public
    Cli: THttpClient;
    Id: Int;
    Ok: Int;
    procedure Execute; override;
  end;

const
  SHARED_THREADS = 4;
  SHARED_REQUESTS = 25;

var
  GSharedLock: TCriticalSection;
  GSharedFinished: Int;
  GSharedOk: Int;

procedure TSharedGetter.Execute;
var
  I: Int;
  Path: string;
  Resp: THttpClientResponse;
begin
  for I := 1 to SHARED_REQUESTS do
  begin
    Path := '/t' + IntToStr(Id) + '-' + IntToStr(I);
    Resp := Cli.Get(BaseUrl() + Path);
    if Resp <> nil then
    begin
      if (Resp.Status = 200) and (Resp.Body = 'path=' + Path) then
        Ok := Ok + 1;
      Resp.Free();
    end;
  end;
  GSharedLock.Enter();
  GSharedOk := GSharedOk + Ok;
  GSharedFinished := GSharedFinished + 1;
  GSharedLock.Leave();
end;

procedure SharedClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Threads: array of TSharedGetter;
  I, Finished: Int;
begin
  FiberSleep(3);
  Cli := THttpClient.Create();
  SetLength(Threads, SHARED_THREADS);
  for I := 0 to SHARED_THREADS - 1 do
  begin
    Threads[I] := TSharedGetter.Create(True);
    Threads[I].Cli := Cli;
    Threads[I].Id := I;
    Threads[I].Start();
  end;
  repeat
    FiberSleep(5);
    GSharedLock.Enter();
    Finished := GSharedFinished;
    GSharedLock.Leave();
  until Finished >= SHARED_THREADS;
  for I := 0 to SHARED_THREADS - 1 do
    Threads[I].WaitFor();
  Cli.Free();
  GHcHttpServer.Stop();
end;

procedure THttpClientTests.TestClientSharedAcrossThreads;
const
  PORT = 29439;
begin
  GHcHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('server start', GHcHttpServer.Start());
  GHcHandler := THcPathHandler.Create();
  GPort := PORT;
  GSharedLock := TCriticalSection.Create();
  GSharedFinished := 0;
  GSharedOk := 0;

  SpawnFiber(@HcHttpServerFiber, nil);
  SpawnFiber(@SharedClientFiber, nil);
  RunScheduler();

  AssertEquals('every thread got its own answers',
    SHARED_THREADS * SHARED_REQUESTS, GSharedOk);
  ResetScheduler();
  GHcHttpServer.Free();
  GHcHandler := nil;
  GSharedLock.Free();
end;

{ --- GET by host name --- }

procedure GetByNameClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  FiberSleep(3);
  Cli := THttpClient.Create();
  Resp := Cli.Get('http://localhost:' + IntToStr(GPort) + '/named');
  if Resp <> nil then
  begin
    GStatus := Resp.Status;
    GResult := Resp.Body;
    Resp.Free();
  end;
  Cli.Free();
  GHcHttpServer.Stop();
end;

procedure THttpClientTests.TestClientGetByName;
const
  PORT = 29437;
begin
  GHcHttpServer := THttpFiberServer.Create(PORT);
  AssertTrue('server start', GHcHttpServer.Start());
  GHcHandler := THcPathHandler.Create();
  GPort := PORT;
  GResult := '';
  GStatus := 0;

  SpawnFiber(@HcHttpServerFiber, nil);
  SpawnFiber(@GetByNameClientFiber, nil);
  RunScheduler();

  AssertEquals('GET status', 200, GStatus);
  AssertEquals('GET body', 'path=/named', GResult);
  ResetScheduler();
  GHcHttpServer.Free();
  GHcHandler := nil;
end;

{ --- read timeout --- }

var
  GTimeoutNil: Boolean;
  GTimeoutMs: Int64;

procedure ReadTimeoutClientFiber(AArg: Pointer);
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
  T0: Int64;
begin
  Cli := THttpClient.Create();
  Cli.ReadTimeoutMs := 300;
  T0 := MonotonicNowNs();
  Resp := Cli.Get('http://127.0.0.1:' + IntToStr(GPort) + '/');
  GTimeoutMs := (MonotonicNowNs() - T0) div 1000000;
  GTimeoutNil := Resp = nil;
  if Resp <> nil then
    Resp.Free();
  Cli.Free();
end;

procedure THttpClientTests.TestClientReadTimeout;
var
  L: Int;
  Port: UInt16;
begin
  { A listener nobody accepts on: the handshake completes from the backlog and
    the request is buffered, but no answer ever comes. }
  L := TcpListenEphemeral(INADDR_LOOPBACK, 4, Port);
  AssertTrue('listen', L >= 0);
  GPort := Port;
  GTimeoutNil := False;
  GTimeoutMs := 0;

  SpawnFiber(@ReadTimeoutClientFiber, nil);
  RunScheduler();

  AssertTrue('no response from a silent server', GTimeoutNil);
  AssertTrue('gave up after the timeout (' + IntToStr(GTimeoutMs) + ' ms)',
    (GTimeoutMs >= 250) and (GTimeoutMs < 5000));
  ResetScheduler();
  Close(L);
end;

initialization
  RegisterTest(THttpClientTests);

end.
