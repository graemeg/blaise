{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Net.Http.Server: request parsing, URL decoding, and a loopback
  request/response round-trip (incl. a WebSocket upgrade + broadcast).
  Self-registers via the initialization section. }

unit HttpServer.Tests;

interface

uses
  blaise.testing, Classes, SysUtils, Net.Http.Server, Net.Sockets, Net.WebSockets,
  StrUtils;

type
  THttpServerTests = class(TTestCase)
  published
    procedure TestUrlDecode;
    procedure TestParseGetWithQuery;
    procedure TestParseWebSocketKey;
    procedure TestRoundTrip;
    procedure TestStartAnyRoundTrip;
    procedure TestWebSocketUpgradeAndBroadcast;
    procedure TestLargeBody_NonBlockingListener;
    procedure TestSlowClient_NonBlockingListener;
  end;

  { Serves a fixed body, whatever the request. }
  TBodyHandler = class(IRequestHandler)
  private
    FBody: string;
  public
    constructor Create(const ABody: string);
    procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
  end;

  { Drives a server the way an application with an event loop does (Luhmann):
    the listener is non-blocking and PollOnce is called until one connection
    has been served.  Runs on its own thread so the test can act as client. }
  TPollServeThread = class(TThread)
  private
    FServer: THttpServer;
    FHandler: IRequestHandler;
    FServed: Boolean;
  protected
    procedure Execute; override;
  public
    constructor Create(AServer: THttpServer; AHandler: IRequestHandler);
    property Served: Boolean read FServed;
  end;

  { A trivial handler: echoes the path and the 'q' query param. }
  TEchoHandler = class(IRequestHandler)
    procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
  end;

implementation

procedure TEchoHandler.Handle(ARequest: THttpRequest; AResponse: THttpResponse);
begin
  AResponse.SetText(200, 'text/plain',
    ARequest.Path + '|' + ARequest.QueryParam('q'));
end;

constructor TBodyHandler.Create(const ABody: string);
begin
  FBody := ABody;
end;

procedure TBodyHandler.Handle(ARequest: THttpRequest; AResponse: THttpResponse);
begin
  AResponse.SetText(200, 'application/octet-stream', FBody);
end;

constructor TPollServeThread.Create(AServer: THttpServer; AHandler: IRequestHandler);
begin
  FServer := AServer;
  FHandler := AHandler;
  FServed := False;
  inherited Create(False);
end;

procedure TPollServeThread.Execute;
var
  Tries: Integer;
begin
  { Give up after ~10 s rather than hang the suite if no client arrives. }
  Tries := 0;
  while (not FServed) and (Tries < 10000) do
  begin
    FServed := FServer.PollOnce(FHandler);
    if not FServed then
    begin
      Sleep(1);
      Tries := Tries + 1;
    end;
  end;
end;

{ Read the whole response until the server closes, in large chunks: a
  megabyte through a 1 KB string-concatenation loop would be quadratic. }
function RecvAllLarge(AFd: Integer): string;
var
  SB: TStringBuilder;
  Chunk: string;
begin
  SB := TStringBuilder.Create();
  repeat
    Chunk := RecvString(AFd, 65536);
    SB.Append(Chunk);
  until Chunk = '';
  Result := SB.ToString();
  SB.Free();
end;

function PatternBody(ACount: Integer): string;
var
  SB: TStringBuilder;
  I: Integer;
begin
  SB := TStringBuilder.Create();
  for I := 0 to ACount - 1 do
    SB.AppendByte(Byte((I * 7 + I div 251) mod 256));
  Result := SB.ToString();
  SB.Free();
end;

{ Read until the server closes the connection.  One recv is not enough: the
  server sends the head and the body in separate writes, and on a slow host
  (FreeBSD under emulation in CI) the body can arrive after the first recv
  returns.  ServeOnce has already closed a plain HTTP connection, so this
  always terminates. }
function RecvUntilClosed(AFd: Integer): string;
var
  Chunk: string;
begin
  Result := '';
  repeat
    Chunk := RecvString(AFd, 1024);
    Result := Result + Chunk;
  until Chunk = '';
end;

procedure THttpServerTests.TestUrlDecode;
begin
  AssertEquals('percent', 'a b', UrlDecode('a%20b'));
  AssertEquals('plus',    'a b', UrlDecode('a+b'));
  AssertEquals('plain',   'abc', UrlDecode('abc'));
end;

procedure THttpServerTests.TestParseGetWithQuery;
var Req: THttpRequest;
begin
  Req := ParseRequest('GET /fruit/apple?q=red&n=2 HTTP/1.1'#13#10'Host: x'#13#10#13#10);
  AssertEquals('method', 'GET', Req.Method);
  AssertEquals('path', '/fruit/apple', Req.Path);
  AssertEquals('q', 'red', Req.QueryParam('q'));
  AssertEquals('n', '2', Req.QueryParam('n'));
  AssertFalse('not ws', Req.IsWebSocketUpgrade());
  Req.Free();
end;

procedure THttpServerTests.TestParseWebSocketKey;
var Req: THttpRequest;
begin
  Req := ParseRequest(
    'GET /reload HTTP/1.1'#13#10 +
    'Upgrade: websocket'#13#10 +
    'Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ=='#13#10#13#10);
  AssertTrue('is ws', Req.IsWebSocketUpgrade());
  AssertEquals('key', 'dGhlIHNhbXBsZSBub25jZQ==', Req.WebSocketKey);
  Req.Free();
end;

procedure THttpServerTests.TestRoundTrip;
const
  PORT = 28991;
var
  Srv: THttpServer;
  H: IRequestHandler;
  Cli: Integer;
  Resp: string;
begin
  Srv := THttpServer.Create(PORT);
  AssertTrue('start', Srv.Start());
  H := TEchoHandler.Create();

  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);
  AssertTrue('send', SendAll(Cli, 'GET /hi?q=net HTTP/1.1'#13#10'Host: x'#13#10#13#10));

  Srv.ServeOnce(H);
  Resp := RecvUntilClosed(Cli);
  AssertTrue('200', ContainsStr(Resp, '200 OK'));
  AssertTrue('body', ContainsStr(Resp, '/hi|net'));

  Close(Cli);
  Srv.Free();
end;

{ StartAny binds INADDR_ANY (0.0.0.0) rather than loopback, so a server is
  reachable from other machines.  Start stays loopback-only: a caller has to ask
  for external exposure by name.

  What this proves and what it does not: connecting over loopback to a socket
  bound to INADDR_ANY succeeds, so this confirms StartAny binds and serves
  correctly.  It does NOT prove external reachability — the suite has no second
  host — and no assertion here should be read as claiming otherwise. }
procedure THttpServerTests.TestStartAnyRoundTrip;
const
  PORT = 28993;
var
  Srv: THttpServer;
  H: IRequestHandler;
  Cli: Integer;
  Resp: string;
begin
  Srv := THttpServer.Create(PORT);
  AssertTrue('start any', Srv.StartAny());
  H := TEchoHandler.Create();

  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);
  AssertTrue('send', SendAll(Cli, 'GET /hi?q=any HTTP/1.1'#13#10'Host: x'#13#10#13#10));

  Srv.ServeOnce(H);
  Resp := RecvUntilClosed(Cli);
  AssertTrue('200', ContainsStr(Resp, '200 OK'));
  AssertTrue('body', ContainsStr(Resp, '/hi|any'));

  Close(Cli);
  Srv.Free();
end;

procedure THttpServerTests.TestWebSocketUpgradeAndBroadcast;
const
  PORT = 28992;
var
  Srv: THttpServer;
  H: IRequestHandler;
  Cli: Integer;
  Resp: string;
  D: TWsFrame;
begin
  Srv := THttpServer.Create(PORT);
  AssertTrue('start', Srv.Start());
  H := TEchoHandler.Create();

  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);
  SendAll(Cli,
    'GET /ws HTTP/1.1'#13#10 +
    'Upgrade: websocket'#13#10 +
    'Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ=='#13#10#13#10);

  Srv.ServeOnce(H);                 { completes handshake, keeps socket }
  Resp := RecvString(Cli, 1024);
  AssertTrue('101', ContainsStr(Resp, '101 Switching Protocols'));
  AssertTrue('accept', ContainsStr(Resp, 's3pPLMBiTxaQ9kYGzzhZRbK+xOo='));

  Srv.Broadcast('reload');
  Resp := RecvString(Cli, 64);
  D := DecodeFrame(Resp);
  AssertTrue('frame valid', D.Valid);
  AssertEquals('opcode', WS_OP_TEXT, D.Opcode);
  AssertEquals('payload', 'reload', D.Payload);

  Close(Cli);
  Srv.Free();
end;

{ A body far larger than a socket send buffer, served after SetNonBlocking.
  On macOS the accepted connection used to inherit O_NONBLOCK from the
  listener, send(2) hit EAGAIN once ~320 KB was buffered, SendAll gave up, and
  the connection closed with the body cut short (Luhmann's cytoscape.min.js). }
procedure THttpServerTests.TestLargeBody_NonBlockingListener;
const
  PORT = 28994;
  SIZE = 1024 * 1024 + 4321;
var
  Srv: THttpServer;
  H: IRequestHandler;
  Body, Resp: string;
  Cli, Sep: Integer;
  T: TPollServeThread;
begin
  Body := PatternBody(SIZE);
  Srv := THttpServer.Create(PORT);
  AssertTrue('start', Srv.Start());
  Srv.SetNonBlocking();
  H := TBodyHandler.Create(Body);
  T := TPollServeThread.Create(Srv, H);

  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);
  AssertTrue('send', SendAll(Cli, 'GET /big HTTP/1.1'#13#10'Host: x'#13#10#13#10));
  Resp := RecvAllLarge(Cli);
  T.WaitFor();
  AssertTrue('served', T.Served);

  AssertTrue('200', ContainsStr(Resp, '200 OK'));
  AssertTrue('content-length', ContainsStr(Resp, 'Content-Length: ' + IntToStr(SIZE)));
  Sep := PosEx(#13#10#13#10, Resp, 0);
  AssertTrue('head terminator', Sep >= 0);
  AssertEquals('every body byte arrives', SIZE, Length(Resp) - (Sep + 4));
  AssertTrue('body intact', Copy(Resp, Sep + 4, SIZE) = Body);

  T := nil;
  Close(Cli);
  Srv.Free();
end;

{ The request arrives AFTER the server has accepted the connection (a slow
  client, or a large request still in flight).  An accepted connection that
  inherited O_NONBLOCK read nothing, so the server parsed an empty request. }
procedure THttpServerTests.TestSlowClient_NonBlockingListener;
const
  PORT = 28995;
var
  Srv: THttpServer;
  H: IRequestHandler;
  Resp: string;
  Cli: Integer;
  T: TPollServeThread;
begin
  Srv := THttpServer.Create(PORT);
  AssertTrue('start', Srv.Start());
  Srv.SetNonBlocking();
  H := TEchoHandler.Create();
  T := TPollServeThread.Create(Srv, H);

  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);
  Sleep(200);                       { the server accepts before the request }
  AssertTrue('send', SendAll(Cli, 'GET /slow?q=late HTTP/1.1'#13#10'Host: x'#13#10#13#10));
  Resp := RecvAllLarge(Cli);
  T.WaitFor();

  AssertTrue('200', ContainsStr(Resp, '200 OK'));
  AssertTrue('request read in full', ContainsStr(Resp, '/slow|late'));

  T := nil;
  Close(Cli);
  Srv.Free();
end;

initialization
  RegisterTest(THttpServerTests);

end.
