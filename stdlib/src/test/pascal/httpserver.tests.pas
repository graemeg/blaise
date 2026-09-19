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
  blaise.testing, Net.Http.Server, Net.Sockets, Net.WebSockets, StrUtils;

type
  THttpServerTests = class(TTestCase)
  published
    procedure TestUrlDecode;
    procedure TestParseGetWithQuery;
    procedure TestParseWebSocketKey;
    procedure TestRoundTrip;
    procedure TestStartAnyRoundTrip;
    procedure TestWebSocketUpgradeAndBroadcast;
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
  Resp := RecvString(Cli, 1024);
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
  Resp := RecvString(Cli, 1024);
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

initialization
  RegisterTest(THttpServerTests);

end.
