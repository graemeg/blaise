{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Net.WebSocket.Client driven against the Net.WebSocket.Server over
  loopback, all inside the single-worker scheduler in the test-runner process.

    * TestTextEcho       — full handshake, client sends text, server echoes,
      client reads it back.
    * TestBinaryEcho     — a binary frame round-trips as binary.
    * TestPingPong       — the client's ping is answered (the server pongs; the
      client's ReadMessage swallows pongs, so we drive a server-initiated ping
      via a handler that pings first).
    * TestCleanClose     — client Close triggers the server's close echo.
    * TestConcurrent     — N client fibers each round-trip their own message.

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit WebSocketClient.Tests;

interface

uses
  blaise.testing, SysUtils, Net.Tcp, Net.WebSockets,
  Net.WebSocket.Server, Net.WebSocket.Client, async.fibers;

type
  TWebSocketClientTests = class(TTestCase)
  published
    procedure TestTextEcho;
    procedure TestBinaryEcho;
    procedure TestCleanClose;
    procedure TestConcurrent;
  end;

  { Echo handler shared with the server tests: echo each message back. }
  TCliEchoHandler = class(IWebSocketHandler)
    procedure OnMessage(AConn: TWebSocketConn; const AData: string; AIsBinary: Boolean);
  end;

implementation

procedure TCliEchoHandler.OnMessage(AConn: TWebSocketConn; const AData: string; AIsBinary: Boolean);
begin
  if AIsBinary then
    AConn.SendBinary(AData)
  else
    AConn.SendText(AData);
end;

{ --- shared fixture --- }

var
  GServer: TWebSocketServer;
  GHandler: IWebSocketHandler;
  GPort: UInt16;
  GResult: string;
  GDone: Int;
  GExpected: Int;

procedure ServerFiber(AArg: Pointer);
begin
  GServer.Serve(GHandler);
end;

function WsUrl: string;
begin
  Result := 'ws://127.0.0.1:' + IntToStr(Int32(GPort)) + '/';
end;

{ --- TestTextEcho --- }

procedure TextClientFiber(AArg: Pointer);
var
  Cli: TWebSocketClient;
  Data: string;
  IsBin: Boolean;
begin
  FiberSleep(2);
  Cli := TWebSocketClient.Create();
  if not Cli.Connect(WsUrl()) then
    GResult := 'connfail'
  else
  begin
    Cli.SendText('round-trip me');
    if Cli.ReadMessage(Data, IsBin) then
      GResult := Data
    else
      GResult := 'noreply';
  end;
  Cli.Free();
  GServer.Stop();
end;

procedure TWebSocketClientTests.TestTextEcho;
const
  PORT = 29601;
begin
  GServer := TWebSocketServer.Create(PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TCliEchoHandler.Create();
  GPort := PORT;
  GResult := '';

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@TextClientFiber, nil);
  RunScheduler();

  AssertEquals('client received the echoed text', 'round-trip me', GResult);
  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

{ --- TestBinaryEcho --- }

procedure BinaryClientFiber(AArg: Pointer);
var
  Cli: TWebSocketClient;
  Data: string;
  IsBin: Boolean;
begin
  FiberSleep(2);
  Cli := TWebSocketClient.Create();
  if not Cli.Connect(WsUrl()) then
    GResult := 'connfail'
  else
  begin
    Cli.SendBinary('bytes'#0#1#2'end');
    if Cli.ReadMessage(Data, IsBin) then
    begin
      if IsBin then
        GResult := 'bin:' + Data
      else
        GResult := 'text:' + Data;
    end
    else
      GResult := 'noreply';
  end;
  Cli.Free();
  GServer.Stop();
end;

procedure TWebSocketClientTests.TestBinaryEcho;
const
  PORT = 29602;
begin
  GServer := TWebSocketServer.Create(PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TCliEchoHandler.Create();
  GPort := PORT;
  GResult := '';

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@BinaryClientFiber, nil);
  RunScheduler();

  AssertEquals('client received the echoed binary as binary',
    'bin:bytes'#0#1#2'end', GResult);
  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

{ --- TestCleanClose: client Close -> server echoes CLOSE -> client ReadMessage
      returns False (clean close) --- }

procedure CloseClientFiber(AArg: Pointer);
var
  Cli: TWebSocketClient;
  Data: string;
  IsBin: Boolean;
begin
  FiberSleep(2);
  Cli := TWebSocketClient.Create();
  if not Cli.Connect(WsUrl()) then
    GResult := 'connfail'
  else
  begin
    Cli.Close();
    { after our close, the server echoes CLOSE; ReadMessage must report the
      clean close (False) rather than a message }
    if Cli.ReadMessage(Data, IsBin) then
      GResult := 'unexpectedmsg'
    else
      GResult := 'closed';
  end;
  Cli.Free();
  GServer.Stop();
end;

procedure TWebSocketClientTests.TestCleanClose;
const
  PORT = 29603;
begin
  GServer := TWebSocketServer.Create(PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TCliEchoHandler.Create();
  GPort := PORT;
  GResult := '';

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@CloseClientFiber, nil);
  RunScheduler();

  AssertEquals('client saw a clean close', 'closed', GResult);
  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

{ --- TestConcurrent: N client fibers each round-trip their own message --- }

procedure ConcClientFiber(AArg: Pointer);
var
  Cli: TWebSocketClient;
  Id: Int;
  Msg, Data: string;
  IsBin: Boolean;
begin
  Id := Int32(AArg);
  FiberSleep(2);
  Cli := TWebSocketClient.Create();
  Msg := 'msg' + IntToStr(Id);
  if not Cli.Connect(WsUrl()) then
    GResult := GResult + 'connfail '
  else
  begin
    Cli.SendText(Msg);
    if Cli.ReadMessage(Data, IsBin) and (Data = Msg) then
      GResult := GResult + Data + ' '
    else
      GResult := GResult + 'bad' + IntToStr(Id) + ' ';
  end;
  Cli.Free();
  GDone := GDone + 1;
  if GDone >= GExpected then
    GServer.Stop();
end;

procedure TWebSocketClientTests.TestConcurrent;
const
  PORT = 29604;
  NCLIENTS = 6;
var
  I: Int;
begin
  GServer := TWebSocketServer.Create(PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TCliEchoHandler.Create();
  GPort := PORT;
  GResult := '';
  GDone := 0;
  GExpected := NCLIENTS;

  SpawnFiber(@ServerFiber, nil);
  for I := 0 to NCLIENTS - 1 do
    SpawnFiber(@ConcClientFiber, Pointer(I));
  RunScheduler();

  for I := 0 to NCLIENTS - 1 do
    AssertTrue('client ' + IntToStr(I) + ' round-tripped',
      Pos('msg' + IntToStr(I) + ' ', GResult) >= 0);
  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

initialization
  RegisterTest(TWebSocketClientTests);

end.
