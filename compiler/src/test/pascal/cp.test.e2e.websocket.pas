{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.websocket;

{ E2E test for L5 WAVE 2 (docs/async-networking-design.adoc): a fiber-driven
  WebSocket server (Net.WebSocket.Server) and client (Net.WebSocket.Client)
  cooperating on one single-worker scheduler over a loopback TCP port.  The
  client completes the RFC 6455 handshake, sends a masked text message, the
  server echoes it back unmasked, and the client prints the round-tripped text —
  the full compile -> native -> run integration proof the stdlib IR harness
  cannot give.

  Plaintext ws:// only (internal linker OK).  wss:// would drag in Net.Tls and
  force the external linker, so it is out of scope for this default e2e.

  BACKEND POSTURE: the WebSocket units pull in Net.Tcp -> async.io ->
  async.fibers (inline-asm context leaf), so this runs on the NATIVE backend
  only. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TWebSocketE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestFiberWsEcho_RoundTrip;
  end;

implementation

const
  LE = #10;

  { A fiber WebSocket echo server and a fiber client on one scheduler.  The
    server echoes each text message; the client handshakes, sends 'hello ws',
    reads the echo back, and prints it. }
  SrcWsEcho =
    '''
    program wse2e;
    uses SysUtils, Net.Tcp, Net.WebSockets, Net.WebSocket.Server,
         Net.WebSocket.Client, async.fibers;
    const PORT = 29711;
    var
      Srv: TWebSocketServer;
      Handler: IWebSocketHandler;

    type
      TEchoWs = class(IWebSocketHandler)
        procedure OnMessage(AConn: TWebSocketConn; const AData: string; AIsBinary: Boolean);
      end;

    procedure TEchoWs.OnMessage(AConn: TWebSocketConn; const AData: string; AIsBinary: Boolean);
    begin
      AConn.SendText(AData);
    end;

    procedure ServerFiber(AArg: Pointer);
    begin
      Srv.Serve(Handler);
    end;

    procedure ClientFiber(AArg: Pointer);
    var
      Cli: TWebSocketClient;
      Data: string;
      IsBin: Boolean;
    begin
      Cli := TWebSocketClient.Create();
      if not Cli.Connect('ws://127.0.0.1:29711/') then
        WriteLn('CONNFAIL')
      else
      begin
        Cli.SendText('hello ws');
        if Cli.ReadMessage(Data, IsBin) then
          WriteLn('ECHO:', Data)
        else
          WriteLn('NOREPLY');
      end;
      Cli.Free();
      Srv.Stop();
    end;

    begin
      Srv := TWebSocketServer.Create(PORT);
      if not Srv.Start() then begin WriteLn('LISTENFAIL'); Halt(1); end;
      Handler := TEchoWs.Create();
      SpawnFiber(@ServerFiber, nil);
      SpawnFiber(@ClientFiber, nil);
      RunScheduler();
      Srv.Free();
      Handler := nil;
      WriteLn('DONE');
    end.
    ''';

procedure TWebSocketE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-websocket')
end;

procedure TWebSocketE2ETests.TestFiberWsEcho_RoundTrip;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'ws-echo', SrcWsEcho,
    'ECHO:hello ws' + LE + 'DONE' + LE, 0)
end;

initialization
  RegisterTest(TWebSocketE2ETests);

end.
