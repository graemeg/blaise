{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.httpfiber;

{ E2E test for L5 Net.Tcp + the rewritten fiber Net.Http.Server
  (docs/async-networking-design.adoc, [#components], GO/NO-GO gate): a fiber
  HTTP server plus a fiber HTTP client (built on Net.Tcp) exchanging a GET over
  a loopback port, asserting the response body reaches stdout — the compile ->
  native -> run integration proof the IR/stdlib harness cannot give.

  BACKEND POSTURE: Net.Tcp/async.io pull in the inline-asm context leaf, so this
  runs on the NATIVE backend only. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TeHttpFiberE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestFiberHttpServerClient_Body;
  end;

implementation

const
  LE = #10;

  { A fiber HTTP server (THttpFiberServer) serving 'path=<path>', plus a fiber
    client (on Net.Tcp) that GETs /hello, reads the body, prints it, and stops
    the server so the scheduler drains. }
  SrcHttpFiber =
    '''
    program httpfibere2e;
    uses SysUtils, StrUtils, Net.Http.Server, Net.Tcp, async.fibers;
    const PORT = 29533;
    type
      TPathHandler = class(IRequestHandler)
        procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
      end;
    procedure TPathHandler.Handle(ARequest: THttpRequest; AResponse: THttpResponse);
    begin
      AResponse.SetText(200, 'text/plain', 'path=' + ARequest.Path);
    end;
    var
      GSrv: THttpFiberServer;
      GHandler: IRequestHandler;

    procedure ServerFiber(AArg: Pointer);
    begin
      GSrv.Serve(GHandler);
    end;

    procedure ClientFiber(AArg: Pointer);
    var
      Cli: TTcpClient;
      Conn: TTcpConn;
      Acc, Chunk: string;
      Sep, HeadLen: Integer;
    begin
      Cli := TTcpClient.Create();
      Conn := Cli.Connect('127.0.0.1', PORT);
      Cli.Free();
      if Conn = nil then begin WriteLn('CONNFAIL'); GSrv.Stop(); Exit; end;
      Conn.Write('GET /hello HTTP/1.1'#13#10'Host: x'#13#10'Connection: close'#13#10#13#10);
      Acc := '';
      while True do
      begin
        Sep := PosEx(#13#10#13#10, Acc, 0);
        if Sep >= 0 then Break;
        Chunk := Conn.Read(4096);
        if Chunk = '' then Break;
        Acc := Acc + Chunk;
      end;
      Sep := PosEx(#13#10#13#10, Acc, 0);
      if Sep < 0 then begin WriteLn('NOHEAD'); Conn.Free(); GSrv.Stop(); Exit; end;
      HeadLen := Sep + 4;
      while Length(Acc) - HeadLen < Length('path=/hello') do
      begin
        Chunk := Conn.Read(64);
        if Chunk = '' then Break;
        Acc := Acc + Chunk;
      end;
      WriteLn('BODY:', Copy(Acc, HeadLen, Length(Acc) - HeadLen));
      Conn.Free();
      GSrv.Stop();
    end;

    begin
      GSrv := THttpFiberServer.Create(PORT);
      if not GSrv.Start() then begin WriteLn('STARTFAIL'); Halt(1); end;
      GHandler := TPathHandler.Create();
      SpawnFiber(@ServerFiber, nil);
      SpawnFiber(@ClientFiber, nil);
      RunScheduler();
      GSrv.Free();
      WriteLn('DONE');
    end.
    ''';

procedure TeHttpFiberE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-httpfiber')
end;

procedure TeHttpFiberE2ETests.TestFiberHttpServerClient_Body;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'httpfiber', SrcHttpFiber,
    'BODY:path=/hello' + LE + 'DONE' + LE, 0)
end;

initialization
  RegisterTest(TeHttpFiberE2ETests);

end.
