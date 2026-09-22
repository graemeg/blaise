{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.httpclient;

{ E2E test for L5 Net.Http.Client (docs/async-networking-design.adoc, L5): a
  fiber HTTP client (THttpClient) GETs from a fiber HTTP server (THttpFiberServer)
  over a loopback port, asserting the decoded response status + body reach stdout
  -- the compile -> native -> run integration proof the IR/stdlib harness cannot
  give.

  BACKEND POSTURE: Net.Tcp/async.io pull in the inline-asm context leaf, so this
  runs on the NATIVE backend only.  Plaintext http keeps it on the default
  internal linker (an https variant would need --linker external + a TLS
  provider). }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TeHttpClientE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestFiberHttpClientGet_Body;
  end;

implementation

const
  LE = #10;

  { A fiber HTTP server serving 'path=<path>', plus a fiber client that uses
    Net.Http.Client.Get to fetch /hello, prints the status and decoded body, and
    stops the server so the scheduler drains. }
  SrcHttpClient =
    '''
    program httpcliente2e;
    uses SysUtils, Net.Http.Server, Net.Http.Client, async.fibers;
    const PORT = 29543;
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
      Cli: THttpClient;
      Resp: THttpClientResponse;
    begin
      Cli := THttpClient.Create();
      Resp := Cli.Get('http://127.0.0.1:29543/hello');
      if Resp = nil then begin WriteLn('REQFAIL'); Cli.Free(); GSrv.Stop(); Exit; end;
      WriteLn('STATUS:', Resp.Status);
      WriteLn('BODY:', Resp.Body);
      Resp.Free();
      Cli.Free();
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

procedure TeHttpClientE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-httpclient')
end;

procedure TeHttpClientE2ETests.TestFiberHttpClientGet_Body;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'httpclient', SrcHttpClient,
    'STATUS:200' + LE + 'BODY:path=/hello' + LE + 'DONE' + LE, 0)
end;

initialization
  RegisterTest(TeHttpClientE2ETests);

end.
