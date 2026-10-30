{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Standalone https round-trip proof for L5 Net.Http.Client over TLS.

  A fiber TTlsServer (self-signed cert, CN/SAN = 127.0.0.1) serves a fixed
  HTTP/1.1 response over TLS.  A THttpClient then performs an https GET against
  https://127.0.0.1:PORT/ THREE ways:

    1. verify=True with the self-signed CA PINNED via TrustCaFile  -> must SUCCEED
       (real certificate verification, not verify-off) and return 200 + body.
    2. verify=True with NO CA pinned                              -> must FAIL
       (the self-signed cert is untrusted; the request fails loudly, returning
       nil, rather than silently succeeding).
    3. InsecureSkipVerify=True (loud opt-out)                     -> must SUCCEED
       (verification disabled), proving the opt-out path.

  It also proves keep-alive POOL REUSE for https (two GETs on one client reuse a
  single server-side TLS connection) and a CROSS-SCHEME REDIRECT (a plaintext
  http 301 -> the https origin, which the client re-dials over TLS).

  Prints a fixed transcript:

    TRUSTED-STATUS:200
    TRUSTED-BODY:hello-https
    UNTRUSTED:rejected
    INSECURE-STATUS:200
    REUSE-BODY1:hello-https
    REUSE-BODY2:hello-https
    REDIRECT-STATUS:200
    REDIRECT-BODY:hello-https
    OK

  On failure prints FAIL:<reason> and exits non-zero.

  MUST be built with `--backend native --linker external`.
  Args: <cert> <key>. }

program HttpsLoopback;

uses
  SysUtils, async.fibers, Net.Tcp, Net.Tls, Net.Tls.Provider,
  Net.Http.Client, Net.Http.Client.Tls;

const
  PORT = 29531;          { TLS server }
  RPORT = 29532;         { plaintext http server that redirects to TLS }
  BODY = 'hello-https';

var
  GServer: TTlsServer;
  GRedir: TTcpServer;
  GCert: string;
  GKey: string;
  GCaFile: string;

  { results captured by the client fiber }
  GTrustedStatus: Int;
  GTrustedBody: string;
  GUntrustedRejected: Boolean;
  GInsecureStatus: Int;
  GReuseBody1: string;
  GReuseBody2: string;
  GConnCount: Int;        { server-side accepted TLS connections }
  GRedirStatus: Int;      { status after following an http->https redirect }
  GRedirBody: string;

type
  { Keep-alive HTTP/1.1 handler over TLS: serves each request on the connection
    with a Content-Length body and keeps the connection open (Connection:
    keep-alive) so the client's pool can reuse it.  Loops until the client
    stops sending.  Each accepted connection bumps GConnCount, so the client
    can prove that two GETs reused ONE connection. }
  THttpsHandler = class(ITlsConnHandler)
    procedure Handle(AStream: TTlsStream);
  end;

procedure THttpsHandler.Handle(AStream: TTlsStream);
var
  Req, Resp: string;
begin
  GConnCount := GConnCount + 1;
  while True do
  begin
    Req := AStream.Read(4096);
    if Req = '' then
      Break;                  { client closed / EOF }
    Resp := 'HTTP/1.1 200 OK'#13#10 +
            'Content-Type: text/plain'#13#10 +
            'Content-Length: ' + IntToStr(Length(BODY)) + #13#10 +
            'Connection: keep-alive'#13#10 +
            #13#10 + BODY;
    if not AStream.Write(Resp) then
      Break;
  end;
end;

type
  { Plaintext http handler that 301-redirects every request to the TLS origin,
    proving an http->https redirect crosses transports (the client must re-dial
    over TLS). }
  TRedirectHandler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

procedure TRedirectHandler.Handle(AConn: TTcpConn);
var
  Req, Resp: string;
begin
  Req := AConn.Read(4096);
  if Req = '' then
    Exit;
  Resp := 'HTTP/1.1 301 Moved Permanently'#13#10 +
          'Location: https://127.0.0.1:' + IntToStr(PORT) + '/'#13#10 +
          'Content-Length: 0'#13#10 +
          'Connection: close'#13#10 +
          #13#10;
  AConn.Write(Resp);
end;

var
  GHandler: ITlsConnHandler;
  GRedirHandler: IConnHandler;

procedure ServerFiber(AArg: Pointer);
begin
  GServer.Serve(GHandler);
end;

procedure RedirServerFiber(AArg: Pointer);
begin
  GRedir.Serve(GRedirHandler);
end;

{ Issue one https GET; return the response (caller frees) or nil on failure. }
function DoGet(ACaFile: string; AInsecure: Boolean): THttpClientResponse;
var
  Cli: THttpClient;
begin
  Cli := THttpClient.Create();
  Cli.TrustCaFile := ACaFile;
  Cli.InsecureSkipVerify := AInsecure;
  Result := Cli.Get('https://127.0.0.1:' + IntToStr(PORT) + '/');
  Cli.Free();
end;

{ GET an explicit URL with a pinned CA (used for the redirect-crossing GET). }
function DoGetOn(AUrl, ACaFile: string): THttpClientResponse;
var
  Cli: THttpClient;
begin
  Cli := THttpClient.Create();
  Cli.TrustCaFile := ACaFile;
  Result := Cli.Get(AUrl);
  Cli.Free();
end;

procedure ClientFiber(AArg: Pointer);
var
  R1, R3: THttpClientResponse;
  R2: THttpClientResponse;
  Reuse: THttpClient;
  RA, RB: THttpClientResponse;
  BaseCount: Int;
begin
  FiberSleep(3);

  { 1. trusted (CA pinned, verify ON) }
  R1 := DoGet(GCaFile, False);
  if R1 <> nil then
  begin
    GTrustedStatus := R1.Status;
    GTrustedBody := R1.Body;
    R1.Free();
  end;

  { 2. untrusted (verify ON, no CA pinned) -> must be rejected (nil) }
  R2 := DoGet('', False);
  GUntrustedRejected := (R2 = nil);
  if R2 <> nil then
    R2.Free();

  { 3. insecure opt-out (verify OFF) -> succeeds }
  R3 := DoGet('', True);
  if R3 <> nil then
  begin
    GInsecureStatus := R3.Status;
    R3.Free();
  end;

  { 4. keep-alive reuse: ONE client, TWO https GETs.  The keep-alive handler
    keeps the TLS connection open, so the pool must reuse it — the server-side
    connection count must NOT increase on the second GET. }
  BaseCount := GConnCount;
  Reuse := THttpClient.Create();
  Reuse.TrustCaFile := GCaFile;
  RA := Reuse.Get('https://127.0.0.1:' + IntToStr(PORT) + '/');
  if RA <> nil then
  begin
    GReuseBody1 := RA.Body;
    RA.Free();
  end;
  RB := Reuse.Get('https://127.0.0.1:' + IntToStr(PORT) + '/');
  if RB <> nil then
  begin
    GReuseBody2 := RB.Body;
    RB.Free();
  end;
  { exactly one new connection for the two GETs proves reuse. }
  if (GConnCount - BaseCount) <> 1 then
    GReuseBody2 := '<no-reuse:conns=' + IntToStr(GConnCount - BaseCount) + '>';
  Reuse.Free();

  { 5. cross-scheme redirect: GET the PLAINTEXT http server, which 301s to the
    https origin; the client must re-dial over TLS and return 200 + body. }
  RA := DoGetOn('http://127.0.0.1:' + IntToStr(RPORT) + '/', GCaFile);
  if RA <> nil then
  begin
    GRedirStatus := RA.Status;
    GRedirBody := RA.Body;
    RA.Free();
  end;

  GRedir.Stop();
  GServer.Stop();
end;

begin
  if ParamCount() < 2 then
  begin
    WriteLn('FAIL:usage <cert> <key>');
    Halt(2);
  end;
  GCert := ParamStr(1);
  GKey := ParamStr(2);
  GCaFile := GCert;            { self-signed: the server cert IS its own CA }

  GTrustedStatus := 0;
  GTrustedBody := '';
  GUntrustedRejected := False;
  GInsecureStatus := 0;
  GReuseBody1 := '';
  GReuseBody2 := '';
  GConnCount := 0;
  GRedirStatus := 0;
  GRedirBody := '';

  InstallOpenSSLProvider();
  if GTlsProvider = nil then
  begin
    WriteLn('FAIL:no-provider');
    Halt(1);
  end;
  if HttpTlsDialer() = nil then
  begin
    WriteLn('FAIL:no-dialer');
    Halt(1);
  end;

  GServer := TTlsServer.Create(PORT, GCert, GKey);
  if not GServer.Start() then
  begin
    WriteLn('FAIL:server-start');
    Halt(1);
  end;
  GHandler := THttpsHandler.Create();

  GRedir := TTcpServer.Create(RPORT);
  if not GRedir.Start() then
  begin
    WriteLn('FAIL:redir-start');
    Halt(1);
  end;
  GRedirHandler := TRedirectHandler.Create();

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@RedirServerFiber, nil);
  SpawnFiber(@ClientFiber, nil);
  RunScheduler();

  WriteLn('TRUSTED-STATUS:' + IntToStr(GTrustedStatus));
  WriteLn('TRUSTED-BODY:' + GTrustedBody);
  if GUntrustedRejected then
    WriteLn('UNTRUSTED:rejected')
  else
    WriteLn('UNTRUSTED:accepted');
  WriteLn('INSECURE-STATUS:' + IntToStr(GInsecureStatus));
  WriteLn('REUSE-BODY1:' + GReuseBody1);
  WriteLn('REUSE-BODY2:' + GReuseBody2);
  WriteLn('REDIRECT-STATUS:' + IntToStr(GRedirStatus));
  WriteLn('REDIRECT-BODY:' + GRedirBody);

  if (GTrustedStatus = 200) and (GTrustedBody = BODY) and
     GUntrustedRejected and (GInsecureStatus = 200) and
     (GReuseBody1 = BODY) and (GReuseBody2 = BODY) and
     (GRedirStatus = 200) and (GRedirBody = BODY) then
    WriteLn('OK')
  else
  begin
    WriteLn('FAIL:assertions');
    Halt(1);
  end;
end.
