{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ E2E test for L5 https (Net.Http.Client over Net.Tls): build a NATIVE program
  that stands up a loopback TLS HTTP/1.1 server + a plaintext redirect server,
  then drives THttpClient over https and asserts the DECRYPTED body + status on
  stdout — the real end-to-end https proof.

  Like cp.test.e2e.tls.pas, this suite SHELLS OUT to the production compiler
  binary (compiler/target/blaise) with `--backend native --linker external`,
  exactly how an https program is built in practice: Net.Http.Client.Tls
  transitively binds libssl/libcrypto via `external 'ssl'/'crypto'`, and only
  the EXTERNAL linker can resolve an external library.  Compiling via the real
  binary (rather than the in-process e2e codegen path) is also the only reliable
  route — the in-process harness corrupts state on `external 'lib'` units (see
  bugs.txt), so the plaintext client stays libssl-free and https lives here.

  The program source is the committed proof stdlib/src/test/pascal/httpsloopback.pas.
  A self-signed server certificate (CN/SAN = 127.0.0.1) is generated in SetUp via
  the openssl CLI into the scratch dir; the proof trusts it via THttpClient's
  TrustCaFile (verify ON — real verification), and also proves the verify-FAILURE
  path (untrusted -> rejected) and the InsecureSkipVerify opt-out.  The suite
  skips cleanly when the compiler binary, the C toolchain, or openssl is absent. }

unit Cp.Test.E2E.HttpsClient;

interface

uses
  SysUtils, process, blaise.testing, cp.test.e2e.base, blaise.codegen.target;

type
  TeHttpsClientE2ETests = class(TE2ETestCase)
  private
    FCert: string;
    FKey: string;
    FBin: string;
    function ToolPresent(const AExe: string; const AArg: string): Boolean;
    function GenerateCert: Boolean;
    function BuildHttpsProgram(out ABuildLog: string): Boolean;
  protected
    procedure SetUp; override;
  published
    procedure TestHttpsLoopback_DecryptedBodyAndVerify;
  end;

implementation

const
  LE = #10;

function TeHttpsClientE2ETests.ToolPresent(const AExe: string; const AArg: string): Boolean;
var
  P: TProcess;
begin
  Result := False;
  try
    P := TProcess.Create(nil);
    try
      P.Executable := AExe;
      P.Parameters.Add(AArg);
      P.Execute();
      P.WaitOnExit();
      Result := True;              { it ran (any exit code) => present }
    finally
      P.Free();
    end;
  except
    Result := False;              { executable not found }
  end;
end;

function TeHttpsClientE2ETests.GenerateCert: Boolean;
var
  P: TProcess;
begin
  FCert := FScratch + '/https-cert.pem';
  FKey := FScratch + '/https-key.pem';
  Result := False;
  try
    P := TProcess.Create(nil);
    try
      P.Executable := 'openssl';
      P.Parameters.Add('req');
      P.Parameters.Add('-x509');
      P.Parameters.Add('-newkey');
      P.Parameters.Add('rsa:2048');
      P.Parameters.Add('-nodes');
      P.Parameters.Add('-keyout');
      P.Parameters.Add(FKey);
      P.Parameters.Add('-out');
      P.Parameters.Add(FCert);
      P.Parameters.Add('-days');
      P.Parameters.Add('3650');
      P.Parameters.Add('-subj');
      P.Parameters.Add('/CN=127.0.0.1');
      P.Parameters.Add('-addext');
      P.Parameters.Add('subjectAltName=DNS:localhost,IP:127.0.0.1');
      P.Execute();
      P.WaitOnExit();
      Result := (P.ExitCode = 0) and FileExists(FCert) and FileExists(FKey);
    finally
      P.Free();
    end;
  except
    Result := False;
  end;
end;

function TeHttpsClientE2ETests.BuildHttpsProgram(out ABuildLog: string): Boolean;
var
  P: TProcess;
  Root, Compiler, Src, Chunk: string;
begin
  Root := Self.ProjectRoot();
  Compiler := Root + 'compiler/target/blaise';
  Src := Root + 'stdlib/src/test/pascal/httpsloopback.pas';
  FBin := FScratch + '/httpsloopback';
  ABuildLog := '';
  Result := False;
  try
    P := TProcess.Create(nil);
    try
      P.Executable := Compiler;
      P.Parameters.Add('--source');
      P.Parameters.Add(Src);
      P.Parameters.Add('--output');
      P.Parameters.Add(FBin);
      P.Parameters.Add('--backend');
      P.Parameters.Add('native');
      P.Parameters.Add('--linker');
      P.Parameters.Add('external');
      P.Parameters.Add('--unit-path');
      P.Parameters.Add(Root + 'stdlib/src/main/pascal');
      P.Parameters.Add('--unit-path');
      P.Parameters.Add(Root + 'runtime/src/main/pascal');
      if Self.OpenSslLibDir() <> '' then
      begin
        P.Parameters.Add('--lib-path');
        P.Parameters.Add(Self.OpenSslLibDir());
      end;
      P.Execute();
      repeat
        Chunk := P.ReadOutput();
        ABuildLog := ABuildLog + Chunk;
      until (Chunk = '') and not P.Running;
      P.WaitOnExit();
      Result := (P.ExitCode = 0) and FileExists(FBin);
      if not Result then
        ABuildLog := ABuildLog + LE + '[compiler exit ' + IntToStr(P.ExitCode) +
          ', binary present: ' + BoolToStr(FileExists(FBin), True) + ']';
    finally
      P.Free();
    end;
  except
    on E: Exception do
    begin
      ABuildLog := ABuildLog + LE + '[exception: ' + E.Message + ']';
      Result := False;
    end;
  end;
end;

procedure TeHttpsClientE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-https');
end;

procedure TeHttpsClientE2ETests.TestHttpsLoopback_DecryptedBodyAndVerify;
var
  P: TProcess;
  BuildLog, Output, Chunk: string;
  Built: Boolean;
begin
  if not ToolPresent('cc', '--version') then begin Ignore('cc unavailable'); Exit; end;
  if not ToolPresent('openssl', 'version') then begin Ignore('openssl unavailable'); Exit; end;
  { macOS ships the openssl CLI but no linkable libssl }
  if (HostTarget().OS = osMacOS) and (Self.OpenSslLibDir() = '') then
  begin Ignore('no linkable libssl (install a Homebrew OpenSSL)'); Exit; end;
  if not FileExists(Self.ProjectRoot() + 'compiler/target/blaise') then
  begin Ignore('compiler binary unavailable'); Exit; end;
  if not GenerateCert() then begin Ignore('cert generation failed'); Exit; end;

  { Build first, then assert: the message argument is evaluated before the
    call it would wrap, so passing the build inline reported an empty log. }
  Built := Self.BuildHttpsProgram(BuildLog);
  AssertTrue('native https program built (--linker external): ' + BuildLog,
    Built);

  { Run the https loopback binary with the cert/key and capture stdout. }
  Output := '';
  P := TProcess.Create(nil);
  try
    P.Executable := FBin;
    P.Parameters.Add(FCert);
    P.Parameters.Add(FKey);
    P.Execute();
    repeat
      Chunk := P.ReadOutput();
      Output := Output + Chunk;
    until (Chunk = '') and not P.Running;
    P.WaitOnExit();
    AssertEquals('https loopback exit code', 0, P.ExitCode);
  finally
    P.Free();
  end;

  { httpsloopback.pas prints a fixed transcript proving: a real TLS handshake +
    decrypted 200 body under verify=True with a pinned CA; a LOUD verify-failure
    (untrusted -> rejected); the insecure opt-out; keep-alive pool reuse; and an
    http->https cross-scheme redirect. }
  AssertTrue('trusted https 200', Pos('TRUSTED-STATUS:200', Output) >= 0);
  AssertTrue('trusted decrypted body', Pos('TRUSTED-BODY:hello-https', Output) >= 0);
  AssertTrue('untrusted cert rejected (verify-failure is loud)',
    Pos('UNTRUSTED:rejected', Output) >= 0);
  AssertTrue('insecure opt-out succeeds', Pos('INSECURE-STATUS:200', Output) >= 0);
  AssertTrue('keep-alive reuse GET #1', Pos('REUSE-BODY1:hello-https', Output) >= 0);
  AssertTrue('keep-alive reuse GET #2', Pos('REUSE-BODY2:hello-https', Output) >= 0);
  AssertTrue('http->https redirect status', Pos('REDIRECT-STATUS:200', Output) >= 0);
  AssertTrue('http->https redirect body', Pos('REDIRECT-BODY:hello-https', Output) >= 0);
  AssertTrue('overall OK', Pos('OK' + LE, Output) >= 0);
end;

initialization
  RegisterTest(TeHttpsClientE2ETests);

end.
