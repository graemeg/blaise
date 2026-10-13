{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ E2E test for L4/L5 TLS (docs/async-networking-design.adoc, "L4 - TLS" +
  [#components]): build a NATIVE program that stands up a loopback TLS echo
  server + TLS client (Net.Tls over Net.Tcp, memory-BIO pump over async.io) and
  assert the DECRYPTED body on stdout — the real end-to-end TLS proof.

  This suite SHELLS OUT to the production compiler binary (compiler/target/blaise)
  with `--backend native --linker external`, exactly how a TLS program is built
  in practice: Net.Tls(.Provider) binds libssl/libcrypto via `external 'ssl'/
  'crypto'`, and only the EXTERNAL linker can resolve an external library (the
  default internal linker errors out).  Compiling via the real binary (rather
  than the in-process e2e codegen path) is also the only reliable route — the
  in-process harness corrupts state on `external 'lib'` units (see bugs.txt).

  The program source is the committed proof program
  stdlib/src/test/pascal/tlsloopback.pas.  The self-signed server certificate is
  generated in SetUp via the openssl CLI into the scratch dir, so nothing secret
  is committed.  The suite skips cleanly when the compiler binary, the C
  toolchain, or the openssl CLI is unavailable. }

unit Cp.Test.E2E.Tls;

interface

uses
  SysUtils, process, blaise.testing, cp.test.e2e.base, blaise.codegen.target;

type
  TeTlsE2ETests = class(TE2ETestCase)
  private
    FCert: string;
    FKey: string;
    FBin: string;
    function ToolPresent(const AExe: string; const AArg: string): Boolean;
    function GenerateCert: Boolean;
    function BuildTlsProgram(out ABuildLog: string): Boolean;
  protected
    procedure SetUp; override;
  published
    procedure TestTlsLoopbackEcho_DecryptedBody;
  end;

implementation

const
  LE = #10;

function TeTlsE2ETests.ToolPresent(const AExe: string; const AArg: string): Boolean;
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

function TeTlsE2ETests.GenerateCert: Boolean;
var
  P: TProcess;
begin
  FCert := FScratch + '/tls-cert.pem';
  FKey := FScratch + '/tls-key.pem';
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
      P.Parameters.Add('/CN=localhost');
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

function TeTlsE2ETests.BuildTlsProgram(out ABuildLog: string): Boolean;
var
  P: TProcess;
  Root, Compiler, Src, Chunk: string;
begin
  Root := Self.ProjectRoot();
  Compiler := Root + 'compiler/target/blaise';
  Src := Root + 'stdlib/src/test/pascal/tlsloopback.pas';
  FBin := FScratch + '/tlsloopback';
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

procedure TeTlsE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-tls');
end;

procedure TeTlsE2ETests.TestTlsLoopbackEcho_DecryptedBody;
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
  Built := Self.BuildTlsProgram(BuildLog);
  AssertTrue('native TLS program built (--linker external): ' + BuildLog,
    Built);

  { Run the loopback TLS echo binary with the cert/key and capture stdout. }
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
    AssertEquals('TLS loopback exit code', 0, P.ExitCode);
  finally
    P.Free();
  end;

  { tlsloopback.pas prints a fixed transcript proving a real handshake +
    encrypted round-trip on both ends. }
  AssertTrue('server handshake completed', Pos('HS-SERVER-OK', Output) >= 0);
  AssertTrue('client handshake completed', Pos('HS-CLIENT-OK', Output) >= 0);
  AssertTrue('server decrypted client plaintext',
    Pos('SERVER-GOT:hello-tls', Output) >= 0);
  AssertTrue('client decrypted server echo',
    Pos('CLIENT-GOT:srv:hello-tls', Output) >= 0);
  AssertTrue('overall OK', Pos('OK' + LE, Output) >= 0);
end;

initialization
  RegisterTest(TeTlsE2ETests);

end.
