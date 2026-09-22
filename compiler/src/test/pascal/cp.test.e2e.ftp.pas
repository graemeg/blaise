{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.ftp;

{ E2E test for the L5 FTP wave (Net.Ftp + Net.Ftp.Server).  A program spins up a
  real TFtpServer (backed by an in-memory store) plus a TFtpClient fiber over a
  loopback port; the client logs in, STORs a file, RETRs it back, LISTs, and the
  program prints markers proving the compile -> native -> run round-trip that the
  IR/stdlib harness cannot give - in particular that the two-connection PASV data
  transfer carries the bytes byte-exact end to end.

  Plaintext only (internal linker); FTPS would need --linker external.

  BACKEND POSTURE: Net.Tcp/async.io pull in the inline-asm context leaf, so this
  runs on the NATIVE backend only. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TeFtpE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestFtpClientServer_RoundTrip;
  end;

implementation

const
  LE = #10;

  SrcFtp =
    '''
    program ftpe2e;
    uses SysUtils, Net.Tcp, Net.Ftp, Net.Ftp.Server, async.fibers,
      Generics.Collections;
    const
      PORT = 29651;
      BODY = 'alpha'#13#10'beta'#0'gamma'#13#10'omega';
    type
      TStore = class(IFtpFileStore)
        FData: string;
        FHave: Boolean;
        function Authenticate(const AUser: string; const APass: string): Boolean;
        function GetFile(const ARemotePath: string; out AData: string): Boolean;
        function PutFile(const ARemotePath: string; const AData: string): Boolean;
        function DeleteFile(const ARemotePath: string): Boolean;
        function List(const ADir: string): string;
      end;
    var
      GSrv: TFtpServer;
      GStore: IFtpFileStore;
      GStoreObj: TStore;
      GLoginOk: Boolean;
      GStorOk: Boolean;
      GRetrOk: Boolean;
      GRetr: string;
      GList: string;

    function TStore.Authenticate(const AUser: string; const APass: string): Boolean;
    begin
      Result := (AUser = 'bob') and (APass = 'pw');
    end;
    function TStore.GetFile(const ARemotePath: string; out AData: string): Boolean;
    begin
      if FHave then begin AData := FData; Result := True; end
      else begin AData := ''; Result := False; end;
    end;
    function TStore.PutFile(const ARemotePath: string; const AData: string): Boolean;
    begin
      FData := AData; FHave := True; Result := True;
    end;
    function TStore.DeleteFile(const ARemotePath: string): Boolean;
    begin
      Result := FHave; FHave := False;
    end;
    function TStore.List(const ADir: string): string;
    begin
      if FHave then Result := 'file.bin' else Result := '';
    end;

    procedure ServerFiber(AArg: Pointer);
    begin
      GSrv.Serve(GStore);
    end;

    procedure ClientFiber(AArg: Pointer);
    var
      Cli: TFtpClient;
    begin
      Cli := TFtpClient.Create();
      if Cli.Connect('127.0.0.1', PORT) then
      begin
        GLoginOk := Cli.Login('bob', 'pw');
        Cli.BinaryMode();
        GStorOk := Cli.Store('file.bin', BODY);
        GRetrOk := Cli.Retrieve('file.bin', GRetr);
        Cli.List('', GList);
        Cli.Quit();
      end;
      Cli.Free();
      GSrv.Stop();
    end;

    begin
      GLoginOk := False;
      GStorOk := False;
      GRetrOk := False;
      GRetr := '';
      GList := '';
      GStoreObj := TStore.Create();
      GStore := GStoreObj;
      GSrv := TFtpServer.Create(PORT);
      if not GSrv.Start() then begin WriteLn('STARTFAIL'); Halt(1); end;
      SpawnFiber(@ServerFiber, nil);
      SpawnFiber(@ClientFiber, nil);
      RunScheduler();
      GSrv.Free();
      if GLoginOk then WriteLn('LOGIN:ok');
      if GStorOk then WriteLn('STOR:ok');
      if GRetrOk then WriteLn('RETR:ok');
      if GRetr = BODY then WriteLn('BYTES:ok');
      if Pos('file.bin', GList) >= 0 then WriteLn('LIST:ok');
      WriteLn('DONE');
    end.
    ''';

procedure TeFtpE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-ftp')
end;

procedure TeFtpE2ETests.TestFtpClientServer_RoundTrip;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'ftpe2e', SrcFtp,
    'LOGIN:ok' + LE + 'STOR:ok' + LE + 'RETR:ok' + LE + 'BYTES:ok' + LE
    + 'LIST:ok' + LE + 'DONE' + LE, 0)
end;

initialization
  RegisterTest(TeFtpE2ETests);

end.
