{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for L5 Net.Ftp (FTP client, RFC 959).  A MOCK FTP server runs as a fiber
  on Net.Tcp inside the test-runner process.  It speaks the two-connection FTP
  protocol:

    220 greeting, 331/230 for USER/PASS, 200 to TYPE I, and PASSIVE transfers:
    on PASV it opens a data listener on a fixed ephemeral port, replies 227 with
    that ip,port tuple, then for RETR serves a known file body over the data
    connection (150 start / 226 complete on control), for STOR accepts an upload
    to EOF, and for NLST serves a fixed listing.

  The client-driving fiber asserts login, a RETR round-trips the exact bytes, a
  STOR delivers the exact bytes to the mock, and NLST returns the entries.
  Plaintext (internal linker).  NATIVE BACKEND ONLY.

  Self-registers via the initialization section. }

unit Ftp.Tests;

interface

uses
  blaise.testing, SysUtils, Net.Tcp, Net.Ftp, Net.Ftp.Server, Net.Mail.Reply,
  async.fibers, async.io, Net.Sockets, Generics.Collections;

type
  TFtpClientTests = class(TTestCase)
  published
    procedure TestLoginRetrStorList;
  end;

  { Client <-> real TFtpServer round-trip. }
  TFtpServerTests = class(TTestCase)
  published
    procedure TestClientServerRoundTrip;
  end;

implementation

const
  CTRL_PORT = 29631;
  DATA_PORT = 29632;
  { The file the mock serves for RETR (includes CRLF + a NUL to prove the
    transfer is byte-exact and binary-clean). }
  RETR_BODY = 'line one' + #13#10 + 'binary' + #0 + 'byte' + #13#10 + 'end';

var
  GServer: TTcpServer;
  GHandler: IConnHandler;
  { results captured by the client fiber }
  GLoginOk: Boolean;
  GBinaryOk: Boolean;
  GRetr: string;
  GRetrOk: Boolean;
  GStorOk: Boolean;
  GList: string;
  GListOk: Boolean;
  GQuitOk: Boolean;
  { what the mock received via STOR }
  GStored: string;

type
  TMockFtpHandler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

{ On PASV: open a data listener on DATA_PORT, reply 227 with its ip,port, accept
  the client's data connection and return it (caller owns / closes it).  Returns
  nil on failure. }
function OpenDataConn(AConn: TTcpConn): TTcpConn;
var
  ListenFd, DataFd: Int;
begin
  Result := nil;
  ListenFd := TcpListenLocal(DATA_PORT, 8);
  if ListenFd < 0 then
    Exit;
  SetNonBlocking(ListenFd);
  { 227 Entering Passive Mode (127,0,0,1,p1,p2) }
  AConn.Write('227 Entering Passive Mode (127,0,0,1,'
    + IntToStr(DATA_PORT div 256) + ',' + IntToStr(DATA_PORT mod 256) + ').' + CRLF);
  DataFd := FiberAccept(ListenFd);
  CloseSocket(ListenFd);
  if DataFd < 0 then
    Exit;
  Result := TTcpConn.Create(DataFd);
end;

procedure TMockFtpHandler.Handle(AConn: TTcpConn);
var
  Line, U: string;
  Data: TTcpConn;
  Chunk: string;
begin
  AConn.Write('220 mock FTP ready' + CRLF);
  { the data connection opened by the most recent PASV, pending a transfer }
  Data := nil;
  while AConn.ReadLine(Line) do
  begin
    U := UpperCase(Line);
    if Copy(U, 0, 4) = 'USER' then
      AConn.Write('331 need password' + CRLF)
    else if Copy(U, 0, 4) = 'PASS' then
      AConn.Write('230 logged in' + CRLF)
    else if Copy(U, 0, 4) = 'TYPE' then
      AConn.Write('200 type set' + CRLF)
    else if U = 'PASV' then
      { the 227 reply and data-conn accept happen inside OpenDataConn }
      Data := OpenDataConn(AConn)
    else if Copy(U, 0, 4) = 'RETR' then
    begin
      if Data = nil then
        AConn.Write('425 no data connection' + CRLF)
      else
      begin
        AConn.Write('150 opening data connection' + CRLF);
        Data.Write(RETR_BODY);
        Data.Close();
        Data.Free();
        Data := nil;
        AConn.Write('226 transfer complete' + CRLF);
      end;
    end
    else if Copy(U, 0, 4) = 'STOR' then
    begin
      if Data = nil then
        AConn.Write('425 no data connection' + CRLF)
      else
      begin
        AConn.Write('150 opening data connection' + CRLF);
        GStored := '';
        while True do
        begin
          Chunk := Data.Read(4096);
          if Chunk = '' then
            Break;
          GStored := GStored + Chunk;
        end;
        Data.Close();
        Data.Free();
        Data := nil;
        AConn.Write('226 transfer complete' + CRLF);
      end;
    end
    else if Copy(U, 0, 4) = 'NLST' then
    begin
      if Data = nil then
        AConn.Write('425 no data connection' + CRLF)
      else
      begin
        AConn.Write('150 here comes the listing' + CRLF);
        Data.Write('hello.bin' + CRLF + 'upload.bin' + CRLF);
        Data.Close();
        Data.Free();
        Data := nil;
        AConn.Write('226 listing complete' + CRLF);
      end;
    end
    else if U = 'QUIT' then
    begin
      AConn.Write('221 bye' + CRLF);
      Break;
    end
    else
      AConn.Write('500 unknown' + CRLF);
  end;
  if Data <> nil then
  begin
    Data.Close();
    Data.Free();
  end;
end;

procedure ServerFiber(AArg: Pointer);
begin
  GServer.Serve(GHandler);
end;

procedure ClientFiber(AArg: Pointer);
var
  Cli: TFtpClient;
begin
  FiberSleep(2);
  Cli := TFtpClient.Create();
  if Cli.Connect('127.0.0.1', CTRL_PORT) then
  begin
    GLoginOk := Cli.Login('alice', 'secret');
    GBinaryOk := Cli.BinaryMode();
    GRetrOk := Cli.Retrieve('hello.bin', GRetr);
    GStorOk := Cli.Store('upload.bin', RETR_BODY);
    GListOk := Cli.List('', GList);
    GQuitOk := Cli.Quit();
  end;
  Cli.Free();
  GServer.Stop();
end;

procedure TFtpClientTests.TestLoginRetrStorList;
begin
  GServer := TTcpServer.Create(CTRL_PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TMockFtpHandler.Create();
  GLoginOk := False;
  GBinaryOk := False;
  GRetr := '';
  GRetrOk := False;
  GStorOk := False;
  GList := '';
  GListOk := False;
  GQuitOk := False;
  GStored := '';

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@ClientFiber, nil);
  RunScheduler();

  AssertTrue('login', GLoginOk);
  AssertTrue('binary mode', GBinaryOk);
  AssertTrue('RETR ok', GRetrOk);
  AssertEquals('RETR byte-exact', RETR_BODY, GRetr);
  AssertTrue('STOR ok', GStorOk);
  AssertEquals('STOR byte-exact at server', RETR_BODY, GStored);
  AssertTrue('LIST ok', GListOk);
  AssertTrue('LIST has entry', Pos('hello.bin', GList) >= 0);
  AssertTrue('QUIT', GQuitOk);

  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

{ ---------------------------------------------------------------------------
  Client <-> real TFtpServer round-trip
  --------------------------------------------------------------------------- }

const
  SRV_PORT = 29641;
  STORE_BODY = 'roundtrip' + #13#10 + 'with' + #0 + 'nul' + #13#10 + 'tail';

type
  { A simple in-memory virtual filesystem backing the FTP server. }
  TMemStore = class(IFtpFileStore)
  private
    FFiles: TOrderedDictionary<string, string>;
  public
    constructor Create;
    destructor Destroy; override;
    function Authenticate(const AUser: string; const APass: string): Boolean;
    function GetFile(const ARemotePath: string; out AData: string): Boolean;
    function PutFile(const ARemotePath: string; const AData: string): Boolean;
    function DeleteFile(const ARemotePath: string): Boolean;
    function List(const ADir: string): string;
  end;

constructor TMemStore.Create;
begin
  FFiles := TOrderedDictionary<string, string>.Create();
end;

destructor TMemStore.Destroy;
begin
  FFiles.Free();
  inherited Destroy();
end;

function TMemStore.Authenticate(const AUser: string; const APass: string): Boolean;
begin
  Result := (AUser = 'bob') and (APass = 'pw');
end;

function TMemStore.GetFile(const ARemotePath: string; out AData: string): Boolean;
var
  V: string;
begin
  Result := FFiles.TryGetValue(ARemotePath, V);
  if Result then
    AData := V
  else
    AData := '';
end;

function TMemStore.PutFile(const ARemotePath: string; const AData: string): Boolean;
begin
  FFiles[ARemotePath] := AData;
  Result := True;
end;

function TMemStore.DeleteFile(const ARemotePath: string): Boolean;
begin
  Result := FFiles.ContainsKey(ARemotePath);
  if Result then
    FFiles.Remove(ARemotePath);
end;

function TMemStore.List(const ADir: string): string;
var
  I: Int;
  R: string;
begin
  R := '';
  for I := 0 to FFiles.Count - 1 do
  begin
    if R <> '' then
      R := R + #10;
    R := R + FFiles.Keys[I];
  end;
  Result := R;
end;

var
  GSrv: TFtpServer;
  GStore: IFtpFileStore;
  GRtLoginOk: Boolean;
  GRtStorOk: Boolean;
  GRtRetr: string;
  GRtRetrOk: Boolean;
  GRtList: string;
  GRtListOk: Boolean;
  GRtDeleteOk: Boolean;
  GRtQuitOk: Boolean;

procedure SrvServeFiber(AArg: Pointer);
begin
  GSrv.Serve(GStore);
end;

procedure RtClientFiber(AArg: Pointer);
var
  Cli: TFtpClient;
begin
  FiberSleep(2);
  Cli := TFtpClient.Create();
  if Cli.Connect('127.0.0.1', SRV_PORT) then
  begin
    GRtLoginOk := Cli.Login('bob', 'pw');
    GRtStorOk := Cli.Store('file.bin', STORE_BODY);
    GRtRetrOk := Cli.Retrieve('file.bin', GRtRetr);
    GRtListOk := Cli.List('', GRtList);
    GRtDeleteOk := Cli.Delete('file.bin');
    GRtQuitOk := Cli.Quit();
  end;
  Cli.Free();
  GSrv.Stop();
end;

procedure TFtpServerTests.TestClientServerRoundTrip;
begin
  GSrv := TFtpServer.Create(SRV_PORT);
  AssertTrue('server start', GSrv.Start());
  GStore := TMemStore.Create();
  GRtLoginOk := False;
  GRtStorOk := False;
  GRtRetr := '';
  GRtRetrOk := False;
  GRtList := '';
  GRtListOk := False;
  GRtDeleteOk := False;
  GRtQuitOk := False;

  SpawnFiber(@SrvServeFiber, nil);
  SpawnFiber(@RtClientFiber, nil);
  RunScheduler();

  AssertTrue('login', GRtLoginOk);
  AssertTrue('STOR ok', GRtStorOk);
  AssertTrue('RETR ok', GRtRetrOk);
  AssertEquals('round-trip byte-exact', STORE_BODY, GRtRetr);
  AssertTrue('LIST ok', GRtListOk);
  AssertTrue('LIST shows uploaded file', Pos('file.bin', GRtList) >= 0);
  AssertTrue('DELETE ok', GRtDeleteOk);
  AssertTrue('QUIT', GRtQuitOk);

  ResetScheduler();
  GSrv.Free();
  GStore := nil;
end;

initialization
  RegisterTest(TFtpClientTests);
  RegisterTest(TFtpServerTests);

end.
