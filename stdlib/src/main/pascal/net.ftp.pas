{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Ftp;

// L5 FTP wave: an FTP CLIENT (RFC 959) over Net.Tcp.  FTP is a TWO-CONNECTION
// protocol: a persistent CONTROL connection carrying text commands and 3-digit
// reply codes (the same reply shape as SMTP - see Net.Mail.Reply.ReadSmtpReply),
// and a short-lived DATA connection per transfer.
//
// TFtpClient drives PASSIVE mode (the firewall-friendly one): for a transfer it
// sends PASV, parses the 227 reply's (h1,h2,h3,h4,p1,p2) tuple, dials a fresh
// data connection to h1.h2.h3.h4 : (p1*256+p2), then issues the transfer command
// (RETR/STOR/LIST/NLST) on the CONTROL connection, moves bytes over the DATA
// connection, and reads the 150 (transfer starting) and 226 (transfer complete)
// replies on the control connection.  ACTIVE mode (PORT) is deferred.
//
// Reply-code parsing reuses ReadSmtpReply: an FTP reply is a 3-digit code, a
// separator ('-' continues a multi-line reply, ' ' ends it), then text.  A
// multi-line reply "230-...\r\n...\r\n230 ok" ends on the "230 " line.
//
// Numeric IPv4 only (DNS deferred).  Plaintext links with the internal linker;
// FTPS (implicit 990 / explicit AUTH TLS) is deferred (would pull in libssl ->
// --linker external).
//
// NATIVE BACKEND ONLY (Net.Tcp -> async.io).

interface

uses
  SysUtils, Net.Tcp, Net.Mail.Reply;

type
  EFtpError = class(Exception);

  TFtpClient = class
  private
    FCtrl: TTcpConn;
    FLastCode: Int;
    FLastText: string;
    { Send a command line (CRLF-terminated) on the control connection. }
    function SendCmd(const ALine: string): Boolean;
    { Read one (possibly multi-line) control reply into FLastCode / FLastText. }
    function ReadReply: Boolean;
    { Send a command then read its reply.  True when the reply's first digit
      matches AExpectFirst (e.g. 2 for a 2xx success). }
    function Command(const ALine: string; AExpectFirst: Int): Boolean;
    { Issue PASV, parse the 227 tuple, dial the data connection.  Returns the
      connected data conn (caller owns it) or nil on failure. }
    function OpenPassiveData: TTcpConn;
    { Core of a download-style transfer (RETR / LIST / NLST): open PASV data,
      send ACmd on control, read 1xx on control, drain the data conn to EOF,
      read the completion 2xx on control.  Returns the received bytes. }
    function DownloadTransfer(const ACmd: string; out AData: string): Boolean;
  public
    constructor Create;
    destructor Destroy; override;

    { Dial a numeric host on APort (21 by default) and read the 220 greeting.
      True on success. }
    function Connect(const AHostIp: string; APort: UInt16): Boolean;

    { USER + PASS.  Handles the 331 (need password) then 230 (logged in) flow;
      also accepts a direct 230 to USER (no password required). }
    function Login(const AUser: string; const APass: string): Boolean;

    { TYPE I - switch to binary (image) transfer mode.  True on 200. }
    function BinaryMode: Boolean;

    { CWD - change working directory.  True on 250. }
    function Cwd(const ADir: string): Boolean;

    { PWD - print working directory.  Returns the path (from the 257 reply's
      quoted string) in APath.  True on 257. }
    function Pwd(out APath: string): Boolean;

    { NLST (bare names) over a PASV data conn.  Returns the raw listing. }
    function List(const ADir: string; out AListing: string): Boolean;

    { LIST (full ls-style listing) over a PASV data conn. }
    function ListDetailed(const ADir: string; out AListing: string): Boolean;

    { RETR - download ARemotePath into AData (exact bytes). }
    function Retrieve(const ARemotePath: string; out AData: string): Boolean;

    { STOR - upload AData to ARemotePath (exact bytes).  True when the server
      confirms with 226. }
    function Store(const ARemotePath: string; const AData: string): Boolean;

    { DELE - delete a remote file.  True on 250. }
    function Delete(const ARemotePath: string): Boolean;

    { QUIT - polite disconnect (221), then close the control connection. }
    function Quit: Boolean;

    { Attach to an already-connected control conn (used by tests / TLS). }
    procedure Attach(AConn: TTcpConn);

    property LastCode: Int read FLastCode;
    property LastText: string read FLastText;
    property Ctrl: TTcpConn read FCtrl;
  end;

implementation

uses
  Net.Sockets;

constructor TFtpClient.Create;
begin
  FCtrl := nil;
  FLastCode := -1;
  FLastText := '';
end;

destructor TFtpClient.Destroy;
begin
  if FCtrl <> nil then
  begin
    FCtrl.Free();
    FCtrl := nil;
  end;
  inherited Destroy();
end;

function TFtpClient.SendCmd(const ALine: string): Boolean;
begin
  if FCtrl = nil then
    Exit(False);
  Result := FCtrl.Write(ALine + CRLF);
end;

function TFtpClient.ReadReply: Boolean;
begin
  Result := ReadSmtpReply(FCtrl, FLastCode, FLastText);
end;

function TFtpClient.Command(const ALine: string; AExpectFirst: Int): Boolean;
begin
  if not Self.SendCmd(ALine) then
    Exit(False);
  if not Self.ReadReply() then
    Exit(False);
  Result := (FLastCode div 100) = AExpectFirst;
end;

function TFtpClient.Connect(const AHostIp: string; APort: UInt16): Boolean;
var
  Cli: TTcpClient;
  C: TTcpConn;
begin
  Cli := TTcpClient.Create();
  C := Cli.Connect(AHostIp, APort);
  Cli.Free();
  if C = nil then
    Exit(False);
  FCtrl := C;
  { greeting: 220 }
  if not Self.ReadReply() then
    Exit(False);
  Result := FLastCode = 220;
end;

procedure TFtpClient.Attach(AConn: TTcpConn);
begin
  FCtrl := AConn;
end;

function TFtpClient.Login(const AUser: string; const APass: string): Boolean;
begin
  if not Self.SendCmd('USER ' + AUser) then
    Exit(False);
  if not Self.ReadReply() then
    Exit(False);
  { 230 = logged in already (anonymous / no password).  331 = need password. }
  if FLastCode = 230 then
    Exit(True);
  if FLastCode <> 331 then
    Exit(False);
  if not Self.SendCmd('PASS ' + APass) then
    Exit(False);
  if not Self.ReadReply() then
    Exit(False);
  Result := FLastCode = 230;
end;

function TFtpClient.BinaryMode: Boolean;
begin
  Result := Self.Command('TYPE I', 2);
end;

function TFtpClient.Cwd(const ADir: string): Boolean;
begin
  if not Self.SendCmd('CWD ' + ADir) then
    Exit(False);
  if not Self.ReadReply() then
    Exit(False);
  Result := FLastCode = 250;
end;

function TFtpClient.Pwd(out APath: string): Boolean;
var
  I, Len, Q1, Q2: Int;
  B: Byte;
begin
  APath := '';
  if not Self.SendCmd('PWD') then
    Exit(False);
  if not Self.ReadReply() then
    Exit(False);
  if FLastCode <> 257 then
    Exit(False);
  { 257 "<path>" is current directory - extract the first double-quoted run. }
  Len := Length(FLastText);
  Q1 := -1;
  Q2 := -1;
  for I := 0 to Len - 1 do
  begin
    B := Byte(FLastText[I]);
    if B = 34 then
    begin
      if Q1 < 0 then
        Q1 := I
      else
      begin
        Q2 := I;
        Break;
      end;
    end;
  end;
  if (Q1 >= 0) and (Q2 > Q1) then
    APath := Copy(FLastText, Q1 + 1, Q2 - Q1 - 1)
  else
    APath := FLastText;
  Result := True;
end;

{ Parse the six comma-separated integers inside an FTP 227 reply text.  The 227
  line looks like "Entering Passive Mode (h1,h2,h3,h4,p1,p2)."; the numbers may
  also appear without the parentheses.  Returns True and fills AVals[0..5]. }
function ParsePasv(const AText: string; out AH1, AH2, AH3, AH4, AP1, AP2: Int): Boolean;
var
  Vals: array[0..5] of Int32;
  Idx, Cur, Digits, I, Len: Int;
  B: Byte;
  InNumbers: Boolean;
begin
  AH1 := 0; AH2 := 0; AH3 := 0; AH4 := 0; AP1 := 0; AP2 := 0;
  for I := 0 to 5 do
    Vals[I] := 0;
  Idx := 0;
  Cur := 0;
  Digits := 0;
  InNumbers := False;
  Len := Length(AText);
  I := 0;
  while I < Len do
  begin
    B := Byte(AText[I]);
    if (B >= 48) and (B <= 57) then
    begin
      Cur := Cur * 10 + (B - 48);
      Digits := Digits + 1;
      InNumbers := True;
    end
    else if B = 44 then                 { ',' separates the six values }
    begin
      if Idx <= 5 then
        Vals[Idx] := Cur;
      Idx := Idx + 1;
      Cur := 0;
      Digits := 0;
    end
    else
    begin
      { a non-digit, non-comma: if we were collecting the number run, this ends
        it (e.g. the ')' or '.').  Only stop once we have started the tuple. }
      if InNumbers and (Digits > 0) then
      begin
        if Idx <= 5 then
          Vals[Idx] := Cur;
        Idx := Idx + 1;
        Cur := 0;
        Digits := 0;
        if Idx > 5 then
          Break;
      end;
    end;
    I := I + 1;
  end;
  { flush a trailing number (no closing char after p2) }
  if (Digits > 0) and (Idx <= 5) then
  begin
    Vals[Idx] := Cur;
    Idx := Idx + 1;
  end;
  if Idx < 6 then
    Exit(False);
  AH1 := Vals[0]; AH2 := Vals[1]; AH3 := Vals[2]; AH4 := Vals[3];
  AP1 := Vals[4]; AP2 := Vals[5];
  Result := True;
end;

function TFtpClient.OpenPassiveData: TTcpConn;
var
  H1, H2, H3, H4, P1, P2, Port: Int;
  HostIp: string;
  Cli: TTcpClient;
begin
  Result := nil;
  if not Self.SendCmd('PASV') then
    Exit;
  if not Self.ReadReply() then
    Exit;
  if FLastCode <> 227 then
    Exit;
  if not ParsePasv(FLastText, H1, H2, H3, H4, P1, P2) then
    Exit;
  Port := P1 * 256 + P2;
  HostIp := IntToStr(H1) + '.' + IntToStr(H2) + '.' + IntToStr(H3) + '.' + IntToStr(H4);
  Cli := TTcpClient.Create();
  Result := Cli.Connect(HostIp, UInt16(Port));
  Cli.Free();
end;

function TFtpClient.DownloadTransfer(const ACmd: string; out AData: string): Boolean;
var
  Data: TTcpConn;
  Chunk: string;
begin
  AData := '';
  Data := Self.OpenPassiveData();
  if Data = nil then
    Exit(False);
  try
    { command on the control channel }
    if not Self.SendCmd(ACmd) then
      Exit(False);
    { 150 (or 125) transfer starting }
    if not Self.ReadReply() then
      Exit(False);
    if (FLastCode div 100) <> 1 then
      Exit(False);
    { drain the data connection to EOF }
    while True do
    begin
      Chunk := Data.Read(4096);
      if Chunk = '' then
        Break;
      AData := AData + Chunk;
    end;
    Data.Close();
  finally
    Data.Free();
  end;
  { 226 transfer complete }
  if not Self.ReadReply() then
    Exit(False);
  Result := (FLastCode div 100) = 2;
end;

function TFtpClient.List(const ADir: string; out AListing: string): Boolean;
var
  Cmd: string;
begin
  Cmd := 'NLST';
  if ADir <> '' then
    Cmd := Cmd + ' ' + ADir;
  Result := Self.DownloadTransfer(Cmd, AListing);
end;

function TFtpClient.ListDetailed(const ADir: string; out AListing: string): Boolean;
var
  Cmd: string;
begin
  Cmd := 'LIST';
  if ADir <> '' then
    Cmd := Cmd + ' ' + ADir;
  Result := Self.DownloadTransfer(Cmd, AListing);
end;

function TFtpClient.Retrieve(const ARemotePath: string; out AData: string): Boolean;
begin
  Result := Self.DownloadTransfer('RETR ' + ARemotePath, AData);
end;

function TFtpClient.Store(const ARemotePath: string; const AData: string): Boolean;
var
  Data: TTcpConn;
begin
  Data := Self.OpenPassiveData();
  if Data = nil then
    Exit(False);
  try
    if not Self.SendCmd('STOR ' + ARemotePath) then
      Exit(False);
    { 150 (or 125) transfer starting }
    if not Self.ReadReply() then
      Exit(False);
    if (FLastCode div 100) <> 1 then
      Exit(False);
    { push all bytes, then half-close so the server sees EOF }
    if not Data.Write(AData) then
      Exit(False);
    Data.Close();
  finally
    Data.Free();
  end;
  { 226 transfer complete }
  if not Self.ReadReply() then
    Exit(False);
  Result := (FLastCode div 100) = 2;
end;

function TFtpClient.Delete(const ARemotePath: string): Boolean;
begin
  if not Self.SendCmd('DELE ' + ARemotePath) then
    Exit(False);
  if not Self.ReadReply() then
    Exit(False);
  Result := FLastCode = 250;
end;

function TFtpClient.Quit: Boolean;
begin
  if not Self.SendCmd('QUIT') then
    Exit(False);
  Self.ReadReply();
  Result := FLastCode = 221;
  if FCtrl <> nil then
    FCtrl.Close();
end;

end.
