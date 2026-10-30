{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Pop3;

// L5 MAIL wave: a POP3 CLIENT (RFC 1939) over Net.Tcp.  TPop3Client drives:
//
//   Connect(host, port)   read the '+OK' greeting
//   User / Pass           USER/PASS authentication
//   Stat                  message count + total size
//   List                  per-message sizes (multi-line)
//   Retr(n)               fetch message n (multi-line, dot-terminated,
//                         dot-UNstuffed)
//   Dele(n)               mark for deletion
//   Quit                  commit deletions, close
//
// Status parsing: a response line begins '+OK' (success) or '-ERR' (failure).
// A multi-line body follows certain commands and is terminated by a line that
// is just '.'; a body line whose first byte is '.' had a '.' prepended by the
// server (dot-stuffing) which Retr undoes.
//
// TLS: implicit TLS on port 995 (POP3S) and the STLS upgrade live in
// Net.Pop3.Tls (needs --linker external).  The plaintext client here links with
// the internal linker.
//
// NATIVE BACKEND ONLY (Net.Tcp -> async.io).

interface

uses
  SysUtils, Net.Tcp, Net.Mail.Reply;

type
  EPop3Error = class(Exception);

  TPop3Client = class
  private
    FConn: TTcpConn;
    FLastLine: string;
    { Read the single status line; sets FLastLine.  Returns True on '+OK'. }
    function ReadStatus: Boolean;
    { Read a multi-line body (after a positive status) until the lone '.',
      un-dot-stuffing each line.  Returns the body with LF-joined lines. }
    function ReadMultiline: string;
    function SendLine(const ALine: string): Boolean;
  public
    constructor Create;
    destructor Destroy; override;

    { Dial a numeric host and read the '+OK' greeting.  True on success. }
    function Connect(const AHostIp: string; APort: UInt16): Boolean;

    { Attach to an already-connected conn (used by the TLS unit / tests). }
    procedure Attach(AConn: TTcpConn);

    function User(const AName: string): Boolean;
    function Pass(const APass: string): Boolean;

    { STAT: sets ACount and ASize from the '+OK n size' status line. }
    function Stat(out ACount: Int; out ASize: Int): Boolean;

    { LIST: returns the raw multi-line listing ('n size' per line). }
    function List(out AListing: string): Boolean;

    { RETR n: returns the message (headers + body), dot-unstuffed. }
    function Retr(AMsg: Int; out AMessage: string): Boolean;

    function Dele(AMsg: Int): Boolean;
    function Quit: Boolean;

    { The last status line received (for diagnostics). }
    property LastLine: string read FLastLine;
    property Conn: TTcpConn read FConn write FConn;
  end;

implementation

{ Parse the leading run of ASCII digits in S into an integer.  Non-digit input
  yields 0 (POP3 status fields are always plain unsigned decimals). }
function ParseUInt(const S: string): Int;
var
  I, Len, V: Int;
  B: Byte;
begin
  V := 0;
  Len := Length(S);
  I := 0;
  while I < Len do
  begin
    B := Byte(S[I]);
    if (B < 48) or (B > 57) then
      Break;
    V := V * 10 + (B - 48);
    I := I + 1;
  end;
  Result := V;
end;

constructor TPop3Client.Create;
begin
  FConn := nil;
  FLastLine := '';
end;

destructor TPop3Client.Destroy;
begin
  if FConn <> nil then
  begin
    FConn.Free();
    FConn := nil;
  end;
  inherited Destroy();
end;

function TPop3Client.ReadStatus: Boolean;
begin
  if not FConn.ReadLine(FLastLine) then
  begin
    FLastLine := '';
    Exit(False);
  end;
  Result := (Length(FLastLine) >= 3) and (Copy(FLastLine, 0, 3) = '+OK');
end;

function TPop3Client.ReadMultiline: string;
var
  Line: string;
  R: string;
begin
  R := '';
  while FConn.ReadLine(Line) do
  begin
    if Line = '.' then
      Break;
    if R <> '' then
      R := R + #10;
    R := R + UnDotStuff(Line);
  end;
  Result := R;
end;

function TPop3Client.SendLine(const ALine: string): Boolean;
begin
  Result := FConn.Write(ALine + CRLF);
end;

function TPop3Client.Connect(const AHostIp: string; APort: UInt16): Boolean;
var
  Cli: TTcpClient;
  C: TTcpConn;
begin
  Cli := TTcpClient.Create();
  C := Cli.Connect(AHostIp, APort);
  Cli.Free();
  if C = nil then
    Exit(False);
  FConn := C;
  Result := Self.ReadStatus();
end;

procedure TPop3Client.Attach(AConn: TTcpConn);
begin
  FConn := AConn;
end;

function TPop3Client.User(const AName: string): Boolean;
begin
  if not Self.SendLine('USER ' + AName) then
    Exit(False);
  Result := Self.ReadStatus();
end;

function TPop3Client.Pass(const APass: string): Boolean;
begin
  if not Self.SendLine('PASS ' + APass) then
    Exit(False);
  Result := Self.ReadStatus();
end;

function TPop3Client.Stat(out ACount: Int; out ASize: Int): Boolean;
var
  Rest, NumStr: string;
  I, Len: Int;
begin
  ACount := 0;
  ASize := 0;
  if not Self.SendLine('STAT') then
    Exit(False);
  if not Self.ReadStatus() then
    Exit(False);
  { FLastLine is '+OK <count> <size>' }
  Rest := Copy(FLastLine, 4, Length(FLastLine) - 4);
  { skip leading spaces }
  Len := Length(Rest);
  I := 0;
  while (I < Len) and (Byte(Rest[I]) = 32) do
    I := I + 1;
  { first integer = count }
  NumStr := '';
  while (I < Len) and (Byte(Rest[I]) <> 32) do
  begin
    NumStr := NumStr + Copy(Rest, I, 1);
    I := I + 1;
  end;
  ACount := ParseUInt(NumStr);
  while (I < Len) and (Byte(Rest[I]) = 32) do
    I := I + 1;
  NumStr := '';
  while (I < Len) and (Byte(Rest[I]) <> 32) do
  begin
    NumStr := NumStr + Copy(Rest, I, 1);
    I := I + 1;
  end;
  ASize := ParseUInt(NumStr);
  Result := True;
end;

function TPop3Client.List(out AListing: string): Boolean;
begin
  AListing := '';
  if not Self.SendLine('LIST') then
    Exit(False);
  if not Self.ReadStatus() then
    Exit(False);
  AListing := Self.ReadMultiline();
  Result := True;
end;

function TPop3Client.Retr(AMsg: Int; out AMessage: string): Boolean;
begin
  AMessage := '';
  if not Self.SendLine('RETR ' + IntToStr(AMsg)) then
    Exit(False);
  if not Self.ReadStatus() then
    Exit(False);
  AMessage := Self.ReadMultiline();
  Result := True;
end;

function TPop3Client.Dele(AMsg: Int): Boolean;
begin
  if not Self.SendLine('DELE ' + IntToStr(AMsg)) then
    Exit(False);
  Result := Self.ReadStatus();
end;

function TPop3Client.Quit: Boolean;
begin
  if not Self.SendLine('QUIT') then
    Exit(False);
  Result := Self.ReadStatus();
  if FConn <> nil then
    FConn.Close();
end;

end.
