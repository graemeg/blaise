{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Nntp;

// L5 NEWS wave: an NNTP CLIENT (RFC 3977 / classic RFC 977) over Net.Tcp.
// TNntpClient drives the classic news read/post session:
//
//   Connect(host, port)   read the 200/201 greeting (200 = posting allowed,
//                         201 = read-only)
//   ModeReader            MODE READER (switch a transit server to reader mode)
//   ListGroups            LIST (multi-line newsgroup listing)
//   SelectGroup(name)     GROUP <name> -> 211 <count> <first> <last> <name>
//   FetchArticle(n/id)    ARTICLE (multi-line: headers, blank line, body)
//   FetchHead / FetchBody HEAD / BODY (multi-line)
//   Next / Last           NEXT / LAST (move the current-article pointer)
//   Post(article)         POST -> 340, send the dot-stuffed article + CRLF.CRLF,
//                         240 on success
//   AuthUser / AuthPass   AUTHINFO USER / AUTHINFO PASS
//   Quit                  QUIT (205), close
//
// Status parsing: every response begins with a 3-digit status code.  2xx is
// success, 3xx wants continuation (POST body), 4xx/5xx are failures.  A data
// command's body is a sequence of lines terminated by a line that is just '.',
// with dot-stuffing ('..' at line start -> '.') undone by UnDotStuff.  Sending
// an article for POST dot-stuffs it and frames it with the terminating
// CRLF.CRLF (DotStuffBody from Net.Mail.Reply does exactly this, since NNTP,
// POP3 and SMTP share the dot-terminated multi-line shape).
//
// TLS: NNTPS (implicit TLS on port 563) is deferred (pulls in libssl ->
// --linker external).  AUTHINFO SASL / DNS are deferred too.  The plaintext
// client here links with the internal linker.
//
// NATIVE BACKEND ONLY (Net.Tcp -> async.io).

interface

uses
  SysUtils, Net.Tcp, Net.Mail.Reply, Generics.Collections;

type
  ENntpError = class(Exception);

  TNntpClient = class
  private
    FConn: TTcpConn;
    FLastLine: string;
    FLastCode: Int;
    FCanPost: Boolean;
    { Read the single status line; sets FLastLine and FLastCode.  Returns the
      3-digit status code (or -1 on connection error). }
    function ReadStatus: Int;
    { Read a multi-line body (after a positive status) until the lone '.',
      un-dot-stuffing each line.  Returns the body with LF-joined lines. }
    function ReadMultiline: string;
    function SendLine(const ALine: string): Boolean;
    { Send ACmd, read one status line, return the code. }
    function Command(const ACmd: string): Int;
  public
    constructor Create;
    destructor Destroy; override;

    { Dial a numeric host and read the 200/201 greeting.  True on 2xx. }
    function Connect(const AHostIp: string; APort: UInt16): Boolean;

    { Attach to an already-connected conn (used by tests / a TLS unit). }
    procedure Attach(AConn: TTcpConn);

    { MODE READER: switch a transit server into reader mode.  True on 2xx. }
    function ModeReader: Boolean;

    { AUTHINFO USER / PASS.  User returns True on 381 (need password); Pass
      returns True on 281 (accepted). }
    function AuthUser(const AName: string): Boolean;
    function AuthPass(const APass: string): Boolean;

    { LIST: returns each newsgroup line ('name last first flag') as a list
      element.  True on success. }
    function ListGroups(out AGroups: TList<string>): Boolean;

    { GROUP <name>: select a group.  On 211 sets ACount/AFirst/ALast and returns
      True; otherwise False (e.g. 411 no such group). }
    function SelectGroup(const AName: string; out ACount: Int;
      out AFirst: Int; out ALast: Int): Boolean;

    { ARTICLE / HEAD / BODY.  AWhich is the article number (as text) or a
      <message-id>; '' means the current article.  Returns the multi-line
      payload (dot-unstuffed) on 2xx. }
    function FetchArticle(const AWhich: string; out AArticle: string): Boolean;
    function FetchHead(const AWhich: string; out AHead: string): Boolean;
    function FetchBody(const AWhich: string; out ABody: string): Boolean;

    { NEXT / LAST: advance / retreat the current-article pointer.  True on 223. }
    function Next: Boolean;
    function Last: Boolean;

    { POST an article (full headers + blank line + body, LF or CRLF delimited).
      Sends POST, expects 340, sends the dot-stuffed article framed by
      CRLF.CRLF, expects 240.  True on success. }
    function Post(const AArticle: string): Boolean;

    function Quit: Boolean;

    { True when the greeting was 200 (posting allowed), False for 201. }
    property CanPost: Boolean read FCanPost;
    { The last status line / code received (for diagnostics). }
    property LastLine: string read FLastLine;
    property LastCode: Int read FLastCode;
    property Conn: TTcpConn read FConn write FConn;
  end;

implementation

{ Parse the leading run of ASCII digits in S (from offset AStart) into an
  integer.  Non-digit input yields 0. }
function ParseUIntAt(const S: string; AStart: Int): Int;
var
  I, Len, V: Int;
  B: Byte;
begin
  V := 0;
  Len := Length(S);
  I := AStart;
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

constructor TNntpClient.Create;
begin
  FConn := nil;
  FLastLine := '';
  FLastCode := -1;
  FCanPost := False;
end;

destructor TNntpClient.Destroy;
begin
  if FConn <> nil then
  begin
    FConn.Free();
    FConn := nil;
  end;
  inherited Destroy();
end;

function TNntpClient.ReadStatus: Int;
begin
  if not FConn.ReadLine(FLastLine) then
  begin
    FLastLine := '';
    FLastCode := -1;
    Exit(-1);
  end;
  if Length(FLastLine) < 3 then
  begin
    FLastCode := -1;
    Exit(-1);
  end;
  FLastCode := (Byte(FLastLine[0]) - 48) * 100
             + (Byte(FLastLine[1]) - 48) * 10
             + (Byte(FLastLine[2]) - 48);
  Result := FLastCode;
end;

function TNntpClient.ReadMultiline: string;
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

function TNntpClient.SendLine(const ALine: string): Boolean;
begin
  Result := FConn.Write(ALine + CRLF);
end;

function TNntpClient.Command(const ACmd: string): Int;
begin
  if not Self.SendLine(ACmd) then
    Exit(-1);
  Result := Self.ReadStatus();
end;

function TNntpClient.Connect(const AHostIp: string; APort: UInt16): Boolean;
var
  Cli: TTcpClient;
  C: TTcpConn;
  Code: Int;
begin
  Cli := TTcpClient.Create();
  C := Cli.Connect(AHostIp, APort);
  Cli.Free();
  if C = nil then
    Exit(False);
  FConn := C;
  Code := Self.ReadStatus();
  FCanPost := Code = 200;
  Result := (Code >= 200) and (Code < 300);
end;

procedure TNntpClient.Attach(AConn: TTcpConn);
begin
  FConn := AConn;
end;

function TNntpClient.ModeReader: Boolean;
var
  Code: Int;
begin
  Code := Self.Command('MODE READER');
  Result := (Code >= 200) and (Code < 300);
end;

function TNntpClient.AuthUser(const AName: string): Boolean;
begin
  Result := Self.Command('AUTHINFO USER ' + AName) = 381;
end;

function TNntpClient.AuthPass(const APass: string): Boolean;
begin
  Result := Self.Command('AUTHINFO PASS ' + APass) = 281;
end;

function TNntpClient.ListGroups(out AGroups: TList<string>): Boolean;
var
  Body: string;
  I, Len, Start: Int;
  Line: string;
begin
  AGroups := TList<string>.Create();
  if Self.Command('LIST') <> 215 then
    Exit(False);
  Body := Self.ReadMultiline();
  { split the LF-joined body into per-group lines }
  Len := Length(Body);
  Start := 0;
  I := 0;
  while I <= Len do
  begin
    if (I = Len) or (Byte(Body[I]) = 10) then
    begin
      Line := Copy(Body, Start, I - Start);
      if Line <> '' then
        AGroups.Add(Line);
      Start := I + 1;
      if I = Len then
        Break;
    end;
    I := I + 1;
  end;
  Result := True;
end;

function TNntpClient.SelectGroup(const AName: string; out ACount: Int;
  out AFirst: Int; out ALast: Int): Boolean;
var
  Code, I, Len: Int;
begin
  ACount := 0;
  AFirst := 0;
  ALast := 0;
  Code := Self.Command('GROUP ' + AName);
  if Code <> 211 then
    Exit(False);
  { FLastLine is '211 <count> <first> <last> <name>' - skip the code, then read
    three space-separated integers. }
  Len := Length(FLastLine);
  I := 3;
  { skip spaces }
  while (I < Len) and (Byte(FLastLine[I]) = 32) do
    I := I + 1;
  ACount := ParseUIntAt(FLastLine, I);
  { skip the count digits }
  while (I < Len) and (Byte(FLastLine[I]) <> 32) do
    I := I + 1;
  while (I < Len) and (Byte(FLastLine[I]) = 32) do
    I := I + 1;
  AFirst := ParseUIntAt(FLastLine, I);
  while (I < Len) and (Byte(FLastLine[I]) <> 32) do
    I := I + 1;
  while (I < Len) and (Byte(FLastLine[I]) = 32) do
    I := I + 1;
  ALast := ParseUIntAt(FLastLine, I);
  Result := True;
end;

function TNntpClient.FetchArticle(const AWhich: string;
  out AArticle: string): Boolean;
var
  Cmd: string;
  Code: Int;
begin
  AArticle := '';
  Cmd := 'ARTICLE';
  if AWhich <> '' then
    Cmd := Cmd + ' ' + AWhich;
  Code := Self.Command(Cmd);
  if (Code < 200) or (Code >= 300) then
    Exit(False);
  AArticle := Self.ReadMultiline();
  Result := True;
end;

function TNntpClient.FetchHead(const AWhich: string; out AHead: string): Boolean;
var
  Cmd: string;
  Code: Int;
begin
  AHead := '';
  Cmd := 'HEAD';
  if AWhich <> '' then
    Cmd := Cmd + ' ' + AWhich;
  Code := Self.Command(Cmd);
  if (Code < 200) or (Code >= 300) then
    Exit(False);
  AHead := Self.ReadMultiline();
  Result := True;
end;

function TNntpClient.FetchBody(const AWhich: string; out ABody: string): Boolean;
var
  Cmd: string;
  Code: Int;
begin
  ABody := '';
  Cmd := 'BODY';
  if AWhich <> '' then
    Cmd := Cmd + ' ' + AWhich;
  Code := Self.Command(Cmd);
  if (Code < 200) or (Code >= 300) then
    Exit(False);
  ABody := Self.ReadMultiline();
  Result := True;
end;

function TNntpClient.Next: Boolean;
begin
  Result := Self.Command('NEXT') = 223;
end;

function TNntpClient.Last: Boolean;
begin
  Result := Self.Command('LAST') = 223;
end;

function TNntpClient.Post(const AArticle: string): Boolean;
var
  Code: Int;
begin
  Code := Self.Command('POST');
  if Code <> 340 then
    Exit(False);
  { DotStuffBody dot-stuffs each line and appends the terminating CRLF.CRLF. }
  if not FConn.Write(DotStuffBody(AArticle)) then
    Exit(False);
  Code := Self.ReadStatus();
  Result := Code = 240;
end;

function TNntpClient.Quit: Boolean;
var
  Code: Int;
begin
  Code := Self.Command('QUIT');
  Result := (Code >= 200) and (Code < 300);
  if FConn <> nil then
    FConn.Close();
end;

end.
