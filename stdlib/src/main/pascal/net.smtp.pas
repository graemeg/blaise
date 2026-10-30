{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Smtp;

// L5 MAIL wave: an SMTP CLIENT (RFC 5321) over Net.Tcp.  TSmtpClient drives the
// classic command/response dialogue:
//
//   Connect(host, port)        read the 220 greeting
//   Ehlo / Helo                announce ourselves, capture capabilities
//   AuthLogin / AuthPlain      base64-encoded SASL credentials
//   MailFrom / RcptTo / Data   the envelope + DATA payload (dot-stuffed,
//                              terminated by CRLF.CRLF)
//   Quit                       221, close
//
// SendMail is the convenience one-shot: connect, EHLO, optional AUTH, envelope,
// build the RFC 5322 headers + body, DATA, QUIT.
//
// TLS: the plaintext client links with the INTERNAL linker.  StartTls (RFC 3207)
// and implicit-TLS (SMTPS, port 465) live in Net.Smtp.Tls, which pulls in
// Net.Tls -> libssl and therefore needs --linker external.  Keeping the TLS
// upgrade in a separate unit lets a plaintext relay client stay libssl-free.
//
// NATIVE BACKEND ONLY (Net.Tcp -> async.io).

interface

uses
  SysUtils, Net.Tcp, Net.Mail.Reply, encoding.base64, Generics.Collections;

type
  ESmtpError = class(Exception);

  { A generic byte stream the client talks over: the plaintext path uses TTcpConn
    directly; the TLS path (Net.Smtp.Tls) supplies an adapter over TTlsStream.
    Only the line-oriented subset the protocol needs is required. }
  IMailStream = interface
    function WriteData(const AData: string): Boolean;
    function ReadLine(out ALine: string): Boolean;
    procedure CloseStream;
  end;

  { Adapter making a plaintext TTcpConn satisfy IMailStream. }
  TTcpMailStream = class(IMailStream)
  private
    FConn: TTcpConn;
    FOwns: Boolean;
  public
    constructor Create(AConn: TTcpConn; AOwns: Boolean);
    destructor Destroy; override;
    function WriteData(const AData: string): Boolean;
    function ReadLine(out ALine: string): Boolean;
    procedure CloseStream;
    property Conn: TTcpConn read FConn;
  end;

  { The SMTP client.  Holds the stream + the last reply code/text so callers can
    inspect failures.  Not thread-safe (one fiber per client). }
  TSmtpClient = class
  private
    FStream: IMailStream;
    FConn: TTcpConn;               { the raw plaintext conn, for the TLS unit }
    FLastCode: Int;
    FLastText: string;
    FCaps: TList<string>;
    function ReadReply: Boolean;
    function Command(const ALine: string): Boolean;
  public
    constructor Create;
    destructor Destroy; override;

    { Dial a numeric host and read the 220 greeting.  Returns True on 220. }
    function Connect(const AHostIp: string; APort: UInt16): Boolean;

    { Attach to an already-connected stream (used by the TLS unit after the
      handshake).  Does not read a greeting. }
    procedure Attach(AStream: IMailStream);

    { EHLO; captures the multi-line capabilities into Capabilities.  Falls back
      to nothing on failure (caller may then try Helo). }
    function Ehlo(const ADomain: string): Boolean;

    { HELO (no capabilities). }
    function Helo(const ADomain: string): Boolean;

    { AUTH LOGIN: base64(username) then base64(password). }
    function AuthLogin(const AUser, APass: string): Boolean;

    { AUTH PLAIN: a single base64(\0 user \0 pass) token. }
    function AuthPlain(const AUser, APass: string): Boolean;

    function MailFrom(const AAddr: string): Boolean;
    function RcptTo(const AAddr: string): Boolean;

    { DATA: sends the DATA command, then the dot-stuffed body + CRLF.CRLF.
      AMessage is the full RFC 5322 message (headers + blank line + body). }
    function Data(const AMessage: string): Boolean;

    function Quit: Boolean;

    { True if EHLO advertised ACap (case-insensitive, e.g. 'STARTTLS'). }
    function HasCapability(const ACap: string): Boolean;

    { One-shot: connect, EHLO, envelope, build message, DATA, QUIT.  No auth /
      no TLS — the plaintext convenience path.  Returns True if the server
      accepted the message (final DATA reply 250). }
    function SendMail(const AHostIp: string; APort: UInt16;
      const AFrom, ATo, ASubject, ABody: string): Boolean;

    property LastCode: Int read FLastCode;
    property LastText: string read FLastText;
    property Capabilities: TList<string> read FCaps;
    property Conn: TTcpConn read FConn;
    property Stream: IMailStream read FStream write FStream;
  end;

implementation

{ ---------------------------------------------------------------------------
  TTcpMailStream
  --------------------------------------------------------------------------- }

constructor TTcpMailStream.Create(AConn: TTcpConn; AOwns: Boolean);
begin
  FConn := AConn;
  FOwns := AOwns;
end;

destructor TTcpMailStream.Destroy;
begin
  if FOwns and (FConn <> nil) then
    FConn.Free();
  FConn := nil;
  inherited Destroy();
end;

function TTcpMailStream.WriteData(const AData: string): Boolean;
begin
  Result := FConn.Write(AData);
end;

function TTcpMailStream.ReadLine(out ALine: string): Boolean;
begin
  Result := FConn.ReadLine(ALine);
end;

procedure TTcpMailStream.CloseStream;
begin
  if FConn <> nil then
    FConn.Close();
end;

{ ---------------------------------------------------------------------------
  TSmtpClient
  --------------------------------------------------------------------------- }

constructor TSmtpClient.Create;
begin
  FStream := nil;
  FConn := nil;
  FLastCode := -1;
  FLastText := '';
  FCaps := TList<string>.Create();
end;

destructor TSmtpClient.Destroy;
begin
  FCaps.Free();
  FStream := nil;
  inherited Destroy();
end;

{ Read a (possibly multi-line) reply through the IMailStream.  We cannot reuse
  ReadSmtpReply directly because it takes a TTcpConn; instead we mirror the same
  continuation logic over the stream's ReadLine. }
function TSmtpClient.ReadReply: Boolean;
var
  Line: string;
  Sep: Byte;
begin
  FLastCode := -1;
  FLastText := '';
  while True do
  begin
    if not FStream.ReadLine(Line) then
      Exit(False);
    if Length(Line) < 3 then
      Exit(False);
    FLastCode := (Byte(Line[0]) - 48) * 100
               + (Byte(Line[1]) - 48) * 10
               + (Byte(Line[2]) - 48);
    if Length(Line) > 3 then
    begin
      if FLastText <> '' then
        FLastText := FLastText + #10;
      FLastText := FLastText + Copy(Line, 4, Length(Line) - 4);
      Sep := Byte(Line[3]);
    end
    else
      Sep := 32;
    if Sep <> 45 then
      Exit(True);
  end;
end;

function TSmtpClient.Command(const ALine: string): Boolean;
begin
  if not FStream.WriteData(ALine + CRLF) then
    Exit(False);
  Result := Self.ReadReply();
end;

function TSmtpClient.Connect(const AHostIp: string; APort: UInt16): Boolean;
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
  FStream := TTcpMailStream.Create(C, True);
  { greeting }
  Result := Self.ReadReply() and (FLastCode = 220);
end;

procedure TSmtpClient.Attach(AStream: IMailStream);
begin
  FStream := AStream;
end;

function TSmtpClient.Ehlo(const ADomain: string): Boolean;
var
  I, Start, Len: Int;
  Cap: string;
begin
  FCaps.Clear();
  if not Self.Command('EHLO ' + ADomain) then
    Exit(False);
  if FLastCode <> 250 then
    Exit(False);
  { FLastText is the capability block, each capability on its own LF-joined line;
    the first line is the greeting text (domain), the rest are capabilities. }
  Len := Length(FLastText);
  Start := 0;
  I := 0;
  while I <= Len do
  begin
    if (I = Len) or (Byte(FLastText[I]) = 10) then
    begin
      Cap := Copy(FLastText, Start, I - Start);
      if (Cap <> '') and (Start > 0) then
        FCaps.Add(Cap)
      else if (Cap <> '') and (Start = 0) then
        { first line is the greeting; skip }
        ;
      Start := I + 1;
      if I = Len then
        Break;
    end;
    I := I + 1;
  end;
  Result := True;
end;

function TSmtpClient.Helo(const ADomain: string): Boolean;
begin
  Result := Self.Command('HELO ' + ADomain) and (FLastCode = 250);
end;

function TSmtpClient.AuthLogin(const AUser, APass: string): Boolean;
begin
  if not Self.Command('AUTH LOGIN') then
    Exit(False);
  if FLastCode <> 334 then
    Exit(False);
  if not Self.Command(Base64Encode(AUser)) then
    Exit(False);
  if FLastCode <> 334 then
    Exit(False);
  Result := Self.Command(Base64Encode(APass)) and (FLastCode = 235);
end;

function TSmtpClient.AuthPlain(const AUser, APass: string): Boolean;
var
  Token: string;
begin
  { SASL PLAIN: authzid \0 authcid \0 passwd; authzid empty. }
  Token := #0 + AUser + #0 + APass;
  Result := Self.Command('AUTH PLAIN ' + Base64Encode(Token))
    and (FLastCode = 235);
end;

function TSmtpClient.MailFrom(const AAddr: string): Boolean;
begin
  Result := Self.Command('MAIL FROM:<' + AAddr + '>') and (FLastCode = 250);
end;

function TSmtpClient.RcptTo(const AAddr: string): Boolean;
begin
  Result := Self.Command('RCPT TO:<' + AAddr + '>')
    and ((FLastCode = 250) or (FLastCode = 251));
end;

function TSmtpClient.Data(const AMessage: string): Boolean;
begin
  if not Self.Command('DATA') then
    Exit(False);
  if FLastCode <> 354 then
    Exit(False);
  { dot-stuffed body + CRLF.CRLF terminator }
  if not FStream.WriteData(DotStuffBody(AMessage)) then
    Exit(False);
  Result := Self.ReadReply() and (FLastCode = 250);
end;

function TSmtpClient.Quit: Boolean;
begin
  Result := Self.Command('QUIT') and (FLastCode = 221);
  if FStream <> nil then
    FStream.CloseStream();
end;

function TSmtpClient.HasCapability(const ACap: string): Boolean;
var
  I: Int;
  Want, Have: string;
begin
  Want := UpperCase(ACap);
  for I := 0 to FCaps.Count - 1 do
  begin
    Have := UpperCase(FCaps[I]);
    { a capability line may carry parameters (e.g. 'AUTH LOGIN PLAIN'); match
      the leading token. }
    if Have = Want then
      Exit(True);
    if (Length(Have) > Length(Want))
      and (Copy(Have, 0, Length(Want)) = Want)
      and (Byte(Have[Length(Want)]) = 32) then
      Exit(True);
  end;
  Result := False;
end;

function TSmtpClient.SendMail(const AHostIp: string; APort: UInt16;
  const AFrom, ATo, ASubject, ABody: string): Boolean;
var
  Msg: string;
begin
  Result := False;
  if not Self.Connect(AHostIp, APort) then
    Exit;
  if not Self.Ehlo('localhost') then
    if not Self.Helo('localhost') then
      Exit;
  if not Self.MailFrom(AFrom) then
    Exit;
  if not Self.RcptTo(ATo) then
    Exit;
  Msg := 'From: ' + AFrom + CRLF
       + 'To: ' + ATo + CRLF
       + 'Subject: ' + ASubject + CRLF
       + CRLF
       + ABody;
  if not Self.Data(Msg) then
    Exit;
  Self.Quit();
  Result := True;
end;

end.
