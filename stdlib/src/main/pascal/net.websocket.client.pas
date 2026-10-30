{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - a fiber-native WebSocket client (RFC 6455).

  TWebSocketClient.Connect(url) parses a ws:// URL, dials the host over Net.Tcp,
  sends the HTTP GET upgrade with a fresh random Sec-WebSocket-Key, reads the
  101 response, and verifies the returned Sec-WebSocket-Accept equals the value
  computed from the key.  On success the connection is a live WebSocket.

  SendText / SendBinary send MASKED frames (RFC 6455 5.3 requires client frames
  to be masked).  ReadMessage reads a complete message, transparently answering
  PING with PONG, honouring CLOSE, and reassembling continuation fragments.
  Close sends a CLOSE frame.

  wss:// (TLS) is DEFERRED here: it requires Net.Tls, which forces the external
  linker, whereas this unit stays plaintext + internal-linker-friendly.  Connect
  returns False for a wss:// URL.  A future TLS variant can dial a TTlsStream in
  place of the TTcpConn and reuse the same framing.

  DNS is not performed — pass a numeric IPv4 host (Net.Tcp limitation).

  NATIVE BACKEND ONLY (Net.Tcp -> async.io -> async.fibers). }

unit Net.WebSocket.Client;

interface

uses
  SysUtils,
  Net.Tcp,
  Net.WebSockets;

type
  TWebSocketClient = class
  private
    FConn: TTcpConn;
    FBuf: string;           { unparsed bytes carried across reads }
    FConnected: Boolean;
    FClosed: Boolean;
    { Pull one complete frame off the socket, buffering partial reads. }
    function NextFrame: TWsFrame;
  public
    constructor Create;
    destructor Destroy; override;

    { Parse AUrl (ws://host:port/path), dial, and perform the upgrade handshake.
      Returns True on a validated 101 response.  wss:// is rejected (see unit
      header).  The host must be a numeric IPv4 address. }
    function Connect(const AUrl: string): Boolean;

    { Send a text/binary message as a single MASKED frame. }
    function SendText(const AData: string): Boolean;
    function SendBinary(const AData: string): Boolean;
    { Send a masked PING with an optional payload. }
    function SendPing(const AData: string): Boolean;

    { Read the next complete application message, answering PING with PONG and
      honouring a CLOSE (returns False).  Reassembles continuation frames.
      Returns True with the payload in AData (AIsBinary for binary); False on a
      clean close or EOF/error. }
    function ReadMessage(out AData: string; out AIsBinary: Boolean): Boolean;

    { Send a CLOSE frame and mark the connection closed. }
    procedure Close;

    property Connected: Boolean read FConnected;
    property Closed: Boolean read FClosed;
  end;

implementation

uses
  StrUtils,
  Net.Uri,
  Net.WebSockets,
  Uuid,
  Encoding.Base64,
  async.fibers;

const
  RECV_BUF = 8192;

{ A fresh Sec-WebSocket-Key: 16 random bytes, base64-encoded (RFC 6455 4.1). }
function NewClientKey: string;
begin
  Result := Base64Encode(TUuid.RandomUuid().ToBytes());
end;

constructor TWebSocketClient.Create;
begin
  FConn := nil;
  FBuf := '';
  FConnected := False;
  FClosed := False;
end;

destructor TWebSocketClient.Destroy;
begin
  if FConn <> nil then
  begin
    FConn.Close();
    FConn.Free();
    FConn := nil;
  end;
  inherited Destroy();
end;

function TWebSocketClient.Connect(const AUrl: string): Boolean;
var
  Uri: TUri;
  Host, Path, Key, Req, RespHead, Chunk, ExpectedAccept, HdrLower: string;
  Port, Colon: Int;
  I, LineStart, N: Int;
  Line: string;
  GotAccept: Boolean;
begin
  Result := False;
  Uri := TUri.Parse(AUrl);
  try
    if LowerCase(Uri.Scheme) = 'wss' then
      Exit;                        { TLS deferred; see unit header }
    if LowerCase(Uri.Scheme) <> 'ws' then
      Exit;
    Host := Uri.Host;
    if Host = '' then
      Exit;
    Port := Uri.Port;
    if Port <= 0 then
      Port := 80;                  { ws:// default }
    Path := Uri.Path;
    if Path = '' then
      Path := '/';

    FConn := TTcpClient.Create().Connect(Host, UInt16(Port));
    if FConn = nil then
      Exit;

    { Send the HTTP upgrade request. }
    Key := NewClientKey();
    Req := 'GET ' + Path + ' HTTP/1.1'#13#10 +
           'Host: ' + Host + ':' + IntToStr(Port) + #13#10 +
           'Upgrade: websocket'#13#10 +
           'Connection: Upgrade'#13#10 +
           'Sec-WebSocket-Key: ' + Key + #13#10 +
           'Sec-WebSocket-Version: 13'#13#10#13#10;
    if not FConn.Write(Req) then
      Exit;

    { Read the response head up to CRLFCRLF; keep any surplus bytes for the
      message stream. }
    FBuf := '';
    while PosEx(#13#10#13#10, FBuf, 0) < 0 do
    begin
      Chunk := FConn.Read(RECV_BUF);
      if Chunk = '' then
        Exit;                      { peer closed before completing handshake }
      FBuf := FBuf + Chunk;
    end;
    Colon := PosEx(#13#10#13#10, FBuf, 0);
    { Copy the head up to (but excluding) the terminating CRLFCRLF, then append a
      trailing CRLF so the LAST header line (e.g. Sec-WebSocket-Accept) is
      newline-terminated for the per-line scan below.  Without it the final line
      carries no LF and the scan silently skips it, so the accept check fails. }
    RespHead := Copy(FBuf, 0, Colon) + #13#10;
    { anything past the header terminator is WebSocket payload }
    FBuf := Copy(FBuf, Colon + 4, Length(FBuf) - Colon - 4);

    { First line must be a 101. }
    if PosEx('101', RespHead, 0) < 0 then
      Exit;

    { Validate Sec-WebSocket-Accept. }
    ExpectedAccept := WebSocketAccept(Key);
    GotAccept := False;
    LineStart := 0;
    N := Length(RespHead);
    for I := 0 to N - 1 do
    begin
      if Byte(RespHead[I]) = 10 then
      begin
        Line := Copy(RespHead, LineStart, I - LineStart);
        if (Length(Line) > 0) and (Byte(Line[Length(Line) - 1]) = 13) then
          Line := Copy(Line, 0, Length(Line) - 1);
        HdrLower := LowerCase(Line);
        if StartsStr('sec-websocket-accept:', HdrLower) then
        begin
          Colon := PosEx(':', Line, 0);
          if Trim(Copy(Line, Colon + 1, Length(Line) - Colon - 1)) = ExpectedAccept then
            GotAccept := True;
        end;
        LineStart := I + 1;
      end;
    end;
    if not GotAccept then
      Exit;

    FConnected := True;
    Result := True;
  finally
    Uri.Free();
  end;
end;

function TWebSocketClient.SendText(const AData: string): Boolean;
begin
  if FClosed or (not FConnected) then
    Exit(False);
  Result := FConn.Write(EncodeMaskedFrame(WS_OP_TEXT, AData));
end;

function TWebSocketClient.SendBinary(const AData: string): Boolean;
begin
  if FClosed or (not FConnected) then
    Exit(False);
  Result := FConn.Write(EncodeMaskedFrame(WS_OP_BINARY, AData));
end;

function TWebSocketClient.SendPing(const AData: string): Boolean;
begin
  if FClosed or (not FConnected) then
    Exit(False);
  Result := FConn.Write(EncodeMaskedFrame(WS_OP_PING, AData));
end;

function TWebSocketClient.NextFrame: TWsFrame;
var
  Frame: TWsFrame;
  Chunk: string;
begin
  while True do
  begin
    Frame := DecodeFrame(FBuf);
    if Frame.Valid then
    begin
      FBuf := Copy(FBuf, Frame.Consumed, Length(FBuf) - Frame.Consumed);
      Result := Frame;
      Exit;
    end;
    Chunk := FConn.Read(RECV_BUF);
    if Chunk = '' then
    begin
      Result.Valid := False;
      Result.Consumed := 0;
      Result.Payload := '';
      Exit;
    end;
    FBuf := FBuf + Chunk;
  end;
end;

function TWebSocketClient.ReadMessage(out AData: string; out AIsBinary: Boolean): Boolean;
var
  Frame: TWsFrame;
  Msg: string;
  MsgOpcode: Int;
  InMessage: Boolean;
begin
  AData := '';
  AIsBinary := False;
  Msg := '';
  MsgOpcode := WS_OP_TEXT;
  InMessage := False;
  while True do
  begin
    Frame := Self.NextFrame();
    if not Frame.Valid then
    begin
      Self.FClosed := True;
      Exit(False);
    end;

    if Frame.Opcode = WS_OP_PING then
    begin
      { answer with a masked PONG carrying the same payload }
      FConn.Write(EncodeMaskedFrame(WS_OP_PONG, Frame.Payload));
      Continue;
    end
    else if Frame.Opcode = WS_OP_PONG then
      Continue
    else if Frame.Opcode = WS_OP_CLOSE then
    begin
      if not Self.FClosed then
      begin
        FConn.Write(EncodeMaskedFrame(WS_OP_CLOSE, Frame.Payload));
        Self.FClosed := True;
      end;
      Exit(False);
    end
    else if Frame.Opcode = WS_OP_CONTINUATION then
      Msg := Msg + Frame.Payload
    else
    begin
      Msg := Frame.Payload;
      MsgOpcode := Frame.Opcode;
      InMessage := True;
    end;

    if InMessage and Frame.Fin then
    begin
      AData := Msg;
      AIsBinary := (MsgOpcode = WS_OP_BINARY);
      Exit(True);
    end;
  end;
end;

procedure TWebSocketClient.Close;
begin
  if FClosed or (FConn = nil) then
    Exit;
  FConn.Write(EncodeMaskedFrame(WS_OP_CLOSE, ''));
  FClosed := True;
end;

end.
