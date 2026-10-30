{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - a fiber-per-connection WebSocket server (RFC 6455).

  Over Net.Tcp's TTcpServer: each accepted connection runs on its own fiber.
  The fiber reads the HTTP upgrade request, validates Upgrade/Connection/
  Sec-WebSocket-Key, answers 101 Switching Protocols with the computed
  Sec-WebSocket-Accept, then enters a message loop:

    * read bytes from the socket, buffering until DecodeFrame yields a complete
      frame (a frame may span several recvs — partial reads are reassembled);
    * TEXT / BINARY frames are handed to an application handler
      (IWebSocketHandler.OnMessage) via a TWebSocketConn;
    * PING frames are answered with a PONG carrying the same payload;
    * a CLOSE frame is echoed and the connection is shut down.

  Server->client frames are sent UNMASKED (EncodeFrame); client frames arrive
  masked and DecodeFrame unmasks them.  Message reassembly across continuation
  frames (FIN=False) is handled: a fragmented message is concatenated until the
  final fragment before dispatch.

  NATIVE BACKEND ONLY (Net.Tcp -> async.io -> async.fibers).

  Usage: create a TWebSocketServer(port), Start, then from inside a fiber under
  a scheduler call Serve(handler); stop it with Stop from another fiber. }

unit Net.WebSocket.Server;

interface

uses
  SysUtils,
  Net.Tcp,
  Net.WebSockets;

type
  TWebSocketConn = class;

  { The application implements this; the server calls OnMessage for each
    complete text/binary message.  AIsBinary distinguishes the two.  The handler
    typically replies via AConn.SendText / AConn.SendBinary, and may AConn.Close
    to end the session. }
  IWebSocketHandler = interface
    procedure OnMessage(AConn: TWebSocketConn; const AData: string; AIsBinary: Boolean);
  end;

  { A live server-side WebSocket connection.  Wraps a TTcpConn (owned by the
    connection fiber) and offers message-level send plus a blocking ReadMessage.
    Server frames are unmasked. }
  TWebSocketConn = class
  private
    FConn: TTcpConn;
    FBuf: string;         { unparsed bytes carried across reads }
    FClosed: Boolean;
    { Pull one complete frame off the socket, buffering partial reads.  Returns
      a Valid=False frame on EOF/error. }
    function NextFrame: TWsFrame;
  public
    { Take an already-upgraded TTcpConn (the caller keeps ownership; the conn
      fiber frees it after the handler returns). }
    constructor Create(AConn: TTcpConn);

    { Send a text message (single unmasked frame). }
    function SendText(const AData: string): Boolean;
    { Send a binary message (single unmasked frame). }
    function SendBinary(const AData: string): Boolean;
    { Send a PING with an optional payload. }
    function SendPing(const AData: string): Boolean;
    { Send a raw frame with an explicit opcode (unmasked). }
    function SendFrame(AOpcode: Int; const AData: string): Boolean;

    { Read the next complete application message, transparently answering PING
      with PONG and honouring a CLOSE (which returns False after echoing the
      close).  Reassembles continuation frames into one message.  Returns True
      and the payload in AData (AIsBinary set for binary messages); False on a
      clean close or EOF/error. }
    function ReadMessage(out AData: string; out AIsBinary: Boolean): Boolean;

    { Send a CLOSE frame and mark the connection closed. }
    procedure Close;

    property Closed: Boolean read FClosed;
  end;

  TWebSocketServer = class
  private
    FServer: TTcpServer;    { ARC-owned; freed in Destroy }
    FPort: Int;
  public
    constructor Create(APort: Int; AReusePort: Boolean = False);
    destructor Destroy; override;
    { Bind + listen on 127.0.0.1:Port.  Returns False on failure. }
    function Start: Boolean;
    { Run the accept loop, spawning a WebSocket handler fiber per connection.
      Returns when Stop is called.  Drive from inside a fiber under a scheduler. }
    procedure Serve(AHandler: IWebSocketHandler);
    { Stop the accept loop and close the listen socket. }
    procedure Stop;
    property Port: Int read FPort;
  end;

{ Perform the server side of the RFC 6455 handshake on an already-connected
  TTcpConn: read the HTTP upgrade head, and if it is a valid WebSocket upgrade
  respond 101 and return True (AConn is now a WebSocket).  Returns False (and
  sends a 400) if the request is not a valid upgrade. }
function WebSocketAcceptHandshake(AConn: TTcpConn): Boolean;

implementation

uses
  StrUtils,
  Net.Http.Server,
  async.fibers;

const
  RECV_BUF = 8192;

{ ---- handshake ---- }

function WebSocketAcceptHandshake(AConn: TTcpConn): Boolean;
var
  Chunk, Acc, Resp: string;
  SB: TStringBuilder;
  Req: THttpRequest;
begin
  Result := False;
  { Read the HTTP request head up to CRLFCRLF (or a runaway guard). }
  SB := TStringBuilder.Create();
  while True do
  begin
    Chunk := AConn.Read(RECV_BUF);
    if Chunk = '' then
      Break;                       { peer closed / error }
    SB.Append(Chunk);
    Acc := SB.ToString();
    if PosEx(#13#10#13#10, Acc, 0) >= 0 then
      Break;
    if PosEx(#10#10, Acc, 0) >= 0 then
      Break;
    if Length(Acc) > 65536 then
      Break;                       { runaway head guard }
  end;
  Acc := SB.ToString();
  SB.Free();
  if Acc = '' then
    Exit;

  { Any bytes read past the header block belong to the WebSocket stream and must
    be returned so the message loop sees them. }
  Req := ParseRequest(Acc);
  try
    if not Req.IsWebSocketUpgrade() then
    begin
      Resp := 'HTTP/1.1 400 Bad Request'#13#10 +
              'Connection: close'#13#10 +
              'Content-Length: 0'#13#10#13#10;
      AConn.Write(Resp);
      Exit;
    end;

    Resp := 'HTTP/1.1 101 Switching Protocols'#13#10 +
            'Upgrade: websocket'#13#10 +
            'Connection: Upgrade'#13#10 +
            'Sec-WebSocket-Accept: ' + WebSocketAccept(Req.WebSocketKey) +
              #13#10#13#10;
    Result := AConn.Write(Resp);
  finally
    Req.Free();
  end;
end;

{ ---- TWebSocketConn ---- }

constructor TWebSocketConn.Create(AConn: TTcpConn);
begin
  FConn := AConn;
  FBuf := '';
  FClosed := False;
end;

function TWebSocketConn.NextFrame: TWsFrame;
var
  Frame: TWsFrame;
  Chunk: string;
begin
  { Try to decode from what we already have, then read more until a complete
    frame arrives (partial-read reassembly). }
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

function TWebSocketConn.SendFrame(AOpcode: Int; const AData: string): Boolean;
begin
  if FClosed then
    Exit(False);
  Result := FConn.Write(EncodeFrame(AOpcode, AData));
end;

function TWebSocketConn.SendText(const AData: string): Boolean;
begin
  Result := Self.SendFrame(WS_OP_TEXT, AData);
end;

function TWebSocketConn.SendBinary(const AData: string): Boolean;
begin
  Result := Self.SendFrame(WS_OP_BINARY, AData);
end;

function TWebSocketConn.SendPing(const AData: string): Boolean;
begin
  Result := Self.SendFrame(WS_OP_PING, AData);
end;

function TWebSocketConn.ReadMessage(out AData: string; out AIsBinary: Boolean): Boolean;
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
      Exit(False);                 { EOF / error }
    end;

    if Frame.Opcode = WS_OP_PING then
    begin
      { answer with a PONG carrying the same payload; keep reading }
      Self.SendFrame(WS_OP_PONG, Frame.Payload);
      Continue;
    end
    else if Frame.Opcode = WS_OP_PONG then
      Continue                     { ignore unsolicited pongs }
    else if Frame.Opcode = WS_OP_CLOSE then
    begin
      { echo the close and end the session }
      if not Self.FClosed then
      begin
        Self.FConn.Write(EncodeFrame(WS_OP_CLOSE, Frame.Payload));
        Self.FClosed := True;
      end;
      Exit(False);
    end
    else if Frame.Opcode = WS_OP_CONTINUATION then
    begin
      { continuation of a fragmented message }
      Msg := Msg + Frame.Payload;
    end
    else
    begin
      { a fresh TEXT / BINARY frame starts a message }
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

procedure TWebSocketConn.Close;
begin
  if not FClosed then
  begin
    FConn.Write(EncodeFrame(WS_OP_CLOSE, ''));
    FClosed := True;
  end;
end;

{ ---- the per-connection handler bridging TTcpServer to IWebSocketHandler ---- }

type
  TWsConnHandler = class(IConnHandler)
  private
    FApp: IWebSocketHandler;
  public
    constructor Create(AApp: IWebSocketHandler);
    procedure Handle(AConn: TTcpConn);
  end;

constructor TWsConnHandler.Create(AApp: IWebSocketHandler);
begin
  FApp := AApp;
end;

procedure TWsConnHandler.Handle(AConn: TTcpConn);
var
  Ws: TWebSocketConn;
  Data: string;
  IsBinary: Boolean;
begin
  if not WebSocketAcceptHandshake(AConn) then
    Exit;                          { not a valid upgrade; TTcpServer closes AConn }
  Ws := TWebSocketConn.Create(AConn);
  try
    while Ws.ReadMessage(Data, IsBinary) do
      FApp.OnMessage(Ws, Data, IsBinary);
  finally
    Ws.Free();
  end;
end;

{ ---- TWebSocketServer ---- }

constructor TWebSocketServer.Create(APort: Int; AReusePort: Boolean = False);
begin
  FPort := APort;
  FServer := TTcpServer.Create(UInt16(APort), AReusePort);
end;

destructor TWebSocketServer.Destroy;
begin
  FServer.Free();
  inherited Destroy();
end;

function TWebSocketServer.Start: Boolean;
begin
  Result := FServer.Start();
end;

procedure TWebSocketServer.Serve(AHandler: IWebSocketHandler);
var
  Conn: IConnHandler;
begin
  Conn := TWsConnHandler.Create(AHandler);
  FServer.Serve(Conn);
end;

procedure TWebSocketServer.Stop;
begin
  FServer.Stop();
end;

end.
