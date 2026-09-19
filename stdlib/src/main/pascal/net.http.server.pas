{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - a minimal single-threaded HTTP/1.1 server (no TLS).

  Connections are accepted and serviced one at a time.  A request is parsed
  into a THttpRequest; the application supplies an IRequestHandler whose Handle
  fills a THttpResponse.  Suitable for a local tool, an internal service, or a
  test fixture — not a high-concurrency front end.

  WebSocket upgrades are recognised automatically (cf. Net.WebSockets): when a
  request carries a Sec-WebSocket-Key the server completes the handshake, keeps
  the socket open, and tracks it.  Broadcast then pushes a text frame to every
  such socket — e.g. a live-reload or notification channel.

  The handler is passed as an interface PARAMETER (not stored as a field), to
  suit backends where an interface field called via Self is problematic. }

unit Net.Http.Server;

interface

uses
  Generics.Collections,
  Net.Tcp;

type
  { A parsed HTTP request.  Query parameters are decoded into a name->value
    map; the first value wins on a repeated key. }
  THttpRequest = class
  public
    Method: string;     { GET, POST, ... }
    Path:   string;     { decoded path, e.g. /fruit/apple.html }
    Query:  TOrderedDictionary<string, string>;
    RawHeaders: TList<string>;
    WebSocketKey: string;  { Sec-WebSocket-Key, '' if not an upgrade }
    constructor Create;
    destructor Destroy; override;
    function QueryParam(const AName: string): string;
    function IsWebSocketUpgrade: Boolean;
  end;

  { A response to send.  Body may be binary (treated as raw bytes). }
  THttpResponse = class
  public
    Status:      Integer;
    ContentType: string;
    Body:        string;
    constructor Create;
    procedure SetText(AStatus: Integer; const AContentType, ABody: string);
  end;

  { The application implements this; the server calls Handle per request. }
  IRequestHandler = interface
    procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
  end;

  THttpServer = class
  private
    FListenFd: Integer;
    FPort:     Integer;
    FRunning:  Boolean;
    { Connected WebSocket fds (upgraded connections kept open). }
    FWsClients: TList<Integer>;
    function ReadRequest(AConnFd: Integer): string;
    procedure SendResponse(AConnFd: Integer; AResp: THttpResponse);
    procedure DoWebSocketHandshake(AConnFd: Integer; const AKey: string);
    procedure ServeConn(AConnFd: Integer; AHandler: IRequestHandler);
  public
    constructor Create(APort: Integer);
    destructor Destroy; override;
    { Bind + listen on 127.0.0.1:Port.  Returns False on failure. }
    function Start: Boolean;
    { Bind + listen on all interfaces (INADDR_ANY):Port.

      Separately named rather than a default or an optional argument to Create:
      binding 0.0.0.0 makes the server reachable from other machines, so a
      caller has to ask for that exposure by name.  Start stays loopback-only. }
    function StartAny: Boolean;
    { Bind + listen on AAddr:Port — the shared path Start and StartAny use.
      Public so a caller that already has a specific interface address can bind
      it directly, as TTcpServer.StartOn allows. }
    function StartOn(AAddr: UInt32): Boolean;
    { Put the listen socket into non-blocking mode so PollOnce never blocks. }
    procedure SetNonBlocking;
    { Accept and service the next connection, dispatching to AHandler.
      Blocks until a connection arrives. }
    procedure ServeOnce(AHandler: IRequestHandler);
    { Non-blocking variant: if a connection is pending, service it and return
      True; otherwise return False immediately. }
    function PollOnce(AHandler: IRequestHandler): Boolean;
    { Push a WebSocket text frame to every connected upgrade socket.  Dead
      sockets are dropped.  Use this for live-reload / push channels. }
    procedure Broadcast(const APayload: string);
    property Port: Integer read FPort;
  end;

  { A fiber-per-connection HTTP/1.1 server (design [#components], the rewritten
    Net.Http.Server that supersedes the one-at-a-time THttpServer above).  The
    accept loop runs on the fiber scheduler (via Net.Tcp.TTcpServer) spawning ONE
    handler fiber per connection; each connection fiber loops reading requests
    and honours HTTP/1.1 keep-alive until the client closes or a request asks to
    close.  It REUSES ParseRequest / THttpRequest / THttpResponse /
    IRequestHandler, so the SAME application handler works on both this server
    and the baseline THttpServer.

    Drive it from inside a fiber under a scheduler: create it, then spawn a fiber
    that calls Serve(handler); stop it with Stop from another fiber.  For the
    multicore per-worker-listener path, pass AReusePort=True and run one server
    per worker on the same port.

    NATIVE BACKEND ONLY (pulls in Net.Tcp -> async.io -> async.fibers). }
  THttpFiberServer = class
  private
    FPort: Integer;
    FReusePort: Boolean;
    FServer: TTcpServer;       { ARC-owned; freed in Destroy }
    FMaxKeepAlive: Integer;    { max requests served per connection (0 = no cap) }
  public
    constructor Create(APort: Integer; AReusePort: Boolean = False);
    destructor Destroy; override;
    { Bind + listen on 127.0.0.1:Port.  Returns False on failure. }
    function Start: Boolean;
    { Bind + listen on all interfaces (INADDR_ANY):Port. }
    function StartAny: Boolean;
    { Run the accept loop, spawning a keep-alive handler fiber per connection.
      Returns when Stop is called.  Drive from inside a fiber. }
    procedure Serve(AHandler: IRequestHandler);
    { Stop the accept loop and close the listen socket. }
    procedure Stop;
    property Port: Integer read FPort;
    property MaxKeepAlive: Integer read FMaxKeepAlive write FMaxKeepAlive;
  end;

{ Parse a raw request head into a THttpRequest (caller owns the result). }
function ParseRequest(const ARaw: string): THttpRequest;

{ Percent-decode a URL component. }
function UrlDecode(const S: string): string;

implementation

uses
  SysUtils,
  StrUtils,
  Net.Sockets,
  Net.WebSockets,
  Net.Tcp,
  async.fibers;

const
  RECV_BUF = 8192;

{ ---- private string helpers ---- }

function StripTrailingCR(const S: string): string;
begin
  if (Length(S) > 0) and (Byte(S[Length(S) - 1]) = 13) then   { trailing CR }
    Result := Copy(S, 0, Length(S) - 1)
  else
    Result := S;
end;

{ Split S on LF, stripping a trailing CR from each line (so CRLF and LF both
  work).  Caller owns the returned list. }
function HttpSplitLines(const S: string): TList<string>;
var
  I, N, Start: Integer;
begin
  Result := TList<string>.Create();
  N := Length(S);
  Start := 0;
  I := 0;
  while I < N do
  begin
    if Byte(S[I]) = 10 then   { LF }
    begin
      Result.Add(StripTrailingCR(Copy(S, Start, I - Start)));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  Result.Add(StripTrailingCR(Copy(S, Start, N - Start)));
end;

{ Split S on a single delimiter byte.  Caller owns the returned list. }
function HttpSplitChar(const S: string; ADelim: Byte): TList<string>;
var
  I, N, Start: Integer;
begin
  Result := TList<string>.Create();
  N := Length(S);
  Start := 0;
  I := 0;
  while I < N do
  begin
    if Byte(S[I]) = ADelim then
    begin
      Result.Add(Copy(S, Start, I - Start));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  Result.Add(Copy(S, Start, N - Start));
end;

{ ---- THttpRequest ---- }

constructor THttpRequest.Create;
begin
  Method := '';
  Path := '';
  Query := TOrderedDictionary<string, string>.Create();
  RawHeaders := TList<string>.Create();
  WebSocketKey := '';
end;

destructor THttpRequest.Destroy;
begin
  Query.Free();
  RawHeaders.Free();
  inherited Destroy();
end;

function THttpRequest.QueryParam(const AName: string): string;
begin
  if not Query.TryGetValue(AName, Result) then
    Result := '';
end;

function THttpRequest.IsWebSocketUpgrade: Boolean;
begin
  Result := WebSocketKey <> '';
end;

{ ---- THttpResponse ---- }

constructor THttpResponse.Create;
begin
  Status := 200;
  ContentType := 'text/html; charset=utf-8';
  Body := '';
end;

procedure THttpResponse.SetText(AStatus: Integer; const AContentType, ABody: string);
begin
  Status := AStatus;
  ContentType := AContentType;
  Body := ABody;
end;

{ ---- parsing ---- }

function HexVal(AByte: Byte): Integer;
begin
  if (AByte >= 48) and (AByte <= 57) then Result := AByte - 48
  else if (AByte >= 65) and (AByte <= 70) then Result := AByte - 55
  else if (AByte >= 97) and (AByte <= 102) then Result := AByte - 87
  else Result := 0;
end;

function UrlDecode(const S: string): string;
var
  SB: TStringBuilder;
  I, N: Integer;
  B: Byte;
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  I := 0;
  while I < N do
  begin
    B := Byte(S[I]);
    if (B = 37) and (I + 2 < N) then   { '%' }
    begin
      SB.AppendByte(HexVal(Byte(S[I+1])) * 16 + HexVal(Byte(S[I+2])));
      I := I + 3;
    end
    else if B = 43 then                { '+' -> space }
    begin
      SB.AppendByte(32);
      I := I + 1;
    end
    else
    begin
      SB.AppendByte(B);
      I := I + 1;
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

procedure ParseQuery(const AQueryStr: string; ADest: TOrderedDictionary<string, string>);
var
  Pairs: TList<string>;
  I, Eq: Integer;
  Pair, Key, Val: string;
begin
  Pairs := HttpSplitChar(AQueryStr, 38);   { '&' }
  for I := 0 to Pairs.Count - 1 do
  begin
    Pair := Pairs.Get(I);
    if Pair = '' then
      Continue;
    Eq := PosEx('=', Pair, 0);
    if Eq < 0 then
    begin
      Key := UrlDecode(Pair);
      Val := '';
    end
    else
    begin
      Key := UrlDecode(Copy(Pair, 0, Eq));
      Val := UrlDecode(Copy(Pair, Eq + 1, Length(Pair) - Eq - 1));
    end;
    if not ADest.ContainsKey(Key) then
      ADest.Add(Key, Val);
  end;
  Pairs.Free();
end;

function ParseRequest(const ARaw: string): THttpRequest;
var
  Lines: TList<string>;
  ReqLine, Target, PathPart, QueryPart, Hdr, HdrLower: string;
  Parts: TList<string>;
  I, Q, Colon: Integer;
begin
  Result := THttpRequest.Create();
  Lines := HttpSplitLines(ARaw);
  if Lines.Count = 0 then
  begin
    Lines.Free();
    Exit;
  end;

  ReqLine := Lines.Get(0);
  Parts := HttpSplitChar(ReqLine, 32);   { space }
  if Parts.Count >= 2 then
  begin
    Result.Method := Parts.Get(0);
    Target := Parts.Get(1);
  end;
  Parts.Free();

  { Split target into path and query. }
  Q := PosEx('?', Target, 0);
  if Q < 0 then
  begin
    PathPart := Target;
    QueryPart := '';
  end
  else
  begin
    PathPart := Copy(Target, 0, Q);
    QueryPart := Copy(Target, Q + 1, Length(Target) - Q - 1);
  end;
  Result.Path := UrlDecode(PathPart);
  if QueryPart <> '' then
    ParseQuery(QueryPart, Result.Query);

  { Headers. }
  for I := 1 to Lines.Count - 1 do
  begin
    Hdr := Lines.Get(I);
    if Trim(Hdr) = '' then
      Break;
    Result.RawHeaders.Add(Hdr);
    HdrLower := LowerCase(Hdr);
    if StartsStr('sec-websocket-key:', HdrLower) then
    begin
      Colon := PosEx(':', Hdr, 0);
      Result.WebSocketKey := Trim(Copy(Hdr, Colon + 1, Length(Hdr) - Colon - 1));
    end;
  end;

  Lines.Free();
end;

{ ---- THttpServer ---- }

constructor THttpServer.Create(APort: Integer);
begin
  FPort := APort;
  FListenFd := -1;
  FRunning := False;
  FWsClients := TList<Integer>.Create();
end;

destructor THttpServer.Destroy;
begin
  if FListenFd >= 0 then
    Close(FListenFd);
  FWsClients.Free();
  inherited Destroy();
end;

function THttpServer.StartOn(AAddr: UInt32): Boolean;
begin
  { The one bind path; Start and StartAny differ only in the address they pass,
    so neither can drift from the other (this mirrors how TTcpServer factors
    Start / StartOn in net.tcp.pas). }
  FListenFd := TcpListen(AAddr, FPort, 64);
  Result := FListenFd >= 0;
  FRunning := Result;
end;

function THttpServer.Start: Boolean;
begin
  Result := Self.StartOn(INADDR_LOOPBACK);
end;

function THttpServer.StartAny: Boolean;
begin
  Result := Self.StartOn(INADDR_ANY);
end;

function THttpServer.ReadRequest(AConnFd: Integer): string;
var
  Chunk, Acc: string;
  SB: TStringBuilder;
begin
  { Read until the end of the header block (CRLFCRLF).  Request bodies are not
    surfaced by this server, so we stop at the head. }
  SB := TStringBuilder.Create();
  while True do
  begin
    Chunk := RecvString(AConnFd, RECV_BUF);
    if Chunk = '' then
      Break;
    SB.Append(Chunk);
    Acc := SB.ToString();
    if PosEx(#13#10#13#10, Acc, 0) >= 0 then
      Break;
    if Length(Acc) > 65536 then
      Break;   { guard against a runaway head }
  end;
  Result := SB.ToString();
  SB.Free();
end;

function StatusText(AStatus: Integer): string;
begin
  if AStatus = 200 then Result := 'OK'
  else if AStatus = 400 then Result := 'Bad Request'
  else if AStatus = 404 then Result := 'Not Found'
  else if AStatus = 500 then Result := 'Internal Server Error'
  else Result := 'OK';
end;

procedure THttpServer.SendResponse(AConnFd: Integer; AResp: THttpResponse);
var
  Head: string;
begin
  Head := 'HTTP/1.1 ' + IntToStr(AResp.Status) + ' ' + StatusText(AResp.Status) + #13#10 +
          'Content-Type: ' + AResp.ContentType + #13#10 +
          'Content-Length: ' + IntToStr(Length(AResp.Body)) + #13#10 +
          'Connection: close' + #13#10 +
          #13#10;
  SendAll(AConnFd, Head);
  if Length(AResp.Body) > 0 then
    SendAll(AConnFd, AResp.Body);
end;

procedure THttpServer.DoWebSocketHandshake(AConnFd: Integer; const AKey: string);
var
  Head: string;
begin
  Head := 'HTTP/1.1 101 Switching Protocols' + #13#10 +
          'Upgrade: websocket' + #13#10 +
          'Connection: Upgrade' + #13#10 +
          'Sec-WebSocket-Accept: ' + WebSocketAccept(AKey) + #13#10 +
          #13#10;
  SendAll(AConnFd, Head);
  { Keep the connection open and remember it for push frames.  The fd is left
    open deliberately (ServeConn does not close it in the websocket case). }
  FWsClients.Add(AConnFd);
end;

procedure THttpServer.SetNonBlocking;
begin
  if FListenFd >= 0 then
    MakeNonBlocking(FListenFd);
end;

procedure THttpServer.ServeConn(AConnFd: Integer; AHandler: IRequestHandler);
var
  Raw: string;
  Req: THttpRequest;
  Resp: THttpResponse;
begin
  Raw := ReadRequest(AConnFd);
  Req := ParseRequest(Raw);

  if Req.IsWebSocketUpgrade() then
  begin
    DoWebSocketHandshake(AConnFd, Req.WebSocketKey);
    { do NOT close AConnFd: it is now a live websocket }
    Req.Free();
    Exit;
  end;

  Resp := THttpResponse.Create();
  AHandler.Handle(Req, Resp);
  SendResponse(AConnFd, Resp);
  Resp.Free();
  Req.Free();
  Close(AConnFd);
end;

procedure THttpServer.ServeOnce(AHandler: IRequestHandler);
var
  ConnFd: Integer;
begin
  ConnFd := AcceptConn(FListenFd);
  if ConnFd < 0 then
    Exit;
  ServeConn(ConnFd, AHandler);
end;

function THttpServer.PollOnce(AHandler: IRequestHandler): Boolean;
var
  ConnFd: Integer;
begin
  ConnFd := AcceptConn(FListenFd);
  if ConnFd < 0 then
  begin
    Result := False;
    Exit;
  end;
  ServeConn(ConnFd, AHandler);
  Result := True;
end;

procedure THttpServer.Broadcast(const APayload: string);
var
  I, Fd: Integer;
  Dead: TList<Integer>;
  Frame: string;
begin
  Frame := EncodeTextFrame(APayload);
  Dead := TList<Integer>.Create();
  for I := 0 to FWsClients.Count - 1 do
  begin
    Fd := FWsClients.Get(I);
    if not SendAll(Fd, Frame) then
      Dead.Add(Fd);
  end;
  { drop sockets that failed to receive }
  for I := 0 to Dead.Count - 1 do
  begin
    Fd := Dead.Get(I);
    Close(Fd);
    FWsClients.Delete(FWsClients.IndexOf(Fd));
  end;
  Dead.Free();
end;

{ ---- THttpFiberServer (fiber-per-connection, keep-alive) ---- }

{ Read one request head (up to CRLFCRLF) from a fiber TCP connection.  Returns
  the raw head, or '' on EOF before any bytes (the keep-alive loop then ends). }
function FiberReadHead(AConn: TTcpConn): string;
var
  Chunk, Acc: string;
  SB: TStringBuilder;
begin
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
  Result := SB.ToString();
  SB.Free();
end;

{ True if the request's Connection header (or HTTP/1.1 default) keeps the
  connection alive. }
function WantsKeepAlive(AReq: THttpRequest): Boolean;
var
  I: Integer;
  H: string;
begin
  { HTTP/1.1 default is keep-alive unless "Connection: close" is present.  We
    do not distinguish 1.0 here (the load path is 1.1); treat "close" as the
    only opt-out. }
  Result := True;
  for I := 0 to AReq.RawHeaders.Count - 1 do
  begin
    H := LowerCase(AReq.RawHeaders.Get(I));
    if StartsStr('connection:', H) then
    begin
      if ContainsStr(H, 'close') then
        Result := False;
      Exit;
    end;
  end;
end;

{ Build the response head for a keep-alive connection.  AKeepAlive controls the
  Connection header. }
function FiberResponseHead(AResp: THttpResponse; AKeepAlive: Boolean): string;
var
  ConnHdr: string;
begin
  if AKeepAlive then
    ConnHdr := 'keep-alive'
  else
    ConnHdr := 'close';
  Result := 'HTTP/1.1 ' + IntToStr(AResp.Status) + ' ' +
              StatusText(AResp.Status) + #13#10 +
            'Content-Type: ' + AResp.ContentType + #13#10 +
            'Content-Length: ' + IntToStr(Length(AResp.Body)) + #13#10 +
            'Connection: ' + ConnHdr + #13#10 +
            #13#10;
end;

type
  { The IConnHandler the fiber TCP server runs per connection.  Loops over the
    persistent connection: read a request head, parse, dispatch to the app
    handler, write a keep-alive response, repeat until the client closes or a
    request opts out.  Reuses the exact THttpServer parse + response contract. }
  THttpKeepAliveHandler = class(IConnHandler)
  private
    FApp: IRequestHandler;
    FMaxKeepAlive: Integer;
  public
    constructor Create(AApp: IRequestHandler; AMaxKeepAlive: Integer);
    procedure Handle(AConn: TTcpConn);
  end;

constructor THttpKeepAliveHandler.Create(AApp: IRequestHandler; AMaxKeepAlive: Integer);
begin
  FApp := AApp;
  FMaxKeepAlive := AMaxKeepAlive;
end;

procedure THttpKeepAliveHandler.Handle(AConn: TTcpConn);
var
  Raw: string;
  Req: THttpRequest;
  Resp: THttpResponse;
  KeepAlive: Boolean;
  Served: Integer;
begin
  Served := 0;
  while True do
  begin
    Raw := FiberReadHead(AConn);
    if Raw = '' then
      Break;                       { connection closed by peer }
    Req := ParseRequest(Raw);
    KeepAlive := WantsKeepAlive(Req);
    if (FMaxKeepAlive > 0) and (Served + 1 >= FMaxKeepAlive) then
      KeepAlive := False;

    Resp := THttpResponse.Create();
    FApp.Handle(Req, Resp);
    AConn.Write(FiberResponseHead(Resp, KeepAlive));
    if Length(Resp.Body) > 0 then
      AConn.Write(Resp.Body);
    Resp.Free();
    Req.Free();

    Served := Served + 1;
    if not KeepAlive then
      Break;
  end;
  { The TCP server's connection trampoline closes+frees AConn after we return. }
end;

constructor THttpFiberServer.Create(APort: Integer; AReusePort: Boolean = False);
begin
  FPort := APort;
  FReusePort := AReusePort;
  FMaxKeepAlive := 0;
  FServer := TTcpServer.Create(UInt16(APort), AReusePort);
end;

destructor THttpFiberServer.Destroy;
begin
  FServer.Free();
  inherited Destroy();
end;

function THttpFiberServer.Start: Boolean;
begin
  Result := FServer.Start();
end;

function THttpFiberServer.StartAny: Boolean;
begin
  Result := FServer.StartOn(INADDR_ANY);
end;

procedure THttpFiberServer.Serve(AHandler: IRequestHandler);
var
  Conn: IConnHandler;
begin
  Conn := THttpKeepAliveHandler.Create(AHandler, FMaxKeepAlive);
  FServer.Serve(Conn);
end;

procedure THttpFiberServer.Stop;
begin
  FServer.Stop();
end;

end.
