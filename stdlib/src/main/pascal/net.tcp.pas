{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Tcp;

// L5 of the fiber runtime (docs/async-networking-design.adoc, [#components]):
// a fiber-native TCP layer over L3 (async.io).  TTcpConn wraps a connected fd
// and exposes ordinary synchronous-looking Read/Write/ReadLine/Close; under a
// running scheduler each call parks the fiber and resumes it on readiness (via
// FiberRecv/FiberSend), so a handler written as straight-line blocking code
// serves at high concurrency.  With NO scheduler running the L3 primitives fall
// back to true blocking calls, so the same code works in a plain program.
//
// TTcpClient.Connect dials a numeric IPv4 address (DNS is deferred — a getaddr-
// info offload is a pinning hazard called out in the design).  TTcpServer runs
// an accept loop that spawns ONE FIBER PER CONNECTION running a supplied
// handler, the whole point of the C10k/C100k design.
//
// NATIVE BACKEND ONLY (async.io -> async.fibers pull in the inline-asm context
// leaf; the QBE backend rejects it).  Linux epoll for now.

interface

uses
  SysUtils, async.fibers, Net.Sockets;

type
  { A connected TCP stream.  Owns the fd: Close (or Free) shuts it down.
    Read/Write are the fiber-parking equivalents of recv/send; ReadLine
    accumulates until an LF (the trailing CR, if any, is stripped). }
  TTcpConn = class
  private
    FFd: Integer;
    FClosed: Boolean;
    FPending: string;      { bytes read past a line boundary in ReadLine }
  public
    { Take ownership of an already-connected fd (set non-blocking here). }
    constructor Create(AFd: Integer);
    destructor Destroy; override;

    { Read up to AMaxBytes into a fresh string.  Returns the bytes read; ''
      means the peer closed (EOF) or an error occurred (see Closed).  A short
      read is normal for a stream — callers wanting a fixed amount must loop
      (or use ReadFull). }
    function Read(AMaxBytes: Integer): string;

    { Read exactly ACount bytes (looping over short reads).  Returns fewer than
      ACount only on EOF/error.  Returns '' for ACount <= 0. }
    function ReadFull(ACount: Integer): string;

    { Write the whole string, looping over short writes.  Returns True when
      every byte was accepted, False on peer close / error. }
    function Write(const AData: string): Boolean;

    { Read one line terminated by LF (CRLF and bare LF both work; the line
      returned excludes the terminator).  Returns True and the line in ALine;
      False on EOF before any terminator (ALine then holds whatever partial
      bytes arrived).  Buffers over-read bytes for the next call. }
    function ReadLine(out ALine: string): Boolean;

    { Push AData back to the front of the read buffer so the next Read/ReadFull/
      ReadLine sees it first.  Used by higher layers (e.g. Net.Http.Client) that
      over-read past a framing boundary and must return the surplus bytes to the
      stream. }
    procedure Unread(const AData: string);

    { Close the underlying fd (idempotent). }
    procedure Close;

    property Fd: Integer read FFd;
    property Closed: Boolean read FClosed;
  end;

  { Dials outbound TCP connections. }
  TTcpClient = class
  public
    { Connect to a numeric dotted-quad AHostIp (e.g. '127.0.0.1') on APort.
      Returns a connected TTcpConn (caller owns it) or nil on failure.  DNS is
      NOT performed — pass a literal IPv4 address. }
    function Connect(const AHostIp: string; APort: UInt16): TTcpConn;
  end;

  { The application supplies this; the server spawns one fiber per accepted
    connection and calls Handle(conn) on it.  The handler owns the connection
    for its lifetime and should Close (or Free) it when done. }
  IConnHandler = interface
    procedure Handle(AConn: TTcpConn);
  end;

  { A fiber-per-connection TCP server.  Start binds+listens; Serve runs the
    accept loop (spawning a handler fiber per connection) until Stop is called
    or the listen socket errors.  Serve MUST be driven from inside a fiber
    (it uses FiberAccept, which parks the calling fiber). }
  TTcpServer = class
  private
    FListenFd: Integer;
    FPort: UInt16;
    FAddr: UInt32;
    FRunning: Boolean;
    FReusePort: Boolean;
    FHandler: IConnHandler;    { the live ref that outlives every connection fiber }
  public
    { APort to listen on; AReusePort opens the socket with SO_REUSEPORT so
      several workers may each run their own TTcpServer on the same port. }
    constructor Create(APort: UInt16; AReusePort: Boolean = False);
    destructor Destroy; override;

    { Bind + listen on 127.0.0.1:APort.  Returns False on failure. }
    function Start: Boolean;

    { Bind + listen on AAddr (network-order IPv4, e.g. INADDR_ANY):APort. }
    function StartOn(AAddr: UInt32): Boolean;

    { Accept loop: for each connection spawn a fiber running AHandler.Handle on
      a fresh TTcpConn.  Returns when Stop is called (or on a fatal accept
      error).  Drive from inside a fiber under a scheduler. }
    procedure Serve(AHandler: IConnHandler);

    { Ask Serve to stop and close the listen socket; the next accept unblocks
      and Serve returns.  Safe to call from another fiber. }
    procedure Stop;

    property Port: UInt16 read FPort;
    property ListenFd: Integer read FListenFd;
    property Running: Boolean read FRunning;
  end;

implementation

uses
  async.io;

const
  { Accept-loop poll interval (ms).  The accept fiber parks for at most this
    long between re-checks of FRunning, so Stop takes effect within one
    interval.  Small enough to feel instant, large enough that an idle server
    never busy-loops. }
  ACCEPT_POLL_MS = 50;

{ ---------------------------------------------------------------------------
  TTcpConn
  --------------------------------------------------------------------------- }

constructor TTcpConn.Create(AFd: Integer);
begin
  FFd := AFd;
  FClosed := AFd < 0;
  FPending := '';
  if AFd >= 0 then
    SetNonBlocking(AFd);
end;

destructor TTcpConn.Destroy;
begin
  Self.Close();
  inherited Destroy();
end;

function TTcpConn.Read(AMaxBytes: Integer): string;
var
  Buf: Pointer;
  N: Int64;
begin
  Result := '';
  if AMaxBytes <= 0 then
    Exit;
  { If ReadLine buffered over-read bytes, hand those back first. }
  if FPending <> '' then
  begin
    if Length(FPending) <= AMaxBytes then
    begin
      Result := FPending;
      FPending := '';
    end
    else
    begin
      Result := Copy(FPending, 0, AMaxBytes);
      FPending := Copy(FPending, AMaxBytes, Length(FPending) - AMaxBytes);
    end;
    Exit;
  end;
  if FClosed then
    Exit;
  Buf := GetMem(AMaxBytes);
  N := FiberRecv(FFd, Buf, AMaxBytes);
  if N > 0 then
    Result := BytesToString(Buf, Integer(N))
  else
    { 0 = peer EOF; negative = error/timeout.  Either way no more data. }
    FClosed := True;
  FreeMem(Buf);
end;

function TTcpConn.ReadFull(ACount: Integer): string;
var
  Chunk: string;
  Got: Integer;
begin
  Result := '';
  if ACount <= 0 then
    Exit;
  Got := 0;
  while Got < ACount do
  begin
    Chunk := Self.Read(ACount - Got);
    if Chunk = '' then
      Break;                 { EOF / error }
    Result := Result + Chunk;
    Got := Got + Length(Chunk);
  end;
end;

function TTcpConn.Write(const AData: string): Boolean;
var
  Total: Integer;
  N: Int64;
  P: PChar;
begin
  Total := Length(AData);
  if Total = 0 then
    Exit(True);
  if FClosed then
    Exit(False);
  P := PChar(AData);
  while Total > 0 do
  begin
    N := FiberSend(FFd, P, Total);
    if N <= 0 then
    begin
      FClosed := True;
      Exit(False);
    end;
    P := P + N;
    Total := Total - Integer(N);
  end;
  Result := True;
end;

function TTcpConn.ReadLine(out ALine: string): Boolean;
var
  Nl, I: Integer;
  Chunk, Line: string;
  B: Byte;
begin
  ALine := '';
  while True do
  begin
    { Look for an LF in the pending buffer. }
    Nl := -1;
    for I := 0 to Length(FPending) - 1 do
    begin
      B := Byte(FPending[I]);
      if B = 10 then
      begin
        Nl := I;
        Break;
      end;
    end;
    if Nl >= 0 then
    begin
      Line := Copy(FPending, 0, Nl);
      FPending := Copy(FPending, Nl + 1, Length(FPending) - Nl - 1);
      { strip a trailing CR }
      if (Length(Line) > 0) and (Byte(Line[Length(Line) - 1]) = 13) then
        Line := Copy(Line, 0, Length(Line) - 1);
      ALine := Line;
      Exit(True);
    end;
    if FClosed then
    begin
      { No terminator will ever arrive; surface the partial bytes. }
      ALine := FPending;
      FPending := '';
      Exit(False);
    end;
    { Need more bytes. }
    Chunk := Self.Read(4096);
    if Chunk = '' then
    begin
      ALine := FPending;
      FPending := '';
      Exit(False);
    end;
    FPending := FPending + Chunk;
  end;
end;

procedure TTcpConn.Unread(const AData: string);
begin
  if AData <> '' then
    FPending := AData + FPending;
end;

procedure TTcpConn.Close;
begin
  if not FClosed then
    FClosed := True;
  if FFd >= 0 then
  begin
    CloseSocket(FFd);
    FFd := -1;
  end;
end;

{ ---------------------------------------------------------------------------
  TTcpClient
  --------------------------------------------------------------------------- }

function TTcpClient.Connect(const AHostIp: string; APort: UInt16): TTcpConn;
var
  Fd, Rc: Integer;
  Ip: UInt32;
  SA: TSockAddrIn;
begin
  Result := nil;
  if not ParseIPv4(AHostIp, Ip) then
    Exit;
  Fd := Socket(AF_INET, SOCK_STREAM, 0);
  if Fd < 0 then
    Exit;
  SuppressSigPipe(Fd);
  SetNonBlocking(Fd);
  FillSockAddr(SA, Ip, APort);
  Rc := FiberConnect(Fd, @SA, 16);
  if Rc <> 0 then
  begin
    CloseSocket(Fd);
    Exit;
  end;
  Result := TTcpConn.Create(Fd);
end;

{ ---------------------------------------------------------------------------
  TTcpServer
  --------------------------------------------------------------------------- }

constructor TTcpServer.Create(APort: UInt16; AReusePort: Boolean = False);
begin
  FPort := APort;
  FListenFd := -1;
  FRunning := False;
  FReusePort := AReusePort;
  FAddr := INADDR_LOOPBACK;
end;

destructor TTcpServer.Destroy;
begin
  Self.Stop();
  inherited Destroy();
end;

function TTcpServer.Start: Boolean;
begin
  Result := Self.StartOn(INADDR_LOOPBACK);
end;

function TTcpServer.StartOn(AAddr: UInt32): Boolean;
begin
  FAddr := AAddr;
  if FReusePort then
    FListenFd := TcpListenReusePort(AAddr, FPort, 128)
  else
    FListenFd := TcpListen(AAddr, FPort, 128);
  if FListenFd >= 0 then
    SetNonBlocking(FListenFd);
  Result := FListenFd >= 0;
  FRunning := Result;
end;

{ The argument each connection fiber receives.  A PLAIN heap record (GetMem),
  NOT an ARC class: passing an ARC object to SpawnFiber as a raw Pointer casts
  away its reference, so the accept loop's local would be the only ref and ARC
  would free it on the next loop iteration — before the fiber ever runs (spawning
  does not switch).  The record carries the raw fd plus the server pointer; the
  fiber owns the record (frees it) and builds its own TTcpConn from the fd, so
  every ARC lifetime lives entirely inside the fiber.  The handler is read from
  the server, whose ref (FHandler) outlives every connection fiber. }
type
  PConnFiberArg = ^TConnFiberArg;
  TConnFiberArg = record
    Fd: Integer;
    Server: Pointer;      { TTcpServer, unretained — outlives the fiber }
  end;

procedure ConnFiberEntry(AArg: Pointer);
var
  A: PConnFiberArg;
  Srv: TTcpServer;
  Fd: Integer;
  Conn: TTcpConn;
begin
  A := PConnFiberArg(AArg);
  Fd := A^.Fd;
  Srv := TTcpServer(A^.Server);
  FreeMem(A);
  Conn := TTcpConn.Create(Fd);
  try
    Srv.FHandler.Handle(Conn);
  finally
    Conn.Close();
    Conn.Free();
  end;
end;

procedure TTcpServer.Serve(AHandler: IConnHandler);
var
  ConnFd: Integer;
  Arg: PConnFiberArg;
begin
  FHandler := AHandler;
  while FRunning do
  begin
    { Timed accept so the loop periodically re-checks FRunning: closing the
      listen fd does NOT reliably wake a fiber parked in epoll_wait, so Stop
      cannot rely on that.  A short deadline lets Stop take effect within one
      poll interval without busy-waiting (the fiber parks between polls). }
    ConnFd := FiberAcceptT(FListenFd, ACCEPT_POLL_MS);
    if ConnFd = IO_ETIMEDOUT then
      Continue;                 { re-evaluate FRunning }
    if ConnFd < 0 then
    begin
      { Stop closed the listen fd (EBADF) or a fatal accept error: leave. }
      if not FRunning then
        Break;
      { A transient error (e.g. the connection was reset before accept): keep
        serving. }
      Continue;
    end;
    Arg := PConnFiberArg(GetMem(SizeOf(TConnFiberArg)));
    Arg^.Fd := ConnFd;
    Arg^.Server := Pointer(Self);
    SpawnFiber(@ConnFiberEntry, Pointer(Arg));
  end;
end;

procedure TTcpServer.Stop;
begin
  FRunning := False;
  if FListenFd >= 0 then
  begin
    CloseSocket(FListenFd);
    FListenFd := -1;
  end;
end;

end.
