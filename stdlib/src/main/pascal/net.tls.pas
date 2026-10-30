{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Tls;

// L5 of the fiber runtime (docs/async-networking-design.adoc, [#components]):
// Net.Tls layers TLS over Net.Tcp using the TTlsConn from L4 (Net.Tls.Provider).
// TTlsClient dials a host:port over TCP, then drives a client-side TLS handshake
// (SNI = host, verification per the security default).  TTlsServer listens and
// spawns one fiber per connection, each wrapping the accepted socket in a
// server-side TTlsConn handshake before handing the encrypted stream to the
// application handler.
//
// These components depend ONLY on TTlsConn (the L4 port), never on OpenSSL
// symbols directly, so a pure-Pascal provider slots in by swapping GTlsProvider.
// If GTlsProvider is nil, asking for TLS raises a clear runtime error (ETlsError)
// rather than failing to link.
//
// LINKING: Net.Tls transitively uses Net.Tls.Provider (which binds libssl/
// libcrypto), so any program using Net.Tls MUST be compiled with
// `--linker external`.  NATIVE BACKEND ONLY.

interface

uses
  SysUtils, async.fibers, Net.Tcp, Net.Tls.Provider;

type
  { Raised when TLS is requested but no provider is installed. }
  ETlsError = class(Exception);

  { A TLS-secured stream, layered over a plaintext TTcpConn.  Owns both the
    TTlsConn (the SSL session) and the underlying TTcpConn (the transport).
    Read/Write move plaintext; Close tears down TLS then the socket. }
  TTlsStream = class
  private
    FTcp: TTcpConn;         { owned transport }
    FTls: TTlsConn;         { owned SSL session over FTcp.Fd }
    FCtx: TTlsContext;      { owned context (kept alive for FTls's lifetime) }
    FClosed: Boolean;
  public
    { Take ownership of a connected TTcpConn, a TTlsContext, and a TTlsConn
      already created over the TCP fd.  The handshake must already have run (the
      client/server helpers do this before constructing the stream). }
    constructor Create(ATcp: TTcpConn; ACtx: TTlsContext; ATls: TTlsConn);
    destructor Destroy; override;

    { Read up to AMaxBytes of plaintext ('' on close/EOF/error). }
    function Read(AMaxBytes: Int): string;
    { Write all of ADATA as plaintext (encrypted on the wire). }
    function Write(const AData: string): Boolean;
    { Close TLS (close-notify) then the transport socket.  Idempotent. }
    procedure Close;

    property Closed: Boolean read FClosed;
  end;

  { Dials outbound TLS connections. }
  TTlsClient = class
  public
    { Connect to AHostIp:APort over TCP, then complete a client-side TLS
      handshake.  ASniHost is the name sent via SNI and matched against the
      certificate (typically the DNS name; for a numeric-IP dial pass the name
      you expect the cert to carry).  AVerify controls peer verification (the
      security default is True).  ACaFile, when non-empty, is a PEM file of extra
      trusted CA certificate(s) added to the trust store before the handshake —
      this lets verify=True succeed against a private/self-signed CA without
      disabling verification.  Returns a connected TTlsStream (caller owns it)
      or nil on TCP/handshake failure.  Raises ETlsError if no provider. }
    function Connect(const AHostIp: string; APort: UInt16;
      const ASniHost: string; AVerify: Boolean = True;
      const ACaFile: string = ''): TTlsStream;
  end;

  { The application supplies this; the TLS server spawns one fiber per accepted
    connection, completes the server-side handshake, and calls Handle(stream) on
    the encrypted stream.  The handler owns the stream and should Close/Free it. }
  ITlsConnHandler = interface
    procedure Handle(AStream: TTlsStream);
  end;

  { A fiber-per-connection TLS server: a TTcpServer underneath whose per-conn
    handler wraps each socket in a server-side TTlsConn handshake, then invokes
    the application's ITlsConnHandler on the secured stream. }
  TTlsServer = class
  private
    FTcp: TTcpServer;
    FCtx: TTlsContext;         { server context (cert+key), shared by all conns }
    FAppHandler: ITlsConnHandler;
    FTlsAdapter: IConnHandler;  { the TCP-level handler that does the TLS wrap }
  public
    { APort to listen on; ACertPemPath/AKeyPemPath are the server certificate
      chain + private key PEM file paths.  Raises ETlsError if no provider. }
    constructor Create(APort: UInt16; const ACertPemPath, AKeyPemPath: string);
    destructor Destroy; override;

    { Bind + listen on 127.0.0.1:APort.  Returns False on bind failure or if the
      certificate/key could not be loaded. }
    function Start: Boolean;

    { Accept loop: per connection, handshake TLS then call AHandler.Handle on the
      secured stream.  Drive from inside a fiber under a scheduler. }
    procedure Serve(AHandler: ITlsConnHandler);

    { Stop the accept loop and close the listen socket. }
    procedure Stop;

    property Port: UInt16 read GetPort;
  private
    function GetPort: UInt16;
  end;

implementation

{ ---------------------------------------------------------------------------
  TTlsStream
  --------------------------------------------------------------------------- }

constructor TTlsStream.Create(ATcp: TTcpConn; ACtx: TTlsContext; ATls: TTlsConn);
begin
  FTcp := ATcp;
  FCtx := ACtx;
  FTls := ATls;
  FClosed := False;
end;

destructor TTlsStream.Destroy;
begin
  Self.Close();
  { FTls holds the SSL over FTcp.Fd; free TLS before the socket.  FCtx must
    outlive FTls. }
  if FTls <> nil then
  begin
    FTls.Free();
    FTls := nil;
  end;
  if FCtx <> nil then
  begin
    FCtx.Free();
    FCtx := nil;
  end;
  if FTcp <> nil then
  begin
    FTcp.Free();
    FTcp := nil;
  end;
  inherited Destroy();
end;

function TTlsStream.Read(AMaxBytes: Int): string;
begin
  if FClosed or (FTls = nil) then
    Exit('');
  Result := FTls.Read(AMaxBytes);
end;

function TTlsStream.Write(const AData: string): Boolean;
begin
  if FClosed or (FTls = nil) then
    Exit(False);
  Result := FTls.Write(AData);
end;

procedure TTlsStream.Close;
begin
  if FClosed then
    Exit;
  FClosed := True;
  if FTls <> nil then
    FTls.Close();          { TLS close-notify; does not close the socket }
  if FTcp <> nil then
    FTcp.Close();          { now shut the transport }
end;

{ ---------------------------------------------------------------------------
  TTlsClient
  --------------------------------------------------------------------------- }

function TTlsClient.Connect(const AHostIp: string; APort: UInt16;
  const ASniHost: string; AVerify: Boolean = True;
  const ACaFile: string = ''): TTlsStream;
var
  Tcp: TTcpClient;
  Conn: TTcpConn;
  Ctx: TTlsContext;
  Tls: TTlsConn;
begin
  Result := nil;
  if GTlsProvider = nil then
    raise ETlsError.Create('TLS requested but no GTlsProvider is installed ' +
      '(call InstallOpenSSLProvider or set GTlsProvider)');
  Tcp := TTcpClient.Create();
  Conn := Tcp.Connect(AHostIp, APort);
  Tcp.Free();
  if Conn = nil then
    Exit;                          { TCP connect failed }
  Ctx := GTlsProvider.CreateClientContext(AVerify);
  if Ctx = nil then
  begin
    Conn.Free();
    Exit;
  end;
  if ACaFile <> '' then
    Ctx.TrustCertFile(ACaFile);    { trust a private/self-signed CA }
  Tls := Ctx.NewConn(Conn.Fd, ASniHost);
  if Tls = nil then
  begin
    Ctx.Free();
    Conn.Free();
    Exit;
  end;
  if not Tls.Handshake() then
  begin
    Tls.Free();
    Ctx.Free();
    Conn.Free();
    Exit;                          { handshake / verification failure }
  end;
  Result := TTlsStream.Create(Conn, Ctx, Tls);
end;

{ ---------------------------------------------------------------------------
  TTlsServer - the TCP-level adapter that upgrades each connection to TLS
  --------------------------------------------------------------------------- }

type
  { Bridges the plaintext TTcpServer to the TLS application handler: for each
    accepted TTcpConn it builds a server-side TTlsConn, handshakes, and (on
    success) invokes the app handler on a TTlsStream.  Holds unretained back-refs
    to the server's context + app handler, both of which outlive every conn. }
  TTlsServerAdapter = class(IConnHandler)
  private
    FOwner: TTlsServer;      { unretained }
  public
    constructor Create(AOwner: TTlsServer);
    procedure Handle(AConn: TTcpConn);
  end;

constructor TTlsServerAdapter.Create(AOwner: TTlsServer);
begin
  FOwner := AOwner;
end;

procedure TTlsServerAdapter.Handle(AConn: TTcpConn);
var
  Tls: TTlsConn;
  Stream: TTlsStream;
begin
  { Build a server-side TLS session over the accepted socket.  The context is
    shared (created once at Start); NewConn allocates a fresh SSL per conn.  We
    must NOT free the shared context here, so build the stream with nil context
    ownership and free only the SSL session. }
  Tls := FOwner.FCtx.NewConn(AConn.Fd, '');
  if Tls = nil then
    Exit;
  if not Tls.Handshake() then
  begin
    Tls.Close();
    Tls.Free();
    Exit;
  end;
  { The stream owns the TTcpConn + the per-conn TTlsConn, but NOT the shared
    context (pass nil so Destroy does not free it). }
  Stream := TTlsStream.Create(AConn, nil, Tls);
  try
    FOwner.FAppHandler.Handle(Stream);
  finally
    Stream.Close();
    Stream.Free();
  end;
end;

{ ---------------------------------------------------------------------------
  TTlsServer
  --------------------------------------------------------------------------- }

constructor TTlsServer.Create(APort: UInt16; const ACertPemPath, AKeyPemPath: string);
begin
  if GTlsProvider = nil then
    raise ETlsError.Create('TLS server requested but no GTlsProvider is installed');
  FTcp := TTcpServer.Create(APort);
  FCtx := GTlsProvider.CreateServerContext(ACertPemPath, AKeyPemPath);
  FTlsAdapter := TTlsServerAdapter.Create(Self);
end;

destructor TTlsServer.Destroy;
begin
  Self.Stop();
  FTlsAdapter := nil;
  if FTcp <> nil then
  begin
    FTcp.Free();
    FTcp := nil;
  end;
  if FCtx <> nil then
  begin
    FCtx.Free();
    FCtx := nil;
  end;
  inherited Destroy();
end;

function TTlsServer.Start: Boolean;
begin
  if FCtx = nil then
    Exit(False);               { certificate/key failed to load }
  Result := FTcp.Start();
end;

procedure TTlsServer.Serve(AHandler: ITlsConnHandler);
begin
  FAppHandler := AHandler;
  FTcp.Serve(FTlsAdapter);
end;

procedure TTlsServer.Stop;
begin
  if FTcp <> nil then
    FTcp.Stop();
end;

function TTlsServer.GetPort: UInt16;
begin
  Result := FTcp.Port;
end;

end.
