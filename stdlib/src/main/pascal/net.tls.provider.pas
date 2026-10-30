{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Tls.Provider;

// L4 of the fiber runtime (docs/async-networking-design.adoc, "L4 - TLS"):
// a TLS layer behind a pluggable port (TTlsProvider) so a future pure-Pascal
// provider can replace OpenSSL without touching any L5 component.  The concrete
// provider here (TOpenSSLProvider) binds a MINIMAL FUNCTION-ONLY surface of
// libssl/libcrypto via `external 'ssl'/'crypto' name '...'` and uses the
// MEMORY-BIO model: OpenSSL never sees the socket fd.  Instead a TTlsConn holds
// two in-memory BIOs (rbio = ciphertext in, wbio = ciphertext out); when an SSL
// operation returns WANT_READ/WANT_WRITE the connection PUMPS ciphertext between
// those BIOs and the transport fd using the fiber-aware FiberRecv/FiberSend from
// L3 (async.io), then retries.  This maps WANT_READ/WANT_WRITE straight onto
// L3's park-on-readable/writable discipline, so TLS drops into the scheduler
// with no special cases.
//
// SECURITY DEFAULTS: client contexts verify the peer certificate against the OS
// trust store (SSL_VERIFY_PEER + SSL_CTX_set_default_verify_paths), send SNI
// (SSL_set_tlsext_host_name), and require the hostname to match the certificate
// (SSL_set1_host).  Opting out of verification is explicit (AVerify = False) and
// deliberately loud in the API.
//
// LINKING: because this unit references `external 'ssl'`/`external 'crypto'`
// symbols, a program that (transitively) uses it binds libssl and libcrypto.
// The internal linker handles that on Linux (AUTO link mode flips to dynamic
// and records each library as DT_NEEDED) and on macOS (one LC_LOAD_DYLIB per
// library; Homebrew's /opt/homebrew/lib is searched, or pass --lib-path).  TLS
// is therefore unavailable only in the static/libc-free build, until a
// pure-Pascal provider exists.
//
// NATIVE BACKEND ONLY (the pump uses async.io -> async.fibers, an inline-asm
// context leaf the QBE backend rejects).  Linux + OpenSSL 3.x for now.

interface

uses
  SysUtils;

type
  { A TLS connection: wraps an SSL object + two memory BIOs + a transport fd.
    Read/Write move PLAINTEXT; the ciphertext pump is internal and fiber-aware.
    Handshake completes the TLS negotiation.  Close sends close-notify then
    frees the SSL object.  The transport fd is NOT owned (the caller/TTcpConn
    owns it), so Close leaves it open for the owner to close. }
  TTlsConn = class
  private
    FSsl: Pointer;         { SSL* }
    FRbio: Pointer;        { BIO* memory bio, ciphertext IN  (peer -> us) }
    FWbio: Pointer;        { BIO* memory bio, ciphertext OUT (us   -> peer) }
    FFd: Int;          { transport socket fd, unretained }
    FClosed: Boolean;
    FServer: Boolean;
    { Drain wbio to the socket (FiberSend all pending ciphertext). }
    function FlushOut: Boolean;
    { Read one chunk of ciphertext from the socket into rbio.  Returns >0 on
      progress, 0 on EOF, <0 on error/timeout. }
    function PumpIn: Int64;
    { Retry loop shared by Handshake/Read/Write: given the SSL_get_error code
      after an SSL op, pump the BIOs and return True to retry, False to stop
      (fatal / EOF). }
    function DriveIo(AErr: Int): Boolean;
  public
    { Wrap an SSL object (already created + configured by the context) around
      the transport fd.  Creates the two memory BIOs and attaches them. }
    constructor Create(ASsl: Pointer; AFd: Int; AIsServer: Boolean);
    destructor Destroy; override;

    { Complete the TLS handshake (parking the fiber while the network round-trip
      is in flight).  Returns True on success, False on failure (verification
      failure, protocol error, or transport EOF). }
    function Handshake: Boolean;

    { Read up to AMaxBytes of PLAINTEXT.  Returns the bytes read; '' on clean
      close-notify / EOF / error (see Closed). }
    function Read(AMaxBytes: Int): string;

    { Write all of ADATA as plaintext (encrypted on the wire).  Returns True
      when every byte was accepted, False on error / peer close. }
    function Write(const AData: string): Boolean;

    { Send TLS close-notify (best effort) and free the SSL object.  Idempotent.
      Does NOT close the transport fd. }
    procedure Close;

    property Fd: Int read FFd;
    property Closed: Boolean read FClosed;
  end;

  { A TLS context (wraps an SSL_CTX).  A client context verifies+SNIs by
    default; a server context is loaded with a certificate + private key.
    NewConn wraps a transport fd in a fresh TTlsConn ready to Handshake. }
  TTlsContext = class
  private
    FCtx: Pointer;         { SSL_CTX* }
    FIsServer: Boolean;
  public
    constructor Create(ACtx: Pointer; AIsServer: Boolean);
    destructor Destroy; override;

    { Create a TTlsConn over AFd.  For a client, AHostName drives SNI and the
      hostname-verification check (pass '' to skip SNI/host-match — only sensible
      when the context was created with verification off).  For a server,
      AHostName is ignored. }
    function NewConn(AFd: Int; const AHostName: string): TTlsConn;

    { Trust the CA certificate(s) in APemPath for peer verification (client
      contexts).  Use to pin a private/self-signed CA in addition to (or instead
      of) the OS trust store.  Returns True on success. }
    function TrustCertFile(const APemPath: string): Boolean;

    property Ctx: Pointer read FCtx;
    property IsServer: Boolean read FIsServer;
  end;

  { The pluggable TLS port.  A component asks GTlsProvider for a context; it
    never references OpenSSL symbols directly, so a pure-Pascal provider can be
    substituted by swapping GTlsProvider with zero change to any component. }
  TTlsProvider = class
  public
    { A client context.  AVerify = True (the default posture) turns on peer
      certificate verification against the OS trust store; AVerify = False
      disables it (explicit, loud opt-out for self-signed / dev use). }
    function CreateClientContext(const AVerify: Boolean): TTlsContext; virtual; abstract;

    { A server context loaded with a certificate chain + private key.
      ACertPemPath / AKeyPemPath are PEM file paths. }
    function CreateServerContext(const ACertPemPath, AKeyPemPath: string): TTlsContext; virtual; abstract;
  end;

  { The OpenSSL-backed provider (libssl.so.3 / libcrypto.so.3 on Linux). }
  TOpenSSLProvider = class(TTlsProvider)
  public
    constructor Create;
    function CreateClientContext(const AVerify: Boolean): TTlsContext; override;
    function CreateServerContext(const ACertPemPath, AKeyPemPath: string): TTlsContext; override;
  end;

var
  { The active provider.  nil until installed (InstallOpenSSLProvider or an
    application-supplied provider).  L5 components raise a clear runtime error
    when TLS is requested and this is nil, rather than failing to link. }
  GTlsProvider: TTlsProvider;

{ Install a TOpenSSLProvider as GTlsProvider (idempotent).  Also performs the
  one-time OpenSSL library init.  Call once at startup in a TLS-using program. }
procedure InstallOpenSSLProvider;

implementation

uses
  async.io, Net.Sockets;

{ ---------------------------------------------------------------------------
  libssl / libcrypto bindings  (FUNCTIONS ONLY - opaque structs survive skew)
  --------------------------------------------------------------------------- }

const
  { SSL_get_error return codes (openssl/ssl.h). }
  SSL_ERROR_NONE        = 0;
  SSL_ERROR_WANT_READ   = 2;
  SSL_ERROR_WANT_WRITE  = 3;
  SSL_ERROR_ZERO_RETURN = 6;

  { Verify modes (openssl/ssl.h). }
  SSL_VERIFY_NONE = 0;
  SSL_VERIFY_PEER = 1;

  { SSL_FILETYPE_PEM = X509_FILETYPE_PEM (openssl/x509.h). }
  SSL_FILETYPE_PEM = 1;

  { X509_V_OK (openssl/x509_vfy.h). }
  X509_V_OK = 0;

  { SSL_ctrl command + SNI name type: SSL_set_tlsext_host_name is a macro over
    SSL_ctrl(s, SSL_CTRL_SET_TLSEXT_HOSTNAME, TLSEXT_NAMETYPE_host_name, name).
    (openssl/ssl.h, openssl/tls1.h) }
  SSL_CTRL_SET_TLSEXT_HOSTNAME = 55;
  TLSEXT_NAMETYPE_host_name    = 0;

  { OPENSSL_init_ssl option: load the SSL error strings + ciphers.  Passing 0 is
    also fine for our uses; we pass 0. }
  OPENSSL_INIT_DEFAULT = 0;

{ --- libssl --- }
function c_OPENSSL_init_ssl(AOpts: UInt64; ASettings: Pointer): Int32;
  external 'ssl' name 'OPENSSL_init_ssl';
function c_TLS_client_method: Pointer;
  external 'ssl' name 'TLS_client_method';
function c_TLS_server_method: Pointer;
  external 'ssl' name 'TLS_server_method';
function c_SSL_CTX_new(AMethod: Pointer): Pointer;
  external 'ssl' name 'SSL_CTX_new';
procedure c_SSL_CTX_free(ACtx: Pointer);
  external 'ssl' name 'SSL_CTX_free';
procedure c_SSL_CTX_set_verify(ACtx: Pointer; AMode: Int32; ACb: Pointer);
  external 'ssl' name 'SSL_CTX_set_verify';
function c_SSL_CTX_set_default_verify_paths(ACtx: Pointer): Int32;
  external 'ssl' name 'SSL_CTX_set_default_verify_paths';
function c_SSL_CTX_load_verify_locations(ACtx: Pointer; ACAFile, ACAPath: PChar): Int32;
  external 'ssl' name 'SSL_CTX_load_verify_locations';
function c_SSL_CTX_use_certificate_file(ACtx: Pointer; AFile: PChar; AType: Int32): Int32;
  external 'ssl' name 'SSL_CTX_use_certificate_file';
function c_SSL_CTX_use_certificate_chain_file(ACtx: Pointer; AFile: PChar): Int32;
  external 'ssl' name 'SSL_CTX_use_certificate_chain_file';
function c_SSL_CTX_use_PrivateKey_file(ACtx: Pointer; AFile: PChar; AType: Int32): Int32;
  external 'ssl' name 'SSL_CTX_use_PrivateKey_file';
function c_SSL_new(ACtx: Pointer): Pointer;
  external 'ssl' name 'SSL_new';
procedure c_SSL_free(ASsl: Pointer);
  external 'ssl' name 'SSL_free';
procedure c_SSL_set_bio(ASsl: Pointer; ARbio, AWbio: Pointer);
  external 'ssl' name 'SSL_set_bio';
function c_SSL_ctrl(ASsl: Pointer; ACmd: Int32; ALarg: Int64; AParg: Pointer): Int64;
  external 'ssl' name 'SSL_ctrl';
function c_SSL_set1_host(ASsl: Pointer; AHostName: PChar): Int32;
  external 'ssl' name 'SSL_set1_host';
procedure c_SSL_set_connect_state(ASsl: Pointer);
  external 'ssl' name 'SSL_set_connect_state';
procedure c_SSL_set_accept_state(ASsl: Pointer);
  external 'ssl' name 'SSL_set_accept_state';
function c_SSL_do_handshake(ASsl: Pointer): Int32;
  external 'ssl' name 'SSL_do_handshake';
function c_SSL_read(ASsl: Pointer; ABuf: Pointer; ANum: Int32): Int32;
  external 'ssl' name 'SSL_read';
function c_SSL_write(ASsl: Pointer; ABuf: Pointer; ANum: Int32): Int32;
  external 'ssl' name 'SSL_write';
function c_SSL_get_error(ASsl: Pointer; ARet: Int32): Int32;
  external 'ssl' name 'SSL_get_error';
function c_SSL_shutdown(ASsl: Pointer): Int32;
  external 'ssl' name 'SSL_shutdown';
function c_SSL_get_verify_result(ASsl: Pointer): Int64;
  external 'ssl' name 'SSL_get_verify_result';

{ --- libcrypto --- }
function c_BIO_new(AType: Pointer): Pointer;
  external 'crypto' name 'BIO_new';
function c_BIO_s_mem: Pointer;
  external 'crypto' name 'BIO_s_mem';
function c_BIO_read(ABio: Pointer; ABuf: Pointer; ALen: Int32): Int32;
  external 'crypto' name 'BIO_read';
function c_BIO_write(ABio: Pointer; ABuf: Pointer; ALen: Int32): Int32;
  external 'crypto' name 'BIO_write';

{ SSL_set_tlsext_host_name(s, name) macro, replicated over SSL_ctrl.  The name
  string must outlive the call (SSL_ctrl copies it internally). }
function SSL_set_tlsext_host_name(ASsl: Pointer; AName: PChar): Int64;
begin
  Result := c_SSL_ctrl(ASsl, SSL_CTRL_SET_TLSEXT_HOSTNAME,
    TLSEXT_NAMETYPE_host_name, Pointer(AName));
end;

var
  GInited: Boolean;

procedure EnsureOpenSSLInit;
begin
  if not GInited then
  begin
    c_OPENSSL_init_ssl(OPENSSL_INIT_DEFAULT, nil);
    GInited := True;
  end;
end;

{ ---------------------------------------------------------------------------
  TTlsConn - the memory-BIO pump
  --------------------------------------------------------------------------- }

const
  { Ciphertext pump chunk (bytes drained from/into a memory BIO per iteration). }
  PUMP_CHUNK = 16384;

constructor TTlsConn.Create(ASsl: Pointer; AFd: Int; AIsServer: Boolean);
begin
  FSsl := ASsl;
  FFd := AFd;
  FServer := AIsServer;
  FClosed := False;
  FRbio := c_BIO_new(c_BIO_s_mem());
  FWbio := c_BIO_new(c_BIO_s_mem());
  { SSL_set_bio takes ownership of both BIOs; SSL_free frees them. }
  c_SSL_set_bio(FSsl, FRbio, FWbio);
end;

destructor TTlsConn.Destroy;
begin
  Self.Close();
  inherited Destroy();
end;

function TTlsConn.FlushOut: Boolean;
var
  Buf: Pointer;
  N: Int;
  Off, Total: Int;
  P: PChar;
  Sent: Int64;
begin
  Result := True;
  Buf := GetMem(PUMP_CHUNK);
  try
    while True do
    begin
      N := c_BIO_read(FWbio, Buf, PUMP_CHUNK);
      if N <= 0 then
        Break;                    { nothing more buffered in wbio }
      { Write the whole chunk to the socket (looping over short writes). }
      P := PChar(Buf);
      Off := 0;
      Total := N;
      while Off < Total do
      begin
        Sent := FiberSend(FFd, P + Off, Total - Off);
        if Sent <= 0 then
        begin
          Result := False;
          Exit;
        end;
        Off := Off + Int32(Sent);
      end;
    end;
  finally
    FreeMem(Buf);
  end;
end;

function TTlsConn.PumpIn: Int64;
var
  Buf: Pointer;
  N: Int64;
  W: Int;
begin
  Buf := GetMem(PUMP_CHUNK);
  try
    N := FiberRecv(FFd, Buf, PUMP_CHUNK);
    if N > 0 then
    begin
      { Feed the ciphertext into rbio for OpenSSL to consume. }
      W := c_BIO_write(FRbio, Buf, Int32(N));
      if W <> Int32(N) then
        Exit(-1);                 { rbio should never short-write a mem bio }
    end;
    Result := N;                  { >0 progress, 0 EOF, <0 error/timeout }
  finally
    FreeMem(Buf);
  end;
end;

function TTlsConn.DriveIo(AErr: Int): Boolean;
var
  N: Int64;
begin
  { On WANT_WRITE OpenSSL has produced ciphertext to send; on WANT_READ it needs
    more ciphertext from the peer.  In both cases we FIRST flush any pending
    outbound ciphertext (a handshake flight often needs sending before the peer
    can answer), then, for WANT_READ, pull a chunk of inbound ciphertext. }
  Result := False;
  case AErr of
    SSL_ERROR_WANT_WRITE:
      begin
        if not Self.FlushOut() then
          Exit;
        Result := True;           { retry the SSL op }
      end;
    SSL_ERROR_WANT_READ:
      begin
        if not Self.FlushOut() then
          Exit;                   { push our flight out before waiting to read }
        N := Self.PumpIn();
        if N <= 0 then
          Exit;                   { EOF or error: cannot make progress }
        Result := True;           { retry the SSL op }
      end;
  end;
end;

function TTlsConn.Handshake: Boolean;
var
  Rc, Err: Int;
begin
  if FServer then
    c_SSL_set_accept_state(FSsl)
  else
    c_SSL_set_connect_state(FSsl);
  while True do
  begin
    Rc := c_SSL_do_handshake(FSsl);
    if Rc = 1 then
    begin
      { Handshake complete; push any final ciphertext (e.g. the client's
        Finished) so the peer sees it. }
      Result := Self.FlushOut();
      Exit;
    end;
    Err := c_SSL_get_error(FSsl, Rc);
    if not Self.DriveIo(Err) then
    begin
      Result := False;
      Exit;
    end;
  end;
end;

function TTlsConn.Read(AMaxBytes: Int): string;
var
  Buf: Pointer;
  Rc, Err: Int;
begin
  Result := '';
  if (AMaxBytes <= 0) or FClosed then
    Exit;
  Buf := GetMem(AMaxBytes);
  try
    while True do
    begin
      Rc := c_SSL_read(FSsl, Buf, AMaxBytes);
      if Rc > 0 then
      begin
        Result := BytesToString(Buf, Rc);
        Exit;
      end;
      Err := c_SSL_get_error(FSsl, Rc);
      if Err = SSL_ERROR_ZERO_RETURN then
      begin
        { Clean TLS close-notify from the peer. }
        FClosed := True;
        Exit;
      end;
      if not Self.DriveIo(Err) then
      begin
        FClosed := True;
        Exit;
      end;
    end;
  finally
    FreeMem(Buf);
  end;
end;

function TTlsConn.Write(const AData: string): Boolean;
var
  Total, Off: Int;
  Rc, Err: Int;
  P: PChar;
begin
  Total := Length(AData);
  if Total = 0 then
    Exit(True);
  if FClosed then
    Exit(False);
  P := PChar(AData);
  Off := 0;
  while Off < Total do
  begin
    Rc := c_SSL_write(FSsl, P + Off, Total - Off);
    if Rc > 0 then
    begin
      Off := Off + Rc;
      { SSL_write produced ciphertext in wbio; flush it to the socket. }
      if not Self.FlushOut() then
      begin
        FClosed := True;
        Exit(False);
      end;
      Continue;
    end;
    Err := c_SSL_get_error(FSsl, Rc);
    if not Self.DriveIo(Err) then
    begin
      FClosed := True;
      Exit(False);
    end;
  end;
  Result := True;
end;

procedure TTlsConn.Close;
begin
  if FClosed and (FSsl = nil) then
    Exit;
  FClosed := True;
  if FSsl <> nil then
  begin
    { Best-effort close-notify: one SSL_shutdown pass + flush.  We do not wait
      for the peer's close-notify (a half-close is fine for our uses). }
    c_SSL_shutdown(FSsl);
    Self.FlushOut();
    c_SSL_free(FSsl);             { frees the attached rbio + wbio too }
    FSsl := nil;
    FRbio := nil;
    FWbio := nil;
  end;
end;

{ ---------------------------------------------------------------------------
  TTlsContext
  --------------------------------------------------------------------------- }

constructor TTlsContext.Create(ACtx: Pointer; AIsServer: Boolean);
begin
  FCtx := ACtx;
  FIsServer := AIsServer;
end;

destructor TTlsContext.Destroy;
begin
  if FCtx <> nil then
  begin
    c_SSL_CTX_free(FCtx);
    FCtx := nil;
  end;
  inherited Destroy();
end;

function TTlsContext.NewConn(AFd: Int; const AHostName: string): TTlsConn;
var
  Ssl: Pointer;
begin
  Ssl := c_SSL_new(FCtx);
  if Ssl = nil then
    Exit(nil);
  if (not FIsServer) and (AHostName <> '') then
  begin
    { SNI + hostname verification.  SSL_set1_host binds the expected name so a
      certificate whose SAN/CN does not match will fail verification loudly. }
    SSL_set_tlsext_host_name(Ssl, PChar(AHostName));
    c_SSL_set1_host(Ssl, PChar(AHostName));
  end;
  Result := TTlsConn.Create(Ssl, AFd, FIsServer);
end;

function TTlsContext.TrustCertFile(const APemPath: string): Boolean;
begin
  Result := c_SSL_CTX_load_verify_locations(FCtx, PChar(APemPath), nil) = 1;
end;

{ ---------------------------------------------------------------------------
  TOpenSSLProvider
  --------------------------------------------------------------------------- }

constructor TOpenSSLProvider.Create;
begin
  EnsureOpenSSLInit();
end;

function TOpenSSLProvider.CreateClientContext(const AVerify: Boolean): TTlsContext;
var
  Ctx: Pointer;
begin
  Ctx := c_SSL_CTX_new(c_TLS_client_method());
  if Ctx = nil then
    Exit(nil);
  if AVerify then
  begin
    c_SSL_CTX_set_verify(Ctx, SSL_VERIFY_PEER, nil);
    c_SSL_CTX_set_default_verify_paths(Ctx);
  end
  else
    c_SSL_CTX_set_verify(Ctx, SSL_VERIFY_NONE, nil);
  Result := TTlsContext.Create(Ctx, False);
end;

function TOpenSSLProvider.CreateServerContext(const ACertPemPath, AKeyPemPath: string): TTlsContext;
var
  Ctx: Pointer;
begin
  Ctx := c_SSL_CTX_new(c_TLS_server_method());
  if Ctx = nil then
    Exit(nil);
  if c_SSL_CTX_use_certificate_chain_file(Ctx, PChar(ACertPemPath)) <> 1 then
  begin
    c_SSL_CTX_free(Ctx);
    Exit(nil);
  end;
  if c_SSL_CTX_use_PrivateKey_file(Ctx, PChar(AKeyPemPath), SSL_FILETYPE_PEM) <> 1 then
  begin
    c_SSL_CTX_free(Ctx);
    Exit(nil);
  end;
  Result := TTlsContext.Create(Ctx, True);
end;

procedure InstallOpenSSLProvider;
begin
  EnsureOpenSSLInit();
  if GTlsProvider = nil then
    GTlsProvider := TOpenSSLProvider.Create();
end;

initialization
  GTlsProvider := nil;
  GInited := False;

end.
