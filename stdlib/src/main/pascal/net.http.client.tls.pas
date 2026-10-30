{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Http.Client.Tls;

// L5 of the fiber runtime: the opt-in TLS binding for Net.Http.Client.
//
// Net.Http.Client is deliberately libssl-free — it never `uses Net.Tls`, so the
// plaintext http client (and the internally-linked stdlib test build) does not
// drag in libssl.  A program that wants https `uses` THIS unit, whose
// initialisation installs GHttpTlsDialer with a dialer backed by Net.Tls's
// TTlsClient.  The dialer adapts a TTlsStream to the IHttpTlsStream surface the
// client needs.
//
// LINKING: this unit transitively uses Net.Tls (and thus libssl/libcrypto via
// `external 'ssl'/'crypto'`), so any program that `uses Net.Http.Client.Tls`
// MUST be built with `--backend native --linker external`.  Call
// InstallOpenSSLProvider once at startup (as for any Net.Tls program) so a
// GTlsProvider is present; without it, https dials raise ETlsError.
//
// Blaise strings are 0-based.

interface

uses
  SysUtils, Net.Http.Client, Net.Tls;

{ Install the OpenSSL-backed TLS dialer as GHttpTlsDialer (idempotent).  Called
  automatically by this unit's initialisation; exposed for explicit re-install. }
procedure InstallHttpTlsDialer;

implementation

type
  { Adapts a Net.Tls TTlsStream (owned) to the IHttpTlsStream surface the HTTP
    client's transport wrapper consumes.  Reference-counted: the client holds it
    for the lifetime of the connection and releases it (freeing the underlying
    TTlsStream) when the THttpConn is destroyed. }
  THttpTlsStreamAdapter = class(IHttpTlsStream)
  private
    FStream: TTlsStream;      { owned }
  public
    constructor Create(AStream: TTlsStream);
    destructor Destroy; override;
    function Read(AMaxBytes: Int): string;
    function Write(const AData: string): Boolean;
    procedure Close;
    function IsClosed: Boolean;
  end;

  { The concrete dialer: dials via TTlsClient and wraps the result. }
  TOpenSSLHttpTlsDialer = class(THttpTlsDialer)
  public
    function Dial(const AHost: string; APort: UInt16; AVerify: Boolean;
      const ACaFile: string): IHttpTlsStream; override;
  end;

{ ---- THttpTlsStreamAdapter ------------------------------------------------ }

constructor THttpTlsStreamAdapter.Create(AStream: TTlsStream);
begin
  FStream := AStream;
end;

destructor THttpTlsStreamAdapter.Destroy;
begin
  if FStream <> nil then
  begin
    FStream.Free();
    FStream := nil;
  end;
  inherited Destroy();
end;

function THttpTlsStreamAdapter.Read(AMaxBytes: Int): string;
begin
  if FStream = nil then
    Exit('');
  Result := FStream.Read(AMaxBytes);
end;

function THttpTlsStreamAdapter.Write(const AData: string): Boolean;
begin
  if FStream = nil then
    Exit(False);
  Result := FStream.Write(AData);
end;

procedure THttpTlsStreamAdapter.Close;
begin
  if FStream <> nil then
    FStream.Close();
end;

function THttpTlsStreamAdapter.IsClosed: Boolean;
begin
  if FStream = nil then
    Exit(True);
  Result := FStream.Closed;
end;

{ ---- TOpenSSLHttpTlsDialer ------------------------------------------------ }

function TOpenSSLHttpTlsDialer.Dial(const AHost: string; APort: UInt16;
  AVerify: Boolean; const ACaFile: string): IHttpTlsStream;
var
  Cli: TTlsClient;
  Stream: TTlsStream;
  Adapter: THttpTlsStreamAdapter;
begin
  Result := nil;
  Cli := TTlsClient.Create();
  Stream := Cli.Connect(AHost, APort, AHost, AVerify, ACaFile);
  Cli.Free();
  if Stream = nil then
    Exit;
  Adapter := THttpTlsStreamAdapter.Create(Stream);
  Result := Adapter;
end;

{ ---- installation --------------------------------------------------------- }

var
  GDialer: TOpenSSLHttpTlsDialer;

procedure InstallHttpTlsDialer;
begin
  if GDialer = nil then
    GDialer := TOpenSSLHttpTlsDialer.Create();
  SetHttpTlsDialer(GDialer);
end;

initialization
  InstallHttpTlsDialer();

end.
