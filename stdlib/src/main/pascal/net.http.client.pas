{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Http.Client;

// L5 of the fiber runtime (docs/async-networking-design.adoc, L5 catalogue):
// an HTTP/1.1 client on the fiber runtime.  THttpClient.Get/Post/Request dial
// via Net.Tcp (http), send the request line + headers (Host from the URI,
// Content-Length for a body) + body, then read the status line, headers and
// body.
//
// HTTP/1.1 features implemented:
//   * Host header + absolute-URL dialling via Net.Uri.
//   * request + response bodies via Content-Length.
//   * chunked transfer-encoding decode on responses.
//   * keep-alive connection reuse: a small per-client pool keyed by
//     scheme:host:port keeps one idle socket per origin, so repeated requests to
//     the same origin reuse the connection (unless the server says Connection:
//     close).
//   * redirect following (301/302/303/307/308) up to MaxRedirects, re-dialling
//     when the redirect target changes origin.  303 (and 301/302 for POST, per
//     common browser behaviour) downgrade the follow-up to GET.
//
// FIBER-NATIVE: the Read/Write inherited from Net.Tcp/async.io park the calling
// fiber under a running scheduler and fall back to blocking calls otherwise, so
// the same client code works in a fiber and in a plain program.
//
// https: an https URL dials TLS through an installable dialer hook
// (GHttpTlsDialer) that yields an IHttpTlsStream (Read/Write/Close/Closed).  The
// encrypted stream is driven through the same buffered read/write path as
// plaintext by wrapping it in a THttpConn transport.
//
// DECOUPLING FROM libssl: this unit does NOT `uses Net.Tls` — that would force
// libssl (and `--linker external`) onto EVERY consumer of the plaintext client,
// including the internally-linked stdlib test build.  Instead the concrete TLS
// binding lives in the opt-in unit Net.Http.Client.Tls, which a program that
// wants https `uses` to install GHttpTlsDialer.  Without that unit, an https
// request fails cleanly (returns nil) rather than dragging in libssl.  A program
// that issues https requests MUST therefore `uses Net.Http.Client.Tls` and be
// built with `--backend native --linker external`; plaintext http needs neither.
//
// TRANSPORT ABSTRACTION: THttpConn wraps EITHER a plaintext TTcpConn OR an
// IHttpTlsStream and presents a single buffered read/write surface
// (Read/Write/ReadLine/ReadFull/Unread/Close/Closed).  The response readers and
// the request writer operate on THttpConn, so exactly one code path serves both
// schemes.  The keep-alive pool stores THttpConn, and because the pool key
// includes the scheme, https (scheme:host:443) and plaintext (scheme:host:80)
// origins pool separately.  Verification can be relaxed per-client via the
// InsecureSkipVerify property (loud opt-out) and a private CA pinned via
// TrustCaFile; both are passed to the installed dialer.
//
// Blaise strings are 0-based; Pos/PosEx return -1 when not found.

interface

uses
  SysUtils, StrUtils, Generics.Collections, Net.Uri, Net.Tcp;

const
  { Default cap on redirect chasing before Request gives up. }
  DEFAULT_MAX_REDIRECTS = 5;

type
  { The minimal encrypted-stream surface the client needs from a TLS provider.
    Net.Http.Client.Tls adapts Net.Tls's TTlsStream to this interface, so this
    unit never references libssl-bound types directly.  Read returns '' on
    EOF/close/error; Write returns True on full write; Close is idempotent. }
  IHttpTlsStream = interface
    function Read(AMaxBytes: Int): string;
    function Write(const AData: string): Boolean;
    procedure Close;
    function IsClosed: Boolean;
  end;

  { Installable TLS dialer.  Dial AHost:APort, completing a client TLS handshake
    (SNI = AHost).  AVerify enables peer verification (True by default); ACaFile,
    when non-empty, pins extra trusted CA cert(s).  Returns a connected stream or
    nil on failure.  Net.Http.Client.Tls installs a concrete subclass backed by
    TTlsClient.  (A dialer OBJECT rather than a proc-var: the native backend
    supports method-call-returning-interface into a local, but not a
    proc-var-call-returning-interface — see the workaround note in TakeConn.) }
  THttpTlsDialer = class
  public
    function Dial(const AHost: string; APort: UInt16; AVerify: Boolean;
      const ACaFile: string): IHttpTlsStream; virtual; abstract;
  end;

  { Transport abstraction for the client's read/write path.  A THttpConn owns
    EITHER a plaintext TTcpConn OR an IHttpTlsStream (exactly one is set) and
    presents a single buffered read/write surface used by the response readers
    and request writer.  A small pushback buffer (FBuf) supports Unread and lets
    ReadLine / ReadFull sit over the raw transport Read regardless of scheme. }
  THttpConn = class
  private
    FTcp: TTcpConn;             { owned when non-nil (plaintext) }
    FTls: IHttpTlsStream;       { held when non-nil (https) }
    FBuf: string;           { pushed-back / over-read bytes, consumed first }
    FClosed: Boolean;
    { Pull up to AMaxBytes straight from the underlying transport. }
    function RawRead(AMaxBytes: Int): string;
  public
    { Wrap a plaintext connection (takes ownership). }
    constructor CreateTcp(ATcp: TTcpConn);
    { Wrap a TLS stream. }
    constructor CreateTls(ATls: IHttpTlsStream);
    destructor Destroy; override;

    { Read up to AMaxBytes ('' on EOF/close).  Serves the pushback buffer first. }
    function Read(AMaxBytes: Int): string;
    { Read exactly ACount bytes (fewer only on premature EOF). }
    function ReadFull(ACount: Int): string;
    { Read one CRLF/LF-terminated line (terminator stripped) into ALine; False on
      EOF with no data. }
    function ReadLine(out ALine: string): Boolean;
    { Push AData back so the next Read/ReadLine/ReadFull sees it first. }
    procedure Unread(const AData: string);
    { Write all of AData. }
    function Write(const AData: string): Boolean;
    { Close the underlying transport.  Idempotent. }
    procedure Close;
    { True once closed or the transport reports closed. }
    function IsClosed: Boolean;
  end;

  { A parsed HTTP response.  Owns its header map; Body holds the fully decoded
    entity body (chunked responses are reassembled).  Header names are stored
    lower-cased for case-insensitive lookup via Header(). }
  THttpClientResponse = class
  private
    FStatus: Int;
    FStatusText: string;
    FBody: string;
    FHeaders: TOrderedDictionary<string, string>;
    FKeepAlive: Boolean;
  public
    constructor Create;
    destructor Destroy; override;
    { Value of header AName (any case), or '' if absent. }
    function Header(const AName: string): string;
    function HasHeader(const AName: string): Boolean;
    property Status: Int read FStatus write FStatus;
    property StatusText: string read FStatusText write FStatusText;
    property Body: string read FBody write FBody;
    property Headers: TOrderedDictionary<string, string> read FHeaders;
    property KeepAlive: Boolean read FKeepAlive write FKeepAlive;
  end;

  { An HTTP/1.1 client.  A single THttpClient owns a per-origin keep-alive pool;
    reuse one client for repeated requests to the same host to benefit from
    connection reuse.  Not safe to share across fibers concurrently (each fiber
    should own its client, or serialise access). }
  THttpClient = class
  private
    FPool: TOrderedDictionary<string, THttpConn>;  { scheme:host:port -> idle conn }
    FMaxRedirects: Int;
    FInsecureSkipVerify: Boolean;                  { loud opt-out of TLS verify }
    FTrustCaFile: string;                          { pinned private CA (PEM), or '' }
    function PoolKey(AUri: TUri): string;
    function TakeConn(AUri: TUri): THttpConn;
    procedure ReturnConn(const AKey: string; AConn: THttpConn);
    function DoRequest(const AMethod: string; AUri: TUri;
      AHeaders: TList<string>; const ABody: string): THttpClientResponse;
  public
    constructor Create;
    destructor Destroy; override;

    { GET AUrl, following redirects. }
    function Get(const AUrl: string): THttpClientResponse;

    { POST ABody (with AContentType) to AUrl, following redirects. }
    function Post(const AUrl, ABody, AContentType: string): THttpClientResponse;

    { General request.  AMethod is the verb; AHeaders may be nil (extra request
      headers as 'Name: Value' lines); ABody is the request entity ('' for
      none).  Follows redirects up to MaxRedirects. }
    function Request(const AMethod, AUrl: string; AHeaders: TList<string>;
      const ABody: string): THttpClientResponse;

    property MaxRedirects: Int read FMaxRedirects write FMaxRedirects;

    { When True, https requests skip peer certificate verification (dev/self-
      signed use).  Default False — verification is ON, the security default.
      A loud, explicit opt-out. }
    property InsecureSkipVerify: Boolean read FInsecureSkipVerify write FInsecureSkipVerify;

    { PEM file of extra trusted CA certificate(s) for https verification.  When
      set, verify=True can succeed against a private/self-signed CA without
      disabling verification. }
    property TrustCaFile: string read FTrustCaFile write FTrustCaFile;
  end;

{ Parse a raw HTTP response (status line + headers + a Content-Length or
  read-to-EOF body already present) into a THttpClientResponse.  Chunked
  bodies are NOT decoded here (DoRequest handles transfer framing).  Exposed
  for testing. }
function ParseResponse(const ARaw: string): THttpClientResponse;

{ Install/replace the process-wide TLS dialer.  Net.Http.Client.Tls calls this
  from its initialisation.  A setter (rather than a directly-assignable global)
  because the native backend duplicates the definition of a cross-unit global
  written from another unit; writing it inside its declaring unit avoids that. }
procedure SetHttpTlsDialer(ADialer: THttpTlsDialer);

{ The currently installed TLS dialer, or nil if none (https then fails cleanly). }
function HttpTlsDialer: THttpTlsDialer;

implementation

var
  { Installed TLS dialer instance.  nil until Net.Http.Client.Tls (or an
    application) sets it via SetHttpTlsDialer; while nil, https requests fail
    cleanly (Request returns nil) instead of forcing libssl onto plaintext
    consumers. }
  GHttpTlsDialer: THttpTlsDialer;

procedure SetHttpTlsDialer(ADialer: THttpTlsDialer);
begin
  GHttpTlsDialer := ADialer;
end;

function HttpTlsDialer: THttpTlsDialer;
begin
  Result := GHttpTlsDialer;
end;

{ ---- small helpers -------------------------------------------------------- }

function AsciiLower(const S: string): string;
begin
  Result := LowerCase(S);
end;

{ Parse a decimal integer; return ADefault when empty or non-numeric. }
function ParseDecimalDef(const S: string; ADefault: Int): Int;
var
  I, N, V: Int;
  T: string;
  B: Byte;
begin
  T := Trim(S);
  N := Length(T);
  if N = 0 then
    Exit(ADefault);
  V := 0;
  for I := 0 to N - 1 do
  begin
    B := Byte(T[I]);
    if (B < 48) or (B > 57) then
      Exit(ADefault);
    V := V * 10 + (B - 48);
  end;
  Result := V;
end;

{ Parse a hex chunk-size line (may carry ';ext'); return -1 on parse error. }
function ParseHexSize(const S: string): Int;
var
  I, N, V, D: Int;
  B: Byte;
  T: string;
begin
  N := PosEx(';', S, 0);
  if N >= 0 then
    T := Copy(S, 0, N)
  else
    T := S;
  T := Trim(T);
  if T = '' then
    Exit(-1);
  V := 0;
  N := Length(T);
  for I := 0 to N - 1 do
  begin
    B := Byte(T[I]);
    if (B >= 48) and (B <= 57) then D := B - 48
    else if (B >= 65) and (B <= 70) then D := B - 55
    else if (B >= 97) and (B <= 102) then D := B - 87
    else Exit(-1);
    V := V * 16 + D;
  end;
  Result := V;
end;

{ Split S on LF, stripping a trailing CR from each line. Caller owns the list. }
function SplitLinesCRLF(const S: string): TList<string>;
var
  I, N, Start: Int;
  Line: string;
begin
  Result := TList<string>.Create();
  N := Length(S);
  Start := 0;
  I := 0;
  while I < N do
  begin
    if Byte(S[I]) = 10 then
    begin
      Line := Copy(S, Start, I - Start);
      if (Length(Line) > 0) and (Byte(Line[Length(Line) - 1]) = 13) then
        Line := Copy(Line, 0, Length(Line) - 1);
      Result.Add(Line);
      Start := I + 1;
    end;
    I := I + 1;
  end;
  Line := Copy(S, Start, N - Start);
  if (Length(Line) > 0) and (Byte(Line[Length(Line) - 1]) = 13) then
    Line := Copy(Line, 0, Length(Line) - 1);
  Result.Add(Line);
end;

{ Resolve a Location header (absolute or path-absolute) against the base URL.
  Absolute (scheme://...) is returned as-is; a leading '/' path replaces the
  base's path; anything else is treated as origin-relative to the base. }
function ResolveLocation(const ABaseUrl, ALocation: string): string;
var
  Base: TUri;
begin
  if (PosEx('://', ALocation, 0) >= 0) then
    Exit(ALocation);
  Base := TUri.Parse(ABaseUrl);
  try
    if (Length(ALocation) > 0) and (Byte(ALocation[0]) = 47) then   { '/' }
      Result := Base.Scheme + '://' + Base.Host + ':' + IntToStr(Base.Port) + ALocation
    else
      Result := Base.Scheme + '://' + Base.Host + ':' + IntToStr(Base.Port) + '/' + ALocation;
  finally
    Base.Free();
  end;
end;

{ ---- THttpConn (transport abstraction) ------------------------------------ }

constructor THttpConn.CreateTcp(ATcp: TTcpConn);
begin
  FTcp := ATcp;
  FTls := nil;
  FBuf := '';
  FClosed := False;
end;

constructor THttpConn.CreateTls(ATls: IHttpTlsStream);
begin
  FTcp := nil;
  FTls := ATls;
  FBuf := '';
  FClosed := False;
end;

destructor THttpConn.Destroy;
begin
  Self.Close();
  if FTcp <> nil then
  begin
    FTcp.Free();
    FTcp := nil;
  end;
  FTls := nil;   { interface: released by ARC }
  inherited Destroy();
end;

function THttpConn.RawRead(AMaxBytes: Int): string;
begin
  if FTls <> nil then
    Result := FTls.Read(AMaxBytes)
  else if FTcp <> nil then
    Result := FTcp.Read(AMaxBytes)
  else
    Result := '';
end;

function THttpConn.Read(AMaxBytes: Int): string;
var
  Take: Int;
begin
  if FBuf <> '' then
  begin
    Take := AMaxBytes;
    if Take > Length(FBuf) then
      Take := Length(FBuf);
    Result := Copy(FBuf, 0, Take);
    FBuf := Copy(FBuf, Take, Length(FBuf) - Take);
    Exit;
  end;
  Result := Self.RawRead(AMaxBytes);
end;

function THttpConn.ReadFull(ACount: Int): string;
var
  SB: TStringBuilder;
  Chunk: string;
  Got: Int;
begin
  SB := TStringBuilder.Create();
  Got := 0;
  while Got < ACount do
  begin
    Chunk := Self.Read(ACount - Got);
    if Chunk = '' then
      Break;
    SB.Append(Chunk);
    Got := Got + Length(Chunk);
  end;
  Result := SB.ToString();
  SB.Free();
end;

function THttpConn.ReadLine(out ALine: string): Boolean;
var
  SB: TStringBuilder;
  Acc, Chunk: string;
  Nl: Int;
begin
  SB := TStringBuilder.Create();
  ALine := '';
  Result := False;
  while True do
  begin
    Acc := SB.ToString();
    Nl := PosEx(#10, Acc, 0);
    if Nl >= 0 then
    begin
      ALine := Copy(Acc, 0, Nl);
      if (Length(ALine) > 0) and (Byte(ALine[Length(ALine) - 1]) = 13) then
        ALine := Copy(ALine, 0, Length(ALine) - 1);
      Self.Unread(Copy(Acc, Nl + 1, Length(Acc) - Nl - 1));
      Result := True;
      Break;
    end;
    Chunk := Self.Read(4096);
    if Chunk = '' then
    begin
      { EOF: return whatever partial line accumulated (True if any bytes). }
      ALine := Acc;
      Result := Length(Acc) > 0;
      Break;
    end;
    SB.Append(Chunk);
  end;
  SB.Free();
end;

procedure THttpConn.Unread(const AData: string);
begin
  if AData = '' then
    Exit;
  FBuf := AData + FBuf;
end;

function THttpConn.Write(const AData: string): Boolean;
begin
  if FTls <> nil then
    Result := FTls.Write(AData)
  else if FTcp <> nil then
    Result := FTcp.Write(AData)
  else
    Result := False;
end;

procedure THttpConn.Close;
begin
  if FClosed then
    Exit;
  FClosed := True;
  if FTls <> nil then
    FTls.Close();
  if FTcp <> nil then
    FTcp.Close();
end;

function THttpConn.IsClosed: Boolean;
begin
  if FClosed then
    Exit(True);
  if FTls <> nil then
    Exit(FTls.IsClosed());
  if FTcp <> nil then
    Exit(FTcp.Closed);
  Result := True;
end;

{ ---- THttpClientResponse -------------------------------------------------- }

constructor THttpClientResponse.Create;
begin
  FStatus := 0;
  FStatusText := '';
  FBody := '';
  FHeaders := TOrderedDictionary<string, string>.Create();
  FKeepAlive := False;
end;

destructor THttpClientResponse.Destroy;
begin
  FHeaders.Free();
  inherited Destroy();
end;

function THttpClientResponse.Header(const AName: string): string;
begin
  if not FHeaders.TryGetValue(AsciiLower(AName), Result) then
    Result := '';
end;

function THttpClientResponse.HasHeader(const AName: string): Boolean;
begin
  Result := FHeaders.ContainsKey(AsciiLower(AName));
end;

{ ---- response head parsing ------------------------------------------------ }

{ Parse the status line + header block (ARawHead excludes the CRLFCRLF).  Fills
  Status/StatusText/Headers/KeepAlive on AResp.  Header names are lower-cased. }
procedure ParseHead(const ARawHead: string; AResp: THttpClientResponse);
var
  Lines: TList<string>;
  StatusLine, Line, Name, Val, LName: string;
  I, Sp1, Sp2, Colon: Int;
begin
  Lines := SplitLinesCRLF(ARawHead);
  if Lines.Count = 0 then
  begin
    Lines.Free();
    Exit;
  end;
  StatusLine := Lines.Get(0);
  Sp1 := PosEx(' ', StatusLine, 0);
  if Sp1 >= 0 then
  begin
    Sp2 := PosEx(' ', StatusLine, Sp1 + 1);
    if Sp2 > Sp1 then
    begin
      AResp.Status := ParseDecimalDef(Copy(StatusLine, Sp1 + 1, Sp2 - Sp1 - 1), 0);
      AResp.StatusText := Copy(StatusLine, Sp2 + 1, Length(StatusLine) - Sp2 - 1);
    end
    else
      AResp.Status := ParseDecimalDef(Copy(StatusLine, Sp1 + 1, Length(StatusLine) - Sp1 - 1), 0);
  end;

  AResp.KeepAlive := True;    { HTTP/1.1 default }
  for I := 1 to Lines.Count - 1 do
  begin
    Line := Lines.Get(I);
    if Line = '' then
      Break;
    Colon := PosEx(':', Line, 0);
    if Colon < 0 then
      Continue;
    Name := Trim(Copy(Line, 0, Colon));
    Val := Trim(Copy(Line, Colon + 1, Length(Line) - Colon - 1));
    LName := AsciiLower(Name);
    if not AResp.Headers.ContainsKey(LName) then
      AResp.Headers.Add(LName, Val);
    if LName = 'connection' then
      if ContainsStr(AsciiLower(Val), 'close') then
        AResp.KeepAlive := False;
  end;
  Lines.Free();
end;

function ParseResponse(const ARaw: string): THttpClientResponse;
var
  Sep, HeadLen: Int;
  Head: string;
  Resp: THttpClientResponse;
begin
  Resp := THttpClientResponse.Create();
  Sep := PosEx(#13#10#13#10, ARaw, 0);
  if Sep < 0 then
  begin
    ParseHead(ARaw, Resp);
    Result := Resp;
    Exit;
  end;
  HeadLen := Sep + 4;
  Head := Copy(ARaw, 0, Sep);
  ParseHead(Head, Resp);
  Resp.Body := Copy(ARaw, HeadLen, Length(ARaw) - HeadLen);
  Result := Resp;
end;

{ ---- body readers --------------------------------------------------------- }

{ Read the status line + header block from AConn.  Returns the head text (minus
  the CRLFCRLF); any over-read body bytes are pushed back onto AConn. }
function ReadResponseHead(AConn: THttpConn; out AHead: string): Boolean;
var
  SB: TStringBuilder;
  Chunk, Acc: string;
  Sep: Int;
begin
  SB := TStringBuilder.Create();
  while True do
  begin
    Acc := SB.ToString();
    if PosEx(#13#10#13#10, Acc, 0) >= 0 then
      Break;
    Chunk := AConn.Read(4096);
    if Chunk = '' then
      Break;
    SB.Append(Chunk);
  end;
  Acc := SB.ToString();
  SB.Free();
  Sep := PosEx(#13#10#13#10, Acc, 0);
  if Sep < 0 then
  begin
    AHead := '';
    Exit(False);
  end;
  AHead := Copy(Acc, 0, Sep);
  AConn.Unread(Copy(Acc, Sep + 4, Length(Acc) - Sep - 4));
  Result := True;
end;

{ Read a chunked body: <hexsize CRLF> <data CRLF> until a 0-size chunk. }
function ReadBodyChunked(AConn: THttpConn): string;
var
  SB: TStringBuilder;
  SizeLine, Data, Crlf: string;
  Size: Int;
begin
  SB := TStringBuilder.Create();
  while True do
  begin
    if not AConn.ReadLine(SizeLine) then
      Break;
    Size := ParseHexSize(SizeLine);
    if Size < 0 then
      Break;
    if Size = 0 then
    begin
      while AConn.ReadLine(Crlf) do
        if Crlf = '' then
          Break;
      Break;
    end;
    Data := AConn.ReadFull(Size);
    SB.Append(Data);
    AConn.ReadLine(Crlf);     { trailing CRLF after the chunk data }
  end;
  Result := SB.ToString();
  SB.Free();
end;

function ReadBodyToEof(AConn: THttpConn): string;
var
  SB: TStringBuilder;
  Chunk: string;
begin
  SB := TStringBuilder.Create();
  while True do
  begin
    Chunk := AConn.Read(4096);
    if Chunk = '' then
      Break;
    SB.Append(Chunk);
  end;
  Result := SB.ToString();
  SB.Free();
end;

{ ---- request-head building ------------------------------------------------ }

function BuildRequestHead(const AMethod, ATarget, AHost: string;
  APort, ADefaultPort: Int; AHeaders: TList<string>;
  const ABody: string): string;
var
  SB: TStringBuilder;
  HostHdr: string;
  I: Int;
begin
  SB := TStringBuilder.Create();
  SB.Append(AMethod);
  SB.Append(' ');
  SB.Append(ATarget);
  SB.Append(' HTTP/1.1'#13#10);

  HostHdr := AHost;
  if (APort > 0) and (APort <> ADefaultPort) then
    HostHdr := HostHdr + ':' + IntToStr(APort);
  SB.Append('Host: ');
  SB.Append(HostHdr);
  SB.Append(#13#10);

  SB.Append('Connection: keep-alive'#13#10);

  if ABody <> '' then
  begin
    SB.Append('Content-Length: ');
    SB.Append(IntToStr(Length(ABody)));
    SB.Append(#13#10);
  end;

  if AHeaders <> nil then
    for I := 0 to AHeaders.Count - 1 do
    begin
      SB.Append(AHeaders.Get(I));
      SB.Append(#13#10);
    end;

  SB.Append(#13#10);
  Result := SB.ToString();
  SB.Free();
end;

{ ---- THttpClient ---------------------------------------------------------- }

constructor THttpClient.Create;
begin
  FPool := TOrderedDictionary<string, THttpConn>.Create();
  FMaxRedirects := DEFAULT_MAX_REDIRECTS;
  FInsecureSkipVerify := False;
  FTrustCaFile := '';
end;

destructor THttpClient.Destroy;
var
  I: Int;
  Conn: THttpConn;
begin
  for I := 0 to FPool.Count - 1 do
  begin
    Conn := FPool.Values[I];
    if Conn <> nil then
    begin
      Conn.Close();
      Conn.Free();
    end;
  end;
  FPool.Free();
  inherited Destroy();
end;

function THttpClient.PoolKey(AUri: TUri): string;
begin
  Result := AUri.Scheme + ':' + AUri.Host + ':' + IntToStr(AUri.Port);
end;

function THttpClient.TakeConn(AUri: TUri): THttpConn;
var
  Key: string;
  Conn: THttpConn;
  Cli: TTcpClient;
  Tcp: TTcpConn;
  Tls: IHttpTlsStream;
  Verify: Boolean;
begin
  Key := Self.PoolKey(AUri);
  if FPool.TryGetValue(Key, Conn) then
  begin
    FPool.Remove(Key);
    if (Conn <> nil) and (not Conn.IsClosed()) then
      Exit(Conn);
    if Conn <> nil then
    begin
      Conn.Close();
      Conn.Free();
    end;
  end;

  if AUri.Scheme = 'https' then
  begin
    { TLS dial via the installed dialer object: SNI = host, verify ON by default
      (loud opt-out via InsecureSkipVerify), optionally pinning a private CA.
      With no dialer installed (Net.Http.Client.Tls not used), fail cleanly.
      WORKAROUND: a method-call returning an interface into a local is fine on
      the native backend; a proc-var call is not — hence a dialer object. }
    if GHttpTlsDialer = nil then
      Exit(nil);
    Verify := not FInsecureSkipVerify;
    Tls := GHttpTlsDialer.Dial(AUri.Host, UInt16(AUri.Port), Verify, FTrustCaFile);
    if Tls = nil then
      Exit(nil);
    Result := THttpConn.CreateTls(Tls);
    Exit;
  end;

  Cli := TTcpClient.Create();
  Tcp := Cli.Connect(AUri.Host, UInt16(AUri.Port));
  Cli.Free();
  if Tcp = nil then
    Exit(nil);
  Result := THttpConn.CreateTcp(Tcp);
end;

procedure THttpClient.ReturnConn(const AKey: string; AConn: THttpConn);
var
  Old: THttpConn;
begin
  if (AConn = nil) or AConn.IsClosed() then
  begin
    if AConn <> nil then
      AConn.Free();
    Exit;
  end;
  if FPool.TryGetValue(AKey, Old) then
  begin
    if Old <> nil then
    begin
      Old.Close();
      Old.Free();
    end;
    FPool.Remove(AKey);
  end;
  FPool.Add(AKey, AConn);
end;

function THttpClient.DoRequest(const AMethod: string; AUri: TUri;
  AHeaders: TList<string>; const ABody: string): THttpClientResponse;
var
  Key, Head, Target, Te: string;
  Conn: THttpConn;
  Resp: THttpClientResponse;
  ContentLen: Int;
begin
  Result := nil;

  Key := Self.PoolKey(AUri);
  Conn := Self.TakeConn(AUri);
  if Conn = nil then
    Exit;

  Target := AUri.Path;
  if AUri.Query <> '' then
    Target := Target + '?' + AUri.Query;

  Head := BuildRequestHead(AMethod, Target, AUri.Host, AUri.Port,
    DefaultPortForScheme(AUri.Scheme), AHeaders, ABody);

  if not Conn.Write(Head) then
  begin
    Conn.Close();
    Conn.Free();
    Exit;
  end;
  if (ABody <> '') and (not Conn.Write(ABody)) then
  begin
    Conn.Close();
    Conn.Free();
    Exit;
  end;

  if not ReadResponseHead(Conn, Head) then
  begin
    Conn.Close();
    Conn.Free();
    Exit;
  end;

  Resp := ParseResponse(Head + #13#10#13#10);
  Resp.Body := '';

  Te := AsciiLower(Resp.Header('transfer-encoding'));
  if ContainsStr(Te, 'chunked') then
    Resp.Body := ReadBodyChunked(Conn)
  else if Resp.HasHeader('content-length') then
  begin
    ContentLen := ParseDecimalDef(Resp.Header('content-length'), 0);
    if ContentLen > 0 then
      Resp.Body := Conn.ReadFull(ContentLen);
  end
  else if (AMethod = 'HEAD') or (Resp.Status = 204) or (Resp.Status = 304) then
    Resp.Body := ''
  else if not Resp.KeepAlive then
    Resp.Body := ReadBodyToEof(Conn)
  else
    Resp.Body := '';

  if Resp.KeepAlive and (not Conn.IsClosed()) then
    Self.ReturnConn(Key, Conn)
  else
  begin
    Conn.Close();
    Conn.Free();
  end;

  Result := Resp;
end;

function THttpClient.Request(const AMethod, AUrl: string;
  AHeaders: TList<string>; const ABody: string): THttpClientResponse;
var
  Uri: TUri;
  Resp: THttpClientResponse;
  Method, CurUrl, Loc, Body: string;
  Redirects: Int;
begin
  Method := AMethod;
  CurUrl := AUrl;
  Body := ABody;
  Redirects := 0;
  Result := nil;

  while True do
  begin
    Uri := TUri.Parse(CurUrl);
    Resp := Self.DoRequest(Method, Uri, AHeaders, Body);
    Uri.Free();
    if Resp = nil then
      Exit(nil);

    if ((Resp.Status = 301) or (Resp.Status = 302) or (Resp.Status = 303) or
        (Resp.Status = 307) or (Resp.Status = 308)) and
       (Redirects < FMaxRedirects) then
    begin
      Loc := Resp.Header('location');
      if Loc <> '' then
      begin
        if (Resp.Status = 303) or
           (((Resp.Status = 301) or (Resp.Status = 302)) and (Method = 'POST')) then
        begin
          Method := 'GET';
          Body := '';
        end;
        CurUrl := ResolveLocation(CurUrl, Loc);
        Redirects := Redirects + 1;
        Resp.Free();
        Continue;
      end;
    end;

    Result := Resp;
    Exit;
  end;
end;

function THttpClient.Get(const AUrl: string): THttpClientResponse;
begin
  Result := Self.Request('GET', AUrl, nil, '');
end;

function THttpClient.Post(const AUrl, ABody, AContentType: string): THttpClientResponse;
var
  Hdrs: TList<string>;
begin
  Hdrs := TList<string>.Create();
  if AContentType <> '' then
    Hdrs.Add('Content-Type: ' + AContentType);
  Result := Self.Request('POST', AUrl, Hdrs, ABody);
  Hdrs.Free();
end;

end.
