{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Uri;

// L5 of the fiber runtime (docs/async-networking-design.adoc, L5 catalogue):
// a transport-agnostic URL/URI parser and builder.  Pure Pascal, no sockets --
// it is the foundation Net.Http.Client dials from, but it is broadly useful on
// its own.
//
// TUri.Parse decomposes a URL of the shape
//
//   scheme://[userinfo@]host[:port][/path][?query][#fragment]
//
// into its components, applying the scheme's default port when none is given
// (http=80, https=443), defaulting a missing path to '/', and exposing the
// query string as decoded name/value pairs (QueryParam).  ToString rebuilds a
// canonical URL from the components.
//
// EncodeComponent / DecodeComponent implement RFC-3986 percent-encoding of a
// single component (path segment, query value, ...): unreserved characters
// (A-Z a-z 0-9 - _ . ~) pass through, everything else is %XX-escaped.  Decode
// reverses %XX (either case) and, unlike a form decoder, leaves '+' as a
// literal '+' (application/x-www-form-urlencoded '+'->space is a query-string
// convention handled by the HTTP layer, not here).
//
// Blaise strings are 0-based; Pos/PosEx return -1 when not found, >= 0 for the
// index of the match.

interface

uses
  SysUtils, Generics.Collections, StrUtils;

type
  { A parsed URI.  Fields are populated by Parse; ToString reconstructs a URL
    from them.  The query string is additionally decoded into FParams on
    demand (QueryParam), keyed by the percent-decoded parameter name. }
  TUri = class
  private
    FScheme: string;
    FUserInfo: string;
    FHost: string;
    FPort: Int;
    FPath: string;
    FQuery: string;
    FFragment: string;
    FParams: TOrderedDictionary<string, string>;   { lazily built by EnsureParams }
    FParamsBuilt: Boolean;
    procedure EnsureParams;
  public
    constructor Create;
    destructor Destroy; override;

    { Parse AUrl into a fresh TUri (caller owns the result).  A malformed URL is
      parsed best-effort: missing components come back empty (or defaulted). }
    static function Parse(const AUrl: string): TUri;

    { Rebuild a canonical URL string from the components. }
    function ToString: string; override;

    { Decoded value of query parameter AName, or '' if absent.  A key present
      with no '=' yields ''. }
    function QueryParam(const AName: string): string;

    { True if AName appears in the query string (even valueless). }
    function HasQueryParam(const AName: string): Boolean;

    property Scheme: string read FScheme write FScheme;
    property UserInfo: string read FUserInfo write FUserInfo;
    property Host: string read FHost write FHost;
    property Port: Int read FPort write FPort;
    property Path: string read FPath write FPath;
    property Query: string read FQuery write FQuery;
    property Fragment: string read FFragment write FFragment;
  end;

{ Default TCP port for a scheme (lower-cased): http=80, https=443, ws=80,
  wss=443.  Returns 0 for an unknown scheme. }
function DefaultPortForScheme(const AScheme: string): Int;

{ RFC-3986 percent-encode a single URI component.  Unreserved characters
  (A-Z a-z 0-9 - _ . ~) pass through; every other byte becomes %XX (uppercase
  hex). }
function EncodeComponent(const S: string): string;

{ Reverse percent-encoding: %XX (either hex case) -> byte.  '+' is left as a
  literal '+' (see the unit header). }
function DecodeComponent(const S: string): string;

implementation

const
  HEX_UPPER = '0123456789ABCDEF';

{ ---- percent-encoding helpers -------------------------------------------- }

function IsUnreserved(AByte: Byte): Boolean;
begin
  Result :=
    ((AByte >= 65) and (AByte <= 90)) or    { A-Z }
    ((AByte >= 97) and (AByte <= 122)) or   { a-z }
    ((AByte >= 48) and (AByte <= 57)) or    { 0-9 }
    (AByte = 45) or                         { - }
    (AByte = 95) or                         { _ }
    (AByte = 46) or                         { . }
    (AByte = 126);                          { ~ }
end;

{ Parse a decimal port string; return ADefault when empty or non-numeric. }
function ParsePortDef(const S: string; ADefault: Int): Int;
var
  I, N, V: Int;
  B: Byte;
begin
  N := Length(S);
  if N = 0 then
    Exit(ADefault);
  V := 0;
  for I := 0 to N - 1 do
  begin
    B := Byte(S[I]);
    if (B < 48) or (B > 57) then
      Exit(ADefault);
    V := V * 10 + (B - 48);
  end;
  Result := V;
end;

function HexDigitVal(AByte: Byte): Int;
begin
  if (AByte >= 48) and (AByte <= 57) then
    Result := AByte - 48
  else if (AByte >= 65) and (AByte <= 70) then
    Result := AByte - 55
  else if (AByte >= 97) and (AByte <= 102) then
    Result := AByte - 87
  else
    Result := 0;
end;

function EncodeComponent(const S: string): string;
var
  SB: TStringBuilder;
  I: Int;
  B: Byte;
begin
  SB := TStringBuilder.Create();
  for I := 0 to Length(S) - 1 do
  begin
    B := Byte(S[I]);
    if IsUnreserved(B) then
      SB.AppendByte(B)
    else
    begin
      SB.AppendByte(37);                       { '%' }
      SB.AppendByte(Byte(HEX_UPPER[(B shr 4) and 15]));
      SB.AppendByte(Byte(HEX_UPPER[B and 15]));
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function DecodeComponent(const S: string): string;
var
  SB: TStringBuilder;
  I, N: Int;
  B: Byte;
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  I := 0;
  while I < N do
  begin
    B := Byte(S[I]);
    if (B = 37) and (I + 2 < N) then           { '%XX' }
    begin
      SB.AppendByte(HexDigitVal(Byte(S[I + 1])) * 16 + HexDigitVal(Byte(S[I + 2])));
      I := I + 3;
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

{ ---- scheme defaults ------------------------------------------------------ }

function DefaultPortForScheme(const AScheme: string): Int;
var
  S: string;
begin
  S := LowerCase(AScheme);
  if S = 'http' then
    Result := 80
  else if S = 'https' then
    Result := 443
  else if S = 'ws' then
    Result := 80
  else if S = 'wss' then
    Result := 443
  else
    Result := 0;
end;

{ ---- TUri ----------------------------------------------------------------- }

constructor TUri.Create;
begin
  FScheme := '';
  FUserInfo := '';
  FHost := '';
  FPort := 0;
  FPath := '';
  FQuery := '';
  FFragment := '';
  FParams := TOrderedDictionary<string, string>.Create();
  FParamsBuilt := False;
end;

destructor TUri.Destroy;
begin
  FParams.Free();
  inherited Destroy();
end;

static function TUri.Parse(const AUrl: string): TUri;
var
  U: TUri;
  Rest, Authority, HostPort, PortStr: string;
  SchemeSep, Slash, Q, Hash, At, Colon: Int;
begin
  U := TUri.Create();
  Rest := AUrl;

  { scheme:// }
  SchemeSep := PosEx('://', Rest, 0);
  if SchemeSep >= 0 then
  begin
    U.FScheme := LowerCase(Copy(Rest, 0, SchemeSep));
    Rest := Copy(Rest, SchemeSep + 3, Length(Rest) - SchemeSep - 3);
  end;

  { Split off #fragment first (it may follow the query). }
  Hash := PosEx('#', Rest, 0);
  if Hash >= 0 then
  begin
    U.FFragment := Copy(Rest, Hash + 1, Length(Rest) - Hash - 1);
    Rest := Copy(Rest, 0, Hash);
  end;

  { Split off ?query. }
  Q := PosEx('?', Rest, 0);
  if Q >= 0 then
  begin
    U.FQuery := Copy(Rest, Q + 1, Length(Rest) - Q - 1);
    Rest := Copy(Rest, 0, Q);
  end;

  { Rest is now authority + path.  The path starts at the first '/'. }
  Slash := PosEx('/', Rest, 0);
  if Slash >= 0 then
  begin
    Authority := Copy(Rest, 0, Slash);
    U.FPath := Copy(Rest, Slash, Length(Rest) - Slash);
  end
  else
  begin
    Authority := Rest;
    U.FPath := '';
  end;

  { Authority = [userinfo@]host[:port] }
  At := PosEx('@', Authority, 0);
  if At >= 0 then
  begin
    U.FUserInfo := Copy(Authority, 0, At);
    HostPort := Copy(Authority, At + 1, Length(Authority) - At - 1);
  end
  else
    HostPort := Authority;

  Colon := PosEx(':', HostPort, 0);
  if Colon >= 0 then
  begin
    U.FHost := Copy(HostPort, 0, Colon);
    PortStr := Copy(HostPort, Colon + 1, Length(HostPort) - Colon - 1);
    U.FPort := ParsePortDef(PortStr, DefaultPortForScheme(U.FScheme));
  end
  else
  begin
    U.FHost := HostPort;
    U.FPort := DefaultPortForScheme(U.FScheme);
  end;

  { A missing path defaults to '/'. }
  if U.FPath = '' then
    U.FPath := '/';

  Result := U;
end;

function TUri.ToString: string;
var
  S: string;
begin
  S := '';
  if FScheme <> '' then
    S := FScheme + '://';
  if FUserInfo <> '' then
    S := S + FUserInfo + '@';
  S := S + FHost;
  { Emit the port only when it differs from the scheme default (keeps the
    reconstruction canonical). }
  if (FPort > 0) and (FPort <> DefaultPortForScheme(FScheme)) then
    S := S + ':' + IntToStr(FPort);
  S := S + FPath;
  if FQuery <> '' then
    S := S + '?' + FQuery;
  if FFragment <> '' then
    S := S + '#' + FFragment;
  Result := S;
end;

procedure TUri.EnsureParams;
var
  Pairs: TList<string>;
  I, Eq, Start, N: Int;
  Pair, Key, Val: string;
  B: Byte;
begin
  if FParamsBuilt then
    Exit;
  FParamsBuilt := True;
  if FQuery = '' then
    Exit;

  { Split FQuery on '&' into pairs. }
  Pairs := TList<string>.Create();
  N := Length(FQuery);
  Start := 0;
  I := 0;
  while I < N do
  begin
    B := Byte(FQuery[I]);
    if B = 38 then                 { '&' }
    begin
      Pairs.Add(Copy(FQuery, Start, I - Start));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  Pairs.Add(Copy(FQuery, Start, N - Start));

  for I := 0 to Pairs.Count - 1 do
  begin
    Pair := Pairs.Get(I);
    if Pair = '' then
      Continue;
    Eq := PosEx('=', Pair, 0);
    if Eq < 0 then
    begin
      Key := DecodeComponent(Pair);
      Val := '';
    end
    else
    begin
      Key := DecodeComponent(Copy(Pair, 0, Eq));
      Val := DecodeComponent(Copy(Pair, Eq + 1, Length(Pair) - Eq - 1));
    end;
    if not FParams.ContainsKey(Key) then
      FParams.Add(Key, Val);
  end;
  Pairs.Free();
end;

function TUri.QueryParam(const AName: string): string;
begin
  Self.EnsureParams();
  if not FParams.TryGetValue(AName, Result) then
    Result := '';
end;

function TUri.HasQueryParam(const AName: string): Boolean;
begin
  Self.EnsureParams();
  Result := FParams.ContainsKey(AName);
end;

end.
