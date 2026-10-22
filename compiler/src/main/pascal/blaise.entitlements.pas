{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.entitlements;

(* macOS code-signing entitlements for the internal ad-hoc signer
  (blaise.machowriter).

  A signed binary carries its entitlements twice: the XML property list
  verbatim (CSSLOT_ENTITLEMENTS) and the same dictionary DER-encoded
  (CSSLOT_DER_ENTITLEMENTS), which current macOS reads.  This unit parses
  the XML plist subset entitlements use and produces the DER form exactly
  as Apple's codesign does:

    [APPLICATION 16] {
      INTEGER 1                        -- version
      [CONTEXT 16] {                   -- the dictionary
        SEQUENCE { UTF8String key, value } ...   -- sorted bytewise by key
      }
    }

  with values encoded as BOOLEAN (true / false), UTF8String (string),
  INTEGER (integer, minimal two's complement), SEQUENCE (array) and a
  nested [CONTEXT 16] dictionary (dict).  <data>, <date> and <real> have no
  use in entitlements and are rejected rather than guessed at. *)

interface

uses
  SysUtils;

type
  EEntitlements = class(Exception);

{ The DER encoding of the entitlements plist APlistXml.  Raises
  EEntitlements on malformed XML or an unsupported value type. }
function EntitlementsDer(const APlistXml: string): string;

{ The plist a --debug-opdf build is signed with: get-task-allow, the
  target's consent to a debugger taking its task port.  Xcode signs Debug
  builds the same way.  It is only required under the hardened runtime,
  which Blaise does not enable yet, so today it is a no-op kept ready. }
function DebugEntitlementsPlist: string;

implementation

uses
  uStrCompat;

type
  { A minimal pull tokenizer over the plist XML: tags and the text between
    them, with the prolog, DOCTYPE and comments skipped. }
  TPlistReader = class
  private
    FSrc: string;
    FPos: Integer;
    procedure SkipSpace;
  public
    constructor Create(const ASrc: string);
    { The next tag's name ('dict', '/dict', 'true/', ...); '' at the end.
      Prolog, DOCTYPE and comment tags are skipped. }
    function NextTag: string;
    { The raw text up to the next '<', entities decoded. }
    function ReadText: string;
    procedure Expect(const ATag: string);
  end;

{ The five predefined XML entities; any other '&' is an error. }
function DecodeEntities(const ARaw: string): string;
var
  I, J: Integer;
  Ent: string;
begin
  Result := '';
  I := 0;
  while I < Length(ARaw) do
  begin
    if StrAt(ARaw, I) <> Ord('&') then
    begin
      Result := Result + Chr(StrAt(ARaw, I));
      Inc(I);
      Continue;
    end;
    J := I;
    while (J < Length(ARaw)) and (StrAt(ARaw, J) <> Ord(';')) do
      Inc(J);
    Ent := Copy(ARaw, I, J - I + 1);
    if Ent = '&amp;' then Result := Result + '&'
    else if Ent = '&lt;' then Result := Result + '<'
    else if Ent = '&gt;' then Result := Result + '>'
    else if Ent = '&quot;' then Result := Result + '"'
    else if Ent = '&apos;' then Result := Result + ''''
    else
      raise EEntitlements.Create('entitlements: unsupported entity ''' +
        Ent + '''');
    I := J + 1;
  end;
end;

constructor TPlistReader.Create(const ASrc: string);
begin
  FSrc := ASrc;
  FPos := 0;
end;

procedure TPlistReader.SkipSpace;
begin
  while (FPos < Length(FSrc)) and (StrAt(FSrc, FPos) <= 32) do
    Inc(FPos);
end;

function TPlistReader.NextTag: string;
var
  Start: Integer;
  Name: string;
  I: Integer;
begin
  while True do
  begin
    SkipSpace();
    if FPos >= Length(FSrc) then
      Exit('');
    if StrAt(FSrc, FPos) <> Ord('<') then
      raise EEntitlements.Create('entitlements: unexpected text at offset ' +
        IntToStr(FPos));
    if Copy(FSrc, FPos, 4) = '<!--' then
    begin
      I := Pos('-->', Copy(FSrc, FPos, Length(FSrc) - FPos));
      if I < 0 then
        raise EEntitlements.Create('entitlements: unterminated comment');
      FPos := FPos + I + 3;
      Continue;
    end;
    Start := FPos + 1;
    while (FPos < Length(FSrc)) and (StrAt(FSrc, FPos) <> Ord('>')) do
      Inc(FPos);
    if FPos >= Length(FSrc) then
      raise EEntitlements.Create('entitlements: unterminated tag');
    Name := Copy(FSrc, Start, FPos - Start);
    Inc(FPos);  { past '>' }
    if (Length(Name) > 0) and ((StrAt(Name, 0) = Ord('?')) or
       (StrAt(Name, 0) = Ord('!'))) then
      Continue;  { <?xml ...?>, <!DOCTYPE ...> }
    { drop attributes: <plist version="1.0"> }
    I := Pos(' ', Name);
    if I >= 0 then
    begin
      if StrAt(Name, Length(Name) - 1) = Ord('/') then
        Name := Copy(Name, 0, I) + '/'
      else
        Name := Copy(Name, 0, I);
    end;
    Exit(Name);
  end;
end;

function TPlistReader.ReadText: string;
var
  Start: Integer;
  Raw: string;
begin
  Start := FPos;
  while (FPos < Length(FSrc)) and (StrAt(FSrc, FPos) <> Ord('<')) do
    Inc(FPos);
  Raw := Copy(FSrc, Start, FPos - Start);
  Result := DecodeEntities(Raw);
end;

procedure TPlistReader.Expect(const ATag: string);
var
  T: string;
begin
  T := NextTag();
  if T <> ATag then
    raise EEntitlements.Create('entitlements: expected <' + ATag +
      '> but found <' + T + '>');
end;

{ ---- DER ---- }

function DerLength(ALen: Integer): string;
begin
  if ALen < 128 then
    Result := Chr(ALen)
  else if ALen < 256 then
    Result := Chr($81) + Chr(ALen)
  else if ALen < 65536 then
    Result := Chr($82) + Chr(ALen shr 8) + Chr(ALen and $FF)
  else
    Result := Chr($83) + Chr(ALen shr 16) + Chr((ALen shr 8) and $FF) +
      Chr(ALen and $FF);
end;

function DerTlv(ATag: Integer; const AContent: string): string;
begin
  Result := Chr(ATag) + DerLength(Length(AContent)) + AContent;
end;

function DerInteger(AValue: Int64): string;
var
  Bytes: string;
  K: Integer;
begin
  { minimal two's complement, big-endian: the eight bytes, then drop a
    leading byte while it only repeats the next byte's sign }
  Bytes := '';
  for K := 7 downto 0 do
    Bytes := Bytes + Chr(Integer((AValue shr (8 * K)) and $FF));
  while (Length(Bytes) > 1) and
        (((StrAt(Bytes, 0) = 0) and (StrAt(Bytes, 1) < $80)) or
         ((StrAt(Bytes, 0) = $FF) and (StrAt(Bytes, 1) >= $80))) do
    Bytes := Copy(Bytes, 1, Length(Bytes) - 1);
  Result := DerTlv($02, Bytes);
end;

{ True when A sorts before B, comparing bytes. }
function ByteLess(const A, B: string): Boolean;
var
  I, N: Integer;
begin
  N := Length(A);
  if Length(B) < N then
    N := Length(B);
  for I := 0 to N - 1 do
    if StrAt(A, I) <> StrAt(B, I) then
      Exit(StrAt(A, I) < StrAt(B, I));
  Result := Length(A) < Length(B);
end;

function ReadValue(AReader: TPlistReader; const ATag: string): string; forward;

{ A dictionary whose opening <dict> has been read. }
function ReadDict(AReader: TPlistReader): string;
var
  Keys, Vals: array of string;
  N, I, J: Integer;
  T, K, V: string;
begin
  N := 0;
  while True do
  begin
    T := AReader.NextTag();
    if T = '/dict' then
      Break;
    if T <> 'key' then
      raise EEntitlements.Create('entitlements: expected <key> in <dict> ' +
        'but found <' + T + '>');
    K := AReader.ReadText();
    AReader.Expect('/key');
    V := ReadValue(AReader, AReader.NextTag());
    SetLength(Keys, N + 1);
    SetLength(Vals, N + 1);
    { insertion by byte order: codesign emits the entries sorted }
    I := N;
    while (I > 0) and ByteLess(K, Keys[I - 1]) do
    begin
      Keys[I] := Keys[I - 1];
      Vals[I] := Vals[I - 1];
      Dec(I);
    end;
    Keys[I] := K;
    Vals[I] := V;
    Inc(N);
  end;
  Result := '';
  for J := 0 to N - 1 do
    Result := Result + DerTlv($30, DerTlv($0C, Keys[J]) + Vals[J]);
  Result := DerTlv($B0, Result);
end;

function ReadValue(AReader: TPlistReader; const ATag: string): string;
var
  Text, T, Items: string;
begin
  if ATag = 'true/' then
    Exit(DerTlv($01, Chr($FF)));
  if ATag = 'false/' then
    Exit(DerTlv($01, Chr(0)));
  if ATag = 'string/' then
    Exit(DerTlv($0C, ''));
  if ATag = 'string' then
  begin
    Text := AReader.ReadText();
    AReader.Expect('/string');
    Exit(DerTlv($0C, Text));
  end;
  if ATag = 'integer' then
  begin
    Text := Trim(AReader.ReadText());
    AReader.Expect('/integer');
    try
      Exit(DerInteger(StrToInt64(Text)));
    except
      on E: Exception do
        raise EEntitlements.Create('entitlements: bad <integer> ''' + Text +
          '''');
    end;
  end;
  if ATag = 'array/' then
    Exit(DerTlv($30, ''));
  if ATag = 'array' then
  begin
    Items := '';
    while True do
    begin
      T := AReader.NextTag();
      if T = '/array' then
        Break;
      Items := Items + ReadValue(AReader, T);
    end;
    Exit(DerTlv($30, Items));
  end;
  if ATag = 'dict/' then
    Exit(DerTlv($B0, ''));
  if ATag = 'dict' then
    Exit(ReadDict(AReader));
  raise EEntitlements.Create('entitlements: unsupported plist value <' +
    ATag + '> (supported: true, false, string, integer, array, dict)');
end;

function EntitlementsDer(const APlistXml: string): string;
var
  Reader: TPlistReader;
  Dict: string;
begin
  Reader := TPlistReader.Create(APlistXml);
  try
    Reader.Expect('plist');
    Reader.Expect('dict');
    Dict := ReadDict(Reader);
    Reader.Expect('/plist');
    if Reader.NextTag() <> '' then
      raise EEntitlements.Create('entitlements: text after </plist>');
  finally
    Reader.Free();
  end;
  Result := DerTlv($70, DerInteger(1) + Dict);
end;

function DebugEntitlementsPlist: string;
begin
  Result :=
    '<?xml version="1.0" encoding="UTF-8"?>' + #10 +
    '<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" ' +
    '"http://www.apple.com/DTDs/PropertyList-1.0.dtd">' + #10 +
    '<plist version="1.0">' + #10 +
    '<dict>' + #10 +
    #9'<key>com.apple.security.get-task-allow</key>' + #10 +
    #9'<true/>' + #10 +
    '</dict>' + #10 +
    '</plist>' + #10;
end;

end.
