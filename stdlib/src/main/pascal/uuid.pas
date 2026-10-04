{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - RFC 4122 version-4 (random) UUID value type.

  TUuid is a 16-byte VALUE record holding an RFC 4122 UUID as two Int64
  halves (FMostSigBits / FLeastSigBits), mirroring java.util.UUID's internal
  layout.  This is deliberate: Blaise strings always heap-allocate (there is
  no small-string optimisation - see runtime.str.pas), so storing the 16
  bytes as a `string` would allocate on every construction, comparison and
  hash, defeating the point of a value-type record.  Two Int64 fields are
  genuinely zero-allocation.

  Randomness for RandomUuid comes from the kernel CSPRNG via getrandom(2)
  (Linux 3.17+, glibc 2.25+); no seeding and no PRNG state.

    TUuid.RandomUuid       -> a fresh random (v4) TUuid.
    TUuid.Parse(S)         -> TUuid from a canonical '8-4-4-4-12' string;
                              raises EUuidParse if S is not well-formed.
    TUuid.TryParse(S, U)   -> non-raising validate-and-parse; False if S is
                              not a well-formed canonical UUID (this is the
                              "is this a valid UUID" check).
    TUuid.FromBytes(Raw)   -> TUuid from the 16 raw bytes (as a string);
                              raises EUuidParse if Raw is not exactly 16 bytes.
    TUuid.Empty            -> the nil UUID (all bits zero).

  Instance methods: ToString (canonical lowercase text), ToBytes (the 16 raw
  bytes, for interop e.g. Base64Encode), CompareTo/Equals, GetHashCode,
  IsEmpty, Version (the RFC 4122 version nibble, 0 if unset).

  CompareTo deliberately does NOT mirror java.util.UUID.compareTo, which
  compares mostSigBits/leastSigBits as SIGNED longs - this gives the wrong
  128-bit ordering whenever the compared values' sign bits differ (a
  well-known UUID.compareTo footgun).  TUuid.CompareTo does genuine unsigned
  128-bit comparison instead, so ordering matches what you would get
  comparing the canonical hex strings byte-for-byte.

  Blaise has no operator overloading yet (see
  docs/operator-overloading-design.adoc), so TUuid has no '=' - use
  Equals/CompareTo instead. A default (zero-initialised, never-assigned)
  TUuid is the nil UUID (IsEmpty returns True) - there is no separate
  "unset" state to worry about.
 }

unit Uuid;

interface

uses
  SysUtils;   { Exception, IntToStr }

type
  { Base class for all errors raised by this unit. }
  EUuidError = class(Exception);

  { Raised by TUuid.Parse / TUuid.FromBytes when the input is not well-formed. }
  EUuidParse = class(EUuidError);

  { Raised by TUuid.RandomUuid if the kernel CSPRNG could not supply 16 bytes. }
  EUuidRandomFailure = class(EUuidError);

  { ------------------------------------------------------------------ }
  { TUuid — RFC 4122 UUID value type                                    }
  { ------------------------------------------------------------------ }

  { A 128-bit UUID value.  See the unit header for the design rationale. }
  TUuid = record
    { The high 64 bits: byte 0 (most significant) .. byte 7. }
    FMostSigBits: Int64;
    { The low 64 bits: byte 8 .. byte 15 (least significant). }
    FLeastSigBits: Int64;

    { A new random (v4) UUID.
      @returns a fresh random TUuid.
      @raises EUuidRandomFailure if the kernel CSPRNG could not supply
              16 bytes. }
    static function RandomUuid: TUuid;

    { Parses a canonical '8-4-4-4-12' UUID string (case-insensitive).
      @param S the UUID text.
      @returns the parsed TUuid.
      @raises EUuidParse if S is not a well-formed canonical UUID. }
    static function Parse(const S: string): TUuid;

    { Non-raising validate-and-parse: the way to check "is this a valid
      UUID".
      @param S the UUID text.
      @param AUuid receives the parsed value when the result is True.
      @returns True iff S is a well-formed canonical UUID. }
    static function TryParse(const S: string; out AUuid: TUuid): Boolean;

    { Builds a TUuid from its 16 raw bytes.
      @param ARaw the 16 raw bytes, as a string.
      @returns the TUuid holding those bytes.
      @raises EUuidParse if ARaw is not exactly 16 bytes long. }
    static function FromBytes(const ARaw: string): TUuid;

    { The nil UUID: '00000000-0000-0000-0000-000000000000'.
      @returns a TUuid with every bit zero. }
    static function Empty: TUuid;

    { Canonical lowercase '8-4-4-4-12' text, e.g.
      '3f2504e0-4f89-41d3-9a0c-0305e82c3301'.
      @returns the canonical string form. }
    function ToString: string;

    { The 16 raw bytes (as a string), for callers that want the binary form.
      @returns the raw bytes. }
    function ToBytes: string;

    { Three-way unsigned 128-bit comparison, most-significant byte first
      (see the unit header for why this is unsigned, unlike Java's).
      @param AOther the value to compare against.
      @returns -1 if Self < AOther, 0 if equal, +1 if Self > AOther. }
    function CompareTo(const AOther: TUuid): Integer;

    { Value equality.
      @param AOther the value to compare against.
      @returns True iff Self and AOther hold the same 128 bits. }
    function Equals(const AOther: TUuid): Boolean;

    { Hash code consistent with Equals, safe for use as a dictionary key.
      @returns a hash of the 128-bit value. }
    function GetHashCode: Integer;

    { Tests whether this is the nil UUID (every bit zero), including a
      never-assigned (default zero-value) TUuid.
      @returns True iff Self holds the nil UUID. }
    function IsEmpty: Boolean;

    { The RFC 4122 version nibble (from byte 6's high nibble).
      @returns 1-5 for a well-formed UUID, 0 if IsEmpty. }
    function Version: Integer;
  end;

implementation

uses
  StrUtils;   { TStringBuilder }

{ ponytail: PORTING BOUNDARY — getrandom(2) is LINUX-specific (3.17+, glibc
  2.25+).  FreeBSD has a compatible getrandom; macOS does NOT (use getentropy(3)
  or SecRandomCopyBytes); Windows uses BCryptGenRandom.  When a second target
  lands, dispatch c_getrandom per platform behind TUuid.RandomUuid — the
  public API stays put.  (/dev/urandom would cover all the Unixes but not
  Windows, hence the syscall.) }

{ getrandom(buf, buflen, flags): fill buf with buflen random bytes from the
  kernel CSPRNG.  flags=0 reads from the same pool as /dev/urandom. }
{$IFDEF DARWIN}
{ macOS has no getrandom(2); getentropy(3) draws from the same kernel CSPRNG
  for up to 256 bytes per call (every caller here asks for 16 or fewer).
  Same contract as getrandom: the byte count on success, -1 on failure. }
function c_getentropy(ABuf: Pointer; ALen: Int64): Integer;
  external name 'getentropy';

function c_getrandom(ABuf: Pointer; ALen: Int64; AFlags: Integer): Int64;
begin
  if c_getentropy(ABuf, ALen) = 0 then
    Result := ALen
  else
    Result := -1;
end;
{$ELSE}
function c_getrandom(ABuf: Pointer; ALen: Int64; AFlags: Integer): Int64;
  external name 'getrandom';
{$ENDIF}

function HexDigit(AValue: Integer): Byte;
begin
  { 0-9 -> '0'..'9' (48..57), 10-15 -> 'a'..'f' (97..102) }
  if AValue < 10 then
    Result := Ord('0') + AValue
  else
    Result := Ord('a') + AValue - 10
end;

{ 0-15 for a hex digit (either case), -1 if ACh is not a hex digit. }
function HexNibbleValue(ACh: Integer): Integer;
begin
  if (ACh >= Ord('0')) and (ACh <= Ord('9')) then
    Result := ACh - Ord('0')
  else if (ACh >= Ord('a')) and (ACh <= Ord('f')) then
    Result := ACh - Ord('a') + 10
  else if (ACh >= Ord('A')) and (ACh <= Ord('F')) then
    Result := ACh - Ord('A') + 10
  else
    Result := -1
end;

{ Extracts byte AIndex (0..15, most-significant first) from a UUID's two
  Int64 halves: 0-7 come from AMsb, 8-15 from ALsb. }
function ByteAt(AMsb, ALsb: Int64; AIndex: Integer): Integer;
var
  V: Int64;
  Shift: Integer;
begin
  if AIndex < 8 then
  begin
    V := AMsb;
    Shift := 7 - AIndex
  end
  else
  begin
    V := ALsb;
    Shift := 15 - AIndex
  end;
  Result := Integer((V shr (Shift * 8)) and Int64($FF))
end;

{ Unsigned 64-bit comparison implemented with only signed Int64 operators:
  same-sign values compare the same signed or unsigned; when the signs
  differ, the non-negative one is the unsigned-SMALLER of the two (its top
  bit is 0, so its unsigned magnitude is below 2^63, while the "negative"
  one's top bit being 1 puts it at or above 2^63 unsigned). }
function UnsignedCompareInt64(A, B: Int64): Integer;
begin
  if (A >= 0) = (B >= 0) then
  begin
    if A < B then Result := -1
    else if A > B then Result := 1
    else Result := 0
  end
  else if A >= 0 then
    Result := -1
  else
    Result := 1
end;

{ ------------------------------------------------------------------ }
{ TUuid static constructors                                            }
{ ------------------------------------------------------------------ }

static function TUuid.RandomUuid: TUuid;
var
  Buf: array[0..15] of Byte;
  Msb, Lsb: Int64;
  I: Integer;
begin
  if c_getrandom(@Buf[0], 16, 0) <> 16 then
    raise EUuidRandomFailure.Create(
      'TUuid.RandomUuid: getrandom(2) failed to supply 16 random bytes');

  { version 4: high nibble of byte 6 = 0100 }
  Buf[6] := (Buf[6] and $0F) or $40;
  { variant RFC 4122: top two bits of byte 8 = 10 }
  Buf[8] := (Buf[8] and $3F) or $80;

  Msb := 0;
  for I := 0 to 7 do
    Msb := (Msb shl 8) or Int64(Buf[I]);
  Lsb := 0;
  for I := 8 to 15 do
    Lsb := (Lsb shl 8) or Int64(Buf[I]);

  Result.FMostSigBits := Msb;
  Result.FLeastSigBits := Lsb
end;

static function TUuid.TryParse(const S: string; out AUuid: TUuid): Boolean;
var
  I, Hi, Lo, B, ByteIdx: Integer;
  Msb, Lsb: Int64;
begin
  if Length(S) <> 36 then
  begin
    Result := False;
    Exit
  end;

  { First pass: validate every position before touching AUuid. }
  I := 0;
  while I < 36 do
  begin
    if (I = 8) or (I = 13) or (I = 18) or (I = 23) then
    begin
      if Byte(S[I]) <> Ord('-') then
      begin
        Result := False;
        Exit
      end
    end
    else if HexNibbleValue(Byte(S[I])) < 0 then
    begin
      Result := False;
      Exit
    end;
    I := I + 1
  end;

  { Second pass: decode hex-digit pairs, accumulating into Msb (bytes 0-7)
    then Lsb (bytes 8-15), skipping hyphens. }
  Msb := 0;
  Lsb := 0;
  ByteIdx := 0;
  I := 0;
  while I < 36 do
  begin
    if (I = 8) or (I = 13) or (I = 18) or (I = 23) then
      I := I + 1
    else
    begin
      Hi := HexNibbleValue(Byte(S[I]));
      Lo := HexNibbleValue(Byte(S[I + 1]));
      B := (Hi shl 4) or Lo;
      if ByteIdx < 8 then
        Msb := (Msb shl 8) or Int64(B)
      else
        Lsb := (Lsb shl 8) or Int64(B);
      ByteIdx := ByteIdx + 1;
      I := I + 2
    end
  end;

  AUuid.FMostSigBits := Msb;
  AUuid.FLeastSigBits := Lsb;
  Result := True
end;

static function TUuid.Parse(const S: string): TUuid;
begin
  if not TUuid.TryParse(S, Result) then
    raise EUuidParse.Create(
      'TUuid.Parse: not a valid canonical UUID: ''' + S + '''')
end;

static function TUuid.FromBytes(const ARaw: string): TUuid;
var
  I: Integer;
  Msb, Lsb: Int64;
begin
  if Length(ARaw) <> 16 then
    raise EUuidParse.Create(
      'TUuid.FromBytes: expected 16 raw bytes, got ' + IntToStr(Length(ARaw)));

  Msb := 0;
  for I := 0 to 7 do
    Msb := (Msb shl 8) or Int64(Byte(ARaw[I]));
  Lsb := 0;
  for I := 8 to 15 do
    Lsb := (Lsb shl 8) or Int64(Byte(ARaw[I]));

  Result.FMostSigBits := Msb;
  Result.FLeastSigBits := Lsb
end;

static function TUuid.Empty: TUuid;
begin
  Result.FMostSigBits := 0;
  Result.FLeastSigBits := 0
end;

{ ------------------------------------------------------------------ }
{ TUuid instance methods                                               }
{ ------------------------------------------------------------------ }

function TUuid.ToString: string;
var
  SB: TStringBuilder;
  I, B: Integer;
begin
  SB := TStringBuilder.Create();
  for I := 0 to 15 do
  begin
    { hyphens after bytes 4, 6, 8, 10 (the 8-4-4-4-12 grouping) }
    if (I = 4) or (I = 6) or (I = 8) or (I = 10) then
      SB.AppendByte(Ord('-'));
    B := ByteAt(FMostSigBits, FLeastSigBits, I);
    SB.AppendByte(HexDigit((B shr 4) and $0F));
    SB.AppendByte(HexDigit(B and $0F))
  end;
  Result := SB.ToString();
  SB.Free()
end;

function TUuid.ToBytes: string;
var
  SB: TStringBuilder;
  I: Integer;
begin
  SB := TStringBuilder.Create();
  for I := 0 to 15 do
    SB.AppendByte(ByteAt(FMostSigBits, FLeastSigBits, I));
  Result := SB.ToString();
  SB.Free()
end;

function TUuid.CompareTo(const AOther: TUuid): Integer;
begin
  Result := UnsignedCompareInt64(FMostSigBits, AOther.FMostSigBits);
  if Result = 0 then
    Result := UnsignedCompareInt64(FLeastSigBits, AOther.FLeastSigBits)
end;

function TUuid.Equals(const AOther: TUuid): Boolean;
begin
  Result := (FMostSigBits = AOther.FMostSigBits) and
            (FLeastSigBits = AOther.FLeastSigBits)
end;

function TUuid.GetHashCode: Integer;
var
  Hilo: Int64;
begin
  Hilo := FMostSigBits xor FLeastSigBits;
  Result := Integer(Hilo shr 32) xor Integer(Hilo)
end;

function TUuid.IsEmpty: Boolean;
begin
  Result := (FMostSigBits = 0) and (FLeastSigBits = 0)
end;

function TUuid.Version: Integer;
begin
  Result := (ByteAt(FMostSigBits, FLeastSigBits, 6) shr 4) and $0F
end;

end.
