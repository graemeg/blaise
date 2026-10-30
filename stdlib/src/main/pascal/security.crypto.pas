{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - cryptographic hash functions.

  The home for hash/digest primitives (Java's java.security, .NET's
  System.Security.Cryptography).  SHA-1 is provided; further digests and HMAC
  belong here.

  NB: SHA-1 is not collision-resistant and must not be used for new security
  decisions.  It remains required for interop where a protocol mandates it
  (e.g. the WebSocket opening handshake, Git object ids).

  NB: MD5 is cryptographically broken and must not be used for new security
  decisions.  It remains required for legacy interop where a protocol or
  existing system mandates it (e.g. content checksums, legacy API signatures).

  Base64 lives in Encoding.Base64, not here: it is a text encoding, not crypto.
  Compose them at the call site, e.g.  Base64Encode(Sha1(Key + GUID)).

  NB: shifts and 'not' are not masked to 32 bits by the backend, so every
  32-bit operation is wrapped with 'and $FFFFFFFF'. }

unit Security.Crypto;

interface

{ Raw 20-byte SHA-1 digest of S (S treated as raw bytes), returned as a string
  of 20 bytes. }
function Sha1(const AData: string): string;

{ SHA-1 digest as a 40-character lower-case hex string. }
function Sha1Hex(const AData: string): string;

{ Raw 32-byte SHA-256 digest of AData (treated as raw bytes). }
function Sha256(const AData: string): string;

{ SHA-256 digest as a 64-character lower-case hex string. }
function Sha256Hex(const AData: string): string;

{ Raw 16-byte MD5 digest of AData (treated as raw bytes). }
function Md5(const AData: string): string;

{ MD5 digest as a 32-character lower-case hex string. }
function Md5Hex(const AData: string): string;

{ HMAC-SHA256 (RFC 2104 / RFC 4231).  Returns raw 32-byte MAC.
  Keys longer than 64 bytes (SHA-256 block size) are hashed first. }
function HmacSha256(const AKey, AData: string): string;

{ HMAC-SHA256 as a 64-character lower-case hex string. }
function HmacSha256Hex(const AKey, AData: string): string;

{ Timing-safe comparison.  XOR-accumulates all bytes up to the shorter
  length, then ORs in a length-mismatch flag.  Never short-circuits. }
function ConstantTimeEqual(const A, B: string): Boolean;

implementation

uses
  StrUtils;

const
  MASK32 = $FFFFFFFF;

function Rotl32(V: UInt32; ABits: Int): UInt32;
begin
  Result := ((V shl ABits) or (V shr (32 - ABits))) and MASK32;
end;

function Rotr32(V: UInt32; ABits: Int): UInt32;
begin
  Result := ((V shr ABits) or (V shl (32 - ABits))) and MASK32;
end;

function DigestToHex(const ARaw: string): string;
var
  SB: TStringBuilder;
  I, B: Int;
const
  Hex = '0123456789abcdef';
begin
  SB := TStringBuilder.Create();
  for I := 0 to Length(ARaw) - 1 do
  begin
    B := Byte(ARaw[I]);
    SB.AppendByte(Byte(Hex[B div 16]));
    SB.AppendByte(Byte(Hex[B mod 16]));
  end;
  Result := SB.ToString();
  SB.Free();
end;

function Sha1(const AData: string): string;
var
  H0, H1, H2, H3, H4: UInt32;
  MsgLen, TotalBits: Int64;
  PadLen, I, T, ChunkStart, NumChunks, C: Int;
  Msg: array[0..63] of Byte;     { current 64-byte chunk }
  W: array[0..79] of UInt32;
  A, B, Cc, D, E, F, K, Temp: UInt32;
  PData: string;
  SB, OutSB: TStringBuilder;
begin
  { Build the padded message:
    original || 0x80 || 0x00... || 64-bit big-endian bit length.
    AppendByte guarantees raw single bytes. }
  MsgLen := Length(AData);
  TotalBits := MsgLen * 8;

  PadLen := 56 - ((MsgLen + 1) mod 64);
  if PadLen < 0 then
    PadLen := PadLen + 64;

  SB := TStringBuilder.Create();
  SB.Append(AData);
  SB.AppendByte(128);
  for I := 1 to PadLen do
    SB.AppendByte(0);
  for I := 7 downto 0 do
    SB.AppendByte((TotalBits shr (I * 8)) and $FF);
  PData := SB.ToString();
  SB.Free();

  H0 := $67452301;
  H1 := $EFCDAB89;
  H2 := $98BADCFE;
  H3 := $10325476;
  H4 := $C3D2E1F0;

  NumChunks := Length(PData) div 64;
  for C := 0 to NumChunks - 1 do
  begin
    ChunkStart := C * 64;
    for I := 0 to 63 do
      Msg[I] := Byte(PData[ChunkStart + I]);

    for T := 0 to 15 do
      W[T] := ((UInt32(Msg[T * 4]) shl 24) or
               (UInt32(Msg[T * 4 + 1]) shl 16) or
               (UInt32(Msg[T * 4 + 2]) shl 8) or
                UInt32(Msg[T * 4 + 3])) and MASK32;
    for T := 16 to 79 do
      W[T] := Rotl32((W[T-3] xor W[T-8] xor W[T-14] xor W[T-16]), 1);

    A := H0; B := H1; Cc := H2; D := H3; E := H4;

    for T := 0 to 79 do
    begin
      if T < 20 then
      begin
        F := (B and Cc) or ((not B) and D);
        K := $5A827999;
      end
      else if T < 40 then
      begin
        F := B xor Cc xor D;
        K := $6ED9EBA1;
      end
      else if T < 60 then
      begin
        F := (B and Cc) or (B and D) or (Cc and D);
        K := $8F1BBCDC;
      end
      else
      begin
        F := B xor Cc xor D;
        K := $CA62C1D6;
      end;
      F := F and MASK32;
      Temp := (Rotl32(A, 5) + F + E + K + W[T]) and MASK32;
      E := D;
      D := Cc;
      Cc := Rotl32(B, 30);
      B := A;
      A := Temp;
    end;

    H0 := (H0 + A) and MASK32;
    H1 := (H1 + B) and MASK32;
    H2 := (H2 + Cc) and MASK32;
    H3 := (H3 + D) and MASK32;
    H4 := (H4 + E) and MASK32;
  end;

  { Emit 20 raw bytes, big-endian. }
  OutSB := TStringBuilder.Create();
  OutSB.AppendByte((H0 shr 24) and $FF); OutSB.AppendByte((H0 shr 16) and $FF);
  OutSB.AppendByte((H0 shr 8) and $FF);  OutSB.AppendByte(H0 and $FF);
  OutSB.AppendByte((H1 shr 24) and $FF); OutSB.AppendByte((H1 shr 16) and $FF);
  OutSB.AppendByte((H1 shr 8) and $FF);  OutSB.AppendByte(H1 and $FF);
  OutSB.AppendByte((H2 shr 24) and $FF); OutSB.AppendByte((H2 shr 16) and $FF);
  OutSB.AppendByte((H2 shr 8) and $FF);  OutSB.AppendByte(H2 and $FF);
  OutSB.AppendByte((H3 shr 24) and $FF); OutSB.AppendByte((H3 shr 16) and $FF);
  OutSB.AppendByte((H3 shr 8) and $FF);  OutSB.AppendByte(H3 and $FF);
  OutSB.AppendByte((H4 shr 24) and $FF); OutSB.AppendByte((H4 shr 16) and $FF);
  OutSB.AppendByte((H4 shr 8) and $FF);  OutSB.AppendByte(H4 and $FF);
  Result := OutSB.ToString();
  OutSB.Free();
end;

function Sha1Hex(const AData: string): string;
begin
  Result := DigestToHex(Sha1(AData));
end;

function Sha256(const AData: string): string;
const
  K: array[0..63] of UInt32 = (
    $428a2f98, $71374491, $b5c0fbcf, $e9b5dba5,
    $3956c25b, $59f111f1, $923f82a4, $ab1c5ed5,
    $d807aa98, $12835b01, $243185be, $550c7dc3,
    $72be5d74, $80deb1fe, $9bdc06a7, $c19bf174,
    $e49b69c1, $efbe4786, $0fc19dc6, $240ca1cc,
    $2de92c6f, $4a7484aa, $5cb0a9dc, $76f988da,
    $983e5152, $a831c66d, $b00327c8, $bf597fc7,
    $c6e00bf3, $d5a79147, $06ca6351, $14292967,
    $27b70a85, $2e1b2138, $4d2c6dfc, $53380d13,
    $650a7354, $766a0abb, $81c2c92e, $92722c85,
    $a2bfe8a1, $a81a664b, $c24b8b70, $c76c51a3,
    $d192e819, $d6990624, $f40e3585, $106aa070,
    $19a4c116, $1e376c08, $2748774c, $34b0bcb5,
    $391c0cb3, $4ed8aa4a, $5b9cca4f, $682e6ff3,
    $748f82ee, $78a5636f, $84c87814, $8cc70208,
    $90befffa, $a4506ceb, $bef9a3f7, $c67178f2
  );
var
  H0, H1, H2, H3, H4, H5, H6, H7: UInt32;
  MsgLen, TotalBits: Int64;
  PadLen, I, T, ChunkStart, NumChunks, C: Int;
  Msg: array[0..63] of Byte;
  W: array[0..63] of UInt32;
  A, B, Cc, D, E, F, G, Hh: UInt32;
  S0, S1, Ch, Maj, Temp1, Temp2: UInt32;
  PData: string;
  SB, OutSB: TStringBuilder;
begin
  MsgLen := Length(AData);
  TotalBits := MsgLen * 8;

  PadLen := 56 - ((MsgLen + 1) mod 64);
  if PadLen < 0 then
    PadLen := PadLen + 64;

  SB := TStringBuilder.Create();
  SB.Append(AData);
  SB.AppendByte(128);
  for I := 1 to PadLen do
    SB.AppendByte(0);
  for I := 7 downto 0 do
    SB.AppendByte((TotalBits shr (I * 8)) and $FF);
  PData := SB.ToString();
  SB.Free();

  H0 := $6a09e667;
  H1 := $bb67ae85;
  H2 := $3c6ef372;
  H3 := $a54ff53a;
  H4 := $510e527f;
  H5 := $9b05688c;
  H6 := $1f83d9ab;
  H7 := $5be0cd19;

  NumChunks := Length(PData) div 64;
  for C := 0 to NumChunks - 1 do
  begin
    ChunkStart := C * 64;
    for I := 0 to 63 do
      Msg[I] := Byte(PData[ChunkStart + I]);

    for T := 0 to 15 do
      W[T] := ((UInt32(Msg[T * 4]) shl 24) or
               (UInt32(Msg[T * 4 + 1]) shl 16) or
               (UInt32(Msg[T * 4 + 2]) shl 8) or
                UInt32(Msg[T * 4 + 3])) and MASK32;

    for T := 16 to 63 do
    begin
      S0 := (Rotr32(W[T-15], 7) xor Rotr32(W[T-15], 18) xor (W[T-15] shr 3)) and MASK32;
      S1 := (Rotr32(W[T-2], 17) xor Rotr32(W[T-2], 19) xor (W[T-2] shr 10)) and MASK32;
      W[T] := (W[T-16] + S0 + W[T-7] + S1) and MASK32;
    end;

    A := H0; B := H1; Cc := H2; D := H3;
    E := H4; F := H5; G := H6; Hh := H7;

    for T := 0 to 63 do
    begin
      S1 := (Rotr32(E, 6) xor Rotr32(E, 11) xor Rotr32(E, 25)) and MASK32;
      Ch := ((E and F) xor (((not E) and MASK32) and G)) and MASK32;
      Temp1 := (Hh + S1 + Ch + K[T] + W[T]) and MASK32;
      S0 := (Rotr32(A, 2) xor Rotr32(A, 13) xor Rotr32(A, 22)) and MASK32;
      Maj := ((A and B) xor (A and Cc) xor (B and Cc)) and MASK32;
      Temp2 := (S0 + Maj) and MASK32;

      Hh := G;
      G := F;
      F := E;
      E := (D + Temp1) and MASK32;
      D := Cc;
      Cc := B;
      B := A;
      A := (Temp1 + Temp2) and MASK32;
    end;

    H0 := (H0 + A) and MASK32;
    H1 := (H1 + B) and MASK32;
    H2 := (H2 + Cc) and MASK32;
    H3 := (H3 + D) and MASK32;
    H4 := (H4 + E) and MASK32;
    H5 := (H5 + F) and MASK32;
    H6 := (H6 + G) and MASK32;
    H7 := (H7 + Hh) and MASK32;
  end;

  OutSB := TStringBuilder.Create();
  OutSB.AppendByte((H0 shr 24) and $FF); OutSB.AppendByte((H0 shr 16) and $FF);
  OutSB.AppendByte((H0 shr 8) and $FF);  OutSB.AppendByte(H0 and $FF);
  OutSB.AppendByte((H1 shr 24) and $FF); OutSB.AppendByte((H1 shr 16) and $FF);
  OutSB.AppendByte((H1 shr 8) and $FF);  OutSB.AppendByte(H1 and $FF);
  OutSB.AppendByte((H2 shr 24) and $FF); OutSB.AppendByte((H2 shr 16) and $FF);
  OutSB.AppendByte((H2 shr 8) and $FF);  OutSB.AppendByte(H2 and $FF);
  OutSB.AppendByte((H3 shr 24) and $FF); OutSB.AppendByte((H3 shr 16) and $FF);
  OutSB.AppendByte((H3 shr 8) and $FF);  OutSB.AppendByte(H3 and $FF);
  OutSB.AppendByte((H4 shr 24) and $FF); OutSB.AppendByte((H4 shr 16) and $FF);
  OutSB.AppendByte((H4 shr 8) and $FF);  OutSB.AppendByte(H4 and $FF);
  OutSB.AppendByte((H5 shr 24) and $FF); OutSB.AppendByte((H5 shr 16) and $FF);
  OutSB.AppendByte((H5 shr 8) and $FF);  OutSB.AppendByte(H5 and $FF);
  OutSB.AppendByte((H6 shr 24) and $FF); OutSB.AppendByte((H6 shr 16) and $FF);
  OutSB.AppendByte((H6 shr 8) and $FF);  OutSB.AppendByte(H6 and $FF);
  OutSB.AppendByte((H7 shr 24) and $FF); OutSB.AppendByte((H7 shr 16) and $FF);
  OutSB.AppendByte((H7 shr 8) and $FF);  OutSB.AppendByte(H7 and $FF);
  Result := OutSB.ToString();
  OutSB.Free();
end;

function Sha256Hex(const AData: string): string;
begin
  Result := DigestToHex(Sha256(AData));
end;

function Md5(const AData: string): string;
const
  T: array[0..63] of UInt32 = (
    $d76aa478, $e8c7b756, $242070db, $c1bdceee,
    $f57c0faf, $4787c62a, $a8304613, $fd469501,
    $698098d8, $8b44f7af, $ffff5bb1, $895cd7be,
    $6b901122, $fd987193, $a679438e, $49b40821,
    $f61e2562, $c040b340, $265e5a51, $e9b6c7aa,
    $d62f105d, $02441453, $d8a1e681, $e7d3fbc8,
    $21e1cde6, $c33707d6, $f4d50d87, $455a14ed,
    $a9e3e905, $fcefa3f8, $676f02d9, $8d2a4c8a,
    $fffa3942, $8771f681, $6d9d6122, $fde5380c,
    $a4beea44, $4bdecfa9, $f6bb4b60, $bebfbc70,
    $289b7ec6, $eaa127fa, $d4ef3085, $04881d05,
    $d9d4d039, $e6db99e5, $1fa27cf8, $c4ac5665,
    $f4292244, $432aff97, $ab9423a7, $fc93a039,
    $655b59c3, $8f0ccc92, $ffeff47d, $85845dd1,
    $6fa87e4f, $fe2ce6e0, $a3014314, $4e0811a1,
    $f7537e82, $bd3af235, $2ad7d2bb, $eb86d391
  );
  S: array[0..63] of Int32 = (
    7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,
    5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,
    4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,
    6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21
  );
var
  H0, H1, H2, H3: UInt32;
  MsgLen, TotalBits: Int64;
  PadLen, I, J, Chunk, ChunkStart, NumChunks, G: Int;
  M: array[0..15] of UInt32;
  A, B, Cc, D, F, Tmp: UInt32;
  PData: string;
  SB, OutSB: TStringBuilder;
begin
  MsgLen := Length(AData);
  TotalBits := MsgLen * 8;

  PadLen := 56 - ((MsgLen + 1) mod 64);
  if PadLen < 0 then
    PadLen := PadLen + 64;

  SB := TStringBuilder.Create();
  SB.Append(AData);
  SB.AppendByte(128);
  for I := 1 to PadLen do
    SB.AppendByte(0);
  { MD5 uses LITTLE-ENDIAN 64-bit bit length. }
  for I := 0 to 7 do
    SB.AppendByte((TotalBits shr (I * 8)) and $FF);
  PData := SB.ToString();
  SB.Free();

  H0 := $67452301;
  H1 := $efcdab89;
  H2 := $98badcfe;
  H3 := $10325476;

  NumChunks := Length(PData) div 64;
  for Chunk := 0 to NumChunks - 1 do
  begin
    ChunkStart := Chunk * 64;
    { Read 16 words in LITTLE-ENDIAN order. }
    for J := 0 to 15 do
      M[J] := (UInt32(Byte(PData[ChunkStart + J * 4 + 3])) shl 24) or
              (UInt32(Byte(PData[ChunkStart + J * 4 + 2])) shl 16) or
              (UInt32(Byte(PData[ChunkStart + J * 4 + 1])) shl 8) or
               UInt32(Byte(PData[ChunkStart + J * 4]));

    A := H0; B := H1; Cc := H2; D := H3;

    for I := 0 to 63 do
    begin
      if I < 16 then
      begin
        F := (B and Cc) or (((not B) and MASK32) and D);
        G := I;
      end
      else if I < 32 then
      begin
        F := (D and B) or (((not D) and MASK32) and Cc);
        G := (5 * I + 1) mod 16;
      end
      else if I < 48 then
      begin
        F := B xor Cc xor D;
        G := (3 * I + 5) mod 16;
      end
      else
      begin
        F := (Cc xor (B or ((not D) and MASK32))) and MASK32;
        G := (7 * I) mod 16;
      end;
      F := F and MASK32;
      Tmp := D;
      D := Cc;
      Cc := B;
      B := (B + Rotl32((A + F + T[I] + M[G]) and MASK32, S[I])) and MASK32;
      A := Tmp;
    end;

    H0 := (H0 + A) and MASK32;
    H1 := (H1 + B) and MASK32;
    H2 := (H2 + Cc) and MASK32;
    H3 := (H3 + D) and MASK32;
  end;

  { Emit 16 raw bytes, LITTLE-ENDIAN per word. }
  OutSB := TStringBuilder.Create();
  OutSB.AppendByte(H0 and $FF); OutSB.AppendByte((H0 shr 8) and $FF);
  OutSB.AppendByte((H0 shr 16) and $FF); OutSB.AppendByte((H0 shr 24) and $FF);
  OutSB.AppendByte(H1 and $FF); OutSB.AppendByte((H1 shr 8) and $FF);
  OutSB.AppendByte((H1 shr 16) and $FF); OutSB.AppendByte((H1 shr 24) and $FF);
  OutSB.AppendByte(H2 and $FF); OutSB.AppendByte((H2 shr 8) and $FF);
  OutSB.AppendByte((H2 shr 16) and $FF); OutSB.AppendByte((H2 shr 24) and $FF);
  OutSB.AppendByte(H3 and $FF); OutSB.AppendByte((H3 shr 8) and $FF);
  OutSB.AppendByte((H3 shr 16) and $FF); OutSB.AppendByte((H3 shr 24) and $FF);
  Result := OutSB.ToString();
  OutSB.Free();
end;

function Md5Hex(const AData: string): string;
begin
  Result := DigestToHex(Md5(AData));
end;

function HmacSha256(const AKey, AData: string): string;
const
  BLOCK_SIZE = 64; { SHA-256 block size; SHA-512 uses 128 }
var
  KeyBlock: string;
  IPad, OPad: TStringBuilder;
  I: Int;
  InnerHash: string;
begin
  if Length(AKey) > BLOCK_SIZE then
    KeyBlock := Sha256(AKey)
  else
    KeyBlock := AKey;

  IPad := TStringBuilder.Create();
  OPad := TStringBuilder.Create();
  for I := 0 to BLOCK_SIZE - 1 do
  begin
    if I < Length(KeyBlock) then
    begin
      IPad.AppendByte(Byte(KeyBlock[I]) xor $36);
      OPad.AppendByte(Byte(KeyBlock[I]) xor $5C);
    end
    else
    begin
      IPad.AppendByte($36);
      OPad.AppendByte($5C);
    end;
  end;

  IPad.Append(AData);
  InnerHash := Sha256(IPad.ToString());
  IPad.Free();

  OPad.Append(InnerHash);
  Result := Sha256(OPad.ToString());
  OPad.Free();
end;

function HmacSha256Hex(const AKey, AData: string): string;
begin
  Result := DigestToHex(HmacSha256(AKey, AData));
end;

function ConstantTimeEqual(const A, B: string): Boolean;
var
  Diff, I, MinLen: Int;
begin
  Diff := Length(A) xor Length(B);
  MinLen := Length(A);
  if Length(B) < MinLen then
    MinLen := Length(B);
  for I := 0 to MinLen - 1 do
    Diff := Diff or (Byte(A[I]) xor Byte(B[I]));
  Result := Diff = 0;
end;

end.
