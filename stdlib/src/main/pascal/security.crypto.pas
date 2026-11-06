{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - cryptographic hash functions.

  The home for hash/digest primitives (Java's java.security, .NET's
  System.Security.Cryptography).  SHA-1, SHA-256, SHA-512 and MD5 are
  provided, one-shot over a string or incrementally through THashDigest;
  further digests and HMAC belong here.

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

uses
  Streams;

type
  { THashDigest - an incremental message digest (Java's MessageDigest, Go's
    hash.Hash).  Feed the message with any number of Update calls, then
    Finish returns the raw digest and resets the object for a new message:

      D := TSha256Digest.Create();
      D.UpdateFile('big.jar');        // read in pieces, never held whole
      Hex := D.FinishHex();
      D.Free();

    The one-shot functions below (Sha1, Sha256, Sha512 and their Hex forms)
    are thin wrappers over these classes. }
  THashDigest = class
  protected
    FBlock: array[0..127] of Byte;   { the partial block not yet compressed }
    FBlockLen: Int;                  { bytes in FBlock }
    FBlockSize: Int;                 { 64 for SHA-1/SHA-256, 128 for SHA-512 }
    FLengthBytes: Int;               { width of the trailing bit length: 8 or 16 }
    FTotal: Int64;                   { message bytes seen so far }
    procedure Compress; virtual; abstract;
    procedure InitState; virtual; abstract;
    function StateBytes: string; virtual; abstract;
  public
    constructor Create;
    { Appends AData (treated as raw bytes) to the message. }
    procedure Update(const AData: string);
    { Appends ACount bytes starting at ABuf to the message. }
    procedure UpdateBuf(ABuf: Pointer; ACount: Int);
    { Appends everything readable from AStream; does not close it. }
    procedure UpdateStream(AStream: TInputStream);
    { Appends the contents of the file at APath, read in pieces.  Raises
      EStreamError when the file cannot be opened. }
    procedure UpdateFile(const APath: string);
    { The raw digest of the message so far, then Reset. }
    function Finish: string;
    { Finish as a lower-case hex string. }
    function FinishHex: string;
    { Discards the message so far. }
    procedure Reset;
    { Length in bytes of the raw digest. }
    function DigestSize: Int; virtual; abstract;
  end;

  { SHA-1 (FIPS 180-4).  See the unit header: interop only. }
  TSha1Digest = class(THashDigest)
  private
    FH: array[0..4] of UInt32;
  protected
    procedure Compress; override;
    procedure InitState; override;
    function StateBytes: string; override;
  public
    function DigestSize: Int; override;
  end;

  { SHA-256 (FIPS 180-4). }
  TSha256Digest = class(THashDigest)
  private
    FH: array[0..7] of UInt32;
  protected
    procedure Compress; override;
    procedure InitState; override;
    function StateBytes: string; override;
  public
    function DigestSize: Int; override;
  end;

  { SHA-512 (FIPS 180-4). }
  TSha512Digest = class(THashDigest)
  private
    FH: array[0..7] of UInt64;
  protected
    procedure Compress; override;
    procedure InitState; override;
    function StateBytes: string; override;
  public
    function DigestSize: Int; override;
  end;

{ Raw 20-byte SHA-1 digest of S (S treated as raw bytes), returned as a string
  of 20 bytes. }
function Sha1(const AData: string): string;

{ SHA-1 digest as a 40-character lower-case hex string. }
function Sha1Hex(const AData: string): string;

{ Raw 32-byte SHA-256 digest of AData (treated as raw bytes). }
function Sha256(const AData: string): string;

{ SHA-256 digest as a 64-character lower-case hex string. }
function Sha256Hex(const AData: string): string;

{ Raw 64-byte SHA-512 digest of AData (treated as raw bytes). }
function Sha512(const AData: string): string;

{ SHA-512 digest as a 128-character lower-case hex string. }
function Sha512Hex(const AData: string): string;

{ Hex digests of the file at APath, read in pieces rather than loaded whole.
  Raise EStreamError when the file cannot be opened. }
function Sha1FileHex(const APath: string): string;
function Sha256FileHex(const APath: string): string;
function Sha512FileHex(const APath: string): string;

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

{ ------------------------------------------------------------------ }
{ THashDigest                                                         }
{ ------------------------------------------------------------------ }

constructor THashDigest.Create;
begin
  inherited Create();
  Self.Reset();
end;

procedure THashDigest.Reset;
begin
  Self.FBlockLen := 0;
  Self.FTotal := 0;
  Self.InitState();
end;

procedure THashDigest.Update(const AData: string);
begin
  if Length(AData) > 0 then
    Self.UpdateBuf(Pointer(AData), Length(AData));
end;

procedure THashDigest.UpdateBuf(ABuf: Pointer; ACount: Int);
var
  P: PByte;
  I: Int;
begin
  { Assigned, not cast: a PByte(...) cast here hits a compiler bug when
    another unit in the program declares its own implementation-section
    PByte (io.process does). }
  P := ABuf;
  for I := 0 to ACount - 1 do
  begin
    Self.FBlock[Self.FBlockLen] := (P + I)^;
    Self.FBlockLen := Self.FBlockLen + 1;
    if Self.FBlockLen = Self.FBlockSize then
    begin
      Self.Compress();
      Self.FBlockLen := 0;
    end;
  end;
  Self.FTotal := Self.FTotal + ACount;
end;

procedure THashDigest.UpdateStream(AStream: TInputStream);
var
  Buf: array[0..16383] of Byte;
  N: Int;
begin
  repeat
    N := AStream.Read(@Buf[0], 16384);
    if N > 0 then
      Self.UpdateBuf(@Buf[0], N);
  until N <= 0;
end;

procedure THashDigest.UpdateFile(const APath: string);
var
  F: TFileInputStream;
begin
  F := TFileInputStream.Create(APath);
  try
    Self.UpdateStream(F);
  finally
    F.Close();
    F.Free();
  end;
end;

function THashDigest.Finish: string;
var
  Bits: Int64;
  I: Int;
begin
  { Padding (FIPS 180-4 5.1): a single 1 bit, zeros, then the message length
    in bits, big-endian, filling the last block.  The length field is 8 bytes
    for 64-byte blocks and 16 bytes for SHA-512; a message cannot exceed
    2^63 bits here, so the upper 8 bytes of a 16-byte field are zero. }
  Bits := Self.FTotal * 8;
  Self.FBlock[Self.FBlockLen] := $80;
  Self.FBlockLen := Self.FBlockLen + 1;
  if Self.FBlockLen > Self.FBlockSize - Self.FLengthBytes then
  begin
    while Self.FBlockLen < Self.FBlockSize do
    begin
      Self.FBlock[Self.FBlockLen] := 0;
      Self.FBlockLen := Self.FBlockLen + 1;
    end;
    Self.Compress();
    Self.FBlockLen := 0;
  end;
  while Self.FBlockLen < Self.FBlockSize - 8 do
  begin
    Self.FBlock[Self.FBlockLen] := 0;
    Self.FBlockLen := Self.FBlockLen + 1;
  end;
  for I := 7 downto 0 do
  begin
    Self.FBlock[Self.FBlockLen] := Byte((Bits shr (I * 8)) and $FF);
    Self.FBlockLen := Self.FBlockLen + 1;
  end;
  Self.Compress();
  Result := Self.StateBytes();
  Self.Reset();
end;

function THashDigest.FinishHex: string;
begin
  Result := DigestToHex(Self.Finish());
end;

procedure AppendBE32(SB: TStringBuilder; V: UInt32);
begin
  SB.AppendByte((V shr 24) and $FF);
  SB.AppendByte((V shr 16) and $FF);
  SB.AppendByte((V shr 8) and $FF);
  SB.AppendByte(V and $FF);
end;

{ ------------------------------------------------------------------ }
{ TSha1Digest                                                         }
{ ------------------------------------------------------------------ }

procedure TSha1Digest.InitState;
begin
  Self.FBlockSize := 64;
  Self.FLengthBytes := 8;
  Self.FH[0] := $67452301;
  Self.FH[1] := $EFCDAB89;
  Self.FH[2] := $98BADCFE;
  Self.FH[3] := $10325476;
  Self.FH[4] := $C3D2E1F0;
end;

function TSha1Digest.DigestSize: Int;
begin
  Result := 20;
end;

procedure TSha1Digest.Compress;
var
  W: array[0..79] of UInt32;
  A, B, Cc, D, E, F, K, Temp: UInt32;
  T: Int;
begin
  for T := 0 to 15 do
    W[T] := ((UInt32(Self.FBlock[T * 4]) shl 24) or
             (UInt32(Self.FBlock[T * 4 + 1]) shl 16) or
             (UInt32(Self.FBlock[T * 4 + 2]) shl 8) or
              UInt32(Self.FBlock[T * 4 + 3])) and MASK32;
  for T := 16 to 79 do
    W[T] := Rotl32((W[T-3] xor W[T-8] xor W[T-14] xor W[T-16]), 1);

  A := Self.FH[0]; B := Self.FH[1]; Cc := Self.FH[2];
  D := Self.FH[3]; E := Self.FH[4];

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

  Self.FH[0] := (Self.FH[0] + A) and MASK32;
  Self.FH[1] := (Self.FH[1] + B) and MASK32;
  Self.FH[2] := (Self.FH[2] + Cc) and MASK32;
  Self.FH[3] := (Self.FH[3] + D) and MASK32;
  Self.FH[4] := (Self.FH[4] + E) and MASK32;
end;

function TSha1Digest.StateBytes: string;
var
  SB: TStringBuilder;
  I: Int;
begin
  SB := TStringBuilder.Create();
  for I := 0 to 4 do
    AppendBE32(SB, Self.FH[I]);
  Result := SB.ToString();
  SB.Free();
end;

{ ------------------------------------------------------------------ }
{ TSha256Digest                                                       }
{ ------------------------------------------------------------------ }

const
  SHA256_K: array[0..63] of UInt32 = (
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

procedure TSha256Digest.InitState;
begin
  Self.FBlockSize := 64;
  Self.FLengthBytes := 8;
  Self.FH[0] := $6a09e667;
  Self.FH[1] := $bb67ae85;
  Self.FH[2] := $3c6ef372;
  Self.FH[3] := $a54ff53a;
  Self.FH[4] := $510e527f;
  Self.FH[5] := $9b05688c;
  Self.FH[6] := $1f83d9ab;
  Self.FH[7] := $5be0cd19;
end;

function TSha256Digest.DigestSize: Int;
begin
  Result := 32;
end;

procedure TSha256Digest.Compress;
var
  W: array[0..63] of UInt32;
  A, B, Cc, D, E, F, G, Hh: UInt32;
  S0, S1, Ch, Maj, Temp1, Temp2: UInt32;
  T: Int;
begin
  for T := 0 to 15 do
    W[T] := ((UInt32(Self.FBlock[T * 4]) shl 24) or
             (UInt32(Self.FBlock[T * 4 + 1]) shl 16) or
             (UInt32(Self.FBlock[T * 4 + 2]) shl 8) or
              UInt32(Self.FBlock[T * 4 + 3])) and MASK32;
  for T := 16 to 63 do
  begin
    S0 := (Rotr32(W[T-15], 7) xor Rotr32(W[T-15], 18) xor (W[T-15] shr 3)) and MASK32;
    S1 := (Rotr32(W[T-2], 17) xor Rotr32(W[T-2], 19) xor (W[T-2] shr 10)) and MASK32;
    W[T] := (W[T-16] + S0 + W[T-7] + S1) and MASK32;
  end;

  A := Self.FH[0]; B := Self.FH[1]; Cc := Self.FH[2]; D := Self.FH[3];
  E := Self.FH[4]; F := Self.FH[5]; G := Self.FH[6]; Hh := Self.FH[7];

  for T := 0 to 63 do
  begin
    S1 := (Rotr32(E, 6) xor Rotr32(E, 11) xor Rotr32(E, 25)) and MASK32;
    Ch := ((E and F) xor (((not E) and MASK32) and G)) and MASK32;
    Temp1 := (Hh + S1 + Ch + SHA256_K[T] + W[T]) and MASK32;
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

  Self.FH[0] := (Self.FH[0] + A) and MASK32;
  Self.FH[1] := (Self.FH[1] + B) and MASK32;
  Self.FH[2] := (Self.FH[2] + Cc) and MASK32;
  Self.FH[3] := (Self.FH[3] + D) and MASK32;
  Self.FH[4] := (Self.FH[4] + E) and MASK32;
  Self.FH[5] := (Self.FH[5] + F) and MASK32;
  Self.FH[6] := (Self.FH[6] + G) and MASK32;
  Self.FH[7] := (Self.FH[7] + Hh) and MASK32;
end;

function TSha256Digest.StateBytes: string;
var
  SB: TStringBuilder;
  I: Int;
begin
  SB := TStringBuilder.Create();
  for I := 0 to 7 do
    AppendBE32(SB, Self.FH[I]);
  Result := SB.ToString();
  SB.Free();
end;

{ ------------------------------------------------------------------ }
{ TSha512Digest                                                       }
{ ------------------------------------------------------------------ }

const
  SHA512_K: array[0..79] of UInt64 = (
    $428a2f98d728ae22, $7137449123ef65cd, $b5c0fbcfec4d3b2f, $e9b5dba58189dbbc,
    $3956c25bf348b538, $59f111f1b605d019, $923f82a4af194f9b, $ab1c5ed5da6d8118,
    $d807aa98a3030242, $12835b0145706fbe, $243185be4ee4b28c, $550c7dc3d5ffb4e2,
    $72be5d74f27b896f, $80deb1fe3b1696b1, $9bdc06a725c71235, $c19bf174cf692694,
    $e49b69c19ef14ad2, $efbe4786384f25e3, $0fc19dc68b8cd5b5, $240ca1cc77ac9c65,
    $2de92c6f592b0275, $4a7484aa6ea6e483, $5cb0a9dcbd41fbd4, $76f988da831153b5,
    $983e5152ee66dfab, $a831c66d2db43210, $b00327c898fb213f, $bf597fc7beef0ee4,
    $c6e00bf33da88fc2, $d5a79147930aa725, $06ca6351e003826f, $142929670a0e6e70,
    $27b70a8546d22ffc, $2e1b21385c26c926, $4d2c6dfc5ac42aed, $53380d139d95b3df,
    $650a73548baf63de, $766a0abb3c77b2a8, $81c2c92e47edaee6, $92722c851482353b,
    $a2bfe8a14cf10364, $a81a664bbc423001, $c24b8b70d0f89791, $c76c51a30654be30,
    $d192e819d6ef5218, $d69906245565a910, $f40e35855771202a, $106aa07032bbd1b8,
    $19a4c116b8d2d0c8, $1e376c085141ab53, $2748774cdf8eeb99, $34b0bcb5e19b48a8,
    $391c0cb3c5c95a63, $4ed8aa4ae3418acb, $5b9cca4f7763e373, $682e6ff3d6b2b8a3,
    $748f82ee5defb2fc, $78a5636f43172f60, $84c87814a1f0ab72, $8cc702081a6439ec,
    $90befffa23631e28, $a4506cebde82bde9, $bef9a3f7b2c67915, $c67178f2e372532b,
    $ca273eceea26619c, $d186b8c721c0c207, $eada7dd6cde0eb1e, $f57d4f7fee6ed178,
    $06f067aa72176fba, $0a637dc5a2c898a6, $113f9804bef90dae, $1b710b35131c471b,
    $28db77f523047d84, $32caab7b40c72493, $3c9ebe0a15c9bebc, $431d67c49c100d4c,
    $4cc5d4becb3e42b6, $597f299cfc657e2a, $5fcb6fab3ad6faec, $6c44198c4a475817
  );

function Rotr64(V: UInt64; ABits: Int): UInt64;
begin
  Result := (V shr ABits) or (V shl (64 - ABits));
end;

procedure TSha512Digest.InitState;
begin
  Self.FBlockSize := 128;
  Self.FLengthBytes := 16;
  Self.FH[0] := $6a09e667f3bcc908;
  Self.FH[1] := $bb67ae8584caa73b;
  Self.FH[2] := $3c6ef372fe94f82b;
  Self.FH[3] := $a54ff53a5f1d36f1;
  Self.FH[4] := $510e527fade682d1;
  Self.FH[5] := $9b05688c2b3e6c1f;
  Self.FH[6] := $1f83d9abfb41bd6b;
  Self.FH[7] := $5be0cd19137e2179;
end;

function TSha512Digest.DigestSize: Int;
begin
  Result := 64;
end;

procedure TSha512Digest.Compress;
var
  W: array[0..79] of UInt64;
  A, B, Cc, D, E, F, G, Hh: UInt64;
  S0, S1, Ch, Maj, Temp1, Temp2: UInt64;
  T, J: Int;
begin
  for T := 0 to 15 do
  begin
    W[T] := 0;
    for J := 0 to 7 do
      W[T] := (W[T] shl 8) or UInt64(Self.FBlock[T * 8 + J]);
  end;
  for T := 16 to 79 do
  begin
    S0 := Rotr64(W[T-15], 1) xor Rotr64(W[T-15], 8) xor (W[T-15] shr 7);
    S1 := Rotr64(W[T-2], 19) xor Rotr64(W[T-2], 61) xor (W[T-2] shr 6);
    W[T] := W[T-16] + S0 + W[T-7] + S1;
  end;

  A := Self.FH[0]; B := Self.FH[1]; Cc := Self.FH[2]; D := Self.FH[3];
  E := Self.FH[4]; F := Self.FH[5]; G := Self.FH[6]; Hh := Self.FH[7];

  for T := 0 to 79 do
  begin
    S1 := Rotr64(E, 14) xor Rotr64(E, 18) xor Rotr64(E, 41);
    Ch := (E and F) xor ((not E) and G);
    Temp1 := Hh + S1 + Ch + SHA512_K[T] + W[T];
    S0 := Rotr64(A, 28) xor Rotr64(A, 34) xor Rotr64(A, 39);
    Maj := (A and B) xor (A and Cc) xor (B and Cc);
    Temp2 := S0 + Maj;
    Hh := G;
    G := F;
    F := E;
    E := D + Temp1;
    D := Cc;
    Cc := B;
    B := A;
    A := Temp1 + Temp2;
  end;

  Self.FH[0] := Self.FH[0] + A;
  Self.FH[1] := Self.FH[1] + B;
  Self.FH[2] := Self.FH[2] + Cc;
  Self.FH[3] := Self.FH[3] + D;
  Self.FH[4] := Self.FH[4] + E;
  Self.FH[5] := Self.FH[5] + F;
  Self.FH[6] := Self.FH[6] + G;
  Self.FH[7] := Self.FH[7] + Hh;
end;

function TSha512Digest.StateBytes: string;
var
  SB: TStringBuilder;
  I, J: Int;
begin
  SB := TStringBuilder.Create();
  for I := 0 to 7 do
    for J := 7 downto 0 do
      SB.AppendByte(Byte((Self.FH[I] shr (J * 8)) and $FF));
  Result := SB.ToString();
  SB.Free();
end;

{ ------------------------------------------------------------------ }
{ One-shot wrappers                                                   }
{ ------------------------------------------------------------------ }

function DigestOf(D: THashDigest; const AData: string): string;
begin
  D.Update(AData);
  Result := D.Finish();
  D.Free();
end;

function DigestFileHex(D: THashDigest; const APath: string): string;
begin
  try
    D.UpdateFile(APath);
    Result := D.FinishHex();
  finally
    D.Free();
  end;
end;

function Sha1(const AData: string): string;
begin
  Result := DigestOf(TSha1Digest.Create(), AData);
end;

function Sha256(const AData: string): string;
begin
  Result := DigestOf(TSha256Digest.Create(), AData);
end;

function Sha512(const AData: string): string;
begin
  Result := DigestOf(TSha512Digest.Create(), AData);
end;

function Sha512Hex(const AData: string): string;
begin
  Result := DigestToHex(Sha512(AData));
end;

function Sha1FileHex(const APath: string): string;
begin
  Result := DigestFileHex(TSha1Digest.Create(), APath);
end;

function Sha256FileHex(const APath: string): string;
begin
  Result := DigestFileHex(TSha256Digest.Create(), APath);
end;

function Sha512FileHex(const APath: string): string;
begin
  Result := DigestFileHex(TSha512Digest.Create(), APath);
end;

function Sha1Hex(const AData: string): string;
begin
  Result := DigestToHex(Sha1(AData));
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
