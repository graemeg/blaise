{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.sha256;

// Pure-Pascal SHA-256 (FIPS 180-4) — the hash the Mach-O ad-hoc code
// signature's CodeDirectory uses for its page slots (Phase 4 of the
// macOS bring-up).  CPU/OS-invariant: all arithmetic runs in Int64
// with explicit 32-bit masking, so the same unit serves every host.
//
// Pinned by TSha256Tests against the FIPS vectors ('abc', '', the
// 448-bit two-block message) — do not modify without them.

interface

{ SHA-256 of ABytes; returns the 32-byte digest as a raw byte string. }
function Sha256(const ABytes: string): string;

{ Digest as lowercase hex (for tests/diagnostics). }
function Sha256Hex(const ABytes: string): string;

implementation

uses
  uStrCompat;

const
  HEX_DIGITS = '0123456789abcdef';

{ The 64 round constants (fractional parts of the cube roots of the
  first 64 primes). }
function KConst(AIdx: Int): Int64;
const
  K: array[0..63] of Int64 = (
    $428A2F98, $71374491, $B5C0FBCF, $E9B5DBA5,
    $3956C25B, $59F111F1, $923F82A4, $AB1C5ED5,
    $D807AA98, $12835B01, $243185BE, $550C7DC3,
    $72BE5D74, $80DEB1FE, $9BDC06A7, $C19BF174,
    $E49B69C1, $EFBE4786, $0FC19DC6, $240CA1CC,
    $2DE92C6F, $4A7484AA, $5CB0A9DC, $76F988DA,
    $983E5152, $A831C66D, $B00327C8, $BF597FC7,
    $C6E00BF3, $D5A79147, $06CA6351, $14292967,
    $27B70A85, $2E1B2138, $4D2C6DFC, $53380D13,
    $650A7354, $766A0ABB, $81C2C92E, $92722C85,
    $A2BFE8A1, $A81A664B, $C24B8B70, $C76C51A3,
    $D192E819, $D6990624, $F40E3585, $106AA070,
    $19A4C116, $1E376C08, $2748774C, $34B0BCB5,
    $391C0CB3, $4ED8AA4A, $5B9CCA4F, $682E6FF3,
    $748F82EE, $78A5636F, $84C87814, $8CC70208,
    $90BEFFFA, $A4506CEB, $BEF9A3F7, $C67178F2);
begin
  Result := K[AIdx];
end;

function Rotr(AVal: Int64; ABits: Int): Int64;
begin
  Result := ((AVal shr ABits) or (AVal shl (32 - ABits))) and $FFFFFFFF;
end;

function Sha256(const ABytes: string): string;
var
  H: array[0..7] of Int64;
  W: array[0..63] of Int64;
  Msg: string;
  BitLen: Int64;
  I, J, Blk, NBlks: Int;
  A, B, C, D, E, F, G, HH: Int64;
  S0, S1, Ch, Maj, T1, T2: Int64;
  Base: Int;
begin
  H[0] := $6A09E667; H[1] := $BB67AE85; H[2] := $3C6EF372;
  H[3] := $A54FF53A; H[4] := $510E527F; H[5] := $9B05688C;
  H[6] := $1F83D9AB; H[7] := $5BE0CD19;

  { padding: 0x80, zeros to 56 mod 64, then the 64-bit bit length BE }
  BitLen := Int64(Length(ABytes)) * 8;
  Msg := ABytes + Chr($80);
  while (Length(Msg) mod 64) <> 56 do
    Msg := Msg + Chr(0);
  for I := 7 downto 0 do
    Msg := Msg + Chr(Int32((BitLen shr (I * 8)) and $FF));

  NBlks := Length(Msg) div 64;
  for Blk := 0 to NBlks - 1 do
  begin
    Base := Blk * 64;
    for I := 0 to 15 do
      W[I] := (Int64(StrAt(Msg, Base + I * 4)) shl 24)
           or (Int64(StrAt(Msg, Base + I * 4 + 1)) shl 16)
           or (Int64(StrAt(Msg, Base + I * 4 + 2)) shl 8)
           or Int64(StrAt(Msg, Base + I * 4 + 3));
    for I := 16 to 63 do
    begin
      S0 := Rotr(W[I - 15], 7) xor Rotr(W[I - 15], 18)
        xor ((W[I - 15] shr 3) and $FFFFFFFF);
      S1 := Rotr(W[I - 2], 17) xor Rotr(W[I - 2], 19)
        xor ((W[I - 2] shr 10) and $FFFFFFFF);
      W[I] := (W[I - 16] + S0 + W[I - 7] + S1) and $FFFFFFFF;
    end;

    A := H[0]; B := H[1]; C := H[2]; D := H[3];
    E := H[4]; F := H[5]; G := H[6]; HH := H[7];
    for I := 0 to 63 do
    begin
      S1 := Rotr(E, 6) xor Rotr(E, 11) xor Rotr(E, 25);
      Ch := (E and F) xor ((not E) and G);
      T1 := (HH + S1 + Ch + KConst(I) + W[I]) and $FFFFFFFF;
      S0 := Rotr(A, 2) xor Rotr(A, 13) xor Rotr(A, 22);
      Maj := (A and B) xor (A and C) xor (B and C);
      T2 := (S0 + Maj) and $FFFFFFFF;
      HH := G; G := F; F := E;
      E := (D + T1) and $FFFFFFFF;
      D := C; C := B; B := A;
      A := (T1 + T2) and $FFFFFFFF;
    end;
    H[0] := (H[0] + A) and $FFFFFFFF;
    H[1] := (H[1] + B) and $FFFFFFFF;
    H[2] := (H[2] + C) and $FFFFFFFF;
    H[3] := (H[3] + D) and $FFFFFFFF;
    H[4] := (H[4] + E) and $FFFFFFFF;
    H[5] := (H[5] + F) and $FFFFFFFF;
    H[6] := (H[6] + G) and $FFFFFFFF;
    H[7] := (H[7] + HH) and $FFFFFFFF;
  end;

  Result := '';
  for I := 0 to 7 do
    for J := 3 downto 0 do
      Result := Result + Chr(Int32((H[I] shr (J * 8)) and $FF));
end;

function Sha256Hex(const ABytes: string): string;
var
  D: string;
  I, V: Int;
begin
  D := Sha256(ABytes);
  Result := '';
  for I := 0 to Length(D) - 1 do
  begin
    V := StrAt(D, I);
    Result := Result + Chr(StrAt(HEX_DIGITS, V shr 4))
      + Chr(StrAt(HEX_DIGITS, V and $F));
  end;
end;

end.
