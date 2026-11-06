{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Compression.Checksums - the CRC-32 and Adler-32 checksums that zip, gzip,
  PNG (CRC-32) and zlib (Adler-32) streams carry.

  Both are error-detection codes, not cryptographic digests: use
  Security.Crypto to authenticate data.

  Every function takes its input as a string of raw bytes.  The Update forms
  continue a running value, so data that arrives in pieces needs no
  concatenation:

    C := Crc32Update(0, Part1);
    C := Crc32Update(C, Part2);      // = Crc32(Part1 + Part2)

  A running CRC-32 starts at 0 and a running Adler-32 at 1, as in zlib. }

unit Compression.Checksums;

interface

{ CRC-32 (ISO-HDLC, reflected polynomial $EDB88320) of AData. }
function Crc32(const AData: string): UInt32;

{ Continues the CRC-32 ACrc (0 to start) over AData. }
function Crc32Update(ACrc: UInt32; const AData: string): UInt32;

{ Continues the CRC-32 ACrc over ACount bytes at ABuf. }
function Crc32UpdateBuf(ACrc: UInt32; ABuf: Pointer; ACount: Int): UInt32;

{ Adler-32 (RFC 1950) of AData. }
function Adler32(const AData: string): UInt32;

{ Continues the Adler-32 AAdler (1 to start) over AData. }
function Adler32Update(AAdler: UInt32; const AData: string): UInt32;

implementation

const
  ADLER_MOD = 65521;
  { The most bytes whose sums cannot overflow 32 bits before the modulo
    must be taken (zlib's NMAX). }
  ADLER_NMAX = 5552;

var
  CrcTable: array[0..255] of UInt32;

procedure BuildCrcTable;
var
  N, K: Int;
  C: UInt32;
begin
  for N := 0 to 255 do
  begin
    C := UInt32(N);
    for K := 0 to 7 do
      if (C and 1) <> 0 then
        C := $EDB88320 xor (C shr 1)
      else
        C := C shr 1;
    CrcTable[N] := C;
  end;
end;

function Crc32UpdateBuf(ACrc: UInt32; ABuf: Pointer; ACount: Int): UInt32;
var
  P: ^Byte;
  C: UInt32;
  I: Int;
begin
  P := ABuf;
  C := ACrc xor $FFFFFFFF;
  for I := 0 to ACount - 1 do
    C := CrcTable[(C xor (P + I)^) and $FF] xor (C shr 8);
  Result := C xor $FFFFFFFF;
end;

function Crc32Update(ACrc: UInt32; const AData: string): UInt32;
begin
  if Length(AData) = 0 then
    Exit(ACrc);
  Result := Crc32UpdateBuf(ACrc, Pointer(AData), Length(AData));
end;

function Crc32(const AData: string): UInt32;
begin
  Result := Crc32Update(0, AData);
end;

function Adler32Update(AAdler: UInt32; const AData: string): UInt32;
var
  A, B: UInt32;
  I, N, Chunk: Int;
begin
  A := AAdler and $FFFF;
  B := (AAdler shr 16) and $FFFF;
  I := 0;
  N := Length(AData);
  while I < N do
  begin
    Chunk := N - I;
    if Chunk > ADLER_NMAX then
      Chunk := ADLER_NMAX;
    while Chunk > 0 do
    begin
      A := A + Byte(AData[I]);
      B := B + A;
      I := I + 1;
      Chunk := Chunk - 1;
    end;
    A := A mod ADLER_MOD;
    B := B mod ADLER_MOD;
  end;
  Result := (B shl 16) or A;
end;

function Adler32(const AData: string): UInt32;
begin
  Result := Adler32Update(1, AData);
end;

initialization
  BuildCrcTable();

end.
