{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Compression.Checksums (CRC-32, Adler-32) and Compression.Deflate
  (raw RFC 1951 and zlib RFC 1950 streams).

  The decoder is checked against streams produced by zlib itself, committed
  under stdlib/src/test/resources/compression (see make-vectors.sh there) and
  embedded at compile time.  The encoder is checked by round trips through
  the decoder; interoperability with zlib is checked by the gzip and zip
  tests, whose output is read back by the system tools. }

unit Compression.Tests;

interface

uses
  blaise.testing, SysUtils, StrUtils, Security.Crypto,
  Compression.Checksums, Compression.Deflate;

type
  TChecksumTests = class(TTestCase)
  published
    procedure TestCrc32_KnownVectors;
    procedure TestCrc32_Incremental;
    procedure TestAdler32_KnownVectors;
    procedure TestAdler32_Incremental;
    procedure TestAdler32_LongInputReducesModulo;
  end;

  TInflateTests = class(TTestCase)
  published
    procedure TestInflate_FixedHuffmanFromZlib;
    procedure TestInflate_DynamicHuffmanFromZlib;
    procedure TestInflate_StoredFromZlib;
    procedure TestInflate_MultiBlockFarDistances;
    procedure TestInflateAt_ReportsEndOfStream;
    procedure TestInflate_TruncatedRaises;
    procedure TestInflate_ReservedBlockTypeRaises;
    procedure TestInflate_StoredLengthMismatchRaises;
    procedure TestInflate_DistanceBeforeStartRaises;
    procedure TestZlibDecompress_FromZlib;
    procedure TestZlibDecompress_BadHeaderRaises;
    procedure TestZlibDecompress_ChecksumMismatchRaises;
    procedure TestZlibDecompress_PresetDictionaryRaises;
  end;

  TDeflateTests = class(TTestCase)
  published
    procedure TestRoundTrip_Empty;
    procedure TestRoundTrip_OneByte;
    procedure TestRoundTrip_TextAllLevels;
    procedure TestRoundTrip_AllByteValues;
    procedure TestRoundTrip_LongRun;
    procedure TestRoundTrip_Incompressible;
    procedure TestRoundTrip_LargeText;
    procedure TestDeflate_CompressesText;
    procedure TestDeflate_LevelZeroIsStored;
    procedure TestZlibCompress_RoundTripAndHeader;
  end;

implementation

const
  LOREM = {$EMBEDSTR '../resources/compression/lorem.txt'};
  LOREM_FIXED = {$EMBEDSTR '../resources/compression/lorem.deflate-fixed'};
  LOREM_DYNAMIC = {$EMBEDSTR '../resources/compression/lorem.deflate-dynamic'};
  LOREM_STORED = {$EMBEDSTR '../resources/compression/lorem.deflate-stored'};
  LOREM_ZLIB = {$EMBEDSTR '../resources/compression/lorem.zlib'};
  WORDS_DEFLATE = {$EMBEDSTR '../resources/compression/words.deflate'};
  WORDS_LENGTH = 49152;
  WORDS_SHA256 = '509fc159e8ed1876f39d167697b39cbb50a6ad90d0f5fa258227c4f184089fc6';

function Bytes(const AValues: array of Int): string;
var
  SB: TStringBuilder;
  I: Int;
begin
  SB := TStringBuilder.Create();
  for I := 0 to High(AValues) do
    SB.AppendByte(AValues[I]);
  Result := SB.ToString();
  SB.Free();
end;

{ The string with byte AIndex replaced by AValue. }
function WithByte(const S: string; AIndex, AValue: Int): string;
begin
  Result := Copy(S, 0, AIndex) + Bytes([AValue]) +
    Copy(S, AIndex + 1, Length(S) - AIndex - 1);
end;

function AllByteValues: string;
var
  SB: TStringBuilder;
  I: Int;
begin
  SB := TStringBuilder.Create();
  for I := 0 to 255 do
    SB.AppendByte(I);
  Result := SB.ToString();
  SB.Free();
end;

{ Bytes from a linear congruential generator: no repeats for LZ77 to find. }
function NoiseBytes(ACount: Int): string;
var
  SB: TStringBuilder;
  I: Int;
  X: UInt32;
begin
  SB := TStringBuilder.Create();
  X := 12345;
  for I := 1 to ACount do
  begin
    X := X * 1103515245 + 12345;
    SB.AppendByte((X shr 16) and $FF);
  end;
  Result := SB.ToString();
  SB.Free();
end;

{ ------------------------------------------------------------------ }
{ TChecksumTests                                                      }
{ ------------------------------------------------------------------ }

procedure TChecksumTests.TestCrc32_KnownVectors;
begin
  { The CRC-32 "check" value (ISO-HDLC, as zip/gzip/PNG use). }
  AssertEquals('empty', Int64(0), Int64(Crc32('')));
  AssertEquals('123456789', Int64($CBF43926), Int64(Crc32('123456789')));
  AssertEquals('fox', Int64($414FA339),
    Int64(Crc32('The quick brown fox jumps over the lazy dog')));
end;

procedure TChecksumTests.TestCrc32_Incremental;
var
  C: UInt32;
begin
  C := Crc32Update(0, '1234');
  C := Crc32Update(C, '');
  C := Crc32Update(C, '56789');
  AssertEquals('split', Int64($CBF43926), Int64(C));
end;

procedure TChecksumTests.TestAdler32_KnownVectors;
begin
  AssertEquals('empty', Int64(1), Int64(Adler32('')));
  AssertEquals('Wikipedia', Int64($11E60398), Int64(Adler32('Wikipedia')));
end;

procedure TChecksumTests.TestAdler32_Incremental;
begin
  AssertEquals('split', Int64($11E60398),
    Int64(Adler32Update(Adler32Update(1, 'Wiki'), 'pedia')));
end;

procedure TChecksumTests.TestAdler32_LongInputReducesModulo;
begin
  { 100000 x $FF overflows the sums many times over: zlib gives $149A302C. }
  AssertEquals('100000 x FF', Int64($149A302C),
    Int64(Adler32(DupeString(Bytes([255]), 100000))));
end;

{ ------------------------------------------------------------------ }
{ TInflateTests                                                       }
{ ------------------------------------------------------------------ }

procedure TInflateTests.TestInflate_FixedHuffmanFromZlib;
begin
  AssertEquals('block type', 1, (Byte(LOREM_FIXED[0]) shr 1) and 3);
  AssertEquals('fixed', LOREM, Inflate(LOREM_FIXED));
end;

procedure TInflateTests.TestInflate_DynamicHuffmanFromZlib;
begin
  AssertEquals('block type', 2, (Byte(LOREM_DYNAMIC[0]) shr 1) and 3);
  AssertEquals('dynamic', LOREM, Inflate(LOREM_DYNAMIC));
end;

procedure TInflateTests.TestInflate_StoredFromZlib;
begin
  AssertEquals('block type', 0, (Byte(LOREM_STORED[0]) shr 1) and 3);
  AssertEquals('stored', LOREM, Inflate(LOREM_STORED));
end;

procedure TInflateTests.TestInflate_MultiBlockFarDistances;
var
  Plain: string;
begin
  Plain := Inflate(WORDS_DEFLATE);
  AssertEquals('length', WORDS_LENGTH, Length(Plain));
  AssertEquals('sha256', WORDS_SHA256, Sha256Hex(Plain));
end;

procedure TInflateTests.TestInflateAt_ReportsEndOfStream;
var
  EndPos: Int;
  Plain: string;
begin
  { A stream inside a larger buffer: the decoder stops at the final block
    and reports where the following data starts (gzip members, zlib
    trailers). }
  Plain := InflateAt('HEAD' + LOREM_FIXED + 'TAIL', 4, EndPos);
  AssertEquals('plain', LOREM, Plain);
  AssertEquals('end', 4 + Length(LOREM_FIXED), EndPos);
end;

procedure TInflateTests.TestInflate_TruncatedRaises;
begin
  AssertRaises('ECompressionError',
    procedure
    begin
      Inflate(Copy(LOREM_DYNAMIC, 0, Length(LOREM_DYNAMIC) - 10));
    end);
  AssertRaises('empty input', 'ECompressionError',
    procedure
    begin
      Inflate('');
    end);
end;

procedure TInflateTests.TestInflate_ReservedBlockTypeRaises;
begin
  { BFINAL=1, BTYPE=11 (reserved). }
  AssertRaises('ECompressionError',
    procedure
    begin
      Inflate(Bytes([7, 0, 0, 0]));
    end);
end;

procedure TInflateTests.TestInflate_StoredLengthMismatchRaises;
begin
  { Stored block: LEN = 3 but NLEN is not its complement. }
  AssertRaises('ECompressionError',
    procedure
    begin
      Inflate(Bytes([1, 3, 0, 0, 0, 65, 66, 67]));
    end);
end;

procedure TInflateTests.TestInflate_DistanceBeforeStartRaises;
begin
  { Fixed block whose first symbol is a match (length 3, distance 1) with
    no output yet to copy from: 1 + 01 (fixed), then length code 257 =
    0000001, distance code 0 = 00000, then end of block. }
  AssertRaises('ECompressionError',
    procedure
    begin
      Inflate(Bytes([$03, $02, $00]));
    end);
end;

procedure TInflateTests.TestZlibDecompress_FromZlib;
begin
  AssertEquals('zlib', LOREM, ZlibDecompress(LOREM_ZLIB));
end;

procedure TInflateTests.TestZlibDecompress_BadHeaderRaises;
begin
  { $78 $9D fails the FCHECK test ((CMF * 256 + FLG) mod 31 <> 0). }
  AssertRaises('ECompressionError',
    procedure
    begin
      ZlibDecompress(WithByte(LOREM_ZLIB, 1, $9D));
    end);
end;

procedure TInflateTests.TestZlibDecompress_ChecksumMismatchRaises;
begin
  AssertRaises('ECompressionError',
    procedure
    begin
      ZlibDecompress(WithByte(LOREM_ZLIB, Length(LOREM_ZLIB) - 1,
        Byte(LOREM_ZLIB[Length(LOREM_ZLIB) - 1]) xor 1));
    end);
end;

procedure TInflateTests.TestZlibDecompress_PresetDictionaryRaises;
begin
  { CMF $78, FLG $BB: FDICT set, FCHECK valid. }
  AssertRaises('ECompressionError',
    procedure
    begin
      ZlibDecompress(Bytes([$78, $BB, 0, 0, 0, 1, 3, 0]));
    end);
end;

{ ------------------------------------------------------------------ }
{ TDeflateTests                                                       }
{ ------------------------------------------------------------------ }

procedure TDeflateTests.TestRoundTrip_Empty;
begin
  AssertEquals('level 6', '', Inflate(Deflate('')));
  AssertEquals('level 0', '', Inflate(Deflate('', 0)));
end;

procedure TDeflateTests.TestRoundTrip_OneByte;
begin
  AssertEquals('one byte', 'x', Inflate(Deflate('x')));
end;

procedure TDeflateTests.TestRoundTrip_TextAllLevels;
var
  Level: Int;
begin
  for Level := 0 to 9 do
    AssertEquals('level ' + IntToStr(Level), LOREM,
      Inflate(Deflate(LOREM, Level)));
end;

procedure TDeflateTests.TestRoundTrip_AllByteValues;
var
  Data: string;
begin
  Data := DupeString(AllByteValues(), 40);
  AssertEquals('all bytes', Data, Inflate(Deflate(Data)));
end;

procedure TDeflateTests.TestRoundTrip_LongRun;
var
  Data: string;
begin
  { Distance-1 matches of the maximum length (258), many times over. }
  Data := DupeString('a', 100000) + 'b' + DupeString('a', 1000);
  AssertEquals('run', Data, Inflate(Deflate(Data, 9)));
  AssertTrue('run compresses well', Length(Deflate(Data, 9)) < 1000);
end;

procedure TDeflateTests.TestRoundTrip_Incompressible;
var
  Data, Comp: string;
begin
  { Noise falls back to stored blocks: the output grows by only a few bytes
    per 64 KiB, never by the 9-bit fixed-Huffman literal cost. }
  Data := NoiseBytes(150000);
  Comp := Deflate(Data);
  AssertEquals('noise', Data, Inflate(Comp));
  AssertTrue('bounded growth', Length(Comp) < Length(Data) + 100);
end;

procedure TDeflateTests.TestRoundTrip_LargeText;
var
  Data: string;
  Level: Int;
begin
  Data := Inflate(WORDS_DEFLATE);
  for Level := 1 to 9 do
    AssertEquals('level ' + IntToStr(Level), WORDS_SHA256,
      Sha256Hex(Inflate(Deflate(Data, Level))));
end;

procedure TDeflateTests.TestDeflate_CompressesText;
var
  Data: string;
begin
  Data := Inflate(WORDS_DEFLATE);
  { zlib level 6 manages 14807 bytes; a fixed-Huffman-only encoder would
    need well over 20000. }
  AssertTrue('ratio ' + IntToStr(Length(Deflate(Data))),
    Length(Deflate(Data)) < 18000);
  AssertTrue('lorem', Length(Deflate(LOREM)) < Length(LOREM) div 2);
end;

procedure TDeflateTests.TestDeflate_LevelZeroIsStored;
var
  Comp: string;
begin
  Comp := Deflate(LOREM, 0);
  AssertEquals('block type', 0, (Byte(Comp[0]) shr 1) and 3);
  AssertEquals('size', Length(LOREM) + 5, Length(Comp));
end;

procedure TDeflateTests.TestZlibCompress_RoundTripAndHeader;
var
  Comp: string;
begin
  Comp := ZlibCompress(LOREM);
  AssertEquals('CMF', $78, Byte(Comp[0]));
  AssertEquals('FCHECK', 0, (Byte(Comp[0]) * 256 + Byte(Comp[1])) mod 31);
  AssertEquals('round trip', LOREM, ZlibDecompress(Comp));
  AssertEquals('empty', '', ZlibDecompress(ZlibCompress('')));
end;

initialization
  RegisterTest(TChecksumTests);
  RegisterTest(TInflateTests);
  RegisterTest(TDeflateTests);

end.
