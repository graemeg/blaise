{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Compression.Gzip (RFC 1952).  The read side is checked against
  files made by gzip(1) and a member with every optional header field (see
  stdlib/src/test/resources/compression/make-vectors.sh); the write side by
  round trips and, where gzip(1) is installed, by gzip itself. }

unit Gzip.Tests;

interface

uses
  blaise.testing, SysUtils, StrUtils, Compression.Deflate, Compression.Gzip;

type
  TGzipTests = class(TTestCase)
  published
    procedure TestDecompress_FromGzipTool;
    procedure TestDecompress_ConcatenatedMembers;
    procedure TestDecompress_AllHeaderFlags;
    procedure TestDecompress_HeaderOfFirstMember;
    procedure TestDecompress_BadHeaderCrcRaises;
    procedure TestDecompress_BadDataCrcRaises;
    procedure TestDecompress_BadSizeRaises;
    procedure TestDecompress_TruncatedRaises;
    procedure TestDecompress_NotGzipRaises;
    procedure TestDecompress_ReservedFlagRaises;
    procedure TestDecompress_TrailingZerosIgnored;
    procedure TestDecompress_TrailingGarbageRaises;
    procedure TestCompress_RoundTrip;
    procedure TestCompress_HeaderFields;
    procedure TestIsGzip;
    procedure TestCompress_ReadByGzipTool;
  end;

implementation

const
  LOREM = {$EMBEDSTR '../resources/compression/lorem.txt'};
  LOREM_GZ = {$EMBEDSTR '../resources/compression/lorem.txt.gz'};
  CONCAT_GZ = {$EMBEDSTR '../resources/compression/concat.gz'};
  FLAGS_GZ = {$EMBEDSTR '../resources/compression/flags.gz'};

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

function WithByte(const S: string; AIndex, AValue: Int): string;
begin
  Result := Copy(S, 0, AIndex) + Bytes([AValue]) +
    Copy(S, AIndex + 1, Length(S) - AIndex - 1);
end;

function FlipByte(const S: string; AIndex: Int): string;
begin
  Result := WithByte(S, AIndex, Byte(S[AIndex]) xor $FF);
end;

procedure TGzipTests.TestDecompress_FromGzipTool;
begin
  AssertEquals('lorem', LOREM, GzipDecompress(LOREM_GZ));
end;

procedure TGzipTests.TestDecompress_ConcatenatedMembers;
begin
  { RFC 1952 2.2: a file may hold several members; the result is their
    contents in order, as gzip -d gives. }
  AssertEquals('both members', 'first member' + #10 + 'second member' + #10,
    GzipDecompress(CONCAT_GZ));
end;

procedure TGzipTests.TestDecompress_AllHeaderFlags;
begin
  AssertEquals('body', 'gzip header flags test' + #10, GzipDecompress(FLAGS_GZ));
end;

procedure TGzipTests.TestDecompress_HeaderOfFirstMember;
var
  H: TGzipHeader;
begin
  GzipDecompress(FLAGS_GZ, H);
  AssertEquals('name', 'flags.txt', H.FileName);
  AssertEquals('comment', 'a comment', H.Comment);
  AssertEquals('mtime', Int64(1700000000), H.ModTime);
  AssertEquals('os', 3, H.OS);
  AssertEquals('extra', 'AP' + Bytes([4, 0, 1, 2, 3, 4]), H.Extra);
  GzipDecompress(LOREM_GZ, H);
  AssertEquals('gzip tool name', 'lorem.txt', H.FileName);
  AssertEquals('no comment', '', H.Comment);
end;

procedure TGzipTests.TestDecompress_BadHeaderCrcRaises;
begin
  { The FHCRC field sits just before the deflate data; the header is 10
    bytes + 2 + 8 extra + 'flags.txt'#0 + 'a comment'#0 = 40 bytes. }
  AssertRaises('ECompressionError',
    procedure
    begin
      GzipDecompress(FlipByte(FLAGS_GZ, 40));
    end);
end;

procedure TGzipTests.TestDecompress_BadDataCrcRaises;
begin
  AssertRaises('ECompressionError',
    procedure
    begin
      GzipDecompress(FlipByte(LOREM_GZ, Length(LOREM_GZ) - 8));
    end);
end;

procedure TGzipTests.TestDecompress_BadSizeRaises;
begin
  AssertRaises('ECompressionError',
    procedure
    begin
      GzipDecompress(FlipByte(LOREM_GZ, Length(LOREM_GZ) - 1));
    end);
end;

procedure TGzipTests.TestDecompress_TruncatedRaises;
begin
  AssertRaises('in trailer', 'ECompressionError',
    procedure
    begin
      GzipDecompress(Copy(LOREM_GZ, 0, Length(LOREM_GZ) - 3));
    end);
  AssertRaises('in header', 'ECompressionError',
    procedure
    begin
      GzipDecompress(Copy(LOREM_GZ, 0, 12));
    end);
end;

procedure TGzipTests.TestDecompress_NotGzipRaises;
begin
  AssertRaises('text', 'ECompressionError',
    procedure
    begin
      GzipDecompress('plain text, not gzip');
    end);
  AssertRaises('empty', 'ECompressionError',
    procedure
    begin
      GzipDecompress('');
    end);
end;

procedure TGzipTests.TestDecompress_ReservedFlagRaises;
begin
  { FLG bit 5 is reserved: a decoder must refuse it. }
  AssertRaises('ECompressionError',
    procedure
    begin
      GzipDecompress(WithByte(LOREM_GZ, 3, Byte(LOREM_GZ[3]) or $20));
    end);
end;

procedure TGzipTests.TestDecompress_TrailingZerosIgnored;
begin
  { Zero padding after the last member (tape blocking) is ignored, as
    gzip -d does. }
  AssertEquals('padded', LOREM, GzipDecompress(LOREM_GZ + Bytes([0, 0, 0, 0])));
end;

procedure TGzipTests.TestDecompress_TrailingGarbageRaises;
begin
  AssertRaises('ECompressionError',
    procedure
    begin
      GzipDecompress(LOREM_GZ + 'junk');
    end);
end;

procedure TGzipTests.TestCompress_RoundTrip;
var
  Big: string;
begin
  AssertEquals('lorem', LOREM, GzipDecompress(GzipCompress(LOREM)));
  AssertEquals('empty', '', GzipDecompress(GzipCompress('')));
  Big := DupeString(LOREM, 300);
  AssertEquals('level 1', Big, GzipDecompress(GzipCompress(Big, 1)));
  AssertEquals('level 9', Big, GzipDecompress(GzipCompress(Big, 9)));
  AssertEquals('two members', LOREM + Big,
    GzipDecompress(GzipCompress(LOREM) + GzipCompress(Big)));
end;

procedure TGzipTests.TestCompress_HeaderFields;
var
  Gz: string;
  H: TGzipHeader;
begin
  Gz := GzipCompress(LOREM, 6, 'notes.txt', 1234567890);
  AssertEquals('magic 1', $1F, Byte(Gz[0]));
  AssertEquals('magic 2', $8B, Byte(Gz[1]));
  AssertEquals('method', 8, Byte(Gz[2]));
  AssertEquals('data', LOREM, GzipDecompress(Gz, H));
  AssertEquals('name', 'notes.txt', H.FileName);
  AssertEquals('mtime', Int64(1234567890), H.ModTime);
end;

procedure TGzipTests.TestIsGzip;
begin
  AssertTrue('gzip file', IsGzip(LOREM_GZ));
  AssertFalse('text', IsGzip(LOREM));
  AssertFalse('empty', IsGzip(''));
  AssertFalse('one byte', IsGzip(Bytes([$1F])));
end;

procedure TGzipTests.TestCompress_ReadByGzipTool;
var
  Base: string;
begin
  { Interoperability: gzip(1) must accept what GzipCompress writes.  Skipped
    where gzip is not installed. }
  if not FileExists('/usr/bin/gzip') then
    Exit;
  Base := ExcludeTrailingPathDelimiter(GetTempDir()) + '/blaise-gzip-' +
    IntToStr(GetProcessID());
  WriteFile(Base + '.gz', GzipCompress(DupeString(LOREM, 50), 9, 'lorem.txt', 0));
  try
    AssertEquals('gzip -t', 0, Exec('/usr/bin/gzip -t ''' + Base + '.gz'''));
    AssertEquals('gzip -d', 0,
      Exec('/usr/bin/gzip -dc ''' + Base + '.gz'' > ''' + Base + '.txt'''));
    AssertEquals('content', DupeString(LOREM, 50), ReadFile(Base + '.txt'));
  finally
    DeleteFile(Base + '.gz');
    DeleteFile(Base + '.txt');
  end;
end;

initialization
  RegisterTest(TGzipTests);

end.
