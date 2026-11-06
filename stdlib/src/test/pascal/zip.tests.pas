{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Compression.Zip.  The reader is checked against an archive made
  by zip(1) and hand-built archives for Zip64, encryption, an unsupported
  method and a path-traversal name (see
  stdlib/src/test/resources/compression/make-vectors.sh); the writer by
  round trips and, where unzip(1) is installed, by unzip itself. }

unit Zip.Tests;

interface

uses
  blaise.testing, SysUtils, StrUtils, DateUtils, Compression.Checksums,
  Compression.Deflate, Compression.Zip;

type
  TZipReaderTests = class(TTestCase)
  private
    FDir: string;
  public
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestList_EntriesFromZipTool;
    procedure TestList_ModifiedTime;
    procedure TestRead_EntryBytes;
    procedure TestRead_FindByName;
    procedure TestRead_FromFile;
    procedure TestRead_Zip64;
    procedure TestRead_EncryptedRefused;
    procedure TestRead_UnsupportedMethodRefused;
    procedure TestRead_CrcMismatchRaises;
    procedure TestOpen_NotAZipRaises;
    procedure TestOpen_TruncatedRaises;
    procedure TestSafePath_Accepted;
    procedure TestSafePath_Refused;
    procedure TestExtractAll;
    procedure TestExtractAll_TraversalRefused;
  end;

  TZipWriterTests = class(TTestCase)
  private
    FDir: string;
  public
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestWrite_RoundTrip;
    procedure TestWrite_IncompressibleIsStored;
    procedure TestWrite_ModifiedTime;
    procedure TestWrite_ManyEntries;
    procedure TestWrite_DuplicateNameRaises;
    procedure TestWrite_UnsafeNameRaises;
    procedure TestWrite_AddFile;
    procedure TestWrite_ReadByUnzipTool;
  end;

implementation

const
  LOREM = {$EMBEDSTR '../resources/compression/lorem.txt'};
  SAMPLE_ZIP = {$EMBEDSTR '../resources/compression/sample.zip'};
  ZIP64_ZIP = {$EMBEDSTR '../resources/compression/zip64.zip'};
  ENCRYPTED_ZIP = {$EMBEDSTR '../resources/compression/encrypted.zip'};
  LZMA_ZIP = {$EMBEDSTR '../resources/compression/lzma.zip'};
  TRAVERSAL_ZIP = {$EMBEDSTR '../resources/compression/traversal.zip'};
  RAW_BIN = 'stored bytes' + #0 + #1 + #2 + #10;

function TempDir(const ATag: string): string;
begin
  Result := ExcludeTrailingPathDelimiter(GetTempDir()) + '/blaise-zip-' + ATag +
    '-' + IntToStr(GetProcessID());
  Exec('rm -rf ''' + Result + '''');
  ForceDirectories(Result);
end;

function NoiseBytes(ACount: Int): string;
var
  SB: TStringBuilder;
  I: Int;
  X: UInt32;
begin
  SB := TStringBuilder.Create();
  X := 99;
  for I := 1 to ACount do
  begin
    X := X * 1103515245 + 12345;
    SB.AppendByte((X shr 16) and $FF);
  end;
  Result := SB.ToString();
  SB.Free();
end;

{ ------------------------------------------------------------------ }
{ TZipReaderTests                                                     }
{ ------------------------------------------------------------------ }

procedure TZipReaderTests.SetUp;
begin
  FDir := TempDir('read');
end;

procedure TZipReaderTests.TearDown;
begin
  Exec('rm -rf ''' + FDir + '''');
end;

procedure TZipReaderTests.TestList_EntriesFromZipTool;
var
  Z: TZipReader;
  E: TZipEntry;
begin
  Z := TZipReader.CreateFromBytes(SAMPLE_ZIP);
  try
    AssertEquals('count', 3, Z.Count);
    E := Z.Entries[0];
    AssertEquals('0 name', 'docs/', E.Name);
    AssertTrue('0 dir', E.IsDirectory);
    E := Z.Entries[1];
    AssertEquals('1 name', 'docs/lorem.txt', E.Name);
    AssertFalse('1 not dir', E.IsDirectory);
    AssertEquals('1 method', ZIP_DEFLATED, E.Method);
    AssertEquals('1 size', Int64(515), E.UncompressedSize);
    AssertEquals('1 packed', Int64(124), E.CompressedSize);
    AssertEquals('1 crc', Int64($8E8352DA), Int64(E.Crc));
    AssertFalse('1 not encrypted', E.IsEncrypted);
    E := Z.Entries[2];
    AssertEquals('2 name', 'raw.bin', E.Name);
    AssertEquals('2 method', ZIP_STORED, E.Method);
    AssertEquals('2 size', Int64(16), E.UncompressedSize);
    AssertEquals('2 crc', Int64($65B2CEEF), Int64(E.Crc));
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestList_ModifiedTime;
var
  Z: TZipReader;
  T: TDateTime;
begin
  { touch -t 202405061530.42: DOS times keep even seconds, so 42 survives. }
  Z := TZipReader.CreateFromBytes(SAMPLE_ZIP);
  try
    T := Z.Entries[1].ModifiedTime;
    AssertEquals('year', 2024, T.Date.Year);
    AssertEquals('month', 5, T.Date.Month);
    AssertEquals('day', 6, T.Date.Day);
    AssertEquals('hour', 15, T.Time.Hour);
    AssertEquals('minute', 30, T.Time.Minute);
    AssertEquals('second', 42, T.Time.Second);
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestRead_EntryBytes;
var
  Z: TZipReader;
begin
  Z := TZipReader.CreateFromBytes(SAMPLE_ZIP);
  try
    AssertEquals('deflated', LOREM, Z.ReadBytes(Z.Entries[1]));
    AssertEquals('stored', RAW_BIN, Z.ReadBytes(Z.Entries[2]));
    AssertEquals('directory', '', Z.ReadBytes(Z.Entries[0]));
    AssertEquals('by name', LOREM, Z.ReadBytes('docs/lorem.txt'));
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestRead_FindByName;
var
  Z: TZipReader;
begin
  Z := TZipReader.CreateFromBytes(SAMPLE_ZIP);
  try
    AssertNotNull('found', Z.Find('raw.bin'));
    AssertEquals('name', 'raw.bin', Z.Find('raw.bin').Name);
    AssertNull('missing', Z.Find('nothing.txt'));
    AssertNull('case-sensitive', Z.Find('RAW.BIN'));
    AssertRaises('EZipError',
      procedure
      begin
        Z.ReadBytes('nothing.txt');
      end);
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestRead_FromFile;
var
  Z: TZipReader;
  Path: string;
begin
  Path := FDir + '/sample.zip';
  WriteFile(Path, SAMPLE_ZIP);
  Z := TZipReader.Create(Path);
  try
    AssertEquals('count', 3, Z.Count);
    AssertEquals('deflated', LOREM, Z.ReadBytes('docs/lorem.txt'));
    AssertEquals('stored', RAW_BIN, Z.ReadBytes('raw.bin'));
  finally
    Z.Free();
  end;
  AssertRaises('missing file', 'EStreamError',
    procedure
    begin
      TZipReader.Create(FDir + '/no-such.zip');
    end);
end;

procedure TZipReaderTests.TestRead_Zip64;
var
  Z: TZipReader;
begin
  { Sizes and offset are $FFFFFFFF in the central directory, with the real
    values in the Zip64 extra field; the end record is found through the
    Zip64 locator. }
  Z := TZipReader.CreateFromBytes(ZIP64_ZIP);
  try
    AssertEquals('count', 1, Z.Count);
    AssertEquals('name', 'zip64/hello.txt', Z.Entries[0].Name);
    AssertEquals('size', Int64(28), Z.Entries[0].UncompressedSize);
    AssertEquals('packed', Int64(30), Z.Entries[0].CompressedSize);
    AssertEquals('data', 'Hello from a Zip64 archive.' + #10,
      Z.ReadBytes(Z.Entries[0]));
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestRead_EncryptedRefused;
var
  Z: TZipReader;
begin
  Z := TZipReader.CreateFromBytes(ENCRYPTED_ZIP);
  try
    AssertTrue('flagged', Z.Entries[0].IsEncrypted);
    AssertRaises('EZipUnsupported',
      procedure
      begin
        Z.ReadBytes(Z.Entries[0]);
      end);
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestRead_UnsupportedMethodRefused;
var
  Z: TZipReader;
begin
  Z := TZipReader.CreateFromBytes(LZMA_ZIP);
  try
    AssertEquals('method', 14, Z.Entries[0].Method);
    AssertRaises('EZipUnsupported',
      procedure
      begin
        Z.ReadBytes(Z.Entries[0]);
      end);
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestRead_CrcMismatchRaises;
var
  Z: TZipReader;
  Corrupt: string;
  At: Int;
begin
  At := Pos('stored bytes', SAMPLE_ZIP);
  AssertTrue('found data', At > 0);
  Corrupt := Copy(SAMPLE_ZIP, 0, At) + 'S' +
    Copy(SAMPLE_ZIP, At + 1, Length(SAMPLE_ZIP) - At - 1);
  Z := TZipReader.CreateFromBytes(Corrupt);
  try
    AssertRaises('EZipError',
      procedure
      begin
        Z.ReadBytes('raw.bin');
      end);
  finally
    Z.Free();
  end;
end;

procedure TZipReaderTests.TestOpen_NotAZipRaises;
begin
  AssertRaises('text', 'EZipError',
    procedure
    begin
      TZipReader.CreateFromBytes('this is not a zip archive at all');
    end);
  AssertRaises('empty', 'EZipError',
    procedure
    begin
      TZipReader.CreateFromBytes('');
    end);
end;

procedure TZipReaderTests.TestOpen_TruncatedRaises;
begin
  { The first 200 bytes are gone: the end record survives, but its offsets
    no longer lead to a central directory. }
  AssertRaises('EZipError',
    procedure
    begin
      TZipReader.CreateFromBytes(Copy(SAMPLE_ZIP, 200, Length(SAMPLE_ZIP) - 200));
    end);
end;

procedure TZipReaderTests.TestSafePath_Accepted;
begin
  AssertEquals('plain', '/out/a/b.txt', ZipSafePath('/out', 'a/b.txt'));
  AssertEquals('trailing slash on dir', '/out/a/b.txt', ZipSafePath('/out/', 'a/b.txt'));
  AssertEquals('dot segments', '/out/a/b.txt', ZipSafePath('/out', './a//b.txt'));
  AssertEquals('directory entry', '/out/a', ZipSafePath('/out', 'a/'));
  AssertEquals('dots in a name', '/out/a..b/c', ZipSafePath('/out', 'a..b/c'));
end;

procedure TZipReaderTests.TestSafePath_Refused;
var
  Bad: array[0..7] of string;
  I: Int;
begin
  Bad[0] := '../evil.txt';
  Bad[1] := 'a/../../evil.txt';
  Bad[2] := 'a/..';
  Bad[3] := '/etc/passwd';
  Bad[4] := 'C:/Windows/evil.dll';
  Bad[5] := 'a\..\..\evil.txt';
  Bad[6] := '';
  Bad[7] := 'a' + #0 + '.txt';
  for I := 0 to 7 do
    AssertRaises('#' + IntToStr(I), 'EZipError',
      procedure
      begin
        ZipSafePath('/out', Bad[I]);
      end);
end;

procedure TZipReaderTests.TestExtractAll;
var
  Z: TZipReader;
begin
  Z := TZipReader.CreateFromBytes(SAMPLE_ZIP);
  try
    Z.ExtractAll(FDir + '/x');
  finally
    Z.Free();
  end;
  AssertTrue('dir', DirectoryExists(FDir + '/x/docs'));
  AssertEquals('lorem', LOREM, ReadFile(FDir + '/x/docs/lorem.txt'));
  AssertEquals('raw', RAW_BIN, ReadFile(FDir + '/x/raw.bin'));
end;

procedure TZipReaderTests.TestExtractAll_TraversalRefused;
var
  Z: TZipReader;
begin
  Z := TZipReader.CreateFromBytes(TRAVERSAL_ZIP);
  try
    AssertEquals('name', '../evil.txt', Z.Entries[0].Name);
    AssertRaises('EZipError',
      procedure
      begin
        Z.ExtractAll(FDir + '/x');
      end);
  finally
    Z.Free();
  end;
  AssertFalse('nothing escaped', FileExists(FDir + '/evil.txt'));
end;

{ ------------------------------------------------------------------ }
{ TZipWriterTests                                                     }
{ ------------------------------------------------------------------ }

procedure TZipWriterTests.SetUp;
begin
  FDir := TempDir('write');
end;

procedure TZipWriterTests.TearDown;
begin
  Exec('rm -rf ''' + FDir + '''');
end;

procedure TZipWriterTests.TestWrite_RoundTrip;
var
  W: TZipWriter;
  Z: TZipReader;
  Noise, Archive: string;
begin
  Noise := NoiseBytes(3000);
  W := TZipWriter.CreateInMemory();
  try
    W.AddDirectory('assets');
    W.AddEntry('assets/lorem.txt', LOREM);
    W.AddEntry('assets/noise.bin', Noise, ZIP_STORED);
    W.AddEntry('empty.txt', '');
    W.Close();
    Archive := W.Bytes();
  finally
    W.Free();
  end;
  Z := TZipReader.CreateFromBytes(Archive);
  try
    AssertEquals('count', 4, Z.Count);
    AssertEquals('dir name', 'assets/', Z.Entries[0].Name);
    AssertTrue('dir', Z.Entries[0].IsDirectory);
    AssertEquals('deflated', ZIP_DEFLATED, Z.Entries[1].Method);
    AssertTrue('smaller', Z.Entries[1].CompressedSize < Z.Entries[1].UncompressedSize);
    AssertEquals('crc', Int64(Crc32(LOREM)), Int64(Z.Entries[1].Crc));
    AssertEquals('lorem', LOREM, Z.ReadBytes('assets/lorem.txt'));
    AssertEquals('stored', ZIP_STORED, Z.Entries[2].Method);
    AssertEquals('noise', Noise, Z.ReadBytes('assets/noise.bin'));
    AssertEquals('empty', '', Z.ReadBytes('empty.txt'));
  finally
    Z.Free();
  end;
end;

procedure TZipWriterTests.TestWrite_IncompressibleIsStored;
var
  W: TZipWriter;
  Z: TZipReader;
  Noise: string;
begin
  { Deflating noise would make it larger, so it is stored, as zip(1) does. }
  Noise := NoiseBytes(5000);
  W := TZipWriter.CreateInMemory();
  W.AddEntry('noise.bin', Noise);
  W.Close();
  Z := TZipReader.CreateFromBytes(W.Bytes());
  try
    AssertEquals('method', ZIP_STORED, Z.Entries[0].Method);
    AssertEquals('data', Noise, Z.ReadBytes(Z.Entries[0]));
  finally
    Z.Free();
    W.Free();
  end;
end;

procedure TZipWriterTests.TestWrite_ModifiedTime;
var
  W: TZipWriter;
  Z: TZipReader;
  T: TDateTime;
begin
  W := TZipWriter.CreateInMemory();
  W.ModifiedTime := MakeDateTime(MakeDate(2023, 12, 25), MakeTime(10, 20, 31));
  W.AddEntry('a.txt', 'a');
  W.Close();
  Z := TZipReader.CreateFromBytes(W.Bytes());
  try
    T := Z.Entries[0].ModifiedTime;
    AssertEquals('date', '2023-12-25', T.Date.ToString());
    { Two-second resolution: 31 is stored as 30. }
    AssertEquals('time', '10:20:30', T.Time.ToString());
  finally
    Z.Free();
    W.Free();
  end;
end;

procedure TZipWriterTests.TestWrite_ManyEntries;
var
  W: TZipWriter;
  Z: TZipReader;
  I: Int;
begin
  W := TZipWriter.CreateInMemory();
  for I := 0 to 499 do
    W.AddEntry('dir' + IntToStr(I mod 7) + '/file' + IntToStr(I) + '.txt',
      'content of ' + IntToStr(I));
  W.Close();
  Z := TZipReader.CreateFromBytes(W.Bytes());
  try
    AssertEquals('count', 500, Z.Count);
    AssertEquals('last', 'content of 499', Z.ReadBytes('dir2/file499.txt'));
    AssertEquals('first', 'content of 0', Z.ReadBytes('dir0/file0.txt'));
  finally
    Z.Free();
    W.Free();
  end;
end;

procedure TZipWriterTests.TestWrite_DuplicateNameRaises;
var
  W: TZipWriter;
begin
  W := TZipWriter.CreateInMemory();
  try
    W.AddEntry('a.txt', 'one');
    AssertRaises('EZipError',
      procedure
      begin
        W.AddEntry('a.txt', 'two');
      end);
  finally
    W.Free();
  end;
end;

procedure TZipWriterTests.TestWrite_UnsafeNameRaises;
var
  W: TZipWriter;
begin
  W := TZipWriter.CreateInMemory();
  try
    AssertRaises('parent', 'EZipError',
      procedure
      begin
        W.AddEntry('../a.txt', 'x');
      end);
    AssertRaises('absolute', 'EZipError',
      procedure
      begin
        W.AddEntry('/a.txt', 'x');
      end);
  finally
    W.Free();
  end;
end;

procedure TZipWriterTests.TestWrite_AddFile;
var
  W: TZipWriter;
  Z: TZipReader;
begin
  WriteFile(FDir + '/src.txt', LOREM);
  W := TZipWriter.Create(FDir + '/out.zip');
  try
    W.AddFile('copied/src.txt', FDir + '/src.txt');
    W.Close();
  finally
    W.Free();
  end;
  Z := TZipReader.Create(FDir + '/out.zip');
  try
    AssertEquals('content', LOREM, Z.ReadBytes('copied/src.txt'));
  finally
    Z.Free();
  end;
end;

procedure TZipWriterTests.TestWrite_ReadByUnzipTool;
var
  W: TZipWriter;
  Path: string;
begin
  { Interoperability: unzip(1) must list, test and extract what TZipWriter
    writes.  Skipped where unzip is not installed. }
  if not FileExists('/usr/bin/unzip') then
    Exit;
  Path := FDir + '/interop.zip';
  W := TZipWriter.Create(Path);
  try
    W.AddDirectory('pack/');
    W.AddEntry('pack/lorem.txt', DupeString(LOREM, 20));
    W.AddEntry('pack/raw.bin', RAW_BIN, ZIP_STORED);
    W.AddEntry('pack/noise.bin', NoiseBytes(70000));
    W.Close();
  finally
    W.Free();
  end;
  AssertEquals('unzip -t', 0, Exec('/usr/bin/unzip -tq ''' + Path + ''' > /dev/null'));
  AssertEquals('unzip -d', 0,
    Exec('/usr/bin/unzip -q ''' + Path + ''' -d ''' + FDir + '/x'''));
  AssertEquals('lorem', DupeString(LOREM, 20), ReadFile(FDir + '/x/pack/lorem.txt'));
  AssertEquals('raw', RAW_BIN, ReadFile(FDir + '/x/pack/raw.bin'));
  AssertEquals('noise', NoiseBytes(70000), ReadFile(FDir + '/x/pack/noise.bin'));
end;

initialization
  RegisterTest(TZipReaderTests);
  RegisterTest(TZipWriterTests);

end.
