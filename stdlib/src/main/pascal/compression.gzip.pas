{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Compression.Gzip - the gzip file format (RFC 1952).

    Gz   := GzipCompress(Data);
    Data := GzipDecompress(ReadFile('level.dat'));

  Data is a string of raw bytes, as in Compression.Deflate.

  GzipDecompress reads every member of a file, as gzip -d does, and returns
  their contents joined.  Each member's header may carry any of the optional
  fields (FEXTRA, FNAME, FCOMMENT, FHCRC); each member's CRC-32 and length
  are verified, and its header CRC when present.  Zero bytes after the last
  member (tape padding) are ignored; anything else after it, a reserved
  flag, or a method other than deflate raises ECompressionError.

  GzipCompress writes a single member, with an optional file name and
  modification time. }

unit Compression.Gzip;

interface

uses
  Compression.Deflate;

type
  { The header fields of a gzip member. }
  TGzipHeader = record
    FileName: string;   { FNAME, '' when absent (ISO 8859-1 bytes as stored) }
    Comment: string;    { FCOMMENT, '' when absent }
    Extra: string;      { the raw FEXTRA field, '' when absent }
    ModTime: Int64;     { MTIME, Unix seconds; 0 when not recorded }
    OS: Int;            { OS byte: 0 FAT, 3 Unix, 255 unknown, ... }
  end;

{ A gzip member holding AData, compressed at ALevel (0-9).  AFileName and
  AModTime (Unix seconds), when given, are recorded in the header. }
function GzipCompress(const AData: string; ALevel: Int = 6;
  const AFileName: string = ''; AModTime: Int64 = 0): string;

{ The contents of every member of the gzip data AData, joined. }
function GzipDecompress(const AData: string): string; overload;

{ As above; AHeader receives the header of the first member. }
function GzipDecompress(const AData: string; out AHeader: TGzipHeader): string; overload;

{ True when AData starts with the gzip magic bytes $1F $8B. }
function IsGzip(const AData: string): Boolean;

implementation

uses
  StrUtils, Compression.Checksums;

const
  FHCRC = $02;
  FEXTRA = $04;
  FNAME = $08;
  FCOMMENT = $10;
  FRESERVED = $E0;
  OS_UNIX = 3;

procedure Fail(const AMsg: string);
begin
  raise ECompressionError.Create('Invalid gzip data: ' + AMsg);
end;

function IsGzip(const AData: string): Boolean;
begin
  Result := (Length(AData) >= 2) and (Byte(AData[0]) = $1F) and
    (Byte(AData[1]) = $8B);
end;

procedure AppendLE32(SB: TStringBuilder; V: UInt32);
begin
  SB.AppendByte(V and $FF);
  SB.AppendByte((V shr 8) and $FF);
  SB.AppendByte((V shr 16) and $FF);
  SB.AppendByte((V shr 24) and $FF);
end;

function ReadLE16(const S: string; APos: Int): Int;
begin
  Result := Byte(S[APos]) or (Byte(S[APos + 1]) shl 8);
end;

function ReadLE32(const S: string; APos: Int): UInt32;
begin
  Result := UInt32(Byte(S[APos])) or (UInt32(Byte(S[APos + 1])) shl 8) or
    (UInt32(Byte(S[APos + 2])) shl 16) or (UInt32(Byte(S[APos + 3])) shl 24);
end;

function GzipCompress(const AData: string; ALevel: Int;
  const AFileName: string; AModTime: Int64): string;
var
  SB: TStringBuilder;
  Flags, Xfl: Int;
begin
  Flags := 0;
  if AFileName <> '' then
    Flags := FNAME;
  { XFL: 2 = maximum compression, 4 = fastest. }
  Xfl := 0;
  if ALevel >= 9 then
    Xfl := 2
  else if ALevel = 1 then
    Xfl := 4;
  SB := TStringBuilder.Create();
  SB.AppendByte($1F);
  SB.AppendByte($8B);
  SB.AppendByte(8);
  SB.AppendByte(Flags);
  AppendLE32(SB, UInt32(AModTime and $FFFFFFFF));
  SB.AppendByte(Xfl);
  SB.AppendByte(OS_UNIX);
  if AFileName <> '' then
  begin
    SB.Append(AFileName);
    SB.AppendByte(0);
  end;
  SB.Append(Deflate(AData, ALevel));
  AppendLE32(SB, Crc32(AData));
  AppendLE32(SB, UInt32(Int64(Length(AData)) and $FFFFFFFF));
  Result := SB.ToString();
  SB.Free();
end;

{ The zero-terminated string at APos; APos moves past the terminator. }
function ReadZString(const AData: string; var APos: Int): string;
var
  Start: Int;
begin
  Start := APos;
  while (APos < Length(AData)) and (Byte(AData[APos]) <> 0) do
    APos := APos + 1;
  if APos >= Length(AData) then
    Fail('unexpected end of header');
  Result := Copy(AData, Start, APos - Start);
  APos := APos + 1;
end;

{ Decodes the member at APos, appending its contents to AOut; APos moves to
  the byte after the member. }
procedure ReadMember(const AData: string; var APos: Int; AOut: TStringBuilder;
  var AHeader: TGzipHeader);
var
  Start, Flags, XLen, EndPos: Int;
  Body: string;
  Crc: UInt32;
begin
  Start := APos;
  if Length(AData) - APos < 10 then
    Fail('unexpected end of header');
  if (Byte(AData[APos]) <> $1F) or (Byte(AData[APos + 1]) <> $8B) then
    Fail('not a gzip member');
  if Byte(AData[APos + 2]) <> 8 then
    raise ECompressionError.Create(
      'Unsupported gzip data: compression method ' +
      IntToStr(Byte(AData[APos + 2])));
  Flags := Byte(AData[APos + 3]);
  if (Flags and FRESERVED) <> 0 then
    Fail('reserved header flag set');
  AHeader.ModTime := Int64(ReadLE32(AData, APos + 4));
  AHeader.OS := Byte(AData[APos + 9]);
  AHeader.Extra := '';
  AHeader.FileName := '';
  AHeader.Comment := '';
  APos := APos + 10;
  if (Flags and FEXTRA) <> 0 then
  begin
    if Length(AData) - APos < 2 then
      Fail('unexpected end of header');
    XLen := ReadLE16(AData, APos);
    if Length(AData) - APos - 2 < XLen then
      Fail('unexpected end of header');
    AHeader.Extra := Copy(AData, APos + 2, XLen);
    APos := APos + 2 + XLen;
  end;
  if (Flags and FNAME) <> 0 then
    AHeader.FileName := ReadZString(AData, APos);
  if (Flags and FCOMMENT) <> 0 then
    AHeader.Comment := ReadZString(AData, APos);
  if (Flags and FHCRC) <> 0 then
  begin
    if Length(AData) - APos < 2 then
      Fail('unexpected end of header');
    if ReadLE16(AData, APos) <>
       Int(Crc32(Copy(AData, Start, APos - Start)) and $FFFF) then
      Fail('header CRC mismatch');
    APos := APos + 2;
  end;

  Body := InflateAt(AData, APos, EndPos);
  if Length(AData) - EndPos < 8 then
    Fail('unexpected end of data in trailer');
  Crc := ReadLE32(AData, EndPos);
  if Crc <> Crc32(Body) then
    Fail('CRC-32 mismatch');
  if ReadLE32(AData, EndPos + 4) <>
     UInt32(Int64(Length(Body)) and $FFFFFFFF) then
    Fail('length mismatch');
  AOut.Append(Body);
  APos := EndPos + 8;
end;

function OnlyZeros(const AData: string; AFrom: Int): Boolean;
var
  I: Int;
begin
  for I := AFrom to Length(AData) - 1 do
    if Byte(AData[I]) <> 0 then
      Exit(False);
  Result := True;
end;

function GzipDecompress(const AData: string; out AHeader: TGzipHeader): string;
var
  SB: TStringBuilder;
  Pos: Int;
  Next: TGzipHeader;
begin
  if not IsGzip(AData) then
    Fail('not a gzip file');
  SB := TStringBuilder.Create();
  try
    Pos := 0;
    ReadMember(AData, Pos, SB, AHeader);
    while (Pos < Length(AData)) and not OnlyZeros(AData, Pos) do
    begin
      if not IsGzip(Copy(AData, Pos, 2)) then
        Fail('unexpected data after the last member');
      ReadMember(AData, Pos, SB, Next);
    end;
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function GzipDecompress(const AData: string): string;
var
  H: TGzipHeader;
begin
  Result := GzipDecompress(AData, H);
end;

end.
