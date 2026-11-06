{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Compression.Zip - reading and writing zip archives (PKWARE APPNOTE).

  Reading:

    Z := TZipReader.Create('mods/example.jar');
    try
      for I := 0 to Z.Count - 1 do
        WriteLn(Z.Entries[I].Name, ' ', Z.Entries[I].UncompressedSize);
      Manifest := Z.ReadBytes('META-INF/MANIFEST.MF');
      Z.ExtractAll('/tmp/unpacked');
    finally
      Z.Free();
    end;

  The archive is indexed from its central directory when opened; each
  entry's data is read from the file only when asked for, so a large
  archive is never loaded whole.  Entries are stored (method 0) or
  deflated (method 8); each is checked against its CRC-32 and size as it is
  read.  Zip64 archives (more than 65535 entries, or sizes and offsets
  beyond 4 GiB) are read.  Refused with EZipUnsupported rather than
  returning wrong data: encrypted entries, other compression methods and
  archives split over several disks.  A malformed archive raises EZipError.

  Entry names are untrusted: '../../.bashrc' is a valid name.  ZipSafePath
  maps a name to a path inside a target folder or raises EZipError, and
  ExtractTo/ExtractAll use it for every entry.

  Writing:

    W := TZipWriter.Create('export.zip');
    try
      W.AddDirectory('config');
      W.AddEntry('config/options.txt', Options);       // deflated
      W.AddFile('mods/a.jar', '/path/to/a.jar', ZIP_STORED);
      W.Close();                                       // writes the directory
    finally
      W.Free();
    end;

  A deflated entry that would not get smaller is stored instead.  Names are
  written as given (UTF-8, flagged as such when not plain ASCII) and must
  pass the same safety check as extraction.  Archives are written without
  Zip64, so an entry or archive of 4 GiB or more, or more than 65535
  entries, raises EZipUnsupported.

  Data is a string of raw bytes, as in Compression.Deflate. }

unit Compression.Zip;

interface

uses
  SysUtils, Generics.Collections, DateUtils, Streams, Compression.Deflate;

const
  ZIP_STORED = 0;
  ZIP_DEFLATED = 8;

type
  { A malformed archive, a failed CRC or size check, a missing entry or an
    unsafe entry name. }
  EZipError = class(ECompressionError)
  end;

  { A valid archive that uses a feature this unit does not support. }
  EZipUnsupported = class(EZipError)
  end;

  { One entry of an archive, as its central directory describes it. }
  TZipEntry = class
  private
    FName: string;
    FComment: string;
    FMethod: Int;
    FFlags: Int;
    FCrc: UInt32;
    FCompressedSize: Int64;
    FUncompressedSize: Int64;
    FLocalOffset: Int64;
    FModifiedTime: TDateTime;
    function GetIsDirectory: Boolean;
    function GetIsEncrypted: Boolean;
  public
    { The entry's path in the archive, '/'-separated; a directory's ends
      in '/'. }
    property Name: string read FName;
    property Comment: string read FComment;
    { ZIP_STORED, ZIP_DEFLATED, or another APPNOTE method number. }
    property Method: Int read FMethod;
    { The general-purpose bit flags. }
    property Flags: Int read FFlags;
    property Crc: UInt32 read FCrc;
    property CompressedSize: Int64 read FCompressedSize;
    property UncompressedSize: Int64 read FUncompressedSize;
    { Local (MS-DOS) time, to two seconds. }
    property ModifiedTime: TDateTime read FModifiedTime;
    property IsDirectory: Boolean read GetIsDirectory;
    property IsEncrypted: Boolean read GetIsEncrypted;
  end;

  TZipReader = class
  private
    FFile: TFileInputStream;   { nil for an in-memory archive }
    FData: string;             { the in-memory archive }
    FSize: Int64;
    FEntries: TList<TZipEntry>;
    FIndex: TDictionary<string, Int>;
    FComment: string;
    function ReadAt(AOffset: Int64; ACount: Int): string;
    procedure ReadDirectory;
    function GetEntry(AIndex: Int): TZipEntry;
    function GetCount: Int;
  public
    { Opens the archive at APath.  Raises EStreamError when it cannot be
      opened and EZipError when it is not a zip archive. }
    constructor Create(const APath: string);
    { Reads an archive held in memory. }
    constructor CreateFromBytes(const AData: string);
    destructor Destroy; override;
    { Closes the archive file; the entries stay listed but cannot be read. }
    procedure Close;
    { The entry named AName (case-sensitive), or nil. }
    function Find(const AName: string): TZipEntry;
    { The uncompressed contents of AEntry ('' for a directory). }
    function ReadBytes(AEntry: TZipEntry): string; overload;
    { The contents of the entry named AName; EZipError when there is none. }
    function ReadBytes(const AName: string): string; overload;
    { Writes AEntry under ATargetDir at ZipSafePath(ATargetDir, Name),
      creating folders as needed. }
    procedure ExtractTo(AEntry: TZipEntry; const ATargetDir: string);
    { Extracts every entry.  Every name is checked before anything is
      written, so an archive with an unsafe name writes nothing. }
    procedure ExtractAll(const ATargetDir: string);
    property Count: Int read GetCount;
    property Entries[AIndex: Int]: TZipEntry read GetEntry; default;
    { The archive comment. }
    property Comment: string read FComment;
  end;

  TZipWriter = class
  private
    FStream: TOutputStream;
    FMemory: TMemoryOutputStream;   { the stream, when writing to memory }
    FOffset: Int64;
    FEntries: TList<TZipEntry>;
    FNames: TDictionary<string, Int>;
    FClosed: Boolean;
    FModifiedTime: TDateTime;
    procedure Emit(const ABytes: string);
    procedure AddRaw(const AName, AData: string; AMethod, ALevel: Int);
  public
    { Creates (or replaces) the archive file APath. }
    constructor Create(const APath: string);
    { Builds the archive in memory; Bytes returns it after Close. }
    constructor CreateInMemory;
    destructor Destroy; override;
    { Adds a file entry holding AData.  AMethod is ZIP_DEFLATED (the
      default) or ZIP_STORED; ALevel is the deflate level, 1-9. }
    procedure AddEntry(const AName, AData: string; AMethod: Int = ZIP_DEFLATED;
      ALevel: Int = 6);
    { Adds a file entry holding the contents of the file ASourcePath. }
    procedure AddFile(const AName, ASourcePath: string;
      AMethod: Int = ZIP_DEFLATED; ALevel: Int = 6);
    { Adds a directory entry; a trailing '/' is added when missing. }
    procedure AddDirectory(const AName: string);
    { Writes the central directory and closes the output.  Must be called:
      without it the archive is incomplete. }
    procedure Close;
    { The finished archive, for one made with CreateInMemory. }
    function Bytes: string;
    { The time recorded for entries added from now on; the local time when
      the writer was created. }
    property ModifiedTime: TDateTime read FModifiedTime write FModifiedTime;
  end;

{ The path under ATargetDir that the entry name AEntryName extracts to.
  Raises EZipError for a name that could reach outside ATargetDir or is
  unusable: empty, absolute ('/x', 'C:x'), containing a '..' segment or a
  NUL byte.  '\' is treated as a separator, as archives made on Windows
  sometimes use it; '.' and empty segments are dropped. }
function ZipSafePath(const ATargetDir, AEntryName: string): string;

implementation

uses
  StrUtils, Compression.Checksums;

const
  SIG_LOCAL = $04034B50;
  SIG_CENTRAL = $02014B50;
  SIG_END = $06054B50;
  SIG_END64 = $06064B50;
  SIG_LOCATOR64 = $07064B50;
  FLAG_ENCRYPTED = $0001;
  FLAG_STRONG_ENCRYPTION = $0040;
  FLAG_UTF8 = $0800;
  END_SIZE = 22;
  MAX_COMMENT = 65535;
  ZIP64_EXTRA = $0001;
  U32_MAX = $FFFFFFFF;
  U16_MAX = $FFFF;
  { Unix st_mode values, kept in the high half of the external attributes. }
  MODE_FILE = $81A4;   { regular file, 0644 }
  MODE_DIR = $41ED;    { directory, 0755 }
  MSDOS_DIR = $10;

procedure Fail(const AMsg: string);
begin
  raise EZipError.Create('Invalid zip archive: ' + AMsg);
end;

function U16(const S: string; APos: Int): Int;
begin
  Result := Byte(S[APos]) or (Byte(S[APos + 1]) shl 8);
end;

function U32(const S: string; APos: Int): Int64;
begin
  Result := Int64(Byte(S[APos])) or (Int64(Byte(S[APos + 1])) shl 8) or
    (Int64(Byte(S[APos + 2])) shl 16) or (Int64(Byte(S[APos + 3])) shl 24);
end;

function U64(const S: string; APos: Int): Int64;
begin
  Result := U32(S, APos) or (U32(S, APos + 4) shl 32);
end;

procedure Put16(SB: TStringBuilder; V: Int);
begin
  SB.AppendByte(V and $FF);
  SB.AppendByte((V shr 8) and $FF);
end;

procedure Put32(SB: TStringBuilder; V: Int64);
begin
  SB.AppendByte(V and $FF);
  SB.AppendByte((V shr 8) and $FF);
  SB.AppendByte((V shr 16) and $FF);
  SB.AppendByte((V shr 24) and $FF);
end;

{ MS-DOS date and time fields <-> TDateTime. }
function DosToDateTime(ADate, ATime: Int): TDateTime;
begin
  Result.Date.Year := 1980 + (ADate shr 9);
  Result.Date.Month := (ADate shr 5) and 15;
  Result.Date.Day := ADate and 31;
  Result.Time.Hour := ATime shr 11;
  Result.Time.Minute := (ATime shr 5) and 63;
  Result.Time.Second := (ATime and 31) * 2;
  Result.Time.Nanosecond := 0;
end;

procedure DateTimeToDos(const AValue: TDateTime; out ADate, ATime: Int);
begin
  if AValue.Date.Year < 1980 then
  begin
    { The earliest time MS-DOS fields can hold. }
    ADate := (1 shl 5) or 1;
    ATime := 0;
    Exit;
  end;
  ADate := ((AValue.Date.Year - 1980) shl 9) or (AValue.Date.Month shl 5) or
    AValue.Date.Day;
  ATime := (AValue.Time.Hour shl 11) or (AValue.Time.Minute shl 5) or
    (AValue.Time.Second div 2);
end;

function ZipSafePath(const ATargetDir, AEntryName: string): string;
var
  Name, Seg, Joined: string;
  I, Start: Int;
begin
  if AEntryName = '' then
    raise EZipError.Create('Unsafe zip entry name: empty');
  Name := AEntryName;
  for I := 0 to Length(Name) - 1 do
    if Byte(Name[I]) = 0 then
      raise EZipError.Create('Unsafe zip entry name: contains a NUL byte');
  Name := ReplaceAll(Name, '\', '/');
  if Byte(Name[0]) = Ord('/') then
    raise EZipError.Create('Unsafe zip entry name (absolute path): ' + AEntryName);
  if (Length(Name) >= 2) and (Byte(Name[1]) = Ord(':')) then
    raise EZipError.Create('Unsafe zip entry name (drive letter): ' + AEntryName);
  Joined := '';
  Start := 0;
  for I := 0 to Length(Name) do
    if (I = Length(Name)) or (Byte(Name[I]) = Ord('/')) then
    begin
      Seg := Copy(Name, Start, I - Start);
      Start := I + 1;
      if Seg = '..' then
        raise EZipError.Create('Unsafe zip entry name (parent folder): ' +
          AEntryName);
      if (Seg <> '') and (Seg <> '.') then
        Joined := Joined + '/' + Seg;
    end;
  if Joined = '' then
    raise EZipError.Create('Unsafe zip entry name: no file name: ' + AEntryName);
  Result := ExcludeTrailingPathDelimiter(ATargetDir) + Joined;
end;

{ ------------------------------------------------------------------ }
{ TZipEntry                                                           }
{ ------------------------------------------------------------------ }

function TZipEntry.GetIsDirectory: Boolean;
begin
  Result := (Length(Self.FName) > 0) and
    (Byte(Self.FName[Length(Self.FName) - 1]) = Ord('/'));
end;

function TZipEntry.GetIsEncrypted: Boolean;
begin
  Result := (Self.FFlags and (FLAG_ENCRYPTED or FLAG_STRONG_ENCRYPTION)) <> 0;
end;

{ ------------------------------------------------------------------ }
{ TZipReader                                                          }
{ ------------------------------------------------------------------ }

constructor TZipReader.Create(const APath: string);
begin
  inherited Create();
  Self.FEntries := TList<TZipEntry>.Create();
  Self.FIndex := TDictionary<string, Int>.Create();
  Self.FFile := TFileInputStream.Create(APath);
  Self.FSize := Self.FFile.Size();
  Self.ReadDirectory();
end;

constructor TZipReader.CreateFromBytes(const AData: string);
begin
  inherited Create();
  Self.FEntries := TList<TZipEntry>.Create();
  Self.FIndex := TDictionary<string, Int>.Create();
  Self.FFile := nil;
  Self.FData := AData;
  Self.FSize := Length(AData);
  Self.ReadDirectory();
end;

destructor TZipReader.Destroy;
var
  I: Int;
begin
  Self.Close();
  for I := 0 to Self.FEntries.Count - 1 do
    Self.FEntries[I].Free();
  Self.FEntries.Free();
  Self.FIndex.Free();
  inherited Destroy();
end;

procedure TZipReader.Close;
begin
  if Self.FFile <> nil then
  begin
    Self.FFile.Close();
    Self.FFile.Free();
    Self.FFile := nil;
  end;
end;

function TZipReader.GetCount: Int;
begin
  Result := Self.FEntries.Count;
end;

function TZipReader.GetEntry(AIndex: Int): TZipEntry;
begin
  Result := Self.FEntries[AIndex];
end;

function TZipReader.ReadAt(AOffset: Int64; ACount: Int): string;
var
  P: ^Byte;
  Got, N: Int;
begin
  if (AOffset < 0) or (ACount < 0) or (AOffset + ACount > Self.FSize) then
    Fail('data lies beyond the end of the archive');
  if ACount = 0 then
    Exit('');
  if Self.FFile = nil then
  begin
    if Self.FData = '' then
      raise EZipError.Create('Zip archive is closed');
    Exit(Copy(Self.FData, Int(AOffset), ACount));
  end;
  Result := '';
  SetLength(Result, ACount);
  P := Pointer(Result);
  Self.FFile.Seek(AOffset, soBeginning);
  Got := 0;
  while Got < ACount do
  begin
    N := Self.FFile.Read(P + Got, ACount - Got);
    if N <= 0 then
      Fail('unexpected end of file');
    Got := Got + N;
  end;
end;

procedure TZipReader.ReadDirectory;
var
  Tail, Dir, Extra: string;
  TailLen, EndPos, I, Pos, NameLen, ExtraLen, CommentLen, X, XEnd, XId,
    XLen, F: Int;
  TailStart, Entries, DirSize, DirOffset, Loc, End64: Int64;
  E: TZipEntry;
begin
  { The end of central directory record is the last 22 bytes, unless the
    archive has a comment (up to 64 KiB) after it: search backwards. }
  if Self.FSize < END_SIZE then
    Fail('too short to be a zip archive');
  TailLen := END_SIZE + MAX_COMMENT;
  if TailLen > Self.FSize then
    TailLen := Int(Self.FSize);
  TailStart := Self.FSize - TailLen;
  Tail := Self.ReadAt(TailStart, TailLen);
  EndPos := -1;
  I := TailLen - END_SIZE;
  while (I >= 0) and (EndPos < 0) do
  begin
    if (U32(Tail, I) = SIG_END) and
       (I + END_SIZE + U16(Tail, I + 20) <= TailLen) then
      EndPos := I;
    I := I - 1;
  end;
  if EndPos < 0 then
    Fail('no end of central directory record');
  if (U16(Tail, EndPos + 4) <> 0) or (U16(Tail, EndPos + 6) <> 0) then
    raise EZipUnsupported.Create('Unsupported zip archive: split over several disks');
  Entries := U16(Tail, EndPos + 10);
  DirSize := U32(Tail, EndPos + 12);
  DirOffset := U32(Tail, EndPos + 16);
  Self.FComment := Copy(Tail, EndPos + END_SIZE, U16(Tail, EndPos + 20));

  { Zip64: a locator just before the end record points at the Zip64 end
    record, whose fields replace the saturated 16- and 32-bit ones. }
  if (EndPos >= 20) and (U32(Tail, EndPos - 20) = SIG_LOCATOR64) then
  begin
    Loc := EndPos - 20;
    End64 := U64(Tail, Int(Loc) + 8);
    Dir := Self.ReadAt(End64, 56);
    if U32(Dir, 0) <> SIG_END64 then
      Fail('bad Zip64 end of central directory record');
    if (U32(Dir, 16) <> 0) or (U32(Dir, 20) <> 0) then
      raise EZipUnsupported.Create('Unsupported zip archive: split over several disks');
    Entries := U64(Dir, 32);
    DirSize := U64(Dir, 40);
    DirOffset := U64(Dir, 48);
  end;

  if (DirSize > Self.FSize) or (DirOffset + DirSize > Self.FSize) then
    Fail('central directory lies beyond the end of the archive');
  Dir := Self.ReadAt(DirOffset, Int(DirSize));
  Pos := 0;
  for I := 0 to Int(Entries) - 1 do
  begin
    if (Pos + 46 > Length(Dir)) or (U32(Dir, Pos) <> SIG_CENTRAL) then
      Fail('bad central directory entry');
    NameLen := U16(Dir, Pos + 28);
    ExtraLen := U16(Dir, Pos + 30);
    CommentLen := U16(Dir, Pos + 32);
    if Pos + 46 + NameLen + ExtraLen + CommentLen > Length(Dir) then
      Fail('central directory entry overruns the directory');
    E := TZipEntry.Create();
    Self.FEntries.Add(E);
    E.FFlags := U16(Dir, Pos + 8);
    E.FMethod := U16(Dir, Pos + 10);
    E.FModifiedTime := DosToDateTime(U16(Dir, Pos + 14), U16(Dir, Pos + 12));
    E.FCrc := UInt32(U32(Dir, Pos + 16));
    E.FCompressedSize := U32(Dir, Pos + 20);
    E.FUncompressedSize := U32(Dir, Pos + 24);
    E.FLocalOffset := U32(Dir, Pos + 42);
    E.FName := Copy(Dir, Pos + 46, NameLen);
    E.FComment := Copy(Dir, Pos + 46 + NameLen + ExtraLen, CommentLen);
    { Zip64 extended information: present fields replace, in this order,
      those of the record that are saturated. }
    Extra := Copy(Dir, Pos + 46 + NameLen, ExtraLen);
    X := 0;
    while X + 4 <= Length(Extra) do
    begin
      XId := U16(Extra, X);
      XLen := U16(Extra, X + 2);
      if X + 4 + XLen > Length(Extra) then
        Break;
      if XId = ZIP64_EXTRA then
      begin
        F := X + 4;
        XEnd := X + 4 + XLen;
        if (E.FUncompressedSize = U32_MAX) and (F + 8 <= XEnd) then
        begin
          E.FUncompressedSize := U64(Extra, F);
          F := F + 8;
        end;
        if (E.FCompressedSize = U32_MAX) and (F + 8 <= XEnd) then
        begin
          E.FCompressedSize := U64(Extra, F);
          F := F + 8;
        end;
        if (E.FLocalOffset = U32_MAX) and (F + 8 <= XEnd) then
          E.FLocalOffset := U64(Extra, F);
      end;
      X := X + 4 + XLen;
    end;
    if not Self.FIndex.ContainsKey(E.FName) then
      Self.FIndex.Add(E.FName, Self.FEntries.Count - 1);
    Pos := Pos + 46 + NameLen + ExtraLen + CommentLen;
  end;
end;

function TZipReader.Find(const AName: string): TZipEntry;
var
  Idx: Int;
begin
  Idx := 0;
  if Self.FIndex.TryGetValue(AName, Idx) then
    Result := Self.FEntries[Idx]
  else
    Result := nil;
end;

function TZipReader.ReadBytes(AEntry: TZipEntry): string;
var
  Header, Comp: string;
  DataStart: Int64;
begin
  if AEntry.IsEncrypted then
    raise EZipUnsupported.Create('Unsupported zip entry (encrypted): ' +
      AEntry.Name);
  if (AEntry.Method <> ZIP_STORED) and (AEntry.Method <> ZIP_DEFLATED) then
    raise EZipUnsupported.Create('Unsupported zip entry (compression method ' +
      IntToStr(AEntry.Method) + '): ' + AEntry.Name);
  Header := Self.ReadAt(AEntry.FLocalOffset, 30);
  if U32(Header, 0) <> SIG_LOCAL then
    Fail('bad local header for ' + AEntry.Name);
  { The local name and extra field may differ from the central ones; the
    sizes come from the central directory, since a streamed entry leaves
    them zero here and puts them in a data descriptor. }
  DataStart := AEntry.FLocalOffset + 30 + U16(Header, 26) + U16(Header, 28);
  if AEntry.CompressedSize > 2147483647 then
    raise EZipUnsupported.Create('Zip entry too large to read into memory: ' +
      AEntry.Name);
  Comp := Self.ReadAt(DataStart, Int(AEntry.CompressedSize));
  if AEntry.Method = ZIP_STORED then
    Result := Comp
  else
  begin
    try
      Result := Inflate(Comp);
    except
      on Ex: ECompressionError do
        raise EZipError.Create('Invalid zip entry ' + AEntry.Name + ': ' +
          Ex.Message);
    end;
  end;
  if Int64(Length(Result)) <> AEntry.UncompressedSize then
    raise EZipError.Create('Invalid zip entry (size mismatch): ' + AEntry.Name);
  if Crc32(Result) <> AEntry.Crc then
    raise EZipError.Create('Invalid zip entry (CRC-32 mismatch): ' + AEntry.Name);
end;

function TZipReader.ReadBytes(const AName: string): string;
var
  E: TZipEntry;
begin
  E := Self.Find(AName);
  if E = nil then
    raise EZipError.Create('No such zip entry: ' + AName);
  Result := Self.ReadBytes(E);
end;

procedure WriteWholeFile(const APath, AData: string);
var
  F: TFileOutputStream;
begin
  F := TFileOutputStream.Create(APath);
  try
    if Length(AData) > 0 then
      F.Write(Pointer(AData), Length(AData));
    F.Close();
  finally
    F.Free();
  end;
end;

procedure TZipReader.ExtractTo(AEntry: TZipEntry; const ATargetDir: string);
var
  Path: string;
begin
  Path := ZipSafePath(ATargetDir, AEntry.Name);
  if AEntry.IsDirectory then
    ForceDirectories(Path)
  else
  begin
    ForceDirectories(ExtractFileDir(Path));
    WriteWholeFile(Path, Self.ReadBytes(AEntry));
  end;
end;

procedure TZipReader.ExtractAll(const ATargetDir: string);
var
  I: Int;
begin
  for I := 0 to Self.FEntries.Count - 1 do
    ZipSafePath(ATargetDir, Self.FEntries[I].Name);
  for I := 0 to Self.FEntries.Count - 1 do
    Self.ExtractTo(Self.FEntries[I], ATargetDir);
end;

{ ------------------------------------------------------------------ }
{ TZipWriter                                                          }
{ ------------------------------------------------------------------ }

constructor TZipWriter.Create(const APath: string);
begin
  inherited Create();
  Self.FEntries := TList<TZipEntry>.Create();
  Self.FNames := TDictionary<string, Int>.Create();
  Self.FModifiedTime := LocalNow(SystemOffset());
  Self.FMemory := nil;
  Self.FStream := TFileOutputStream.Create(APath);
end;

constructor TZipWriter.CreateInMemory;
begin
  inherited Create();
  Self.FEntries := TList<TZipEntry>.Create();
  Self.FNames := TDictionary<string, Int>.Create();
  Self.FModifiedTime := LocalNow(SystemOffset());
  Self.FMemory := TMemoryOutputStream.Create();
  Self.FStream := Self.FMemory;
end;

destructor TZipWriter.Destroy;
var
  I: Int;
begin
  { An unclosed archive is abandoned, not finished: Close can raise, and a
    destructor must not. }
  if not Self.FClosed then
  begin
    try
      Self.FStream.Close();
    except
    end;
  end;
  Self.FStream.Free();
  for I := 0 to Self.FEntries.Count - 1 do
    Self.FEntries[I].Free();
  Self.FEntries.Free();
  Self.FNames.Free();
  inherited Destroy();
end;

procedure TZipWriter.Emit(const ABytes: string);
begin
  if Length(ABytes) > 0 then
    Self.FStream.Write(Pointer(ABytes), Length(ABytes));
  Self.FOffset := Self.FOffset + Length(ABytes);
end;

function NeedsUtf8Flag(const AName: string): Boolean;
var
  I: Int;
begin
  for I := 0 to Length(AName) - 1 do
    if Byte(AName[I]) >= $80 then
      Exit(True);
  Result := False;
end;

procedure TZipWriter.AddRaw(const AName, AData: string; AMethod, ALevel: Int);
var
  E: TZipEntry;
  Comp: string;
  SB: TStringBuilder;
  DosDate, DosTime: Int;
begin
  if Self.FClosed then
    raise EZipError.Create('Zip archive is already closed');
  ZipSafePath('', AName);
  if Self.FNames.ContainsKey(AName) then
    raise EZipError.Create('Duplicate zip entry name: ' + AName);
  if (AMethod <> ZIP_STORED) and (AMethod <> ZIP_DEFLATED) then
    raise EZipUnsupported.Create('Unsupported zip compression method ' +
      IntToStr(AMethod));
  if Self.FEntries.Count >= U16_MAX then
    raise EZipUnsupported.Create('Zip archive has too many entries (Zip64 is not written)');
  if Int64(Length(AData)) >= U32_MAX then
    raise EZipUnsupported.Create('Zip entry too large (Zip64 is not written): ' + AName);

  Comp := AData;
  if (AMethod = ZIP_DEFLATED) and (Length(AData) > 0) then
  begin
    Comp := Deflate(AData, ALevel);
    if Length(Comp) >= Length(AData) then
    begin
      Comp := AData;
      AMethod := ZIP_STORED;
    end;
  end
  else
    AMethod := ZIP_STORED;
  if Self.FOffset + 30 + Length(AName) + Length(Comp) >= U32_MAX then
    raise EZipUnsupported.Create('Zip archive too large (Zip64 is not written)');

  E := TZipEntry.Create();
  E.FName := AName;
  E.FMethod := AMethod;
  E.FFlags := 0;
  if NeedsUtf8Flag(AName) then
    E.FFlags := FLAG_UTF8;
  E.FCrc := Crc32(AData);
  E.FCompressedSize := Length(Comp);
  E.FUncompressedSize := Length(AData);
  E.FLocalOffset := Self.FOffset;
  E.FModifiedTime := Self.FModifiedTime;
  Self.FEntries.Add(E);
  Self.FNames.Add(AName, Self.FEntries.Count - 1);

  DateTimeToDos(E.FModifiedTime, DosDate, DosTime);
  SB := TStringBuilder.Create();
  Put32(SB, SIG_LOCAL);
  Put16(SB, 20);               { version needed: 2.0 }
  Put16(SB, E.FFlags);
  Put16(SB, E.FMethod);
  Put16(SB, DosTime);
  Put16(SB, DosDate);
  Put32(SB, E.FCrc);
  Put32(SB, E.FCompressedSize);
  Put32(SB, E.FUncompressedSize);
  Put16(SB, Length(AName));
  Put16(SB, 0);                { extra field length }
  SB.Append(AName);
  Self.Emit(SB.ToString());
  SB.Free();
  Self.Emit(Comp);
end;

procedure TZipWriter.AddEntry(const AName, AData: string; AMethod: Int;
  ALevel: Int);
begin
  if (Length(AName) > 0) and (Byte(AName[Length(AName) - 1]) = Ord('/')) then
    raise EZipError.Create('A file entry name cannot end in ''/'': ' + AName);
  Self.AddRaw(AName, AData, AMethod, ALevel);
end;

procedure TZipWriter.AddFile(const AName, ASourcePath: string; AMethod: Int;
  ALevel: Int);
var
  F: TFileInputStream;
  Data: string;
  P: ^Byte;
  Size, Got, N: Int;
begin
  F := TFileInputStream.Create(ASourcePath);
  try
    Size := Int(F.Size());
    Data := '';
    if Size > 0 then
    begin
      SetLength(Data, Size);
      P := Pointer(Data);
      Got := 0;
      while Got < Size do
      begin
        N := F.Read(P + Got, Size - Got);
        if N <= 0 then
          raise EStreamError.Create('Unexpected end of file: ' + ASourcePath);
        Got := Got + N;
      end;
    end;
    F.Close();
  finally
    F.Free();
  end;
  Self.AddEntry(AName, Data, AMethod, ALevel);
end;

procedure TZipWriter.AddDirectory(const AName: string);
var
  Name: string;
begin
  Name := AName;
  if (Length(Name) = 0) or (Byte(Name[Length(Name) - 1]) <> Ord('/')) then
    Name := Name + '/';
  Self.AddRaw(Name, '', ZIP_STORED, 0);
end;

procedure TZipWriter.Close;
var
  SB: TStringBuilder;
  E: TZipEntry;
  I, DosDate, DosTime: Int;
  DirStart: Int64;
begin
  if Self.FClosed then
    Exit;
  DirStart := Self.FOffset;
  SB := TStringBuilder.Create();
  for I := 0 to Self.FEntries.Count - 1 do
  begin
    E := Self.FEntries[I];
    DateTimeToDos(E.FModifiedTime, DosDate, DosTime);
    Put32(SB, SIG_CENTRAL);
    Put16(SB, (3 shl 8) or 20);  { made by: Unix, version 2.0 }
    Put16(SB, 20);               { version needed }
    Put16(SB, E.FFlags);
    Put16(SB, E.FMethod);
    Put16(SB, DosTime);
    Put16(SB, DosDate);
    Put32(SB, E.FCrc);
    Put32(SB, E.FCompressedSize);
    Put32(SB, E.FUncompressedSize);
    Put16(SB, Length(E.FName));
    Put16(SB, 0);                { extra field length }
    Put16(SB, 0);                { comment length }
    Put16(SB, 0);                { disk number }
    Put16(SB, 0);                { internal attributes }
    if E.IsDirectory then
      Put32(SB, (Int64(MODE_DIR) shl 16) or MSDOS_DIR)
    else
      Put32(SB, Int64(MODE_FILE) shl 16);
    Put32(SB, E.FLocalOffset);
    SB.Append(E.FName);
  end;
  Self.Emit(SB.ToString());
  SB.Clear();
  if Self.FOffset >= U32_MAX then
    raise EZipUnsupported.Create('Zip archive too large (Zip64 is not written)');
  Put32(SB, SIG_END);
  Put16(SB, 0);                  { this disk }
  Put16(SB, 0);                  { disk with the directory }
  Put16(SB, Self.FEntries.Count);
  Put16(SB, Self.FEntries.Count);
  Put32(SB, Self.FOffset - DirStart);
  Put32(SB, DirStart);
  Put16(SB, 0);                  { comment length }
  Self.Emit(SB.ToString());
  SB.Free();
  Self.FStream.Close();
  Self.FClosed := True;
end;

function TZipWriter.Bytes: string;
var
  M: TMemoryOutputStream;
begin
  if Self.FMemory = nil then
    raise EZipError.Create('Bytes is only available for an in-memory zip archive');
  if not Self.FClosed then
    raise EZipError.Create('Zip archive is not closed yet');
  M := Self.FMemory;
  Result := M.ToString();
end;

end.
