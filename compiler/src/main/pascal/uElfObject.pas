{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  uElfObject.pas author: Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  ELF relocatable object reader/writer.

  Narrow scope: two operations the .bif-in-.o pipeline needs —
  append a named SHT_PROGBITS section, and read a named section
  back out.  No symbol-table editing, no relocation fix-up, no
  section removal, no PE/COFF.

  This stage lands ProbeElf + the SHT walker.  AppendSection and
  ReadSection are next.

  Byte buffers are carried as Blaise strings (0-indexed, byte
  oriented — matching TMemoryInputStream / TBuffer style).
}

unit uElfObject;

interface

uses
  SysUtils, streams;

type
  EElfObject = class(Exception);

  { Light identification record populated by ProbeElf.  Callers use
    this to decide whether a file is worth opening at all. }
  TElfInfo = record
    IsElf:         Boolean;
    Is64:          Boolean;     { ELFCLASS64 vs ELFCLASS32 }
    LittleEndian:  Boolean;     { ELFDATA2LSB vs ELFDATA2MSB }
    IsRelocatable: Boolean;     { e_type = ET_REL }
    Machine:       Integer;     { e_machine (EM_X86_64=62, EM_AARCH64=183, ...) }
    ShOff:         Int64;       { section header table file offset }
    ShEntSize:     Integer;
    ShNum:         Integer;
    ShStrNdx:      Integer;     { index of .shstrtab in SHT }
  end;

  { One parsed section header table entry.

    Class rather than record because Blaise's dynamic-array-of-record
    element assignment (Sects[I] := SomeRec) silently scrambles the
    payload; using a heap object makes Sects[I] a plain pointer copy. }
  TElfSection = class
  public
    Name:    string;     { resolved from .shstrtab }
    SType:   Integer;    { sh_type }
    Offset:  Int64;      { sh_offset }
    Size:    Int64;      { sh_size }
    NameOff: Integer;    { sh_name (raw index into .shstrtab) }
  end;

  TElfSectionArray = array of TElfSection;

const
  { Selected ELF constants — copied locally so the compiler has no
    dependency on FPC's elf bindings. }
  ELFMAG0     = $7F;
  ELFMAG1     = $45;  { 'E' }
  ELFMAG2     = $4C;  { 'L' }
  ELFMAG3     = $46;  { 'F' }

  EI_CLASS    = 4;
  EI_DATA     = 5;
  EI_VERSION  = 6;
  EI_NIDENT   = 16;

  ELFCLASSNONE = 0;
  ELFCLASS32   = 1;
  ELFCLASS64   = 2;

  ELFDATANONE  = 0;
  ELFDATA2LSB  = 1;
  ELFDATA2MSB  = 2;

  EV_CURRENT   = 1;

  ET_NONE = 0;
  ET_REL  = 1;
  ET_EXEC = 2;
  ET_DYN  = 3;

  SHT_NULL     = 0;
  SHT_PROGBITS = 1;
  SHT_SYMTAB   = 2;
  SHT_STRTAB   = 3;
  SHT_RELA     = 4;

  SHF_NONE     = 0;
  { GNU extension: tell the linker to drop this section when producing
    a final executable or shared library.  Survives `ar`/`ld -r`, so a
    .bif section embedded here rides through static archives but never
    ends up in a runnable binary. }
  SHF_EXCLUDE  = $80000000;

  SHN_UNDEF    = 0;

  { Fixed on-disk sizes — the spec doesn't allow these to change.
    e_ehsize in the header confirms them at runtime. }
  ELF64_EHDR_SIZE = 64;
  ELF32_EHDR_SIZE = 52;
  ELF64_SHDR_SIZE = 64;
  ELF32_SHDR_SIZE = 40;

  { True iff APath starts with a valid ELF magic and we could
    decode the identifying header fields.  Never raises — returns
    False for non-ELF, short files, or I/O errors. }
function ProbeElf(const APath: string; out AInfo: TElfInfo): Boolean;

  { Read the full section header table out of APath, resolving each
    sh_name through .shstrtab.  Raises EElfObject on malformed input;
    returns an empty array if AInfo is not a valid ELF. }
function LoadSections(const APath: string; const AInfo: TElfInfo): TElfSectionArray;

  { Linear lookup by name.  Returns the index into ASections, or -1
    if not found (Blaise convention). }
function FindSection(const ASections: TElfSectionArray;
                     const AName: string): Integer;

  { Append a SHT_PROGBITS section named ASectionName containing AData
    to the relocatable ELF at APath.  The section is written with
    sh_flags = 0, so the system linker drops it from the final
    executable.

    Implementation strategy: the new .shstrtab and the appended
    section's data are placed at the current end-of-data; the section
    header table is rewritten and moved to the new end-of-file.
    Existing section contents never move, so relocations / symbols
    pointing into them stay valid.

    Raises EElfObject if APath isn't a usable ET_REL ELF, if the
    section already exists, or on I/O failure.  Currently 64-bit
    little-endian only — the only target the .bif pipeline cares
    about today. }
procedure AppendSection(const APath, ASectionName: string;
                        const AData: string);

  { Read the bytes of section ASectionName out of APath into a Blaise
    byte-string.  Returns True + fills AData on success, False if the
    section is absent (AData is set to '').  Raises EElfObject on a
    malformed ELF or I/O failure. }
function ReadSection(const APath, ASectionName: string;
                     var AData: string): Boolean;

implementation

{ ---- Endian helpers --------------------------------------------------

  All operate on a Blaise byte-oriented string (0-indexed); ABuf must
  be at least AOff + width bytes long. }

function ReadU16(ABuf: string; AOff: Integer; ALE: Boolean): Integer;
var
  B0, B1, K: Integer;
begin
  K := AOff;
  B0 := Ord(ABuf[K]);
  K := K + 1;
  B1 := Ord(ABuf[K]);
  if ALE then
    Result := B0 or (B1 shl 8)
  else
    Result := (B0 shl 8) or B1;
end;

function ReadU32(ABuf: string; AOff: Integer; ALE: Boolean): Integer;
var
  B0, B1, B2, B3, K: Integer;
begin
  K := AOff;
  B0 := Ord(ABuf[K]);  K := K + 1;
  B1 := Ord(ABuf[K]);  K := K + 1;
  B2 := Ord(ABuf[K]);  K := K + 1;
  B3 := Ord(ABuf[K]);
  if ALE then
    Result := B0 or (B1 shl 8) or (B2 shl 16) or (B3 shl 24)
  else
    Result := (B0 shl 24) or (B1 shl 16) or (B2 shl 8) or B3;
end;

function ReadU64(ABuf: string; AOff: Integer; ALE: Boolean): Int64;
var
  Lo, Hi: Int64;
begin
  if ALE then
  begin
    Lo := Int64(ReadU32(ABuf, AOff,     True))     and $FFFFFFFF;
    Hi := Int64(ReadU32(ABuf, AOff + 4, True))     and $FFFFFFFF;
  end
  else
  begin
    Hi := Int64(ReadU32(ABuf, AOff,     False))    and $FFFFFFFF;
    Lo := Int64(ReadU32(ABuf, AOff + 4, False))    and $FFFFFFFF;
  end;
  Result := Lo or (Hi shl 32);
end;

{ ---- Block-read helper ----------------------------------------------- }

{ Read ACount bytes from AStream at AOffset into a fresh Blaise string.
  Returns False (and leaves AOut empty) if the read came up short. }
function BlockRead(AStream: TFileInputStream; AOffset: Int64; ACount: Integer;
                   var AOut: string): Boolean;
var
  Got: Integer;
begin
  AOut := '';
  if ACount <= 0 then
  begin
    Result := True;
    Exit;
  end;
  SetLength(AOut, ACount);
  AStream.Seek(AOffset, soBeginning);
  Got := AStream.Read(PChar(AOut), ACount);
  Result := Got = ACount;
end;

{ ---- ProbeElf -------------------------------------------------------- }

function ProbeElf(const APath: string; out AInfo: TElfInfo): Boolean;
var
  FS:    TFileInputStream;
  Buf:   string;
  LE:    Boolean;
  Is64:  Boolean;
  HSize: Integer;
begin
  AInfo.IsElf         := False;
  AInfo.Is64          := False;
  AInfo.LittleEndian  := False;
  AInfo.IsRelocatable := False;
  AInfo.Machine       := 0;
  AInfo.ShOff         := 0;
  AInfo.ShEntSize     := 0;
  AInfo.ShNum         := 0;
  AInfo.ShStrNdx      := 0;
  Result := False;

  if not FileExists(APath) then
    Exit;

  try
    FS := TFileInputStream.Create(APath);
  except
    Exit;
  end;
  try
    if FS.Size() < ELF32_EHDR_SIZE then
      Exit;

    { Always read the larger 64-bit header — if the file is 32-bit
      we just look at fewer of the trailing fields. }
    HSize := ELF64_EHDR_SIZE;
    if FS.Size() < HSize then
      HSize := ELF32_EHDR_SIZE;

    if not BlockRead(FS, 0, HSize, Buf) then
      Exit;

    { Magic. }
    if (Ord(Buf[0]) <> ELFMAG0) or (Ord(Buf[1]) <> ELFMAG1)
    or (Ord(Buf[2]) <> ELFMAG2) or (Ord(Buf[3]) <> ELFMAG3) then
      Exit;

    AInfo.IsElf := True;

    case Ord(Buf[EI_CLASS]) of
      ELFCLASS32: Is64 := False;
      ELFCLASS64: Is64 := True;
    else
      Exit;
    end;
    AInfo.Is64 := Is64;

    case Ord(Buf[EI_DATA]) of
      ELFDATA2LSB: LE := True;
      ELFDATA2MSB: LE := False;
    else
      Exit;
    end;
    AInfo.LittleEndian := LE;

    if Ord(Buf[EI_VERSION]) <> EV_CURRENT then
      Exit;

    if Is64 and (HSize < ELF64_EHDR_SIZE) then
      Exit;

    { Fixed offsets per ELF spec. }
    AInfo.Machine       := ReadU16(Buf, EI_NIDENT + 2, LE);
    AInfo.IsRelocatable := ReadU16(Buf, EI_NIDENT,     LE) = ET_REL;

    if Is64 then
    begin
      AInfo.ShOff     := ReadU64(Buf, 40, LE);
      AInfo.ShEntSize := ReadU16(Buf, 58, LE);
      AInfo.ShNum     := ReadU16(Buf, 60, LE);
      AInfo.ShStrNdx  := ReadU16(Buf, 62, LE);
    end
    else
    begin
      AInfo.ShOff     := ReadU32(Buf, 32, LE);
      AInfo.ShEntSize := ReadU16(Buf, 46, LE);
      AInfo.ShNum     := ReadU16(Buf, 48, LE);
      AInfo.ShStrNdx  := ReadU16(Buf, 50, LE);
    end;

    Result := True;
  finally
    FS.Free();
  end;
end;

{ ---- Section header table walker ------------------------------------ }

{ Extract a NUL-terminated string from a byte buffer at AOff.  Returns
  '' if AOff is out of range or no terminator is found. }
function StringFromStrtab(const ABuf: string; AOff: Integer): string;
var
  EndIdx, I, Len: Integer;
  S: string;
begin
  Result := '';
  Len := Length(ABuf);
  if (AOff < 0) or (AOff >= Len) then
    Exit;
  EndIdx := -1;
  I := AOff;
  while I < Len do
  begin
    if Ord(ABuf[I]) = 0 then
    begin
      EndIdx := I;
      break;
    end;
    I := I + 1;
  end;
  if EndIdx < 0 then
    Exit;
  if EndIdx > AOff then
    S := Copy(ABuf, AOff, EndIdx - AOff)
  else
    S := '';
  Result := S;
end;

{ Decode the four fields we care about from a single SHT entry buffer.
  Field offsets in both Elf32_Shdr (40 B) and Elf64_Shdr (64 B):
    sh_name   @ 0  (4 B, both)
    sh_type   @ 4  (4 B, both)
    sh_offset @ 16 (4 B Elf32) / 24 (8 B Elf64)
    sh_size   @ 20 (4 B Elf32) / 32 (8 B Elf64) }
procedure DecodeShdr(const ABuf: string; AOff: Integer;
                     AIs64, ALE: Boolean;
                     var ANameOff, AType: Integer;
                     var AOffset, ASize: Int64);
begin
  ANameOff := ReadU32(ABuf, AOff + 0, ALE);
  AType    := ReadU32(ABuf, AOff + 4, ALE);
  if AIs64 then
  begin
    AOffset := ReadU64(ABuf, AOff + 24, ALE);
    ASize   := ReadU64(ABuf, AOff + 32, ALE);
  end
  else
  begin
    AOffset := Int64(ReadU32(ABuf, AOff + 16, ALE)) and $FFFFFFFF;
    ASize   := Int64(ReadU32(ABuf, AOff + 20, ALE)) and $FFFFFFFF;
  end;
end;

function LoadSections(const APath: string; const AInfo: TElfInfo): TElfSectionArray;
var
  FS:        TFileInputStream;
  ShtBuf:    string;
  StrBuf:    string;
  I:         Integer;
  StrOff:    Int64;
  StrSize:   Int64;
  StrType:   Integer;
  StrName:   Integer;
  EntrySize: Integer;
  NameOff, SType: Integer;
  Offset, Size:   Int64;
  Sects:     TElfSectionArray;
  Sec:       TElfSection;
begin
  SetLength(Result, 0);
  if (not AInfo.IsElf) or (AInfo.ShNum = 0) then
    Exit;

  EntrySize := AInfo.ShEntSize;
  if EntrySize < ELF32_SHDR_SIZE then
    raise EElfObject.Create(APath + ': section header entry too small');
  if AInfo.ShStrNdx >= AInfo.ShNum then
    raise EElfObject.Create(APath + ': e_shstrndx out of range');

  FS := TFileInputStream.Create(APath);
  try
    { Slurp the whole SHT in one go.  Even 1000 sections × 64 B is
      64 KB — cheap. }
    FS.Seek(AInfo.ShOff, soBeginning);
    SetLength(ShtBuf, AInfo.ShNum * EntrySize);
    if FS.Read(PChar(ShtBuf), AInfo.ShNum * EntrySize) <> AInfo.ShNum * EntrySize then
      raise EElfObject.Create(APath + ': short read on section header table');

    { Pull .shstrtab — the section at index e_shstrndx. }
    DecodeShdr(ShtBuf, AInfo.ShStrNdx * EntrySize,
               AInfo.Is64, AInfo.LittleEndian,
               StrName, StrType, StrOff, StrSize);
    if StrType <> SHT_STRTAB then
      raise EElfObject.Create(APath + ': e_shstrndx is not SHT_STRTAB');

    StrBuf := '';
    if StrSize > 0 then
    begin
      FS.Seek(StrOff, soBeginning);
      SetLength(StrBuf, Integer(StrSize));
      if FS.Read(PChar(StrBuf), Integer(StrSize)) <> Integer(StrSize) then
        raise EElfObject.Create(APath + ': short read on .shstrtab');
    end;

    SetLength(Sects, AInfo.ShNum);
    I := 0;
    while I < AInfo.ShNum do
    begin
      { Inline decode — keep parameter passing out of the hot loop. }
      NameOff := ReadU32(ShtBuf, I * EntrySize + 0,  AInfo.LittleEndian);
      SType   := ReadU32(ShtBuf, I * EntrySize + 4,  AInfo.LittleEndian);
      if AInfo.Is64 then
      begin
        Offset := ReadU64(ShtBuf, I * EntrySize + 24, AInfo.LittleEndian);
        Size   := ReadU64(ShtBuf, I * EntrySize + 32, AInfo.LittleEndian);
      end
      else
      begin
        Offset := Int64(ReadU32(ShtBuf, I * EntrySize + 16, AInfo.LittleEndian)) and $FFFFFFFF;
        Size   := Int64(ReadU32(ShtBuf, I * EntrySize + 20, AInfo.LittleEndian)) and $FFFFFFFF;
      end;
      Sec := TElfSection.Create();
      Sec.NameOff := NameOff;
      Sec.SType   := SType;
      Sec.Offset  := Offset;
      Sec.Size    := Size;
      Sec.Name    := StringFromStrtab(StrBuf, NameOff);
      Sects[I]    := Sec;
      I := I + 1;
    end;
    Result := Sects;
  finally
    FS.Free();
  end;
end;

function FindSection(const ASections: TElfSectionArray;
                     const AName: string): Integer;
var
  I: Integer;
begin
  I := 0;
  while I <= High(ASections) do
  begin
    if ASections[I].Name = AName then
    begin
      Result := I;
      Exit;
    end;
    I := I + 1;
  end;
  Result := -1;
end;

{ Zero a Blaise byte-string in place — Blaise's parser rejects
  `PChar(buf)[i] := ...`, so the indirection through a local pointer
  is mandatory. }
procedure ZeroBuf(var ABuf: string; ACount: Integer);
var
  P: PChar;
  I: Integer;
begin
  P := PChar(ABuf);
  I := 0;
  while I < ACount do
  begin
    P[I] := Chr(0);
    I := I + 1;
  end;
end;

{ ---- Endian-aware byte writers (LE only for now) -------------------- }

procedure WriteU16LE(var ABuf: string; AOff: Integer; AVal: Integer);
var
  P: PChar;
  K: Integer;
begin
  P := PChar(ABuf);
  K := AOff;
  P[K] := Chr(AVal and $FF);          K := K + 1;
  P[K] := Chr((AVal shr 8) and $FF);
end;

procedure WriteU32LE(var ABuf: string; AOff: Integer; AVal: Integer);
var
  P: PChar;
  K: Integer;
begin
  P := PChar(ABuf);
  K := AOff;
  P[K] := Chr(AVal and $FF);          K := K + 1;
  P[K] := Chr((AVal shr 8) and $FF);  K := K + 1;
  P[K] := Chr((AVal shr 16) and $FF); K := K + 1;
  P[K] := Chr((AVal shr 24) and $FF);
end;

procedure WriteU64LE(var ABuf: string; AOff: Integer; AVal: Int64);
var
  Lo, Hi: Int64;
begin
  Lo := AVal and $FFFFFFFF;
  Hi := (AVal shr 32) and $FFFFFFFF;
  WriteU32LE(ABuf, AOff,     Integer(Lo));
  WriteU32LE(ABuf, AOff + 4, Integer(Hi));
end;

{ Round AVal up to the next multiple of AAlign (AAlign must be a power of 2). }
function AlignUp(AVal: Int64; AAlign: Int64): Int64;
var
  Rem: Int64;
begin
  Rem := AVal mod AAlign;
  if Rem = 0 then
    Result := AVal
  else
    Result := AVal + (AAlign - Rem);
end;

{ ---- AppendSection -------------------------------------------------- }

procedure AppendSection(const APath, ASectionName: string;
                        const AData: string);
var
  Info:      TElfInfo;
  Secs:      TElfSectionArray;
  FIn:       TFileInputStream;
  FOut:      TFileOutputStream;
  OldFile:   string;       { entire original file }
  OldStrBuf: string;       { current .shstrtab contents }
  NewStrBuf: string;       { .shstrtab with our name appended }
  ShtBuf:    string;       { rewritten SHT }
  Pad:       string;
  TmpPath:   string;
  I:         Integer;
  DataEnd:   Int64;        { highest sh_offset+sh_size across all sections }
  StrEnd:    Int64;
  NewStrOff: Int64;
  NewDataOff: Int64;
  NewShOff:  Int64;
  NewShNum:  Integer;
  NewNameOff: Integer;
  EntrySize: Integer;
  HdrBuf:    string;
  BodyBuf:   string;
begin
  if not ProbeElf(APath, Info) then
    raise EElfObject.Create(APath + ': not a valid ELF');
  if not Info.IsRelocatable then
    raise EElfObject.Create(APath + ': not a relocatable ELF (ET_REL)');
  if not Info.Is64 then
    raise EElfObject.Create(APath + ': only 64-bit ELF supported');
  if not Info.LittleEndian then
    raise EElfObject.Create(APath + ': only little-endian ELF supported');

  Secs := LoadSections(APath, Info);
  if FindSection(Secs, ASectionName) >= 0 then
    raise EElfObject.Create(APath + ': section ' + ASectionName +
                            ' already present');

  { Slurp the entire file. }
  FIn := TFileInputStream.Create(APath);
  try
    SetLength(OldFile, Integer(FIn.Size()));
    if FIn.Read(PChar(OldFile), Length(OldFile)) <> Length(OldFile) then
      raise EElfObject.Create(APath + ': short read on original file');
  finally
    FIn.Free();
  end;

  EntrySize := Info.ShEntSize;

  { Pull the existing .shstrtab contents from OldFile. }
  StrEnd := Secs[Info.ShStrNdx].Offset + Secs[Info.ShStrNdx].Size;
  OldStrBuf := Copy(OldFile, Integer(Secs[Info.ShStrNdx].Offset),
                    Integer(Secs[Info.ShStrNdx].Size));

  { New .shstrtab = old + name + #0.  Record the offset at which our
    name starts — that becomes the new entry's sh_name. }
  NewNameOff := Length(OldStrBuf);
  NewStrBuf  := OldStrBuf + ASectionName + Chr(0);

  { Compute DataEnd — the highest end of any existing section's bytes,
    excluding the SHT itself.  We will place new data after this point
    so existing offsets remain valid. }
  DataEnd := 0;
  I := 0;
  while I <= High(Secs) do
  begin
    if (Secs[I].SType <> SHT_NULL) and (Secs[I].SType <> 8) then  { 8 = SHT_NOBITS }
    begin
      if Secs[I].Offset + Secs[I].Size > DataEnd then
        DataEnd := Secs[I].Offset + Secs[I].Size;
    end;
    I := I + 1;
  end;

  { Layout (file offsets), aligned to 8 between blocks:
        [0 .. DataEnd)             — original file body, verbatim
        NewStrOff  .. + NewStrBuf  — replacement .shstrtab
        NewDataOff .. + AData      — our section's payload
        NewShOff   .. + new SHT    — rewritten section header table }
  NewStrOff  := AlignUp(DataEnd,    1);
  NewDataOff := AlignUp(NewStrOff + Length(NewStrBuf), 8);
  NewShOff   := AlignUp(NewDataOff + Length(AData),    8);
  NewShNum   := Info.ShNum + 1;

  { Build the new SHT in memory.  Start with the verbatim original
    SHT slice from the file, padded with one zero entry for our new
    section. }
  ShtBuf := Copy(OldFile, Integer(Info.ShOff), Info.ShNum * EntrySize);
  { Append EntrySize zero bytes for the new entry. }
  SetLength(Pad, EntrySize);
  ZeroBuf(Pad, EntrySize);
  ShtBuf := ShtBuf + Pad;

  { Patch .shstrtab entry: sh_offset and sh_size. }
  WriteU64LE(ShtBuf, Info.ShStrNdx * EntrySize + 24, NewStrOff);
  WriteU64LE(ShtBuf, Info.ShStrNdx * EntrySize + 32, Int64(Length(NewStrBuf)));
  WriteU32LE(ShtBuf, Info.ShNum * EntrySize + 0,  NewNameOff);          { sh_name }
  WriteU32LE(ShtBuf, Info.ShNum * EntrySize + 4,  SHT_PROGBITS);         { sh_type }
  { Pass SHF_EXCLUDE as a positive Int64 — the Integer constant
    $80000000 sign-extends to 0xFFFFFFFF80000000 otherwise. }
  WriteU64LE(ShtBuf, Info.ShNum * EntrySize + 8,
             Int64(SHF_EXCLUDE) and $FFFFFFFF);                          { sh_flags }
  WriteU64LE(ShtBuf, Info.ShNum * EntrySize + 16, 0);                    { sh_addr }
  WriteU64LE(ShtBuf, Info.ShNum * EntrySize + 24, NewDataOff);           { sh_offset }
  WriteU64LE(ShtBuf, Info.ShNum * EntrySize + 32, Int64(Length(AData))); { sh_size }
  WriteU32LE(ShtBuf, Info.ShNum * EntrySize + 40, SHN_UNDEF);            { sh_link }
  WriteU32LE(ShtBuf, Info.ShNum * EntrySize + 44, 0);                    { sh_info }
  WriteU64LE(ShtBuf, Info.ShNum * EntrySize + 48, 1);                    { sh_addralign }
  WriteU64LE(ShtBuf, Info.ShNum * EntrySize + 56, 0);                    { sh_entsize }

  { Patch the file header: e_shoff and e_shnum.  We hold the original
    64-byte header in a separate buffer so we can update it in place. }
  HdrBuf := Copy(OldFile, 0, ELF64_EHDR_SIZE);
  WriteU64LE(HdrBuf, 40, NewShOff);
  WriteU16LE(HdrBuf, 60, NewShNum);

  { Pad helper — bytes of zero. }
  SetLength(Pad, 8);
  ZeroBuf(Pad, 8);

  { Write everything to APath.tmp, then rename over APath. }
  TmpPath := APath + '.tmp';
  FOut := TFileOutputStream.Create(TmpPath);
  try
    { 1. Patched ELF header. }
    FOut.Write(PChar(HdrBuf), ELF64_EHDR_SIZE);
    { 2. Original body from EhSize .. DataEnd. }
    BodyBuf := Copy(OldFile, ELF64_EHDR_SIZE,
                    Integer(DataEnd) - ELF64_EHDR_SIZE);
    FOut.Write(PChar(BodyBuf), Length(BodyBuf));
    { 3. New .shstrtab. }
    if NewStrOff > DataEnd then
      FOut.Write(PChar(Pad), Integer(NewStrOff - DataEnd));
    FOut.Write(PChar(NewStrBuf), Length(NewStrBuf));
    { 4. Padding to NewDataOff, then our payload. }
    if NewDataOff > NewStrOff + Length(NewStrBuf) then
      FOut.Write(PChar(Pad), Integer(NewDataOff - (NewStrOff + Length(NewStrBuf))));
    if Length(AData) > 0 then
      FOut.Write(PChar(AData), Length(AData));
    { 5. Padding to NewShOff, then the rewritten SHT. }
    if NewShOff > NewDataOff + Length(AData) then
      FOut.Write(PChar(Pad), Integer(NewShOff - (NewDataOff + Length(AData))));
    FOut.Write(PChar(ShtBuf), Length(ShtBuf));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;

  { Atomic-ish rename. }
  if not RenameFile(TmpPath, APath) then
    raise EElfObject.Create(APath + ': rename of temp file failed');
end;

{ ---- ReadSection ---------------------------------------------------- }

function ReadSection(const APath, ASectionName: string;
                     var AData: string): Boolean;
var
  Info:  TElfInfo;
  Secs:  TElfSectionArray;
  Idx:   Integer;
  FIn:   TFileInputStream;
  Sec:   TElfSection;
begin
  AData  := '';
  Result := False;
  if not ProbeElf(APath, Info) then
    Exit;
  Secs := LoadSections(APath, Info);
  Idx := FindSection(Secs, ASectionName);
  if Idx < 0 then
    Exit;
  Sec := Secs[Idx];
  if Sec.Size <= 0 then
  begin
    Result := True;
    Exit;
  end;
  FIn := TFileInputStream.Create(APath);
  try
    FIn.Seek(Sec.Offset, soBeginning);
    SetLength(AData, Integer(Sec.Size));
    if FIn.Read(PChar(AData), Integer(Sec.Size)) <> Integer(Sec.Size) then
      raise EElfObject.Create(APath + ': short read on section ' + ASectionName);
  finally
    FIn.Free();
  end;
  Result := True;
end;

end.
