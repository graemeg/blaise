{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.elfreader;

{ ELF relocatable-object and ar-archive reader for the internal linker.

  Phase A of the internal-linker plan (docs/internal-linker-design.adoc):
  parse ELF64 little-endian ET_REL object files — section headers with
  contents, the symbol table, and RELA relocation entries — plus the
  `!<arch>` static archive format with GNU long-name table support
  (blaise_rtl.a contains member names longer than the 15-character ar
  limit).

  Scope deliberately mirrors what the linker consumes: 64-bit
  little-endian x86-64 relocatable objects only.  uElfObject.pas stays
  untouched — its narrow .bif-section append/read purpose and this
  unit's whole-object parse serve different pipelines.

  All parsed entities are heap objects (classes), not records, because
  dynamic-array-of-record element assignment scrambles payloads in the
  current compiler (see uElfObject.pas).  Byte buffers are Blaise
  strings (0-indexed, byte oriented). }

interface

uses
  SysUtils, Generics.Collections, streams;

const
  { ELF identification }
  ELFCLASS64  = 2;
  ELFDATA2LSB = 1;
  ET_REL      = 1;
  EM_X86_64   = 62;

  ELF64_EHDR_SIZE = 64;
  ELF64_SHDR_SIZE = 64;
  ELF64_SYM_SIZE  = 24;
  ELF64_RELA_SIZE = 24;

  { Section header types }
  SHT_NULL     = 0;
  SHT_PROGBITS = 1;
  SHT_SYMTAB   = 2;
  SHT_STRTAB   = 3;
  SHT_RELA     = 4;
  SHT_NOBITS   = 8;
  SHT_INIT_ARRAY = 14;
  SHT_FINI_ARRAY = 15;

  { Section flags }
  SHF_WRITE     = $1;
  SHF_ALLOC     = $2;
  SHF_EXECINSTR = $4;
  SHF_TLS       = $400;

  { Symbol binding / type }
  STB_LOCAL  = 0;
  STB_GLOBAL = 1;
  STB_WEAK   = 2;

  STT_NOTYPE  = 0;
  STT_OBJECT  = 1;
  STT_FUNC    = 2;
  STT_SECTION = 3;
  STT_FILE    = 4;
  STT_TLS     = 6;

  { Special section indices }
  SHN_UNDEF  = 0;
  SHN_ABS    = $FFF1;
  SHN_COMMON = $FFF2;

  { x86-64 relocation types }
  R_X86_64_NONE       = 0;
  R_X86_64_64         = 1;
  R_X86_64_PC32       = 2;
  R_X86_64_PLT32      = 4;
  R_X86_64_GOTPCREL   = 9;
  R_X86_64_32         = 10;
  R_X86_64_32S        = 11;
  R_X86_64_TPOFF32    = 23;
  R_X86_64_GOTPCRELX  = 41;
  R_X86_64_REX_GOTPCRELX = 42;

type
  EElfReader = class(Exception);

  { One parsed section: header fields plus raw contents (empty for
    SHT_NOBITS). }
  TRdSection = class
  public
    Name:       string;
    ShType:     Int;
    Flags:      Int64;
    FileOffset: Int64;
    Size:       Int64;
    Link:       Int;
    Info:       Int;
    AddrAlign:  Int64;
    EntSize:    Int64;
    Data:       string;
  end;

  { One symbol-table entry. }
  TRdSymbol = class
  public
    Name:    string;
    Value:   Int64;
    Size:    Int64;
    Bind:    Int;    { STB_* }
    SymType: Int;    { STT_* }
    Shndx:   Int;    { SHN_UNDEF / SHN_ABS / section index }
  end;

  { One RELA entry, tagged with the section it patches. }
  TRdReloc = class
  public
    TargetSection: Int;  { ELF section index the reloc applies to }
    Offset:        Int64;    { byte offset within that section }
    SymIndex:      Int;  { index into Symbols }
    RelocType:     Int;  { R_X86_64_* }
    Addend:        Int64;
  end;

  { A fully parsed relocatable object. }
  TElfObjectFile = class
  public
    SourceName: string;                 { file or archive member name }
    Sections:   TList<TRdSection>;      { index = ELF section index }
    Symbols:    TList<TRdSymbol>;       { index = symtab index }
    Relocs:     TList<TRdReloc>;
    constructor Create;
    destructor Destroy; override;
    function SectionIndexOf(const AName: string): Int;
    function FindSection(const AName: string): TRdSection;
  end;

  { One member of a static archive. }
  TArchiveMember = class
  public
    Name: string;
    Data: string;
  end;

{ Parse an ELF64 LSB ET_REL object from an in-memory byte buffer.
  ASourceName is used in error messages and stored on the result.
  Raises EElfReader on malformed or unsupported input.  Caller frees. }
function ParseElfObject(const ABytes: string;
  const ASourceName: string): TElfObjectFile;

{ Read and parse an object file from disk. }
function ReadElfObjectFile(const APath: string): TElfObjectFile;

{ Parse a `!<arch>` static archive into AMembers.  Resolves GNU long
  names via the `//` table; the symbol-index members (`/` and
  `/SYM64/`) and the long-name table itself are not returned.  The
  caller owns AMembers and frees its elements. }
procedure ParseArchive(const ABytes: string; const ASourceName: string;
  AMembers: TList<TArchiveMember>);

{ Read and parse an archive from disk into AMembers. }
procedure ReadArchiveFile(const APath: string;
  AMembers: TList<TArchiveMember>);

{ Read an entire file into a byte string.  Raises EElfReader on I/O
  failure. }
function ReadWholeFile(const APath: string): string;

implementation

{ ---- Little-endian readers (x86-64 scope: LE only) -------------------- }

function RdU16(const ABuf: string; AOff: Int): Int32;
begin
  Result := (Ord(ABuf[AOff]) and $FF)
         or ((Ord(ABuf[AOff + 1]) and $FF) shl 8);
end;

function RdU32(const ABuf: string; AOff: Int): Int32;
begin
  Result := (Ord(ABuf[AOff]) and $FF)
         or ((Ord(ABuf[AOff + 1]) and $FF) shl 8)
         or ((Ord(ABuf[AOff + 2]) and $FF) shl 16)
         or ((Ord(ABuf[AOff + 3]) and $FF) shl 24);
end;

function RdU64(const ABuf: string; AOff: Int): Int64;
var
  Lo, Hi: Int64;
begin
  Lo := Int64(RdU32(ABuf, AOff)) and $FFFFFFFF;
  Hi := Int64(RdU32(ABuf, AOff + 4)) and $FFFFFFFF;
  Result := Lo or (Hi shl 32);
end;

{ NUL-terminated string starting at AOff. }
function RdStrZ(const ABuf: string; AOff: Int): string;
var
  P: Int;
begin
  Result := '';
  P := AOff;
  while (P < Length(ABuf)) and (ABuf[P] <> 0) do
  begin
    Result := Result + Chr(ABuf[P]);
    P := P + 1;
  end;
end;

{ ---- TElfObjectFile ---------------------------------------------------- }

constructor TElfObjectFile.Create;
begin
  inherited Create();
  SourceName := '';
  Sections := TList<TRdSection>.Create();
  Symbols := TList<TRdSymbol>.Create();
  Relocs := TList<TRdReloc>.Create();
end;

destructor TElfObjectFile.Destroy;
var
  I: Int;
begin
  for I := 0 to Sections.Count - 1 do
    Sections.Get(I).Free();
  Sections.Free();
  for I := 0 to Symbols.Count - 1 do
    Symbols.Get(I).Free();
  Symbols.Free();
  for I := 0 to Relocs.Count - 1 do
    Relocs.Get(I).Free();
  Relocs.Free();
  inherited Destroy();
end;

function TElfObjectFile.SectionIndexOf(const AName: string): Int;
var
  I: Int;
begin
  for I := 0 to Sections.Count - 1 do
    if Sections.Get(I).Name = AName then
    begin
      Result := I;
      Exit;
    end;
  Result := -1;
end;

function TElfObjectFile.FindSection(const AName: string): TRdSection;
var
  Idx: Int;
begin
  Idx := Self.SectionIndexOf(AName);
  if Idx >= 0 then
    Result := Sections.Get(Idx)
  else
    Result := nil;
end;

{ ---- Object parsing ---------------------------------------------------- }

function ParseElfObject(const ABytes: string;
  const ASourceName: string): TElfObjectFile;
var
  Obj: TElfObjectFile;
  ShOff: Int64;
  ShEntSize, ShNum, ShStrNdx: Int;
  I, J: Int;
  HdrOff: Int64;
  Sec: TRdSection;
  ShStr: TRdSection;
  Sym: TRdSymbol;
  Rel: TRdReloc;
  StrSec: TRdSection;
  SymCount, RelCount: Int;
  EntOff: Int64;
  InfoByte: Int;
  RInfo: Int64;
begin
  if Length(ABytes) < ELF64_EHDR_SIZE then
    raise EElfReader.Create(ASourceName + ': file too small for ELF header');
  if (Ord(ABytes[0]) <> $7F) or (Ord(ABytes[1]) <> Ord('E')) or
     (Ord(ABytes[2]) <> Ord('L')) or (Ord(ABytes[3]) <> Ord('F')) then
    raise EElfReader.Create(ASourceName + ': not an ELF file (bad magic)');
  if Ord(ABytes[4]) <> ELFCLASS64 then
    raise EElfReader.Create(ASourceName + ': not ELFCLASS64');
  if Ord(ABytes[5]) <> ELFDATA2LSB then
    raise EElfReader.Create(ASourceName + ': not little-endian');
  if RdU16(ABytes, 16) <> ET_REL then
    raise EElfReader.Create(ASourceName + ': not a relocatable object (ET_REL)');
  if RdU16(ABytes, 18) <> EM_X86_64 then
    raise EElfReader.Create(ASourceName + ': not an x86-64 object');

  ShOff := RdU64(ABytes, 40);
  ShEntSize := RdU16(ABytes, 58);
  ShNum := RdU16(ABytes, 60);
  ShStrNdx := RdU16(ABytes, 62);
  if ShEntSize <> ELF64_SHDR_SIZE then
    raise EElfReader.Create(ASourceName + ': unexpected e_shentsize '
      + IntToStr(ShEntSize));
  if (ShNum <= 0) or (ShOff <= 0) then
    raise EElfReader.Create(ASourceName + ': missing section header table');
  if ShOff + Int64(ShNum) * ELF64_SHDR_SIZE > Length(ABytes) then
    raise EElfReader.Create(ASourceName + ': section header table truncated');

  Obj := TElfObjectFile.Create();
  try
    Obj.SourceName := ASourceName;

    { Pass 1: headers + raw data.  Names resolved after .shstrtab is in. }
    for I := 0 to ShNum - 1 do
    begin
      HdrOff := ShOff + Int64(I) * ELF64_SHDR_SIZE;
      Sec := TRdSection.Create();
      Sec.Name := '';
      Sec.ShType := RdU32(ABytes, Int32(HdrOff) + 4);
      Sec.Flags := RdU64(ABytes, Int32(HdrOff) + 8);
      Sec.FileOffset := RdU64(ABytes, Int32(HdrOff) + 24);
      Sec.Size := RdU64(ABytes, Int32(HdrOff) + 32);
      Sec.Link := RdU32(ABytes, Int32(HdrOff) + 40);
      Sec.Info := RdU32(ABytes, Int32(HdrOff) + 44);
      Sec.AddrAlign := RdU64(ABytes, Int32(HdrOff) + 48);
      Sec.EntSize := RdU64(ABytes, Int32(HdrOff) + 56);
      Sec.Data := '';
      if (Sec.ShType <> SHT_NOBITS) and (Sec.ShType <> SHT_NULL) and
         (Sec.Size > 0) then
      begin
        if Sec.FileOffset + Sec.Size > Length(ABytes) then
          raise EElfReader.Create(ASourceName + ': section '
            + IntToStr(I) + ' data truncated');
        Sec.Data := Copy(ABytes, Int32(Sec.FileOffset), Int32(Sec.Size));
      end;
      Obj.Sections.Add(Sec);
    end;

    { Pass 2: resolve section names through .shstrtab. }
    if (ShStrNdx <= 0) or (ShStrNdx >= ShNum) then
      raise EElfReader.Create(ASourceName + ': bad e_shstrndx');
    ShStr := Obj.Sections.Get(ShStrNdx);
    for I := 0 to ShNum - 1 do
    begin
      HdrOff := ShOff + Int64(I) * ELF64_SHDR_SIZE;
      Sec := Obj.Sections.Get(I);
      Sec.Name := RdStrZ(ShStr.Data, RdU32(ABytes, Int32(HdrOff)));
    end;

    { Symbol table (at most one SHT_SYMTAB in a relocatable object). }
    for I := 0 to ShNum - 1 do
    begin
      Sec := Obj.Sections.Get(I);
      if Sec.ShType <> SHT_SYMTAB then Continue;
      if (Sec.Link <= 0) or (Sec.Link >= ShNum) then
        raise EElfReader.Create(ASourceName + ': symtab has bad strtab link');
      StrSec := Obj.Sections.Get(Sec.Link);
      SymCount := Int32(Sec.Size) div ELF64_SYM_SIZE;
      for J := 0 to SymCount - 1 do
      begin
        EntOff := Int64(J) * ELF64_SYM_SIZE;
        Sym := TRdSymbol.Create();
        Sym.Name := RdStrZ(StrSec.Data, RdU32(Sec.Data, Int32(EntOff)));
        InfoByte := Ord(Sec.Data[Int32(EntOff) + 4]) and $FF;
        Sym.Bind := InfoByte shr 4;
        Sym.SymType := InfoByte and $F;
        Sym.Shndx := RdU16(Sec.Data, Int32(EntOff) + 6);
        Sym.Value := RdU64(Sec.Data, Int32(EntOff) + 8);
        Sym.Size := RdU64(Sec.Data, Int32(EntOff) + 16);
        Obj.Symbols.Add(Sym);
      end;
    end;

    { Relocation sections. }
    for I := 0 to ShNum - 1 do
    begin
      Sec := Obj.Sections.Get(I);
      if Sec.ShType <> SHT_RELA then Continue;
      RelCount := Int32(Sec.Size) div ELF64_RELA_SIZE;
      for J := 0 to RelCount - 1 do
      begin
        EntOff := Int64(J) * ELF64_RELA_SIZE;
        Rel := TRdReloc.Create();
        Rel.TargetSection := Sec.Info;
        Rel.Offset := RdU64(Sec.Data, Int32(EntOff));
        RInfo := RdU64(Sec.Data, Int32(EntOff) + 8);
        Rel.SymIndex := Int32(RInfo shr 32);
        Rel.RelocType := Int32(RInfo and $FFFFFFFF);
        Rel.Addend := RdU64(Sec.Data, Int32(EntOff) + 16);
        Obj.Relocs.Add(Rel);
      end;
    end;

    Result := Obj;
  except
    Obj.Free();
    raise;
  end;
end;

function ReadWholeFile(const APath: string): string;
var
  FS: TFileInputStream;
  Sz: Int64;
  Got: Int;
begin
  FS := TFileInputStream.Create(APath);
  try
    Sz := FS.Size();
    Result := '';
    if Sz > 0 then
    begin
      SetLength(Result, Int32(Sz));
      Got := FS.Read(PChar(Result), Int32(Sz));
      if Got <> Int32(Sz) then
        raise EElfReader.Create(APath + ': short read ('
          + IntToStr(Got) + ' of ' + IntToStr(Sz) + ' bytes)');
    end;
  finally
    FS.Close();
    FS.Free();
  end;
end;

function ReadElfObjectFile(const APath: string): TElfObjectFile;
begin
  Result := ParseElfObject(ReadWholeFile(APath), APath);
end;

{ ---- Archive parsing --------------------------------------------------- }

function ArTrimField(const S: string): string;
var
  Hi: Int;
begin
  Hi := Length(S) - 1;
  while (Hi >= 0) and ((S[Hi] = Ord(' ')) or (S[Hi] = 0)) do
    Hi := Hi - 1;
  Result := Copy(S, 0, Hi + 1);
end;

function ArParseDec(const S: string): Int64;
var
  I: Int;
  C: Int;
begin
  Result := 0;
  I := 0;
  while I < Length(S) do
  begin
    C := S[I];
    if (C < Ord('0')) or (C > Ord('9')) then break;
    Result := Result * 10 + (C - Ord('0'));
    I := I + 1;
  end;
end;

procedure ParseArchive(const ABytes: string; const ASourceName: string;
  AMembers: TList<TArchiveMember>);
var
  P: Int64;
  NameField, SizeField: string;
  MemberSize: Int64;
  LongNames: string;
  Name: string;
  NameOff: Int;
  E: Int;
  M: TArchiveMember;
  I: Int;
begin
  if (Length(ABytes) < 8) or (Copy(ABytes, 0, 8) <> '!<arch>' + #10) then
    raise EElfReader.Create(ASourceName + ': not an ar archive (bad magic)');

  LongNames := '';
  P := 8;
  try
    while P + 60 <= Length(ABytes) do
    begin
      { 60-byte member header: name[16] mtime[12] uid[6] gid[6]
        mode[8] size[10] magic[2] }
      if (Ord(ABytes[Int32(P) + 58]) <> Ord('`')) or
         (Ord(ABytes[Int32(P) + 59]) <> 10) then
        raise EElfReader.Create(ASourceName
          + ': corrupt member header at offset ' + IntToStr(P));
      NameField := ArTrimField(Copy(ABytes, Int32(P), 16));
      SizeField := Copy(ABytes, Int32(P) + 48, 10);
      MemberSize := ArParseDec(ArTrimField(SizeField));
      P := P + 60;
      if P + MemberSize > Length(ABytes) then
        raise EElfReader.Create(ASourceName + ': member data truncated');

      if NameField = '//' then
        { GNU long-name table }
        LongNames := Copy(ABytes, Int32(P), Int32(MemberSize))
      else if (NameField = '/') or (NameField = '/SYM64/') then
        { symbol index — skip }
      else
      begin
        if (Length(NameField) > 1) and (NameField[0] = Ord('/')) and
           (NameField[1] >= Ord('0')) and (NameField[1] <= Ord('9')) then
        begin
          { /N — offset into the long-name table; the entry runs to
            '/' or newline. }
          NameOff := Int32(ArParseDec(Copy(NameField, 1,
            Length(NameField) - 1)));
          Name := '';
          E := NameOff;
          while (E < Length(LongNames)) and (LongNames[E] <> Ord('/'))
                and (LongNames[E] <> 10) do
          begin
            Name := Name + Chr(LongNames[E]);
            E := E + 1;
          end;
        end
        else
        begin
          { Short name — strip the trailing '/'. }
          Name := NameField;
          if (Length(Name) > 0) and (Name[Length(Name) - 1] = Ord('/')) then
            Name := Copy(Name, 0, Length(Name) - 1);
        end;
        M := TArchiveMember.Create();
        M.Name := Name;
        M.Data := Copy(ABytes, Int32(P), Int32(MemberSize));
        AMembers.Add(M);
      end;

      P := P + MemberSize;
      if (P and 1) = 1 then
        P := P + 1;       { members are 2-byte aligned }
    end;
  except
    { On failure, hand back an empty list — free anything added. }
    for I := 0 to AMembers.Count - 1 do
      AMembers.Get(I).Free();
    AMembers.Clear();
    raise;
  end;
end;

procedure ReadArchiveFile(const APath: string;
  AMembers: TList<TArchiveMember>);
begin
  ParseArchive(ReadWholeFile(APath), APath, AMembers);
end;

end.
