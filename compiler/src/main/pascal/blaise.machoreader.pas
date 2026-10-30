{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.machoreader;

{ Mach-O 64-bit reader — the Mach-O sibling of blaise.elfreader.

  Parses MH_OBJECT and MH_EXECUTE little-endian images: the header,
  every load command (kept as raw (cmd, offset, size) triples so callers
  can assert on commands this reader does not model), LC_SEGMENT_64
  segments with their section_64 entries, per-section relocation_info
  records, and the LC_SYMTAB nlist_64 symbol + string tables.

  Used by the structural test lane (Linux CI parses back what
  blaise.machowriter emitted — no Mac needed) and, later, by the
  macos-arm64 link path. }

interface

uses
  SysUtils, Generics.Collections;

type
  EMachOReader = class(Exception);

  TMoReloc = class
  public
    Address:   Int;   { r_address — offset within the section }
    SymbolNum: Int;   { r_symbolnum (24-bit) }
    PcRel:     Boolean;
    Length_:   Int;   { r_length: 0=1,1=2,2=4,3=8 bytes }
    IsExtern:  Boolean;
    RType:     Int;   { ARM64_RELOC_* }
  end;

  TMoSection = class
  public
    SegName:  string;
    SectName: string;
    Addr:     Int64;
    Size:     Int64;
    Offset:   Int;
    Align:    Int;    { log2 }
    Flags:    Int;
    Relocs:   TList<TMoReloc>;
    Data:     string;     { file-backed bytes ('' for zerofill) }
    constructor Create;
    destructor Destroy; override;
  end;

  TMoSymbol = class
  public
    Name:  string;
    NType: Int;
    Sect:  Int;       { 1-based section ordinal; 0 = NO_SECT }
    Desc:  Int;
    Value: Int64;
    function IsExt: Boolean;
    function IsUndef: Boolean;
  end;

  TMoSegment = class
  public
    Name:     string;
    VmAddr:   Int64;
    VmSize:   Int64;
    FileOff:  Int64;
    FileSize: Int64;
    MaxProt:  Int;
    InitProt: Int;
    NSects:   Int;
  end;

  { A raw load command: enough to assert presence/shape of commands the
    reader does not model structurally (LC_MAIN, LC_LOAD_DYLIB, ...). }
  TMoLoadCmd = class
  public
    Cmd:     Int;
    CmdSize: Int;
    Offset:  Int;     { file offset of the command header }
  end;

  TMachOFile = class
  public
    SourceName: string;
    CpuType:    Int;
    CpuSubtype: Int;
    FileType:   Int;
    Flags:      Int;
    LoadCmds:   TList<TMoLoadCmd>;
    Segments:   TList<TMoSegment>;
    Sections:   TList<TMoSection>;   { across all segments, in file order }
    Symbols:    TList<TMoSymbol>;
    { LC_DYSYMTAB ranges (all -1 when the command is absent). }
    ILocalSym, NLocalSym: Int;
    IExtDefSym, NExtDefSym: Int;
    IUndefSym, NUndefSym: Int;
    Raw: string;                      { the whole image }
    constructor Create;
    destructor Destroy; override;
    function FindSection(const ASegName, ASectName: string): TMoSection;
    function FindSegment(const AName: string): TMoSegment;
    function FindLoadCmd(ACmd: Int): TMoLoadCmd;
    function FindSymbol(const AName: string): TMoSymbol;
  end;

{ Parse a Mach-O 64-bit image from an in-memory byte buffer.  Raises
  EMachOReader on malformed input.  Caller frees. }
function ParseMachO(const ABytes: string; const ASourceName: string): TMachOFile;

implementation

uses
  uStrCompat, blaise.machowriter;

function RdU16(const ABuf: string; AOff: Int): Int32;
begin
  Result := StrAt(ABuf, AOff) or (StrAt(ABuf, AOff + 1) shl 8);
end;

function RdU32(const ABuf: string; AOff: Int): Int32;
begin
  Result := StrAt(ABuf, AOff)
         or (StrAt(ABuf, AOff + 1) shl 8)
         or (StrAt(ABuf, AOff + 2) shl 16)
         or (StrAt(ABuf, AOff + 3) shl 24);
end;

function RdU64(const ABuf: string; AOff: Int): Int64;
var
  Lo, Hi: Int64;
begin
  Lo := Int64(RdU32(ABuf, AOff)) and $FFFFFFFF;
  Hi := Int64(RdU32(ABuf, AOff + 4)) and $FFFFFFFF;
  Result := Lo or (Hi shl 32);
end;

{ Fixed 16-byte NUL-padded name field. }
function RdName16(const ABuf: string; AOff: Int): string;
var
  I, C: Int;
begin
  Result := '';
  for I := 0 to 15 do
  begin
    C := StrAt(ABuf, AOff + I);
    if C = 0 then Break;
    Result := Result + Chr(C);
  end;
end;

function RdStrZ(const ABuf: string; AOff: Int): string;
var
  P, C: Int;
begin
  Result := '';
  P := AOff;
  while P < Length(ABuf) do
  begin
    C := StrAt(ABuf, P);
    if C = 0 then Break;
    Result := Result + Chr(C);
    P := P + 1;
  end;
end;

{ ---- TMoSection / TMachOFile ------------------------------------------ }

constructor TMoSection.Create;
begin
  inherited Create();
  Relocs := TList<TMoReloc>.Create();
end;

destructor TMoSection.Destroy;
var
  I: Int;
begin
  for I := 0 to Relocs.Count - 1 do
    Relocs.Get(I).Free();
  Relocs.Free();
  inherited Destroy();
end;

function TMoSymbol.IsExt: Boolean;
begin
  Result := (NType and N_EXT) <> 0;
end;

function TMoSymbol.IsUndef: Boolean;
begin
  Result := ((NType and $0E) = N_UNDF) and (Sect = 0);
end;

constructor TMachOFile.Create;
begin
  inherited Create();
  LoadCmds := TList<TMoLoadCmd>.Create();
  Segments := TList<TMoSegment>.Create();
  Sections := TList<TMoSection>.Create();
  Symbols  := TList<TMoSymbol>.Create();
  ILocalSym := -1; NLocalSym := -1;
  IExtDefSym := -1; NExtDefSym := -1;
  IUndefSym := -1; NUndefSym := -1;
end;

destructor TMachOFile.Destroy;
var
  I: Int;
begin
  for I := 0 to LoadCmds.Count - 1 do
    LoadCmds.Get(I).Free();
  LoadCmds.Free();
  for I := 0 to Segments.Count - 1 do
    Segments.Get(I).Free();
  Segments.Free();
  for I := 0 to Sections.Count - 1 do
    Sections.Get(I).Free();
  Sections.Free();
  for I := 0 to Symbols.Count - 1 do
    Symbols.Get(I).Free();
  Symbols.Free();
  inherited Destroy();
end;

function TMachOFile.FindSection(const ASegName, ASectName: string): TMoSection;
var
  I: Int;
begin
  for I := 0 to Sections.Count - 1 do
  begin
    if (Sections.Get(I).SegName = ASegName) and
       (Sections.Get(I).SectName = ASectName) then
    begin
      Result := Sections.Get(I);
      Exit;
    end;
  end;
  Result := nil;
end;

function TMachOFile.FindSegment(const AName: string): TMoSegment;
var
  I: Int;
begin
  for I := 0 to Segments.Count - 1 do
  begin
    if Segments.Get(I).Name = AName then
    begin
      Result := Segments.Get(I);
      Exit;
    end;
  end;
  Result := nil;
end;

function TMachOFile.FindLoadCmd(ACmd: Int): TMoLoadCmd;
var
  I: Int;
begin
  for I := 0 to LoadCmds.Count - 1 do
  begin
    if LoadCmds.Get(I).Cmd = ACmd then
    begin
      Result := LoadCmds.Get(I);
      Exit;
    end;
  end;
  Result := nil;
end;

function TMachOFile.FindSymbol(const AName: string): TMoSymbol;
var
  I: Int;
begin
  for I := 0 to Symbols.Count - 1 do
  begin
    if Symbols.Get(I).Name = AName then
    begin
      Result := Symbols.Get(I);
      Exit;
    end;
  end;
  Result := nil;
end;

{ ---- parser ------------------------------------------------------------ }

function ParseMachO(const ABytes: string; const ASourceName: string): TMachOFile;
var
  F: TMachOFile;
  NCmds, SizeOfCmds: Int;
  Off: Int;
  Cmd, CmdSize: Int;
  LC: TMoLoadCmd;
  Seg: TMoSegment;
  Sec: TMoSection;
  Rel: TMoReloc;
  Sym: TMoSymbol;
  I, J, NSects: Int;
  SecOff: Int;
  RelOff, NReloc, W: Int;
  SymOff, NSyms, StrOff: Int;
begin
  if Length(ABytes) < 32 then
    raise EMachOReader.Create(ASourceName + ': too small for a Mach-O header');
  if RdU32(ABytes, 0) <> MH_MAGIC_64 then
    raise EMachOReader.Create(ASourceName + ': not a 64-bit LE Mach-O image');

  F := TMachOFile.Create();
  F.SourceName := ASourceName;
  F.Raw := ABytes;
  F.CpuType    := RdU32(ABytes, 4);
  F.CpuSubtype := RdU32(ABytes, 8);
  F.FileType   := RdU32(ABytes, 12);
  NCmds        := RdU32(ABytes, 16);
  SizeOfCmds   := RdU32(ABytes, 20);
  F.Flags      := RdU32(ABytes, 24);

  if 32 + SizeOfCmds > Length(ABytes) then
  begin
    F.Free();
    raise EMachOReader.Create(ASourceName + ': load commands overrun the file');
  end;

  Off := 32;
  for I := 0 to NCmds - 1 do
  begin
    Cmd := RdU32(ABytes, Off);
    CmdSize := RdU32(ABytes, Off + 4);
    if CmdSize < 8 then
    begin
      F.Free();
      raise EMachOReader.Create(ASourceName + ': malformed load command size');
    end;
    LC := TMoLoadCmd.Create();
    LC.Cmd := Cmd;
    LC.CmdSize := CmdSize;
    LC.Offset := Off;
    F.LoadCmds.Add(LC);

    if Cmd = LC_SEGMENT_64 then
    begin
      Seg := TMoSegment.Create();
      Seg.Name     := RdName16(ABytes, Off + 8);
      Seg.VmAddr   := RdU64(ABytes, Off + 24);
      Seg.VmSize   := RdU64(ABytes, Off + 32);
      Seg.FileOff  := RdU64(ABytes, Off + 40);
      Seg.FileSize := RdU64(ABytes, Off + 48);
      Seg.MaxProt  := RdU32(ABytes, Off + 56);
      Seg.InitProt := RdU32(ABytes, Off + 60);
      NSects       := RdU32(ABytes, Off + 64);
      Seg.NSects   := NSects;
      F.Segments.Add(Seg);

      SecOff := Off + 72;
      for J := 0 to NSects - 1 do
      begin
        Sec := TMoSection.Create();
        Sec.SectName := RdName16(ABytes, SecOff);
        Sec.SegName  := RdName16(ABytes, SecOff + 16);
        Sec.Addr     := RdU64(ABytes, SecOff + 32);
        Sec.Size     := RdU64(ABytes, SecOff + 40);
        Sec.Offset   := RdU32(ABytes, SecOff + 48);
        Sec.Align    := RdU32(ABytes, SecOff + 52);
        RelOff       := RdU32(ABytes, SecOff + 56);
        NReloc       := RdU32(ABytes, SecOff + 60);
        Sec.Flags    := RdU32(ABytes, SecOff + 64);
        if (Sec.Offset > 0) and (Sec.Size > 0) and
           (Sec.Offset + Sec.Size <= Length(ABytes)) then
          Sec.Data := Copy(ABytes, Sec.Offset, Int32(Sec.Size))
        else
          Sec.Data := '';
        while NReloc > 0 do
        begin
          Rel := TMoReloc.Create();
          Rel.Address := RdU32(ABytes, RelOff);
          W := RdU32(ABytes, RelOff + 4);
          Rel.SymbolNum := W and $FFFFFF;
          Rel.PcRel     := ((W shr 24) and 1) <> 0;
          Rel.Length_   := (W shr 25) and 3;
          Rel.IsExtern  := ((W shr 27) and 1) <> 0;
          Rel.RType     := (W shr 28) and $F;
          Sec.Relocs.Add(Rel);
          RelOff := RelOff + 8;
          NReloc := NReloc - 1;
        end;
        F.Sections.Add(Sec);
        SecOff := SecOff + 80;
      end;
    end
    else if Cmd = LC_SYMTAB then
    begin
      SymOff := RdU32(ABytes, Off + 8);
      NSyms  := RdU32(ABytes, Off + 12);
      StrOff := RdU32(ABytes, Off + 16);
      for J := 0 to NSyms - 1 do
      begin
        Sym := TMoSymbol.Create();
        Sym.Name  := RdStrZ(ABytes, StrOff + RdU32(ABytes, SymOff + J * 16));
        Sym.NType := StrAt(ABytes, SymOff + J * 16 + 4);
        Sym.Sect  := StrAt(ABytes, SymOff + J * 16 + 5);
        Sym.Desc  := RdU16(ABytes, SymOff + J * 16 + 6);
        Sym.Value := RdU64(ABytes, SymOff + J * 16 + 8);
        F.Symbols.Add(Sym);
      end;
    end
    else if Cmd = LC_DYSYMTAB then
    begin
      F.ILocalSym  := RdU32(ABytes, Off + 8);
      F.NLocalSym  := RdU32(ABytes, Off + 12);
      F.IExtDefSym := RdU32(ABytes, Off + 16);
      F.NExtDefSym := RdU32(ABytes, Off + 20);
      F.IUndefSym  := RdU32(ABytes, Off + 24);
      F.NUndefSym  := RdU32(ABytes, Off + 28);
    end;

    Off := Off + CmdSize;
  end;

  Result := F;
end;

end.
