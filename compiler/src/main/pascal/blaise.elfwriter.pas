{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.elfwriter;

{ ELF relocatable-object writer for the internal assembler.

  Creates ET_REL (relocatable) ELF64 little-endian object files from
  scratch — the output format GNU `as` produces.  Scope: .text, .data,
  .rodata, .bss, .tbss sections; .symtab + .strtab; .rela.* relocation
  sections; .shstrtab.

  The API is append-oriented: callers select a section, append code/data
  bytes, define symbols at the current offset, and record relocations.
  Finish() serialises everything to a byte buffer suitable for writing
  to disk. }

interface

uses
  SysUtils, Generics.Collections, blaise.container.writer;

{ The writer's section/symbol/relocation vocabulary (TContainerSectionKind,
  TContainerSymBind, TContainerSymType, TContainerRelocKind, TContainerReloc)
  and the IContainerWriter contract live in blaise.container.writer — the
  container-agnostic seam this ELF writer implements. }

type
  EElfWriter = class(Exception);

  { TByteBuf (the amortized-growth byte buffer both container writers
    assemble their final images with) lives in blaise.container.writer. }

  { In-memory section: accumulates bytes (for non-BSS) and relocations.

    Byte storage is a capacity-doubled array (Bytes holds the backing
    store, Count the logical length) rather than a `string` grown with
    `Data := Data + ...`.  String concatenation reallocates and copies the
    whole buffer on every append, which is O(n^2): assembling the
    compiler's own ~2 MB .text one byte at a time that way needed tens of
    GB of peak memory and OOM-killed.  Amortized doubling makes appends
    O(1) and peak memory ~2x the section size.  An `array of Byte` (not a
    string) is also the natural shape for the future internal linker, which
    needs indexed byte access into section bodies. }
  TElfWriterSection = class
  public
    Kind:      TContainerSectionKind;
    Bytes:     array of Byte;  { backing store; capacity = Length(Bytes) }
    Count:     Integer;        { logical byte length (<= Length(Bytes)) }
    Size:      Integer;        { for BSS: logical size; for others: Count }
    Align:     Integer;        { section alignment (power of 2) }
    Relocs:    array of TContainerReloc;
    RelocCount: Integer;
    constructor Create(AKind: TContainerSectionKind);
    destructor Destroy; override;
    { Append one byte, growing the backing store geometrically. }
    procedure PushByte(AVal: Integer);
    { Materialise the section body as a string (used only at serialise
      time, once per section — not on the hot append path). }
    function AsString: string;
  end;

  { Symbol definition recorded before serialisation. }
  TElfWriterSym = class
  public
    Name:      string;
    Section:   TContainerSectionKind;
    Value:     Integer;
    Size:      Integer;
    Bind:      TContainerSymBind;
    SType:     TContainerSymType;
    IsExtern:  Boolean;
  end;

  { The main ELF object builder.  Implements the container-agnostic
    IContainerWriter seam (ARC-managed when held through the interface —
    do not mix with manual Free in that case). }
  TElfObjectWriter = class(TObject, IContainerWriter)
  private
    FSections: array of TElfWriterSection;
    FSymbols:  TList<TElfWriterSym>;
    FSymMap:   TDictionary<string, Integer>;

    function GetSection(AKind: TContainerSectionKind): TElfWriterSection;
    function SectionName(AKind: TContainerSectionKind): string;
  public
    constructor Create;
    destructor Destroy; override;

    { Switch to a section (creates on first use). }
    procedure SelectSection(AKind: TContainerSectionKind);

    { Append raw bytes to a section.  Returns the offset at which the
      bytes were placed. }
    function Append(AKind: TContainerSectionKind; const ABytes: string): Integer;
    { Append a single byte. }
    procedure AppendByte(AKind: TContainerSectionKind; AVal: Integer);
    { Append a 16-bit little-endian value. }
    procedure AppendWord(AKind: TContainerSectionKind; AVal: Integer);
    { Append a 32-bit little-endian value. }
    procedure AppendDWord(AKind: TContainerSectionKind; AVal: Integer);
    { Append a 64-bit little-endian value. }
    procedure AppendQWord(AKind: TContainerSectionKind; AVal: Int64);
    { Append N zero bytes. }
    procedure AppendZeros(AKind: TContainerSectionKind; ACount: Integer);
    { Pad the section to the next multiple of AAlign. }
    procedure AlignSection(AKind: TContainerSectionKind; AAlign: Integer);
    { Reserve ASize bytes in a BSS/TBSS section (no data emitted). }
    procedure ReserveBss(AKind: TContainerSectionKind; ASize: Integer);

    { Current write offset in a section. }
    function CurrentOffset(AKind: TContainerSectionKind): Integer;

    { Patch a 32-bit value at an existing offset in a section. }
    procedure Patch32(AKind: TContainerSectionKind; AOffset: Integer; AVal: Integer);

    { Define a symbol.  Returns the symbol index. }
    function DefineSymbol(const AName: string; ASection: TContainerSectionKind;
      AValue: Integer; ASize: Integer;
      ABind: TContainerSymBind; ASType: TContainerSymType): Integer;
    { Reference an external (undefined) symbol.  Returns the symbol index.
      Idempotent — returns existing index if already declared. }
    function ExternSymbol(const AName: string): Integer;
    { Look up a symbol by name.  Returns index or -1. }
    function FindSymbol(const AName: string): Integer;

    { Add a relocation to a section. }
    procedure AddReloc(ASection: TContainerSectionKind; AOffset: Integer;
      ASymIndex: Integer; ARType: TContainerRelocKind; AAddend: Int64);

    { Serialise the complete ELF object to a byte string. }
    function Finish: string;

    { Write the ELF object to a file. }
    procedure WriteToFile(const APath: string);
  end;

implementation

uses
  streams;

{ Bulk memory copy, used to materialise a section's byte array into a
  string in one O(n) pass at serialise time. }
procedure _ew_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

const
  ELFCLASS64  = 2;
  ELFDATA2LSB = 1;
  EV_CURRENT  = 1;
  ELFOSABI_NONE = 0;
  ET_REL      = 1;
  EM_X86_64   = 62;
  ELF64_EHDR_SIZE = 64;
  ELF64_SHDR_SIZE = 64;
  ELF64_SYM_SIZE  = 24;
  ELF64_RELA_SIZE = 24;

  SHT_NULL     = 0;
  SHT_PROGBITS = 1;
  SHT_SYMTAB   = 2;
  SHT_STRTAB   = 3;
  SHT_RELA     = 4;
  SHT_NOBITS   = 8;
  SHT_INIT_ARRAY = 14;

  SHF_WRITE     = $1;
  SHF_ALLOC     = $2;
  SHF_EXECINSTR = $4;
  SHF_TLS       = $400;

  STB_LOCAL  = 0;
  STB_GLOBAL = 1;
  STB_WEAK   = 2;

  STT_NOTYPE  = 0;
  STT_OBJECT  = 1;
  STT_FUNC    = 2;
  STT_SECTION = 3;
  STT_TLS     = 6;

  SHN_UNDEF  = 0;

  R_X86_64_NONE       = 0;
  R_X86_64_64         = 1;
  R_X86_64_PC32       = 2;
  R_X86_64_32         = 10;
  R_X86_64_32S        = 11;
  R_X86_64_TPOFF32    = 23;
  R_X86_64_GOTPCREL   = 9;
  R_X86_64_PLT32      = 4;
  R_X86_64_GOTPCRELX  = 41;
  R_X86_64_REX_GOTPCRELX = 42;

{ ---- TElfWriterSection ------------------------------------------------ }

constructor TElfWriterSection.Create(AKind: TContainerSectionKind);
begin
  inherited Create();
  Kind  := AKind;
  SetLength(Bytes, 0);
  Count := 0;
  Size  := 0;
  Align := 1;
  SetLength(Relocs, 0);
  RelocCount := 0;
end;

destructor TElfWriterSection.Destroy;
begin
  SetLength(Bytes, 0);
  SetLength(Relocs, 0);
  inherited Destroy();
end;

procedure TElfWriterSection.PushByte(AVal: Integer);
var
  NewCap: Integer;
begin
  if Count >= Length(Bytes) then
  begin
    { Geometric growth: amortised O(1) append, peak memory ~2x size. }
    NewCap := Length(Bytes) * 2;
    if NewCap < 64 then
      NewCap := 64;
    SetLength(Bytes, NewCap);
  end;
  Bytes[Count] := AVal and $FF;
  Count := Count + 1;
  Size := Count;
end;

function TElfWriterSection.AsString: string;
begin
  { Bulk byte-array -> string, done once per section at serialise time
    (NOT on the hot append path).  SetLength preallocates the string and
    memcpy fills it in one O(n) copy. }
  SetLength(Result, Count);
  if Count > 0 then
    _ew_memcpy(PChar(Result), @Bytes[0], Count);
end;

{ ---- Byte helpers ----------------------------------------------------- }

procedure PutU8(var ABuf: string; AVal: Integer);
begin
  ABuf := ABuf + Chr(AVal and $FF);
end;

procedure PutU16LE(var ABuf: string; AVal: Integer);
begin
  ABuf := ABuf + Chr(AVal and $FF) + Chr((AVal shr 8) and $FF);
end;

procedure PutU32LE(var ABuf: string; AVal: Integer);
begin
  ABuf := ABuf + Chr(AVal and $FF)
              + Chr((AVal shr 8) and $FF)
              + Chr((AVal shr 16) and $FF)
              + Chr((AVal shr 24) and $FF);
end;

procedure PutU64LE(var ABuf: string; AVal: Int64);
var
  Lo, Hi: Integer;
begin
  Lo := Integer(AVal and $FFFFFFFF);
  Hi := Integer((AVal shr 32) and $FFFFFFFF);
  PutU32LE(ABuf, Lo);
  PutU32LE(ABuf, Hi);
end;

procedure PatchU32LE(var ABuf: string; AOff: Integer; AVal: Integer);
var
  P: PChar;
begin
  P := PChar(ABuf);
  P[AOff]     := Chr(AVal and $FF);
  P[AOff + 1] := Chr((AVal shr 8) and $FF);
  P[AOff + 2] := Chr((AVal shr 16) and $FF);
  P[AOff + 3] := Chr((AVal shr 24) and $FF);
end;

function MakeZeros(ACount: Integer): string;
var
  I: Integer;
begin
  Result := '';
  I := 0;
  while I < ACount do
  begin
    Result := Result + Chr(0);
    I := I + 1;
  end;
end;

function ElfAlignUp(AVal: Integer; AAlign: Integer): Integer;
var
  Rem: Integer;
begin
  if AAlign <= 1 then
  begin
    Result := AVal;
    Exit;
  end;
  Rem := AVal mod AAlign;
  if Rem = 0 then
    Result := AVal
  else
    Result := AVal + (AAlign - Rem);
end;

function ElfAlignUp64(AVal: Int64; AAlign: Int64): Int64;
var
  Rem: Int64;
begin
  if AAlign <= 1 then
  begin
    Result := AVal;
    Exit;
  end;
  Rem := AVal mod AAlign;
  if Rem = 0 then
    Result := AVal
  else
    Result := AVal + (AAlign - Rem);
end;

{ ---- TElfObjectWriter ------------------------------------------------- }

constructor TElfObjectWriter.Create;
var
  I: Integer;
begin
  inherited Create();
  { sized from the enum (BUG-045): ELF never emits the Mach-O-only TLV
    kinds, but every ordinal must stay in bounds }
  SetLength(FSections, Ord(High(TContainerSectionKind)) + 1);
  for I := 0 to Ord(High(TContainerSectionKind)) do
    FSections[I] := nil;
  FSymbols  := TList<TElfWriterSym>.Create();
  FSymMap   := TDictionary<string, Integer>.Create();
end;

destructor TElfObjectWriter.Destroy;
var
  I: Integer;
begin
  for I := 0 to Length(FSections) - 1 do
  begin
    if FSections[I] <> nil then
      FSections[I].Free();
  end;
  SetLength(FSections, 0);
  if FSymbols <> nil then
  begin
    for I := 0 to FSymbols.Count - 1 do
      FSymbols.Get(I).Free();
  end;
  FSymbols.Free();
  FSymMap.Free();
  inherited Destroy();
end;

function TElfObjectWriter.SectionName(AKind: TContainerSectionKind): string;
begin
  case AKind of
    cskText:   Result := '.text';
    cskData:   Result := '.data';
    cskRodata: Result := '.rodata';
    cskBss:    Result := '.bss';
    cskTbss:   Result := '.tbss';
    cskTdata:  Result := '.tdata';
    cskTvars:  Result := '.tvars';   { never emitted for ELF — Mach-O only }
    cskOpdf:   Result := '.opdf';
    cskIface:  Result := '.blaise.iface';  { never emitted for ELF — the
                 post-hoc uElfObject embedding owns this section on ELF, so
                 cskIface is absent from SecOrder below, like cskTvars }
    cskInitArray: Result := '.init_array';
  else
    Result := '.text';
  end;
end;

function TElfObjectWriter.GetSection(AKind: TContainerSectionKind): TElfWriterSection;
var
  Idx: Integer;
begin
  Idx := Ord(AKind);
  if FSections[Idx] = nil then
    FSections[Idx] := TElfWriterSection.Create(AKind);
  Result := FSections[Idx];
end;

procedure TElfObjectWriter.SelectSection(AKind: TContainerSectionKind);
begin
  GetSection(AKind);
end;

function TElfObjectWriter.Append(AKind: TContainerSectionKind; const ABytes: string): Integer;
var
  Sec: TElfWriterSection;
  I: Integer;
begin
  Sec := GetSection(AKind);
  Result := Sec.Count;
  for I := 0 to Length(ABytes) - 1 do
    Sec.PushByte(Ord(ABytes[I]));
end;

procedure TElfObjectWriter.AppendByte(AKind: TContainerSectionKind; AVal: Integer);
begin
  GetSection(AKind).PushByte(AVal);
end;

procedure TElfObjectWriter.AppendWord(AKind: TContainerSectionKind; AVal: Integer);
var
  Sec: TElfWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.PushByte(AVal and $FF);
  Sec.PushByte((AVal shr 8) and $FF);
end;

procedure TElfObjectWriter.AppendDWord(AKind: TContainerSectionKind; AVal: Integer);
var
  Sec: TElfWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.PushByte(AVal and $FF);
  Sec.PushByte((AVal shr 8) and $FF);
  Sec.PushByte((AVal shr 16) and $FF);
  Sec.PushByte((AVal shr 24) and $FF);
end;

procedure TElfObjectWriter.AppendQWord(AKind: TContainerSectionKind; AVal: Int64);
var
  Sec: TElfWriterSection;
  I: Integer;
begin
  Sec := GetSection(AKind);
  for I := 0 to 7 do
    Sec.PushByte(Integer((AVal shr (I * 8)) and $FF));
end;

procedure TElfObjectWriter.AppendZeros(AKind: TContainerSectionKind; ACount: Integer);
var
  Sec: TElfWriterSection;
  I: Integer;
begin
  Sec := GetSection(AKind);
  for I := 1 to ACount do
    Sec.PushByte(0);
end;

procedure TElfObjectWriter.AlignSection(AKind: TContainerSectionKind; AAlign: Integer);
var
  Sec: TElfWriterSection;
  Pad, I: Integer;
begin
  Sec := GetSection(AKind);
  if AAlign > Sec.Align then
    Sec.Align := AAlign;
  if (AKind = cskBss) or (AKind = cskTbss) then
  begin
    Sec.Size := ElfAlignUp(Sec.Size, AAlign);
  end
  else
  begin
    Pad := ElfAlignUp(Sec.Count, AAlign) - Sec.Count;
    for I := 1 to Pad do
      Sec.PushByte(0);
  end;
end;

procedure TElfObjectWriter.ReserveBss(AKind: TContainerSectionKind; ASize: Integer);
var
  Sec: TElfWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.Size := Sec.Size + ASize;
end;

function TElfObjectWriter.CurrentOffset(AKind: TContainerSectionKind): Integer;
var
  Sec: TElfWriterSection;
begin
  Sec := GetSection(AKind);
  if (AKind = cskBss) or (AKind = cskTbss) then
    Result := Sec.Size
  else
    Result := Sec.Count;
end;

procedure TElfObjectWriter.Patch32(AKind: TContainerSectionKind; AOffset: Integer;
  AVal: Integer);
var
  Sec: TElfWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.Bytes[AOffset]     := AVal and $FF;
  Sec.Bytes[AOffset + 1] := (AVal shr 8) and $FF;
  Sec.Bytes[AOffset + 2] := (AVal shr 16) and $FF;
  Sec.Bytes[AOffset + 3] := (AVal shr 24) and $FF;
end;

function TElfObjectWriter.DefineSymbol(const AName: string;
  ASection: TContainerSectionKind; AValue: Integer; ASize: Integer;
  ABind: TContainerSymBind; ASType: TContainerSymType): Integer;
var
  Sym: TElfWriterSym;
  Existing: Integer;
begin
  if FSymMap.TryGetValue(AName, Existing) then
  begin
    Result := Existing;
    Exit;
  end;
  Sym := TElfWriterSym.Create();
  Sym.Name     := AName;
  Sym.Section  := ASection;
  Sym.Value    := AValue;
  Sym.Size     := ASize;
  Sym.Bind     := ABind;
  Sym.SType    := ASType;
  Sym.IsExtern := False;
  Result := FSymbols.Count;
  FSymbols.Add(Sym);
  FSymMap.Add(AName, Result);
end;

function TElfObjectWriter.ExternSymbol(const AName: string): Integer;
var
  Sym: TElfWriterSym;
  Existing: Integer;
begin
  if FSymMap.TryGetValue(AName, Existing) then
  begin
    Result := Existing;
    Exit;
  end;
  Sym := TElfWriterSym.Create();
  Sym.Name     := AName;
  Sym.Section  := cskText;
  Sym.Value    := 0;
  Sym.Size     := 0;
  Sym.Bind     := csbGlobal;
  Sym.SType    := cstNone;
  Sym.IsExtern := True;
  Result := FSymbols.Count;
  FSymbols.Add(Sym);
  FSymMap.Add(AName, Result);
end;

function TElfObjectWriter.FindSymbol(const AName: string): Integer;
var
  Val: Integer;
begin
  if FSymMap.TryGetValue(AName, Val) then
    Result := Val
  else
    Result := -1;
end;

procedure TElfObjectWriter.AddReloc(ASection: TContainerSectionKind; AOffset: Integer;
  ASymIndex: Integer; ARType: TContainerRelocKind; AAddend: Int64);
var
  Sec: TElfWriterSection;
  R: TContainerReloc;
begin
  Sec := GetSection(ASection);
  R.Offset   := AOffset;
  R.SymIndex := ASymIndex;
  R.RType    := ARType;
  R.Addend   := AAddend;
  if Sec.RelocCount = Length(Sec.Relocs) then
    SetLength(Sec.Relocs, Sec.RelocCount * 2 + 8);
  Sec.Relocs[Sec.RelocCount] := R;
  Sec.RelocCount := Sec.RelocCount + 1;
end;

{ ---- Finish: serialise to ELF bytes ---------------------------------- }

function RelocTypeToElf(ARType: TContainerRelocKind): Integer;
begin
  case ARType of
    crkNone:           Result := R_X86_64_NONE;
    crk64:             Result := R_X86_64_64;
    crk32:             Result := R_X86_64_32;
    crk32S:            Result := R_X86_64_32S;
    crkPC32:           Result := R_X86_64_PC32;
    crkPLT32:          Result := R_X86_64_PLT32;
    crkGOTPCREL:       Result := R_X86_64_GOTPCREL;
    crkTPOFF32:        Result := R_X86_64_TPOFF32;
    crkGOTPCRELX:      Result := R_X86_64_GOTPCRELX;
    crkREX_GOTPCRELX:  Result := R_X86_64_REX_GOTPCRELX;
  else
    Result := R_X86_64_NONE;
  end;
end;

function SymBindToElf(ABind: TContainerSymBind): Integer;
begin
  case ABind of
    csbLocal:  Result := STB_LOCAL;
    csbGlobal: Result := STB_GLOBAL;
    csbWeak:   Result := STB_WEAK;
  else
    Result := STB_LOCAL;
  end;
end;

function SymTypeToElf(ASType: TContainerSymType): Integer;
begin
  case ASType of
    cstNone:    Result := STT_NOTYPE;
    cstFunc:    Result := STT_FUNC;
    cstObject:  Result := STT_OBJECT;
    cstSection: Result := STT_SECTION;
    cstTLS:     Result := STT_TLS;
  else
    Result := STT_NOTYPE;
  end;
end;

function ElfAddStrtab(var ATab: string; const AStr: string): Integer;
begin
  if AStr = '' then
  begin
    Result := 0;
    Exit;
  end;
  Result := Length(ATab);
  ATab := ATab + AStr + Chr(0);
end;

procedure ElfEmitShdr(var ABuf: string; ANameIdx: Integer; AType: Integer;
  AFlags: Int64; AAddr: Int64; AOffset: Int64; ASize: Int64;
  ALink: Integer; AInfo: Integer; AAddrAlign: Int64; AEntSize: Int64);
begin
  PutU32LE(ABuf, ANameIdx);
  PutU32LE(ABuf, AType);
  PutU64LE(ABuf, AFlags);
  PutU64LE(ABuf, AAddr);
  PutU64LE(ABuf, AOffset);
  PutU64LE(ABuf, ASize);
  PutU32LE(ABuf, ALink);
  PutU32LE(ABuf, AInfo);
  PutU64LE(ABuf, AAddrAlign);
  PutU64LE(ABuf, AEntSize);
end;

procedure ElfEmitSym(var ABuf: string; ANameIdx: Integer; AInfo: Integer;
  AOther: Integer; AShndx: Integer; AValue: Int64; ASize: Int64);
begin
  PutU32LE(ABuf, ANameIdx);  { st_name }
  PutU8(ABuf, AInfo);        { st_info }
  PutU8(ABuf, AOther);       { st_other }
  PutU16LE(ABuf, AShndx);    { st_shndx }
  PutU64LE(ABuf, AValue);    { st_value }
  PutU64LE(ABuf, ASize);     { st_size }
end;

procedure ElfEmitRela(var ABuf: string; AOffset: Int64; ASymIdx: Integer;
  AType: Integer; AAddend: Int64);
var
  RInfo: Int64;
begin
  PutU64LE(ABuf, AOffset);
  RInfo := (Int64(ASymIdx) shl 32) or (Int64(AType) and $FFFFFFFF);
  PutU64LE(ABuf, RInfo);
  PutU64LE(ABuf, AAddend);
end;

{ TByteBuf-based variants used for the large, per-element-built tables
  (.strtab, .symtab, .rela.*) so building them is amortized O(1) per
  element instead of O(n^2) string concatenation. }

function ElfAddStrtabBB(ATab: TByteBuf; const AStr: string): Integer;
begin
  if AStr = '' then
  begin
    Result := 0;
    Exit;
  end;
  Result := ATab.Count;
  ATab.AppendBytes(AStr);
  ATab.PushByte(0);
end;

procedure ElfEmitSymBB(ABuf: TByteBuf; ANameIdx: Integer; AInfo: Integer;
  AOther: Integer; AShndx: Integer; AValue: Int64; ASize: Int64);
begin
  ABuf.PushU32(ANameIdx);   { st_name }
  ABuf.PushByte(AInfo);     { st_info }
  ABuf.PushByte(AOther);    { st_other }
  ABuf.PushU16(AShndx);     { st_shndx }
  ABuf.PushU64(AValue);     { st_value }
  ABuf.PushU64(ASize);      { st_size }
end;

procedure ElfEmitRelaBB(ABuf: TByteBuf; AOffset: Int64; ASymIdx: Integer;
  AType: Integer; AAddend: Int64);
var
  RInfo: Int64;
begin
  ABuf.PushU64(AOffset);
  RInfo := (Int64(ASymIdx) shl 32) or (Int64(AType) and $FFFFFFFF);
  ABuf.PushU64(RInfo);
  ABuf.PushU64(AAddend);
end;

function TElfObjectWriter.Finish: string;
const
  { Upper bound of the SecOrder emit list below.  This list is hand-maintained
    and position-indexed (SecOrder[I] maps a position to a kind), so it is NOT
    sized from the enum: TContainerSectionKind carries Mach-O-only kinds that
    ELF never emits.  Adding a kind that ELF *does* emit means extending the
    list AND this bound — otherwise the section is silently dropped from the
    object with no error. }
  MaxSecOrder = 6;

var
  Buf: string;
  { Section ordering: NULL, .text, .data, .rodata, .bss, .tbss, .opdf,
    .init_array, then .rela.text, .rela.data, .rela.rodata,
    then .symtab, .strtab, .shstrtab.
    We track which sections exist and their SHT indices. }
  SecOrder: array[0..MaxSecOrder] of TContainerSectionKind;
  SecPresent: array[0..MaxSecOrder] of Boolean;
  SecShtIdx: array[0..MaxSecOrder] of Integer;
  NumDataSecs: Integer;
  RelaShtIdx: array[0..MaxSecOrder] of Integer;
  NumRelaSecs: Integer;
  SymtabIdx, StrtabIdx, ShstrtabIdx, NoteIdx: Integer;
  TotalShNum: Integer;
  I, J, K: Integer;
  Sec: TElfWriterSection;
  Sym: TElfWriterSym;
  R: TContainerReloc;

  Strtab: TByteBuf;
  Shstrtab: TByteBuf;

  ShdrOff: Int64;
  CurOff: Int64;

  SecFileOff: array[0..MaxSecOrder] of Int64;
  RelaFileOff: array[0..MaxSecOrder] of Int64;
  SymtabFileOff, StrtabFileOff, ShstrtabFileOff, NoteFileOff: Int64;

  SymtabBuf: TByteBuf;
  FirstGlobal: Integer;
  SymSecIdx: Integer;
  StInfo: Integer;

  RelaBuf: array[0..MaxSecOrder] of TByteBuf;
  RelaCount: array[0..MaxSecOrder] of Integer;
  SymRemapIdx: array of Integer;
  LocalSymCount, GlobalSymCount: Integer;
  LocalSyms, GlobalSyms: TList<Integer>;
  OutBuf: TByteBuf;

  ShFlags: Int64;
  ShType: Integer;
  SecNameIdx: array[0..MaxSecOrder] of Integer;
  RelaNameIdx: array[0..MaxSecOrder] of Integer;
  SymtabNameIdx, StrtabNameIdx, ShstrtabNameIdx, NoteNameIdx: Integer;

begin
  SecOrder[0] := cskText;
  SecOrder[1] := cskData;
  SecOrder[2] := cskRodata;
  SecOrder[3] := cskBss;
  SecOrder[4] := cskTbss;
  SecOrder[5] := cskOpdf;
  SecOrder[6] := cskInitArray;

  NumDataSecs := 0;
  for I := 0 to MaxSecOrder do
  begin
    SecPresent[I] := FSections[Ord(SecOrder[I])] <> nil;
    if SecPresent[I] then
    begin
      SecShtIdx[I] := NumDataSecs + 1;
      NumDataSecs := NumDataSecs + 1;
    end
    else
      SecShtIdx[I] := 0;
  end;

  NumRelaSecs := 0;
  for I := 0 to MaxSecOrder do
  begin
    if SecPresent[I] and (GetSection(SecOrder[I]).RelocCount > 0) then
    begin
      RelaShtIdx[I] := NumDataSecs + NumRelaSecs + 1;
      NumRelaSecs := NumRelaSecs + 1;
    end
    else
      RelaShtIdx[I] := 0;
  end;

  { An empty .note.GNU-stack section marks the stack non-executable.
    Without it the kernel/linker default to an executable stack — a
    security regression relative to GNU as output. }
  NoteIdx      := NumDataSecs + NumRelaSecs + 1;
  SymtabIdx    := NoteIdx + 1;
  StrtabIdx    := SymtabIdx + 1;
  ShstrtabIdx  := StrtabIdx + 1;
  TotalShNum   := ShstrtabIdx + 1;

  { All large per-element-built tables use amortized TByteBuf, not string
    concatenation. }
  Strtab := TByteBuf.Create();
  Shstrtab := TByteBuf.Create();
  SymtabBuf := TByteBuf.Create();
  for I := 0 to MaxSecOrder do
    RelaBuf[I] := nil;
  LocalSyms := TList<Integer>.Create();
  GlobalSyms := TList<Integer>.Create();
  OutBuf := nil;
  try
    { Build .strtab — symbol name string table (starts with NUL byte) }
    Strtab.PushByte(0);

    { Build .shstrtab — section name string table }
    Shstrtab.PushByte(0);
    for I := 0 to MaxSecOrder do
    begin
      SecNameIdx[I] := 0;
      RelaNameIdx[I] := 0;
      if SecPresent[I] then
        SecNameIdx[I] := ElfAddStrtabBB(Shstrtab, SectionName(SecOrder[I]));
      if RelaShtIdx[I] > 0 then
        RelaNameIdx[I] := ElfAddStrtabBB(Shstrtab, '.rela' + SectionName(SecOrder[I]));
    end;
    NoteNameIdx     := ElfAddStrtabBB(Shstrtab, '.note.GNU-stack');
    SymtabNameIdx   := ElfAddStrtabBB(Shstrtab, '.symtab');
    StrtabNameIdx   := ElfAddStrtabBB(Shstrtab, '.strtab');
    ShstrtabNameIdx := ElfAddStrtabBB(Shstrtab, '.shstrtab');

    for I := 0 to FSymbols.Count - 1 do
    begin
      Sym := FSymbols.Get(I);
      if Sym.Bind = csbLocal then
        LocalSyms.Add(I)
      else
        GlobalSyms.Add(I);
    end;

    SetLength(SymRemapIdx, FSymbols.Count);
    { Remap: slot 0 is the NULL symbol; then locals, then globals }
    for I := 0 to LocalSyms.Count - 1 do
      SymRemapIdx[LocalSyms.Get(I)] := I + 1;
    for I := 0 to GlobalSyms.Count - 1 do
      SymRemapIdx[GlobalSyms.Get(I)] := LocalSyms.Count + I + 1;

    FirstGlobal := LocalSyms.Count + 1;

    { Serialise .symtab }
    { NULL symbol (entry 0) }
    ElfEmitSymBB(SymtabBuf, 0, 0, 0, SHN_UNDEF, 0, 0);
    { Locals first }
    for I := 0 to LocalSyms.Count - 1 do
    begin
      Sym := FSymbols.Get(LocalSyms.Get(I));
      if Sym.IsExtern then
        SymSecIdx := SHN_UNDEF
      else
      begin
        SymSecIdx := 0;
        for J := 0 to MaxSecOrder do
          if SecPresent[J] and (SecOrder[J] = Sym.Section) then
          begin
            SymSecIdx := SecShtIdx[J];
            break;
          end;
      end;
      StInfo := (SymBindToElf(Sym.Bind) shl 4) or SymTypeToElf(Sym.SType);
      ElfEmitSymBB(SymtabBuf, ElfAddStrtabBB(Strtab, Sym.Name), StInfo, 0,
              SymSecIdx, Int64(Sym.Value), Int64(Sym.Size));
    end;
    { Globals }
    for I := 0 to GlobalSyms.Count - 1 do
    begin
      Sym := FSymbols.Get(GlobalSyms.Get(I));
      if Sym.IsExtern then
        SymSecIdx := SHN_UNDEF
      else
      begin
        SymSecIdx := 0;
        for J := 0 to MaxSecOrder do
          if SecPresent[J] and (SecOrder[J] = Sym.Section) then
          begin
            SymSecIdx := SecShtIdx[J];
            break;
          end;
      end;
      StInfo := (SymBindToElf(Sym.Bind) shl 4) or SymTypeToElf(Sym.SType);
      ElfEmitSymBB(SymtabBuf, ElfAddStrtabBB(Strtab, Sym.Name), StInfo, 0,
              SymSecIdx, Int64(Sym.Value), Int64(Sym.Size));
    end;

    { Build .rela.* sections }
    for I := 0 to MaxSecOrder do
    begin
      RelaBuf[I] := TByteBuf.Create();
      RelaCount[I] := 0;
      if (not SecPresent[I]) or (RelaShtIdx[I] = 0) then Continue;
      Sec := GetSection(SecOrder[I]);
      for J := 0 to Sec.RelocCount - 1 do
      begin
        R := Sec.Relocs[J];
        ElfEmitRelaBB(RelaBuf[I], Int64(R.Offset),
                 SymRemapIdx[R.SymIndex],
                 RelocTypeToElf(R.RType), R.Addend);
        RelaCount[I] := RelaCount[I] + 1;
      end;
    end;

    { Now lay out the file.  ELF header first, then section contents in order,
      then the section header table at the end. }
    CurOff := Int64(ELF64_EHDR_SIZE);

    for I := 0 to MaxSecOrder do
    begin
      SecFileOff[I] := Int64(0);
      if not SecPresent[I] then Continue;
      Sec := GetSection(SecOrder[I]);
      if Sec.Align > 1 then
        CurOff := ElfAlignUp64(CurOff, Int64(Sec.Align));
      SecFileOff[I] := CurOff;
      if (SecOrder[I] <> cskBss) and (SecOrder[I] <> cskTbss) then
        CurOff := CurOff + Int64(Sec.Count);
    end;

    for I := 0 to MaxSecOrder do
    begin
      RelaFileOff[I] := Int64(0);
      if RelaShtIdx[I] = 0 then Continue;
      CurOff := ElfAlignUp64(CurOff, 8);
      RelaFileOff[I] := CurOff;
      CurOff := CurOff + Int64(RelaCount[I]) * ELF64_RELA_SIZE;
    end;

    NoteFileOff := CurOff;

    CurOff := ElfAlignUp64(CurOff, 8);
    SymtabFileOff := CurOff;
    CurOff := CurOff + Int64(SymtabBuf.Count);

    CurOff := ElfAlignUp64(CurOff, 1);
    StrtabFileOff := CurOff;
    CurOff := CurOff + Int64(Strtab.Count);

    CurOff := ElfAlignUp64(CurOff, 1);
    ShstrtabFileOff := CurOff;
    CurOff := CurOff + Int64(Shstrtab.Count);

    ShdrOff := ElfAlignUp64(CurOff, 8);

    { Assemble the final image into an amortized byte buffer.  Each fixed
      piece (ELF header, section-header table) is built into a small local
      string then bulk-copied in; section bodies and tables are bulk-copied;
      padding is a single PadTo per gap.  This avoids the O(n^2) per-byte
      `Buf := Buf + ...` growth that OOM-killed on the compiler's own
      object. }
    OutBuf := TByteBuf.Create();

    { ELF header (64 bytes) built locally then appended. }
    Buf := '';
    PutU8(Buf, $7F);
    PutU8(Buf, $45);  { E }
    PutU8(Buf, $4C);  { L }
    PutU8(Buf, $46);  { F }
    PutU8(Buf, ELFCLASS64);                      { class }
    PutU8(Buf, ELFDATA2LSB);                     { data }
    PutU8(Buf, EV_CURRENT);                      { version }
    PutU8(Buf, ELFOSABI_NONE);                   { OS/ABI }
    Buf := Buf + MakeZeros(8);                    { padding }
    PutU16LE(Buf, ET_REL);                       { e_type }
    PutU16LE(Buf, EM_X86_64);                    { e_machine }
    PutU32LE(Buf, EV_CURRENT);                   { e_version }
    PutU64LE(Buf, 0);                            { e_entry }
    PutU64LE(Buf, 0);                            { e_phoff }
    PutU64LE(Buf, ShdrOff);                      { e_shoff }
    PutU32LE(Buf, 0);                            { e_flags }
    PutU16LE(Buf, ELF64_EHDR_SIZE);              { e_ehsize }
    PutU16LE(Buf, 0);                            { e_phentsize }
    PutU16LE(Buf, 0);                            { e_phnum }
    PutU16LE(Buf, ELF64_SHDR_SIZE);              { e_shentsize }
    PutU16LE(Buf, TotalShNum);                   { e_shnum }
    PutU16LE(Buf, ShstrtabIdx);                  { e_shstrndx }
    OutBuf.AppendBytes(Buf);

    { Emit section data bodies }
    for I := 0 to MaxSecOrder do
    begin
      if not SecPresent[I] then Continue;
      Sec := GetSection(SecOrder[I]);
      if (SecOrder[I] = cskBss) or (SecOrder[I] = cskTbss) then Continue;
      OutBuf.PadTo(Integer(SecFileOff[I]));
      OutBuf.AppendBytes(Sec.AsString());
    end;

    { Emit .rela.* bodies }
    for I := 0 to MaxSecOrder do
    begin
      if RelaShtIdx[I] = 0 then Continue;
      OutBuf.PadTo(Integer(RelaFileOff[I]));
      OutBuf.AppendBuf(RelaBuf[I]);
    end;

    { Emit .symtab }
    OutBuf.PadTo(Integer(SymtabFileOff));
    OutBuf.AppendBuf(SymtabBuf);

    { Emit .strtab }
    OutBuf.PadTo(Integer(StrtabFileOff));
    OutBuf.AppendBuf(Strtab);

    { Emit .shstrtab }
    OutBuf.PadTo(Integer(ShstrtabFileOff));
    OutBuf.AppendBuf(Shstrtab);

    { Pad to section header table }
    OutBuf.PadTo(Integer(ShdrOff));

    { Section header table — built into a local string then appended. }
    Buf := '';
    { Entry 0: NULL }
    ElfEmitShdr(Buf, 0, SHT_NULL, 0, 0, 0, 0, 0, 0, 0, 0);

    { Data sections }
    for I := 0 to MaxSecOrder do
    begin
      if not SecPresent[I] then Continue;
      Sec := GetSection(SecOrder[I]);
      case SecOrder[I] of
        cskText:
        begin
          ShFlags := SHF_ALLOC or SHF_EXECINSTR;
          ShType  := SHT_PROGBITS;
        end;
        cskData:
        begin
          ShFlags := SHF_ALLOC or SHF_WRITE;
          ShType  := SHT_PROGBITS;
        end;
        cskRodata:
        begin
          ShFlags := SHF_ALLOC;
          ShType  := SHT_PROGBITS;
        end;
        cskBss:
        begin
          ShFlags := SHF_ALLOC or SHF_WRITE;
          ShType  := SHT_NOBITS;
        end;
        cskTbss:
        begin
          ShFlags := SHF_ALLOC or SHF_WRITE or SHF_TLS;
          ShType  := SHT_NOBITS;
        end;
        cskOpdf:
        begin
          { OPDF debug section: alloc+write progbits, matching GNU as output
            for `.section .opdf, "aw", @progbits`.  SHF_ALLOC makes it ride
            into the loadable image so the debugger finds it by name. }
          ShFlags := SHF_ALLOC or SHF_WRITE;
          ShType  := SHT_PROGBITS;
        end;
        cskInitArray:
        begin
          { .init_array: an array of load-time constructor pointers the dynamic
            loader runs (DT_INIT_ARRAY).  SHT_INIT_ARRAY rather than PROGBITS —
            the linker recognises the type, not the name, when building the
            DT_INIT_ARRAY entry.  Writable: the entries are relocated. }
          ShFlags := SHF_ALLOC or SHF_WRITE;
          ShType  := SHT_INIT_ARRAY;
        end;
      else
        { cskTdata / cskTvars / cskIface are Mach-O-only section kinds and
          never reach the ELF writer.  Without this arm they would inherit the
          PREVIOUS iteration's ShFlags/ShType (neither is reset per loop) and
          silently emit a malformed section header.  Fail loudly instead. }
        raise Exception.Create(
          'ELF writer: unsupported section kind ' + IntToStr(Ord(SecOrder[I])));
      end;
      ElfEmitShdr(Buf, SecNameIdx[I], ShType, ShFlags, 0,
               SecFileOff[I], Int64(Sec.Size), 0, 0,
               Int64(Sec.Align), 0);
    end;

    { .rela.* sections }
    for I := 0 to MaxSecOrder do
    begin
      if RelaShtIdx[I] = 0 then Continue;
      ElfEmitShdr(Buf, RelaNameIdx[I], SHT_RELA,
               0, 0, RelaFileOff[I],
               Int64(RelaCount[I]) * ELF64_RELA_SIZE,
               SymtabIdx,     { sh_link -> .symtab }
               SecShtIdx[I],  { sh_info -> target section }
               8, ELF64_RELA_SIZE);
    end;

    { .note.GNU-stack — empty, type PROGBITS, no flags (=> RW stack) }
    ElfEmitShdr(Buf, NoteNameIdx, SHT_PROGBITS, 0, 0,
             NoteFileOff, 0, 0, 0, 1, 0);

    { .symtab }
    ElfEmitShdr(Buf, SymtabNameIdx, SHT_SYMTAB, 0, 0,
             SymtabFileOff, Int64(SymtabBuf.Count),
             StrtabIdx,     { sh_link -> .strtab }
             FirstGlobal,   { sh_info = index of first global sym }
             8, ELF64_SYM_SIZE);

    { .strtab }
    ElfEmitShdr(Buf, StrtabNameIdx, SHT_STRTAB, 0, 0,
             StrtabFileOff, Int64(Strtab.Count),
             0, 0, 1, 0);

    { .shstrtab }
    ElfEmitShdr(Buf, ShstrtabNameIdx, SHT_STRTAB, 0, 0,
             ShstrtabFileOff, Int64(Shstrtab.Count),
             0, 0, 1, 0);

    { Append the section-header table and materialise the final image. }
    OutBuf.AppendBytes(Buf);
    Result := OutBuf.AsString();
  finally
    OutBuf.Free();
    Strtab.Free();
    Shstrtab.Free();
    SymtabBuf.Free();
    { RelaBuf elements are ARC-owned: the scope-exit walk releases each
      element of the static-array local (BUG-016), so no manual per-element
      Free here — that would be the second decrement of the same reference.
      (A[I].Free() nils the slot since the BUG-016 groundwork, so a manual
      loop would be a safe no-op for the walk — but redundant.) }
    LocalSyms.Free();
    GlobalSyms.Free();
  end;
end;

procedure TElfObjectWriter.WriteToFile(const APath: string);
var
  FOut: TFileOutputStream;
  Buf: string;
begin
  Buf := Self.Finish();
  FOut := TFileOutputStream.Create(APath);
  try
    FOut.Write(PChar(Buf), Length(Buf));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;
end;

end.
