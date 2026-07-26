{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.machowriter;

{ Mach-O relocatable-object writer for the internal AArch64 assembler —
  the Mach-O sibling of blaise.elfwriter behind the IContainerWriter
  Bridge (docs/macos-arm64-backend-design.adoc, Phase 1).

  Creates MH_OBJECT (relocatable) Mach-O 64-bit little-endian arm64
  object files from scratch — the output format `clang -c` produces on
  Apple Silicon.  Shape:

    mach_header_64
    LC_SEGMENT_64 (one, unnamed) holding every section_64
    LC_BUILD_VERSION (platform macOS, minos 11.0)
    LC_SYMTAB   (nlist_64 entries + string table)
    LC_DYSYMTAB (local / externally-defined / undefined index ranges)
    section data, per-section relocation_info arrays, symtab, strtab

  Section mapping from the container vocabulary:

    cskText   -> (__TEXT,__text)   S_REGULAR + PURE/SOME_INSTRUCTIONS
    cskRodata -> (__TEXT,__const)  S_REGULAR
    cskData   -> (__DATA,__data)   S_REGULAR
    cskOpdf   -> (__OPDF,__opdf)   S_REGULAR (OPDF debug payload)
    cskBss    -> (__DATA,__bss)          S_ZEROFILL
    cskTbss   -> (__DATA,__thread_bss)   S_THREAD_LOCAL_ZEROFILL

  Zerofill sections are laid out LAST in the segment (a Mach-O rule).
  Symbols are serialised locals -> externally-defined -> undefined (the
  order LC_DYSYMTAB requires); relocation records are remapped to the
  reordered symbol indices.

  Relocations use the AArch64 crkArm64* container kinds only (they are
  architecture facts — the x86-64 crk* kinds are rejected).  Mach-O
  relocation_info has no addend field: an ARM64_RELOC_ADDEND pseudo-
  relocation precedes BRANCH26/PAGE21/PAGEOFF12 records that carry one,
  and an UNSIGNED addend is added into the section bytes themselves.
  GOT/TLV kinds must be addend-free (rejected otherwise). }

interface

uses
  SysUtils, Generics.Collections, blaise.container.writer;

type
  EMachOWriter = class(Exception);

  { In-memory section: same amortized-growth backing store as the ELF
    writer's section (see blaise.elfwriter for the O(n^2) rationale). }
  TMachOWriterSection = class
  public
    Kind:       TContainerSectionKind;
    Bytes:      array of Byte;
    Count:      Integer;
    Size:       Integer;       { for zerofill: logical size; else Count }
    Align:      Integer;       { section alignment (power of 2) }
    Relocs:     array of TContainerReloc;
    RelocCount: Integer;
    constructor Create(AKind: TContainerSectionKind);
    destructor Destroy; override;
    procedure PushByte(AVal: Integer);
    function AsString: string;
  end;

  { Symbol definition recorded before serialisation. }
  TMachOWriterSym = class
  public
    Name:      string;
    Section:   TContainerSectionKind;
    Value:     Integer;
    Size:      Integer;
    Bind:      TContainerSymBind;
    SType:     TContainerSymType;
    IsExtern:  Boolean;
  end;

  { The MH_OBJECT builder.  Implements the container-agnostic
    IContainerWriter seam (ARC-managed when held through the interface —
    do not mix with manual Free in that case). }
  TMachOObjectWriter = class(TObject, IContainerWriter)
  private
    FSections: array of TMachOWriterSection;
    FSymbols:  TList<TMachOWriterSym>;
    FSymMap:   TDictionary<string, Integer>;

    function GetSection(AKind: TContainerSectionKind): TMachOWriterSection;
  public
    constructor Create;
    destructor Destroy; override;

    procedure SelectSection(AKind: TContainerSectionKind);
    function Append(AKind: TContainerSectionKind; const ABytes: string): Integer;
    procedure AppendByte(AKind: TContainerSectionKind; AVal: Integer);
    procedure AppendWord(AKind: TContainerSectionKind; AVal: Integer);
    procedure AppendDWord(AKind: TContainerSectionKind; AVal: Integer);
    procedure AppendQWord(AKind: TContainerSectionKind; AVal: Int64);
    procedure AppendZeros(AKind: TContainerSectionKind; ACount: Integer);
    procedure AlignSection(AKind: TContainerSectionKind; AAlign: Integer);
    procedure ReserveBss(AKind: TContainerSectionKind; ASize: Integer);
    function CurrentOffset(AKind: TContainerSectionKind): Integer;
    procedure Patch32(AKind: TContainerSectionKind; AOffset: Integer;
      AVal: Integer);
    function DefineSymbol(const AName: string; ASection: TContainerSectionKind;
      AValue: Integer; ASize: Integer;
      ABind: TContainerSymBind; ASType: TContainerSymType): Integer;
    function ExternSymbol(const AName: string): Integer;
    function FindSymbol(const AName: string): Integer;
    procedure AddReloc(ASection: TContainerSectionKind; AOffset: Integer;
      ASymIndex: Integer; ARType: TContainerRelocKind; AAddend: Int64);
    function Finish: string;
    procedure WriteToFile(const APath: string);
  end;

  { MH_EXECUTE emitter — the executable side of the container (Phase 1B).

    The linker core resolves every address; this writer serialises the
    resolved image: __PAGEZERO (4 GiB NULL trap), __TEXT at 0x100000000
    holding the header + load commands + code + rodata, __DATA (data +
    zerofill bss), and __LINKEDIT holding the legacy LC_DYLD_INFO_ONLY
    rebase/bind opcode streams and the LC_SYMTAB tables.  Segments are
    16 KiB-aligned (arm64 macOS page size).  Entry is LC_MAIN (entryoff =
    file offset of the entry code inside __TEXT); the dynamic loader is
    /usr/lib/dyld and the single v1 dylib is libSystem.B.dylib.

    Rebases/binds use the LEGACY dyld-info opcodes (simpler than chained
    fixups; accepted by current dyld for MH_EXECUTE — migrating to
    LC_DYLD_CHAINED_FIXUPS is a Phase 6 decision).  LC_CODE_SIGNATURE is
    Phase 4; its absence makes the binary structurally complete but not
    yet runnable on Apple Silicon. }
  { Resolved virtual addresses of every payload the exec image carries.
    Derived purely from the CURRENT payload sizes, so the linker can set
    its merged (still unfixed) section bytes, read the layout, apply the
    relocation fixups against these final addresses, and re-set the
    patched bytes — Finish recomputes the identical layout. }
  TMachOExecLayout = record
    TextVm:  Int64;   { __TEXT,__text }
    ConstVm: Int64;   { __TEXT,__const }
    DataVm:  Int64;   { __DATA,__data }
    TvarsVm: Int64;   { __DATA,__thread_vars (TLV descriptors) }
    TdataVm: Int64;   { __DATA,__thread_data (TLV initial image) }
    TbssVm:  Int64;   { __DATA,__thread_bss (zerofill, follows tdata so
                        the TLV content region tdata..tbss is contiguous) }
    BssVm:   Int64;   { __DATA,__bss }
  end;

  TMachOExecWriter = class
  private
    FText:      string;   { __TEXT,__text bytes }
    FConst:     string;   { __TEXT,__const bytes }
    FData:      string;   { __DATA,__data bytes }
    FTvars:     string;   { __DATA,__thread_vars bytes }
    FTdata:     string;   { __DATA,__thread_data bytes }
    FTbssSize:  Int64;    { __DATA,__thread_bss zerofill size }
    FBssSize:   Int64;    { __DATA,__bss zerofill size }
    FEntryTextOff: Integer;      { entry offset within __text }
    FRebases:   TList<Int64>;    { vm addresses needing slide }
    FBindAddrs: TList<Int64>;    { vm addresses of dylib-bound pointers }
    FBindNames: TList<string>;   { parallel: bound symbol names }
    FGlobalNames: TList<string>; { exported/global symbols }
    FGlobalAddrs: TList<Int64>;
    FIdent: string;              { CodeDirectory identifier }
  public
    constructor Create;
    destructor Destroy; override;
    procedure SetText(const ABytes: string);
    procedure SetConst(const ABytes: string);
    procedure SetData(const ABytes: string);
    procedure SetTvars(const ABytes: string);
    procedure SetTdata(const ABytes: string);
    procedure SetTbssSize(ASize: Int64);
    procedure SetBssSize(ASize: Int64);
    { Entry point, as an offset into the __text payload. }
    procedure SetEntryTextOffset(AOff: Integer);
    { CodeDirectory identifier (conventionally the binary's name). }
    procedure SetIdentifier(const AName: string);
    { Record a pointer slot at AVmAddr that dyld must slide (rebase). }
    procedure AddRebase(AVmAddr: Int64);
    { Record a pointer slot at AVmAddr bound to libSystem symbol AName. }
    procedure AddBind(AVmAddr: Int64; const AName: string);
    { Record a defined global for the symbol table. }
    procedure AddGlobal(const AName: string; AVmAddr: Int64);
    { Virtual address the __text payload starts at (fixed for the v1
      load-command configuration, so callers can resolve before Finish). }
    function TextVmAddr: Int64;
    { Full payload layout for the CURRENT sizes — Finish uses the same
      computation, so addresses read here are final. }
    function ComputeLayout: TMachOExecLayout;
    function Finish: string;
  end;

const
  { Executable layout knobs (arm64 macOS). }
  MACHO_PAGEZERO_SIZE = $100000000;   { 4 GiB }
  MACHO_EXEC_BASE     = $100000000;   { __TEXT vmaddr }
  MACHO_PAGE_SIZE     = $4000;        { 16 KiB pages }

  MH_PIE       = $200000;
  MH_NOUNDEFS  = $1;
  MH_DYLDLINK  = $4;
  MH_TWOLEVEL  = $80;

  LC_LOAD_DYLIB      = $0C;
  LC_LOAD_DYLINKER   = $0E;
  { $22/$28 or LC_REQ_DYLD ($80000000) — precomputed literals }
  LC_DYLD_INFO_ONLY  = Integer($80000022);
  LC_MAIN            = Integer($80000028);
  LC_UNIXTHREAD      = $05;

  { legacy dyld-info opcodes }
  REBASE_TYPE_POINTER                        = 1;
  REBASE_OPCODE_SET_TYPE_IMM                 = $10;
  REBASE_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB  = $20;
  REBASE_OPCODE_DO_REBASE_IMM_TIMES          = $50;
  REBASE_OPCODE_DONE                         = $00;
  BIND_TYPE_POINTER                          = 1;
  BIND_OPCODE_SET_DYLIB_ORDINAL_IMM          = $10;
  BIND_OPCODE_SET_SYMBOL_TRAILING_FLAGS_IMM  = $40;
  BIND_OPCODE_SET_TYPE_IMM                   = $50;
  BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB    = $70;
  BIND_OPCODE_DO_BIND                        = $90;
  BIND_OPCODE_DONE                           = $00;

{ (segname, sectname) a container section kind maps to — shared with the
  structural tests and the future link path. }
procedure MachOSectionNames(AKind: TContainerSectionKind;
  out ASegName, ASectName: string);

const
  MH_MAGIC_64        = Integer($FEEDFACF);
  CPU_TYPE_ARM64     = Integer($0100000C);
  CPU_SUBTYPE_ARM64_ALL = 0;
  MH_OBJECT          = 1;
  MH_EXECUTE         = 2;
  MH_SUBSECTIONS_VIA_SYMBOLS = $2000;

  LC_SEGMENT_64      = $19;
  LC_SYMTAB          = $02;
  LC_DYSYMTAB        = $0B;
  LC_BUILD_VERSION   = $32;

  PLATFORM_MACOS     = 1;

  { section_64 flags }
  S_REGULAR                = $00;
  S_ZEROFILL               = $01;
  S_THREAD_LOCAL_REGULAR   = $11;
  S_THREAD_LOCAL_ZEROFILL  = $12;
  S_THREAD_LOCAL_VARIABLES = $13;
  S_ATTR_PURE_INSTRUCTIONS = Integer($80000000);
  S_ATTR_SOME_INSTRUCTIONS = $00000400;

  { nlist_64 n_type / n_desc }
  N_EXT      = $01;
  N_UNDF     = $00;
  N_SECT     = $0E;
  N_WEAK_REF = $0040;
  N_WEAK_DEF = $0080;

  { AArch64 relocation types (r_type) }
  ARM64_RELOC_UNSIGNED            = 0;
  ARM64_RELOC_SUBTRACTOR          = 1;
  ARM64_RELOC_BRANCH26            = 2;
  ARM64_RELOC_PAGE21              = 3;
  ARM64_RELOC_PAGEOFF12           = 4;
  ARM64_RELOC_GOT_LOAD_PAGE21     = 5;
  ARM64_RELOC_GOT_LOAD_PAGEOFF12  = 6;
  ARM64_RELOC_POINTER_TO_GOT      = 7;
  ARM64_RELOC_TLVP_LOAD_PAGE21    = 8;
  ARM64_RELOC_TLVP_LOAD_PAGEOFF12 = 9;
  ARM64_RELOC_ADDEND              = 10;

implementation

uses
  streams, uStrCompat, blaise.sha256;

procedure _mw_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

const
  MACH_HEADER_SIZE   = 32;
  SEGMENT_CMD_SIZE   = 72;
  SECTION_64_SIZE    = 80;
  BUILD_VERSION_SIZE = 24;
  SYMTAB_CMD_SIZE    = 24;
  DYSYMTAB_CMD_SIZE  = 80;
  NLIST_64_SIZE      = 16;
  RELOC_INFO_SIZE    = 8;

  { Serialisation order: file-backed sections first, zerofill LAST (a
    Mach-O segment rule).  Indexed by emission position.

    cskInitArray is deliberately absent: it is the ELF .init_array kind.  The
    Mach-O analogue is __DATA,__mod_init_func (S_MOD_INIT_FUNC_POINTERS), which
    is not emitted yet — shared-object output is ELF-only, gated by
    TBackendDriver.SupportsLibrary.  Add it here when Darwin libraries land. }
  { cskIface sits with the other non-loaded metadata, ahead of the zerofill
    sections which must stay last. }
  SectionEmitOrder: array[0..8] of TContainerSectionKind = (
    cskText, cskRodata, cskData, cskTdata, cskTvars, cskOpdf, cskIface,
    cskBss, cskTbss);

procedure MachOSectionNames(AKind: TContainerSectionKind;
  out ASegName, ASectName: string);
begin
  case AKind of
    cskText:
    begin
      ASegName := '__TEXT'; ASectName := '__text';
    end;
    cskRodata:
    begin
      ASegName := '__TEXT'; ASectName := '__const';
    end;
    cskData:
    begin
      ASegName := '__DATA'; ASectName := '__data';
    end;
    cskBss:
    begin
      ASegName := '__DATA'; ASectName := '__bss';
    end;
    cskTbss:
    begin
      ASegName := '__DATA'; ASectName := '__thread_bss';
    end;
    cskTdata:
    begin
      ASegName := '__DATA'; ASectName := '__thread_data';
    end;
    cskTvars:
    begin
      ASegName := '__DATA'; ASectName := '__thread_vars';
    end;
    cskOpdf:
    begin
      ASegName := '__OPDF'; ASectName := '__opdf';
    end;
    cskIface:
    begin
      { Embedded unit interface (.bif).  Metadata an executable never carries,
        so the linker drops it by name — blaise.linker.macho.pas already lists
        '__blaise_iface' / segment '__BLAISE' among the dropped sections, which
        is where these names come from. }
      ASegName := '__BLAISE'; ASectName := '__blaise_iface';
    end;
  else
    begin
      ASegName := '__TEXT'; ASectName := '__text';
    end;
  end;
end;

function MachOSectionFlags(AKind: TContainerSectionKind): Integer;
begin
  case AKind of
    cskText:   Result := S_REGULAR or S_ATTR_PURE_INSTRUCTIONS
                         or S_ATTR_SOME_INSTRUCTIONS;
    cskBss:    Result := S_ZEROFILL;
    cskTbss:   Result := S_THREAD_LOCAL_ZEROFILL;
    cskTdata:  Result := S_THREAD_LOCAL_REGULAR;
    cskTvars:  Result := S_THREAD_LOCAL_VARIABLES;
  else
    Result := S_REGULAR;
  end;
end;

function IsZeroFill(AKind: TContainerSectionKind): Boolean;
begin
  Result := (AKind = cskBss) or (AKind = cskTbss);
end;

function MoAlignUp(AVal: Integer; AAlign: Integer): Integer;
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

function Log2Align(AAlign: Integer): Integer;
var
  V: Integer;
begin
  Result := 0;
  V := AAlign;
  while V > 1 do
  begin
    V := V shr 1;
    Result := Result + 1;
  end;
end;

{ 16-byte fixed-width name field (segname/sectname), NUL-padded. }
procedure PushName16(ABuf: TByteBuf; const AName: string);
var
  I: Integer;
begin
  for I := 0 to 15 do
  begin
    if I < Length(AName) then
      ABuf.PushByte(StrAt(AName, I))
    else
      ABuf.PushByte(0);
  end;
end;

{ ---- TMachOWriterSection ---------------------------------------------- }

constructor TMachOWriterSection.Create(AKind: TContainerSectionKind);
begin
  inherited Create();
  Kind := AKind;
  SetLength(Bytes, 0);
  Count := 0;
  Size := 0;
  Align := 1;
  SetLength(Relocs, 0);
  RelocCount := 0;
end;

destructor TMachOWriterSection.Destroy;
begin
  SetLength(Bytes, 0);
  SetLength(Relocs, 0);
  inherited Destroy();
end;

procedure TMachOWriterSection.PushByte(AVal: Integer);
var
  NewCap: Integer;
begin
  if Count >= Length(Bytes) then
  begin
    NewCap := Length(Bytes) * 2;
    if NewCap < 64 then
      NewCap := 64;
    SetLength(Bytes, NewCap);
  end;
  Bytes[Count] := AVal and $FF;
  Count := Count + 1;
  Size := Count;
end;

function TMachOWriterSection.AsString: string;
begin
  SetLength(Result, Count);
  if Count > 0 then
    _mw_memcpy(PChar(Result), @Bytes[0], Count);
end;

{ ---- TMachOObjectWriter ------------------------------------------------ }

constructor TMachOObjectWriter.Create;
var
  I: Integer;
begin
  inherited Create();
  { sized from the enum — a new TContainerSectionKind member must never
    silently shift ordinals past the array (BUG-045) }
  SetLength(FSections, Ord(High(TContainerSectionKind)) + 1);
  for I := 0 to Ord(High(TContainerSectionKind)) do
    FSections[I] := nil;
  FSymbols := TList<TMachOWriterSym>.Create();
  FSymMap  := TDictionary<string, Integer>.Create();
end;

destructor TMachOObjectWriter.Destroy;
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

function TMachOObjectWriter.GetSection(AKind: TContainerSectionKind): TMachOWriterSection;
var
  Idx: Integer;
begin
  Idx := Ord(AKind);
  if FSections[Idx] = nil then
    FSections[Idx] := TMachOWriterSection.Create(AKind);
  Result := FSections[Idx];
end;

procedure TMachOObjectWriter.SelectSection(AKind: TContainerSectionKind);
begin
  GetSection(AKind);
end;

function TMachOObjectWriter.Append(AKind: TContainerSectionKind;
  const ABytes: string): Integer;
var
  Sec: TMachOWriterSection;
  I: Integer;
begin
  Sec := GetSection(AKind);
  Result := Sec.Count;
  for I := 0 to Length(ABytes) - 1 do
    Sec.PushByte(StrAt(ABytes, I));
end;

procedure TMachOObjectWriter.AppendByte(AKind: TContainerSectionKind; AVal: Integer);
begin
  GetSection(AKind).PushByte(AVal);
end;

procedure TMachOObjectWriter.AppendWord(AKind: TContainerSectionKind; AVal: Integer);
var
  Sec: TMachOWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.PushByte(AVal and $FF);
  Sec.PushByte((AVal shr 8) and $FF);
end;

procedure TMachOObjectWriter.AppendDWord(AKind: TContainerSectionKind; AVal: Integer);
var
  Sec: TMachOWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.PushByte(AVal and $FF);
  Sec.PushByte((AVal shr 8) and $FF);
  Sec.PushByte((AVal shr 16) and $FF);
  Sec.PushByte((AVal shr 24) and $FF);
end;

procedure TMachOObjectWriter.AppendQWord(AKind: TContainerSectionKind; AVal: Int64);
var
  Sec: TMachOWriterSection;
  I: Integer;
begin
  Sec := GetSection(AKind);
  for I := 0 to 7 do
    Sec.PushByte(Integer((AVal shr (I * 8)) and $FF));
end;

procedure TMachOObjectWriter.AppendZeros(AKind: TContainerSectionKind; ACount: Integer);
var
  Sec: TMachOWriterSection;
  I: Integer;
begin
  Sec := GetSection(AKind);
  for I := 1 to ACount do
    Sec.PushByte(0);
end;

procedure TMachOObjectWriter.AlignSection(AKind: TContainerSectionKind; AAlign: Integer);
var
  Sec: TMachOWriterSection;
  Pad, I: Integer;
begin
  Sec := GetSection(AKind);
  if AAlign > Sec.Align then
    Sec.Align := AAlign;
  if IsZeroFill(AKind) then
  begin
    Sec.Size := MoAlignUp(Sec.Size, AAlign);
  end
  else
  begin
    Pad := MoAlignUp(Sec.Count, AAlign) - Sec.Count;
    for I := 1 to Pad do
      Sec.PushByte(0);
  end;
end;

procedure TMachOObjectWriter.ReserveBss(AKind: TContainerSectionKind; ASize: Integer);
var
  Sec: TMachOWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.Size := Sec.Size + ASize;
end;

function TMachOObjectWriter.CurrentOffset(AKind: TContainerSectionKind): Integer;
var
  Sec: TMachOWriterSection;
begin
  Sec := GetSection(AKind);
  if IsZeroFill(AKind) then
    Result := Sec.Size
  else
    Result := Sec.Count;
end;

procedure TMachOObjectWriter.Patch32(AKind: TContainerSectionKind;
  AOffset: Integer; AVal: Integer);
var
  Sec: TMachOWriterSection;
begin
  Sec := GetSection(AKind);
  Sec.Bytes[AOffset]     := AVal and $FF;
  Sec.Bytes[AOffset + 1] := (AVal shr 8) and $FF;
  Sec.Bytes[AOffset + 2] := (AVal shr 16) and $FF;
  Sec.Bytes[AOffset + 3] := (AVal shr 24) and $FF;
end;

function TMachOObjectWriter.DefineSymbol(const AName: string;
  ASection: TContainerSectionKind; AValue: Integer; ASize: Integer;
  ABind: TContainerSymBind; ASType: TContainerSymType): Integer;
var
  Sym: TMachOWriterSym;
  Existing: Integer;
begin
  if FSymMap.TryGetValue(AName, Existing) then
  begin
    Result := Existing;
    Exit;
  end;
  Sym := TMachOWriterSym.Create();
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

function TMachOObjectWriter.ExternSymbol(const AName: string): Integer;
var
  Sym: TMachOWriterSym;
  Existing: Integer;
begin
  if FSymMap.TryGetValue(AName, Existing) then
  begin
    Result := Existing;
    Exit;
  end;
  Sym := TMachOWriterSym.Create();
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

function TMachOObjectWriter.FindSymbol(const AName: string): Integer;
var
  Val: Integer;
begin
  if FSymMap.TryGetValue(AName, Val) then
    Result := Val
  else
    Result := -1;
end;

procedure TMachOObjectWriter.AddReloc(ASection: TContainerSectionKind;
  AOffset: Integer; ASymIndex: Integer; ARType: TContainerRelocKind;
  AAddend: Int64);
var
  Sec: TMachOWriterSection;
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

{ ---- Finish: serialise to MH_OBJECT bytes ------------------------------ }

function RelocKindToMachO(ARType: TContainerRelocKind): Integer;
begin
  case ARType of
    crkArm64Abs64:        Result := ARM64_RELOC_UNSIGNED;
    crkArm64Branch26:     Result := ARM64_RELOC_BRANCH26;
    crkArm64Page21:       Result := ARM64_RELOC_PAGE21;
    crkArm64PageOff12:    Result := ARM64_RELOC_PAGEOFF12;
    crkArm64GotPage21:    Result := ARM64_RELOC_GOT_LOAD_PAGE21;
    crkArm64GotPageOff12: Result := ARM64_RELOC_GOT_LOAD_PAGEOFF12;
    crkArm64TlvPage21:    Result := ARM64_RELOC_TLVP_LOAD_PAGE21;
    crkArm64TlvPageOff12: Result := ARM64_RELOC_TLVP_LOAD_PAGEOFF12;
  else
    raise EMachOWriter.Create(
      'machowriter: non-AArch64 relocation kind at a Mach-O arm64 section ('
      + IntToStr(Ord(ARType)) + ')');
  end;
end;

function RelocIsPcRel(AMachType: Integer): Boolean;
begin
  Result := (AMachType = ARM64_RELOC_BRANCH26)
    or (AMachType = ARM64_RELOC_PAGE21)
    or (AMachType = ARM64_RELOC_GOT_LOAD_PAGE21)
    or (AMachType = ARM64_RELOC_TLVP_LOAD_PAGE21);
end;

{ One packed relocation_info record.  r_address, then the packed word:
  r_symbolnum:24 | r_pcrel:1 | r_length:2 | r_extern:1 | r_type:4. }
procedure PushRelocInfo(ABuf: TByteBuf; AAddress, ASymNum: Integer;
  APcRel: Boolean; ALength: Integer; AExtern: Boolean; AType: Integer);
var
  W: Integer;
begin
  ABuf.PushU32(AAddress);
  W := ASymNum and $FFFFFF;
  if APcRel then
    W := W or (1 shl 24);
  W := W or ((ALength and 3) shl 25);
  if AExtern then
    W := W or (1 shl 27);
  W := W or ((AType and $F) shl 28);
  ABuf.PushU32(W);
end;

function TMachOObjectWriter.Finish: string;
var
  Emitted: array of TMachOWriterSection;   { emission-ordered, non-empty }
  NSects, I, J, K: Integer;
  Sec: TMachOWriterSection;
  SecAddr: array of Int64;                 { vm address per emitted section }
  SecFileOff: array of Integer;            { file offset per emitted section }
  SecRelOff: array of Integer;             { reloff per emitted section }
  SecNReloc: array of Integer;             { encoded reloc count per section }
  SectOrdinalOf: array of Integer;         { Ord(kind) -> 1-based ordinal }
  VmOff: Int64;
  FileOff, DataStart: Integer;
  SizeOfCmds, NCmds: Integer;
  Order: TList<Integer>;                   { old symbol index, serial order }
  NewIdxOf: array of Integer;              { old index -> serialised index }
  NLocal, NExtDef, NUndef: Integer;
  Sym: TMachOWriterSym;
  StrTab: TByteBuf;
  SymTabBuf: TByteBuf;
  RelocBuf: TByteBuf;
  Head: TByteBuf;
  StrOff: Integer;
  NType, NSect, NDesc: Integer;
  NValue: Int64;
  MachType, RelLen: Integer;
  R: TContainerReloc;
  V: Int64;
  SegName, SectName: string;
  SymOff, StrTabOff: Integer;
  FileSizeTotal: Int64;
  VmSizeTotal: Int64;
begin
  { ---- collect non-empty sections in emission order (zerofill last) ---- }
  SetLength(Emitted, 0);
  NSects := 0;
  SetLength(SectOrdinalOf, Ord(High(TContainerSectionKind)) + 1);
  for I := 0 to Ord(High(TContainerSectionKind)) do
    SectOrdinalOf[I] := 0;
  for I := 0 to Length(SectionEmitOrder) - 1 do
  begin
    Sec := FSections[Ord(SectionEmitOrder[I])];
    if Sec = nil then Continue;
    if (Sec.Count = 0) and (Sec.Size = 0) then Continue;
    SetLength(Emitted, NSects + 1);
    Emitted[NSects] := Sec;
    SectOrdinalOf[Ord(Sec.Kind)] := NSects + 1;   { 1-based n_sect ordinal }
    NSects := NSects + 1;
  end;

  { ---- order symbols: locals, externally-defined, undefined ---- }
  Order := TList<Integer>.Create();
  StrTab := TByteBuf.Create();
  SymTabBuf := TByteBuf.Create();
  RelocBuf := TByteBuf.Create();
  Head := TByteBuf.Create();
  try
    NLocal := 0;
    NExtDef := 0;
    NUndef := 0;
    for I := 0 to FSymbols.Count - 1 do
      if (not FSymbols.Get(I).IsExtern) and
         (FSymbols.Get(I).Bind = csbLocal) then
      begin
        Order.Add(I);
        NLocal := NLocal + 1;
      end;
    for I := 0 to FSymbols.Count - 1 do
      if (not FSymbols.Get(I).IsExtern) and
         (FSymbols.Get(I).Bind <> csbLocal) then
      begin
        Order.Add(I);
        NExtDef := NExtDef + 1;
      end;
    for I := 0 to FSymbols.Count - 1 do
      if FSymbols.Get(I).IsExtern then
      begin
        Order.Add(I);
        NUndef := NUndef + 1;
      end;
    SetLength(NewIdxOf, FSymbols.Count);
    for I := 0 to Order.Count - 1 do
      NewIdxOf[Order.Get(I)] := I;

    { ---- layout: header + load commands, then section data ---- }
    SizeOfCmds := (SEGMENT_CMD_SIZE + NSects * SECTION_64_SIZE)
      + BUILD_VERSION_SIZE + SYMTAB_CMD_SIZE + DYSYMTAB_CMD_SIZE;
    NCmds := 4;
    DataStart := MACH_HEADER_SIZE + SizeOfCmds;

    SetLength(SecAddr, NSects);
    SetLength(SecFileOff, NSects);
    SetLength(SecRelOff, NSects);
    SetLength(SecNReloc, NSects);

    VmOff := 0;
    FileOff := DataStart;
    for I := 0 to NSects - 1 do
    begin
      Sec := Emitted[I];
      VmOff := MoAlignUp(Integer(VmOff), Sec.Align);
      SecAddr[I] := VmOff;
      if IsZeroFill(Sec.Kind) then
      begin
        SecFileOff[I] := 0;
        VmOff := VmOff + Sec.Size;
      end
      else
      begin
        FileOff := MoAlignUp(FileOff, Sec.Align);
        SecFileOff[I] := FileOff;
        FileOff := FileOff + Sec.Count;
        VmOff := VmOff + Sec.Count;
      end;
    end;
    FileSizeTotal := FileOff - DataStart;   { file-backed section bytes }
    VmSizeTotal := VmOff;

    { ---- encode relocations (after section data) ---- }
    FileOff := MoAlignUp(FileOff, 8);
    for I := 0 to NSects - 1 do
    begin
      Sec := Emitted[I];
      SecRelOff[I] := FileOff;
      SecNReloc[I] := 0;
      for J := 0 to Sec.RelocCount - 1 do
      begin
        R := Sec.Relocs[J];
        MachType := RelocKindToMachO(R.RType);
        if MachType = ARM64_RELOC_UNSIGNED then
          RelLen := 3
        else
          RelLen := 2;
        if R.Addend <> 0 then
        begin
          if MachType = ARM64_RELOC_UNSIGNED then
          begin
            { No addend slot in relocation_info: fold it into the section
              bytes the relocation targets. }
            V := 0;
            for K := 0 to 7 do
              V := V or (Int64(Sec.Bytes[R.Offset + K]) shl (K * 8));
            V := V + R.Addend;
            for K := 0 to 7 do
              Sec.Bytes[R.Offset + K] := Integer((V shr (K * 8)) and $FF);
          end
          else if (MachType = ARM64_RELOC_BRANCH26)
               or (MachType = ARM64_RELOC_PAGE21)
               or (MachType = ARM64_RELOC_PAGEOFF12) then
          begin
            if (R.Addend > $7FFFFF) or (R.Addend < -$800000) then
              raise EMachOWriter.Create(
                'machowriter: ARM64_RELOC_ADDEND out of 24-bit range: '
                + IntToStr(R.Addend));
            { ADDEND pseudo-relocation immediately precedes its target. }
            PushRelocInfo(RelocBuf, R.Offset,
              Integer(R.Addend) and $FFFFFF, False, 2, False,
              ARM64_RELOC_ADDEND);
            SecNReloc[I] := SecNReloc[I] + 1;
          end
          else
            raise EMachOWriter.Create(
              'machowriter: relocation kind ' + IntToStr(MachType)
              + ' cannot carry an addend');
        end;
        PushRelocInfo(RelocBuf, R.Offset, NewIdxOf[R.SymIndex],
          RelocIsPcRel(MachType), RelLen, True, MachType);
        SecNReloc[I] := SecNReloc[I] + 1;
      end;
      FileOff := FileOff + SecNReloc[I] * RELOC_INFO_SIZE;
      if SecNReloc[I] = 0 then
        SecRelOff[I] := 0;
    end;

    { ---- symbol table + string table ---- }
    SymOff := FileOff;
    StrTab.PushByte(0);   { index 0 = empty name }
    for I := 0 to Order.Count - 1 do
    begin
      Sym := FSymbols.Get(Order.Get(I));
      if Sym.Name = '' then
        StrOff := 0
      else
      begin
        StrOff := StrTab.Count;
        StrTab.AppendBytes(Sym.Name);
        StrTab.PushByte(0);
      end;
      NDesc := 0;
      if Sym.IsExtern then
      begin
        NType := N_UNDF or N_EXT;
        NSect := 0;
        NValue := 0;
        if Sym.Bind = csbWeak then
          NDesc := N_WEAK_REF;
      end
      else
      begin
        NType := N_SECT;
        if Sym.Bind <> csbLocal then
          NType := NType or N_EXT;
        if Sym.Bind = csbWeak then
          NDesc := N_WEAK_DEF;
        NSect := SectOrdinalOf[Ord(Sym.Section)];
        if NSect = 0 then
          raise EMachOWriter.Create('machowriter: symbol "' + Sym.Name
            + '" defined in an empty/unemitted section');
        NValue := SecAddr[NSect - 1] + Sym.Value;
      end;
      SymTabBuf.PushU32(StrOff);
      SymTabBuf.PushByte(NType);
      SymTabBuf.PushByte(NSect);
      SymTabBuf.PushU16(NDesc);
      SymTabBuf.PushU64(NValue);
    end;
    StrTabOff := SymOff + Order.Count * NLIST_64_SIZE;

    { ---- header ---- }
    Head.PushU32(MH_MAGIC_64);
    Head.PushU32(CPU_TYPE_ARM64);
    Head.PushU32(CPU_SUBTYPE_ARM64_ALL);
    Head.PushU32(MH_OBJECT);
    Head.PushU32(NCmds);
    Head.PushU32(SizeOfCmds);
    Head.PushU32(MH_SUBSECTIONS_VIA_SYMBOLS);
    Head.PushU32(0);   { reserved }

    { ---- LC_SEGMENT_64 (single, unnamed) ---- }
    Head.PushU32(LC_SEGMENT_64);
    Head.PushU32(SEGMENT_CMD_SIZE + NSects * SECTION_64_SIZE);
    PushName16(Head, '');                 { segname: empty in MH_OBJECT }
    Head.PushU64(0);                      { vmaddr }
    Head.PushU64(VmSizeTotal);            { vmsize }
    Head.PushU64(DataStart);              { fileoff }
    Head.PushU64(FileSizeTotal);          { filesize }
    Head.PushU32(7);                      { maxprot rwx }
    Head.PushU32(7);                      { initprot rwx }
    Head.PushU32(NSects);
    Head.PushU32(0);                      { flags }
    for I := 0 to NSects - 1 do
    begin
      Sec := Emitted[I];
      MachOSectionNames(Sec.Kind, SegName, SectName);
      PushName16(Head, SectName);
      PushName16(Head, SegName);
      Head.PushU64(SecAddr[I]);
      if IsZeroFill(Sec.Kind) then
        Head.PushU64(Sec.Size)
      else
        Head.PushU64(Sec.Count);
      Head.PushU32(SecFileOff[I]);
      Head.PushU32(Log2Align(Sec.Align));
      Head.PushU32(SecRelOff[I]);
      Head.PushU32(SecNReloc[I]);
      Head.PushU32(MachOSectionFlags(Sec.Kind));
      Head.PushU32(0);                    { reserved1 }
      Head.PushU32(0);                    { reserved2 }
      Head.PushU32(0);                    { reserved3 }
    end;

    { ---- LC_BUILD_VERSION ---- }
    Head.PushU32(LC_BUILD_VERSION);
    Head.PushU32(BUILD_VERSION_SIZE);
    Head.PushU32(PLATFORM_MACOS);
    Head.PushU32($000B0000);              { minos 11.0.0 }
    Head.PushU32(0);                      { sdk (none recorded) }
    Head.PushU32(0);                      { ntools }

    { ---- LC_SYMTAB ---- }
    Head.PushU32(LC_SYMTAB);
    Head.PushU32(SYMTAB_CMD_SIZE);
    Head.PushU32(SymOff);
    Head.PushU32(Order.Count);
    Head.PushU32(StrTabOff);
    Head.PushU32(StrTab.Count);

    { ---- LC_DYSYMTAB ---- }
    Head.PushU32(LC_DYSYMTAB);
    Head.PushU32(DYSYMTAB_CMD_SIZE);
    Head.PushU32(0);                      { ilocalsym }
    Head.PushU32(NLocal);
    Head.PushU32(NLocal);                 { iextdefsym }
    Head.PushU32(NExtDef);
    Head.PushU32(NLocal + NExtDef);       { iundefsym }
    Head.PushU32(NUndef);
    for I := 1 to 12 do
      Head.PushU32(0);                    { toc..nlocrel: unused }

    if Head.Count <> DataStart then
      raise EMachOWriter.Create('machowriter: load-command size mismatch: '
        + IntToStr(Head.Count) + ' vs ' + IntToStr(DataStart));

    { ---- section data ---- }
    for I := 0 to NSects - 1 do
    begin
      Sec := Emitted[I];
      if IsZeroFill(Sec.Kind) then Continue;
      Head.PadTo(SecFileOff[I]);
      Head.AppendBytes(Sec.AsString());
    end;

    { ---- relocations, symtab, strtab ---- }
    Head.PadTo(SymOff - RelocBuf.Count);
    Head.AppendBuf(RelocBuf);
    Head.AppendBuf(SymTabBuf);
    Head.AppendBuf(StrTab);

    Result := Head.AsString();
  finally
    Head.Free();
    RelocBuf.Free();
    SymTabBuf.Free();
    StrTab.Free();
    Order.Free();
  end;
end;

procedure TMachOObjectWriter.WriteToFile(const APath: string);
var
  Buf: string;
  FOut: TFileOutputStream;
begin
  Buf := Finish();
  FOut := TFileOutputStream.Create(APath);
  try
    FOut.Write(PChar(Buf), Length(Buf));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;
end;

{ ---- TMachOExecWriter --------------------------------------------------- }

{ Fixed v1 load-command configuration:
    __PAGEZERO, __TEXT(__text,__const), __DATA(__data,__bss), __LINKEDIT,
    LC_DYLD_INFO_ONLY, LC_SYMTAB, LC_DYSYMTAB, LC_LOAD_DYLINKER,
    LC_BUILD_VERSION, LC_LOAD_DYLIB, LC_MAIN  (ncmds = 11). }
const
  DYLD_PATH    = '/usr/lib/dyld';
  LIBSYSTEM    = '/usr/lib/libSystem.B.dylib';
  DYLINKER_CMD_SIZE = 32;   { 12 + len(dyld path)+1 = 26, padded to 8 }
  DYLIB_CMD_SIZE    = 56;   { 24 + len(libSystem)+1 = 51, padded to 8 }
  DYLDINFO_CMD_SIZE = 48;
  MAIN_CMD_SIZE     = 24;
  { 72(__PAGEZERO) + 232(__TEXT: 72+2*80) + 472(__DATA: 72+5*80: data,
    thread_vars, thread_data, thread_bss, bss) + 72(__LINKEDIT)
    + 48(dyld-info) + 24(symtab) + 80(dysymtab) + 32(dylinker)
    + 24(build-version) + 56(dylib) + 24(main) — the Finish size check
    guards this precomputed literal. }
  EXEC_SIZEOFCMDS = 1176;   { 1136 + 16 (LC_CODE_SIGNATURE) + 24 (LC_UUID) }
  EXEC_NCMDS = 13;
  LC_UUID = $1B;
  MH_HAS_TLV_DESCRIPTORS = $800000;

  { ad-hoc code signature (Phase 4).  All signature-blob fields are
    BIG-endian.  Unsigned arm64 binaries are SIGKILLed at exec — the
    kernel demands at least an ad-hoc CodeDirectory with SHA-256 page
    hashes covering the whole file up to the signature itself. }
  LC_CODE_SIGNATURE = $1D;
  CSMAGIC_EMBEDDED_SIGNATURE = Integer($FADE0CC0);
  CSMAGIC_CODEDIRECTORY      = Integer($FADE0C02);
  CS_ADHOC = $2;
  CS_EXECSEG_MAIN_BINARY = $1;
  CS_HASHTYPE_SHA256 = 2;
  CS_PAGE_BITS = 12;      { 4096-byte signature pages }
  CD_HEADER_SIZE = 88;    { version $20400 layout }

procedure PushUleb(ABuf: TByteBuf; AVal: Int64);
var
  B: Integer;
begin
  repeat
    B := Integer(AVal and $7F);
    AVal := AVal shr 7;
    if AVal <> 0 then
      B := B or $80;
    ABuf.PushByte(B);
  until AVal = 0;
end;

function MoAlignUp64(AVal: Int64; AAlign: Int64): Int64;
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

constructor TMachOExecWriter.Create;
begin
  inherited Create();
  FRebases := TList<Int64>.Create();
  FBindAddrs := TList<Int64>.Create();
  FBindNames := TList<string>.Create();
  FGlobalNames := TList<string>.Create();
  FGlobalAddrs := TList<Int64>.Create();
end;

destructor TMachOExecWriter.Destroy;
begin
  FRebases.Free();
  FBindAddrs.Free();
  FBindNames.Free();
  FGlobalNames.Free();
  FGlobalAddrs.Free();
  inherited Destroy();
end;

procedure TMachOExecWriter.SetText(const ABytes: string);
begin
  FText := ABytes;
end;

procedure TMachOExecWriter.SetConst(const ABytes: string);
begin
  FConst := ABytes;
end;

procedure TMachOExecWriter.SetData(const ABytes: string);
begin
  FData := ABytes;
end;

procedure TMachOExecWriter.SetTvars(const ABytes: string);
begin
  FTvars := ABytes;
end;

procedure TMachOExecWriter.SetTdata(const ABytes: string);
begin
  FTdata := ABytes;
end;

procedure TMachOExecWriter.SetTbssSize(ASize: Int64);
begin
  FTbssSize := ASize;
end;

procedure TMachOExecWriter.SetBssSize(ASize: Int64);
begin
  FBssSize := ASize;
end;

procedure TMachOExecWriter.SetEntryTextOffset(AOff: Integer);
begin
  FEntryTextOff := AOff;
end;

procedure TMachOExecWriter.SetIdentifier(const AName: string);
begin
  FIdent := AName;
end;

procedure TMachOExecWriter.AddRebase(AVmAddr: Int64);
begin
  FRebases.Add(AVmAddr);
end;

procedure TMachOExecWriter.AddBind(AVmAddr: Int64; const AName: string);
begin
  FBindAddrs.Add(AVmAddr);
  FBindNames.Add(AName);
end;

procedure TMachOExecWriter.AddGlobal(const AName: string; AVmAddr: Int64);
begin
  FGlobalNames.Add(AName);
  FGlobalAddrs.Add(AVmAddr);
end;

function TMachOExecWriter.TextVmAddr: Int64;
begin
  Result := MACHO_EXEC_BASE
    + MoAlignUp(MACH_HEADER_SIZE + EXEC_SIZEOFCMDS, 16);
end;

function TMachOExecWriter.ComputeLayout: TMachOExecLayout;
var
  TextOff, ConstOff: Integer;
  TextSegFileSize, DataOff: Int64;
begin
  TextOff := MoAlignUp(MACH_HEADER_SIZE + EXEC_SIZEOFCMDS, 16);
  ConstOff := MoAlignUp(TextOff + Length(FText), 16);
  TextSegFileSize := MoAlignUp64(ConstOff + Length(FConst), MACHO_PAGE_SIZE);
  DataOff := TextSegFileSize;
  Result.TextVm := MACHO_EXEC_BASE + TextOff;
  Result.ConstVm := MACHO_EXEC_BASE + ConstOff;
  Result.DataVm := MACHO_EXEC_BASE + DataOff;
  Result.TvarsVm := MoAlignUp64(Result.DataVm + Length(FData), 8);
  Result.TdataVm := MoAlignUp64(Result.TvarsVm + Length(FTvars), 8);
  { zerofill sections trail the file-backed bytes: thread_bss directly
    after thread_data (keeping the TLV content region contiguous), then
    the plain bss }
  Result.TbssVm := Result.TdataVm + Length(FTdata);
  Result.BssVm := MoAlignUp64(Result.TbssVm + FTbssSize, 8);
end;

function Be32(AVal: Int64): string;
begin
  Result := Chr(Integer((AVal shr 24) and $FF))
    + Chr(Integer((AVal shr 16) and $FF))
    + Chr(Integer((AVal shr 8) and $FF))
    + Chr(Integer(AVal and $FF));
end;

function Be64(AVal: Int64): string;
begin
  Result := Be32((AVal shr 32) and $FFFFFFFF) + Be32(AVal and $FFFFFFFF);
end;

function TMachOExecWriter.Finish: string;
var
  Head, Reb, Bind, SymT, StrT: TByteBuf;
  L: TMachOExecLayout;
  TextOff, ConstOff: Integer;
  TextSegFileSize: Int64;
  DataOff, TvarsOff, TdataOff, DataFileEnd: Int64;
  DataVm, BssVm, DataSegVmSize, DataSegFileSize: Int64;
  LinkOff, LinkVm: Int64;
  RebOff, BindOff, SymOff, StrOff: Int64;
  SigOff, SigSize: Int64;
  NSlots, PageLen: Integer;
  Unsigned, Blob, Page: string;
  I: Integer;
  A: Int64;
  StrIdx: Integer;
  NSectOf: Integer;
  HdrFlags: Integer;
begin
  if FIdent = '' then
    FIdent := 'blaise';
  L := ComputeLayout();
  TextOff := Integer(L.TextVm - MACHO_EXEC_BASE);
  ConstOff := Integer(L.ConstVm - MACHO_EXEC_BASE);
  TextSegFileSize := MoAlignUp64(ConstOff + Length(FConst), MACHO_PAGE_SIZE);
  DataOff := L.DataVm - MACHO_EXEC_BASE;
  DataVm := L.DataVm;
  TvarsOff := L.TvarsVm - MACHO_EXEC_BASE;
  TdataOff := L.TdataVm - MACHO_EXEC_BASE;
  DataFileEnd := TdataOff + Length(FTdata);
  BssVm := L.BssVm;
  DataSegFileSize := MoAlignUp64(DataFileEnd - DataOff, MACHO_PAGE_SIZE);
  DataSegVmSize := MoAlignUp64(BssVm + FBssSize - DataVm, MACHO_PAGE_SIZE);
  LinkOff := DataOff + DataSegFileSize;
  LinkVm := DataVm + DataSegVmSize;

  Head := TByteBuf.Create();
  Reb := TByteBuf.Create();
  Bind := TByteBuf.Create();
  SymT := TByteBuf.Create();
  StrT := TByteBuf.Create();
  try
    { ---- rebase opcodes (segment 2 = __DATA) ---- }
    if FRebases.Count > 0 then
    begin
      Reb.PushByte(REBASE_OPCODE_SET_TYPE_IMM or REBASE_TYPE_POINTER);
      for I := 0 to FRebases.Count - 1 do
      begin
        A := FRebases.Get(I);
        if (A < DataVm) or (A >= DataVm + DataSegVmSize) then
          raise EMachOWriter.Create('machowriter: rebase target outside __DATA');
        Reb.PushByte(REBASE_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB or 2);
        PushUleb(Reb, A - DataVm);
        Reb.PushByte(REBASE_OPCODE_DO_REBASE_IMM_TIMES or 1);
      end;
      Reb.PushByte(REBASE_OPCODE_DONE);
      while (Reb.Count mod 8) <> 0 do
        Reb.PushByte(0);
    end;

    { ---- bind opcodes (dylib ordinal 1 = libSystem) ---- }
    if FBindAddrs.Count > 0 then
    begin
      Bind.PushByte(BIND_OPCODE_SET_DYLIB_ORDINAL_IMM or 1);
      Bind.PushByte(BIND_OPCODE_SET_TYPE_IMM or BIND_TYPE_POINTER);
      for I := 0 to FBindAddrs.Count - 1 do
      begin
        A := FBindAddrs.Get(I);
        if (A < DataVm) or (A >= DataVm + DataSegVmSize) then
          raise EMachOWriter.Create('machowriter: bind target outside __DATA');
        Bind.PushByte(BIND_OPCODE_SET_SYMBOL_TRAILING_FLAGS_IMM or 0);
        Bind.AppendBytes(FBindNames.Get(I));
        Bind.PushByte(0);
        Bind.PushByte(BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB or 2);
        PushUleb(Bind, A - DataVm);
        Bind.PushByte(BIND_OPCODE_DO_BIND);
      end;
      Bind.PushByte(BIND_OPCODE_DONE);
      while (Bind.Count mod 8) <> 0 do
        Bind.PushByte(0);
    end;

    RebOff := LinkOff;
    BindOff := RebOff + Reb.Count;
    SymOff := BindOff + Bind.Count;

    { ---- symtab (globals only; n_sect by address range) ---- }
    StrT.PushByte(0);
    for I := 0 to FGlobalNames.Count - 1 do
    begin
      A := FGlobalAddrs.Get(I);
      if A >= BssVm then NSectOf := 7
      else if A >= L.TbssVm then NSectOf := 6
      else if A >= L.TdataVm then NSectOf := 5
      else if A >= L.TvarsVm then NSectOf := 4
      else if A >= DataVm then NSectOf := 3
      else if A >= MACHO_EXEC_BASE + ConstOff then NSectOf := 2
      else NSectOf := 1;
      StrIdx := StrT.Count;
      StrT.AppendBytes(FGlobalNames.Get(I));
      StrT.PushByte(0);
      SymT.PushU32(StrIdx);
      SymT.PushByte(N_SECT or N_EXT);
      SymT.PushByte(NSectOf);
      SymT.PushU16(0);
      SymT.PushU64(A);
    end;
    StrOff := SymOff + FGlobalNames.Count * NLIST_64_SIZE;
    { the ad-hoc signature trails everything: 16-aligned, covering the
      file up to its own start (codeLimit = SigOff) }
    SigOff := MoAlignUp64(StrOff + StrT.Count, 16);
    NSlots := Integer((SigOff + 4095) div 4096);
    SigSize := 12 + 8 + CD_HEADER_SIZE + Length(FIdent) + 1
      + Int64(NSlots) * 32;

    { ---- header ---- }
    Head.PushU32(MH_MAGIC_64);
    Head.PushU32(CPU_TYPE_ARM64);
    Head.PushU32(CPU_SUBTYPE_ARM64_ALL);
    Head.PushU32(MH_EXECUTE);
    Head.PushU32(EXEC_NCMDS);
    Head.PushU32(EXEC_SIZEOFCMDS);
    HdrFlags := MH_NOUNDEFS or MH_DYLDLINK or MH_TWOLEVEL or MH_PIE;
    if Length(FTvars) > 0 then
      HdrFlags := HdrFlags or MH_HAS_TLV_DESCRIPTORS;
    Head.PushU32(HdrFlags);
    Head.PushU32(0);

    { ---- __PAGEZERO ---- }
    Head.PushU32(LC_SEGMENT_64);
    Head.PushU32(SEGMENT_CMD_SIZE);
    PushName16(Head, '__PAGEZERO');
    Head.PushU64(0);
    Head.PushU64(MACHO_PAGEZERO_SIZE);
    Head.PushU64(0);
    Head.PushU64(0);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);

    { ---- __TEXT (maps file 0 .. TextSegFileSize) ---- }
    Head.PushU32(LC_SEGMENT_64);
    Head.PushU32(SEGMENT_CMD_SIZE + 2 * SECTION_64_SIZE);
    PushName16(Head, '__TEXT');
    Head.PushU64(MACHO_EXEC_BASE);
    Head.PushU64(TextSegFileSize);
    Head.PushU64(0);
    Head.PushU64(TextSegFileSize);
    Head.PushU32(5);   { r-x }
    Head.PushU32(5);
    Head.PushU32(2);
    Head.PushU32(0);
    PushName16(Head, '__text');
    PushName16(Head, '__TEXT');
    Head.PushU64(MACHO_EXEC_BASE + TextOff);
    Head.PushU64(Length(FText));
    Head.PushU32(TextOff);
    Head.PushU32(4);   { 2^4 = 16 }
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(S_REGULAR or S_ATTR_PURE_INSTRUCTIONS
      or S_ATTR_SOME_INSTRUCTIONS);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);
    PushName16(Head, '__const');
    PushName16(Head, '__TEXT');
    Head.PushU64(MACHO_EXEC_BASE + ConstOff);
    Head.PushU64(Length(FConst));
    Head.PushU32(ConstOff);
    Head.PushU32(4);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(S_REGULAR);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);

    { ---- __DATA (data, thread_vars, thread_data, thread_bss, bss) ---- }
    Head.PushU32(LC_SEGMENT_64);
    Head.PushU32(SEGMENT_CMD_SIZE + 5 * SECTION_64_SIZE);
    PushName16(Head, '__DATA');
    Head.PushU64(DataVm);
    Head.PushU64(DataSegVmSize);
    Head.PushU64(DataOff);
    Head.PushU64(DataSegFileSize);
    Head.PushU32(3);   { rw- }
    Head.PushU32(3);
    Head.PushU32(5);
    Head.PushU32(0);
    PushName16(Head, '__data');
    PushName16(Head, '__DATA');
    Head.PushU64(DataVm);
    Head.PushU64(Length(FData));
    Head.PushU32(Integer(DataOff));
    Head.PushU32(3);   { 2^3 = 8 }
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(S_REGULAR);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);
    PushName16(Head, '__thread_vars');
    PushName16(Head, '__DATA');
    Head.PushU64(L.TvarsVm);
    Head.PushU64(Length(FTvars));
    Head.PushU32(Integer(TvarsOff));
    Head.PushU32(3);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(S_THREAD_LOCAL_VARIABLES);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);
    PushName16(Head, '__thread_data');
    PushName16(Head, '__DATA');
    Head.PushU64(L.TdataVm);
    Head.PushU64(Length(FTdata));
    Head.PushU32(Integer(TdataOff));
    Head.PushU32(3);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(S_THREAD_LOCAL_REGULAR);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);
    PushName16(Head, '__thread_bss');
    PushName16(Head, '__DATA');
    Head.PushU64(L.TbssVm);
    Head.PushU64(FTbssSize);
    Head.PushU32(0);
    Head.PushU32(3);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(S_THREAD_LOCAL_ZEROFILL);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);
    PushName16(Head, '__bss');
    PushName16(Head, '__DATA');
    Head.PushU64(BssVm);
    Head.PushU64(FBssSize);
    Head.PushU32(0);
    Head.PushU32(3);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(S_ZEROFILL);
    Head.PushU32(0);
    Head.PushU32(0);
    Head.PushU32(0);

    { ---- __LINKEDIT ---- }
    Head.PushU32(LC_SEGMENT_64);
    Head.PushU32(SEGMENT_CMD_SIZE);
    PushName16(Head, '__LINKEDIT');
    Head.PushU64(LinkVm);
    Head.PushU64(MoAlignUp64(SigOff + SigSize - LinkOff, MACHO_PAGE_SIZE));
    Head.PushU64(LinkOff);
    Head.PushU64(SigOff + SigSize - LinkOff);
    Head.PushU32(1);   { r-- }
    Head.PushU32(1);
    Head.PushU32(0);
    Head.PushU32(0);

    { ---- LC_DYLD_INFO_ONLY ---- }
    Head.PushU32(LC_DYLD_INFO_ONLY);
    Head.PushU32(DYLDINFO_CMD_SIZE);
    if Reb.Count > 0 then Head.PushU32(Integer(RebOff)) else Head.PushU32(0);
    Head.PushU32(Reb.Count);
    if Bind.Count > 0 then Head.PushU32(Integer(BindOff)) else Head.PushU32(0);
    Head.PushU32(Bind.Count);
    Head.PushU32(0); Head.PushU32(0);   { weak bind }
    Head.PushU32(0); Head.PushU32(0);   { lazy bind }
    Head.PushU32(0); Head.PushU32(0);   { export trie }

    { ---- LC_SYMTAB ---- }
    Head.PushU32(LC_SYMTAB);
    Head.PushU32(SYMTAB_CMD_SIZE);
    Head.PushU32(Integer(SymOff));
    Head.PushU32(FGlobalNames.Count);
    Head.PushU32(Integer(StrOff));
    Head.PushU32(StrT.Count);

    { ---- LC_DYSYMTAB ---- }
    Head.PushU32(LC_DYSYMTAB);
    Head.PushU32(DYSYMTAB_CMD_SIZE);
    Head.PushU32(0); Head.PushU32(0);                     { locals }
    Head.PushU32(0); Head.PushU32(FGlobalNames.Count);    { extdef }
    Head.PushU32(FGlobalNames.Count); Head.PushU32(0);    { undef }
    for I := 1 to 12 do
      Head.PushU32(0);

    { ---- LC_LOAD_DYLINKER ---- }
    Head.PushU32(LC_LOAD_DYLINKER);
    Head.PushU32(DYLINKER_CMD_SIZE);
    Head.PushU32(12);   { name offset }
    Head.AppendBytes(DYLD_PATH);
    Head.PushByte(0);
    while (Head.Count mod 8) <> 0 do
      Head.PushByte(0);

    { ---- LC_BUILD_VERSION ---- }
    Head.PushU32(LC_BUILD_VERSION);
    Head.PushU32(BUILD_VERSION_SIZE);
    Head.PushU32(PLATFORM_MACOS);
    Head.PushU32($000B0000);   { minos 11.0 }
    Head.PushU32(0);
    Head.PushU32(0);

    { ---- LC_LOAD_DYLIB ---- }
    Head.PushU32(LC_LOAD_DYLIB);
    Head.PushU32(DYLIB_CMD_SIZE);
    Head.PushU32(24);          { name offset }
    Head.PushU32(0);           { timestamp }
    Head.PushU32($00010000);   { current_version 1.0 }
    Head.PushU32($00010000);   { compat_version 1.0 }
    Head.AppendBytes(LIBSYSTEM);
    Head.PushByte(0);
    while (Head.Count mod 8) <> 0 do
      Head.PushByte(0);

    { ---- LC_MAIN ---- }
    Head.PushU32(LC_MAIN);
    Head.PushU32(MAIN_CMD_SIZE);
    Head.PushU64(TextOff + FEntryTextOff);   { entryoff (file offset) }
    Head.PushU64(0);                         { stacksize: default }

    { ---- LC_UUID ----
      Content-derived (first 16 bytes of SHA-256 over the payloads +
      identifier) so builds stay reproducible.  Without it, lldb and
      the crash reporter cannot identify the image — crash reports
      showed uuid 00000000-... and lldb could not dedupe section
      mappings (M1 feedback). }
    Head.PushU32(LC_UUID);
    Head.PushU32(24);
    Head.AppendBytes(Copy(
      Sha256(FText + FConst + FData + FTvars + FTdata + FIdent), 0, 16));

    { ---- LC_CODE_SIGNATURE (must stay the LAST command) ---- }
    Head.PushU32(LC_CODE_SIGNATURE);
    Head.PushU32(16);
    Head.PushU32(Integer(SigOff));
    Head.PushU32(Integer(SigSize));

    if Head.Count <> MACH_HEADER_SIZE + EXEC_SIZEOFCMDS then
      raise EMachOWriter.Create('machowriter: exec load-command size mismatch: '
        + IntToStr(Head.Count) + ' vs '
        + IntToStr(MACH_HEADER_SIZE + EXEC_SIZEOFCMDS));

    { ---- payloads ---- }
    Head.PadTo(TextOff);
    Head.AppendBytes(FText);
    Head.PadTo(ConstOff);
    Head.AppendBytes(FConst);
    Head.PadTo(Integer(DataOff));
    Head.AppendBytes(FData);
    Head.PadTo(Integer(TvarsOff));
    Head.AppendBytes(FTvars);
    Head.PadTo(Integer(TdataOff));
    Head.AppendBytes(FTdata);
    Head.PadTo(Integer(LinkOff));
    Head.AppendBuf(Reb);
    Head.AppendBuf(Bind);
    Head.AppendBuf(SymT);
    Head.AppendBuf(StrT);
    Head.PadTo(Integer(SigOff));

    { ---- ad-hoc signature: a SuperBlob holding one CodeDirectory ----
      Everything BIG-endian.  The page hashes cover [0, SigOff) of the
      exact bytes emitted above — nothing may change after this point. }
    Unsigned := Head.AsString();
    Blob := Be32(CSMAGIC_EMBEDDED_SIGNATURE)
      + Be32(SigSize)
      + Be32(1)                                { blob count }
      + Be32(0)                                { CSSLOT_CODEDIRECTORY }
      + Be32(20);                              { its offset }
    Blob := Blob
      + Be32(CSMAGIC_CODEDIRECTORY)
      + Be32(SigSize - 20)                     { CD length }
      + Be32($20400)                           { version }
      + Be32(CS_ADHOC)
      + Be32(CD_HEADER_SIZE + Length(FIdent) + 1)   { hashOffset }
      + Be32(CD_HEADER_SIZE)                   { identOffset }
      + Be32(0)                                { nSpecialSlots }
      + Be32(NSlots)                           { nCodeSlots }
      + Be32(SigOff)                           { codeLimit }
      + Chr(32) + Chr(CS_HASHTYPE_SHA256)      { hashSize, hashType }
      + Chr(0) + Chr(CS_PAGE_BITS)             { platform, log2 page }
      + Be32(0)                                { spare2 }
      + Be32(0)                                { scatterOffset }
      + Be32(0)                                { teamOffset }
      + Be32(0)                                { spare3 }
      + Be64(0)                                { codeLimit64 }
      + Be64(0)                                { execSegBase }
      + Be64(TextSegFileSize)                  { execSegLimit }
      + Be64(CS_EXECSEG_MAIN_BINARY)           { execSegFlags }
      + FIdent + Chr(0);
    for I := 0 to NSlots - 1 do
    begin
      PageLen := 4096;
      if Int64(I) * 4096 + PageLen > SigOff then
        PageLen := Integer(SigOff - Int64(I) * 4096);
      Page := Copy(Unsigned, I * 4096, PageLen);
      Blob := Blob + Sha256(Page);
    end;

    Result := Unsigned + Blob;
  finally
    Head.Free();
    Reb.Free();
    Bind.Free();
    SymT.Free();
    StrT.Free();
  end;
end;

end.
