{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.linker.elf;

{ Internal ELF linker — section merging, symbol resolution, static
  and dynamic relocations, and executable emission (Phases A–C of
  docs/internal-linker-design.adoc).

  Phase A — TSectionMerger concatenates like-named allocatable
  sections from a set of parsed input objects, padding each
  contribution to its section's alignment, and records a placement
  (merged section + offset) for every input section.  Placements are
  the basis for symbol and relocation rebasing: a symbol's final
  offset is its object-local value plus its section's placement
  offset.

  SHT_NOBITS contributions advance the merged size without adding
  bytes; mixing NOBITS and PROGBITS under one name is rejected.
  Non-allocatable bookkeeping sections (symtab, strtab, rela,
  .note.GNU-stack, .comment) are skipped — the linker rebuilds those
  itself.  Non-alloc .opdf.* debug sections ARE kept: they must ride
  through into the final executable for the OPDF debugger.

  Phase B — TLinker in static mode takes a set of parsed objects,
  merges their sections, assigns virtual addresses at a fixed base
  (non-PIE ET_EXEC, no GOT/PLT, no dynamic linking), builds a global
  symbol table, resolves intra-program PC-relative relocations
  (R_X86_64_PC32, R_X86_64_PLT32), and writes a runnable executable.
  This is the standalone-program path of the design: a hand-written
  object that talks to the kernel through raw syscalls links and runs
  with Phase B alone.

  Phase C — TLinker in dynamic mode (SetDynamic(True)) produces a
  PIE (ET_DYN) executable linked against libc.  It generates GOT/PLT
  for undefined (libc) symbols, emits .dynamic/.dynsym/.dynstr/.hash
  sections, resolves R_X86_64_64 as R_X86_64_RELATIVE in .rela.dyn,
  handles R_X86_64_TPOFF32 for TLS, and merges any .init_array/
  .fini_array a linked object contributes.  The entry point is _start,
  which the runtime archive supplies (blaise_start_x86_64.s) and which
  calls __libc_start_main with main as the program's entry — no system
  Scrt1.o / crtbegin / crtend / crti / crtn is needed (issue #142). }

interface

uses
  SysUtils, Generics.Collections, streams, blaise.elfreader;

type
  ELinker = class(Exception);

  { Platform/architecture parameters for one link target.

    Phase B fills this for Linux x86-64 ELF only, but every value that
    differs across the roadmap targets (i386/x86-64, Linux/FreeBSD,
    later Windows) lives here rather than hard-coded in the emitter,
    so adding a target is a new record value plus, where the container
    differs (PE/Mach-O), a sibling writer behind the same TLinker
    symbol/relocation core.  See the "Platform Parameterisation"
    section of docs/internal-linker-design.adoc.

    The pointer width (Is64) drives ELF class, header sizes, address
    arithmetic and the relocation set; OSABI/BaseAddr/PageSize are the
    per-OS knobs.  Container format (ELF vs PE/Mach-O) is implied by
    which writer is invoked; only ELF targets are modelled here. }
  TLinkArch = (laX86_64, laI386);

  TLinkTarget = class
  public
    Arch:      TLinkArch;
    Is64:      Boolean;       { 64-bit pointers/addresses }
    OSABI:     Integer;       { EI_OSABI: 0 = SysV/Linux, 9 = FreeBSD }
    EMachine:  Integer;       { e_machine: EM_X86_64 / EM_386 }
    BaseAddr:  Int64;         { fixed load base for non-PIE ET_EXEC }
    PageSize:  Int64;         { segment alignment }
    constructor Create;
  end;

  { Linux x86-64 ELF, non-PIE ET_EXEC.  Caller frees. }
function LinuxX86_64Target: TLinkTarget;

  { FreeBSD x86-64 ELF.  Same System V AMD64 machine/arch as Linux; differs
    only in EI_OSABI (9 = FreeBSD).  Caller frees. }
function FreeBSDX86_64Target: TLinkTarget;

type
  { One output section accumulating contributions from input objects. }
  TMergedSection = class
  public
    Name:   string;
    ShType: Integer;
    Flags:  Int64;
    Align:  Int64;
    Data:   string;     { concatenated bytes; empty for SHT_NOBITS }
    Size:   Int64;      { total size including NOBITS reservations }
  end;

  { Where one input section landed: merged section + byte offset. }
  TSectionPlacement = class
  public
    ObjIndex: Integer;        { caller-assigned input object index }
    SecIndex: Integer;        { ELF section index within that object }
    Merged:   TMergedSection; { destination (not owned) }
    Offset:   Int64;          { offset of the contribution }
  end;

  TSectionMerger = class
  private
    FMerged:     TList<TMergedSection>;
    FPlacements: TList<TSectionPlacement>;
    function GetOrCreate(ASec: TRdSection): TMergedSection;
    function WantSection(ASec: TRdSection): Boolean;
  public
    constructor Create;
    destructor Destroy; override;

    { Merge every wanted section of AObj.  AObjIndex tags the
      placements; callers number their inputs sequentially. }
    procedure AddObject(AObjIndex: Integer; AObj: TElfObjectFile);

    function FindMerged(const AName: string): TMergedSection;
    { Placement of input object AObjIndex's section ASecIndex, or nil
      if that section was skipped. }
    function PlacementOf(AObjIndex, ASecIndex: Integer): TSectionPlacement;

    property Merged: TList<TMergedSection> read FMerged;
    property Placements: TList<TSectionPlacement> read FPlacements;
  end;

  { A resolved global symbol: name plus final virtual address.  Built
    after layout, so Addr is absolute for the chosen load base. }
  TLinkSymbol = class
  public
    Name:       string;
    Addr:       Int64;     { final virtual address (0 for weak-undef) }
    Defined:    Boolean;   { False = weak undefined resolved to 0 }
    IsFunc:     Boolean;
    IsWeakSlot: Boolean;   { defined only by a STB_WEAK symbol so far }
  end;

  { A pending runtime relocation for .rela.dyn (R_X86_64_RELATIVE). }
  TRelaDynEntry = class
  public
    VAddr:  Int64;   { virtual address to patch at load time }
    Addend: Int64;   { absolute target address (base-relative) }
  end;

  { A PLT/GOT slot for one external (libc) symbol. }
  TPltEntry = class
  public
    Name:       string;    { symbol name (e.g. 'write') }
    DynSymIdx:  Integer;   { index in .dynsym (set during BuildDynamic) }
    GotOffset:  Integer;   { byte offset within .got for this slot }
    PltOffset:  Integer;   { byte offset within .plt for this stub }
  end;

  { A non-PLT GOT slot for GOTPCREL references to locally-defined or
    weak-undefined symbols (e.g. __dso_handle, __gmon_start__). }
  TGotSlot = class
  public
    Name:      string;
    GotOffset: Integer;
    Value:     Int64;     { resolved absolute address (0 for weak-undef) }
  end;

  { Linker: merge → layout → resolve symbols → relocate → emit.

    In static mode (default): non-PIE ET_EXEC, PC-relative relocations
    only, no dynamic linker.

    In dynamic mode (SetDynamic(True)): PIE ET_DYN, GOT/PLT for
    external symbols, .dynamic/.dynsym/.dynstr/.hash, R_X86_64_64 →
    R_X86_64_RELATIVE, TLS (R_X86_64_TPOFF32), CRT startup objects.

    Lifecycle: SetDynamic, AddObject* for each input, then Link. }
  TLinker = class
  private
    FTarget:   TLinkTarget;
    FOwnTarget: Boolean;
    FObjects:  TList<TElfObjectFile>;
    FOwned:    TList<TElfObjectFile>;   { objects we must free }
    FMerger:   TSectionMerger;
    FSymbols:  TList<TLinkSymbol>;
    FSecAddr:  TList<TMergedSection>;   { merged sections, in layout order }
    FAddrOf:   TList<Int64>;            { virtual base addr per FSecAddr entry }
    FEntry:    Int64;
    FDynamic:  Boolean;

    { Phase C dynamic linking state }
    FPltEntries:  TList<TPltEntry>;     { external symbols needing PLT }
    FGotSlots:    TList<TGotSlot>;      { non-PLT GOT slots }
    FRelaDyn:     TList<TRelaDynEntry>; { R_X86_64_RELATIVE entries }
    FDynSymNames: TList<string>;        { .dynsym name list }
    FDynStrTab:   string;               { .dynstr contents }
    FDynSymTab:   string;               { .dynsym contents }
    FHashTab:     string;               { .hash (SysV) contents }
    FPltCode:     string;               { .plt section bytes }
    FGotData:     string;               { .got section bytes }
    FRelaPlt:     string;               { .rela.plt contents }
    FRelaDynData: string;               { .rela.dyn contents }
    FDynamicData: string;               { .dynamic section contents }
    FExtraNeeded: TList<string>;        { extra DT_NEEDED sonames beyond libc
                                          (e.g. libpthread.so.0, libm.so.6) —
                                          demand-driven from AddNeededLib }
    FExtraNeededDyn: string;            { pre-built DT_NEEDED,<off> pairs for the
                                          extra sonames; spliced into BOTH
                                          .dynamic builders after the libc entry }
    FInterpData:  string;               { .interp contents }
    FTlsSize:     Int64;                { total TLS block size }
    FTlsAlign:    Int64;                { TLS block alignment }
    FTlsFileSize: Int64;                { .tdata file size }

    { Section virtual addresses for dynamic linking (set during layout) }
    FInterpAddr:    Int64;
    FHashAddr:      Int64;
    FDynSymAddr:    Int64;
    FDynStrAddr:    Int64;
    FRelaDynAddr:   Int64;
    FRelaPltAddr:   Int64;
    FPltAddr:       Int64;
    FGotAddr:       Int64;
    FDynamicAddr:   Int64;
    FInitArrayAddr: Int64;
    FInitArraySize: Int64;
    FFiniArrayAddr: Int64;
    FFiniArraySize: Int64;
    FTlsAddr:       Int64;

    function MergedAddr(AMerged: TMergedSection): Int64;
    function SectionOfPlacement(AObjIdx, ASecIdx: Integer): TMergedSection;
    function PlacementBaseAddr(AObjIdx, ASecIdx: Integer): Int64;
    function FileOffset(AAddr: Int64): Integer;
    procedure PlaceSection(AM: TMergedSection; var AAddr: Int64);
    procedure LayoutSections;
    procedure BuildSymbols;
    function FindSymbol(const AName: string): TLinkSymbol;
    procedure AddSynthSymbol(const AName: string; AAddr: Int64);
    procedure DefineSynthSymbols;
    procedure ApplyRelocations;
    function ResolveSymbolAddr(AObj: TElfObjectFile; ASymIdx: Integer;
      const AContext: string): Int64;
    function EmitExecutable(AEntry: Int64): string;

    { Phase C methods }
    procedure CollectExternals;
    procedure CollectGotSlots;
    function CountRelativeRelocs: Integer;
    function FindPltEntry(const AName: string): TPltEntry;
    function FindOrCreateGotSlot(const AName: string): TGotSlot;
    procedure BuildDynamic;
    procedure LayoutDynamic;
    function EmitDynExecutable(AEntry: Int64): string;
  public
    constructor Create; overload;
    constructor Create(ATarget: TLinkTarget); overload;  { borrows target }
    destructor Destroy; override;

    { Enable dynamic linking mode (PIE, GOT/PLT, libc). }
    procedure SetDynamic(AEnabled: Boolean);
    { True when linking a dynamic (libc, DT_NEEDED) binary; False for a
      --static / freestanding link that has no .dynamic section. }
    function IsDynamic: Boolean;

    { Add a DT_NEEDED shared library beyond the implicit libc.so.6 (e.g.
      'libpthread.so.0', 'libm.so.6').  Demand-driven: the native driver calls
      this for each `external 'lib'` / codegen-required lib.  A no-op in static
      mode (no .dynamic section at all — a --static/freestanding binary needs no
      shared libraries).  Pass the SONAME the dynamic loader expects. }
    procedure AddNeededLib(const ASoname: string);
    { Pre-link query for the driver's AUTO link-mode decision: appends to
      ADest every STRONG undefined symbol that no loaded object defines and
      that the linker will not synthesise.  Returns the count appended.  An
      empty result means the loaded objects form a complete freestanding
      image; a non-empty result names the C symbols that would need libc /
      shared libraries.  Weak undefineds are excluded (they legally resolve
      to 0). }
    function CollectUnresolvedExternals(ADest: TStringList): Integer;

    { Add a parsed object the caller owns (not freed by the linker). }
    procedure AddObject(AObj: TElfObjectFile);
    { Add an object the linker takes ownership of and frees. }
    procedure AddOwnedObject(AObj: TElfObjectFile);

    { Add a system CRT object file by path (linker takes ownership). }
    procedure AddCrtObject(const APath: string);
    { Add all members of a static archive (linker takes ownership). }
    procedure AddArchive(const APath: string);

    { Merge, lay out, resolve, relocate and write an executable.
      In static mode: ET_EXEC; in dynamic mode: PIE ET_DYN.
      Raises ELinker on unresolved symbol, duplicate definition,
      or unsupported relocation. }
    procedure Link(const AEntryName, AOutputPath: string);

    { Same pipeline, returning the executable bytes instead of writing
      a file (used by tests for structural assertions). }
    function LinkToBytes(const AEntryName: string): string;

    { Address a global symbol resolved to (valid only after Link/
      LinkToBytes).  -1 if absent. }
    function AddrOfSymbol(const AName: string): Int64;

    { Merged section by name (e.g. '.text'), or nil — exposes the
      relocated bytes for tests/inspection.  Valid after Link. }
    function FindMerged(const AName: string): TMergedSection;
    function FindMergedText: TMergedSection;

    property Target: TLinkTarget read FTarget;
    property Dynamic: Boolean read FDynamic;
  end;

{ Mark a file user+group+other readable/executable (0755).  Used to
  make the linked output runnable. }
procedure MakeFileExecutable(const APath: string);

implementation

function LkAlignUp(AVal: Int64; AAlign: Int64): Int64;
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

function LkZeros(ACount: Int64): string;
var
  P: PChar;
  I: Integer;
begin
  if ACount <= 0 then
  begin
    Result := '';
    Exit;
  end;
  SetLength(Result, Integer(ACount));
  P := PChar(Result);
  for I := 0 to Integer(ACount) - 1 do
    P[I] := Chr(0);
end;

constructor TSectionMerger.Create;
begin
  inherited Create();
  FMerged := TList<TMergedSection>.Create();
  FPlacements := TList<TSectionPlacement>.Create();
end;

destructor TSectionMerger.Destroy;
var
  I: Integer;
begin
  for I := 0 to FMerged.Count - 1 do
    FMerged.Get(I).Free();
  FMerged.Free();
  for I := 0 to FPlacements.Count - 1 do
    FPlacements.Get(I).Free();
  FPlacements.Free();
  inherited Destroy();
end;

function TSectionMerger.WantSection(ASec: TRdSection): Boolean;
begin
  { Bookkeeping sections are rebuilt by the linker, never merged. }
  if (ASec.ShType = SHT_NULL) or (ASec.ShType = SHT_SYMTAB) or
     (ASec.ShType = SHT_STRTAB) or (ASec.ShType = SHT_RELA) then
  begin
    Result := False;
    Exit;
  end;
  if (ASec.Name = '.note.GNU-stack') or (ASec.Name = '.comment') then
  begin
    Result := False;
    Exit;
  end;
  { Allocatable sections always merge; non-alloc only for the OPDF
    debug pass-through. }
  if (ASec.Flags and SHF_ALLOC) <> 0 then
    Result := True
  else
    Result := Pos('.opdf', ASec.Name) = 0;
end;

function TSectionMerger.GetOrCreate(ASec: TRdSection): TMergedSection;
var
  I: Integer;
  M: TMergedSection;
begin
  for I := 0 to FMerged.Count - 1 do
  begin
    M := FMerged.Get(I);
    if M.Name = ASec.Name then
    begin
      if (M.ShType = SHT_NOBITS) <> (ASec.ShType = SHT_NOBITS) then
        raise ELinker.Create('section ' + ASec.Name
          + ': NOBITS and PROGBITS contributions cannot be merged');
      Result := M;
      Exit;
    end;
  end;
  M := TMergedSection.Create();
  M.Name := ASec.Name;
  M.ShType := ASec.ShType;
  M.Flags := ASec.Flags;
  M.Align := 1;
  M.Data := '';
  M.Size := 0;
  FMerged.Add(M);
  Result := M;
end;

procedure TSectionMerger.AddObject(AObjIndex: Integer; AObj: TElfObjectFile);
var
  I: Integer;
  Sec: TRdSection;
  M: TMergedSection;
  P: TSectionPlacement;
  Aligned: Int64;
  SecAlign: Int64;
begin
  for I := 0 to AObj.Sections.Count - 1 do
  begin
    Sec := AObj.Sections.Get(I);
    if not Self.WantSection(Sec) then Continue;

    M := Self.GetOrCreate(Sec);
    SecAlign := Sec.AddrAlign;
    if SecAlign < 1 then SecAlign := 1;
    if SecAlign > M.Align then M.Align := SecAlign;

    Aligned := LkAlignUp(M.Size, SecAlign);
    if M.ShType <> SHT_NOBITS then
    begin
      if Aligned > M.Size then
        M.Data := M.Data + LkZeros(Aligned - M.Size);
      M.Data := M.Data + Sec.Data;
    end;
    P := TSectionPlacement.Create();
    P.ObjIndex := AObjIndex;
    P.SecIndex := I;
    P.Merged := M;
    P.Offset := Aligned;
    FPlacements.Add(P);
    M.Size := Aligned + Sec.Size;
  end;
end;

function TSectionMerger.FindMerged(const AName: string): TMergedSection;
var
  I: Integer;
begin
  for I := 0 to FMerged.Count - 1 do
    if FMerged.Get(I).Name = AName then
    begin
      Result := FMerged.Get(I);
      Exit;
    end;
  Result := nil;
end;

function TSectionMerger.PlacementOf(AObjIndex,
  ASecIndex: Integer): TSectionPlacement;
var
  I: Integer;
  P: TSectionPlacement;
begin
  for I := 0 to FPlacements.Count - 1 do
  begin
    P := FPlacements.Get(I);
    if (P.ObjIndex = AObjIndex) and (P.SecIndex = ASecIndex) then
    begin
      Result := P;
      Exit;
    end;
  end;
  Result := nil;
end;

{ ---- ELF executable constants ----------------------------------------- }

const
  ET_EXEC = 2;
  ET_DYN  = 3;
  EM_386  = 3;

  EV_CURRENT = 1;

  ELFOSABI_SYSV    = 0;
  ELFOSABI_FREEBSD = 9;

  PT_LOAD    = 1;
  PT_DYNAMIC = 2;
  PT_INTERP  = 3;
  PT_TLS     = 7;
  PT_PHDR      = 6;
  PT_GNU_STACK = $6474E551;
  PT_GNU_RELRO = $6474E552;

  PF_X = 1;
  PF_W = 2;
  PF_R = 4;

  EI_NIDENT = 16;

  { Dynamic section tag values }
  DT_NULL       = 0;
  DT_NEEDED     = 1;
  DT_PLTRELSZ   = 2;
  DT_PLTGOT     = 3;
  DT_HASH       = 4;
  DT_STRTAB     = 5;
  DT_SYMTAB     = 6;
  DT_RELA       = 7;
  DT_RELASZ     = 8;
  DT_RELAENT    = 9;
  DT_STRSZ      = 10;
  DT_SYMENT     = 11;
  DT_INIT       = 12;
  DT_FINI       = 13;
  DT_INIT_ARRAY    = 25;
  DT_FINI_ARRAY    = 26;
  DT_INIT_ARRAYSZ  = 27;
  DT_FINI_ARRAYSZ  = 28;
  DT_FLAGS      = 30;
  DT_FLAGS_1    = $6FFFFFFB;
  DT_PLTREL     = 20;
  DT_JMPREL     = 23;
  DT_RELACOUNT  = $6FFFFFF9;
  DT_DEBUG      = 21;

  DF_1_PIE = $08000000;

  R_X86_64_RELATIVE   = 8;
  R_X86_64_JUMP_SLOT  = 7;
  R_X86_64_GLOB_DAT   = 6;

  PLT_ENTRY_SIZE = 16;
  PLT_HEADER_SIZE = 16;
  DYN_MAX_ENTRIES = 32;   { upper bound on .dynamic tag entries (base ~21 +
                            headroom for demand-driven extra DT_NEEDED libs) }

{ ---- Little-endian byte writers --------------------------------------- }

{ Blaise codegen does not support assigning to a string element through
  a var-string parameter (`ABuf[i] := c` on a var param), so every
  encoder here RETURNS the bytes and callers append them; fixed-offset
  patching is done with memcpy (a pointer write, which is fine). }

{ N-byte little-endian encoding of AVal. }
function LkLE(AVal: Int64; ANBytes: Integer): string;
var
  I: Integer;
  P: PChar;
begin
  SetLength(Result, ANBytes);
  P := PChar(Result);
  for I := 0 to ANBytes - 1 do
    P[I] := Chr(Integer((AVal shr (I * 8)) and $FF));
end;

{ Overwrite ABuf[AOff..] in place with ASrc's bytes (ABuf already large
  enough).  Blaise rejects `ABuf[i] := c` and `@ABuf[i]`, so writes go
  through a local PChar — the one idiom the native backend accepts for
  in-place string mutation (see ZeroBuf in uElfObject.pas). }
procedure LkCopyInto(var ABuf: string; AOff: Integer; const ASrc: string);
var
  P: PChar;
  I: Integer;
begin
  if Length(ASrc) = 0 then Exit;
  P := PChar(ABuf);
  for I := 0 to Length(ASrc) - 1 do
    P[AOff + I] := ASrc[I];
end;

{ Patch a 32-bit LE value at AOff. }
procedure LkPatch32(var ABuf: string; AOff: Integer; AVal: Int64);
begin
  LkCopyInto(ABuf, AOff, LkLE(AVal, 4));
end;

{ Patch a 64-bit LE value at AOff. }
procedure LkPatch64(var ABuf: string; AOff: Integer; AVal: Int64);
begin
  LkCopyInto(ABuf, AOff, LkLE(AVal, 8));
end;

{ Add a NUL-terminated string to a string table; return its offset. }
function LkAddStr(var ATab: string; const AStr: string): Integer;
begin
  if AStr = '' then
  begin
    Result := 0;
    Exit;
  end;
  Result := Length(ATab);
  ATab := ATab + AStr + Chr(0);
end;

{ ---- chmod binding ----------------------------------------------------- }

function _lk_chmod(APath: PChar; AMode: Integer): Integer;
  external name 'chmod';

procedure MakeFileExecutable(const APath: string);
begin
  { 0o755 = rwxr-xr-x }
  _lk_chmod(PChar(APath), 493);
end;

{ ---- TLinkTarget ------------------------------------------------------- }

constructor TLinkTarget.Create;
begin
  inherited Create();
  Arch := laX86_64;
  Is64 := True;
  OSABI := ELFOSABI_SYSV;
  EMachine := EM_X86_64;
  BaseAddr := $400000;
  PageSize := $1000;
end;

function LinuxX86_64Target: TLinkTarget;
begin
  Result := TLinkTarget.Create();
  { defaults already describe Linux x86-64 }
end;

function FreeBSDX86_64Target: TLinkTarget;
begin
  Result := TLinkTarget.Create();
  { Identical to Linux x86-64 except the OS/ABI byte in the ELF header. }
  Result.OSABI := ELFOSABI_FREEBSD;
end;

{ ---- TLinker ----------------------------------------------------------- }

constructor TLinker.Create;
begin
  Self.Create(LinuxX86_64Target());
  FOwnTarget := True;
end;

constructor TLinker.Create(ATarget: TLinkTarget);
begin
  inherited Create();
  FTarget := ATarget;
  FOwnTarget := False;
  FDynamic := False;
  FObjects := TList<TElfObjectFile>.Create();
  FOwned := TList<TElfObjectFile>.Create();
  FMerger := TSectionMerger.Create();
  FSymbols := TList<TLinkSymbol>.Create();
  FSecAddr := TList<TMergedSection>.Create();
  FAddrOf := TList<Int64>.Create();
  FEntry := 0;
  FPltEntries := TList<TPltEntry>.Create();
  FGotSlots := TList<TGotSlot>.Create();
  FRelaDyn := TList<TRelaDynEntry>.Create();
  FDynSymNames := TList<string>.Create();
  FDynStrTab := '';
  FDynSymTab := '';
  FHashTab := '';
  FPltCode := '';
  FGotData := '';
  FRelaPlt := '';
  FRelaDynData := '';
  FDynamicData := '';
  FExtraNeeded := TList<string>.Create();
  FExtraNeededDyn := '';
  FInterpData := '';
  FTlsSize := 0;
  FTlsAlign := 0;
  FTlsFileSize := 0;
end;

destructor TLinker.Destroy;
var
  I: Integer;
begin
  for I := 0 to FPltEntries.Count - 1 do
    FPltEntries.Get(I).Free();
  FPltEntries.Free();
  for I := 0 to FGotSlots.Count - 1 do
    FGotSlots.Get(I).Free();
  FGotSlots.Free();
  for I := 0 to FRelaDyn.Count - 1 do
    FRelaDyn.Get(I).Free();
  FRelaDyn.Free();
  FDynSymNames.Free();
  FExtraNeeded.Free();
  for I := 0 to FSymbols.Count - 1 do
    FSymbols.Get(I).Free();
  FSymbols.Free();
  FAddrOf.Free();
  FSecAddr.Free();           { sections owned by FMerger }
  FMerger.Free();
  for I := 0 to FOwned.Count - 1 do
    FOwned.Get(I).Free();
  FOwned.Free();
  FObjects.Free();
  if FOwnTarget then
    FTarget.Free();
  inherited Destroy();
end;

procedure TLinker.AddObject(AObj: TElfObjectFile);
begin
  FMerger.AddObject(FObjects.Count, AObj);
  FObjects.Add(AObj);
end;

procedure TLinker.AddOwnedObject(AObj: TElfObjectFile);
begin
  FOwned.Add(AObj);
  Self.AddObject(AObj);
end;

procedure TLinker.SetDynamic(AEnabled: Boolean);
begin
  FDynamic := AEnabled;
end;

function TLinker.IsDynamic: Boolean;
begin
  Result := FDynamic;
end;

procedure TLinker.AddNeededLib(const ASoname: string);
var
  I: Integer;
begin
  if ASoname = '' then Exit;
  { De-dup by value (small list; avoids a second DT_NEEDED for the same lib). }
  for I := 0 to FExtraNeeded.Count - 1 do
    if FExtraNeeded.Get(I) = ASoname then Exit;
  FExtraNeeded.Add(ASoname);
end;

procedure TLinker.AddCrtObject(const APath: string);
var
  Obj: TElfObjectFile;
begin
  Obj := ReadElfObjectFile(APath);
  Self.AddOwnedObject(Obj);
end;

procedure TLinker.AddArchive(const APath: string);
var
  Members: TList<TArchiveMember>;
  M: TArchiveMember;
  Obj: TElfObjectFile;
  I: Integer;
begin
  Members := TList<TArchiveMember>.Create();
  try
    ReadArchiveFile(APath, Members);
    for I := 0 to Members.Count - 1 do
    begin
      M := Members.Get(I);
      Obj := ParseElfObject(M.Data, APath + '(' + M.Name + ')');
      Self.AddOwnedObject(Obj);
    end;
  finally
    for I := 0 to Members.Count - 1 do
      Members.Get(I).Free();
    Members.Free();
  end;
end;

{ Virtual base address assigned to a merged section, or -1 if it was
  not laid out (e.g. a non-alloc debug section). }
function TLinker.MergedAddr(AMerged: TMergedSection): Int64;
var
  I: Integer;
begin
  for I := 0 to FSecAddr.Count - 1 do
    if FSecAddr.Get(I) = AMerged then
    begin
      Result := FAddrOf.Get(I);
      Exit;
    end;
  Result := -1;
end;

{ File offset for a virtual address in a laid-out section: the file
  image mirrors the virtual layout shifted down by the load base. }
function TLinker.FileOffset(AAddr: Int64): Integer;
begin
  Result := Integer(AAddr - FTarget.BaseAddr);
end;

function TLinker.SectionOfPlacement(AObjIdx,
  ASecIdx: Integer): TMergedSection;
var
  P: TSectionPlacement;
begin
  P := FMerger.PlacementOf(AObjIdx, ASecIdx);
  if P = nil then
    Result := nil
  else
    Result := P.Merged;
end;

function TLinker.PlacementBaseAddr(AObjIdx, ASecIdx: Integer): Int64;
var
  P: TSectionPlacement;
  Base: Int64;
begin
  P := FMerger.PlacementOf(AObjIdx, ASecIdx);
  if P = nil then
  begin
    Result := -1;
    Exit;
  end;
  Base := Self.MergedAddr(P.Merged);
  if Base < 0 then
  begin
    Result := -1;
    Exit;
  end;
  Result := Base + P.Offset;
end;

{ Assign virtual addresses.  Allocatable PROGBITS/NOBITS sections are
  grouped by permission into two loadable runs — executable (text +
  rodata) then writable (data + bss) — each starting on a fresh page.
  The first run begins after the ELF header + program headers, with
  p_vaddr congruent to p_offset modulo PageSize, as the loader
  requires.  Non-allocatable sections (.opdf.*) are not assigned an
  address; they ride through unmapped. }
procedure TLinker.PlaceSection(AM: TMergedSection; var AAddr: Int64);
var
  Al: Int64;
begin
  Al := AM.Align;
  if Al < 1 then Al := 1;
  AAddr := LkAlignUp(AAddr, Al);
  FSecAddr.Add(AM);
  FAddrOf.Add(AAddr);
  AAddr := AAddr + AM.Size;
end;

procedure TLinker.LayoutSections;
var
  I: Integer;
  M: TMergedSection;
  Addr: Int64;
  HdrBytes: Int64;
  IsAlloc, IsExec, IsWrite, HasTlsSec: Boolean;
begin
  { Program headers: PT_LOAD x2 (exec run, write run), plus PT_TLS when the
    program has any TLS section (.tdata/.tbss).  Reserve header space so the
    first section's file offset (= addr - base) clears the headers; otherwise
    the first section would overlap and overwrite the PT_TLS phdr.  Phdr = 56. }
  HasTlsSec := False;
  for I := 0 to FMerger.Merged.Count - 1 do
    if (FMerger.Merged.Get(I).Flags and SHF_TLS) <> 0 then HasTlsSec := True;
  if HasTlsSec then
    HdrBytes := ELF64_EHDR_SIZE + 3 * 56
  else
    HdrBytes := ELF64_EHDR_SIZE + 2 * 56;

  { Executable run: header bytes share its first page. }
  Addr := FTarget.BaseAddr + HdrBytes;
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsExec  := (M.Flags and SHF_EXECINSTR) <> 0;
    if IsAlloc and IsExec then Self.PlaceSection(M, Addr);
  end;
  { Read-only non-exec (rodata) joins the executable run. }
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsExec  := (M.Flags and SHF_EXECINSTR) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if IsAlloc and (not IsExec) and (not IsWrite) then
      Self.PlaceSection(M, Addr);
  end;

  { Writable run starts on a fresh page.  TLS sections (.tdata/.tbss, SHF_TLS)
    are placed separately below and must be skipped here. }
  Addr := LkAlignUp(Addr, FTarget.PageSize);
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if IsAlloc and IsWrite and (M.ShType <> SHT_NOBITS)
       and ((M.Flags and SHF_TLS) = 0) then
      Self.PlaceSection(M, Addr);
  end;
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if IsAlloc and IsWrite and (M.ShType = SHT_NOBITS)
       and ((M.Flags and SHF_TLS) = 0) then
      Self.PlaceSection(M, Addr);
  end;

  { TLS sections (.tdata then .tbss).  Mirror LayoutDynamic so a static ET_EXEC
    also gets a correct TLS block + FTlsAddr/FTlsSize for TPOFF relocations and
    the PT_TLS program header (which the freestanding _start reads to set up the
    thread pointer). }
  FTlsAddr := 0;
  FTlsSize := 0;
  FTlsAlign := 1;
  FTlsFileSize := 0;
  M := FMerger.FindMerged('.tdata');
  if M <> nil then
  begin
    Self.PlaceSection(M, Addr);
    FTlsAddr := Self.MergedAddr(M);
    FTlsFileSize := M.Size;
    FTlsSize := M.Size;
    if M.Align > FTlsAlign then FTlsAlign := M.Align;
  end;
  M := FMerger.FindMerged('.tbss');
  if M <> nil then
  begin
    Self.PlaceSection(M, Addr);
    if FTlsAddr = 0 then FTlsAddr := Self.MergedAddr(M);
    FTlsSize := FTlsSize + M.Size;
    if M.Align > FTlsAlign then FTlsAlign := M.Align;
  end;
  { Variant-II TLS: the thread pointer sits at the ALIGNED end of the block, and
    TPOFF32 is computed as (sym - FTlsAddr - FTlsSize).  The freestanding _start
    places TP at AlignUp(memsz, align); align FTlsSize to match so both agree even
    when the raw section sum is not a multiple of FTlsAlign (else every threadvar
    read is off by the alignment padding). }
  FTlsSize := LkAlignUp(FTlsSize, FTlsAlign);
end;

function TLinker.FindSymbol(const AName: string): TLinkSymbol;
var
  I: Integer;
begin
  for I := 0 to FSymbols.Count - 1 do
    if FSymbols.Get(I).Name = AName then
    begin
      Result := FSymbols.Get(I);
      Exit;
    end;
  Result := nil;
end;

procedure TLinker.AddSynthSymbol(const AName: string; AAddr: Int64);
var
  S: TLinkSymbol;
begin
  S := Self.FindSymbol(AName);
  if S <> nil then Exit;     { a real definition wins over the synth one }
  S := TLinkSymbol.Create();
  S.Name := AName;
  S.Addr := AAddr;
  S.Defined := True;
  S.IsFunc := False;
  FSymbols.Add(S);
end;

{ Build the global symbol table from every input object.  Only
  STB_GLOBAL / STB_WEAK symbols with a real definition (section index
  not SHN_UNDEF, not ABS/COMMON) are entered; a second STB_GLOBAL
  definition of the same name is a duplicate-symbol error, while a
  STB_GLOBAL overrides a previously seen STB_WEAK.  LayoutSections
  must have run so addresses are known. }
procedure TLinker.BuildSymbols;
var
  Oi, Si: Integer;
  Obj: TElfObjectFile;
  Sym: TRdSymbol;
  Existing: TLinkSymbol;
  NewSym: TLinkSymbol;
  Base: Int64;
begin
  for Oi := 0 to FObjects.Count - 1 do
  begin
    Obj := FObjects.Get(Oi);
    for Si := 0 to Obj.Symbols.Count - 1 do
    begin
      Sym := Obj.Symbols.Get(Si);
      if (Sym.Bind <> STB_GLOBAL) and (Sym.Bind <> STB_WEAK) then Continue;
      if Sym.Name = '' then Continue;
      if Sym.Shndx = SHN_UNDEF then Continue;
      if (Sym.Shndx = SHN_ABS) or (Sym.Shndx = SHN_COMMON) then Continue;

      Base := Self.PlacementBaseAddr(Oi, Sym.Shndx);
      if Base < 0 then Continue;   { defined in a section we did not lay out }

      Existing := Self.FindSymbol(Sym.Name);
      if Existing <> nil then
      begin
        { Strong over weak → replace.  Both strong → first definition wins
          (matches ld behaviour when archive members re-export a symbol the
          main object already provides). }
        if (Sym.Bind = STB_GLOBAL) and Existing.Defined
           and (not Existing.IsWeakSlot) then
          Continue;
        if Sym.Bind = STB_GLOBAL then
        begin
          Existing.Addr := Base + Sym.Value;
          Existing.Defined := True;
          Existing.IsFunc := Sym.SymType = STT_FUNC;
          Existing.IsWeakSlot := False;
        end;
        Continue;
      end;

      NewSym := TLinkSymbol.Create();
      NewSym.Name := Sym.Name;
      NewSym.Addr := Base + Sym.Value;
      NewSym.Defined := True;
      NewSym.IsFunc := Sym.SymType = STT_FUNC;
      NewSym.IsWeakSlot := Sym.Bind = STB_WEAK;
      FSymbols.Add(NewSym);
    end;
  end;
end;

{ Linker-synthesised symbols.  Phase B has no GOT, so
  _GLOBAL_OFFSET_TABLE_ resolves to the writable run base (harmless
  for the standalone path that does not touch it); __bss_start/_edata/
  _end mark the data/bss boundaries; __TMC_END__ resolves to _end.
  Only defined if not already provided by an input object. }
procedure TLinker.DefineSynthSymbols;
var
  I: Integer;
  M: TMergedSection;
  DataEnd, BssStart, BssEnd, WritableBase: Int64;
  A: Int64;
begin
  DataEnd := FTarget.BaseAddr;
  BssStart := -1;
  BssEnd := FTarget.BaseAddr;
  WritableBase := -1;

  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if (M.Flags and SHF_WRITE) <> 0 then
    begin
      if WritableBase < 0 then WritableBase := A;
      if M.ShType = SHT_NOBITS then
      begin
        if BssStart < 0 then BssStart := A;
        if A + M.Size > BssEnd then BssEnd := A + M.Size;
      end
      else
      begin
        if A + M.Size > DataEnd then DataEnd := A + M.Size;
        if A + M.Size > BssEnd then BssEnd := A + M.Size;
      end;
    end;
  end;
  if BssStart < 0 then BssStart := DataEnd;
  if WritableBase < 0 then WritableBase := DataEnd;

  Self.AddSynthSymbol('_GLOBAL_OFFSET_TABLE_', WritableBase);
  Self.AddSynthSymbol('__bss_start', BssStart);
  Self.AddSynthSymbol('_edata', DataEnd);
  Self.AddSynthSymbol('_end', BssEnd);
  Self.AddSynthSymbol('__TMC_END__', BssEnd);
end;

{ ---- Phase C: dynamic linking ----------------------------------------- }

{ Scan all objects for undefined symbols that have no definition in
  any object.  Each such symbol becomes a PLT entry (for function
  calls via the dynamic linker).  Does not require BuildSymbols —
  scans raw object symbol tables directly. }
procedure TLinker.CollectExternals;
var
  Oi, Si, Di, Dsi: Integer;
  Obj, DefObj: TElfObjectFile;
  Sym, DefSym: TRdSymbol;
  PE: TPltEntry;
  Seen: TDictionary<string, Boolean>;
  Dummy: Boolean;
  Found: Boolean;
begin
  Seen := TDictionary<string, Boolean>.Create();
  try
    for Oi := 0 to FObjects.Count - 1 do
    begin
      Obj := FObjects.Get(Oi);
      for Si := 0 to Obj.Symbols.Count - 1 do
      begin
        Sym := Obj.Symbols.Get(Si);
        if Sym.Shndx <> SHN_UNDEF then Continue;
        if Sym.Name = '' then Continue;
        if Sym.Bind = STB_LOCAL then Continue;
        if Seen.TryGetValue(Sym.Name, Dummy) then Continue;
        Seen.Add(Sym.Name, True);

        { Skip linker-synthesised symbols. }
        if (Sym.Name = '_GLOBAL_OFFSET_TABLE_') or
           (Sym.Name = '__bss_start') or
           (Sym.Name = '_edata') or
           (Sym.Name = '_end') or
           (Sym.Name = '__TMC_END__') then
          Continue;

        { Check if any object defines this symbol. }
        Found := False;
        for Di := 0 to FObjects.Count - 1 do
        begin
          DefObj := FObjects.Get(Di);
          for Dsi := 0 to DefObj.Symbols.Count - 1 do
          begin
            DefSym := DefObj.Symbols.Get(Dsi);
            if (DefSym.Name = Sym.Name) and (DefSym.Shndx <> SHN_UNDEF)
               and (DefSym.Shndx <> SHN_COMMON) then
            begin
              Found := True;
              Break;
            end;
          end;
          if Found then Break;
        end;
        if Found then Continue;

        { Weak undefined symbols without a definition resolve to 0;
          they do not need a PLT entry. }
        if Sym.Bind = STB_WEAK then
          Continue;

        PE := TPltEntry.Create();
        PE.Name := Sym.Name;
        PE.DynSymIdx := 0;
        PE.GotOffset := 0;
        PE.PltOffset := 0;
        FPltEntries.Add(PE);
      end;
    end;
  finally
    Seen.Free();
  end;
end;

function TLinker.CollectUnresolvedExternals(ADest: TStringList): Integer;
var
  Oi, Si, Di, Dsi: Integer;
  Obj, DefObj: TElfObjectFile;
  Sym, DefSym: TRdSymbol;
  Seen: TDictionary<string, Boolean>;
  Dummy: Boolean;
  Found: Boolean;
begin
  Result := 0;
  Seen := TDictionary<string, Boolean>.Create();
  try
    for Oi := 0 to FObjects.Count - 1 do
    begin
      Obj := FObjects.Get(Oi);
      for Si := 0 to Obj.Symbols.Count - 1 do
      begin
        Sym := Obj.Symbols.Get(Si);
        if Sym.Shndx <> SHN_UNDEF then Continue;
        if Sym.Name = '' then Continue;
        if Sym.Bind = STB_LOCAL then Continue;
        if Sym.Bind = STB_WEAK then Continue;   { weak undefined -> 0, legal }
        if Seen.TryGetValue(Sym.Name, Dummy) then Continue;
        Seen.Add(Sym.Name, True);

        { Skip linker-synthesised symbols (same set CollectExternals skips). }
        if (Sym.Name = '_GLOBAL_OFFSET_TABLE_') or
           (Sym.Name = '__bss_start') or
           (Sym.Name = '_edata') or
           (Sym.Name = '_end') or
           (Sym.Name = '__TMC_END__') then
          Continue;

        Found := False;
        for Di := 0 to FObjects.Count - 1 do
        begin
          DefObj := FObjects.Get(Di);
          for Dsi := 0 to DefObj.Symbols.Count - 1 do
          begin
            DefSym := DefObj.Symbols.Get(Dsi);
            if (DefSym.Name = Sym.Name) and (DefSym.Shndx <> SHN_UNDEF) and
               (DefSym.Bind <> STB_LOCAL) then
            begin
              Found := True;
              Break;
            end;
          end;
          if Found then Break;
        end;
        if not Found then
        begin
          ADest.Add(Sym.Name);
          Result := Result + 1;
        end;
      end;
    end;
  finally
    Seen.Free();
  end;
end;

function TLinker.FindPltEntry(const AName: string): TPltEntry;
var
  I: Integer;
begin
  for I := 0 to FPltEntries.Count - 1 do
    if FPltEntries.Get(I).Name = AName then
    begin
      Result := FPltEntries.Get(I);
      Exit;
    end;
  Result := nil;
end;

function TLinker.FindOrCreateGotSlot(const AName: string): TGotSlot;
var
  I: Integer;
  GS: TGotSlot;
begin
  for I := 0 to FGotSlots.Count - 1 do
    if FGotSlots.Get(I).Name = AName then
    begin
      Result := FGotSlots.Get(I);
      Exit;
    end;
  GS := TGotSlot.Create();
  GS.Name := AName;
  GS.GotOffset := 0;
  GS.Value := 0;
  FGotSlots.Add(GS);
  Result := GS;
end;

{ Scan all objects for GOTPCREL/REX_GOTPCRELX relocations against symbols
  that are NOT external (no PLT entry).  Each such symbol needs a GOT
  slot so GOTPCREL can resolve through it.  Called after CollectExternals. }
procedure TLinker.CollectGotSlots;
var
  Oi, Ri: Integer;
  Obj: TElfObjectFile;
  Rel: TRdReloc;
  Sym: TRdSymbol;
begin
  for Oi := 0 to FObjects.Count - 1 do
  begin
    Obj := FObjects.Get(Oi);
    for Ri := 0 to Obj.Relocs.Count - 1 do
    begin
      Rel := Obj.Relocs.Get(Ri);
      if (Rel.RelocType <> R_X86_64_GOTPCREL) and
         (Rel.RelocType <> R_X86_64_GOTPCRELX) and
         (Rel.RelocType <> R_X86_64_REX_GOTPCRELX) then Continue;
      Sym := Obj.Symbols.Get(Rel.SymIndex);
      if Sym.Name = '' then Continue;
      if Self.FindPltEntry(Sym.Name) <> nil then Continue;
      Self.FindOrCreateGotSlot(Sym.Name);
    end;
  end;
end;

{ Count how many R_X86_64_64 relocations exist across all objects
  (each becomes an R_X86_64_RELATIVE in .rela.dyn), plus non-PLT GOT
  slots that will need RELATIVE entries.  Used to reserve space for
  .rela.dyn before layout. }
function TLinker.CountRelativeRelocs: Integer;
var
  Oi, Ri: Integer;
  Obj: TElfObjectFile;
  Rel: TRdReloc;
begin
  Result := 0;
  for Oi := 0 to FObjects.Count - 1 do
  begin
    Obj := FObjects.Get(Oi);
    for Ri := 0 to Obj.Relocs.Count - 1 do
    begin
      Rel := Obj.Relocs.Get(Ri);
      if Rel.RelocType = R_X86_64_64 then
        Result := Result + 1;
    end;
  end;
  Result := Result + FGotSlots.Count;
end;

{ Build the dynamic linking tables: .dynsym, .dynstr, .hash, .plt,
  .got, .rela.plt, .rela.dyn, .dynamic, .interp.

  The PLT uses the x86-64 lazy binding scheme:
    PLT[0] — resolver stub (pushes linkmap, jumps to _dl_runtime_resolve)
    PLT[n] — per-symbol stub (pushes reloc index, jumps to PLT[0])
  Each PLT entry has a corresponding GOT entry initialised to point
  at the second instruction of the PLT stub (push + jmp).

  GOT layout:
    GOT[0] = .dynamic address (filled by ld.so)
    GOT[1] = linkmap (filled by ld.so)
    GOT[2] = _dl_runtime_resolve (filled by ld.so)
    GOT[3..] = per-PLT-entry slots

  This method is called after BuildSymbols and CollectExternals but
  before LayoutDynamic, so it builds the data blobs that LayoutDynamic
  then places at virtual addresses. }
procedure TLinker.BuildDynamic;
var
  I: Integer;
  PE: TPltEntry;
  NameOff: Integer;
  SymInfo: Int64;
  NumBuckets, Bkt: Integer;
  HashChain: TList<Integer>;
  HashBuckets: TList<Integer>;
  H, J: Integer;
  RInfo: Int64;
begin
  FInterpData := '/lib64/ld-linux-x86-64.so.2' + Chr(0);

  { .dynstr: NUL byte at [0], then 'libc.so.6' at [1]. }
  FDynStrTab := Chr(0);
  LkAddStr(FDynStrTab, 'libc.so.6');

  { Extra DT_NEEDED sonames (demand-driven via AddNeededLib, e.g. libpthread /
    libm).  Add each to .dynstr and pre-build the DT_NEEDED,<off> pairs spliced
    into both .dynamic builders after the libc entry.  Empty when no extra lib
    was requested (the common case), so .dynamic is byte-identical to before —
    the fixpoint is unperturbed for programs that need only libc. }
  FExtraNeededDyn := '';
  for I := 0 to FExtraNeeded.Count - 1 do
    FExtraNeededDyn := FExtraNeededDyn +
      LkLE(DT_NEEDED, 8) + LkLE(LkAddStr(FDynStrTab, FExtraNeeded.Get(I)), 8);

  { .dynsym: entry 0 is NULL, then one entry per external symbol. }
  FDynSymTab := LkZeros(ELF64_SYM_SIZE);
  FDynSymNames.Add('');

  for I := 0 to FPltEntries.Count - 1 do
  begin
    PE := FPltEntries.Get(I);
    PE.DynSymIdx := I + 1;
    NameOff := LkAddStr(FDynStrTab, PE.Name);
    FDynSymNames.Add(PE.Name);
    SymInfo := (Int64(STB_GLOBAL) shl 4) or Int64(STT_FUNC);
    FDynSymTab := FDynSymTab + LkLE(NameOff, 4);
    FDynSymTab := FDynSymTab + Chr(Integer(SymInfo) and $FF);
    FDynSymTab := FDynSymTab + Chr(0);
    FDynSymTab := FDynSymTab + LkLE(SHN_UNDEF, 2);
    FDynSymTab := FDynSymTab + LkLE(0, 8);
    FDynSymTab := FDynSymTab + LkLE(0, 8);
  end;

  { SysV .hash: nbucket, nchain, buckets[], chains[].
    Simple hash: sum of bytes mod nbucket. }
  NumBuckets := FPltEntries.Count;
  if NumBuckets < 1 then NumBuckets := 1;

  HashBuckets := TList<Integer>.Create();
  HashChain := TList<Integer>.Create();
  try
    for I := 0 to NumBuckets - 1 do
      HashBuckets.Add(0);
    for I := 0 to FDynSymNames.Count - 1 do
      HashChain.Add(0);

    for I := 1 to FDynSymNames.Count - 1 do
    begin
      H := 0;
      for J := 0 to Length(FDynSymNames.Get(I)) - 1 do
        H := ((H shl 4) + Ord(FDynSymNames.Get(I)[J])) and $0FFFFFFF;
      Bkt := H mod NumBuckets;
      HashChain.SetItem(I, HashBuckets.Get(Bkt));
      HashBuckets.SetItem(Bkt, I);
    end;

    FHashTab := LkLE(NumBuckets, 4) + LkLE(FDynSymNames.Count, 4);
    for I := 0 to NumBuckets - 1 do
      FHashTab := FHashTab + LkLE(HashBuckets.Get(I), 4);
    for I := 0 to FDynSymNames.Count - 1 do
      FHashTab := FHashTab + LkLE(HashChain.Get(I), 4);
  finally
    HashBuckets.Free();
    HashChain.Free();
  end;

  { .got: 3 reserved entries + 1 per PLT entry + 1 per non-PLT GOT slot. }
  FGotData := LkZeros(8 * (3 + FPltEntries.Count + FGotSlots.Count));
  for I := 0 to FGotSlots.Count - 1 do
    FGotSlots.Get(I).GotOffset := (3 + FPltEntries.Count + I) * 8;

  { .plt: header + one stub per entry.
    PLT header (16 bytes):
      pushq GOT[1](%rip)
      jmpq  *GOT[2](%rip)
      nop; nop; nop; nop
    PLT[n] (16 bytes):
      jmpq  *GOT[n+3](%rip)
      pushq $reloc_index
      jmpq  PLT[0]

    The RIP-relative offsets are computed in LayoutDynamic after
    addresses are assigned; we emit placeholder bytes here. }
  FPltCode := LkZeros(PLT_HEADER_SIZE);
  for I := 0 to FPltEntries.Count - 1 do
  begin
    PE := FPltEntries.Get(I);
    PE.PltOffset := PLT_HEADER_SIZE + I * PLT_ENTRY_SIZE;
    PE.GotOffset := (3 + I) * 8;
    FPltCode := FPltCode + LkZeros(PLT_ENTRY_SIZE);
  end;

  { .rela.plt: one JUMP_SLOT per PLT entry. }
  FRelaPlt := '';
  for I := 0 to FPltEntries.Count - 1 do
  begin
    PE := FPltEntries.Get(I);
    FRelaPlt := FRelaPlt + LkLE(0, 8);
    RInfo := (Int64(PE.DynSymIdx) shl 32) or R_X86_64_JUMP_SLOT;
    FRelaPlt := FRelaPlt + LkLE(RInfo, 8);
    FRelaPlt := FRelaPlt + LkLE(0, 8);
  end;

  { .rela.dyn: R_X86_64_RELATIVE entries are collected during
    ApplyRelocations (each R_X86_64_64 becomes one).  We serialise
    them in LayoutDynamic after addresses are known.

    Also add _GLOBAL_OFFSET_TABLE_ weak references. }

  { .dynamic: built in LayoutDynamic once addresses are assigned. }
end;

{ Assign virtual addresses for a PIE (ET_DYN) executable.

  Layout (page-aligned segments, 0-based for PIE):
    PHDR + read-only headers   — PT_LOAD R
    .interp                     — (inside read-only run)
    .hash, .dynsym, .dynstr    — (inside read-only run)
    .rela.dyn, .rela.plt       — (inside read-only run)
    .text (+ merged .text)     — PT_LOAD R+X
    .plt                       — (inside executable run)
    .rodata                    — PT_LOAD R (after text)
    .init_array, .fini_array   — PT_LOAD R+W (RELRO)
    .dynamic                   — (inside RELRO)
    .got                       — (inside RELRO)
    .data                      — PT_LOAD R+W
    .bss, .tbss                — (after data, NOBITS)

  For simplicity the initial implementation uses a flat layout:
  all read-only stuff on one page, executable on next, writable on next.
  Addresses start at 0 (PIE). }
procedure TLinker.LayoutDynamic;
var
  I, J: Integer;
  M: TMergedSection;
  Addr: Int64;
  PhdrCount: Integer;
  HdrBytes: Int64;
  IsAlloc, IsExec, IsWrite: Boolean;
  PE: TPltEntry;
  GotRelOff: Int64;
  PltRelOff: Int64;
begin
  { Phase C program-header count: PT_PHDR, PT_INTERP, PT_LOAD x4,
    PT_DYNAMIC, PT_TLS, PT_GNU_STACK, PT_GNU_RELRO = 11 max.
    Always reserve space for PT_TLS — real Blaise programs use
    threadvars (SHF_TLS sections), so the header slot is almost
    always needed. }
  PhdrCount := 11;
  HdrBytes := ELF64_EHDR_SIZE + Int64(PhdrCount) * 56;

  { Read-only run: starts after headers. }
  Addr := LkAlignUp(HdrBytes, 16);

  { .interp }
  FInterpAddr := Addr;
  Addr := Addr + Length(FInterpData);
  Addr := LkAlignUp(Addr, 8);

  { .hash }
  FHashAddr := Addr;
  Addr := Addr + Length(FHashTab);
  Addr := LkAlignUp(Addr, 8);

  { .dynsym }
  FDynSymAddr := Addr;
  Addr := Addr + Length(FDynSymTab);
  Addr := LkAlignUp(Addr, 8);

  { .dynstr }
  FDynStrAddr := Addr;
  Addr := Addr + Length(FDynStrTab);
  Addr := LkAlignUp(Addr, 8);

  { .rela.dyn — reserve space for the pre-counted RELATIVE entries.
    The actual data is serialised after ApplyRelocations has collected
    the entries.  The count may overestimate (not every GOT slot ends
    up needing a RELATIVE), but that is safe — the final data will be
    <= the reservation and gets padded or fit within the reserved area. }
  FRelaDynAddr := Addr;
  FRelaDynData := '';
  Addr := Addr + Int64(Self.CountRelativeRelocs()) * ELF64_RELA_SIZE;
  Addr := LkAlignUp(Addr, 8);

  { .rela.plt }
  FRelaPltAddr := Addr;
  Addr := Addr + Length(FRelaPlt);
  Addr := LkAlignUp(Addr, 8);

  { Read-only merged sections (.rodata, .eh_frame, .note.*, etc.)
    go into the same RO segment as the linker metadata above. }
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsExec  := (M.Flags and SHF_EXECINSTR) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if IsAlloc and (not IsExec) and (not IsWrite) and
       ((M.Flags and SHF_TLS) = 0) then
      Self.PlaceSection(M, Addr);
  end;

  { Align to page for executable run. }
  Addr := LkAlignUp(Addr, FTarget.PageSize);

  { Executable sections: .text, .init, .fini. }
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsExec  := (M.Flags and SHF_EXECINSTR) <> 0;
    if IsAlloc and IsExec then
      Self.PlaceSection(M, Addr);
  end;

  { .plt }
  Addr := LkAlignUp(Addr, 16);
  FPltAddr := Addr;
  Addr := Addr + Length(FPltCode);

  { Writable / RELRO run — align to page. }
  Addr := LkAlignUp(Addr, FTarget.PageSize);

  { .init_array }
  FInitArrayAddr := Addr;
  FInitArraySize := 0;
  M := FMerger.FindMerged('.init_array');
  if M <> nil then
  begin
    Self.PlaceSection(M, Addr);
    FInitArraySize := M.Size;
  end;

  { .fini_array }
  FFiniArrayAddr := Addr;
  FFiniArraySize := 0;
  M := FMerger.FindMerged('.fini_array');
  if M <> nil then
  begin
    Self.PlaceSection(M, Addr);
    FFiniArraySize := M.Size;
  end;

  { .dynamic — reserve space for up to DYN_MAX_ENTRIES entries (16 bytes each). }
  Addr := LkAlignUp(Addr, 8);
  FDynamicAddr := Addr;
  Addr := Addr + DYN_MAX_ENTRIES * 16;

  { .got }
  Addr := LkAlignUp(Addr, 8);
  FGotAddr := Addr;
  Addr := Addr + Length(FGotData);

  { GOT[0] = .dynamic address; patched by ld.so but we set it. }
  LkPatch64(FGotData, 0, FDynamicAddr);

  { Fix up PLT stubs now that addresses are known. }
  if FPltEntries.Count > 0 then
  begin
    { PLT header: pushq GOT[1](%rip), jmpq *GOT[2](%rip), nop4 }
    GotRelOff := (FGotAddr + 8) - (FPltAddr + 6);
    LkCopyInto(FPltCode, 0, Chr($FF) + Chr($35));
    LkPatch32(FPltCode, 2, GotRelOff);
    GotRelOff := (FGotAddr + 16) - (FPltAddr + 12);
    LkCopyInto(FPltCode, 6, Chr($FF) + Chr($25));
    LkPatch32(FPltCode, 8, GotRelOff);
    LkCopyInto(FPltCode, 12, Chr($0F) + Chr($1F) + Chr($40) + Chr(0));

    for I := 0 to FPltEntries.Count - 1 do
    begin
      PE := FPltEntries.Get(I);
      J := PE.PltOffset;
      { jmpq *GOT[n+3](%rip) }
      GotRelOff := (FGotAddr + PE.GotOffset) - (FPltAddr + J + 6);
      LkCopyInto(FPltCode, J, Chr($FF) + Chr($25));
      LkPatch32(FPltCode, J + 2, GotRelOff);
      { pushq $reloc_index }
      LkCopyInto(FPltCode, J + 6, Chr($68));
      LkPatch32(FPltCode, J + 7, I);
      { jmpq PLT[0] }
      PltRelOff := -(J + 16);
      LkCopyInto(FPltCode, J + 11, Chr($E9));
      LkPatch32(FPltCode, J + 12, PltRelOff);

      { Initialise GOT[n+3] to PLT[n]+6 (pushq instruction). }
      LkPatch64(FGotData, PE.GotOffset, FPltAddr + J + 6);

      { Fix up .rela.plt entry with GOT address. }
      LkPatch64(FRelaPlt, I * ELF64_RELA_SIZE, FGotAddr + PE.GotOffset);

      { Register the PLT address as a resolved symbol so
        R_X86_64_PLT32 relocations against this name resolve. }
      Self.AddSynthSymbol(PE.Name, FPltAddr + J);
    end;
  end;

  { Non-PLT GOT slot values are filled in LinkToBytes after BuildSymbols. }

  { _GLOBAL_OFFSET_TABLE_ → .got base }
  Self.AddSynthSymbol('_GLOBAL_OFFSET_TABLE_', FGotAddr);

  { Writable data sections. }
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if not IsAlloc then Continue;
    if not IsWrite then Continue;
    if (M.Flags and SHF_TLS) <> 0 then Continue;
    if M.Name = '.init_array' then Continue;
    if M.Name = '.fini_array' then Continue;
    if M.ShType <> SHT_NOBITS then
      Self.PlaceSection(M, Addr);
  end;
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if not IsAlloc then Continue;
    if not IsWrite then Continue;
    if (M.Flags and SHF_TLS) <> 0 then Continue;
    if M.Name = '.init_array' then Continue;
    if M.Name = '.fini_array' then Continue;
    if M.ShType = SHT_NOBITS then
      Self.PlaceSection(M, Addr);
  end;

  { TLS sections (.tdata, .tbss).  PlaceSection aligns AAddr before
    recording — FTlsAddr must be the aligned start, not the pre-align
    cursor, so we read it back from MergedAddr after the first place. }
  FTlsAddr := 0;
  FTlsSize := 0;
  FTlsAlign := 1;
  FTlsFileSize := 0;
  M := FMerger.FindMerged('.tdata');
  if M <> nil then
  begin
    Self.PlaceSection(M, Addr);
    FTlsAddr := Self.MergedAddr(M);
    FTlsFileSize := M.Size;
    FTlsSize := M.Size;
    if M.Align > FTlsAlign then FTlsAlign := M.Align;
  end;
  M := FMerger.FindMerged('.tbss');
  if M <> nil then
  begin
    Self.PlaceSection(M, Addr);
    if FTlsAddr = 0 then FTlsAddr := Self.MergedAddr(M);
    FTlsSize := FTlsSize + M.Size;
    if M.Align > FTlsAlign then FTlsAlign := M.Align;
  end;
  { TP sits at the aligned end of the TLS block (variant II); align FTlsSize so
    TPOFF32 (sym - FTlsAddr - FTlsSize) matches the aligned thread pointer. }
  FTlsSize := LkAlignUp(FTlsSize, FTlsAlign);

  { Build .dynamic section.  'libc.so.6' is at offset 1 in .dynstr.  Any extra
    DT_NEEDED libs (libpthread/libm) follow immediately — empty string when none. }
  FDynamicData := '';
  FDynamicData := FDynamicData + LkLE(DT_NEEDED, 8) + LkLE(1, 8);
  FDynamicData := FDynamicData + FExtraNeededDyn;
  FDynamicData := FDynamicData + LkLE(DT_HASH, 8) + LkLE(FHashAddr, 8);
  FDynamicData := FDynamicData + LkLE(DT_STRTAB, 8) + LkLE(FDynStrAddr, 8);
  FDynamicData := FDynamicData + LkLE(DT_SYMTAB, 8) + LkLE(FDynSymAddr, 8);
  FDynamicData := FDynamicData + LkLE(DT_STRSZ, 8) + LkLE(Length(FDynStrTab), 8);
  FDynamicData := FDynamicData + LkLE(DT_SYMENT, 8) + LkLE(ELF64_SYM_SIZE, 8);
  FDynamicData := FDynamicData + LkLE(DT_PLTGOT, 8) + LkLE(FGotAddr, 8);
  FDynamicData := FDynamicData + LkLE(DT_PLTRELSZ, 8) + LkLE(Length(FRelaPlt), 8);
  FDynamicData := FDynamicData + LkLE(DT_PLTREL, 8) + LkLE(DT_RELA, 8);
  FDynamicData := FDynamicData + LkLE(DT_JMPREL, 8) + LkLE(FRelaPltAddr, 8);
  if Length(FRelaDynData) > 0 then
  begin
    FDynamicData := FDynamicData + LkLE(DT_RELA, 8) + LkLE(FRelaDynAddr, 8);
    FDynamicData := FDynamicData + LkLE(DT_RELASZ, 8) + LkLE(Length(FRelaDynData), 8);
    FDynamicData := FDynamicData + LkLE(DT_RELAENT, 8) + LkLE(ELF64_RELA_SIZE, 8);
    FDynamicData := FDynamicData + LkLE(DT_RELACOUNT, 8) + LkLE(FRelaDyn.Count, 8);
  end;
  if FInitArraySize > 0 then
  begin
    FDynamicData := FDynamicData + LkLE(DT_INIT_ARRAY, 8) + LkLE(FInitArrayAddr, 8);
    FDynamicData := FDynamicData + LkLE(DT_INIT_ARRAYSZ, 8) + LkLE(FInitArraySize, 8);
  end;
  if FFiniArraySize > 0 then
  begin
    FDynamicData := FDynamicData + LkLE(DT_FINI_ARRAY, 8) + LkLE(FFiniArrayAddr, 8);
    FDynamicData := FDynamicData + LkLE(DT_FINI_ARRAYSZ, 8) + LkLE(FFiniArraySize, 8);
  end;
  FDynamicData := FDynamicData + LkLE(DT_DEBUG, 8) + LkLE(0, 8);
  FDynamicData := FDynamicData + LkLE(DT_FLAGS_1, 8) + LkLE(DF_1_PIE, 8);
  FDynamicData := FDynamicData + LkLE(DT_NULL, 8) + LkLE(0, 8);
  { Pad to the reserved size. }
  if Length(FDynamicData) < DYN_MAX_ENTRIES * 16 then
    FDynamicData := FDynamicData + LkZeros(DYN_MAX_ENTRIES * 16 - Length(FDynamicData));
end;

{ Resolve a relocation's symbol to its final virtual address.  A
  reference to a STB_LOCAL section/symbol resolves through that
  object's own section placement; a global reference goes through the
  resolved symbol table.  A strong undefined symbol with no definition
  is a link error; a weak undefined resolves to 0. }
function TLinker.ResolveSymbolAddr(AObj: TElfObjectFile; ASymIdx: Integer;
  const AContext: string): Int64;
var
  Sym: TRdSymbol;
  Oi: Integer;
  Base: Int64;
  G: TLinkSymbol;
begin
  if (ASymIdx < 0) or (ASymIdx >= AObj.Symbols.Count) then
    raise ELinker.Create(AContext + ': relocation symbol index out of range');
  Sym := AObj.Symbols.Get(ASymIdx);

  { Locally-defined symbol: resolve via its section — but for globals
    that are defined in multiple objects, use the canonical address from
    the global symbol table so every reference resolves to the same copy.
    BuildSymbols uses first-definition-wins for duplicate STB_GLOBAL
    symbols, so the global table holds the single canonical address. }
  if (Sym.Shndx <> SHN_UNDEF) and (Sym.Shndx <> SHN_ABS)
     and (Sym.Shndx <> SHN_COMMON) then
  begin
    if Sym.Bind = STB_GLOBAL then
    begin
      G := Self.FindSymbol(Sym.Name);
      if (G <> nil) and G.Defined then
      begin
        Result := G.Addr;
        Exit;
      end;
    end;
    Oi := FObjects.IndexOf(AObj);
    Base := Self.PlacementBaseAddr(Oi, Sym.Shndx);
    if Base < 0 then
      raise ELinker.Create(AContext + ': symbol ' + Sym.Name
        + ' defined in an unlaid-out section');
    Result := Base + Sym.Value;
    Exit;
  end;

  if Sym.Shndx = SHN_ABS then
  begin
    Result := Sym.Value;
    Exit;
  end;

  { Undefined here — look up the global table. }
  G := Self.FindSymbol(Sym.Name);
  if (G <> nil) and G.Defined and (not G.IsWeakSlot) then
  begin
    Result := G.Addr;
    Exit;
  end;
  if (G <> nil) and G.Defined then   { resolved weak slot }
  begin
    Result := G.Addr;
    Exit;
  end;
  { Weak undefined resolves to 0; strong undefined is an error. }
  if Sym.Bind = STB_WEAK then
  begin
    Result := 0;
    Exit;
  end;
  raise ELinker.Create('undefined reference to `' + Sym.Name + '''');
end;

{ Patch the merged section bytes for every relocation.  Static mode
  (Phase B) supports PC-relative and absolute forms (every symbol has a
  final link-time address in a non-PIE ET_EXEC); dynamic mode (Phase C)
  additionally handles GOT-relative and emits RELATIVE fixups. }
procedure TLinker.ApplyRelocations;
var
  Oi, Ri: Integer;
  Obj: TElfObjectFile;
  Rel: TRdReloc;
  M: TMergedSection;
  P: TSectionPlacement;
  PAddr: Int64;
  PFileOff: Integer;
  S, Val: Int64;
  Ctx: string;
  Sym: TRdSymbol;
  PE: TPltEntry;
  GS: TGotSlot;
  RE: TRelaDynEntry;
  GotSlotAddr: Int64;
begin
  for Oi := 0 to FObjects.Count - 1 do
  begin
    Obj := FObjects.Get(Oi);
    for Ri := 0 to Obj.Relocs.Count - 1 do
    begin
      Rel := Obj.Relocs.Get(Ri);
      P := FMerger.PlacementOf(Oi, Rel.TargetSection);
      if P = nil then Continue;
      M := P.Merged;
      if Self.MergedAddr(M) < 0 then Continue;

      Ctx := Obj.SourceName;
      PFileOff := Integer(P.Offset + Rel.Offset);
      PAddr := Self.MergedAddr(M) + P.Offset + Rel.Offset;

      Sym := Obj.Symbols.Get(Rel.SymIndex);

      case Rel.RelocType of
        R_X86_64_NONE: ;

        R_X86_64_PC32, R_X86_64_PLT32:
          begin
            S := Self.ResolveSymbolAddr(Obj, Rel.SymIndex, Ctx);
            Val := S + Rel.Addend - PAddr;
            if M.ShType = SHT_NOBITS then
              raise ELinker.Create(Ctx
                + ': relocation into a NOBITS section');
            LkPatch32(M.Data, PFileOff, Val and $FFFFFFFF);
          end;

        R_X86_64_64:
          begin
            S := Self.ResolveSymbolAddr(Obj, Rel.SymIndex, Ctx);
            Val := S + Rel.Addend;
            if M.ShType = SHT_NOBITS then
              raise ELinker.Create(Ctx
                + ': relocation into a NOBITS section');
            { Patch the absolute 64-bit target address.  In a non-PIE ET_EXEC
              (static mode) every symbol has a fixed load address, so this value
              is final and needs no run-time fixup.  In PIE/dynamic mode the
              image base is unknown until load, so the same slot also gets an
              R_X86_64_RELATIVE entry in .rela.dyn for the loader to re-add the
              base. }
            LkPatch64(M.Data, PFileOff, Val);
            if FDynamic then
            begin
              RE := TRelaDynEntry.Create();
              RE.VAddr := PAddr;
              RE.Addend := Val;
              FRelaDyn.Add(RE);
            end;
          end;

        R_X86_64_32, R_X86_64_32S:
          begin
            S := Self.ResolveSymbolAddr(Obj, Rel.SymIndex, Ctx);
            Val := S + Rel.Addend;
            if M.ShType = SHT_NOBITS then
              raise ELinker.Create(Ctx
                + ': relocation into a NOBITS section');
            { Resolvable in BOTH modes: static ET_EXEC links at a fixed base
              (0x400000) where every mapped address fits in 32 bits, and in
              PIE mode the patched value is the unslid link-time address
              (the OPDF reader applies the run-time slide itself; code never
              uses abs32 in PIE objects).  Range-check like GNU ld does:
              R_X86_64_32 must fit zero-extended, R_X86_64_32S sign-extended. }
            if Rel.RelocType = R_X86_64_32 then
            begin
              if (Val < 0) or (Val > $FFFFFFFF) then
                raise ELinker.Create(Ctx
                  + ': R_X86_64_32 overflow against ' + Sym.Name);
            end
            else
            begin
              if (Val < -2147483648) or (Val > 2147483647) then
                raise ELinker.Create(Ctx
                  + ': R_X86_64_32S overflow against ' + Sym.Name);
            end;
            LkPatch32(M.Data, PFileOff, Val and $FFFFFFFF);
          end;

        R_X86_64_GOTPCREL, R_X86_64_GOTPCRELX, R_X86_64_REX_GOTPCRELX:
          begin
            if not FDynamic then
              raise ELinker.Create(Ctx
                + ': GOT relocation needs dynamic linking');
            PE := Self.FindPltEntry(Sym.Name);
            if PE <> nil then
              GotSlotAddr := FGotAddr + PE.GotOffset
            else
            begin
              GS := Self.FindOrCreateGotSlot(Sym.Name);
              GotSlotAddr := FGotAddr + GS.GotOffset;
            end;
            Val := GotSlotAddr + Rel.Addend - PAddr;
            LkPatch32(M.Data, PFileOff, Val and $FFFFFFFF);
          end;

        R_X86_64_TPOFF32:
          { Local-Exec TLS: the offset from the thread pointer (which points at
            the END of the static TLS block) down to this threadvar.  This is the
            STATIC TLS model — it is resolvable at link time in both static and
            PIE/dynamic executables (the threadvar's position within the initial
            TLS block is fixed at link), so it needs no dynamic relocation. }
          begin
            S := Self.ResolveSymbolAddr(Obj, Rel.SymIndex, Ctx);
            Val := S - FTlsAddr + Rel.Addend - FTlsSize;
            LkPatch32(M.Data, PFileOff, Val and $FFFFFFFF);
          end;
      else
        raise ELinker.Create(Ctx + ': unsupported relocation type '
          + IntToStr(Rel.RelocType));
      end;
    end;
  end;
end;

{ Build the ET_EXEC byte image: ELF header, two PT_LOAD program
  headers (exec run, write run), section payloads at file offsets that
  match (vaddr - base), then a minimal section-header table so
  readelf/objdump can inspect the result. }
function TLinker.EmitExecutable(AEntry: Int64): string;
var
  Buf: string;
  I: Integer;
  M: TMergedSection;
  A: Int64;
  Base, PageSz: Int64;
  ExecLo, ExecHi, WriteLo, WriteMemHi, WriteFileHi: Int64;
  PhOff, FirstSecFileEnd: Integer;
  ShStr: string;
  ShStrOff: TList<Integer>;
  SecCount, ShTabOff: Integer;
  NamePos: Integer;
begin
  Base := FTarget.BaseAddr;
  PageSz := FTarget.PageSize;

  { Compute the address extents of each run. }
  ExecLo := -1; ExecHi := Base;
  WriteLo := -1; WriteMemHi := Base; WriteFileHi := Base;
  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if (M.Flags and SHF_WRITE) <> 0 then
    begin
      if WriteLo < 0 then WriteLo := A;
      if A + M.Size > WriteMemHi then WriteMemHi := A + M.Size;
      if (M.ShType <> SHT_NOBITS) and (A + M.Size > WriteFileHi) then
        WriteFileHi := A + M.Size;
    end
    else
    begin
      if ExecLo < 0 then ExecLo := A;
      if A + M.Size > ExecHi then ExecHi := A + M.Size;
    end;
  end;
  if ExecLo < 0 then ExecLo := Base + ELF64_EHDR_SIZE;
  if WriteLo < 0 then begin WriteLo := ExecHi; WriteFileHi := ExecHi;
    WriteMemHi := ExecHi; end;

  { ---- ELF header + program headers (assembled front-to-back) ---- }
  PhOff := ELF64_EHDR_SIZE;
  Buf := '';
  Buf := Buf + Chr($7F) + 'ELF';            { e_ident magic }
  Buf := Buf + Chr(ELFCLASS64) + Chr(ELFDATA2LSB) + Chr(EV_CURRENT)
             + Chr(FTarget.OSABI);
  Buf := Buf + LkZeros(8);                   { e_ident[8..15] }
  Buf := Buf + LkLE(ET_EXEC, 2);             { e_type }
  Buf := Buf + LkLE(FTarget.EMachine, 2);    { e_machine }
  Buf := Buf + LkLE(EV_CURRENT, 4);          { e_version }
  Buf := Buf + LkLE(AEntry, 8);              { e_entry }
  Buf := Buf + LkLE(PhOff, 8);               { e_phoff }
  Buf := Buf + LkLE(0, 8);                   { e_shoff (patched later) }
  Buf := Buf + LkLE(0, 4);                   { e_flags }
  Buf := Buf + LkLE(ELF64_EHDR_SIZE, 2);     { e_ehsize }
  Buf := Buf + LkLE(56, 2);                  { e_phentsize }
  { 2 PT_LOAD, plus PT_TLS when the program has threadvars (so the static
    _start can set up the thread pointer from the PT_TLS init image). }
  if FTlsSize > 0 then
    Buf := Buf + LkLE(3, 2)                  { e_phnum }
  else
    Buf := Buf + LkLE(2, 2);
  Buf := Buf + LkLE(ELF64_SHDR_SIZE, 2);     { e_shentsize }
  Buf := Buf + LkLE(0, 2);                   { e_shnum (patched later) }
  Buf := Buf + LkLE(0, 2);                   { e_shstrndx (patched later) }

  { PT_LOAD #0 — executable run; covers the headers (file offset 0). }
  Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_X, 4);
  Buf := Buf + LkLE(0, 8);                    { p_offset }
  Buf := Buf + LkLE(Base, 8);                 { p_vaddr }
  Buf := Buf + LkLE(Base, 8);                 { p_paddr }
  Buf := Buf + LkLE(Self.FileOffset(ExecHi), 8);    { p_filesz }
  Buf := Buf + LkLE(ExecHi - Base, 8);        { p_memsz }
  Buf := Buf + LkLE(PageSz, 8);               { p_align }

  { PT_LOAD #1 — writable run (data + bss). }
  Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_W, 4);
  Buf := Buf + LkLE(Self.FileOffset(WriteLo), 8);   { p_offset }
  Buf := Buf + LkLE(WriteLo, 8);              { p_vaddr }
  Buf := Buf + LkLE(WriteLo, 8);              { p_paddr }
  Buf := Buf + LkLE(WriteFileHi - WriteLo, 8);{ p_filesz }
  Buf := Buf + LkLE(WriteMemHi - WriteLo, 8); { p_memsz }
  Buf := Buf + LkLE(PageSz, 8);               { p_align }

  { PT_TLS — the initial TLS image (.tdata file bytes + .tbss zero size).  The
    static _start reads this segment to build the per-thread block and set %fs.
    Only emitted when the program has threadvars (e_phnum reflects this). }
  if FTlsSize > 0 then
  begin
    Buf := Buf + LkLE(PT_TLS, 4) + LkLE(PF_R, 4);
    Buf := Buf + LkLE(Self.FileOffset(FTlsAddr), 8);  { p_offset }
    Buf := Buf + LkLE(FTlsAddr, 8);           { p_vaddr }
    Buf := Buf + LkLE(FTlsAddr, 8);           { p_paddr }
    Buf := Buf + LkLE(FTlsFileSize, 8);       { p_filesz (.tdata) }
    Buf := Buf + LkLE(FTlsSize, 8);           { p_memsz (.tdata + .tbss) }
    Buf := Buf + LkLE(FTlsAlign, 8);          { p_align }
  end;

  { Pad headers out to the first section's file offset (the exec run's
    first byte sits at Self.FileOffset(ExecLo)). }
  if Length(Buf) < Self.FileOffset(ExecLo) then
    Buf := Buf + LkZeros(Self.FileOffset(ExecLo) - Length(Buf));

  { ---- section payloads ---- }
  { Grow the image to the end of writable file data, then splat every
    PROGBITS section at its file offset (= vaddr - Base). }
  FirstSecFileEnd := Self.FileOffset(WriteFileHi);
  if Length(Buf) < FirstSecFileEnd then
    Buf := Buf + LkZeros(FirstSecFileEnd - Length(Buf));
  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if M.ShType = SHT_NOBITS then Continue;
    if Length(M.Data) > 0 then
      LkCopyInto(Buf, Self.FileOffset(A), M.Data);
  end;

  { ---- section header table (for tooling) ---- }
  { .shstrtab: NULL, one name per laid-out section, then .shstrtab. }
  ShStr := Chr(0);
  ShStrOff := TList<Integer>.Create();
  try
    for I := 0 to FSecAddr.Count - 1 do
    begin
      ShStrOff.Add(Length(ShStr));
      ShStr := ShStr + FSecAddr.Get(I).Name + Chr(0);
    end;
    NamePos := Length(ShStr);
    ShStr := ShStr + '.shstrtab' + Chr(0);

    ShTabOff := Length(Buf);
    Buf := Buf + ShStr;

    SecCount := FSecAddr.Count + 2;     { NULL + sections + .shstrtab }
    while (Length(Buf) and 7) <> 0 do Buf := Buf + Chr(0);

    { Patch e_shoff / e_shnum / e_shstrndx now that the table offset is
      known.  e_shoff @40, e_shnum @60, e_shstrndx @62. }
    LkCopyInto(Buf, 40, LkLE(Length(Buf), 8));
    LkCopyInto(Buf, 60, LkLE(SecCount, 2));
    LkCopyInto(Buf, 62, LkLE(SecCount - 1, 2));

    { SHT_NULL header. }
    Buf := Buf + LkZeros(ELF64_SHDR_SIZE);

    for I := 0 to FSecAddr.Count - 1 do
    begin
      M := FSecAddr.Get(I);
      A := FAddrOf.Get(I);
      Buf := Buf + LkLE(ShStrOff.Get(I), 4);    { sh_name }
      Buf := Buf + LkLE(M.ShType, 4);           { sh_type }
      Buf := Buf + LkLE(M.Flags, 8);            { sh_flags }
      Buf := Buf + LkLE(A, 8);                  { sh_addr }
      if M.ShType = SHT_NOBITS then
        Buf := Buf + LkLE(Self.FileOffset(WriteFileHi), 8)   { sh_offset }
      else
        Buf := Buf + LkLE(Self.FileOffset(A), 8);
      Buf := Buf + LkLE(M.Size, 8);             { sh_size }
      Buf := Buf + LkLE(0, 4);                  { sh_link }
      Buf := Buf + LkLE(0, 4);                  { sh_info }
      Buf := Buf + LkLE(M.Align, 8);            { sh_addralign }
      Buf := Buf + LkLE(0, 8);                  { sh_entsize }
    end;

    { .shstrtab section header. }
    Buf := Buf + LkLE(NamePos, 4);
    Buf := Buf + LkLE(SHT_STRTAB, 4);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(ShTabOff, 8);
    Buf := Buf + LkLE(Length(ShStr), 8);
    Buf := Buf + LkLE(0, 4);
    Buf := Buf + LkLE(0, 4);
    Buf := Buf + LkLE(1, 8);
    Buf := Buf + LkLE(0, 8);
  finally
    ShStrOff.Free();
  end;

  Result := Buf;
end;

{ Emit a PIE (ET_DYN) executable with program headers for dynamic
  linking: PT_PHDR, PT_INTERP, PT_LOAD (read-only, executable,
  RELRO+writable, data+bss), PT_DYNAMIC, PT_TLS, PT_GNU_STACK,
  PT_GNU_RELRO.  File layout mirrors virtual layout at base 0. }
function TLinker.EmitDynExecutable(AEntry: Int64): string;
var
  Buf: string;
  I: Integer;
  M: TMergedSection;
  A: Int64;
  PhdrCount: Integer;
  HdrBytes: Int64;
  RoLo, RoHi: Int64;
  ExecLo, ExecHi: Int64;
  RelroLo, RelroHi: Int64;
  DataLo, DataMemHi, DataFileHi: Int64;
  ShStr: string;
  ShStrOff: TList<Integer>;
  SecCount, ShTabOff: Integer;
  NamePos: Integer;
  PhIdx: Integer;
  HasTls: Boolean;
begin
  { Compute extents for each loadable segment.
    RO: headers + linker metadata + .rodata + .eh_frame etc.
    Exec: .text + .init + .fini + .plt
    RELRO: .init_array + .fini_array + .dynamic + .got
    Data: .data + .bss }
  RoLo := 0;
  RoHi := 0;
  ExecLo := -1; ExecHi := 0;
  RelroLo := -1; RelroHi := 0;
  DataLo := -1; DataMemHi := 0; DataFileHi := 0;

  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if (M.Flags and SHF_ALLOC) = 0 then Continue;

    if (M.Flags and SHF_EXECINSTR) <> 0 then
    begin
      if ExecLo < 0 then ExecLo := A;
      if A + M.Size > ExecHi then ExecHi := A + M.Size;
    end
    else if (M.Flags and SHF_WRITE) <> 0 then
    begin
      if (M.Name = '.init_array') or (M.Name = '.fini_array') then
      begin
        if RelroLo < 0 then RelroLo := A;
        if A + M.Size > RelroHi then RelroHi := A + M.Size;
      end
      else if (M.Flags and SHF_TLS) = 0 then
      begin
        if DataLo < 0 then DataLo := A;
        if A + M.Size > DataMemHi then DataMemHi := A + M.Size;
        if (M.ShType <> SHT_NOBITS) and (A + M.Size > DataFileHi) then
          DataFileHi := A + M.Size;
      end;
    end
    else
    begin
      if A + M.Size > RoHi then RoHi := A + M.Size;
    end;
  end;

  { Linker-generated read-only sections extend RoHi. }
  if FRelaPltAddr + Length(FRelaPlt) > RoHi then
    RoHi := FRelaPltAddr + Length(FRelaPlt);
  if FRelaDynAddr + Int64(Self.CountRelativeRelocs()) * ELF64_RELA_SIZE > RoHi then
    RoHi := FRelaDynAddr + Int64(Self.CountRelativeRelocs()) * ELF64_RELA_SIZE;

  { .plt is part of the executable segment. }
  if Length(FPltCode) > 0 then
  begin
    if (ExecLo < 0) or (FPltAddr < ExecLo) then ExecLo := FPltAddr;
    if FPltAddr + Length(FPltCode) > ExecHi then
      ExecHi := FPltAddr + Length(FPltCode);
  end;

  { .dynamic and .got are in the RELRO segment. }
  if RelroLo < 0 then RelroLo := FDynamicAddr;
  if FDynamicAddr < RelroLo then RelroLo := FDynamicAddr;
  if FDynamicAddr + Length(FDynamicData) > RelroHi then
    RelroHi := FDynamicAddr + Length(FDynamicData);
  if FGotAddr + Length(FGotData) > RelroHi then
    RelroHi := FGotAddr + Length(FGotData);

  if ExecLo < 0 then ExecLo := 0;
  if DataLo < 0 then begin DataLo := RelroHi; DataFileHi := RelroHi;
    DataMemHi := RelroHi; end;

  HasTls := FTlsSize > 0;

  { Must match the PhdrCount used by LayoutDynamic so addresses agree. }
  PhdrCount := 11;
  HdrBytes := ELF64_EHDR_SIZE + Int64(PhdrCount) * 56;

  { The read-only segment starts at file/vaddr 0, covering the ELF
    header, program headers, and linker-generated read-only sections
    (.interp, .hash, .dynsym, .dynstr, .rela.dyn, .rela.plt).
    Then rodata sections follow. }

  { ---- ELF header ---- }
  Buf := '';
  Buf := Buf + Chr($7F) + 'ELF';
  Buf := Buf + Chr(ELFCLASS64) + Chr(ELFDATA2LSB) + Chr(EV_CURRENT)
             + Chr(FTarget.OSABI);
  Buf := Buf + LkZeros(8);
  Buf := Buf + LkLE(ET_DYN, 2);
  Buf := Buf + LkLE(FTarget.EMachine, 2);
  Buf := Buf + LkLE(EV_CURRENT, 4);
  Buf := Buf + LkLE(AEntry, 8);
  Buf := Buf + LkLE(ELF64_EHDR_SIZE, 8);   { e_phoff }
  Buf := Buf + LkLE(0, 8);                  { e_shoff (patched later) }
  Buf := Buf + LkLE(0, 4);
  Buf := Buf + LkLE(ELF64_EHDR_SIZE, 2);
  Buf := Buf + LkLE(56, 2);
  Buf := Buf + LkLE(PhdrCount, 2);
  Buf := Buf + LkLE(ELF64_SHDR_SIZE, 2);
  Buf := Buf + LkLE(0, 2);  { e_shnum patched later }
  Buf := Buf + LkLE(0, 2);  { e_shstrndx patched later }

  { ---- Program headers ---- }
  PhIdx := 0;

  { PT_PHDR — describes the program-header table itself. }
  Buf := Buf + LkLE(PT_PHDR, 4) + LkLE(PF_R, 4);
  Buf := Buf + LkLE(ELF64_EHDR_SIZE, 8);
  Buf := Buf + LkLE(ELF64_EHDR_SIZE, 8);
  Buf := Buf + LkLE(ELF64_EHDR_SIZE, 8);
  Buf := Buf + LkLE(Int64(PhdrCount) * 56, 8);
  Buf := Buf + LkLE(Int64(PhdrCount) * 56, 8);
  Buf := Buf + LkLE(8, 8);
  PhIdx := PhIdx + 1;

  { PT_INTERP }
  Buf := Buf + LkLE(PT_INTERP, 4) + LkLE(PF_R, 4);
  Buf := Buf + LkLE(FInterpAddr, 8);
  Buf := Buf + LkLE(FInterpAddr, 8);
  Buf := Buf + LkLE(FInterpAddr, 8);
  Buf := Buf + LkLE(Length(FInterpData), 8);
  Buf := Buf + LkLE(Length(FInterpData), 8);
  Buf := Buf + LkLE(1, 8);
  PhIdx := PhIdx + 1;

  { PT_LOAD #0 — read-only: headers + .interp + .hash + .dynsym +
    .dynstr + .rela.dyn + .rela.plt + .rodata sections.
    Covers file offset 0 to end of read-only range. }
  Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R, 4);
  Buf := Buf + LkLE(0, 8);         { p_offset }
  Buf := Buf + LkLE(0, 8);         { p_vaddr }
  Buf := Buf + LkLE(0, 8);         { p_paddr }
  Buf := Buf + LkLE(RoHi, 8);      { p_filesz }
  Buf := Buf + LkLE(RoHi, 8);      { p_memsz }
  Buf := Buf + LkLE(FTarget.PageSize, 8);
  PhIdx := PhIdx + 1;

  { PT_LOAD #1 — executable: .text + .plt (+ .init/.fini if present). }
  Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_X, 4);
  Buf := Buf + LkLE(ExecLo, 8);
  Buf := Buf + LkLE(ExecLo, 8);
  Buf := Buf + LkLE(ExecLo, 8);
  Buf := Buf + LkLE(ExecHi - ExecLo, 8);
  Buf := Buf + LkLE(ExecHi - ExecLo, 8);
  Buf := Buf + LkLE(FTarget.PageSize, 8);
  PhIdx := PhIdx + 1;

  { PT_LOAD #2 — RELRO + writable: .init_array, .fini_array,
    .dynamic, .got. }
  Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_W, 4);
  Buf := Buf + LkLE(RelroLo, 8);
  Buf := Buf + LkLE(RelroLo, 8);
  Buf := Buf + LkLE(RelroLo, 8);
  Buf := Buf + LkLE(RelroHi - RelroLo, 8);
  Buf := Buf + LkLE(RelroHi - RelroLo, 8);
  Buf := Buf + LkLE(FTarget.PageSize, 8);
  PhIdx := PhIdx + 1;

  { PT_LOAD #3 — writable data + bss. }
  if DataLo < DataMemHi then
  begin
    Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_W, 4);
    Buf := Buf + LkLE(DataLo, 8);
    Buf := Buf + LkLE(DataLo, 8);
    Buf := Buf + LkLE(DataLo, 8);
    Buf := Buf + LkLE(DataFileHi - DataLo, 8);
    Buf := Buf + LkLE(DataMemHi - DataLo, 8);
    Buf := Buf + LkLE(FTarget.PageSize, 8);
  end
  else
  begin
    Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_W, 4);
    Buf := Buf + LkLE(RelroHi, 8);
    Buf := Buf + LkLE(RelroHi, 8);
    Buf := Buf + LkLE(RelroHi, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(FTarget.PageSize, 8);
  end;
  PhIdx := PhIdx + 1;

  { PT_DYNAMIC }
  Buf := Buf + LkLE(PT_DYNAMIC, 4) + LkLE(PF_R or PF_W, 4);
  Buf := Buf + LkLE(FDynamicAddr, 8);
  Buf := Buf + LkLE(FDynamicAddr, 8);
  Buf := Buf + LkLE(FDynamicAddr, 8);
  Buf := Buf + LkLE(Length(FDynamicData), 8);
  Buf := Buf + LkLE(Length(FDynamicData), 8);
  Buf := Buf + LkLE(8, 8);
  PhIdx := PhIdx + 1;

  { PT_TLS — always emitted (slot reserved by LayoutDynamic); zero-sized
    when there are no TLS sections. }
  Buf := Buf + LkLE(PT_TLS, 4) + LkLE(PF_R, 4);
  if HasTls then
  begin
    Buf := Buf + LkLE(FTlsAddr, 8);
    Buf := Buf + LkLE(FTlsAddr, 8);
    Buf := Buf + LkLE(FTlsAddr, 8);
    Buf := Buf + LkLE(FTlsFileSize, 8);
    Buf := Buf + LkLE(FTlsSize, 8);
    Buf := Buf + LkLE(FTlsAlign, 8);
  end
  else
  begin
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(8, 8);
  end;
  PhIdx := PhIdx + 1;

  { PT_GNU_STACK — non-executable stack. }
  Buf := Buf + LkLE(PT_GNU_STACK, 4) + LkLE(PF_R or PF_W, 4);
  Buf := Buf + LkLE(0, 8);
  Buf := Buf + LkLE(0, 8);
  Buf := Buf + LkLE(0, 8);
  Buf := Buf + LkLE(0, 8);
  Buf := Buf + LkLE(0, 8);
  Buf := Buf + LkLE(16, 8);
  PhIdx := PhIdx + 1;

  { PT_GNU_RELRO — marks the RELRO region for mprotect after relocation. }
  Buf := Buf + LkLE(PT_GNU_RELRO, 4) + LkLE(PF_R, 4);
  Buf := Buf + LkLE(RelroLo, 8);
  Buf := Buf + LkLE(RelroLo, 8);
  Buf := Buf + LkLE(RelroLo, 8);
  Buf := Buf + LkLE(RelroHi - RelroLo, 8);
  Buf := Buf + LkLE(RelroHi - RelroLo, 8);
  Buf := Buf + LkLE(1, 8);
  PhIdx := PhIdx + 1;

  { ---- Section payloads ---- }
  { Grow the image to cover all file-backed data, then copy everything
    into place.  File offset = virtual address for a PIE at base 0. }
  { Find the highest file-backed address. }
  A := RoHi;
  if ExecHi > A then A := ExecHi;
  if RelroHi > A then A := RelroHi;
  if DataFileHi > A then A := DataFileHi;
  if Length(Buf) < Integer(A) then
    Buf := Buf + LkZeros(Integer(A) - Length(Buf));

  { Copy linker-generated sections. }
  LkCopyInto(Buf, Integer(FInterpAddr), FInterpData);
  LkCopyInto(Buf, Integer(FHashAddr), FHashTab);
  LkCopyInto(Buf, Integer(FDynSymAddr), FDynSymTab);
  LkCopyInto(Buf, Integer(FDynStrAddr), FDynStrTab);
  if Length(FRelaDynData) > 0 then
    LkCopyInto(Buf, Integer(FRelaDynAddr), FRelaDynData);
  if Length(FRelaPlt) > 0 then
    LkCopyInto(Buf, Integer(FRelaPltAddr), FRelaPlt);
  if Length(FPltCode) > 0 then
    LkCopyInto(Buf, Integer(FPltAddr), FPltCode);
  LkCopyInto(Buf, Integer(FDynamicAddr), FDynamicData);
  LkCopyInto(Buf, Integer(FGotAddr), FGotData);

  { Copy merged sections at their virtual addresses. }
  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if M.ShType = SHT_NOBITS then Continue;
    if Length(M.Data) > 0 then
      LkCopyInto(Buf, Integer(A), M.Data);
  end;

  { ---- Section header table (for readelf / objdump) ---- }
  ShStr := Chr(0);
  ShStrOff := TList<Integer>.Create();
  try
    for I := 0 to FSecAddr.Count - 1 do
    begin
      ShStrOff.Add(Length(ShStr));
      ShStr := ShStr + FSecAddr.Get(I).Name + Chr(0);
    end;
    NamePos := Length(ShStr);
    ShStr := ShStr + '.shstrtab' + Chr(0);

    ShTabOff := Length(Buf);
    Buf := Buf + ShStr;

    SecCount := FSecAddr.Count + 2;
    while (Length(Buf) and 7) <> 0 do Buf := Buf + Chr(0);

    LkCopyInto(Buf, 40, LkLE(Length(Buf), 8));
    LkCopyInto(Buf, 60, LkLE(SecCount, 2));
    LkCopyInto(Buf, 62, LkLE(SecCount - 1, 2));

    Buf := Buf + LkZeros(ELF64_SHDR_SIZE);

    for I := 0 to FSecAddr.Count - 1 do
    begin
      M := FSecAddr.Get(I);
      A := FAddrOf.Get(I);
      Buf := Buf + LkLE(ShStrOff.Get(I), 4);
      Buf := Buf + LkLE(M.ShType, 4);
      Buf := Buf + LkLE(M.Flags, 8);
      Buf := Buf + LkLE(A, 8);
      if M.ShType = SHT_NOBITS then
        Buf := Buf + LkLE(Integer(DataFileHi), 8)
      else
        Buf := Buf + LkLE(Integer(A), 8);
      Buf := Buf + LkLE(M.Size, 8);
      Buf := Buf + LkLE(0, 4);
      Buf := Buf + LkLE(0, 4);
      Buf := Buf + LkLE(M.Align, 8);
      Buf := Buf + LkLE(0, 8);
    end;

    Buf := Buf + LkLE(NamePos, 4);
    Buf := Buf + LkLE(SHT_STRTAB, 4);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(ShTabOff, 8);
    Buf := Buf + LkLE(Length(ShStr), 8);
    Buf := Buf + LkLE(0, 4);
    Buf := Buf + LkLE(0, 4);
    Buf := Buf + LkLE(1, 8);
    Buf := Buf + LkLE(0, 8);
  finally
    ShStrOff.Free();
  end;

  Result := Buf;
end;

function TLinker.LinkToBytes(const AEntryName: string): string;
var
  Sym: TLinkSymbol;
  RE: TRelaDynEntry;
  I: Integer;
begin
  if FDynamic then
  begin
    { Phase C dynamic pipeline:
      1. Collect external (undefined) symbols → PLT entries.
      2. Collect GOTPCREL targets → non-PLT GOT slots.
      3. Build the dynamic table blobs (.dynsym, .dynstr, .hash, etc.)
      4. Layout all sections at virtual addresses (base 0, PIE).
      5. Build global symbol table from laid-out sections.
      6. Synthesise linker symbols (__bss_start, _GLOBAL_OFFSET_TABLE_ etc.)
      7. Apply relocations (R_X86_64_64→RELATIVE, GOTPCREL, TPOFF32).
      8. Re-serialise .rela.dyn with collected RELATIVE entries.
      9. Rebuild .dynamic with final .rela.dyn addresses.
     10. Emit the PIE executable. }

    { Steps 1-2: scan object symbol tables for externals and GOT targets. }
    Self.CollectExternals();
    Self.CollectGotSlots();

    { Step 3: build the dynamic table blobs. }
    Self.BuildDynamic();

    { Step 4: assign final virtual addresses (PIE, base 0). }
    Self.LayoutDynamic();

    { Step 5: build the global symbol table from laid-out sections. }
    Self.BuildSymbols();

    { Step 6: synthesise remaining symbols. }
    Self.DefineSynthSymbols();

    { Step 6b: fill non-PLT GOT slots with resolved symbol addresses.
      These need RELATIVE entries so ld.so fixes them up at load time. }
    for I := 0 to FGotSlots.Count - 1 do
    begin
      Sym := Self.FindSymbol(FGotSlots.Get(I).Name);
      if (Sym <> nil) and Sym.Defined then
        FGotSlots.Get(I).Value := Sym.Addr
      else
        FGotSlots.Get(I).Value := 0;
      LkPatch64(FGotData, FGotSlots.Get(I).GotOffset,
        FGotSlots.Get(I).Value);
      if FGotSlots.Get(I).Value <> 0 then
      begin
        RE := TRelaDynEntry.Create();
        RE.VAddr := FGotAddr + FGotSlots.Get(I).GotOffset;
        RE.Addend := FGotSlots.Get(I).Value;
        FRelaDyn.Add(RE);
      end;
    end;

    { Step 7: apply relocations (collects R_X86_64_RELATIVE entries). }
    Self.ApplyRelocations();

    { Step 9: re-serialise .rela.dyn with the collected entries. }
    FRelaDynData := '';
    for I := 0 to FRelaDyn.Count - 1 do
    begin
      FRelaDynData := FRelaDynData + LkLE(FRelaDyn.Get(I).VAddr, 8);
      FRelaDynData := FRelaDynData + LkLE(Int64(R_X86_64_RELATIVE), 8);
      FRelaDynData := FRelaDynData + LkLE(FRelaDyn.Get(I).Addend, 8);
    end;

    { Update DT_RELA* in .dynamic if we now have entries. }
    if Length(FRelaDynData) > 0 then
    begin
      { Rebuild the .dynamic section with correct .rela.dyn entries.
        The addresses of other sections haven't changed. }
      FDynamicData := '';
      FDynamicData := FDynamicData + LkLE(DT_NEEDED, 8) + LkLE(1, 8);
      FDynamicData := FDynamicData + FExtraNeededDyn;
      FDynamicData := FDynamicData + LkLE(DT_HASH, 8) + LkLE(FHashAddr, 8);
      FDynamicData := FDynamicData + LkLE(DT_STRTAB, 8) + LkLE(FDynStrAddr, 8);
      FDynamicData := FDynamicData + LkLE(DT_SYMTAB, 8) + LkLE(FDynSymAddr, 8);
      FDynamicData := FDynamicData + LkLE(DT_STRSZ, 8) + LkLE(Length(FDynStrTab), 8);
      FDynamicData := FDynamicData + LkLE(DT_SYMENT, 8) + LkLE(ELF64_SYM_SIZE, 8);
      FDynamicData := FDynamicData + LkLE(DT_PLTGOT, 8) + LkLE(FGotAddr, 8);
      FDynamicData := FDynamicData + LkLE(DT_PLTRELSZ, 8) + LkLE(Length(FRelaPlt), 8);
      FDynamicData := FDynamicData + LkLE(DT_PLTREL, 8) + LkLE(DT_RELA, 8);
      FDynamicData := FDynamicData + LkLE(DT_JMPREL, 8) + LkLE(FRelaPltAddr, 8);
      FDynamicData := FDynamicData + LkLE(DT_RELA, 8) + LkLE(FRelaDynAddr, 8);
      FDynamicData := FDynamicData + LkLE(DT_RELASZ, 8) + LkLE(Length(FRelaDynData), 8);
      FDynamicData := FDynamicData + LkLE(DT_RELAENT, 8) + LkLE(ELF64_RELA_SIZE, 8);
      FDynamicData := FDynamicData + LkLE(DT_RELACOUNT, 8) + LkLE(FRelaDyn.Count, 8);
      if FInitArraySize > 0 then
      begin
        FDynamicData := FDynamicData + LkLE(DT_INIT_ARRAY, 8) + LkLE(FInitArrayAddr, 8);
        FDynamicData := FDynamicData + LkLE(DT_INIT_ARRAYSZ, 8) + LkLE(FInitArraySize, 8);
      end;
      if FFiniArraySize > 0 then
      begin
        FDynamicData := FDynamicData + LkLE(DT_FINI_ARRAY, 8) + LkLE(FFiniArrayAddr, 8);
        FDynamicData := FDynamicData + LkLE(DT_FINI_ARRAYSZ, 8) + LkLE(FFiniArraySize, 8);
      end;
      FDynamicData := FDynamicData + LkLE(DT_DEBUG, 8) + LkLE(0, 8);
      FDynamicData := FDynamicData + LkLE(DT_FLAGS_1, 8) + LkLE(DF_1_PIE, 8);
      FDynamicData := FDynamicData + LkLE(DT_NULL, 8) + LkLE(0, 8);
      if Length(FDynamicData) < DYN_MAX_ENTRIES * 16 then
        FDynamicData := FDynamicData + LkZeros(DYN_MAX_ENTRIES * 16 - Length(FDynamicData));
    end;

    Sym := Self.FindSymbol(AEntryName);
    if (Sym = nil) or (not Sym.Defined) or Sym.IsWeakSlot then
      raise ELinker.Create('entry symbol not found: ' + AEntryName);
    FEntry := Sym.Addr;
    Result := Self.EmitDynExecutable(FEntry);
  end
  else
  begin
    { Phase B static pipeline. }
    Self.LayoutSections();
    Self.BuildSymbols();
    Self.DefineSynthSymbols();
    Self.ApplyRelocations();

    Sym := Self.FindSymbol(AEntryName);
    if (Sym = nil) or (not Sym.Defined) or Sym.IsWeakSlot then
      raise ELinker.Create('entry symbol not found: ' + AEntryName);
    FEntry := Sym.Addr;
    Result := Self.EmitExecutable(FEntry);
  end;
end;

procedure TLinker.Link(const AEntryName, AOutputPath: string);
var
  Bytes: string;
  FOut: TFileOutputStream;
begin
  Bytes := Self.LinkToBytes(AEntryName);
  if FileExists(AOutputPath) then
    DeleteFile(AOutputPath);
  FOut := TFileOutputStream.Create(AOutputPath);
  try
    FOut.Write(PChar(Bytes), Length(Bytes));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;
  MakeFileExecutable(AOutputPath);
end;

function TLinker.AddrOfSymbol(const AName: string): Int64;
var
  S: TLinkSymbol;
begin
  S := Self.FindSymbol(AName);
  if S = nil then
    Result := -1
  else
    Result := S.Addr;
end;

function TLinker.FindMerged(const AName: string): TMergedSection;
begin
  Result := FMerger.FindMerged(AName);
end;

function TLinker.FindMergedText: TMergedSection;
begin
  Result := FMerger.FindMerged('.text');
end;

end.
