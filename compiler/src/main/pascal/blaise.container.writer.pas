{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.container.writer;

{ Container-writer seam (the Bridge "Implementor" role).

  The internal assemblers produce relocatable objects by driving an
  append-oriented writer: select a section, append code/data bytes, define
  symbols at the current offset, record relocations, then Finish() to a
  byte buffer.  That surface is container-agnostic — ELF (ET_REL) and
  Mach-O (MH_OBJECT) disagree about headers, section naming, and the
  relocation encoding, but they agree about everything the assembler
  computes.

  IContainerWriter is that surface as an interface, so an assembler holds
  "a writer" without naming the container: TElfObjectWriter
  (blaise.elfwriter) implements it today; TMachOWriter is the planned
  sibling (docs/macos-arm64-backend-design.adoc).  Which concrete writer is
  constructed is the per-target choice, made by the toolkit family — never
  by conditional compilation or a case statement inside the assembler.

  Lifetime: IContainerWriter is ARC-managed (same convention as ICodeGen).
  Assign a freshly-created concrete writer to an IContainerWriter variable
  and let assignment/scope-exit release it — no manual Free.  (Mixing an
  explicit Free with ARC would double-free.)

  The types below are the writer's vocabulary:

  * TContainerSectionKind — the abstract section set the backends emit
    into.  Each writer maps a kind to its native name (.text/.data/... for
    ELF; __text/__data/... for Mach-O).
  * TContainerSymBind / TContainerSymType — symbol binding and type,
    encoded per container (ELF st_info; Mach-O nlist n_type/n_desc).
  * TContainerRelocKind — relocation kinds.  These are ARCHITECTURE facts
    (they name what the CPU's addressing needs fixed up), so the enum is a
    union of per-arch families: the x86-64 members below today; the
    AArch64 family (ARM64_RELOC_BRANCH26, PAGE21/PAGEOFF12, ...) joins
    when the arm64 assembler lands.  Each writer encodes the kinds its
    container defines and rejects the rest. }

interface

type
  { Abstract section identity.  The writer owns the container-specific
    section name, flags, and alignment defaults. }
  TContainerSectionKind = (
    cskText,     { executable code }
    cskData,     { read-write initialised data }
    cskRodata,   { read-only data }
    cskBss,      { zero-initialised read-write data (no file bytes) }
    cskTbss,     { thread-local zero-initialised data }
    cskTdata,    { thread-local initialised data (Mach-O __thread_data) }
    cskTvars,    { Mach-O TLV descriptors (__thread_vars) }
    cskOpdf,     { OPDF debug info (alloc+write, progbits) }
    cskIface,    { embedded unit-interface (.bif) metadata.  Mach-O only —
                   (__BLAISE,__blaise_iface), dropped by the linker.  ELF keeps
                   its post-hoc uElfObject embedding, so this kind is never
                   populated there and never reaches the ELF writer's section
                   order, exactly like cskTvars. }
    cskInitArray { load-time constructor pointers the dynamic loader runs.
                   ELF .init_array (DT_INIT_ARRAY); the Mach-O analogue is
                   __DATA,__mod_init_func (S_MOD_INIT_FUNC_POINTERS), not yet
                   emitted — a shared object's load constructor registers here }
  );

  TContainerSymBind = (
    csbLocal,    { file scope }
    csbGlobal,   { visible to the linker }
    csbWeak      { overridable global }
  );

  TContainerSymType = (
    cstNone,
    cstFunc,
    cstObject,
    cstSection,
    cstTLS
  );

  { Relocation kinds — a union of per-architecture families; each writer
    encodes the kinds its container defines and rejects the rest.

    x86-64 family (ELF R_X86_64_* semantics): }
  TContainerRelocKind = (
    crkNone,
    crk64,           { absolute 64-bit }
    crk32,           { absolute 32-bit (zero-extend) }
    crk32S,          { absolute 32-bit (sign-extend) }
    crkPC32,         { PC-relative 32-bit }
    crkPLT32,        { PLT-relative 32-bit }
    crkGOTPCREL,     { GOT PC-relative 32-bit }
    crkTPOFF32,      { TLS TP-relative 32-bit }
    crkGOTPCRELX,    { relaxable GOTPCREL }
    crkREX_GOTPCRELX,{ relaxable GOTPCREL with REX prefix }
    { AArch64 family (Mach-O ARM64_RELOC_* semantics): }
    crkArm64Abs64,        { ARM64_RELOC_UNSIGNED — absolute 64-bit pointer }
    crkArm64Branch26,     { ARM64_RELOC_BRANCH26 — b/bl ±128 MiB }
    crkArm64Page21,       { ARM64_RELOC_PAGE21 — adrp page delta }
    crkArm64PageOff12,    { ARM64_RELOC_PAGEOFF12 — add/ldr low 12 bits }
    crkArm64GotPage21,    { ARM64_RELOC_GOT_LOAD_PAGE21 }
    crkArm64GotPageOff12, { ARM64_RELOC_GOT_LOAD_PAGEOFF12 }
    crkArm64TlvPage21,    { ARM64_RELOC_TLVP_LOAD_PAGE21 }
    crkArm64TlvPageOff12  { ARM64_RELOC_TLVP_LOAD_PAGEOFF12 }
  );

  TContainerReloc = record
    Offset:   Integer;             { byte offset within the section }
    SymIndex: Integer;             { index into the writer's symbol table }
    RType:    TContainerRelocKind; { relocation kind }
    Addend:   Int64;               { addend (RELA-style) }
  end;

  { Amortized-growth byte buffer shared by the container writers.  Used to
    assemble a final on-disk image without the O(n^2) `Buf := Buf + ...`
    per-byte string growth that OOM-killed on the compiler's own ~2 MB
    object.  Appends are amortized O(1); a section body or table is
    bulk-copied in via AppendBytes. }
  TByteBuf = class
  public
    Bytes: array of Byte;
    Count: Integer;
    constructor Create;
    destructor Destroy; override;
    procedure PushByte(AVal: Integer);
    procedure PushU16(AVal: Integer);
    procedure PushU32(AVal: Integer);
    procedure PushU64(AVal: Int64);
    procedure PadTo(ALen: Integer);        { append zeros until Count = ALen }
    procedure AppendBytes(const ASrc: string);   { bulk-copy a byte string }
    procedure AppendBuf(ASrc: TByteBuf);          { bulk-copy another buffer }
    function AsString: string;
  end;

  { The append-oriented writer contract the assemblers drive. }
  IContainerWriter = interface
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
    procedure Patch32(AKind: TContainerSectionKind; AOffset: Integer;
      AVal: Integer);

    { Define a symbol.  Returns the symbol index. }
    function DefineSymbol(const AName: string; ASection: TContainerSectionKind;
      AValue: Integer; ASize: Integer;
      ABind: TContainerSymBind; ASType: TContainerSymType): Integer;
    { Reference an external (undefined) symbol.  Returns the symbol index.
      Idempotent — returns the existing index if already declared. }
    function ExternSymbol(const AName: string): Integer;
    { Look up a symbol by name.  Returns index or -1. }
    function FindSymbol(const AName: string): Integer;

    { Add a relocation to a section. }
    procedure AddReloc(ASection: TContainerSectionKind; AOffset: Integer;
      ASymIndex: Integer; ARType: TContainerRelocKind; AAddend: Int64);

    { Serialise the complete object to a byte string. }
    function Finish: string;

    { Write the object to a file. }
    procedure WriteToFile(const APath: string);
  end;

implementation

{ Bulk memory copy, used for O(n) buffer appends and materialisation. }
procedure _cw_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

{ ---- TByteBuf --------------------------------------------------------- }

constructor TByteBuf.Create;
begin
  inherited Create();
  SetLength(Bytes, 0);
  Count := 0;
end;

destructor TByteBuf.Destroy;
begin
  SetLength(Bytes, 0);
  inherited Destroy();
end;

procedure TByteBuf.PushByte(AVal: Integer);
var
  NewCap: Integer;
begin
  if Count >= Length(Bytes) then
  begin
    NewCap := Length(Bytes) * 2;
    if NewCap < 4096 then
      NewCap := 4096;
    SetLength(Bytes, NewCap);
  end;
  Bytes[Count] := AVal and $FF;
  Count := Count + 1;
end;

procedure TByteBuf.PushU16(AVal: Integer);
begin
  PushByte(AVal and $FF);
  PushByte((AVal shr 8) and $FF);
end;

procedure TByteBuf.PushU32(AVal: Integer);
begin
  PushByte(AVal and $FF);
  PushByte((AVal shr 8) and $FF);
  PushByte((AVal shr 16) and $FF);
  PushByte((AVal shr 24) and $FF);
end;

procedure TByteBuf.PushU64(AVal: Int64);
var
  I: Integer;
begin
  for I := 0 to 7 do
    PushByte(Integer((AVal shr (I * 8)) and $FF));
end;

procedure TByteBuf.PadTo(ALen: Integer);
begin
  while Count < ALen do
    PushByte(0);
end;

procedure TByteBuf.AppendBytes(const ASrc: string);
var
  N, NewCap: Integer;
begin
  N := Length(ASrc);
  if N = 0 then Exit;
  if Count + N > Length(Bytes) then
  begin
    NewCap := Length(Bytes);
    if NewCap < 4096 then NewCap := 4096;
    while Count + N > NewCap do
      NewCap := NewCap * 2;
    SetLength(Bytes, NewCap);
  end;
  _cw_memcpy(@Bytes[Count], PChar(ASrc), N);
  Count := Count + N;
end;

procedure TByteBuf.AppendBuf(ASrc: TByteBuf);
var
  N, NewCap: Integer;
begin
  N := ASrc.Count;
  if N = 0 then Exit;
  if Count + N > Length(Bytes) then
  begin
    NewCap := Length(Bytes);
    if NewCap < 4096 then NewCap := 4096;
    while Count + N > NewCap do
      NewCap := NewCap * 2;
    SetLength(Bytes, NewCap);
  end;
  _cw_memcpy(@Bytes[Count], @ASrc.Bytes[0], N);
  Count := Count + N;
end;

function TByteBuf.AsString: string;
begin
  SetLength(Result, Count);
  if Count > 0 then
    _cw_memcpy(PChar(Result), @Bytes[0], Count);
end;

end.
