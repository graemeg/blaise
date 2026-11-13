{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.pewriter;

{ PE32+ image writer for the windows-x86_64 target
  (windows-x86_64-backend-design.adoc, "PE32+ linker").

  TPeImageWriter serialises the DOS header and stub, the COFF and PE32+
  optional headers, the section table and the section bodies.  The caller
  (the PE linker) chooses every section's RVA, so it can resolve
  relocations before the image is written; the writer checks the layout and
  places the raw data.

  The table builders produce the bytes of the tables the loader reads -- the
  import directory with its lookup and address tables, base relocations and
  the TLS directory -- so the linker and the tests share one encoding.

  Output is deterministic: TimeDateStamp and CheckSum are 0, and every table
  is emitted in sorted order. }

interface

uses
  SysUtils, Classes, Generics.Collections, blaise.container.writer;

const
  PeMachineAmd64 = $8664;

  { COFF file-header characteristics }
  PeFileExecutableImage = $0002;
  PeFileLargeAddressAware = $0020;

  PeMagicPe32Plus = $20B;

  PeSubsystemGui = 2;
  PeSubsystemConsole = 3;

  { optional-header DllCharacteristics }
  PeDllHighEntropyVa = $0020;
  PeDllDynamicBase = $0040;
  PeDllNxCompat = $0100;
  PeDllTerminalServerAware = $8000;

  { section characteristics }
  PeScnCode = $00000020;
  PeScnInitialisedData = $00000040;
  PeScnUninitialisedData = $00000080;
  PeScnMemDiscardable = $02000000;
  PeScnMemExecute = $20000000;
  PeScnMemRead = $40000000;
  PeScnMemWrite = $80000000;

  { data-directory indices }
  PeDirExport = 0;
  PeDirImport = 1;
  PeDirException = 3;
  PeDirBaseReloc = 5;
  PeDirTls = 9;
  PeDirIat = 12;
  PeDirectoryCount = 16;

  { base-relocation entry types }
  PeRelBasedAbsolute = 0;
  PeRelBasedDir64 = 10;

  PeDefaultImageBase = $140000000;
  PeSectionAlignment = $1000;
  PeFileAlignment = $200;
  { e_lfanew: the PE signature follows the DOS header and stub }
  PeHeaderOffset = $80;

  PeTlsDirectorySize = 40;

type
  EPeWriter = class(Exception);

  { One image section as the linker lays it out. }
  TPeOutSection = class
  public
    Name: string;
    VirtualAddress: Int;
    VirtualSize: Int;
    Data: string;
    Characteristics: Int64;
  end;

  TPeImageWriter = class
  private
    FSections: TList<TPeOutSection>;
    FDirRva: array[0..15] of Int;
    FDirSize: array[0..15] of Int;
    procedure CheckLayout;
  public
    ImageBase: Int64;
    Subsystem: Int;
    EntryRva: Int;
    StackReserve: Int64;
    StackCommit: Int64;
    HeapReserve: Int64;
    HeapCommit: Int64;
    constructor Create;
    destructor Destroy; override;
    { Add a section at ARva spanning AVirtualSize bytes in memory, of which
      AData are initialised; the rest of the span reads as zero.  Sections
      are added in ascending RVA order. }
    procedure AddSection(const AName: string; ARva, AVirtualSize: Int;
      const AData: string; ACharacteristics: Int64);
    procedure SetDirectory(AIndex, ARva, ASize: Int);
    { Serialise the image. }
    function Finish: string;
  end;

  { The import directory: one descriptor per DLL, a lookup table and an
    address table per DLL (the address tables contiguous, so one IAT
    directory covers them), hint/name entries and the DLL names.  Imports
    are by name with hint 0. }
  TPeImportTableBuilder = class
  private
    FDlls: TList<string>;
    FSyms: TList<TList<string>>;
    FSlotRva: TDictionary<string, Int>;
    FBuilt: Boolean;
    function DllIndex(const ADll: string): Int;
  public
    DirectoryRva: Int;
    DirectorySize: Int;
    IatRva: Int;
    IatSize: Int;
    constructor Create;
    destructor Destroy; override;
    { Import ASymbol from ADll.  A repeated pair is ignored; DLL names
      compare case-insensitively, as Windows compares them. }
    procedure Add(const ADll, ASymbol: string);
    function IsEmpty: Boolean;
    { Lay the tables out starting at ABaseRva and return their bytes ('' when
      nothing is imported).  Sets the directory fields. }
    function Build(ABaseRva: Int): string;
    { The RVA of the address-table slot the loader fills with ASymbol's
      address.  Valid after Build. }
    function IatSlotRva(const ADll, ASymbol: string): Int;
  end;

{ The size of the headers for an image of ASectionCount sections, rounded up
  to the file alignment. }
function PeHeadersSize(ASectionCount: Int): Int;

{ The lowest RVA the first section may take. }
function PeFirstSectionRva(ASectionCount: Int): Int;

function PeAlignUp(AValue, AAlign: Int64): Int64;

{ The .reloc contents for the 64-bit absolute pointers at ARvas: one block per
  4 KiB page, entries sorted, each block padded to a multiple of four bytes.
  Duplicates are dropped.  '' when ARvas is empty. }
function BuildBaseRelocs(ARvas: TList<Int>): string;

{ An IMAGE_TLS_DIRECTORY64.  The addresses are virtual addresses (image base
  included) and each needs a base relocation. }
function BuildTlsDirectory(AStartVa, AEndVa, AIndexVa, ACallbacksVa: Int64;
  AZeroFill: Int): string;

implementation

uses
  uStrCompat;

{ V in hexadecimal, for diagnostics. }
function HexOf(AValue: Int64): string;
const
  Digits = '0123456789ABCDEF';
var
  V: Int64;
begin
  if AValue = 0 then
  begin
    Result := '0';
    Exit;
  end;
  Result := '';
  V := AValue;
  while V <> 0 do
  begin
    Result := Copy(Digits, V and 15, 1) + Result;
    V := V shr 4;
  end;
end;

function PeAlignUp(AValue, AAlign: Int64): Int64;
begin
  Result := ((AValue + AAlign - 1) div AAlign) * AAlign;
end;

function PeHeadersSize(ASectionCount: Int): Int;
begin
  { DOS header and stub, signature, COFF header, PE32+ optional header with
    16 directories, section table }
  Result := PeAlignUp(PeHeaderOffset + 4 + 20 + 240 + 40 * ASectionCount,
    PeFileAlignment);
end;

function PeFirstSectionRva(ASectionCount: Int): Int;
begin
  Result := PeAlignUp(PeHeadersSize(ASectionCount), PeSectionAlignment);
end;

{ ---- TPeImageWriter ---- }

constructor TPeImageWriter.Create;
var
  I: Int;
begin
  inherited Create();
  FSections := TList<TPeOutSection>.Create();
  for I := 0 to PeDirectoryCount - 1 do
  begin
    FDirRva[I] := 0;
    FDirSize[I] := 0;
  end;
  ImageBase := PeDefaultImageBase;
  Subsystem := PeSubsystemConsole;
  EntryRva := 0;
  StackReserve := 8 * 1024 * 1024;
  StackCommit := 64 * 1024;
  HeapReserve := 1024 * 1024;
  HeapCommit := 4096;
end;

destructor TPeImageWriter.Destroy;
var
  I: Int;
begin
  for I := 0 to FSections.Count - 1 do
    FSections[I].Free();
  FSections.Free();
  inherited Destroy();
end;

procedure TPeImageWriter.AddSection(const AName: string; ARva,
  AVirtualSize: Int; const AData: string; ACharacteristics: Int64);
var
  S: TPeOutSection;
begin
  if (Length(AName) = 0) or (Length(AName) > 8) then
    raise EPeWriter.Create('PE section name ''' + AName +
      ''' must be one to eight bytes');
  if Length(AData) > AVirtualSize then
    raise EPeWriter.Create('PE section ' + AName +
      ': initialised data exceeds its virtual size');
  S := TPeOutSection.Create();
  S.Name := AName;
  S.VirtualAddress := ARva;
  S.VirtualSize := AVirtualSize;
  S.Data := AData;
  S.Characteristics := ACharacteristics;
  FSections.Add(S);
end;

procedure TPeImageWriter.SetDirectory(AIndex, ARva, ASize: Int);
begin
  if (AIndex < 0) or (AIndex >= PeDirectoryCount) then
    raise EPeWriter.Create('PE data directory index out of range: ' +
      IntToStr(AIndex));
  FDirRva[AIndex] := ARva;
  FDirSize[AIndex] := ASize;
end;

procedure TPeImageWriter.CheckLayout;
var
  I: Int;
  S, Prev: TPeOutSection;
begin
  if FSections.Count = 0 then
    raise EPeWriter.Create('a PE image needs at least one section');
  for I := 0 to FSections.Count - 1 do
  begin
    S := FSections[I];
    if S.VirtualAddress mod PeSectionAlignment <> 0 then
      raise EPeWriter.Create('PE section ' + S.Name + ' at RVA $' +
        HexOf(S.VirtualAddress) + ' is not section-aligned');
    if I = 0 then
    begin
      if S.VirtualAddress < PeFirstSectionRva(FSections.Count) then
        raise EPeWriter.Create('PE section ' + S.Name +
          ' overlaps the headers');
    end
    else
    begin
      Prev := FSections[I - 1];
      if S.VirtualAddress < Prev.VirtualAddress + Prev.VirtualSize then
        raise EPeWriter.Create('PE section ' + S.Name + ' overlaps ' +
          Prev.Name);
    end;
  end;
end;

procedure PushName8(ABuf: TByteBuf; const AName: string);
var
  I: Int;
begin
  for I := 0 to 7 do
    if I < Length(AName) then
      ABuf.PushByte(StrAt(AName, I))
    else
      ABuf.PushByte(0);
end;

procedure PushDosHeaderAndStub(ABuf: TByteBuf);
const
  { push cs; pop ds; mov dx, 0Eh; mov ah, 9; int 21h; mov ax, 4C01h;
    int 21h.  Bytes, not a string literal: a character above #127 in a
    literal is UTF-8 encoded. }
  StubCode: array[0..13] of Byte = ($0E, $1F, $BA, $0E, $00, $B4, $09, $CD,
    $21, $B8, $01, $4C, $CD, $21);
  StubText = 'This program cannot be run in DOS mode.'#13#13#10'$';
var
  I: Int;
begin
  ABuf.PushU16($5A4D);          { e_magic 'MZ' }
  ABuf.PushU16($90);            { e_cblp }
  ABuf.PushU16(3);              { e_cp }
  ABuf.PushU16(0);              { e_crlc }
  ABuf.PushU16(4);              { e_cparhdr }
  ABuf.PushU16(0);              { e_minalloc }
  ABuf.PushU16($FFFF);          { e_maxalloc }
  ABuf.PushU16(0);              { e_ss }
  ABuf.PushU16($B8);            { e_sp }
  ABuf.PushU16(0);              { e_csum }
  ABuf.PushU16(0);              { e_ip }
  ABuf.PushU16(0);              { e_cs }
  ABuf.PushU16($40);            { e_lfarlc }
  ABuf.PushU16(0);              { e_ovno }
  ABuf.PadTo($3C);              { e_res, e_oemid, e_oeminfo, e_res2 }
  ABuf.PushU32(PeHeaderOffset); { e_lfanew }
  for I := 0 to High(StubCode) do
    ABuf.PushByte(StubCode[I]);
  ABuf.AppendBytes(StubText);
  ABuf.PadTo(PeHeaderOffset);
end;

function TPeImageWriter.Finish: string;
var
  Buf: TByteBuf;
  I, N, HdrSize, RawPtr, RawSize, BaseOfCode: Int;
  SizeOfCode, SizeOfInit, SizeOfUninit, SizeOfImage: Int64;
  RawPtrs: array of Int;
  RawSizes: array of Int;
  S, Last: TPeOutSection;
begin
  CheckLayout();
  N := FSections.Count;
  HdrSize := PeHeadersSize(N);
  SetLength(RawPtrs, N);
  SetLength(RawSizes, N);
  RawPtr := HdrSize;
  SizeOfCode := 0;
  SizeOfInit := 0;
  SizeOfUninit := 0;
  BaseOfCode := 0;
  for I := 0 to N - 1 do
  begin
    S := FSections[I];
    RawSize := PeAlignUp(Length(S.Data), PeFileAlignment);
    RawSizes[I] := RawSize;
    if RawSize > 0 then
    begin
      RawPtrs[I] := RawPtr;
      RawPtr := RawPtr + RawSize;
    end
    else
      RawPtrs[I] := 0;
    if (S.Characteristics and PeScnCode) <> 0 then
    begin
      SizeOfCode := SizeOfCode + RawSize;
      if BaseOfCode = 0 then
        BaseOfCode := S.VirtualAddress;
    end;
    if (S.Characteristics and PeScnInitialisedData) <> 0 then
      SizeOfInit := SizeOfInit + RawSize;
    if (S.Characteristics and PeScnUninitialisedData) <> 0 then
      SizeOfUninit := SizeOfUninit + PeAlignUp(S.VirtualSize,
        PeFileAlignment);
  end;
  Last := FSections[N - 1];
  SizeOfImage := PeAlignUp(Last.VirtualAddress + Last.VirtualSize,
    PeSectionAlignment);

  Buf := TByteBuf.Create();
  try
    PushDosHeaderAndStub(Buf);
    Buf.PushU32($00004550);   { 'PE'#0#0 }

    { COFF file header }
    Buf.PushU16(PeMachineAmd64);
    Buf.PushU16(N);
    Buf.PushU32(0);           { TimeDateStamp: deterministic }
    Buf.PushU32(0);           { PointerToSymbolTable }
    Buf.PushU32(0);           { NumberOfSymbols }
    Buf.PushU16(240);         { SizeOfOptionalHeader }
    Buf.PushU16(PeFileExecutableImage or PeFileLargeAddressAware);

    { PE32+ optional header }
    Buf.PushU16(PeMagicPe32Plus);
    Buf.PushByte(1);          { MajorLinkerVersion }
    Buf.PushByte(0);          { MinorLinkerVersion }
    Buf.PushU32(SizeOfCode);
    Buf.PushU32(SizeOfInit);
    Buf.PushU32(SizeOfUninit);
    Buf.PushU32(EntryRva);
    Buf.PushU32(BaseOfCode);
    Buf.PushU64(ImageBase);
    Buf.PushU32(PeSectionAlignment);
    Buf.PushU32(PeFileAlignment);
    Buf.PushU16(6);           { MajorOperatingSystemVersion }
    Buf.PushU16(0);
    Buf.PushU16(0);           { MajorImageVersion }
    Buf.PushU16(0);
    Buf.PushU16(6);           { MajorSubsystemVersion }
    Buf.PushU16(0);
    Buf.PushU32(0);           { Win32VersionValue }
    Buf.PushU32(SizeOfImage);
    Buf.PushU32(HdrSize);
    Buf.PushU32(0);           { CheckSum: deterministic }
    Buf.PushU16(Subsystem);
    Buf.PushU16(PeDllHighEntropyVa or PeDllDynamicBase or PeDllNxCompat or
      PeDllTerminalServerAware);
    Buf.PushU64(StackReserve);
    Buf.PushU64(StackCommit);
    Buf.PushU64(HeapReserve);
    Buf.PushU64(HeapCommit);
    Buf.PushU32(0);           { LoaderFlags }
    Buf.PushU32(PeDirectoryCount);
    for I := 0 to PeDirectoryCount - 1 do
    begin
      Buf.PushU32(FDirRva[I]);
      Buf.PushU32(FDirSize[I]);
    end;

    { section table }
    for I := 0 to N - 1 do
    begin
      S := FSections[I];
      PushName8(Buf, S.Name);
      Buf.PushU32(S.VirtualSize);
      Buf.PushU32(S.VirtualAddress);
      Buf.PushU32(RawSizes[I]);
      Buf.PushU32(RawPtrs[I]);
      Buf.PushU32(0);         { PointerToRelocations }
      Buf.PushU32(0);         { PointerToLinenumbers }
      Buf.PushU16(0);
      Buf.PushU16(0);
      Buf.PushU32(S.Characteristics);
    end;
    Buf.PadTo(HdrSize);

    for I := 0 to N - 1 do
      if RawSizes[I] > 0 then
      begin
        Buf.AppendBytes(FSections[I].Data);
        Buf.PadTo(RawPtrs[I] + RawSizes[I]);
      end;
    Result := Buf.AsString();
  finally
    Buf.Free();
  end;
end;

{ ---- TPeImportTableBuilder ---- }

constructor TPeImportTableBuilder.Create;
begin
  inherited Create();
  FDlls := TList<string>.Create();
  FSyms := TList<TList<string>>.Create();
  FSlotRva := TDictionary<string, Int>.Create();
  FBuilt := False;
  DirectoryRva := 0;
  DirectorySize := 0;
  IatRva := 0;
  IatSize := 0;
end;

destructor TPeImportTableBuilder.Destroy;
var
  I: Int;
begin
  for I := 0 to FSyms.Count - 1 do
    FSyms[I].Free();
  FSyms.Free();
  FDlls.Free();
  FSlotRva.Free();
  inherited Destroy();
end;

function TPeImportTableBuilder.DllIndex(const ADll: string): Int;
var
  I: Int;
begin
  Result := -1;
  for I := 0 to FDlls.Count - 1 do
    if LowerCase(FDlls[I]) = LowerCase(ADll) then
    begin
      Result := I;
      Exit;
    end;
end;

procedure TPeImportTableBuilder.Add(const ADll, ASymbol: string);
var
  D, I: Int;
  Syms: TList<string>;
begin
  D := DllIndex(ADll);
  if D < 0 then
  begin
    { keep the DLLs sorted, case-insensitively }
    D := 0;
    while (D < FDlls.Count) and (LowerCase(FDlls[D]) < LowerCase(ADll)) do
      Inc(D);
    FDlls.Insert(D, ADll);
    FSyms.Insert(D, TList<string>.Create());
  end;
  Syms := FSyms[D];
  I := 0;
  while (I < Syms.Count) and (Syms[I] < ASymbol) do
    Inc(I);
  if (I < Syms.Count) and (Syms[I] = ASymbol) then
    Exit;
  Syms.Insert(I, ASymbol);
  FBuilt := False;
end;

function TPeImportTableBuilder.IsEmpty: Boolean;
begin
  Result := FDlls.Count = 0;
end;

function SlotKey(const ADll, ASymbol: string): string;
begin
  Result := LowerCase(ADll) + #0 + ASymbol;
end;

function TPeImportTableBuilder.Build(ABaseRva: Int): string;
var
  Buf: TByteBuf;
  D, I, J, Pass, Off, IltOff, IatOff, HintOff, NameOff, Slots: Int;
  IltStart: array of Int;
  IatStart: array of Int;
  NameRva: array of Int;
  HintRva: TList<Int>;
  Syms: TList<string>;
begin
  FSlotRva.Clear();
  if FDlls.Count = 0 then
  begin
    DirectoryRva := 0;
    DirectorySize := 0;
    IatRva := 0;
    IatSize := 0;
    FBuilt := True;
    Result := '';
    Exit;
  end;
  SetLength(IltStart, FDlls.Count);
  SetLength(IatStart, FDlls.Count);
  SetLength(NameRva, FDlls.Count);
  Slots := 0;
  for D := 0 to FDlls.Count - 1 do
    Slots := Slots + FSyms[D].Count + 1;

  { pass 1: offsets }
  DirectorySize := (FDlls.Count + 1) * 20;
  IltOff := PeAlignUp(DirectorySize, 8);
  IatOff := IltOff + Slots * 8;
  HintOff := IatOff + Slots * 8;
  Off := 0;
  for D := 0 to FDlls.Count - 1 do
  begin
    IltStart[D] := IltOff + Off;
    IatStart[D] := IatOff + Off;
    Off := Off + (FSyms[D].Count + 1) * 8;
  end;
  HintRva := TList<Int>.Create();
  Buf := TByteBuf.Create();
  try
    NameOff := HintOff;
    for D := 0 to FDlls.Count - 1 do
    begin
      Syms := FSyms[D];
      for I := 0 to Syms.Count - 1 do
      begin
        HintRva.Add(ABaseRva + NameOff);
        NameOff := NameOff + PeAlignUp(2 + Length(Syms[I]) + 1, 2);
      end;
    end;
    for D := 0 to FDlls.Count - 1 do
    begin
      NameRva[D] := ABaseRva + NameOff;
      NameOff := NameOff + PeAlignUp(Length(FDlls[D]) + 1, 2);
    end;

    { pass 2: bytes }
    for D := 0 to FDlls.Count - 1 do
    begin
      Buf.PushU32(ABaseRva + IltStart[D]);  { OriginalFirstThunk }
      Buf.PushU32(0);                       { TimeDateStamp }
      Buf.PushU32(0);                       { ForwarderChain }
      Buf.PushU32(NameRva[D]);
      Buf.PushU32(ABaseRva + IatStart[D]);  { FirstThunk }
    end;
    Buf.PadTo(DirectorySize);
    Buf.PadTo(IltOff);
    { the lookup tables, then the address tables: identical before binding }
    for Pass := 0 to 1 do
    begin
      I := 0;
      for D := 0 to FDlls.Count - 1 do
      begin
        Syms := FSyms[D];
        for J := 0 to Syms.Count - 1 do
        begin
          Buf.PushU64(HintRva[I]);
          if Pass = 1 then
            FSlotRva.SetItem(SlotKey(FDlls[D], Syms[J]),
              ABaseRva + IatStart[D] + J * 8);
          Inc(I);
        end;
        Buf.PushU64(0);
      end;
    end;
    for D := 0 to FDlls.Count - 1 do
    begin
      Syms := FSyms[D];
      for I := 0 to Syms.Count - 1 do
      begin
        Buf.PushU16(0);                     { hint }
        Buf.AppendBytes(Syms[I]);
        Buf.PushByte(0);
        if Buf.Count mod 2 <> 0 then
          Buf.PushByte(0);
      end;
    end;
    for D := 0 to FDlls.Count - 1 do
    begin
      Buf.AppendBytes(FDlls[D]);
      Buf.PushByte(0);
      if Buf.Count mod 2 <> 0 then
        Buf.PushByte(0);
    end;
    Result := Buf.AsString();
  finally
    Buf.Free();
    HintRva.Free();
  end;
  DirectoryRva := ABaseRva;
  IatRva := ABaseRva + IatOff;
  IatSize := Slots * 8;
  FBuilt := True;
end;

function TPeImportTableBuilder.IatSlotRva(const ADll,
  ASymbol: string): Int;
begin
  if not FBuilt then
    raise EPeWriter.Create('import table not built');
  if not FSlotRva.TryGetValue(SlotKey(ADll, ASymbol), Result) then
    raise EPeWriter.Create('no import of ' + ASymbol + ' from ' + ADll);
end;

{ ---- base relocations and TLS ---- }

function BuildBaseRelocs(ARvas: TList<Int>): string;
var
  Sorted: TList<Int>;
  Buf: TByteBuf;
  I, J, K, Page, Count: Int;
begin
  Sorted := TList<Int>.Create();
  Buf := TByteBuf.Create();
  try
    { insertion into a sorted, duplicate-free list }
    for I := 0 to ARvas.Count - 1 do
    begin
      J := 0;
      while (J < Sorted.Count) and (Sorted[J] < ARvas[I]) do
        Inc(J);
      if (J >= Sorted.Count) or (Sorted[J] <> ARvas[I]) then
        Sorted.Insert(J, ARvas[I]);
    end;
    I := 0;
    while I < Sorted.Count do
    begin
      Page := Sorted[I] and not $FFF;
      J := I;
      while (J < Sorted.Count) and ((Sorted[J] and not $FFF) = Page) do
        Inc(J);
      Count := J - I;
      if Count mod 2 <> 0 then
        Count := Count + 1;
      Buf.PushU32(Page);
      Buf.PushU32(8 + Count * 2);
      for K := I to J - 1 do
        Buf.PushU16((PeRelBasedDir64 shl 12) or (Sorted[K] and $FFF));
      if (J - I) mod 2 <> 0 then
        Buf.PushU16(PeRelBasedAbsolute shl 12);
      I := J;
    end;
    Result := Buf.AsString();
  finally
    Buf.Free();
    Sorted.Free();
  end;
end;

function BuildTlsDirectory(AStartVa, AEndVa, AIndexVa, ACallbacksVa: Int64;
  AZeroFill: Int): string;
var
  Buf: TByteBuf;
begin
  Buf := TByteBuf.Create();
  try
    Buf.PushU64(AStartVa);
    Buf.PushU64(AEndVa);
    Buf.PushU64(AIndexVa);
    Buf.PushU64(ACallbacksVa);
    Buf.PushU32(AZeroFill);
    Buf.PushU32(0);           { Characteristics }
    Result := Buf.AsString();
  finally
    Buf.Free();
  end;
end;

end.
