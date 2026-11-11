{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.linker.pe;

{ The PE32+ linker for windows-x86_64 (windows-x86_64-backend-design.adoc,
  "PE32+ linker").

  Input is the ELF relocatable objects the x86_64 backend and the internal
  assembler produce for every x86_64 target (design decision D2).  The linker
  merges their sections into the image sections, resolves symbols (strong
  over weak; the first strong definition wins, as in the ELF linker), turns
  every undefined symbol named in a .blaise.imports pair into a DLL import
  reached through a jmp thunk, applies the relocations, and writes the image
  with blaise.pewriter.

  Image sections, in address order, each present only when it has content
  (.text always):

    .text   R X   code, then the import thunks
    .rdata  R     read-only data, the import tables, the TLS directory
    .data   R W   initialised data, the TLS index, then .bss as a tail
    .tls    R W   .tdata, then .tbss as zero fill
    .blunw  R W   the blaise_unwind blocks, bracketed by
                  __start_blaise_unwind and __stop_blaise_unwind
    .opdf   R     OPDF debug records
    .reloc  R     base relocations (discardable)

  Relocations: PC32 and PLT32 resolve directly (an import resolves to its
  thunk); R_X86_64_64 writes the preferred virtual address and records a
  DIR64 base relocation; TPOFF32 is the symbol's offset into the TLS
  template.  A 32-bit absolute relocation cannot be rebased above 4 GiB and
  is an error, as is any GOT relocation: the backend emits neither. }

interface

uses
  SysUtils, Classes, Generics.Collections, blaise.elfreader,
  blaise.container.writer, blaise.pewriter;

type
  EPeLinker = class(Exception);

  { Maps a library name as written in external '<lib>' to its DLL file
    name.  The Windows toolkit supplies it; without one the name is used
    verbatim. }
  TPeDllNameFunc = function(const ALib: string): string of object;

  TPeLinker = class
  private
    FObjs: TList<TElfObjectFile>;      { owned }
    FStreams: array[0..7] of TByteBuf;  { owned; nil for the NOBITS ones }
    FStreamSize: array[0..7] of Int64;
    FStreamAlign: array[0..7] of Int64;
    FStreamRva: array[0..7] of Int64;
    { per input section, flat in FSecFirst[obj] + section index order: the
      stream (-1 = not placed) and the offset in it }
    FSecFirst: TList<Int>;
    FSecStream: TList<Int>;
    FSecOff: TList<Int64>;
    { global definitions: name -> index into the FDef lists }
    FDefIndex: TDictionary<string, Int>;
    FDefStream: TList<Int>;
    FDefOff: TList<Int64>;
    FDefWeak: TList<Boolean>;
    { .blaise.imports pairs, symbol -> library }
    FImportLib: TDictionary<string, string>;
    { the imports actually used, in first-reference order }
    FImpNames: TList<string>;
    FImpIndex: TDictionary<string, Int>;
    FImpTable: TPeImportTableBuilder;
    FThunkOff: Int64;                  { offset of thunk 0 in .text }
    FBaseRelocs: TList<Int>;
    FHasTls: Boolean;
    FTlsIndexOff: Int64;               { offset of the index slot in .data }
    FTlsDirOff: Int64;                 { offset of the TLS directory in .rdata }
    FImpTableOff: Int64;               { offset of the import tables in .rdata }
    FTextRva, FRdataRva, FDataRva, FTlsRva, FUnwRva, FOpdfRva: Int64;
    procedure PlaceSections;
    procedure ReadImportPairs(AObj: TElfObjectFile; ASec: TRdSection);
    procedure CollectDefinitions;
    procedure CollectImports;
    procedure Layout;
    procedure ApplyRelocations;
    function SymbolRva(AObjIdx, ASymIdx: Int; out AAbsolute: Boolean;
      const ACtx: string): Int64;
    function DefinedRva(const AName: string; out AFound: Boolean): Int64;
    function IsSynthName(const AName: string): Boolean;
    function SynthRva(const AName: string): Int64;
    function DllOf(const ALib: string): string;
    procedure Patch32(AStream: Int; AOff: Int64; AValue: Int64);
    procedure Patch64(AStream: Int; AOff: Int64; AValue: Int64);
  public
    { PE subsystem of the image: PeSubsystemConsole (default) or
      PeSubsystemGui. }
    Subsystem: Int;
    DllNameOf: TPeDllNameFunc;
    constructor Create;
    destructor Destroy; override;
    { Takes ownership of AObj. }
    procedure AddObject(AObj: TElfObjectFile);
    procedure AddObjectFile(const APath: string);
    { Link everything into a PE32+ image whose entry point is AEntrySym. }
    function Link(const AEntrySym: string): string;
    procedure LinkToFile(const AEntrySym, AOutPath: string);
  end;

implementation

uses
  streams, uStrCompat;

const
  stText = 0;
  stRdata = 1;
  stData = 2;
  stBss = 3;
  stTdata = 4;
  stTbss = 5;
  stUnwind = 6;
  stOpdf = 7;
  StreamCount = 8;

  ThunkSize = 8;    { jmp *disp32(%rip) is 6 bytes, padded to 8 }

  R_X86_64_REX_GOTPCRELX = 42;

function StartsWith(const S, APrefix: string): Boolean;
begin
  Result := Copy(S, 0, Length(APrefix)) = APrefix;
end;

{ The stream an allocated input section merges into, or -1 for a section
  the image has no place for. }
function StreamOfSection(ASec: TRdSection): Int;
var
  N: string;
begin
  N := ASec.Name;
  if (N = '.text') or StartsWith(N, '.text.') then
    Result := stText
  else if (N = '.rodata') or StartsWith(N, '.rodata.') then
    Result := stRdata
  else if (N = '.data') or StartsWith(N, '.data.') then
    Result := stData
  else if (N = '.bss') or StartsWith(N, '.bss.') then
    Result := stBss
  else if (N = '.tdata') or StartsWith(N, '.tdata.') then
    Result := stTdata
  else if (N = '.tbss') or StartsWith(N, '.tbss.') then
    Result := stTbss
  else if N = 'blaise_unwind' then
    Result := stUnwind
  else if N = '.opdf' then
    Result := stOpdf
  else
    Result := -1;
end;

function IsNoBits(AStream: Int): Boolean;
begin
  Result := (AStream = stBss) or (AStream = stTbss);
end;

{ ---- TPeLinker ---- }

constructor TPeLinker.Create;
var
  I: Int;
begin
  inherited Create();
  FObjs := TList<TElfObjectFile>.Create();
  for I := 0 to StreamCount - 1 do
  begin
    if IsNoBits(I) then
      FStreams[I] := nil
    else
      FStreams[I] := TByteBuf.Create();
    FStreamSize[I] := 0;
    FStreamAlign[I] := 1;
    FStreamRva[I] := 0;
  end;
  FSecFirst := TList<Int>.Create();
  FSecStream := TList<Int>.Create();
  FSecOff := TList<Int64>.Create();
  FDefIndex := TDictionary<string, Int>.Create();
  FDefStream := TList<Int>.Create();
  FDefOff := TList<Int64>.Create();
  FDefWeak := TList<Boolean>.Create();
  FImportLib := TDictionary<string, string>.Create();
  FImpNames := TList<string>.Create();
  FImpIndex := TDictionary<string, Int>.Create();
  FImpTable := TPeImportTableBuilder.Create();
  FBaseRelocs := TList<Int>.Create();
  Subsystem := PeSubsystemConsole;
  DllNameOf := nil;
end;

destructor TPeLinker.Destroy;
var
  I: Int;
begin
  for I := 0 to FObjs.Count - 1 do
    FObjs[I].Free();
  FObjs.Free();
  for I := 0 to StreamCount - 1 do
    FStreams[I].Free();
  FSecFirst.Free();
  FSecStream.Free();
  FSecOff.Free();
  FDefIndex.Free();
  FDefStream.Free();
  FDefOff.Free();
  FDefWeak.Free();
  FImportLib.Free();
  FImpNames.Free();
  FImpIndex.Free();
  FImpTable.Free();
  FBaseRelocs.Free();
  inherited Destroy();
end;

procedure TPeLinker.AddObject(AObj: TElfObjectFile);
begin
  FObjs.Add(AObj);
end;

procedure TPeLinker.AddObjectFile(const APath: string);
begin
  AddObject(ReadElfObjectFile(APath));
end;

function TPeLinker.DllOf(const ALib: string): string;
begin
  if Assigned(DllNameOf) then
    Result := DllNameOf(ALib)
  else
    Result := ALib;
end;

procedure TPeLinker.ReadImportPairs(AObj: TElfObjectFile; ASec: TRdSection);
var
  P, Q: Int;
  Sym, Lib, Prev: string;
begin
  P := 0;
  while P < Length(ASec.Data) do
  begin
    Q := P;
    while (Q < Length(ASec.Data)) and (StrAt(ASec.Data, Q) <> 0) do
      Inc(Q);
    Sym := Copy(ASec.Data, P, Q - P);
    P := Q + 1;
    Q := P;
    while (Q < Length(ASec.Data)) and (StrAt(ASec.Data, Q) <> 0) do
      Inc(Q);
    if Q >= Length(ASec.Data) then
      raise EPeLinker.Create(AObj.SourceName +
        ': malformed .blaise.imports (unterminated pair)');
    Lib := Copy(ASec.Data, P, Q - P);
    P := Q + 1;
    if FImportLib.TryGetValue(Sym, Prev) then
    begin
      if LowerCase(DllOf(Prev)) <> LowerCase(DllOf(Lib)) then
        raise EPeLinker.Create('''' + Sym + ''' is imported from both ' +
          DllOf(Prev) + ' and ' + DllOf(Lib));
    end
    else
      FImportLib.Add(Sym, Lib);
  end;
end;

{ Merge every placed input section into its stream, in input order. }
procedure TPeLinker.PlaceSections;
var
  Oi, Si, St: Int;
  Obj: TElfObjectFile;
  Sec: TRdSection;
  Align, Off: Int64;
begin
  for Oi := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs[Oi];
    FSecFirst.Add(FSecStream.Count);
    for Si := 0 to Obj.Sections.Count - 1 do
    begin
      Sec := Obj.Sections[Si];
      St := -1;
      if (Sec.ShType = SHT_NULL) or (Sec.ShType = SHT_SYMTAB) or
         (Sec.ShType = SHT_STRTAB) or (Sec.ShType = SHT_RELA) then
        St := -1
      else if Sec.Name = '.blaise.imports' then
        ReadImportPairs(Obj, Sec)
      else if (Sec.Flags and SHF_ALLOC) = 0 then
        { .note.GNU-stack, .comment, the embedded unit interface: nothing
          the loaded image needs }
        St := -1
      else
      begin
        St := StreamOfSection(Sec);
        if St < 0 then
          raise EPeLinker.Create(Obj.SourceName + ': section ' + Sec.Name +
            ' has no place in a PE image');
      end;
      if St < 0 then
      begin
        FSecStream.Add(-1);
        FSecOff.Add(0);
        Continue;
      end;
      Align := Sec.AddrAlign;
      if Align < 1 then
        Align := 1;
      if Align > FStreamAlign[St] then
        FStreamAlign[St] := Align;
      Off := PeAlignUp(FStreamSize[St], Align);
      if FStreams[St] <> nil then
      begin
        FStreams[St].PadTo(Off);
        FStreams[St].AppendBytes(Sec.Data);
      end;
      FStreamSize[St] := Off + Sec.Size;
      FSecStream.Add(St);
      FSecOff.Add(Off);
    end;
  end;
end;

procedure TPeLinker.CollectDefinitions;
var
  Oi, Si, Flat, D: Int;
  Obj: TElfObjectFile;
  Sym: TRdSymbol;
begin
  for Oi := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs[Oi];
    for Si := 0 to Obj.Symbols.Count - 1 do
    begin
      Sym := Obj.Symbols[Si];
      if (Sym.Bind <> STB_GLOBAL) and (Sym.Bind <> STB_WEAK) then Continue;
      if (Sym.Name = '') or (Sym.Shndx = SHN_UNDEF) then Continue;
      if Sym.Shndx = SHN_COMMON then
        raise EPeLinker.Create(Obj.SourceName + ': common symbol ' +
          Sym.Name + ' is not supported');
      if Sym.Shndx = SHN_ABS then Continue;
      Flat := FSecFirst[Oi] + Sym.Shndx;
      if FSecStream[Flat] < 0 then Continue;
      if FDefIndex.TryGetValue(Sym.Name, D) then
      begin
        { strong replaces weak; otherwise the first definition stands }
        if FDefWeak[D] and (Sym.Bind = STB_GLOBAL) then
        begin
          FDefStream[D] := FSecStream[Flat];
          FDefOff[D] := FSecOff[Flat] + Sym.Value;
          FDefWeak[D] := False;
        end;
        Continue;
      end;
      FDefIndex.Add(Sym.Name, FDefStream.Count);
      FDefStream.Add(FSecStream[Flat]);
      FDefOff.Add(FSecOff[Flat] + Sym.Value);
      FDefWeak.Add(Sym.Bind = STB_WEAK);
    end;
  end;
end;

function TPeLinker.IsSynthName(const AName: string): Boolean;
begin
  Result := (AName = '__start_blaise_unwind') or
    (AName = '__stop_blaise_unwind') or (AName = '__ImageBase');
end;

{ Every strong undefined reference that no object defines must be an
  import named by a .blaise.imports pair. }
procedure TPeLinker.CollectImports;
var
  Oi, Ri, D: Int;
  Obj: TElfObjectFile;
  Rel: TRdReloc;
  Sym: TRdSymbol;
  Lib: string;
begin
  for Oi := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs[Oi];
    for Ri := 0 to Obj.Relocs.Count - 1 do
    begin
      Rel := Obj.Relocs[Ri];
      if FSecStream[FSecFirst[Oi] + Rel.TargetSection] < 0 then Continue;
      Sym := Obj.Symbols[Rel.SymIndex];
      if Sym.Shndx <> SHN_UNDEF then Continue;
      if FDefIndex.ContainsKey(Sym.Name) or IsSynthName(Sym.Name) then
        Continue;
      if FImpIndex.TryGetValue(Sym.Name, D) then Continue;
      if not FImportLib.TryGetValue(Sym.Name, Lib) then
      begin
        if Sym.Bind = STB_WEAK then Continue;
        raise EPeLinker.Create(Obj.SourceName + ': undefined symbol ''' +
          Sym.Name + ''': no object defines it and no library is named ' +
          'for it; declare it external ''<dll>'' name ''' + Sym.Name + '''');
      end;
      FImpIndex.Add(Sym.Name, FImpNames.Count);
      FImpNames.Add(Sym.Name);
      FImpTable.Add(DllOf(Lib), Sym.Name);
    end;
  end;
end;

{ Lay out the image: append the thunks, the import tables and the TLS
  bookkeeping to their streams, then give each stream its RVA. }
procedure TPeLinker.Layout;
var
  I, NumSecs: Int;
  Imports, Probe: string;
  Rva: Int64;
begin
  { the thunks: placeholders, patched in ApplyRelocations }
  if FImpNames.Count > 0 then
  begin
    FThunkOff := PeAlignUp(FStreamSize[stText], 16);
    FStreams[stText].PadTo(FThunkOff);
    for I := 0 to FImpNames.Count - 1 do
    begin
      FStreams[stText].PushByte($FF);
      FStreams[stText].PushByte($25);
      FStreams[stText].PushU32(0);
      FStreams[stText].PushU16($9090);
    end;
    FStreamSize[stText] := FStreams[stText].Count;
  end;

  FHasTls := (FStreamSize[stTdata] > 0) or (FStreamSize[stTbss] > 0);
  if FHasTls then
  begin
    { the index slot the loader writes }
    FTlsIndexOff := PeAlignUp(FStreamSize[stData], 8);
    FStreams[stData].PadTo(FTlsIndexOff);
    FStreams[stData].PushU64(0);
    FStreamSize[stData] := FStreams[stData].Count;
  end;

  { the import tables' size does not depend on where they go }
  Probe := FImpTable.Build(0);
  if Length(Probe) > 0 then
  begin
    FImpTableOff := PeAlignUp(FStreamSize[stRdata], 8);
    FStreams[stRdata].PadTo(FImpTableOff + Length(Probe));
    FStreamSize[stRdata] := FStreams[stRdata].Count;
  end;
  if FHasTls then
  begin
    { the directory, then an empty callback list }
    FTlsDirOff := PeAlignUp(FStreamSize[stRdata], 8);
    FStreams[stRdata].PadTo(FTlsDirOff + PeTlsDirectorySize + 8);
    FStreamSize[stRdata] := FStreams[stRdata].Count;
  end;

  { count the image sections, then assign RVAs in address order }
  NumSecs := 1;
  if FStreamSize[stRdata] > 0 then Inc(NumSecs);
  if (FStreamSize[stData] > 0) or (FStreamSize[stBss] > 0) then Inc(NumSecs);
  if FHasTls then Inc(NumSecs);
  if FStreamSize[stUnwind] > 0 then Inc(NumSecs);
  if FStreamSize[stOpdf] > 0 then Inc(NumSecs);
  { .reloc is decided after relocation; reserve its header slot }
  Inc(NumSecs);

  Rva := PeFirstSectionRva(NumSecs);
  FTextRva := Rva;
  FStreamRva[stText] := Rva;
  Rva := PeAlignUp(Rva + FStreamSize[stText], PeSectionAlignment);
  FRdataRva := Rva;
  FStreamRva[stRdata] := Rva;
  if FStreamSize[stRdata] > 0 then
    Rva := PeAlignUp(Rva + FStreamSize[stRdata], PeSectionAlignment);
  FDataRva := Rva;
  FStreamRva[stData] := Rva;
  FStreamRva[stBss] := Rva + PeAlignUp(FStreamSize[stData],
    FStreamAlign[stBss]);
  if (FStreamSize[stData] > 0) or (FStreamSize[stBss] > 0) then
    Rva := PeAlignUp(FStreamRva[stBss] + FStreamSize[stBss],
      PeSectionAlignment);
  FTlsRva := Rva;
  FStreamRva[stTdata] := Rva;
  FStreamRva[stTbss] := Rva + PeAlignUp(FStreamSize[stTdata],
    FStreamAlign[stTbss]);
  if FHasTls then
    Rva := PeAlignUp(FStreamRva[stTbss] + FStreamSize[stTbss],
      PeSectionAlignment);
  FUnwRva := Rva;
  FStreamRva[stUnwind] := Rva;
  if FStreamSize[stUnwind] > 0 then
    Rva := PeAlignUp(Rva + FStreamSize[stUnwind], PeSectionAlignment);
  FOpdfRva := Rva;
  FStreamRva[stOpdf] := Rva;

  { now the import tables can be built where they live }
  if not FImpTable.IsEmpty() then
  begin
    Imports := FImpTable.Build(FRdataRva + FImpTableOff);
    for I := 0 to Length(Imports) - 1 do
      FStreams[stRdata].Bytes[FImpTableOff + I] := Ord(Imports[I]);
  end;
end;

function TPeLinker.SynthRva(const AName: string): Int64;
begin
  if AName = '__start_blaise_unwind' then
    Result := FStreamRva[stUnwind]
  else if AName = '__stop_blaise_unwind' then
    Result := FStreamRva[stUnwind] + FStreamSize[stUnwind]
  else
    Result := 0;   { __ImageBase }
end;

function TPeLinker.DefinedRva(const AName: string;
  out AFound: Boolean): Int64;
var
  D: Int;
begin
  AFound := FDefIndex.TryGetValue(AName, D);
  if AFound then
    Result := FStreamRva[FDefStream[D]] + FDefOff[D]
  else
    Result := 0;
end;

{ The RVA a relocation against symbol ASymIdx of object AObjIdx resolves
  to.  AAbsolute is set for an SHN_ABS value or an unresolved weak
  reference, which are plain numbers, not image addresses. }
function TPeLinker.SymbolRva(AObjIdx, ASymIdx: Int; out AAbsolute: Boolean;
  const ACtx: string): Int64;
var
  Obj: TElfObjectFile;
  Sym: TRdSymbol;
  Flat, Imp: Int;
  Found: Boolean;
begin
  AAbsolute := False;
  Obj := FObjs[AObjIdx];
  Sym := Obj.Symbols[ASymIdx];
  if Sym.Shndx = SHN_ABS then
  begin
    AAbsolute := True;
    Result := Sym.Value;
    Exit;
  end;
  if Sym.Shndx <> SHN_UNDEF then
  begin
    { a global resolves to its canonical definition, so every reference
      reaches the same copy }
    if Sym.Bind <> STB_LOCAL then
    begin
      Result := DefinedRva(Sym.Name, Found);
      if Found then Exit;
    end;
    Flat := FSecFirst[AObjIdx] + Sym.Shndx;
    if FSecStream[Flat] < 0 then
      raise EPeLinker.Create(ACtx + ': symbol ' + Sym.Name +
        ' is in a section the image does not contain');
    Result := FStreamRva[FSecStream[Flat]] + FSecOff[Flat] + Sym.Value;
    Exit;
  end;
  Result := DefinedRva(Sym.Name, Found);
  if Found then Exit;
  if IsSynthName(Sym.Name) then
  begin
    Result := SynthRva(Sym.Name);
    Exit;
  end;
  if FImpIndex.TryGetValue(Sym.Name, Imp) then
  begin
    Result := FTextRva + FThunkOff + Imp * ThunkSize;
    Exit;
  end;
  { an unresolved weak reference is zero }
  AAbsolute := True;
  Result := 0;
end;

procedure TPeLinker.Patch32(AStream: Int; AOff: Int64; AValue: Int64);
var
  B: TByteBuf;
begin
  B := FStreams[AStream];
  B.Bytes[AOff] := AValue and $FF;
  B.Bytes[AOff + 1] := (AValue shr 8) and $FF;
  B.Bytes[AOff + 2] := (AValue shr 16) and $FF;
  B.Bytes[AOff + 3] := (AValue shr 24) and $FF;
end;

procedure TPeLinker.Patch64(AStream: Int; AOff: Int64; AValue: Int64);
begin
  Patch32(AStream, AOff, AValue and $FFFFFFFF);
  Patch32(AStream, AOff + 4, (AValue shr 32) and $FFFFFFFF);
end;

procedure TPeLinker.ApplyRelocations;
var
  Oi, Ri, St, I: Int;
  Obj: TElfObjectFile;
  Rel: TRdReloc;
  Flat: Int;
  Off, P, S, Val: Int64;
  Abs: Boolean;
  Ctx, SymName: string;
begin
  for Oi := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs[Oi];
    Ctx := Obj.SourceName;
    for Ri := 0 to Obj.Relocs.Count - 1 do
    begin
      Rel := Obj.Relocs[Ri];
      Flat := FSecFirst[Oi] + Rel.TargetSection;
      St := FSecStream[Flat];
      if St < 0 then Continue;
      if IsNoBits(St) then
        raise EPeLinker.Create(Ctx + ': relocation into a NOBITS section');
      Off := FSecOff[Flat] + Rel.Offset;
      P := FStreamRva[St] + Off;
      SymName := Obj.Symbols[Rel.SymIndex].Name;
      case Rel.RelocType of
        R_X86_64_NONE: ;
        R_X86_64_PC32, R_X86_64_PLT32:
          begin
            S := SymbolRva(Oi, Rel.SymIndex, Abs, Ctx);
            Val := S + Rel.Addend - P;
            if (Val < -2147483648) or (Val > 2147483647) then
              raise EPeLinker.Create(Ctx + ': PC-relative relocation ' +
                'against ' + SymName + ' is out of range');
            Patch32(St, Off, Val);
          end;
        R_X86_64_64:
          begin
            S := SymbolRva(Oi, Rel.SymIndex, Abs, Ctx);
            if Abs then
              Patch64(St, Off, S + Rel.Addend)
            else
            begin
              Patch64(St, Off, PeDefaultImageBase + S + Rel.Addend);
              FBaseRelocs.Add(P);
            end;
          end;
        R_X86_64_TPOFF32:
          begin
            S := SymbolRva(Oi, Rel.SymIndex, Abs, Ctx);
            Patch32(St, Off, S - FTlsRva + Rel.Addend);
          end;
        R_X86_64_32, R_X86_64_32S:
          raise EPeLinker.Create(Ctx + ': R_X86_64_32 relocation against ' +
            SymName + ': a 32-bit absolute address cannot be rebased in a ' +
            'PE image (a code-generation defect: Windows code must be ' +
            'position-independent)');
        R_X86_64_GOTPCREL, R_X86_64_GOTPCRELX, R_X86_64_REX_GOTPCRELX:
          raise EPeLinker.Create(Ctx + ': GOT relocation against ' +
            SymName + ' is not supported in a PE image');
      else
        raise EPeLinker.Create(Ctx + ': unsupported relocation type ' +
          IntToStr(Rel.RelocType) + ' against ' + SymName);
      end;
    end;
  end;

  { the thunks: jmp *slot(%rip) }
  for I := 0 to FImpNames.Count - 1 do
  begin
    Off := FThunkOff + I * ThunkSize;
    P := FTextRva + Off + 6;
    S := FImpTable.IatSlotRva(DllOf(FImportLib.GetItem(FImpNames[I])),
      FImpNames[I]);
    Patch32(stText, Off + 2, S - P);
  end;

  { the TLS directory and its four rebased pointers }
  if FHasTls then
  begin
    Off := FTlsDirOff;
    Patch64(stRdata, Off, PeDefaultImageBase + FTlsRva);
    Patch64(stRdata, Off + 8, PeDefaultImageBase + FTlsRva +
      FStreamSize[stTdata]);
    Patch64(stRdata, Off + 16, PeDefaultImageBase + FDataRva + FTlsIndexOff);
    Patch64(stRdata, Off + 24, PeDefaultImageBase + FRdataRva + Off +
      PeTlsDirectorySize);
    Patch32(stRdata, Off + 32, (FStreamRva[stTbss] - FTlsRva -
      FStreamSize[stTdata]) + FStreamSize[stTbss]);
    for I := 0 to 3 do
      FBaseRelocs.Add(FRdataRva + Off + I * 8);
  end;
end;

function TPeLinker.Link(const AEntrySym: string): string;
var
  W: TPeImageWriter;
  Found: Boolean;
  Entry, RelocRva: Int64;
  Relocs: string;
begin
  PlaceSections();
  CollectDefinitions();
  CollectImports();
  Layout();
  ApplyRelocations();
  Entry := DefinedRva(AEntrySym, Found);
  if not Found then
    raise EPeLinker.Create('entry symbol ' + AEntrySym + ' is not defined');

  W := TPeImageWriter.Create();
  try
    W.Subsystem := Subsystem;
    W.EntryRva := Entry;
    W.AddSection('.text', FTextRva, FStreamSize[stText],
      FStreams[stText].AsString(),
      PeScnCode or PeScnMemExecute or PeScnMemRead);
    RelocRva := PeAlignUp(FTextRva + FStreamSize[stText], PeSectionAlignment);
    if FStreamSize[stRdata] > 0 then
    begin
      W.AddSection('.rdata', FRdataRva, FStreamSize[stRdata],
        FStreams[stRdata].AsString(), PeScnInitialisedData or PeScnMemRead);
      RelocRva := PeAlignUp(FRdataRva + FStreamSize[stRdata],
        PeSectionAlignment);
    end;
    if (FStreamSize[stData] > 0) or (FStreamSize[stBss] > 0) then
    begin
      W.AddSection('.data', FDataRva,
        FStreamRva[stBss] + FStreamSize[stBss] - FDataRva,
        FStreams[stData].AsString(),
        PeScnInitialisedData or PeScnMemRead or PeScnMemWrite);
      RelocRva := PeAlignUp(FStreamRva[stBss] + FStreamSize[stBss],
        PeSectionAlignment);
    end;
    if FHasTls then
    begin
      W.AddSection('.tls', FTlsRva,
        FStreamRva[stTbss] + FStreamSize[stTbss] - FTlsRva,
        FStreams[stTdata].AsString(),
        PeScnInitialisedData or PeScnMemRead or PeScnMemWrite);
      RelocRva := PeAlignUp(FStreamRva[stTbss] + FStreamSize[stTbss],
        PeSectionAlignment);
    end;
    if FStreamSize[stUnwind] > 0 then
    begin
      W.AddSection('.blunw', FUnwRva, FStreamSize[stUnwind],
        FStreams[stUnwind].AsString(),
        PeScnInitialisedData or PeScnMemRead or PeScnMemWrite);
      RelocRva := PeAlignUp(FUnwRva + FStreamSize[stUnwind],
        PeSectionAlignment);
    end;
    if FStreamSize[stOpdf] > 0 then
    begin
      W.AddSection('.opdf', FOpdfRva, FStreamSize[stOpdf],
        FStreams[stOpdf].AsString(), PeScnInitialisedData or PeScnMemRead);
      RelocRva := PeAlignUp(FOpdfRva + FStreamSize[stOpdf],
        PeSectionAlignment);
    end;
    Relocs := BuildBaseRelocs(FBaseRelocs);
    if Length(Relocs) > 0 then
    begin
      W.AddSection('.reloc', RelocRva, Length(Relocs), Relocs,
        PeScnInitialisedData or PeScnMemRead or PeScnMemDiscardable);
      W.SetDirectory(PeDirBaseReloc, RelocRva, Length(Relocs));
    end;
    if not FImpTable.IsEmpty() then
    begin
      W.SetDirectory(PeDirImport, FImpTable.DirectoryRva,
        FImpTable.DirectorySize);
      W.SetDirectory(PeDirIat, FImpTable.IatRva, FImpTable.IatSize);
    end;
    if FHasTls then
      W.SetDirectory(PeDirTls, FRdataRva + FTlsDirOff, PeTlsDirectorySize);
    Result := W.Finish();
  finally
    W.Free();
  end;
end;

procedure TPeLinker.LinkToFile(const AEntrySym, AOutPath: string);
var
  Bytes: string;
  FOut: TFileOutputStream;
begin
  Bytes := Link(AEntrySym);
  if FileExists(AOutPath) then
    DeleteFile(AOutPath);
  FOut := TFileOutputStream.Create(AOutPath);
  try
    FOut.Write(PChar(Bytes), Length(Bytes));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;
end;

end.
