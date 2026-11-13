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

  A named library says where a routine lives and that it is called the C
  way (design decision D6).  So a reference from an object that names a
  library for its symbol binds to the DLL even when the link defines the
  same name -- runtime.cstub's strlen, say, compiled the internal way --
  unless that definition is itself a C entry: a cdecl routine with a body,
  whose object lists it in .blaise.imports with an empty library (the
  pthread_* routines runtime.thread.windows supplies).

  Image sections, in address order, each present only when it has content
  (.text always):

    .text   R X   code, then the import thunks
    .rdata  R     read-only data, the import tables, the TLS directory, the
                  unwind data (.pdata entries and their one UNWIND_INFO)
    .data   R W   initialised data, the TLS index, then .bss as a tail
    .tls    R W   .tdata, then .tbss written out as zero bytes
    .blunw  R W   the blaise_unwind blocks, bracketed by
                  __start_blaise_unwind and __stop_blaise_unwind
    .opdf   R     OPDF debug records
    .reloc  R     base relocations (discardable)

  Relocations: PC32 and PLT32 resolve directly (an import resolves to its
  thunk); R_X86_64_64 writes the preferred virtual address and records a
  DIR64 base relocation; TPOFF32 is the symbol's offset into the TLS
  template.  A 32-bit absolute relocation cannot be rebased above 4 GiB and
  is an error, as is any GOT relocation: the backend emits neither.

  Unwind data.  Windows walks a stack -- for a debugger, a crash report,
  RtlCaptureStackBackTrace, the exception dispatcher -- with the image's
  exception directory: a RUNTIME_FUNCTION per routine, naming its
  UNWIND_INFO.  A routine with none is taken for a leaf, whose return
  address is at the stack pointer, so a walk lost its way in the first
  Blaise frame.  Every routine the backend compiles opens with the same
  frame, push %rbp then mov %rsp, %rbp, so one UNWIND_INFO describes them
  all: a 4-byte prologue that pushes RBP and makes it the frame register.
  The linker gives an entry to every routine (an STT_FUNC symbol in .text)
  whose code starts with those 4 bytes, ending where the next routine or
  its input section does;
  a routine that starts any other way (a nostackframe assembler routine,
  an import thunk) keeps no entry and is walked as a leaf, which is what
  it is.  The registers a routine saves into its frame by MOV are not
  described, so the data serves a walk of the stack, not the recovery of
  those registers by an exception unwinding through Blaise frames.  Nor is
  the one instruction between pop %rbp and ret, where RBP is the caller's
  again. }

interface

uses
  SysUtils, Classes, Generics.Collections, blaise.elfreader,
  blaise.container.writer, blaise.pewriter, blaise.pereader;

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
    { the pairs per object, keyed ObjIdx#0symbol }
    FObjImports: TDictionary<string, Boolean>;
    { symbols some object defines as a C entry (an empty library) }
    FCEntries: TDictionary<string, Boolean>;
    { the imports actually used, in first-reference order }
    FImpNames: TList<string>;
    FImpIndex: TDictionary<string, Int>;
    FImpTable: TPeImportTableBuilder;
    FThunkOff: Int64;                  { offset of thunk 0 in .text }
    FBaseRelocs: TList<Int>;
    FHasTls: Boolean;
    FTlsIndexOff: Int64;               { offset of the index slot in .data }
    FWantTlsIndex: Boolean;            { an object references _tls_index }
    FTlsDirOff: Int64;                 { offset of the TLS directory in .rdata }
    FImpTableOff: Int64;               { offset of the import tables in .rdata }
    { the routines given unwind data: start and end offsets in .text }
    FUnwStarts, FUnwEnds: TList<Int64>;
    FXdataOff: Int64;                  { the UNWIND_INFO, in .rdata }
    FPdataOff: Int64;                  { the RUNTIME_FUNCTION entries }
    FTextRva, FRdataRva, FDataRva, FTlsRva, FUnwRva, FOpdfRva: Int64;
    procedure PlaceSections;
    procedure ReadImportPairs(AObjIdx: Int; AObj: TElfObjectFile;
      ASec: TRdSection);
    { True when object AObjIdx's reference to AName goes to the DLL its
      import pair names, although the link defines AName. }
    function ImportOverridesDefinition(AObjIdx: Int;
      const AName: string): Boolean;
    procedure CollectDefinitions;
    procedure CollectImports;
    procedure CheckImportsExported;
    procedure CollectUnwindRanges;
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
    { Directories holding the DLLs the image imports from, for the export
      check: each import from a DLL found here must be one it exports.  A
      native Windows link names the system directory; a cross link has
      none and trusts the names.  Not owned; may be nil. }
    LibDirs: TStringList;
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
  FObjImports := TDictionary<string, Boolean>.Create();
  FCEntries := TDictionary<string, Boolean>.Create();
  FImpNames := TList<string>.Create();
  FImpIndex := TDictionary<string, Int>.Create();
  FImpTable := TPeImportTableBuilder.Create();
  FBaseRelocs := TList<Int>.Create();
  FUnwStarts := TList<Int64>.Create();
  FUnwEnds := TList<Int64>.Create();
  Subsystem := PeSubsystemConsole;
  DllNameOf := nil;
  LibDirs := nil;
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
  FObjImports.Free();
  FCEntries.Free();
  FImpNames.Free();
  FImpIndex.Free();
  FImpTable.Free();
  FBaseRelocs.Free();
  FUnwStarts.Free();
  FUnwEnds.Free();
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

procedure TPeLinker.ReadImportPairs(AObjIdx: Int; AObj: TElfObjectFile;
  ASec: TRdSection);
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
    if Lib = '' then
    begin
      { a C entry this object defines }
      if not FCEntries.ContainsKey(Sym) then
        FCEntries.Add(Sym, True);
      Continue;
    end;
    if not FObjImports.ContainsKey(IntToStr(AObjIdx) + #0 + Sym) then
      FObjImports.Add(IntToStr(AObjIdx) + #0 + Sym, True);
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
        ReadImportPairs(Oi, Obj, Sec)
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

function TPeLinker.ImportOverridesDefinition(AObjIdx: Int;
  const AName: string): Boolean;
begin
  Result := FObjImports.ContainsKey(IntToStr(AObjIdx) + #0 + AName) and
    not FCEntries.ContainsKey(AName);
end;

function TPeLinker.IsSynthName(const AName: string): Boolean;
begin
  Result := (AName = '__start_blaise_unwind') or
    (AName = '__stop_blaise_unwind') or (AName = '__ImageBase') or
    (AName = '_tls_index');
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
      if Sym.Name = '_tls_index' then
        FWantTlsIndex := True;
      if IsSynthName(Sym.Name) then
        Continue;
      if FDefIndex.ContainsKey(Sym.Name) and
         not ImportOverridesDefinition(Oi, Sym.Name) then
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

const
  { push %rbp; mov %rsp, %rbp }
  FramePrologue: array[0..3] of Byte = ($55, $48, $89, $E5);
  { UNWIND_INFO: version 1, no handler; a 4-byte prologue; two codes;
    frame register RBP (5) at offset 0.  The codes, last prologue
    instruction first: at 4 UWOP_SET_FPREG (3), at 1 UWOP_PUSH_NONVOL (0)
    of RBP. }
  FrameUnwindInfo: array[0..7] of Byte = ($01, $04, $02, $05,
    $04, $03, $01, $50);
  RuntimeFunctionSize = 12;

{ The .text ranges of the routines that open with the Blaise frame (see the
  unit comment): each runs from its symbol to the next routine or the end
  of its input section. }
procedure TPeLinker.CollectUnwindRanges;
var
  Oi, Si, Flat, I, J: Int;
  Obj: TElfObjectFile;
  Sym: TRdSymbol;
  Bounds, Starts: TList<Int64>;
  S, E: Int64;
  Match: Boolean;
begin
  Bounds := TList<Int64>.Create();
  Starts := TList<Int64>.Create();
  try
    for Oi := 0 to FObjs.Count - 1 do
    begin
      Obj := FObjs[Oi];
      for Si := 0 to Obj.Sections.Count - 1 do
      begin
        Flat := FSecFirst[Oi] + Si;
        if FSecStream[Flat] <> stText then Continue;
        Bounds.Add(FSecOff[Flat]);
        Bounds.Add(FSecOff[Flat] + Obj.Sections[Si].Size);
      end;
      for Si := 0 to Obj.Symbols.Count - 1 do
      begin
        Sym := Obj.Symbols[Si];
        if (Sym.Name = '') or (Sym.Shndx = SHN_UNDEF) or
           (Sym.Shndx = SHN_ABS) or (Sym.Shndx = SHN_COMMON) then Continue;
        { routines only: the backend's .L labels inside them are symbols
          too, for the relocations that name them }
        if Sym.SymType <> STT_FUNC then
          Continue;
        Flat := FSecFirst[Oi] + Sym.Shndx;
        if FSecStream[Flat] <> stText then Continue;
        Bounds.Add(FSecOff[Flat] + Sym.Value);
        Starts.Add(FSecOff[Flat] + Sym.Value);
      end;
    end;
    Bounds.Sort(function(A, B: Int64): Int32
      begin
        if A < B then Result := -1
        else if A > B then Result := 1
        else Result := 0;
      end);
    Starts.Sort(function(A, B: Int64): Int32
      begin
        if A < B then Result := -1
        else if A > B then Result := 1
        else Result := 0;
      end);
    J := 0;
    for I := 0 to Starts.Count - 1 do
    begin
      S := Starts[I];
      if (I > 0) and (Starts[I - 1] = S) then Continue;
      while (J < Bounds.Count) and (Bounds[J] <= S) do
        Inc(J);
      if J >= Bounds.Count then Break;
      E := Bounds[J];
      if E - S <= Length(FramePrologue) then Continue;
      Match := True;
      for Si := 0 to High(FramePrologue) do
        if FStreams[stText].Bytes[S + Si] <> FramePrologue[Si] then
          Match := False;
      if not Match then Continue;
      FUnwStarts.Add(S);
      FUnwEnds.Add(E);
    end;
  finally
    Bounds.Free();
    Starts.Free();
  end;
end;

{ Each import from a DLL that LibDirs holds must be a name the DLL
  exports: a misspelt import otherwise links, and the program dies at load
  with STATUS_ENTRYPOINT_NOT_FOUND.  A DLL that is not there, or that
  cannot be read, is trusted. }
procedure TPeLinker.CheckImportsExported;
var
  Exports: TDictionary<string, TStringList>;
  Missing: TStringList;
  I, D: Int;
  Dll, Key, Path, Lib: string;
  Names: TStringList;
  Img: TPeImage;
begin
  if (LibDirs = nil) or (LibDirs.Count = 0) or (FImpNames.Count = 0) then
    Exit;
  Exports := TDictionary<string, TStringList>.Create();
  Missing := TStringList.Create();
  try
    for I := 0 to FImpNames.Count - 1 do
    begin
      if not FImportLib.TryGetValue(FImpNames[I], Lib) then Continue;
      Dll := DllOf(Lib);
      Key := LowerCase(Dll);
      if not Exports.TryGetValue(Key, Names) then
      begin
        Names := nil;
        for D := 0 to LibDirs.Count - 1 do
        begin
          Path := IncludeTrailingPathDelimiter(LibDirs[D]) + Dll;
          if not FileExists(Path) then Continue;
          try
            Img := ParsePeImage(ReadFile(Path), Path);
            try
              Names := TStringList.Create();
              Names.Sorted := True;
              Names.CaseSensitive := True;
              Names.AddStrings(Img.ExportNames);
            finally
              Img.Free();
            end;
          except
            on E: EPeReader do
              Names := nil;
          end;
          Break;
        end;
        Exports.Add(Key, Names);
      end;
      if (Names <> nil) and (Names.IndexOf(FImpNames[I]) < 0) then
        Missing.Add('''' + FImpNames[I] + ''' (' + Dll + ')');
    end;
    if Missing.Count > 0 then
    begin
      Path := '';
      for I := 0 to Missing.Count - 1 do
      begin
        if I > 0 then Path := Path + ', ';
        Path := Path + Missing[I];
      end;
      raise EPeLinker.Create('imported but not exported: ' + Path +
        '; check the name in its external declaration');
    end;
  finally
    { the name lists go with the dictionary, by reference count }
    Exports.Free();
    Missing.Free();
  end;
end;

{ Lay out the image: append the thunks, the import tables, the TLS
  bookkeeping and the unwind data to their streams, then give each stream
  its RVA. }
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
  if FHasTls or FWantTlsIndex then
  begin
    { the index slot the loader writes, named _tls_index; without TLS it
      stays 0 }
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
  { the unwind data: the UNWIND_INFO now, the entries once .text has its
    RVA }
  CollectUnwindRanges();
  if FUnwStarts.Count > 0 then
  begin
    FXdataOff := PeAlignUp(FStreamSize[stRdata], 4);
    FStreams[stRdata].PadTo(FXdataOff);
    for I := 0 to High(FrameUnwindInfo) do
      FStreams[stRdata].PushByte(FrameUnwindInfo[I]);
    FPdataOff := PeAlignUp(FStreams[stRdata].Count, 4);
    FStreams[stRdata].PadTo(FPdataOff +
      Int64(FUnwStarts.Count) * RuntimeFunctionSize);
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

  for I := 0 to FUnwStarts.Count - 1 do
  begin
    Patch32(stRdata, FPdataOff + Int64(I) * RuntimeFunctionSize,
      FTextRva + FUnwStarts[I]);
    Patch32(stRdata, FPdataOff + Int64(I) * RuntimeFunctionSize + 4,
      FTextRva + FUnwEnds[I]);
    Patch32(stRdata, FPdataOff + Int64(I) * RuntimeFunctionSize + 8,
      FRdataRva + FXdataOff);
  end;

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
  else if AName = '_tls_index' then
    Result := FDataRva + FTlsIndexOff
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
  if not ImportOverridesDefinition(AObjIdx, Sym.Name) then
  begin
    Result := DefinedRva(Sym.Name, Found);
    if Found then Exit;
  end;
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
    { The template covers .tbss as well, materialised as zeros, and the
      zero fill is 0: the loader in Windows 11 on ARM sizes the block from
      the raw data range alone, so .tbss counted only as zero fill left
      threadvars outside the allocation (heap corruption at exit). }
    Patch64(stRdata, Off + 8, PeDefaultImageBase + FStreamRva[stTbss] +
      FStreamSize[stTbss]);
    Patch64(stRdata, Off + 16, PeDefaultImageBase + FDataRva + FTlsIndexOff);
    Patch64(stRdata, Off + 24, PeDefaultImageBase + FRdataRva + Off +
      PeTlsDirectorySize);
    Patch32(stRdata, Off + 32, 0);
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
  CheckImportsExported();
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
      { the .tbss bytes follow the .tdata ones as zeros (see the TLS
        directory in ApplyRelocations) }
      FStreams[stTdata].PadTo(FStreamRva[stTbss] + FStreamSize[stTbss] -
        FTlsRva);
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
    if FUnwStarts.Count > 0 then
      W.SetDirectory(PeDirException, FRdataRva + FPdataOff,
        FUnwStarts.Count * RuntimeFunctionSize);
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
