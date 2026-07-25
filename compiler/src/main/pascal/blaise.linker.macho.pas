{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.linker.macho;

// The Mach-O executable linker for macos-arm64 (Phase 5 of the macOS
// bring-up).  Merges MH_OBJECT inputs (parsed by blaise.machoreader),
// resolves every arm64 relocation, and hands the resolved payloads plus
// the rebase/bind facts to TMachOExecWriter, which serialises the
// MH_EXECUTE image (LC_MAIN entry, /usr/lib/dyld, libSystem.B.dylib).
//
// The UNDERSCORE RULE: an external symbol still undefined after all
// objects merge is a libSystem import, bound under '_' + name — the C
// symbol-prefix convention on Mach-O.  Pascal `external name 'open'`
// therefore reaches libSystem's _open with no per-symbol import table
// anywhere in the RTL; the same rule covers stdlib and user `external`
// declarations (this replaces the runtime.libsystem.darwin trampoline
// leaf the original plan called for).
//
//   * a BRANCH26 to an import gets a synthesised STUB (adrp/ldr/br
//     through a GOT slot appended to __data; the slot is dyld-BOUND) —
//     non-lazy binding, no lazy-stub machinery;
//   * an UNSIGNED (absolute pointer) site referencing an import becomes
//     a direct dyld BIND at that address;
//   * an UNSIGNED site referencing an internal symbol gets the final
//     address written plus a dyld REBASE (the image is PIE);
//   * TLV descriptors (__thread_vars) are special-cased: the storage
//     field holds the OFFSET of the variable inside the contiguous TLV
//     content region (__thread_data..__thread_bss), not an address, and
//     the thunk field binds to __tlv_bootstrap like any data import.
//
// Absolute pointers are only legal in writable sections: a .quad in
// __TEXT,__const would need a rebase in a read-only segment, which dyld
// cannot slide — the linker rejects it loudly so the codegen keeps
// pointer-carrying tables in .data.

interface

uses
  SysUtils, Classes, Generics.Collections,
  blaise.machoreader, blaise.machowriter;

type
  EMachOLinker = class(Exception);

  TMachOLinker = class
  private
    FObjs: TList<TMachOFile>;          { owned }
    { merged output streams (indices into these are pre-layout offsets) }
    FText, FConst, FData, FTvars, FTdata: string;
    FTbssSize, FBssSize: Int64;
    { per input section (flat, in FSecFirst[obj]+sectIdx order):
      which stream (-1 = dropped) and the base offset inside it }
    FSecStream: TList<Integer>;
    FSecBase: TList<Int64>;
    FSecFirst: TList<Integer>;         { first flat index per object }
    { defined external symbols: name -> (flat section index, offset) }
    FDefNames: TList<string>;
    FDefSec: TList<Integer>;           { flat section index }
    FDefOff: TList<Int64>;             { offset within that section }
    FDefWeak: TList<Boolean>;
    FDefIndex: TDictionary<string, Integer>;
    { imports (undefined after merge): name -> got slot ordinal or -1 }
    FImpNames: TList<string>;
    FImpGot: TList<Integer>;           { got slot index; -1 = data-only }
    FImpIndex: TDictionary<string, Integer>;
    FNumGot: Integer;
    FStubBase: Int64;                  { offset of stub 0 within FText }
    FGotBase: Int64;                   { offset of got slot 0 within FData }
    FWriter: TMachOExecWriter;
    FLayout: TMachOExecLayout;
    procedure MergeSections;
    procedure CollectSymbols;
    procedure CollectImports;
    procedure SynthesiseStubs;
    procedure ApplyFixups;
    function StreamOfSection(ASect: TMoSection): Integer;
    function SectionVm(AFlat: Integer): Int64;
    function StreamVm(AStream: Integer): Int64;
    function DefinedVm(AIdx: Integer): Int64;
    function ImportOf(const AName: string): Integer;
    function BindNameOf(const AName: string): string;
    procedure PatchStream(AStream: Integer; AOff: Int64; ASize: Integer;
      AValue: Int64);
    function ReadStream(AStream: Integer; AOff: Int64;
      ASize: Integer): Int64;
  public
    constructor Create;
    destructor Destroy; override;
    { Takes ownership of AObj. }
    procedure AddObject(AObj: TMachOFile);
    procedure AddObjectFile(const APath: string);
    { Link everything into an MH_EXECUTE image.  AEntrySym must resolve
      (the backend's program entry is '_main' — the LC_MAIN contract). }
    function Link(const AEntrySym: string): string;
    procedure LinkToFile(const AEntrySym, AOutPath: string);
  end;

implementation

uses
  streams;

const
  smText = 0;
  smConst = 1;
  smData = 2;
  smTvars = 3;
  smTdata = 4;
  smTbss = 5;
  smBss = 6;
  smDropped = -1;

  STUB_SIZE = 12;   { adrp x16 / ldr x16 / br x16 }

function AlignUp(AVal: Int64; AAlign: Int64): Int64;
var
  Rem: Int64;
begin
  if AAlign <= 1 then Exit(AVal);
  Rem := AVal mod AAlign;
  if Rem = 0 then Result := AVal else Result := AVal + (AAlign - Rem);
end;

procedure PadStream(var S: string; AAlign: Integer);
begin
  while (Length(S) mod AAlign) <> 0 do
    S := S + Chr(0);
end;

constructor TMachOLinker.Create;
begin
  inherited Create();
  FObjs := TList<TMachOFile>.Create();
  FSecStream := TList<Integer>.Create();
  FSecBase := TList<Int64>.Create();
  FSecFirst := TList<Integer>.Create();
  FDefNames := TList<string>.Create();
  FDefSec := TList<Integer>.Create();
  FDefOff := TList<Int64>.Create();
  FDefWeak := TList<Boolean>.Create();
  FDefIndex := TDictionary<string, Integer>.Create();
  FImpNames := TList<string>.Create();
  FImpGot := TList<Integer>.Create();
  FImpIndex := TDictionary<string, Integer>.Create();
  FWriter := TMachOExecWriter.Create();
end;

destructor TMachOLinker.Destroy;
var
  I: Integer;
begin
  for I := 0 to FObjs.Count - 1 do
    FObjs.Get(I).Free();
  FObjs.Free();
  FSecStream.Free();
  FSecBase.Free();
  FSecFirst.Free();
  FDefNames.Free();
  FDefSec.Free();
  FDefOff.Free();
  FDefWeak.Free();
  FDefIndex.Free();
  FImpNames.Free();
  FImpGot.Free();
  FImpIndex.Free();
  FWriter.Free();
  inherited Destroy();
end;

procedure TMachOLinker.AddObject(AObj: TMachOFile);
begin
  FObjs.Add(AObj);
end;

procedure TMachOLinker.AddObjectFile(const APath: string);
var
  FIn: TFileInputStream;
  Bytes: string;
begin
  FIn := TFileInputStream.Create(APath);
  try
    SetLength(Bytes, Integer(FIn.Size()));
    if Length(Bytes) > 0 then
      FIn.Read(PChar(Bytes), Length(Bytes));
  finally
    FIn.Free();
  end;
  AddObject(ParseMachO(Bytes, APath));
end;

function TMachOLinker.StreamOfSection(ASect: TMoSection): Integer;
begin
  if (ASect.SegName = '__TEXT') and (ASect.SectName = '__text') then
    Exit(smText);
  if (ASect.SegName = '__TEXT') and (ASect.SectName = '__const') then
    Exit(smConst);
  if (ASect.SegName = '__DATA') and (ASect.SectName = '__data') then
    Exit(smData);
  if (ASect.SegName = '__DATA') and (ASect.SectName = '__thread_vars') then
    Exit(smTvars);
  if (ASect.SegName = '__DATA') and (ASect.SectName = '__thread_data') then
    Exit(smTdata);
  if (ASect.SegName = '__DATA') and (ASect.SectName = '__thread_bss') then
    Exit(smTbss);
  if (ASect.SegName = '__DATA') and (ASect.SectName = '__bss') then
    Exit(smBss);
  { metadata sections an executable does not carry (embedded iface,
    OPDF debug payloads) are dropped; anything else is a hard error so
    a new section kind cannot silently vanish }
  if (ASect.SectName = '__blaise_iface') or (ASect.SegName = '__BLAISE')
     or (ASect.SectName = '__opdf') then
    Exit(smDropped);
  raise EMachOLinker.Create('macho linker: unmapped input section ' +
    ASect.SegName + ',' + ASect.SectName);
end;

procedure TMachOLinker.MergeSections;
var
  I, J, Strm: Integer;
  Obj: TMachOFile;
  Sec: TMoSection;
  Align: Integer;
begin
  for I := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs.Get(I);
    FSecFirst.Add(FSecStream.Count);
    for J := 0 to Obj.Sections.Count - 1 do
    begin
      Sec := Obj.Sections.Get(J);
      Strm := StreamOfSection(Sec);
      Align := 1 shl Sec.Align;
      if Align < 1 then Align := 1;
      case Strm of
        smText:
        begin
          PadStream(FText, Align);
          FSecBase.Add(Length(FText));
          FText := FText + Sec.Data;
        end;
        smConst:
        begin
          PadStream(FConst, Align);
          FSecBase.Add(Length(FConst));
          FConst := FConst + Sec.Data;
        end;
        smData:
        begin
          PadStream(FData, Align);
          FSecBase.Add(Length(FData));
          FData := FData + Sec.Data;
        end;
        smTvars:
        begin
          PadStream(FTvars, Align);
          FSecBase.Add(Length(FTvars));
          FTvars := FTvars + Sec.Data;
        end;
        smTdata:
        begin
          PadStream(FTdata, Align);
          FSecBase.Add(Length(FTdata));
          FTdata := FTdata + Sec.Data;
        end;
        smTbss:
        begin
          FTbssSize := AlignUp(FTbssSize, Align);
          FSecBase.Add(FTbssSize);
          FTbssSize := FTbssSize + Sec.Size;
        end;
        smBss:
        begin
          FBssSize := AlignUp(FBssSize, Align);
          FSecBase.Add(FBssSize);
          FBssSize := FBssSize + Sec.Size;
        end;
      else
        FSecBase.Add(0);
      end;
      FSecStream.Add(Strm);
    end;
  end;
end;

procedure TMachOLinker.CollectSymbols;
var
  I, J, Flat, Prev: Integer;
  Obj: TMachOFile;
  Sym: TMoSymbol;
  Sec: TMoSection;
  IsWeak: Boolean;
begin
  for I := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs.Get(I);
    for J := 0 to Obj.Symbols.Count - 1 do
    begin
      Sym := Obj.Symbols.Get(J);
      if not Sym.IsExt() then Continue;
      if Sym.Sect = 0 then Continue;   { undefined — import candidates }
      Flat := FSecFirst.Get(I) + (Sym.Sect - 1);
      if FSecStream.Get(Flat) = smDropped then Continue;
      Sec := Obj.Sections.Get(Sym.Sect - 1);
      IsWeak := (Sym.Desc and N_WEAK_DEF) <> 0;
      if FDefIndex.TryGetValue(Sym.Name, Prev) then
      begin
        { duplicate definition: weak copies collapse (any one wins);
          two strong copies are a genuine link error }
        if IsWeak then Continue;
        if FDefWeak.Get(Prev) then
        begin
          FDefSec.SetItem(Prev, Flat);
          FDefOff.SetItem(Prev, Sym.Value - Sec.Addr);
          FDefWeak.SetItem(Prev, False);
          Continue;
        end;
        raise EMachOLinker.Create('macho linker: duplicate symbol ' +
          Sym.Name + ' (in ' + Obj.SourceName + ')');
      end;
      FDefIndex.Add(Sym.Name, FDefNames.Count);
      FDefNames.Add(Sym.Name);
      FDefSec.Add(Flat);
      FDefOff.Add(Sym.Value - Sec.Addr);
      FDefWeak.Add(IsWeak);
    end;
  end;
end;

{ The libSystem surface the RTL legitimately imports, plus the dyld TLV
  thunk.  NOT an allow-list — user `external name` imports may reference
  anything — but an unknown name gets a loud build-time NOTE, because a
  compiler-side wrong symbol otherwise surfaces only as a baffling
  dyld abort at launch (see SMOKE_MAC_DYLD_HANDOVER.md: a mis-named RTL
  routine was silently bound to libSystem as __UpperCase). }
function IsKnownLibSystemImport(const AName: string): Boolean;
const
  KNOWN: array[0..45] of string = (
    'abort', 'chdir', 'chmod', 'clock_gettime', 'close', 'dup2',
    'execvp', 'exit', '_exit', 'fork', 'fstat', 'getcwd', 'getenv',
    'getpid', 'gmtime_r', 'localtime_r', 'lseek', 'memcmp', 'memcpy',
    'memmove', 'memset', 'mkdir', 'mkstemp', 'mmap', 'munmap',
    'nanosleep', 'open', 'pipe', 'pthread_create', 'pthread_join',
    'pthread_key_create', 'pthread_mutex_destroy', 'pthread_mutex_init',
    'pthread_mutex_lock', 'pthread_mutex_unlock', 'pthread_setspecific',
    'read', 'rename', 'rmdir', 'stat', 'strlen', 'sysconf', 'system',
    'time', 'unlink', 'waitpid');
var
  I: Integer;
begin
  if (AName = '_tlv_bootstrap') or (AName = '__cxa_atexit') or
     (AName = '__error') or (AName = 'timegm') or (AName = 'write') or
     (AName = 'getrusage') then
    Exit(True);
  for I := 0 to 45 do
    if AName = KNOWN[I] then
      Exit(True);
  Result := False;
end;

function TMachOLinker.BindNameOf(const AName: string): string;
begin
  { the underscore rule — see the unit comment }
  if not IsKnownLibSystemImport(AName) then
    WriteLn(StdErr, 'macho linker: note: binding ''', AName,
      ''' from libSystem as ''_', AName,
      ''' — if that is not a real libSystem export, dyld will abort ' +
      'at launch (a mis-spelled RTL/external symbol looks exactly ' +
      'like this)');
  Result := '_' + AName;
end;

function TMachOLinker.ImportOf(const AName: string): Integer;
begin
  if not FImpIndex.TryGetValue(AName, Result) then
  begin
    Result := FImpNames.Count;
    FImpIndex.Add(AName, Result);
    FImpNames.Add(AName);
    FImpGot.Add(-1);
  end;
end;

procedure TMachOLinker.CollectImports;
var
  I, J, K, Imp: Integer;
  Obj: TMachOFile;
  Sec: TMoSection;
  R: TMoReloc;
  Sym: TMoSymbol;
begin
  { classify every reloc target: an extern reloc naming a symbol that no
    object defines is a libSystem import.  BRANCH26 imports additionally
    need a got slot (their stub loads through it). }
  for I := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs.Get(I);
    for J := 0 to Obj.Sections.Count - 1 do
    begin
      Sec := Obj.Sections.Get(J);
      for K := 0 to Sec.Relocs.Count - 1 do
      begin
        R := Sec.Relocs.Get(K);
        if R.RType = ARM64_RELOC_ADDEND then Continue;
        if not R.IsExtern then
          raise EMachOLinker.Create(
            'macho linker: section-relative relocation in ' +
            Obj.SourceName + ' (only symbol relocations are emitted)');
        Sym := Obj.Symbols.Get(R.SymbolNum);
        if Sym.Sect <> 0 then Continue;              { defined here }
        if FDefIndex.ContainsKey(Sym.Name) then Continue;  { elsewhere }
        Imp := ImportOf(Sym.Name);
        if (R.RType = ARM64_RELOC_BRANCH26) and (FImpGot.Get(Imp) < 0) then
        begin
          FImpGot.SetItem(Imp, FNumGot);
          FNumGot := FNumGot + 1;
        end;
      end;
    end;
  end;
end;

procedure TMachOLinker.SynthesiseStubs;
var
  I: Integer;
begin
  { stub area at the end of __text (one 12-byte stub per got-backed
    import, in got order), got slots at the end of __data.  The stub
    instruction words are written AFTER layout in ApplyFixups — the
    adrp/ldr pair needs the final addresses. }
  PadStream(FText, 4);
  FStubBase := Length(FText);
  for I := 1 to FNumGot * STUB_SIZE do
    FText := FText + Chr(0);
  PadStream(FData, 8);
  FGotBase := Length(FData);
  for I := 1 to FNumGot * 8 do
    FData := FData + Chr(0);
end;

function TMachOLinker.StreamVm(AStream: Integer): Int64;
begin
  case AStream of
    smText:  Result := FLayout.TextVm;
    smConst: Result := FLayout.ConstVm;
    smData:  Result := FLayout.DataVm;
    smTvars: Result := FLayout.TvarsVm;
    smTdata: Result := FLayout.TdataVm;
    smTbss:  Result := FLayout.TbssVm;
    smBss:   Result := FLayout.BssVm;
  else
    raise EMachOLinker.Create('macho linker: address of dropped section');
  end;
end;

function TMachOLinker.SectionVm(AFlat: Integer): Int64;
begin
  Result := StreamVm(FSecStream.Get(AFlat)) + FSecBase.Get(AFlat);
end;

function TMachOLinker.DefinedVm(AIdx: Integer): Int64;
begin
  Result := SectionVm(FDefSec.Get(AIdx)) + FDefOff.Get(AIdx);
end;

procedure TMachOLinker.PatchStream(AStream: Integer; AOff: Int64;
  ASize: Integer; AValue: Int64);

  procedure PutInto(var S: string);
  var
    L: Integer;
  begin
    for L := 0 to ASize - 1 do
      S[AOff + L] := Chr(Integer((AValue shr (L * 8)) and $FF));
  end;

begin
  case AStream of
    smText:  PutInto(FText);
    smConst: PutInto(FConst);
    smData:  PutInto(FData);
    smTvars: PutInto(FTvars);
    smTdata: PutInto(FTdata);
  else
    raise EMachOLinker.Create('macho linker: patch into zerofill section');
  end;
end;

function TMachOLinker.ReadStream(AStream: Integer; AOff: Int64;
  ASize: Integer): Int64;

  function GetFrom(const S: string): Int64;
  var
    M: Integer;
    V: Int64;
  begin
    V := 0;
    for M := 0 to ASize - 1 do
      V := V or (Int64(OrdAt(S, Integer(AOff) + M) and $FF) shl (M * 8));
    Result := V;
  end;

begin
  case AStream of
    smText:  Result := GetFrom(FText);
    smConst: Result := GetFrom(FConst);
    smData:  Result := GetFrom(FData);
    smTvars: Result := GetFrom(FTvars);
    smTdata: Result := GetFrom(FTdata);
  else
    raise EMachOLinker.Create('macho linker: read from zerofill section');
  end;
end;

procedure TMachOLinker.ApplyFixups;
var
  I, J, K, Strm, Imp: Integer;
  Obj: TMachOFile;
  Sec: TMoSection;
  R: TMoReloc;
  Sym: TMoSymbol;
  Flat, DefIdx: Integer;
  SiteOff, SiteVm, Target, Addend, Delta, PageDelta: Int64;
  W: Integer;
  Scale: Integer;
  IsImport: Boolean;
  StubVm, GotVm: Int64;
begin
  { got binds: each slot binds its import at launch (non-lazy) }
  for I := 0 to FImpNames.Count - 1 do
    if FImpGot.Get(I) >= 0 then
      FWriter.AddBind(FLayout.DataVm + FGotBase + Int64(FImpGot.Get(I)) * 8,
        BindNameOf(FImpNames.Get(I)));

  { stub bodies: adrp x16, got@page / ldr x16, [x16, got&fff] / br x16 }
  for I := 0 to FImpNames.Count - 1 do
  begin
    if FImpGot.Get(I) < 0 then Continue;
    StubVm := FLayout.TextVm + FStubBase + Int64(FImpGot.Get(I)) * STUB_SIZE;
    GotVm := FLayout.DataVm + FGotBase + Int64(FImpGot.Get(I)) * 8;
    PageDelta := (GotVm shr 12) - (StubVm shr 12);
    W := Integer($90000010)
      or (Integer(PageDelta and 3) shl 29)
      or (Integer((PageDelta shr 2) and $7FFFF) shl 5);
    PatchStream(smText, FStubBase + Int64(FImpGot.Get(I)) * STUB_SIZE,
      4, W);
    W := Integer($F9400210) or (Integer((GotVm and $FFF) shr 3) shl 10);
    PatchStream(smText, FStubBase + Int64(FImpGot.Get(I)) * STUB_SIZE + 4,
      4, W);
    PatchStream(smText, FStubBase + Int64(FImpGot.Get(I)) * STUB_SIZE + 8,
      4, Integer($D61F0200));
  end;

  for I := 0 to FObjs.Count - 1 do
  begin
    Obj := FObjs.Get(I);
    for J := 0 to Obj.Sections.Count - 1 do
    begin
      Sec := Obj.Sections.Get(J);
      Flat := FSecFirst.Get(I) + J;
      Strm := FSecStream.Get(Flat);
      if Strm = smDropped then Continue;
      Addend := 0;
      for K := 0 to Sec.Relocs.Count - 1 do
      begin
        R := Sec.Relocs.Get(K);
        if R.RType = ARM64_RELOC_ADDEND then
        begin
          { pseudo-reloc: 24-bit addend for the reloc that follows }
          Addend := R.SymbolNum;
          if (Addend and $800000) <> 0 then
            Addend := Addend - $1000000;
          Continue;
        end;
        Sym := Obj.Symbols.Get(R.SymbolNum);
        SiteOff := FSecBase.Get(Flat) + R.Address;
        SiteVm := StreamVm(Strm) + SiteOff;
        IsImport := False;
        Target := 0;
        if Sym.Sect <> 0 then
          Target := SectionVm(FSecFirst.Get(I) + (Sym.Sect - 1))
            + (Sym.Value - Obj.Sections.Get(Sym.Sect - 1).Addr)
        else if FDefIndex.TryGetValue(Sym.Name, DefIdx) then
          Target := DefinedVm(DefIdx)
        else
          IsImport := True;

        case R.RType of
          ARM64_RELOC_UNSIGNED:
          begin
            if R.Length_ <> 3 then
              raise EMachOLinker.Create(
                'macho linker: non-8-byte absolute relocation');
            if IsImport then
            begin
              { direct data bind at the site (e.g. a TLV descriptor's
                thunk pointer to __tlv_bootstrap) }
              PatchStream(Strm, SiteOff, 8, 0);
              FWriter.AddBind(SiteVm, BindNameOf(Sym.Name));
            end
            else if (Strm = smTvars) and
                    ((FSecStream.Get(FSecFirst.Get(I) + (Sym.Sect - 1))
                        = smTdata) or
                     (FSecStream.Get(FSecFirst.Get(I) + (Sym.Sect - 1))
                        = smTbss)) then
            begin
              { TLV descriptor storage field: the OFFSET of the variable
                inside the contiguous TLV content region, not an address }
              PatchStream(Strm, SiteOff, 8,
                Target + ReadStream(Strm, SiteOff, 8)
                - FLayout.TdataVm);
            end
            else if (Strm = smText) or (Strm = smConst) then
              raise EMachOLinker.Create(
                'macho linker: absolute pointer to ' + Sym.Name +
                ' in a read-only section (' + Obj.SourceName +
                ') — pointer-carrying tables belong in .data')
            else
            begin
              PatchStream(Strm, SiteOff, 8,
                Target + ReadStream(Strm, SiteOff, 8));
              FWriter.AddRebase(SiteVm);
            end;
          end;
          ARM64_RELOC_BRANCH26:
          begin
            if IsImport then
            begin
              Imp := ImportOf(Sym.Name);
              Target := FLayout.TextVm + FStubBase
                + Int64(FImpGot.Get(Imp)) * STUB_SIZE;
            end;
            Delta := (Target + Addend) - SiteVm;
            if (Delta > $7FFFFFF) or (Delta < -$8000000) then
              raise EMachOLinker.Create('macho linker: branch to ' +
                Sym.Name + ' out of range');
            W := Integer(ReadStream(Strm, SiteOff, 4));
            W := W or (Integer((Delta shr 2)) and $3FFFFFF);
            PatchStream(Strm, SiteOff, 4, W);
          end;
          ARM64_RELOC_PAGE21,
          ARM64_RELOC_TLVP_LOAD_PAGE21:
          begin
            if IsImport then
              raise EMachOLinker.Create('macho linker: page reference to '
                + 'undefined symbol ' + Sym.Name);
            PageDelta := ((Target + Addend) shr 12) - (SiteVm shr 12);
            W := Integer(ReadStream(Strm, SiteOff, 4));
            W := W or (Integer(PageDelta and 3) shl 29)
              or (Integer((PageDelta shr 2) and $7FFFF) shl 5);
            PatchStream(Strm, SiteOff, 4, W);
          end;
          ARM64_RELOC_PAGEOFF12,
          ARM64_RELOC_TLVP_LOAD_PAGEOFF12:
          begin
            if IsImport then
              raise EMachOLinker.Create('macho linker: pageoff reference '
                + 'to undefined symbol ' + Sym.Name);
            W := Integer(ReadStream(Strm, SiteOff, 4));
            if (R.RType = ARM64_RELOC_TLVP_LOAD_PAGEOFF12)
               and ((W and Integer($3B000000)) = Integer($39000000)) then
            begin
              { TLV RELAXATION, exactly as Apple's ld performs it.  The
                canonical access sequence LOADS the descriptor's address out of
                a __thread_ptrs slot, because the descriptor may live in another
                image.  For one defined in THIS image no slot is needed — the
                address can be formed directly — so the linker rewrites the LDR
                into an ADD.  We never materialise a slot, so this relaxation is
                mandatory, not an optimisation: without it the LDR would deref
                one level too many and we would call through the thunk's
                CONTENTS (BUG-20260726-arm64-tlv-nonldr-reloc).

                Keep Rn (bits 9:5) and Rd (bits 4:0), swap the LDR opcode for
                ADD-immediate (0xF9400000 -> 0x91000000) and write the RAW
                12-bit offset: an add-immediate is unscaled, whereas the LDR it
                replaces had its immediate scaled by the access size. }
              W := Integer($91000000) or (W and $3FF);
              W := W or (Integer((Target + Addend) and $FFF) shl 10);
            end
            else
            begin
              { scaled load/store class shifts the immediate by its size;
                add-immediate takes the raw low 12 bits }
              if (W and Integer($3B000000)) = Integer($39000000) then
                Scale := (W shr 30) and 3
              else
                Scale := 0;
              W := W or (Integer(((Target + Addend) and $FFF) shr Scale)
                shl 10);
            end;
            PatchStream(Strm, SiteOff, 4, W);
          end;
        else
          raise EMachOLinker.Create('macho linker: relocation kind ' +
            IntToStr(R.RType) + ' not supported (in ' + Obj.SourceName
            + ')');
        end;
        Addend := 0;
      end;
    end;
  end;
end;

function TMachOLinker.Link(const AEntrySym: string): string;
var
  I, DefIdx: Integer;
begin
  MergeSections();
  CollectSymbols();
  CollectImports();
  SynthesiseStubs();

  FWriter.SetText(FText);
  FWriter.SetConst(FConst);
  FWriter.SetData(FData);
  FWriter.SetTvars(FTvars);
  FWriter.SetTdata(FTdata);
  FWriter.SetTbssSize(FTbssSize);
  FWriter.SetBssSize(FBssSize);
  FLayout := FWriter.ComputeLayout();

  ApplyFixups();

  { payloads changed in place — hand the patched bytes over (same sizes,
    so the layout is unchanged) }
  FWriter.SetText(FText);
  FWriter.SetConst(FConst);
  FWriter.SetData(FData);
  FWriter.SetTvars(FTvars);
  FWriter.SetTdata(FTdata);

  for I := 0 to FDefNames.Count - 1 do
    FWriter.AddGlobal(FDefNames.Get(I), DefinedVm(I));

  if not FDefIndex.TryGetValue(AEntrySym, DefIdx) then
    raise EMachOLinker.Create('macho linker: entry symbol ' + AEntrySym +
      ' is not defined by any input');
  FWriter.SetEntryTextOffset(
    Integer(DefinedVm(DefIdx) - FLayout.TextVm));

  Result := FWriter.Finish();
end;

procedure TMachOLinker.LinkToFile(const AEntrySym, AOutPath: string);
var
  Bytes: string;
  FOut: TFileOutputStream;
begin
  FWriter.SetIdentifier(ExtractFileName(AOutPath));
  Bytes := Link(AEntrySym);
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
