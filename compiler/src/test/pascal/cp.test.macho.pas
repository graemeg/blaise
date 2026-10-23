{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.macho;

{ Structural tests for the Mach-O container writer (macos-arm64 Phase 1).

  Emit an MH_OBJECT with blaise.machowriter, parse it back with
  blaise.machoreader, and assert the header, section, symbol-ordering and
  relocation shapes.  This is the Linux-CI lane of the macOS target: no
  Mac is needed to pin the container format. }

interface

uses
  SysUtils, Classes, Generics.Collections, blaise.testing, uStrCompat,
  blaise.container.writer,
  blaise.machowriter, blaise.machoreader, blaise.sha256,
  blaise.linker.macho.dylib;

type
  TMachOWriterTests = class(TTestCase)
  private
    function BuildProbe: TMachOFile;
  published
    procedure TestHeader_MagicCpuFiletype;
    procedure TestSections_NamesAndOrder_ZerofillLast;
    procedure TestSections_FileOffsetsAndAddrs;
    procedure TestSymbols_OrderedLocalExtdefUndef;
    procedure TestSymbols_ValuesAreSectionRelativeAddrs;
    procedure TestSymbols_WeakDefCarriesDesc;
    procedure TestReloc_Branch26_ExternPcRel;
    procedure TestReloc_PagePair_Types;
    procedure TestReloc_AddendPseudo_PrecedesTarget;
    procedure TestReloc_Unsigned_AddendFoldedIntoData;
    procedure TestReloc_SymbolIndexRemappedAfterReorder;
    procedure TestReloc_X86KindRejected;
    procedure TestInterfaceSeam_MachOViaIContainerWriter;
  end;

  { MH_EXECUTE structural tests (Phase 1B): build a tiny resolved image
    with TMachOExecWriter and pin the segment/load-command shape dyld
    checks.  LC_CODE_SIGNATURE is Phase 4, so the image is structurally
    complete but not yet runnable on Apple Silicon. }
  TMachOExecWriterTests = class(TTestCase)
  private
    function BuildExec: TMachOFile;
    function RdU32At(const ABuf: string; AOff: Integer): Integer;
    function RdU64At(const ABuf: string; AOff: Integer): Int64;
  published
    procedure TestExecHeader_TypeAndPieFlags;
    procedure TestPageZero_FourGiBUnmapped;
    procedure TestTextSegment_BaseAndPageAlignment;
    procedure TestDataSegment_BssZerofillTail;
    procedure TestLinkEdit_CoversDyldInfoAndSymtab;
    procedure TestEntry_LCMainNotUnixthread;
    procedure TestDylinkerAndLibSystem;
    procedure TestBuildVersion_PlatformMacOS;
    procedure TestRebaseStream_OpcodesDecode;
    procedure TestBindStream_NamesLibSystemSymbol;
    procedure TestGlobals_InSymtab;
    { a library beyond libSystem gets its own LC_LOAD_DYLIB (ordinal 2),
      the load commands grow by it, and each bind carries its library's
      ordinal -- set in the opcode stream only where it changes; a
      flat-lookup bind uses the special ordinal }
    procedure TestExtraDylib_LoadCommandAndBindOrdinals;
    { AddDylib after a layout query would move __TEXT under code already
      resolved against the old address: refused }
    procedure TestExtraDylib_AfterLayoutRefused;
  end;

  { blaise.linker.macho.dylib: what a bound C library exports }
  TMachODylibTests = class(TTestCase)
  published
    procedure TestTbdStub_InstallNameAndSymbols;
    procedure TestTbdStub_ReexportsMarkExportsUnknown;
    procedure TestExportTrie_EveryTerminalNamed;
    procedure TestDylibImage_FatArm64SliceIdAndTrie;
    procedure TestLibSystemLinkNames;
    { the SDK's text stub resolves -lz to the shared-cache install name;
      skipped without Xcode Command Line Tools }
    procedure TestResolve_SdkLibz;
    procedure TestResolve_MissingLibraryNamesTheSearch;
  end;

  TSha256Tests = class(TTestCase)
  published
    procedure TestFipsVectors;
    procedure TestExecSignature_PageHashesRecompute;
  end;

implementation

{ Build a representative object through the IContainerWriter seam:
    __text:  16 bytes, one local label, one global func, a bl to an
             undefined symbol, an adrp/add pair against the global data
    __const: 8 bytes
    __data:  a pointer-sized slot with an UNSIGNED reloc (addend 16)
    __bss:   reserved zerofill
  Symbol insertion order deliberately interleaves undef/global/local so
  the serialised local->extdef->undef reordering is actually exercised. }
function TMachOWriterTests.BuildProbe: TMachOFile;
var
  W: IContainerWriter;
  UndefIdx, GlobIdx, LocIdx, DataIdx: Integer;
  Buf: string;
begin
  W := TMachOObjectWriter.Create();

  { interleave: extern first, then a global, then a local }
  UndefIdx := W.ExternSymbol('_puts');

  W.AlignSection(cskText, 4);
  GlobIdx := W.DefineSymbol('_probe_fn', cskText, 0, 0, csbGlobal, cstFunc);
  W.AppendDWord(cskText, $D503201F);          { nop }
  W.AppendDWord(cskText, $94000000);          { bl 0 (reloc patches) }
  W.AddReloc(cskText, 4, UndefIdx, crkArm64Branch26, 0);
  LocIdx := W.DefineSymbol('Lloc', cskText, 8, 0, csbLocal, cstNone);
  W.AppendDWord(cskText, $90000000);          { adrp x0, _probe_data@PAGE }
  W.AppendDWord(cskText, $91000000);          { add x0, x0, @PAGEOFF }

  W.AlignSection(cskData, 8);
  DataIdx := W.DefineSymbol('_probe_data', cskData, 0, 8, csbGlobal, cstObject);
  W.AppendQWord(cskData, 0);
  W.AddReloc(cskData, 0, GlobIdx, crkArm64Abs64, 16);

  W.AddReloc(cskText, 8, DataIdx, crkArm64Page21, 0);
  W.AddReloc(cskText, 12, DataIdx, crkArm64PageOff12, 0);

  W.AlignSection(cskRodata, 8);
  W.AppendQWord(cskRodata, $1122334455667788);

  W.ReserveBss(cskBss, 32);

  { weak-defined global in __data }
  W.DefineSymbol('_probe_weak', cskData, 8, 0, csbWeak, cstObject);
  W.AppendQWord(cskData, 0);

  Buf := W.Finish();
  Result := ParseMachO(Buf, 'probe.o');
end;

procedure TMachOWriterTests.TestHeader_MagicCpuFiletype;
var
  F: TMachOFile;
begin
  F := BuildProbe();
  try
    AssertEquals(CPU_TYPE_ARM64, F.CpuType);
    AssertEquals(CPU_SUBTYPE_ARM64_ALL, F.CpuSubtype);
    AssertEquals(MH_OBJECT, F.FileType);
    AssertTrue('MH_SUBSECTIONS_VIA_SYMBOLS set',
      (F.Flags and MH_SUBSECTIONS_VIA_SYMBOLS) <> 0);
    AssertEquals(1, F.Segments.Count);
    AssertEquals('', F.Segments.Get(0).Name);
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestSections_NamesAndOrder_ZerofillLast;
var
  F: TMachOFile;
  I, TextIdx, BssIdx: Integer;
begin
  F := BuildProbe();
  try
    AssertTrue('__text present', F.FindSection('__TEXT', '__text') <> nil);
    AssertTrue('__const present', F.FindSection('__TEXT', '__const') <> nil);
    AssertTrue('__data present', F.FindSection('__DATA', '__data') <> nil);
    AssertTrue('__bss present', F.FindSection('__DATA', '__bss') <> nil);
    AssertTrue('__bss is zerofill',
      (F.FindSection('__DATA', '__bss').Flags and $FF) = S_ZEROFILL);
    TextIdx := -1;
    BssIdx := -1;
    for I := 0 to F.Sections.Count - 1 do
    begin
      if F.Sections.Get(I).SectName = '__text' then TextIdx := I;
      if F.Sections.Get(I).SectName = '__bss' then BssIdx := I;
    end;
    AssertTrue('zerofill section serialised after file-backed ones',
      BssIdx > TextIdx);
    AssertEquals('zerofill has no file offset', 0,
      F.FindSection('__DATA', '__bss').Offset);
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestSections_FileOffsetsAndAddrs;
var
  F: TMachOFile;
  T: TMoSection;
begin
  F := BuildProbe();
  try
    T := F.FindSection('__TEXT', '__text');
    AssertEquals(16, Integer(T.Size));
    AssertTrue('text data offset lands after the load commands',
      T.Offset >= 32);
    AssertEquals('text bytes round-trip: nop first',
      $1F, StrAt(T.Data, 0));
    AssertEquals('text addr starts the object vm layout', 0, Integer(T.Addr));
    AssertTrue('data addr follows text/const',
      F.FindSection('__DATA', '__data').Addr >=
      T.Addr + T.Size);
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestSymbols_OrderedLocalExtdefUndef;
var
  F: TMachOFile;
begin
  F := BuildProbe();
  try
    { local (Lloc), extdef (_probe_fn/_probe_data/_probe_weak), undef (_puts) }
    AssertEquals(0, F.ILocalSym);
    AssertEquals(1, F.NLocalSym);
    AssertEquals(1, F.IExtDefSym);
    AssertEquals(3, F.NExtDefSym);
    AssertEquals(4, F.IUndefSym);
    AssertEquals(1, F.NUndefSym);
    AssertEquals('Lloc', F.Symbols.Get(0).Name);
    AssertEquals('_puts', F.Symbols.Get(4).Name);
    AssertTrue('undef symbol shape', F.Symbols.Get(4).IsUndef());
    AssertTrue('undef symbol external', F.Symbols.Get(4).IsExt());
    AssertTrue('local symbol not external', not F.Symbols.Get(0).IsExt());
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestSymbols_ValuesAreSectionRelativeAddrs;
var
  F: TMachOFile;
  S: TMoSymbol;
  D: TMoSection;
begin
  F := BuildProbe();
  try
    S := F.FindSymbol('Lloc');
    AssertTrue(S <> nil);
    AssertEquals('n_value = section addr + offset', 8, Integer(S.Value));
    S := F.FindSymbol('_probe_data');
    D := F.FindSection('__DATA', '__data');
    AssertEquals(Integer(D.Addr), Integer(S.Value));
    AssertEquals('n_sect is the 1-based ordinal of __data',
      3, S.Sect);   { emitted order: __text(1) __const(2) __data(3) }
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestSymbols_WeakDefCarriesDesc;
var
  F: TMachOFile;
  S: TMoSymbol;
begin
  F := BuildProbe();
  try
    S := F.FindSymbol('_probe_weak');
    AssertTrue(S <> nil);
    AssertTrue('weak definition flagged N_WEAK_DEF',
      (S.Desc and N_WEAK_DEF) <> 0);
    AssertTrue('weak definition still external', S.IsExt());
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestReloc_Branch26_ExternPcRel;
var
  F: TMachOFile;
  T: TMoSection;
  R: TMoReloc;
begin
  F := BuildProbe();
  try
    T := F.FindSection('__TEXT', '__text');
    AssertEquals(3, T.Relocs.Count);   { branch26 + page21 + pageoff12 }
    R := T.Relocs.Get(0);
    AssertEquals(ARM64_RELOC_BRANCH26, R.RType);
    AssertEquals(4, R.Address);
    AssertTrue('branch26 is pc-relative', R.PcRel);
    AssertTrue('branch26 is extern', R.IsExtern);
    AssertEquals('branch26 width 4 bytes', 2, R.Length_);
    AssertEquals('targets _puts',
      '_puts', F.Symbols.Get(R.SymbolNum).Name);
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestReloc_PagePair_Types;
var
  F: TMachOFile;
  T: TMoSection;
begin
  F := BuildProbe();
  try
    T := F.FindSection('__TEXT', '__text');
    AssertEquals(ARM64_RELOC_PAGE21, T.Relocs.Get(1).RType);
    AssertTrue('page21 pc-relative', T.Relocs.Get(1).PcRel);
    AssertEquals(ARM64_RELOC_PAGEOFF12, T.Relocs.Get(2).RType);
    AssertTrue('pageoff12 not pc-relative', not T.Relocs.Get(2).PcRel);
    AssertEquals('page21 targets _probe_data',
      '_probe_data', F.Symbols.Get(T.Relocs.Get(1).SymbolNum).Name);
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestReloc_AddendPseudo_PrecedesTarget;
var
  W: IContainerWriter;
  F: TMachOFile;
  T: TMoSection;
  Idx: Integer;
begin
  W := TMachOObjectWriter.Create();
  Idx := W.ExternSymbol('_target');
  W.AppendDWord(cskText, $94000000);
  W.AddReloc(cskText, 0, Idx, crkArm64Branch26, 8);
  F := ParseMachO(W.Finish(), 'addend.o');
  try
    T := F.FindSection('__TEXT', '__text');
    AssertEquals(2, T.Relocs.Count);
    AssertEquals('pseudo first', ARM64_RELOC_ADDEND, T.Relocs.Get(0).RType);
    AssertEquals('addend rides in r_symbolnum', 8, T.Relocs.Get(0).SymbolNum);
    AssertTrue('pseudo is non-extern', not T.Relocs.Get(0).IsExtern);
    AssertEquals('same address as its target reloc',
      T.Relocs.Get(1).Address, T.Relocs.Get(0).Address);
    AssertEquals(ARM64_RELOC_BRANCH26, T.Relocs.Get(1).RType);
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestReloc_Unsigned_AddendFoldedIntoData;
var
  F: TMachOFile;
  D: TMoSection;
  R: TMoReloc;
begin
  F := BuildProbe();
  try
    D := F.FindSection('__DATA', '__data');
    AssertEquals(1, D.Relocs.Count);
    R := D.Relocs.Get(0);
    AssertEquals(ARM64_RELOC_UNSIGNED, R.RType);
    AssertEquals('pointer width 8 bytes', 3, R.Length_);
    AssertTrue('absolute, not pc-relative', not R.PcRel);
    { the addend (16) was folded into the slot bytes, not a pseudo-reloc }
    AssertEquals(16, StrAt(D.Data, 0));
    AssertEquals(0, StrAt(D.Data, 1));
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestReloc_SymbolIndexRemappedAfterReorder;
var
  F: TMachOFile;
  T: TMoSection;
begin
  F := BuildProbe();
  try
    { _puts was inserted FIRST (writer index 0) but serialises LAST
      (undef range).  The branch26 record must reference the serialised
      index — if the remap were missing it would name Lloc instead. }
    T := F.FindSection('__TEXT', '__text');
    AssertEquals(4, T.Relocs.Get(0).SymbolNum);
    AssertEquals('_puts', F.Symbols.Get(T.Relocs.Get(0).SymbolNum).Name);
  finally
    F.Free();
  end;
end;

procedure TMachOWriterTests.TestReloc_X86KindRejected;
var
  W: IContainerWriter;
  Raised: Boolean;
  Buf: string;
begin
  W := TMachOObjectWriter.Create();
  W.AppendDWord(cskText, 0);
  W.AddReloc(cskText, 0, W.ExternSymbol('x'), crkPC32, 0);
  Raised := False;
  try
    Buf := W.Finish();
  except
    on EMachOWriter do
      Raised := True;
  end;
  AssertTrue('x86-64 reloc kind rejected by the arm64 Mach-O writer', Raised);
end;

procedure TMachOWriterTests.TestInterfaceSeam_MachOViaIContainerWriter;
var
  W: IContainerWriter;
  Buf: string;
begin
  { The Bridge in action: the same seam the assembler drives TElfObjectWriter
    through produces a Mach-O object when the concrete writer differs. }
  W := TMachOObjectWriter.Create();
  W.AppendDWord(cskText, $D65F03C0);   { ret }
  W.DefineSymbol('_f', cskText, 0, 0, csbGlobal, cstFunc);
  Buf := W.Finish();
  AssertEquals($CF, StrAt(Buf, 0));
  AssertEquals($FA, StrAt(Buf, 1));
  AssertEquals($ED, StrAt(Buf, 2));
  AssertEquals($FE, StrAt(Buf, 3));
end;

{ ---- TMachOExecWriterTests ---- }

function TMachOExecWriterTests.RdU32At(const ABuf: string; AOff: Integer): Integer;
begin
  Result := StrAt(ABuf, AOff)
         or (StrAt(ABuf, AOff + 1) shl 8)
         or (StrAt(ABuf, AOff + 2) shl 16)
         or (StrAt(ABuf, AOff + 3) shl 24);
end;

function TMachOExecWriterTests.RdU64At(const ABuf: string; AOff: Integer): Int64;
begin
  Result := (Int64(RdU32At(ABuf, AOff)) and $FFFFFFFF)
    or (Int64(RdU32At(ABuf, AOff + 4)) shl 32);
end;

function TMachOExecWriterTests.BuildExec: TMachOFile;
var
  W: TMachOExecWriter;
  T, D: string;
  I: Integer;
  Buf: string;
begin
  { 8 instructions of nop + ret }
  T := '';
  for I := 0 to 6 do
    T := T + Chr($1F) + Chr($20) + Chr($03) + Chr($D5);   { nop }
  T := T + Chr($C0) + Chr($03) + Chr($5F) + Chr($D6);     { ret }
  D := '';
  for I := 0 to 15 do
    D := D + Chr(0);

  W := TMachOExecWriter.Create();
  try
    W.SetText(T);
    W.SetConst(Chr(1) + Chr(2) + Chr(3) + Chr(4));
    W.SetData(D);
    W.SetBssSize(64);
    W.SetEntryTextOffset(4);
    { __DATA starts at the first 16 KiB page after __TEXT; with this tiny
      payload that is exactly base + one page. }
    W.AddRebase($100000000 + $4000);
    W.AddBind($100000000 + $4000 + 8, '_environ');
    W.AddGlobal('_main', W.TextVmAddr() + 4);
    Buf := W.Finish();
  finally
    W.Free();
  end;
  Result := ParseMachO(Buf, 'probe_exec');
end;

procedure TMachOExecWriterTests.TestExecHeader_TypeAndPieFlags;
var
  F: TMachOFile;
begin
  F := BuildExec();
  try
    AssertEquals(MH_EXECUTE, F.FileType);
    AssertEquals(CPU_TYPE_ARM64, F.CpuType);
    AssertTrue('MH_PIE set', (F.Flags and MH_PIE) <> 0);
    AssertTrue('MH_DYLDLINK set', (F.Flags and MH_DYLDLINK) <> 0);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestPageZero_FourGiBUnmapped;
var
  F: TMachOFile;
  S: TMoSegment;
begin
  F := BuildExec();
  try
    S := F.FindSegment('__PAGEZERO');
    AssertTrue(S <> nil);
    AssertEquals(0, Integer(S.VmAddr));
    AssertTrue('vmsize is 4 GiB', S.VmSize = $100000000);
    AssertEquals(0, Integer(S.FileSize));
    AssertEquals('no access', 0, S.InitProt);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestTextSegment_BaseAndPageAlignment;
var
  F: TMachOFile;
  S: TMoSegment;
  T: TMoSection;
begin
  F := BuildExec();
  try
    S := F.FindSegment('__TEXT');
    AssertTrue(S <> nil);
    AssertTrue('__TEXT at the 4 GiB base', S.VmAddr = $100000000);
    AssertEquals('maps from file offset 0', 0, Integer(S.FileOff));
    AssertEquals('16 KiB-aligned filesize', 0,
      Integer(S.FileSize mod $4000));
    AssertEquals('r-x', 5, S.InitProt);
    T := F.FindSection('__TEXT', '__text');
    AssertTrue(T <> nil);
    AssertTrue('vmaddr = base + fileoff',
      T.Addr = $100000000 + T.Offset);
    AssertEquals('ret rides at the right file spot',
      $D6, StrAt(F.Raw, T.Offset + Integer(T.Size) - 1));
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestDataSegment_BssZerofillTail;
var
  F: TMachOFile;
  S: TMoSegment;
  B: TMoSection;
begin
  F := BuildExec();
  try
    S := F.FindSegment('__DATA');
    AssertTrue(S <> nil);
    AssertEquals('16 KiB-aligned vmaddr', 0, Integer(S.VmAddr mod $4000));
    AssertEquals('rw-', 3, S.InitProt);
    B := F.FindSection('__DATA', '__bss');
    AssertTrue(B <> nil);
    AssertEquals('zerofill', S_ZEROFILL, B.Flags and $FF);
    AssertEquals(64, Integer(B.Size));
    AssertEquals('no file bytes', 0, B.Offset);
    AssertTrue('bss follows data in vm',
      B.Addr = F.FindSection('__DATA', '__data').Addr + 16);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestLinkEdit_CoversDyldInfoAndSymtab;
var
  F: TMachOFile;
  S: TMoSegment;
  LC: TMoLoadCmd;
  RebOff, RebSize, BindOff, BindSize: Integer;
begin
  F := BuildExec();
  try
    S := F.FindSegment('__LINKEDIT');
    AssertTrue(S <> nil);
    LC := F.FindLoadCmd(LC_DYLD_INFO_ONLY);
    AssertTrue('LC_DYLD_INFO_ONLY present', LC <> nil);
    RebOff := RdU32At(F.Raw, LC.Offset + 8);
    RebSize := RdU32At(F.Raw, LC.Offset + 12);
    BindOff := RdU32At(F.Raw, LC.Offset + 16);
    BindSize := RdU32At(F.Raw, LC.Offset + 20);
    AssertTrue('rebase stream present', RebSize > 0);
    AssertTrue('bind stream present', BindSize > 0);
    AssertTrue('rebase inside __LINKEDIT',
      (RebOff >= S.FileOff) and (RebOff + RebSize <= S.FileOff + S.FileSize));
    AssertTrue('bind inside __LINKEDIT',
      (BindOff >= S.FileOff) and (BindOff + BindSize <= S.FileOff + S.FileSize));
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestEntry_LCMainNotUnixthread;
var
  F: TMachOFile;
  LC: TMoLoadCmd;
  EntryOff: Int64;
  T: TMoSection;
begin
  F := BuildExec();
  try
    AssertTrue('LC_UNIXTHREAD absent', F.FindLoadCmd(LC_UNIXTHREAD) = nil);
    LC := F.FindLoadCmd(LC_MAIN);
    AssertTrue('LC_MAIN present', LC <> nil);
    EntryOff := RdU64At(F.Raw, LC.Offset + 8);
    T := F.FindSection('__TEXT', '__text');
    AssertTrue('entryoff = __text fileoff + 4',
      EntryOff = T.Offset + 4);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestDylinkerAndLibSystem;
var
  F: TMachOFile;
  LC: TMoLoadCmd;
begin
  F := BuildExec();
  try
    LC := F.FindLoadCmd(LC_LOAD_DYLINKER);
    AssertTrue(LC <> nil);
    AssertTrue('dyld path',
      Pos('/usr/lib/dyld', Copy(F.Raw, LC.Offset, LC.CmdSize)) >= 0);
    LC := F.FindLoadCmd(LC_LOAD_DYLIB);
    AssertTrue(LC <> nil);
    AssertTrue('libSystem path',
      Pos('/usr/lib/libSystem.B.dylib', Copy(F.Raw, LC.Offset, LC.CmdSize)) >= 0);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestBuildVersion_PlatformMacOS;
var
  F: TMachOFile;
  LC: TMoLoadCmd;
begin
  F := BuildExec();
  try
    LC := F.FindLoadCmd(LC_BUILD_VERSION);
    AssertTrue(LC <> nil);
    AssertEquals(PLATFORM_MACOS, RdU32At(F.Raw, LC.Offset + 8));
    AssertEquals('minos 11.0', $000B0000, RdU32At(F.Raw, LC.Offset + 12));
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestRebaseStream_OpcodesDecode;
var
  F: TMachOFile;
  LC: TMoLoadCmd;
  RebOff: Integer;
begin
  F := BuildExec();
  try
    LC := F.FindLoadCmd(LC_DYLD_INFO_ONLY);
    RebOff := RdU32At(F.Raw, LC.Offset + 8);
    { SET_TYPE_IMM|POINTER, SET_SEGMENT_AND_OFFSET_ULEB|2, uleb(0),
      DO_REBASE_IMM_TIMES|1, DONE }
    AssertEquals($11, StrAt(F.Raw, RebOff));
    AssertEquals($22, StrAt(F.Raw, RebOff + 1));
    AssertEquals(0, StrAt(F.Raw, RebOff + 2));
    AssertEquals($51, StrAt(F.Raw, RebOff + 3));
    AssertEquals(0, StrAt(F.Raw, RebOff + 4));
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestBindStream_NamesLibSystemSymbol;
var
  F: TMachOFile;
  LC: TMoLoadCmd;
  BindOff, BindSize: Integer;
begin
  F := BuildExec();
  try
    LC := F.FindLoadCmd(LC_DYLD_INFO_ONLY);
    BindOff := RdU32At(F.Raw, LC.Offset + 16);
    BindSize := RdU32At(F.Raw, LC.Offset + 20);
    AssertEquals('dylib ordinal 1 first', $11, StrAt(F.Raw, BindOff));
    AssertEquals('bind type pointer', $51, StrAt(F.Raw, BindOff + 1));
    AssertTrue('bound symbol name embedded',
      Pos('_environ', Copy(F.Raw, BindOff, BindSize)) >= 0);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestGlobals_InSymtab;
var
  F: TMachOFile;
  S: TMoSymbol;
  T: TMoSection;
begin
  F := BuildExec();
  try
    S := F.FindSymbol('_main');
    AssertTrue(S <> nil);
    AssertTrue('external', S.IsExt());
    T := F.FindSection('__TEXT', '__text');
    AssertTrue('addr = __text vmaddr + 4', S.Value = T.Addr + 4);
    AssertEquals('n_sect = __text ordinal', 1, S.Sect);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestExtraDylib_LoadCommandAndBindOrdinals;
var
  W: TMachOExecWriter;
  F: TMachOFile;
  LC: TMoLoadCmd;
  Buf, Bind: string;
  Base: Int64;
  I, NDylibs, BindOff, BindSize, PZ, PC: Integer;
begin
  W := TMachOExecWriter.Create();
  try
    W.SetText(Chr($C0) + Chr($03) + Chr($5F) + Chr($D6));
    Buf := '';
    for I := 0 to 31 do
      Buf := Buf + Chr(0);
    W.SetData(Buf);
    W.SetEntryTextOffset(0);
    AssertEquals('ordinal of the first extra dylib', 2,
      W.AddDylib('/usr/lib/libz.1.dylib'));
    Base := $100000000 + $4000;
    W.AddBind(Base, '_environ');
    W.AddBind(Base + 8, '_crc32', 2);
    W.AddBind(Base + 16, '_zlibVersion', 2);
    W.AddBind(Base + 24, '_anything', BIND_SPECIAL_DYLIB_FLAT_LOOKUP);
    AssertEquals('load commands grew by the dylib command',
      1176 + 48, W.ExecSizeOfCmds());
    W.AddGlobal('_main', W.TextVmAddr());
    Buf := W.Finish();
  finally
    W.Free();
  end;
  F := ParseMachO(Buf, 'probe_dylib');
  try
    NDylibs := 0;
    for I := 0 to F.LoadCmds.Count - 1 do
    begin
      LC := F.LoadCmds.Get(I);
      if LC.Cmd = LC_LOAD_DYLIB then
      begin
        NDylibs := NDylibs + 1;
        if NDylibs = 2 then
          AssertTrue('second dylib is libz',
            Pos('/usr/lib/libz.1.dylib', Copy(F.Raw, LC.Offset, LC.CmdSize)) >= 0);
      end;
    end;
    AssertEquals('libSystem + libz', 2, NDylibs);
    LC := F.FindLoadCmd(LC_DYLD_INFO_ONLY);
    BindOff := RdU32At(F.Raw, LC.Offset + 16);
    BindSize := RdU32At(F.Raw, LC.Offset + 20);
    Bind := Copy(F.Raw, BindOff, BindSize);
    PC := Pos('_crc32', Bind);
    PZ := Pos('_zlibVersion', Bind);
    AssertTrue('libSystem ordinal before _environ',
      Pos(Chr($11), Copy(Bind, 0, Pos('_environ', Bind))) >= 0);
    AssertTrue('ordinal 2 set before _crc32',
      Pos(Chr($12), Copy(Bind, Pos('_environ', Bind), PC - Pos('_environ', Bind))) >= 0);
    AssertTrue('ordinal not re-set between two libz binds',
      Pos(Chr($12), Copy(Bind, PC, PZ - PC)) < 0);
    AssertTrue('flat lookup before _anything (SET_DYLIB_SPECIAL_IMM -2)',
      Pos(Chr($3E), Copy(Bind, PZ, Pos('_anything', Bind) - PZ)) >= 0);
  finally
    F.Free();
  end;
end;

procedure TMachOExecWriterTests.TestExtraDylib_AfterLayoutRefused;
var
  W: TMachOExecWriter;
  Raised: Boolean;
begin
  W := TMachOExecWriter.Create();
  try
    W.TextVmAddr();
    Raised := False;
    try
      W.AddDylib('/usr/lib/libz.1.dylib');
    except
      on E: EMachOWriter do Raised := True;
    end;
    AssertTrue('refused', Raised);
  finally
    W.Free();
  end;
end;

{ ---- TMachODylibTests ---- }

procedure TMachODylibTests.TestTbdStub_InstallNameAndSymbols;
const
  Stub = '--- !tapi-tbd' + #10 +
    'tbd-version:     4' + #10 +
    'targets:         [ x86_64-macos, arm64-macos ]' + #10 +
    'install-name:    ''/usr/lib/libz.1.dylib''' + #10 +
    'exports:' + #10 +
    '  - targets:         [ x86_64-macos, arm64-macos ]' + #10 +
    '    symbols:         [ _adler32, _crc32,' + #10 +
    '                       _zlibVersion ]' + #10 +
    '    weak-symbols:    [ _zWeak ]' + #10 +
    '...' + #10;
var
  D: TMachODylib;
begin
  D := TMachODylib.Create();
  try
    ReadTbdStub(Stub, D);
    AssertEquals('/usr/lib/libz.1.dylib', D.InstallName);
    AssertTrue('exports known', D.ExportsKnown);
    AssertTrue('_crc32', D.ExportSet.Contains('_crc32'));
    AssertTrue('_zlibVersion (continued line)', D.ExportSet.Contains('_zlibVersion'));
    AssertTrue('weak symbol', D.ExportSet.Contains('_zWeak'));
    AssertTrue('not a target name', not D.ExportSet.Contains('arm64-macos'));
  finally
    D.Free();
  end;
end;

procedure TMachODylibTests.TestTbdStub_ReexportsMarkExportsUnknown;
var
  D: TMachODylib;
begin
  D := TMachODylib.Create();
  try
    ReadTbdStub('install-name: ''/usr/lib/libSystem.B.dylib''' + #10 +
      'reexported-libraries:' + #10 + '  - libraries: [ /usr/lib/system/libc.dylib ]' + #10, D);
    AssertEquals('/usr/lib/libSystem.B.dylib', D.InstallName);
    AssertTrue('exports not all read', not D.ExportsKnown);
  finally
    D.Free();
  end;
end;

{ A trie node: <terminal size uleb> [terminal info] <child count> then per
  child <edge NUL> <child offset uleb>. }
function TrieOf(): string;
begin
  { node  0 (bytes 0..4):   not terminal, 1 child '_' -> 5
    node  5 (bytes 5..12):  not terminal, 2 children 'a' -> 13, 'b' -> 17
    node 13 (bytes 13..16): terminal (2 info bytes), 0 children
    node 17 (bytes 17..23): terminal (2 info bytes), 1 child 'c' -> 24
    node 24 (bytes 24..27): terminal (2 info bytes), 0 children }
  Result := Chr(0) + Chr(1) + '_' + Chr(0) + Chr(5) +
    Chr(0) + Chr(2) + 'a' + Chr(0) + Chr(13) + 'b' + Chr(0) + Chr(17) +
    Chr(2) + Chr(0) + Chr(0) + Chr(0) +
    Chr(2) + Chr(0) + Chr(0) + Chr(1) + 'c' + Chr(0) + Chr(24) +
    Chr(2) + Chr(0) + Chr(0) + Chr(0);
end;

procedure TMachODylibTests.TestExportTrie_EveryTerminalNamed;
var
  S: TSet<string>;
  T: string;
begin
  T := TrieOf();
  AssertEquals('trie size', 28, Length(T));
  S := TSet<string>.Create();
  try
    ReadExportTrie('xx' + T, 2, Length(T), S);
    AssertEquals('three symbols', 3, S.Count);
    AssertTrue('_a', S.Contains('_a'));
    AssertTrue('_b', S.Contains('_b'));
    AssertTrue('_bc', S.Contains('_bc'));
    AssertTrue('the bare prefix is not a symbol', not S.Contains('_'));
  finally
    S.Free();
  end;
end;

function Le32(V: Integer): string;
begin
  Result := Chr(V and $FF) + Chr((V shr 8) and $FF) + Chr((V shr 16) and $FF) +
    Chr((V shr 24) and $FF);
end;

function Be32Of(V: Integer): string;
begin
  Result := Chr((V shr 24) and $FF) + Chr((V shr 16) and $FF) +
    Chr((V shr 8) and $FF) + Chr(V and $FF);
end;

procedure TMachODylibTests.TestDylibImage_FatArm64SliceIdAndTrie;
var
  Thin, Name, Trie, Fat: string;
  IdCmd, TrieCmd: string;
  D: TMachODylib;
  TrieOff: Integer;
begin
  Name := '/opt/x/libdemo.1.dylib' + Chr(0);
  while (Length(Name) mod 8) <> 0 do Name := Name + Chr(0);
  IdCmd := Le32($0D) + Le32(24 + Length(Name)) + Le32(24) + Le32(0) +
    Le32($10000) + Le32($10000) + Name;
  Trie := TrieOf();
  TrieOff := 32 + Length(IdCmd) + 16;
  TrieCmd := Le32(Integer($80000033)) + Le32(16) + Le32(TrieOff) + Le32(Length(Trie));
  Thin := Le32(Integer($FEEDFACF)) + Le32($0100000C) + Le32(0) + Le32(6) +
    Le32(2) + Le32(Length(IdCmd) + Length(TrieCmd)) + Le32(0) + Le32(0) +
    IdCmd + TrieCmd + Trie;
  { a fat wrapper: an x86_64 entry first (must be skipped), then arm64 }
  Fat := Be32Of(Integer($CAFEBABE)) + Be32Of(2) +
    Be32Of($01000007) + Be32Of(3) + Be32Of(64) + Be32Of(4) + Be32Of(0) +
    Be32Of($0100000C) + Be32Of(0) + Be32Of(64) + Be32Of(Length(Thin)) + Be32Of(0);
  while Length(Fat) < 64 do Fat := Fat + Chr(0);
  Fat := Fat + Thin;
  D := TMachODylib.Create();
  try
    ReadDylibImage(Fat, D);
    AssertEquals('/opt/x/libdemo.1.dylib', D.InstallName);
    AssertTrue('_bc from the trie', D.ExportSet.Contains('_bc'));
    AssertTrue('exports known', D.ExportsKnown);
  finally
    D.Free();
  end;
end;

procedure TMachODylibTests.TestLibSystemLinkNames;
begin
  AssertTrue('c', IsLibSystemLib('c'));
  AssertTrue('pthread', IsLibSystemLib('pthread'));
  AssertTrue('m', IsLibSystemLib('M'));
  AssertTrue('z is its own library', not IsLibSystemLib('z'));
  AssertTrue('ssl is its own library', not IsLibSystemLib('ssl'));
end;

procedure TMachODylibTests.TestResolve_SdkLibz;
const
  Sdk = '/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib';
var
  Dirs: TStringList;
  D: TMachODylib;
begin
  if not FileExists(Sdk + '/libz.tbd') then
  begin
    Ignore('no macOS SDK text stubs');
    Exit;
  end;
  Dirs := TStringList.Create();
  try
    Dirs.Add(Sdk);
    D := ResolveMachODylib('z', Dirs);
    try
      AssertEquals('/usr/lib/libz.1.dylib', D.InstallName);
      AssertTrue('exports _crc32', D.ExportSet.Contains('_crc32'));
    finally
      D.Free();
    end;
  finally
    Dirs.Free();
  end;
end;

procedure TMachODylibTests.TestResolve_MissingLibraryNamesTheSearch;
var
  Dirs: TStringList;
  Msg: string;
begin
  Dirs := TStringList.Create();
  try
    Dirs.Add('/nonexistent-blaise-dir');
    Msg := '';
    try
      ResolveMachODylib('nosuchlib', Dirs).Free();
    except
      on E: EMachODylib do Msg := E.Message;
    end;
    AssertTrue('names the library: ' + Msg, Pos('''nosuchlib''', Msg) >= 0);
    AssertTrue('names the search path: ' + Msg,
      Pos('/nonexistent-blaise-dir', Msg) >= 0);
    AssertTrue('suggests --lib-path: ' + Msg, Pos('--lib-path', Msg) >= 0);
  finally
    Dirs.Free();
  end;
end;

{ ---- TSha256Tests ---- }

procedure TSha256Tests.TestFipsVectors;
begin
  AssertEquals('ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad',
    Sha256Hex('abc'));
  AssertEquals('e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
    Sha256Hex(''));
  AssertEquals('248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1',
    Sha256Hex('abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq'));
end;

procedure TSha256Tests.TestExecSignature_PageHashesRecompute;
var
  W: TMachOExecWriter;
  Img, Page, Slot: string;
  SigOff, CdOff, HashOff, CodeLimit: Integer;
  NSlots, I, PageLen: Integer;

  function BeU32(AOff: Integer): Integer;
  begin
    Result := (StrAt(Img, AOff) shl 24) or (StrAt(Img, AOff + 1) shl 16)
      or (StrAt(Img, AOff + 2) shl 8) or StrAt(Img, AOff + 3);
  end;

  function LeU32(AOff: Integer): Integer;
  begin
    Result := StrAt(Img, AOff) or (StrAt(Img, AOff + 1) shl 8)
      or (StrAt(Img, AOff + 2) shl 16) or (StrAt(Img, AOff + 3) shl 24);
  end;

var
  Off, Cmd, CSz, N: Integer;
begin
  { emit a minimal signed executable and re-verify every CodeDirectory
    page hash independently — the structural self-check that runs on
    Linux CI in place of `codesign --verify` }
  W := TMachOExecWriter.Create();
  try
    W.SetText(Chr($C0) + Chr($03) + Chr($5F) + Chr($D6));   { ret }
    W.SetIdentifier('probe');
    W.SetEntryTextOffset(0);
    Img := W.Finish();
  finally
    W.Free();
  end;
  { find LC_CODE_SIGNATURE (cmd $1D) }
  SigOff := 0;
  Off := 32;
  for N := 0 to LeU32(16) - 1 do
  begin
    Cmd := LeU32(Off);
    CSz := LeU32(Off + 4);
    if Cmd = $1D then    { LC_CODE_SIGNATURE }
      SigOff := LeU32(Off + 8);
    Off := Off + CSz;
  end;
  AssertTrue('LC_CODE_SIGNATURE present', SigOff > 0);
  { SuperBlob: magic, length, count=1, type=0, cd offset }
  AssertEquals(Integer($FADE0CC0), BeU32(SigOff));
  CdOff := SigOff + BeU32(SigOff + 16);
  AssertEquals(Integer($FADE0C02), BeU32(CdOff));
  HashOff := CdOff + BeU32(CdOff + 16);
  NSlots := BeU32(CdOff + 28);
  CodeLimit := BeU32(CdOff + 32);
  AssertEquals('codeLimit is the signature start', SigOff, CodeLimit);
  for I := 0 to NSlots - 1 do
  begin
    PageLen := 4096;
    if I * 4096 + PageLen > CodeLimit then
      PageLen := CodeLimit - I * 4096;
    Page := Copy(Img, I * 4096, PageLen);
    Slot := Copy(Img, HashOff + I * 32, 32);
    AssertEquals('page ' + IntToStr(I) + ' hash matches',
      Sha256(Page), Slot);
  end;
end;

initialization
  RegisterTest(TSha256Tests);
  RegisterTest(TMachOWriterTests);
  RegisterTest(TMachOExecWriterTests);
  RegisterTest(TMachODylibTests);

end.
