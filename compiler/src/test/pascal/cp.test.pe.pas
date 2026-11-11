{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.pe;

{ Layer 0 structural tests for the PE32+ image writer and reader
  (windows-x86_64-backend-design.adoc, "PE32+ linker" and "Testing").

  Build an image with blaise.pewriter, parse it back with blaise.pereader,
  and assert the header fields, the section table and the import, base
  relocation and TLS tables the Windows loader reads.  No Windows host is
  needed. }

interface

uses
  SysUtils, Classes, Generics.Collections, blaise.testing, uStrCompat,
  blaise.pewriter, blaise.pereader;

type
  TPeWriterTests = class(TTestCase)
  private
    { .text (code), .rdata (one import table), .data with a .bss tail }
    function BuildProbe: TPeImage;
    function CodeBytes: string;
  published
    procedure TestDosHeader_MagicStubAndLfanew;
    procedure TestCoffHeader_MachineAndCharacteristics;
    procedure TestOptionalHeader_Pe32PlusFields;
    procedure TestOptionalHeader_DeterministicStampAndChecksum;
    procedure TestEntryPoint_InsideText;
    procedure TestSections_AlignedAndInOrder;
    procedure TestSections_Characteristics;
    procedure TestSections_BssTailIsZeroAndNotOnDisk;
    procedure TestSections_ContentsRoundTrip;
    procedure TestSizeOfImage_CoversLastSection;
    procedure TestSubsystem_Gui;
    procedure TestWriter_UnalignedSectionRaises;
    procedure TestWriter_OverlappingSectionsRaise;
    procedure TestWriter_LongSectionNameRaises;
  end;

  TPeTableTests = class(TTestCase)
  published
    procedure TestImports_DllsSortedSymbolsSorted;
    procedure TestImports_IatSlotsMatchBuilder;
    procedure TestImports_DirectoryAndIatRoundTrip;
    procedure TestImports_HintNameRvasBeforeBinding;
    procedure TestImports_DuplicateIgnored;
    procedure TestBaseRelocs_PageBlocksSortedDir64;
    procedure TestBaseRelocs_BlockPaddedToFourBytes;
    procedure TestBaseRelocs_Empty;
    procedure TestTls_DirectoryRoundTrip;
  end;

implementation

const
  TextRva = $1000;

{ ---- TPeWriterTests ---- }

function TPeWriterTests.CodeBytes: string;
begin
  { mov ecx, 42 ; ret }
  Result := Chr($B9) + #$2A#0#0#0 + Chr($C3);
end;

function TPeWriterTests.BuildProbe: TPeImage;
var
  W: TPeImageWriter;
  Imp: TPeImportTableBuilder;
  RData: string;
begin
  W := TPeImageWriter.Create();
  Imp := TPeImportTableBuilder.Create();
  try
    Imp.Add('kernel32.dll', 'ExitProcess');
    RData := Imp.Build($2000);
    W.EntryRva := TextRva + 0;
    W.AddSection('.text', TextRva, Length(CodeBytes()), CodeBytes(),
      PeScnCode or PeScnMemExecute or PeScnMemRead);
    W.AddSection('.rdata', $2000, Length(RData), RData,
      PeScnInitialisedData or PeScnMemRead);
    W.AddSection('.data', $3000, $2010, #1#2#3#4,
      PeScnInitialisedData or PeScnMemRead or PeScnMemWrite);
    W.SetDirectory(PeDirImport, Imp.DirectoryRva, Imp.DirectorySize);
    W.SetDirectory(PeDirIat, Imp.IatRva, Imp.IatSize);
    Result := ParsePeImage(W.Finish(), 'probe.exe');
  finally
    Imp.Free();
    W.Free();
  end;
end;

procedure TPeWriterTests.TestDosHeader_MagicStubAndLfanew;
var
  W: TPeImageWriter;
  B: string;
  Lfanew: Int;
begin
  W := TPeImageWriter.Create();
  try
    W.EntryRva := TextRva;
    W.AddSection('.text', TextRva, 6, CodeBytes(),
      PeScnCode or PeScnMemExecute or PeScnMemRead);
    B := W.Finish();
  finally
    W.Free();
  end;
  AssertEquals('MZ', Copy(B, 0, 2));
  Lfanew := StrAt(B, $3C) or (StrAt(B, $3D) shl 8);
  AssertEquals('PE header follows the DOS stub', $80, Lfanew);
  AssertEquals('PE'#0#0, Copy(B, Lfanew, 4));
  AssertTrue('conventional DOS stub message',
    Pos('This program cannot be run in DOS mode', B) >= 0);
end;

procedure TPeWriterTests.TestCoffHeader_MachineAndCharacteristics;
var
  Img: TPeImage;
begin
  Img := BuildProbe();
  try
    AssertEquals('x86-64', $8664, Img.Machine);
    AssertEquals('EXECUTABLE_IMAGE | LARGE_ADDRESS_AWARE', $22,
      Img.Characteristics);
    AssertEquals(3, Img.Sections.Count);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestOptionalHeader_Pe32PlusFields;
var
  Img: TPeImage;
begin
  Img := BuildProbe();
  try
    AssertEquals('PE32+ magic', $20B, Img.Magic);
    AssertTrue('image base', Img.ImageBase = $140000000);
    AssertEquals($1000, Img.SectionAlignment);
    AssertEquals($200, Img.FileAlignment);
    AssertEquals('OS version 6.0', 6, Img.MajorOsVersion);
    AssertEquals(0, Img.MinorOsVersion);
    AssertEquals('subsystem version 6.0', 6, Img.MajorSubsystemVersion);
    AssertEquals(0, Img.MinorSubsystemVersion);
    AssertEquals('console', PeSubsystemConsole, Img.Subsystem);
    AssertEquals('HIGH_ENTROPY_VA | DYNAMIC_BASE | NX_COMPAT | ' +
      'TERMINAL_SERVER_AWARE', $8160, Img.DllCharacteristics);
    AssertTrue('8 MiB stack reserve', Img.StackReserve = 8 * 1024 * 1024);
    AssertTrue('64 KiB stack commit', Img.StackCommit = 64 * 1024);
    AssertEquals('16 data directories', 16, Img.NumberOfRvaAndSizes);
    AssertEquals('headers are file-aligned', 0,
      Img.SizeOfHeaders mod Img.FileAlignment);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestOptionalHeader_DeterministicStampAndChecksum;
var
  Img: TPeImage;
begin
  Img := BuildProbe();
  try
    AssertEquals('TimeDateStamp', 0, Img.TimeDateStamp);
    AssertEquals('CheckSum', 0, Img.CheckSum);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestEntryPoint_InsideText;
var
  Img: TPeImage;
  S: TPeSection;
begin
  Img := BuildProbe();
  try
    AssertEquals(TextRva, Img.EntryRva);
    S := Img.SectionOfRva(Img.EntryRva);
    AssertNotNull('entry lies in a section', S);
    AssertEquals('.text', S.Name);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestSections_AlignedAndInOrder;
var
  Img: TPeImage;
  I: Int;
  S: TPeSection;
begin
  Img := BuildProbe();
  try
    AssertEquals('.text', Img.Sections[0].Name);
    AssertEquals('.rdata', Img.Sections[1].Name);
    AssertEquals('.data', Img.Sections[2].Name);
    for I := 0 to Img.Sections.Count - 1 do
    begin
      S := Img.Sections[I];
      AssertEquals(S.Name + ' VA section-aligned', 0,
        S.VirtualAddress mod Img.SectionAlignment);
      AssertEquals(S.Name + ' raw pointer file-aligned', 0,
        S.PointerToRawData mod Img.FileAlignment);
      AssertEquals(S.Name + ' raw size file-aligned', 0,
        S.SizeOfRawData mod Img.FileAlignment);
      if I > 0 then
        AssertTrue(S.Name + ' after its predecessor',
          S.VirtualAddress >= Img.Sections[I - 1].VirtualAddress +
            Img.Sections[I - 1].VirtualSize);
    end;
    AssertTrue('first section after the headers',
      Img.Sections[0].PointerToRawData >= Img.SizeOfHeaders);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestSections_Characteristics;
var
  Img: TPeImage;
begin
  Img := BuildProbe();
  try
    AssertEquals('.text: code, execute, read', $60000020,
      Img.Sections[0].Characteristics);
    AssertEquals('.rdata: initialised data, read', $40000040,
      Img.Sections[1].Characteristics);
    AssertTrue('.data: initialised data, read, write',
      Img.Sections[2].Characteristics = $C0000040);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestSections_BssTailIsZeroAndNotOnDisk;
var
  Img: TPeImage;
  D: TPeSection;
begin
  Img := BuildProbe();
  try
    D := Img.Sections[2];
    AssertEquals($2010, D.VirtualSize);
    AssertEquals('only the initialised bytes are on disk', $200,
      D.SizeOfRawData);
    AssertEquals(#1#2#3#4#0#0, Img.ReadRva($3000, 6));
    AssertEquals('the tail beyond the raw data reads as zero', #0#0#0#0,
      Img.ReadRva($3000 + $2000, 4));
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestSections_ContentsRoundTrip;
var
  Img: TPeImage;
begin
  Img := BuildProbe();
  try
    AssertEquals(CodeBytes(), Img.ReadRva(TextRva, 6));
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestSizeOfImage_CoversLastSection;
var
  Img: TPeImage;
begin
  Img := BuildProbe();
  try
    { .data at $3000 spans $2010 bytes, so it ends inside page $5000 }
    AssertEquals($6000, Img.SizeOfImage);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestSubsystem_Gui;
var
  W: TPeImageWriter;
  Img: TPeImage;
begin
  W := TPeImageWriter.Create();
  try
    W.EntryRva := TextRva;
    W.Subsystem := PeSubsystemGui;
    W.AddSection('.text', TextRva, 6, CodeBytes(),
      PeScnCode or PeScnMemExecute or PeScnMemRead);
    Img := ParsePeImage(W.Finish(), 'gui.exe');
  finally
    W.Free();
  end;
  try
    AssertEquals(PeSubsystemGui, Img.Subsystem);
  finally
    Img.Free();
  end;
end;

procedure TPeWriterTests.TestWriter_UnalignedSectionRaises;
var
  W: TPeImageWriter;
  Raised: Boolean;
begin
  W := TPeImageWriter.Create();
  Raised := False;
  try
    try
      W.AddSection('.text', TextRva + 8, 6, CodeBytes(),
        PeScnCode or PeScnMemExecute or PeScnMemRead);
      W.Finish();
    except
      on E: EPeWriter do
        Raised := True;
    end;
  finally
    W.Free();
  end;
  AssertTrue('a section RVA off the section alignment is rejected', Raised);
end;

procedure TPeWriterTests.TestWriter_OverlappingSectionsRaise;
var
  W: TPeImageWriter;
  Raised: Boolean;
begin
  W := TPeImageWriter.Create();
  Raised := False;
  try
    try
      W.AddSection('.text', TextRva, $1800, CodeBytes(),
        PeScnCode or PeScnMemExecute or PeScnMemRead);
      W.AddSection('.data', $2000 - $1000, 4, #1#2#3#4,
        PeScnInitialisedData or PeScnMemRead or PeScnMemWrite);
      W.Finish();
    except
      on E: EPeWriter do
        Raised := True;
    end;
  finally
    W.Free();
  end;
  AssertTrue('a section starting inside its predecessor is rejected',
    Raised);
end;

procedure TPeWriterTests.TestWriter_LongSectionNameRaises;
var
  W: TPeImageWriter;
  Raised: Boolean;
begin
  W := TPeImageWriter.Create();
  Raised := False;
  try
    try
      W.AddSection('.blaise_unwind', TextRva, 6, CodeBytes(),
        PeScnInitialisedData or PeScnMemRead);
    except
      on E: EPeWriter do
        Raised := True;
    end;
  finally
    W.Free();
  end;
  AssertTrue('an image section name is at most eight bytes', Raised);
end;

{ ---- TPeTableTests ---- }

{ Wrap an import table built at ARva into a one-section image and parse it. }
function ImageWithImports(AImp: TPeImportTableBuilder; ARva: Int): TPeImage;
var
  W: TPeImageWriter;
  RData: string;
begin
  RData := AImp.Build(ARva);
  W := TPeImageWriter.Create();
  try
    W.EntryRva := ARva;
    W.AddSection('.rdata', ARva, Length(RData), RData,
      PeScnInitialisedData or PeScnMemRead);
    W.SetDirectory(PeDirImport, AImp.DirectoryRva, AImp.DirectorySize);
    W.SetDirectory(PeDirIat, AImp.IatRva, AImp.IatSize);
    Result := ParsePeImage(W.Finish(), 'imports.exe');
  finally
    W.Free();
  end;
end;

procedure TPeTableTests.TestImports_DllsSortedSymbolsSorted;
var
  Imp: TPeImportTableBuilder;
  Img: TPeImage;
begin
  Imp := TPeImportTableBuilder.Create();
  try
    Imp.Add('user32.dll', 'MessageBoxW');
    Imp.Add('kernel32.dll', 'WriteFile');
    Imp.Add('kernel32.dll', 'ExitProcess');
    Img := ImageWithImports(Imp, $1000);
  finally
    Imp.Free();
  end;
  try
    AssertEquals(2, Img.Imports.Count);
    AssertEquals('kernel32.dll', Img.Imports[0].Dll);
    AssertEquals('user32.dll', Img.Imports[1].Dll);
    AssertEquals(2, Img.Imports[0].Symbols.Count);
    AssertEquals('ExitProcess', Img.Imports[0].Symbols[0]);
    AssertEquals('WriteFile', Img.Imports[0].Symbols[1]);
    AssertEquals('MessageBoxW', Img.Imports[1].Symbols[0]);
  finally
    Img.Free();
  end;
end;

procedure TPeTableTests.TestImports_IatSlotsMatchBuilder;
var
  Imp: TPeImportTableBuilder;
  Img: TPeImage;
  ExitSlot, WriteSlot, MsgSlot: Int;
begin
  Imp := TPeImportTableBuilder.Create();
  try
    Imp.Add('user32.dll', 'MessageBoxW');
    Imp.Add('kernel32.dll', 'WriteFile');
    Imp.Add('kernel32.dll', 'ExitProcess');
    Img := ImageWithImports(Imp, $1000);
    ExitSlot := Imp.IatSlotRva('kernel32.dll', 'ExitProcess');
    WriteSlot := Imp.IatSlotRva('kernel32.dll', 'WriteFile');
    MsgSlot := Imp.IatSlotRva('user32.dll', 'MessageBoxW');
  finally
    Imp.Free();
  end;
  try
    AssertEquals(ExitSlot, Img.Imports[0].IatSlotRvas[0]);
    AssertEquals(WriteSlot, Img.Imports[0].IatSlotRvas[1]);
    AssertEquals(MsgSlot, Img.Imports[1].IatSlotRvas[0]);
    AssertEquals('slots are eight bytes apart', 8, WriteSlot - ExitSlot);
  finally
    Img.Free();
  end;
end;

procedure TPeTableTests.TestImports_DirectoryAndIatRoundTrip;
var
  Imp: TPeImportTableBuilder;
  Img: TPeImage;
  IatRva, IatSize, DirRva, DirSize: Int;
begin
  Imp := TPeImportTableBuilder.Create();
  try
    Imp.Add('kernel32.dll', 'ExitProcess');
    Imp.Add('msvcrt.dll', 'puts');
    Img := ImageWithImports(Imp, $1000);
    IatRva := Imp.IatRva;
    IatSize := Imp.IatSize;
    DirRva := Imp.DirectoryRva;
    DirSize := Imp.DirectorySize;
  finally
    Imp.Free();
  end;
  try
    AssertEquals(DirRva, Img.DirectoryRva(PeDirImport));
    AssertEquals('two descriptors plus the null one', 3 * 20, DirSize);
    AssertEquals(DirSize, Img.DirectorySize(PeDirImport));
    AssertEquals(IatRva, Img.DirectoryRva(PeDirIat));
    AssertEquals('one slot and a terminator per DLL', 4 * 8, IatSize);
    AssertEquals(IatSize, Img.DirectorySize(PeDirIat));
    AssertEquals('IAT slots are eight-byte aligned', 0, IatRva mod 8);
  finally
    Img.Free();
  end;
end;

procedure TPeTableTests.TestImports_HintNameRvasBeforeBinding;
var
  Imp: TPeImportTableBuilder;
  Img: TPeImage;
  Slot: string;
  HintRva: Int;
begin
  Imp := TPeImportTableBuilder.Create();
  try
    Imp.Add('kernel32.dll', 'ExitProcess');
    Img := ImageWithImports(Imp, $1000);
  finally
    Imp.Free();
  end;
  try
    Slot := Img.ReadRva(Img.Imports[0].IatSlotRvas[0], 8);
    HintRva := StrAt(Slot, 0) or (StrAt(Slot, 1) shl 8) or (StrAt(Slot, 2) shl 16)
      or (StrAt(Slot, 3) shl 24);
    AssertEquals('an unbound IAT slot holds its hint/name RVA, by name',
      #0#0#0#0, Copy(Slot, 4, 4));
    AssertEquals('hint 0, then the name', #0#0'ExitProcess'#0,
      Img.ReadRva(HintRva, 14));
  finally
    Img.Free();
  end;
end;

procedure TPeTableTests.TestImports_DuplicateIgnored;
var
  Imp: TPeImportTableBuilder;
  Img: TPeImage;
begin
  Imp := TPeImportTableBuilder.Create();
  try
    Imp.Add('kernel32.dll', 'ExitProcess');
    Imp.Add('kernel32.dll', 'ExitProcess');
    Img := ImageWithImports(Imp, $1000);
  finally
    Imp.Free();
  end;
  try
    AssertEquals(1, Img.Imports.Count);
    AssertEquals(1, Img.Imports[0].Symbols.Count);
  finally
    Img.Free();
  end;
end;

procedure TPeTableTests.TestBaseRelocs_PageBlocksSortedDir64;
var
  Rvas: TList<Int>;
  Bytes: string;
  W: TPeImageWriter;
  Img: TPeImage;
begin
  Rvas := TList<Int>.Create();
  try
    Rvas.Add($2010);
    Rvas.Add($1008);
    Rvas.Add($1000);
    Bytes := BuildBaseRelocs(Rvas);
  finally
    Rvas.Free();
  end;
  AssertEquals('page $1000: 8-byte header + 2 entries', $1000,
    StrAt(Bytes, 0) or (StrAt(Bytes, 1) shl 8) or (StrAt(Bytes, 2) shl 16));
  W := TPeImageWriter.Create();
  try
    W.EntryRva := $1000;
    W.AddSection('.text', $1000, $1100, Chr($C3), PeScnCode or PeScnMemExecute
      or PeScnMemRead);
    W.AddSection('.reloc', $3000, Length(Bytes), Bytes,
      PeScnInitialisedData or PeScnMemRead or PeScnMemDiscardable);
    W.SetDirectory(PeDirBaseReloc, $3000, Length(Bytes));
    Img := ParsePeImage(W.Finish(), 'reloc.exe');
  finally
    W.Free();
  end;
  try
    AssertEquals(3, Img.BaseRelocs.Count);
    AssertEquals($1000, Img.BaseRelocs[0]);
    AssertEquals($1008, Img.BaseRelocs[1]);
    AssertEquals($2010, Img.BaseRelocs[2]);
  finally
    Img.Free();
  end;
end;

procedure TPeTableTests.TestBaseRelocs_BlockPaddedToFourBytes;
var
  Rvas: TList<Int>;
  Bytes: string;
begin
  Rvas := TList<Int>.Create();
  try
    Rvas.Add($1000);
    Bytes := BuildBaseRelocs(Rvas);
  finally
    Rvas.Free();
  end;
  { header 8 + one entry 2 + one ABSOLUTE padding entry 2 }
  AssertEquals(12, Length(Bytes));
  AssertEquals('block size field', 12, StrAt(Bytes, 4));
  AssertEquals('DIR64 entry, offset 0', $A0, StrAt(Bytes, 9));
  AssertEquals('padding entry is IMAGE_REL_BASED_ABSOLUTE', #0#0,
    Copy(Bytes, 10, 2));
end;

procedure TPeTableTests.TestBaseRelocs_Empty;
var
  Rvas: TList<Int>;
begin
  Rvas := TList<Int>.Create();
  try
    AssertEquals('', BuildBaseRelocs(Rvas));
  finally
    Rvas.Free();
  end;
end;

procedure TPeTableTests.TestTls_DirectoryRoundTrip;
var
  W: TPeImageWriter;
  Img: TPeImage;
  Dir: string;
begin
  Dir := BuildTlsDirectory($140004000, $140004010, $140003000, $140003008,
    $20);
  AssertEquals('PE32+ TLS directory size', 40, Length(Dir));
  W := TPeImageWriter.Create();
  try
    W.EntryRva := $1000;
    W.AddSection('.text', $1000, 1, Chr($C3), PeScnCode or PeScnMemExecute
      or PeScnMemRead);
    W.AddSection('.rdata', $2000, Length(Dir), Dir,
      PeScnInitialisedData or PeScnMemRead);
    W.SetDirectory(PeDirTls, $2000, Length(Dir));
    Img := ParsePeImage(W.Finish(), 'tls.exe');
  finally
    W.Free();
  end;
  try
    AssertTrue('TLS directory present', Img.HasTls);
    AssertTrue(Img.Tls.StartAddressOfRawData = $140004000);
    AssertTrue(Img.Tls.EndAddressOfRawData = $140004010);
    AssertTrue(Img.Tls.AddressOfIndex = $140003000);
    AssertTrue(Img.Tls.AddressOfCallBacks = $140003008);
    AssertEquals($20, Img.Tls.SizeOfZeroFill);
  finally
    Img.Free();
  end;
end;

initialization
  RegisterTest(TPeWriterTests);
  RegisterTest(TPeTableTests);
end.
