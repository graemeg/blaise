{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.pelinker;

{ Layer 0 structural tests for the PE32+ linker
  (windows-x86_64-backend-design.adoc, "PE32+ linker" and "Testing").

  Assemble small x86_64 programs with the internal assembler (ELF objects,
  design decision D2), link them with TPeLinker and read the image back with
  blaise.pereader.  TestLink_Exit42Fixture links the milestone M1 program
  under test and leaves the executable for scripts/windows-vm.sh. }

interface

uses
  SysUtils, Classes, blaise.testing, uStrCompat,
  blaise.pewriter, blaise.pereader, blaise.linker.pe, blaise.elfreader,
  blaise.assembler.x86_64;

type
  { The PE linker: ELF relocatable objects in, a PE32+ image out. }
  TPeLinkerTests = class(TTestCase)
  private
    { Link the objects assembled from AAsm (one string per object) with
      entry _start and parse the image. }
    function LinkAsm(AAsm: array of string): TPeImage;
    function LinkError(AAsm: array of string): string;
    function TextRvaOf(AImg: TPeImage): Int;
  published
    procedure TestLink_EntryIsStart;
    procedure TestLink_SectionsPresentOnlyWhenUsed;
    procedure TestLink_ImportFromMetadata;
    procedure TestLink_LibraryMappedToDll;
    procedure TestLink_CallGoesThroughThunkToIatSlot;
    procedure TestLink_UndefinedWithoutMetadataFails;
    procedure TestLink_MetadataForDefinedSymbolIgnored;
    procedure TestLink_CrossObjectCallResolved;
    procedure TestLink_WeakOverriddenByStrong;
    procedure TestLink_Abs64PointerRebasedWithBaseReloc;
    procedure TestLink_Abs32Rejected;
    procedure TestLink_BssIsDataTail;
    procedure TestLink_NoTlsWithoutThreadvars;
    procedure TestLink_TlsDirectoryForThreadvars;
    procedure TestLink_TpOffIsOffsetIntoTlsTemplate;
    procedure TestLink_UnwindBoundsDefined;
    procedure TestLink_Deterministic;
    procedure TestLink_MissingEntryFails;
    procedure TestLink_Exit42Fixture;
  end;

implementation

{ ---- TPeLinkerTests ---- }

const
  NL = #10;
  StartRet = '.text' + NL + '.globl _start' + NL + '_start:' + NL + 'ret' + NL;

function TPeLinkerTests.LinkAsm(AAsm: array of string): TPeImage;
var
  Lk: TPeLinker;
  I: Int;
begin
  Lk := TPeLinker.Create();
  try
    for I := 0 to High(AAsm) do
      Lk.AddObject(ParseElfObject(AssembleToBytes(AAsm[I]),
        'o' + IntToStr(I) + '.o'));
    Result := ParsePeImage(Lk.Link('_start'), 'out.exe');
  finally
    Lk.Free();
  end;
end;

function TPeLinkerTests.LinkError(AAsm: array of string): string;
var
  Img: TPeImage;
begin
  Result := '';
  try
    Img := LinkAsm(AAsm);
    Img.Free();
  except
    on E: EPeLinker do
      Result := E.Message;
  end;
end;

function TPeLinkerTests.TextRvaOf(AImg: TPeImage): Int;
begin
  Result := AImg.Sections[0].VirtualAddress;
end;

function Le32(const S: string; AOff: Int): Int64;
begin
  Result := StrAt(S, AOff) or (StrAt(S, AOff + 1) shl 8) or
    (StrAt(S, AOff + 2) shl 16) or (Int64(StrAt(S, AOff + 3)) shl 24);
end;

function Le64(const S: string; AOff: Int): Int64;
begin
  Result := Le32(S, AOff) or (Le32(S, AOff + 4) shl 32);
end;

{ A signed rel32 at AOff. }
function Rel32(const S: string; AOff: Int): Int64;
begin
  Result := Le32(S, AOff);
  if Result >= $80000000 then
    Result := Result - $100000000;
end;

function ImportsAsm(const ASym, ALib: string): string;
begin
  Result := '.section .blaise.imports,"",@progbits' + NL +
    '.ascii "' + ASym + '"' + NL + '.byte 0' + NL +
    '.ascii "' + ALib + '"' + NL + '.byte 0' + NL;
end;

procedure TPeLinkerTests.TestLink_EntryIsStart;
var
  Img: TPeImage;
begin
  Img := LinkAsm([StartRet]);
  try
    AssertEquals('.text', Img.Sections[0].Name);
    AssertEquals(TextRvaOf(Img), Img.EntryRva);
    AssertEquals(Chr($C3), Img.ReadRva(Img.EntryRva, 1));
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_SectionsPresentOnlyWhenUsed;
var
  Img: TPeImage;
  I: Int;
  Names: string;
begin
  Img := LinkAsm([StartRet]);
  try
    Names := '';
    for I := 0 to Img.Sections.Count - 1 do
      Names := Names + Img.Sections[I].Name + ' ';
    AssertEquals('a ret-only program has code and nothing else',
      '.text ', Names);
    AssertEquals(0, Img.DirectoryRva(PeDirImport));
    AssertEquals(0, Img.DirectoryRva(PeDirBaseReloc));
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_ImportFromMetadata;
var
  Img: TPeImage;
begin
  Img := LinkAsm([StartRet + 'call ExitProcess' + NL +
    ImportsAsm('ExitProcess', 'kernel32.dll')]);
  try
    AssertEquals(1, Img.Imports.Count);
    AssertEquals('kernel32.dll', Img.Imports[0].Dll);
    AssertEquals('ExitProcess', Img.Imports[0].Symbols[0]);
  finally
    Img.Free();
  end;
end;

{ A dll mapper standing in for the Windows toolkit. }
type
  TTestDllMap = class
  public
    function Map(const ALib: string): string;
  end;

function TTestDllMap.Map(const ALib: string): string;
begin
  Result := 'mapped_' + ALib + '.dll';
end;

procedure TPeLinkerTests.TestLink_LibraryMappedToDll;
var
  Lk: TPeLinker;
  M: TTestDllMap;
  Img: TPeImage;
begin
  M := TTestDllMap.Create();
  Lk := TPeLinker.Create();
  try
    Lk.DllNameOf := @M.Map;
    Lk.AddObject(ParseElfObject(AssembleToBytes(StartRet +
      'call ExitProcess' + NL + ImportsAsm('ExitProcess', 'kernel32')),
      'a.o'));
    Img := ParsePeImage(Lk.Link('_start'), 'out.exe');
  finally
    Lk.Free();
    M.Free();
  end;
  try
    AssertEquals('mapped_kernel32.dll', Img.Imports[0].Dll);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_CallGoesThroughThunkToIatSlot;
var
  Img: TPeImage;
  Text: string;
  CallAt, Thunk, Slot: Int64;
begin
  { _start: ret (1 byte), then call rel32 (5 bytes) }
  Img := LinkAsm([StartRet + 'call ExitProcess' + NL +
    ImportsAsm('ExitProcess', 'kernel32.dll')]);
  try
    Text := Img.ReadRva(TextRvaOf(Img), Img.Sections[0].VirtualSize);
    AssertEquals('call', $E8, StrAt(Text, 1));
    CallAt := TextRvaOf(Img) + 1;
    Thunk := CallAt + 5 + Rel32(Text, 2);
    AssertTrue('the call lands in .text',
      Img.SectionOfRva(Thunk) = Img.Sections[0]);
    AssertEquals('jmp *disp32(%rip)', Chr($FF) + Chr($25),
      Img.ReadRva(Thunk, 2));
    Slot := Thunk + 6 + Rel32(Img.ReadRva(Thunk + 2, 4), 0);
    AssertEquals('the thunk jumps through the IAT slot',
      Img.Imports[0].IatSlotRvas[0], Slot);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_UndefinedWithoutMetadataFails;
var
  Msg: string;
begin
  Msg := LinkError([StartRet + 'call Mystery' + NL]);
  AssertContains('Mystery', Msg);
  AssertContains('external', Msg);
end;

procedure TPeLinkerTests.TestLink_MetadataForDefinedSymbolIgnored;
var
  Img: TPeImage;
begin
  { runtime.thread binds external 'pthread'; on Windows the runtime defines
    those symbols itself, so the metadata entry must not import them }
  Img := LinkAsm([StartRet + 'call pthread_self' + NL +
    ImportsAsm('pthread_self', 'pthread'),
    '.text' + NL + '.globl pthread_self' + NL + 'pthread_self:' + NL +
    'ret' + NL]);
  try
    AssertEquals(0, Img.Imports.Count);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_CrossObjectCallResolved;
var
  Img: TPeImage;
  Text: string;
begin
  Img := LinkAsm([StartRet + 'call helper' + NL,
    '.text' + NL + '.globl helper' + NL + 'helper:' + NL + 'nop' + NL +
    'ret' + NL]);
  try
    Text := Img.ReadRva(TextRvaOf(Img), 6);
    { _start is ret + call rel32: the call ends 6 bytes in }
    AssertEquals('nop at the call target', $90,
      StrAt(Img.ReadRva(TextRvaOf(Img) + 6 + Rel32(Text, 2), 1), 0));
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_WeakOverriddenByStrong;
var
  Img: TPeImage;
  Text: string;
begin
  { the weak and the strong definition each in an object of their own, as
    the runtime's weak trampolines are; the weak one comes first }
  Img := LinkAsm([StartRet + 'call hook' + NL,
    '.text' + NL + '.weak hook' + NL + 'hook:' + NL + 'ret' + NL,
    '.text' + NL + '.globl hook' + NL + 'hook:' + NL + 'nop' + NL +
    'ret' + NL]);
  try
    Text := Img.ReadRva(TextRvaOf(Img), 6);
    AssertEquals('the strong definition wins', $90,
      StrAt(Img.ReadRva(TextRvaOf(Img) + 6 + Rel32(Text, 2), 1), 0));
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_Abs64PointerRebasedWithBaseReloc;
var
  Img: TPeImage;
  D: TPeSection;
  Ptr: Int64;
begin
  Img := LinkAsm([StartRet + '.data' + NL + '.globl table' + NL +
    'table:' + NL + '.quad _start' + NL]);
  try
    D := Img.SectionOfRva(Img.BaseRelocs[0]);
    AssertNotNull(D);
    AssertEquals('.data', D.Name);
    AssertEquals(1, Img.BaseRelocs.Count);
    Ptr := Img.ReadU64(D.VirtualAddress);
    AssertTrue('the pointer holds the preferred VA of _start',
      Ptr = Img.ImageBase + Img.EntryRva);
    AssertEquals(D.VirtualAddress, Img.BaseRelocs[0]);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_Abs32Rejected;
var
  Msg: string;
begin
  Msg := LinkError([StartRet + '.data' + NL + '.long _start' + NL]);
  AssertContains('R_X86_64_32', Msg);
end;

procedure TPeLinkerTests.TestLink_BssIsDataTail;
var
  Img: TPeImage;
  D: TPeSection;
begin
  Img := LinkAsm([StartRet + '.data' + NL + '.quad 7' + NL +
    '.section .bss,"aw",@nobits' + NL + '.skip 8192' + NL]);
  try
    D := Img.Sections[1];
    AssertEquals('.data', D.Name);
    AssertTrue('the .bss tail is in the virtual size',
      D.VirtualSize >= 8 + 8192);
    AssertEquals('only the initialised data is on disk', $200,
      D.SizeOfRawData);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_NoTlsWithoutThreadvars;
var
  Img: TPeImage;
begin
  Img := LinkAsm([StartRet]);
  try
    AssertFalse(Img.HasTls);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_TlsDirectoryForThreadvars;
var
  Img: TPeImage;
  Tls: TPeSection;
  I: Int;
  Found: Int;
begin
  Img := LinkAsm([StartRet + '.section .tdata,"awT",@progbits' + NL +
    'tv_a:' + NL + '.quad 5' + NL +
    '.section .tbss,"awT",@nobits' + NL + 'tv_b:' + NL + '.skip 16' + NL]);
  try
    AssertTrue('TLS directory present', Img.HasTls);
    Tls := nil;
    for I := 0 to Img.Sections.Count - 1 do
      if Img.Sections[I].Name = '.tls' then
        Tls := Img.Sections[I];
    AssertNotNull('.tls section', Tls);
    AssertTrue('raw data starts at .tls',
      Img.Tls.StartAddressOfRawData = Img.ImageBase + Tls.VirtualAddress);
    AssertTrue('raw data is the .tdata bytes',
      Img.Tls.EndAddressOfRawData = Img.Tls.StartAddressOfRawData + 8);
    AssertEquals('the .tbss bytes are zero fill', 16, Img.Tls.SizeOfZeroFill);
    AssertTrue('the index slot is writable',
      (Img.SectionOfRva(Img.Tls.AddressOfIndex - Img.ImageBase)
        .Characteristics and PeScnMemWrite) <> 0);
    AssertTrue('an empty callback list',
      Img.ReadU64(Img.Tls.AddressOfCallBacks - Img.ImageBase) = 0);
    { the directory's four pointers are rebased }
    Found := 0;
    for I := 0 to Img.BaseRelocs.Count - 1 do
      if (Img.BaseRelocs[I] >= Img.DirectoryRva(PeDirTls)) and
         (Img.BaseRelocs[I] < Img.DirectoryRva(PeDirTls) + 32) then
        Inc(Found);
    AssertEquals(4, Found);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_TpOffIsOffsetIntoTlsTemplate;
var
  Img: TPeImage;
  Text: string;
begin
  { movl %fs:tv_b@tpoff, %eax: 64 8B 04 25 disp32, after the 1-byte ret }
  Img := LinkAsm([StartRet + 'movl %fs:tv_b@tpoff, %eax' + NL +
    '.section .tdata,"awT",@progbits' + NL + 'tv_a:' + NL + '.quad 5' + NL +
    '.section .tbss,"awT",@nobits' + NL + 'tv_b:' + NL + '.skip 16' + NL]);
  try
    Text := Img.ReadRva(TextRvaOf(Img), 9);
    AssertEquals('fs-prefixed mov', $64, StrAt(Text, 1));
    AssertEquals('tv_b sits after the 8 bytes of .tdata', 8,
      Rel32(Text, 5));
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_UnwindBoundsDefined;
var
  Img: TPeImage;
  U: TPeSection;
  StartPtr, StopPtr: Int64;
begin
  Img := LinkAsm([StartRet + '.data' + NL + '.quad __start_blaise_unwind' +
    NL + '.quad __stop_blaise_unwind' + NL +
    '.section blaise_unwind,"aw",@progbits' + NL + '.quad 1' + NL +
    '.quad 2' + NL]);
  try
    U := Img.Sections[2];
    AssertEquals('.blunw', U.Name);
    StartPtr := Img.ReadU64(Img.Sections[1].VirtualAddress);
    StopPtr := Img.ReadU64(Img.Sections[1].VirtualAddress + 8);
    AssertTrue(StartPtr = Img.ImageBase + U.VirtualAddress);
    AssertTrue(StopPtr = StartPtr + 16);
  finally
    Img.Free();
  end;
end;

procedure TPeLinkerTests.TestLink_Deterministic;
var
  Lk: TPeLinker;
  A, B: string;
  Pass: Int;
begin
  A := '';
  B := '';
  for Pass := 0 to 1 do
  begin
    Lk := TPeLinker.Create();
    try
      Lk.AddObject(ParseElfObject(AssembleToBytes(StartRet +
        'call WriteFile' + NL + 'call ExitProcess' + NL +
        ImportsAsm('WriteFile', 'kernel32.dll') +
        ImportsAsm('ExitProcess', 'kernel32.dll') + '.data' + NL +
        '.quad _start' + NL), 'a.o'));
      if Pass = 0 then
        A := Lk.Link('_start')
      else
        B := Lk.Link('_start');
    finally
      Lk.Free();
    end;
  end;
  AssertTrue('two links of the same input are byte-identical', A = B);
end;

procedure TPeLinkerTests.TestLink_MissingEntryFails;
var
  Msg: string;
begin
  Msg := LinkError(['.text' + NL + 'ret' + NL]);
  AssertContains('_start', Msg);
end;

{ compiler/src/it/windows/exit42.s, the M1 program under test: linked here
  and left at compiler/target/it/windows/exit42.exe for windows-vm.sh. }
procedure TPeLinkerTests.TestLink_Exit42Fixture;
var
  Root, Src, OutDir: string;
  L: TStringList;
  Lk: TPeLinker;
  Img: TPeImage;
begin
  Root := GetCurrentDir();
  while (Root <> '') and
        not FileExists(Root + '/compiler/src/it/windows/exit42.s') do
    Root := ExtractFileDir(Root);
  AssertTrue('fixture found', Root <> '');
  L := TStringList.Create();
  try
    L.LoadFromFile(Root + '/compiler/src/it/windows/exit42.s');
    Src := L.Text;
  finally
    L.Free();
  end;
  OutDir := Root + '/compiler/target/it/windows';
  ForceDirectories(OutDir);
  Lk := TPeLinker.Create();
  try
    Lk.AddObject(ParseElfObject(AssembleToBytes(Src), 'exit42.o'));
    Lk.LinkToFile('_start', OutDir + '/exit42.exe');
  finally
    Lk.Free();
  end;
  Img := ReadPeImageFile(OutDir + '/exit42.exe');
  try
    AssertEquals($8664, Img.Machine);
    AssertEquals(PeSubsystemConsole, Img.Subsystem);
    AssertEquals(1, Img.Imports.Count);
    AssertEquals('kernel32.dll', Img.Imports[0].Dll);
    AssertEquals('ExitProcess', Img.Imports[0].Symbols[0]);
    AssertTrue('entry in .text',
      Img.SectionOfRva(Img.EntryRva) = Img.Sections[0]);
  finally
    Img.Free();
  end;
end;

initialization
  RegisterTest(TPeLinkerTests);
end.
