{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.targettoolkit;

{ Tests for the multi-target toolkit + registry (docs/native-target-
  architecture.adoc).  A TTargetToolkit is the Abstract Factory that produces
  the consistent family of per-target objects (backend, link target); the
  registry resolves a toolkit by target.

  These tests pin the behaviour-preserving Step 0a refactor: the existing
  Linux x86_64 target must resolve through the registry, and the FreeBSD
  x86_64 target must be registered (its codegen lands in later steps, so we
  only assert it is known to the registry here, not that it emits code). }

interface

uses
  SysUtils, Classes, blaise.testing,
  blaise.codegen.target, blaise.codegen.toolkit,
  blaise.codegen.native.backend, blaise.linker.elf,
  blaise.codegen.native.x86_64, blaise.codegen.native.x86_64.abi;

type
  TTargetToolkitTests = class(TTestCase)
  private
    function LinuxTarget: TTargetDesc;
    function FreeBSDTarget: TTargetDesc;
  published
    { Linux x86_64 resolves to a toolkit, and that toolkit reports its name. }
    procedure TestResolve_LinuxX86_64_ReturnsToolkit;
    procedure TestResolve_LinuxX86_64_ToolkitName;
    { The Linux toolkit makes a real backend (the existing TX86_64Backend). }
    procedure TestLinuxToolkit_MakeBackend_NotNil;
    { The Linux toolkit makes a SysV/Linux link target (OSABI 0). }
    procedure TestLinuxToolkit_MakeLinkTarget_IsLinuxOSABI;
    { RegisteredHasNativeBackend mirrors the old TargetHasNativeBackend for
      Linux x86_64. }
    procedure TestRegistered_LinuxX86_64_HasBackend;
    { FreeBSD x86_64 is registered (resolves to a toolkit). }
    procedure TestResolve_FreeBSDX86_64_ReturnsToolkit;
    { FreeBSD toolkit produces a FreeBSD-OSABI link target (OSABI 9). }
    procedure TestFreeBSDToolkit_MakeLinkTarget_IsFreeBSDOSABI;
    procedure TestResolve_MacOSArm64_ReturnsToolkit;
    procedure TestMacOSToolkit_MakeBackend_NotNil;
    procedure TestMacOSToolkit_MakeLinkTarget_NilUntilMachOLinker;
    { Object format and image format are separate questions (Windows design
      D2: ELF relocatable objects, PE image). }
    procedure TestObjectIsElf_PerTarget;
    procedure TestImageIsElf_PerTarget;
    { The x86-64 toolkits supply the backend's strategy objects: System V at
      the foreign boundary, ELF local-exec for threadvars. }
    procedure TestLinuxToolkit_Backend_HasSysVAndElfTls;
    procedure TestFreeBSDToolkit_Backend_HasSysVAndElfTls;
    procedure TestSysVBoundaryAbi_NoProbeNoTranslation;
    procedure TestElfLocalExecTls_OperandAndAddress;
    { The toolkit names the image container the driver dispatches on. }
    procedure TestImageFormat_PerToolkit;
    { Default library search directories, in search order, per toolkit. }
    procedure TestLinuxToolkit_SystemLibDirs_MultiarchFirst;
    procedure TestFreeBSDToolkit_SystemLibDirs_NoMultiarch;
    procedure TestSystemLibDirs_SkipsDirsAlreadyListed;
    { A Mach-O toolkit does not map ELF link libraries. }
    procedure TestMacOSToolkit_LibraryImageName_Raises;
    { windows-x86_64: PE image over ELF objects (Windows M1) }
    procedure TestWindowsToolkit_NameAndPeImage;
    procedure TestWindowsToolkit_NoElfLinkTarget;
    procedure TestWindowsToolkit_DllNames;
    procedure TestWindowsToolkit_NoSystemLibDirsOnCrossHost;
    { Registered since M2: System V inside, Win64 at the foreign boundary,
      PE TLS for threadvars (M3). }
    procedure TestWindowsToolkit_Registered;
    procedure TestWindowsToolkit_Backend_HasWin64AbiAndPeTls;
    procedure TestWin64BoundaryAbi_ProbesAndTranslates;
    procedure TestWin64BoundaryAbi_ArgLocations;
    procedure TestPeTlsModel_OperandAndAddress;
    procedure TestPeTlsModel_LineUsingR11_IsAnError;
    { The OS suffix of the RTL's per-OS units, and the layout initialiser
      every program's main calls. }
    procedure TestRTLOSSuffix_PerOS;
    procedure TestPlatformLayoutInitSym_Windows;
  end;

implementation

const
  ELFOSABI_SYSV    = 0;
  ELFOSABI_FREEBSD = 9;

function TTargetToolkitTests.LinuxTarget: TTargetDesc;
begin
  MakeTarget(osLinux, cpuX86_64, Result);
end;

function TTargetToolkitTests.FreeBSDTarget: TTargetDesc;
begin
  MakeTarget(osFreeBSD, cpuX86_64, Result);
end;

procedure TTargetToolkitTests.TestResolve_LinuxX86_64_ReturnsToolkit;
var
  Tk: TTargetToolkit;
begin
  Tk := ResolveToolkit(Self.LinuxTarget());
  AssertTrue('linux-x86_64 must resolve to a toolkit', Tk <> nil);
end;

procedure TTargetToolkitTests.TestResolve_LinuxX86_64_ToolkitName;
var
  Tk: TTargetToolkit;
begin
  Tk := ResolveToolkit(Self.LinuxTarget());
  AssertEquals('linux-x86_64', Tk.Name());
end;

procedure TTargetToolkitTests.TestLinuxToolkit_MakeBackend_NotNil;
var
  Tk: TTargetToolkit;
  B:  TNativeBackend;
begin
  Tk := ResolveToolkit(Self.LinuxTarget());
  B  := Tk.MakeBackend();
  try
    AssertTrue('Linux toolkit must produce a backend', B <> nil);
  finally
    B.Free();
  end;
end;

procedure TTargetToolkitTests.TestLinuxToolkit_MakeLinkTarget_IsLinuxOSABI;
var
  Tk: TTargetToolkit;
  Lt: TLinkTarget;
begin
  Tk := ResolveToolkit(Self.LinuxTarget());
  Lt := Tk.MakeLinkTarget();
  try
    AssertEquals(ELFOSABI_SYSV, Lt.OSABI);
  finally
    Lt.Free();
  end;
end;

procedure TTargetToolkitTests.TestRegistered_LinuxX86_64_HasBackend;
begin
  AssertTrue('linux-x86_64 must have a native backend',
    RegisteredHasNativeBackend(Self.LinuxTarget()));
end;

procedure TTargetToolkitTests.TestResolve_FreeBSDX86_64_ReturnsToolkit;
var
  Tk: TTargetToolkit;
begin
  Tk := ResolveToolkit(Self.FreeBSDTarget());
  AssertTrue('freebsd-x86_64 must resolve to a toolkit', Tk <> nil);
end;

procedure TTargetToolkitTests.TestFreeBSDToolkit_MakeLinkTarget_IsFreeBSDOSABI;
var
  Tk: TTargetToolkit;
  Lt: TLinkTarget;
begin
  Tk := ResolveToolkit(Self.FreeBSDTarget());
  Lt := Tk.MakeLinkTarget();
  try
    AssertEquals(ELFOSABI_FREEBSD, Lt.OSABI);
  finally
    Lt.Free();
  end;
end;

procedure TTargetToolkitTests.TestResolve_MacOSArm64_ReturnsToolkit;
var
  T:  TTargetDesc;
  Tk: TTargetToolkit;
begin
  MakeTarget(osMacOS, cpuArm64, T);
  Tk := ResolveToolkit(T);
  AssertTrue('macos-arm64 must resolve to a toolkit', Tk <> nil);
  AssertEquals('macos-arm64', Tk.Name());
end;

procedure TTargetToolkitTests.TestMacOSToolkit_MakeBackend_NotNil;
var
  T:  TTargetDesc;
  Tk: TTargetToolkit;
  B:  TNativeBackend;
begin
  MakeTarget(osMacOS, cpuArm64, T);
  Tk := ResolveToolkit(T);
  B  := Tk.MakeBackend();
  try
    AssertTrue('macOS toolkit must produce a backend', B <> nil);
  finally
    B.Free();
  end;
end;

procedure TTargetToolkitTests.TestMacOSToolkit_MakeLinkTarget_NilUntilMachOLinker;
var
  T:  TTargetDesc;
  Tk: TTargetToolkit;
begin
  { the ELF internal linker cannot drive a Mach-O target; the nil link
    target is the driver's honest gate until the Mach-O linker lands }
  MakeTarget(osMacOS, cpuArm64, T);
  Tk := ResolveToolkit(T);
  AssertTrue('no ELF link facts for macos-arm64',
    Tk.MakeLinkTarget() = nil);
end;

procedure TTargetToolkitTests.TestObjectIsElf_PerTarget;
var
  T: TTargetDesc;
begin
  MakeTarget(osLinux, cpuX86_64, T);
  AssertTrue('linux objects are ELF', TargetObjectIsElf(T));
  MakeTarget(osFreeBSD, cpuX86_64, T);
  AssertTrue('freebsd objects are ELF', TargetObjectIsElf(T));
  MakeTarget(osWindows, cpuX86_64, T);
  AssertTrue('windows objects are ELF (D2)', TargetObjectIsElf(T));
  MakeTarget(osMacOS, cpuArm64, T);
  AssertFalse('macos objects are Mach-O', TargetObjectIsElf(T));
end;

procedure TTargetToolkitTests.TestImageIsElf_PerTarget;
var
  T: TTargetDesc;
begin
  MakeTarget(osLinux, cpuX86_64, T);
  AssertTrue('linux image is ELF', TargetImageIsElf(T));
  MakeTarget(osFreeBSD, cpuX86_64, T);
  AssertTrue('freebsd image is ELF', TargetImageIsElf(T));
  MakeTarget(osWindows, cpuX86_64, T);
  AssertFalse('windows image is PE', TargetImageIsElf(T));
  MakeTarget(osMacOS, cpuArm64, T);
  AssertFalse('macos image is Mach-O', TargetImageIsElf(T));
end;

procedure CheckSysVElfBackend(ATest: TTargetToolkitTests;
  const ATarget: TTargetDesc);
var
  B: TNativeBackend;
begin
  B := ResolveToolkit(ATarget).MakeBackend();
  try
    ATest.AssertTrue('an x86-64 backend', B is TX86_64Backend);
    ATest.AssertTrue('System V boundary ABI',
      TX86_64Backend(B).BoundaryAbi is TSysVBoundaryAbi);
    ATest.AssertTrue('ELF local-exec TLS model',
      TX86_64Backend(B).TlsModel is TElfLocalExecTls);
  finally
    B.Free();
  end;
end;

procedure TTargetToolkitTests.TestLinuxToolkit_Backend_HasSysVAndElfTls;
begin
  CheckSysVElfBackend(Self, Self.LinuxTarget());
end;

procedure TTargetToolkitTests.TestFreeBSDToolkit_Backend_HasSysVAndElfTls;
begin
  CheckSysVElfBackend(Self, Self.FreeBSDTarget());
end;

procedure TTargetToolkitTests.TestSysVBoundaryAbi_NoProbeNoTranslation;
var
  A: TX86BoundaryAbi;
begin
  A := TSysVBoundaryAbi.Create();
  try
    AssertFalse('no stack probe', A.NeedsStackProbe());
    AssertFalse('C convention = internal', A.ForeignDiffers());
  finally
    A.Free();
  end;
end;

type
  { Collects emitted lines for the TLS-model test. }
  TLineSink = class
  public
    Lines: string;
    procedure Add(const ALine: string);
  end;

procedure TLineSink.Add(const ALine: string);
begin
  Lines := Lines + ALine + '|';
end;

procedure TTargetToolkitTests.TestElfLocalExecTls_OperandAndAddress;
var
  M: TX86TlsModel;
  Sink: TLineSink;
begin
  M := TElfLocalExecTls.Create();
  Sink := TLineSink.Create();
  try
    AssertEquals('%fs:U_X@tpoff', M.DirectOperand('U_X'));
    M.EmitAddress('U_X', '%rax', @Sink.Add);
    AssertEquals(#9'movq %fs:0, %rax|'#9'leaq U_X@tpoff(%rax), %rax|',
      Sink.Lines);
    Sink.Lines := '';
    AssertTrue('leaq of the operand is rewritten',
      M.RewriteLine(#9'leaq %fs:U_X@tpoff, %rcx', @Sink.Add));
    AssertEquals(#9'movq %fs:0, %rcx|'#9'leaq U_X@tpoff(%rcx), %rcx|',
      Sink.Lines);
    AssertFalse('other lines pass through',
      M.RewriteLine(#9'leaq U_X(%rip), %rcx', @Sink.Add));
  finally
    Sink.Free();
    M.Free();
  end;
end;

procedure TTargetToolkitTests.TestImageFormat_PerToolkit;
var
  T: TTargetDesc;
begin
  AssertTrue('linux image is ELF',
    ResolveToolkit(Self.LinuxTarget()).ImageFormat() = ifElf);
  AssertTrue('freebsd image is ELF',
    ResolveToolkit(Self.FreeBSDTarget()).ImageFormat() = ifElf);
  MakeTarget(osMacOS, cpuArm64, T);
  AssertTrue('macos image is Mach-O',
    ResolveToolkit(T).ImageFormat() = ifMachO);
end;

function SystemDirs(const ATarget: TTargetDesc; const APreset: string): string;
var
  L: TStringList;
begin
  L := TStringList.Create();
  try
    if APreset <> '' then
      L.Add(APreset);
    ResolveToolkit(ATarget).AddSystemLibDirs(L);
    Result := L.CommaText;
  finally
    L.Free();
  end;
end;

procedure TTargetToolkitTests.TestLinuxToolkit_SystemLibDirs_MultiarchFirst;
begin
  AssertEquals('/lib/x86_64-linux-gnu,/usr/lib/x86_64-linux-gnu,' +
    '/usr/local/lib,/lib,/usr/lib', SystemDirs(Self.LinuxTarget(), ''));
end;

procedure TTargetToolkitTests.TestFreeBSDToolkit_SystemLibDirs_NoMultiarch;
begin
  AssertEquals('/usr/local/lib,/lib,/usr/lib',
    SystemDirs(Self.FreeBSDTarget(), ''));
end;

procedure TTargetToolkitTests.TestSystemLibDirs_SkipsDirsAlreadyListed;
begin
  { a --lib-path or LD_LIBRARY_PATH entry keeps its earlier position }
  AssertEquals('/lib,/usr/local/lib,/usr/lib',
    SystemDirs(Self.FreeBSDTarget(), '/lib'));
end;

procedure TTargetToolkitTests.TestMacOSToolkit_LibraryImageName_Raises;
var
  T: TTargetDesc;
  Raised: Boolean;
begin
  MakeTarget(osMacOS, cpuArm64, T);
  Raised := False;
  try
    ResolveToolkit(T).LibraryImageName('c');
  except
    on E: Exception do
      Raised := True;
  end;
  AssertTrue('Mach-O dylibs are resolved by the Mach-O linker', Raised);
end;

procedure TTargetToolkitTests.TestWindowsToolkit_NameAndPeImage;
var
  Tk: TWindowsX86_64Toolkit;
begin
  Tk := TWindowsX86_64Toolkit.Create();
  try
    AssertEquals('windows-x86_64', Tk.Name());
    AssertTrue('windows image is PE', Tk.ImageFormat() = ifPe);
  finally
    Tk.Free();
  end;
end;

procedure TTargetToolkitTests.TestWindowsToolkit_NoElfLinkTarget;
var
  Tk: TWindowsX86_64Toolkit;
  LT: TLinkTarget;
begin
  Tk := TWindowsX86_64Toolkit.Create();
  try
    LT := Tk.MakeLinkTarget();
    AssertTrue('no ELF link facts for a PE image', LT = nil);
  finally
    Tk.Free();
  end;
end;

procedure TTargetToolkitTests.TestWindowsToolkit_DllNames;
var
  Tk: TWindowsX86_64Toolkit;
begin
  Tk := TWindowsX86_64Toolkit.Create();
  try
    AssertEquals('the C runtime', 'msvcrt.dll', Tk.LibraryImageName('c'));
    AssertEquals('libm lives in the C runtime', 'msvcrt.dll',
      Tk.LibraryImageName('m'));
    AssertEquals('kernel32.dll', Tk.LibraryImageName('kernel32'));
    AssertEquals('ws2_32.dll', Tk.LibraryImageName('ws2_32'));
    AssertEquals('a DLL name is used verbatim', 'user32.dll',
      Tk.LibraryImageName('user32.dll'));
    AssertEquals('whatever its case', 'GDI32.DLL',
      Tk.LibraryImageName('GDI32.DLL'));
  finally
    Tk.Free();
  end;
end;

procedure TTargetToolkitTests.TestWindowsToolkit_NoSystemLibDirsOnCrossHost;
var
  Tk: TWindowsX86_64Toolkit;
  L: TStringList;
begin
  Tk := TWindowsX86_64Toolkit.Create();
  L := TStringList.Create();
  try
    Tk.AddSystemLibDirs(L);
    AssertEquals('a cross link reads no DLLs', 0, L.Count);
  finally
    L.Free();
    Tk.Free();
  end;
end;

procedure TTargetToolkitTests.TestWindowsToolkit_Registered;
var
  T: TTargetDesc;
begin
  MakeTarget(osWindows, cpuX86_64, T);
  AssertTrue('windows-x86_64 resolves to a toolkit', ResolveToolkit(T) <> nil);
  AssertEquals('windows-x86_64', ResolveToolkit(T).Name());
end;

procedure TTargetToolkitTests.TestWindowsToolkit_Backend_HasWin64AbiAndPeTls;
var
  T: TTargetDesc;
  B: TNativeBackend;
begin
  MakeTarget(osWindows, cpuX86_64, T);
  B := ResolveToolkit(T).MakeBackend();
  try
    AssertTrue('an x86-64 backend', B is TX86_64Backend);
    AssertTrue('Win64 boundary ABI',
      TX86_64Backend(B).BoundaryAbi is TWin64BoundaryAbi);
    AssertTrue('PE TLS model',
      TX86_64Backend(B).TlsModel is TPeTlsModel);
  finally
    B.Free();
  end;
end;

procedure TTargetToolkitTests.TestWin64BoundaryAbi_ProbesAndTranslates;
var
  A: TX86BoundaryAbi;
begin
  A := TWin64BoundaryAbi.Create();
  try
    AssertTrue('stack probe', A.NeedsStackProbe());
    AssertTrue('C convention differs', A.ForeignDiffers());
    AssertEquals('home space only', 32, A.ForeignOutgoingBytes(0));
    AssertEquals('home space for four', 32, A.ForeignOutgoingBytes(4));
    AssertEquals('plus two stack slots', 48, A.ForeignOutgoingBytes(6));
  finally
    A.Free();
  end;
end;

procedure TTargetToolkitTests.TestWin64BoundaryAbi_ArgLocations;
var
  A: TX86BoundaryAbi;
  L: TX86ForeignArgLoc;
begin
  A := TWin64BoundaryAbi.Create();
  try
    AssertEquals('%rcx', A.ForeignArgLoc(0, fakInt, 0, False).Reg);
    { positional: an integer second argument uses RDX after a float }
    AssertEquals('%xmm0', A.ForeignArgLoc(0, fakDouble, 0, False).Reg);
    AssertEquals('%rdx', A.ForeignArgLoc(1, fakInt, 0, False).Reg);
    AssertEquals('%xmm2', A.ForeignArgLoc(2, fakSingle, 0, False).Reg);
    AssertEquals('%r9', A.ForeignArgLoc(3, fakInt, 0, False).Reg);
    L := A.ForeignArgLoc(4, fakInt, 0, False);
    AssertEquals('fifth on the stack', '', L.Reg);
    AssertEquals('above the home space', 32, L.StackOff);
    AssertEquals('sixth', 40, A.ForeignArgLoc(5, fakDouble, 0, False).StackOff);
    { a variadic float is mirrored into the integer register }
    L := A.ForeignArgLoc(1, fakDouble, 0, True);
    AssertEquals('%xmm1', L.Reg);
    AssertEquals('%rdx', L.MirrorReg);
    AssertEquals('no mirror when fixed', '',
      A.ForeignArgLoc(1, fakDouble, 0, False).MirrorReg);
    { records: 1, 2, 4 and 8 bytes by value, anything else by reference }
    AssertFalse('8-byte record by value', A.ForeignArgLoc(0, fakRecord, 8, False).ByRef);
    AssertFalse('2-byte record by value', A.ForeignArgLoc(0, fakRecord, 2, False).ByRef);
    AssertTrue('3-byte record by reference', A.ForeignArgLoc(0, fakRecord, 3, False).ByRef);
    AssertTrue('16-byte record by reference', A.ForeignArgLoc(0, fakRecord, 16, False).ByRef);
    AssertEquals('a record travels in an integer register', '%rcx',
      A.ForeignArgLoc(0, fakRecord, 16, False).Reg);
  finally
    A.Free();
  end;
end;

procedure TTargetToolkitTests.TestPeTlsModel_OperandAndAddress;
var
  M: TX86TlsModel;
  Sink: TLineSink;
  Op: string;
begin
  M := TPeTlsModel.Create();
  Sink := TLineSink.Create();
  try
    { the address form: the TLS block of this thread, then the offset }
    M.EmitAddress('U_X', '%rax', @Sink.Add);
    AssertEquals(#9'movq %gs:88, %rax|'#9'movq (%rax), %rax|' +
      #9'leaq U_X@tpoff(%rax), %rax|', Sink.Lines);
    { the operand form is expanded at each line that uses it, so an operand
      reused after a call is still right }
    Op := M.DirectOperand('U_X');
    Sink.Lines := '';
    AssertTrue('a line using the operand is rewritten',
      M.RewriteLine(#9'movq ' + Op + ', %rdi', @Sink.Add));
    AssertEquals(#9'movq %gs:88, %r11|'#9'movq (%r11), %r11|' +
      #9'movq U_X@tpoff(%r11), %rdi|', Sink.Lines);
    Sink.Lines := '';
    AssertTrue('its address too',
      M.RewriteLine(#9'leaq ' + Op + ', %rcx', @Sink.Add));
    AssertEquals(#9'movq %gs:88, %r11|'#9'movq (%r11), %r11|' +
      #9'leaq U_X@tpoff(%r11), %rcx|', Sink.Lines);
    AssertFalse('other lines pass through',
      M.RewriteLine(#9'leaq U_X(%rip), %rcx', @Sink.Add));
  finally
    Sink.Free();
    M.Free();
  end;
end;

procedure TTargetToolkitTests.TestPeTlsModel_LineUsingR11_IsAnError;
var
  M: TX86TlsModel;
  Sink: TLineSink;
  Msg: string;
begin
  M := TPeTlsModel.Create();
  Sink := TLineSink.Create();
  try
    Msg := '';
    try
      M.RewriteLine(#9'movq %r11, ' + M.DirectOperand('U_X'), @Sink.Add);
    except
      on E: Exception do
        Msg := E.Message;
    end;
    AssertTrue('the TLS base register clash is reported: ' + Msg,
      Pos('%r11', Msg) >= 0);
  finally
    Sink.Free();
    M.Free();
  end;
end;

procedure TTargetToolkitTests.TestRTLOSSuffix_PerOS;
begin
  AssertEquals('linux', RTLOSSuffix(osLinux));
  AssertEquals('freebsd', RTLOSSuffix(osFreeBSD));
  AssertEquals('darwin', RTLOSSuffix(osMacOS));
  AssertEquals('windows', RTLOSSuffix(osWindows));
end;

procedure TTargetToolkitTests.TestPlatformLayoutInitSym_Windows;
var
  T: TTargetDesc;
begin
  MakeTarget(osWindows, cpuX86_64, T);
  AssertEquals('rtl.platform.layout.windows_init', PlatformLayoutInitSym(T));
end;

initialization
  RegisterTest(TTargetToolkitTests);

end.
