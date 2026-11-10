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
      M.RewriteAddressOf(#9'leaq %fs:U_X@tpoff, %rcx', @Sink.Add));
    AssertEquals(#9'movq %fs:0, %rcx|'#9'leaq U_X@tpoff(%rcx), %rcx|',
      Sink.Lines);
    AssertFalse('other lines pass through',
      M.RewriteAddressOf(#9'leaq U_X(%rip), %rcx', @Sink.Add));
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

initialization
  RegisterTest(TTargetToolkitTests);

end.
