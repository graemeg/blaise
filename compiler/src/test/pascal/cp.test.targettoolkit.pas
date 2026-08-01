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
  blaise.testing,
  blaise.codegen.target, blaise.codegen.toolkit,
  blaise.codegen.native.backend, blaise.linker.elf;

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

initialization
  RegisterTest(TTargetToolkitTests);

end.
