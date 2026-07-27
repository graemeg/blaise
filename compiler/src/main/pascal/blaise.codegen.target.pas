{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.target;

{ Target description for the native code-generation backend.

  A target is an (OS, CPU) pair plus the derived facts the backend and the
  toolchain driver need: pointer size, canonical name, and (later) register
  sets / ABI descriptors.  Kept in its own unit so both the toolchain
  resolver (uToolchain) and the native codegen (blaise.codegen.native) can
  depend on it without a cycle.

  Only x86_64-linux is implemented for codegen today; the other (OS, CPU)
  combinations are accepted by ParseTargetName so --target can name them and
  the driver can fail with a clear "backend not yet implemented for <target>"
  message rather than an opaque error.  Adding a real backend for one of them
  is a new TNativeBackend subclass keyed on these enums.

  FreeBSD/x86_64 shares the System V AMD64 ABI with Linux, so the x86_64
  instruction selection will be reused; the OS differences are confined to the
  link line (CRT objects, dynamic linker) handled by the toolchain driver. }

interface

type
  TTargetOS  = (osLinux, osFreeBSD, osWindows, osMacOS);
  TTargetCPU = (cpuX86_64, cpuI386, cpuArm64);

  { Pointer-size and other per-target facts live here so nothing in the
    backend hard-codes 8.  PtrSize flips to 4 for i386 by this record alone. }
  TTargetDesc = record
    OS:  TTargetOS;
    CPU: TTargetCPU;
  end;

{ Build a target record. }
procedure MakeTarget(AOS: TTargetOS; ACPU: TTargetCPU; out ATarget: TTargetDesc);

{ The host target this compiler binary runs on (the default when --target is
  omitted).  The host OS is one of TTargetOS, detected from our own
  executable's name — a '.exe' suffix means Windows (including under wine). }
function HostTarget: TTargetDesc;

{ Pointer size in bytes for the target (8 for 64-bit, 4 for 32-bit). }
function PtrSize(const ATarget: TTargetDesc): Integer;

{ Parse a CLI target identifier of the form "<os>-<cpu>", e.g.
  "linux-x86_64".  Returns False on an unknown/unsupported identifier;
  ATarget is left unchanged in that case. }
function ParseTargetName(const AName: string; out ATarget: TTargetDesc): Boolean;

{ Canonical "<os>-<cpu>" name — inverse of ParseTargetName, for messages. }
function TargetName(const ATarget: TTargetDesc): string;

{ True when the native backend can actually generate code for this target. }
function TargetHasNativeBackend(const ATarget: TTargetDesc): Boolean;

{ True when the QBE backend can produce a WORKING program for ATarget.

  False for Darwin.  QBE is the legacy backend — native has been the default
  since v0.12.0 — and it was never ported to Mach-O: a QBE-compiled program
  links against the natively-built RTL but crashes before reaching main (control
  reaches a routine nothing calls, via neither a vtable slot nor fall-through,
  which points at symbol resolution in the QBE->native-RTL link).  Rather than
  emit a binary that cannot run, the QBE driver refuses the target outright, and
  the e2e harness drops QBE from its backend set on macOS so the NATIVE arm of
  every dual-backend test still runs and still counts.

  Linux and FreeBSD are unaffected and keep full QBE coverage; this is not a
  step toward removing QBE, only an honest statement of where it works. }
function TargetHasQBEBackend(const ATarget: TTargetDesc): Boolean;

{ True when the target's object/executable container is ELF.  macOS uses
  Mach-O; everything else we target is ELF.  Gate ELF-specific output on this
  rather than on an OS blocklist, so a new ELF OS needs no edit here. }
function TargetUsesElf(const ATarget: TTargetDesc): Boolean;

{ True when the target is FREESTANDING — reached via direct syscalls with no
  libc, so it is always linked as a static ET_EXEC with a self-supplied _start
  and no PT_INTERP / libc NEEDED (Strategy B, see
  docs/freebsd-x86_64-backend-design.adoc).  FreeBSD is freestanding; Linux
  links dynamic libc by default.  Drives both the RTL unit-list selection
  (the kernel leaf is always pulled in) and the internal linker's static mode. }
function TargetIsFreestanding(const ATarget: TTargetDesc): Boolean;

{ Lower-case OS token used in the OS-specific RTL unit names, e.g.
  'linux' / 'freebsd' in rtl.platform.layout.<os>, runtime.syscall.<os>.
  The single source of truth for the OS suffix, shared by the driver's RTL
  unit-list selection and the codegen backends' platform-layout-init call. }
function TargetOSName(const ATarget: TTargetDesc): string;

{ Assembler symbol of the target's platform-layout unit initialiser
  (rtl.platform.layout.<os>_init).  The compiler emits a direct call to this
  from main so the compile-time --target's layout assigns GPlatformLayout first,
  regardless of the program's import graph. }
{ The OS suffix used by RTL UNIT FILENAMES (rtl.platform.layout.<suffix>,
  runtime.errno.<suffix>, ...).  This is NOT always TargetOSName: macOS's
  adapter leaves are named '.darwin', the platform name, while the target is
  spelled 'macos'.  Everything that names an RTL unit — the driver's
  BuildRTLUnitList and PlatformLayoutInitSym — must derive it from here, because
  the two spellings coincide for linux and freebsd and diverge ONLY for macOS: a
  second, independent mapping stayed invisible on the other targets and then
  emitted a call to rtl.platform.layout.macos_init that nothing defines. }
function RTLOSSuffix(AOS: TTargetOS): string;

function PlatformLayoutInitSym(const ATarget: TTargetDesc): string;

{ Platform constants derived from the target OS. }
function TargetLineEnding(const ATarget: TTargetDesc): string;
function TargetDirectorySeparator(const ATarget: TTargetDesc): string;
function TargetPathSeparator(const ATarget: TTargetDesc): string;

{ Executable-file extension for binaries that run on ATarget's OS: '.exe' on
  Windows, empty elsewhere.  Used to probe host tools (llc, cc) with the right
  suffix and to name output binaries. }
function ExecutableExtension(const ATarget: TTargetDesc): string;

var
  GTarget: TTargetDesc;

implementation

uses
  SysUtils;

procedure MakeTarget(AOS: TTargetOS; ACPU: TTargetCPU; out ATarget: TTargetDesc);
begin
  ATarget.OS  := AOS;
  ATarget.CPU := ACPU;
end;

function HostTarget: TTargetDesc;
begin
  { The host OS is a COMPILE-TIME property of this binary: a blaise built with
    `--target freebsd-x86_64` runs on FreeBSD, so its HostTarget must report
    FreeBSD.  The OS conditional symbols are target-driven (injected by the
    driver from the resolved --target; see Blaise.pas and uLexer.SeedPredefines),
    the IFDEF FREEBSD below is true exactly when THIS compiler was built for
    FreeBSD.  This is what lets a FreeBSD-hosted blaise default (no --target) to
    producing FreeBSD binaries — the basis of self-hosting on FreeBSD. }
{$IFDEF FREEBSD}
  MakeTarget(osFreeBSD, cpuX86_64, Result);
{$ELSE}
  {$IFDEF DARWIN}
  { macOS is arm64 for our purposes: the only Darwin target the backend
    supports is macos-arm64.  Without this branch a macOS-built compiler fell
    through to the Linux default and misreported its own host as
    linux-x86_64 — so it defaulted to emitting ELF/x86-64 when run with no
    --target (found during the 2026-07-23 on-device bring-up). }
  MakeTarget(osMacOS, cpuArm64, Result);
  {$ELSE}
  {$IFDEF WINDOWS}
  MakeTarget(osWindows, cpuX86_64, Result);
  {$ELSE}
  MakeTarget(osLinux, cpuX86_64, Result);
  {$ENDIF}
  {$ENDIF}
{$ENDIF}
end;

function PtrSize(const ATarget: TTargetDesc): Integer;
begin
  if ATarget.CPU = cpuI386 then
    Result := 4
  else
    Result := 8;
end;

function ParseTargetName(const AName: string; out ATarget: TTargetDesc): Boolean;
var
  Lower: string;
begin
  Result := True;
  Lower  := LowerCase(AName);
  if Lower = 'linux-x86_64' then
    MakeTarget(osLinux, cpuX86_64, ATarget)
  else if Lower = 'linux-i386' then
    MakeTarget(osLinux, cpuI386, ATarget)
  else if Lower = 'linux-arm64' then
    MakeTarget(osLinux, cpuArm64, ATarget)
  else if Lower = 'freebsd-x86_64' then
    MakeTarget(osFreeBSD, cpuX86_64, ATarget)
  else if Lower = 'freebsd-arm64' then
    MakeTarget(osFreeBSD, cpuArm64, ATarget)
  else if Lower = 'windows-x86_64' then
    MakeTarget(osWindows, cpuX86_64, ATarget)
  else if Lower = 'macos-arm64' then
    MakeTarget(osMacOS, cpuArm64, ATarget)
  else
    Result := False;
end;

function TargetName(const ATarget: TTargetDesc): string;
var
  OSPart, CPUPart: string;
begin
  case ATarget.OS of
    osLinux:   OSPart := 'linux';
    osFreeBSD: OSPart := 'freebsd';
    osWindows: OSPart := 'windows';
    osMacOS:   OSPart := 'macos';
  else
    OSPart := 'unknown';
  end;
  case ATarget.CPU of
    cpuX86_64: CPUPart := 'x86_64';
    cpuI386:   CPUPart := 'i386';
    cpuArm64:  CPUPart := 'arm64';
  else
    CPUPart := 'unknown';
  end;
  Result := OSPart + '-' + CPUPart;
end;

function TargetHasNativeBackend(const ATarget: TTargetDesc): Boolean;
begin
  { Only x86_64-linux is implemented so far. }
  Result := (ATarget.OS = osLinux) and (ATarget.CPU = cpuX86_64);
end;

function TargetHasQBEBackend(const ATarget: TTargetDesc): Boolean;
begin
  { see the declaration — Darwin was never ported }
  Result := ATarget.OS <> osMacOS;
end;

function TargetUsesElf(const ATarget: TTargetDesc): Boolean;
begin
  { macOS is Mach-O; Linux/FreeBSD are ELF.  Windows would be PE, and is not a
    native-backend target yet — it is excluded here rather than assumed ELF. }
  Result := (ATarget.OS = osLinux) or (ATarget.OS = osFreeBSD);
end;

function TargetIsFreestanding(const ATarget: TTargetDesc): Boolean;
begin
  { FreeBSD uses Strategy B — direct syscalls, no libc — so it is always a
    static, freestanding ET_EXEC.  Other OSes link dynamic libc by default. }
  Result := (ATarget.OS = osFreeBSD);
end;

function TargetOSName(const ATarget: TTargetDesc): string;
begin
  case ATarget.OS of
    osFreeBSD: Result := 'freebsd';
    osWindows: Result := 'windows';
    osMacOS:   Result := 'macos';
  else
    Result := 'linux';
  end;
end;

function RTLOSSuffix(AOS: TTargetOS): string;
begin
  case AOS of
    osFreeBSD: Result := 'freebsd';
    osMacOS:   Result := 'darwin';
  else
    { Linux is the default host leaf; other OSes gain their own suffix as
      their adapter set lands. }
    Result := 'linux';
  end;
end;

function PlatformLayoutInitSym(const ATarget: TTargetDesc): string;
begin
  { NativeMangle/QBE mangling of an rtl.* unit keeps the dotted name verbatim
    and appends '_init'; the layout unit is rtl.platform.layout.<suffix>.
    RTLOSSuffix, not TargetOSName — see the note on RTLOSSuffix. }
  Result := 'rtl.platform.layout.' + RTLOSSuffix(ATarget.OS) + '_init';
end;

function TargetLineEnding(const ATarget: TTargetDesc): string;
begin
  case ATarget.OS of
    osWindows: Result := #13#10;
  else
    Result := #10;
  end;
end;

function TargetDirectorySeparator(const ATarget: TTargetDesc): string;
begin
  case ATarget.OS of
    osWindows: Result := '\';
  else
    Result := '/';
  end;
end;

function TargetPathSeparator(const ATarget: TTargetDesc): string;
begin
  case ATarget.OS of
    osWindows: Result := ';';
  else
    Result := ':';
  end;
end;

function ExecutableExtension(const ATarget: TTargetDesc): string;
begin
  case ATarget.OS of
    osWindows: Result := '.exe';
  else
    Result := '';
  end;
end;

initialization
  GTarget := HostTarget();

end.
