{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.toolkit;

{ Multi-target toolkit + registry (docs/native-target-architecture.adoc).

  A TTargetToolkit is the Abstract Factory that produces the consistent
  *family* of per-target compiler-side objects: the native backend and the
  link target.  Keeping them behind one factory guarantees the family is
  coherent — a FreeBSD backend paired with a Linux link target is a bug a
  registry-resolved toolkit cannot produce.

  TTargetRegistry maps a TTargetDesc to its toolkit.  Adding a target is a new
  TTargetToolkit subclass plus one registration call — no existing dispatch is
  edited (Open/Closed).  --target resolution and "does this target have a
  native backend?" both go through the registry, replacing the previous
  hard-coded case statements in blaise.codegen.native and
  blaise.codegen.target.

  This is the compiler-side half of the architecture.  The runtime-side ports
  (TKernelABI / TPlatformLayout) live in the RTL and are introduced in later
  steps; they are not part of this unit. }

interface

uses
  SysUtils, Generics.Collections,
  blaise.codegen.target, blaise.codegen.native.backend, blaise.linker.elf;

type
  { Abstract Factory for one target's compiler-side object family. }
  TTargetToolkit = class
  public
    { Canonical "<os>-<cpu>" name (matches blaise.codegen.target.TargetName). }
    function Name: string; virtual; abstract;
    { Construct the native backend for this target.  Caller owns the result. }
    function MakeBackend: TNativeBackend; virtual; abstract;
    { Construct the link target (ELF header facts) for this target.  Caller
      owns the result. }
    function MakeLinkTarget: TLinkTarget; virtual; abstract;
  end;

  { Linux x86_64 — the original (and, before FreeBSD, only) target. }
  TLinuxX86_64Toolkit = class(TTargetToolkit)
  public
    function Name: string; override;
    function MakeBackend: TNativeBackend; override;
    function MakeLinkTarget: TLinkTarget; override;
  end;

  { FreeBSD x86_64 — shares the System V AMD64 ABI and the x86_64 instruction
    selector with Linux, so MakeBackend reuses TX86_64Backend; only the link
    target's OS/ABI byte differs.  The runtime/syscall divergence is handled
    in the RTL (TKernelABI / TPlatformLayout), not here. }
  TFreeBSDX86_64Toolkit = class(TTargetToolkit)
  public
    function Name: string; override;
    function MakeBackend: TNativeBackend; override;
    function MakeLinkTarget: TLinkTarget; override;
  end;

  { macOS arm64 — the first Mach-O target: TArm64Backend + the in-process
    arm64 assembler produce Mach-O MH_OBJECT files.  MakeLinkTarget returns
    nil for now: the executable link needs the Mach-O linker + ad-hoc code
    signature (Phase 4/5 of the macOS bring-up); until then the target
    supports object emission and --emit-asm only. }
  TMacOSArm64Toolkit = class(TTargetToolkit)
  public
    function Name: string; override;
    function MakeBackend: TNativeBackend; override;
    function MakeLinkTarget: TLinkTarget; override;
  end;

  { Toolkit registry.  Owns the registered toolkit instances.  A linear list
    is correct here: the target count is tiny (one per supported OS/CPU), so a
    name scan is cheaper than a hash map and avoids instantiating a generic
    map over a class type. }
  TTargetRegistry = class
  private
    FByName: TOrderedDictionary<string, TTargetToolkit>;
  public
    constructor Create;
    destructor Destroy; override;
    { Register a toolkit.  Registry takes ownership. }
    procedure Register(AToolkit: TTargetToolkit);
    { Resolve the toolkit for ATarget, or nil if none is registered. }
    function Resolve(const ATarget: TTargetDesc): TTargetToolkit;
  end;

{ The process-wide registry, populated in this unit's initialization. }
function GTargetRegistry: TTargetRegistry;

{ Resolve the toolkit for ATarget via the global registry (nil if unknown). }
function ResolveToolkit(const ATarget: TTargetDesc): TTargetToolkit;

{ True when ATarget has a registered native backend toolkit.  Replacement for
  blaise.codegen.target.TargetHasNativeBackend, driven by the registry. }
function RegisteredHasNativeBackend(const ATarget: TTargetDesc): Boolean;

implementation

uses
  blaise.codegen.native.x86_64, blaise.codegen.native.arm64;

{ ---- TLinuxX86_64Toolkit --------------------------------------------- }

function TLinuxX86_64Toolkit.Name: string;
begin
  Result := 'linux-x86_64';
end;

function TLinuxX86_64Toolkit.MakeBackend: TNativeBackend;
var
  T: TTargetDesc;
begin
  MakeTarget(osLinux, cpuX86_64, T);
  Result := TX86_64Backend.Create(T);
end;

function TLinuxX86_64Toolkit.MakeLinkTarget: TLinkTarget;
begin
  Result := LinuxX86_64Target();
end;

{ ---- TFreeBSDX86_64Toolkit ------------------------------------------- }

function TFreeBSDX86_64Toolkit.Name: string;
begin
  Result := 'freebsd-x86_64';
end;

function TFreeBSDX86_64Toolkit.MakeBackend: TNativeBackend;
var
  T: TTargetDesc;
begin
  MakeTarget(osFreeBSD, cpuX86_64, T);
  Result := TX86_64Backend.Create(T);
end;

function TFreeBSDX86_64Toolkit.MakeLinkTarget: TLinkTarget;
begin
  Result := FreeBSDX86_64Target();
end;

{ ---- TMacOSArm64Toolkit ----------------------------------------------- }

function TMacOSArm64Toolkit.Name: string;
begin
  Result := 'macos-arm64';
end;

function TMacOSArm64Toolkit.MakeBackend: TNativeBackend;
var
  T: TTargetDesc;
begin
  MakeTarget(osMacOS, cpuArm64, T);
  Result := TArm64Backend.Create(T);
end;

function TMacOSArm64Toolkit.MakeLinkTarget: TLinkTarget;
begin
  { no ELF link facts for a Mach-O target — the executable link path
    checks for nil and reports the honest gap }
  Result := nil;
end;

{ ---- TTargetRegistry ------------------------------------------------- }

constructor TTargetRegistry.Create;
begin
  inherited Create();
  FByName := TOrderedDictionary<string, TTargetToolkit>.Create();
end;

destructor TTargetRegistry.Destroy;
var
  I:  Int;
  Tk: TTargetToolkit;
begin
  if FByName <> nil then
  begin
    for I := 0 to FByName.Count - 1 do
    begin
      Tk := FByName.Values[I];
      Tk.Free();
    end;
    FByName.Free();
  end;
  inherited Destroy();
end;

procedure TTargetRegistry.Register(AToolkit: TTargetToolkit);
begin
  FByName.Items[AToolkit.Name()] := AToolkit;
end;

function TTargetRegistry.Resolve(const ATarget: TTargetDesc): TTargetToolkit;
var
  Key: string;
  Tk:  TTargetToolkit;
begin
  Key := TargetName(ATarget);
  if FByName.TryGetValue(Key, Tk) then
    Result := Tk
  else
    Result := nil;
end;

{ ---- Global registry -------------------------------------------------- }

var
  GRegistry: TTargetRegistry;

{ Build the registry on first use.  This unit's initialization section calls
  EnsureRegistry once at startup (single-threaded, before any worker thread is
  spawned), so the common path is a no-op nil check.  The lazy guard also
  covers the case where a codegen unit's own initialization constructs a
  backend before this unit's initialization runs (link-order independence).

  Thread-safety note: the incremental compile worker pool is THREADS, not
  processes.  The registry must be FULLY built before it is published to the
  global, or a second thread could observe a non-nil GRegistry whose toolkit
  list is still empty and wrongly conclude a target has no backend.  Build
  into a local and assign the global last (publish-after-populate). }
procedure EnsureRegistry;
var
  R: TTargetRegistry;
begin
  if GRegistry = nil then
  begin
    R := TTargetRegistry.Create();
    R.Register(TLinuxX86_64Toolkit.Create());
    R.Register(TFreeBSDX86_64Toolkit.Create());
    R.Register(TMacOSArm64Toolkit.Create());
    GRegistry := R;
  end;
end;

function GTargetRegistry: TTargetRegistry;
begin
  EnsureRegistry();
  Result := GRegistry;
end;

function ResolveToolkit(const ATarget: TTargetDesc): TTargetToolkit;
begin
  EnsureRegistry();
  Result := GRegistry.Resolve(ATarget);
end;

function RegisteredHasNativeBackend(const ATarget: TTargetDesc): Boolean;
begin
  EnsureRegistry();
  Result := GRegistry.Resolve(ATarget) <> nil;
end;

initialization
  EnsureRegistry();

finalization
  GRegistry.Free();

end.
