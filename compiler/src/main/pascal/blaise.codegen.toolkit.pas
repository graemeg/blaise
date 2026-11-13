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
  SysUtils, Classes, Generics.Collections,
  blaise.codegen.target, blaise.codegen.native.backend, blaise.linker.elf;

type
  { The container of a linked image.  The driver dispatches the image link
    on this rather than on the OS. }
  TImageFormat = (ifElf, ifMachO, ifPe);

  { Abstract Factory for one target's compiler-side object family. }
  TTargetToolkit = class
  public
    { Canonical "<os>-<cpu>" name (matches blaise.codegen.target.TargetName). }
    function Name: string; virtual; abstract;
    { Construct the native backend for this target.  Caller owns the result. }
    function MakeBackend: TNativeBackend; virtual; abstract;
    { Construct the link target (ELF header facts) for this target, or nil
      when the image is not ELF.  Caller owns the result. }
    function MakeLinkTarget: TLinkTarget; virtual; abstract;
    { The container the linker writes for this target. }
    function ImageFormat: TImageFormat; virtual; abstract;
    { The name under which the linked image records a dependency on the
      link library ALibName (as written in `external '<lib>'`): the
      DT_NEEDED soname for an ELF image.  On a native link the driver
      prefers the soname read off the library file; this table is the
      authority for a cross link, and the fallback on a miss. }
    function LibraryImageName(const ALibName: string): string; virtual;
    { Append this target's default library search directories to AOut,
      skipping any already present.  The driver adds --lib-path and the
      environment's lists first. }
    procedure AddSystemLibDirs(AOut: TStringList); virtual;
  end;

  { An x86-64 target with an ELF image and the System V convention: the
    backend uses the System V boundary ABI and ELF local-exec TLS. }
  TSysVElfX86_64Toolkit = class(TTargetToolkit)
  public
    function MakeBackend: TNativeBackend; override;
    function ImageFormat: TImageFormat; override;
    { The POSIX directories common to every ELF target; on FreeBSD
      /usr/local/lib is where pkg(8) installs third-party libraries such as
      X11 and ncurses. }
    procedure AddSystemLibDirs(AOut: TStringList); override;
  end;

  { Linux x86_64 — the original (and, before FreeBSD, only) target. }
  TLinuxX86_64Toolkit = class(TSysVElfX86_64Toolkit)
  public
    function Name: string; override;
    function MakeLinkTarget: TLinkTarget; override;
    { glibc's canonical sonames. }
    function LibraryImageName(const ALibName: string): string; override;
    { The Debian/Ubuntu multiarch directories, ahead of the common set. }
    procedure AddSystemLibDirs(AOut: TStringList); override;
  end;

  { FreeBSD x86_64 — shares the System V AMD64 ABI and the x86_64 instruction
    selector with Linux, so MakeBackend reuses TX86_64Backend; only the link
    target's OS/ABI byte differs.  The runtime/syscall divergence is handled
    in the RTL (TKernelABI / TPlatformLayout), not here. }
  TFreeBSDX86_64Toolkit = class(TSysVElfX86_64Toolkit)
  public
    function Name: string; override;
    function MakeLinkTarget: TLinkTarget; override;
    { FreeBSD is not a re-versioned Linux: threads live in libthr, and
      dlopen/dlsym and the POSIX realtime routines are part of libc. }
    function LibraryImageName(const ALibName: string): string; override;
  end;

  { macOS arm64 — the Mach-O target: TArm64Backend + the in-process arm64
    assembler produce Mach-O MH_OBJECT files, and the Mach-O linker writes
    the image.  There are no ELF link facts, so MakeLinkTarget returns nil;
    dylib resolution lives with the Mach-O linker
    (blaise.linker.macho.dylib). }
  TMacOSArm64Toolkit = class(TTargetToolkit)
  public
    function Name: string; override;
    function MakeBackend: TNativeBackend; override;
    function MakeLinkTarget: TLinkTarget; override;
    function ImageFormat: TImageFormat; override;
  end;

  { Windows x86_64 -- a PE32+ image linked from ELF objects (design
    decision D2, blaise.linker.pe).  The backend keeps the System V
    convention internally and uses the Win64 convention at the foreign
    boundary (D1); threadvars use the PE TLS model. }
  TWindowsX86_64Toolkit = class(TTargetToolkit)
  public
    function Name: string; override;
    function MakeBackend: TNativeBackend; override;
    { nil: a PE image has no ELF link facts }
    function MakeLinkTarget: TLinkTarget; override;
    function ImageFormat: TImageFormat; override;
    { The DLL that exports a library's routines: the C runtime for c and m,
      OpenSSL 3's libssl-3-x64.dll and libcrypto-3-x64.dll for ssl and
      crypto, a name already ending in .dll verbatim, otherwise the name with
      .dll appended. }
    function LibraryImageName(const ALibName: string): string; override;
    { Nothing on a cross host: the linker cannot read the DLLs, so a cross
      link trusts the import names.  A native Windows host adds its system
      directory, %SystemRoot%\System32, for the export check
      (TPeLinker.LibDirs). }
    procedure AddSystemLibDirs(AOut: TStringList); override;
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
  blaise.codegen.native.x86_64, blaise.codegen.native.x86_64.abi,
  blaise.codegen.native.arm64;

{ Add ADir to AOut unless it is already listed. }
procedure AddLibDir(AOut: TStringList; const ADir: string);
begin
  if AOut.IndexOf(ADir) < 0 then
    AOut.Add(ADir);
end;

{ ---- TTargetToolkit -------------------------------------------------- }

function TTargetToolkit.LibraryImageName(const ALibName: string): string;
begin
  raise Exception.Create('internal: target ' + Self.Name() +
    ' does not map link libraries to image dependencies');
end;

procedure TTargetToolkit.AddSystemLibDirs(AOut: TStringList);
begin
  raise Exception.Create('internal: target ' + Self.Name() +
    ' has no ELF library search directories');
end;

{ ---- TSysVElfX86_64Toolkit -------------------------------------------- }

function TSysVElfX86_64Toolkit.MakeBackend: TNativeBackend;
var
  T: TTargetDesc;
  B: TX86_64Backend;
begin
  if not ParseTargetName(Self.Name(), T) then
    raise Exception.Create('internal: unparsable toolkit name ' + Self.Name());
  B := TX86_64Backend.Create(T);
  B.AdoptStrategies(TSysVBoundaryAbi.Create(), TElfLocalExecTls.Create());
  Result := B;
end;

function TSysVElfX86_64Toolkit.ImageFormat: TImageFormat;
begin
  Result := ifElf;
end;

procedure TSysVElfX86_64Toolkit.AddSystemLibDirs(AOut: TStringList);
begin
  AddLibDir(AOut, '/usr/local/lib');
  AddLibDir(AOut, '/lib');
  AddLibDir(AOut, '/usr/lib');
end;

{ ---- TLinuxX86_64Toolkit --------------------------------------------- }

function TLinuxX86_64Toolkit.Name: string;
begin
  Result := 'linux-x86_64';
end;

function TLinuxX86_64Toolkit.MakeLinkTarget: TLinkTarget;
begin
  Result := LinuxX86_64Target();
end;

function TLinuxX86_64Toolkit.LibraryImageName(const ALibName: string): string;
begin
  if SameText(ALibName, 'pthread') then Result := 'libpthread.so.0'
  else if SameText(ALibName, 'm')  then Result := 'libm.so.6'
  else if SameText(ALibName, 'dl') then Result := 'libdl.so.2'
  else if SameText(ALibName, 'rt') then Result := 'librt.so.1'
  else if SameText(ALibName, 'c')  then Result := 'libc.so.6'
  else Result := 'lib' + ALibName + '.so';
end;

procedure TLinuxX86_64Toolkit.AddSystemLibDirs(AOut: TStringList);
begin
  AddLibDir(AOut, '/lib/x86_64-linux-gnu');
  AddLibDir(AOut, '/usr/lib/x86_64-linux-gnu');
  inherited AddSystemLibDirs(AOut);
end;

{ ---- TFreeBSDX86_64Toolkit ------------------------------------------- }

function TFreeBSDX86_64Toolkit.Name: string;
begin
  Result := 'freebsd-x86_64';
end;

function TFreeBSDX86_64Toolkit.MakeLinkTarget: TLinkTarget;
begin
  Result := FreeBSDX86_64Target();
end;

function TFreeBSDX86_64Toolkit.LibraryImageName(const ALibName: string): string;
begin
  if SameText(ALibName, 'pthread') then Result := 'libthr.so.3'
  else if SameText(ALibName, 'm')  then Result := 'libm.so.5'
  else if SameText(ALibName, 'dl') then Result := 'libc.so.7'
  else if SameText(ALibName, 'rt') then Result := 'libc.so.7'
  else if SameText(ALibName, 'c')  then Result := 'libc.so.7'
  else Result := 'lib' + ALibName + '.so';
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
  { no ELF link facts for a Mach-O image }
  Result := nil;
end;

function TMacOSArm64Toolkit.ImageFormat: TImageFormat;
begin
  Result := ifMachO;
end;

{ ---- TWindowsX86_64Toolkit ---- }

function TWindowsX86_64Toolkit.Name: string;
begin
  Result := 'windows-x86_64';
end;

function TWindowsX86_64Toolkit.MakeBackend: TNativeBackend;
var
  T: TTargetDesc;
  B: TX86_64Backend;
begin
  if not ParseTargetName(Self.Name(), T) then
    raise Exception.Create('internal: unparsable toolkit name ' + Self.Name());
  B := TX86_64Backend.Create(T);
  B.AdoptStrategies(TWin64BoundaryAbi.Create(), TPeTlsModel.Create());
  Result := B;
end;

function TWindowsX86_64Toolkit.MakeLinkTarget: TLinkTarget;
begin
  Result := nil;
end;

function TWindowsX86_64Toolkit.ImageFormat: TImageFormat;
begin
  Result := ifPe;
end;

function TWindowsX86_64Toolkit.LibraryImageName(
  const ALibName: string): string;
var
  Lower: string;
begin
  Lower := LowerCase(ALibName);
  if (Lower = 'c') or (Lower = 'm') then
    Result := 'msvcrt.dll'
  else if Lower = 'ssl' then
    Result := 'libssl-3-x64.dll'
  else if Lower = 'crypto' then
    Result := 'libcrypto-3-x64.dll'
  else if (Length(Lower) > 4) and
          (Copy(Lower, Length(Lower) - 4, 4) = '.dll') then
    Result := ALibName
  else
    Result := ALibName + '.dll';
end;

procedure TWindowsX86_64Toolkit.AddSystemLibDirs(AOut: TStringList);
var
  Root: string;
begin
  if HostTarget().OS <> osWindows then
    Exit;
  Root := GetEnvironmentVariable('SystemRoot');
  if Root <> '' then
    AddLibDir(AOut, IncludeTrailingPathDelimiter(Root) + 'System32');
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
    R.Register(TWindowsX86_64Toolkit.Create());
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
