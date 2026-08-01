{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.driver;

{ Cross-backend driver abstraction.

  Each backend registers a TBackendDriver subclass singleton.  Blaise.pas
  and TCompileWorker drive the shared pipeline through the base class and
  stop branching on the backend kind for per-backend tool invocation,
  file extensions, and codegen construction.

  Responsibilities a driver OWNS:

    * Codegen construction: which ICodeGen to create and how to apply its
      backend-specific knobs (e.g. the native backend's SetTarget).

    * IR-text artefact shape: the file extension used for the emitted IR,
      so the shared pipeline can pick the right file name without a
      backend switch.

    * Lowering and linking: turning the emitted IR file into a
      relocatable object (per-unit incremental path) or the final linked
      binary (program path).  The QBE driver runs qbe + cc; the native
      driver runs cc on its assembly directly, or the in-process
      assembler + linker driver when --assembler internal is selected.

  Responsibilities a driver does NOT own:

    * Warm-cache discovery, source-hash validation, prebuilt-object
      probing.  Those stay in uUnitLoader and are backend-agnostic.
      SupportsWarmCache exists only as a hint for future "this backend's
      .o isn't trusted for cache reuse yet" gating.

    * .bif embedding into unit objects — an object-format concern shared
      across backends; it stays with the caller (Blaise.pas).

  The architecture follows Andrew Haines' unify_backend_interface
  proposal, with a class-based dispatch surface (virtual methods on an
  abstract base) instead of an interface so shared behaviour — toolchain
  resolution, the common link line — lives in the base class.

  Lifetime: driver singletons are registered once at unit initialization
  into a fixed array of class references.  They are ARC-managed globals,
  released by the program-exit global release pass (the codebase norm for
  unit-level singletons — no explicit finalization needed). }

interface

uses
  Classes,
  blaise.codegen,
  blaise.codegen.target,
  uToolchain;

type
  TBackendKind = (bkQBE, bkNative);

  { Result of offering an unrecognised flag to a driver (Chain of
    Responsibility). }
  TOptionAccept = (
    oaUnknown,        { not my flag — keep trying / report unknown }
    oaConsumedFlag,   { mine, took no value argument }
    oaConsumedValue   { mine, consumed the following arg as its value }
  );

  { Cross-cutting flags that affect codegen, lowering, and linking.
    Built once by the Blaise.pas flag parser and shared (read-only) with
    the compile workers.  Adding a new backend knob is a field here plus
    the driver that reads it; Blaise.pas does not branch on backend to
    apply it. }
  { How the final executable binds to the C world.  lmAuto is the default:
    freestanding when the program binds no C libraries and every external
    symbol resolves from the RTL, dynamic+libc otherwise (with a note naming
    what forced it).  --static / --dynamic force a mode explicitly.  See the
    link-mode section in docs/toolchain-independence.adoc. }
  TLinkMode = (lmAuto, lmStatic, lmDynamic);

  TBackendOpts = class
  public
    Target: TTargetDesc;
    DebugMode: Boolean;       { codegen debug / leak tracking }
    OPDFEnabled: Boolean;     { OPDF code shaping }
    OPDFAsmFile: string;      { OPDF sidecar path, if any }
    UseInternalAsm: Boolean;  { --assembler internal (native backend) }
    AssemblerExplicit: Boolean;  { True when user passed --assembler }
    AssemblerChoiceBad: Boolean;  { a --assembler value was given that is
                                neither 'internal' nor 'external'; the
                                native driver's ValidateOptions rejects it }
    UseInternalLinker: Boolean;  { --linker internal (native backend) }
    LinkerExplicit: Boolean;     { True when user passed --linker }
    LinkerChoiceBad: Boolean;    { --linker value not 'internal' or 'external' }
    RTLSrcDir: string;           { --rtl-src DIR: explicit RTL source directory.
                                   Overrides the binary/CWD-relative lookup, for
                                   a relocated/release binary whose RTL source
                                   lives elsewhere (empty = use default lookup) }
    LinkMode: TLinkMode;         { requested link mode: lmAuto (default) decides
                                   at link time; lmStatic = --static forces the
                                   freestanding, libc-free ELF (the kernel leaf
                                   runtime.syscall.<os> + runtime.cstub +
                                   runtime.start.static.<os> replaces libc; a
                                   non-PIE ET_EXEC with no PT_INTERP); lmDynamic
                                   = --dynamic forces the dynamic PIE + libc.
                                   docs/linux-syscall-migration.adoc }
    LinkLibs: TStringList;       { extra libraries to link (-l<name>), unioned by
                                   the frontend from the program's and its used
                                   units' 'external ''lib''' declarations
                                   (TUnitInterface.LinkLibs).  nil = none.  Owned;
                                   ARC-released with the opts object. }
    LibPaths: TStringList;       { --lib-path DIR: extra directories to search
                                   when the internal linker resolves a -l<name>
                                   to its SONAME (GH #188).  Prepended ahead of
                                   the default system lib dirs.  nil = none.
                                   Owned; released with the opts object. }
    UserLinkLibs: TStringList;   { the subset of LinkLibs that USER code bound
                                   (external 'lib' in the program / non-RTL
                                   units, plus backend-demanded libs).  Libs
                                   bound by runtime.*/rtl.* units are excluded:
                                   the freestanding kernel leaf replaces those,
                                   so they must not force a dynamic link under
                                   lmAuto.  nil = none.  Owned; ARC-released
                                   with the opts object. }
  end;

  TBackendDriver = class
  public
    { Static description of the backend. }
    function Kind: TBackendKind; virtual; abstract;
    function Name: string; virtual; abstract;       { '--backend' identifier }
    function IRFileExt: string; virtual; abstract;  { '.ssa' | '.s' }

    { True when the driver can emit a per-unit linkable artefact for the
      --incremental worker pool.  A driver returning True here MUST
      return a non-nil codegen from CreateUnitCodeGen — the worker fails
      loudly otherwise. }
    function SupportsIncremental: Boolean; virtual;

    { True when uUnitLoader may reuse this backend's .o + .bif on a
      content-hash match.  QBE = true today; native = false until it
      learns to write .bif sidecars and the loader trusts them. }
    function SupportsWarmCache: Boolean; virtual;

    { True when the driver can emit a shared object (the `library` and
      `package` source forms) for ATarget.  Keyed on the TARGET, not just the
      backend: shared-object emission is ELF-specific (ET_DYN, .init_array
      load constructors, .dynsym exports), so a native backend that can emit a
      library for linux-x86_64 cannot for macos-arm64, whose container is
      Mach-O.  The base refuses — a backend opts in by overriding. }
    function SupportsLibrary(const ATarget: TTargetDesc): Boolean; virtual;

    { The external tools this backend needs for ATarget, as resolvable
      specs.  uToolchain.ResolveSpec turns each into a path (env override,
      $BLAISE_TOOLCHAIN_PREFIX, cross-triple prefix, $PATH, host ext).  The
      base lists the shared linker (cc, or the mingw cross-linker for a
      Windows target); a backend overrides to add its own (e.g. the LLVM
      driver appends llc) — call inherited and extend. }
    function DescribeTools(const ATarget: TTargetDesc): TToolSpecArray; virtual;

    { Resolve one named tool from DescribeTools for ATarget; '' if the
      backend declares no such tool. }
    function ToolPath(const AName: string; const ATarget: TTargetDesc): string;

    { Verify any tools the backend needs are reachable.  Returns '' on
      success, an error message otherwise.  Called once before the
      front-end runs (skipped for stdout-only modes, which need no
      toolchain). }
    function CheckToolchain(AOpts: TBackendOpts): string; virtual;

    { Construct the backend's code generator and apply opts.  Returns an
      ARC-managed ICodeGen — do not Free. }
    function CreateCodeGen(AOpts: TBackendOpts): ICodeGen; virtual; abstract;

    { Per-unit codegen for the parallel incremental worker, configured to
      emit a single unit's IR with exports visible to sibling units.
      Default nil: the driver does not support separate-unit emission and
      the dispatcher falls back to the QBE driver. }
    function CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen; virtual;

    { Lower one unit's IR file to a relocatable object (--incremental
      worker path and unit-as-top-level mode).  Returns '' on success,
      an error message otherwise.  Default fails loudly: a driver that
      claims SupportsIncremental must override this. }
    { AIfaceBytes: the unit's .bif payload to embed in the emitted object, or
      '' for none.  A PARAMETER rather than a TBackendOpts field on purpose —
      units are lowered on PARALLEL WORKER THREADS that share one opts object,
      so per-unit data on opts is a data race (it crashed the warm-cache build
      with a torn string pointer in StringAddRef).  Honoured by the native
      driver on Mach-O targets; ELF embeds post-hoc via uElfObject, and the QBE
      driver ignores it. }
    function LowerToObject(const AIRFile, AObjFile: string;
      AOpts: TBackendOpts; const AIfaceBytes: string): string; virtual;

    { Lower the top program's IR file and link the final binary —
      including the OPDF sidecar, prebuilt dep objects, the RTL archive,
      and -lm/-lpthread.  Returns '' on success, an error message
      otherwise.  AExtraObjects may be nil. }
    function LinkProgram(const AIRFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string; virtual; abstract;

    { --- Option contract (Chain of Responsibility + Template Method) --- }

    { The common parser, on a flag it does not own, offers it here.  The
      driver writes any parsed state into the shared AOpts (the same
      TBackendOpts the drivers later read).  Returns oaConsumedValue when
      it took ANextArg as the flag's value, oaConsumedFlag when the flag
      stood alone, oaUnknown when the flag is not this driver's.  Default
      oaUnknown. }
    function AcceptOption(const AFlag, ANextArg: string;
      AOpts: TBackendOpts): TOptionAccept; virtual;

    { Contribute this backend's flag lines to --help.  One (flag,
      description) pair per AddOptionLine call; FormatFlagLine owns the
      column layout so driver lines never drift from the shared block.
      Default: nothing. }
    procedure DescribeOptions(ALines: TStringList); virtual;

    { Post-parse validation with the resolved TBackendOpts visible.
      Returns '' when valid, else a user-facing message.  THIS is where
      cross-cutting rules live ("OPDF debug info is not supported by the
      LLVM backend").  Default ''. }
    function ValidateOptions(AOpts: TBackendOpts): string; virtual;

    { Selection policy: does this backend produce the IR text that
      --emit-ir prints?  QBE = True (fixpoint / RTL-Makefile contract on
      byte-identical QBE IR); native = False (its IR IS assembly, surfaced
      via --emit-asm).  PickTopDriver asks this instead of hard-coding
      bkQBE.  Default False. }
    function ClaimsEmitIR: Boolean; virtual;

  protected
    { The shared linker tool spec for ATarget (cc/clang, or the mingw
      cross-linker for a Windows target).  A subclass's DescribeTools builds
      its array from this plus its own tools — the parser has no
      expression-position `inherited`, so this is the reuse seam. }
    function LinkerToolSpec(const ATarget: TTargetDesc): TToolSpec;

    { Shared link line: cc-driver resolved via uToolchain (env overrides
      and target awareness apply), input file, OPDF sidecar, extra
      objects, the RTL objects, -lm, -lpthread.  Used by every driver's
      LinkProgram. }
    function LinkViaToolchain(const AInputFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string;

    { Compile the implicit RTL units (runtime.* + rtl.platform.*) from source
      into a per-compiler object cache and return their .o paths in AObjPaths
      (link order).  A unit is (re)compiled only when its cached .o is missing
      or older than the source.  Replaces the pre-built blaise_rtl.a — the RTL
      is built from source by the compiler itself (docs/rtl-unification-plan.adoc).
      Both the cc link line and the native internal linker call this.

      RTL units carry inline asm, so they are always built with the native
      backend + internal assembler.  Building goes through a --unit-cache so a
      unit that uses another RTL unit references its globals externally instead
      of re-defining them — without that, the per-unit objects clash on
      duplicate global definitions when linked directly (the archive's member
      selection used to hide this).  The cache also auto-builds intermediate
      deps (e.g. rtl.platform), which are collected too.

      AIncludeStartup controls whether runtime.start.o (which defines the bare
      `_start` entry) is included.  The native internal linker needs it (Blaise
      owns the entry point); the cc/QBE link line must omit it (libc's startup
      provides `_start` and calls `main`), or the two `_start`s collide.

      AAlreadyProvided lists object paths the caller already puts on the link
      line (the program's own prebuilt/incremental deps).  A program that uses
      an RTL unit (e.g. `uses classes` pulls runtime.arc) compiles that unit
      into its own object cache, so supplying our copy too would double-define
      it.  Any RTL unit whose <name>.o basename matches an entry here is skipped.
      Pass nil when the caller adds no objects of its own.

      Returns '' on success, else an error message. }
    function EnsureRTLObjects(AOpts: TBackendOpts; AIncludeStartup: Boolean;
                              AStaticLink: Boolean;
      AAlreadyProvided, AObjPaths: TStringList): string;
  end;

{ Run an external tool, capturing combined output.  Shared by the
  drivers; exposed because the lowering steps run from worker threads
  as well as the main compile path. }
function RunProcess(const AExe: string; AArgs: TStringList;
  out AOutput: string): Integer;

{ Build the leaf-first RTL unit list for a target.  The base list is shared;
  the OS-specific bits are selected from AOS:

    * the platform-layout adapter (rtl.platform.layout.<os>), and
    * for a --static (freestanding, no-libc) link, the kernel leaf that
      replaces libc — the freestanding runtime.start.static.<os> in place of
      the libc runtime.start, plus runtime.syscall.<os> / runtime.libc.<os> /
      runtime.libc2.<os> / runtime.thread.static.<os> and the OS-invariant
      runtime.cstub.

  A dynamic (libc) link keeps the plain list with only the layout adapter
  swapped.  Exposed for unit testing; EnsureRTLObjects drives it off
  AOpts.Static and AOpts.Target.OS.  Caller owns and frees the result. }
function BuildRTLUnitList(AStatic: Boolean;
  AOS: TTargetOS; ACPU: TTargetCPU = cpuX86_64): TStringList;

{ The RTL object-cache directory for a target: <bindir>/rtl/<target>-<key>.

  Keyed on BOTH the target and the identity of the compiler that produced the
  objects.  The target part is obvious (different bytes, different container
  per target).  The compiler part fixes BUG-20260726: cached objects were
  invalidated on source mtime alone, which cannot see that the COMPILER
  changed, so a rebuilt compiler linked the previous one's RTL objects and the
  failure surfaced far from its cause.  See the RTLCacheKey note in the
  implementation for why the identity goes in the directory NAME rather than a
  stamp file.  No trailing delimiter.  Exposed for unit testing;
  EnsureRTLObjects is the only production caller. }
function RTLObjectCacheDir(const ATarget: TTargetDesc): string;

{ Format one --help flag line with the shared 2-space indent and flag
  column.  Single source of truth for the column width so the common
  usage block (Blaise.pas PrintUsage) and each driver's DescribeOptions
  cannot drift.  Example:
    FormatFlagLine('--assembler <id>', 'internal | external (default: external)')
  produces '  --assembler <id>    internal | external (default: external)'. }
function FormatFlagLine(const AFlag, ADesc: string): string;

{ Registry.  Each backend unit registers its singleton in its
  initialization block; consumers fetch by kind.  Looking up an
  unregistered kind raises an exception (programmer error — the backend
  unit wasn't pulled into the uses clause). }

procedure RegisterDriver(ADriver: TBackendDriver);
function GetDriver(AKind: TBackendKind): TBackendDriver;

{ Enumerate registered backends in TBackendKind ordinal order.  Returns a
  TStringList of Name values; caller owns and frees.  Drives --backend
  validation and the usage printer so neither hard-codes the list. }
function RegisteredBackendNames: TStringList;

{ Parse a --backend identifier against the registered drivers.  Returns
  False on an unknown name; caller writes the user-facing error. }
function ParseBackendName(const AName: string; out AKind: TBackendKind): Boolean;

{ The single backend-selection policy decision.  --emit-ir always forces
  QBE (the fixpoint check + RTL Makefile depend on byte-identical QBE
  IR); --emit-asm implies native (its IR IS the .s text the consumer
  expects); otherwise --backend selects directly. }
function PickTopDriver(ABackend: TBackendKind;
  AEmitIR, AEmitAsm: Boolean): TBackendDriver;

implementation

uses
  SysUtils,
  Process,
  blaise.elfreader,
  uToolchain,
  uUnitInterfaceIO;   { EffectiveCompilerId / ContentHashFnv1a64 — RTL cache key }

{ Process id + directory removal, for the per-process private RTL build
  directory.  Declared directly rather than via GRtlPlatform to avoid a
  unit-initialisation-order dependency (this unit may run before the platform
  layer assigns GRtlPlatform). }
function _driver_getpid: Integer; external name 'getpid';
function _driver_rmdir(APath: PChar): Integer; external name 'rmdir';

{ Short key identifying the COMPILER that produced a cached RTL object.

  BUG-20260726: the RTL object cache used to be keyed on --target alone and
  invalidated a unit only when its .o was missing or OLDER THAN ITS SOURCE.  A
  compiler change does not touch RTL source mtimes, so every cached object
  looked current and a new compiler happily linked the PREVIOUS compiler's
  objects.  The symptom lands far from the cause — e.g. a Darwin symbol-naming
  change produced new-style references against old-style definitions and dyld
  aborted on a missing symbol that "should" exist.  The dependency-unit path
  already guards this (a .bif carries EffectiveCompilerId and is rejected on
  mismatch); the RTL .o cache had no equivalent.

  Folding the identity into the DIRECTORY NAME rather than validating a stamp
  file inside a shared directory is deliberate:
    * race-free by construction — the existing concurrency design (private
      build dir + atomic rename, "two builders publish identical results")
      relies on never removing a published object, and an invalidate-by-delete
      would have to remove files a concurrent linker is reading;
    * it closes the partial-unit-set hole a per-directory stamp leaves open: a
      build whose link mode needs FEWER units (BuildRTLUnitList varies with
      --static and target) would refresh only its own subset while marking the
      whole directory current, leaving the untouched objects stale-by-compiler;
    * switching compilers back and forth (a bisect) reuses each one's cache
      instead of forcing a full rebuild every time.
  The cost is that directories accumulate under <bindir>/rtl/; they are build
  artefacts under target/ and go away with a clean.

  EffectiveCompilerId is COMPILER_ID plus a content hash of the running binary,
  and is fixpoint-stable: stage-2 and stage-3 are byte-identical, so they hash
  equal and warm-cache reuse still works.  Hashed again here only to keep the
  directory name short and free of '+'/'.' characters. }
function RTLCacheKey: string;
begin
  Result := Copy(ContentHashFnv1a64(EffectiveCompilerId()), 0, 12);
end;

function RTLObjectCacheDir(const ATarget: TTargetDesc): string;
begin
  Result := IncludeTrailingPathDelimiter(CompilerBinDir()) + 'rtl'
    + '/' + TargetName(ATarget) + '-' + RTLCacheKey();
end;

{ Collect the names of all symbols an ELF object DEFINES with global or weak
  binding (STB_GLOBAL/STB_WEAK and Shndx not SHN_UNDEF) into ADest.
  Used by EnsureRTLObjects to decide, by symbol rather than by filename,
  whether an RTL unit is already supplied by the program's own objects.  Any
  read/parse failure (non-ELF target, truncated file) leaves ADest unchanged —
  the caller then falls back to supplying its copy, which is always safe. }
procedure CollectDefinedSymbols(const AObjPath: string; ADest: TStringList);
var
  Obj: TElfObjectFile;
  I:   Integer;
  Sym: TRdSymbol;
begin
  Obj := nil;
  try
    try
      Obj := ReadElfObjectFile(AObjPath);
    except
      Exit;  { not a readable ELF object — be conservative }
    end;
    for I := 0 to Obj.Symbols.Count - 1 do
    begin
      Sym := Obj.Symbols.Get(I);
      if (Sym.Name <> '') and (Sym.Shndx <> SHN_UNDEF) and
         ((Sym.Bind = STB_GLOBAL) or (Sym.Bind = STB_WEAK)) then
        if ADest.IndexOf(Sym.Name) < 0 then
          ADest.Add(Sym.Name);
    end;
  finally
    Obj.Free();
  end;
end;

{ Indexed by Ord(TBackendKind).  The bound is a literal because the
  parser only accepts integer literals on array decls; keep the upper
  bound in sync with the enum's highest ordinal (bkNative = 1). }
var
  GDrivers: array[0..1] of TBackendDriver;

function TBackendDriver.SupportsIncremental: Boolean;
begin
  Result := False;
end;

function TBackendDriver.SupportsWarmCache: Boolean;
begin
  Result := False;
end;

function TBackendDriver.SupportsLibrary(const ATarget: TTargetDesc): Boolean;
begin
  { Refuse by default: a backend that has not implemented shared-object
    emission must not silently produce a malformed object. }
  Result := False;
end;

function TBackendDriver.LinkerToolSpec(const ATarget: TTargetDesc): TToolSpec;
begin
  { Shared linker slot.  A target tool (HostTool=False): native build uses
    cc/clang; a Windows target cross-links via the mingw clang driver
    (x86_64-w64-mingw32-clang) and never falls back to the host cc. }
  Result.Name     := 'linker';
  Result.EnvVar   := 'BLAISE_LINKER';
  SetLength(Result.Cands, 2);
  Result.Cands[0] := 'cc';
  Result.Cands[1] := 'clang';
  Result.HostTool := False;
  if ATarget.OS = osWindows then
    Result.CrossPrefix := 'x86_64-w64-mingw32-'
  else
    Result.CrossPrefix := '';
end;

function TBackendDriver.DescribeTools(const ATarget: TTargetDesc): TToolSpecArray;
begin
  SetLength(Result, 1);
  Result[0] := Self.LinkerToolSpec(ATarget);
end;

function TBackendDriver.ToolPath(const AName: string;
  const ATarget: TTargetDesc): string;
var
  Specs: TToolSpecArray;
  I:     Integer;
begin
  Result := '';
  Specs := Self.DescribeTools(ATarget);
  for I := 0 to High(Specs) do
    if SameText(Specs[I].Name, AName) then
      Exit(ResolveSpec(Specs[I], ATarget));
end;

function TBackendDriver.CheckToolchain(AOpts: TBackendOpts): string;
begin
  { No tools to probe by default.  AOpts is part of the signature so a
    backend probe can read e.g. AOpts.Target. }
  Result := '';
end;

function TBackendDriver.AcceptOption(const AFlag, ANextArg: string;
  AOpts: TBackendOpts): TOptionAccept;
begin
  Result := oaUnknown;
end;

procedure TBackendDriver.DescribeOptions(ALines: TStringList);
begin
  { No backend-private flags by default. }
end;

function TBackendDriver.ValidateOptions(AOpts: TBackendOpts): string;
begin
  Result := '';
end;

function TBackendDriver.ClaimsEmitIR: Boolean;
begin
  Result := False;
end;

function TBackendDriver.CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen;
begin
  Result := nil;
end;

function TBackendDriver.LowerToObject(const AIRFile, AObjFile: string;
  AOpts: TBackendOpts; const AIfaceBytes: string): string;
begin
  Result := Self.Name() +
    ' backend does not support per-unit object lowering';
end;

{ The implicit RTL units, in dependency/link order (leaf-first).  The compiler
  emits calls to their symbols (_SetArgs, _BlaiseGetMem, _start, ARC helpers, …)
  in every program, so every program links them.  Names are the dotted-flat
  unit names; the source files are <name>.pas in the RTL source directory.
  rtl.platform is the base abstraction layout.linux + posix both use; it owns
  the shared globals (GPlatformLayout, GRtlPlatform) so it must be built first
  and linked once. }
const
  RTL_UNITS: array[0..16] of string = (
    'rtl.platform',
    'runtime.start', 'runtime.atomic', 'runtime.setjmp', 'runtime.utf8',
    'runtime.mem', 'runtime.str', 'runtime.set', 'runtime.arc',
    'runtime.weak', 'runtime.float', 'runtime.math', 'runtime.thread',
    'runtime.exc',
    'runtime.errno.linux',
    'rtl.platform.layout.linux', 'rtl.platform.posix');

{ Lower-case OS suffix used in the OS-specific RTL unit names
  (rtl.platform.layout.<os>, runtime.syscall.<os>, …). }
{ RTLOSSuffix now lives in blaise.codegen.target, so PlatformLayoutInitSym and
  this unit's list-building cannot drift apart (they did, on macOS only). }

function BuildRTLUnitList(AStatic: Boolean; AOS: TTargetOS;
  ACPU: TTargetCPU): TStringList;
var
  I: Integer;
  OS: string;
begin
  OS := RTLOSSuffix(AOS);
  Result := TStringList.Create();
  { The base list, in leaf-first order.  Substitutions: the platform-layout
    and errno adapters always follow the target OS; the CPU-keyed asm leaves
    (atomics, setjmp) follow the target CPU; and the entry point is
    per-profile — a --static link replaces runtime.start with the
    freestanding per-OS start, a dynamic link keeps runtime.start, and
    macOS has NO start unit at all (LC_MAIN + dyld's libSystem glue call
    main directly and exit() its return; the backend's _main follows that
    contract). }
  for I := 0 to High(RTL_UNITS) do
    if SameText(RTL_UNITS[I], 'rtl.platform.layout.linux') then
      Result.Add('rtl.platform.layout.' + OS)
    else if SameText(RTL_UNITS[I], 'runtime.start') then
    begin
      if AOS = osMacOS then
        { omitted — see the LC_MAIN note above }
      else if AStatic then
        Result.Add('runtime.start.static.' + OS)
      else
        Result.Add(RTL_UNITS[I]);
    end
    else if SameText(RTL_UNITS[I], 'runtime.errno.linux') then
    begin
      { The errno-classification leaf (P3, async design) follows the target OS
        on both profiles and swaps to the raw negative-errno variant under
        --static (the raw syscall leaves return -errno; no errno variable). }
      if AStatic then
        Result.Add('runtime.errno.static.' + OS)
      else
        Result.Add('runtime.errno.' + OS);
    end
    else
      Result.Add(RTL_UNITS[I]);
  { NOTE on the CPU dimension: the CPU-keyed asm units (runtime.atomic,
    runtime.setjmp, runtime.utf8) carry BOTH bodies behind CPUX86_64 /
    CPUARM64 defines that follow --target, so the unit NAMES never change —
    a filename split would break `uses runtime.atomic` in shared units.
    ACPU is accepted for future list-level divergence only. }
  { The freestanding kernel leaf that replaces libc under --static: the raw
    syscall stubs, the OS-invariant freestanding C functions (runtime.cstub),
    the libc-shim layers, and the static-TLS thread leaf. }
  if AStatic then
  begin
    Result.Add('runtime.syscall.' + OS);
    Result.Add('runtime.cstub');
    Result.Add('runtime.libc.' + OS);
    Result.Add('runtime.libc2.' + OS);
    Result.Add('runtime.thread.static.' + OS);
  end;
end;

function TBackendDriver.EnsureRTLObjects(AOpts: TBackendOpts;
  AIncludeStartup: Boolean; AStaticLink: Boolean;
  AAlreadyProvided, AObjPaths: TStringList): string;
var
  SrcDir, CacheDir, BuildDir, BlaiseBin: string;
  SrcFile, ObjFile, TmpObj: string;
  I, J, ExitCode: Integer;
  Args: TStringList;
  Msg: string;
  ProvidedSyms, MySyms, Units: TStringList;
  Redundant: Boolean;
begin
  Result := '';
  { Collect every symbol the caller's own objects already DEFINE (the program's
    prebuilt/incremental deps).  An RTL unit the program compiled itself (e.g.
    `uses classes` pulls runtime.arc) is already on the link line; supplying our
    copy too would double-define it.  Match by symbol rather than by filename so
    a same-named-but-different object (e.g. a stale mangled cache entry) does NOT
    suppress the real provider — this mirrors the old archive's member
    selection. }
  ProvidedSyms := TStringList.Create();
  ProvidedSyms.CaseSensitive := True;
  ProvidedSyms.Sorted := True;
  ProvidedSyms.Duplicates := dupIgnore;
  MySyms := TStringList.Create();
  if AAlreadyProvided <> nil then
    for J := 0 to AAlreadyProvided.Count - 1 do
      CollectDefinedSymbols(AAlreadyProvided.Strings[J], ProvidedSyms);
  try
  { RTL source lives in the compiler's own source tree.  Resolution order:
      1. --rtl-src DIR (AOpts.RTLSrcDir) — explicit, for a relocated binary;
      2. $BLAISE_RTL_SRC;
      3. binary/CWD-relative default (RTLSourceDir). }
  if AOpts.RTLSrcDir <> '' then
    SrcDir := ExpandFileName(AOpts.RTLSrcDir)
  else
  begin
    SrcDir := GetEnvironmentVariable('BLAISE_RTL_SRC');
    if SrcDir = '' then
      SrcDir := ExpandFileName(RTLSourceDir());
  end;
  if not DirectoryExists(SrcDir) then
    Exit('RTL source directory not found (' + SrcDir +
      '); pass --rtl-src DIR or set $BLAISE_RTL_SRC to compiler/src/main/pascal');

  { Object cache lives beside the compiler binary so repeated program builds
    reuse it (compiler/target/rtl/).  The shared cache is read for reuse and is
    the link source, but the actual build happens in a per-process private
    sub-directory (rtl/build-<pid>/) and finished objects are atomically renamed
    into the shared cache.  This keeps cross-build reuse while making concurrent
    builders (e.g. parallel e2e suites all warming a cold cache) race-free: a
    reader never sees a half-written object, and two builders just publish
    identical results, last-writer-wins. }
  { the cache is TARGET-KEYED: the same unit compiles to different bytes
    (and a different container) per --target — a shared directory would
    hand a macos-arm64 link Linux ELF objects (or a FreeBSD link objects
    baked with Linux defines).
    It is also COMPILER-KEYED (RTLCacheKey): mtime alone cannot see that the
    COMPILER changed, so a shared-per-target directory handed a new compiler
    the previous one's objects — see the BUG-20260726 note on RTLCacheKey. }
  CacheDir := RTLObjectCacheDir(AOpts.Target);
  ForceDirectories(CacheDir);
  BuildDir := IncludeTrailingPathDelimiter(CacheDir) + 'build-' +
              IntToStr(_driver_getpid());
  ForceDirectories(BuildDir);
  BlaiseBin := ParamStr(0);

  { The unit list to build/link, in leaf-first order.  Selection is driven off
    the target (AOpts.Target.OS) and link mode: the platform layout adapter
    follows the target, and a static link swaps in the freestanding per-OS
    kernel leaf (start / syscall / libc shims / thread) in place of libc.  A
    freestanding target (FreeBSD, Strategy B) has no libc, so it is static
    regardless of the --static flag — but ONLY when the internal linker owns
    the link (AIncludeStartup).  A cc link line (AIncludeStartup=False) always
    links libc: crt1 supplies _start and environ, so the freestanding kernel
    leaf must stay off that line or both are doubly defined.
    See BuildRTLUnitList. }
  Units := BuildRTLUnitList(AStaticLink and AIncludeStartup,
    AOpts.Target.OS, AOpts.Target.CPU);

  for I := 0 to Units.Count - 1 do
  begin
    SrcFile := IncludeTrailingPathDelimiter(SrcDir) + Units.Strings[I] + '.pas';
    ObjFile := IncludeTrailingPathDelimiter(CacheDir) + Units.Strings[I] + '.o';
    if not FileExists(SrcFile) then
      Exit('RTL unit source missing: ' + SrcFile);

    { Recompile only when the shared cached object is missing or stale.  Build
      into the private BuildDir (its own --unit-cache so each unit's RTL deps
      are referenced externally and intermediate deps are built leaf-first),
      then atomically rename the result into the shared CacheDir.  RTL units
      carry inline asm, so the native backend + internal assembler is mandatory. }
    if (not FileExists(ObjFile)) or (FileAge(ObjFile) < FileAge(SrcFile)) then
    begin
      TmpObj := IncludeTrailingPathDelimiter(BuildDir) + Units.Strings[I] + '.o';
      Args := TStringList.Create();
      try
        Args.Add('--backend');     Args.Add('native');
        Args.Add('--assembler');   Args.Add('internal');
        { Propagate the target: the OS conditional-compilation defines follow
          --target, and the per-OS layout units carry target-guarded sections
          (flat leaves + initialization).  Without this the child compiles the
          FreeBSD layout unit with the HOST defines, its guarded sections drop
          out, and the cross link dies with an undefined
          rtl.platform.layout.freebsd_init / _MapAnonFlag. }
        Args.Add('--target');      Args.Add(TargetName(AOpts.Target));
        Args.Add('--source');      Args.Add(SrcFile);
        Args.Add('--unit-path');   Args.Add(SrcDir);
        Args.Add('--unit-cache');  Args.Add(BuildDir);
        Args.Add('--output');      Args.Add(TmpObj);
        ExitCode := RunProcess(BlaiseBin, Args, Msg);
      finally
        Args.Free();
      end;
      if ExitCode <> 0 then
        Exit('failed to build RTL unit ' + Units.Strings[I] +
          ' (exit ' + IntToStr(ExitCode) + '): ' + Msg);
      { Publish atomically.  RenameFile within the same directory tree is an
        atomic rename(2); a concurrent builder doing the same is harmless. }
      if not RenameFile(TmpObj, ObjFile) then
        Exit('failed to publish RTL object ' + ObjFile);
    end;

    { runtime.start defines the bare _start entry — include it only for the
      native internal linker (Blaise owns the entry); the cc link line gets
      _start from libc and must omit it to avoid a multiple-definition. }
    if SameText(Units.Strings[I], 'runtime.start') and (not AIncludeStartup) then
      Continue;
    { Skip this RTL object if EVERY symbol it defines is already defined by the
      caller's objects — i.e. the program compiled this RTL unit itself.  A
      partially-overlapping object is still supplied (its unique symbols are
      needed); the linker resolves the shared ones to the first definition.
      The unit is always built above so later RTL units that depend on it
      resolve against our cache's iface. }
    if ProvidedSyms.Count > 0 then
    begin
      MySyms.Clear();
      CollectDefinedSymbols(ObjFile, MySyms);
      Redundant := MySyms.Count > 0;
      for J := 0 to MySyms.Count - 1 do
        if ProvidedSyms.IndexOf(MySyms.Strings[J]) < 0 then
        begin
          Redundant := False;
          Break;
        end;
      if Redundant then
        Continue;
    end;
    AObjPaths.Add(ObjFile);
  end;

  { Tidy the private build directory.  The published .o files live in the shared
    cache now; the build dir holds only intermediate .bif/.o stragglers.  Remove
    the known per-unit artefacts and the (now-empty) directory.  Best-effort —
    a leftover dir is harmless. }
  for I := 0 to Units.Count - 1 do
  begin
    DeleteFile(IncludeTrailingPathDelimiter(BuildDir) + Units.Strings[I] + '.o');
    DeleteFile(IncludeTrailingPathDelimiter(BuildDir) + Units.Strings[I] + '.bif');
  end;
  _driver_rmdir(PChar(ExcludeTrailingPathDelimiter(BuildDir)));
  Units.Free();
  finally
    ProvidedSyms.Free();
    MySyms.Free();
  end;
end;

function TBackendDriver.LinkViaToolchain(const AInputFile, AOutputFile: string;
  AOpts: TBackendOpts; AExtraObjects: TStringList): string;
var
  Args: TStringList;
  RTLObjs: TStringList;
  Msg, RTLErr: string;
  ExitCode: Integer;
  I: Integer;
begin
  Result := '';
  { Every Blaise program links the implicit RTL units (runtime.* +
    rtl.platform.*).  They are no longer shipped as a pre-built blaise_rtl.a;
    the compiler builds them from source into a per-compiler object cache
    (EnsureRTLObjects) and links the resulting .o files directly.  This is the
    same RTL the native internal linker uses — one source of truth. }
  Args := TStringList.Create();
  RTLObjs := TStringList.Create();
  try
    { cc link line: libc supplies _start, so omit runtime.start.  Pass the
      program's prebuilt deps so an RTL unit it compiled itself (e.g. via
      `uses classes`) is not supplied twice. }
    { AStaticLink=False: a cc link line always links libc (crt1 supplies
      _start), so the freestanding kernel leaf never joins it — this was
      already true before link modes existed (AIncludeStartup=False made
      BuildRTLUnitList's static arm unreachable). }
    RTLErr := Self.EnsureRTLObjects(AOpts, False, False, AExtraObjects, RTLObjs);
    if RTLErr <> '' then
      Exit(RTLErr);
    Args.Add('-o');
    Args.Add(AOutputFile);
    Args.Add(AInputFile);
    { Linker resolved via DescribeTools so a Windows target picks the mingw
      cross-linker and a Windows host adds the .exe extension. }
    { OPDF sidecar (QBE backend only — the native backend appends its
      exact-facts OPDF section to the main assembly instead). }
    if (AOpts.OPDFAsmFile <> '') and FileExists(AOpts.OPDFAsmFile) then
      Args.Add(AOpts.OPDFAsmFile);
    { Pre-built dep object files (auto-discovered by the loader or
      produced by the --incremental workers). }
    if AExtraObjects <> nil then
      for I := 0 to AExtraObjects.Count - 1 do
        Args.Add(AExtraObjects.Strings[I]);
    { RTL objects, in link order. }
    for I := 0 to RTLObjs.Count - 1 do
      Args.Add(RTLObjs.Strings[I]);
    { Link libraries are now demand-driven, not hardcoded: libm ('m') is added
      by the QBE backend only when it emits a libm math call, and libpthread
      ('pthread') flows from runtime.thread's `external 'pthread'` bindings.
      Both arrive via AOpts.LinkLibs.  The native default, --static, and FreeBSD
      paths need neither and get a clean link line.
      Libraries declared via 'external ''lib''' in the program or any used unit
      (plus the backend-demanded libs above) are emitted here as -l<name> — ld
      expands to lib<name>.so/.a. }
    { --lib-path dirs (GH #188): passed to cc as -L so ld searches them too. }
    if AOpts.LibPaths <> nil then
      for I := 0 to AOpts.LibPaths.Count - 1 do
        Args.Add('-L' + AOpts.LibPaths.Strings[I]);
    if AOpts.LinkLibs <> nil then
      for I := 0 to AOpts.LinkLibs.Count - 1 do
        Args.Add('-l' + AOpts.LinkLibs.Strings[I]);
    ExitCode := RunProcess(Self.ToolPath('linker', AOpts.Target), Args, Msg);
  finally
    RTLObjs.Free();
    Args.Free();
  end;
  if ExitCode <> 0 then
    Result := 'link error (exit ' + IntToStr(ExitCode) + '): ' + Msg;
end;

function FormatFlagLine(const AFlag, ADesc: string): string;
const
  { Matches the shared usage block in Blaise.pas PrintUsage: 2-space
    indent, flag field padded so the description starts at column 20. }
  Indent = '  ';
  FlagFieldWidth = 18;
var
  Pad: Integer;
begin
  Result := Indent + AFlag;
  Pad := FlagFieldWidth - Length(AFlag);
  if Pad < 1 then
    Pad := 1;   { always at least one space before the description }
  while Pad > 0 do
  begin
    Result := Result + ' ';
    Pad := Pad - 1;
  end;
  Result := Result + ADesc;
end;

function ReadProcessChunk(AProc: TProcess): string;
begin
  Result := AProc.ReadOutput()
end;

function RunProcess(const AExe: string; AArgs: TStringList;
  out AOutput: string): Integer;
var
  Proc: TProcess;
  Chunk: string;
  I: Integer;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to AArgs.Count - 1 do
      Proc.Parameters.Add(AArgs.Strings[I]);
    Proc.Execute();
    AOutput := '';
    repeat
      Chunk := ReadProcessChunk(Proc);
      AOutput := AOutput + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

procedure RegisterDriver(ADriver: TBackendDriver);
begin
  GDrivers[Ord(ADriver.Kind())] := ADriver;
end;

function GetDriver(AKind: TBackendKind): TBackendDriver;
begin
  Result := GDrivers[Ord(AKind)];
  if Result = nil then
    raise Exception.Create(
      'blaise.codegen.driver: no driver registered for backend kind ' +
      IntToStr(Ord(AKind)) + ' (unit not pulled into uses clause?)');
end;

function RegisteredBackendNames: TStringList;
var
  I: Integer;
begin
  Result := TStringList.Create();
  for I := 0 to 1 do
    if GDrivers[I] <> nil then
      Result.Add(GDrivers[I].Name());
end;

function ParseBackendName(const AName: string; out AKind: TBackendKind): Boolean;
var
  I: Integer;
begin
  Result := False;
  for I := 0 to 1 do
    if (GDrivers[I] <> nil) and SameText(AName, GDrivers[I].Name()) then
    begin
      AKind := GDrivers[I].Kind();
      Result := True;
      Exit;
    end;
end;

function PickTopDriver(ABackend: TBackendKind;
  AEmitIR, AEmitAsm: Boolean): TBackendDriver;
var
  I: Integer;
begin
  if AEmitIR then
  begin
    { --emit-ir prints the IR text of whichever backend claims it.  Ask
      the drivers instead of hard-coding bkQBE, so a future IR-producing
      backend (LLVM) needs no carve-out here. }
    for I := 0 to 1 do
      if (GDrivers[I] <> nil) and GDrivers[I].ClaimsEmitIR() then
        Exit(GDrivers[I]);
    { No registered backend claims --emit-ir: fall back to QBE, the
      historical owner of the byte-identical IR contract. }
    Result := GetDriver(bkQBE);
  end
  else if AEmitAsm then
    Result := GetDriver(bkNative)
  else
    Result := GetDriver(ABackend);
end;

end.
