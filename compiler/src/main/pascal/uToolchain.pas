{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines, Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uToolchain;

{ Resolution of the external tools the Blaise driver shells out to and the
  install-relative path to the Blaise RTL archive.

  Lives separately from Blaise.pas so the policy — env-var overrides, PATH
  probing, install-dir lookups — is in one place.

  Resolution is uniform across all slots:

    1. Explicit env-var override (BLAISE_QBE, BLAISE_AS, BLAISE_LINKER,
       BLAISE_RTL).  If set and the file exists, use it verbatim.
    2. Walk $PATH for a list of candidate basenames in preference order.
    3. Fall back to the first candidate basename — RunProcess surfaces a
       "not found" error at exec time if the tool was actually needed.

  This trimmed version was ported from a contributor LLVM-backend branch.  The
  LLVM-specific slots (llc / opt / llvm-dlltool, Windows import libs, well-
  known LLVM install-dir probing) were dropped: the native backend emits
  assembly text and links with a cc driver, exactly like the QBE path. }

interface

uses
  blaise.codegen.target;

type
  { Variant of a tool, determining the CLI syntax callers emit. }
  TToolKind = (
    tkUnknown,        { resolver couldn't classify }
    tkGnuAs,          { as -o OUT IN.s — GNU assembler.  Named tkGnuAs (not the
                        bare tkAs) so it does not collide with uLexer's
                        TTokenKind.tkAs: a bare `tkAs` here is ambiguous and
                        bare-member resolution is cross-unit order-fragile,
                        which could bind it to TTokenKind.tkAs (ordinal 40) —
                        out of range for this 4-member enum, sending downstream
                        Kind-indexing off the end into a layout-sensitive crash. }
    tkCCDriver,       { cc / gcc / clang-as-driver — GNU link line }
    tkQBE             { qbe -o OUT IN.ssa }
  );

  TTool = record
    Path: string;     { absolute path on a hit, basename on miss }
    Kind: TToolKind;  { set by the per-tool resolver }
  end;

  TToolchain = record
    QBE:        TTool;   { QBE backend only }
    Assembler:  TTool;   { native backend: assemble .s -> .o (reserved) }
    Linker:     TTool;   { both backends: link final binary }
  end;

  { One external tool a backend declares it needs (TBackendDriver.DescribeTools).
    Cands lists candidate basenames in preference order (e.g. 'llc-18','llc'),
    '' terminates the list.  Resolution order in ResolveSpec, per candidate:
      1. EnvVar override (verbatim, FileExists)            — once, before Cands
      2. $BLAISE_TOOLCHAIN_PREFIX + candidate              (+ host ext)
      3. CrossPrefix + candidate on $PATH, when cross-compiling
      4. bare candidate on $PATH                           (+ host ext)
      5. fallback to the first candidate (clean exec-time error)
    The host extension ('.exe' on a Windows host) is appended at every probe.

    HostTool distinguishes the two natures the cross case needs:
      * True  — the tool runs on the host and targets via flags (llc with
                -mtriple); a bare $PATH match is fine even when cross.
      * False — the tool must be the *target's* own binary (the linker); on a
                cross build the bare host fallback (step 4) is suppressed so we
                don't link Windows output with the host cc. }
  TToolSpec = record
    Name:        string;            { 'linker' | 'llc' | 'qbe' | 'as' }
    EnvVar:      string;            { per-tool override, e.g. 'BLAISE_LLC' }
    Cands:       array of string;   { ordered candidate basenames }
    CrossPrefix: string;            { triple prefix, 'x86_64-w64-mingw32-' }
    HostTool:    Boolean;           { see above }
  end;

  TToolSpecArray = array of TToolSpec;

{ One-shot resolver — call once per native/QBE compile, read the resulting
  record for every subprocess + library path. }
function ResolveToolchain(const ATarget: TTargetDesc): TToolchain;

{ Per-tool resolvers — exported for diagnostics + selective use. }
function ResolveQBE: TTool;
function ResolveAssembler: TTool;
function ResolveLinker(const ATarget: TTargetDesc): TTool;

{ Directory containing the running compiler binary (ParamStr(0)). }
function CompilerBinDir: string;

{ RTL source directory (compiler/src/main/pascal), relative to the binary.
  The driver builds the RTL objects from here when linking; overridable via
  $BLAISE_RTL_SRC. }
function RTLSourceDir: string;

{ Walks $PATH for the first file named ABaseName that exists.  Returns the
  absolute path on hit, '' on miss.  On Windows hosts also tries '.exe'. }
function WhichInPath(const ABaseName: string): string;

{ Host executable-file extension ('.exe' on a Windows host, else '').
  Derived from blaise.codegen.target.HostTarget. }
function HostExeExt: string;

{ Resolve one tool spec against the active target (see TToolSpec). }
function ResolveSpec(const ASpec: TToolSpec; const ATarget: TTargetDesc): string;

implementation

uses
  SysUtils;

{ Host path conventions.  The Blaise compiler currently runs only on POSIX
  hosts (linux/freebsd/macos), so the host directory delimiter is '/' and the
  PATH list separator is ':'.  These describe the HOST the compiler runs on,
  not the --target it generates code for (cross-compilation does not change how
  we probe the local $PATH).  When a Windows host build lands, switch these to
  query the active platform RTL. }

{ ------------------------------------------------------------------ }
{ PATH walker                                                          }
{ ------------------------------------------------------------------ }

function HostExeExt: string;
begin
  Result := ExecutableExtension(HostTarget());
end;

function PathSep: string;
begin
  Result := PathSeparator;  { ':' on POSIX, ';' on a Windows host }
end;

function TrySingleName(const ADir, ABaseName: string): string;
var
  Candidate, Ext: string;
begin
  Candidate := IncludeTrailingPathDelimiter(ADir) + ABaseName;
  if FileExists(Candidate) then
  begin
    Exit(Candidate);
  end;
  { On a Windows host, retry with the executable extension — unless the
    basename already carries it.  Blaise Pos: -1 = not found. }
  Ext := HostExeExt();
  if (Ext <> '') and (Pos(LowerCase(Ext), LowerCase(ABaseName)) < 0) then
  begin
    Candidate := IncludeTrailingPathDelimiter(ADir) + ABaseName + Ext;
    if FileExists(Candidate) then
    begin
      Exit(Candidate);
    end;
  end;
  Result := '';
end;

{ FileExists(APath), then FileExists(APath+AExt) when AExt is non-empty. }
function TryPathWithExt(const APath, AExt: string): string;
begin
  if FileExists(APath) then Exit(APath);
  if (AExt <> '') and FileExists(APath + AExt) then Exit(APath + AExt);
  Result := '';
end;

function WhichInPath(const ABaseName: string): string;
var
  Path, Entry: string;
  SepPos:      Integer;
  Hit:         string;
begin
  Result := '';
  if ABaseName = '' then Exit;
  Path := GetEnvironmentVariable('PATH');
  while Length(Path) > 0 do
  begin
    { Blaise Pos/Copy are 0-based; -1 = not found.  Consume one PATH entry
      per iteration. }
    SepPos := Pos(PathSep(), Path);
    if SepPos >= 0 then
    begin
      Entry := Copy(Path, 0, SepPos);
      Path  := Copy(Path, SepPos + 1, MaxInt);
    end
    else
    begin
      Entry := Path;
      Path  := '';
    end;
    if Entry = '' then Continue;
    Hit := TrySingleName(Entry, ABaseName);
    if Hit <> '' then
    begin
      Exit(Hit);
    end;
  end;
end;

{ ------------------------------------------------------------------ }
{ Generic resolver                                                     }
{ ------------------------------------------------------------------ }

{ Resolve one candidate string.  If it contains a path separator, treat it as
  a path and FileExists-check directly; otherwise PATH-walk for the basename. }
function TryCandidate(const ACand: string): string;
begin
  Result := '';
  if ACand = '' then Exit;
  if (Pos('/', ACand) >= 0) or (Pos('\', ACand) >= 0) then
  begin
    if FileExists(ACand) then Result := ACand;
  end
  else
    Result := WhichInPath(ACand);
end;

{ Two-stage probe — env override, then candidate-walk (each candidate may be a
  bare basename -> PATH-search or a path -> FileExists), then bare-name
  fallback so RunProcess surfaces a clean error at invoke time. }
function ResolveToolPath(const AEnvVar, ACandA, ACandB: string): string;
var
  EnvPath, Hit: string;
begin
  Result := '';
  if AEnvVar <> '' then
  begin
    EnvPath := GetEnvironmentVariable(AEnvVar);
    if (EnvPath <> '') and FileExists(EnvPath) then
    begin
      Exit(EnvPath);
    end;
  end;
  Hit := TryCandidate(ACandA);
  if Hit <> '' then begin Result := Hit; Exit end;
  Hit := TryCandidate(ACandB);
  if Hit <> '' then begin Result := Hit; Exit end;
  if ACandA <> '' then
    Result := ACandA
  else
    Result := ACandB;
end;

{ Spec-driven resolver — the path a backend's DescribeTools spec takes.
  See TToolSpec for the order.  HostExeExt is appended at every probe. }
function ResolveSpec(const ASpec: TToolSpec; const ATarget: TTargetDesc): string;
var
  Ext, EnvP, Pref, Hit: string;
  Cross: Boolean;
  I: Integer;
begin
  Ext   := HostExeExt();
  Cross := HostTarget().OS <> ATarget.OS;

  { 1. explicit per-tool override — verbatim, wins over everything. }
  if ASpec.EnvVar <> '' then
  begin
    EnvP := GetEnvironmentVariable(ASpec.EnvVar);
    if (EnvP <> '') and FileExists(EnvP) then Exit(EnvP);
  end;

  Pref := GetEnvironmentVariable('BLAISE_TOOLCHAIN_PREFIX');

  { 2. $BLAISE_TOOLCHAIN_PREFIX + each candidate. }
  if Pref <> '' then
    for I := 0 to High(ASpec.Cands) do
    begin
      Hit := TryPathWithExt(Pref + ASpec.Cands[I], Ext);
      if Hit <> '' then Exit(Hit);
    end;

  { 3. derived cross-triple prefix on $PATH (cross builds only). }
  if Cross and (ASpec.CrossPrefix <> '') then
    for I := 0 to High(ASpec.Cands) do
    begin
      Hit := WhichInPath(ASpec.CrossPrefix + ASpec.Cands[I]);
      if Hit <> '' then Exit(Hit);
    end;

  { 4. bare candidate on $PATH.  Host tools (llc) always; target tools
       (the linker) only on a native build — never fall back to the host
       linker for a cross target. }
  if ASpec.HostTool or (not Cross) then
    for I := 0 to High(ASpec.Cands) do
    begin
      Hit := WhichInPath(ASpec.Cands[I]);
      if Hit <> '' then Exit(Hit);
    end;

  { 5. fallback — name the cross tool when we have a prefix so the exec-time
       "not found" error is actionable. }
  if Cross and (ASpec.CrossPrefix <> '') then
    Result := ASpec.CrossPrefix + ASpec.Cands[0]
  else
    Result := ASpec.Cands[0];
end;

{ ------------------------------------------------------------------ }
{ Per-tool resolvers                                                   }
{ ------------------------------------------------------------------ }

function ResolveQBE: TTool;
begin
  Result.Path := ResolveToolPath('BLAISE_QBE', 'qbe', '');
  Result.Kind := tkQBE;
end;

function ResolveAssembler: TTool;
begin
  Result.Path := ResolveToolPath('BLAISE_AS', 'as', '');
  Result.Kind := tkGnuAs;
end;

function ResolveLinker(const ATarget: TTargetDesc): TTool;
begin
  Result.Path := ResolveToolPath('BLAISE_LINKER', 'cc', '');
  Result.Kind := tkCCDriver;
end;

{ ------------------------------------------------------------------ }
{ Install-relative paths                                               }
{ ------------------------------------------------------------------ }

function CompilerBinDir: string;
begin
  Result := ExtractFilePath(ParamStr(0));
end;

function RTLDirHasUnits(const ADir: string): Boolean;
begin
  Result := (ADir <> '') and
    FileExists(IncludeTrailingPathDelimiter(ADir) + 'runtime.arc.pas');
end;

function RTLSourceDir: string;
var
  Cand, Up: string;
  I: Integer;
begin
  { The RTL units (runtime.*, rtl.platform.*) live in the compiler's own source
    tree.  Resolve the directory robustly across the ways the compiler is run:

      1. binary-relative: <bindir>/../src/main/pascal — the in-tree
         compiler/target/blaise.
      2. binary-ANCESTOR-relative: <bindir>/..^N/compiler/src/main/pascal —
         a binary living elsewhere in the repo, e.g. releases/v0.14.0-pre/
         (two levels up from the binary is the repo root).
      3. CWD-relative: compiler/src/main/pascal then src/main/pascal — the
         binary may be copied elsewhere (e.g. /tmp during a fixpoint) but
         invoked from the project root by the build.
      4. CWD-ANCESTOR-relative: ..^N/compiler/src/main/pascal — the build
         tool runs module compiles from the MODULE directory (PasBuild's
         stdlib compile has CWD stdlib/), so walk up a few levels looking
         for the compiler tree.  This is what made
         `pasbuild test -m blaise-stdlib --compiler releases/v*-pre/blaise`
         fail while the same command with compiler/target/blaise worked:
         neither the releases/ binary nor the stdlib/ CWD resolved under
         rules 1 and 3 alone.

    Every candidate is validated by content (runtime.arc.pas present), so a
    wrong guess can never be returned.  The driver consults $BLAISE_RTL_SRC
    before calling this, for a fully relocated binary (release) that ships
    its RTL source elsewhere. }
  Cand := IncludeTrailingPathDelimiter(CompilerBinDir()) + '../src/main/pascal';
  if RTLDirHasUnits(ExpandFileName(Cand)) then Exit(ExpandFileName(Cand));

  Up := '';
  for I := 1 to 4 do
  begin
    Up := Up + '../';
    Cand := IncludeTrailingPathDelimiter(CompilerBinDir()) + Up
      + 'compiler/src/main/pascal';
    if RTLDirHasUnits(ExpandFileName(Cand)) then Exit(ExpandFileName(Cand));
  end;

  Cand := 'compiler/src/main/pascal';
  if RTLDirHasUnits(ExpandFileName(Cand)) then Exit(ExpandFileName(Cand));

  Cand := 'src/main/pascal';
  if RTLDirHasUnits(ExpandFileName(Cand)) then Exit(ExpandFileName(Cand));

  Up := '';
  for I := 1 to 4 do
  begin
    Up := Up + '../';
    Cand := Up + 'compiler/src/main/pascal';
    if RTLDirHasUnits(ExpandFileName(Cand)) then Exit(ExpandFileName(Cand));
  end;

  { Fall back to the binary-relative path so callers get a meaningful "not
    found" message naming a concrete location. }
  Result := ExpandFileName(IncludeTrailingPathDelimiter(CompilerBinDir())
    + '../src/main/pascal');
end;

{ ------------------------------------------------------------------ }
{ Top-level resolver                                                   }
{ ------------------------------------------------------------------ }

function ResolveToolchain(const ATarget: TTargetDesc): TToolchain;
begin
  Result.QBE       := ResolveQBE();
  Result.Assembler := ResolveAssembler();
  Result.Linker    := ResolveLinker(ATarget);
end;

end.
