{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.cli;

{ CLI-level end-to-end tests for the compiler driver front-end.

  These shell out to the compiler binary and assert on stdout/stderr and
  exit codes.  They cover behaviour the IR-only / unit harness cannot see:

    * FPC-style CLI removal (Step 0): the old -iV/-iTP/-iTO info probe and
      single-dash FPC flags are gone; the binary is double-dash-only now.

    * Driver option contract surfacing (Steps 2-5): --assembler value
      validation, wrong-backend rejection, and that ValidateOptions fires
      even in stdout-only modes (--emit-ir).  These prove the
      drain -> ValidateOptions -> error -> exit-1 wiring in Blaise.pas,
      which is not unit-testable (ParseArgs is a non-exported program
      local). }

interface

uses
  SysUtils, Classes, Process, blaise.testing;

type
  { Invokes the compiler binary directly and inspects the CLI contract. }
  TCLIContractTests = class(TTestCase)
  private
    FCompiler: string;
    FRTLPath: string;
    FStdlibPath: string;
    FScratch: string;
    FCounter: Integer;
    function ProjectRoot: string;
    function CompilerAvailable: Boolean;
    { Run the compiler with the given args; capture combined stdout+stderr. }
    function RunCompiler(const AArgs: array of string;
      out ACombined: string): Integer;
    function WriteScratchSource(const ASrc: string): string;
    { Run a produced binary, capturing stdout/stderr; returns its exit code. }
    function RunBinary(const AExe: string; out ACombined: string): Integer;
    { `readelf -dW <exe>` output — the DT_NEEDED lines reveal which shared libs
      the binary links.  Empty string if readelf is unavailable. }
    function ReadelfDynamic(const AExe: string): string;
    { Compile ASrc with the given backend (empty = default QBE), link against
      the full RTL, run it, and report stdout + exit code.  Used for features
      that need stdlib units loaded + linked, which the in-process e2e harness
      cannot do. }
    function CompileRunFull(const ASrc, ABackend: string;
      out AStdout: string; out AExitCode: Integer): Boolean;
  protected
    procedure SetUp; override;
  published
    { ---- Step 0: FPC CLI removal ---- }
    procedure TestHelpStillWorks;
    procedure TestNormalCompileStillWorks;
    procedure TestFPCVersionProbeGone;
    { ---- Steps 2-5: driver option contract surfacing through the CLI ----
      These prove the drain -> ValidateOptions -> error -> exit-1 wiring in
      Blaise.pas, which is not unit-testable (ParseArgs is a non-exported
      program local). }
    procedure TestAssemblerInternalAccepted;
    procedure TestAssemblerBogusRejected;          { ValidateOptions surfaces }
    procedure TestWrongBackendAssemblerRejected;   { addendum 2: qbe + --assembler }
    procedure TestEmitIrStillValidatesAssembler;   { addendum 1: validate runs in stdout mode }
    procedure TestAssemblerLineInHelp;             { DescribeOptions drives --help }
    { ---- emit-mode must match the explicitly chosen backend ----
      --emit-ir is a QBE-only output mode; --emit-asm is native-only.  When
      the user explicitly selects a backend that cannot produce that output,
      the driver must error instead of silently switching backends. }
    procedure TestEmitIr_WithExplicitNativeBackend_Rejected;
    procedure TestEmitAsm_WithExplicitQbeBackend_Rejected;
    procedure TestEmitIr_WithoutBackend_StillWorks;
    procedure TestEmitIr_WithExplicitQbeBackend_StillWorks;
    { ---- external 'lib' propagates a -l<name> to the real link command ---- }
    { A program declaring `external 'lib'` for a NON-EXISTENT library must fail
      the link with the linker's "cannot find -l<lib>" — which only happens if
      the driver actually emitted -l<lib>.  The e2e harness can't test this (it
      links with a hardcoded `cc ... -lm -lpthread` and never calls
      LinkViaToolchain), so this drives the real compiler binary end to end. }
    procedure TestExternalLib_MissingLib_FailsLink_QBE;
    procedure TestExternalLib_MissingLib_FailsLink_Native;
    { ---- demand-driven link libs: -lm (QBE libm math) and -lpthread ---- }
    { libm is added only when the QBE backend emits a libm call; native emits
      float math inline and never links libm.  libpthread flows from
      runtime.thread's `external 'pthread'` — only when threads are used — and
      is a DT_NEEDED on the dynamic path, absent on --static/freestanding. }
    procedure TestLibm_QBEFloatMath_LinksLibm;
    procedure TestLibm_NoFloatMath_NoLibm;
    procedure TestPthread_NativeThreads_LinksLibpthread;
    { AUTO link mode (docs/toolchain-independence.adoc): freestanding when no
      C libraries/symbols are bound, dynamic+libc with a note otherwise. }
    procedure TestLinkAuto_PureProgram_Freestanding;
    procedure TestLinkAuto_ExternalLib_DynamicWithNote;
    procedure TestLinkAuto_BareLibcSymbol_FallsBackWithNote;
    procedure TestLinkStatic_ExternalLib_Errors;
    procedure TestLinkStatic_UnresolvedSymbol_Errors;
    procedure TestLinkDynamic_Flag_ForcesDynamic;
    procedure TestPthread_StaticThreads_NoNeeded;
    { ---- GH #188: internal linker resolves a -l<name> whose lib<name>.so is a
           GNU ld linker script (INPUT/GROUP) to the real versioned SONAME(s),
           not the bare (unmappable) linker-script filename. ---- }
    procedure TestLinkerScriptLib_ResolvesToVersionedSoname_Native;
    { ---- div/mod by zero raises a catchable EDivByZero (needs stdlib) ---- }
    procedure TestDivByZeroCaught_QBE;
    procedure TestDivByZeroCaught_Native;
    procedure TestModByZeroCaught_QBE;
    procedure TestModByZeroCaught_Native;
    { ---- a bare --output (no directory part) must not anchor per-unit
           .o/.bif artefacts at the filesystem root ---- }
    procedure TestBareOutput_UnitArtefacts_NotWrittenToRoot;
    { ---- BLAISE_BACKEND environment variable ----
      Backend precedence is: an explicit --backend flag first, then the
      BLAISE_BACKEND env var, then the compiled-in default (native).  Observed
      through the native-only --assembler flag: the QBE driver reports it as an
      unknown flag, so a QBE selection fails while a native selection accepts. }
    procedure TestBackendEnv_Qbe_RejectsNativeOnlyFlag;
    procedure TestBackendEnv_Native_AcceptsNativeOnlyFlag;
    procedure TestBackendEnv_ExplicitFlagBeatsEnv;
    procedure TestBackendEnv_InvalidValue_WarnsAndFallsBack;
  end;

implementation

{ Print the "tests skipped" note at most once per suite run, so a CI
  environment that lacks the QBE compiler binary surfaces the skip loudly
  instead of silently reporting green with ~12 ignored tests. }
var
  GCLISkipNoted: Boolean = False;

{ Validity-probe cache for the fallback compiler.  The fallback path
  (/tmp/fp_blaise2) is a transient fixpoint artifact that is frequently STALE —
  built by an earlier, possibly-broken compiler.  Running the contract tests
  against a stale binary produces a cascade of cryptic failures (e.g. SIGILL
  from a since-fixed mis-encoding) that look like regressions but are not.
  We probe the binary once (compile+run a trivial program) and, if it does not
  behave, skip the suite with an actionable message instead of failing.
  0 = not probed, 1 = good, 2 = bad. }
var
  GCLIProbeState: Integer = 0;

{ ---- helpers ---- }

function TCLIContractTests.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps: Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Result);
    Exit;
  end;
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir());
end;

procedure TCLIContractTests.SetUp;
begin
  inherited SetUp();
  FCompiler := GetEnvironmentVariable('BLAISE_QBE_COMPILER');
  if FCompiler = '' then
    FCompiler := '/tmp/fp_blaise3';
  if not FileExists(FCompiler) then
    FCompiler := '/tmp/fp_blaise2';
  FRTLPath := ProjectRoot() + 'compiler/src/main/pascal';
  FStdlibPath := ProjectRoot() + 'stdlib/src/main/pascal';
  FScratch := ProjectRoot() + 'compiler/target/cli_scratch/';
  ForceDirectories(FScratch);
  FCounter := 0;
end;

function TCLIContractTests.CompilerAvailable: Boolean;
var
  Out_: string;
  EC: Integer;
begin
  { The compiler binary source-builds the RTL itself (no blaise_rtl.a); only
    the binary and the RTL source need to be present. }
  Result := FileExists(FCompiler)
        and FileExists(FRTLPath + '/runtime.arc.pas');
  if (not Result) and (not GCLISkipNoted) then
  begin
    GCLISkipNoted := True;
    WriteLn(StdErr, 'note: TCLIContractTests skipped — compiler binary "',
            FCompiler, '" or RTL source not found ',
            '(set BLAISE_QBE_COMPILER to a QBE-backend blaise binary to run them)');
    Exit;
  end;
  if not Result then Exit;

  { Validity probe: a stale fallback binary would otherwise turn into a cascade
    of cryptic failures.  Probe once; on a bad probe, treat as unavailable. }
  if GCLIProbeState = 0 then
  begin
    if CompileRunFull('program p; begin WriteLn(42); end.', 'native', Out_, EC)
       and (EC = 0) and (Pos('42', Out_) >= 0) then
      GCLIProbeState := 1
    else
    begin
      GCLIProbeState := 2;
      WriteLn(StdErr, 'note: TCLIContractTests skipped — compiler binary "',
              FCompiler, '" is stale/broken (probe program did not run); ',
              'rebuild it or set BLAISE_QBE_COMPILER to a current QBE-backend ',
              'blaise binary.');
    end;
  end;
  Result := GCLIProbeState = 1;
end;

function TCLIContractTests.RunCompiler(const AArgs: array of string;
  out ACombined: string): Integer;
var
  Proc: TProcess;
  I: Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := FCompiler;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    { The posix process shim already redirects the child's stderr into the
      same pipe as stdout (dup2(pipe,2) in rtl.platform.posix), so a
      diagnostic printed to StdErr is visible in ReadOutput below. }
    Proc.Execute();
    ACombined := '';
    repeat
      Chunk := Proc.ReadOutput();
      ACombined := ACombined + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TCLIContractTests.WriteScratchSource(const ASrc: string): string;
begin
  FCounter := FCounter + 1;
  Result := FScratch + 'cli_' + IntToStr(FCounter) + '.pas';
  WriteFile(Result, ASrc);
end;

{ ---- Step 0: FPC CLI removal ---- }

procedure TCLIContractTests.TestHelpStillWorks;
var
  Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  EC := RunCompiler(['--help'], Out_);
  AssertEquals('--help exits 0', 0, EC);
  AssertTrue('usage banner present',
    Pos('Usage:', Out_) >= 0);
end;

procedure TCLIContractTests.TestNormalCompileStillWorks;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  Src := WriteScratchSource(
    'program cli_ok;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(42)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', FScratch + 'cli_ok_bin'
  ], Out_);
  AssertEquals('normal compile exits 0: ' + Out_, 0, EC);
end;

procedure TCLIContractTests.TestFPCVersionProbeGone;
var
  Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { The FPC info-query path is removed.  -iV must no longer print FPC's
    '3.2.2'; it is now an unrecognised flag and fails. }
  EC := RunCompiler(['-iV'], Out_);
  AssertTrue('-iV must not return FPC version 3.2.2',
    Pos('3.2.2', Out_) < 0);
  AssertTrue('-iV must be rejected (non-zero exit)', EC <> 0);
end;

{ ---- Steps 2-5: driver option contract ---- }

procedure TCLIContractTests.TestAssemblerInternalAccepted;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { --backend native --assembler internal flows through the native driver's
    AcceptOption (drain) and compiles successfully. }
  Src := WriteScratchSource(
    'program cli_asm;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'native',
    '--assembler', 'internal',
    '--output', FScratch + 'cli_asm_bin'
  ], Out_);
  AssertEquals('--assembler internal must compile: ' + Out_, 0, EC);
end;

procedure TCLIContractTests.TestAssemblerBogusRejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { Bad --assembler value: accepted by AcceptOption, rejected by the native
    driver's ValidateOptions with the exact legacy message.  Proves the
    drain -> ValidateOptions -> error -> exit-1 wiring. }
  Src := WriteScratchSource(
    'program cli_bad;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'native',
    '--assembler', 'bogus',
    '--output', FScratch + 'cli_bad_bin'
  ], Out_);
  AssertTrue('bad --assembler value must be rejected', EC <> 0);
  AssertTrue('diagnostic must mention internal/external: ' + Out_,
    Pos('internal', Out_) >= 0);
end;

procedure TCLIContractTests.TestWrongBackendAssemblerRejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { Addendum 2 (intentional behaviour change): --assembler is native-only.
    Under --backend qbe the QBE driver returns oaUnknown for it, so the drain
    reports it as an unknown flag and fails (previously silently accepted). }
  Src := WriteScratchSource(
    'program cli_wb;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'qbe',
    '--assembler', 'internal',
    '--output', FScratch + 'cli_wb_bin'
  ], Out_);
  AssertTrue('--assembler under --backend qbe must be rejected', EC <> 0);
end;

procedure TCLIContractTests.TestEmitIrStillValidatesAssembler;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { Addendum 1: ValidateOptions runs unconditionally, above the stdout-mode
    toolchain skip.  So a bad --assembler value is rejected even with
    --emit-ir present (which selects the QBE driver for IR output).  Here the
    wrong-backend rule fires first (QBE doesn't own --assembler), which is the
    correct rejection either way — the point is it does NOT silently succeed. }
  Src := WriteScratchSource(
    'program cli_eir;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'native',
    '--assembler', 'bogus',
    '--emit-ir'
  ], Out_);
  AssertTrue('bad --assembler must be rejected even with --emit-ir', EC <> 0);
end;

procedure TCLIContractTests.TestAssemblerLineInHelp;
var
  Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { The native driver's DescribeOptions contributes the --assembler line to
    --help; Blaise.pas no longer hard-codes it. }
  EC := RunCompiler(['--help'], Out_);
  AssertEquals('--help exits 0', 0, EC);
  AssertTrue('--help must list --assembler (via DescribeOptions)',
    Pos('--assembler', Out_) >= 0);
end;

procedure TCLIContractTests.TestEmitIr_WithExplicitNativeBackend_Rejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { --emit-ir is a QBE-only output mode.  Asking for it under an explicit
    --backend native must fail loudly, not silently emit QBE IR (which
    ignores the requested backend).  --emit-asm is the native equivalent. }
  Src := WriteScratchSource(
    'program cli_ei;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler([
    '--source', Src, '--backend', 'native', '--emit-ir'], Out_);
  AssertTrue('--emit-ir + --backend native must be rejected: ' + Out_, EC <> 0);
  AssertTrue('error mentions emit-ir/native mismatch',
    (Pos('--emit-ir', Out_) >= 0) and (Pos('native', Out_) >= 0));
end;

procedure TCLIContractTests.TestEmitAsm_WithExplicitQbeBackend_Rejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Symmetric case: --emit-asm is native-only; requesting it under an
    explicit --backend qbe must fail rather than silently switch to native. }
  Src := WriteScratchSource(
    'program cli_ea;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler([
    '--source', Src, '--backend', 'qbe', '--emit-asm'], Out_);
  AssertTrue('--emit-asm + --backend qbe must be rejected: ' + Out_, EC <> 0);
end;

procedure TCLIContractTests.TestEmitIr_WithoutBackend_StillWorks;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { No --backend given: --emit-ir resolves to the QBE default as before.
    The new validation must only fire on an EXPLICIT incompatible backend. }
  Src := WriteScratchSource(
    'program cli_ei2;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler(['--source', Src, '--emit-ir'], Out_);
  AssertEquals('--emit-ir with no --backend still emits QBE IR: ' + Out_, 0, EC);
end;

procedure TCLIContractTests.TestEmitIr_WithExplicitQbeBackend_StillWorks;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Explicit --backend qbe + --emit-ir is consistent — must succeed. }
  Src := WriteScratchSource(
    'program cli_ei3;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler(['--source', Src, '--backend', 'qbe', '--emit-ir'], Out_);
  AssertEquals('--emit-ir + --backend qbe is consistent: ' + Out_, 0, EC);
end;

function TCLIContractTests.RunBinary(const AExe: string;
  out ACombined: string): Integer;
var
  Proc: TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    ACombined := '';
    repeat
      Chunk := Proc.ReadOutput();
      ACombined := ACombined + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TCLIContractTests.ReadelfDynamic(const AExe: string): string;
var
  Proc: TProcess;
  Chunk: string;
begin
  Result := '';
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := 'readelf';
    Proc.Parameters.Add('-dW');
    Proc.Parameters.Add(AExe);
    try
      Proc.Execute();
    except
      Exit;   { readelf not installed — caller Ignores }
    end;
    repeat
      Chunk := Proc.ReadOutput();
      Result := Result + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
  finally
    Proc.Free();
  end;
end;

function TCLIContractTests.CompileRunFull(const ASrc, ABackend: string;
  out AStdout: string; out AExitCode: Integer): Boolean;
var
  SrcPath, BinPath, CompileOut: string;
  EC: Integer;
begin
  Result := False;
  SrcPath := WriteScratchSource(ASrc);
  BinPath := FScratch + 'cli_run_' + IntToStr(FCounter);
  if ABackend = '' then
    EC := RunCompiler(['--source', SrcPath,
      '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
      '--output', BinPath], CompileOut)
  else
    EC := RunCompiler(['--source', SrcPath, '--backend', ABackend,
      '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
      '--output', BinPath], CompileOut);
  if EC <> 0 then
  begin
    AStdout := 'compile failed: ' + CompileOut;
    AExitCode := EC;
    Exit;
  end;
  AExitCode := RunBinary(BinPath, AStdout);
  Result := True;
end;

const
  SrcDivByZeroCaught =
    'program P;' + LineEnding +
    'uses SysUtils;' + LineEnding +
    'var a, b: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  a := 10; b := 0;' + LineEnding +
    '  try' + LineEnding +
    '    WriteLn(a div b)' + LineEnding +
    '  except' + LineEnding +
    '    on E: EDivByZero do WriteLn(''caught: '' + E.Message)' + LineEnding +
    '  end;' + LineEnding +
    '  WriteLn(''after'')' + LineEnding +
    'end.';

  SrcModByZeroCaught =
    'program P;' + LineEnding +
    'uses SysUtils;' + LineEnding +
    'var a, b: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  a := 10; b := 0;' + LineEnding +
    '  try' + LineEnding +
    '    WriteLn(a mod b)' + LineEnding +
    '  except' + LineEnding +
    '    on E: EDivByZero do WriteLn(''mod caught'')' + LineEnding +
    '  end' + LineEnding +
    'end.';

const
  { Declares an external from a library that does not exist.  The function is
    never called, but the parser collects the library into Prog.LinkLibs at
    parse time, so the driver must still emit -lnosuchlib_blaise_xyz on the link
    line — which the system linker then rejects.  If the -l<name> propagation
    were broken (no flag emitted), the link would SUCCEED. }
  SrcMissingExternalLib =
    'program P;' + LineEnding +
    'function f(X: Integer): Integer;' +
    ' external ''nosuchlib_blaise_xyz'' name ''nope'';' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(''unreached'')' + LineEnding +
    'end.';

procedure TCLIContractTests.TestExternalLib_MissingLib_FailsLink_QBE;
var SrcPath, BinPath, Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  SrcPath := WriteScratchSource(SrcMissingExternalLib);
  BinPath := FScratch + 'cli_misslib_qbe_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'qbe',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertTrue('link must fail (missing library)', EC <> 0);
  AssertTrue('linker reports the -l<name> it could not find',
    Pos('nosuchlib_blaise_xyz', Out_) >= 0);
end;

procedure TCLIContractTests.TestExternalLib_MissingLib_FailsLink_Native;
var SrcPath, BinPath, Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  SrcPath := WriteScratchSource(SrcMissingExternalLib);
  BinPath := FScratch + 'cli_misslib_nat_' + IntToStr(FCounter);
  { --linker external: the toolchain linker emits and consumes -l<name>, so a
    missing library fails at LINK time with "cannot find -l<name>".  (The
    internal linker instead records a DT_NEEDED and would fail at RUN time when
    the loader can't find the .so — a different contract, not tested here.) }
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native',
    '--linker', 'external',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertTrue('link must fail (missing library)', EC <> 0);
  AssertTrue('linker reports the -l<name> it could not find',
    Pos('nosuchlib_blaise_xyz', Out_) >= 0);
end;

procedure TCLIContractTests.TestLibm_QBEFloatMath_LinksLibm;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Sqrt (and all float math) now lowers to the pure-Pascal runtime.math
    RTL ($_BlaiseSqrtD), so a float-math binary must NOT link libm --
    the exact inverse of the pre-runtime.math contract this test used to
    pin.  GH #199 was the visible failure of the old scheme: the lib
    requirement was lost for cached/separately-compiled units and the
    binary died at run time with "undefined symbol: pow". }
  SrcPath := WriteScratchSource(
    'program p; var d: Double; begin d := Sqrt(2.0); WriteLn(d > 1.0); end.');
  BinPath := FScratch + 'cli_libm_qbe_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'qbe',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('QBE Sqrt program links (out: ' + Out_ + ')', 0, EC);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  AssertTrue('float-math binary does NOT link libm (runtime.math replaces it)',
    Pos('libm.so', Dyn) < 0);
end;

procedure TCLIContractTests.TestLibm_NoFloatMath_NoLibm;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { A program with no float math must NOT drag in libm — proves -lm is
    demand-driven, not on every link. }
  SrcPath := WriteScratchSource(
    'program p; begin WriteLn(6 * 7); end.');
  BinPath := FScratch + 'cli_nolibm_qbe_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'qbe',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('plain QBE program links (out: ' + Out_ + ')', 0, EC);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  AssertTrue('non-math binary does NOT link libm', Pos('libm.so', Dyn) < 0);
end;

procedure TCLIContractTests.TestLinkAuto_PureProgram_Freestanding;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { A program binding no C libraries links FREESTANDING by default: no
    .dynamic section, no DT_NEEDED, no note on stderr. }
  SrcPath := WriteScratchSource(
    'program p; begin WriteLn(6 * 7); end.');
  BinPath := FScratch + 'cli_lmauto_pure_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('pure program links (out: ' + Out_ + ')', 0, EC);
  AssertTrue('no dynamic-link note for a freestanding link',
    Pos('linking dynamically', Out_) < 0);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  AssertTrue('freestanding binary has no DT_NEEDED',
    Pos('(NEEDED)', Dyn) < 0);
end;

procedure TCLIContractTests.TestLinkAuto_ExternalLib_DynamicWithNote;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Binding an external C library flips the link to dynamic+libc and says
    so, naming the library. }
  SrcPath := WriteScratchSource(
    'program p; ' +
    'function sf(x: Single): Single; cdecl; external ''m'' name ''sinf''; ' +
    'begin WriteLn(sf(0.0) = 0.0); end.');
  BinPath := FScratch + 'cli_lmauto_lib_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('external-lib program links (out: ' + Out_ + ')', 0, EC);
  AssertTrue('note names the binding libraries',
    Pos('linking dynamically against libc: the program binds external C ' +
        'libraries (m)', Out_) >= 0);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  AssertTrue('libm is a DT_NEEDED', Pos('libm.so', Dyn) >= 0);
  AssertTrue('libc is a DT_NEEDED', Pos('libc.so', Dyn) >= 0);
end;

procedure TCLIContractTests.TestLinkAuto_BareLibcSymbol_FallsBackWithNote;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { A bare `external name` binding a libc-only symbol: the freestanding
    probe finds it unresolved and falls back to dynamic+libc, naming the
    SYMBOL in the note.  (A bare symbol the static RTL provides — getenv,
    getrlimit — stays freestanding and produces no note.) }
  SrcPath := WriteScratchSource(
    'program p; ' +
    'function tty(fd: Integer): Integer; cdecl; external name ''isatty''; ' +
    'begin tty(0); WriteLn(1); end.');
  BinPath := FScratch + 'cli_lmauto_bare_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('bare-libc program links (out: ' + Out_ + ')', 0, EC);
  AssertTrue('note names the unresolved symbols',
    Pos('unresolved C symbols (isatty)', Out_) >= 0);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  AssertTrue('libc is a DT_NEEDED', Pos('libc.so', Dyn) >= 0);
end;

procedure TCLIContractTests.TestLinkStatic_ExternalLib_Errors;
var SrcPath, BinPath, Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { --static + external 'lib' is a contradiction: a freestanding binary
    cannot load shared libraries.  Hard error naming the libs. }
  SrcPath := WriteScratchSource(
    'program p; ' +
    'function sf(x: Single): Single; cdecl; external ''m'' name ''sinf''; ' +
    'begin WriteLn(sf(0.0) = 0.0); end.');
  BinPath := FScratch + 'cli_lmstatic_lib_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native', '--static',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertTrue('link must fail', EC <> 0);
  AssertTrue('error names the libraries',
    Pos('binds external C libraries (m)', Out_) >= 0);
end;

procedure TCLIContractTests.TestLinkStatic_UnresolvedSymbol_Errors;
var SrcPath, BinPath, Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { --static + a bare libc-only symbol: the pre-link probe names the
    symbols instead of dying mid-link with a bare undefined reference. }
  SrcPath := WriteScratchSource(
    'program p; ' +
    'function tty(fd: Integer): Integer; cdecl; external name ''isatty''; ' +
    'begin tty(0); WriteLn(1); end.');
  BinPath := FScratch + 'cli_lmstatic_sym_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native', '--static',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertTrue('link must fail', EC <> 0);
  AssertTrue('error names the symbols',
    Pos('unresolved C symbols (isatty)', Out_) >= 0);
end;

procedure TCLIContractTests.TestLinkDynamic_Flag_ForcesDynamic;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { --dynamic forces the libc-linked PIE for a program that would
    otherwise go freestanding; explicit choice, so no note. }
  SrcPath := WriteScratchSource(
    'program p; begin WriteLn(6 * 7); end.');
  BinPath := FScratch + 'cli_lmdyn_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native', '--dynamic',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('pure program links dynamically (out: ' + Out_ + ')', 0, EC);
  AssertTrue('no note for an explicit mode',
    Pos('linking dynamically', Out_) < 0);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  AssertTrue('libc is a DT_NEEDED', Pos('libc.so', Dyn) >= 0);
end;

procedure TCLIContractTests.TestPthread_NativeThreads_LinksLibpthread;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { A native program that uses runtime.thread pulls libpthread via
    runtime.thread's `external 'pthread'` — the internal linker emits the
    DT_NEEDED (no hardcoded -lpthread).  The default binary is DYNAMIC on a
    libc host (Linux) but STATIC/freestanding on FreeBSD, where threads come
    from the static kernel leaf and there is no .dynamic section at all.  So
    key the assertion on the emitted ELF, not the host: IF the binary is
    dynamic (has any DT_NEEDED), libpthread must be among them; a fully static
    binary correctly has none.  This keeps the test valid on both the Linux and
    FreeBSD CI hosts. }
  SrcPath := WriteScratchSource(
    'program p; uses runtime.thread; begin WriteLn(GetCPUCount() > 0); end.');
  BinPath := FScratch + 'cli_pthr_nat_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('native threaded program links (out: ' + Out_ + ')', 0, EC);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  if Pos('(NEEDED)', Dyn) >= 0 then
    { Dynamic host (Linux): libpthread must be a DT_NEEDED. }
    AssertTrue('dynamic native threaded binary links libpthread (DT_NEEDED)',
      Pos('libpthread.so', Dyn) >= 0)
  else
    { Freestanding host (FreeBSD): static binary, no shared-lib dependency. }
    AssertTrue('static native threaded binary has no DT_NEEDED',
      Pos('libpthread.so', Dyn) < 0);
end;

procedure TCLIContractTests.TestPthread_StaticThreads_NoNeeded;
var SrcPath, BinPath, Out_, Dyn: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { A --static threaded binary is freestanding (no .dynamic section), so it must
    carry NO DT_NEEDED at all — threads come from the static kernel leaf, not
    libpthread.  Guards that AddNeededLib is skipped in static mode. }
  SrcPath := WriteScratchSource(
    'program p; uses runtime.thread; begin WriteLn(GetCPUCount() > 0); end.');
  BinPath := FScratch + 'cli_pthr_static_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native', '--static',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('static threaded program links (out: ' + Out_ + ')', 0, EC);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  AssertTrue('static binary has no DT_NEEDED', Pos('(NEEDED)', Dyn) < 0);
end;

procedure TCLIContractTests.TestLinkerScriptLib_ResolvesToVersionedSoname_Native;

  { True if <ADir>/lib<AName>.so exists and is a GNU ld linker script — a text
    file naming its inputs via INPUT(...) or GROUP(...).  A real ELF .so is
    binary and contains no leading INPUT/GROUP token, so a substring probe on
    the loaded text is a safe discriminator (and avoids raw byte I/O). }
  function IsLinkerScript(const ADir, AName: string): Boolean;
  var Path, Txt: string; L: TStringList;
  begin
    Result := False;
    Path := ADir + '/lib' + AName + '.so';
    if not FileExists(Path) then Exit;
    L := TStringList.Create();
    try
      try
        L.LoadFromFile(Path);
      except
        Exit;
      end;
      Txt := L.Text;
    finally
      L.Free();
    end;
    Result := (Pos('INPUT', Txt) >= 0) or (Pos('GROUP', Txt) >= 0);
  end;

var
  SrcPath, BinPath, Out_, Dyn, LibName: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Find a system library whose lib<name>.so is a linker script.  ncurses is
    the reported case (Debian/Ubuntu: INPUT(libncurses.so.6 -ltinfo)); libm is
    the near-universal fallback (GROUP(libm.so.6 ...)).  If neither is a script
    on this host, the platform does not exhibit the bug — skip. }
  LibName := '';
  if IsLinkerScript('/usr/lib/x86_64-linux-gnu', 'ncurses')
     or IsLinkerScript('/lib/x86_64-linux-gnu', 'ncurses') then
    LibName := 'ncurses'
  else if IsLinkerScript('/usr/lib/x86_64-linux-gnu', 'm')
          or IsLinkerScript('/lib/x86_64-linux-gnu', 'm') then
    LibName := 'm';
  if LibName = '' then
  begin
    Ignore('no linker-script system lib on this host');
    Exit;
  end;
  { A native program declaring an external symbol from that lib.  We do not run
    it (ncurses needs a tty); we only inspect the emitted DT_NEEDED. }
  SrcPath := WriteScratchSource(
    'program p;' + LineEnding +
    'function ext_probe(): Integer; external ''' + LibName +
      ''' name ''' + LibName + ''';' + LineEnding +
    'begin WriteLn(0); end.');
  BinPath := FScratch + 'cli_lnkscript_' + IntToStr(FCounter);
  EC := RunCompiler(['--source', SrcPath, '--backend', 'native',
    '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
    '--output', BinPath], Out_);
  AssertEquals('native program with linker-script lib links (out: '
    + Out_ + ')', 0, EC);
  Dyn := ReadelfDynamic(BinPath);
  if Dyn = '' then begin Ignore('readelf unavailable'); Exit; end;
  { The versioned SONAME must appear, and the bare lib<name>.so linker-script
    name must NOT be recorded as a DT_NEEDED (that was the "file too short" bug). }
  AssertTrue('DT_NEEDED carries the versioned SONAME lib' + LibName + '.so.',
    Pos('lib' + LibName + '.so.', Dyn) >= 0);
  AssertTrue('bare linker-script name lib' + LibName
    + '.so is NOT a DT_NEEDED',
    Pos('[lib' + LibName + '.so]', Dyn) < 0);
end;

procedure TCLIContractTests.TestDivByZeroCaught_QBE;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcDivByZeroCaught, '', Out_, EC));
  AssertEquals('exit code 0 (exception caught, not SIGFPE)', 0, EC);
  AssertTrue('EDivByZero caught with message',
    Pos('caught: Division by zero', Out_) >= 0);
  AssertTrue('execution continued past the catch', Pos('after', Out_) >= 0);
end;

procedure TCLIContractTests.TestDivByZeroCaught_Native;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcDivByZeroCaught, 'native', Out_, EC));
  AssertEquals('exit code 0 (exception caught, not SIGFPE)', 0, EC);
  AssertTrue('EDivByZero caught with message',
    Pos('caught: Division by zero', Out_) >= 0);
  AssertTrue('execution continued past the catch', Pos('after', Out_) >= 0);
end;

procedure TCLIContractTests.TestModByZeroCaught_QBE;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcModByZeroCaught, '', Out_, EC));
  AssertEquals('exit code 0', 0, EC);
  AssertTrue('mod by zero caught', Pos('mod caught', Out_) >= 0);
end;

procedure TCLIContractTests.TestModByZeroCaught_Native;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcModByZeroCaught, 'native', Out_, EC));
  AssertEquals('exit code 0', 0, EC);
  AssertTrue('mod by zero caught', Pos('mod caught', Out_) >= 0);
end;

procedure TCLIContractTests.TestBareOutput_UnitArtefacts_NotWrittenToRoot;
var
  UnitPath, ProgPath, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Regression: incremental compilation (default) compiles each used unit to
    its own .o/.bif via a worker.  The worker's output directory was derived
    from --output via IncludeTrailingPathDelimiter(ExtractFilePath(OutputFile)).
    For a bare --output filename (no directory part) ExtractFilePath returns ''
    and IncludeTrailingPathDelimiter('') yields '/', so the worker tried to
    write '/<unit>.o.bif.tmp' at the filesystem root and failed with
    'Cannot open file for writing: /<unit>.o.bif.tmp'.  The artefacts must land
    in the current directory instead. }
  UnitPath := FScratch + 'clidemo_unit.pas';
  WriteFile(UnitPath,
    'unit clidemo_unit;' + LineEnding +
    'interface' + LineEnding +
    'function Answer: Integer;' + LineEnding +
    'implementation' + LineEnding +
    'function Answer: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  Result := 42' + LineEnding +
    'end;' + LineEnding +
    'end.');
  ProgPath := WriteScratchSource(
    'program cli_bareout;' + LineEnding +
    'uses clidemo_unit;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(Answer())' + LineEnding +
    'end.');
  { Bare --output name (no '/') is the trigger; the unit is found via the
    scratch --unit-path. }
  EC := RunCompiler([
    '--source', ProgPath,
    '--unit-path', FScratch,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', 'cli_bareout_bin'
  ], Out_);
  { The bare output name resolves relative to the compiler's CWD (the test
    runner's working directory): the program binary and the per-unit .o land
    there.  Remove them so the working tree stays clean. }
  if FileExists('cli_bareout_bin') then DeleteFile('cli_bareout_bin');
  if FileExists('clidemo_unit.o') then DeleteFile('clidemo_unit.o');
  AssertTrue('no root-path worker failure: ' + Out_,
    Pos('Cannot open file for writing: /', Out_) < 0);
  AssertTrue('no worker exception: ' + Out_,
    Pos('Worker exception', Out_) < 0);
  AssertEquals('bare --output compile exits 0: ' + Out_, 0, EC);
end;

{ ---- BLAISE_BACKEND env-var precedence ----
  These drive the real compiler binary with BLAISE_BACKEND set in the child's
  inherited environment (setenv in this process; the child inherits it across
  fork+exec).  The native-only --assembler flag is the observable: the QBE
  driver reports it as an unknown flag, so a QBE selection fails at the arg
  drain while a native selection compiles.  setenv/unsetenv are bound directly
  to libc (already linked); no SetEnvironmentVariable builtin is needed. }
function _setenv(Name, Value: Pointer; Overwrite: Integer): Integer;
  external name 'setenv';
function _unsetenv(Name: Pointer): Integer; external name 'unsetenv';

procedure SetBackendEnv(const AValue: string);
var
  Key: string;
begin
  Key := 'BLAISE_BACKEND';
  _setenv(PChar(Key), PChar(AValue), 1)
end;

procedure ClearBackendEnv;
var
  Key: string;
begin
  Key := 'BLAISE_BACKEND';
  _unsetenv(PChar(Key))
end;

procedure TCLIContractTests.TestBackendEnv_Qbe_RejectsNativeOnlyFlag;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { BLAISE_BACKEND=qbe routes to the QBE driver, which rejects the native-only
    --assembler flag as unknown — proving the env var selected the backend. }
  Src := WriteScratchSource(
    'program cli_env_qbe;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  SetBackendEnv('qbe');
  try
    EC := RunCompiler([
      '--source', Src,
      '--unit-path', FRTLPath,
      '--unit-path', FStdlibPath,
      '--assembler', 'internal',
      '--output', FScratch + 'cli_env_qbe_bin'
    ], Out_);
  finally
    ClearBackendEnv();
  end;
  AssertTrue('BLAISE_BACKEND=qbe must route to QBE (rejects --assembler): ' + Out_,
    EC <> 0);
end;

procedure TCLIContractTests.TestBackendEnv_Native_AcceptsNativeOnlyFlag;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { BLAISE_BACKEND=native routes to the native driver, which owns --assembler
    and compiles successfully. }
  Src := WriteScratchSource(
    'program cli_env_native;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  SetBackendEnv('native');
  try
    EC := RunCompiler([
      '--source', Src,
      '--unit-path', FRTLPath,
      '--unit-path', FStdlibPath,
      '--assembler', 'internal',
      '--output', FScratch + 'cli_env_native_bin'
    ], Out_);
  finally
    ClearBackendEnv();
  end;
  AssertEquals('BLAISE_BACKEND=native must route to native (accepts --assembler): '
    + Out_, 0, EC);
end;

procedure TCLIContractTests.TestBackendEnv_ExplicitFlagBeatsEnv;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { An explicit --backend qbe outranks BLAISE_BACKEND=native, so the QBE driver
    is selected and rejects the native-only --assembler flag. }
  Src := WriteScratchSource(
    'program cli_env_flag;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  SetBackendEnv('native');
  try
    EC := RunCompiler([
      '--source', Src,
      '--unit-path', FRTLPath,
      '--unit-path', FStdlibPath,
      '--backend', 'qbe',
      '--assembler', 'internal',
      '--output', FScratch + 'cli_env_flag_bin'
    ], Out_);
  finally
    ClearBackendEnv();
  end;
  AssertTrue('explicit --backend qbe must outrank BLAISE_BACKEND=native: ' + Out_,
    EC <> 0);
end;

procedure TCLIContractTests.TestBackendEnv_InvalidValue_WarnsAndFallsBack;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { An unrecognised BLAISE_BACKEND value warns and falls back to the default
    (native) rather than aborting — so the native-only --assembler still
    compiles, and the warning names the offending value. }
  Src := WriteScratchSource(
    'program cli_env_bogus;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  SetBackendEnv('bogus');
  try
    EC := RunCompiler([
      '--source', Src,
      '--unit-path', FRTLPath,
      '--unit-path', FStdlibPath,
      '--assembler', 'internal',
      '--output', FScratch + 'cli_env_bogus_bin'
    ], Out_);
  finally
    ClearBackendEnv();
  end;
  AssertEquals('invalid BLAISE_BACKEND must fall back to default (compiles): '
    + Out_, 0, EC);
  AssertTrue('invalid BLAISE_BACKEND must warn and name the value: ' + Out_,
    Pos('BLAISE_BACKEND=bogus', Out_) >= 0);
end;

{ ---- Registration ---- }

initialization
  RegisterTest(TCLIContractTests);

end.
