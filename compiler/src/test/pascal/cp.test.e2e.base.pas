{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.base;

{ Shared base class for all E2E test suites.
  Provides toolchain setup, scratch directory management, and two
  CompileAndRun variants:
    - CompileAndRun        : single-program, no RTL units (inline classes)
    - CompileAndRunWithRTL : multi-unit, loads RTL units via TUnitLoader }

interface

uses
  classes, sysutils, process, contnrs, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uUnitLoader,
  blaise.codegen, blaise.codegen.target, blaise.codegen.native;

type
  TBackend = (beNative);
  TBackends = set of TBackend;

const
  { The backend set behind AssertRunsOnAll / AssertRTLRunsOnAll: the native
    backend for the host.  QBE left the e2e suite before the backend was
    removed in v0.15.0. }
  AllBackends: TBackends = [beNative];

function BackendName(ABackend: TBackend): string;


type
  TE2ETestCase = class(TTestCase)
  private
    FRTLUnitPath: string;
    FStdlibUnitPath: string;
    FScratch:     string;
    FCounter:     Integer;
    function  RunProc(const AExe: string; const AArgs: array of string;
                      out AStdout: string): Integer;
    function  RunProcNoArgs(const AExe: string; out AStdout: string): Integer;
    { Compile ASrc for the NATIVE backend by invoking the blaise compiler
      binary's own CLI, instead of driving TCodeGenNative + external cc in
      process.  The native driver defaults BOTH --assembler and --linker to
      internal, so this ONE subprocess does front-end + codegen + assemble +
      RTL + link entirely in-process — no qbe, no cc -c, no
      build-rtl-objects.sh, no external cc link.  Only two subprocesses run
      per test: this compile, and executing the produced binary.  Self-
      contained: does not go through LinkWithRTL, so it cannot support the
      -l extra-library case (LinkWithRTLLibs) — none of the native e2e
      callers need one today.  AExtraUnitPath, when non-empty, is added as a
      further --unit-path entry (e.g. FScratch, for CompileAndRunWithUnitOn's
      user-authored unit files); pass '' when the program has no such
      dependency. }
    function  CompileAndRunNativeCLI(const ASrc: string; ADebugMode: Boolean;
                          const AExtraUnitPath: string;
                          out AStdout: string;
                          out AExitCode: Integer): Boolean;
    { Compile-only half of CompileAndRunNativeCLI: returns the compiler's exit
      code, the binary path in ABinFile and its diagnostics in AToolOut. }
    function  CompileNativeCLI(const ASrc: string; ADebugMode: Boolean;
                          const AExtraUnitPath: string;
                          out ABinFile: string;
                          out AToolOut: string): Integer;
    { Link an assembled program (AAsmFile) into ABinFile against the RTL.  The
      RTL is built from source by scripts/build-rtl-objects.sh (no blaise_rtl.a
      archive); --exclude-defined-by drops the RTL objects the whole-program
      assembly already inlines, so the loose objects do not double-define.
      Returns the cc exit code; AStdout carries any tool output. }
    function  LinkWithRTL(const AAsmFile, ABinFile: string;
                          out AStdout: string): Integer;
    { As LinkWithRTL but appends extra -l libraries (e.g. 'ssl','crypto') so an
      RTL program that binds an external library links via the external toolchain
      path.  The internal linker cannot resolve external libraries; this e2e path
      always links with cc, which can. }
    function  LinkWithRTLLibs(const AAsmFile, ABinFile: string;
                          const AExtraLibs: array of string;
                          out AStdout: string): Integer;
  protected
    function  ProjectRoot: string;
    function  ToolchainAvailable(): Boolean;
    function  ValgrindAvailable(): Boolean;
    procedure SetUpScratch(const ADirName: string);
    procedure SetUp; override;
    function  CompileAndRun(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean; overload;
    function  CompileAndRun(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer;
                            const AExtraArgs: array of string): Boolean; overload;
    { Same as CompileAndRun; kept for the callers that name the backend. }
    function  CompileAndRunNative(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Compile and run ASrc on the chosen backend through the compiler's own
      CLI.  CompileAndRun and CompileAndRunNative both delegate here. }
    function  CompileAndRunOn(ABackend: TBackend; const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { As CompileAndRunOn; AExtraLibs is accepted for the callers that name
      libraries, which the native compiler links itself from the program's
      external declarations. }
    function  CompileAndRunOnLibs(ABackend: TBackend; const ASrc: string;
                            const AExtraLibs: array of string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Run ASrc on every backend in AllBackends (native only) and assert each
      produces AExpectedOut / AExpectedCode. }
    procedure AssertRunsOnAll(const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    { As AssertRunsOnAll but links with extra -l libraries.  For FFI tests
      whose external symbols live in a real system library (e.g. libm's
      sinf) -- the plain harness link deliberately carries no -lm. }
    procedure AssertRunsOnAllLibs(const ASrc: string;
                            const ALibs: array of string;
                            const AExpectedOut: string;
                            AExpectedCode: Integer);
    { Run ASrc on a specific set of backends only.  Use when a test should
      exercise fewer than AllBackends (e.g. a feature not yet ported). }
    procedure AssertRunsOn(ABackends: TBackends; const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    { RTL/stdlib equivalents of AssertRunsOn*: compile+run ASrc against the RTL
      and stdlib (multi-unit, TUnitLoader) on every backend in the set. }
    procedure AssertRTLRunsOnAll(const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    procedure AssertRTLRunsOn(ABackends: TBackends; const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    procedure AssertRTLRunsOnOne(ABackend: TBackend; const AName, ASrc,
                            AExpectedOut: string; AExpectedCode: Integer);
    { Convenience: RTL/stdlib compile+run on a specific backend (debug off). }
    function  CompileAndRunWithRTLOn(ABackend: TBackend; const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Per-backend worker used by AssertRunsOn (separate method because Blaise
      has no nested procedures). }
    procedure AssertRunsOnOne(ABackend: TBackend; const AName, ASrc,
                            AExpectedOut: string; AExpectedCode: Integer);
    { Assert ASrc runs with NO ARC leak under the --debug leak tracker, on
      every backend in AllBackends.  Complements RunUnderValgrind: valgrind
      catches UAF / invalid access but is BLIND to ARC refcount leaks (the
      Blaise allocator is mmap-backed, so valgrind sees zero malloc traffic);
      the --debug tracker reports Blaise objects still live at exit — the true
      leak signal.  Asserts exit 0 and no 'leak' in stdout.  AExpectSubstr,
      when non-empty, must appear in stdout too. }
    procedure AssertLeakFreeOnAll(const ASrc: string; const AExpectSubstr: string);
    { Compile ASrc and run it under valgrind --leak-check=full; True when
      valgrind reports nothing.  ALog carries valgrind's report. }
    function  RunUnderValgrind(const ASrc: string; out ALog: string): Boolean;
    { As RunUnderValgrind, but the in-process codegen + cc link and no leak
      check: an invalid read or write alone fails it. }
    function  RunUnderValgrindNative(const ASrc: string; out ALog: string): Boolean;
    function  CompileAndRunWithRTL(const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean; overload;
    function  CompileAndRunWithRTL(const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer;
                                   ADebugMode: Boolean): Boolean; overload;
    function  CompileAndRunWithRTLDebug(const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer;
                                   ADebugMode: Boolean): Boolean;
    function  CompileAndRunWithRTLDebugOn(ABackend: TBackend;
                                   const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer;
                                   ADebugMode: Boolean): Boolean;
    { Compile a program that USES a user unit written to the scratch dir, so
      the unit (not the program) is the compilation unit.  Exercises the
      multi-unit codegen path.  AUnitName is the unit identifier; AUnitSrc and
      ASrc are full sources.  RTL + stdlib units are also on the search path. }
    function  CompileAndRunWithUnit(const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
    { Backend-parameterised multi-unit compile+run: the user unit is written
      to the scratch dir, which goes on the compiler's --unit-path. }
    function  CompileAndRunWithUnitOn(ABackend: TBackend;
                                   const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
    { Native convenience over the multi-unit path. }
    function  CompileAndRunWithUnitNative(const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
    { Two-written-units compile+run.  Writes both units to the scratch
      dir (filename derived from each `unit <name>;` header) so the program's
      `uses` clause resolves them, then lowers + links + runs.  Needed for
      cross-unit tests (two units exporting the same name: last-wins shadowing,
      unit-qualified disambiguation).  Kept at 5 params (Self+5 = 6 register
      slots) so the stage-1 native ABI does not overflow. }
    function  CompileAndRunWithUnits(const AUnit1Src, AUnit2Src, ASrc: string;
                                     out AStdout: string;
                                     out AExitCode: Integer): Boolean;
  end;

implementation

var
  { Process-lifetime-unique counter for CompileAndRunNativeCLI's output paths.
    FCounter resets to 0 in every test's SetUp, so two DIFFERENT test methods
    can end up compiling to the exact same "t2" path moments apart.  Even with
    the Mach-O linker's delete-before-write fix (blaise.linker.macho.pas), that
    rapid delete+recreate-same-path+immediately-execute sequence still raced
    against macOS's asynchronous code-integrity bookkeeping for the old inode,
    producing flaky SIGKILLs across a full-suite run (not reproducible when a
    single test ran in isolation).  A counter that never resets guarantees
    every compile in the process gets a path no earlier compile ever used,
    which sidesteps the race entirely rather than depending on exactly how
    fast the kernel retires the previous inode. }
  GNativeCLICounter: Integer = 0;

{ ------------------------------------------------------------------ }
{ TE2ETestCase                                                         }
{ ------------------------------------------------------------------ }

function TE2ETestCase.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps: Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then begin Result := IncludeTrailingPathDelimiter(Result); Exit end;
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'compiler/src/main/pascal') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir())
end;

function TE2ETestCase.ToolchainAvailable(): Boolean;
begin
  { The compiler binary (it compiles, assembles and links every e2e program
    and source-builds the RTL) and the RTL source.  No archive, no qbe. }
  Result := FileExists(ProjectRoot() + 'compiler/target/blaise')
        and FileExists(ProjectRoot() + 'compiler/src/main/pascal/runtime.arc.pas')
end;

function TE2ETestCase.ValgrindAvailable(): Boolean;
var Dummy: string;
begin
  Result := RunProc('valgrind', ['--version'], Dummy) = 0
end;

procedure TE2ETestCase.SetUp;
begin
  { Subclasses must call SetUpScratch to set FScratch and FCounter }
  inherited SetUp();
  FCounter := 0;
  { RTL units (runtime.*, rtl.platform.*) now live in the compiler's own source
    tree after the RTL-unification move; the old runtime/src/main/pascal is empty. }
  FRTLUnitPath := ProjectRoot() + 'compiler/src/main/pascal';
  FStdlibUnitPath := ProjectRoot() + 'stdlib/src/main/pascal'
end;

procedure TE2ETestCase.SetUpScratch(const ADirName: string);
begin
  FScratch := ProjectRoot() + ADirName;
  ForceDirectories(FScratch);
  FCounter := 0
end;

function TE2ETestCase.RunProc(const AExe: string;
                              const AArgs: array of string;
                              out AStdout: string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TE2ETestCase.CompileNativeCLI(const ASrc: string;
                                       ADebugMode: Boolean;
                                       const AExtraUnitPath: string;
                                       out ABinFile: string;
                                       out AToolOut: string): Integer;
var
  SrcFile, BinFile, ToolOut, Chunk: string;
  Proc: TProcess;
  Rc: Integer;
begin
  Inc(GNativeCLICounter);
  SrcFile := FScratch + '/n' + IntToStr(GNativeCLICounter) + '.pas';
  BinFile := FScratch + '/n' + IntToStr(GNativeCLICounter);
  WriteFile(SrcFile, ASrc);

  Proc := TProcess.Create(nil);
  try
    Proc.Executable := ProjectRoot() + 'compiler/target/blaise';
    Proc.Parameters.Add('--source');
    Proc.Parameters.Add(SrcFile);
    Proc.Parameters.Add('--backend');
    Proc.Parameters.Add('native');
    Proc.Parameters.Add('--unit-path');
    Proc.Parameters.Add(FRTLUnitPath);
    Proc.Parameters.Add('--unit-path');
    Proc.Parameters.Add(FStdlibUnitPath);
    if AExtraUnitPath <> '' then
    begin
      Proc.Parameters.Add('--unit-path');
      Proc.Parameters.Add(AExtraUnitPath)
    end;
    if ADebugMode then
      Proc.Parameters.Add('--debug');
    Proc.Parameters.Add('--output');
    Proc.Parameters.Add(BinFile);
    Proc.Execute();
    ToolOut := '';
    repeat
      Chunk := Proc.ReadOutput();
      ToolOut := ToolOut + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Rc := Proc.ExitCode
  finally
    Proc.Free()
  end;
  ABinFile := BinFile;
  AToolOut := ToolOut;
  Result := Rc
end;

function TE2ETestCase.CompileAndRunNativeCLI(const ASrc: string;
                                             ADebugMode: Boolean;
                                             const AExtraUnitPath: string;
                                             out AStdout: string;
                                             out AExitCode: Integer): Boolean;
var
  BinFile, ToolOut: string;
  Rc: Integer;
begin
  Result := False;
  Rc := Self.CompileNativeCLI(ASrc, ADebugMode, AExtraUnitPath, BinFile, ToolOut);
  if Rc <> 0 then begin AStdout := 'compile failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

function TE2ETestCase.LinkWithRTL(const AAsmFile, ABinFile: string;
                                 out AStdout: string): Integer;
var
  NoLibs: array[0..0] of string;
begin
  { No extra libraries beyond the RTL's own -lpthread. }
  NoLibs[0] := '';
  Result := Self.LinkWithRTLLibs(AAsmFile, ABinFile, NoLibs, AStdout);
end;

function TE2ETestCase.LinkWithRTLLibs(const AAsmFile, ABinFile: string;
                                 const AExtraLibs: array of string;
                                 out AStdout: string): Integer;
var
  ProgObj, ObjDir, Compiler, ScriptOut: string;
  Objs: TStringList;
  Proc: TProcess;
  I: Integer;
begin
  { 1. Assemble the program to an object so build-rtl-objects.sh can see which
       RTL symbols it already defines (it inlines the RTL units it uses). }
  ProgObj := AAsmFile + '.o';
  Result := RunProc('cc', ['-c', '-o', ProgObj, AAsmFile], AStdout);
  if Result <> 0 then Exit;

  { 2. Build the RTL objects from source, excluding the units the program
       already inlined.  Compiler binary is the freshly-built compiler/target. }
  Compiler := ProjectRoot() + 'compiler/target/blaise';
  ObjDir   := IncludeTrailingPathDelimiter(FScratch) + 'rtlobj';
  Result := RunProc(ProjectRoot() + 'scripts/build-rtl-objects.sh',
                    [Compiler, ObjDir, '--exclude-defined-by', ProgObj],
                    ScriptOut);
  if Result <> 0 then
  begin
    AStdout := 'build-rtl-objects failed: ' + ScriptOut;
    Exit;
  end;

  { 3. Link: cc -o Bin ProgObj <rtl objects> -lpthread [extra -l...].  Build
       the TProcess directly so the object list (variable length) can be
       appended.  Deliberately NO -lm: the RTL's runtime.math replaces libm,
       and a hardcoded -lm here would mask any regression that reintroduces
       a libm symbol (exactly how the GH #199 undefined-pow escape stayed
       invisible to the e2e suite).  A test that really wants libm (the FFI
       marshalling tests targeting sinf/sqrtf) passes 'm' as an extra lib. }
  Objs := TStringList.Create();
  Proc := TProcess.Create(nil);
  try
    Objs.Text := ScriptOut;
    Proc.Executable := 'cc';
    Proc.Parameters.Add('-o');
    Proc.Parameters.Add(ABinFile);
    Proc.Parameters.Add(ProgObj);
    for I := 0 to Objs.Count - 1 do
      if Trim(Objs.Strings[I]) <> '' then
        Proc.Parameters.Add(Trim(Objs.Strings[I]));
    Proc.Parameters.Add('-lpthread');
    for I := 0 to High(AExtraLibs) do
      if Trim(AExtraLibs[I]) <> '' then
        Proc.Parameters.Add('-l' + Trim(AExtraLibs[I]));
    Proc.Execute();
    AStdout := '';
    repeat
      ScriptOut := Proc.ReadOutput();
      AStdout := AStdout + ScriptOut
    until (ScriptOut = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
    Objs.Free();
  end;
end;


function TE2ETestCase.RunProcNoArgs(const AExe: string;
                                    out AStdout: string): Integer;
const
  { Wall-clock budget for one compiled e2e program.  Generous: the slowest
    legitimate program (the 10k-fiber scheduler smoke test) runs in ~2 s. }
  RunTimeoutSecs = '60';
  Watchdog = '/usr/bin/perl';
var
  Proc:  TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    { A miscompiled program can block forever (the errno probe did, on
      Apple's variadic ABI) and ReadOutput has no timeout, so one hang stalled
      the whole suite.  Run under a watchdog: perl's alarm survives exec, so
      the program itself is killed by SIGALRM (exit 142) once the budget is
      spent, and no helper process is left holding the output pipe.  Hosts
      without perl in base (FreeBSD) run the program directly, as before. }
    if FileExists(Watchdog) then
    begin
      Proc.Executable := Watchdog;
      Proc.Parameters.Add('-e');
      Proc.Parameters.Add('alarm shift; exec @ARGV or exit 127');
      Proc.Parameters.Add(RunTimeoutSecs);
      Proc.Parameters.Add(AExe)
    end
    else
      Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TE2ETestCase.CompileAndRunOn(ABackend: TBackend; const ASrc: string;
                                     out AStdout: string;
                                     out AExitCode: Integer): Boolean;
var
  NoLibs: array[0..0] of string;
begin
  NoLibs[0] := '';
  Result := Self.CompileAndRunOnLibs(ABackend, ASrc, NoLibs, AStdout, AExitCode);
end;

function TE2ETestCase.CompileAndRunOnLibs(ABackend: TBackend; const ASrc: string;
                                     const AExtraLibs: array of string;
                                     out AStdout: string;
                                     out AExitCode: Integer): Boolean;
begin
  { Single choke point for a plain compile+run.  The compiler's own CLI does
    front-end, codegen, assembly, RTL and link in one subprocess (see
    CompileAndRunNativeCLI); it links the libraries a program's external
    declarations name, so AExtraLibs needs no handling here. }
  Result := Self.CompileAndRunNativeCLI(ASrc, False, '', AStdout, AExitCode)
end;

function TE2ETestCase.CompileAndRun(const ASrc: string;
                                    out AStdout: string;
                                    out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunOn(beNative, ASrc, AStdout, AExitCode)
end;

function TE2ETestCase.CompileAndRunNative(const ASrc: string;
                                          out AStdout: string;
                                          out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunOn(beNative, ASrc, AStdout, AExitCode)
end;

{ Run ASrc on one backend and assert its stdout/exit match the expected
  values, tagging the failure message with the backend name. }
procedure TE2ETestCase.AssertRunsOnOne(ABackend: TBackend; const AName, ASrc,
                                       AExpectedOut: string; AExpectedCode: Integer);
var
  Output: string;
  RCode:  Integer;
  OK:     Boolean;
begin
  OK := Self.CompileAndRunOn(ABackend, ASrc, Output, RCode);
  AssertTrue('[' + AName + '] compile+run: ' + Output, OK);
  if RCode <> AExpectedCode then
    AssertEquals('[' + AName + '] exit code (stdout: ' + Output + ')',
      AExpectedCode, RCode)
  else
    AssertEquals('[' + AName + '] exit code', AExpectedCode, RCode);
  AssertEquals('[' + AName + '] stdout', AExpectedOut, Output)
end;

function BackendName(ABackend: TBackend): string;
begin
  Result := 'native'
end;

procedure TE2ETestCase.AssertRunsOnAll(const ASrc, AExpectedOut: string;
                                       AExpectedCode: Integer);
begin
  Self.AssertRunsOn(AllBackends, ASrc, AExpectedOut, AExpectedCode)
end;

procedure TE2ETestCase.AssertRunsOnAllLibs(const ASrc: string;
                                       const ALibs: array of string;
                                       const AExpectedOut: string;
                                       AExpectedCode: Integer);
var
  BE: TBackend;
  Backends: TBackends;
  Output: string;
  RCode:  Integer;
  OK:     Boolean;
begin
  Backends := AllBackends;
  if Backends = [] then
  begin
    Ignore('no backend supported on this host for this test');
    Exit;
  end;
  for BE := Low(TBackend) to High(TBackend) do
    if BE in Backends then
    begin
      OK := Self.CompileAndRunOnLibs(BE, ASrc, ALibs, Output, RCode);
      AssertTrue('[' + BackendName(BE) + '] compile+run: ' + Output, OK);
      AssertEquals('[' + BackendName(BE) + '] exit code', AExpectedCode, RCode);
      AssertEquals('[' + BackendName(BE) + '] stdout', AExpectedOut, Output);
    end;
end;

procedure TE2ETestCase.AssertRunsOn(ABackends: TBackends; const ASrc, AExpectedOut: string;
                                    AExpectedCode: Integer);
var
  BE: TBackend;
begin
  if ABackends = [] then
  begin
    Ignore('no backend supported on this host for this test');
    Exit;
  end;
  for BE := Low(TBackend) to High(TBackend) do
    if BE in ABackends then
      Self.AssertRunsOnOne(BE, BackendName(BE), ASrc, AExpectedOut, AExpectedCode)
end;

function TE2ETestCase.CompileAndRun(const ASrc: string;
                                    out AStdout: string;
                                    out AExitCode: Integer;
                                    const AExtraArgs: array of string): Boolean;
var
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  { As CompileAndRun, running the binary with AExtraArgs. }
  Result := False;
  Rc := Self.CompileNativeCLI(ASrc, False, '', BinFile, ToolOut);
  if Rc <> 0 then begin AStdout := 'compile failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProc(BinFile, AExtraArgs, AStdout);
  Result := True
end;

procedure TE2ETestCase.AssertLeakFreeOnAll(const ASrc: string;
  const AExpectSubstr: string);
var
  Output: string;
  ExitCode: Integer;
  Ok: Boolean;
  BE: TBackend;
  Tag: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  for BE := Low(TBackend) to High(TBackend) do
    if BE in AllBackends then
    begin
      Tag := BackendName(BE);
      Ok := CompileAndRunWithRTLDebugOn(BE, ASrc, Output, ExitCode, True);
      AssertTrue(Tag + ' compile+run (--debug): ' + Output, Ok);
      AssertEquals(Tag + ' exit 0 (output: ' + Output + ')', 0, ExitCode);
      if AExpectSubstr <> '' then
        AssertTrue(Tag + ' stdout contains ''' + AExpectSubstr + ''', got: ' +
          Output, Pos(AExpectSubstr, Output) >= 0);
      AssertTrue(Tag + ' no leak report, got: ' + Output, Pos('leak', Output) < 0);
    end;
end;

function TE2ETestCase.RunUnderValgrind(const ASrc: string; out ALog: string): Boolean;
var
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  ALog   := '';
  Rc := Self.CompileNativeCLI(ASrc, False, '', BinFile, ToolOut);
  if Rc <> 0 then begin ALog := 'compile failed: ' + ToolOut; Exit end;
  Rc := RunProc('valgrind',
    ['--error-exitcode=99', '--leak-check=full', '--quiet', BinFile], ALog);
  Result := Rc = 0
end;

function TE2ETestCase.RunUnderValgrindNative(const ASrc: string; out ALog: string): Boolean;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  NCG:      TCodeGenNative;
  CG:       ICodeGen;
  Asm_:     string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  ALog   := '';
  Inc(FCounter);
  AsmFile := FScratch + '/vgn' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/vgn' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    NCG      := TCodeGenNative.Create();
    NCG.SetTarget(HostTarget());
    CG       := NCG;            { ARC-managed; released at scope exit }
    CG.Generate(Prog);
    Asm_     := CG.GetOutput()
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(AsmFile, Asm_);
  Rc := LinkWithRTL(AsmFile, BinFile, ToolOut);
  if Rc <> 0 then begin ALog := 'cc failed: ' + ToolOut; Exit end;

  { --error-exitcode=99: any invalid read/write (the use-after-free) makes
    valgrind exit non-zero even when the program does not itself crash. }
  Rc := RunProc('valgrind',
    ['--error-exitcode=99', '--leak-check=no', '--quiet', BinFile], ALog);
  Result := Rc = 0
end;

function TE2ETestCase.CompileAndRunWithRTL(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithRTLDebugOn(beNative, ASrc, AStdout, AExitCode,
                                             False)
end;

function TE2ETestCase.CompileAndRunWithRTL(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer;
                                           ADebugMode: Boolean): Boolean;
begin
  Result := CompileAndRunWithRTLDebug(ASrc, AStdout, AExitCode, ADebugMode);
end;

function TE2ETestCase.CompileAndRunWithRTLDebug(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer;
                                           ADebugMode: Boolean): Boolean;
begin
  Result := Self.CompileAndRunWithRTLDebugOn(beNative, ASrc, AStdout, AExitCode,
                                             ADebugMode)
end;

function TE2ETestCase.CompileAndRunWithRTLOn(ABackend: TBackend;
                                           const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithRTLDebugOn(ABackend, ASrc, AStdout, AExitCode,
                                             False)
end;

procedure TE2ETestCase.AssertRTLRunsOnAll(const ASrc, AExpectedOut: string;
                                          AExpectedCode: Integer);
begin
  Self.AssertRTLRunsOn(AllBackends, ASrc, AExpectedOut, AExpectedCode)
end;

procedure TE2ETestCase.AssertRTLRunsOn(ABackends: TBackends;
                                       const ASrc, AExpectedOut: string;
                                       AExpectedCode: Integer);
var
  BE: TBackend;
begin
  if ABackends = [] then
  begin
    Ignore('no backend supported on this host for this test');
    Exit;
  end;
  for BE := Low(TBackend) to High(TBackend) do
    if BE in ABackends then
      Self.AssertRTLRunsOnOne(BE, BackendName(BE), ASrc, AExpectedOut,
                              AExpectedCode)
end;

procedure TE2ETestCase.AssertRTLRunsOnOne(ABackend: TBackend;
                                          const AName, ASrc, AExpectedOut: string;
                                          AExpectedCode: Integer);
var
  Output: string;
  RCode:  Integer;
  Ok:     Boolean;
begin
  { Evaluate FIRST, then build the message: Output is an out-param, so it is
    only populated by the call.  On a compile failure it carries the
    compiler's own diagnostic, which is the only clue a CI-only failure
    leaves behind. }
  Ok := Self.CompileAndRunWithRTLOn(ABackend, ASrc, Output, RCode);
  AssertTrue('[' + AName + '] compile+run (RTL): ' + Output, Ok);
  if RCode <> AExpectedCode then
    AssertEquals('[' + AName + '] exit code (stdout: ' + Output + ')',
      AExpectedCode, RCode)
  else
    AssertEquals('[' + AName + '] exit code', AExpectedCode, RCode);
  AssertEquals('[' + AName + '] stdout', AExpectedOut, Output)
end;

function TE2ETestCase.CompileAndRunWithRTLDebugOn(ABackend: TBackend;
                                         const ASrc: string;
                                         out AStdout: string;
                                         out AExitCode: Integer;
                                         ADebugMode: Boolean): Boolean;
begin
  { The CLI's --unit-path RTL/stdlib pair gives the compiler's own unit
    loader the search paths the program needs. }
  Result := Self.CompileAndRunNativeCLI(ASrc, ADebugMode, '', AStdout,
                                        AExitCode)
end;

function TE2ETestCase.CompileAndRunWithUnit(const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithUnitOn(beNative, AUnitName, AUnitSrc, ASrc,
                                         AStdout, AExitCode)
end;

function TE2ETestCase.CompileAndRunWithUnitNative(const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithUnitOn(beNative, AUnitName, AUnitSrc, ASrc,
                                         AStdout, AExitCode)
end;

function TE2ETestCase.CompileAndRunWithUnitOn(ABackend: TBackend;
                                            const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
begin
  { Write the user unit to the scratch dir, which goes on the compiler's
    --unit-path so the program's uses clause resolves it. }
  WriteFile(FScratch + '/' + AUnitName + '.pas', AUnitSrc);
  Result := Self.CompileAndRunNativeCLI(ASrc, False, FScratch, AStdout,
                                        AExitCode)
end;

{ Extract the unit name from a 'unit <name>;' header so the source can be
  written to the matching <name>.pas the unit loader expects.  Strings are
  byte-indexed (S[i] returns a Byte); Pos is 0-based and returns -1 when the
  substring is absent. }
function UnitNameOf(const ASrc: string): string;
var
  P, Q: Integer;
begin
  P := Pos('unit ', ASrc);
  if P < 0 then begin Result := ''; Exit; end;
  P := P + 5;                  { skip past 'unit ' }
  Q := P;
  while (Q < Length(ASrc)) and (ASrc[Q] <> Ord(';')) and (ASrc[Q] <> Ord(' '))
        and (ASrc[Q] <> 10) and (ASrc[Q] <> 13) do
    Q := Q + 1;
  Result := Copy(ASrc, P, Q - P);
end;

function TE2ETestCase.CompileAndRunWithUnits(const AUnit1Src, AUnit2Src,
                                             ASrc: string;
                                             out AStdout: string;
                                             out AExitCode: Integer): Boolean;
begin
  { Both units go beside the program, named from their own headers, so the
    compiler's loader finds them on the scratch path. }
  WriteFile(FScratch + '/' + UnitNameOf(AUnit1Src) + '.pas', AUnit1Src);
  WriteFile(FScratch + '/' + UnitNameOf(AUnit2Src) + '.pas', AUnit2Src);
  Result := Self.CompileAndRunNativeCLI(ASrc, False, FScratch, AStdout,
    AExitCode)
end;

end.
