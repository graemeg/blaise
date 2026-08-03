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
  uLexer, uParser, uAST, uSemantic, blaise.codegen.qbe, uUnitLoader,
  blaise.codegen, blaise.codegen.target, blaise.codegen.native;

type
  TBackend = (beQBE, beNative);
  TBackends = set of TBackend;

const
  AllBackends: TBackends = [beQBE, beNative];

function BackendName(ABackend: TBackend): string;

{ True when ABackend can produce a program that actually RUNS on the host.
  False for QBE on macOS — see TargetHasQBEBackend in blaise.codegen.target.
  The e2e harness always compiles for the host, so the host target is the only
  one that matters here. }
function BackendRunnableOnHost(ABackend: TBackend): Boolean;

type
  TE2ETestCase = class(TTestCase)
  private
    FQBE:         string;
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
    { Native-backend equivalent of CompileAndRun: lowers the program to
      assembly via TCodeGenNative (no QBE), links with cc, and runs.  The
      correctness oracle is parity with the QBE path on the same source. }
    function  CompileAndRunNative(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Compile and run ASrc on the chosen backend.  Shared front-end (lex,
      parse, semantic); the backend selects QBE-text+qbe or direct native
      assembly.  CompileAndRun and CompileAndRunNative both delegate here. }
    function  CompileAndRunOn(ABackend: TBackend; const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { As CompileAndRunOn but links with extra -l libraries (see
      AssertRunsOnAllLibs). }
    function  CompileAndRunOnLibs(ABackend: TBackend; const ASrc: string;
                            const AExtraLibs: array of string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Run ASrc on every backend in AllBackends and assert each produces
      AExpectedOut / AExpectedCode.  When a new backend is added to AllBackends,
      all callers pick it up automatically. }
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
      and stdlib (multi-unit, TUnitLoader) on every backend and assert parity.
      Use these in RTL/stdlib suites so native gets the same coverage as QBE. }
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
    { QBE-only RTL compile+run.  Escape hatch for the rare case where native
      has a known, documented gap that is tracked separately — keeps the rest of
      a suite dual-backend while not blocking on the one failing construct.  Add
      a comment at each call site naming the tracked bug. }
    function  CompileAndRunWithRTLQBEOnly(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Per-backend worker used by AssertRunsOn (separate method because Blaise
      has no nested procedures). }
    procedure AssertRunsOnOne(ABackend: TBackend; const AName, ASrc,
                            AExpectedOut: string; AExpectedCode: Integer);
    { Assert ASrc runs with NO ARC leak on both backends under the --debug
      leak tracker.  Complements RunUnderValgrind: valgrind catches native
      UAF / invalid access but is BLIND to ARC refcount leaks (the Blaise
      allocator is mmap-backed, so valgrind sees zero malloc traffic); the
      --debug tracker reports Blaise objects still live at exit — the true
      leak signal.  Runs QBE and native, asserts exit 0 and no 'leak' in
      stdout.  AExpectSubstr, when non-empty, must appear in stdout too. }
    procedure AssertLeakFreeOnAll(const ASrc: string; const AExpectSubstr: string);
    function  RunUnderValgrind(const ASrc: string; out ALog: string): Boolean;
    { Native-backend twin of RunUnderValgrind: compile ASrc with the NATIVE
      codegen, link, and run under valgrind.  Needed to detect native-only
      use-after-free/leak bugs that the QBE-only RunUnderValgrind cannot see. }
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
    { Backend-parameterised multi-unit compile+run: lowers the unit(s) + program
      via the QBE or native backend (whole-program model: AppendUnit per
      dependency, then AppendProgram), then links and runs.  The native path
      exercises TX86_64Backend.EmitUnit / AppendProgram. }
    function  CompileAndRunWithUnitOn(ABackend: TBackend;
                                   const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
    { Native convenience over the multi-unit path. }
    function  CompileAndRunWithUnitNative(const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
    { Two-written-units compile+run (QBE).  Writes both units to the scratch
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
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
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
  { Need the QBE assembler, the compiler binary (build-rtl-objects.sh drives it
    to source-build the RTL), and the RTL source.  No blaise_rtl.a archive. }
  Result := FileExists(FQBE)
        and FileExists(ProjectRoot() + 'compiler/target/blaise')
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
  FQBE := GetEnvironmentVariable('BLAISE_QBE');
  if FQBE = '' then
    FQBE := ProjectRoot() + 'vendor/qbe/qbe';
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

function TE2ETestCase.CompileAndRunNativeCLI(const ASrc: string;
                                             ADebugMode: Boolean;
                                             const AExtraUnitPath: string;
                                             out AStdout: string;
                                             out AExitCode: Integer): Boolean;
var
  SrcFile, BinFile, ToolOut, Chunk: string;
  Proc: TProcess;
  Rc: Integer;
begin
  Result := False;
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
var
  Proc:  TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
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
{ Single choke point for every compile+run in the harness, so the
  unsupported-backend skip cannot be forgotten by a caller.  A QBE-ONLY test
  (CompileAndRunWithRTLDebug and friends hard-code beQBE) has no other arm to
  fall back on, so Ignore is the honest outcome: EIgnoredTest aborts the test and
  it is REPORTED as skipped with this reason rather than passing vacuously.
  Dual-backend callers never reach this — AssertRunsOn filters QBE out of the
  set first, keeping their native arm. }
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  QCG:      TCodeGenQBE;
  Emitted:  string;       { QBE IR text }
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  { Gate EVERY backend-taking entry point, so a caller cannot bypass the
    unsupported-backend skip.  Ignore raises EIgnoredTest: the test is REPORTED
    as skipped with a reason, not silently passed.  Dual-backend callers never
    arrive here for an unsupported backend — AssertRunsOn drops it from the set
    first so their native arm still runs. }
  if not BackendRunnableOnHost(ABackend) then
    Ignore(BackendName(ABackend) +
      ' backend is not supported on this host target');
  { Native goes through the compiler's own CLI (front-end + codegen + internal
    assemble + internal link all inside that one subprocess) — see
    CompileAndRunNativeCLI.  Only QBE needs the manual IR/asm/link pipeline
    below, because qbe itself is an external tool this compiler does not (and
    is not meant to) absorb. }
  if ABackend = beNative then
  begin
    Result := Self.CompileAndRunNativeCLI(ASrc, False, '', AStdout, AExitCode);
    Exit
  end;
  Inc(FCounter);
  IRFile  := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/t' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; QCG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    QCG := TCodeGenQBE.Create();
    QCG.Generate(Prog);
    Emitted := QCG.GetOutput()
  finally
    QCG.Free();
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  { beNative already returned above via CompileAndRunNativeCLI; from here on
    only the QBE path remains. }
  WriteFile(IRFile, Emitted);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := LinkWithRTLLibs(AsmFile, BinFile, AExtraLibs, ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

function TE2ETestCase.CompileAndRun(const ASrc: string;
                                    out AStdout: string;
                                    out AExitCode: Integer): Boolean;
begin
  { QBE-only.  A blanket dual-backend flip here is unsafe: some inline e2e
    programs print non-deterministic values (e.g. GetProcessID) that cannot be
    compared across two separate process runs, and several genuine native gaps
    (StrToDouble/DoubleToStr formatting, InheritsFrom/ToString builtins, class
    const-array, interface-field-assignment-RHS) are still open — see bugs.txt.
    Suites whose programs ARE deterministic and native-clean use AssertRunsOnAll
    instead, which runs both backends.  As the native gaps close, more inline
    suites can migrate to AssertRunsOnAll. }
  Result := Self.CompileAndRunOn(beQBE, ASrc, AStdout, AExitCode)
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

function BackendRunnableOnHost(ABackend: TBackend): Boolean;
begin
  if ABackend = beQBE then
    Result := TargetHasQBEBackend(HostTarget())
  else
    Result := True;
end;

function BackendName(ABackend: TBackend): string;
begin
  case ABackend of
    beQBE:    Result := 'qbe';
    beNative: Result := 'native'
  else
    Result := 'unknown'
  end
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
  if not BackendRunnableOnHost(beQBE) then
    Backends := Backends - [beQBE];
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
  { Skip a backend the HOST target cannot actually run — QBE on macOS, which was
    never ported to Mach-O (TargetHasQBEBackend).

    FILTERED, not Ignore()d, and that distinction is the whole point: Ignore
    raises EIgnoredTest and would mark the ENTIRE test skipped, silently
    discarding the native arm of ~283 dual-backend tests that pass today.  By
    dropping only the unsupported backend from the set, each test still runs and
    still asserts on native — the coverage that matters on this platform — and
    goes genuinely green rather than green-by-omission.

    A test whose set becomes EMPTY is a different case: it had nothing but the
    unsupported backend, so there is no coverage left to report and it is
    honestly skipped. }
  if not BackendRunnableOnHost(beQBE) then
    ABackends := ABackends - [beQBE];
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
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
  IR:       string;
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  { Gate EVERY backend-taking entry point, so a caller cannot bypass the
    unsupported-backend skip.  Ignore raises EIgnoredTest: the test is REPORTED
    as skipped with a reason, not silently passed.  Dual-backend callers never
    arrive here for an unsupported backend — AssertRunsOn drops it from the set
    first so their native arm still runs. }
  if not BackendRunnableOnHost(beQBE) then
    Ignore(BackendName(beQBE) +
      ' backend is not supported on this host target');
  Inc(FCounter);
  IRFile  := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/t' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    CG       := TCodeGenQBE.Create();
    CG.Generate(Prog);
    IR       := CG.GetOutput()
  finally
    CG.Free(); Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, IR);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := LinkWithRTL(AsmFile, BinFile, ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProc(BinFile, AExtraArgs, AStdout);
  Result := True
end;

procedure TE2ETestCase.AssertLeakFreeOnAll(const ASrc: string;
  const AExpectSubstr: string);
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { QBE, --debug }
  AssertTrue('qbe compile+run (--debug)',
    CompileAndRunWithRTLDebugOn(beQBE, ASrc, Output, ExitCode, True));
  AssertEquals('qbe exit 0', 0, ExitCode);
  if AExpectSubstr <> '' then
    AssertTrue('qbe stdout contains ''' + AExpectSubstr + ''', got: ' + Output,
      Pos(AExpectSubstr, Output) >= 0);
  AssertTrue('qbe no leak report, got: ' + Output, Pos('leak', Output) < 0);
  { native, --debug }
  AssertTrue('native compile+run (--debug)',
    CompileAndRunWithRTLDebugOn(beNative, ASrc, Output, ExitCode, True));
  AssertEquals('native exit 0', 0, ExitCode);
  if AExpectSubstr <> '' then
    AssertTrue('native stdout contains ''' + AExpectSubstr + ''', got: ' + Output,
      Pos(AExpectSubstr, Output) >= 0);
  AssertTrue('native no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

function TE2ETestCase.RunUnderValgrind(const ASrc: string; out ALog: string): Boolean;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
  IR:       string;
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  ALog   := '';
  Inc(FCounter);
  IRFile  := FScratch + '/vg' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/vg' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/vg' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    CG       := TCodeGenQBE.Create();
    CG.Generate(Prog);
    IR       := CG.GetOutput()
  finally
    CG.Free(); Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, IR);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then Exit;
  Rc := LinkWithRTL(AsmFile, BinFile, ToolOut);
  if Rc <> 0 then Exit;

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
var
  NOut: string;
  NCode: Integer;
  NOk: Boolean;
begin
  { Run on BOTH backends and require parity.  Historically this helper was
    QBE-only, which left every RTL/stdlib suite that uses it unvalidated on the
    native backend.  We now compile+run the program with QBE first (its result
    is returned so the caller's existing assertions still pin correctness), then
    repeat on native and assert the native stdout/exit code match QBE.  A native
    codegen or RTL-ABI divergence therefore fails the test with a clear message
    rather than going unnoticed.  Debug-mode and *On variants stay single-backend
    for callers that need a specific backend (e.g. leak checks). }
  Result := Self.CompileAndRunWithRTLDebugOn(beQBE, ASrc, AStdout, AExitCode,
                                             False);
  if not Result then Exit;
  NOk := Self.CompileAndRunWithRTLDebugOn(beNative, ASrc, NOut, NCode, False);
  AssertTrue('[native] RTL compile+run', NOk);
  if NCode <> AExitCode then
    AssertEquals('[native] exit code parity with qbe (native stdout: ' +
      NOut + ')', AExitCode, NCode)
  else
    AssertEquals('[native] exit code parity with qbe', AExitCode, NCode);
  AssertEquals('[native] stdout parity with qbe', AStdout, NOut);
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
  { QBE-backed convenience; the full dual-backend implementation lives in
    CompileAndRunWithRTLDebugOn.  Kept so existing QBE-only callers behave
    exactly as before. }
  Result := Self.CompileAndRunWithRTLDebugOn(beQBE, ASrc, AStdout, AExitCode,
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

function TE2ETestCase.CompileAndRunWithRTLQBEOnly(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithRTLDebugOn(beQBE, ASrc, AStdout, AExitCode,
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
begin
  AssertTrue('[' + AName + '] compile+run (RTL)',
    Self.CompileAndRunWithRTLOn(ABackend, ASrc, Output, RCode));
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
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  QCG:         TCodeGenQBE;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Emitted:     string;
  IRFile:      string;
  AsmFile:     string;
  BinFile:     string;
  ToolOut:     string;
  Rc:          Integer;
  I:           Integer;
begin
  Result := False;
  { Gate EVERY backend-taking entry point, so a caller cannot bypass the
    unsupported-backend skip.  Ignore raises EIgnoredTest: the test is REPORTED
    as skipped with a reason, not silently passed.  Dual-backend callers never
    arrive here for an unsupported backend — AssertRunsOn drops it from the set
    first so their native arm still runs. }
  if not BackendRunnableOnHost(ABackend) then
    Ignore(BackendName(ABackend) +
      ' backend is not supported on this host target');
  { Native goes through the compiler's own CLI — see CompileAndRunNativeCLI.
    Its --unit-path RTL/stdlib pair already gives the compiler's own unit
    loader exactly the search paths this method builds manually below for
    QBE, so no separate whole-program AppendUnit dance is needed here. }
  if ABackend = beNative then
  begin
    Result := Self.CompileAndRunNativeCLI(ASrc, ADebugMode, '', AStdout,
                                          AExitCode);
    Exit
  end;
  Inc(FCounter);
  IRFile  := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/t' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  QCG := nil; Loader := nil; Units := nil; SearchPaths := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    QCG := TCodeGenQBE.Create();
    QCG.SetDebugMode(ADebugMode);
    QCG.SetSymbolTable(Prog.SymbolTable);
    for I := 0 to Units.Count - 1 do
      QCG.AppendUnit(TUnit(Units.Items[I]));
    QCG.AppendProgram(Prog);
    Emitted := QCG.GetOutput()
  finally
    QCG.Free(); Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, Emitted);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := LinkWithRTL(AsmFile, BinFile, ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

function TE2ETestCase.CompileAndRunWithUnit(const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithUnitOn(beQBE, AUnitName, AUnitSrc, ASrc,
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
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  QCG:         TCodeGenQBE;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Emitted:     string;       { QBE IR text }
  IRFile, AsmFile, BinFile, ToolOut, UnitFile: string;
  Rc, I:       Integer;
begin
  Result := False;
  { Gate EVERY backend-taking entry point, so a caller cannot bypass the
    unsupported-backend skip.  Ignore raises EIgnoredTest: the test is REPORTED
    as skipped with a reason, not silently passed.  Dual-backend callers never
    arrive here for an unsupported backend — AssertRunsOn drops it from the set
    first so their native arm still runs. }
  if not BackendRunnableOnHost(ABackend) then
    Ignore(BackendName(ABackend) +
      ' backend is not supported on this host target');
  UnitFile := FScratch + '/' + AUnitName + '.pas';
  { Write the user unit to the scratch dir so the unit loader resolves it. }
  WriteFile(UnitFile, AUnitSrc);

  { Native goes through the compiler's own CLI, with FScratch as an extra
    --unit-path so the just-written user unit resolves exactly as it does for
    QBE's manual TUnitLoader below. }
  if ABackend = beNative then
  begin
    Result := Self.CompileAndRunNativeCLI(ASrc, False, FScratch, AStdout,
                                          AExitCode);
    Exit
  end;
  Inc(FCounter);
  IRFile   := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile  := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile  := FScratch + '/t' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  QCG := nil;
  Loader := nil; Units := nil; SearchPaths := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FScratch);            { the written user unit }
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    QCG := TCodeGenQBE.Create();
    QCG.SetSymbolTable(Prog.SymbolTable);
    for I := 0 to Units.Count - 1 do
      QCG.AppendUnit(TUnit(Units.Items[I]));
    QCG.AppendProgram(Prog);
    Emitted := QCG.GetOutput()
  finally
    QCG.Free();
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, Emitted);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := LinkWithRTL(AsmFile, BinFile, ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
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
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  QCG:         TCodeGenQBE;
  CG:          ICodeGen;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Emitted:     string;
  IRFile, AsmFile, BinFile, ToolOut: string;
  Rc, I:       Integer;
begin
  Result := False;
  { Gate EVERY backend-taking entry point, so a caller cannot bypass the
    unsupported-backend skip.  Ignore raises EIgnoredTest: the test is REPORTED
    as skipped with a reason, not silently passed.  Dual-backend callers never
    arrive here for an unsupported backend — AssertRunsOn drops it from the set
    first so their native arm still runs. }
  if not BackendRunnableOnHost(beQBE) then
    Ignore(BackendName(beQBE) +
      ' backend is not supported on this host target');
  Inc(FCounter);
  IRFile   := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile  := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile  := FScratch + '/t' + IntToStr(FCounter);

  { Write both user units to the scratch dir so the loader resolves them.
    Filenames are derived from each unit's own `unit <name>;` header. }
  WriteFile(FScratch + '/' + UnitNameOf(AUnit1Src) + '.pas', AUnit1Src);
  WriteFile(FScratch + '/' + UnitNameOf(AUnit2Src) + '.pas', AUnit2Src);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  QCG := nil; CG := nil;
  Loader := nil; Units := nil; SearchPaths := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FScratch);
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    QCG := TCodeGenQBE.Create();
    CG  := QCG;
    CG.SetSymbolTable(Prog.SymbolTable);
    for I := 0 to Units.Count - 1 do
      CG.AppendUnit(TUnit(Units.Items[I]));
    CG.AppendProgram(Prog);
    Emitted := CG.GetOutput()
  finally
    QCG.Free();
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, Emitted);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := LinkWithRTL(AsmFile, BinFile, ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

end.
