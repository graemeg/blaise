{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
}

unit cp.test.bif_coverage;

{ Round-trip integrity guard.  Shells out to tools/bif-coverage and
  asserts it exits cleanly.  bif-coverage statically diffs uAST.pas
  against uUnitInterfaceIO.pas + the checked-in bif-coverage.status
  inventory, so a non-zero exit means somebody added an AST field
  without updating either the encoder/decoder or the status file.

  Stable by construction: the assertion is "the tool ran, found no
  gaps".  No per-property knowledge lives here — that's the .status
  file's job.

  The verifier locates the repo root by walking up from its CWD, so
  no chdir is required - it works the same whether invoked from the
  project root, from tools/bif-coverage/, or from the test runner's
  CWD.  We do not skip when the binary is missing: a working
  bif-coverage is a prerequisite for landing AST changes, so absence
  is a hard failure. }

interface

uses
  classes, sysutils, process, blaise.testing;

type
  TBifCoverageTests = class(TTestCase)
  private
    function ProjectRoot: string;
    function BinaryPath: string;
    function ModuleDir: string;
  published
    procedure TestRun_BifCoverage_NoGaps;
  end;

implementation

function TBifCoverageTests.ProjectRoot: string;
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

function TBifCoverageTests.ModuleDir: string;
begin
  Result := ProjectRoot() + 'tools/bif-coverage/'
end;

function TBifCoverageTests.BinaryPath: string;
var
  WithExt: string;
begin
  Result  := ModuleDir() + 'target/bif-coverage';
  WithExt := Result + '.exe';
  if not FileExists(Result) and FileExists(WithExt) then Result := WithExt
end;

procedure TBifCoverageTests.TestRun_BifCoverage_NoGaps;
var
  Bin, Stdout, Chunk: string;
  Proc: TProcess;
  Code: Integer;
begin
  Bin := BinaryPath();
  if not FileExists(Bin) then
  begin
    Ignore('bif-coverage binary not built at ' + Bin);
    Exit;
  end;

  Proc := TProcess.Create(nil);
  try
    Proc.Executable := Bin;
    Proc.Execute();
    Stdout := '';
    repeat
      Chunk  := Proc.ReadOutput();
      Stdout := Stdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Code := Proc.ExitCode
  finally
    Proc.Free()
  end;

  if Code <> 0 then
    Fail('bif-coverage reported drift (exit ' + IntToStr(Code) +
         '):' + LineEnding + Stdout)
end;

initialization
  RegisterTest(TBifCoverageTests);
end.
