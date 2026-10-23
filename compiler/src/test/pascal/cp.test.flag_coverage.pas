{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
}

unit cp.test.flag_coverage;

{ Backend annotation-flag drift guard.  Shells out to tools/flag-coverage
  and asserts it exits cleanly.  flag-coverage counts how often each
  backend reads each semantic annotation flag on the AST node classes
  codegen dispatches on, and compares the counts against the checked-in
  flag-coverage.status baseline.  A non-zero exit means a backend lost
  an arm for a flag (a DROP), or a new flag has no baseline entry yet.

  Before this test existed the tool ran only by hand, and its baseline
  drifted without anyone noticing.  Like the bif-coverage
  guard, the assertion is "the tool ran, found no drops"; the counts
  themselves live in the .status file.  The test is ignored when the
  binary has not been built. }

interface

uses
  classes, sysutils, process, blaise.testing;

type
  TFlagCoverageTests = class(TTestCase)
  private
    function ProjectRoot: string;
    function BinaryPath: string;
    function ModuleDir: string;
  published
    procedure TestRun_FlagCoverage_NoDrops;
  end;

implementation

function TFlagCoverageTests.ProjectRoot: string;
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

function TFlagCoverageTests.ModuleDir: string;
begin
  Result := ProjectRoot() + 'tools/flag-coverage/'
end;

function TFlagCoverageTests.BinaryPath: string;
var
  WithExt: string;
begin
  Result  := ModuleDir() + 'target/flag-coverage';
  WithExt := Result + '.exe';
  if not FileExists(Result) and FileExists(WithExt) then Result := WithExt
end;

procedure TFlagCoverageTests.TestRun_FlagCoverage_NoDrops;
var
  Bin, Stdout, Chunk: string;
  Proc: TProcess;
  Code: Integer;
begin
  Bin := BinaryPath();
  if not FileExists(Bin) then
  begin
    Ignore('flag-coverage binary not built at ' + Bin);
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
    Fail('flag-coverage reported a drop (exit ' + IntToStr(Code) +
         '):' + LineEnding + Stdout)
end;

initialization
  RegisterTest(TFlagCoverageTests);
end.
