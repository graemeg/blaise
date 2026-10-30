{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Unit tests for how BlaiseGuard turns its input options into the files to
  analyse (GitHub discussion #241):

    * `--project project.xml` -- a project file named WITHOUT a directory --
      scans the current directory.  It used to scan the empty path, and the
      `find` error text came back as a "source file" with a parse error.
    * A missing input is a usage error with a clear message, not an empty
      or bogus report.
    * The directory scan finds .pas files recursively, in a stable order. }

unit Guard.Input.Tests;

interface

uses
  blaise.testing;

type
  TGuardInputTests = class(TTestCase)
  private
    FRoot: string;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestProjectDir_BareFileNameIsCurrentDir;
    procedure TestProjectDir_KeepsDirectoryPart;
    procedure TestCheckInput_ExistingProjectIsAccepted;
    procedure TestCheckInput_MissingProjectIsRejected;
    procedure TestCheckInput_ProjectThatIsADirectoryIsRejected;
    procedure TestCheckInput_MissingScanDirIsRejected;
    procedure TestCheckInput_ExistingScanDirIsAccepted;
    procedure TestCheckInput_MissingFileIsRejected;
    procedure TestCheckInput_FileOrDirectoryPathIsAccepted;
    procedure TestScan_FindsPasFilesRecursivelyInOrder;
    procedure TestScan_EmptyRootIsCurrentDir;
    procedure TestScan_MissingRootRaises;
  end;

implementation

uses
  SysUtils,
  Generics.Collections,
  IO.Files,
  Guard.Cli,
  Guard.Sources;

procedure TGuardInputTests.SetUp;
begin
  FRoot := ExcludeTrailingPathDelimiter(GetTempDir()) + '/blaise-guard-input-' +
    IntToStr(GetProcessID());
  Exec('rm -rf ''' + FRoot + '''');
  ForceDirectories(FRoot + '/src/sub');
  WriteFile(FRoot + '/project.xml', '<project/>');
  WriteFile(FRoot + '/src/b.pas', 'x');
  WriteFile(FRoot + '/src/a.pas', 'x');
  WriteFile(FRoot + '/src/notes.txt', 'x');
  WriteFile(FRoot + '/src/sub/c.pas', 'x');
end;

procedure TGuardInputTests.TearDown;
begin
  Exec('rm -rf ''' + FRoot + '''');
end;

procedure TGuardInputTests.TestProjectDir_BareFileNameIsCurrentDir;
begin
  AssertEquals('.', ProjectDir('project.xml'));
end;

procedure TGuardInputTests.TestProjectDir_KeepsDirectoryPart;
begin
  AssertEquals('relative', 'tools/guard', ProjectDir('tools/guard/project.xml'));
  AssertEquals('dot', '.', ProjectDir('./project.xml'));
end;

procedure TGuardInputTests.TestCheckInput_ExistingProjectIsAccepted;
var
  Opt: TCliOptions;
begin
  Opt := TCliOptions.Create();
  Opt.HasProject := True;
  Opt.ProjectPath := FRoot + '/project.xml';
  AssertEquals('', CheckInput(Opt));
end;

procedure TGuardInputTests.TestCheckInput_MissingProjectIsRejected;
var
  Opt: TCliOptions;
begin
  Opt := TCliOptions.Create();
  Opt.HasProject := True;
  Opt.ProjectPath := FRoot + '/nope.xml';
  AssertContains('Project file not found', CheckInput(Opt));
  AssertContains('nope.xml', CheckInput(Opt));
end;

procedure TGuardInputTests.TestCheckInput_ProjectThatIsADirectoryIsRejected;
var
  Opt: TCliOptions;
begin
  Opt := TCliOptions.Create();
  Opt.HasProject := True;
  Opt.ProjectPath := FRoot + '/src';
  AssertContains('Project file not found', CheckInput(Opt));
end;

procedure TGuardInputTests.TestCheckInput_MissingScanDirIsRejected;
var
  Opt: TCliOptions;
begin
  Opt := TCliOptions.Create();
  Opt.HasScan := True;
  Opt.ScanPath := FRoot + '/missing';
  AssertContains('Directory not found', CheckInput(Opt));
end;

procedure TGuardInputTests.TestCheckInput_ExistingScanDirIsAccepted;
var
  Opt: TCliOptions;
begin
  Opt := TCliOptions.Create();
  Opt.HasScan := True;
  Opt.ScanPath := FRoot + '/src';
  AssertEquals('', CheckInput(Opt));
end;

procedure TGuardInputTests.TestCheckInput_MissingFileIsRejected;
var
  Opt: TCliOptions;
begin
  Opt := TCliOptions.Create();
  Opt.HasFile := True;
  Opt.FilePath := FRoot + '/src/missing.pas';
  AssertContains('No such file or directory', CheckInput(Opt));
end;

procedure TGuardInputTests.TestCheckInput_FileOrDirectoryPathIsAccepted;
var
  Opt: TCliOptions;
begin
  { A bare path may name a file or a directory to scan. }
  Opt := TCliOptions.Create();
  Opt.HasFile := True;
  Opt.FilePath := FRoot + '/src/a.pas';
  AssertEquals('file', '', CheckInput(Opt));
  Opt.FilePath := FRoot + '/src';
  AssertEquals('directory', '', CheckInput(Opt));
end;

procedure TGuardInputTests.TestScan_FindsPasFilesRecursivelyInOrder;
var
  L: TList<string>;
begin
  L := TDirectoryScanSource.Create(FRoot + '/src').Collect();
  AssertEquals('count', 3, Int32(L.Count));
  AssertEquals('0', FRoot + '/src/a.pas', L[0]);
  AssertEquals('1', FRoot + '/src/b.pas', L[1]);
  AssertEquals('2', FRoot + '/src/sub/c.pas', L[2]);
end;

procedure TGuardInputTests.TestScan_EmptyRootIsCurrentDir;
var
  Saved: string;
  L: TList<string>;
begin
  Saved := GetCurrentDir();
  SetCurrentDir(FRoot + '/src');
  try
    L := TDirectoryScanSource.Create('').Collect();
  finally
    SetCurrentDir(Saved);
  end;
  AssertEquals('count', 3, Int32(L.Count));
  AssertEquals('0', './a.pas', L[0]);
end;

procedure TGuardInputTests.TestScan_MissingRootRaises;
var
  Root: string;
begin
  Root := FRoot + '/missing';
  AssertRaises('EDirectoryNotFound',
    procedure
    begin
      TDirectoryScanSource.Create(Root).Collect();
    end);
end;

initialization
  RegisterTest(TGuardInputTests);

end.
