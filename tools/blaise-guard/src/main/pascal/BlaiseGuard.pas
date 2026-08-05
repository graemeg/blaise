{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - a static analyzer for the Blaise language.

  This is the composition root: it wires the driving adapter (CLI) to the
  application core (engine) and the driven adapters (source provider, report
  formatter).  All policy lives in the units it composes; this file only
  assembles them and maps the result to a process exit code.

  Exit codes:
    0  clean, or findings below the --fail-on threshold
    1  findings at/above the --fail-on threshold
    2  usage error or unreadable configuration }

program BlaiseGuard;

uses
  SysUtils,
  Classes,
  Guard.Domain,
  Guard.Report,
  Guard.Config,
  Guard.Sources,
  Guard.Engine,
  Guard.Format,
  Guard.Format.Console,
  Guard.Format.Json,
  Guard.Format.Xml,
  Guard.Format.Html,
  Guard.Cli,
  Guard.Rules.All;   { pulls every rule unit in so they self-register }

const
  { Discovered by walking up from the analysis root; --config overrides. }
  CONFIG_NAME = 'blaise-guard.json';

{ The directory the analysis starts from — the scan root, the project file's
  directory, or the single file's directory.  Discovery walks up from here. }
function AnalysisRoot(AOpt: TCliOptions): string;
begin
  if AOpt.HasScan then
    Result := AOpt.ScanPath
  else if AOpt.HasProject then
    Result := ExtractFileDir(AOpt.ProjectPath)
  else if AOpt.FilePath <> '' then
    Result := ExtractFileDir(AOpt.FilePath)
  else
    Result := '';
  if Result = '' then
    Result := GetCurrentDir();
end;

{ Look for CONFIG_NAME in ADir and each ancestor, nearest first.  Returns ''
  when none is found.

  Why walk UP: the natural invocation is from the project root
  (`blaise-guard --scan compiler/src/main/pascal`), but it is equally natural
  to run it against a subdirectory from inside that subdirectory.  Both should
  find the project's one config.  Nearest-wins lets a subtree override. }
function DiscoverConfig(const ADir: string): string;
var
  Dir, Prev, Candidate: string;
begin
  Result := '';
  Dir := ExpandFileName(ADir);
  Prev := '';
  while (Dir <> '') and (Dir <> Prev) do
  begin
    Candidate := IncludeTrailingPathDelimiter(Dir) + CONFIG_NAME;
    if FileExists(Candidate) then
      Exit(Candidate);
    Prev := Dir;
    Dir  := ExtractFileDir(Dir);
  end;
end;

function BuildConfig(AOpt: TCliOptions): TGuardConfig;
var
  Found: string;
begin
  { An explicit --config always wins — discovery must never override what the
    caller named. }
  if AOpt.ConfigPath <> '' then
    Exit(TGuardConfig.LoadFromFile(AOpt.ConfigPath));

  Found := DiscoverConfig(AnalysisRoot(AOpt));
  if Found <> '' then
    Result := TGuardConfig.LoadFromFile(Found)
  else
    Result := TGuardConfig.Default();
end;

function BuildProvider(AOpt: TCliOptions): ISourceProvider;
begin
  if AOpt.HasScan then
    Result := TDirectoryScanSource.Create(AOpt.ScanPath)
  else if AOpt.HasProject then
    { MVP: analyse every source under the project file's directory.  Parsing
      the project's explicit unitPaths is a later refinement. }
    Result := TDirectoryScanSource.Create(ExtractFileDir(AOpt.ProjectPath))
  else if FileExists(AOpt.FilePath) then
    Result := TSingleFileSource.Create(AOpt.FilePath)
  else
    Result := TDirectoryScanSource.Create(AOpt.FilePath);
end;

function BuildFormatter(AOpt: TCliOptions): IReportFormatter;
begin
  { Strategy selection.  Colour applies only to the console renderer, and only
    when writing to a terminal (not a file). }
  case AOpt.OutputFormat of
    fmtJson: Result := TJsonFormatter.Create();
    fmtXml:  Result := TXmlFormatter.Create();
    fmtHtml: Result := THtmlFormatter.Create();
  else
    Result := TConsoleFormatter.Create(AOpt.UseColor and (AOpt.OutputPath = ''));
  end;
end;

procedure WriteOutput(const AText, APath: string);
var
  SL: TStringList;
begin
  if APath = '' then
    Write(AText)
  else
  begin
    SL := TStringList.Create();
    SL.Text := AText;
    SL.SaveToFile(APath);
    WriteLn('Report written to ' + APath);
  end;
end;

function ComputeExitCode(AReport: TReport; AFailOn: TFailOn): Integer;
begin
  Result := 0;
  case AFailOn of
    foWarning: if AReport.HasAtLeast(sevWarning) then Result := 1;
    foError:   if AReport.HasAtLeast(sevError)   then Result := 1;
  end;
end;

var
  Opt:       TCliOptions;
  Config:    TGuardConfig;
  Provider:  ISourceProvider;
  Engine:    TAnalysisEngine;
  Report:    TReport;
  Formatter: IReportFormatter;
begin
  Opt := ParseCommandLine();

  if Opt.ShowHelp then
  begin
    Write(UsageText());
    Halt(0);
  end;

  if not Opt.Valid then
  begin
    WriteLn('error: ' + Opt.ErrorText);
    WriteLn();
    Write(UsageText());
    Halt(2);
  end;

  try
    Config := BuildConfig(Opt);
  except
    on E: Exception do
    begin
      WriteLn('error: ' + E.Message);
      Halt(2);
    end;
  end;

  Provider  := BuildProvider(Opt);
  Engine    := TAnalysisEngine.Create(Config);
  Report    := Engine.Run(Provider);
  Formatter := BuildFormatter(Opt);

  WriteOutput(Formatter.Render(Report), Opt.OutputPath);

  Halt(ComputeExitCode(Report, Opt.FailOn));
end.
