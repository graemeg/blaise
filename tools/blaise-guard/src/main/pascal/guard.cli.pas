{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - command-line parsing (a driving adapter).

  Turns argv into a validated TCliOptions the composition root acts on.  Kept
  free of any analysis logic: it only decides *what* was asked for. }

unit Guard.Cli;

interface

type
  TFormatKind = (fmtConsole, fmtJson, fmtXml, fmtHtml);

  { --fail-on threshold: the minimum severity that forces a non-zero exit. }
  TFailOn = (foNever, foWarning, foError);

  TCliOptions = class
  public
    { Exactly one input source is chosen. }
    HasScan:     Boolean;
    ScanPath:    string;
    HasProject:  Boolean;
    ProjectPath: string;
    HasFile:     Boolean;
    FilePath:    string;

    ConfigPath:  string;   { '' = built-in defaults }
    OutputPath:  string;   { '' = stdout }
    OutputFormat: TFormatKind;
    FailOn:      TFailOn;
    UseColor:    Boolean;

    ShowHelp:    Boolean;
    Valid:       Boolean;
    ErrorText:   string;

    constructor Create;
  end;

{ Parse the process command line into options.  Never raises; on a bad
  invocation it returns options with Valid = False and ErrorText set. }
function ParseCommandLine: TCliOptions;

{ The --help / usage text. }
function UsageText: string;

implementation

uses
  SysUtils;

constructor TCliOptions.Create;
begin
  inherited Create();
  HasScan     := False;
  HasProject  := False;
  HasFile     := False;
  ConfigPath  := '';
  OutputPath  := '';
  OutputFormat := fmtConsole;
  FailOn      := foNever;
  UseColor    := True;
  ShowHelp    := False;
  Valid       := True;
  ErrorText   := '';
end;

function ParseFormat(const AValue: string; out AOut: TFormatKind): Boolean;
var
  V: string;
begin
  V := LowerCase(AValue);
  Result := True;
  if V = 'console' then AOut := fmtConsole
  else if V = 'json' then AOut := fmtJson
  else if V = 'xml'  then AOut := fmtXml
  else if V = 'html' then AOut := fmtHtml
  else Result := False;
end;

function ParseFailOn(const AValue: string; out AOut: TFailOn): Boolean;
var
  V: string;
begin
  V := LowerCase(AValue);
  Result := True;
  if V = 'warning' then AOut := foWarning
  else if V = 'error' then AOut := foError
  else Result := False;
end;

function ParseCommandLine: TCliOptions;
var
  Opt:    TCliOptions;
  I:      Integer;
  Arg:    string;
  Val:    string;
  Fmt:    TFormatKind;
  Fail:   TFailOn;

  { Consume the value that follows a --flag; report a clean error if missing. }
  function NextValue(const AFlag: string; out AValue: string): Boolean;
  begin
    if I >= ParamCount() then
    begin
      Opt.Valid     := False;
      Opt.ErrorText := 'Option ' + AFlag + ' requires a value';
      Exit(False);
    end;
    Inc(I);
    AValue := ParamStr(I);
    Result := True;
  end;

begin
  Opt := TCliOptions.Create();
  I := 1;
  while I <= ParamCount() do
  begin
    Arg := ParamStr(I);

    if (Arg = '--help') or (Arg = '-h') then
      Opt.ShowHelp := True

    else if Arg = '--no-color' then
      Opt.UseColor := False

    else if Arg = '--scan' then
    begin
      if not NextValue('--scan', Val) then Exit(Opt);
      Opt.HasScan  := True;
      Opt.ScanPath := Val;
    end

    else if Arg = '--project' then
    begin
      if not NextValue('--project', Val) then Exit(Opt);
      Opt.HasProject  := True;
      Opt.ProjectPath := Val;
    end

    else if Arg = '--config' then
    begin
      if not NextValue('--config', Val) then Exit(Opt);
      Opt.ConfigPath := Val;
    end

    else if Arg = '--output' then
    begin
      if not NextValue('--output', Val) then Exit(Opt);
      Opt.OutputPath := Val;
    end

    else if Arg = '--format' then
    begin
      if not NextValue('--format', Val) then Exit(Opt);
      if not ParseFormat(Val, Fmt) then
      begin
        Opt.Valid := False;
        Opt.ErrorText := 'Unknown --format value: ' + Val;
        Exit(Opt);
      end;
      Opt.OutputFormat := Fmt;
    end

    else if Arg = '--fail-on' then
    begin
      if not NextValue('--fail-on', Val) then Exit(Opt);
      if not ParseFailOn(Val, Fail) then
      begin
        Opt.Valid := False;
        Opt.ErrorText := 'Unknown --fail-on value: ' + Val;
        Exit(Opt);
      end;
      Opt.FailOn := Fail;
    end

    else if (Length(Arg) >= 2) and (Arg[0] = '-') and (Arg[1] = '-') then
    begin
      Opt.Valid := False;
      Opt.ErrorText := 'Unknown option: ' + Arg;
      Exit(Opt);
    end

    else
    begin
      { A bare positional path: a single source file (or a directory, which the
        composition root resolves to a scan). }
      Opt.HasFile  := True;
      Opt.FilePath := Arg;
    end;

    Inc(I);
  end;

  { A help request short-circuits input validation. }
  if Opt.ShowHelp then
    Exit(Opt);

  if not (Opt.HasScan or Opt.HasProject or Opt.HasFile) then
  begin
    Opt.Valid := False;
    Opt.ErrorText := 'No input given (use --scan DIR, --project FILE, or a path)';
  end;

  Result := Opt;
end;

function UsageText: string;
const
  NL = #10;
begin
  Result :=
    'blaise-guard - static analyzer for the Blaise language' + NL +
    NL +
    'Usage:' + NL +
    '  blaise-guard --scan <dir>        Analyze every *.pas under a directory' + NL +
    '  blaise-guard --project <xml>     Analyze the sources of a PasBuild project' + NL +
    '  blaise-guard <file.pas>          Analyze a single source file' + NL +
    NL +
    'Options:' + NL +
    '  --config <file>    Rules configuration (JSON); default = built-in' + NL +
    '  --output <file>    Write the report to a file instead of stdout' + NL +
    '  --format <fmt>     console (default), json, xml, or html' + NL +
    '  --fail-on <sev>    Exit non-zero when >= warning|error findings exist' + NL +
    '  --no-color         Disable ANSI colour in console output' + NL +
    '  -h, --help         Show this help' + NL;
end;

end.
