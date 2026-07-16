{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - source discovery port + adapters.

  ISourceProvider is a driven (outbound) port: the engine asks it for the set
  of files to analyse and does not care how they were found.  Two adapters
  implement it:

    * TSingleFileSource   - one explicit .pas file.
    * TDirectoryScanSource - every *.pas under a directory tree.

  The directory adapter shells out to `find` (the RTL currently exposes no
  readdir), which is fine on the Linux/BSD targets BlaiseGuard builds for.
  Isolating that behind the port means a future native directory walker is a
  drop-in replacement with no change to the engine. }

unit Guard.Sources;

interface

uses
  SysUtils,
  Classes,
  Generics.Collections;

type
  ISourceProvider = interface
    { The .pas files to analyse, in discovery order. }
    function Collect: TList<string>;
    { Human description of what this provider points at, for messages. }
    function Describe: string;
  end;

  TSingleFileSource = class(ISourceProvider)
  private
    FPath: string;
  public
    constructor Create(const APath: string);
    function Collect: TList<string>;
    function Describe: string;
  end;

  TDirectoryScanSource = class(ISourceProvider)
  private
    FRoot: string;
  public
    constructor Create(const ARoot: string);
    function Collect: TList<string>;
    function Describe: string;
  end;

implementation

uses
  Process;

{ ---- TSingleFileSource ---- }

constructor TSingleFileSource.Create(const APath: string);
begin
  inherited Create();
  FPath := APath;
end;

function TSingleFileSource.Collect: TList<string>;
begin
  Result := TList<string>.Create();
  if FileExists(FPath) then
    Result.Add(FPath);
end;

function TSingleFileSource.Describe: string;
begin
  Result := 'file ' + FPath;
end;

{ ---- TDirectoryScanSource ---- }

constructor TDirectoryScanSource.Create(const ARoot: string);
begin
  inherited Create();
  FRoot := ExcludeTrailingPathDelimiter(ARoot);
end;

function TDirectoryScanSource.Collect: TList<string>;
var
  Proc:   TProcess;
  Chunk:  string;
  Output: string;
  Lines:  TStringList;
  I:      Integer;
  Line:   string;
begin
  Result := TList<string>.Create();

  { find <root> -type f -name '*.pas' - one path per line on stdout. }
  Proc := TProcess.Create(nil);
  Proc.Executable := 'sh';
  Proc.Parameters.Add('-c');
  Proc.Parameters.Add('find ''' + FRoot + ''' -type f -name ''*.pas''');
  Proc.Execute();
  Output := '';
  repeat
    Chunk  := Proc.ReadOutput();
    Output := Output + Chunk;
  until (Chunk = '') and (not Proc.Running);
  Proc.WaitOnExit();

  Lines := TStringList.Create();
  Lines.Text := Output;
  for I := 0 to Lines.Count - 1 do
  begin
    Line := Trim(Lines[I]);
    if Line <> '' then
      Result.Add(Line);
  end;
end;

function TDirectoryScanSource.Describe: string;
begin
  Result := 'directory ' + FRoot;
end;

end.
