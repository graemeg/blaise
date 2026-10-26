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

  The directory adapter walks the tree with IO.Files.FindFiles: recursive,
  in a stable order, and no shell or `find` (which Windows lacks, and whose
  error text a shell-out once returned as a "source file" -- discussion
  #241). }

unit Guard.Sources;

interface

uses
  SysUtils,
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
    { An empty ARoot is the current directory. }
    constructor Create(const ARoot: string);
    { Every *.pas under the root.  Raises EDirectoryNotFound (IO.Files) when
      the root is not a directory. }
    function Collect: TList<string>;
    function Describe: string;
  end;

implementation

uses
  IO.Files;

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
  FRoot := ARoot;
  if FRoot = '' then
    FRoot := '.';
end;

function TDirectoryScanSource.Collect: TList<string>;
begin
  Result := FindFiles(FRoot, '*.pas');
end;

function TDirectoryScanSource.Describe: string;
begin
  Result := 'directory ' + FRoot;
end;

end.
