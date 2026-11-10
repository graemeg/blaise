{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ cp-migrate: report FPC / Delphi constructs that Blaise rejects, with the
  Blaise replacement.  Analysis and reporting only; it never edits a file.

    cp-migrate <file-or-directory>...

  A directory is scanned recursively for *.pas, *.pp, *.inc, *.lpr and
  *.dpr files.  Prints one line per finding (file:line:col: [RULE] message)
  and a summary.  Exit code: 0 no findings, 1 findings, 2 usage or I/O
  error. }

program MigrationAnalyser;

uses
  SysUtils, Classes, Generics.Collections, IO.Files, Migration.Rules;

function IsPascalSource(const APath: string): Boolean;
var
  Ext: string;
begin
  Ext := LowerCase(ExtractFileExt(APath));
  Result := (Ext = '.pas') or (Ext = '.pp') or (Ext = '.inc') or
    (Ext = '.lpr') or (Ext = '.dpr');
end;

procedure CollectSources(const APath: string; AOut: TStringList);
var
  Found: TList<string>;
  I: Int;
begin
  if DirectoryExists(APath) then
  begin
    Found := FindFiles(APath, '*');
    try
      for I := 0 to Found.Count - 1 do
        if IsPascalSource(Found[I]) then
          AOut.Add(Found[I]);
    finally
      Found.Free();
    end;
  end
  else
    AOut.Add(APath);
end;

function ReadSource(const APath: string): string;
var
  L: TStringList;
begin
  L := TStringList.Create();
  try
    L.LoadFromFile(APath);
    Result := L.Text;
  finally
    L.Free();
  end;
end;

var
  Files: TStringList;
  Report: TMigrationReport;
  I, Before, WithFindings: Int;
begin
  if ParamCount() < 1 then
  begin
    WriteLn(StdErr, 'usage: cp-migrate <file-or-directory>...');
    Halt(2);
  end;
  Files := TStringList.Create();
  Report := TMigrationReport.Create();
  try
    for I := 1 to ParamCount() do
      CollectSources(ParamStr(I), Files);
    Files.Sort();
    WithFindings := 0;
    for I := 0 to Files.Count - 1 do
    begin
      if not FileExists(Files.Strings[I]) then
      begin
        WriteLn(StdErr, 'cp-migrate: cannot read ', Files.Strings[I]);
        Halt(2);
      end;
      Before := Report.Count();
      AnalyseSource(ReadSource(Files.Strings[I]), Files.Strings[I], Report);
      if Report.Count() > Before then
        Inc(WithFindings);
    end;
    for I := 0 to Report.Count() - 1 do
      WriteLn(Report[I].AsText());
    WriteLn(Format('%d finding(s) in %d of %d file(s)',
      [Report.Count(), WithFindings, Files.Count]));
    if Report.Count() > 0 then
      Halt(1);
  finally
    Report.Free();
    Files.Free();
  end;
end.
