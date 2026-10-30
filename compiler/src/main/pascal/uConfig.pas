{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uConfig;

interface

uses
  Classes, SysUtils;

function FindConfigFile: string;

{ Parse blaise.cfg lines.  Recognised keys (KEY=VALUE, '#' comments, blank lines
  ignored): `unit-path=<dir>` appends to APaths; `rtl-src=<dir>` sets ARtlSrc.
  A relative VALUE is resolved against ABaseDir (the config file's directory).
  ARtlSrc is only written when an rtl-src line is present (left unchanged
  otherwise), so a caller can pre-seed it and let the config override only if
  set. }
procedure ParseConfigLines(ALines: TStringList; const ABaseDir: string;
  APaths: TStringList; var ARtlSrc: string); overload;

{ Convenience overload for callers that only want unit-paths (ignores rtl-src). }
procedure ParseConfigLines(ALines: TStringList; const ABaseDir: string;
  APaths: TStringList); overload;

{ Load the resolved blaise.cfg: appends unit-path entries to APaths and returns
  any rtl-src via ARtlSrc (unchanged if the file has none / no file). }
procedure LoadConfigPaths(APaths: TStringList; var ARtlSrc: string);

implementation

function FindConfigFile: string;
var
  BinDir: string;
  Home:   string;
begin
  BinDir := IncludeTrailingPathDelimiter(ExtractFilePath(ParamStr(0)));
  Result := BinDir + 'blaise.cfg';
  if FileExists(Result) then
    Exit;
  Home := GetEnvironmentVariable('HOME');
  if Home <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Home) + '.blaise.cfg';
    if FileExists(Result) then
      Exit;
  end;
  Result := '';
end;

{ Resolve a blaise.cfg path value.  An absolute path (leading '/') is used as
  is; a leading '~' or '~/' expands to $HOME (so a config can name paths under
  the user's home directory); anything else is relative and resolved against
  ABaseDir (the config file's own directory). }
function ResolveCfgPath(const AValue, ABaseDir: string): string;
var
  Home: string;
begin
  if Length(AValue) = 0 then
    Exit('');
  { Home expansion: '~' alone, or a '~/...' prefix. }
  if (Copy(AValue, 0, 1) = '~') and
     ((Length(AValue) = 1) or (Copy(AValue, 1, 1) = '/')) then
  begin
    Home := GetEnvironmentVariable('HOME');
    if Home <> '' then
    begin
      if Length(AValue) = 1 then
        Exit(Home);
      { drop the '~', keep the rest (which starts with '/') }
      Exit(IncludeTrailingPathDelimiter(Home) + Copy(AValue, 2, Length(AValue)));
    end;
    { No $HOME — leave '~' untouched rather than mis-resolving. }
    Exit(AValue);
  end;
  if Copy(AValue, 0, 1) = '/' then
    Exit(AValue);
  Result := IncludeTrailingPathDelimiter(ABaseDir) + AValue;
end;

procedure ParseConfigLines(ALines: TStringList; const ABaseDir: string;
  APaths: TStringList; var ARtlSrc: string);
var
  I:     Int;
  Line:  string;
  EqPos: Int;
  Key:   string;
  Value: string;
begin
  for I := 0 to ALines.Count - 1 do
  begin
    Line := Trim(ALines.Strings[I]);
    if Length(Line) = 0 then
      Continue;
    if Copy(Line, 0, 1) = '#' then
      Continue;
    EqPos := Pos('=', Line);
    if EqPos < 0 then
      Continue;
    Key   := Trim(Copy(Line, 0, EqPos));
    Value := Trim(Copy(Line, EqPos + 1, Length(Line)));
    if SameText(Key, 'unit-path') then
      APaths.Add(ResolveCfgPath(Value, ABaseDir))
    else if SameText(Key, 'rtl-src') then
      ARtlSrc := ResolveCfgPath(Value, ABaseDir)
    else
      ; { silently skip unrecognised keys }
  end;
end;

procedure ParseConfigLines(ALines: TStringList; const ABaseDir: string;
  APaths: TStringList);
var
  IgnoredRtlSrc: string;
begin
  IgnoredRtlSrc := '';
  ParseConfigLines(ALines, ABaseDir, APaths, IgnoredRtlSrc);
end;

procedure LoadConfigPaths(APaths: TStringList; var ARtlSrc: string);
var
  CfgFile: string;
  Lines:   TStringList;
  BaseDir: string;
begin
  CfgFile := FindConfigFile();
  if CfgFile = '' then
    Exit;
  Lines := TStringList.Create();
  try
    Lines.LoadFromFile(CfgFile);
    BaseDir := ExtractFilePath(CfgFile);
    ParseConfigLines(Lines, BaseDir, APaths, ARtlSrc);
  finally
    Lines.Free();
  end;
end;

end.
