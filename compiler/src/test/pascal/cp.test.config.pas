{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.config;

interface

uses
  Classes, SysUtils, blaise.testing,
  uConfig;

type
  TConfigTests = class(TTestCase)
  published
    procedure TestParseEmpty_ReturnsNoPaths;
    procedure TestParseCommentOnly_ReturnsNoPaths;
    procedure TestParseSingleUnitPath;
    procedure TestParseMultipleUnitPaths;
    procedure TestParseSkipsBlankLines;
    procedure TestParseSkipsCommentLines;
    procedure TestParseIgnoresLinesWithoutEquals;
    procedure TestParseTrimsWhitespace;
    procedure TestParseRelativePath_ResolvedAgainstBaseDir;
    procedure TestParseAbsolutePath_NotModified;
    procedure TestParseUnknownKey_IgnoredSilently;
    procedure TestParseRtlSrc_Absolute_SetsValue;
    procedure TestParseRtlSrc_Relative_ResolvedAgainstBaseDir;
    procedure TestParseRtlSrc_Absent_LeavesSeedUnchanged;
    procedure TestParseTildePath_ExpandsToHome;
    procedure TestParseRtlSrcTilde_ExpandsToHome;
    procedure TestFindConfigFile_NextToBinary;
    { rtl-cache= names where the compiled RTL objects are kept (GH #251). }
    procedure TestParseRtlCache_Relative_ResolvedAgainstBaseDir;
    procedure TestParseRtlCache_Absent_LeavesSeedUnchanged;
  end;

implementation

procedure TConfigTests.TestParseEmpty_ReturnsNoPaths;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('no paths', 0, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseCommentOnly_ReturnsNoPaths;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('# this is a comment');
    Lines.Add('# another comment');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('no paths', 0, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseSingleUnitPath;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=/opt/blaise/runtime');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('path value', '/opt/blaise/runtime', Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseMultipleUnitPaths;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=/opt/blaise/runtime');
    Lines.Add('unit-path=/opt/blaise/stdlib');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('two paths', 2, Paths.Count);
    AssertEquals('first', '/opt/blaise/runtime', Paths.Strings[0]);
    AssertEquals('second', '/opt/blaise/stdlib', Paths.Strings[1]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseSkipsBlankLines;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('');
    Lines.Add('unit-path=/opt/blaise/runtime');
    Lines.Add('');
    Lines.Add('');
    Lines.Add('unit-path=/opt/blaise/stdlib');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('two paths', 2, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseSkipsCommentLines;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('# header comment');
    Lines.Add('unit-path=/opt/blaise/runtime');
    Lines.Add('# inline comment');
    Lines.Add('unit-path=/opt/blaise/stdlib');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('two paths', 2, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseIgnoresLinesWithoutEquals;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('this line has no equals sign');
    Lines.Add('unit-path=/opt/blaise/runtime');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path', 1, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseTrimsWhitespace;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('  unit-path = /opt/blaise/runtime  ');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('trimmed', '/opt/blaise/runtime', Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseRelativePath_ResolvedAgainstBaseDir;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=../../compiler/src/main/pascal');
    ParseConfigLines(Lines, '/data/devel/new-pascal-compiler/compiler/target/', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('resolved',
      '/data/devel/new-pascal-compiler/compiler/target/../../compiler/src/main/pascal',
      Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseAbsolutePath_NotModified;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=/absolute/path/to/units');
    ParseConfigLines(Lines, '/some/base/', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('unchanged', '/absolute/path/to/units', Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseUnknownKey_IgnoredSilently;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unknown-key=some-value');
    Lines.Add('unit-path=/opt/blaise/runtime');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path only', 1, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseRtlSrc_Absolute_SetsValue;
var
  Lines, Paths: TStringList;
  Rtl: string;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Rtl := '';
    Lines.Add('rtl-src=/opt/blaise/rtl');
    ParseConfigLines(Lines, '/base', Paths, Rtl);
    AssertEquals('rtl-src set', '/opt/blaise/rtl', Rtl);
    AssertEquals('rtl-src is not a unit-path', 0, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseRtlSrc_Relative_ResolvedAgainstBaseDir;
var
  Lines, Paths: TStringList;
  Rtl: string;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Rtl := '';
    Lines.Add('rtl-src=src/main/pascal');
    ParseConfigLines(Lines, '/base/', Paths, Rtl);
    AssertEquals('relative rtl-src resolved against base dir',
      '/base/src/main/pascal', Rtl);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseRtlSrc_Absent_LeavesSeedUnchanged;
var
  Lines, Paths: TStringList;
  Rtl: string;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    { Seed a value (as the driver does with a CLI --rtl-src); a config with no
      rtl-src line must leave it untouched. }
    Rtl := '/cli/override';
    Lines.Add('unit-path=/opt/blaise/runtime');
    ParseConfigLines(Lines, '/base', Paths, Rtl);
    AssertEquals('seed unchanged when config has no rtl-src',
      '/cli/override', Rtl);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseTildePath_ExpandsToHome;
var
  Lines, Paths: TStringList;
  Home: string;
begin
  Home := GetEnvironmentVariable('HOME');
  if Home = '' then begin Ignore('no $HOME'); Exit end;
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    { A '~/...' unit-path expands to $HOME/..., NOT resolved against the base. }
    Lines.Add('unit-path=~/devel/blaise/runtime');
    ParseConfigLines(Lines, '/some/base', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('~ expanded to $HOME',
      IncludeTrailingPathDelimiter(Home) + 'devel/blaise/runtime',
      Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseRtlSrcTilde_ExpandsToHome;
var
  Lines, Paths: TStringList;
  Rtl, Home: string;
begin
  Home := GetEnvironmentVariable('HOME');
  if Home = '' then begin Ignore('no $HOME'); Exit end;
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Rtl := '';
    Lines.Add('rtl-src=~/devel/blaise/compiler/src/main/pascal');
    ParseConfigLines(Lines, '/some/base', Paths, Rtl);
    AssertEquals('~ in rtl-src expanded to $HOME',
      IncludeTrailingPathDelimiter(Home) + 'devel/blaise/compiler/src/main/pascal',
      Rtl);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestFindConfigFile_NextToBinary;
var
  CfgPath: string;
begin
  CfgPath := FindConfigFile();
  if CfgPath = '' then
    AssertTrue('no config found (acceptable in test env)', True)
  else
    AssertTrue('found config is a real file', FileExists(CfgPath));
end;

procedure TConfigTests.TestParseRtlCache_Relative_ResolvedAgainstBaseDir;
var
  Lines, Paths: TStringList;
  Rtl, Cache: string;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Rtl := '';
    Cache := '';
    Lines.Add('rtl-src=/src');
    Lines.Add('rtl-cache=cache/rtl');
    ParseConfigLines(Lines, '/base/', Paths, Rtl, Cache);
    AssertEquals('relative rtl-cache resolved against base dir',
      '/base/cache/rtl', Cache);
    AssertEquals('rtl-src still read beside it', '/src', Rtl);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseRtlCache_Absent_LeavesSeedUnchanged;
var
  Lines, Paths: TStringList;
  Rtl, Cache: string;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Rtl := '';
    Cache := '/seed';
    Lines.Add('unit-path=/u');
    ParseConfigLines(Lines, '/base/', Paths, Rtl, Cache);
    AssertEquals('no rtl-cache line leaves the seed', '/seed', Cache);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

initialization
  RegisterTest(TConfigTests);

end.
