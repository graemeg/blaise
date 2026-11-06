{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Unit tests for the stdlib TOML library: Toml.Writer (streaming), Toml.Types
  (document model and typed accessors), Toml.Parser / Toml.Reader (parsing
  and error reporting), and round-tripping through them.  In-process tests
  via blaise.testing.

  Self-registers with the test registry via the initialization section. }

unit Toml.Tests;

interface

uses
  SysUtils,
  blaise.testing,
  Toml.Writer,
  Toml.Types,
  Toml.Parser,
  Toml.Reader;

type
  TTomlTests = class(TTestCase)
  published
    { Toml.Writer }
    procedure TestWriter_KeyValues;
    procedure TestWriter_Sections;
    procedure TestWriter_InlineContainers;
    procedure TestWriter_KeyQuoting;
    procedure TestWriter_Escape;
    procedure TestWriter_Floats;
    { Toml.Types }
    procedure TestDom_BuildAndWrite;
    procedure TestDom_PutReplacesInPlace;
    procedure TestDom_Remove;
    procedure TestDom_TypedAccessors;
    procedure TestDom_WrongKindIsIgnored;
    procedure TestDom_EnsureTable;
    procedure TestDom_ArrayOfTablesWrite;
    procedure TestDom_EmptyTableWrite;
    { Toml.Parser / Toml.Reader }
    procedure TestParse_Scalars;
    procedure TestParse_BasicStrings;
    procedure TestParse_LiteralStrings;
    procedure TestParse_MultiLineStrings;
    procedure TestParse_Integers;
    procedure TestParse_Floats;
    procedure TestParse_DateTimes;
    procedure TestParse_Arrays;
    procedure TestParse_InlineTables;
    procedure TestParse_Tables;
    procedure TestParse_DottedAndQuotedKeys;
    procedure TestParse_ArrayOfTables;
    procedure TestParse_CommentsAndCRLF;
    procedure TestParse_EmptyDocument;
    { malformed input }
    procedure TestError_Garbage;
    procedure TestError_LineAndColumn;
    procedure TestError_DuplicateKey;
    procedure TestError_RedefinedTable;
    procedure TestError_TableVersusDottedKeys;
    procedure TestError_InlineTableIsSealed;
    procedure TestError_StaticArrayIsSealed;
    procedure TestError_BadValues;
    { round trip }
    procedure TestRoundTrip_Stable;
    procedure TestRoundTrip_KeepsUntouchedTables;
    procedure TestRoundTrip_PathKeys;
  end;

implementation

const
  NL = #10;

{ True when parsing ASrc raises ETOMLParseError. }
function ParseFails(const ASrc: string): Boolean;
var
  T: TTOMLTable;
begin
  Result := False;
  try
    T := GetTOML(ASrc);
    T.Free();
  except
    on E: ETOMLParseError do Result := True;
  end;
end;

{ ---- Toml.Writer ---- }

procedure TTomlTests.TestWriter_KeyValues;
var
  W: TTOMLWriter;
begin
  W := TTOMLWriter.Create();
  W.WriteString('name', 'facet');
  W.WriteInt('version', 12);
  W.WriteBool('stable', True);
  W.WriteFloat('ratio', 1.5);
  W.WriteKey('when');
  W.WriteRaw('1979-05-27');
  AssertEquals('key/values',
    'name = "facet"' + NL + 'version = 12' + NL + 'stable = true' + NL +
    'ratio = 1.5' + NL + 'when = 1979-05-27' + NL, W.ToString());
  W.Free();
end;

procedure TTomlTests.TestWriter_Sections;
var
  W: TTOMLWriter;
begin
  W := TTOMLWriter.Create();
  W.WriteInt('a', 1);
  W.BeginTable(['server', 'tls']);
  W.WriteBool('enabled', False);
  W.BeginArrayTable(['product']);
  W.WriteString('name', 'nail');
  AssertEquals('sections',
    'a = 1' + NL + NL + '[server.tls]' + NL + 'enabled = false' + NL + NL +
    '[[product]]' + NL + 'name = "nail"' + NL, W.ToString());
  W.Free();
end;

procedure TTomlTests.TestWriter_InlineContainers;
var
  W: TTOMLWriter;
begin
  W := TTOMLWriter.Create();
  W.WriteKey('ports');
  W.BeginArray();
  W.WriteIntValue(80);
  W.WriteIntValue(443);
  W.EndArray();
  W.WriteKey('point');
  W.BeginInlineTable();
  W.WriteInt('x', 1);
  W.WriteKey('tags');
  W.BeginArray();
  W.WriteStringValue('a');
  W.EndArray();
  W.EndInlineTable();
  W.WriteKey('none');
  W.BeginArray();
  W.EndArray();
  W.WriteKey('empty');
  W.BeginInlineTable();
  W.EndInlineTable();
  AssertEquals('inline containers',
    'ports = [80, 443]' + NL + 'point = { x = 1, tags = ["a"] }' + NL +
    'none = []' + NL + 'empty = {}' + NL, W.ToString());
  W.Free();
end;

procedure TTomlTests.TestWriter_KeyQuoting;
begin
  AssertEquals('bare', 'bare_key-1', TOMLFormatKey('bare_key-1'));
  AssertEquals('dot needs quotes', '"a.b"', TOMLFormatKey('a.b'));
  AssertEquals('space needs quotes', '"a b"', TOMLFormatKey('a b'));
  AssertEquals('empty key', '""', TOMLFormatKey(''));
  AssertEquals('path key',
    '"/data/Prism Launcher/1.21 \"Fabric\""',
    TOMLFormatKey('/data/Prism Launcher/1.21 "Fabric"'));
end;

procedure TTomlTests.TestWriter_Escape;
begin
  AssertEquals('quote+backslash', 'a\"b\\c', TOMLEscape('a"b\c'));
  AssertEquals('controls', '\t\n\r\b\f', TOMLEscape(#9#10#13#8#12));
  AssertEquals('other control', '\u0001\u007F', TOMLEscape(#1#127));
  AssertEquals('utf8 untouched', Chr($C3) + Chr($A9),
    TOMLEscape(Chr($C3) + Chr($A9)));
end;

procedure TTomlTests.TestWriter_Floats;
var
  Z: Float64;
begin
  Z := 0.0;
  AssertEquals('whole float keeps point', '3.0', TOMLFormatFloat(3.0));
  AssertEquals('fraction', '0.1', TOMLFormatFloat(0.1));
  AssertEquals('exponent', '1e+20', TOMLFormatFloat(1.0e20));
  AssertEquals('inf', 'inf', TOMLFormatFloat(1.0 / Z));
  AssertEquals('-inf', '-inf', TOMLFormatFloat(-1.0 / Z));
  AssertEquals('nan', 'nan', TOMLFormatFloat(Z / Z));
end;

{ ---- Toml.Types ---- }

procedure TTomlTests.TestDom_BuildAndWrite;
var
  Root, Srv: TTOMLTable;
  Arr: TTOMLArray;
begin
  Root := TTOMLTable.Create();
  Srv := TTOMLTable.Create();
  Srv.Put('host', 'localhost');
  Srv.Put('port', Int64(8080));
  Root.Put('server', Srv);           { a section, listed before plain keys }
  Root.Put('title', 'Facet');
  Arr := TTOMLArray.Create();
  Arr.Add('x');
  Arr.Add(Int64(2));
  Root.Put('mixed', Arr);
  Root.Put('debug', False);
  AssertEquals('plain keys first, then sections',
    'title = "Facet"' + NL + 'mixed = ["x", 2]' + NL + 'debug = false' + NL +
    NL + '[server]' + NL + 'host = "localhost"' + NL + 'port = 8080' + NL,
    Root.AsTOML());
  Root.Free();
end;

procedure TTomlTests.TestDom_PutReplacesInPlace;
var
  Root: TTOMLTable;
begin
  Root := TTOMLTable.Create();
  Root.Put('a', Int64(1));
  Root.Put('b', Int64(2));
  Root.Put('a', 'one');
  AssertEquals('count', 2, Root.Count);
  AssertEquals('order kept', 'a', Root.Names[0]);
  AssertEquals('replaced', 'a = "one"' + NL + 'b = 2' + NL, Root.AsTOML());
  Root.Free();
end;

procedure TTomlTests.TestDom_Remove;
var
  Root: TTOMLTable;
begin
  Root := TTOMLTable.Create();
  Root.Put('a', Int64(1));
  Root.Put('b', Int64(2));
  AssertTrue('remove existing', Root.Remove('a'));
  AssertFalse('remove absent', Root.Remove('zzz'));
  AssertFalse('gone', Root.Contains('a'));
  AssertEquals('after remove', 'b = 2' + NL, Root.AsTOML());
  Root.Free();
end;

procedure TTomlTests.TestDom_TypedAccessors;
var
  T: TTOMLTable;
  S: string;
  I: Int64;
  F: Float64;
  B: Boolean;
begin
  T := GetTOML('s = "str"' + NL + 'i = 42' + NL + 'f = 2.5' + NL +
    'b = true' + NL + 'd = 1979-05-27' + NL + '[sub]' + NL + 'x = 1' + NL +
    'arr = [1]' + NL);
  AssertTrue('string kind', T.Find('s').TOMLType = ttString);
  AssertTrue('integer kind', T.Find('i').TOMLType = ttInteger);
  AssertTrue('float kind', T.Find('f').TOMLType = ttFloat);
  AssertTrue('boolean kind', T.Find('b').TOMLType = ttBoolean);
  AssertTrue('date kind', T.Find('d').TOMLType = ttLocalDate);
  AssertTrue('table kind', T.Find('sub').TOMLType = ttTable);
  AssertTrue('IsString', T.Find('s').IsString());
  AssertTrue('IsBoolean', T.Find('b').IsBoolean());
  AssertTrue('IsDateTime', T.Find('d').IsDateTime());
  AssertTrue('IsTable', T.Find('sub').IsTable());
  AssertTrue('IsArray', T.FindTable('sub').Find('arr').IsArray());

  AssertTrue('TryGetString', T.TryGetString('s', S));
  AssertEquals('string value', 'str', S);
  AssertTrue('TryGetInt64', T.TryGetInt64('i', I));
  AssertEquals('int value', Int64(42), I);
  AssertTrue('TryGetFloat', T.TryGetFloat('f', F));
  AssertTrue('float value', F = 2.5);
  AssertTrue('TryGetFloat accepts integer', T.TryGetFloat('i', F));
  AssertTrue('integer as float', F = 42.0);
  AssertTrue('TryGetBoolean', T.TryGetBoolean('b', B));
  AssertTrue('bool value', B);
  AssertEquals('GetString', 'str', T.GetString('s', 'dflt'));
  AssertEquals('GetInt64', Int64(42), T.GetInt64('i', 0));
  AssertEquals('date text', '1979-05-27', T.GetString('d', ''));
  AssertEquals('AsString of date', '1979-05-27', T.Find('d').AsString);
  AssertTrue('FindTable', T.FindTable('sub') <> nil);
  AssertTrue('FindTable on scalar', T.FindTable('s') = nil);
  AssertTrue('FindArray', T.FindTable('sub').FindArray('arr') <> nil);
  AssertTrue('FindArray absent', T.FindArray('nope') = nil);
  T.Free();
end;

procedure TTomlTests.TestDom_WrongKindIsIgnored;
var
  T: TTOMLTable;
  B: Boolean;
  I: Int64;
begin
  T := GetTOML('automaticJava = "yes"' + NL + 'count = "12"' + NL);
  B := False;
  AssertFalse('string is not a Boolean', T.TryGetBoolean('automaticJava', B));
  AssertTrue('default kept', T.GetBoolean('automaticJava', True));
  AssertFalse('absent Boolean', T.TryGetBoolean('missing', B));
  AssertFalse('default kept for absent', T.GetBoolean('missing', False));
  AssertFalse('string is not an integer', T.TryGetInt64('count', I));
  AssertEquals('int default', Int64(7), T.GetInt64('count', 7));
  AssertEquals('string default for a non-string', 'd',
    T.GetString('missing', 'd'));
  T.Free();
end;

procedure TTomlTests.TestDom_EnsureTable;
var
  Root, A, A2: TTOMLTable;
begin
  Root := TTOMLTable.Create();
  A := Root.EnsureTable('a');
  A.Put('k', Int64(1));
  A2 := Root.EnsureTable('a');
  AssertTrue('same table returned', A = A2);
  A2.EnsureTable('b').Put('z', True);
  AssertEquals('nested ensure',
    '[a]' + NL + 'k = 1' + NL + NL + '[a.b]' + NL + 'z = true' + NL,
    Root.AsTOML());
  Root.Free();
end;

procedure TTomlTests.TestDom_ArrayOfTablesWrite;
var
  Root, P1, P2, Dims: TTOMLTable;
  Arr: TTOMLArray;
begin
  Root := TTOMLTable.Create();
  Arr := TTOMLArray.Create();
  P1 := TTOMLTable.Create();
  P1.Put('name', 'Hammer');
  Dims := TTOMLTable.Create();
  Dims.Put('w', Int64(3));
  P1.Put('dims', Dims);
  Arr.Add(P1);
  P2 := TTOMLTable.Create();
  P2.Put('name', 'Nail');
  Arr.Add(P2);
  Root.Put('products', Arr);
  AssertEquals('array of tables',
    '[[products]]' + NL + 'name = "Hammer"' + NL + NL +
    '[products.dims]' + NL + 'w = 3' + NL + NL +
    '[[products]]' + NL + 'name = "Nail"' + NL, Root.AsTOML());
  Root.Free();
end;

procedure TTomlTests.TestDom_EmptyTableWrite;
var
  Root, Outer: TTOMLTable;
begin
  Root := TTOMLTable.Create();
  Root.EnsureTable('empty');
  Outer := Root.EnsureTable('outer');
  Outer.EnsureTable('inner').Put('v', Int64(1));
  AssertEquals('empty table kept, implicit parent skipped',
    '[empty]' + NL + NL + '[outer.inner]' + NL + 'v = 1' + NL,
    Root.AsTOML());
  Root.Free();
end;

{ ---- Toml.Parser / Toml.Reader ---- }

procedure TTomlTests.TestParse_Scalars;
var
  T: TTOMLTable;
begin
  T := GetTOML('s = "hi"' + NL + 'i = 7' + NL + 't = true' + NL +
    'f = false' + NL + 'x = 1.25' + NL);
  AssertEquals('count', 5, T.Count);
  AssertEquals('string', 'hi', T.Find('s').AsString);
  AssertEquals('int', Int64(7), T.Find('i').AsInt64);
  AssertTrue('true', T.Find('t').AsBoolean);
  AssertFalse('false', T.Find('f').AsBoolean);
  AssertTrue('float', T.Find('x').AsFloat = 1.25);
  T.Free();
end;

procedure TTomlTests.TestParse_BasicStrings;
var
  T: TTOMLTable;
begin
  T := GetTOML('a = "tab\there \"q\" back\\slash"' + NL +
    'b = "\u00E9"' + NL + 'c = "\U0001F600"' + NL + 'd = ""' + NL +
    'e = "nl\nfeed\b\f\r"' + NL);
  AssertEquals('escapes', 'tab' + #9 + 'here "q" back\slash',
    T.GetString('a', ''));
  AssertEquals('\u escape', Chr($C3) + Chr($A9), T.GetString('b', ''));
  AssertEquals('\U escape', Chr($F0) + Chr($9F) + Chr($98) + Chr($80),
    T.GetString('c', ''));
  AssertEquals('empty', '', T.GetString('d', 'x'));
  AssertEquals('control escapes', 'nl' + #10 + 'feed' + #8 + #12 + #13,
    T.GetString('e', ''));
  T.Free();
end;

procedure TTomlTests.TestParse_LiteralStrings;
var
  T: TTOMLTable;
begin
  T := GetTOML('path = ''C:\Users\nodejs\templates''' + NL +
    'quoted = ''Tom "Dubs" Preston''' + NL);
  AssertEquals('no escapes', 'C:\Users\nodejs\templates',
    T.GetString('path', ''));
  AssertEquals('quotes kept', 'Tom "Dubs" Preston', T.GetString('quoted', ''));
  T.Free();
end;

procedure TTomlTests.TestParse_MultiLineStrings;
var
  T: TTOMLTable;
begin
  T := GetTOML(
    'a = """' + NL + 'Roses' + NL + 'Violets"""' + NL +
    'b = """The quick \' + NL + '    brown \' + NL + NL + '  fox."""' + NL +
    'c = """Here are two quotes: "". Done."""' + NL +
    'd = """ends with quotes"""""' + NL +
    'e = ''''''' + NL + 'raw \n line' + NL + '''''''' + NL +
    'f = ''''''That''s it''''''' + NL);
  AssertEquals('leading newline trimmed', 'Roses' + NL + 'Violets',
    T.GetString('a', ''));
  AssertEquals('line-ending backslash', 'The quick brown fox.',
    T.GetString('b', ''));
  AssertEquals('embedded quotes', 'Here are two quotes: "". Done.',
    T.GetString('c', ''));
  AssertEquals('trailing quotes', 'ends with quotes""', T.GetString('d', ''));
  AssertEquals('multi-line literal', 'raw \n line' + NL, T.GetString('e', ''));
  AssertEquals('apostrophe in literal', 'That''s it', T.GetString('f', ''));
  T.Free();
end;

procedure TTomlTests.TestParse_Integers;
var
  T: TTOMLTable;
begin
  T := GetTOML('a = +99' + NL + 'b = -17' + NL + 'c = 0' + NL +
    'd = 1_000_000' + NL + 'e = 0xDEAD_beef' + NL + 'f = 0o755' + NL +
    'g = 0b1101' + NL + 'h = 9223372036854775807' + NL +
    'i = -9223372036854775808' + NL + 'j = -0' + NL);
  AssertEquals('+99', Int64(99), T.GetInt64('a', 0));
  AssertEquals('-17', Int64(-17), T.GetInt64('b', 0));
  AssertEquals('0', Int64(0), T.GetInt64('c', 1));
  AssertEquals('underscores', Int64(1000000), T.GetInt64('d', 0));
  AssertEquals('hex', Int64($DEADBEEF), T.GetInt64('e', 0));
  AssertEquals('octal', Int64(493), T.GetInt64('f', 0));
  AssertEquals('binary', Int64(13), T.GetInt64('g', 0));
  AssertEquals('max', Int64(9223372036854775807), T.GetInt64('h', 0));
  AssertTrue('min', T.GetInt64('i', 0) < -9223372036854775807);
  AssertEquals('-0', Int64(0), T.GetInt64('j', 1));
  T.Free();
end;

procedure TTomlTests.TestParse_Floats;
var
  T: TTOMLTable;
  V: Float64;
begin
  T := GetTOML('a = 3.1415' + NL + 'b = -0.01' + NL + 'c = 5e+22' + NL +
    'd = 1e06' + NL + 'e = -2E-2' + NL + 'f = 6.626e-34' + NL +
    'g = 224_617.445_991' + NL + 'h = inf' + NL + 'i = -inf' + NL +
    'j = nan' + NL + 'k = +nan' + NL + 'l = +1.5' + NL);
  AssertTrue('3.1415', T.GetFloat('a', 0.0) = 3.1415);
  AssertTrue('-0.01', T.GetFloat('b', 0.0) = -0.01);
  AssertTrue('5e+22', T.GetFloat('c', 0.0) = 5e+22);
  AssertTrue('1e06', T.GetFloat('d', 0.0) = 1e06);
  AssertTrue('-2E-2', T.GetFloat('e', 0.0) = -2E-2);
  AssertTrue('6.626e-34', T.GetFloat('f', 0.0) = 6.626e-34);
  AssertTrue('underscores', T.GetFloat('g', 0.0) = 224617.445991);
  AssertTrue('float kind', T.Find('h').TOMLType = ttFloat);
  V := T.GetFloat('h', 0.0);
  AssertTrue('inf', (V > 1.0e308) and (V = V));
  V := T.GetFloat('i', 0.0);
  AssertTrue('-inf', V < -1.0e308);
  V := T.GetFloat('j', 0.0);
  AssertTrue('nan', V <> V);
  V := T.GetFloat('k', 0.0);
  AssertTrue('+nan', V <> V);
  AssertTrue('+1.5', T.GetFloat('l', 0.0) = 1.5);
  T.Free();
end;

procedure TTomlTests.TestParse_DateTimes;
var
  T: TTOMLTable;
begin
  T := GetTOML('odt1 = 1979-05-27T07:32:00Z' + NL +
    'odt2 = 1979-05-27T00:32:00.999999-07:00' + NL +
    'odt3 = 1979-05-27 07:32:00Z' + NL +
    'ldt = 1979-05-27T07:32:00' + NL +
    'ld = 1979-05-27' + NL +
    'lt1 = 07:32:00' + NL +
    'lt2 = 00:32:00.999999' + NL);
  AssertTrue('odt1 kind', T.Find('odt1').TOMLType = ttOffsetDateTime);
  AssertTrue('odt2 kind', T.Find('odt2').TOMLType = ttOffsetDateTime);
  AssertTrue('odt3 kind', T.Find('odt3').TOMLType = ttOffsetDateTime);
  AssertTrue('ldt kind', T.Find('ldt').TOMLType = ttLocalDateTime);
  AssertTrue('ld kind', T.Find('ld').TOMLType = ttLocalDate);
  AssertTrue('lt kind', T.Find('lt1').TOMLType = ttLocalTime);
  AssertTrue('lt2 kind', T.Find('lt2').TOMLType = ttLocalTime);
  AssertEquals('odt2 text', '1979-05-27T00:32:00.999999-07:00',
    T.Find('odt2').AsString);
  AssertEquals('odt3 text', '1979-05-27 07:32:00Z', T.Find('odt3').AsString);
  AssertEquals('lt2 text', '00:32:00.999999', T.Find('lt2').AsString);
  T.Free();
end;

procedure TTomlTests.TestParse_Arrays;
var
  T: TTOMLTable;
  A, Inner: TTOMLArray;
begin
  T := GetTOML('ints = [ 1, 2, 3 ]' + NL +
    'nested = [ [ 1, 2 ], ["a", ''b''] ]' + NL +
    'mixed = [ 0.1, "x", true, 1979-05-27 ]' + NL +
    'multi = [' + NL + '  1,  # first' + NL + NL + '  2, # second' + NL +
    ']' + NL + 'empty = []' + NL);
  A := T.FindArray('ints');
  AssertEquals('ints count', 3, A.Count);
  AssertEquals('ints[2]', Int64(3), A[2].AsInt64);
  A := T.FindArray('nested');
  AssertEquals('nested count', 2, A.Count);
  Inner := TTOMLArray(A[1]);
  AssertEquals('nested[1][1]', 'b', Inner[1].AsString);
  A := T.FindArray('mixed');
  AssertTrue('mixed[3] is a date', A[3].TOMLType = ttLocalDate);
  A := T.FindArray('multi');
  AssertEquals('multi-line + trailing comma', 2, A.Count);
  AssertEquals('empty', 0, T.FindArray('empty').Count);
  T.Free();
end;

procedure TTomlTests.TestParse_InlineTables;
var
  T, P: TTOMLTable;
begin
  T := GetTOML('name = { first = "Tom", last = "Preston-Werner" }' + NL +
    'point = { x = 1, y = 2, z.deep = true }' + NL +
    'empty = {}' + NL + 'nest = { a = { b = 1 } }' + NL);
  P := T.FindTable('name');
  AssertEquals('first', 'Tom', P.GetString('first', ''));
  AssertTrue('inline flag', P.IsInline);
  P := T.FindTable('point');
  AssertEquals('y', Int64(2), P.GetInt64('y', 0));
  AssertTrue('dotted key in inline table',
    P.FindTable('z').GetBoolean('deep', False));
  AssertEquals('empty inline', 0, T.FindTable('empty').Count);
  AssertEquals('nested inline', Int64(1),
    T.FindTable('nest').FindTable('a').GetInt64('b', 0));
  T.Free();
end;

procedure TTomlTests.TestParse_Tables;
var
  T, A: TTOMLTable;
begin
  T := GetTOML('top = 1' + NL + NL + '[table]' + NL + 'k = "v"' + NL + NL +
    '[a.b.c]' + NL + 'deep = true' + NL + NL + '[a]' + NL +
    'shallow = 2' + NL + NL + '[ x . "y" ]' + NL + 'z = 3' + NL);
  AssertEquals('top', Int64(1), T.GetInt64('top', 0));
  AssertEquals('table.k', 'v', T.FindTable('table').GetString('k', ''));
  A := T.FindTable('a');
  AssertTrue('a.b.c.deep',
    A.FindTable('b').FindTable('c').GetBoolean('deep', False));
  AssertEquals('implicit a defined later', Int64(2), A.GetInt64('shallow', 0));
  AssertEquals('spaced header', Int64(3),
    T.FindTable('x').FindTable('y').GetInt64('z', 0));
  T.Free();
end;

procedure TTomlTests.TestParse_DottedAndQuotedKeys;
var
  T, Fruit: TTOMLTable;
begin
  T := GetTOML('"127.0.0.1" = "ip"' + NL +
    '"character encoding" = "utf8"' + NL +
    '''key2'' = "lit"' + NL + '"" = "blank"' + NL +
    'site."google.com" = true' + NL + 'a . b = 1' + NL +
    '1234 = "digits"' + NL + '[fruit]' + NL + 'apple.colour = "red"' + NL +
    'apple.taste.sweet = true' + NL + NL + '[fruit.apple.texture]' + NL +
    'smooth = true' + NL);
  AssertEquals('quoted dots', 'ip', T.GetString('127.0.0.1', ''));
  AssertEquals('quoted space', 'utf8', T.GetString('character encoding', ''));
  AssertEquals('literal key', 'lit', T.GetString('key2', ''));
  AssertEquals('empty quoted key', 'blank', T.GetString('', ''));
  AssertTrue('dotted with quoted part',
    T.FindTable('site').GetBoolean('google.com', False));
  AssertEquals('whitespace around dot', Int64(1),
    T.FindTable('a').GetInt64('b', 0));
  AssertEquals('digit bare key', 'digits', T.GetString('1234', ''));
  Fruit := T.FindTable('fruit');
  AssertEquals('apple.colour', 'red',
    Fruit.FindTable('apple').GetString('colour', ''));
  AssertTrue('sub-table of a dotted table',
    Fruit.FindTable('apple').FindTable('texture').GetBoolean('smooth', False));
  T.Free();
end;

procedure TTomlTests.TestParse_ArrayOfTables;
var
  T, P: TTOMLTable;
  A: TTOMLArray;
begin
  T := GetTOML('[[products]]' + NL + 'name = "Hammer"' + NL + NL +
    '[products.dims]' + NL + 'w = 3' + NL + NL + '[[products]]' + NL + NL +
    '[[products]]' + NL + 'name = "Nail"' + NL + NL +
    '[[products.variants]]' + NL + 'size = 1' + NL);
  A := T.FindArray('products');
  AssertEquals('3 products', 3, A.Count);
  P := TTOMLTable(A[0]);
  AssertEquals('first name', 'Hammer', P.GetString('name', ''));
  AssertEquals('sub-table of first', Int64(3),
    P.FindTable('dims').GetInt64('w', 0));
  AssertEquals('empty middle', 0, TTOMLTable(A[1]).Count);
  P := TTOMLTable(A[2]);
  AssertEquals('nested array of tables', Int64(1),
    TTOMLTable(P.FindArray('variants')[0]).GetInt64('size', 0));
  T.Free();
end;

procedure TTomlTests.TestParse_CommentsAndCRLF;
var
  T: TTOMLTable;
begin
  T := GetTOML('# leading comment' + #13#10 + 'a = 1 # trailing' + #13#10 +
    '   ' + #13#10 + '[t] # header comment' + #13#10 + 'b = "x#y"' +
    #13#10);
  AssertEquals('a', Int64(1), T.GetInt64('a', 0));
  AssertEquals('hash in string', 'x#y', T.FindTable('t').GetString('b', ''));
  T.Free();
end;

procedure TTomlTests.TestParse_EmptyDocument;
var
  T: TTOMLTable;
begin
  T := GetTOML('');
  AssertEquals('empty', 0, T.Count);
  T.Free();
  T := GetTOML('# only a comment' + NL + NL);
  AssertEquals('comment only', 0, T.Count);
  AssertEquals('writes nothing', '', T.AsTOML());
  T.Free();
end;

{ ---- malformed input ---- }

procedure TTomlTests.TestError_Garbage;
var
  T: TTOMLTable;
  Raised: Boolean;
  Line, Col: Int;
begin
  Raised := False;
  Line := 0;
  Col := 0;
  try
    T := GetTOML('this is = = not toml');
    T.Free();
  except
    on E: ETOMLParseError do
    begin
      Raised := True;
      Line := E.Line;
      Col := E.Column;
    end;
  end;
  AssertTrue('garbage raises', Raised);
  AssertEquals('line', 1, Line);
  AssertEquals('column of "is"', 6, Col);
end;

procedure TTomlTests.TestError_LineAndColumn;
var
  T: TTOMLTable;
  Line, Col: Int;
  Msg: string;
begin
  Line := 0;
  Col := 0;
  Msg := '';
  try
    T := GetTOML('a = 1' + NL + '# c' + NL + 'b = = 2' + NL);
    T.Free();
  except
    on E: ETOMLParseError do
    begin
      Line := E.Line;
      Col := E.Column;
      Msg := E.Message;
    end;
  end;
  AssertEquals('line', 3, Line);
  AssertEquals('column', 5, Col);
  AssertTrue('message names the position',
    Pos('line 3, column 5', Msg) >= 0);
end;

procedure TTomlTests.TestError_DuplicateKey;
begin
  AssertTrue('duplicate key', ParseFails('a = 1' + NL + 'a = 2' + NL));
  AssertTrue('duplicate quoted key',
    ParseFails('spelling = 1' + NL + '"spelling" = 2' + NL));
  AssertTrue('key over table',
    ParseFails('a.b = 1' + NL + 'a = 2' + NL));
  AssertTrue('dotted over scalar',
    ParseFails('a = 1' + NL + 'a.b = 2' + NL));
  AssertTrue('duplicate in inline table', ParseFails('t = { a = 1, a = 2 }'));
end;

procedure TTomlTests.TestError_RedefinedTable;
begin
  AssertTrue('table twice',
    ParseFails('[a]' + NL + 'x = 1' + NL + '[a]' + NL + 'y = 2' + NL));
  AssertTrue('table over key',
    ParseFails('[a]' + NL + 'b = 1' + NL + '[a.b]' + NL));
  AssertTrue('array of tables over table',
    ParseFails('[a]' + NL + '[[a]]' + NL));
  AssertTrue('table over array of tables',
    ParseFails('[[a]]' + NL + '[a]' + NL));
  AssertTrue('empty header', ParseFails('[]' + NL));
  AssertTrue('unclosed header', ParseFails('[a' + NL));
end;

procedure TTomlTests.TestError_TableVersusDottedKeys;
begin
  AssertTrue('header over dotted-key table',
    ParseFails('[fruit]' + NL + 'apple.colour = "red"' + NL +
      '[fruit.apple]' + NL));
  AssertTrue('dotted keys into a header-defined table',
    ParseFails('[a.b]' + NL + 'x = 1' + NL + '[a]' + NL + 'b.y = 2' + NL));
end;

procedure TTomlTests.TestError_InlineTableIsSealed;
begin
  AssertTrue('header extends inline table',
    ParseFails('t = { a = 1 }' + NL + '[t]' + NL + 'b = 2' + NL));
  AssertTrue('header below inline table',
    ParseFails('t = { a = 1 }' + NL + '[t.sub]' + NL));
  AssertTrue('dotted key extends inline table',
    ParseFails('t = { a = 1 }' + NL + 't.b = 2' + NL));
  AssertTrue('newline inside inline table',
    ParseFails('t = { a = 1,' + NL + 'b = 2 }' + NL));
  AssertTrue('trailing comma in inline table', ParseFails('t = { a = 1, }'));
end;

procedure TTomlTests.TestError_StaticArrayIsSealed;
begin
  AssertTrue('[[x]] appends to a static array',
    ParseFails('x = [1, 2]' + NL + '[[x]]' + NL));
  AssertTrue('[x] over a static array',
    ParseFails('x = [{a = 1}]' + NL + '[x]' + NL));
end;

procedure TTomlTests.TestError_BadValues;
begin
  AssertTrue('missing value', ParseFails('a =' + NL));
  AssertTrue('missing equals', ParseFails('a 1' + NL));
  AssertTrue('no key', ParseFails('= 1' + NL));
  AssertTrue('two pairs on a line', ParseFails('a = 1 b = 2' + NL));
  AssertTrue('leading zero', ParseFails('a = 01' + NL));
  AssertTrue('double underscore', ParseFails('a = 1__0' + NL));
  AssertTrue('trailing underscore', ParseFails('a = 1_' + NL));
  AssertTrue('empty hex', ParseFails('a = 0x' + NL));
  AssertTrue('signed hex', ParseFails('a = +0x1' + NL));
  AssertTrue('overflow', ParseFails('a = 9223372036854775808' + NL));
  AssertTrue('float no int part', ParseFails('a = .5' + NL));
  AssertTrue('float no frac digits', ParseFails('a = 1.' + NL));
  AssertTrue('float bad exponent', ParseFails('a = 1e' + NL));
  AssertTrue('unterminated string', ParseFails('a = "abc' + NL));
  AssertTrue('newline in basic string', ParseFails('a = "ab' + NL + 'c"'));
  AssertTrue('bad escape', ParseFails('a = "\q"' + NL));
  AssertTrue('bare word value', ParseFails('a = yes' + NL));
  AssertTrue('unclosed array', ParseFails('a = [1, 2' + NL));
  AssertTrue('array missing comma', ParseFails('a = [1 2]' + NL));
  AssertTrue('bad month', ParseFails('a = 1979-13-27' + NL));
  AssertTrue('bad time', ParseFails('a = 25:00:00' + NL));
  AssertTrue('lone CR', ParseFails('a = 1' + #13 + 'b = 2'));
end;

{ ---- round trip ---- }

procedure TTomlTests.TestRoundTrip_Stable;
var
  T, T2: TTOMLTable;
  Src, Once: string;
begin
  Src := 'title = "TOML \"Example\""' + NL +
    'hex = 0xFF' + NL + 'f = 1e06' + NL + 'when = 1979-05-27 07:32:00Z' + NL +
    'arr = [1, [2, 3], { k = "v" }]' + NL + 'inl = { a = 1, b = { c = 2 } }' +
    NL + NL + '[owner]' + NL + 'name = "Tom"' + NL + NL + '[[fruit]]' + NL +
    'name = "apple"' + NL + NL + '[fruit.physical]' + NL +
    'colour = "red"' + NL + NL + '[[fruit]]' + NL + 'name = "banana"' + NL;
  T := GetTOML(Src);
  Once := T.AsTOML();
  AssertEquals('canonical source writes back unchanged', Src, Once);
  T2 := GetTOML(Once);
  AssertEquals('second pass identical', Once, T2.AsTOML());
  T.Free();
  T2.Free();
end;

procedure TTomlTests.TestRoundTrip_KeepsUntouchedTables;
var
  T, T2: TTOMLTable;
  Src, Expected: string;
begin
  Src := '# Facet settings' + NL +
    'automaticJava = true' + NL + 'theme = "dark"' + NL +
    'unknownKey = [1, 2]' + NL + NL +
    '[window]' + NL + 'width = 854' + NL + 'height = 480' + NL + NL +
    '[plugins.future.deeply.nested]' + NL + 'enabled = true' + NL +
    'when = 2026-11-06' + NL;
  T := GetTOML(Src);
  T.Put('theme', 'light');
  T.Remove('automaticJava');
  T.FindTable('window').Put('maximised', True);
  T.Put('newKey', Int64(5));
  Expected := 'theme = "light"' + NL + 'unknownKey = [1, 2]' + NL +
    'newKey = 5' + NL + NL +
    '[window]' + NL + 'width = 854' + NL + 'height = 480' + NL +
    'maximised = true' + NL + NL +
    '[plugins.future.deeply.nested]' + NL + 'enabled = true' + NL +
    'when = 2026-11-06' + NL;
  AssertEquals('changed document', Expected, T.AsTOML());
  T2 := GetTOML(T.AsTOML());
  AssertTrue('nested unknown table survives',
    T2.FindTable('plugins').FindTable('future').FindTable('deeply')
      .FindTable('nested').GetBoolean('enabled', False));
  AssertTrue('date kind survives',
    T2.FindTable('plugins').FindTable('future').FindTable('deeply')
      .FindTable('nested').Find('when').TOMLType = ttLocalDate);
  T.Free();
  T2.Free();
end;

procedure TTomlTests.TestRoundTrip_PathKeys;
var
  T, Inst, T2: TTOMLTable;
  PathKey, Text: string;
begin
  PathKey := '/data/Prism Launcher/1.21 "Fabric"';
  T := TTOMLTable.Create();
  Inst := T.EnsureTable('instances');
  Inst.EnsureTable(PathKey).Put('java', 'C:\Program Files\Java' + #9 + 'x');
  Text := T.AsTOML();
  AssertEquals('quoted path key in header',
    '[instances."/data/Prism Launcher/1.21 \"Fabric\""]' + NL +
    'java = "C:\\Program Files\\Java\tx"' + NL, Text);
  T2 := GetTOML(Text);
  AssertEquals('path key reads back', 'C:\Program Files\Java' + #9 + 'x',
    T2.FindTable('instances').FindTable(PathKey).GetString('java', ''));
  T.Free();
  T2.Free();
end;

initialization
  RegisterTest(TTomlTests);

end.
