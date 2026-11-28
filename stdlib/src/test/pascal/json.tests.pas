{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Unit tests for the stdlib JSON library: Json.Writer (streaming), Json.Types
  (DOM), Json.Parser / Json.Reader (parsing), and round-tripping through them.
  In-process tests via blaise.testing — no toolchain spawning.

  Self-registers with the test registry via the initialization section; the
  test runner program pulls this unit in (through test.registry) and runs it. }

unit Json.Tests;

interface

uses
  SysUtils,
  blaise.testing,
  Json.Writer,
  Json.Types,
  Json.Parser,
  Json.Reader;

type
  TJsonTests = class(TTestCase)
  published
    procedure TestTyped_MembersAndElements;
    procedure TestTyped_WrongTypeOrMissingRaises;
    procedure TestFindPath;
    { Json.Writer }
    procedure TestWriter_Fields;
    procedure TestWriter_Array;
    procedure TestWriter_Nested;
    procedure TestWriter_Pretty;
    procedure TestWriter_Escape;
    procedure TestWriter_Raw;
    procedure TestWriter_Float;
    { Json.Types (DOM) }
    procedure TestDom_Build;
    procedure TestDom_Accessors;
    procedure TestDom_Empty;
    procedure TestDom_Remove;
    { Json.Parser / Json.Reader }
    procedure TestParse_Scalars;
    procedure TestParse_Escapes;
    procedure TestParse_Unicode;
    procedure TestParse_Nested;
    procedure TestParse_RoundTrip;
    procedure TestParse_Whitespace;
    procedure TestParse_Error;
    procedure TestParse_Trailing;
  end;

implementation

{ ---- Json.Writer ---- }

procedure TJsonTests.TestWriter_Fields;
var W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.BeginObject();
    W.WriteString('name', 'blaise');
    W.WriteInt('version', 12);
    W.WriteBool('stable', True);
    W.WriteNull('extra');
  W.EndObject();
  AssertEquals('compact object',
    '{"name":"blaise","version":12,"stable":true,"extra":null}', W.ToString());
  W.Free();
end;

procedure TJsonTests.TestWriter_Array;
var W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.BeginArray();
    W.WriteStringValue('a');
    W.WriteIntValue(1);
    W.WriteBoolValue(False);
  W.EndArray();
  AssertEquals('array elements', '["a",1,false]', W.ToString());
  W.Free();
end;

procedure TJsonTests.TestWriter_Nested;
var W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.BeginObject();
    W.WriteString('id', 'x');
    W.WriteKey('tags');
    W.BeginArray();
      W.WriteStringValue('p');
      W.WriteStringValue('q');
    W.EndArray();
  W.EndObject();
  AssertEquals('nested array', '{"id":"x","tags":["p","q"]}', W.ToString());
  W.Free();
end;

procedure TJsonTests.TestWriter_Pretty;
var W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.Pretty := True;
  W.BeginObject();
    W.WriteInt('a', 1);
    W.WriteKey('b');
    W.BeginArray();
      W.WriteIntValue(2);
    W.EndArray();
  W.EndObject();
  AssertEquals('pretty',
    '{' + #10 + '  "a": 1,' + #10 + '  "b": [' + #10 + '    2' + #10 +
    '  ]' + #10 + '}', W.ToString());
  W.Free();
end;

procedure TJsonTests.TestWriter_Escape;
var W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.WriteStringValue('a"b\' + #9 + #10 + 'c' + Chr(1));
  AssertEquals('escapes', '"a\"b\\\t\nc\u0001"', W.ToString());
  W.Free();
end;

procedure TJsonTests.TestWriter_Raw;
var W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.BeginObject();
    W.WriteKey('geo');
    W.WriteRaw('{"x":1,"y":2}');
  W.EndObject();
  AssertEquals('raw', '{"geo":{"x":1,"y":2}}', W.ToString());
  W.Free();
end;

procedure TJsonTests.TestWriter_Float;
var W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.WriteFloatValue(1.5);
  AssertEquals('float', '1.5', W.ToString());
  W.Free();
end;

{ ---- Json.Types (DOM) ---- }

procedure TJsonTests.TestDom_Build;
var Root: TJSONObject; Arr: TJSONArray;
begin
  Root := TJSONObject.Create();
  Root.Add('name', 'blaise');
  Root.Add('version', Int64(12));
  Root.Add('ratio', 1.5);
  Root.Add('stable', True);
  Arr := TJSONArray.Create();
  Arr.Add('DEBUG'); Arr.Add('UNIX');
  Root.Add('defines', Arr);
  Root.AddNull('extra');
  AssertEquals('dom compact',
    '{"name":"blaise","version":12,"ratio":1.5,"stable":true,' +
    '"defines":["DEBUG","UNIX"],"extra":null}', Root.AsJSON());
  Root.Free();
end;

procedure TJsonTests.TestDom_Accessors;
var Root: TJSONObject; v: Int64; s: string;
begin
  Root := TJSONObject.Create();
  Root.Add('version', Int64(12));
  Root.Add('name', 'blaise');
  v := Root.Find('version').AsInt64;
  AssertEquals('AsInt64', Int64(12), v);
  s := Root.Find('name').AsString;
  AssertEquals('AsString', 'blaise', s);
  AssertTrue('Contains', Root.Contains('name'));
  AssertFalse('not Contains', Root.Contains('nope'));
  AssertEquals('Count', 2, Root.Count);
  Root.Free();
end;

procedure TJsonTests.TestDom_Empty;
var O: TJSONObject; A: TJSONArray;
begin
  O := TJSONObject.Create();
  AssertEquals('empty object', '{}', O.AsJSON());
  O.Free();
  A := TJSONArray.Create();
  AssertEquals('empty array', '[]', A.AsJSON());
  A.Free();
end;

procedure TJsonTests.TestDom_Remove;
var Root: TJSONObject;
begin
  Root := TJSONObject.Create();
  Root.Add('a', Int64(1));
  Root.Add('b', Int64(2));
  AssertTrue('remove existing', Root.Remove('a'));
  AssertFalse('remove absent', Root.Remove('zzz'));
  AssertEquals('after remove', '{"b":2}', Root.AsJSON());
  Root.Free();
end;

{ ---- Json.Parser / Json.Reader ---- }

procedure TJsonTests.TestParse_Scalars;
var D: TJSONData; v: Int64; s: string; b: Boolean;
begin
  D := GetJSON('42');   v := D.AsInt64;    AssertEquals('int', Int64(42), v);  D.Free();
  D := GetJSON('"hi"'); s := D.AsString;   AssertEquals('str', 'hi', s);       D.Free();
  D := GetJSON('true'); b := D.AsBoolean;  AssertTrue('bool', b);              D.Free();
  D := GetJSON('null'); AssertTrue('null', D.IsNull());                        D.Free();
end;

procedure TJsonTests.TestParse_Escapes;
var D: TJSONData; s: string;
begin
  D := GetJSON('"say \"hi\"\tbye"');
  s := D.AsString;
  AssertEquals('unescape', 'say "hi"' + #9 + 'bye', s);
  D.Free();
end;

procedure TJsonTests.TestParse_Unicode;
var D: TJSONData; s: string;
begin
  { é is U+00E9 -> two UTF-8 bytes. }
  D := GetJSON('"' + Chr($C3) + Chr($A9) + '"');
  s := D.AsString;
  AssertEquals('é is 2 utf8 bytes', 2, Length(s));
  D.Free();
end;

procedure TJsonTests.TestParse_Nested;
var D: TJSONData; Obj: TJSONObject; v: Int64; b: Boolean;
begin
  D := GetJSON('{"a":1,"b":[2,3],"c":{"d":true}}');
  Obj := TJSONObject(D);
  v := Obj.Find('a').AsInt64;
  AssertEquals('a', Int64(1), v);
  AssertEquals('b count', 2, Obj.Find('b').Count);
  b := TJSONObject(Obj.Find('c')).Find('d').AsBoolean;
  AssertTrue('c.d', b);
  D.Free();
end;

procedure TJsonTests.TestParse_RoundTrip;
var D: TJSONData; src: string;
begin
  src := '{"n":"x","v":12,"r":1.5,"ok":true,"a":[1,2,3],"z":null}';
  D := GetJSON(src);
  AssertEquals('round-trip', src, D.AsJSON());
  D.Free();
end;

procedure TJsonTests.TestParse_Whitespace;
var D: TJSONData;
begin
  D := GetJSON('  {  "a" : 1 ,  "b" : [ 2 , 3 ]  }  ');
  AssertEquals('ws-tolerant', '{"a":1,"b":[2,3]}', D.AsJSON());
  D.Free();
end;

procedure TJsonTests.TestParse_Error;
var D: TJSONData; raised: Boolean;
begin
  raised := False;
  try
    D := GetJSON('{bad}');
    D.Free();
  except
    on E: EJSONParseError do raised := True;
  end;
  AssertTrue('malformed raises', raised);
end;

procedure TJsonTests.TestParse_Trailing;
var D: TJSONData; raised: Boolean;
begin
  raised := False;
  try
    D := GetJSON('1 2');
    D.Free();
  except
    on E: EJSONParseError do raised := True;
  end;
  AssertTrue('trailing content raises', raised);
end;


procedure TJsonTests.TestTyped_MembersAndElements;
var
  O: TJSONObject;
begin
  O := TJSONObject(GetJSON('{"name":"pasbuild","n":3,"ok":true,' +
    '"compiler":{"exe":"blaise"},"paths":["a","b",{"x":1},[7]]}'));
  AssertEquals('pasbuild', O.Strings['name']);
  AssertEquals(Int64(3), O.Integers['n']);
  AssertTrue(O.Booleans['ok']);
  AssertEquals('blaise', O.Objects['compiler'].Strings['exe']);
  AssertEquals(Int64(4), Int64(O.Arrays['paths'].Count));
  AssertEquals('b', O.Arrays['paths'].Strings[1]);
  AssertEquals(Int64(1), O.Arrays['paths'].Objects[2].Integers['x']);
  AssertEquals(Int64(7), O.Arrays['paths'].Arrays[3].Integers[0]);
  AssertEquals('public IndexOfName', Int64(1), Int64(O.IndexOfName('n')));
  AssertEquals(Int64(-1), Int64(O.IndexOfName('absent')));
end;

procedure TJsonTests.TestTyped_WrongTypeOrMissingRaises;
var
  O: TJSONObject;
  Raised: Int;
  S: string;
  X: TJSONData;
begin
  O := TJSONObject(GetJSON('{"n":3,"a":[true]}'));
  Raised := 0;
  try
    S := O.Strings['n'];
  except
    on E: EJSONTypeError do Raised := Raised + 1;
  end;
  try
    X := O.Objects['absent'];
  except
    on E: EJSONTypeError do Raised := Raised + 1;
  end;
  try
    S := O.Arrays['a'].Strings[0];
  except
    on E: EJSONTypeError do Raised := Raised + 1;
  end;
  AssertEquals('each raises EJSONTypeError', Int64(3), Int64(Raised));
end;

procedure TJsonTests.TestFindPath;
var
  D: TJSONData;
begin
  D := GetJSON('{"a":{"b":[10,{"c":"deep"}]},"top":"t"}');
  AssertEquals('t', D.FindPath('top').AsString);
  AssertEquals(Int64(10), D.FindPath('a.b[0]').AsInt64);
  AssertEquals('deep', D.FindPath('a.b[1].c').AsString);
  AssertTrue('empty path is the node', D.FindPath('') = D);
  AssertTrue('missing member', D.FindPath('a.x') = nil);
  AssertTrue('index out of range', D.FindPath('a.b[5]') = nil);
  AssertTrue('index on an object', D.FindPath('a[0]') = nil);
end;

initialization
  RegisterTest(TJsonTests);

end.
