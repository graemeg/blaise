{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the Classes unit.  Self-registers via the initialization
  section.

  Focus: TStringList.Text accepts every line break: LF, CR LF and a lone CR.
  The getter writes the platform's LineEnding, so on Windows the setter
  must read CR LF back, and a file written on one platform must load on
  another without a CR left on each line. }

unit Classes.Tests;

interface

uses
  blaise.testing, Classes;

type
  TClassesTests = class(TTestCase)
  published
    procedure TestText_LineFeed;
    procedure TestText_CarriageReturnLineFeed;
    procedure TestText_LoneCarriageReturn;
    procedure TestText_EmptyLinesKept;
    procedure TestText_RoundTrip;
  end;

implementation

function Lines(const AText: string): TStringList;
begin
  Result := TStringList.Create();
  Result.Text := AText;
end;

procedure TClassesTests.TestText_LineFeed;
var
  L: TStringList;
begin
  L := Lines('a' + #10 + 'b' + #10);
  AssertEquals('count', 2, L.Count);
  AssertEquals('first', 'a', L[0]);
  AssertEquals('second', 'b', L[1]);
end;

procedure TClassesTests.TestText_CarriageReturnLineFeed;
var
  L: TStringList;
begin
  L := Lines('a' + #13#10 + 'b' + #13#10);
  AssertEquals('count', 2, L.Count);
  AssertEquals('no CR left on the line', 'a', L[0]);
  AssertEquals('second', 'b', L[1]);
  AssertEquals('found by value', 0, L.IndexOf('a'));
end;

procedure TClassesTests.TestText_LoneCarriageReturn;
var
  L: TStringList;
begin
  L := Lines('a' + #13 + 'b');
  AssertEquals('count', 2, L.Count);
  AssertEquals('first', 'a', L[0]);
  AssertEquals('second', 'b', L[1]);
end;

procedure TClassesTests.TestText_EmptyLinesKept;
var
  L: TStringList;
begin
  L := Lines('a' + #13#10 + #13#10 + 'b' + #10 + #10 + 'c');
  AssertEquals('count', 5, L.Count);
  AssertEquals('empty after CR LF', '', L[1]);
  AssertEquals('empty after LF', '', L[3]);
  AssertEquals('last', 'c', L[4]);
end;

procedure TClassesTests.TestText_RoundTrip;
var
  L, M: TStringList;
begin
  L := TStringList.Create();
  L.Add('one');
  L.Add('');
  L.Add('three');
  M := Lines(L.Text);
  AssertEquals('count', 3, M.Count);
  AssertEquals('first', 'one', M[0]);
  AssertEquals('empty', '', M[1]);
  AssertEquals('last', 'three', M[2]);
end;

initialization
  RegisterTest(TClassesTests);
end.
