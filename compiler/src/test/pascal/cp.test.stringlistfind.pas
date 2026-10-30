{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.stringlistfind;

{ In-process behaviour tests for TStringList.Find/IndexOf on UNSORTED lists.

  These pin the lookup contract that the compiler's symbol indexes rely on
  (FProcIndex, FMethodIndex, FUnitSymbols, FStrLits):

    - IndexOf returns the FIRST-ADDED index when duplicate keys exist
      (overload registration depends on first-wins ordering),
    - case-insensitive lists match case-insensitively; case-sensitive
      lists do not,
    - mutation (Delete, Insert, Strings[i] :=, Clear) is reflected by
      subsequent lookups,
    - Objects ride along with their strings.

  The list sizes deliberately exceed any lazy-index threshold so an
  accelerated lookup path (hash index) is exercised, not the small-list
  linear fallback.  The tests run directly against the TStringList compiled
  into the test runner — the same class the compiler itself uses. }

interface

uses
  Classes, SysUtils, blaise.testing;

type
  TStringListFindTests = class(TTestCase)
  private
    function MakeList(ACaseSensitive: Boolean; ACount: Int): TStringList;
  published
    procedure TestIndexOf_HitAndMiss_LargeUnsorted;
    procedure TestIndexOf_CaseInsensitive_Matches;
    procedure TestIndexOf_CaseSensitive_Distinguishes;
    procedure TestIndexOf_DuplicateKeys_ReturnsFirstAdded;
    procedure TestIndexOf_AfterAdd_FindsNewEntry;
    procedure TestIndexOf_AfterDelete_IndexesShift;
    procedure TestIndexOf_AfterStringsWrite_ReflectsNewValue;
    procedure TestIndexOf_AfterClear_MissesEverything;
    procedure TestFind_ReturnsSameIndexAsIndexOf;
    procedure TestObjects_FollowIndexOf;
    procedure TestIndexOf_EmptyString_Hit;
    procedure TestSorted_FindStillWorks;
  end;

implementation

function TStringListFindTests.MakeList(ACaseSensitive: Boolean;
  ACount: Int): TStringList;
var
  I: Int;
begin
  Result := TStringList.Create();
  Result.CaseSensitive := ACaseSensitive;
  for I := 0 to ACount - 1 do
    Result.Add('sym_' + IntToStr(I));
end;

procedure TStringListFindTests.TestIndexOf_HitAndMiss_LargeUnsorted;
var
  L: TStringList;
begin
  L := MakeList(False, 200);
  try
    AssertEquals('first', 0, L.IndexOf('sym_0'));
    AssertEquals('middle', 117, L.IndexOf('sym_117'));
    AssertEquals('last', 199, L.IndexOf('sym_199'));
    AssertEquals('miss', -1, L.IndexOf('sym_200'));
    AssertEquals('miss prefix', -1, L.IndexOf('sym_'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_CaseInsensitive_Matches;
var
  L: TStringList;
begin
  L := MakeList(False, 50);
  try
    AssertEquals('upper key', 33, L.IndexOf('SYM_33'));
    AssertEquals('mixed key', 7, L.IndexOf('Sym_7'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_CaseSensitive_Distinguishes;
var
  L: TStringList;
begin
  L := MakeList(True, 50);
  try
    AssertEquals('exact hit', 12, L.IndexOf('sym_12'));
    AssertEquals('case miss', -1, L.IndexOf('SYM_12'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_DuplicateKeys_ReturnsFirstAdded;
var
  L: TStringList;
  I: Int;
begin
  { Mirrors FProcIndex overload registration: the same name added several
    times; IndexOf must return the first-added occurrence. }
  L := TStringList.Create();
  L.CaseSensitive := False;
  try
    for I := 0 to 29 do
      L.Add('filler_' + IntToStr(I));
    L.AddObject('Overloaded', Pointer(1));   { index 30 }
    for I := 30 to 59 do
      L.Add('filler_' + IntToStr(I));
    L.AddObject('Overloaded', Pointer(2));   { index 61 }
    L.AddObject('overloaded', Pointer(3));   { index 62 — case-folded dup }
    AssertEquals('first added wins', 30, L.IndexOf('Overloaded'));
    AssertEquals('case-folded query', 30, L.IndexOf('OVERLOADED'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_AfterAdd_FindsNewEntry;
var
  L: TStringList;
begin
  L := MakeList(False, 100);
  try
    { Force a lookup first so any lazy index is built, then append. }
    AssertEquals('pre', 50, L.IndexOf('sym_50'));
    L.Add('late_arrival');
    AssertEquals('appended entry found', 100, L.IndexOf('late_arrival'));
    AssertEquals('old entry still found', 50, L.IndexOf('sym_50'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_AfterDelete_IndexesShift;
var
  L: TStringList;
begin
  L := MakeList(False, 100);
  try
    AssertEquals('pre', 80, L.IndexOf('sym_80'));
    L.Delete(10);
    AssertEquals('shifted down', 79, L.IndexOf('sym_80'));
    AssertEquals('deleted gone', -1, L.IndexOf('sym_10'));
    AssertEquals('below deletion unchanged', 5, L.IndexOf('sym_5'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_AfterStringsWrite_ReflectsNewValue;
var
  L: TStringList;
begin
  L := MakeList(False, 100);
  try
    AssertEquals('pre', 42, L.IndexOf('sym_42'));
    L.Strings[42] := 'renamed';
    AssertEquals('old key gone', -1, L.IndexOf('sym_42'));
    AssertEquals('new key found', 42, L.IndexOf('renamed'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_AfterClear_MissesEverything;
var
  L: TStringList;
begin
  L := MakeList(False, 100);
  try
    AssertEquals('pre', 3, L.IndexOf('sym_3'));
    L.Clear();
    AssertEquals('cleared', -1, L.IndexOf('sym_3'));
    L.Add('fresh');
    AssertEquals('fresh after clear', 0, L.IndexOf('fresh'));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestFind_ReturnsSameIndexAsIndexOf;
var
  L: TStringList;
  Idx: Int;
begin
  L := MakeList(False, 100);
  try
    AssertTrue('find hit', L.Find('sym_64', Idx));
    AssertEquals('find index', 64, Idx);
    AssertTrue('find miss', not L.Find('nope', Idx));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestObjects_FollowIndexOf;
var
  L: TStringList;
  I: Int;
begin
  L := TStringList.Create();
  L.CaseSensitive := False;
  try
    for I := 0 to 99 do
      L.AddObject('key_' + IntToStr(I), Pointer(I + 1000));
    I := L.IndexOf('key_77');
    AssertEquals('object rides along', 1077, Int32(L.Objects[I]));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestIndexOf_EmptyString_Hit;
var
  L: TStringList;
begin
  L := MakeList(False, 50);
  try
    AssertEquals('empty miss', -1, L.IndexOf(''));
    L.Add('');
    AssertEquals('empty hit', 50, L.IndexOf(''));
  finally
    L.Free();
  end;
end;

procedure TStringListFindTests.TestSorted_FindStillWorks;
var
  L: TStringList;
  I: Int;
begin
  L := TStringList.Create();
  L.CaseSensitive := False;
  L.Sorted := True;
  try
    for I := 0 to 99 do
      L.Add('key_' + IntToStr(I));
    AssertTrue('sorted hit', L.IndexOf('key_42') >= 0);
    AssertEquals('sorted miss', -1, L.IndexOf('absent'));
  finally
    L.Free();
  end;
end;

initialization
  RegisterTest(TStringListFindTests);

end.
