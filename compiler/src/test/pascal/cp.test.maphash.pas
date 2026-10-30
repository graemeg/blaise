{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.maphash;

{ In-process behaviour tests for TDictionary/TOrderedDictionary/TSet at
  sizes that engage an accelerated (hashed) key lookup.  These pin the
  contract before the linear FindKey scan is replaced:

    - string keys match by CONTENT, including keys rebuilt at lookup time
      (different buffers, equal bytes),
    - Add on an existing key overwrites in place (no duplicate entry),
    - Remove compacts and subsequent lookups stay correct,
    - TOrderedDictionary preserves insertion order under indexed access,
    - TSet Include/Exclude/Contains stay consistent at scale.

  They run against the same generics the compiler itself uses. }

interface

uses
  Classes, SysUtils, blaise.testing, Generics.Collections;

type
  TMapHashTests = class(TTestCase)
  published
    procedure TestDict_StringKeys_ContentEquality_Large;
    procedure TestDict_AddExistingKey_Overwrites;
    procedure TestDict_Remove_ThenLookups;
    procedure TestDict_IntegerKeys_Large;
    procedure TestOrderedDict_PreservesInsertionOrder;
    procedure TestOrderedDict_Remove_KeepsOrder;
    procedure TestSet_IncludeExcludeContains_Large;
  end;

implementation

procedure TMapHashTests.TestDict_StringKeys_ContentEquality_Large;
var
  D: TDictionary<string, Int>;
  I, V: Int;
begin
  D := TDictionary<string, Int>.Create();
  try
    for I := 0 to 199 do
      D.Add('key_' + IntToStr(I), I * 10);
    AssertEquals('count', 200, D.Count);
    { Lookup keys are freshly concatenated — different buffers, same bytes. }
    AssertTrue('hit 0', D.TryGetValue('key_' + IntToStr(0), V));
    AssertEquals('val 0', 0, V);
    AssertTrue('hit 157', D.TryGetValue('key_' + IntToStr(157), V));
    AssertEquals('val 157', 1570, V);
    AssertTrue('miss', not D.TryGetValue('key_200', V));
    AssertTrue('contains', D.ContainsKey('key_42'));
    AssertTrue('not contains', not D.ContainsKey('KEY_42'));
  finally
    D.Free();
  end;
end;

procedure TMapHashTests.TestDict_AddExistingKey_Overwrites;
var
  D: TDictionary<string, Int>;
  I, V: Int;
begin
  D := TDictionary<string, Int>.Create();
  try
    for I := 0 to 49 do
      D.Add('k' + IntToStr(I), I);
    D.Add('k25', 9999);
    AssertEquals('count unchanged', 50, D.Count);
    AssertTrue('still found', D.TryGetValue('k25', V));
    AssertEquals('overwritten', 9999, V);
  finally
    D.Free();
  end;
end;

procedure TMapHashTests.TestDict_Remove_ThenLookups;
var
  D: TDictionary<string, Int>;
  I, V: Int;
begin
  D := TDictionary<string, Int>.Create();
  try
    for I := 0 to 99 do
      D.Add('k' + IntToStr(I), I);
    D.Remove('k10');
    D.Remove('k99');
    AssertEquals('count', 98, D.Count);
    AssertTrue('removed gone', not D.ContainsKey('k10'));
    AssertTrue('removed gone 2', not D.ContainsKey('k99'));
    AssertTrue('survivor', D.TryGetValue('k11', V));
    AssertEquals('survivor val', 11, V);
    AssertTrue('survivor low', D.ContainsKey('k0'));
    { Re-add a removed key. }
    D.Add('k10', 1010);
    AssertTrue('re-added', D.TryGetValue('k10', V));
    AssertEquals('re-added val', 1010, V);
  finally
    D.Free();
  end;
end;

procedure TMapHashTests.TestDict_IntegerKeys_Large;
var
  D: TDictionary<Int, Int>;
  I, V: Int;
begin
  D := TDictionary<Int, Int>.Create();
  try
    for I := 0 to 199 do
      D.Add(I * 7, I);
    AssertTrue('hit', D.TryGetValue(7 * 123, V));
    AssertEquals('val', 123, V);
    AssertTrue('miss', not D.TryGetValue(5, V));
  finally
    D.Free();
  end;
end;

procedure TMapHashTests.TestOrderedDict_PreservesInsertionOrder;
var
  D: TOrderedDictionary<string, Int>;
  I, V: Int;
begin
  D := TOrderedDictionary<string, Int>.Create();
  try
    for I := 0 to 99 do
      D.Add('k' + IntToStr(I), I);
    for I := 0 to 99 do
    begin
      AssertEquals('key order ' + IntToStr(I), 'k' + IntToStr(I), D.Keys[I]);
      AssertEquals('value order ' + IntToStr(I), I, D.Values[I]);
    end;
    AssertTrue('lookup', D.TryGetValue('k73', V));
    AssertEquals('lookup val', 73, V);
  finally
    D.Free();
  end;
end;

procedure TMapHashTests.TestOrderedDict_Remove_KeepsOrder;
var
  D: TOrderedDictionary<string, Int>;
  V: Int;
  I: Int;
begin
  D := TOrderedDictionary<string, Int>.Create();
  try
    for I := 0 to 49 do
      D.Add('k' + IntToStr(I), I);
    D.Remove('k0');
    AssertEquals('count', 49, D.Count);
    AssertEquals('new first key', 'k1', D.Keys[0]);
    AssertTrue('lookup after remove', D.TryGetValue('k30', V));
    AssertEquals('val after remove', 30, V);
  finally
    D.Free();
  end;
end;

procedure TMapHashTests.TestSet_IncludeExcludeContains_Large;
var
  S: TSet<Int>;
  I: Int;
begin
  S := TSet<Int>.Create();
  try
    for I := 0 to 199 do
      S.Include(I * 3);
    AssertEquals('count', 200, S.Count);
    S.Include(33);   { 33 = 3*11 already present — no duplicate }
    AssertEquals('no dup', 200, S.Count);
    AssertTrue('contains', S.Contains(597));
    AssertTrue('not contains', not S.Contains(598));
    S.Exclude(597);
    AssertTrue('excluded', not S.Contains(597));
    AssertEquals('count after exclude', 199, S.Count);
  finally
    S.Free();
  end;
end;

initialization
  RegisterTest(TMapHashTests);

end.
