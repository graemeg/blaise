{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Collections.Tests;

{ Tests for the Generics.Collections types.

  The suite is named for the unit under test, not for one type, so tests for
  TList/TDictionary/TQueue/TStack have an obvious home alongside these.

  TSet<T> is covered first because it had NO tests at all despite ~37 real
  uses in the bindgen tool.  These cover the existing surface
  (Include/Exclude/Contains/Count/Clear) as well as the From([...]) factory.
  The hash path only engages at 16+ elements (GCHashThreshold), so the
  size-crossing cases below are the ones that exercise HashRebuild rather
  than the linear scan. }

interface

uses
  blaise.testing;

type
  TCollectionsTests = class(TTestCase)
  published
    { --- TSet<T>: core membership --- }
    procedure TestSet_Include_AddsMember;
    procedure TestSet_Include_IsIdempotent;
    procedure TestSet_Contains_MissReturnsFalse;
    procedure TestSet_Exclude_RemovesMember;
    procedure TestSet_Exclude_MissingIsNoOp;
    procedure TestSet_Clear_EmptiesTheSet;
    procedure TestSet_Empty_ContainsNothing;

    { --- TSet<T>: growth across the hash threshold --- }
    procedure TestSet_GrowsPastHashThreshold;
    procedure TestSet_ExcludeAfterHashRebuild;

    { --- TSet<T>: element type other than string --- }
    procedure TestSet_IntegerElements;

    { --- TSet<T>: From([...]) factory --- }
    procedure TestSet_From_BuildsSetFromLiteral;
    procedure TestSet_From_DeduplicatesRepeats;
    procedure TestSet_From_EmptyLiteralYieldsEmptySet;
    procedure TestSet_From_SingleElement;
    procedure TestSet_From_IntegerElements;
    procedure TestSet_From_ResultIsMutable;

    { --- TList<T>: From([...]) factory --- }
    procedure TestList_From_BuildsListFromLiteral;
    procedure TestList_From_PreservesOrder;
    procedure TestList_From_KeepsDuplicates;
    procedure TestList_From_EmptyLiteralYieldsEmptyList;
    procedure TestList_From_IntegerElements;
    procedure TestList_From_ResultIsMutable;

    { --- TDictionary<K,V>: From([...], [...]) factory --- }
    procedure TestDict_From_BuildsFromParallelArrays;
    procedure TestDict_From_EmptyLiteralsYieldEmptyDict;
    procedure TestDict_From_LaterKeyWins;
    procedure TestDict_From_LengthMismatchPairsUpToShorter;
    procedure TestDict_From_ResultIsMutable;
  end;

implementation

uses
  SysUtils, Generics.Collections;

{ ------------------------------------------------------------------ }
{ Core membership                                                      }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestSet_Include_AddsMember;
var S: TSet<string>;
begin
  S := TSet<string>.Create();
  S.Include('LINUX');
  AssertTrue('contains the member', S.Contains('LINUX'));
  AssertEquals('count', 1, S.Count);
end;

procedure TCollectionsTests.TestSet_Include_IsIdempotent;
var S: TSet<string>;
begin
  { A set holds each value once — re-including must not grow it. }
  S := TSet<string>.Create();
  S.Include('A');
  S.Include('A');
  S.Include('A');
  AssertEquals('still one member', 1, S.Count);
  AssertTrue('still present', S.Contains('A'));
end;

procedure TCollectionsTests.TestSet_Contains_MissReturnsFalse;
var S: TSet<string>;
begin
  S := TSet<string>.Create();
  S.Include('A');
  AssertFalse('absent value', S.Contains('B'));
end;

procedure TCollectionsTests.TestSet_Exclude_RemovesMember;
var S: TSet<string>;
begin
  S := TSet<string>.Create();
  S.Include('A');
  S.Include('B');
  S.Exclude('A');
  AssertFalse('excluded value gone', S.Contains('A'));
  AssertTrue('other value kept', S.Contains('B'));
  AssertEquals('count dropped', 1, S.Count);
end;

procedure TCollectionsTests.TestSet_Exclude_MissingIsNoOp;
var S: TSet<string>;
begin
  S := TSet<string>.Create();
  S.Include('A');
  S.Exclude('NOT-THERE');
  AssertEquals('count unchanged', 1, S.Count);
  AssertTrue('member kept', S.Contains('A'));
end;

procedure TCollectionsTests.TestSet_Clear_EmptiesTheSet;
var S: TSet<string>;
begin
  S := TSet<string>.Create();
  S.Include('A');
  S.Include('B');
  S.Clear();
  AssertEquals('count zero', 0, S.Count);
  AssertFalse('member gone', S.Contains('A'));
end;

procedure TCollectionsTests.TestSet_Empty_ContainsNothing;
var S: TSet<string>;
begin
  S := TSet<string>.Create();
  AssertEquals('count zero', 0, S.Count);
  AssertFalse('nothing present', S.Contains('anything'));
end;

{ ------------------------------------------------------------------ }
{ Growth across the hash threshold                                     }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestSet_GrowsPastHashThreshold;
var
  S: TSet<string>;
  I: Integer;
begin
  { Below 16 elements IndexOf scans linearly; at/after it the hash table
    engages.  Crossing the boundary is where a rebuild bug would show. }
  S := TSet<string>.Create();
  for I := 0 to 49 do
    S.Include('key-' + IntToStr(I));
  AssertEquals('all fifty stored', 50, S.Count);
  AssertTrue('first still found',  S.Contains('key-0'));
  AssertTrue('middle still found', S.Contains('key-25'));
  AssertTrue('last still found',   S.Contains('key-49'));
  AssertFalse('absent still absent', S.Contains('key-50'));
end;

procedure TCollectionsTests.TestSet_ExcludeAfterHashRebuild;
var
  S: TSet<string>;
  I: Integer;
begin
  { Removal must keep the hash index consistent, or a later lookup finds a
    stale slot. }
  S := TSet<string>.Create();
  for I := 0 to 29 do
    S.Include('k' + IntToStr(I));
  S.Exclude('k10');
  S.Exclude('k20');
  AssertEquals('count reflects removals', 28, S.Count);
  AssertFalse('k10 gone', S.Contains('k10'));
  AssertFalse('k20 gone', S.Contains('k20'));
  AssertTrue('k11 kept', S.Contains('k11'));
  AssertTrue('k29 kept', S.Contains('k29'));
end;

procedure TCollectionsTests.TestSet_IntegerElements;
var S: TSet<Integer>;
begin
  S := TSet<Integer>.Create();
  S.Include(1);
  S.Include(2);
  S.Include(1);
  AssertEquals('deduplicated', 2, S.Count);
  AssertTrue('has 1', S.Contains(1));
  AssertTrue('has 2', S.Contains(2));
  AssertFalse('no 3', S.Contains(3));
end;

{ ------------------------------------------------------------------ }
{ From([...]) factory                                                  }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestSet_From_BuildsSetFromLiteral;
var S: TSet<string>;
begin
  S := TSet<string>.From(['LINUX', 'FREEBSD', 'DARWIN']);
  AssertEquals('three members', 3, S.Count);
  AssertTrue('has LINUX',   S.Contains('LINUX'));
  AssertTrue('has FREEBSD', S.Contains('FREEBSD'));
  AssertTrue('has DARWIN',  S.Contains('DARWIN'));
  AssertFalse('no WINDOWS', S.Contains('WINDOWS'));
end;

procedure TCollectionsTests.TestSet_From_DeduplicatesRepeats;
var S: TSet<string>;
begin
  { Set semantics apply to the literal too — a repeated entry is folded. }
  S := TSet<string>.From(['A', 'B', 'A', 'B', 'A']);
  AssertEquals('two distinct members', 2, S.Count);
  AssertTrue('has A', S.Contains('A'));
  AssertTrue('has B', S.Contains('B'));
end;

procedure TCollectionsTests.TestSet_From_EmptyLiteralYieldsEmptySet;
var S: TSet<string>;
begin
  S := TSet<string>.From([]);
  AssertEquals('empty', 0, S.Count);
  AssertFalse('contains nothing', S.Contains('A'));
end;

procedure TCollectionsTests.TestSet_From_SingleElement;
var S: TSet<string>;
begin
  S := TSet<string>.From(['ONLY']);
  AssertEquals('one member', 1, S.Count);
  AssertTrue('has it', S.Contains('ONLY'));
end;

procedure TCollectionsTests.TestSet_From_IntegerElements;
var S: TSet<Integer>;
begin
  { The factory is generic, not string-specific. }
  S := TSet<Integer>.From([10, 20, 30]);
  AssertEquals('three members', 3, S.Count);
  AssertTrue('has 20', S.Contains(20));
  AssertFalse('no 40', S.Contains(40));
end;

procedure TCollectionsTests.TestSet_From_ResultIsMutable;
var S: TSet<string>;
begin
  { From returns an ordinary TSet, not a frozen view — Java's Set.of() is
    immutable, ours deliberately is not. }
  S := TSet<string>.From(['A']);
  S.Include('B');
  S.Exclude('A');
  AssertEquals('mutated', 1, S.Count);
  AssertTrue('B added', S.Contains('B'));
  AssertFalse('A removed', S.Contains('A'));
end;

{ ------------------------------------------------------------------ }
{ TList<T>.From([...])                                                 }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestList_From_BuildsListFromLiteral;
var L: TList<string>;
begin
  L := TList<string>.From(['a', 'b', 'c']);
  AssertEquals('three items', 3, L.Count);
  AssertEquals('first',  'a', L[0]);
  AssertEquals('second', 'b', L[1]);
  AssertEquals('third',  'c', L[2]);
end;

procedure TCollectionsTests.TestList_From_PreservesOrder;
var
  L: TList<Integer>;
  I: Integer;
begin
  { A list is ordered — unlike TSet, the literal's order is the contract. }
  L := TList<Integer>.From([5, 3, 9, 1]);
  AssertEquals('count', 4, L.Count);
  AssertEquals('idx 0', 5, L[0]);
  AssertEquals('idx 1', 3, L[1]);
  AssertEquals('idx 2', 9, L[2]);
  AssertEquals('idx 3', 1, L[3]);
end;

procedure TCollectionsTests.TestList_From_KeepsDuplicates;
var L: TList<string>;
begin
  { The opposite of TSet.From: a list keeps every occurrence. }
  L := TList<string>.From(['x', 'x', 'x']);
  AssertEquals('all three kept', 3, L.Count);
end;

procedure TCollectionsTests.TestList_From_EmptyLiteralYieldsEmptyList;
var L: TList<string>;
begin
  L := TList<string>.From([]);
  AssertEquals('empty', 0, L.Count);
end;

procedure TCollectionsTests.TestList_From_IntegerElements;
var L: TList<Integer>;
begin
  L := TList<Integer>.From([10, 20]);
  AssertEquals('count', 2, L.Count);
  AssertEquals('sum', 30, L[0] + L[1]);
end;

procedure TCollectionsTests.TestList_From_ResultIsMutable;
var L: TList<string>;
begin
  L := TList<string>.From(['a']);
  L.Add('b');
  AssertEquals('grew', 2, L.Count);
  AssertEquals('appended', 'b', L[1]);
end;

{ ------------------------------------------------------------------ }
{ TDictionary<K,V>.From([...], [...])                                  }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestDict_From_BuildsFromParallelArrays;
var D: TDictionary<string, Integer>;
begin
  D := TDictionary<string, Integer>.From(['one', 'two'], [1, 2]);
  AssertEquals('two entries', 2, D.Count);
  AssertEquals('one', 1, D['one']);
  AssertEquals('two', 2, D['two']);
  AssertTrue('has key',  D.ContainsKey('one'));
  AssertFalse('no such key', D.ContainsKey('three'));
end;

procedure TCollectionsTests.TestDict_From_EmptyLiteralsYieldEmptyDict;
var D: TDictionary<string, Integer>;
begin
  D := TDictionary<string, Integer>.From([], []);
  AssertEquals('empty', 0, D.Count);
  AssertFalse('no keys', D.ContainsKey('anything'));
end;

procedure TCollectionsTests.TestDict_From_LaterKeyWins;
var D: TDictionary<string, Integer>;
begin
  { A repeated key is an overwrite, matching SetItem semantics rather than
    silently keeping two entries under one key. }
  D := TDictionary<string, Integer>.From(['k', 'k'], [1, 2]);
  AssertEquals('one entry', 1, D.Count);
  AssertEquals('last value wins', 2, D['k']);
end;

procedure TCollectionsTests.TestDict_From_LengthMismatchPairsUpToShorter;
var D: TDictionary<string, Integer>;
begin
  { generics.collections is deliberately exception-free (an out-of-range
    TList.Get simply reads past the end), so From does not raise on a
    mismatch — it pairs up to the shorter array and ignores the tail.
    Pinned here so the behaviour is a decision rather than an accident. }
  D := TDictionary<string, Integer>.From(['a', 'b', 'c'], [1, 2]);
  AssertEquals('paired up to the shorter', 2, D.Count);
  AssertTrue('a paired',  D.ContainsKey('a'));
  AssertTrue('b paired',  D.ContainsKey('b'));
  AssertFalse('c dropped', D.ContainsKey('c'));
end;

procedure TCollectionsTests.TestDict_From_ResultIsMutable;
var D: TDictionary<string, Integer>;
begin
  D := TDictionary<string, Integer>.From(['a'], [1]);
  D.Add('b', 2);
  AssertEquals('grew', 2, D.Count);
  AssertEquals('added', 2, D['b']);
end;

initialization
  RegisterTest(TCollectionsTests);

end.
