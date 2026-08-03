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

initialization
  RegisterTest(TCollectionsTests);

end.
