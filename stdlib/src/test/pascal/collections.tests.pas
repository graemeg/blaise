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

    { --- TList<T>: core operations --- }
    procedure TestList_AddAndIndexRead;
    procedure TestList_SetItemOverwrites;
    procedure TestList_IndexOf_HitAndMiss;
    procedure TestList_Delete_ShiftsTail;
    procedure TestList_Delete_LastElement;
    procedure TestList_Clear_EmptiesTheList;
    procedure TestList_GrowsPastInitialCapacity;
    procedure TestList_ForIn_VisitsAllInOrder;

    { --- TStack<T> --- }
    procedure TestStack_PushPop_IsLifo;
    procedure TestStack_Peek_DoesNotRemove;
    procedure TestStack_Clear_EmptiesTheStack;
    procedure TestStack_GrowsPastInitialCapacity;

    { --- TQueue<T> --- }
    procedure TestQueue_EnqueueDequeue_IsFifo;
    procedure TestQueue_Peek_DoesNotRemove;
    procedure TestQueue_Clear_EmptiesTheQueue;
    procedure TestQueue_WrapsAroundCircularBuffer;

    { --- TDictionary<K,V>: core operations --- }
    procedure TestDict_AddAndLookup;
    procedure TestDict_SetItemOverwrites;
    procedure TestDict_TryGetValue_HitAndMiss;
    procedure TestDict_Remove_DropsTheKey;
    procedure TestDict_Clear_EmptiesTheDict;
    procedure TestDict_GrowsPastHashThreshold;
    procedure TestDict_IntegerKeys;

    { --- TOrderedDictionary<K,V> --- }
    procedure TestOrdDict_PreservesInsertionOrder;
    procedure TestOrdDict_AddAndLookup;
    procedure TestOrdDict_SetItemOverwritesInPlace;
    procedure TestOrdDict_Remove_DropsTheKey;
    procedure TestOrdDict_From_BuildsFromParallelArrays;

    { --- managed (string) elements across a Grow --- }
    procedure TestList_GrowWithManagedElements;
    procedure TestQueue_GrowWithManagedElements;
    procedure TestStack_GrowWithManagedElements;

    { --- IsEmpty --- }
    procedure TestIsEmpty_TrueWhenFresh;
    procedure TestIsEmpty_FalseOncePopulated;
    procedure TestIsEmpty_TrueAgainAfterDrain;

    { --- empty-container access raises EListError --- }
    procedure TestStack_Pop_OnEmptyRaises;
    procedure TestStack_Peek_OnEmptyRaises;
    procedure TestQueue_Dequeue_OnEmptyRaises;
    procedure TestQueue_Peek_OnEmptyRaises;
    procedure TestStack_StaysUsableAfterEmptyPopRaised;

    { --- missing key raises instead of halting the process --- }
    procedure TestDict_GetItem_MissingKeyRaises;
    procedure TestOrdDict_GetItem_MissingKeyRaises;
    procedure TestDict_GetItem_PresentKeyStillWorks;

    { --- TList index bounds --- }
    procedure TestList_Get_OutOfRangeRaises;
    procedure TestList_SetItem_OutOfRangeRaises;
    procedure TestList_Delete_OutOfRangeRaises;
    procedure TestList_StaysUsableAfterOutOfRangeRaised;
    procedure TestList_InRangeAccessStillWorks;

    { --- TOrderedDictionary positional bounds --- }
    procedure TestOrdDict_GetKey_OutOfRangeRaises;
    procedure TestOrdDict_GetValue_OutOfRangeRaises;
    procedure TestOrdDict_InRangePositionalAccessStillWorks;
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

{ ------------------------------------------------------------------ }
{ TList<T> — core operations                                           }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestList_AddAndIndexRead;
var L: TList<string>;
begin
  L := TList<string>.Create();
  L.Add('a');
  L.Add('b');
  AssertEquals('count', 2, L.Count);
  AssertEquals('idx 0', 'a', L[0]);
  AssertEquals('idx 1', 'b', L[1]);
end;

procedure TCollectionsTests.TestList_SetItemOverwrites;
var L: TList<string>;
begin
  L := TList<string>.From(['a', 'b']);
  L[0] := 'z';
  AssertEquals('count unchanged', 2, L.Count);
  AssertEquals('overwritten', 'z', L[0]);
  AssertEquals('neighbour intact', 'b', L[1]);
end;

procedure TCollectionsTests.TestList_IndexOf_HitAndMiss;
var L: TList<string>;
begin
  L := TList<string>.From(['a', 'b', 'c']);
  AssertEquals('first', 0, L.IndexOf('a'));
  AssertEquals('middle', 1, L.IndexOf('b'));
  AssertTrue('miss is negative', L.IndexOf('zzz') < 0);
end;

procedure TCollectionsTests.TestList_Delete_ShiftsTail;
var L: TList<string>;
begin
  { Deleting from the middle must close the gap, not leave a hole. }
  L := TList<string>.From(['a', 'b', 'c']);
  L.Delete(1);
  AssertEquals('count dropped', 2, L.Count);
  AssertEquals('head kept', 'a', L[0]);
  AssertEquals('tail shifted down', 'c', L[1]);
end;

procedure TCollectionsTests.TestList_Delete_LastElement;
var L: TList<string>;
begin
  { The boundary case — nothing to shift. }
  L := TList<string>.From(['a', 'b']);
  L.Delete(1);
  AssertEquals('count', 1, L.Count);
  AssertEquals('remaining', 'a', L[0]);
end;

procedure TCollectionsTests.TestList_Clear_EmptiesTheList;
var L: TList<string>;
begin
  L := TList<string>.From(['a', 'b']);
  L.Clear();
  AssertEquals('empty', 0, L.Count);
  L.Add('fresh');
  AssertEquals('reusable after clear', 1, L.Count);
  AssertEquals('value', 'fresh', L[0]);
end;

procedure TCollectionsTests.TestList_GrowsPastInitialCapacity;
var
  L: TList<Integer>;
  I: Integer;
begin
  { Exercises Grow's realloc-and-copy repeatedly; a broken grow shows up as
    a wrong count or a corrupted early element. }
  L := TList<Integer>.Create();
  for I := 0 to 199 do
    L.Add(I);
  AssertEquals('all stored', 200, L.Count);
  AssertEquals('first intact', 0, L[0]);
  AssertEquals('middle intact', 100, L[100]);
  AssertEquals('last intact', 199, L[199]);
end;

procedure TCollectionsTests.TestList_ForIn_VisitsAllInOrder;
var
  L:   TList<string>;
  Acc: string;
  S:   string;
begin
  { GetEnumerator via for-in — untested until now. }
  L := TList<string>.From(['a', 'b', 'c']);
  Acc := '';
  for S in L do
    Acc := Acc + S;
  AssertEquals('visited in order', 'abc', Acc);
end;

{ ------------------------------------------------------------------ }
{ TStack<T>                                                            }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestStack_PushPop_IsLifo;
var S: TStack<string>;
begin
  S := TStack<string>.Create();
  S.Push('a');
  S.Push('b');
  S.Push('c');
  AssertEquals('count', 3, S.Count);
  AssertEquals('last in, first out', 'c', S.Pop());
  AssertEquals('then b', 'b', S.Pop());
  AssertEquals('then a', 'a', S.Pop());
  AssertEquals('drained', 0, S.Count);
end;

procedure TCollectionsTests.TestStack_Peek_DoesNotRemove;
var S: TStack<string>;
begin
  S := TStack<string>.Create();
  S.Push('a');
  S.Push('b');
  AssertEquals('peek sees the top', 'b', S.Peek());
  AssertEquals('count unchanged by peek', 2, S.Count);
  AssertEquals('pop still returns it', 'b', S.Pop());
end;

procedure TCollectionsTests.TestStack_Clear_EmptiesTheStack;
var S: TStack<string>;
begin
  S := TStack<string>.Create();
  S.Push('a');
  S.Push('b');
  S.Clear();
  AssertEquals('empty', 0, S.Count);
  S.Push('fresh');
  AssertEquals('reusable', 1, S.Count);
  AssertEquals('value', 'fresh', S.Peek());
end;

procedure TCollectionsTests.TestStack_GrowsPastInitialCapacity;
var
  S: TStack<Integer>;
  I: Integer;
begin
  S := TStack<Integer>.Create();
  for I := 0 to 199 do
    S.Push(I);
  AssertEquals('all pushed', 200, S.Count);
  AssertEquals('top is the last pushed', 199, S.Pop());
  AssertEquals('and the one below it', 198, S.Pop());
end;

{ ------------------------------------------------------------------ }
{ TQueue<T>                                                            }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestQueue_EnqueueDequeue_IsFifo;
var Q: TQueue<string>;
begin
  Q := TQueue<string>.Create();
  Q.Enqueue('a');
  Q.Enqueue('b');
  Q.Enqueue('c');
  AssertEquals('count', 3, Q.Count);
  AssertEquals('first in, first out', 'a', Q.Dequeue());
  AssertEquals('then b', 'b', Q.Dequeue());
  AssertEquals('then c', 'c', Q.Dequeue());
  AssertEquals('drained', 0, Q.Count);
end;

procedure TCollectionsTests.TestQueue_Peek_DoesNotRemove;
var Q: TQueue<string>;
begin
  Q := TQueue<string>.Create();
  Q.Enqueue('a');
  Q.Enqueue('b');
  AssertEquals('peek sees the head', 'a', Q.Peek());
  AssertEquals('count unchanged by peek', 2, Q.Count);
  AssertEquals('dequeue still returns it', 'a', Q.Dequeue());
end;

procedure TCollectionsTests.TestQueue_Clear_EmptiesTheQueue;
var Q: TQueue<string>;
begin
  Q := TQueue<string>.Create();
  Q.Enqueue('a');
  Q.Enqueue('b');
  Q.Clear();
  AssertEquals('empty', 0, Q.Count);
  Q.Enqueue('fresh');
  AssertEquals('reusable', 1, Q.Count);
  AssertEquals('value', 'fresh', Q.Peek());
end;

procedure TCollectionsTests.TestQueue_WrapsAroundCircularBuffer;
var
  Q: TQueue<Integer>;
  I: Integer;
begin
  { The queue is a circular buffer: interleaving enqueue and dequeue walks
    the head past the tail and forces a wrap.  A wrap bug shows as values
    coming back out of order, which a simple fill-then-drain never catches. }
  Q := TQueue<Integer>.Create();
  for I := 0 to 9 do
    Q.Enqueue(I);
  for I := 0 to 4 do
    AssertEquals('drained in order', I, Q.Dequeue());
  for I := 10 to 19 do
    Q.Enqueue(I);
  AssertEquals('count after wrap', 15, Q.Count);
  for I := 5 to 19 do
    AssertEquals('order preserved across the wrap', I, Q.Dequeue());
  AssertEquals('drained', 0, Q.Count);
end;

{ ------------------------------------------------------------------ }
{ TDictionary<K,V> — core operations                                   }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestDict_AddAndLookup;
var D: TDictionary<string, Integer>;
begin
  D := TDictionary<string, Integer>.Create();
  D.Add('a', 1);
  D.Add('b', 2);
  AssertEquals('count', 2, D.Count);
  AssertEquals('a', 1, D['a']);
  AssertEquals('b', 2, D['b']);
end;

procedure TCollectionsTests.TestDict_SetItemOverwrites;
var D: TDictionary<string, Integer>;
begin
  D := TDictionary<string, Integer>.Create();
  D.Add('k', 1);
  D['k'] := 99;
  AssertEquals('still one entry', 1, D.Count);
  AssertEquals('overwritten', 99, D['k']);
end;

procedure TCollectionsTests.TestDict_TryGetValue_HitAndMiss;
var
  D: TDictionary<string, Integer>;
  V: Integer;
begin
  D := TDictionary<string, Integer>.From(['a'], [1]);
  V := -1;
  AssertTrue('hit returns True', D.TryGetValue('a', V));
  AssertEquals('and yields the value', 1, V);
  V := -1;
  AssertFalse('miss returns False', D.TryGetValue('nope', V));
  AssertEquals('and leaves the out param alone', -1, V);
end;

procedure TCollectionsTests.TestDict_Remove_DropsTheKey;
var D: TDictionary<string, Integer>;
begin
  D := TDictionary<string, Integer>.From(['a', 'b'], [1, 2]);
  D.Remove('a');
  AssertEquals('count dropped', 1, D.Count);
  AssertFalse('key gone', D.ContainsKey('a'));
  AssertTrue('other key kept', D.ContainsKey('b'));
  AssertEquals('and its value', 2, D['b']);
end;

procedure TCollectionsTests.TestDict_Clear_EmptiesTheDict;
var D: TDictionary<string, Integer>;
begin
  D := TDictionary<string, Integer>.From(['a'], [1]);
  D.Clear();
  AssertEquals('empty', 0, D.Count);
  AssertFalse('key gone', D.ContainsKey('a'));
  D.Add('fresh', 7);
  AssertEquals('reusable', 1, D.Count);
  AssertEquals('value', 7, D['fresh']);
end;

procedure TCollectionsTests.TestDict_GrowsPastHashThreshold;
var
  D: TDictionary<string, Integer>;
  I: Integer;
begin
  { As with TSet, the hash index only engages at 16+ entries, so crossing
    the boundary is where a rebuild bug surfaces. }
  D := TDictionary<string, Integer>.Create();
  for I := 0 to 49 do
    D.Add('key-' + IntToStr(I), I);
  AssertEquals('all stored', 50, D.Count);
  AssertEquals('first', 0, D['key-0']);
  AssertEquals('middle', 25, D['key-25']);
  AssertEquals('last', 49, D['key-49']);
  AssertFalse('absent stays absent', D.ContainsKey('key-50'));
end;

procedure TCollectionsTests.TestDict_IntegerKeys;
var D: TDictionary<Integer, string>;
begin
  { Key type other than string — hashing dispatches through GCHashOf. }
  D := TDictionary<Integer, string>.Create();
  D.Add(1, 'one');
  D.Add(2, 'two');
  AssertEquals('count', 2, D.Count);
  AssertEquals('lookup', 'two', D[2]);
  AssertFalse('miss', D.ContainsKey(3));
end;

{ ------------------------------------------------------------------ }
{ TOrderedDictionary<K,V>                                              }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestOrdDict_PreservesInsertionOrder;
var
  D: TOrderedDictionary<string, Integer>;
begin
  { The whole point of this type: iteration follows insertion order, which
    a plain TDictionary does not promise.  Inserted deliberately out of
    alphabetical order so a sorted implementation would fail. }
  D := TOrderedDictionary<string, Integer>.Create();
  D.Add('zulu', 1);
  D.Add('alpha', 2);
  D.Add('mike', 3);
  AssertEquals('count', 3, D.Count);
  AssertEquals('slot 0', 'zulu',  D.Keys[0]);
  AssertEquals('slot 1', 'alpha', D.Keys[1]);
  AssertEquals('slot 2', 'mike',  D.Keys[2]);
  AssertEquals('value 0', 1, D.Values[0]);
  AssertEquals('value 2', 3, D.Values[2]);
end;

procedure TCollectionsTests.TestOrdDict_AddAndLookup;
var D: TOrderedDictionary<string, Integer>;
begin
  D := TOrderedDictionary<string, Integer>.Create();
  D.Add('a', 1);
  AssertEquals('lookup by key', 1, D['a']);
  AssertTrue('contains', D.ContainsKey('a'));
  AssertFalse('miss', D.ContainsKey('b'));
end;

procedure TCollectionsTests.TestOrdDict_SetItemOverwritesInPlace;
var D: TOrderedDictionary<string, Integer>;
begin
  { Overwriting an existing key must update in place, NOT append a second
    slot — otherwise the ordering view grows a duplicate. }
  D := TOrderedDictionary<string, Integer>.Create();
  D.Add('a', 1);
  D.Add('b', 2);
  D['a'] := 99;
  AssertEquals('no new slot', 2, D.Count);
  AssertEquals('updated', 99, D['a']);
  AssertEquals('position kept', 'a', D.Keys[0]);
end;

procedure TCollectionsTests.TestOrdDict_Remove_DropsTheKey;
var D: TOrderedDictionary<string, Integer>;
begin
  D := TOrderedDictionary<string, Integer>.Create();
  D.Add('a', 1);
  D.Add('b', 2);
  D.Add('c', 3);
  D.Remove('b');
  AssertEquals('count dropped', 2, D.Count);
  AssertFalse('key gone', D.ContainsKey('b'));
  AssertEquals('order closes the gap', 'a', D.Keys[0]);
  AssertEquals('and shifts the tail down', 'c', D.Keys[1]);
  { Values must shift WITH their keys -- checking Keys alone would pass for a
    Remove that compacted the key array and left the values behind. }
  AssertEquals('value 0 still pairs', 1, D.Values[0]);
  AssertEquals('value 1 still pairs', 3, D.Values[1]);
  AssertEquals('and by key lookup', 3, D['c']);
end;

procedure TCollectionsTests.TestOrdDict_From_BuildsFromParallelArrays;
var D: TOrderedDictionary<string, Integer>;
begin
  D := TOrderedDictionary<string, Integer>.From(['x', 'y'], [10, 20]);
  AssertEquals('count', 2, D.Count);
  AssertEquals('x', 10, D['x']);
  AssertEquals('y', 20, D['y']);
  AssertEquals('literal order kept', 'x', D.Keys[0]);
end;

{ ------------------------------------------------------------------ }
{ Managed (string) elements across a Grow                              }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestList_GrowWithManagedElements;
var
  L: TList<string>;
  I: Integer;
begin
  { The growth tests above use Integer, so Grow's realloc-and-copy never runs
    with a REFERENCE-COUNTED element.  That is exactly where a bug is silent:
    a missing retain leaks, a double release frees a live string, and neither
    shows up until something else reads freed memory.  Capacity starts at 0
    and doubles 4,8,...  so 100 strings cross several reallocs.

    Each string is built at run time rather than being a literal, so it is a
    genuine heap allocation with a refcount, not an immortal constant. }
  L := TList<string>.Create();
  for I := 0 to 99 do
    L.Add('item-' + IntToStr(I));
  AssertEquals('all stored', 100, L.Count);
  AssertEquals('first survived the reallocs', 'item-0', L[0]);
  AssertEquals('middle survived', 'item-50', L[50]);
  AssertEquals('last survived', 'item-99', L[99]);
  { Overwrite and delete exercise the release paths on managed slots. }
  L[0] := 'replaced';
  AssertEquals('overwrite released the old value cleanly', 'replaced', L[0]);
  L.Delete(0);
  AssertEquals('delete shifted managed elements', 'item-1', L[0]);
  AssertEquals('count', 99, L.Count);
end;

procedure TCollectionsTests.TestQueue_GrowWithManagedElements;
var
  Q: TQueue<string>;
  I: Integer;
begin
  { TQueue.Grow linearises a wrapped circular buffer AND clears the vacated
    source slots -- the most intricate managed-element path in the unit. }
  Q := TQueue<string>.Create();
  for I := 0 to 9 do
    Q.Enqueue('q-' + IntToStr(I));
  for I := 0 to 4 do
    AssertEquals('drained in order', 'q-' + IntToStr(I), Q.Dequeue());
  for I := 10 to 49 do
    Q.Enqueue('q-' + IntToStr(I));
  AssertEquals('count after wrap + grow', 45, Q.Count);
  for I := 5 to 49 do
    AssertEquals('order kept across wrap and grow',
                 'q-' + IntToStr(I), Q.Dequeue());
  AssertEquals('drained', 0, Q.Count);
end;

procedure TCollectionsTests.TestStack_GrowWithManagedElements;
var
  S: TStack<string>;
  I: Integer;
begin
  S := TStack<string>.Create();
  for I := 0 to 99 do
    S.Push('s-' + IntToStr(I));
  AssertEquals('all pushed', 100, S.Count);
  for I := 99 downto 0 do
    AssertEquals('LIFO order intact after reallocs',
                 's-' + IntToStr(I), S.Pop());
  AssertEquals('drained', 0, S.Count);
end;

{ ------------------------------------------------------------------ }
{ IsEmpty                                                              }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestIsEmpty_TrueWhenFresh;
var
  L: TList<string>;
  S: TStack<string>;
  Q: TQueue<string>;
  E: TSet<string>;
  D: TDictionary<string, Integer>;
  O: TOrderedDictionary<string, Integer>;
begin
  L := TList<string>.Create();
  S := TStack<string>.Create();
  Q := TQueue<string>.Create();
  E := TSet<string>.Create();
  D := TDictionary<string, Integer>.Create();
  O := TOrderedDictionary<string, Integer>.Create();
  AssertTrue('list',  L.IsEmpty());
  AssertTrue('stack', S.IsEmpty());
  AssertTrue('queue', Q.IsEmpty());
  AssertTrue('set',   E.IsEmpty());
  AssertTrue('dict',  D.IsEmpty());
  AssertTrue('ordered dict', O.IsEmpty());
end;

procedure TCollectionsTests.TestIsEmpty_FalseOncePopulated;
var
  L: TList<string>;
  S: TStack<string>;
  Q: TQueue<string>;
  E: TSet<string>;
  D: TDictionary<string, Integer>;
begin
  L := TList<string>.From(['a']);
  S := TStack<string>.Create();  S.Push('a');
  Q := TQueue<string>.Create();  Q.Enqueue('a');
  E := TSet<string>.From(['a']);
  D := TDictionary<string, Integer>.From(['a'], [1]);
  AssertFalse('list',  L.IsEmpty());
  AssertFalse('stack', S.IsEmpty());
  AssertFalse('queue', Q.IsEmpty());
  AssertFalse('set',   E.IsEmpty());
  AssertFalse('dict',  D.IsEmpty());
end;

procedure TCollectionsTests.TestIsEmpty_TrueAgainAfterDrain;
var
  S: TStack<string>;
  Q: TQueue<string>;
  L: TList<string>;
begin
  { IsEmpty must track removals, not just report "never populated". }
  S := TStack<string>.Create();
  S.Push('a');
  S.Pop();
  AssertTrue('stack empty after pop', S.IsEmpty());
  Q := TQueue<string>.Create();
  Q.Enqueue('a');
  Q.Dequeue();
  AssertTrue('queue empty after dequeue', Q.IsEmpty());
  L := TList<string>.From(['a']);
  L.Clear();
  AssertTrue('list empty after clear', L.IsEmpty());
end;

{ ------------------------------------------------------------------ }
{ Empty-container access raises EListError                             }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestStack_Pop_OnEmptyRaises;
var
  S:      TStack<Integer>;
  Raised: Boolean;
begin
  { Was a SIGSEGV: Pop drove FCount to -1 and read FData[-1].  Removal from
    an empty container is a caller bug, so it raises rather than inventing a
    value (BUG-20260803-empty-container-pop-segfaults). }
  S := TStack<Integer>.Create();
  Raised := False;
  try
    S.Pop();
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Pop on empty raises EListError', Raised);
end;

procedure TCollectionsTests.TestStack_Peek_OnEmptyRaises;
var
  S:      TStack<Integer>;
  Raised: Boolean;
begin
  { Peek raises too rather than returning Default(T): unlike Java's null,
    Default(T) is a legitimate element value here (0 / '') and would be
    indistinguishable from a real stored one. }
  S := TStack<Integer>.Create();
  Raised := False;
  try
    S.Peek();
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Peek on empty raises EListError', Raised);
end;

procedure TCollectionsTests.TestQueue_Dequeue_OnEmptyRaises;
var
  Q:      TQueue<Integer>;
  Raised: Boolean;
begin
  { Was a SIGSEGV twice over on a never-used queue: nil FData deref, plus
    `mod FCapacity` with FCapacity still 0. }
  Q := TQueue<Integer>.Create();
  Raised := False;
  try
    Q.Dequeue();
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Dequeue on empty raises EListError', Raised);
end;

procedure TCollectionsTests.TestQueue_Peek_OnEmptyRaises;
var
  Q:      TQueue<Integer>;
  Raised: Boolean;
begin
  Q := TQueue<Integer>.Create();
  Raised := False;
  try
    Q.Peek();
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Peek on empty raises EListError', Raised);
end;

procedure TCollectionsTests.TestStack_StaysUsableAfterEmptyPopRaised;
var
  S:      TStack<Integer>;
  Raised: Boolean;
begin
  { The guard must return BEFORE mutating FCount.  The old code decremented
    first, so even a caught failure left the stack permanently corrupt —
    this asserts the container is still sound afterwards. }
  S := TStack<Integer>.Create();
  Raised := False;
  try
    S.Pop();
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
  AssertEquals('count not driven negative', 0, S.Count);
  AssertTrue('still reports empty', S.IsEmpty());
  S.Push(42);
  AssertEquals('usable again', 1, S.Count);
  AssertEquals('and returns the value', 42, S.Pop());
end;

{ ------------------------------------------------------------------ }
{ Missing key raises instead of halting the process                    }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestDict_GetItem_MissingKeyRaises;
var
  D:      TDictionary<string, Integer>;
  Raised: Boolean;
  V:      Integer;
begin
  { Was Halt(1) — a missing key terminated the whole PROCESS with no message
    and no chance to catch it.  A test could not even observe the old
    behaviour without taking the runner down with it. }
  D := TDictionary<string, Integer>.From(['a'], [1]);
  Raised := False;
  try
    V := D['nope'];
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('missing key raises EListError', Raised);
end;

procedure TCollectionsTests.TestOrdDict_GetItem_MissingKeyRaises;
var
  D:      TOrderedDictionary<string, Integer>;
  Raised: Boolean;
  V:      Integer;
begin
  D := TOrderedDictionary<string, Integer>.From(['a'], [1]);
  Raised := False;
  try
    V := D['nope'];
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('missing key raises EListError', Raised);
end;

procedure TCollectionsTests.TestDict_GetItem_PresentKeyStillWorks;
var D: TDictionary<string, Integer>;
begin
  { The guard must not cost the happy path — a fix that raised on everything
    would pass the two tests above. }
  D := TDictionary<string, Integer>.From(['a', 'b'], [1, 2]);
  AssertEquals('a', 1, D['a']);
  AssertEquals('b', 2, D['b']);
  AssertTrue('and TryGetValue still branches instead of raising',
             D.ContainsKey('a'));
  AssertFalse('miss via ContainsKey does not raise', D.ContainsKey('zzz'));
end;

{ ------------------------------------------------------------------ }
{ TList index bounds                                                   }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestList_Get_OutOfRangeRaises;
var
  L:      TList<string>;
  Raised: Boolean;
  V:      string;
begin
  { Same family as the empty-container crashes: reading L[0] on an EMPTY
    list dereferenced a nil FData, and any out-of-range index read wild
    memory rather than failing. }
  L := TList<string>.Create();
  Raised := False;
  try
    V := L[0];
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Get on empty raises', Raised);
end;

procedure TCollectionsTests.TestList_SetItem_OutOfRangeRaises;
var
  L:      TList<string>;
  Raised: Boolean;
begin
  L := TList<string>.From(['a']);
  Raised := False;
  try
    L[5] := 'x';
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('SetItem past the end raises', Raised);
end;

procedure TCollectionsTests.TestList_Delete_OutOfRangeRaises;
var
  L:      TList<string>;
  Raised: Boolean;
begin
  L := TList<string>.From(['a']);
  Raised := False;
  try
    L.Delete(5);
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Delete past the end raises', Raised);
end;

procedure TCollectionsTests.TestList_StaysUsableAfterOutOfRangeRaised;
var
  L:      TList<string>;
  Raised: Boolean;
begin
  { Delete guarded BEFORE the shift: the old code decremented FCount and
    wrote through Dst even for a bad index, so a caught failure still left
    the list corrupt. }
  L := TList<string>.From(['a', 'b']);
  Raised := False;
  try
    L.Delete(99);
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
  AssertEquals('count untouched', 2, L.Count);
  AssertEquals('contents intact', 'a', L[0]);
  AssertEquals('and the tail', 'b', L[1]);
end;

procedure TCollectionsTests.TestList_InRangeAccessStillWorks;
var L: TList<string>;
begin
  { A guard that raised on everything would pass the four tests above. }
  L := TList<string>.From(['a', 'b', 'c']);
  AssertEquals('first', 'a', L[0]);
  AssertEquals('last', 'c', L[2]);
  L[1] := 'z';
  AssertEquals('write in range', 'z', L[1]);
  L.Delete(0);
  AssertEquals('delete in range', 2, L.Count);
  AssertEquals('shifted', 'z', L[0]);
end;

{ ------------------------------------------------------------------ }
{ TOrderedDictionary positional bounds                                 }
{ ------------------------------------------------------------------ }

procedure TCollectionsTests.TestOrdDict_GetKey_OutOfRangeRaises;
var
  D:      TOrderedDictionary<string, Integer>;
  Raised: Boolean;
  Key:    string;
begin
  { Keys[0] on an empty ordered dictionary dereferenced a nil FKeys -- the
    positional accessors were the last unguarded siblings of the same bug. }
  D := TOrderedDictionary<string, Integer>.Create();
  Raised := False;
  try
    Key := D.Keys[0];
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Keys[0] on empty raises', Raised);
end;

procedure TCollectionsTests.TestOrdDict_GetValue_OutOfRangeRaises;
var
  D:      TOrderedDictionary<string, Integer>;
  Raised: Boolean;
  V:      Integer;
begin
  D := TOrderedDictionary<string, Integer>.From(['a'], [1]);
  Raised := False;
  try
    V := D.Values[5];
  except
    on E: EListError do
      Raised := True;
  end;
  AssertTrue('Values past the end raises', Raised);
end;

procedure TCollectionsTests.TestOrdDict_InRangePositionalAccessStillWorks;
var D: TOrderedDictionary<string, Integer>;
begin
  { A guard that raised on everything would pass the two tests above. }
  D := TOrderedDictionary<string, Integer>.From(['a', 'b'], [1, 2]);
  AssertEquals('key 0', 'a', D.Keys[0]);
  AssertEquals('key 1', 'b', D.Keys[1]);
  AssertEquals('value 0', 1, D.Values[0]);
  AssertEquals('value 1', 2, D.Values[1]);
end;

initialization
  RegisterTest(TCollectionsTests);

end.
