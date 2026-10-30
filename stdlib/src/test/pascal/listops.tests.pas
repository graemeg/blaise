{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit ListOps.Tests;

{ Phase 10 (anonymous methods): eager LINQ-lite operators on TList<T> +
  closure-ordered Sort/BinarySearch.  Includes the double-monomorphisation
  probe (a generic method with its OWN type param on a generic class,
  instantiated at two different R's). }

interface

uses
  blaise.testing;

type
  TListOpsTests = class(TTestCase)
  published
    procedure TestMap_ProducesNewListOfR;
    procedure TestMap_DoubleMonomorphisation_TwoRs;
    procedure TestWhere_FiltersAndPreservesOrder;
    procedure TestWhere_EmptySource_YieldsEmpty;
    procedure TestWhere_NoneMatch_YieldsEmpty;
    procedure TestReduce_SumsWithSeed;
    procedure TestForEach_VisitsAllInOrder;
    procedure TestAnyAll_EdgeCases;
    procedure TestFind_FirstMatchAndMiss;
    procedure TestSort_OrdersByComparison;
    procedure TestSort_IsStable;
    procedure TestBinarySearch_HitAndMiss;
    procedure TestMap_CapturingClosure;
  end;

implementation

uses
  SysUtils, Generics.Collections, Functional;

function MakeInts(A, B, C: Int): TList<Int>;
begin
  Result := TList<Int>.Create();
  Result.Add(A);
  Result.Add(B);
  Result.Add(C)
end;

procedure TListOpsTests.TestMap_ProducesNewListOfR;
var
  L: TList<Int>;
  M: TList<string>;
begin
  L := MakeInts(3, 1, 2);
  M := L.Map<string>(N -> 'n' + IntToStr(N));
  AssertEquals('count', 3, M.Count);
  AssertEquals('first', 'n3', M[0]);
  AssertEquals('second', 'n1', M[1]);
  AssertEquals('third', 'n2', M[2]);
  AssertEquals('source untouched', 3, L.Count)
end;

procedure TListOpsTests.TestMap_DoubleMonomorphisation_TwoRs;
var
  L: TList<Int>;
  S: TList<string>;
  D: TList<Int>;
begin
  { The gate probe as a pinned test: TList<T>.Map<R> monomorphised at TWO
    different R's from the same T. }
  L := MakeInts(1, 2, 3);
  S := L.Map<string>(N -> IntToStr(N * 10));
  D := L.Map<Int>(N -> N * N);
  AssertEquals('string inst', '20', S[1]);
  AssertEquals('integer inst', 9, D[2])
end;

procedure TListOpsTests.TestWhere_FiltersAndPreservesOrder;
var
  L, W: TList<Int>;
begin
  L := MakeInts(3, 1, 2);
  W := L.Where(N -> N >= 2);
  AssertEquals('count', 2, W.Count);
  AssertEquals('order kept: 3 first', 3, W[0]);
  AssertEquals('order kept: 2 second', 2, W[1])
end;

procedure TListOpsTests.TestWhere_EmptySource_YieldsEmpty;
var
  L, W: TList<Int>;
begin
  L := TList<Int>.Create();
  W := L.Where(N -> True);
  AssertEquals('empty in, empty out', 0, W.Count)
end;

procedure TListOpsTests.TestWhere_NoneMatch_YieldsEmpty;
var
  L, W: TList<Int>;
begin
  L := MakeInts(1, 2, 3);
  W := L.Where(N -> N > 100);
  AssertEquals('none match', 0, W.Count)
end;

procedure TListOpsTests.TestReduce_SumsWithSeed;
var
  L, E: TList<Int>;
begin
  L := MakeInts(1, 2, 3);
  AssertEquals('sum with seed 10', 16,
    L.Reduce<Int>(10, (Acc, N) -> Acc + N));
  E := TList<Int>.Create();
  AssertEquals('empty list yields seed', 7,
    E.Reduce<Int>(7, (Acc, N) -> Acc + N))
end;

procedure TListOpsTests.TestForEach_VisitsAllInOrder;
var
  L: TList<Int>;
  Trace: string;
begin
  L := MakeInts(3, 1, 2);
  Trace := '';
  L.ForEach(procedure(N: Int)
    begin
      Trace := Trace + IntToStr(N)
    end);
  AssertEquals('visit order', '312', Trace)
end;

procedure TListOpsTests.TestAnyAll_EdgeCases;
var
  L, E: TList<Int>;
begin
  L := MakeInts(1, 2, 3);
  E := TList<Int>.Create();
  AssertTrue('any match', L.Any(N -> N = 2));
  AssertFalse('any no-match', L.Any(N -> N > 9));
  AssertFalse('any on empty', E.Any(N -> True));
  AssertTrue('all match', L.All(N -> N > 0));
  AssertFalse('all partial', L.All(N -> N > 1));
  AssertTrue('all on empty (vacuous)', E.All(N -> False))
end;

procedure TListOpsTests.TestFind_FirstMatchAndMiss;
var
  L: TList<Int>;
  V: Int;
begin
  L := MakeInts(3, 1, 2);
  V := 0;
  AssertTrue('finds first >= 1', L.Find(N -> N >= 1, V));
  AssertEquals('first in ORDER, not smallest', 3, V);
  AssertFalse('miss', L.Find(N -> N > 100, V))
end;

procedure TListOpsTests.TestSort_OrdersByComparison;
var
  L: TList<Int>;
begin
  L := MakeInts(3, 1, 2);
  L.Sort((A, B) -> A - B);
  AssertEquals('asc 0', 1, L[0]);
  AssertEquals('asc 1', 2, L[1]);
  AssertEquals('asc 2', 3, L[2]);
  L.Sort((A, B) -> B - A);
  AssertEquals('desc 0', 3, L[0]);
  AssertEquals('desc 2', 1, L[2])
end;

procedure TListOpsTests.TestSort_IsStable;
var
  L: TList<Int>;
begin
  { Sort by the TENS digit only: 31 and 32 compare equal, so their relative
    order (32 before 31 in the source) must survive the sort. }
  L := TList<Int>.Create();
  L.Add(52);
  L.Add(32);
  L.Add(31);
  L.Add(11);
  L.Sort((A, B) -> (A div 10) - (B div 10));
  AssertEquals('s0', 11, L[0]);
  AssertEquals('stable: 32 kept before 31', 32, L[1]);
  AssertEquals('s2', 31, L[2]);
  AssertEquals('s3', 52, L[3])
end;

procedure TListOpsTests.TestBinarySearch_HitAndMiss;
var
  L: TList<Int>;
  Idx: Int;
begin
  L := MakeInts(1, 2, 3);
  L.Add(5);
  Idx := -1;
  AssertTrue('hit', L.BinarySearch(3, (A, B) -> A - B, Idx));
  AssertEquals('hit index', 2, Idx);
  AssertFalse('miss', L.BinarySearch(4, (A, B) -> A - B, Idx));
  AssertEquals('insertion point', 3, Idx)
end;

procedure TListOpsTests.TestMap_CapturingClosure;
var
  L: TList<Int>;
  M: TList<Int>;
  Base: Int;
begin
  Base := 100;
  L := MakeInts(1, 2, 3);
  M := L.Map<Int>(N -> N + Base);
  AssertEquals('captured base applied', 102, M[1])
end;

initialization
  RegisterTest(TListOpsTests);

end.
