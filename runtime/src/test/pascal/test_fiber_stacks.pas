{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ punit tests for the fiber stack allocator + pool (L0 of
  docs/async-networking-design.adoc): mmap'd guard-page stacks served from a
  per-thread free list (async.fibers.context).

  NATIVE BACKEND ONLY (the fiber unit contains inline asm).

  Compile and run:
    compiler/target/blaise --source runtime/src/test/pascal/test_fiber_stacks.pas
        --unit-path runtime/src/test/pascal --unit-path stdlib/src/main/pascal
        --output /tmp/test_fiber_stacks
    /tmp/test_fiber_stacks }

program test_fiber_stacks;

uses punit, async.fibers.context;

function TestAcquire_PageAlignedAndSized: string;
var
  Base: Pointer;
  Total: Int64;
begin
  Base := FiberStackAcquire(FiberDefaultStackSize, Total);
  AssertTrue('base not nil', Base <> nil);
  AssertTrue('base page-aligned', (PtrUInt(Base) and 4095) = 0);
  AssertEquals('total = usable + guard page',
    Int64(FiberDefaultStackSize + FiberPageSize), Total);
  FiberStackReturn(Base, Total);
  Result := '';
end;

function TestAcquire_OddSizeRoundsUp: string;
var
  Base: Pointer;
  Total: Int64;
begin
  Base := FiberStackAcquire(5000, Total);
  AssertTrue('base not nil', Base <> nil);
  AssertEquals('5000 rounds to 2 pages + guard', Int64(3 * FiberPageSize),
    Total);
  FiberStackReturn(Base, Total);
  Result := '';
end;

function TestUsableRegion_WritableAtBothEnds: string;
var
  Base: Pointer;
  Total: Int64;
  P: ^Byte;
begin
  Base := FiberStackAcquire(FiberDefaultStackSize, Total);
  AssertTrue('base not nil', Base <> nil);
  P := Base + FiberPageSize;        { first usable byte, just above guard }
  P^ := 170;
  AssertEquals('low end readable', 170, Integer(P^));
  P := Base + Total - 1;            { last usable byte }
  P^ := 85;
  AssertEquals('high end readable', 85, Integer(P^));
  FiberStackReturn(Base, Total);
  Result := '';
end;

function TestPool_ReusesReturnedStack: string;
var
  B1, B2: Pointer;
  T1, T2: Int64;
  CountBefore: Integer;
begin
  B1 := FiberStackAcquire(FiberDefaultStackSize, T1);
  CountBefore := FiberStackPoolCount();
  FiberStackReturn(B1, T1);
  AssertEquals('return parks the stack', CountBefore + 1,
    FiberStackPoolCount());
  B2 := FiberStackAcquire(FiberDefaultStackSize, T2);
  AssertEquals('acquire drains the pool', CountBefore, FiberStackPoolCount());
  AssertTrue('same-size acquire reuses the pooled stack', B1 = B2);
  AssertEquals('pooled stack keeps its size', T1, T2);
  FiberStackReturn(B2, T2);
  Result := '';
end;

function TestPool_SizeClassed_NoWrongSizeHit: string;
var
  BSmall, BBig: Pointer;
  TSmall, TBig: Int64;
begin
  BSmall := FiberStackAcquire(FiberPageSize, TSmall);       { 2 pages total }
  FiberStackReturn(BSmall, TSmall);
  BBig := FiberStackAcquire(FiberDefaultStackSize, TBig);   { 17 pages total }
  AssertTrue('different size must not reuse the pooled stack',
    BSmall <> BBig);
  FiberStackReturn(BBig, TBig);
  { Drain the small one again so the pool state is clean for other tests. }
  BSmall := FiberStackAcquire(FiberPageSize, TSmall);
  FiberStackReturn(BSmall, TSmall);
  Result := '';
end;

function TestSpawnFree_RoundTrip: string;
var
  F: PFiber;
begin
  F := FiberSpawn(nil, nil, 0);
  AssertTrue('spawn returns a fiber', F <> nil);
  AssertTrue('fiber has a stack', F^.StackBase <> nil);
  AssertTrue('fresh fiber not done', not FiberIsDone(F));
  AssertTrue('context SP inside the stack',
    (PtrUInt(F^.Ctx.SP) > PtrUInt(F^.StackBase)) and
    (PtrUInt(F^.Ctx.SP) < PtrUInt(F^.StackBase) + PtrUInt(F^.StackTotal)));
  AssertTrue('context SP 16-byte aligned', (PtrUInt(F^.Ctx.SP) and 15) = 0);
  FiberFree(F);
  Result := '';
end;

begin
  RequirePassed := True;
  AddSuite('FiberStacks', nil, nil, nil, False);
  AddTest('Acquire_PageAlignedAndSized',
    @TestAcquire_PageAlignedAndSized, 'FiberStacks');
  AddTest('Acquire_OddSizeRoundsUp',
    @TestAcquire_OddSizeRoundsUp, 'FiberStacks');
  AddTest('UsableRegion_WritableAtBothEnds',
    @TestUsableRegion_WritableAtBothEnds, 'FiberStacks');
  AddTest('Pool_ReusesReturnedStack',
    @TestPool_ReusesReturnedStack, 'FiberStacks');
  AddTest('Pool_SizeClassed_NoWrongSizeHit',
    @TestPool_SizeClassed_NoWrongSizeHit, 'FiberStacks');
  AddTest('SpawnFree_RoundTrip',
    @TestSpawnFree_RoundTrip, 'FiberStacks');
  RunAllSysTests();
end.
