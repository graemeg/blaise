{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ punit tests for the MULTI-THREADED allocator paths — the P2 acceptance
  tests from concurrent-allocator-design.adoc §Testing strategy:

    * the cross-thread free test (small blocks: allocate on the main
      thread, free on a worker, prove the blocks return to the owning
      arena's freelists by pointer identity);
    * the large-block foreign-free path (munmap on foreign free —
      option 2 of §The large-block remote path);
    * a bounded version of the pthread ring stress (memstresscore);

  and the phase-5 abandoned-arena reclamation tests (§Teardown,
  §Reclamation protocol):

    * the global arena registry (arenas register on creation; a worker
      whose arenas are all empty at thread exit has them unmapped by the
      thread-exit hook — registry returns to baseline);
    * the per-arena live-block counter's decrement-at-drain rule (a
      foreign free does NOT decrement at push time; the owner's drain
      does);
    * adoption + unmap-when-empty-and-abandoned (a worker exits holding
      live blocks — its arenas are abandoned, the main thread's foreign
      frees land on the abandoned queue, and the reclamation sweep
      adopts, drains and unmaps them);
    * a bounded worker-churn stress (generations of workers spawned and
      joined mid-run while traffic continues; the registry must return
      to baseline).

  Worker threads deliberately use NO punit asserts, NO strings and NO
  I/O: punit's counters are process-global and the string runtime would
  add allocator traffic outside the experiment.  Workers record results
  into plain shared globals; the main thread asserts after pthread_join.

  Build:
    blaise --source runtime/src/test/pascal/test_blaise_mem_mt.pas \
           --unit-path compiler/src/main/pascal \
           --unit-path runtime/src/test/pascal \
           --output /tmp/test_mem_mt
    /tmp/test_mem_mt -v
}

program test_blaise_mem_mt;

uses
  punit, runtime.mem, runtime.thread, memstresscore;

type
  TThreadProc = procedure(Arg: Pointer);

const
  NPerClass = 8;
  NClasses = 8;
  TotalBlocks = 64;    { NPerClass * NClasses }
  MaxPump = 8192;

var
  { Phase-5 shared state (registry / counter / reclamation tests). }
  GCntPtr: Pointer;
  GAbBlocks: array[0..63] of Pointer;

  { Cross-thread small-free shared state (written by main, freed by B). }
  GBlocks: array[0..63] of Pointer;
  GSizes: array[0..63] of Int32;
  GBadPattern: Int64;
  GForeignLeak: Int64;
  GPump: array[0..8191] of Pointer;

  { Cross-thread large-free shared state. }
  GLargePtr: Pointer;
  GLargeSize: Int;
  GLargeBadPattern: Int64;
  GLargeProbeMapped: Int64;
  GLargeProbeOk: Int64;

function ClassSize(C: Int): Int;
begin
  Result := 16 shl C;
end;

{ ------------------------------------------------------------------ }
{ Worker: free the main thread's small blocks (every free is foreign), }
{ then prove none of them landed on THIS thread's freelists.           }
{ ------------------------------------------------------------------ }
procedure SmallFreeWorker(Arg: Pointer);
var
  I, J: Int;
  P: PChar;
  Q: Pointer;
begin
  GBadPattern := -1;
  for I := 0 to TotalBlocks - 1 do
  begin
    { Verify the pattern the main thread wrote — cross-thread read. }
    P := PChar(GBlocks[I]);
    for J := 0 to GSizes[I] - 1 do
      if Int32(P[J]) <> ((J + I) and $FF) then
      begin
        if GBadPattern = -1 then
          GBadPattern := Int64(I) * 100000 + Int64(J);
        Break;
      end;
    _BlaiseFreeMem(GBlocks[I]);
  end;
  { Control (design §Cross-thread free test, step 5): this thread never
    freed anything locally, so an allocation here must come from its own
    fresh arena — never from the foreign-freed set. }
  GForeignLeak := 0;
  for I := 0 to NClasses - 1 do
  begin
    Q := _BlaiseGetMem(ClassSize(I));
    for J := 0 to TotalBlocks - 1 do
      if Q = GBlocks[J] then
        GForeignLeak := GForeignLeak + 1;
    _BlaiseFreeMem(Q);
  end;
end;

{ ------------------------------------------------------------------ }
{ Test: allocate on main, free on worker, drain + reuse on main.       }
{ Leak check = every foreign-freed block is recycled back to the main  }
{ thread by pointer identity (returned to the owning arena, not lost   }
{ and not stranded on the worker).                                     }
{ ------------------------------------------------------------------ }
function Test_CrossThread_SmallFree: string;
var
  I, C, J, K, Sz, PumpCount, Rc, RcJoin, PumpNilFails: Int;
  P: PChar;
  Q: Pointer;
  H: Int64;
  Fn: TThreadProc;
  Found: array[0..63] of Boolean;
  FoundPerClass: array[0..7] of Int32;
begin
  for C := 0 to NClasses - 1 do
    for I := 0 to NPerClass - 1 do
    begin
      K := C * NPerClass + I;
      Sz := ClassSize(C);
      GSizes[K] := Sz;
      P := PChar(_BlaiseGetMem(Sz));
      AssertNotNull('alloc class ' + IntToStr(C) + ' #' + IntToStr(I),
                    Pointer(P));
      for J := 0 to Sz - 1 do
        P[J] := (J + K) and $FF;
      GBlocks[K] := Pointer(P);
    end;

  Fn := @SmallFreeWorker;
  H := 0;
  { pthread calls hoisted out of assert argument positions — see the
    stack-alignment note in punit.pas / bugs.txt. }
  Rc := pthread_create(@H, nil, Pointer(Fn), nil);
  RcJoin := pthread_join(H, nil);

  { Drain + reuse: pump allocations of each class until every freed
    pointer has been handed back to THIS thread.  The empty-freelist
    head-arena drain and the arena-exhaustion drain-all guarantee
    progress; MaxPump bounds the walk (worst case: one full arena of
    the smallest class plus pre-existing freelist entries).

    IMPORTANT: the join -> pump window and the pump itself perform NO
    punit asserts and NO string operations.  Assert messages allocate
    small blocks, and a long-lived punit allocation that captures a
    drained test block would break the pointer-identity check.  All
    assertions run after the pump. }
  for K := 0 to TotalBlocks - 1 do
    Found[K] := False;
  PumpNilFails := 0;
  for C := 0 to NClasses - 1 do
  begin
    FoundPerClass[C] := 0;
    PumpCount := 0;
    while (FoundPerClass[C] < NPerClass) and (PumpCount < MaxPump) do
    begin
      Q := _BlaiseGetMem(ClassSize(C));
      if Q = nil then
      begin
        PumpNilFails := PumpNilFails + 1;
        Break;
      end;
      GPump[PumpCount] := Q;
      PumpCount := PumpCount + 1;
      for I := 0 to NPerClass - 1 do
      begin
        K := C * NPerClass + I;
        if (not Found[K]) and (Q = GBlocks[K]) then
        begin
          Found[K] := True;
          FoundPerClass[C] := FoundPerClass[C] + 1;
        end;
      end;
    end;
    for I := 0 to PumpCount - 1 do
      _BlaiseFreeMem(GPump[I]);
  end;

  AssertEquals('pthread_create', 0, Rc);
  AssertEquals('pthread_join', 0, RcJoin);
  AssertEquals('patterns intact when read on the freeing thread',
               Int64(-1), GBadPattern);
  AssertEquals('no foreign-freed block on the worker''s freelists',
               Int64(0), GForeignLeak);
  AssertEquals('pump allocations all succeeded', 0, PumpNilFails);
  for C := 0 to NClasses - 1 do
    AssertEquals('class ' + IntToStr(C)
                 + ': all foreign-freed blocks recycled to the owner',
                 NPerClass, FoundPerClass[C]);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Worker: free the main thread's LARGE block (foreign), then prove the }
{ block was NOT captured by this thread's large LIFO cache.  The probe }
{ is the TotalMapped header field of a subsequent smaller allocation:  }
{ a fresh mmap maps exactly PageRound(24 + size) bytes, while a cache  }
{ hit would hand back the big foreign mapping (TotalMapped large).     }
{ Address identity is deliberately NOT used — the kernel readily       }
{ reuses a just-munmapped range for the next mmap.                     }
{ ------------------------------------------------------------------ }
procedure LargeFreeWorker(Arg: Pointer);
var
  P: PChar;
  Q: Pointer;
  I: Int;
  MappedP: ^Int64;
begin
  P := PChar(GLargePtr);
  GLargeBadPattern := -1;
  I := 0;
  while I < GLargeSize do
  begin
    if Int32(P[I]) <> ((I * 7) and $FF) then
    begin
      GLargeBadPattern := I;
      Break;
    end;
    I := I + 997;
  end;

  _BlaiseFreeMem(GLargePtr);              { FOREIGN large free }

  { Probe: allocate a much smaller large block.  8192 + 24 rounds to
    12288 mapped bytes; a buggy cache capture would return the foreign
    256 KiB mapping instead. }
  Q := _BlaiseGetMem(8192);
  GLargeProbeOk := 0;
  if Q <> nil then
    GLargeProbeOk := 1;
  MappedP := Pointer(UInt(Q) - 24);
  GLargeProbeMapped := MappedP^;
  _BlaiseFreeMem(Q);                       { local free — cached here }
end;

function Test_CrossThread_LargeFree: string;
var
  P: PChar;
  I, Rc: Int;
  H: Int64;
  Fn: TThreadProc;
  Q: PChar;
begin
  GLargeSize := 262144;
  P := PChar(_BlaiseGetMem(GLargeSize));
  AssertNotNull('large alloc on main', Pointer(P));
  I := 0;
  while I < GLargeSize do
  begin
    P[I] := (I * 7) and $FF;
    I := I + 997;
  end;
  GLargePtr := Pointer(P);

  Fn := @LargeFreeWorker;
  H := 0;
  Rc := pthread_create(@H, nil, Pointer(Fn), nil);
  AssertEquals('pthread_create', 0, Rc);
  Rc := pthread_join(H, nil);
  AssertEquals('pthread_join', 0, Rc);

  AssertEquals('pattern intact when read on the freeing thread',
               Int64(-1), GLargeBadPattern);
  AssertEquals('worker probe alloc succeeded', Int64(1), GLargeProbeOk);
  AssertEquals('foreign large free munmaps — worker cache did not '
               + 'capture the foreign mapping',
               Int64(12288), GLargeProbeMapped);

  { The owner must still be fully functional afterwards. }
  Q := PChar(_BlaiseGetMem(GLargeSize));
  AssertNotNull('main can allocate large again', Pointer(Q));
  Q[0] := 42;
  Q[GLargeSize - 1] := 43;
  AssertEquals('new large block writable (first)', 42, Int32(Q[0]));
  AssertEquals('new large block writable (last)', 43,
               Int32(Q[GLargeSize - 1]));
  _BlaiseFreeMem(Pointer(Q));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: bounded pthread ring stress (suite-friendly run of the P2      }
{ stress; the standalone long run lives in stress_blaise_mem_mt.pas).  }
{ ------------------------------------------------------------------ }
function Test_Stress_Bounded: string;
var
  Bad: Int64;
begin
  Bad := RunMemStress(4, 30000);
  AssertEquals('stress integrity failures', Int64(0), Bad);
  AssertEquals('stress allocation failures', Int64(0), StressAllocFails());
  AssertTrue('stress performed allocations', StressAllocTotal() > 0);
  AssertEquals('terminal drain balances: allocated = freed',
               StressAllocTotal(), StressFreeTotal());
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Phase 5: live-block counter — decrement-at-drain rule.               }
{ A foreign free must NOT decrement the owning arena's live-block      }
{ counter at push time; the decrement happens when the owner drains    }
{ (concurrent-allocator-design.adoc §Reclamation protocol).            }
{ ------------------------------------------------------------------ }
procedure CounterFreeWorker(Arg: Pointer);
begin
  _BlaiseFreeMem(GCntPtr);   { foreign free — remote push, no decrement }
end;

function Test_LiveCounter_DecrementAtDrain: string;
var
  R, Q: Pointer;
  BeforeLocal, AfterLocal: Int64;
  BeforeRemote, AfterPush, AfterDrain: Int64;
  H: Int64;
  Rc, RcJoin: Int;
  Fn: TThreadProc;
begin
  { Local free decrements immediately. }
  R := _BlaiseGetMem(48);
  BeforeLocal := _MemArenaLiveBlocks(R);
  _BlaiseFreeMem(R);
  AfterLocal := _MemArenaLiveBlocks(R);   { header survives a free }

  { Foreign free: no decrement at push; decrement at the owner's drain. }
  Q := _BlaiseGetMem(48);
  GCntPtr := Q;
  BeforeRemote := _MemArenaLiveBlocks(Q);
  Fn := @CounterFreeWorker;
  H := 0;
  Rc := pthread_create(@H, nil, Pointer(Fn), nil);
  RcJoin := pthread_join(H, nil);
  AfterPush := _MemArenaLiveBlocks(Q);
  _MemDrainRemoteFrees();
  AfterDrain := _MemArenaLiveBlocks(Q);

  AssertEquals('pthread_create', 0, Rc);
  AssertEquals('pthread_join', 0, RcJoin);
  AssertEquals('local free decrements the live-block counter',
               BeforeLocal - 1, AfterLocal);
  AssertEquals('foreign push does NOT decrement (decrement-at-drain)',
               BeforeRemote, AfterPush);
  AssertEquals('owner drain performs the decrement',
               BeforeRemote - 1, AfterDrain);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Phase 5: registry + thread-exit hook.  A worker that frees all its   }
{ blocks locally exits with empty arenas; the exit hook must unmap     }
{ them and the registry must return to its pre-worker size.            }
{ ------------------------------------------------------------------ }
procedure RegistryWorker(Arg: Pointer);
var
  I: Int;
  Ptrs: array[0..255] of Pointer;
begin
  { >2 arenas' worth of traffic on a fresh thread, all freed locally. }
  for I := 0 to 255 do
    Ptrs[I] := _BlaiseGetMem(512);
  for I := 0 to 255 do
    _BlaiseFreeMem(Ptrs[I]);
end;

function Test_Registry_WorkerExitReclaim: string;
var
  R0, R1, A1: Int;
  H: Int64;
  Rc, RcJoin: Int;
  Fn: TThreadProc;
begin
  { Normalise: reclaim any abandoned arenas earlier tests left behind,
    so the baseline below is stable for the duration of this test. }
  _MemReclaimAbandoned();
  R0 := _MemArenaCount();
  Fn := @RegistryWorker;
  H := 0;
  Rc := pthread_create(@H, nil, Pointer(Fn), nil);
  RcJoin := pthread_join(H, nil);
  R1 := _MemArenaCount();
  A1 := _MemAbandonedArenaCount();

  AssertEquals('pthread_create', 0, Rc);
  AssertEquals('pthread_join', 0, RcJoin);
  AssertTrue('registry counts this thread''s arenas', R0 > 0);
  AssertEquals('empty worker arenas unmapped at thread exit '
               + '(registry back to baseline)', R0, R1);
  AssertEquals('no arenas left abandoned', 0, A1);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Phase 5: abandonment + adoption + unmap-when-empty-and-abandoned.    }
{ A worker exits while its blocks are still live: its arenas must be   }
{ abandoned (not unmapped).  The main thread's frees are foreign       }
{ pushes onto the abandoned queues; the reclamation sweep then adopts, }
{ drains and unmaps — registry back to baseline.                       }
{ ------------------------------------------------------------------ }
procedure AbandonWorker(Arg: Pointer);
var
  I: Int;
begin
  for I := 0 to 63 do
    GAbBlocks[I] := _BlaiseGetMem(256);
  { exits WITHOUT freeing — every block stays live in its arenas }
end;

function Test_Abandoned_AdoptAndReclaim: string;
var
  R0, RAbandoned, AAbandoned, RAfter, AAfter, Reclaimed: Int;
  I: Int;
  H: Int64;
  Rc, RcJoin: Int;
  Fn: TThreadProc;
begin
  _MemReclaimAbandoned();
  R0 := _MemArenaCount();
  Fn := @AbandonWorker;
  H := 0;
  Rc := pthread_create(@H, nil, Pointer(Fn), nil);
  RcJoin := pthread_join(H, nil);
  RAbandoned := _MemArenaCount();
  AAbandoned := _MemAbandonedArenaCount();

  { Foreign frees onto the dead worker's abandoned arenas. }
  for I := 0 to 63 do
    _BlaiseFreeMem(GAbBlocks[I]);

  Reclaimed := _MemReclaimAbandoned();
  RAfter := _MemArenaCount();
  AAfter := _MemAbandonedArenaCount();

  AssertEquals('pthread_create', 0, Rc);
  AssertEquals('pthread_join', 0, RcJoin);
  AssertTrue('worker arenas stay registered after exit (live blocks)',
             RAbandoned > R0);
  AssertTrue('worker arenas are marked abandoned, not unmapped',
             AAbandoned > 0);
  AssertTrue('reclamation sweep unmapped the drained arenas',
             Reclaimed > 0);
  AssertEquals('registry back to baseline after adopt+drain+unmap',
               R0, RAfter);
  AssertEquals('no abandoned arenas remain', 0, AAfter);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Phase 5: bounded worker-churn stress — workers spawned and joined    }
{ mid-run while allocation traffic continues.  Integrity + terminal    }
{ balance + the reclamation guarantee (registry returns to baseline,   }
{ no abandoned arenas survive).                                        }
{ ------------------------------------------------------------------ }
function Test_Stress_WorkerChurn: string;
var
  R0, R1, A1: Int;
  Bad: Int64;
begin
  _MemReclaimAbandoned();
  R0 := _MemArenaCount();
  Bad := RunChurnStress(4, 6000, 5);
  _MemReclaimAbandoned();
  R1 := _MemArenaCount();
  A1 := _MemAbandonedArenaCount();

  AssertEquals('churn integrity failures', Int64(0), Bad);
  AssertEquals('churn allocation failures', Int64(0), StressAllocFails());
  AssertTrue('churn performed allocations', StressAllocTotal() > 0);
  AssertEquals('terminal drain balances: allocated = freed',
               StressAllocTotal(), StressFreeTotal());
  AssertEquals('no abandoned arenas after churn + reclaim', 0, A1);
  AssertTrue('registry returned to baseline after churn '
             + '(worker arenas reclaimed): R1=' + IntToStr(R1)
             + ' R0=' + IntToStr(R0), R1 <= R0 + 8);
  Result := '';
end;

begin
  AddSuite('blaise_mem_mt', nil);
  AddTest('CrossThread_SmallFree', @Test_CrossThread_SmallFree, 'blaise_mem_mt');
  AddTest('CrossThread_LargeFree', @Test_CrossThread_LargeFree, 'blaise_mem_mt');
  AddTest('Stress_Bounded', @Test_Stress_Bounded, 'blaise_mem_mt');
  AddTest('LiveCounter_DecrementAtDrain', @Test_LiveCounter_DecrementAtDrain,
          'blaise_mem_mt');
  AddTest('Registry_WorkerExitReclaim', @Test_Registry_WorkerExitReclaim,
          'blaise_mem_mt');
  AddTest('Abandoned_AdoptAndReclaim', @Test_Abandoned_AdoptAndReclaim,
          'blaise_mem_mt');
  AddTest('Stress_WorkerChurn', @Test_Stress_WorkerChurn, 'blaise_mem_mt');
  RunAllSysTests();
end.
