{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ memstresscore — the pthread producer/consumer allocator stress
  (concurrent-allocator-design.adoc, §The pthread stress, part of the
  P2 GO/NO-GO gate).

  N worker threads form a ring: each thread allocates blocks across all
  small size classes plus periodic large blocks, fills them with a
  self-describing pattern (size + seed stored in the first 8 bytes),
  and hands them to the next thread through a fixed mailbox of atomic
  slots.  Each thread also drains its own inbound mailbox, verifies the
  pattern and frees the block — a free that always executes on a thread
  other than the allocator (the foreign path).  A mailbox slot that is
  still busy makes the producer free its own fresh block locally, so the
  local fast path stays exercised too.

  Shared state is touched only through runtime.atomic primitives; the
  workers use no strings, no punit and no I/O, so the only cross-thread
  machinery under test is the allocator itself.

  Used by test_blaise_mem_mt.pas (bounded, suite-friendly run) and
  stress_blaise_mem_mt.pas (standalone long-running stress). }

unit memstresscore;

interface

{ Runs the ring stress with NThreads workers (clamped to 2..16), each
  performing Iters produce/consume iterations, then performs the
  terminal drain of every mailbox.  Returns the number of integrity
  failures (0 = clean); returns -1 if a worker thread could not be
  created. }
function RunMemStress(NThreads, Iters: Int): Int64;

{ Phase-5 worker-churn stress (concurrent-allocator-design.adoc,
  §Teardown): Gens generations of ring workers are spawned and joined
  while allocation traffic continues — worker iteration counts are
  staggered so some workers exit mid-generation (their arenas are
  abandoned under live ring load and adopted/reclaimed by the survivors'
  refill scans), and the main thread keeps allocating throughout.  Each
  generation ends with the mailbox terminal drain and a reclamation
  sweep.  Returns the number of integrity failures (0 = clean);
  -1 if a worker thread could not be created. }
function RunChurnStress(NThreads, Iters, Gens: Int): Int64;

{ Counters from the most recent RunMemStress / RunChurnStress call. }
function StressAllocTotal: Int64;
function StressFreeTotal: Int64;
function StressAllocFails: Int64;
function StressBadCount: Int64;

implementation

uses
  runtime.mem, runtime.atomic, runtime.thread;

const
  MAXT = 16;
  SLOTS = 64;

type
  TThreadProc = procedure(Arg: Pointer);
  TMailRow = array[0..63] of Pointer;

var
  GMail: array[0..15] of TMailRow;
  GIdx: array[0..15] of Int32;
  GNThreads: Int;
  GIters: Int;
  { Per-worker iteration counts — uniform for RunMemStress, staggered
    for RunChurnStress so some workers exit mid-generation. }
  GItersOf: array[0..15] of Int32;
  GBad: Int64;
  GAllocFail: Int64;
  GAllocTotal: Int64;
  GFreeTotal: Int64;

{ Size schedule: every small class in rotation, with a periodic large
  block (4096..36864 bytes) so the large foreign-free path is hammered
  alongside the small remote-free queue. }
function PickSize(I: Int): Int;
begin
  if (I mod 61) = 0 then
    Result := 4096 + (I mod 5) * 8192
  else
    Result := 16 shl (I mod 8);
end;

{ Self-describing fill: bytes 0..3 hold the size, 4..7 the seed, the
  body up to 256 bytes holds (Seed + J) mod 256, and the final byte is
  patterned too when it lies beyond the checked prefix. }
procedure FillBlock(P: PChar; Sz, Seed: Int);
var
  IP: ^Int32;
  J, Limit: Int;
begin
  IP := Pointer(P);
  IP^ := Sz;
  IP := Pointer(UInt(P) + 4);
  IP^ := Seed;
  Limit := Sz;
  if Limit > 256 then Limit := 256;
  for J := 8 to Limit - 1 do
    P[J] := (Seed + J) and $FF;
  if Sz - 1 >= Limit then
    P[Sz - 1] := (Seed + Sz - 1) and $FF;
end;

function CheckBlock(P: PChar): Boolean;
var
  IP: ^Int32;
  Sz, Seed, J, Limit: Int;
begin
  IP := Pointer(P);
  Sz := IP^;
  IP := Pointer(UInt(P) + 4);
  Seed := IP^;
  { A corrupt size field is itself an integrity failure — and must be
    range-checked before it is used as a read bound. }
  if (Sz < 16) or (Sz > 65536) then Exit(False);
  Limit := Sz;
  if Limit > 256 then Limit := 256;
  for J := 8 to Limit - 1 do
    if Int32(P[J]) <> ((Seed + J) and $FF) then Exit(False);
  if Sz - 1 >= Limit then
    if Int32(P[Sz - 1]) <> ((Seed + Sz - 1) and $FF) then Exit(False);
  Result := True;
end;

procedure StressWorker(Arg: Pointer);
var
  IdxP: ^Int32;
  Idx, Target, I, S, Sz, Seed: Int;
  P: PChar;
  Q: Pointer;
begin
  IdxP := Arg;
  Idx := IdxP^;
  Target := Idx + 1;
  if Target >= GNThreads then Target := 0;
  for I := 0 to GItersOf[Idx] - 1 do
  begin
    { Consume one inbound slot: verify the pattern written by the
      producing thread, then free — a foreign free by construction. }
    S := I mod SLOTS;
    Q := _AtomicXchgPtr(@GMail[Idx][S], nil);
    if Q <> nil then
    begin
      if not CheckBlock(PChar(Q)) then
        _AtomicAddInt64(@GBad, 1);
      _BlaiseFreeMem(Q);
      _AtomicAddInt64(@GFreeTotal, 1);
    end;
    { Produce one block and hand it to the next thread in the ring. }
    Sz := PickSize(I + Idx * 7);
    P := PChar(_BlaiseGetMem(Sz));
    if P = nil then
      _AtomicAddInt64(@GAllocFail, 1)
    else
    begin
      _AtomicAddInt64(@GAllocTotal, 1);
      Seed := (Idx shl 20) + I;
      FillBlock(P, Sz, Seed);
      if not _AtomicCASPtr(@GMail[Target][S], nil, Pointer(P)) then
      begin
        { Slot still busy — free the fresh block locally instead, which
          keeps the local fast path exercised under the same load. }
        _BlaiseFreeMem(Pointer(P));
        _AtomicAddInt64(@GFreeTotal, 1);
      end;
    end;
  end;
end;

{ Terminal drain: every block still in flight in the mailboxes is
  verified and freed by the calling (main) thread.  After this,
  allocated = freed or the run leaked. }
procedure DrainMailboxes;
var
  I, S: Int;
  Q: Pointer;
begin
  for I := 0 to GNThreads - 1 do
    for S := 0 to SLOTS - 1 do
    begin
      Q := _AtomicXchgPtr(@GMail[I][S], nil);
      if Q <> nil then
      begin
        if not CheckBlock(PChar(Q)) then
          _AtomicAddInt64(@GBad, 1);
        _BlaiseFreeMem(Q);
        _AtomicAddInt64(@GFreeTotal, 1);
      end;
    end;
end;

procedure ResetCounters(NThreads: Int);
var
  I, S: Int;
begin
  GNThreads := NThreads;
  GBad := 0;
  GAllocFail := 0;
  GAllocTotal := 0;
  GFreeTotal := 0;
  for I := 0 to MAXT - 1 do
    for S := 0 to SLOTS - 1 do
      GMail[I][S] := nil;
end;

function RunMemStress(NThreads, Iters: Int): Int64;
var
  H: array[0..15] of Int64;
  I, Rc: Int;
  Fn: TThreadProc;
begin
  if NThreads > MAXT then NThreads := MAXT;
  if NThreads < 2 then NThreads := 2;
  GIters := Iters;
  ResetCounters(NThreads);

  Fn := @StressWorker;
  for I := 0 to NThreads - 1 do
  begin
    GIdx[I] := I;
    GItersOf[I] := Iters;
    H[I] := 0;
    Rc := pthread_create(@H[I], nil, Pointer(Fn), Pointer(@GIdx[I]));
    if Rc <> 0 then Exit(-1);
  end;
  for I := 0 to NThreads - 1 do
    pthread_join(H[I], nil);

  DrainMailboxes();
  Result := GBad;
end;

function RunChurnStress(NThreads, Iters, Gens: Int): Int64;
var
  H: array[0..15] of Int64;
  G, I, Rc, S: Int;
  Fn: TThreadProc;
  P: PChar;
  MainBuf: array[0..31] of Pointer;
begin
  if NThreads > MAXT then NThreads := MAXT;
  if NThreads < 2 then NThreads := 2;
  if Gens < 1 then Gens := 1;
  GIters := Iters;
  ResetCounters(NThreads);
  for S := 0 to 31 do
    MainBuf[S] := nil;

  Fn := @StressWorker;
  for G := 0 to Gens - 1 do
  begin
    { Staggered iteration counts: even-index workers run a third of the
      odd ones, so they exit mid-generation while ring traffic to and
      from their arenas continues — their arenas are abandoned under
      live load and adopted/reclaimed by the survivors' refill scans. }
    for I := 0 to NThreads - 1 do
    begin
      GIdx[I] := I;
      if (I and 1) = 0 then
        GItersOf[I] := Iters div 3
      else
        GItersOf[I] := Iters;
      H[I] := 0;
      Rc := pthread_create(@H[I], nil, Pointer(Fn), Pointer(@GIdx[I]));
      if Rc <> 0 then Exit(-1);
    end;

    { Main-thread allocation traffic WHILE the workers churn: alloc,
      fill, verify, free — kept out of the ring totals (it is pure
      local-path load; the balance assertion is about ring blocks). }
    for I := 0 to Iters - 1 do
    begin
      S := I and 31;
      if MainBuf[S] <> nil then
      begin
        if not CheckBlock(PChar(MainBuf[S])) then
          _AtomicAddInt64(@GBad, 1);
        _BlaiseFreeMem(MainBuf[S]);
        MainBuf[S] := nil;
      end;
      P := PChar(_BlaiseGetMem(PickSize(I + G * 13)));
      if P <> nil then
      begin
        FillBlock(P, PickSize(I + G * 13), (G shl 24) + I);
        MainBuf[S] := Pointer(P);
      end;
    end;
    for S := 0 to 31 do
      if MainBuf[S] <> nil then
      begin
        if not CheckBlock(PChar(MainBuf[S])) then
          _AtomicAddInt64(@GBad, 1);
        _BlaiseFreeMem(MainBuf[S]);
        MainBuf[S] := nil;
      end;

    for I := 0 to NThreads - 1 do
      pthread_join(H[I], nil);

    { Generation teardown: free every in-flight block (foreign pushes
      onto the dead workers' abandoned arenas), then run the
      reclamation sweep so empty abandoned arenas are unmapped mid-run,
      not just at the end. }
    DrainMailboxes();
    _MemReclaimAbandoned();
  end;
  Result := GBad;
end;

function StressAllocTotal: Int64;
begin
  Result := GAllocTotal;
end;

function StressFreeTotal: Int64;
begin
  Result := GFreeTotal;
end;

function StressAllocFails: Int64;
begin
  Result := GAllocFail;
end;

function StressBadCount: Int64;
begin
  Result := GBad;
end;

end.
