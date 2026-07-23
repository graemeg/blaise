{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  blaise_mem — Pascal memory allocator for the Blaise runtime.

  Replaces libc malloc/free/realloc with an allocator backed by POSIX
  mmap/munmap.  Self-contained: no dependency on strings, ARC, or
  any stdlib unit.

  Design:

  Small allocations (up to LARGE_THRESHOLD bytes):
    Served from 64 KB arenas obtained via mmap.  Each allocation has
    a 16-byte header storing the usable size and a back-pointer to the
    owning arena (the routing key for the migration-safe cross-thread
    free path — docs/concurrent-allocator-design.adoc).  Freed blocks
    go onto a per-size-class freelist for O(1) reuse.  Size classes are
    powers of two: 16, 32, 64, 128, 256, 512, 1024, 2048.

    Only the head arena is used for bump allocation.  When it fills,
    a new arena is allocated and becomes the head.  No arena-list walk.

  Large allocations (above LARGE_THRESHOLD):
    Each gets its own mmap region with a 24-byte header.  Freed large
    blocks are cached on a LIFO freelist for O(1) reuse.  The cache
    holds up to LARGE_CACHE_MAX entries; excess blocks are munmap-ed
    immediately.  Large reallocs allocate a new region, copy, and free
    the old one.  All mmap sizes are rounded up to page granularity
    (4 KB) for better cache hit rates.

  All returned pointers are 8-byte aligned.

  Thread safety:
    All allocator state (arenas, freelists, large-block cache) is
    declared as threadvar, giving each thread its own independent
    allocator instance with zero contention and no locks on the local
    paths.  Spawned threads start with nil arenas and empty freelists;
    their first allocation creates a fresh arena via mmap.  Memory
    allocated on one thread MAY be freed on another: a foreign free is
    routed back to the owning arena through its MPSC remote-free queue
    and drained by the owner (concurrent-allocator-design.adoc).

  Teardown (phase 5, §Teardown of the design):
    Every arena is registered on a process-global registry (CAS
    spinlock).  A thread-exit hook (pthread TSD destructor for workers,
    __cxa_atexit for the main thread) unmaps the exiting thread's fully
    free arenas and marks the rest abandoned (OwnerTid = 0); abandoned
    arenas are later adopted or unmapped by the reclamation sweep, run
    from the allocation cold path and _MemReclaimAbandoned.  A per-arena
    live-block counter with decrement-at-drain semantics decides "fully
    free".
}

unit runtime.mem;

interface

uses
  runtime.atomic;

function  _BlaiseGetMem(Size: Integer): Pointer;
procedure _BlaiseFreeMem(Ptr: Pointer);
function  _BlaiseReallocMem(Ptr: Pointer; NewSize: Integer): Pointer;

{ Phase-5 teardown / reclamation API (concurrent-allocator-design.adoc,
  §Teardown, §Reclamation protocol).  The _Mem* functions below are
  maintenance and diagnostic entry points — none of them is on the
  allocation hot path.  The runtime test suite uses them to observe the
  global arena registry and the per-arena live-block counters. }

{ Number of arenas on the process-global arena registry. }
function _MemArenaCount: Integer;

{ Number of registered arenas that are abandoned (OwnerTid = 0: their
  owning thread has exited and no thread has adopted them yet). }
function _MemAbandonedArenaCount: Integer;

{ Live-block counter of the arena owning the given SMALL block.  The
  counter counts blocks in use or still in flight on the arena's remote
  queue — a remote push does NOT decrement it; the owner's drain does
  (decrement-at-drain).  Valid for small blocks only; the block header
  survives a free, so Ptr may name a freed block whose arena is still
  mapped. }
function _MemArenaLiveBlocks(Ptr: Pointer): Int64;

{ Drain every remote-free queue of the arenas the CALLING thread owns
  onto its local freelists (the owner-side consume step, on demand). }
procedure _MemDrainRemoteFrees;

{ The reclamation sweep: adopt every abandoned arena on the registry
  (CAS OwnerTid 0 -> caller), drain its remote queue, and either unmap
  it (fully free once drained — unlinked under the registry lock, so
  adoption and unmap are serialised) or keep it as the caller's own.
  Also run from the allocation cold path before a fresh arena is
  mapped.  Returns the number of arenas unmapped. }
function _MemReclaimAbandoned: Integer;

implementation

function  _libc_mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Integer;
            Offset: Int64): Pointer; external name 'mmap';
function  _libc_munmap(Addr: Pointer; Length: Int64): Integer;
            external name 'munmap';
procedure _libc_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

{ Thread-exit hook bindings (phase 5).  pthread_key_create registers a
  TSD destructor that pthreads runs on worker-thread exit; __cxa_atexit
  covers the main thread (key destructors do not run for it).  The
  static (libc-free) build resolves these from no-op seams in
  runtime.thread.static.* — its worker threads exit via SYS_exit with
  no TSD machinery, so their arenas are reclaimed only by later
  adoption or at process exit (the static worker-thread allocator path
  is out of scope; concurrent-allocator-design.adoc §Scope). }
function _pthread_key_create(Key: Pointer; Dtor: Pointer): Integer;
  external name 'pthread_key_create';
{ Key is pthread_key_t — 64-bit on Darwin.  Declaring the parameter Integer
  truncated it (harmless while keys are small, but wrong by type). }
function _pthread_setspecific(Key: Int64; Value: Pointer): Integer;
  external name 'pthread_setspecific';
function _libc_cxa_atexit(Fn, Arg, DsoHandle: Pointer): Integer;
  external name '__cxa_atexit';

{ OS-specific MAP_ANONYMOUS value, provided by the linked platform layout
  unit (rtl.platform.layout.<os>).  Linux = $20, FreeBSD = $1000.  A flat
  function rather than a GPlatformLayout virtual call because the allocator
  runs before the platform layer is initialised. }
function  _MapAnonFlag: Integer; external name '_MapAnonFlag';

const
  PROT_READ       = 1;
  PROT_WRITE      = 2;
  MAP_PRIVATE     = 2;
  MAP_FAILED_VAL  = -1;

  PAGE_SIZE       = 4096;
  ARENA_SIZE      = 65536;
  LARGE_THRESHOLD = 2048;
  HEADER_SIZE     = 16;
  LARGE_HEADER    = 24;
  LARGE_CACHE_MAX = 32;

{ CROSS-LAYOUT INVARIANT (concurrent-allocator-design.adoc, §Data
  structures): IsLarge and GetAllocSize classify a block by reading Flags
  through the SMALL layout at Ptr - HEADER_SIZE, regardless of the block
  kind.  This works only because both layouts place Flags at the same
  distance from the user pointer:

    small: Ptr - 16 + 4  = Ptr - 12
    large: Ptr - 24 + 12 = Ptr - 12

  New fields must therefore be appended AFTER Flags in both records;
  reordering either silently breaks every free.  The invariant is pinned
  by Test_FlagsOffset_Invariant in test_blaise_mem.pas. }

type
  PArena = ^TArena;

  PBlockHeader = ^TBlockHeader;
  TBlockHeader = record
    AllocSize: Integer;
    Flags:     Integer;
    Arena:     PArena;   { owning arena — the cross-thread routing key }
  end;

  PLargeHeader = ^TLargeHeader;
  TLargeHeader = record
    TotalMapped: Int64;
    AllocSize:   Integer;
    Flags:       Integer;
    OwnerTid:    Int64;  { allocating thread's tid (MyTid).  LargeFreeMem
                           caches on a local free and munmaps on a
                           foreign one (concurrent-allocator-design.adoc,
                           §The large-block remote path, option 2) }
  end;

  PFreeNode = ^TFreeNode;
  TFreeNode = record
    Next: PFreeNode;
  end;

  PLargeFreeNode = ^TLargeFreeNode;
  TLargeFreeNode = record
    Next:        PLargeFreeNode;
    TotalMapped: Int64;
  end;

  TArena = record
    Base:     Pointer;
    Offset:   Integer;
    Capacity: Integer;
    Next:     PArena;
    { Migration-safe cross-thread free path (concurrent-allocator-design.adoc).
      OwnerTid identifies the owning thread (0 = abandoned).  It is
      written at creation (before the arena is published), and afterwards
      only under the registry spinlock — abandonment stores 0 via
      _AtomicXchgPtr, adoption CASes 0 -> adopter tid — while the free
      path reads it without the lock (the owner-vs-foreign test).
      RemoteHead is the MPSC remote-free stack head, touched ONLY through
      _AtomicCASPtr (producer push) / _AtomicXchgPtr (owner drain/claim).
      RemoteList links the arena onto the process-global arena registry
      (phase 5), mutated only under the registry spinlock.
      LiveCount is the live-block counter (§Reclamation protocol):
      +1 per allocation from the arena, -1 per LOCAL free, -1 per block
      at DRAIN time (never at remote-push time — decrement-at-drain).
      All mutations go through _AtomicAddInt64; only the current owner
      mutates it, and ownership handoff is serialised by the registry
      lock, so a zero observed by the owner is stable: a remote push
      requires the pusher to hold a live (counted) block. }
    OwnerTid:   Int64;
    RemoteHead: Pointer;
    RemoteList: PArena;
    LiveCount:  Int64;
  end;

  { A foreign-freed block's intrusive node, living in the block's user
    bytes while it waits on an arena's RemoteHead.  SizeClass lets the
    draining owner file it without re-reading the block header.  16 bytes
    with default alignment — fits even the smallest (16-byte) class. }
  PRemoteNode = ^TRemoteNode;
  TRemoteNode = record
    Next:      PRemoteNode;
    SizeClass: Integer;
  end;

const
  FLAG_LARGE = 1;
  FLAG_SMALL = 0;

threadvar
  FreeLists: array[0..7] of PFreeNode;
  ArenaHead: PArena;
  LargeFreeHead: PLargeFreeNode;
  LargeFreeCount: Integer;
  { Cross-thread free path state.  TidAnchor exists only for its per-thread
    TLS address (see MyTid); FreeDrainCounter and DrainCursor implement the
    periodic rotating free-side drain. }
  TidAnchor: Int64;
  FreeDrainCounter: Integer;
  DrainCursor: PArena;
  { True once this thread's exit hook is armed (pthread_setspecific with a
    non-nil value, so the TSD destructor fires at thread exit). }
  ExitHookArmed: Boolean;

{ Process-global reclamation state (phase 5).  Everything below is
  mutated only while GRegLock is held; GAbandonedCount is additionally
  READ without the lock as the allocation cold path's cheap "is there
  anything to reclaim?" pre-check (a stale read is benign — it only
  skips or wastes one sweep). }
var
  GRegLock: Pointer;           { CAS spinlock word: nil = free }
  GArenaRegistry: PArena;      { all live arenas, linked via RemoteList }
  GAbandonedCount: Int64;      { registered arenas with OwnerTid = 0 }
  GHooksReady: Integer;        { pthread key + atexit registered once }
  { pthread_key_t of the exit destructor.  MUST be 64-bit: pthread_key_create
    writes a full pthread_key_t through this pointer, and on Darwin (arm64 and
    x86-64 alike) that type is 64 bits.  Declaring it Integer made the call
    write 4 bytes past the variable, silently clobbering GExitKeyValue — a real
    out-of-bounds global write (found auditing the 2026-07-23 macOS arm64
    allocator failure). }
  GExitKey: Int64;
  GExitKeyValue: Int64;        { its per-thread value: any non-nil ptr }

{ Registry spinlock — CAS built on the allocator's own atomic leaves,
  deliberately NOT a pthread_mutex, so runtime.mem stays free of libc
  object dependencies (design §Teardown).  All critical sections are
  short, cold-path walks (arena create/abandon/adopt/unmap/probes). }
procedure RegLockAcquire;
begin
  while not _AtomicCASPtr(@GRegLock, nil, @GRegLock) do ;
end;

procedure RegLockRelease;
begin
  _AtomicXchgPtr(@GRegLock, nil);
end;

{ Per-thread identity for the owner-vs-foreign test.  The address of a
  threadvar is unique among live threads (each thread has its own TLS
  block) and never zero, which is all OwnerTid needs.  This deliberately
  deviates from the design doc's pthread_self binding: it costs one leaq
  instead of a libc call, needs no pthread_self shim in the static
  (libc-free) build, and is CPU/OS-invariant. }
function MyTid: Int64;
begin
  Result := Int64(PtrUInt(@TidAnchor));
end;

{ Producer side: push a foreign-freed block onto its owning arena's MPSC
  remote-free stack (Treiber push; one CAS, retried on contention with
  another producer).  lock cmpxchg is a full barrier on x86-64, so the
  node-field stores are published before the new head (release). }
procedure RemoteFreePush(Arena: PArena; Ptr: Pointer; SizeClass: Integer);
var
  Node: PRemoteNode;
  OldHead: Pointer;
begin
  Node := PRemoteNode(Ptr);
  Node^.SizeClass := SizeClass;
  repeat
    OldHead := Arena^.RemoteHead;
    Node^.Next := PRemoteNode(OldHead);
  until _AtomicCASPtr(@Arena^.RemoteHead, OldHead, Pointer(Node));
end;

{ Consumer side: the OWNING thread claims the whole remote stack with one
  atomic exchange, then walks the now-private list with no atomics and
  files each block onto its normal freelist.  Only the owner ever drains
  its arenas — the single-consumer guarantee that makes the walk safe. }
procedure DrainRemoteFrees(Arena: PArena);
var
  Claimed, Nxt: PRemoteNode;
  FNode: PFreeNode;
  N: Int64;
begin
  if Arena^.RemoteHead = nil then Exit;
  Claimed := PRemoteNode(_AtomicXchgPtr(@Arena^.RemoteHead, nil));
  N := 0;
  while Claimed <> nil do
  begin
    Nxt := Claimed^.Next;
    FNode := PFreeNode(Claimed);
    FNode^.Next := FreeLists[Claimed^.SizeClass];
    FreeLists[Claimed^.SizeClass] := FNode;
    N := N + 1;
    Claimed := Nxt;
  end;
  { Decrement-at-drain (§Reclamation protocol): the live-block counter
    drops only now that the blocks are filed, never at push time — so
    LiveCount = 0 can never be observed while nodes still sit on the
    remote queue's backing pages. }
  if N <> 0 then
    _AtomicAddInt64(@Arena^.LiveCount, -N);
end;

{ Cold path: drain every arena the calling thread owns.  Used before
  growing the arena list — reclaiming foreign frees can avoid the mmap. }
procedure DrainAllRemoteFrees;
var
  A: PArena;
begin
  A := ArenaHead;
  while A <> nil do
  begin
    DrainRemoteFrees(A);
    A := A^.Next;
  end;
end;

{ Unlink an arena from the global registry.  Caller holds GRegLock. }
procedure RegistryUnlink(Arena: PArena);
var
  R, Prev: PArena;
begin
  Prev := nil;
  R := GArenaRegistry;
  while (R <> nil) and (R <> Arena) do
  begin
    Prev := R;
    R := R^.RemoteList;
  end;
  if R = Arena then
  begin
    if Prev = nil then
      GArenaRegistry := Arena^.RemoteList
    else
      Prev^.RemoteList := Arena^.RemoteList;
  end;
end;

{ The reclamation sweep (§Teardown, §Reclamation protocol).  Walks the
  registry under the spinlock; every abandoned arena is ADOPTED (CAS
  OwnerTid 0 -> caller tid — atomic because the free path reads OwnerTid
  without the lock), its remote queue is claimed and counted, and then:

    * fully free once drained (LiveCount - claimed = 0) — the claimed
      nodes are discarded WITH the mapping: unlink from the registry
      (under the lock, so no other sweep can adopt it) and munmap.
      LiveCount = 0 is stable — a remote push requires the pusher to
      hold a live, counted block, and none remain;
    * still-live blocks — the claimed nodes are filed onto the caller's
      freelists (with the matching counter decrement) and the arena is
      linked into the caller's working set behind the bump head; its
      future foreign frees are routed to the caller as owner.

  Returns the number of arenas unmapped. }
function ReclaimAbandonedSweep: Integer;
var
  A, Nxt: PArena;
  Claimed, Node, NodeNext: PRemoteNode;
  FNode: PFreeNode;
  N: Int64;
  Tid: Int64;
begin
  Result := 0;
  Tid := MyTid();
  RegLockAcquire();
  A := GArenaRegistry;
  while A <> nil do
  begin
    Nxt := A^.RemoteList;
    if A^.OwnerTid = 0 then
    begin
      if _AtomicCASPtr(@A^.OwnerTid, nil, Pointer(PtrUInt(Tid))) then
      begin
        GAbandonedCount := GAbandonedCount - 1;
        { Claim and count the remote queue (the adopter is now the
          single consumer). }
        Claimed := PRemoteNode(_AtomicXchgPtr(@A^.RemoteHead, nil));
        N := 0;
        Node := Claimed;
        while Node <> nil do
        begin
          N := N + 1;
          Node := Node^.Next;
        end;
        if A^.LiveCount - N = 0 then
        begin
          { Unmap-when-empty-and-abandoned: unlink first (still under
            the lock), then release the mapping — the claimed nodes'
            bytes live inside it and are discarded with it. }
          RegistryUnlink(A);
          _libc_munmap(A^.Base, Int64(A^.Capacity));
          Inc(Result);
        end
        else
        begin
          if N <> 0 then
            _AtomicAddInt64(@A^.LiveCount, -N);
          Node := Claimed;
          while Node <> nil do
          begin
            NodeNext := Node^.Next;
            FNode := PFreeNode(Node);
            FNode^.Next := FreeLists[Node^.SizeClass];
            FreeLists[Node^.SizeClass] := FNode;
            Node := NodeNext;
          end;
          if ArenaHead = nil then
          begin
            A^.Next := nil;
            ArenaHead := A;
          end
          else
          begin
            A^.Next := ArenaHead^.Next;
            ArenaHead^.Next := A;
          end;
        end;
      end;
    end;
    A := Nxt;
  end;
  RegLockRelease();
end;

{ Thread-exit sweep: run for a worker thread by the pthread TSD
  destructor and for the main thread by the __cxa_atexit handler
  (§Teardown).  Both run ON the owning thread, so its threadvars are
  still valid.  For every arena the thread owns:

    * fully free (after claiming + counting the remote queue) — unlink
      from the registry and munmap right here; no abandonment needed;
    * still-live blocks — RE-PUBLISH the claimed remote chain (a plain
      producer push of the whole chain; the count stays untouched so the
      future adopter's drain performs the decrement), then mark the
      arena abandoned (OwnerTid := 0, atomically — unlocked free-path
      readers).  It stays on the registry for adoption/reclamation.

  Afterwards the thread's allocator threadvars are reset: freelist
  entries pointing into unmapped or abandoned arenas must not survive.
  Blocks that sat on the local freelists of a NOW-ABANDONED arena lie
  fallow inside it until the arena drains empty and is unmapped —
  internal fragmentation, not a process-footprint leak (design note). }
procedure SweepThisThread;
var
  A, Nxt: PArena;
  Claimed, Node, Tail: PRemoteNode;
  N: Int64;
  OldHead: Pointer;
  I: Integer;
begin
  if ArenaHead <> nil then
  begin
    RegLockAcquire();
    A := ArenaHead;
    while A <> nil do
    begin
      Nxt := A^.Next;
      Claimed := PRemoteNode(_AtomicXchgPtr(@A^.RemoteHead, nil));
      N := 0;
      Tail := nil;
      Node := Claimed;
      while Node <> nil do
      begin
        N := N + 1;
        Tail := Node;
        Node := Node^.Next;
      end;
      if A^.LiveCount - N = 0 then
      begin
        RegistryUnlink(A);
        _libc_munmap(A^.Base, Int64(A^.Capacity));
      end
      else
      begin
        if Claimed <> nil then
        begin
          { Push the claimed chain back for the adopter (Treiber push of
            a whole chain; concurrent pushes may land above it). }
          repeat
            OldHead := A^.RemoteHead;
            Tail^.Next := PRemoteNode(OldHead);
          until _AtomicCASPtr(@A^.RemoteHead, OldHead, Pointer(Claimed));
        end;
        _AtomicXchgPtr(@A^.OwnerTid, nil);
        GAbandonedCount := GAbandonedCount + 1;
      end;
      A := Nxt;
    end;
    RegLockRelease();
  end;
  ArenaHead := nil;
  DrainCursor := nil;
  for I := 0 to 7 do
    FreeLists[I] := nil;
end;

{ TSD destructor (worker threads) and atexit handler (main thread).
  Signatures match void (*)(void *). }
procedure MemThreadExitSweep(Value: Pointer);
begin
  SweepThisThread();
end;

procedure MemAtExitSweep(Arg: Pointer);
begin
  SweepThisThread();
end;

{ Arm the exit hooks: once per process, register the TSD destructor and
  the atexit sweep; once per thread, set a non-nil TSD value so the
  destructor actually fires for this thread (§Teardown — "Why a
  thread-exit hook exists, and how").  Called from AllocArena, i.e. only
  on the arena-creation cold path. }
procedure EnsureExitHooks;
begin
  if ExitHookArmed then Exit;
  RegLockAcquire();
  if GHooksReady = 0 then
  begin
    _pthread_key_create(@GExitKey, Pointer(@MemThreadExitSweep));
    _libc_cxa_atexit(Pointer(@MemAtExitSweep), nil, nil);
    GHooksReady := 1;
  end;
  RegLockRelease();
  _pthread_setspecific(GExitKey, @GExitKeyValue);
  ExitHookArmed := True;
end;

function MapFailed(P: Pointer): Boolean;
begin
  Result := (P = nil) or (PtrUInt(P) = PtrUInt(MAP_FAILED_VAL));
end;

function PageRound(Size: Int64): Int64;
begin
  Result := (Size + Int64(PAGE_SIZE - 1)) and Int64($FFFFFFFFFFFFF000);
end;

function MmapAlloc(Size: Int64): Pointer;
begin
  Size := PageRound(Size);
  Result := _libc_mmap(nil, Size,
    PROT_READ or PROT_WRITE,
    MAP_PRIVATE or _MapAnonFlag(),
    -1, 0);
  if MapFailed(Result) then
    Result := nil;
end;

function SizeClassIndex(Size: Integer): Integer;
begin
  if Size <= 16 then begin Result := 0; Exit end;
  if Size <= 32 then begin Result := 1; Exit end;
  if Size <= 64 then begin Result := 2; Exit end;
  if Size <= 128 then begin Result := 3; Exit end;
  if Size <= 256 then begin Result := 4; Exit end;
  if Size <= 512 then begin Result := 5; Exit end;
  if Size <= 1024 then begin Result := 6; Exit end;
  Result := 7;
end;

function SizeClassBytes(Index: Integer): Integer;
begin
  case Index of
    0: Result := 16;
    1: Result := 32;
    2: Result := 64;
    3: Result := 128;
    4: Result := 256;
    5: Result := 512;
    6: Result := 1024;
  else
    Result := 2048;
  end;
end;

function RoundUpToClass(Size: Integer): Integer;
begin
  Result := SizeClassBytes(SizeClassIndex(Size));
end;

function AllocArena: PArena;
var
  Base: Pointer;
  A: PArena;
begin
  Base := MmapAlloc(Int64(ARENA_SIZE));
  if Base = nil then
  begin
    Exit(nil);
  end;
  A := PArena(Base);
  A^.Base := Base;
  A^.Offset := SizeOf(TArena);
  A^.Capacity := ARENA_SIZE;
  A^.Next := ArenaHead;
  A^.OwnerTid := MyTid();
  A^.RemoteHead := nil;
  A^.RemoteList := nil;
  A^.LiveCount := 0;
  ArenaHead := A;
  { Publish on the global registry (phase 5) — fully initialised first,
    so a registry walker never sees a half-built arena. }
  RegLockAcquire();
  A^.RemoteList := GArenaRegistry;
  GArenaRegistry := A;
  RegLockRelease();
  EnsureExitHooks();
  Result := A;
end;

function ArenaAlloc(Size: Integer): Pointer;
var
  A: PArena;
  BlockSize, Needed: Integer;
  Hdr: PBlockHeader;
  Node: PFreeNode;
  Idx: Integer;
begin
  BlockSize := RoundUpToClass(Size);
  Needed := HEADER_SIZE + BlockSize;

  A := ArenaHead;
  if (A <> nil) and (A^.Offset + Needed <= A^.Capacity) then
  begin
    Hdr := Pointer(PtrUInt(A^.Base) + PtrUInt(A^.Offset));
    Hdr^.AllocSize := Size;
    Hdr^.Flags := FLAG_SMALL;
    Hdr^.Arena := A;
    A^.Offset := A^.Offset + Needed;
    _AtomicAddInt64(@A^.LiveCount, 1);
    Exit(Pointer(PtrUInt(Hdr) + HEADER_SIZE));
  end;

  { Head arena exhausted (cold path).  Drain every owned arena's remote
    queue first — a foreign-freed block of the needed class avoids the
    mmap entirely.  If abandoned arenas exist (dead workers), run the
    reclamation sweep too: adoption may recycle a whole arena instead of
    mapping fresh (§Teardown — adoption).  The GAbandonedCount pre-check
    keeps this branch a single load for every program without worker
    churn. }
  DrainAllRemoteFrees();
  if GAbandonedCount <> 0 then
    ReclaimAbandonedSweep();
  Idx := SizeClassIndex(Size);
  Node := FreeLists[Idx];
  if Node <> nil then
  begin
    FreeLists[Idx] := Node^.Next;
    Hdr := PBlockHeader(Pointer(PtrUInt(Node) - HEADER_SIZE));
    Hdr^.AllocSize := Size;
    A := Hdr^.Arena;
    _AtomicAddInt64(@A^.LiveCount, 1);
    Exit(Pointer(Node));
  end;

  A := AllocArena();
  if A = nil then
  begin
    Exit(nil);
  end;
  Hdr := Pointer(PtrUInt(A^.Base) + PtrUInt(A^.Offset));
  Hdr^.AllocSize := Size;
  Hdr^.Flags := FLAG_SMALL;
  Hdr^.Arena := A;
  A^.Offset := A^.Offset + Needed;
  _AtomicAddInt64(@A^.LiveCount, 1);
  Result := Pointer(PtrUInt(Hdr) + HEADER_SIZE);
end;

function SmallGetMem(Size: Integer): Pointer;
var
  Idx: Integer;
  Node: PFreeNode;
  Hdr: PBlockHeader;
  A: PArena;
begin
  Idx := SizeClassIndex(Size);

  Node := FreeLists[Idx];
  if (Node = nil) and (ArenaHead <> nil)
     and (ArenaHead^.RemoteHead <> nil) then
  begin
    { Empty freelist: drain the head arena's remote queue first — a
      foreign free of this class satisfies the request without growing
      the arena.  The nil check above keeps the non-fiber fast path at
      one load + not-taken branch. }
    DrainRemoteFrees(ArenaHead);
    Node := FreeLists[Idx];
  end;
  if Node <> nil then
  begin
    FreeLists[Idx] := Node^.Next;
    Hdr := PBlockHeader(Pointer(PtrUInt(Node) - HEADER_SIZE));
    Hdr^.AllocSize := Size;
    A := Hdr^.Arena;
    _AtomicAddInt64(@A^.LiveCount, 1);
    Exit(Pointer(Node));
  end;

  Result := ArenaAlloc(Size);
end;

procedure SmallFreeMem(Ptr: Pointer);
var
  Hdr: PBlockHeader;
  Idx: Integer;
  Node: PFreeNode;
  Arena: PArena;
begin
  Hdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
  Idx := SizeClassIndex(Hdr^.AllocSize);
  Arena := Hdr^.Arena;

  if Arena^.OwnerTid = MyTid() then
  begin
    { LOCAL fast path — the freelist push is unchanged; the live-block
      counter decrement (phase 5, decrement-at-drain protocol: a LOCAL
      free decrements immediately, a remote push does not) is the one
      atomic the reclamation accounting costs this path. }
    Node := PFreeNode(Ptr);
    Node^.Next := FreeLists[Idx];
    FreeLists[Idx] := Node;
    _AtomicAddInt64(@Arena^.LiveCount, -1);
    { Periodic rotating drain: every 64th local free, drain ONE arena,
      walking ArenaHead -> Next and wrapping, so foreign frees to
      non-head arenas cannot starve regardless of allocation rate. }
    Inc(FreeDrainCounter);
    if (FreeDrainCounter and 63) = 0 then
    begin
      if DrainCursor = nil then
        DrainCursor := ArenaHead;
      if DrainCursor <> nil then
      begin
        DrainRemoteFrees(DrainCursor);
        DrainCursor := DrainCursor^.Next;
      end;
    end;
  end
  else
    { FOREIGN path: the block belongs to another thread's arena — route
      it back via the arena's MPSC remote-free queue; never touch this
      thread's freelists. }
    RemoteFreePush(Arena, Ptr, Idx);
end;

function LargeGetMem(Size: Integer): Pointer;
var
  Total: Int64;
  Base: Pointer;
  Hdr: PLargeHeader;
  Node: PLargeFreeNode;
  Needed, CachedSize: Int64;
begin
  Needed := PageRound(Int64(LARGE_HEADER) + Int64(Size));

  Node := LargeFreeHead;
  if Node <> nil then
  begin
    CachedSize := Node^.TotalMapped;
    LargeFreeHead := Node^.Next;
    Dec(LargeFreeCount);
    if CachedSize >= Needed then
    begin
      Hdr := PLargeHeader(Pointer(Node));
      Hdr^.TotalMapped := CachedSize;
      Hdr^.AllocSize := Size;
      Hdr^.Flags := FLAG_LARGE;
      Hdr^.OwnerTid := MyTid();
      Exit(Pointer(PtrUInt(Hdr) + LARGE_HEADER));
    end;
    { Cached block too small — free it and fall through to a fresh mmap. }
    _libc_munmap(Pointer(Node), CachedSize);
  end;

  Total := Needed;
  Base := MmapAlloc(Total);
  if Base = nil then
  begin
    Exit(nil);
  end;
  Hdr := PLargeHeader(Base);
  Hdr^.TotalMapped := Total;
  Hdr^.AllocSize := Size;
  Hdr^.Flags := FLAG_LARGE;
  Hdr^.OwnerTid := MyTid();
  Result := Pointer(PtrUInt(Base) + LARGE_HEADER);
end;

procedure LargeFreeMem(Ptr: Pointer);
var
  Hdr: PLargeHeader;
  Node: PLargeFreeNode;
begin
  Hdr := PLargeHeader(Pointer(PtrUInt(Ptr) - LARGE_HEADER));
  { Foreign free: a large block is its own private mapping, so any
    thread can munmap it directly — the design's option 2 (§The
    large-block remote path).  Only a LOCAL free may cache the block;
    otherwise a mapping allocated by thread A would sit on thread B's
    threadvar LIFO cache and be handed out from there. }
  if Hdr^.OwnerTid <> MyTid() then
  begin
    _libc_munmap(Pointer(Hdr), Hdr^.TotalMapped);
    Exit;
  end;
  if LargeFreeCount < LARGE_CACHE_MAX then
  begin
    Node := PLargeFreeNode(Pointer(Hdr));
    Node^.TotalMapped := Hdr^.TotalMapped;
    Node^.Next := LargeFreeHead;
    LargeFreeHead := Node;
    Inc(LargeFreeCount);
  end
  else
    _libc_munmap(Pointer(Hdr), Hdr^.TotalMapped);
end;

function IsLarge(Ptr: Pointer): Boolean;
var
  Hdr: PBlockHeader;
begin
  Hdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
  Result := Hdr^.Flags = FLAG_LARGE;
end;

function GetAllocSize(Ptr: Pointer): Integer;
var
  SmallHdr: PBlockHeader;
  LargeHdr: PLargeHeader;
begin
  SmallHdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
  if SmallHdr^.Flags = FLAG_LARGE then
  begin
    LargeHdr := PLargeHeader(Pointer(PtrUInt(Ptr) - LARGE_HEADER));
    Result := LargeHdr^.AllocSize;
  end
  else
    Result := SmallHdr^.AllocSize;
end;

{ ------------------------------------------------------------------ }
{ Phase-5 maintenance / diagnostic API (see interface comments)        }
{ ------------------------------------------------------------------ }

function _MemArenaCount: Integer;
var
  A: PArena;
begin
  Result := 0;
  RegLockAcquire();
  A := GArenaRegistry;
  while A <> nil do
  begin
    Inc(Result);
    A := A^.RemoteList;
  end;
  RegLockRelease();
end;

function _MemAbandonedArenaCount: Integer;
var
  A: PArena;
begin
  Result := 0;
  RegLockAcquire();
  A := GArenaRegistry;
  while A <> nil do
  begin
    if A^.OwnerTid = 0 then
      Inc(Result);
    A := A^.RemoteList;
  end;
  RegLockRelease();
end;

function _MemArenaLiveBlocks(Ptr: Pointer): Int64;
var
  Hdr: PBlockHeader;
  A: PArena;
begin
  Hdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
  A := Hdr^.Arena;
  Result := A^.LiveCount;
end;

procedure _MemDrainRemoteFrees;
begin
  DrainAllRemoteFrees();
end;

function _MemReclaimAbandoned: Integer;
begin
  Result := ReclaimAbandonedSweep();
end;

{ ------------------------------------------------------------------ }
{ Public API                                                           }
{ ------------------------------------------------------------------ }

function _BlaiseGetMem(Size: Integer): Pointer;
begin
  if Size <= 0 then
  begin
    Exit(nil);
  end;
  if Size > LARGE_THRESHOLD then
    Result := LargeGetMem(Size)
  else
    Result := SmallGetMem(Size);
end;

procedure _BlaiseFreeMem(Ptr: Pointer);
begin
  if Ptr = nil then Exit;
  if IsLarge(Ptr) then
    LargeFreeMem(Ptr)
  else
    SmallFreeMem(Ptr);
end;

function _BlaiseReallocMem(Ptr: Pointer; NewSize: Integer): Pointer;
var
  OldSize, CopySize: Integer;
  Hdr: PBlockHeader;
  LHdr: PLargeHeader;
  OldMapped, NewMapped: Int64;
begin
  if Ptr = nil then
  begin
    Exit(_BlaiseGetMem(NewSize));
  end;
  if NewSize <= 0 then
  begin
    _BlaiseFreeMem(Ptr);
    Exit(nil);
  end;
  OldSize := GetAllocSize(Ptr);
  if (not IsLarge(Ptr)) and (NewSize <= LARGE_THRESHOLD) then
  begin
    if RoundUpToClass(NewSize) = RoundUpToClass(OldSize) then
    begin
      Hdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
      Hdr^.AllocSize := NewSize;
      Exit(Ptr);
    end;
  end;
  if IsLarge(Ptr) and (NewSize > LARGE_THRESHOLD) then
  begin
    LHdr := PLargeHeader(Pointer(PtrUInt(Ptr) - LARGE_HEADER));
    OldMapped := LHdr^.TotalMapped;
    NewMapped := PageRound(Int64(LARGE_HEADER) + Int64(NewSize));
    if NewMapped = OldMapped then
    begin
      LHdr^.AllocSize := NewSize;
      Exit(Ptr);
    end;
    { Fall through to the alloc-copy-free path below. }
  end;
  Result := _BlaiseGetMem(NewSize);
  if Result = nil then Exit;
  if OldSize < NewSize then
    CopySize := OldSize
  else
    CopySize := NewSize;
  _libc_memcpy(Result, Ptr, Int64(CopySize));
  _BlaiseFreeMem(Ptr);
end;

end.
