{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit async.deque;

// L1 of the fiber runtime (docs/async-networking-design.adoc, [#scheduler]):
// a single-owner, multi-thief Chase-Lev work-stealing deque of task pointers.
//
// The owning worker does PushBottom / PopBottom lock-free at the BOTTOM end;
// any number of thieves do Steal at the TOP end via CAS.  This is the exact
// structure Go's scheduler, Tokio and the Java ForkJoinPool use for their
// per-worker run queues.
//
// The classic reference is Chase & Lev, "Dynamic Circular Work-Stealing
// Deque" (SPAA 2005), with the memory-ordering corrections from Le et al.,
// "Correct and Efficient Work-Stealing for Weak Memory Models" (PPoPP 2013).
//
//   * `top`    — the index thieves steal from (monotonically increasing).
//   * `bottom` — the index the owner pushes to / pops from.
//   * a circular buffer of capacity 2^k that GROWS (never shrinks here) when
//     the owner would overflow it.
//
// The subtle case is PopBottom when the deque has exactly one element: the
// owner and a thief both target that element, and the tie is broken by the
// SAME CAS on `top` that Steal uses, so exactly one of them wins.
//
// The tasks are UNTYPED pointers (Pointer), so this unit has no dependency on
// the scheduler's TFiberTask type — the scheduler stores TFiberTask instances
// as their raw pointer.  Ownership/ARC of the tasks is the scheduler's job;
// the deque only moves pointers.
//
// NATIVE BACKEND ONLY (transitively): it is only ever driven under N worker
// OS threads, and the whole fiber runtime is native-only.  The deque itself
// uses no inline asm — the atomics live in runtime.atomic.

interface

type
  { A growable circular buffer of Pointer slots.  Capacity is always a power
    of two so index-into-slot is a mask, not a modulo.  Buffers are chained
    (OldBuf) rather than freed on growth, because a concurrent thief may still
    hold a reference to the previous buffer when the owner grows it; the whole
    chain is freed when the deque is destroyed. }
  PDequeBuf = ^TDequeBuf;
  TDequeBuf = record
    Cap: Int64;         { number of slots (power of two) }
    Mask: Int64;        { Cap - 1 }
    Slots: Pointer;     { ^array of Pointer, Cap entries }
    OldBuf: PDequeBuf;  { previous buffer, retired on growth }
  end;

  { Single-owner, multi-thief Chase-Lev deque of Pointer.  One worker owns the
    bottom end (PushBottom/PopBottom); any thread may Steal from the top. }
  TWorkStealDeque = class
  private
    FTop: Int64;        { steal index — CAS target (8-byte aligned field) }
    FBottom: Int64;     { push/pop index — owner only }
    FBuf: PDequeBuf;    { current circular buffer }
    procedure Grow;
  public
    constructor Create(AInitCap: Int64 = 64);
    destructor Destroy; override;

    { Owner-only.  Append AItem at the bottom.  Never fails (grows the buffer). }
    procedure PushBottom(AItem: Pointer);

    { Owner-only.  Remove and return the bottom item, or nil if empty.
      Resolves the last-element race with a thief via CAS on top. }
    function PopBottom: Pointer;

    { Any thread.  Remove and return the top item, or nil if empty or if a
      concurrent operation won the race (caller should retry / move on). }
    function Steal: Pointer;

    { Approximate number of queued items (owner's view; racy for thieves). }
    function ApproxCount: Int64;
  end;

implementation

uses
  runtime.atomic;

type
  PPointer = ^Pointer;

function AllocBuf(ACap: Int64): PDequeBuf;
begin
  Result := GetMem(SizeOf(TDequeBuf));
  Result^.Cap := ACap;
  Result^.Mask := ACap - 1;
  Result^.Slots := GetMem(ACap * SizeOf(Pointer));
  Result^.OldBuf := nil;
end;

constructor TWorkStealDeque.Create(AInitCap: Int64);
var
  C: Int64;
begin
  { Round AInitCap up to a power of two, minimum 2. }
  C := 2;
  while C < AInitCap do
    C := C * 2;
  Self.FBuf := AllocBuf(C);
  Self.FTop := 0;
  Self.FBottom := 0;
end;

destructor TWorkStealDeque.Destroy;
var
  B, N: PDequeBuf;
begin
  B := Self.FBuf;
  while B <> nil do
  begin
    N := B^.OldBuf;
    FreeMem(B^.Slots);
    FreeMem(B);
    B := N;
  end;
  inherited Destroy();
end;

function BufGet(ABuf: PDequeBuf; AIdx: Int64): Pointer;
var
  Slot: PPointer;
begin
  Slot := PPointer(ABuf^.Slots + (AIdx and ABuf^.Mask) * SizeOf(Pointer));
  Result := Slot^;
end;

procedure BufPut(ABuf: PDequeBuf; AIdx: Int64; AItem: Pointer);
var
  Slot: PPointer;
begin
  Slot := PPointer(ABuf^.Slots + (AIdx and ABuf^.Mask) * SizeOf(Pointer));
  Slot^ := AItem;
end;

procedure TWorkStealDeque.Grow;
var
  OldB, NewB: PDequeBuf;
  T, B, I: Int64;
begin
  OldB := Self.FBuf;
  NewB := AllocBuf(OldB^.Cap * 2);
  { Copy the live window [top, bottom) across, preserving absolute indices so
    thieves' in-flight top values still address the right slot. }
  T := Self.FTop;
  B := Self.FBottom;
  I := T;
  while I < B do
  begin
    BufPut(NewB, I, BufGet(OldB, I));
    I := I + 1;
  end;
  NewB^.OldBuf := OldB;
  { Publish the new buffer.  The owner is the only writer of FBuf; a thief that
    read the old buffer before this store still sees a valid (retired) buffer,
    and its Steal will fail the top-CAS if the owner has moved on.
    The publish must be a RELEASE: the copied slots (and NewB's own Cap /
    Mask / Slots) have to be visible before the pointer is.  A plain store let
    a weakly ordered CPU (arm64) show a thief the new buffer ahead of its
    contents, so it read a stale slot, won the top-CAS and lost the task.
    The atomic exchange is a full barrier on both ISAs (x86 xchg, arm64
    swpal); the thief's dependent load through FBuf then sees the copies. }
  _AtomicXchgPtr(@Self.FBuf, NewB);
end;

procedure TWorkStealDeque.PushBottom(AItem: Pointer);
var
  B, T, Size: Int64;
begin
  B := Self.FBottom;
  T := Self.FTop;
  Size := B - T;
  if Size >= Self.FBuf^.Cap then
    Self.Grow();
  BufPut(Self.FBuf, B, AItem);
  { Publish the item BEFORE the bottom bump so a thief that observes the new
    bottom also observes the slot content.  A full barrier via the atomic
    add (release is all that is strictly needed). }
  _AtomicAddInt64(@Self.FBottom, 1);
end;

function TWorkStealDeque.PopBottom: Pointer;
var
  B, T: Int64;
  Item: Pointer;
begin
  B := Self.FBottom - 1;
  Self.FBottom := B;
  { Full barrier: the bottom store must be visible before we read top, else a
    thief could steal the same element we are about to claim (Chase-Lev needs
    a StoreLoad fence here). }
  _AtomicAddInt64(@Self.FBottom, 0);
  T := Self.FTop;
  if T > B then
  begin
    { Empty.  Restore bottom to top (canonical empty state). }
    Self.FBottom := T;
    Exit(nil);
  end;
  Item := BufGet(Self.FBuf, B);
  if T < B then
    { More than one element: no thief can contend for the bottom one. }
    Exit(Item);
  { Exactly one element (T = B): race with a thief.  Try to claim it by
    bumping top ourselves; whoever wins the CAS gets it. }
  if not _AtomicCASPtr(@Self.FTop, Pointer(T), Pointer(T + 1)) then
    Item := nil;         { a thief won the race }
  { Either way top is now T+1; reset bottom to the canonical empty state. }
  Self.FBottom := T + 1;
  Result := Item;
end;

function TWorkStealDeque.Steal: Pointer;
var
  T, B: Int64;
  Buf: PDequeBuf;
  Item: Pointer;
begin
  T := Self.FTop;
  { Acquire ordering: read top before bottom (paired with PushBottom's release
    on FBottom).  The atomic read of FBottom is a full barrier, and B must be
    the value IT returned: a separate plain re-read could observe a newer
    bottom than the one the barrier synchronised with, leaving the slot and
    FBuf reads below unordered against the owner's writes for that index. }
  B := _AtomicAddInt64(@Self.FBottom, 0);
  if T >= B then
    Exit(nil);           { empty }
  { Read the item from the CURRENT buffer.  If the owner grew the buffer, the
    old buffer is still valid (chained, not freed), and the copied window
    preserves absolute indices, so reading either buffer at index T is safe.
    Re-read FBuf after establishing T < B. }
  Buf := Self.FBuf;
  Item := BufGet(Buf, T);
  { Try to claim slot T by advancing top.  On success the item is ours; on
    failure another thief or the owner took it — return nil, caller retries. }
  if not _AtomicCASPtr(@Self.FTop, Pointer(T), Pointer(T + 1)) then
    Exit(nil);
  Result := Item;
end;

function TWorkStealDeque.ApproxCount: Int64;
var
  B, T: Int64;
begin
  B := Self.FBottom;
  T := Self.FTop;
  Result := B - T;
  if Result < 0 then
    Result := 0;
end;

end.
