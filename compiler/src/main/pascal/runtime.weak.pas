{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — Zeroing weak references (Pascal port of blaise_weak.c)

  A weak reference is a slot (variable or field) pointing at a class
  instance without contributing to its refcount.  When the backing
  object's last strong reference is released and the object is about to
  be freed, every registered weak slot pointing at it is nil'd -- so a
  subsequent dereference sees nil rather than dangling memory.

  Design: two open-chained hash tables that grow with their contents.
  The entry table is keyed on the user_ptr of the backing object; each
  entry carries a doubly linked list of the slots (pointers-to-pointers)
  that reference it.  The slot table is keyed on the slot address, so a
  slot is found, and unlinked from its entry, in constant time.  Every
  operation is O(1) on average however many weak references there are,
  and however many name one target (a tree's children naming their
  parent): with a fixed table and a slot list scanned on every removal,
  releasing a large tree took seconds.

  Thread safety: a single pthread mutex protects all table mutations.
  The lock is coarse-grained but sufficient because weak references
  are infrequent relative to strong ARC operations.

  API:
    _WeakAssign(slot, new_target) -- register slot under new_target and
                                    store new_target at *slot; any prior
                                    registration for *slot is removed.
                                    new_target may be nil (just unregister).
    _WeakClear(slot)              -- unregister and zero *slot.  Called at
                                    scope exit and field cleanup for weak
                                    declarations.
    _WeakZeroSlots(target)        -- nil every slot pointing at target and
                                    drop target's entry from the table.
                                    Called from _ClassRelease at refcount
                                    zero, before the field-cleanup fn
                                    runs and before the block is freed.
}

unit runtime.weak;

interface

procedure _WeakAssign(Slot: Pointer; NewTarget: Pointer);
procedure _WeakClear(Slot: Pointer);
procedure _WeakZeroSlots(Target: Pointer);

{ RTL startup hook — every Blaise program's main calls this once, before its
  body, to run RTL initialisation that the per-unit `initialization` sections
  do not: units linked from a prebuilt archive never get their _init called,
  only units compiled into the program's own TU do.  Currently this sets up
  the weak-reference table mutex; other RTL one-time setup belongs here too
  as it arises. }
procedure _BlaiseInit;

implementation

const
  { Initial bucket count of each table; a power of two. }
  WEAK_BUCKETS = 256;

type
  PWeakEntry = ^TWeakEntry;
  PWeakSlot = ^TWeakSlot;

  TWeakSlot = record
    Addr: Pointer;
    Entry: PWeakEntry;
    { In the entry's list. }
    Prev: PWeakSlot;
    Next: PWeakSlot;
    { In the slot table's chain. }
    HNext: PWeakSlot;
  end;
  PPWeakSlot = ^PWeakSlot;

  TWeakEntry = record
    Target: Pointer;
    Slots: PWeakSlot;
    Next: PWeakEntry;
  end;
  PPWeakEntry = ^PWeakEntry;

function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';
function pthread_mutex_init(Mutex: Pointer; Attr: Pointer): Int32;
  external name 'pthread_mutex_init';
function pthread_mutex_lock(Mutex: Pointer): Int32;
  external name 'pthread_mutex_lock';
function pthread_mutex_unlock(Mutex: Pointer): Int32;
  external name 'pthread_mutex_unlock';

var
  { Buckets of entries (by target) and of slots (by address). }
  WeakEntries: Pointer;
  WeakEntryCap: Int;
  WeakEntryCount: Int;
  WeakSlots: Pointer;
  WeakSlotCap: Int;
  WeakSlotCount: Int;
  WeakMutex: array[0..7] of Int64;
  WeakMutexReady: Boolean;   { False until WeakMutex has been mutex_init'd }

{ Initialise WeakMutex exactly once.  Driven by _BlaiseInit at program
  startup; the WeakMutexReady guard makes it idempotent so the foot-of-unit
  `initialization` block (which runs only when blaise_weak is compiled into
  the program's own TU) and _BlaiseInit cannot double-init.  Initialising
  explicitly matters because a zero-filled mutex object is not a valid
  unlocked mutex on every platform — where it happens to be, skipping the
  init merely worked by luck.  The guard is non-atomic, consistent with the
  weak table's single-threaded-RTL assumption. }
procedure EnsureWeakMutex;
begin
  if not WeakMutexReady then
  begin
    pthread_mutex_init(@WeakMutex, nil);
    WeakMutexReady := True;
  end;
end;

{ Program-startup hook (see interface comment).  Runs the RTL's one-time
  setup that the per-unit init dispatch misses for archive units.
  Idempotent — safe even if a future caller invokes it twice. }
procedure _BlaiseInit;
begin
  EnsureWeakMutex();
end;

function WeakHash(Ptr: Pointer; ACap: Int): Int;
var
  U: UInt;
begin
  U := UInt(Ptr) shr 3;
  U := U xor (U shr 13);
  Result := Int(U and UInt(ACap - 1));
end;

{ Count zeroed pointers. }
function NewBuckets(ACount: Int): Pointer;
var
  I: Int;
  P: ^Pointer;
begin
  Result := _BlaiseGetMem(ACount * 8);
  if Result = nil then
    Exit;
  for I := 0 to ACount - 1 do
  begin
    P := Result + I * 8;
    P^ := nil;
  end;
end;

function EntryBucket(H: Int): PPWeakEntry;
begin
  Result := PPWeakEntry(WeakEntries + H * 8);
end;

function SlotBucket(H: Int): PPWeakSlot;
begin
  Result := PPWeakSlot(WeakSlots + H * 8);
end;

{ The tables exist and have room for one more of each; False when memory
  ran out. }
function WeakReady(): Boolean;
var
  Old: Pointer;
  OldCap, I, H: Int;
  E, NE: PWeakEntry;
  S, NS: PWeakSlot;
  B: Pointer;
begin
  Result := False;
  if WeakEntries = nil then
  begin
    WeakEntries := NewBuckets(WEAK_BUCKETS);
    WeakSlots := NewBuckets(WEAK_BUCKETS);
    if (WeakEntries = nil) or (WeakSlots = nil) then
      Exit;
    WeakEntryCap := WEAK_BUCKETS;
    WeakSlotCap := WEAK_BUCKETS;
  end;
  if WeakEntryCount >= WeakEntryCap then
  begin
    B := NewBuckets(WeakEntryCap * 2);
    if B = nil then
      Exit;
    Old := WeakEntries;
    OldCap := WeakEntryCap;
    WeakEntries := B;
    WeakEntryCap := OldCap * 2;
    for I := 0 to OldCap - 1 do
    begin
      E := PPWeakEntry(Old + I * 8)^;
      while E <> nil do
      begin
        NE := E^.Next;
        H := WeakHash(E^.Target, WeakEntryCap);
        E^.Next := EntryBucket(H)^;
        EntryBucket(H)^ := E;
        E := NE;
      end;
    end;
    _BlaiseFreeMem(Old);
  end;
  if WeakSlotCount >= WeakSlotCap then
  begin
    B := NewBuckets(WeakSlotCap * 2);
    if B = nil then
      Exit;
    Old := WeakSlots;
    OldCap := WeakSlotCap;
    WeakSlots := B;
    WeakSlotCap := OldCap * 2;
    for I := 0 to OldCap - 1 do
    begin
      S := PPWeakSlot(Old + I * 8)^;
      while S <> nil do
      begin
        NS := S^.HNext;
        H := WeakHash(S^.Addr, WeakSlotCap);
        S^.HNext := SlotBucket(H)^;
        SlotBucket(H)^ := S;
        S := NS;
      end;
    end;
    _BlaiseFreeMem(Old);
  end;
  Result := True;
end;

function WeakFindEntry(ATarget: Pointer): PWeakEntry;
begin
  Result := nil;
  if WeakEntries = nil then
    Exit;
  Result := EntryBucket(WeakHash(ATarget, WeakEntryCap))^;
  while (Result <> nil) and (Result^.Target <> ATarget) do
    Result := Result^.Next;
end;

function WeakFindOrCreate(ATarget: Pointer): PWeakEntry;
var
  H: Int;
begin
  Result := WeakFindEntry(ATarget);
  if Result <> nil then
    Exit;
  Result := PWeakEntry(_BlaiseGetMem(SizeOf(TWeakEntry)));
  if Result = nil then
    Exit;
  H := WeakHash(ATarget, WeakEntryCap);
  Result^.Target := ATarget;
  Result^.Slots := nil;
  Result^.Next := EntryBucket(H)^;
  EntryBucket(H)^ := Result;
  WeakEntryCount := WeakEntryCount + 1;
end;

{ Unlinks AEntry from its chain and frees it (its slots are gone). }
procedure WeakDropEntry(AEntry: PWeakEntry);
var
  B: PPWeakEntry;
  Prev, E: PWeakEntry;
begin
  B := EntryBucket(WeakHash(AEntry^.Target, WeakEntryCap));
  Prev := nil;
  E := B^;
  while (E <> nil) and (E <> AEntry) do
  begin
    Prev := E;
    E := E^.Next;
  end;
  if E = AEntry then
  begin
    if Prev = nil then
      B^ := AEntry^.Next
    else
      Prev^.Next := AEntry^.Next;
  end;
  _BlaiseFreeMem(AEntry);
  WeakEntryCount := WeakEntryCount - 1;
end;

{ Unlinks ASlot from the slot table's chain. }
procedure WeakUnhashSlot(ASlot: PWeakSlot);
var
  B: PPWeakSlot;
  Prev, S: PWeakSlot;
begin
  B := SlotBucket(WeakHash(ASlot^.Addr, WeakSlotCap));
  Prev := nil;
  S := B^;
  while (S <> nil) and (S <> ASlot) do
  begin
    Prev := S;
    S := S^.HNext;
  end;
  if S = ASlot then
  begin
    if Prev = nil then
      B^ := ASlot^.HNext
    else
      Prev^.HNext := ASlot^.HNext;
  end;
  WeakSlotCount := WeakSlotCount - 1;
end;

procedure WeakUnregister(ASlot: Pointer);
var
  S, P, N: PWeakSlot;
  E: PWeakEntry;
begin
  if WeakSlotCount = 0 then
    Exit;
  S := SlotBucket(WeakHash(ASlot, WeakSlotCap))^;
  while (S <> nil) and (S^.Addr <> ASlot) do
    S := S^.HNext;
  if S = nil then
    Exit;
  E := S^.Entry;
  P := S^.Prev;
  N := S^.Next;
  if P = nil then
    E^.Slots := N
  else
    P^.Next := N;
  if N <> nil then
    N^.Prev := P;
  WeakUnhashSlot(S);
  _BlaiseFreeMem(S);
  if E^.Slots = nil then
    WeakDropEntry(E);
end;

procedure _WeakAssign(Slot: Pointer; NewTarget: Pointer);
var
  PP: ^Pointer;
  E: PWeakEntry;
  S, First: PWeakSlot;
  H: Int;
begin
  if Slot = nil then
    Exit;
  pthread_mutex_lock(@WeakMutex);
  WeakUnregister(Slot);
  PP := Slot;
  PP^ := NewTarget;
  if (NewTarget <> nil) and WeakReady() then
  begin
    E := WeakFindOrCreate(NewTarget);
    if E <> nil then
    begin
      S := PWeakSlot(_BlaiseGetMem(SizeOf(TWeakSlot)));
      if S <> nil then
      begin
        S^.Addr := Slot;
        S^.Entry := E;
        S^.Prev := nil;
        First := E^.Slots;
        S^.Next := First;
        if First <> nil then
          First^.Prev := S;
        E^.Slots := S;
        H := WeakHash(Slot, WeakSlotCap);
        S^.HNext := SlotBucket(H)^;
        SlotBucket(H)^ := S;
        WeakSlotCount := WeakSlotCount + 1;
      end
      else if E^.Slots = nil then
        WeakDropEntry(E);
    end;
  end;
  pthread_mutex_unlock(@WeakMutex);
end;

procedure _WeakClear(Slot: Pointer);
var
  PP: ^Pointer;
begin
  if Slot = nil then
    Exit;
  pthread_mutex_lock(@WeakMutex);
  WeakUnregister(Slot);
  PP := Slot;
  PP^ := nil;
  pthread_mutex_unlock(@WeakMutex);
end;

procedure _WeakZeroSlots(Target: Pointer);
var
  E: PWeakEntry;
  S, NS: PWeakSlot;
  PP: ^Pointer;
begin
  if Target = nil then
    Exit;
  pthread_mutex_lock(@WeakMutex);
  if WeakEntryCount = 0 then
  begin
    pthread_mutex_unlock(@WeakMutex);
    Exit;
  end;
  E := WeakFindEntry(Target);
  if E <> nil then
  begin
    S := E^.Slots;
    while S <> nil do
    begin
      NS := S^.Next;
      PP := S^.Addr;
      PP^ := nil;
      WeakUnhashSlot(S);
      _BlaiseFreeMem(S);
      S := NS;
    end;
    E^.Slots := nil;
    WeakDropEntry(E);
  end;
  pthread_mutex_unlock(@WeakMutex);
end;

initialization
  { Runs only when blaise_weak is compiled into the program's own TU.
    For the archive case EnsureWeakMutex() does the work lazily; setting
    the flag here keeps the two paths from double-initialising. }
  pthread_mutex_init(@WeakMutex, nil);
  WeakMutexReady := True;

end.
