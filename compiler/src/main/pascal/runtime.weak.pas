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

  Design: one global open-chained hash table, keyed on the user_ptr of
  the backing object.  Each entry carries a linked list of slot
  addresses (pointers-to-pointers) that reference it.  Inserts and
  removals are O(bucket-chain + slot-list) -- acceptable because weak
  references are rare relative to strong references.

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
  WEAK_BUCKETS = 256;

type
  PWeakSlot = ^TWeakSlot;
  TWeakSlot = record
    Addr: Pointer;
    Next: PWeakSlot;
  end;

  PWeakEntry = ^TWeakEntry;
  TWeakEntry = record
    Target: Pointer;
    Slots: PWeakSlot;
    Next: PWeakEntry;
  end;

function _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';
function pthread_mutex_init(Mutex: Pointer; Attr: Pointer): Integer;
  external name 'pthread_mutex_init';
function pthread_mutex_lock(Mutex: Pointer): Integer;
  external name 'pthread_mutex_lock';
function pthread_mutex_unlock(Mutex: Pointer): Integer;
  external name 'pthread_mutex_unlock';

var
  WeakTable: array[0..255] of PWeakEntry;
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

function WeakHash(Ptr: Pointer): Integer;
begin
  Result := Integer((PtrUInt(Ptr) shr 4) and PtrUInt(WEAK_BUCKETS - 1));
end;

function WeakFindOrCreate(ATarget: Pointer): PWeakEntry;
var
  H: Integer;
  E: PWeakEntry;
begin
  H := WeakHash(ATarget);
  E := WeakTable[H];
  while E <> nil do
  begin
    if E^.Target = ATarget then
    begin
      Exit(E);
    end;
    E := E^.Next;
  end;
  E := PWeakEntry(_BlaiseGetMem(24));
  if E = nil then
  begin
    Exit(nil);
  end;
  E^.Target := ATarget;
  E^.Slots := nil;
  E^.Next := WeakTable[H];
  WeakTable[H] := E;
  Result := E;
end;

procedure WeakUnregister(ASlot: Pointer);
var
  PP: ^Pointer;
  CurTarget: Pointer;
  H: Integer;
  E: PWeakEntry;
  Prev: PWeakSlot;
  Cur: PWeakSlot;
  Dead: PWeakSlot;
begin
  PP := ASlot;
  CurTarget := PP^;
  if CurTarget = nil then
    Exit;
  H := WeakHash(CurTarget);
  E := WeakTable[H];
  while E <> nil do
  begin
    if E^.Target = CurTarget then
    begin
      Prev := nil;
      Cur := E^.Slots;
      while Cur <> nil do
      begin
        if Cur^.Addr = ASlot then
        begin
          Dead := Cur;
          if Prev = nil then
            E^.Slots := Dead^.Next
          else
            Prev^.Next := Dead^.Next;
          _BlaiseFreeMem(Dead);
          Exit;
        end;
        Prev := Cur;
        Cur := Cur^.Next;
      end;
      Exit;
    end;
    E := E^.Next;
  end;
end;

procedure _WeakAssign(Slot: Pointer; NewTarget: Pointer);
var
  PP: ^Pointer;
  E: PWeakEntry;
  S: PWeakSlot;
begin
  if Slot = nil then
    Exit;
  pthread_mutex_lock(@WeakMutex);
  WeakUnregister(Slot);
  PP := Slot;
  PP^ := NewTarget;
  if NewTarget <> nil then
  begin
    E := WeakFindOrCreate(NewTarget);
    if E = nil then
    begin
      pthread_mutex_unlock(@WeakMutex);
      Exit;
    end;
    S := PWeakSlot(_BlaiseGetMem(16));
    if S = nil then
    begin
      pthread_mutex_unlock(@WeakMutex);
      Exit;
    end;
    S^.Addr := Slot;
    S^.Next := E^.Slots;
    E^.Slots := S;
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
  H: Integer;
  Prev: PWeakEntry;
  E: PWeakEntry;
  Dead: PWeakEntry;
  S: PWeakSlot;
  NS: PWeakSlot;
  PP: ^Pointer;
begin
  if Target = nil then
    Exit;
  pthread_mutex_lock(@WeakMutex);
  H := WeakHash(Target);
  Prev := nil;
  E := WeakTable[H];
  while E <> nil do
  begin
    if E^.Target = Target then
    begin
      Dead := E;
      S := Dead^.Slots;
      while S <> nil do
      begin
        NS := S^.Next;
        PP := S^.Addr;
        PP^ := nil;
        _BlaiseFreeMem(S);
        S := NS;
      end;
      if Prev = nil then
        WeakTable[H] := Dead^.Next
      else
        Prev^.Next := Dead^.Next;
      _BlaiseFreeMem(Dead);
      pthread_mutex_unlock(@WeakMutex);
      Exit;
    end;
    Prev := E;
    E := E^.Next;
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
