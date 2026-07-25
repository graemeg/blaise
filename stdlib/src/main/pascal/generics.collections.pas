{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Generics.Collections;

// Blaise RTL — generic collections (mirrors Delphi's System.Generics.Collections
// and FPC's Generics.Collections for source-level compatibility).
//
// NOTE: This file is compiled by the Blaise compiler, not FPC.

interface

uses
  Functional;

type
  { Generic forward enumerator for TList<T>.  Holds a pointer to the list's
    backing buffer and the count at the time GetEnumerator was called.
    MoveNext advances the cursor; Current returns the element at the cursor. }
  TListEnumerator<T> = class
    FData:  ^T;
    FIndex: Integer;
    FCount: Integer;
    constructor Create(AData: ^T; ACount: Integer);
    function MoveNext: Boolean;
    function GetCurrent: T;
    property Current: T read GetCurrent;
  end;

  TList<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    procedure Add(Value: T);
    function  Get(AIndex: Integer): T;
    procedure SetItem(AIndex: Integer; Value: T);
    function  IndexOf(const Value: T): Integer;
    procedure Delete(AIndex: Integer);
    procedure Clear;
    procedure Destroy;
    function  GetEnumerator: TListEnumerator<T>;
    { Eager LINQ-lite operators (docs/anonymous-methods-design.adoc,
      Phase 10).  Map/Where allocate and return NEW lists the caller owns;
      the source list is never modified except by Sort. }
    function  Map<R>(F: TFunc<T, R>): TList<R>;
    function  Where(P: TPredicate<T>): TList<T>;
    function  Reduce<R>(AInit: R; F: TFunc2<R, T, R>): R;
    procedure ForEach(A: TAction<T>);
    function  Any(P: TPredicate<T>): Boolean;
    function  All(P: TPredicate<T>): Boolean;
    function  Find(P: TPredicate<T>; out AValue: T): Boolean;
    { In-place STABLE sort (straight insertion) ordered by the three-way
      comparison closure; BinarySearch requires the list already sorted by
      the same comparison. }
    procedure Sort(C: TComparison<T>);
    function  BinarySearch(AItem: T; C: TComparison<T>;
                           out AIndex: Integer): Boolean;
    property Count: Integer read FCount;
    { Default array property — enables List[i] for read and write. }
    property Items[AIndex: Integer]: T read Get write SetItem; default;
  end;

  { Generic LIFO stack backed by a dynamic array.  Push/Pop/Peek operate on
    the top of the stack; Count reflects the number of items currently held. }
  TStack<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    procedure Push(Value: T);
    function  Pop: T;
    function  Peek: T;
    procedure Clear;
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  { Generic FIFO queue backed by a dynamic circular-buffer array.
    Enqueue appends to the tail; Dequeue removes from the head.
    The buffer doubles when full, preserving insertion order. }
  TQueue<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    FHead:     Integer;
    FTail:     Integer;
    procedure Grow;
    procedure ReleaseElements;
    procedure Enqueue(Value: T);
    function  Dequeue: T;
    function  Peek: T;
    procedure Clear;
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  { Generic unordered set backed by a dynamic array.  Membership tests use a
    lazy hash index once the set is large enough (see GCHashOf); small sets
    keep the linear scan.  Include adds an element only if not already
    present; Exclude removes it. }
  TSet<T> = class
    FData:      ^T;
    FCount:     Integer;
    FCapacity:  Integer;
    FHashSlots: ^Integer;
    FHashCap:   Integer;
    procedure Grow;
    procedure HashInvalidate;
    procedure HashInsertIdx(AIdx: Integer);
    procedure HashRebuild;
    function  IndexOf(const Value: T): Integer;
    procedure Include(Value: T);
    procedure Exclude(Value: T);
    function  Contains(const Value: T): Boolean;
    procedure Clear;
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  { Generic map interface: common contract for dictionary-like types. }
  IMap<K, V> = interface
    procedure Add(Key: K; Value: V);
    { Lookups borrow the key (const): they never store it, so a borrowed key
      needs no by-value copy/release.  This also removes the arm64
      pass-borrowed-string-by-value over-release hazard on the hot FindKey
      path (FFrame.TryGetValue over-release, macOS arm64 2026-07-24). }
    function  TryGetValue(const Key: K; var Value: V): Boolean;
    function  ContainsKey(const Key: K): Boolean;
    procedure Remove(const Key: K);
    function  GetCount: Integer;
  end;

  { Generic dictionary backed by two parallel arrays (insertion-ordered
    storage).  Key lookup uses a lazy open-addressing hash index once the
    dictionary is large enough; small dictionaries keep the linear scan.
    Key equality uses the '=' operator on the monomorphized type (content
    equality for string keys); hashing dispatches through the GCHashOf
    overloads, so a key type needs a matching GCHashOf to instantiate. }
  TDictionary<K, V> = class(IMap<K, V>)
    FKeys:      ^K;
    FValues:    ^V;
    FCount:     Integer;
    FCapacity:  Integer;
    FHashSlots: ^Integer;
    FHashCap:   Integer;
    procedure Grow;
    procedure HashInvalidate;
    procedure HashInsertIdx(AIdx: Integer);
    procedure HashRebuild;
    function  FindKey(const Key: K): Integer;
    procedure ReleaseEntries;
    procedure Add(Key: K; Value: V);
    function  GetItem(const Key: K): V;
    procedure SetItem(Key: K; Value: V);
    function  TryGetValue(const Key: K; var Value: V): Boolean;
    function  ContainsKey(const Key: K): Boolean;
    procedure Remove(const Key: K);
    { Drop all entries; keeps the allocated capacity for reuse. }
    procedure Clear;
    function  GetCount: Integer;
    procedure Destroy;
    property Count: Integer read FCount;
    property Items[Key: K]: V read GetItem write SetItem; default;
  end;

  { Generic insertion-ordered map.  Entries are stored in the order they were
    first added; iteration and indexed access preserve that order.  Like
    TDictionary it uses linear-scan equality, so it is suitable for small maps
    where insertion order matters (e.g. preserving configuration file order,
    deterministic output). }
  TOrderedDictionary<K, V> = class(IMap<K, V>)
    FKeys:      ^K;
    FValues:    ^V;
    FCount:     Integer;
    FCapacity:  Integer;
    FHashSlots: ^Integer;
    FHashCap:   Integer;
    procedure Grow;
    procedure HashInvalidate;
    procedure HashInsertIdx(AIdx: Integer);
    procedure HashRebuild;
    function  FindKey(const Key: K): Integer;
    procedure ReleaseEntries;
    procedure Add(Key: K; Value: V);
    function  GetItem(const Key: K): V;
    procedure SetItem(Key: K; Value: V);
    function  TryGetValue(const Key: K; var Value: V): Boolean;
    function  ContainsKey(const Key: K): Boolean;
    procedure Remove(const Key: K);
    function  GetKey(AIndex: Integer): K;
    function  GetValue(AIndex: Integer): V;
    function  GetCount: Integer;
    procedure Destroy;
    property Count: Integer read FCount;
    property Items[Key: K]: V read GetItem write SetItem; default;
    property Keys[Index: Integer]: K read GetKey;
    property Values[Index: Integer]: V read GetValue;
  end;

{ Key hashing for the generic containers.  Monomorphisation resolves
  GCHashOf(Key) against these overloads per instantiation, so each key type
  gets a content-appropriate hash: strings hash their bytes (matching the
  content semantics of '=' on strings), integers and pointers mix their
  value.  Instantiating a keyed container with a type that has no matching
  overload is a compile-time error — add an overload here for new key types. }
{ `const`: a hash only READS its key.  By value, the callee retains on entry
  and releases at exit — on a refcount-0 transient key (a fresh concat handed
  straight to a lookup) that pair is AddRef(0->1)/Release(1->0) = FREE, and
  the caller's still-owned string dies under it.  The value-typed overloads
  carry no ARC and need no `const`. }
function GCHashOf(const AValue: string): Integer; overload;
function GCHashOf(AValue: Integer): Integer; overload;
function GCHashOf(AValue: Int64): Integer; overload;
function GCHashOf(AValue: Pointer): Integer; overload;
function GCHashOf(AValue: Boolean): Integer; overload;

const
  { Below this size a linear scan beats building a hash table.  Interface
    visibility because generic bodies are analysed at their instantiation
    site. }
  GCHashThreshold = 16;

implementation

{ ------------------------------------------------------------------ }
{ GCHashOf — key hashing overloads                                     }
{ ------------------------------------------------------------------ }

function GCHashOf(const AValue: string): Integer; overload;
var
  I: Integer;
begin
  { FNV-1a over the bytes; case-sensitive to match '=' on strings. }
  Result := -2128831035;   { FNV offset basis 2166136261 as signed 32-bit }
  for I := 0 to Length(AValue) - 1 do
    Result := (Result xor Ord(AValue[I])) * 16777619;
end;

function GCHashOf(AValue: Integer): Integer; overload;
begin
  { Knuth multiplicative mix (2654435761 as signed 32-bit). }
  Result := AValue * -1640531527;
end;

function GCHashOf(AValue: Int64): Integer; overload;
begin
  Result := Integer(AValue xor (AValue shr 32)) * -1640531527;
end;

function GCHashOf(AValue: Pointer): Integer; overload;
begin
  Result := GCHashOf(Int64(AValue));
end;

function GCHashOf(AValue: Boolean): Integer; overload;
begin
  if AValue then
    Result := 1
  else
    Result := 0;
end;

{ ------------------------------------------------------------------ }
{ TList<T>                                                             }
{ ------------------------------------------------------------------ }

procedure TList<T>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(T));
  ZeroMem(Self.FData + OldCap * SizeOf(T), (NewCap - OldCap) * SizeOf(T));
  Self.FCapacity := NewCap
end;

function TList<T>.Map<R>(F: TFunc<T, R>): TList<R>;
var
  I: Integer;
begin
  Result := TList<R>.Create();
  for I := 0 to FCount - 1 do
    Result.Add(F(Get(I)));
end;

function TList<T>.Where(P: TPredicate<T>): TList<T>;
var
  I: Integer;
begin
  Result := TList<T>.Create();
  for I := 0 to FCount - 1 do
    if P(Get(I)) then
      Result.Add(Get(I));
end;

function TList<T>.Reduce<R>(AInit: R; F: TFunc2<R, T, R>): R;
var
  I: Integer;
begin
  Result := AInit;
  for I := 0 to FCount - 1 do
    Result := F(Result, Get(I));
end;

procedure TList<T>.ForEach(A: TAction<T>);
var
  I: Integer;
begin
  for I := 0 to FCount - 1 do
    A(Get(I));
end;

function TList<T>.Any(P: TPredicate<T>): Boolean;
var
  I: Integer;
begin
  Result := False;
  for I := 0 to FCount - 1 do
    if P(Get(I)) then
      Exit(True);
end;

function TList<T>.All(P: TPredicate<T>): Boolean;
var
  I: Integer;
begin
  Result := True;
  for I := 0 to FCount - 1 do
    if not P(Get(I)) then
      Exit(False);
end;

function TList<T>.Find(P: TPredicate<T>; out AValue: T): Boolean;
var
  I: Integer;
begin
  Result := False;
  for I := 0 to FCount - 1 do
    if P(Get(I)) then
    begin
      AValue := Get(I);
      Exit(True);
    end;
end;

procedure TList<T>.Sort(C: TComparison<T>);
var
  I, J: Integer;
  Cur: T;
begin
  { Straight insertion: stable (equal keys keep their relative order because
    the inner loop shifts only strictly-greater items). }
  for I := 1 to FCount - 1 do
  begin
    Cur := Get(I);
    J := I - 1;
    while (J >= 0) and (C(Get(J), Cur) > 0) do
    begin
      SetItem(J + 1, Get(J));
      J := J - 1;
    end;
    SetItem(J + 1, Cur);
  end;
end;

function TList<T>.BinarySearch(AItem: T; C: TComparison<T>;
                               out AIndex: Integer): Boolean;
var
  Lo, Hi, Mid, Cmp: Integer;
begin
  Result := False;
  Lo := 0;
  Hi := FCount - 1;
  while Lo <= Hi do
  begin
    Mid := (Lo + Hi) div 2;
    Cmp := C(Get(Mid), AItem);
    if Cmp = 0 then
    begin
      AIndex := Mid;
      Exit(True);
    end;
    if Cmp < 0 then
      Lo := Mid + 1
    else
      Hi := Mid - 1;
  end;
  AIndex := Lo;   { insertion point }
end;

procedure TList<T>.Add(Value: T);
var
  Dest: ^T;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FCount * SizeOf(T);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1
end;

function TList<T>.Get(AIndex: Integer): T;
var
  Src: ^T;
begin
  Src    := Self.FData + AIndex * SizeOf(T);
  Result := Src^
end;

procedure TList<T>.SetItem(AIndex: Integer; Value: T);
var
  Dest: ^T;
begin
  { The ^T := Value store carries the compiler's ARC discipline for a managed
    T — the previous element is released and the new one retained. }
  Dest  := Self.FData + AIndex * SizeOf(T);
  Dest^ := Value
end;

function TList<T>.IndexOf(const Value: T): Integer;
var
  I:   Integer;
  Ptr: ^T;
begin
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FData + I * SizeOf(T);
    if Ptr^ = Value then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TList<T>.Delete(AIndex: Integer);
var
  Src:   ^T;
  Dst:   ^T;
  I:     Integer;
  Empty: T;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(T);
    Src  := Self.FData + (I + 1) * SizeOf(T);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1;
  { The shift leaves the (now unused) tail slot holding a duplicate of the last
    element; clear it so its managed ref is released, not leaked. }
  Dst  := Self.FData + Self.FCount * SizeOf(T);
  Dst^ := Empty
end;

procedure TList<T>.Clear;
var
  I:     Integer;
  Slot:  ^T;
  Empty: T;
begin
  { Release each managed element before dropping the count (see Destroy). }
  I := 0;
  while I < Self.FCount do
  begin
    Slot  := Self.FData + I * SizeOf(T);
    Slot^ := Empty;
    I     := I + 1
  end;
  Self.FCount := 0
end;

procedure TList<T>.Destroy;
var
  I:     Integer;
  Slot:  ^T;
  Empty: T;
begin
  { Release each managed element so freeing the list cascades to its items
    (Blaise is reference-counted): storing a zero-initialised T through the
    slot runs the compiler's ARC discipline — the old element is released; for
    a plain (non-managed) T the store is a harmless zero write. }
  I := 0;
  while I < Self.FCount do
  begin
    Slot  := Self.FData + I * SizeOf(T);
    Slot^ := Empty;
    I     := I + 1
  end;
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

function TList<T>.GetEnumerator: TListEnumerator<T>;
begin
  Result := TListEnumerator<T>.Create(Self.FData, Self.FCount)
end;

{ ------------------------------------------------------------------ }
{ TListEnumerator<T>                                                   }
{ ------------------------------------------------------------------ }

constructor TListEnumerator<T>.Create(AData: ^T; ACount: Integer);
begin
  Self.FData  := AData;
  Self.FIndex := -1;
  Self.FCount := ACount
end;

function TListEnumerator<T>.MoveNext: Boolean;
begin
  Self.FIndex := Self.FIndex + 1;
  Result      := Self.FIndex < Self.FCount
end;

function TListEnumerator<T>.GetCurrent: T;
var
  Ptr: ^T;
begin
  Ptr    := Self.FData + Self.FIndex * SizeOf(T);
  Result := Ptr^
end;

{ ------------------------------------------------------------------ }
{ TStack<T>                                                            }
{ ------------------------------------------------------------------ }

procedure TStack<T>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(T));
  ZeroMem(Self.FData + OldCap * SizeOf(T), (NewCap - OldCap) * SizeOf(T));
  Self.FCapacity := NewCap
end;

procedure TStack<T>.Push(Value: T);
var
  Dest: ^T;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FCount * SizeOf(T);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1
end;

function TStack<T>.Pop: T;
var
  Src:   ^T;
  Empty: T;
begin
  Self.FCount := Self.FCount - 1;
  Src         := Self.FData + Self.FCount * SizeOf(T);
  Result      := Src^;
  { Ownership moves to the caller; clear the vacated slot so its managed ref
    is released rather than stranded (see TList<T>.Delete). }
  Src^        := Empty
end;

function TStack<T>.Peek: T;
var
  Src: ^T;
begin
  Src    := Self.FData + (Self.FCount - 1) * SizeOf(T);
  Result := Src^
end;

procedure TStack<T>.Clear;
var
  I:     Integer;
  Slot:  ^T;
  Empty: T;
begin
  { Release each managed element before dropping the count (see
    TList<T>.Destroy for why the zero-store is the release primitive). }
  I := 0;
  while I < Self.FCount do
  begin
    Slot  := Self.FData + I * SizeOf(T);
    Slot^ := Empty;
    I     := I + 1
  end;
  Self.FCount := 0
end;

procedure TStack<T>.Destroy;
var
  I:     Integer;
  Slot:  ^T;
  Empty: T;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Slot  := Self.FData + I * SizeOf(T);
    Slot^ := Empty;
    I     := I + 1
  end;
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

{ ------------------------------------------------------------------ }
{ TQueue<T>                                                            }
{ ------------------------------------------------------------------ }

procedure TQueue<T>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
  NewData: ^T;
  I: Integer;
  Src: ^T;
  Dst: ^T;
  Empty: T;
begin
  OldCap  := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  NewData := GetMem(NewCap * SizeOf(T));
  ZeroMem(NewData, NewCap * SizeOf(T));
  I := 0;
  while I < Self.FCount do
  begin
    Src  := Self.FData + ((Self.FHead + I) mod OldCap) * SizeOf(T);
    Dst  := NewData + I * SizeOf(T);
    Dst^ := Src^;
    { The copy retained a second managed ref; release the old slot before the
      buffer is freed, or every surviving element leaks a +1. }
    Src^ := Empty;
    I    := I + 1
  end;
  FreeMem(Self.FData);
  Self.FData     := NewData;
  Self.FHead     := 0;
  Self.FTail     := Self.FCount;
  Self.FCapacity := NewCap
end;

procedure TQueue<T>.Enqueue(Value: T);
var
  Dest: ^T;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FTail * SizeOf(T);
  Dest^       := Value;
  Self.FTail  := (Self.FTail + 1) mod Self.FCapacity;
  Self.FCount := Self.FCount + 1
end;

function TQueue<T>.Dequeue: T;
var
  Src:   ^T;
  Empty: T;
begin
  Src         := Self.FData + Self.FHead * SizeOf(T);
  Result      := Src^;
  { Ownership moves to the caller; clear the vacated slot (see
    TStack<T>.Pop). }
  Src^        := Empty;
  Self.FHead  := (Self.FHead + 1) mod Self.FCapacity;
  Self.FCount := Self.FCount - 1
end;

function TQueue<T>.Peek: T;
var
  Src: ^T;
begin
  Src    := Self.FData + Self.FHead * SizeOf(T);
  Result := Src^
end;

{ Release every live element.  The storage is circular, so the live slots are
  (FHead + I) mod FCapacity for I in 0..FCount-1 — not 0..FCount-1. }
procedure TQueue<T>.ReleaseElements;
var
  I:     Integer;
  Slot:  ^T;
  Empty: T;
begin
  if Self.FCapacity = 0 then
    Exit;
  I := 0;
  while I < Self.FCount do
  begin
    Slot  := Self.FData + ((Self.FHead + I) mod Self.FCapacity) * SizeOf(T);
    Slot^ := Empty;
    I     := I + 1
  end
end;

procedure TQueue<T>.Clear;
begin
  Self.ReleaseElements();
  Self.FCount := 0;
  Self.FHead  := 0;
  Self.FTail  := 0
end;

procedure TQueue<T>.Destroy;
begin
  Self.ReleaseElements();
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0;
  Self.FHead     := 0;
  Self.FTail     := 0
end;

{ ------------------------------------------------------------------ }
{ TSet<T>                                                              }
{ ------------------------------------------------------------------ }

procedure TSet<T>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(T));
  ZeroMem(Self.FData + OldCap * SizeOf(T), (NewCap - OldCap) * SizeOf(T));
  Self.FCapacity := NewCap
end;

procedure TSet<T>.HashInvalidate;
begin
  if Self.FHashSlots <> nil then
  begin
    FreeMem(Self.FHashSlots);
    Self.FHashSlots := nil;
  end;
  Self.FHashCap := 0;
end;

procedure TSet<T>.HashInsertIdx(AIdx: Integer);
var
  Slot:  Integer;
  SlotP: ^Integer;
  EPtr:  ^T;
begin
  EPtr := Self.FData + AIdx * SizeOf(T);
  Slot := GCHashOf(EPtr^) and (Self.FHashCap - 1);
  while True do
  begin
    SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
    if SlotP^ = -1 then
    begin
      SlotP^ := AIdx;
      Exit;
    end;
    Slot := (Slot + 1) and (Self.FHashCap - 1);
  end;
end;

procedure TSet<T>.HashRebuild;
var
  Cap: Integer;
  I:   Integer;
  P:   ^Integer;
begin
  Cap := 16;
  while Cap < Self.FCount * 2 do
    Cap := Cap * 2;
  if Self.FHashSlots <> nil then
    FreeMem(Self.FHashSlots);
  Self.FHashSlots := GetMem(Cap * SizeOf(Integer));
  Self.FHashCap   := Cap;
  for I := 0 to Cap - 1 do
  begin
    P  := Self.FHashSlots + I * SizeOf(Integer);
    P^ := -1;
  end;
  for I := 0 to Self.FCount - 1 do
    Self.HashInsertIdx(I);
end;

function TSet<T>.IndexOf(const Value: T): Integer;
var
  I:     Integer;
  Ptr:   ^T;
  Slot:  Integer;
  SlotP: ^Integer;
begin
  if Self.FCount >= GCHashThreshold then
  begin
    if Self.FHashCap = 0 then
      Self.HashRebuild();
    Slot := GCHashOf(Value) and (Self.FHashCap - 1);
    while True do
    begin
      SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
      if SlotP^ = -1 then
        Exit(-1);
      Ptr := Self.FData + SlotP^ * SizeOf(T);
      if Ptr^ = Value then
        Exit(SlotP^);
      Slot := (Slot + 1) and (Self.FHashCap - 1);
    end;
  end;
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FData + I * SizeOf(T);
    if Ptr^ = Value then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TSet<T>.Include(Value: T);
var
  Dest: ^T;
begin
  if Self.IndexOf(Value) >= 0 then
    Exit;
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FCount * SizeOf(T);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1;
  if Self.FHashCap > 0 then
  begin
    if Self.FCount * 2 > Self.FHashCap then
      Self.HashInvalidate()
    else
      Self.HashInsertIdx(Self.FCount - 1);
  end;
end;

procedure TSet<T>.Exclude(Value: T);
var
  Idx:   Integer;
  I:     Integer;
  Dst:   ^T;
  Src:   ^T;
  Empty: T;
begin
  Idx := Self.IndexOf(Value);
  if Idx < 0 then
    Exit;
  I := Idx;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(T);
    Src  := Self.FData + (I + 1) * SizeOf(T);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1;
  { The shift leaves the vacated tail slot holding a duplicate of the last
    element; clear it so its managed ref is released (see TList<T>.Delete). }
  Dst  := Self.FData + Self.FCount * SizeOf(T);
  Dst^ := Empty;
  { Indexes shifted — rebuild lazily on the next lookup. }
  Self.HashInvalidate()
end;

function TSet<T>.Contains(const Value: T): Boolean;
begin
  Result := Self.IndexOf(Value) >= 0
end;

procedure TSet<T>.Clear;
var
  I:     Integer;
  Slot:  ^T;
  Empty: T;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Slot  := Self.FData + I * SizeOf(T);
    Slot^ := Empty;
    I     := I + 1
  end;
  Self.FCount := 0;
  Self.HashInvalidate()
end;

procedure TSet<T>.Destroy;
var
  I:     Integer;
  Slot:  ^T;
  Empty: T;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Slot  := Self.FData + I * SizeOf(T);
    Slot^ := Empty;
    I     := I + 1
  end;
  Self.HashInvalidate();
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

{ ------------------------------------------------------------------ }
{ TDictionary<K, V>                                                    }
{ ------------------------------------------------------------------ }

procedure TDictionary<K, V>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 8
  else
    NewCap := OldCap * 2;
  Self.FKeys     := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
  ZeroMem(Self.FKeys + OldCap * SizeOf(K), (NewCap - OldCap) * SizeOf(K));
  Self.FValues   := ReallocMem(Self.FValues, NewCap * SizeOf(V));
  ZeroMem(Self.FValues + OldCap * SizeOf(V), (NewCap - OldCap) * SizeOf(V));
  Self.FCapacity := NewCap
end;

procedure TDictionary<K, V>.HashInvalidate;
begin
  if Self.FHashSlots <> nil then
  begin
    FreeMem(Self.FHashSlots);
    Self.FHashSlots := nil;
  end;
  Self.FHashCap := 0;
end;

procedure TDictionary<K, V>.HashInsertIdx(AIdx: Integer);
var
  Slot:  Integer;
  SlotP: ^Integer;
  KPtr:  ^K;
begin
  KPtr := Self.FKeys + AIdx * SizeOf(K);
  Slot := GCHashOf(KPtr^) and (Self.FHashCap - 1);
  while True do
  begin
    SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
    if SlotP^ = -1 then
    begin
      SlotP^ := AIdx;
      Exit;
    end;
    Slot := (Slot + 1) and (Self.FHashCap - 1);
  end;
end;

{ Keys are unique, so occupancy equals FCount; rebuilt at <= 50% load so
  an empty slot terminates every probe chain. }
procedure TDictionary<K, V>.HashRebuild;
var
  Cap: Integer;
  I:   Integer;
  P:   ^Integer;
begin
  Cap := 16;
  while Cap < Self.FCount * 2 do
    Cap := Cap * 2;
  if Self.FHashSlots <> nil then
    FreeMem(Self.FHashSlots);
  Self.FHashSlots := GetMem(Cap * SizeOf(Integer));
  Self.FHashCap   := Cap;
  for I := 0 to Cap - 1 do
  begin
    P  := Self.FHashSlots + I * SizeOf(Integer);
    P^ := -1;
  end;
  for I := 0 to Self.FCount - 1 do
    Self.HashInsertIdx(I);
end;

function TDictionary<K, V>.FindKey(const Key: K): Integer;
var
  I:     Integer;
  Ptr:   ^K;
  Slot:  Integer;
  SlotP: ^Integer;
begin
  if Self.FCount >= GCHashThreshold then
  begin
    if Self.FHashCap = 0 then
      Self.HashRebuild();
    Slot := GCHashOf(Key) and (Self.FHashCap - 1);
    while True do
    begin
      SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
      if SlotP^ = -1 then
        Exit(-1);
      Ptr := Self.FKeys + SlotP^ * SizeOf(K);
      if Ptr^ = Key then
        Exit(SlotP^);
      Slot := (Slot + 1) and (Self.FHashCap - 1);
    end;
  end;
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FKeys + I * SizeOf(K);
    if Ptr^ = Key then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TDictionary<K, V>.Add(Key: K; Value: V);
var
  Idx:  Integer;
  KPtr: ^K;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    { Update existing entry }
    VPtr  := Self.FValues + Idx * SizeOf(V);
    VPtr^ := Value
  end
  else
  begin
    { Insert new entry }
    if Self.FCount = Self.FCapacity then
      Self.Grow();
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(K);
    VPtr  := Self.FValues + Self.FCount * SizeOf(V);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1;
    { Keep the hash live across appends; past 50% load drop it and let the
      next lookup rebuild at double size. }
    if Self.FHashCap > 0 then
    begin
      if Self.FCount * 2 > Self.FHashCap then
        Self.HashInvalidate()
      else
        Self.HashInsertIdx(Self.FCount - 1);
    end;
  end
end;

function TDictionary<K, V>.TryGetValue(const Key: K; var Value: V): Boolean;
var
  Idx:  Integer;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(V);
    Value  := VPtr^;
    Result := True
  end
  else
    Result := False
end;

function TDictionary<K, V>.ContainsKey(const Key: K): Boolean;
begin
  Result := Self.FindKey(Key) >= 0
end;

procedure TDictionary<K, V>.Remove(const Key: K);
var
  Idx:      Integer;
  I:        Integer;
  KDst:     ^K;
  KSrc:     ^K;
  VDst:     ^V;
  VSrc:     ^V;
  EmptyKey: K;
  EmptyVal: V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    { Compact: shift entries after Idx one slot left }
    I := Idx;
    while I < Self.FCount - 1 do
    begin
      KDst  := Self.FKeys   + I * SizeOf(K);
      KSrc  := Self.FKeys   + (I + 1) * SizeOf(K);
      VDst  := Self.FValues + I * SizeOf(V);
      VSrc  := Self.FValues + (I + 1) * SizeOf(V);
      KDst^ := KSrc^;
      VDst^ := VSrc^;
      I     := I + 1
    end;
    Self.FCount := Self.FCount - 1;
    { The shift leaves the vacated tail slots holding duplicates of the last
      entry; clear both axes so their managed refs are released. }
    KDst  := Self.FKeys   + Self.FCount * SizeOf(K);
    VDst  := Self.FValues + Self.FCount * SizeOf(V);
    KDst^ := EmptyKey;
    VDst^ := EmptyVal;
    { Indexes shifted — rebuild lazily on the next lookup. }
    Self.HashInvalidate()
  end
end;

procedure TDictionary<K, V>.Clear;
begin
  Self.ReleaseEntries();
  Self.FCount := 0;
  Self.HashInvalidate();
end;

function TDictionary<K, V>.GetItem(const Key: K): V;
var
  Idx:  Integer;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(V);
    Result := VPtr^
  end
  else
    Halt(1)
end;

procedure TDictionary<K, V>.SetItem(Key: K; Value: V);
begin
  Self.Add(Key, Value)
end;

function TDictionary<K, V>.GetCount: Integer;
begin
  Result := Self.FCount
end;

{ Release every live key AND value.  Both axes matter — a
  TDictionary<String, TFoo> holds a managed ref on each side. }
procedure TDictionary<K, V>.ReleaseEntries;
var
  I:        Integer;
  KSlot:    ^K;
  VSlot:    ^V;
  EmptyKey: K;
  EmptyVal: V;
begin
  I := 0;
  while I < Self.FCount do
  begin
    KSlot  := Self.FKeys   + I * SizeOf(K);
    VSlot  := Self.FValues + I * SizeOf(V);
    KSlot^ := EmptyKey;
    VSlot^ := EmptyVal;
    I      := I + 1
  end
end;

procedure TDictionary<K, V>.Destroy;
begin
  Self.ReleaseEntries();
  Self.HashInvalidate();
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  Self.FKeys     := nil;
  Self.FValues   := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

{ ------------------------------------------------------------------ }
{ TOrderedDictionary<K, V>                                             }
{ ------------------------------------------------------------------ }

procedure TOrderedDictionary<K, V>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 8
  else
    NewCap := OldCap * 2;
  Self.FKeys     := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
  ZeroMem(Self.FKeys + OldCap * SizeOf(K), (NewCap - OldCap) * SizeOf(K));
  Self.FValues   := ReallocMem(Self.FValues, NewCap * SizeOf(V));
  ZeroMem(Self.FValues + OldCap * SizeOf(V), (NewCap - OldCap) * SizeOf(V));
  Self.FCapacity := NewCap
end;

procedure TOrderedDictionary<K, V>.HashInvalidate;
begin
  if Self.FHashSlots <> nil then
  begin
    FreeMem(Self.FHashSlots);
    Self.FHashSlots := nil;
  end;
  Self.FHashCap := 0;
end;

procedure TOrderedDictionary<K, V>.HashInsertIdx(AIdx: Integer);
var
  Slot:  Integer;
  SlotP: ^Integer;
  KPtr:  ^K;
begin
  KPtr := Self.FKeys + AIdx * SizeOf(K);
  Slot := GCHashOf(KPtr^) and (Self.FHashCap - 1);
  while True do
  begin
    SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
    if SlotP^ = -1 then
    begin
      SlotP^ := AIdx;
      Exit;
    end;
    Slot := (Slot + 1) and (Self.FHashCap - 1);
  end;
end;

procedure TOrderedDictionary<K, V>.HashRebuild;
var
  Cap: Integer;
  I:   Integer;
  P:   ^Integer;
begin
  Cap := 16;
  while Cap < Self.FCount * 2 do
    Cap := Cap * 2;
  if Self.FHashSlots <> nil then
    FreeMem(Self.FHashSlots);
  Self.FHashSlots := GetMem(Cap * SizeOf(Integer));
  Self.FHashCap   := Cap;
  for I := 0 to Cap - 1 do
  begin
    P  := Self.FHashSlots + I * SizeOf(Integer);
    P^ := -1;
  end;
  for I := 0 to Self.FCount - 1 do
    Self.HashInsertIdx(I);
end;

function TOrderedDictionary<K, V>.FindKey(const Key: K): Integer;
var
  I:     Integer;
  Ptr:   ^K;
  Slot:  Integer;
  SlotP: ^Integer;
begin
  if Self.FCount >= GCHashThreshold then
  begin
    if Self.FHashCap = 0 then
      Self.HashRebuild();
    Slot := GCHashOf(Key) and (Self.FHashCap - 1);
    while True do
    begin
      SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
      if SlotP^ = -1 then
        Exit(-1);
      Ptr := Self.FKeys + SlotP^ * SizeOf(K);
      if Ptr^ = Key then
        Exit(SlotP^);
      Slot := (Slot + 1) and (Self.FHashCap - 1);
    end;
  end;
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FKeys + I * SizeOf(K);
    if Ptr^ = Key then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TOrderedDictionary<K, V>.Add(Key: K; Value: V);
var
  Idx:  Integer;
  KPtr: ^K;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr  := Self.FValues + Idx * SizeOf(V);
    VPtr^ := Value
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow();
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(K);
    VPtr  := Self.FValues + Self.FCount * SizeOf(V);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1;
    if Self.FHashCap > 0 then
    begin
      if Self.FCount * 2 > Self.FHashCap then
        Self.HashInvalidate()
      else
        Self.HashInsertIdx(Self.FCount - 1);
    end;
  end
end;

function TOrderedDictionary<K, V>.TryGetValue(const Key: K; var Value: V): Boolean;
var
  Idx:  Integer;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(V);
    Value  := VPtr^;
    Result := True
  end
  else
    Result := False
end;

function TOrderedDictionary<K, V>.ContainsKey(const Key: K): Boolean;
begin
  Result := Self.FindKey(Key) >= 0
end;

procedure TOrderedDictionary<K, V>.Remove(const Key: K);
var
  Idx:      Integer;
  I:        Integer;
  KDst:     ^K;
  KSrc:     ^K;
  VDst:     ^V;
  VSrc:     ^V;
  EmptyKey: K;
  EmptyVal: V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    I := Idx;
    while I < Self.FCount - 1 do
    begin
      KDst  := Self.FKeys   + I * SizeOf(K);
      KSrc  := Self.FKeys   + (I + 1) * SizeOf(K);
      VDst  := Self.FValues + I * SizeOf(V);
      VSrc  := Self.FValues + (I + 1) * SizeOf(V);
      KDst^ := KSrc^;
      VDst^ := VSrc^;
      I     := I + 1
    end;
    Self.FCount := Self.FCount - 1;
    { The shift leaves the vacated tail slots holding duplicates of the last
      entry; clear both axes so their managed refs are released. }
    KDst  := Self.FKeys   + Self.FCount * SizeOf(K);
    VDst  := Self.FValues + Self.FCount * SizeOf(V);
    KDst^ := EmptyKey;
    VDst^ := EmptyVal;
    { Indexes shifted — rebuild lazily on the next lookup. }
    Self.HashInvalidate()
  end
end;

function TOrderedDictionary<K, V>.GetKey(AIndex: Integer): K;
var
  Ptr: ^K;
begin
  Ptr    := Self.FKeys + AIndex * SizeOf(K);
  Result := Ptr^
end;

function TOrderedDictionary<K, V>.GetValue(AIndex: Integer): V;
var
  Ptr: ^V;
begin
  Ptr    := Self.FValues + AIndex * SizeOf(V);
  Result := Ptr^
end;

function TOrderedDictionary<K, V>.GetItem(const Key: K): V;
var
  Idx:  Integer;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(V);
    Result := VPtr^
  end
  else
    Halt(1)
end;

procedure TOrderedDictionary<K, V>.SetItem(Key: K; Value: V);
begin
  Self.Add(Key, Value)
end;

function TOrderedDictionary<K, V>.GetCount: Integer;
begin
  Result := Self.FCount
end;

{ Release every live key AND value (see TDictionary<K,V>.ReleaseEntries). }
procedure TOrderedDictionary<K, V>.ReleaseEntries;
var
  I:        Integer;
  KSlot:    ^K;
  VSlot:    ^V;
  EmptyKey: K;
  EmptyVal: V;
begin
  I := 0;
  while I < Self.FCount do
  begin
    KSlot  := Self.FKeys   + I * SizeOf(K);
    VSlot  := Self.FValues + I * SizeOf(V);
    KSlot^ := EmptyKey;
    VSlot^ := EmptyVal;
    I      := I + 1
  end
end;

procedure TOrderedDictionary<K, V>.Destroy;
begin
  Self.ReleaseEntries();
  Self.HashInvalidate();
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  Self.FKeys     := nil;
  Self.FValues   := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

end.
