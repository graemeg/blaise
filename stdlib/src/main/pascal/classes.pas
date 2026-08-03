{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Classes;

// Blaise RTL — Classes unit.
//
// Provides TComponent, TStringList with a method-based API compatible with
// the Blaise compiler source for self-hosting.  TObjectList has been moved
// to the Contnrs unit to match FPC's layout.
//
// Design notes:
//   - TObjectList has been moved to the Contnrs unit (uses Contnrs).
//   - TDuplicates is a proper Pascal enum (dupAccept, dupIgnore, dupError).
//   - TStringList stores strings as ^string; ARC is emitted by the compiler
//     for pointer-dereference writes (EmitPointerWrite). ZeroMem is used to
//     zero-initialise newly grown string slots so no garbage is ever released.
//   - Text property: getter = GetText (lines joined by #10, no trailing newline);
//     setter = Clear + SplitIntoList(AText, Ord(#10), Self).
//   - LoadFromFile/SaveToFile use the ReadFile/WriteFile built-ins.
//   - TComponent: minimal owner-component pattern (Name, Owner, Components[]).
//     Children list uses a raw ^Pointer array (same pattern as TStringList) to
//     avoid a circular dependency with generics.collections in this unit.
//   - TStringListSortCompare: function type for CustomSort.
//   - CommaText: getter joins items with commas, quoting items that contain
//     commas or spaces; setter splits on commas respecting double-quote groups.

interface

uses
  runtime.arc, runtime.thread, StrUtils;

type
  TDuplicates = (dupAccept, dupIgnore, dupError);

  TStringListSortCompare = function(const A: string; const B: string): Integer;

  { ------------------------------------------------------------------ }
  { TComponent                                                           }
  { ------------------------------------------------------------------ }

  TComponent = class
  private
    FName:     string;
    { Non-owning back-reference: the owner keeps its children alive (via the
      raw FChildren array), not the other way round.  A strong ARC ref here
      would form an owner<->child cycle and, worse, make the child's field
      cleanup release the owner mid-destruction — re-entering the owner's
      Destroy and crashing. }
    [Unretained] FOwner: TComponent;
    FChildren: ^Pointer;
    FChildCap: Integer;
    FChildCnt: Integer;
    procedure GrowChildren;
    procedure AddComponent(AComp: TComponent);
    procedure RemoveComponent(AComp: TComponent);
    function  GetComponent(AIndex: Integer): TComponent;
  public
    constructor Create(AOwner: TComponent);
    destructor Destroy; override;
    property Name:           string     read FName     write FName;
    property Owner:          TComponent read FOwner;
    property ComponentCount: Integer    read FChildCnt;
    property Components[Index: Integer]: TComponent read GetComponent;
  end;

  { ------------------------------------------------------------------ }
  { TCriticalSection                                                     }
  { ------------------------------------------------------------------ }

  TCriticalSection = class
  private
    FMutexBuf: array[0..5] of Int64;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Enter;
    procedure Leave;
  end;

  { ------------------------------------------------------------------ }
  { TThread                                                              }
  { ------------------------------------------------------------------ }

  { Lightweight wrapper around a POSIX thread.
    Lifetime is managed by ARC — there is no FreeOnTerminate property.
    When the last reference is released, Destroy calls WaitFor (which
    joins the OS thread) before freeing the object. This guarantees the
    thread has fully exited before the memory is reclaimed.

    Typical usage:

      T := TMyThread.Create(False);   // starts immediately
      // ... do other work ...
      T.Free;                         // blocks until Execute returns

    Or simply let ARC handle it:

      procedure SpawnWork;
      var T: TMyThread;
      begin
        T := TMyThread.Create(False);
      end;  // scope exit joins and frees automatically }

  TThreadProc = procedure(Arg: Pointer);

  TThread = class
  private
    FHandle:          Int64;
    FFinished:        Boolean;
    FTerminated:      Boolean;
  protected
    { Override this method with the thread's workload. Check Terminated
      periodically in long-running loops to support cooperative shutdown. }
    procedure Execute; virtual;
  public
    { Pass False to start the thread immediately, or True to defer
      execution until Start is called. }
    constructor Create(ACreateSuspended: Boolean);
    { Joins the OS thread (if still running) then frees the object.
      Called automatically by ARC when the last reference is released. }
    destructor Destroy; override;
    { Spawns the OS thread. Called automatically by Create(False).
      Has no effect if the thread is already running. }
    procedure Start;
    { Sets the Terminated flag. Does not forcibly stop the thread —
      Execute must poll Terminated and exit cooperatively. }
    procedure Terminate;
    { Blocks until the thread has finished. Called automatically by
      Destroy; call it explicitly when you need the result before
      releasing the reference. }
    procedure WaitFor;
    property Finished:        Boolean read FFinished;
    property Terminated:      Boolean read FTerminated;
  end;

  { ------------------------------------------------------------------ }
  { TStringListEnumerator                                                }
  { ------------------------------------------------------------------ }

  TStringListEnumerator = class
    FList:  TStringList;
    FIndex: Integer;
    constructor Create(AList: TStringList);
    function MoveNext: Boolean;
    function GetCurrent: string;
    property Current: string read GetCurrent;
  end;

  { ------------------------------------------------------------------ }
  { TStringList                                                          }
  { ------------------------------------------------------------------ }

  TStringList = class
    FStrings:       ^string;
    FObjects:       ^Pointer;
    FCount:         Integer;
    FCapacity:      Integer;
    FCaseSensitive: Boolean;
    FSorted:        Boolean;
    FDuplicates:    TDuplicates;
    { Lazy hash index for UNSORTED lists: open-addressing table mapping a
      case-folded FNV-1a hash of the string to its list index.  Built on the
      first Find once Count reaches the threshold; duplicate keys keep the
      first-added index (IndexOf contract).  Any structural mutation
      (Delete, Insert, Put, Clear, sort, case-sensitivity change)
      invalidates it; appends update it in place.  Sorted lists never use
      it — they binary-search. }
    FHashSlots:     ^Integer;   { slot -> list index; -1 = empty }
    FHashCap:       Integer;    { power of two; 0 = index not built }
    FHashUsed:      Integer;    { occupied slots (excludes duplicate keys) }
    procedure Grow;
    function  Compare(const S1: string; const S2: string): Integer;
    function  FindSorted(const S: string; var Idx: Integer): Boolean;
    function  HashOf(const S: string): Integer;
    function  KeyEquals(const S1: string; const S2: string): Boolean;
    procedure HashInvalidate;
    procedure HashInsertIdx(AIdx: Integer);
    procedure HashRebuild;
    procedure SetSorted(AValue: Boolean);
    procedure SetCaseSensitive(AValue: Boolean);
    constructor Create;
    destructor Destroy; override;
    function    Add(S: string): Integer;
    { Objects[] is NON-OWNING by design: slots hold raw, untyped pointers
      with no ARC retain/release.  Callers commonly store integer payloads
      cast to pointers (TObject(PtrUInt(N))), which makes blind retention
      impossible.  When storing real objects, the caller must keep a strong
      reference alive for the lifetime of the entry (e.g. an owning
      TObjectList keep-alive) — see docs/language-rationale.adoc,
      "Collection Ownership". }
    procedure   AddObject(S: string; AObject: Pointer);
    function    Find(const S: string; var Index: Integer): Boolean;
    function    IndexOf(const S: string): Integer;
    function    Get(AIndex: Integer): string;
    procedure   Put(AIndex: Integer; S: string);
    function    GetObject(AIndex: Integer): Pointer;
    procedure   SetObject(AIndex: Integer; AObject: Pointer);
    procedure   Delete(AIndex: Integer);
    procedure   Clear;
    procedure   Insert(AIndex: Integer; S: string);
    procedure   AddStrings(ASource: TStringList);
    function    GetText: string;
    procedure   SetText(AText: string);
    procedure   LoadFromFile(APath: string);
    procedure   SaveToFile(APath: string);
    function    GetEnumerator: TStringListEnumerator;
    procedure   CustomSort(ACompare: TStringListSortCompare);
    function    GetCommaText: string;
    procedure   SetCommaText(const S: string);
    property Count:         Integer read FCount;
    property CaseSensitive: Boolean read FCaseSensitive write SetCaseSensitive;
    property Sorted:        Boolean read FSorted        write SetSorted;
    property Duplicates:    TDuplicates read FDuplicates write FDuplicates;
    property Text:          string  read GetText        write SetText;
    property CommaText:     string  read GetCommaText   write SetCommaText;
    property Strings[Index: Integer]: string  read Get  write Put; default;
    property Objects[Index: Integer]: Pointer read GetObject write SetObject;
  end;

procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);

implementation

{ ================================================================== }
{ TComponent                                                           }
{ ================================================================== }

procedure TComponent.GrowChildren;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FChildCap;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FChildren := ReallocMem(Self.FChildren, NewCap * SizeOf(Pointer));
  ZeroMem(Self.FChildren + OldCap * SizeOf(Pointer),
          (NewCap - OldCap) * SizeOf(Pointer));
  Self.FChildCap := NewCap
end;

procedure TComponent.AddComponent(AComp: TComponent);
var
  Slot: ^Pointer;
begin
  if Self.FChildCnt = Self.FChildCap then
    Self.GrowChildren();
  Slot  := Self.FChildren + Self.FChildCnt * SizeOf(Pointer);
  Slot^ := Pointer(AComp);
  Self.FChildCnt := Self.FChildCnt + 1;
  { The owner holds a strong reference to each child: that is what keeps the
    child alive for as long as the owner lives and lets the owner free its
    children on destruction.  The matching release happens in RemoveComponent
    and Destroy.  FChildren is a raw pointer array, so the ref must be taken
    manually here. }
  _ClassAddRef(Pointer(AComp))
end;

procedure TComponent.RemoveComponent(AComp: TComponent);
var
  I:   Integer;
  Dst: ^Pointer;
  Src: ^Pointer;
begin
  I := 0;
  while I < Self.FChildCnt do
  begin
    Dst := Self.FChildren + I * SizeOf(Pointer);
    if Dst^ = Pointer(AComp) then
    begin
      while I < Self.FChildCnt - 1 do
      begin
        Dst  := Self.FChildren + I * SizeOf(Pointer);
        Src  := Self.FChildren + (I + 1) * SizeOf(Pointer);
        Dst^ := Src^;
        I    := I + 1
      end;
      Dst  := Self.FChildren + (Self.FChildCnt - 1) * SizeOf(Pointer);
      Dst^ := nil;
      Self.FChildCnt := Self.FChildCnt - 1;
      Exit
    end;
    I := I + 1
  end
end;

function TComponent.GetComponent(AIndex: Integer): TComponent;
var
  Slot: ^Pointer;
begin
  Slot   := Self.FChildren + AIndex * SizeOf(Pointer);
  Result := TComponent(Slot^)
end;

constructor TComponent.Create(AOwner: TComponent);
begin
  Self.FOwner    := nil;
  Self.FChildren := nil;
  Self.FChildCap := 0;
  Self.FChildCnt := 0;
  if AOwner <> nil then
  begin
    Self.FOwner := AOwner;
    AOwner.AddComponent(Self)
  end
end;

destructor TComponent.Destroy;
var
  Slot:  ^Pointer;
  Child: TComponent;
begin
  { Release the owner's strong reference to each child in reverse order.
    Detaching FOwner first means the child's own Destroy (if this release
    takes it to zero) skips the RemoveComponent call-back into this object,
    which is already being torn down.  Releasing — rather than Free — is what
    keeps a child alive that the caller still holds a reference to: the owner
    only drops its hold, it does not force destruction. }
  while Self.FChildCnt > 0 do
  begin
    Slot   := Self.FChildren + (Self.FChildCnt - 1) * SizeOf(Pointer);
    Child  := TComponent(Slot^);
    Slot^  := nil;
    Self.FChildCnt := Self.FChildCnt - 1;
    if Child <> nil then
    begin
      Child.FOwner := nil;
      _ClassRelease(Pointer(Child))
    end
  end;
  FreeMem(Self.FChildren);
  Self.FChildren := nil;
  { Detach from owner so its array does not keep a dangling pointer.  This
    object's strong ref held by the owner is the one that just reached zero,
    so RemoveComponent must only unlink the slot — it must not release again. }
  if Self.FOwner <> nil then
    Self.FOwner.RemoveComponent(Self)
end;

procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);
var
  I:     Integer;
  Start: Integer;
begin
  { Line-splitter for TStringList.Text / LoadFromFile.  Each segment between
    separators is added verbatim — leading and trailing whitespace is part of
    the line and must be preserved (standard TStringList semantics).  Trimming
    here previously stripped indentation, which silently corrupted any
    whitespace-significant text round-tripped through Text. }
  AList.Clear();
  Start := 0;
  I     := 0;
  while I < Length(S) do
  begin
    if OrdAt(S, I) = ASep then
    begin
      AList.Add(Copy(S, Start, I - Start));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  if Start < Length(S) then
    AList.Add(Copy(S, Start, Length(S) - Start));
end;


{ ================================================================== }
{ TStringList                                                          }
{ ================================================================== }

procedure TStringList.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FStrings  := ReallocMem(Self.FStrings, NewCap * SizeOf(string));
  Self.FObjects  := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));
  { Zero-initialise new string slots so ARC release of "old" value is safe }
  ZeroMem(Self.FStrings + OldCap * SizeOf(string),
          (NewCap - OldCap) * SizeOf(string));
  Self.FCapacity := NewCap
end;

function TStringList.Compare(const S1: string; const S2: string): Integer;
begin
  if Self.FCaseSensitive then
    Result := CompareStr(S1, S2)
  else
    Result := CompareText(S1, S2)
end;

{ Equality-only comparison for hash probing.  Cheaper than Compare: both
  RTL helpers reject on length before touching the bytes. }
function TStringList.KeyEquals(const S1: string; const S2: string): Boolean;
begin
  if Self.FCaseSensitive then
    Result := S1 = S2
  else
    Result := SameText(S1, S2)
end;

{ FNV-1a over the string bytes, folding A..Z to a..z when the list is
  case-insensitive so equal-modulo-case keys land in the same bucket. }
function TStringList.HashOf(const S: string): Integer;
var
  I: Integer;
  C: Integer;
begin
  Result := -2128831035;   { FNV offset basis 2166136261 as signed 32-bit }
  for I := 0 to Length(S) - 1 do
  begin
    C := Ord(S[I]);
    if (not Self.FCaseSensitive) and (C >= 65) and (C <= 90) then
      C := C + 32;
    Result := (Result xor C) * 16777619;
  end;
end;

procedure TStringList.HashInvalidate;
begin
  if Self.FHashSlots <> nil then
  begin
    FreeMem(Self.FHashSlots);
    Self.FHashSlots := nil;
  end;
  Self.FHashCap  := 0;
  Self.FHashUsed := 0;
end;

{ Insert list index AIdx into the hash table.  A slot already holding an
  equal key is left untouched so IndexOf keeps returning the first-added
  occurrence (overload registration relies on this). }
procedure TStringList.HashInsertIdx(AIdx: Integer);
var
  Slot:  Integer;
  SlotP: ^Integer;
  SPtr:  ^string;
  NPtr:  ^string;
begin
  NPtr := Self.FStrings + AIdx * SizeOf(string);
  Slot := Self.HashOf(NPtr^) and (Self.FHashCap - 1);
  while True do
  begin
    SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
    if SlotP^ = -1 then
    begin
      SlotP^ := AIdx;
      Self.FHashUsed := Self.FHashUsed + 1;
      Exit;
    end;
    SPtr := Self.FStrings + SlotP^ * SizeOf(string);
    if Self.KeyEquals(NPtr^, SPtr^) then
      Exit;   { duplicate key — keep the first-added index }
    Slot := (Slot + 1) and (Self.FHashCap - 1);
  end;
end;

{ (Re)build the table at <= 50% load so probe chains stay short and the
  probe loop in Find always terminates on an empty slot. }
procedure TStringList.HashRebuild;
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
  Self.FHashUsed  := 0;
  for I := 0 to Cap - 1 do
  begin
    P  := Self.FHashSlots + I * SizeOf(Integer);
    P^ := -1;
  end;
  for I := 0 to Self.FCount - 1 do
    Self.HashInsertIdx(I);
end;

procedure TStringList.SetSorted(AValue: Boolean);
begin
  if AValue <> Self.FSorted then
  begin
    Self.FSorted := AValue;
    Self.HashInvalidate();
  end;
end;

procedure TStringList.SetCaseSensitive(AValue: Boolean);
begin
  if AValue <> Self.FCaseSensitive then
  begin
    Self.FCaseSensitive := AValue;
    Self.HashInvalidate();
  end;
end;

function TStringList.FindSorted(const S: string; var Idx: Integer): Boolean;
var
  Lo:   Integer;
  Hi:   Integer;
  Mid:  Integer;
  Cmp:  Integer;
  Ptr:  ^string;
begin
  { Compare against the slot in place via the CompareStr/CompareText
    builtins (raw-pointer RTL calls, no ARC): copying the probe string
    into a local and dispatching through Compare cost several ARC
    operations per binary-search step on the hottest lookup path. }
  Lo := 0;
  Hi := Self.FCount - 1;
  while Lo <= Hi do
  begin
    Mid := (Lo + Hi) div 2;
    Ptr := Self.FStrings + Mid * SizeOf(string);
    if Self.FCaseSensitive then
      Cmp := CompareStr(S, Ptr^)
    else
      Cmp := CompareText(S, Ptr^);
    if Cmp = 0 then
    begin
      Idx    := Mid;
      Result := True;
      Exit
    end
    else if Cmp < 0 then
      Hi := Mid - 1
    else
      Lo := Mid + 1
  end;
  Idx    := Lo;
  Result := False
end;

constructor TStringList.Create;
begin
  Self.FCaseSensitive := True;
  Self.FSorted        := False;
  Self.FDuplicates    := dupAccept
end;

destructor TStringList.Destroy;
var
  I:   Integer;
  Ptr: ^string;
begin
  { Release all strings before freeing the backing store }
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FStrings + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  FreeMem(Self.FStrings);
  FreeMem(Self.FObjects);
  Self.FStrings  := nil;
  Self.FObjects  := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0;
  Self.HashInvalidate()
end;

function TStringList.Add(S: string): Integer;
var
  Idx:  Integer;
  StrP: ^string;
  ObjP: ^Pointer;
begin
  if Self.FSorted then
  begin
    Self.FindSorted(S, Idx);
    if (Self.FDuplicates = dupIgnore) and
       (Idx < Self.FCount) then
    begin
      { Check for exact match at Idx }
      StrP := Self.FStrings + Idx * SizeOf(string);
      if Self.Compare(S, StrP^) = 0 then
      begin
        Result := Idx;
        Exit
      end
    end;
    Self.Insert(Idx, S);
    Result := Idx
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow();
    StrP        := Self.FStrings + Self.FCount * SizeOf(string);
    ObjP        := Self.FObjects + Self.FCount * SizeOf(Pointer);
    StrP^       := S;
    ObjP^       := nil;
    Result      := Self.FCount;
    Self.FCount := Self.FCount + 1;
    { Keep the hash index live across appends; once the table would pass
      50% load, drop it and let the next Find rebuild at double size. }
    if Self.FHashCap > 0 then
    begin
      if (Self.FHashUsed + 1) * 2 > Self.FHashCap then
        Self.HashInvalidate()
      else
        Self.HashInsertIdx(Result);
    end;
  end
end;

procedure TStringList.AddObject(S: string; AObject: Pointer);
var
  Idx:  Integer;
  ObjP: ^Pointer;
begin
  Idx  := Self.Add(S);
  ObjP := Self.FObjects + Idx * SizeOf(Pointer);
  ObjP^ := AObject
end;

function TStringList.Find(const S: string; var Index: Integer): Boolean;
const
  cHashThreshold = 16;   { below this a linear scan beats building a table }
var
  I:     Integer;
  Ptr:   ^string;
  Slot:  Integer;
  SlotP: ^Integer;
begin
  if Self.FSorted then
    Result := Self.FindSorted(S, Index)
  else if Self.FCount >= cHashThreshold then
  begin
    { Hash probe for large unsorted lists.  The table is at most half
      full (HashRebuild / the Add guard), so an empty slot terminates
      every probe chain. }
    if Self.FHashCap = 0 then
      Self.HashRebuild();
    Slot := Self.HashOf(S) and (Self.FHashCap - 1);
    while True do
    begin
      SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
      if SlotP^ = -1 then
      begin
        Index := -1;
        Exit(False);
      end;
      Ptr := Self.FStrings + SlotP^ * SizeOf(string);
      if Self.KeyEquals(S, Ptr^) then
      begin
        Index := SlotP^;
        Exit(True);
      end;
      Slot := (Slot + 1) and (Self.FHashCap - 1);
    end;
  end
  else
  begin
    { Linear search for small unsorted list }
    I := 0;
    while I < Self.FCount do
    begin
      Ptr := Self.FStrings + I * SizeOf(string);
      if Self.Compare(S, Ptr^) = 0 then
      begin
        Index  := I;
        Result := True;
        Exit
      end;
      I := I + 1
    end;
    Index  := -1;
    Result := False
  end
end;

function TStringList.IndexOf(const S: string): Integer;
var
  Idx: Integer;
begin
  if Self.Find(S, Idx) then
    Result := Idx
  else
    Result := -1
end;

function TStringList.Get(AIndex: Integer): string;
var
  Ptr: ^string;
begin
  Ptr    := Self.FStrings + AIndex * SizeOf(string);
  Result := Ptr^
end;

procedure TStringList.Put(AIndex: Integer; S: string);
var
  Ptr: ^string;
begin
  Ptr  := Self.FStrings + AIndex * SizeOf(string);
  Ptr^ := S;
  Self.HashInvalidate()
end;

function TStringList.GetObject(AIndex: Integer): Pointer;
var
  Ptr: ^Pointer;
begin
  Ptr    := Self.FObjects + AIndex * SizeOf(Pointer);
  Result := Ptr^
end;

procedure TStringList.SetObject(AIndex: Integer; AObject: Pointer);
var
  Ptr: ^Pointer;
begin
  Ptr  := Self.FObjects + AIndex * SizeOf(Pointer);
  Ptr^ := AObject
end;

procedure TStringList.Delete(AIndex: Integer);
var
  I:    Integer;
  SDst: ^string;
  SSrc: ^string;
  ODst: ^Pointer;
  OSrc: ^Pointer;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    SDst  := Self.FStrings + I * SizeOf(string);
    SSrc  := Self.FStrings + (I + 1) * SizeOf(string);
    ODst  := Self.FObjects + I * SizeOf(Pointer);
    OSrc  := Self.FObjects + (I + 1) * SizeOf(Pointer);
    SDst^ := SSrc^;
    ODst^ := OSrc^;
    I     := I + 1
  end;
  { Release the last (duplicate) string slot and clear the object slot }
  SDst  := Self.FStrings + (Self.FCount - 1) * SizeOf(string);
  SDst^ := nil;
  ODst  := Self.FObjects + (Self.FCount - 1) * SizeOf(Pointer);
  ODst^ := nil;
  Self.FCount := Self.FCount - 1;
  Self.HashInvalidate()
end;

procedure TStringList.Clear;
var
  I:   Integer;
  Ptr: ^string;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FStrings + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  Self.FCount := 0;
  Self.HashInvalidate()
end;

procedure TStringList.Insert(AIndex: Integer; S: string);
var
  I:    Integer;
  SDst: ^string;
  SSrc: ^string;
  ODst: ^Pointer;
  OSrc: ^Pointer;
  Ptr:  ^string;
  OPtr: ^Pointer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  { Shift elements right from FCount-1 down to AIndex }
  I := Self.FCount;
  while I > AIndex do
  begin
    SDst  := Self.FStrings + I * SizeOf(string);
    SSrc  := Self.FStrings + (I - 1) * SizeOf(string);
    ODst  := Self.FObjects + I * SizeOf(Pointer);
    OSrc  := Self.FObjects + (I - 1) * SizeOf(Pointer);
    SDst^ := SSrc^;
    ODst^ := OSrc^;
    I     := I - 1
  end;
  { Zero the source slot that was shifted (now duplicated at AIndex+1) }
  SSrc  := Self.FStrings + AIndex * SizeOf(string);
  SSrc^ := nil;  { release the "old" value ARC wrote there during shift }
  { Write the new string at AIndex }
  Ptr   := Self.FStrings + AIndex * SizeOf(string);
  OPtr  := Self.FObjects + AIndex * SizeOf(Pointer);
  Ptr^  := S;
  OPtr^ := nil;
  Self.FCount := Self.FCount + 1;
  Self.HashInvalidate()
end;

procedure TStringList.AddStrings(ASource: TStringList);
var
  I: Integer;
begin
  I := 0;
  while I < ASource.FCount do
  begin
    Self.Add(ASource.Get(I));
    I := I + 1
  end;
end;

function TStringList.GetText: string;
var
  SB:  TStringBuilder;
  I:   Integer;
  Ptr: ^string;
begin
  SB := TStringBuilder.Create();
  try
    I := 0;
    while I < Self.FCount do
    begin
      Ptr := Self.FStrings + I * SizeOf(string);
      SB.AppendLine(Ptr^);
      I := I + 1
    end;
    Result := SB.ToString();
  finally
    SB.Free()
  end
end;

procedure TStringList.SetText(AText: string);
begin
  Self.Clear();
  SplitIntoList(AText, Ord(#10), Self)
end;

procedure TStringList.LoadFromFile(APath: string);
begin
  Self.SetText(ReadFile(APath))
end;

procedure TStringList.SaveToFile(APath: string);
begin
  WriteFile(APath, Self.GetText())
end;

function TStringList.GetEnumerator: TStringListEnumerator;
begin
  Result := TStringListEnumerator.Create(Self)
end;

procedure TStringList.CustomSort(ACompare: TStringListSortCompare);
var
  { Iterative bottom-up merge sort on the string+object arrays }
  Width:  Integer;
  Lo:     Integer;
  Mid:    Integer;
  Hi:     Integer;
  N:      Integer;
  { merge workspace }
  TmpStr: ^string;
  TmpObj: ^Pointer;
  I:      Integer;
  J:      Integer;
  K:      Integer;
  SA:     ^string;
  SB:     ^string;
  OA:     ^Pointer;
  OB:     ^Pointer;
  WS:     ^string;
  WO:     ^Pointer;
  DS:     ^string;
  DO_:    ^Pointer;
begin
  N := Self.FCount;
  if N < 2 then Exit;
  TmpStr := GetMem(N * SizeOf(string));
  TmpObj := GetMem(N * SizeOf(Pointer));
  ZeroMem(TmpStr, N * SizeOf(string));
  ZeroMem(TmpObj, N * SizeOf(Pointer));
  Width := 1;
  while Width < N do
  begin
    Lo := 0;
    while Lo < N do
    begin
      Mid := Lo + Width;
      if Mid > N then Mid := N;
      Hi  := Lo + Width * 2;
      if Hi > N then Hi := N;
      { merge [Lo..Mid) and [Mid..Hi) into TmpStr/TmpObj }
      I := Lo;
      J := Mid;
      K := Lo;
      while (I < Mid) and (J < Hi) do
      begin
        SA := Self.FStrings + I * SizeOf(string);
        SB := Self.FStrings + J * SizeOf(string);
        if ACompare(SA^, SB^) <= 0 then
        begin
          WS  := TmpStr + K * SizeOf(string);
          WO  := TmpObj + K * SizeOf(Pointer);
          OA  := Self.FObjects + I * SizeOf(Pointer);
          WS^ := SA^;
          WO^ := OA^;
          I   := I + 1
        end
        else
        begin
          WS  := TmpStr + K * SizeOf(string);
          WO  := TmpObj + K * SizeOf(Pointer);
          OB  := Self.FObjects + J * SizeOf(Pointer);
          WS^ := SB^;
          WO^ := OB^;
          J   := J + 1
        end;
        K := K + 1
      end;
      while I < Mid do
      begin
        SA  := Self.FStrings + I * SizeOf(string);
        OA  := Self.FObjects + I * SizeOf(Pointer);
        WS  := TmpStr + K * SizeOf(string);
        WO  := TmpObj + K * SizeOf(Pointer);
        WS^ := SA^;
        WO^ := OA^;
        I   := I + 1;
        K   := K + 1
      end;
      while J < Hi do
      begin
        SB  := Self.FStrings + J * SizeOf(string);
        OB  := Self.FObjects + J * SizeOf(Pointer);
        WS  := TmpStr + K * SizeOf(string);
        WO  := TmpObj + K * SizeOf(Pointer);
        WS^ := SB^;
        WO^ := OB^;
        J   := J + 1;
        K   := K + 1
      end;
      { copy merged run back }
      K := Lo;
      while K < Hi do
      begin
        WS  := TmpStr + K * SizeOf(string);
        WO  := TmpObj + K * SizeOf(Pointer);
        DS  := Self.FStrings + K * SizeOf(string);
        DO_ := Self.FObjects + K * SizeOf(Pointer);
        DS^ := WS^;
        DO_^ := WO^;
        K   := K + 1
      end;
      Lo := Lo + Width * 2
    end;
    Width := Width * 2
  end;
  { Release temp arrays — zero strings first so ARC doesn't double-release }
  I := 0;
  while I < N do
  begin
    WS  := TmpStr + I * SizeOf(string);
    WS^ := nil;
    I   := I + 1
  end;
  FreeMem(TmpStr);
  FreeMem(TmpObj);
  Self.HashInvalidate()
end;

function TStringList.GetCommaText: string;
var
  SB:   TStringBuilder;
  I:    Integer;
  Item: string;
  Need: Boolean;
  J:    Integer;
  Ch:   Integer;
begin
  SB := TStringBuilder.Create();
  try
    I := 0;
    while I < Self.FCount do
    begin
      Item := Self.Get(I);
      { Quote if item contains comma, space, or double-quote }
      Need := False;
      J := 0;
      while J < Length(Item) do
      begin
        Ch := OrdAt(Item, J);
        if (Ch = Ord(',')) or (Ch = Ord(' ')) or (Ch = Ord('"')) then
        begin
          Need := True;
          Break
        end;
        J := J + 1
      end;
      if I > 0 then SB.AppendByte(Ord(','));
      if Need then
      begin
        { Wrap in double quotes; escape inner double-quotes as "" }
        SB.AppendByte(Ord('"'));
        J := 0;
        while J < Length(Item) do
        begin
          Ch := OrdAt(Item, J);
          if Ch = Ord('"') then
          begin
            SB.AppendByte(Ord('"'));
            SB.AppendByte(Ord('"'))
          end
          else
            SB.AppendByte(Ch);
          J := J + 1
        end;
        SB.AppendByte(Ord('"'))
      end
      else
        SB.Append(Item);
      I := I + 1
    end;
    Result := SB.ToString();
  finally
    SB.Free()
  end
end;

procedure TStringList.SetCommaText(const S: string);
var
  I:    Integer;
  N:    Integer;
  Item: string;
  InQ:  Boolean;
  Ch:   Integer;
begin
  Self.Clear();
  N    := Length(S);
  I    := 0;
  Item := '';
  while I <= N do
  begin
    if I = N then
    begin
      Self.Add(Item);
      I := I + 1
    end
    else
    begin
      Ch := OrdAt(S, I);
      if Ch = Ord('"') then
      begin
        { quoted token }
        I    := I + 1;
        Item := '';
        InQ  := True;
        while (I < N) and InQ do
        begin
          Ch := OrdAt(S, I);
          if Ch = Ord('"') then
          begin
            if (I + 1 < N) and (OrdAt(S, I + 1) = Ord('"')) then
            begin
              { escaped double-quote }
              Item := Item + '"';
              I    := I + 2
            end
            else
            begin
              InQ := False;
              I   := I + 1
            end
          end
          else
          begin
            Item := Item + Chr(Ch);
            I    := I + 1
          end
        end;
        Self.Add(Item);
        { skip trailing comma if present }
        if (I < N) and (OrdAt(S, I) = Ord(',')) then
          I := I + 1;
        Item := ''
      end
      else if Ch = Ord(',') then
      begin
        Self.Add(Item);
        Item := '';
        I    := I + 1
      end
      else
      begin
        Item := Item + Chr(Ch);
        I    := I + 1
      end
    end
  end
end;

{ ================================================================== }
{ TCriticalSection                                                     }
{ ================================================================== }

constructor TCriticalSection.Create;
var P: Pointer;
begin
  P := Pointer(Self) + 8;
  ZeroMem(P, 48);
  pthread_mutex_init(P, nil)
end;

destructor TCriticalSection.Destroy;
var P: Pointer;
begin
  P := Pointer(Self) + 8;
  pthread_mutex_destroy(P)
end;

procedure TCriticalSection.Enter;
var P: Pointer;
begin
  P := Pointer(Self) + 8;
  pthread_mutex_lock(P)
end;

procedure TCriticalSection.Leave;
var P: Pointer;
begin
  P := Pointer(Self) + 8;
  pthread_mutex_unlock(P)
end;

{ ================================================================== }
{ TThread                                                              }
{ ================================================================== }

procedure ThreadTrampoline(Arg: Pointer);
var
  T: TThread;
begin
  T := TThread(Arg);
  try
    T.Execute()
  finally
    T.FFinished := True
  end
end;

constructor TThread.Create(ACreateSuspended: Boolean);
begin
  Self.FHandle := 0;
  Self.FFinished := False;
  Self.FTerminated := False;
  if not ACreateSuspended then
    Self.Start()
end;

destructor TThread.Destroy;
begin
  if (Self.FHandle <> 0) and (not Self.FFinished) then
    Self.WaitFor()
end;

procedure TThread.Execute;
begin
end;

procedure TThread.Start;
var
  Fn: TThreadProc;
  H: Int64;
begin
  if Self.FHandle <> 0 then Exit;
  Fn := @ThreadTrampoline;
  H := 0;
  pthread_create(@H, nil, Pointer(Fn), Pointer(Self));
  Self.FHandle := H
end;

procedure TThread.Terminate;
begin
  Self.FTerminated := True
end;

procedure TThread.WaitFor;
begin
  if Self.FHandle <> 0 then
  begin
    pthread_join(Self.FHandle, nil);
    Self.FHandle := 0
  end
end;

{ ================================================================== }
{ TStringListEnumerator                                                }
{ ================================================================== }

constructor TStringListEnumerator.Create(AList: TStringList);
begin
  Self.FList  := AList;
  Self.FIndex := -1
end;

function TStringListEnumerator.MoveNext: Boolean;
begin
  Self.FIndex := Self.FIndex + 1;
  Result := Self.FIndex < Self.FList.Count
end;

function TStringListEnumerator.GetCurrent: string;
begin
  Result := Self.FList.Get(Self.FIndex)
end;

end.
