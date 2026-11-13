{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit rtl.platform.watch.windows;
// The file-change notification IO.Watch uses, on Windows, over
// ReadDirectoryChangesW.  The flat _Watch* functions and their contract are
// those of rtl.platform.watch.inotify.
//
// Windows reports changes to a directory's entries, not to a file, and a
// directory's own deletion or rename shows only in its parent.  So every
// watched path watches its parent directory for the entry of its own name:
// that entry modified is a change, and removed, renamed, or added anew (an
// editor's save renames a new file over the old) is the path gone.  A
// watched directory also watches itself, for its entries.
//
// A watch set is a completion port.  Each directory read is overlapped and
// completes there, keyed by the watch's id and which of its two reads it
// is.  A watch removed or gone cancels its reads, but its record -- which
// the system writes the changes into -- is kept until the last cancelled
// read has completed, and its id is not reused until then.

interface

function _WatchOpen: Int64;
procedure _WatchClose(ASet: Int64);
function _WatchAdd(ASet: Int64; const APath: string): Int64;
procedure _WatchRemove(ASet, AId: Int64);
function _WatchWait(ASet: Int64; ATimeoutMs: Int32; AEvents: Pointer;
  AMax: Int32): Int32;

implementation

function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';

function W32CreateFileW(AName: Pointer; AAccess, AShare: UInt32;
  ASecurity: Pointer; ADisposition, AFlags: UInt32;
  ATemplate: Pointer): Pointer; external 'kernel32' name 'CreateFileW';
function W32CloseHandle(AHandle: Pointer): Int32;
  external 'kernel32' name 'CloseHandle';
function W32GetFileAttributesW(AName: Pointer): UInt32;
  external 'kernel32' name 'GetFileAttributesW';
function W32MultiByteToWideChar(ACodePage, AFlags: UInt32; AMulti: Pointer;
  AMultiLen: Int32; AWide: Pointer; AWideLen: Int32): Int32;
  external 'kernel32' name 'MultiByteToWideChar';
function W32CreateIoCompletionPort(AFile, APort: Pointer; AKey: UInt64;
  AThreads: UInt32): Pointer; external 'kernel32' name 'CreateIoCompletionPort';
function W32GetQueuedCompletionStatus(APort: Pointer; ABytes, AKey,
  AOverlapped: Pointer; ATimeout: UInt32): Int32;
  external 'kernel32' name 'GetQueuedCompletionStatus';
function W32ReadDirectoryChangesW(ADir: Pointer; ABuffer: Pointer;
  ASize: UInt32; ASubtree: Int32; AFilter: UInt32; ABytes: Pointer;
  AOverlapped: Pointer; ARoutine: Pointer): Int32;
  external 'kernel32' name 'ReadDirectoryChangesW';
function W32CancelIoEx(AHandle: Pointer; AOverlapped: Pointer): Int32;
  external 'kernel32' name 'CancelIoEx';
function W32CompareStringOrdinal(A: Pointer; ALen: Int32; B: Pointer;
  BLen: Int32; AIgnoreCase: Int32): Int32;
  external 'kernel32' name 'CompareStringOrdinal';
function W32GetTickCount64: Int64; external 'kernel32' name 'GetTickCount64';

const
  CP_UTF8 = 65001;
  FILE_LIST_DIRECTORY = $0001;
  FILE_SHARE_ALL = $0007;
  OPEN_EXISTING = 3;
  FILE_FLAG_BACKUP_SEMANTICS = $02000000;
  FILE_FLAG_OVERLAPPED = $40000000;
  INVALID_FILE_ATTRIBUTES = $FFFFFFFF;
  FILE_ATTRIBUTE_DIRECTORY = $0010;
  FILE_NOTIFY_CHANGE_FILE_NAME = $0001;
  FILE_NOTIFY_CHANGE_DIR_NAME = $0002;
  FILE_NOTIFY_CHANGE_ATTRIBUTES = $0004;
  FILE_NOTIFY_CHANGE_SIZE = $0008;
  FILE_NOTIFY_CHANGE_LAST_WRITE = $0010;
  { the parent is asked about its entries' names and contents, the
    directory itself only about its entries' names }
  PARENT_FILTER = FILE_NOTIFY_CHANGE_FILE_NAME or FILE_NOTIFY_CHANGE_DIR_NAME
    or FILE_NOTIFY_CHANGE_ATTRIBUTES or FILE_NOTIFY_CHANGE_SIZE
    or FILE_NOTIFY_CHANGE_LAST_WRITE;
  SELF_FILTER = FILE_NOTIFY_CHANGE_FILE_NAME or FILE_NOTIFY_CHANGE_DIR_NAME;
  FILE_ACTION_MODIFIED = 3;
  CSTR_EQUAL = 2;
  INFINITE = $FFFFFFFF;
  OVERLAPPED_SIZE = 32;
  NOTIFY_BUF_SIZE = 16384;
  { the two reads of a watch }
  READ_PARENT = 0;
  READ_SELF = 1;
  KIND_NONE = -1;
  KIND_CHANGED = 0;
  KIND_GONE = 1;

type
  PUInt16 = ^UInt16;
  PUInt32 = ^UInt32;
  PInt64 = ^Int64;
  PPointer = ^Pointer;

  { One watched path.  Dirs, Bufs and the two OVERLAPPEDs in Ovs are
    indexed by READ_PARENT and READ_SELF; a watch of a file, or of a root
    directory (which has no parent), uses one of them. }
  TWinWatch = record
    { 2 * OVERLAPPED_SIZE: an implementation-section type cannot size
      itself on an implementation-section constant yet }
    Ovs: array[0..63] of Byte;
    Dirs: array[0..1] of Pointer;
    Bufs: array[0..1] of Pointer;
    { the path's last component, UTF-16 }
    Name: Pointer;
    NameUnits: Int32;
    { reads issued and not yet completed }
    Pending: Int32;
    { 0 once the watch is removed or gone }
    Active: Int32;
  end;
  PWinWatch = ^TWinWatch;

  TWinWatchSet = record
    Port: Pointer;
    { a PWinWatch per id, nil when free }
    Slots: Pointer;
    Cap: Int32;
  end;
  PWinWatchSet = ^TWinWatchSet;

function IsValidHandle(H: Pointer): Boolean;
begin
  Result := (H <> nil) and (H <> Pointer(-1));
end;

{ S as UTF-16 in a new block with room for a NUL; AUnits gets its length
  in units. }
function ToWide(const S: string; out AUnits: Int32): Pointer;
var
  Len: Int32;
begin
  Len := Int32(Length(S));
  AUnits := 0;
  if Len > 0 then
    AUnits := W32MultiByteToWideChar(CP_UTF8, 0, PChar(S), Len, nil, 0);
  Result := _BlaiseGetMem((Int64(AUnits) + 1) * 2);
  if AUnits > 0 then
    W32MultiByteToWideChar(CP_UTF8, 0, PChar(S), Len, Result, AUnits);
  PUInt16(Result + Int64(AUnits) * 2)^ := 0;
end;

{ A NUL-terminated copy of AUnits units at W, in a new block. }
function WideCopy(W: Pointer; AUnits: Int32): Pointer;
var
  I: Int32;
begin
  Result := _BlaiseGetMem((Int64(AUnits) + 1) * 2);
  for I := 0 to AUnits - 1 do
    PUInt16(Result + Int64(I) * 2)^ := PUInt16(W + Int64(I) * 2)^;
  PUInt16(Result + Int64(AUnits) * 2)^ := 0;
end;

function UnitAt(W: Pointer; I: Int32): UInt16;
begin
  Result := PUInt16(W + Int64(I) * 2)^;
end;

function OpenDir(W: Pointer): Pointer;
begin
  Result := W32CreateFileW(W, FILE_LIST_DIRECTORY, FILE_SHARE_ALL, nil,
    OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS or FILE_FLAG_OVERLAPPED, nil);
  if not IsValidHandle(Result) then
    Result := nil;
end;

function SlotOf(S: PWinWatchSet; AId: Int64): PWinWatch;
begin
  if (AId < 0) or (AId >= S^.Cap) then
    Exit(nil);
  Result := PPointer(S^.Slots + AId * SizeOf(Pointer))^;
end;

procedure SetSlot(S: PWinWatchSet; AId: Int64; W: PWinWatch);
begin
  PPointer(S^.Slots + AId * SizeOf(Pointer))^ := W;
end;

{ A free id, the table grown by doubling when it is full; -1 when it
  cannot grow. }
function FreeId(S: PWinWatchSet): Int64;
var
  I, NewCap: Int32;
  NewSlots: Pointer;
begin
  for I := 0 to S^.Cap - 1 do
    if SlotOf(S, I) = nil then
      Exit(I);
  NewCap := S^.Cap * 2;
  if NewCap < 16 then
    NewCap := 16;
  NewSlots := _BlaiseGetMem(Int64(NewCap) * SizeOf(Pointer));
  if NewSlots = nil then
    Exit(-1);
  for I := 0 to NewCap - 1 do
    PPointer(NewSlots + Int64(I) * SizeOf(Pointer))^ := nil;
  for I := 0 to S^.Cap - 1 do
    PPointer(NewSlots + Int64(I) * SizeOf(Pointer))^ := SlotOf(S, I);
  if S^.Slots <> nil then
    _BlaiseFreeMem(S^.Slots);
  Result := S^.Cap;
  S^.Slots := NewSlots;
  S^.Cap := NewCap;
end;

{ Issue read AWhich of watch W; False when it cannot be issued. }
function Arm(W: PWinWatch; AWhich: Int32): Boolean;
var
  I: Int32;
  Ov: Pointer;
  Filter: UInt32;
begin
  Ov := @W^.Ovs[AWhich * OVERLAPPED_SIZE];
  for I := 0 to OVERLAPPED_SIZE - 1 do
    W^.Ovs[AWhich * OVERLAPPED_SIZE + I] := 0;
  Filter := PARENT_FILTER;
  if AWhich = READ_SELF then
    Filter := SELF_FILTER;
  Result := W32ReadDirectoryChangesW(W^.Dirs[AWhich], W^.Bufs[AWhich],
    NOTIFY_BUF_SIZE, 0, Filter, nil, Ov, nil) <> 0;
  if Result then
    W^.Pending := W^.Pending + 1;
end;

procedure FreeWatch(S: PWinWatchSet; AId: Int64);
var
  W: PWinWatch;
  I: Int32;
begin
  W := SlotOf(S, AId);
  if W = nil then
    Exit;
  for I := 0 to 1 do
    if W^.Bufs[I] <> nil then
      _BlaiseFreeMem(W^.Bufs[I]);
  if W^.Name <> nil then
    _BlaiseFreeMem(W^.Name);
  _BlaiseFreeMem(W);
  SetSlot(S, AId, nil);
end;

{ End watch AId: cancel its reads and close its directories.  Its record
  goes once no read is pending. }
procedure Deactivate(S: PWinWatchSet; AId: Int64);
var
  W: PWinWatch;
  I: Int32;
begin
  W := SlotOf(S, AId);
  if (W = nil) or (W^.Active = 0) then
    Exit;
  W^.Active := 0;
  for I := 0 to 1 do
    if W^.Dirs[I] <> nil then
    begin
      W32CancelIoEx(W^.Dirs[I], nil);
      W32CloseHandle(W^.Dirs[I]);
      W^.Dirs[I] := nil;
    end;
  if W^.Pending = 0 then
    FreeWatch(S, AId);
end;

function _WatchOpen: Int64;
var
  S: PWinWatchSet;
begin
  S := _BlaiseGetMem(SizeOf(TWinWatchSet));
  if S = nil then
    Exit(-1);
  S^.Port := W32CreateIoCompletionPort(Pointer(-1), nil, 0, 1);
  S^.Slots := nil;
  S^.Cap := 0;
  if S^.Port = nil then
  begin
    _BlaiseFreeMem(S);
    Exit(-1);
  end;
  Result := Int64(S);
end;

{ The completions of reads still pending are collected before the records
  they write into are freed; a record whose read never completes (within
  a second) is left allocated rather than freed under the system. }
procedure _WatchClose(ASet: Int64);
var
  S: PWinWatchSet;
  I: Int32;
  Busy: Boolean;
  W: PWinWatch;
  Bytes: UInt32;
  Key: UInt64;
  Ov: Pointer;
begin
  if ASet = -1 then
    Exit;
  S := PWinWatchSet(ASet);
  for I := 0 to S^.Cap - 1 do
    Deactivate(S, I);
  Busy := True;
  while Busy do
  begin
    Busy := False;
    for I := 0 to S^.Cap - 1 do
      if SlotOf(S, I) <> nil then
        Busy := True;
    if not Busy then
      Break;
    Ov := nil;
    Key := 0;
    W32GetQueuedCompletionStatus(S^.Port, @Bytes, @Key, @Ov, 1000);
    if Ov = nil then
      Break;
    W := SlotOf(S, Int64(Key shr 1));
    if W <> nil then
    begin
      W^.Pending := W^.Pending - 1;
      if W^.Pending = 0 then
        FreeWatch(S, Int64(Key shr 1));
    end;
  end;
  W32CloseHandle(S^.Port);
  if not Busy then
  begin
    if S^.Slots <> nil then
      _BlaiseFreeMem(S^.Slots);
    _BlaiseFreeMem(S);
  end;
end;

function _WatchAdd(ASet: Int64; const APath: string): Int64;
var
  S: PWinWatchSet;
  W: PWinWatch;
  Full, Parent: Pointer;
  Units, Last, I, ParentUnits: Int32;
  Attrs: UInt32;
  Id: Int64;
  B: PChar;
begin
  S := PWinWatchSet(ASet);
  if Length(APath) = 0 then
    Exit(-1);
  Full := ToWide(APath, Units);
  { one separator, and none at the end but a root's }
  for I := 0 to Units - 1 do
    if UnitAt(Full, I) = Ord('/') then
      PUInt16(Full + Int64(I) * 2)^ := Ord('\');
  while (Units > 1) and (UnitAt(Full, Units - 1) = Ord('\')) and
        not ((Units = 3) and (UnitAt(Full, 1) = Ord(':'))) do
  begin
    Units := Units - 1;
    PUInt16(Full + Int64(Units) * 2)^ := 0;
  end;
  Attrs := W32GetFileAttributesW(Full);
  if Attrs = INVALID_FILE_ATTRIBUTES then
  begin
    _BlaiseFreeMem(Full);
    Exit(-1);
  end;
  W := _BlaiseGetMem(SizeOf(TWinWatch));
  B := PChar(W);
  for I := 0 to SizeOf(TWinWatch) - 1 do
    B[I] := #0;
  W^.Active := 1;
  { the parent and the last component: 'C:\a\b' is 'C:\a' and 'b', 'C:\a'
    is 'C:\' and 'a', a bare name lives in '.'; a root has no parent }
  Last := -1;
  for I := 0 to Units - 1 do
    if UnitAt(Full, I) = Ord('\') then
      Last := I;
  Parent := nil;
  if Last < 0 then
  begin
    if (Units >= 2) and (UnitAt(Full, 1) = Ord(':')) then
    begin
      Parent := WideCopy(Full, 2);
      W^.Name := WideCopy(Full + 4, Units - 2);
      W^.NameUnits := Units - 2;
    end
    else
    begin
      Parent := ToWide('.', ParentUnits);
      W^.Name := WideCopy(Full, Units);
      W^.NameUnits := Units;
    end;
  end
  else if Last < Units - 1 then
  begin
    ParentUnits := Last;
    if (Last = 0) or ((Last = 2) and (UnitAt(Full, 1) = Ord(':'))) then
      ParentUnits := Last + 1;
    Parent := WideCopy(Full, ParentUnits);
    W^.Name := WideCopy(Full + Int64(Last + 1) * 2, Units - Last - 1);
    W^.NameUnits := Units - Last - 1;
  end;
  if (W^.NameUnits = 0) and (W^.Name <> nil) then
  begin
    _BlaiseFreeMem(Parent);
    Parent := nil;
  end;
  if Parent <> nil then
  begin
    W^.Dirs[READ_PARENT] := OpenDir(Parent);
    _BlaiseFreeMem(Parent);
  end;
  if (Attrs and FILE_ATTRIBUTE_DIRECTORY) <> 0 then
    W^.Dirs[READ_SELF] := OpenDir(Full);
  _BlaiseFreeMem(Full);
  Id := FreeId(S);
  if ((W^.Dirs[READ_PARENT] = nil) and (W^.Dirs[READ_SELF] = nil)) or
     (Id < 0) then
  begin
    for I := 0 to 1 do
      if W^.Dirs[I] <> nil then
        W32CloseHandle(W^.Dirs[I]);
    if W^.Name <> nil then
      _BlaiseFreeMem(W^.Name);
    _BlaiseFreeMem(W);
    Exit(-1);
  end;
  SetSlot(S, Id, W);
  for I := 0 to 1 do
    if W^.Dirs[I] <> nil then
    begin
      W^.Bufs[I] := _BlaiseGetMem(NOTIFY_BUF_SIZE);
      if (W32CreateIoCompletionPort(W^.Dirs[I], S^.Port, UInt64(Id * 2 + I),
           0) = nil) or not Arm(W, I) then
      begin
        Deactivate(S, Id);
        Exit(-1);
      end;
    end;
  Result := Id;
end;

procedure _WatchRemove(ASet, AId: Int64);
begin
  Deactivate(PWinWatchSet(ASet), AId);
end;

{ What read AWhich of W reported in its ABytes of FILE_NOTIFY_INFORMATION
  records (NextEntryOffset, Action, FileNameLength in bytes, then the name):
  for the directory itself, any entry is a change; for the parent, only the
  entry of W's name counts, and anything but its modification means the
  path no longer names what was watched. }
function KindOf(W: PWinWatch; AWhich: Int32; ABytes: UInt32): Int32;
var
  P: Pointer;
  Next, Action, NameBytes: UInt32;
begin
  if ABytes = 0 then
    { the changes overflowed the buffer: which they were is not known }
    Exit(KIND_CHANGED);
  if AWhich = READ_SELF then
    Exit(KIND_CHANGED);
  Result := KIND_NONE;
  P := W^.Bufs[AWhich];
  while True do
  begin
    Next := PUInt32(P)^;
    Action := PUInt32(P + 4)^;
    NameBytes := PUInt32(P + 8)^;
    if W32CompareStringOrdinal(P + 12, Int32(NameBytes div 2), W^.Name,
         W^.NameUnits, 1) = CSTR_EQUAL then
    begin
      if Action <> FILE_ACTION_MODIFIED then
        Exit(KIND_GONE);
      Result := KIND_CHANGED;
    end;
    if Next = 0 then
      Break;
    P := P + Next;
  end;
end;

function _WatchWait(ASet: Int64; ATimeoutMs: Int32; AEvents: Pointer;
  AMax: Int32): Int32;
var
  S: PWinWatchSet;
  W: PWinWatch;
  Deadline, Now: Int64;
  Wait, Bytes: UInt32;
  Key: UInt64;
  Ov: Pointer;
  Ok, Which, Kind: Int32;
  Id: Int64;
begin
  S := PWinWatchSet(ASet);
  Result := 0;
  Deadline := 0;
  Wait := INFINITE;
  if ATimeoutMs >= 0 then
  begin
    Deadline := W32GetTickCount64() + ATimeoutMs;
    Wait := UInt32(ATimeoutMs);
  end;
  while Result < AMax do
  begin
    Ov := nil;
    Key := 0;
    Bytes := 0;
    Ok := W32GetQueuedCompletionStatus(S^.Port, @Bytes, @Key, @Ov, Wait);
    if Ov = nil then
      Break;   { the time ran out }
    Id := Int64(Key shr 1);
    Which := Int32(Key and 1);
    W := SlotOf(S, Id);
    if W <> nil then
    begin
      W^.Pending := W^.Pending - 1;
      if W^.Active = 0 then
      begin
        if W^.Pending = 0 then
          FreeWatch(S, Id);
      end
      else
      begin
        if Ok = 0 then
          { the directory has gone, or can no longer be read }
          Kind := KIND_GONE
        else
          Kind := KindOf(W, Which, Bytes);
        if (Kind <> KIND_GONE) and not Arm(W, Which) then
          Kind := KIND_GONE;
        if Kind <> KIND_NONE then
        begin
          PInt64(AEvents + Int64(Result) * 16)^ := Id;
          PInt64(AEvents + Int64(Result) * 16 + 8)^ := Kind;
          Result := Result + 1;
        end;
        if Kind = KIND_GONE then
          Deactivate(S, Id);
      end;
    end;
    { once there is an event, only what is queued already is collected;
      until then the rest of the time is waited out }
    if Result > 0 then
      Wait := 0
    else if ATimeoutMs >= 0 then
    begin
      Now := W32GetTickCount64();
      if Now >= Deadline then
        Wait := 0
      else
        Wait := UInt32(Deadline - Now);
    end;
  end;
end;

end.
