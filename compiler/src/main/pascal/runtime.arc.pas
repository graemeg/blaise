{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — ARC management (pure Pascal)

  String layout — data-pointer convention (shared with blaise_str.pas):
    data_ptr - 12  RefCount  (Integer, 4 bytes)
    data_ptr -  8  Length    (Integer, 4 bytes)
    data_ptr -  4  Capacity  (Integer, 4 bytes)
    data_ptr +  0  UTF-8 char data + NUL terminator
    the DATA POINTER is what the variable slot holds

  Class instance layout — same offset convention for ARC header:
    +--[4 bytes]--+--[4 bytes]--+--[8 bytes]--+--[user fields...]--+
    | RefCount    | (padding)   | cleanup ptr | ...                |
    +-------------+-------------+-------------+--------------------+
                                               ^--- user pointer (what Pascal code sees)

  nil = unassigned.  RefCount = -1 = immortal (string literals).

  Thread safety: all refcount increments and decrements use atomic
  lock xadd instructions (via _AtomicAddInt32/_AtomicSubInt32 from
  blaise_atomic_x86_64.s).  The atomic decrement returns the previous
  value, so exactly one thread sees the transition to zero and performs
  destruction -- no TOCTOU race.
}

unit runtime.arc;

interface

type
  TFieldCleanupProc = procedure(Self: Pointer);
  { Signature of the compiler-synthesised attribute factory thunks stored in
    the typeinfo attrs tables — each constructs one attribute instance with
    its declared constructor arguments and returns it. }
  TAttrThunk = function: Pointer;
  PPointer = ^Pointer;
  PInteger = ^Integer;

procedure _StringAddRef(Ptr: Pointer);
procedure _StringRelease(Ptr: Pointer);
procedure _DynArrayAddRef(Ptr: Pointer);
procedure _DynArrayRelease(Ptr: Pointer);
{ Element hooks for dynamic arrays of managed elements.  A hook retains
  (ARetain <> 0) or releases the Count elements starting at Data; the
  array's header records it (see _DynArraySetLengthM in runtime.str) and
  _DynArrayRelease runs it when the last reference goes.  The backends emit
  their own hook for a record / static-array element with managed fields. }
procedure _DynElemsString(Data: Pointer; Count, ARetain: Integer);
procedure _DynElemsClass(Data: Pointer; Count, ARetain: Integer);
procedure _DynElemsDynArray(Data: Pointer; Count, ARetain: Integer);
procedure _DynElemsIntf(Data: Pointer; Count, ARetain: Integer);
procedure _DynElemsRefEnv(Data: Pointer; Count, ARetain: Integer);
function  _StringEquals(S1, S2: Pointer): Integer;
function  _StringConcat(S1, S2: Pointer): Pointer;
procedure TObject_Destroy(Self: Pointer);
function  TObject_ToString(Self: Pointer): Pointer;
function  _MethodAddress(Self, Name: Pointer): Pointer;
function  _InheritsFrom(AChild, AParent: Pointer): Boolean;
function  _ClassCreate(TInfo: Pointer): Pointer;
procedure _ClassAddRef(UserPtr: Pointer);
procedure _ClassRelease(UserPtr: Pointer);
function  _ClassAlloc(Size: Int64; Cleanup: Pointer): Pointer;
procedure _ClassFree(UserPtr: Pointer);
function  _HasClassAttribute(AClassTI, AAttrTI: Pointer): Boolean;
{ Attribute reification.  The Get* helpers construct a FRESH attribute
  instance on every call by invoking the factory thunk stored next to the
  attribute's typeinfo pointer in the class attrs table (typeinfo slot 7,
  (typeinfo, thunk) pairs) or the method-attrs table (typeinfo slot 8,
  (method name, typeinfo, thunk) triples).  All walk the parent chain.
  AName is a Blaise string (data pointer); matching uses _StringEquals. }
function  _GetClassAttribute(AClassTI, AAttrTI: Pointer): Pointer;
function  _HasMethodAttribute(AClassTI, AName, AAttrTI: Pointer): Boolean;
function  _GetMethodAttribute(AClassTI, AName, AAttrTI: Pointer): Pointer;
function  _MethodAttributeCount(AClassTI, AName: Pointer): Integer;
function  _GetMethodAttributeAt(AClassTI, AName: Pointer; AIndex: Integer): Pointer;
procedure _AbstractMethodError;
procedure _LeakTrackerEnable;
procedure _LeakTrackerRegister(UserPtr: Pointer; ClassName: Pointer;
  UnitName: Pointer; Line: Int64);
{ Temporarily suspend / resume the leak tracker.  The tracker's table is a
  global open-addressed map with NO locking; running it while N worker OS
  threads concurrently create/release objects (the multicore fiber scheduler)
  corrupts it.  The scheduler suspends it while N>1 workers run and resumes it
  afterwards.  Suspend returns the previous enabled state so the caller can
  restore exactly (a no-op when the tracker was never enabled, e.g. a non-debug
  build).  Idempotent-safe: Resume(False) leaves it disabled. }
function  _LeakTrackerSuspend: Boolean;
procedure _LeakTrackerResume(APrevEnabled: Boolean);
{ True while the leak tracker is actively recording (used by the multicore
  leak-guard test to prove the tracker is suspended under N workers). }
function  _LeakTrackerIsEnabled: Boolean;
{ Register an at-exit handler.  Uses __cxa_atexit, NOT atexit: glibc's bare
  `atexit` lives only in the static libc_nonshared.a (it is not a dynamic export
  of libc.so.6), so a link that does not pull that archive — as the native
  backend's internal and external linkers do not — leaves `atexit` unresolved at
  load time.  __cxa_atexit is a genuine dynamic libc export and resolves on
  every link path.  Its third argument is the DSO handle; nil registers the
  handler against the main program.  The handler is passed one (ignored) arg. }
function _libc_cxa_atexit(Fn, Arg, DsoHandle: Pointer): Integer;
  external name '__cxa_atexit';

implementation

const
  IMMORTAL  = -1;
  HDR_SIZE  = 12;   { string header: RefCount + Length + Capacity }
  CLASS_HDR = 16;   { class header:  RefCount + pad + cleanup ptr }
  STDERR_FD = 2;
  MAX_1GIB  = 1073741824;

procedure _libc_memcpy(Dst, Src: Pointer; N: Int64);       external name 'memcpy';
function  _libc_memcmp(P1, P2: Pointer; N: Int64): Integer; external name 'memcmp';
procedure _libc_memset(Dst: Pointer; Val: Integer; N: Int64); external name 'memset';
function  _libc_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64; external name 'write';
procedure _libc_abort; external name 'abort';

function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);          external name '_BlaiseFreeMem';
procedure _WeakZeroSlots(Target: Pointer);       external name '_WeakZeroSlots';

function  _AtomicAddInt32(Ptr: PInteger; Delta: Integer): Integer;
            external name '_AtomicAddInt32';
function  _AtomicSubInt32(Ptr: PInteger; Delta: Integer): Integer;
            external name '_AtomicSubInt32';

procedure MemCopy(Dst, Src: Pointer; N: Integer);
begin
  if N > 0 then
    _libc_memcpy(Dst, Src, N);
end;

function MemCompare(P1, P2: Pointer; N: Integer): Integer;
begin
  if N = 0 then
    Result := 0
  else
    Result := _libc_memcmp(P1, P2, N);
end;

{ ------------------------------------------------------------------ }
{ Diagnostic helpers                                                   }
{ ------------------------------------------------------------------ }

procedure DiagAbort(Msg: Pointer; Len: Integer);
var
  NL: Byte;
begin
  _libc_write(STDERR_FD, Msg, Int64(Len));
  NL := 10;
  _libc_write(STDERR_FD, @NL, 1);
  _libc_abort();
end;

procedure _AbstractMethodError;
begin
  DiagAbort('Runtime error: abstract method called.', 39);
end;

{ ------------------------------------------------------------------ }
{ Leak tracker — separate hash map, zero overhead when disabled        }
{ ------------------------------------------------------------------ }
{
  Open-addressing hash map: key = UserPtr (Pointer), value = className
  string data pointer (immortal — points into the binary's typeinfo).
  Enabled only when _LeakTrackerEnable is called (i.e. --debug builds).
  _ClassAlloc registers every live object; _ClassRelease unregisters it.
  On exit, _LeakTrackerReport walks all buckets and prints survivors.

  Bucket layout (each bucket is two pointer-sized slots):
    slot[0]  key   (UserPtr; nil = empty; $DEADBEEF = tombstone)
    slot[1]  value (class-name string data ptr)

  Table is allocated via _BlaiseGetMem and never freed (debug mode only).
}

const
  LT_BUCKETS   = 4096;   { must be power of two; larger for string/dynarray tracking }
  LT_BUCKET_SZ = 32;     { 4 × 8-byte slots: key, classname, unitname, line }

var
  GLTEnabled:   Boolean;
  GLTTable:     PChar;    { raw bucket array, LT_BUCKETS * LT_BUCKET_SZ bytes }
  GLTCount:     Integer;
  GLTTombstone: Pointer;  { sentinel for deleted slots, set to Pointer(1) at init }
  GLTTagString:  Pointer; { sentinel classname tag for leaked strings, Pointer(2) }
  GLTTagDynArray: Pointer; { sentinel classname tag for leaked dyn-arrays, Pointer(3) }

function LTHash(P: Pointer): Integer;
var
  V: PtrUInt;
begin
  V := PtrUInt(P);
  V := V xor (V shr 13);
  V := V xor (V shr 7);
  Result := Integer(V and (LT_BUCKETS - 1));
end;

procedure LTInsert(Key, ClassName, UnitName: Pointer; Line: Int64);
var
  Idx, Step: Integer;
  Slot: ^Pointer;
  LineSlot: ^Int64;
begin
  Idx := LTHash(Key);
  Step := 0;
  while Step < LT_BUCKETS do
  begin
    Slot := Pointer(GLTTable + Idx * LT_BUCKET_SZ);
    if (Slot^ = nil) or (Slot^ = GLTTombstone) then
    begin
      Slot^ := Key;
      Slot  := Pointer(Pointer(Slot) + 8);
      Slot^ := ClassName;
      Slot  := Pointer(Pointer(Slot) + 8);
      Slot^ := UnitName;
      LineSlot := Pointer(Pointer(Slot) + 8);
      LineSlot^ := Line;
      Inc(GLTCount);
      Exit;
    end;
    Idx := (Idx + 1) and (LT_BUCKETS - 1);
    Inc(Step);
  end;
end;

procedure LTDelete(Key: Pointer);
var
  Idx, Step: Integer;
  Slot: ^Pointer;
begin
  Idx := LTHash(Key);
  Step := 0;
  while Step < LT_BUCKETS do
  begin
    Slot := Pointer(GLTTable + Idx * LT_BUCKET_SZ);
    if Slot^ = nil then Exit;
    if Slot^ = Key then
    begin
      Slot^ := GLTTombstone;
      Dec(GLTCount);
      Exit;
    end;
    Idx := (Idx + 1) and (LT_BUCKETS - 1);
    Inc(Step);
  end;
end;

procedure WriteStr(Msg: Pointer; Len: Integer);
begin
  _libc_write(STDERR_FD, Msg, Int64(Len));
end;

procedure WriteNL;
var
  NL: Byte;
begin
  NL := 10;
  _libc_write(STDERR_FD, @NL, 1);
end;

procedure WriteInt(V: Integer);
var
  Buf: array[0..19] of Byte;
  Pos: Integer;
  N: Integer;
begin
  if V = 0 then
  begin
    Buf[0] := Ord('0');
    _libc_write(STDERR_FD, @Buf[0], 1);
    Exit;
  end;
  Pos := 19;
  N := V;
  while N > 0 do
  begin
    Buf[Pos] := Ord('0') + Byte(N mod 10);
    N := N div 10;
    Dec(Pos);
  end;
  _libc_write(STDERR_FD, @Buf[Pos + 1], Int64(19 - Pos));
end;

procedure WriteSignedInt(V: Integer);
var
  Neg: Byte;
begin
  if V < 0 then
  begin
    Neg := Ord('-');
    _libc_write(STDERR_FD, @Neg, 1);
    WriteInt(-V);
  end
  else
    WriteInt(V);
end;

procedure WriteStrSlot(DataPtr: Pointer);
var
  LenSlot: ^Integer;
  Len: Integer;
begin
  if DataPtr = nil then begin WriteStr('(unknown)', 9); Exit end;
  LenSlot := DataPtr - 8;
  Len := LenSlot^;
  if (Len > 0) and (Len < 256) then
    WriteStr(DataPtr, Len)
  else
    WriteStr('(unknown)', 9);
end;

procedure _LeakTrackerReport;
var
  I: Integer;
  Slot: ^Pointer;
  NamePtr: ^Pointer;
  ClassName: Pointer;
  UnitSlot: ^Pointer;
  UnitName: Pointer;
  LineSlot: ^Int64;
  Line: Int64;
  RCSlot: ^Integer;
  RC: Integer;
begin
  if not GLTEnabled then Exit;
  if GLTCount = 0 then Exit;
  WriteStr('Blaise leak report:', 19);
  WriteNL();
  WriteStr('  ', 2);
  WriteInt(GLTCount);
  WriteStr(' leak(s) not released:', 22);
  WriteNL();
  for I := 0 to LT_BUCKETS - 1 do
  begin
    Slot := Pointer(GLTTable + I * LT_BUCKET_SZ);
    if (Slot^ <> nil) and (Slot^ <> GLTTombstone) then
    begin
      NamePtr   := Pointer(Pointer(Slot) + 8);
      ClassName := NamePtr^;
      UnitSlot  := Pointer(Pointer(Slot) + 16);
      UnitName  := UnitSlot^;
      LineSlot  := Pointer(Pointer(Slot) + 24);
      Line      := LineSlot^;
      WriteStr('  - ', 4);
      if ClassName = GLTTagString then
      begin
        WriteStr('string', 6);
        RCSlot := Slot^ - HDR_SIZE;
        RC := RCSlot^;
      end
      else if ClassName = GLTTagDynArray then
      begin
        WriteStr('dynarray', 8);
        RCSlot := Slot^ - 8;
        RC := RCSlot^;
      end
      else
      begin
        WriteStrSlot(ClassName);
        RCSlot := Slot^ - CLASS_HDR;
        RC := RCSlot^;
      end;
      WriteStr(' (rc=', 5);
      WriteSignedInt(RC);
      WriteStr(')', 1);
      if UnitName <> nil then
      begin
        WriteStr(' at ', 4);
        WriteStrSlot(UnitName);
        WriteStr(':', 1);
        WriteInt(Integer(Line));
      end;
      WriteNL();
    end;
  end;
end;

procedure _LeakTrackerRegister(UserPtr: Pointer; ClassName: Pointer;
  UnitName: Pointer; Line: Int64);
begin
  if not GLTEnabled then Exit;
  if UserPtr = nil then Exit;
  LTInsert(UserPtr, ClassName, UnitName, Line);
end;

procedure _LeakTrackerEnable;
var
  TableSize: Integer;
  Sentinel: PtrUInt;
begin
  if GLTEnabled then Exit;
  GLTEnabled := True;
  GLTCount := 0;
  { Use address 1 as tombstone — never a valid heap pointer (heap starts
    well above page 0, and address 1 is in the unmapped zero page). }
  Sentinel := 1;
  GLTTombstone := Pointer(Sentinel);
  Sentinel := 2;
  GLTTagString := Pointer(Sentinel);
  Sentinel := 3;
  GLTTagDynArray := Pointer(Sentinel);
  TableSize := LT_BUCKETS * LT_BUCKET_SZ;
  GLTTable := PChar(_BlaiseGetMem(TableSize));
  if GLTTable = nil then begin GLTEnabled := False; Exit end;
  _libc_memset(GLTTable, 0, Int64(TableSize));
  _libc_cxa_atexit(Pointer(@_LeakTrackerReport), nil, nil);
end;

function _LeakTrackerSuspend: Boolean;
begin
  Result := GLTEnabled;
  GLTEnabled := False;
end;

procedure _LeakTrackerResume(APrevEnabled: Boolean);
begin
  { Only re-enable when the table actually exists; a suspend from a build that
    never enabled tracking (GLTTable = nil) must stay disabled. }
  if APrevEnabled and (GLTTable <> nil) then
    GLTEnabled := True;
end;

function _LeakTrackerIsEnabled: Boolean;
begin
  Result := GLTEnabled;
end;

{ ------------------------------------------------------------------ }
{ Class ARC                                                            }
{ ------------------------------------------------------------------ }

function _ClassAlloc(Size: Int64; Cleanup: Pointer): Pointer;
var
  Total: Integer;
  Base: PChar;
  CleanupSlot: PPointer;
begin
  Total := Integer(Size) + CLASS_HDR;
  Base := PChar(_BlaiseGetMem(Total));
  if Base = nil then begin Result := nil; Exit end;
  _libc_memset(Pointer(Base), 0, Int64(Total));
  CleanupSlot := PPointer(Base + 8);
  CleanupSlot^ := Cleanup;
  Result := Pointer(Base + CLASS_HDR);
end;

procedure _ClassRelease(UserPtr: Pointer);
var
  Base: PChar;
  OldRC: Integer;
  CleanupSlot: PPointer;
  Cleanup: TFieldCleanupProc;
begin
  if UserPtr = nil then Exit;
  Base := PChar(UserPtr) - CLASS_HDR;
  OldRC := _AtomicSubInt32(PInteger(Base), 1);
  if OldRC = 1 then
  begin
    if GLTEnabled then
      LTDelete(UserPtr);
    _WeakZeroSlots(UserPtr);
    CleanupSlot := PPointer(Base + 8);
    if CleanupSlot^ <> nil then
    begin
      Cleanup := TFieldCleanupProc(CleanupSlot^);
      Cleanup(UserPtr);
    end;
    _BlaiseFreeMem(Pointer(Base));
  end;
end;

{ ------------------------------------------------------------------ }
{ String ARC                                                           }
{ ------------------------------------------------------------------ }

procedure _StringAddRef(Ptr: Pointer);
var
  RC: PInteger;
  OldRC: Integer;
begin
  if Ptr = nil then Exit;
  RC := PInteger(Ptr - HDR_SIZE);
  if RC^ = IMMORTAL then Exit;
  OldRC := _AtomicAddInt32(RC, 1);
  if (OldRC = 0) and GLTEnabled then
    LTInsert(Ptr, GLTTagString, nil, 0);
end;

procedure _StringRelease(Ptr: Pointer);
var
  Base: Pointer;
  RC: PInteger;
  LN, CP: ^Integer;
  OldRC: Integer;
begin
  if Ptr = nil then Exit;
  Base := Ptr - HDR_SIZE;
  RC := PInteger(Base);
  if RC^ = IMMORTAL then Exit;
  LN := Base + 4;
  CP := Base + 8;
  { Header sanity checks inlined — this is the hottest runtime function
    (one call per string release, ~350M per compiler self-compile) and the
    out-of-line _StringReleaseCheck call doubled its cost.  DiagAbort is
    the cold path. }
  if RC^ < -1 then
    DiagAbort('blaise: _StringRelease double-free (refcount < -1)', 51);
  if (LN^ < 0) or (LN^ > MAX_1GIB) then
    DiagAbort('blaise: _StringRelease corrupted header (bad length)', 55);
  if (CP^ < LN^) or (CP^ > MAX_1GIB) then
    DiagAbort('blaise: _StringRelease corrupted header (bad capacity)', 57);
  OldRC := _AtomicSubInt32(RC, 1);
  if OldRC = 1 then
  begin
    if GLTEnabled then LTDelete(Ptr);
    _BlaiseFreeMem(Base);
  end;
end;

{ Dynamic-array block: [element hook:8][refcount:4][length:4][elements].
  The data pointer points at element 0, so the refcount is at Ptr - 8, the
  length at Ptr - 4 (both unchanged from the 8-byte header the hook was
  added in front of -- code emitted by older compilers, and the debugger,
  read them there) and the hook at Ptr - 16.  Layout is defined by
  _DynArraySetLengthM in runtime.str. }

type
  TDynElemHook = procedure(Data: Pointer; Count, ARetain: Integer);

procedure _DynArrayAddRef(Ptr: Pointer);
var
  RC: PInteger;
  OldRC: Integer;
begin
  if Ptr = nil then Exit;
  RC := PInteger(Ptr - 8);
  if RC^ = IMMORTAL then Exit;
  OldRC := _AtomicAddInt32(RC, 1);
  if (OldRC = 0) and GLTEnabled then
    LTInsert(Ptr, GLTTagDynArray, nil, 0);
end;

procedure _DynArrayRelease(Ptr: Pointer);
var
  RC:     PInteger;
  OldRC:  Integer;
  HookP:  ^Pointer;
  LenP:   PInteger;
  Hook:   TDynElemHook;
begin
  if Ptr = nil then Exit;
  RC := PInteger(Ptr - 8);
  if RC^ = IMMORTAL then Exit;
  OldRC := _AtomicSubInt32(RC, 1);
  if OldRC = 1 then
  begin
    if GLTEnabled then LTDelete(Ptr);
    { the last reference: release the managed elements first }
    HookP := Ptr - 16;
    if HookP^ <> nil then
    begin
      LenP := PInteger(Ptr - 4);
      Hook := TDynElemHook(HookP^);
      Hook(Ptr, LenP^, 0);
    end;
    _BlaiseFreeMem(Ptr - 16);
  end;
end;

procedure _DynElemsString(Data: Pointer; Count, ARetain: Integer);
var
  I: Integer;
  P: ^Pointer;
begin
  P := Data;
  for I := 0 to Count - 1 do
  begin
    if ARetain <> 0 then _StringAddRef(P^) else _StringRelease(P^);
    P := Pointer(P) + 8;
  end;
end;

procedure _DynElemsClass(Data: Pointer; Count, ARetain: Integer);
var
  I: Integer;
  P: ^Pointer;
begin
  P := Data;
  for I := 0 to Count - 1 do
  begin
    if ARetain <> 0 then _ClassAddRef(P^) else _ClassRelease(P^);
    P := Pointer(P) + 8;
  end;
end;

procedure _DynElemsDynArray(Data: Pointer; Count, ARetain: Integer);
var
  I: Integer;
  P: ^Pointer;
begin
  P := Data;
  for I := 0 to Count - 1 do
  begin
    if ARetain <> 0 then _DynArrayAddRef(P^) else _DynArrayRelease(P^);
    P := Pointer(P) + 8;
  end;
end;

procedure _DynElemsIntf(Data: Pointer; Count, ARetain: Integer);
var
  I: Integer;
  P: ^Pointer;
begin
  { an interface element is the 16-byte (obj, itab) pair; only the obj
    half is counted }
  P := Data;
  for I := 0 to Count - 1 do
  begin
    if ARetain <> 0 then _ClassAddRef(P^) else _ClassRelease(P^);
    P := Pointer(P) + 16;
  end;
end;

procedure _DynElemsRefEnv(Data: Pointer; Count, ARetain: Integer);
var
  I: Integer;
  P: ^Pointer;
begin
  { a 'reference to' closure element is (Code, Env); the Env at +8 is the
    counted object }
  P := Data + 8;
  for I := 0 to Count - 1 do
  begin
    if ARetain <> 0 then _ClassAddRef(P^) else _ClassRelease(P^);
    P := Pointer(P) + 16;
  end;
end;

function _StringEquals(S1, S2: Pointer): Integer;
var
  Len1, Len2: Integer;
  LN:         ^Integer;
  C1, C2:     PChar;
begin
  if S1 = S2 then
  begin
    Exit(1);
  end;
  if S1 = nil then
    Len1 := 0
  else
  begin
    LN   := S1 - 8;   { Length at data_ptr − 8 }
    Len1 := LN^;
  end;
  if S2 = nil then
    Len2 := 0
  else
  begin
    LN   := S2 - 8;
    Len2 := LN^;
  end;
  if Len1 <> Len2 then
  begin
    Exit(0);
  end;
  if Len1 = 0 then
  begin
    Exit(1);
  end;
  C1 := PChar(S1);    { data IS the pointer }
  C2 := PChar(S2);
  if MemCompare(C1, C2, Len1) = 0 then
    Result := 1
  else
    Result := 0;
end;

function _StringConcat(S1, S2: Pointer): Pointer;
var
  Len1, Len2, Total: Integer;
  LN:                ^Integer;
  Base:              Pointer;
  RC, LenF, CapF:    ^Integer;
  Dst:               PChar;
begin
  if S1 = nil then
    Len1 := 0
  else
  begin
    LN   := S1 - 8;   { Length at data_ptr − 8 }
    Len1 := LN^;
  end;
  if S2 = nil then
    Len2 := 0
  else
  begin
    LN   := S2 - 8;
    Len2 := LN^;
  end;
  Total  := Len1 + Len2;
  Base   := _BlaiseGetMem(HDR_SIZE + Total + 1);
  if Base = nil then Exit;
  RC    := Base;             { RefCount at base+0 }
  RC^   := 0;
  LenF  := Base + 4;
  LenF^ := Total;
  CapF  := Base + 8;
  CapF^ := Total;
  Result := Base + HDR_SIZE; { DATA POINTER }
  Dst    := PChar(Result);
  if Len1 > 0 then
    MemCopy(Dst, PChar(S1), Len1);
  if Len2 > 0 then
    MemCopy(Dst + Len1, PChar(S2), Len2);
  Dst[Total] := 0;
end;

{ ------------------------------------------------------------------ }
{ TObject virtuals                                                     }
{ ------------------------------------------------------------------ }

procedure TObject_Destroy(Self: Pointer);
begin
end;

{ TObject_ToString: returns the class name as an immortal string.
  Instance layout: Self[0] = vptr -> vtable.
  Vtable layout:   vtable[0] = typeinfo, vtable[1] = Destroy, vtable[2] = ToString.
  Typeinfo layout: typeinfo[0]=parent, typeinfo[1]=impllist, typeinfo[2]=classname ptr. }
function TObject_ToString(Self: Pointer): Pointer;
var
  Slot:   ^Pointer;
  VTable: Pointer;
  TInfo:  Pointer;
begin
  if Self = nil then
    begin
    Exit(nil);
    end;
  Slot   := Self;         { instance: first 8 bytes = vptr }
  VTable := Slot^;        { VTable points to vtable data }
  Slot   := VTable;       { vtable[0] = typeinfo ptr }
  TInfo  := Slot^;        { TInfo points to typeinfo data }
  Slot   := TInfo + 16;   { typeinfo[2] = classname, at byte offset 16 }
  Result := Slot^;
end;

{ _MethodAddress: walk the typeinfo chain for an instance, looking up
  Name in each class's published-method table.  Layout:
    instance[0]  = vptr -> vtable
    vtable[0]    = typeinfo
    typeinfo[3]  = published-methods table (or 0)
    methods[0]   = count (Int64)
    methods[1+]  = triples of (name-string-data-ptr, code-ptr,
                   param-sig-string-data-ptr or 0)
  Returns nil when no match is found.  Equality on names uses
  _StringEquals so the caller passes a Blaise string. }
function _MethodAddress(Self, Name: Pointer): Pointer;
var
  Slot:    ^Pointer;
  VTable:  Pointer;
  TInfo:   Pointer;
  Methods: Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  EntName: Pointer;
  EntAddr: Pointer;
  I:       Integer;
begin
  Result := nil;
  if (Self = nil) or (Name = nil) then Exit;
  Slot   := Self;
  VTable := Slot^;
  if VTable = nil then Exit;
  Slot  := VTable;
  TInfo := Slot^;
  while TInfo <> nil do
  begin
    Slot    := TInfo + 24;   { typeinfo[3] = methods table ptr }
    Methods := Slot^;
    if Methods <> nil then
    begin
      Count := Methods;
      Entry := Methods + 8;  { skip 8-byte count }
      for I := 0 to Integer(Count^) - 1 do
      begin
        EntName := Entry^;
        Entry   := Pointer(Entry) + 8;
        EntAddr := Entry^;
        Entry   := Pointer(Entry) + 16;  { skip code ptr + param-sig ptr }
        if _StringEquals(EntName, Name) <> 0 then
        begin
          Exit(EntAddr);
        end;
      end;
    end;
    Slot  := TInfo;          { typeinfo[0] = parent }
    TInfo := Slot^;
  end;
end;

{ _InheritsFrom: class-identity walk for TObject.InheritsFrom.
  AChild and AParent are both typeinfo pointers (the values returned by
  Obj.ClassType or a bare class-identifier reference).
  Returns True when AChild equals AParent or is a descendant of AParent.
  A nil AParent always returns False; a nil AChild always returns False. }
function _InheritsFrom(AChild, AParent: Pointer): Boolean;
var
  TI: ^Pointer;
  Current: Pointer;
begin
  Result := False;
  if (AChild = nil) or (AParent = nil) then Exit;
  Current := AChild;
  while Current <> nil do
  begin
    if Current = AParent then
    begin
      Exit(True);
    end;
    TI      := Current;   { typeinfo[0] = parent pointer }
    Current := TI^;
  end;
end;

{ _ClassCreate: runtime equivalent of the inline EmitConstructorCall
  lowering the codegen produces for the static 'TFoo.Create' form.
  Reads totalsize, fieldcleanup pointer, and vtable pointer from the
  expanded class typeinfo (see typeinfo layout in blaise.codegen.qbe.pas's
  EmitTypeInfoDefs).  Allocates an instance, installs the vtable
  pointer at slot 0, and bumps the refcount once.

  Typeinfo offsets read here:
    typeinfo[ 4]  +32  -> totalsize  (Int64)
    typeinfo[ 5]  +40  -> $_FieldCleanup_<T>
    typeinfo[ 6]  +48  -> $vtable_<T> }
function _ClassCreate(TInfo: Pointer): Pointer;
var
  SizeSlot:   ^Int64;
  PtrSlot:    ^Pointer;
  Size:       Int64;
  Cleanup:    Pointer;
  VTable:     Pointer;
  UserPtr:    Pointer;
  VTableSlot: ^Pointer;
begin
  Result := nil;
  if TInfo = nil then Exit;

  SizeSlot := TInfo + 32;
  Size     := SizeSlot^;

  PtrSlot  := TInfo + 40;
  Cleanup  := PtrSlot^;

  PtrSlot  := TInfo + 48;
  VTable   := PtrSlot^;

  UserPtr  := _ClassAlloc(Size, Cleanup);
  if UserPtr = nil then Exit;

  { Install the vtable pointer at instance[0] — the codegen emits
    'storel $vtable_T, %self' immediately after _ClassAlloc; mirror
    that here. }
  VTableSlot  := UserPtr;
  VTableSlot^ := VTable;

  _ClassAddRef(UserPtr);
  Result := UserPtr;
end;

procedure _ClassAddRef(UserPtr: Pointer);
var
  Hdr: Pointer;
begin
  if UserPtr = nil then Exit;
  Hdr := UserPtr - CLASS_HDR;
  _AtomicAddInt32(PInteger(Hdr), 1);
end;

procedure _ClassFree(UserPtr: Pointer);
begin
  _ClassRelease(UserPtr);
end;

{ _HasClassAttribute: check whether a class (identified by its typeinfo pointer
  AClassTI) carries the custom attribute identified by AAttrTI.  Reads typeinfo
  slot 7 (offset 56) for the attribute table, then walks the parent chain via
  slot 0 so attributes on a parent class are visible on derived classes.

  Class attribute table layout (emitted by EmitTypeInfoDefs):
    table[0]  = count (Int64/l-slot)
    table[1+] = (attr typeinfo ptr, factory thunk ptr) pairs }
function _HasClassAttribute(AClassTI, AAttrTI: Pointer): Boolean;
var
  Current: Pointer;
  Slot:    ^Pointer;
  Attrs:   Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  I:       Integer;
begin
  Result := False;
  if (AClassTI = nil) or (AAttrTI = nil) then Exit;
  Current := AClassTI;
  while Current <> nil do
  begin
    Slot  := Current + 56;   { typeinfo slot 7 = attribute table ptr }
    Attrs := Slot^;
    if Attrs <> nil then
    begin
      Count := Attrs;        { first l-slot = count }
      Entry := Attrs + 8;    { entries start after 8-byte count }
      for I := 0 to Integer(Count^) - 1 do
      begin
        if Entry^ = AAttrTI then
        begin
          Exit(True);
        end;
        Entry := Pointer(Entry) + 16;  { pair stride: typeinfo + thunk }
      end;
    end;
    Slot    := Current;      { typeinfo slot 0 = parent typeinfo ptr }
    Current := Slot^;
  end;
end;

{ _GetClassAttribute: reify the class attribute identified by AAttrTI — find
  its (typeinfo, thunk) pair in the class attrs table (walking the parent
  chain like _HasClassAttribute) and call the factory thunk, which constructs
  the attribute instance with its declared constructor arguments.  Returns a
  FRESH instance on every call, or nil when the attribute is absent. }
function _GetClassAttribute(AClassTI, AAttrTI: Pointer): Pointer;
var
  Current: Pointer;
  Slot:    ^Pointer;
  Attrs:   Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  Thunk:   ^Pointer;
  Make:    TAttrThunk;
  I:       Integer;
begin
  Result := nil;
  if (AClassTI = nil) or (AAttrTI = nil) then Exit;
  Current := AClassTI;
  while Current <> nil do
  begin
    Slot  := Current + 56;   { typeinfo slot 7 = attribute table ptr }
    Attrs := Slot^;
    if Attrs <> nil then
    begin
      Count := Attrs;
      Entry := Attrs + 8;
      for I := 0 to Integer(Count^) - 1 do
      begin
        if Entry^ = AAttrTI then
        begin
          Thunk := Pointer(Entry) + 8;
          Make  := TAttrThunk(Thunk^);
          Exit(Make());
        end;
        Entry := Pointer(Entry) + 16;
      end;
    end;
    Slot    := Current;
    Current := Slot^;
  end;
end;

{ Method-attrs table lookups.  Table layout (typeinfo slot 8, offset 64):
    table[0]  = count (Int64/l-slot)
    table[1+] = (method name string-data ptr, attr typeinfo ptr,
                 factory thunk ptr) triples
  The name is compared with _StringEquals against the caller's Blaise
  string.  The parent chain is walked so attributes on inherited published
  methods remain visible on derived classes. }

function _MethodAttributeCount(AClassTI, AName: Pointer): Integer;
var
  Current: Pointer;
  Slot:    ^Pointer;
  Attrs:   Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  I:       Integer;
begin
  Result := 0;
  if (AClassTI = nil) or (AName = nil) then Exit;
  Current := AClassTI;
  while Current <> nil do
  begin
    Slot  := Current + 64;   { typeinfo slot 8 = method-attrs table ptr }
    Attrs := Slot^;
    if Attrs <> nil then
    begin
      Count := Attrs;
      Entry := Attrs + 8;
      for I := 0 to Integer(Count^) - 1 do
      begin
        if _StringEquals(Entry^, AName) <> 0 then
          Result := Result + 1;
        Entry := Pointer(Entry) + 24;  { triple stride }
      end;
    end;
    Slot    := Current;
    Current := Slot^;
  end;
end;

function _HasMethodAttribute(AClassTI, AName, AAttrTI: Pointer): Boolean;
var
  Current: Pointer;
  Slot:    ^Pointer;
  Attrs:   Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  AttrPtr: ^Pointer;
  I:       Integer;
begin
  Result := False;
  if (AClassTI = nil) or (AName = nil) or (AAttrTI = nil) then Exit;
  Current := AClassTI;
  while Current <> nil do
  begin
    Slot  := Current + 64;
    Attrs := Slot^;
    if Attrs <> nil then
    begin
      Count := Attrs;
      Entry := Attrs + 8;
      for I := 0 to Integer(Count^) - 1 do
      begin
        AttrPtr := Pointer(Entry) + 8;
        if (AttrPtr^ = AAttrTI) and (_StringEquals(Entry^, AName) <> 0) then
        begin
          Exit(True);
        end;
        Entry := Pointer(Entry) + 24;
      end;
    end;
    Slot    := Current;
    Current := Slot^;
  end;
end;

function _GetMethodAttribute(AClassTI, AName, AAttrTI: Pointer): Pointer;
var
  Current: Pointer;
  Slot:    ^Pointer;
  Attrs:   Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  AttrPtr: ^Pointer;
  Thunk:   ^Pointer;
  Make:    TAttrThunk;
  I:       Integer;
begin
  Result := nil;
  if (AClassTI = nil) or (AName = nil) or (AAttrTI = nil) then Exit;
  Current := AClassTI;
  while Current <> nil do
  begin
    Slot  := Current + 64;
    Attrs := Slot^;
    if Attrs <> nil then
    begin
      Count := Attrs;
      Entry := Attrs + 8;
      for I := 0 to Integer(Count^) - 1 do
      begin
        AttrPtr := Pointer(Entry) + 8;
        if (AttrPtr^ = AAttrTI) and (_StringEquals(Entry^, AName) <> 0) then
        begin
          Thunk := Pointer(Entry) + 16;
          Make  := TAttrThunk(Thunk^);
          Exit(Make());
        end;
        Entry := Pointer(Entry) + 24;
      end;
    end;
    Slot    := Current;
    Current := Slot^;
  end;
end;

{ _GetMethodAttributeAt: reify the AIndex'th (0-based) attribute on the named
  method, counting across the parent chain in declaration order (own class
  first).  Pairs with _MethodAttributeCount for enumeration.  Returns nil
  when AIndex is out of range. }
function _GetMethodAttributeAt(AClassTI, AName: Pointer; AIndex: Integer): Pointer;
var
  Current: Pointer;
  Slot:    ^Pointer;
  Attrs:   Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  Thunk:   ^Pointer;
  Make:    TAttrThunk;
  I:       Integer;
  Seen:    Integer;
begin
  Result := nil;
  if (AClassTI = nil) or (AName = nil) or (AIndex < 0) then Exit;
  Seen    := 0;
  Current := AClassTI;
  while Current <> nil do
  begin
    Slot  := Current + 64;
    Attrs := Slot^;
    if Attrs <> nil then
    begin
      Count := Attrs;
      Entry := Attrs + 8;
      for I := 0 to Integer(Count^) - 1 do
      begin
        if _StringEquals(Entry^, AName) <> 0 then
        begin
          if Seen = AIndex then
          begin
            Thunk := Pointer(Entry) + 16;
            Make  := TAttrThunk(Thunk^);
            Exit(Make());
          end;
          Seen := Seen + 1;
        end;
        Entry := Pointer(Entry) + 24;
      end;
    end;
    Slot    := Current;
    Current := Slot^;
  end;
end;

end.
