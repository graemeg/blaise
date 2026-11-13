{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit runtime.syscall.windows;
// The POSIX-named leaves the core runtime binds, over kernel32
// (docs/windows-x86_64-backend-design.adoc, "runtime.syscall.windows").
//
// runtime.mem, runtime.arc, runtime.exc and the platform layer reach the OS
// through a handful of POSIX names bound with a library-less
// `external name 'write'` and so on.  On Linux libc supplies them; here these
// Blaise routines do, with the internal convention.  Only their own calls into
// kernel32 cross the boundary, each through an `external 'kernel32'` binding.
//
// File descriptors 0, 1 and 2 are the standard handles.  A file or pipe the
// platform adapter opens is entered in a descriptor table and gets the next
// free number from 3, so the RTL's Int32 descriptors work unchanged.

interface

{ write(2): Count bytes from Buf to descriptor Fd.  Returns the bytes
  written, or -1.  `write` collides with the Write builtin as a Pascal
  identifier, so the Pascal name is _sys_write and an asm alias publishes the
  bare `write` symbol. }
function _sys_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;

{ mmap(2), anonymous mappings only: committed read-write memory.  Returns
  the address, or Pointer(-1) (MAP_FAILED). }
function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Int32;
  Offset: Int64): Pointer;
{ munmap(2): runtime.mem only ever releases a whole mapping, which is what
  MEM_RELEASE requires. }
function munmap(Addr: Pointer; Length: Int64): Int32;

{ The at-exit list: handlers run last-registered first, by exit. }
function __cxa_atexit(Func, Arg, DsoHandle: Pointer): Int32;
{ Run the at-exit handlers, then end the process with Code.  The bare
  `exit` symbol is an alias of it. }
procedure _RunAtExitAndExit(Code: Int32);
{ End the process at once, running no handlers. }
procedure _exit(Code: Int32);
{ Report an abnormal end on standard error and exit with code 3, as the
  Microsoft C runtime's abort does. }
procedure abort;

{ sysconf(3): the only name the runtime asks for is the online processor
  count. }
function sysconf(Name: Int32): Int64;

const
  { A descriptor's flags: a Winsock SOCKET rather than a kernel32 handle,
    and (for a socket) in non-blocking mode, which Winsock cannot be asked
    for afterwards. }
  WIN_FD_SOCKET = 1;
  WIN_FD_NONBLOCK = 2;

type
  { Closes a socket's handle: Winsock's closesocket, which runtime.net.windows
    supplies once it has loaded ws2_32.  0, or -1 with the error set. }
  TWinSocketCloser = function(AHandle: Pointer): Int32;

{ The kernel32 handle (or SOCKET) behind descriptor Fd, or nil. }
function _WinHandleOfFd(Fd: Int32): Pointer;
{ Enter AHandle in the descriptor table: its descriptor, or -1 (error
  ERROR_TOO_MANY_OPEN_FILES) when the table cannot grow. }
function _WinFdAdd(AHandle: Pointer): Int32;
{ As _WinFdAdd, with the descriptor's WIN_FD_* flags. }
function _WinFdAddFlags(AHandle: Pointer; AFlags: Int32): Int32;
{ Descriptor Fd's WIN_FD_* flags: 0 for a standard descriptor, -1 when Fd
  is not open. }
function _WinFdFlags(Fd: Int32): Int32;
{ Replace descriptor Fd's flags; False when Fd is not a table entry. }
function _WinFdSetFlags(Fd: Int32; AFlags: Int32): Boolean;
{ Take descriptor Fd out of the table: its handle, for the caller to close,
  or nil when Fd is not a table entry. }
function _WinFdRemove(Fd: Int32): Pointer;
{ close(2): take Fd out of the table and close its handle, the socket way
  for a socket.  The standard descriptors stay open.  0, or -1 with the
  error set.  The bare `close` symbol is an alias of it. }
function _WinFdClose(Fd: Int32): Int32;
{ Install the closer for socket descriptors. }
procedure _WinSetSocketCloser(ACloser: TWinSocketCloser);

implementation

{ ---- kernel32 ---- }

function GetStdHandle(AStdHandle: UInt32): Pointer;
  external 'kernel32' name 'GetStdHandle';
function Win32WriteFile(AFile: Pointer; ABuffer: Pointer; ACount: UInt32;
  AWritten: Pointer; AOverlapped: Pointer): Int32;
  external 'kernel32' name 'WriteFile';
function VirtualAlloc(AAddress: Pointer; ASize: UInt64; AAllocationType,
  AProtect: UInt32): Pointer; external 'kernel32' name 'VirtualAlloc';
function VirtualFree(AAddress: Pointer; ASize: UInt64;
  AFreeType: UInt32): Int32; external 'kernel32' name 'VirtualFree';
procedure ExitProcess(ACode: UInt32); external 'kernel32' name 'ExitProcess';
procedure GetSystemInfo(AInfo: Pointer); external 'kernel32' name 'GetSystemInfo';
procedure AcquireSRWLockExclusive(ALock: Pointer);
  external 'kernel32' name 'AcquireSRWLockExclusive';
procedure ReleaseSRWLockExclusive(ALock: Pointer);
  external 'kernel32' name 'ReleaseSRWLockExclusive';
function CloseHandle(AHandle: Pointer): Int32; external 'kernel32' name 'CloseHandle';
procedure SetLastError(ACode: UInt32); external 'kernel32' name 'SetLastError';

const
  STD_INPUT_HANDLE = UInt32(-10);
  STD_OUTPUT_HANDLE = UInt32(-11);
  STD_ERROR_HANDLE = UInt32(-12);
  MEM_COMMIT = $1000;
  MEM_RESERVE = $2000;
  MEM_RELEASE = $8000;
  PAGE_READWRITE = $04;
  MAX_ATEXIT = 64;
  { The first descriptor the table hands out; the table's first size, and
    the most it grows to, by doubling. }
  FIRST_TABLE_FD = 3;
  INITIAL_TABLE_FDS = 1024;
  MAX_TABLE_FDS = 1048576;
  ERROR_INVALID_HANDLE = 6;
  ERROR_TOO_MANY_OPEN_FILES = 4;

type
  { SYSTEM_INFO: dwNumberOfProcessors is the DWORD at offset 32. }
  TSystemInfo = record
    Head: array[0..3] of Int64;
    NumberOfProcessors: UInt32;
    Tail: array[0..2] of UInt32;
  end;

var
  GAtExitFns: array[0..MAX_ATEXIT - 1] of Pointer;
  GAtExitArgs: array[0..MAX_ATEXIT - 1] of Pointer;
  GAtExitCount: Int;
  { The descriptor table: GFdCount TFdEntry slots, slot I holding
    descriptor FIRST_TABLE_FD + I (a nil Handle when free), allocated on the
    first open and doubled when full.  GFdLock, an SRWLOCK, guards it and is
    all zero bits when unlocked, so the zeroed global needs no
    initialisation. }
  GFdTable: Pointer;
  GFdCount: Int;
  GFdLock: Pointer;
  GSocketCloser: TWinSocketCloser;

type
  TFdEntry = record
    Handle: Pointer;
    Flags: Int64;
  end;
  PFdEntry = ^TFdEntry;

{ Slot I of the table; GFdLock held. }
function EntryAt(I: Int): PFdEntry;
begin
  Result := PFdEntry(GFdTable + I * SizeOf(TFdEntry));
end;

{ The slot of descriptor Fd, or nil when Fd is outside the table; GFdLock
  held. }
function SlotOf(Fd: Int32): PFdEntry;
begin
  if (Fd < FIRST_TABLE_FD) or (Fd >= FIRST_TABLE_FD + GFdCount) then
    Exit(nil);
  Result := EntryAt(Fd - FIRST_TABLE_FD);
end;

{ Double the table (or make its first one); False when it cannot grow.
  GFdLock held. }
function GrowTable: Boolean;
var
  NewCount, I: Int;
  NewTable: Pointer;
begin
  if GFdCount = 0 then
    NewCount := INITIAL_TABLE_FDS
  else
    NewCount := GFdCount * 2;
  if NewCount > MAX_TABLE_FDS then
    Exit(False);
  { VirtualAlloc returns zeroed pages: every new slot is free. }
  NewTable := VirtualAlloc(nil, UInt64(NewCount * SizeOf(TFdEntry)),
    MEM_RESERVE or MEM_COMMIT, PAGE_READWRITE);
  if NewTable = nil then
    Exit(False);
  for I := 0 to GFdCount - 1 do
    PFdEntry(NewTable + I * SizeOf(TFdEntry))^ := EntryAt(I)^;
  if GFdTable <> nil then
    VirtualFree(GFdTable, 0, MEM_RELEASE);
  GFdTable := NewTable;
  GFdCount := NewCount;
  Result := True;
end;

function _WinHandleOfFd(Fd: Int32): Pointer;
var
  E: PFdEntry;
begin
  case Fd of
    0: Result := GetStdHandle(STD_INPUT_HANDLE);
    1: Result := GetStdHandle(STD_OUTPUT_HANDLE);
    2: Result := GetStdHandle(STD_ERROR_HANDLE);
  else
    AcquireSRWLockExclusive(@GFdLock);
    E := SlotOf(Fd);
    if E <> nil then
      Result := E^.Handle
    else
      Result := nil;
    ReleaseSRWLockExclusive(@GFdLock);
  end;
end;

function _WinFdAddFlags(AHandle: Pointer; AFlags: Int32): Int32;
var
  I, Start: Int;
begin
  Result := -1;
  AcquireSRWLockExclusive(@GFdLock);
  { The lowest free descriptor, as open(2) gives. }
  Start := 0;
  while Result < 0 do
  begin
    for I := Start to GFdCount - 1 do
      if EntryAt(I)^.Handle = nil then
      begin
        EntryAt(I)^.Handle := AHandle;
        EntryAt(I)^.Flags := AFlags;
        Result := Int32(FIRST_TABLE_FD + I);
        Break;
      end;
    if Result >= 0 then
      Break;
    Start := GFdCount;
    if not GrowTable() then
      Break;
  end;
  ReleaseSRWLockExclusive(@GFdLock);
  if Result < 0 then
    SetLastError(ERROR_TOO_MANY_OPEN_FILES);
end;

function _WinFdAdd(AHandle: Pointer): Int32;
begin
  Result := _WinFdAddFlags(AHandle, 0);
end;

function _WinFdFlags(Fd: Int32): Int32;
var
  E: PFdEntry;
begin
  if (Fd >= 0) and (Fd < FIRST_TABLE_FD) then
    Exit(0);
  Result := -1;
  AcquireSRWLockExclusive(@GFdLock);
  E := SlotOf(Fd);
  if (E <> nil) and (E^.Handle <> nil) then
    Result := Int32(E^.Flags);
  ReleaseSRWLockExclusive(@GFdLock);
end;

function _WinFdSetFlags(Fd: Int32; AFlags: Int32): Boolean;
var
  E: PFdEntry;
begin
  Result := False;
  AcquireSRWLockExclusive(@GFdLock);
  E := SlotOf(Fd);
  if (E <> nil) and (E^.Handle <> nil) then
  begin
    E^.Flags := AFlags;
    Result := True;
  end;
  ReleaseSRWLockExclusive(@GFdLock);
end;

function _WinFdRemove(Fd: Int32): Pointer;
var
  E: PFdEntry;
begin
  AcquireSRWLockExclusive(@GFdLock);
  E := SlotOf(Fd);
  if E <> nil then
  begin
    Result := E^.Handle;
    E^.Handle := nil;
    E^.Flags := 0;
  end
  else
    Result := nil;
  ReleaseSRWLockExclusive(@GFdLock);
end;

function _WinFdClose(Fd: Int32): Int32;
var
  Flags: Int64;
  H: Pointer;
  E: PFdEntry;
begin
  if (Fd >= 0) and (Fd < FIRST_TABLE_FD) then
    Exit(0);
  { The handle and its kind in one step, so a racing close and reopen of
    the same number cannot pair one with the other. }
  H := nil;
  Flags := 0;
  AcquireSRWLockExclusive(@GFdLock);
  E := SlotOf(Fd);
  if E <> nil then
  begin
    H := E^.Handle;
    Flags := E^.Flags;
    E^.Handle := nil;
    E^.Flags := 0;
  end;
  ReleaseSRWLockExclusive(@GFdLock);
  if H = nil then
  begin
    SetLastError(ERROR_INVALID_HANDLE);
    Exit(-1);
  end;
  if ((Flags and WIN_FD_SOCKET) <> 0) and (GSocketCloser <> nil) then
    Result := GSocketCloser(H)
  else if CloseHandle(H) <> 0 then
    Result := 0
  else
    Result := -1;
end;

procedure _close_alias; assembler; nostackframe;
asm
.globl close
close:
    jmp _WinFdClose
end;

procedure _WinSetSocketCloser(ACloser: TWinSocketCloser);
begin
  GSocketCloser := ACloser;
end;

function _sys_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
var
  H: Pointer;
  Written: UInt32;
  Chunk: UInt32;
begin
  H := _WinHandleOfFd(Fd);
  if H = nil then Exit(-1);
  { WriteFile takes a 32-bit count; a larger write reports the part written,
    as a short write(2) does, and the caller loops }
  if Count > $40000000 then
    Chunk := $40000000
  else
    Chunk := UInt32(Count);
  Written := 0;
  if Win32WriteFile(H, Buf, Chunk, @Written, nil) = 0 then
    Exit(-1);
  Result := Written;
end;

{ The bare symbol rtl.platform and runtime.* bind; the arguments are already
  where _sys_write takes them. }
procedure _write_alias; assembler; nostackframe;
asm
.globl write
write:
    jmp _sys_write
end;

function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Int32;
  Offset: Int64): Pointer;
begin
  Result := VirtualAlloc(nil, UInt64(Length), MEM_RESERVE or MEM_COMMIT,
    PAGE_READWRITE);
  if Result = nil then
    Result := Pointer(-1);
end;

function munmap(Addr: Pointer; Length: Int64): Int32;
begin
  if VirtualFree(Addr, 0, MEM_RELEASE) <> 0 then
    Result := 0
  else
    Result := -1;
end;

function __cxa_atexit(Func, Arg, DsoHandle: Pointer): Int32;
begin
  if GAtExitCount >= MAX_ATEXIT then
    Exit(-1);
  GAtExitFns[GAtExitCount] := Func;
  GAtExitArgs[GAtExitCount] := Arg;
  GAtExitCount := GAtExitCount + 1;
  Result := 0;
end;

{ Call a registered handler, void (*func)(void *arg), the internal way: the
  handlers are Blaise routines. }
procedure CallHandler(Func, Arg: Pointer); assembler; nostackframe;
asm
    movq %rsi, %rax
    movq %rdi, %r11
    movq %rax, %rdi
    jmp  *%r11
end;

procedure _RunAtExitAndExit(Code: Int32);
var
  I: Int;
begin
  I := GAtExitCount - 1;
  while I >= 0 do
  begin
    if GAtExitFns[I] <> nil then
      CallHandler(GAtExitFns[I], GAtExitArgs[I]);
    I := I - 1;
  end;
  ExitProcess(UInt32(Code));
end;

procedure _exit_alias; assembler; nostackframe;
asm
.globl exit
exit:
    jmp _RunAtExitAndExit
end;

procedure _exit(Code: Int32);
begin
  ExitProcess(UInt32(Code));
end;

procedure abort;
const
  Msg = 'abnormal program termination'#13#10;
begin
  _sys_write(2, PChar(Msg), Length(Msg));
  ExitProcess(3);
end;

function sysconf(Name: Int32): Int64;
var
  Info: TSystemInfo;
begin
  GetSystemInfo(@Info);
  Result := Info.NumberOfProcessors;
end;

end.
