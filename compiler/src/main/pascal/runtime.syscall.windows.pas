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

{ The kernel32 handle behind descriptor Fd, or nil. }
function _WinHandleOfFd(Fd: Int32): Pointer;
{ Enter AHandle in the descriptor table: its descriptor, or -1 when the
  table is full. }
function _WinFdAdd(AHandle: Pointer): Int32;
{ Take descriptor Fd out of the table: its handle, for the caller to close,
  or nil when Fd is not a table entry. }
function _WinFdRemove(Fd: Int32): Pointer;

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

const
  STD_INPUT_HANDLE = UInt32(-10);
  STD_OUTPUT_HANDLE = UInt32(-11);
  STD_ERROR_HANDLE = UInt32(-12);
  MEM_COMMIT = $1000;
  MEM_RESERVE = $2000;
  MEM_RELEASE = $8000;
  PAGE_READWRITE = $04;
  MAX_ATEXIT = 64;
  { The first descriptor the table hands out, and its size. }
  FIRST_TABLE_FD = 3;
  MAX_TABLE_FDS = 1024;

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
  { The descriptor table: slot I holds descriptor FIRST_TABLE_FD + I, nil
    when free.  GFdLock, an SRWLOCK, is all zero bits when unlocked, so the
    zeroed global needs no initialisation. }
  GFdHandles: array[0..MAX_TABLE_FDS - 1] of Pointer;
  GFdLock: Pointer;

function _WinHandleOfFd(Fd: Int32): Pointer;
begin
  case Fd of
    0: Result := GetStdHandle(STD_INPUT_HANDLE);
    1: Result := GetStdHandle(STD_OUTPUT_HANDLE);
    2: Result := GetStdHandle(STD_ERROR_HANDLE);
  else
    if (Fd >= FIRST_TABLE_FD) and (Fd < FIRST_TABLE_FD + MAX_TABLE_FDS) then
    begin
      AcquireSRWLockExclusive(@GFdLock);
      Result := GFdHandles[Fd - FIRST_TABLE_FD];
      ReleaseSRWLockExclusive(@GFdLock);
    end
    else
      Result := nil;
  end;
end;

function _WinFdAdd(AHandle: Pointer): Int32;
var
  I: Int;
begin
  Result := -1;
  AcquireSRWLockExclusive(@GFdLock);
  for I := 0 to MAX_TABLE_FDS - 1 do
    if GFdHandles[I] = nil then
    begin
      GFdHandles[I] := AHandle;
      Result := Int32(FIRST_TABLE_FD + I);
      Break;
    end;
  ReleaseSRWLockExclusive(@GFdLock);
end;

function _WinFdRemove(Fd: Int32): Pointer;
begin
  Result := nil;
  if (Fd < FIRST_TABLE_FD) or (Fd >= FIRST_TABLE_FD + MAX_TABLE_FDS) then
    Exit;
  AcquireSRWLockExclusive(@GFdLock);
  Result := GFdHandles[Fd - FIRST_TABLE_FD];
  GFdHandles[Fd - FIRST_TABLE_FD] := nil;
  ReleaseSRWLockExclusive(@GFdLock);
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
