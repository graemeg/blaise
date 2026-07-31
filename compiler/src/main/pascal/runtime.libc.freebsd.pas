{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.libc.freebsd;

// libc-shaped leaves that are MORE than a raw syscall - they need logic the
// kernel does not provide: env lookup, the libc-style return shapes, the
// hw.ncpu sysctl.  Built on the raw syscalls in runtime.syscall.freebsd.
// Linked only in a static (libc-free) FreeBSD build
// (docs/freebsd-x86_64-backend-design.adoc).  The FreeBSD sibling of
// runtime.libc.linux.
//
// These DEFINE the bare POSIX names (getcwd, getenv, time, waitpid, execvp,
// sysconf) that rtl.platform.posix / runtime.thread import via `external name`,
// so they resolve here instead of FreeBSD's libc.
//
// Deltas from the Linux sibling:
//   * time() has no SYS_time on FreeBSD; it reads CLOCK_REALTIME via
//     clock_gettime and returns tv_sec.
//   * sysconf(CPU count) uses sysctl(hw.ncpu) — FreeBSD has no
//     sched_getaffinity.
// getcwd / getenv / waitpid / execvp are structurally identical (the syscall
// leaf provides sys_getcwd / wait4 / execve / environ on both targets).

interface

uses
  runtime.syscall.freebsd;   { provides `environ`, captured by _start }

{ libc-shaped getcwd: returns Buf on success, nil on error (the raw syscall
  returns 0 / -errno). }
function getcwd(Buf: PChar; Size: Int64): PChar;

{ getenv: linear scan of `environ` for "Name="   returns a pointer to the value
  (just past '='), or nil if not present. }
function getenv(Name: PChar): PChar;

{ time(2): FreeBSD has no SYS_time — read CLOCK_REALTIME and return tv_sec.  If
  T is non-nil the same value is written there (libc's optional out-param). }
function time(T: Pointer): Int64;

{ waitpid via wait4 with a NULL rusage. }
function waitpid(Pid: Integer; Status: Pointer; Options: Integer): Integer;

{ execvp: execve the name with the current `environ` as envp.  No $PATH search
  yet (matches the Linux sibling — the RTL only execs explicit paths). }
function execvp(File_: PChar; Argv: Pointer): Integer;

{ sysconf for the few names the RTL queries - currently only the online CPU
  count (_SC_NPROCESSORS_ONLN, passed as 84 by runtime.thread on every target),
  via sysctl(hw.ncpu). }
function sysconf(Name: Integer): Int64;

{ setenv: insert or replace "Name=Value" in `environ`.  When the key exists a
  new entry string replaces the slot in place (Overwrite=0 leaves it alone);
  when it does not, a fresh NULL-terminated pointer array (old count + 2) is
  mmap-ed, the pointers copied, and `environ` repointed at it.  Entry strings
  and arrays are mmap-ed and never freed — setenv traffic is test-harness
  scale, not allocator scale.  Children see changes because execvp/execve pass
  the current `environ`. }
function setenv(Name, Value: PChar; Overwrite: Integer): Integer;

{ unsetenv: remove every "Name=..." entry by shifting the tail of the pointer
  array down one slot (the array — original stack envp or our mmap-ed copy —
  is writable either way). }
function unsetenv(Name: PChar): Integer;

{ pthread_self: the calling thread's opaque id.  Freestanding FreeBSD has no
  pthread library; the kernel thread id from thr_self(2) serves the same
  purpose (tests use it only to tell threads apart). }
function pthread_self: Int64;

implementation

type
  PPointer = ^Pointer;
  PInt64   = ^Int64;
  PByte    = ^Byte;

const
  { mmap protection/flags for the tiny env allocations below.  MAP_ANON is the
    FreeBSD value ($1000) — this unit is the FreeBSD leaf, selected at link
    time, so the constant lives here (never IFDEF-ed). }
  PROT_READ    = 1;
  PROT_WRITE   = 2;
  MAP_PRIVATE  = 2;
  MAP_ANON_OS  = $1000;
  PAGE_SIZE    = 4096;

  { The token runtime.thread passes for the CPU-count query.  It is an internal
    RTL contract value (runtime.thread hardcodes 84 on every target), NOT
    FreeBSD's libc _SC_NPROCESSORS_ONLN (58) — we never reach FreeBSD's libc. }
  _SC_NPROCESSORS_ONLN = 84;
  CLOCK_REALTIME       = 0;
  { sysctl MIB for hw.ncpu (FreeBSD sys/sysctl.h): CTL_HW=6, HW_NCPU=3. }
  CTL_HW   = 6;
  HW_NCPU  = 3;

{ --- small freestanding string helpers (no dependency on runtime.str) --- }

function CStrLen(S: PChar): Int64;
var I: Int64;
begin
  I := 0;
  while (S[I] and $FF) <> 0 do I := I + 1;
  Result := I;
end;

{ Compare the "KEY=" prefix of an environ entry against Name (length NLen).
  Returns True when Entry starts with Name immediately followed by '='. }
function EnvKeyMatches(Entry, Name: PChar; NLen: Int64): Boolean;
var I: Int64;
begin
  I := 0;
  while I < NLen do
  begin
    if (Entry[I] and $FF) <> (Name[I] and $FF) then Exit(False);
    if (Entry[I] and $FF) = 0 then Exit(False);
    I := I + 1;
  end;
  Result := (Entry[NLen] and $FF) = Ord('=');
end;

function getcwd(Buf: PChar; Size: Int64): PChar;
var Rc: Int64;
begin
  Rc := sys_getcwd(Buf, Size);
  if Rc < 0 then
    Result := nil
  else
    Result := Buf;
end;

function getenv(Name: PChar): PChar;
var
  Entry: PChar;
  NLen, Off: Int64;
begin
  Result := nil;
  if environ = nil then Exit;
  NLen := CStrLen(Name);
  { environ is a NULL-terminated array of PChar; read the I-th slot as a
    Pointer at environ + I*8 (PPointer deref, the RTL idiom - no [] on a typed
    pointer). }
  Off := 0;
  Entry := PChar(PPointer(Pointer(PChar(environ) + Off))^);
  while Entry <> nil do
  begin
    if EnvKeyMatches(Entry, Name, NLen) then
    begin
      Result := PChar(Pointer(PChar(Entry) + NLen + 1));  { just past '=' }
      Exit;
    end;
    Off := Off + 8;
    Entry := PChar(PPointer(Pointer(PChar(environ) + Off))^);
  end;
end;

function time(T: Pointer): Int64;
var
  Ts: array[0..1] of Int64;   { struct timespec: tv_sec (Int64), tv_nsec (long) }
  Rc: Integer;
  Out_: PInt64;
begin
  Rc := clock_gettime(CLOCK_REALTIME, @Ts[0]);
  if Rc <> 0 then
    Result := -1
  else
    Result := Ts[0];          { tv_sec }
  if (T <> nil) and (Result >= 0) then
  begin
    Out_ := PInt64(T);
    Out_^ := Result;          { libc's optional out-param: *T = tv_sec }
  end;
end;

function waitpid(Pid: Integer; Status: Pointer; Options: Integer): Integer;
begin
  Result := wait4(Pid, Status, Options, nil);
end;

function execvp(File_: PChar; Argv: Pointer): Integer;
var
  PathEnv: PChar;
  PathKey: array[0..4] of Byte;
  Buf: array[0..4095] of Byte;
  NLen, DirStart, DirLen, I, J: Int64;
begin
  { Names containing '/' resolve relative to the CWD only (POSIX semantics):
    execve directly, no $PATH scan. }
  NLen := CStrLen(File_);
  I := 0;
  while I < NLen do
  begin
    if (File_[I] and $FF) = Ord('/') then
      Exit(execve(File_, Argv, environ));
    I := I + 1;
  end;

  { Bare name: try each colon-separated $PATH prefix in order.  execve only
    returns on failure, so falling through means "try the next directory".
    The 'PATH' key is copied into a local byte buffer for a stable address
    (freestanding: no managed-string literals here). }
  PathKey[0]:=Ord('P'); PathKey[1]:=Ord('A'); PathKey[2]:=Ord('T'); PathKey[3]:=Ord('H'); PathKey[4]:=0;
  PathEnv := getenv(PChar(@PathKey[0]));
  if PathEnv = nil then
    Exit(execve(File_, Argv, environ));

  DirStart := 0;
  while True do
  begin
    DirLen := 0;
    while ((PathEnv[DirStart + DirLen] and $FF) <> 0) and
          ((PathEnv[DirStart + DirLen] and $FF) <> Ord(':')) do
      DirLen := DirLen + 1;
    if DirLen + 1 + NLen + 1 <= 4096 then   { skip entries that cannot fit }
    begin
      J := 0;
      if DirLen = 0 then
      begin
        { An empty $PATH entry means the CWD: use "./name". }
        Buf[0] := Ord('.');
        J := 1;
      end
      else
      begin
        I := 0;
        while I < DirLen do
        begin
          Buf[J] := PathEnv[DirStart + I] and $FF;
          J := J + 1;
          I := I + 1;
        end;
      end;
      Buf[J] := Ord('/');
      J := J + 1;
      I := 0;
      while I < NLen do
      begin
        Buf[J] := File_[I] and $FF;
        J := J + 1;
        I := I + 1;
      end;
      Buf[J] := 0;
      execve(PChar(@Buf[0]), Argv, environ);
    end;
    if (PathEnv[DirStart + DirLen] and $FF) = 0 then Break;
    DirStart := DirStart + DirLen + 1;
  end;
  Result := -1;
end;

{ --- env mutation helpers (setenv/unsetenv) --- }

{ Page-rounded anonymous mmap; nil on failure.  Mirrors runtime.mem's
  MmapAlloc but stays self-contained — this unit must not depend on the
  allocator (it links into the earliest freestanding layer). }
function EnvAlloc(Size: Int64): Pointer;
begin
  Size := (Size + Int64(PAGE_SIZE - 1)) and Int64($FFFFFFFFFFFFF000);
  Result := mmap(nil, Size, PROT_READ or PROT_WRITE,
                 MAP_PRIVATE or MAP_ANON_OS, -1, 0);
  if (Result = nil) or (PtrUInt(Result) = PtrUInt(Int64(-1))) then
    Result := nil;
end;

{ Slot I of the environ pointer array (the RTL idiom: no [] on typed ptrs). }
function EnvSlot(I: Int64): PPointer;
begin
  Result := PPointer(Pointer(PChar(environ) + I * 8));
end;

{ Number of entries before the NULL terminator (0 when environ is nil). }
function EnvCount: Int64;
begin
  Result := 0;
  if environ = nil then Exit;
  while EnvSlot(Result)^ <> nil do Result := Result + 1;
end;

{ Index of the entry whose key is Name (length NLen), or -1. }
function EnvFind(Name: PChar; NLen: Int64): Int64;
var I: Int64;
begin
  Result := -1;
  if environ = nil then Exit;
  I := 0;
  while EnvSlot(I)^ <> nil do
  begin
    if EnvKeyMatches(PChar(EnvSlot(I)^), Name, NLen) then Exit(I);
    I := I + 1;
  end;
end;

function setenv(Name, Value: PChar; Overwrite: Integer): Integer;
var
  NLen, VLen, Idx, Cnt, I: Int64;
  Entry: PChar;
  NewArr: Pointer;
  B: PByte;
  S: PPointer;
begin
  Result := -1;
  if (Name = nil) or (Value = nil) then Exit;
  NLen := CStrLen(Name);
  if NLen = 0 then Exit;
  { A '=' inside the key is invalid (POSIX EINVAL). }
  I := 0;
  while I < NLen do
  begin
    if (Name[I] and $FF) = Ord('=') then Exit;
    I := I + 1;
  end;

  Idx := EnvFind(Name, NLen);
  if (Idx >= 0) and (Overwrite = 0) then Exit(0);

  { Build the "Name=Value" entry string. }
  VLen := CStrLen(Value);
  Entry := PChar(EnvAlloc(NLen + 1 + VLen + 1));
  if Entry = nil then Exit;
  I := 0;
  while I < NLen do
  begin
    B := PByte(Pointer(PChar(Entry) + I));
    B^ := Name[I] and $FF;
    I := I + 1;
  end;
  B := PByte(Pointer(PChar(Entry) + NLen));
  B^ := Ord('=');
  I := 0;
  while I < VLen do
  begin
    B := PByte(Pointer(PChar(Entry) + NLen + 1 + I));
    B^ := Value[I] and $FF;
    I := I + 1;
  end;
  B := PByte(Pointer(PChar(Entry) + NLen + 1 + VLen));
  B^ := 0;

  if Idx >= 0 then
  begin
    S := EnvSlot(Idx);                   { replace in place }
    S^ := Pointer(Entry);
  end
  else
  begin
    { Append: fresh array with room for the new entry + NULL terminator. }
    Cnt := EnvCount();
    NewArr := EnvAlloc((Cnt + 2) * 8);
    if NewArr = nil then Exit;
    I := 0;
    while I < Cnt do
    begin
      S := PPointer(Pointer(PChar(NewArr) + I * 8));
      S^ := EnvSlot(I)^;
      I := I + 1;
    end;
    S := PPointer(Pointer(PChar(NewArr) + Cnt * 8));
    S^ := Pointer(Entry);
    S := PPointer(Pointer(PChar(NewArr) + (Cnt + 1) * 8));
    S^ := nil;
    environ := NewArr;
  end;
  Result := 0;
end;

function unsetenv(Name: PChar): Integer;
var
  NLen, I, J: Int64;
  S: PPointer;
begin
  Result := -1;
  if Name = nil then Exit;
  NLen := CStrLen(Name);
  if NLen = 0 then Exit;
  Result := 0;
  if environ = nil then Exit;
  I := 0;
  while EnvSlot(I)^ <> nil do
  begin
    if EnvKeyMatches(PChar(EnvSlot(I)^), Name, NLen) then
    begin
      { Shift the tail (including the NULL) down one slot; re-test index I. }
      J := I;
      repeat
        S := EnvSlot(J);
        S^ := EnvSlot(J + 1)^;
        J := J + 1;
      until EnvSlot(J - 1)^ = nil;
    end
    else
      I := I + 1;
  end;
end;

function sysconf(Name: Integer): Int64;
var
  Mib: array[0..1] of Integer;   { the two-element MIB: CTL_HW, HW_NCPU }
  NCpu: Integer;
  OldLen: Int64;                 { size_t }
  Rc: Integer;
begin
  if Name = _SC_NPROCESSORS_ONLN then
  begin
    Mib[0] := CTL_HW;
    Mib[1] := HW_NCPU;
    NCpu := 0;
    OldLen := SizeOf(NCpu);      { 4 }
    Rc := sysctl(@Mib[0], 2, @NCpu, @OldLen, nil, 0);
    if (Rc <> 0) or (NCpu < 1) then
      Result := 1                { fall back to single CPU on error }
    else
      Result := NCpu;
  end
  else
    Result := -1;
end;


function pthread_self: Int64;
var
  Id: Int64;
begin
  Id := 0;
  thr_self(@Id);
  Result := Id;
end;

end.
