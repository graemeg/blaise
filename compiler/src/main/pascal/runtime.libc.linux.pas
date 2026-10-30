{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.libc.linux;

// libc-shaped leaves that are MORE than a raw syscall - they need logic the
// kernel does not provide: PATH/env lookup, the libc-style return shapes, etc.
// Built on the raw syscalls in runtime.syscall.linux.  Linked only in a
// --static (libc-free) build (docs/linux-syscall-migration.adoc).
//
// These DEFINE the bare POSIX names (getcwd, getenv,  ) that rtl.platform.posix
// imports via `external name`, so they resolve here instead of libc.so.6.

interface

uses
  runtime.syscall.linux;   { provides `environ`, captured by _start }

{ libc-shaped getcwd: returns Buf on success, nil on error (the raw syscall
  returns a length / -errno). }
function getcwd(Buf: PChar; Size: Int64): PChar;

{ getenv: linear scan of `environ` for "Name="   returns a pointer to the value
  (just past '='), or nil if not present. }
function getenv(Name: PChar): PChar;

{ time(2) wrapper matching libc's signature (the raw syscall already supports the
  optional out-param, so this just forwards). }
function time(T: Pointer): Int64;

{ waitpid via wait4 with a NULL rusage. }
function waitpid(Pid: Int; Status: Pointer; Options: Int): Int;

{ execvp: search $PATH for File when it has no '/', then execve.  Argv is the
  NULL-terminated argument vector; the current `environ` is passed as envp. }
function execvp(File_: PChar; Argv: Pointer): Int;

{ sysconf for the few names the RTL queries - currently only the online CPU
  count (_SC_NPROCESSORS_ONLN = 84), via sched_getaffinity + popcount. }
function sysconf(Name: Int): Int64;

implementation

type
  PPointer = ^Pointer;

const
  _SC_NPROCESSORS_ONLN = 84;

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
begin
  Result := sys_time(T);
end;

function waitpid(Pid: Int; Status: Pointer; Options: Int): Int;
begin
  Result := wait4(Pid, Status, Options, nil);
end;

function execvp(File_: PChar; Argv: Pointer): Int;
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

{ Population count of a 1024-bit affinity mask (128 bytes), counting set CPUs. }
function PopCountMask(Mask: PChar; NBytes: Int64): Int64;
var
  I, J, Cnt: Int64;
  B: Int;
begin
  Cnt := 0;
  I := 0;
  while I < NBytes do
  begin
    B := Mask[I] and $FF;
    J := 0;
    while J < 8 do
    begin
      if (B and (1 shl J)) <> 0 then Cnt := Cnt + 1;
      J := J + 1;
    end;
    I := I + 1;
  end;
  Result := Cnt;
end;

function sysconf(Name: Int): Int64;
var
  Mask: array[0..127] of Byte;   { 1024 CPUs worth of affinity bits }
  Rc: Int;
begin
  if Name = _SC_NPROCESSORS_ONLN then
  begin
    Rc := sched_getaffinity(0, 128, @Mask[0]);
    if Rc <= 0 then
      Result := 1                { fall back to single CPU on error }
    else
      Result := PopCountMask(PChar(@Mask[0]), Rc);
    if Result < 1 then Result := 1;
  end
  else
    Result := -1;
end;

end.
