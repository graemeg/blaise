{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit runtime.thread.windows;
// The pthread_* names over Windows threads and slim reader/writer locks
// (docs/windows-x86_64-backend-design.adoc, "runtime.thread.windows").
//
// runtime.thread and runtime.weak bind these through `external 'pthread'`, so
// by design decision D6 their call sites use the C convention, and every
// definition here is declared cdecl: on Windows each gets a foreign entry
// that takes the Win64 arguments.  The PE linker ignores the 'pthread' import
// metadata for symbols the link defines, so no pthread DLL is imported.
//
// A thread's start routine is a Blaise routine, called the internal way.
// _BlaiseThreadAtExit registers a handler the calling thread runs when its
// start routine returns, while its threadvars are still readable; for the
// main thread the at-exit list (__cxa_atexit) does the same job.

interface

function pthread_create(Thread: Pointer; Attr: Pointer;
  StartRoutine: Pointer; Arg: Pointer): Int32; cdecl;
function pthread_join(Thread: Int64; RetVal: Pointer): Int32; cdecl;
{ Let the thread run on unjoined: its handle is closed now, and the system
  frees the thread when it ends. }
function pthread_detach(Thread: Int64): Int32; cdecl;
{ The mutex buffer is runtime.thread's 64-byte block; an SRWLOCK is its
  first pointer-sized word.  Not recursive, as a default pthread mutex. }
function pthread_mutex_init(Mutex: Pointer; Attr: Pointer): Int32; cdecl;
function pthread_mutex_lock(Mutex: Pointer): Int32; cdecl;
function pthread_mutex_unlock(Mutex: Pointer): Int32; cdecl;
function pthread_mutex_destroy(Mutex: Pointer): Int32; cdecl;

{ Register Fn(Arg) to run when the calling thread ends.  Returns 0, or -1
  when the thread's list is full. }
function _BlaiseThreadAtExit(Fn, Arg: Pointer): Int32;

implementation

function CreateThread(AAttributes: Pointer; AStackSize: UInt64;
  AStart: Pointer; AParam: Pointer; AFlags: UInt32;
  AThreadId: Pointer): Pointer; external 'kernel32' name 'CreateThread';
function WaitForSingleObject(AHandle: Pointer; AMilliseconds: UInt32): UInt32;
  external 'kernel32' name 'WaitForSingleObject';
function CloseHandle(AHandle: Pointer): Int32;
  external 'kernel32' name 'CloseHandle';
procedure InitializeSRWLock(ALock: Pointer);
  external 'kernel32' name 'InitializeSRWLock';
procedure AcquireSRWLockExclusive(ALock: Pointer);
  external 'kernel32' name 'AcquireSRWLockExclusive';
procedure ReleaseSRWLockExclusive(ALock: Pointer);
  external 'kernel32' name 'ReleaseSRWLockExclusive';

function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';

const
  INFINITE = $FFFFFFFF;
  MAX_THREAD_EXIT = 16;

type
  { What CreateThread hands the new thread: the start routine and its
    argument. }
  TThreadStart = record
    Start: Pointer;
    Arg: Pointer;
  end;
  PThreadStart = ^TThreadStart;
  PInt64 = ^Int64;
  PPointer = ^Pointer;

threadvar
  GExitFns: array[0..MAX_THREAD_EXIT - 1] of Pointer;
  GExitArgs: array[0..MAX_THREAD_EXIT - 1] of Pointer;
  GExitCount: Int;

{ Call Fn(Arg) the internal way and return its result. }
function CallRoutine(Fn, Arg: Pointer): Pointer; assembler; nostackframe;
asm
    movq %rdi, %r11
    movq %rsi, %rdi
    jmp  *%r11
end;

function _BlaiseThreadAtExit(Fn, Arg: Pointer): Int32;
var
  N: Int;
begin
  N := GExitCount;
  if N >= MAX_THREAD_EXIT then
    Exit(-1);
  GExitFns[N] := Fn;
  GExitArgs[N] := Arg;
  GExitCount := N + 1;
  Result := 0;
end;

{ The routine CreateThread starts: Windows calls it, so it is cdecl. }
function ThreadEntry(AParam: Pointer): UInt32; cdecl;
var
  P: PThreadStart;
  Start, Arg: Pointer;
  I: Int;
begin
  P := PThreadStart(AParam);
  Start := P^.Start;
  Arg := P^.Arg;
  _BlaiseFreeMem(P);
  CallRoutine(Start, Arg);
  { the thread's exit handlers, last registered first }
  I := GExitCount - 1;
  while I >= 0 do
  begin
    CallRoutine(GExitFns[I], GExitArgs[I]);
    I := I - 1;
  end;
  GExitCount := 0;
  Result := 0;
end;

function pthread_create(Thread: Pointer; Attr: Pointer;
  StartRoutine: Pointer; Arg: Pointer): Int32; cdecl;
var
  P: PThreadStart;
  H: Pointer;
begin
  P := PThreadStart(_BlaiseGetMem(SizeOf(TThreadStart)));
  if P = nil then
    Exit(12);                       { ENOMEM }
  P^.Start := StartRoutine;
  P^.Arg := Arg;
  H := CreateThread(nil, 0, Pointer(@ThreadEntry), P, 0, nil);
  if H = nil then
  begin
    _BlaiseFreeMem(P);
    Exit(11);                       { EAGAIN }
  end;
  PInt64(Thread)^ := Int64(H);
  Result := 0;
end;

function pthread_join(Thread: Int64; RetVal: Pointer): Int32; cdecl;
begin
  WaitForSingleObject(Pointer(Thread), INFINITE);
  CloseHandle(Pointer(Thread));
  if RetVal <> nil then
    PPointer(RetVal)^ := nil;
  Result := 0;
end;

function pthread_detach(Thread: Int64): Int32; cdecl;
begin
  if CloseHandle(Pointer(Thread)) <> 0 then
    Result := 0
  else
    Result := 3;                    { ESRCH }
end;

function pthread_mutex_init(Mutex: Pointer; Attr: Pointer): Int32; cdecl;
begin
  InitializeSRWLock(Mutex);
  Result := 0;
end;

function pthread_mutex_lock(Mutex: Pointer): Int32; cdecl;
begin
  AcquireSRWLockExclusive(Mutex);
  Result := 0;
end;

function pthread_mutex_unlock(Mutex: Pointer): Int32; cdecl;
begin
  ReleaseSRWLockExclusive(Mutex);
  Result := 0;
end;

function pthread_mutex_destroy(Mutex: Pointer): Int32; cdecl;
begin
  Result := 0;
end;

end.
