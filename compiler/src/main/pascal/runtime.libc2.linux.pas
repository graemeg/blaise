{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.libc2.linux;

// Tier 2 libc leaves that need real logic, not a raw syscall:
//   * the atexit registry + `exit` (runs handlers then exit_group)
//   * __cxa_atexit (register a handler)
//   * abort (raise SIGABRT, then exit_group 134)
//   * gmtime_r / localtime_r / timegm (freestanding civil-calendar math, UTC)
//   * mkstemp (random-named O_CREAT|O_EXCL file)
//   * system (fork + execve /bin/sh -c + wait4)
//
// Linked only in a --static (libc-free) build (docs/linux-syscall-migration.adoc).
// Built on runtime.syscall.linux's raw syscalls.

interface

uses
  runtime.syscall.linux;

{ __cxa_atexit(func, arg, dso_handle): register func(arg) to run at exit, LIFO.
  Returns 0 on success.  dso_handle is ignored (single program, no DSO unload). }
function __cxa_atexit(Func, Arg, DsoHandle: Pointer): Int32;

{ exit(code): run the registered handlers (LIFO), then exit_group(code).  This
  is the bare `exit` main's epilogue calls; it is a reserved word in Pascal, so
  the Pascal proc is _libc2_exit and the asm/Pascal body publishes `exit`. }
procedure _RunAtExitAndExit(Code: Int32);

{ abort(): raise SIGABRT to self; if the signal is caught/ignored, force-exit
  with status 134 (128 + SIGABRT). }
procedure abort;

{ struct tm split/join (UTC).  T points at a time_t (Int64 epoch seconds). }
function gmtime_r(T: Pointer; Tm: Pointer): Pointer;
function localtime_r(T: Pointer; Tm: Pointer): Pointer;
function timegm(Tm: Pointer): Int64;

{ mkstemp(template): template ends with "XXXXXX"; replace with random chars and
  open O_CREAT|O_EXCL|O_RDWR mode 0600.  Returns the fd or -1. }
function mkstemp(Template: PChar): Int;

{ system(cmd): fork, child execve "/bin/sh -c <cmd>", parent wait4; returns the
  child's raw wait status (the RTL extracts the exit code). }
function system(Cmd: PChar): Int;

implementation

type
  PInt64  = ^Int64;
  PInteger = ^Int32;

const
  SIGABRT  = 6;
  O_RDWR   = 2;
  O_CREAT  = $40;
  O_EXCL   = $80;
  MAX_ATEXIT = 64;

{ struct tm field byte offsets (Linux/SysV layout the RTL's TTm mirrors):
  Sec@0 Min@4 Hour@8 MDay@12 Mon@16 Year@20 WDay@24 YDay@28 IsDST@32 (all int). }
const
  TM_SEC=0; TM_MIN=4; TM_HOUR=8; TM_MDAY=12; TM_MON=16; TM_YEAR=20;
  TM_WDAY=24; TM_YDAY=28; TM_ISDST=32;

{ --- atexit registry --- }

var
  GAtExitFns:  array[0..MAX_ATEXIT - 1] of Pointer;
  GAtExitArgs: array[0..MAX_ATEXIT - 1] of Pointer;
  GAtExitCount: Int;

function __cxa_atexit(Func, Arg, DsoHandle: Pointer): Int32;
begin
  if GAtExitCount >= MAX_ATEXIT then
  begin
    Result := -1;
    Exit;
  end;
  GAtExitFns[GAtExitCount]  := Func;
  GAtExitArgs[GAtExitCount] := Arg;
  GAtExitCount := GAtExitCount + 1;
  Result := 0;
end;

{ Call a registered handler: void (*func)(void* arg).  The handler is invoked
  with its arg in %rdi (a 0-arg Pascal handler simply ignores it). }
procedure CallHandler(Func, Arg: Pointer); assembler; nostackframe;
asm
    movq %rsi, %rax           { Arg -> scratch; Func is in %rdi }
    movq %rdi, %r11           { Func }
    movq %rax, %rdi           { Arg -> first C arg }
    jmp  *%r11
end;

procedure _RunAtExitAndExit(Code: Int32);
var
  I: Int;
begin
  { LIFO. }
  I := GAtExitCount - 1;
  while I >= 0 do
  begin
    if GAtExitFns[I] <> nil then
      CallHandler(GAtExitFns[I], GAtExitArgs[I]);
    I := I - 1;
  end;
  _exit(Code);
end;

{ Publish the bare `exit` symbol as a tail-call into _RunAtExitAndExit (Code is
  already in %edi). }
procedure _libc2_exit(Code: Int32); assembler; nostackframe;
asm
.globl exit
exit:
    jmp _RunAtExitAndExit
end;

procedure abort;
begin
  kill(getpid(), SIGABRT);
  _exit(134);
end;

{ --- civil calendar (UTC), based on Howard Hinnant's days_from_civil --- }

{ Days since 1970-01-01 for a y/m/d (proleptic Gregorian). }
function DaysFromCivil(Y, M, D: Int64): Int64;
var
  Era, Yoe, Doy, Doe: Int64;
  YY: Int64;
begin
  if M <= 2 then YY := Y - 1 else YY := Y;
  if YY >= 0 then Era := YY div 400 else Era := (YY - 399) div 400;
  Yoe := YY - Era * 400;
  if M > 2 then Doy := (153 * (M - 3) + 2) div 5 + D - 1
           else Doy := (153 * (M + 9) + 2) div 5 + D - 1;
  Doe := Yoe * 365 + Yoe div 4 - Yoe div 100 + Doy;
  Result := Era * 146097 + Doe - 719468;
end;

{ Inverse: y/m/d from days-since-epoch. }
procedure CivilFromDays(Z: Int64; var Y, M, D: Int64);
var
  Era, Doe, Yoe, Doy, Mp: Int64;
begin
  Z := Z + 719468;
  if Z >= 0 then Era := Z div 146097 else Era := (Z - 146096) div 146097;
  Doe := Z - Era * 146097;
  Yoe := (Doe - Doe div 1460 + Doe div 36524 - Doe div 146096) div 365;
  Y := Yoe + Era * 400;
  Doy := Doe - (365 * Yoe + Yoe div 4 - Yoe div 100);
  Mp := (5 * Doy + 2) div 153;
  D := Doy - (153 * Mp + 2) div 5 + 1;
  if Mp < 10 then M := Mp + 3 else M := Mp - 9;
  if M <= 2 then Y := Y + 1;
end;

procedure FillTm(T: Int64; Tm: Pointer);
var
  Days, Secs, Y, M, D: Int64;
  P: PInteger;
begin
  Days := T div 86400;
  Secs := T - Days * 86400;
  if Secs < 0 then
  begin
    Secs := Secs + 86400;
    Days := Days - 1;
  end;
  CivilFromDays(Days, Y, M, D);

  P := PInteger(Pointer(PChar(Tm) + TM_SEC));   P^ := Int32(Secs mod 60);
  P := PInteger(Pointer(PChar(Tm) + TM_MIN));   P^ := Int32((Secs div 60) mod 60);
  P := PInteger(Pointer(PChar(Tm) + TM_HOUR));  P^ := Int32(Secs div 3600);
  P := PInteger(Pointer(PChar(Tm) + TM_MDAY));  P^ := Int32(D);
  P := PInteger(Pointer(PChar(Tm) + TM_MON));   P^ := Int32(M - 1);     { 0-based }
  P := PInteger(Pointer(PChar(Tm) + TM_YEAR));  P^ := Int32(Y - 1900);  { years since 1900 }
  { WDay: 1970-01-01 was a Thursday (4). }
  P := PInteger(Pointer(PChar(Tm) + TM_WDAY));
  P^ := Int32(((Days mod 7) + 4 + 7) mod 7);
  P := PInteger(Pointer(PChar(Tm) + TM_YDAY));
  P^ := Int32(Days - DaysFromCivil(Y, 1, 1));
  P := PInteger(Pointer(PChar(Tm) + TM_ISDST)); P^ := 0;
end;

function gmtime_r(T: Pointer; Tm: Pointer): Pointer;
begin
  FillTm(PInt64(T)^, Tm);
  Result := Tm;
end;

function localtime_r(T: Pointer; Tm: Pointer): Pointer;
begin
  { No timezone database in the freestanding RTL - treat local as UTC. }
  Result := gmtime_r(T, Tm);
end;

function timegm(Tm: Pointer): Int64;
var
  Y, M, D, Hh, Mm, Ss: Int64;
  P: PInteger;
begin
  P := PInteger(Pointer(PChar(Tm) + TM_SEC));   Ss := P^;
  P := PInteger(Pointer(PChar(Tm) + TM_MIN));   Mm := P^;
  P := PInteger(Pointer(PChar(Tm) + TM_HOUR));  Hh := P^;
  P := PInteger(Pointer(PChar(Tm) + TM_MDAY));  D  := P^;
  P := PInteger(Pointer(PChar(Tm) + TM_MON));   M  := P^ + 1;
  P := PInteger(Pointer(PChar(Tm) + TM_YEAR));  Y  := P^ + 1900;
  Result := DaysFromCivil(Y, M, D) * 86400 + Hh * 3600 + Mm * 60 + Ss;
end;

{ --- mkstemp --- }

function mkstemp(Template: PChar): Int;
const
  ALPHABET = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';
var
  Len, I, Tries, Got: Int;
  N: Int64;
  RandBuf: array[0..5] of Byte;
  Fd: Int;
begin
  Len := 0;
  while (Template[Len] and $FF) <> 0 do Len := Len + 1;
  if Len < 6 then Exit(-1);
  Tries := 0;
  while Tries < 256 do
  begin
    { Fill all 6 bytes; getrandom may short-read, so loop until satisfied rather
      than leave stale/zero bytes that would weaken the random suffix. }
    Got := 0;
    while Got < 6 do
    begin
      N := getrandom(@RandBuf[Got], 6 - Got, 0);
      if N <= 0 then Continue;   { EINTR / transient: retry }
      Got := Got + Int32(N);
    end;
    for I := 0 to 5 do
      Template[Len - 6 + I] := Ord(ALPHABET[(RandBuf[I] mod 62)]);
    Fd := open(Template, O_RDWR or O_CREAT or O_EXCL, 384);   { 0600 }
    if Fd >= 0 then Exit(Fd);
    Tries := Tries + 1;
  end;
  Result := -1;
end;

{ --- system --- }

function system(Cmd: PChar): Int;
var
  Pid, Status: Int;
  Argv: array[0..3] of Pointer;
  ShPath, DashC: array[0..15] of Byte;
begin
  { Build argv = /bin/sh, -c, cmd, NULL.  The /bin/sh path and -c flag are short
    literals copied into local byte buffers so they have stable addresses. }
  ShPath[0]:=Ord('/'); ShPath[1]:=Ord('b'); ShPath[2]:=Ord('i'); ShPath[3]:=Ord('n');
  ShPath[4]:=Ord('/'); ShPath[5]:=Ord('s'); ShPath[6]:=Ord('h'); ShPath[7]:=0;
  DashC[0]:=Ord('-'); DashC[1]:=Ord('c'); DashC[2]:=0;
  Argv[0] := @ShPath[0];
  Argv[1] := @DashC[0];
  Argv[2] := Pointer(Cmd);
  Argv[3] := nil;

  Pid := fork();
  if Pid = 0 then
  begin
    { Child: replace image; on failure exit 127 like the shell.  Forward the
      process environment so the spawned shell sees PATH/HOME/etc. }
    execve(PChar(@ShPath[0]), @Argv[0], environ);
    _exit(127);
  end;
  if Pid < 0 then Exit(-1);
  Status := 0;
  wait4(Pid, @Status, 0, nil);
  Result := Status;
end;

end.
