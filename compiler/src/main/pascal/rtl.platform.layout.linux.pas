{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit rtl.platform.layout.linux;

// Linux x86_64 struct layouts and OS constants — the concrete TPlatformLayout
// adapter for Linux (docs/native-target-architecture.adoc, Step 0b).
//
// These are the values that previously lived as `const` declarations and the
// TStatBuf record inside rtl.platform.posix.pas.  Moving them behind the
// TPlatformLayout port keeps the POSIX method bodies (which are shared with
// FreeBSD) free of any Linux-specific layout assumption; the FreeBSD adapter
// supplies its own offsets and flag values without conditional compilation.
//
// struct stat offsets below match the Linux x86_64 `struct stat`
// (sys/stat.h): st_mode at byte 24, st_size at byte 48, st_mtime at byte 88.
// The buffer is sized at 144 bytes (sizeof(struct stat) on Linux x86_64).

interface

uses
  rtl.platform;

type
  TPlatformLayoutLinuxX86_64 = class(TPlatformLayout)
  public
    function O_RDONLY: Int32; override;
    function O_WRONLY: Int32; override;
    function O_RDWR:   Int32; override;
    function O_CREAT:  Int32; override;
    function O_TRUNC:  Int32; override;
    function O_APPEND: Int32; override;

    function S_IFMT:  Int32; override;
    function S_IFDIR: Int32; override;
    function S_IFREG: Int32; override;
    function S_IFLNK: Int32; override;

    function SEEK_SET: Int32; override;
    function SEEK_CUR: Int32; override;
    function SEEK_END: Int32; override;

    function CLOCK_REALTIME: Int32; override;
    function WNOHANG:        Int32; override;

    function SC_NPROCESSORS_ONLN: Int32; override;

    function StatBufSize: Int32; override;
    function StatSize(Buf: Pointer):  Int64; override;
    function StatMtime(Buf: Pointer): Int64; override;
    function StatMode(Buf: Pointer):  Int32; override;

    function DirentRecLen(Ent: Pointer): Int32; override;
    function DirentName(Ent: Pointer): Pointer; override;
  end;

{ Flat function for runtime.mem (imported there via `external name`): returns
  the target's MAP_ANONYMOUS value.  Called before GPlatformLayout is
  initialised, so it cannot be a layout method.  Linux MAP_ANONYMOUS = $20.
  Guarded by the target define: link-level flat functions exist in BOTH layout
  units under the SAME global symbol name, and a host test build may link the
  foreign layout unit alongside this one (cp.test.platformlayout.freebsd) — an
  unguarded pair collides at link time and the loose test object wins over the
  archived host copy, handing the allocator the wrong OS's value (every
  fresh-arena mmap then fails EBADF).  The guard keeps the class API
  IFDEF-free (the rtl.platform doctrine); only the link-level leaf is
  conditional. }
{$IFDEF LINUX}
function _MapAnonFlag: Int32;

{ Flat park/wake primitives for the fiber scheduler (async.fibers): raw
  futex(2), issued as a raw syscall so the same unit serves both the libc
  and --static profiles.  _ParkWait blocks while the 32-bit word at AAddr
  equals AExpected, bounded by the RELATIVE timeout in ATs (a plain struct
  timespec — never nil; callers always bound the wait).  _ParkWake wakes up
  to ACount waiters on AAddr.  The FreeBSD twin maps these onto _umtx_op(2). }
procedure _ParkWait(AAddr: Pointer; AExpected: Int32; ATs: Pointer);
procedure _ParkWake(AAddr: Pointer; ACount: Int32);

{ The target's CLOCK_MONOTONIC clockid for clock_gettime: Linux 1.
  (FreeBSD is 4 — its 1 is CLOCK_VIRTUAL.) }
function _ClockMonotonicId: Int32;

{ Socket-layer OS constants (Net.Sockets / async.io) — the per-platform layer
  the Net.Sockets PORTING BOUNDARY note calls for.  Linux x86_64 values. }
function _SolSocket: Int32;      { SOL_SOCKET   = 1 }
function _SoReuseAddr: Int32;    { SO_REUSEADDR = 2 }
function _SoReusePort: Int32;    { SO_REUSEPORT = 15 }
function _SoError: Int32;        { SO_ERROR     = 4 }
function _MsgNoSignal: Int32;    { MSG_NOSIGNAL = $4000 }
function _ONonBlock: Int32;      { O_NONBLOCK   = $800 }
function _SockNonBlock: Int32;   { SOCK_NONBLOCK = $800 (accept4) }
function _SoNoSigPipe: Int32;    { none — MSG_NOSIGNAL covers it — 0 }

{ Fill a 16-byte struct sockaddr_in at P for AF_INET.  APortN/AAddrN are
  ALREADY in network byte order.  Linux layout: sin_family (u16, = AF_INET),
  sin_port (u16), sin_addr (u32), sin_zero[8].  (FreeBSD splits the first
  u16 into sin_len + a u8 sin_family — hence the seam.) }
procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);

{ Flat function for runtime.mem: register Fn(Arg) to run when the CALLING
  thread exits, while its threadvars are still readable.  glibc's
  __cxa_thread_atexit_impl under a libc link; the --static build supplies
  its own (runtime.thread.static.linux), run by the clone trampoline. }
function _BlaiseThreadAtExit(Fn, Arg: Pointer): Int32;
{$ENDIF}

implementation

const
  { Linux x86_64 struct stat field offsets (bytes). }
  STAT_OFF_MODE  = 24;   { st_mode  (Integer) }
  STAT_OFF_SIZE  = 48;   { st_size  (Int64)   }
  STAT_OFF_MTIME = 88;   { st_mtim.tv_sec (Int64) }
  STAT_SIZE      = 144;  { sizeof(struct stat) }

  { Linux x86_64 struct linux_dirent64 (getdents64):
      d_ino (8) d_off (8) d_reclen (u16 @16) d_type (u8 @18) d_name (@19). }
  DIRENT_OFF_RECLEN = 16;
  DIRENT_OFF_NAME   = 19;

function TPlatformLayoutLinuxX86_64.O_RDONLY: Int32; begin Result := 0;     end;
function TPlatformLayoutLinuxX86_64.O_WRONLY: Int32; begin Result := 1;     end;
function TPlatformLayoutLinuxX86_64.O_RDWR:   Int32; begin Result := 2;     end;
function TPlatformLayoutLinuxX86_64.O_CREAT:  Int32; begin Result := $40;   end;
function TPlatformLayoutLinuxX86_64.O_TRUNC:  Int32; begin Result := $200;  end;
function TPlatformLayoutLinuxX86_64.O_APPEND: Int32; begin Result := $400;  end;

function TPlatformLayoutLinuxX86_64.S_IFMT:  Int32; begin Result := $F000; end;
function TPlatformLayoutLinuxX86_64.S_IFDIR: Int32; begin Result := $4000; end;
function TPlatformLayoutLinuxX86_64.S_IFREG: Int32; begin Result := $8000; end;
function TPlatformLayoutLinuxX86_64.S_IFLNK: Int32; begin Result := $A000; end;

function TPlatformLayoutLinuxX86_64.SEEK_SET: Int32; begin Result := 0; end;
function TPlatformLayoutLinuxX86_64.SEEK_CUR: Int32; begin Result := 1; end;
function TPlatformLayoutLinuxX86_64.SEEK_END: Int32; begin Result := 2; end;

function TPlatformLayoutLinuxX86_64.CLOCK_REALTIME: Int32; begin Result := 0; end;
function TPlatformLayoutLinuxX86_64.WNOHANG:        Int32; begin Result := 1; end;

{ glibc bits/confname.h. }
function TPlatformLayoutLinuxX86_64.SC_NPROCESSORS_ONLN: Int32; begin Result := 84; end;

function TPlatformLayoutLinuxX86_64.StatBufSize: Int32;
begin
  Result := STAT_SIZE;
end;

function TPlatformLayoutLinuxX86_64.StatSize(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_SIZE);
  Result := P^;
end;

function TPlatformLayoutLinuxX86_64.StatMtime(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MTIME);
  Result := P^;
end;

function TPlatformLayoutLinuxX86_64.StatMode(Buf: Pointer): Int32;
var
  P: ^Int32;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MODE);
  Result := P^;
end;

function TPlatformLayoutLinuxX86_64.DirentRecLen(Ent: Pointer): Int32;
var
  P: ^UInt16;
begin
  { d_reclen is an unsigned 16-bit field — read it as a Word so a record
    longer than 32767 bytes (not reachable in practice, but free to be
    correct about) cannot come back negative. }
  P := Pointer(PChar(Ent) + DIRENT_OFF_RECLEN);
  Result := P^;
end;

function TPlatformLayoutLinuxX86_64.DirentName(Ent: Pointer): Pointer;
begin
  Result := Pointer(PChar(Ent) + DIRENT_OFF_NAME);
end;

{ Assign GPlatformLayout to this target's layout, once.  Called both from this
  unit's initialization (rtl.platform.layout.linux_init, which main invokes
  by-name for a Linux --target) and from the weak _BlaisePlatformInit trampoline
  below. }
procedure AssignLayoutLinux;
begin
  if GPlatformLayout = nil then
    GPlatformLayout := TPlatformLayoutLinuxX86_64.Create();
end;

{ Bootstrap fallback: a binary built by a codegen that does not yet emit main's
  direct, strong, by-name call to rtl.platform.layout.<os>_init reaches the
  layout through _SetArgs -> _BlaisePlatformInit instead.  A tiny asm
  trampoline that tail-calls AssignLayout.  Kept WEAK, but ALSO target-guarded
  like the flat functions below: first-seen-weak depends on object link order,
  and a loose test-unit object (a test importing a foreign layout) precedes
  the archived host copy — the guard, not the weakness, is what guarantees
  exactly one trampoline per link. }
{$IFDEF LINUX}
procedure _BlaisePlatformInit; assembler; nostackframe;
asm
    .weak _BlaisePlatformInit
    jmp AssignLayoutLinux
end;
{$ENDIF}

{$IFDEF LINUX}
function _MapAnonFlag: Int32;
begin
  Result := $20;
end;

const
  FUTEX_WAIT_PRIVATE = 128;   { FUTEX_WAIT | FUTEX_PRIVATE_FLAG }
  FUTEX_WAKE_PRIVATE = 129;   { FUTEX_WAKE | FUTEX_PRIVATE_FLAG }

{ futex(uaddr, op, val, timeout) — SYS 202; arg4 (%rcx) -> %r10.  Same shape
  as the runtime.syscall.linux leaf, duplicated here because that unit is
  only linked under --static and these primitives must exist on both
  profiles.  uaddr2/val3 are ignored by WAIT/WAKE. }
function _park_futex(Uaddr: Pointer; Op, Val: Int32;
  Timeout: Pointer): Int64; assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $202, %rax          { SYS_futex }
    syscall
    ret
end;

procedure _ParkWait(AAddr: Pointer; AExpected: Int32; ATs: Pointer);
begin
  _park_futex(AAddr, FUTEX_WAIT_PRIVATE, AExpected, ATs);
end;

procedure _ParkWake(AAddr: Pointer; ACount: Int32);
begin
  _park_futex(AAddr, FUTEX_WAKE_PRIVATE, ACount, nil);
end;

function _ClockMonotonicId: Int32;
begin
  Result := 1;
end;

function _SolSocket: Int32;    begin Result := 1;    end;
function _SoReuseAddr: Int32;  begin Result := 2;    end;
function _SoReusePort: Int32;  begin Result := 15;   end;
function _SoError: Int32;      begin Result := 4;    end;
function _MsgNoSignal: Int32;  begin Result := $4000; end;
function _ONonBlock: Int32;    begin Result := $800; end;
function _SockNonBlock: Int32; begin Result := $800; end;
function _SoNoSigPipe: Int32;  begin Result := 0;    end;

procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
var
  PB: ^Byte;
  PW: ^UInt16;
  PD: ^UInt32;
  I: Int;
begin
  PW := P;
  PW^ := 2;                                { sin_family = AF_INET }
  PW := Pointer(PChar(P) + 2);
  PW^ := APortN;                           { sin_port (network order) }
  PD := Pointer(PChar(P) + 4);
  PD^ := AAddrN;                           { sin_addr (network order) }
  for I := 8 to 15 do
  begin
    PB := Pointer(PChar(P) + I);
    PB^ := 0;                              { sin_zero }
  end;
end;

function cxa_thread_atexit_impl(Fn, Arg, Dso: Pointer): Int32;
  external name '__cxa_thread_atexit_impl';

function _BlaiseThreadAtExit(Fn, Arg: Pointer): Int32;
begin
  { The third argument names the module the callback lives in (C passes
    &__dso_handle, which has no Blaise equivalent); any address inside it
    serves, so pass the callback's own.  It must not be nil: glibc keeps a
    one-entry module cache that starts out nil, so a nil argument skipped the
    lookup and the registration dereferenced a nil link map (every dynamic
    program segfaulted on its first allocation). }
  Result := cxa_thread_atexit_impl(Fn, Arg, Fn);
end;
{$ENDIF}

initialization
{ Target-guarded like the FreeBSD twin: only the unit matching the build
  target may claim GPlatformLayout — the nil-guard in AssignLayout is no
  protection when a foreign layout unit's init happens to run first. }
{$IFDEF LINUX}
  AssignLayoutLinux();
{$ENDIF}

end.
