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
    function O_RDONLY: Integer; override;
    function O_WRONLY: Integer; override;
    function O_RDWR:   Integer; override;
    function O_CREAT:  Integer; override;
    function O_TRUNC:  Integer; override;
    function O_APPEND: Integer; override;

    function S_IFMT:  Integer; override;
    function S_IFDIR: Integer; override;

    function SEEK_SET: Integer; override;
    function SEEK_CUR: Integer; override;
    function SEEK_END: Integer; override;

    function CLOCK_REALTIME: Integer; override;
    function WNOHANG:        Integer; override;

    function SC_NPROCESSORS_ONLN: Integer; override;

    function StatBufSize: Integer; override;
    function StatSize(Buf: Pointer):  Int64; override;
    function StatMtime(Buf: Pointer): Int64; override;
    function StatMode(Buf: Pointer):  Integer; override;
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
function _MapAnonFlag: Integer;

{ Flat park/wake primitives for the fiber scheduler (async.fibers): raw
  futex(2), issued as a raw syscall so the same unit serves both the libc
  and --static profiles.  _ParkWait blocks while the 32-bit word at AAddr
  equals AExpected, bounded by the RELATIVE timeout in ATs (a plain struct
  timespec — never nil; callers always bound the wait).  _ParkWake wakes up
  to ACount waiters on AAddr.  The FreeBSD twin maps these onto _umtx_op(2). }
procedure _ParkWait(AAddr: Pointer; AExpected: Integer; ATs: Pointer);
procedure _ParkWake(AAddr: Pointer; ACount: Integer);

{ The target's CLOCK_MONOTONIC clockid for clock_gettime: Linux 1.
  (FreeBSD is 4 — its 1 is CLOCK_VIRTUAL.) }
function _ClockMonotonicId: Integer;

{ Socket-layer OS constants (Net.Sockets / async.io) — the per-platform layer
  the Net.Sockets PORTING BOUNDARY note calls for.  Linux x86_64 values. }
function _SolSocket: Integer;      { SOL_SOCKET   = 1 }
function _SoReuseAddr: Integer;    { SO_REUSEADDR = 2 }
function _SoReusePort: Integer;    { SO_REUSEPORT = 15 }
function _SoError: Integer;        { SO_ERROR     = 4 }
function _MsgNoSignal: Integer;    { MSG_NOSIGNAL = $4000 }
function _ONonBlock: Integer;      { O_NONBLOCK   = $800 }
function _SockNonBlock: Integer;   { SOCK_NONBLOCK = $800 (accept4) }

{ Fill a 16-byte struct sockaddr_in at P for AF_INET.  APortN/AAddrN are
  ALREADY in network byte order.  Linux layout: sin_family (u16, = AF_INET),
  sin_port (u16), sin_addr (u32), sin_zero[8].  (FreeBSD splits the first
  u16 into sin_len + a u8 sin_family — hence the seam.) }
procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
{$ENDIF}

implementation

const
  { Linux x86_64 struct stat field offsets (bytes). }
  STAT_OFF_MODE  = 24;   { st_mode  (Integer) }
  STAT_OFF_SIZE  = 48;   { st_size  (Int64)   }
  STAT_OFF_MTIME = 88;   { st_mtim.tv_sec (Int64) }
  STAT_SIZE      = 144;  { sizeof(struct stat) }

function TPlatformLayoutLinuxX86_64.O_RDONLY: Integer; begin Result := 0;     end;
function TPlatformLayoutLinuxX86_64.O_WRONLY: Integer; begin Result := 1;     end;
function TPlatformLayoutLinuxX86_64.O_RDWR:   Integer; begin Result := 2;     end;
function TPlatformLayoutLinuxX86_64.O_CREAT:  Integer; begin Result := $40;   end;
function TPlatformLayoutLinuxX86_64.O_TRUNC:  Integer; begin Result := $200;  end;
function TPlatformLayoutLinuxX86_64.O_APPEND: Integer; begin Result := $400;  end;

function TPlatformLayoutLinuxX86_64.S_IFMT:  Integer; begin Result := $F000; end;
function TPlatformLayoutLinuxX86_64.S_IFDIR: Integer; begin Result := $4000; end;

function TPlatformLayoutLinuxX86_64.SEEK_SET: Integer; begin Result := 0; end;
function TPlatformLayoutLinuxX86_64.SEEK_CUR: Integer; begin Result := 1; end;
function TPlatformLayoutLinuxX86_64.SEEK_END: Integer; begin Result := 2; end;

function TPlatformLayoutLinuxX86_64.CLOCK_REALTIME: Integer; begin Result := 0; end;
function TPlatformLayoutLinuxX86_64.WNOHANG:        Integer; begin Result := 1; end;

{ glibc bits/confname.h. }
function TPlatformLayoutLinuxX86_64.SC_NPROCESSORS_ONLN: Integer; begin Result := 84; end;

function TPlatformLayoutLinuxX86_64.StatBufSize: Integer;
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

function TPlatformLayoutLinuxX86_64.StatMode(Buf: Pointer): Integer;
var
  P: ^Integer;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MODE);
  Result := P^;
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
function _MapAnonFlag: Integer;
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
function _park_futex(Uaddr: Pointer; Op, Val: Integer;
  Timeout: Pointer): Int64; assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $202, %rax          { SYS_futex }
    syscall
    ret
end;

procedure _ParkWait(AAddr: Pointer; AExpected: Integer; ATs: Pointer);
begin
  _park_futex(AAddr, FUTEX_WAIT_PRIVATE, AExpected, ATs);
end;

procedure _ParkWake(AAddr: Pointer; ACount: Integer);
begin
  _park_futex(AAddr, FUTEX_WAKE_PRIVATE, ACount, nil);
end;

function _ClockMonotonicId: Integer;
begin
  Result := 1;
end;

function _SolSocket: Integer;    begin Result := 1;    end;
function _SoReuseAddr: Integer;  begin Result := 2;    end;
function _SoReusePort: Integer;  begin Result := 15;   end;
function _SoError: Integer;      begin Result := 4;    end;
function _MsgNoSignal: Integer;  begin Result := $4000; end;
function _ONonBlock: Integer;    begin Result := $800; end;
function _SockNonBlock: Integer; begin Result := $800; end;

procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
var
  PB: ^Byte;
  PW: ^UInt16;
  PD: ^UInt32;
  I: Integer;
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
{$ENDIF}

initialization
{ Target-guarded like the FreeBSD twin: only the unit matching the build
  target may claim GPlatformLayout — the nil-guard in AssignLayout is no
  protection when a foreign layout unit's init happens to run first. }
{$IFDEF LINUX}
  AssignLayoutLinux();
{$ENDIF}

end.
