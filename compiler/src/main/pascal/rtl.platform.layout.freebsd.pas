{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit rtl.platform.layout.freebsd;

// FreeBSD x86_64 struct layouts and OS constants — the concrete TPlatformLayout
// adapter for FreeBSD (docs/native-target-architecture.adoc, Step 0b;
// docs/freebsd-x86_64-backend-design.adoc, Step 2).
//
// This is the FreeBSD sibling of rtl.platform.layout.linux.  The POSIX method
// bodies in rtl.platform.posix are shared between Linux and FreeBSD; the only
// per-target divergence is the struct stat layout and a handful of OS constant
// values, both of which live here.  The class API uses no conditional
// compilation: the FreeBSD RTL archive composes this unit in place of the
// Linux one.  Link-level FLAT functions (same global symbol name in every
// layout unit, imported elsewhere via `external name`) are the one exception —
// they are guarded by the target define so a host build that imports this unit
// for its class API (cp.test.platformlayout.freebsd) emits no colliding
// symbols.
//
// Layout pinned to FreeBSD 14.x amd64 (sys/sys/stat.h).  It is identical on
// FreeBSD 13.x: the ino_t/dev_t widening that changed struct stat landed in
// FreeBSD 12 and has been stable since, so 13.x and 14.x share these offsets.
//
// struct stat offsets (FreeBSD amd64): st_mode at byte 24, st_size at byte 112,
// st_mtim.tv_sec at byte 64.  The buffer is sized at 224 bytes
// (sizeof(struct stat)).  These differ from Linux (48/88/144) — reusing the
// Linux offsets here would read garbage file sizes and dates, the single most
// error-prone item in the FreeBSD port.
//
// The O_CREAT / O_TRUNC / O_APPEND flag bits also differ from Linux; the rest
// (S_*, SEEK_*, CLOCK_REALTIME, WNOHANG) happen to share Linux's values.

interface

uses
  rtl.platform;

type
  TPlatformLayoutFreeBSDX86_64 = class(TPlatformLayout)
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
  initialised, so it cannot be a layout method.  FreeBSD MAP_ANON = $1000.
  Guarded by the target define — see the twin in rtl.platform.layout.linux for
  the full rationale: a host (Linux) test build links this unit for its class
  API (cp.test.platformlayout.freebsd), and an unguarded flat function here
  would collide with — and win over — the archived Linux copy, handing the
  Linux allocator FreeBSD's MAP_ANON. }
{$IFDEF FREEBSD}
function _MapAnonFlag: Integer;

{ Flat park/wake primitives for the fiber scheduler (async.fibers).  The
  FreeBSD futex analogue is _umtx_op(2); issued as a raw syscall so the same
  unit serves both the libc and --static profiles.  _ParkWait blocks while
  the 32-bit word at AAddr equals AExpected, bounded by the RELATIVE timeout
  in ATs (a plain struct timespec — never nil; callers always bound the
  wait).  _ParkWake wakes up to ACount waiters on AAddr. }
procedure _ParkWait(AAddr: Pointer; AExpected: Integer; ATs: Pointer);
procedure _ParkWake(AAddr: Pointer; ACount: Integer);

{ The target's CLOCK_MONOTONIC clockid for clock_gettime: FreeBSD 4.
  (Linux is 1; FreeBSD's 1 is CLOCK_VIRTUAL — using it would give process
  CPU time, silently breaking the fiber timer heap.) }
function _ClockMonotonicId: Integer;

{ Socket-layer OS constants (Net.Sockets / async.io) — the per-platform layer
  the Net.Sockets PORTING BOUNDARY note calls for.  FreeBSD values from
  sys/socket.h / sys/fcntl.h. }
function _SolSocket: Integer;      { SOL_SOCKET   = $FFFF }
function _SoReuseAddr: Integer;    { SO_REUSEADDR = $0004 }
function _SoReusePort: Integer;    { SO_REUSEPORT = $0200 }
function _SoError: Integer;        { SO_ERROR     = $1007 }
function _MsgNoSignal: Integer;    { MSG_NOSIGNAL = $20000 }
function _ONonBlock: Integer;      { O_NONBLOCK   = $0004 }
function _SockNonBlock: Integer;   { SOCK_NONBLOCK = $20000000 (accept4) }

{ Fill a 16-byte struct sockaddr_in at P for AF_INET.  APortN/AAddrN are
  ALREADY in network byte order.  FreeBSD layout: sin_len (u8, = 16),
  sin_family (u8, = AF_INET), sin_port (u16), sin_addr (u32), sin_zero[8].
  (Linux has no sin_len; its sin_family is a u16 — hence the seam.) }
procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
{$ENDIF}

implementation

const
  { FreeBSD 14.x amd64 struct stat field offsets (bytes). }
  STAT_OFF_MODE  = 24;   { st_mode  (mode_t, u16) }
  STAT_OFF_MTIME = 64;   { st_mtim.tv_sec (Int64) }
  STAT_OFF_SIZE  = 112;  { st_size  (off_t, Int64) }
  STAT_SIZE      = 224;  { sizeof(struct stat) }

function TPlatformLayoutFreeBSDX86_64.O_RDONLY: Integer; begin Result := 0;      end;
function TPlatformLayoutFreeBSDX86_64.O_WRONLY: Integer; begin Result := 1;      end;
function TPlatformLayoutFreeBSDX86_64.O_RDWR:   Integer; begin Result := 2;      end;
function TPlatformLayoutFreeBSDX86_64.O_CREAT:  Integer; begin Result := $0200;  end;
function TPlatformLayoutFreeBSDX86_64.O_TRUNC:  Integer; begin Result := $0400;  end;
function TPlatformLayoutFreeBSDX86_64.O_APPEND: Integer; begin Result := $0008;  end;

function TPlatformLayoutFreeBSDX86_64.S_IFMT:  Integer; begin Result := $F000; end;
function TPlatformLayoutFreeBSDX86_64.S_IFDIR: Integer; begin Result := $4000; end;

function TPlatformLayoutFreeBSDX86_64.SEEK_SET: Integer; begin Result := 0; end;
function TPlatformLayoutFreeBSDX86_64.SEEK_CUR: Integer; begin Result := 1; end;
function TPlatformLayoutFreeBSDX86_64.SEEK_END: Integer; begin Result := 2; end;

function TPlatformLayoutFreeBSDX86_64.CLOCK_REALTIME: Integer; begin Result := 0; end;
function TPlatformLayoutFreeBSDX86_64.WNOHANG:        Integer; begin Result := 1; end;

{ FreeBSD sys/unistd.h.  Not glibc's 84 — that number is _SC_THREAD_CPUTIME
  here and answers 200112 rather than failing, so the mistake reads as a CPU
  count instead of an error. }
function TPlatformLayoutFreeBSDX86_64.SC_NPROCESSORS_ONLN: Integer; begin Result := 58; end;

function TPlatformLayoutFreeBSDX86_64.StatBufSize: Integer;
begin
  Result := STAT_SIZE;
end;

function TPlatformLayoutFreeBSDX86_64.StatSize(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_SIZE);
  Result := P^;
end;

function TPlatformLayoutFreeBSDX86_64.StatMtime(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MTIME);
  Result := P^;
end;

function TPlatformLayoutFreeBSDX86_64.StatMode(Buf: Pointer): Integer;
var
  P: ^Integer;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MODE);
  Result := P^;
end;

{ Assign GPlatformLayout to the FreeBSD layout, once.  Called from this unit's
  initialization (rtl.platform.layout.freebsd_init, which main invokes by-name
  for a FreeBSD --target) and from the weak _BlaisePlatformInit trampoline. }
procedure AssignLayoutFreeBSD;
begin
  if GPlatformLayout = nil then
    GPlatformLayout := TPlatformLayoutFreeBSDX86_64.Create();
end;

{$IFDEF FREEBSD}
{ Weak bootstrap-fallback trampoline — see the twin in rtl.platform.layout.linux
  for the full rationale.  Target-guarded like the flat functions above: on a
  host build that links both layout units, only the host unit may provide the
  trampoline (the nil-guard in AssignLayout is no protection — it just hands
  the layout to whichever init runs FIRST, and unit-init order put this unit
  before the host one, breaking every O_CREAT open in the process). }
procedure _BlaisePlatformInit; assembler; nostackframe;
asm
    .weak _BlaisePlatformInit
    jmp AssignLayoutFreeBSD
end;
{$ENDIF}

{$IFDEF FREEBSD}
function _MapAnonFlag: Integer;
begin
  Result := $1000;
end;

const
  UMTX_OP_WAIT_UINT_PRIVATE = 15;
  UMTX_OP_WAKE_PRIVATE      = 16;

{ _umtx_op(obj, op, val, uaddr, uaddr2) — SYS 454; arg4 (%rcx) -> %r10.
  Same shape as the runtime.syscall.freebsd leaf, duplicated here because
  that unit is only linked under --static and these primitives must exist
  on both profiles. }
function _park_umtx_op(Obj: Pointer; Op, Val: Integer;
  Uaddr, Uaddr2: Pointer): Integer; assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $454, %rax          { SYS__umtx_op }
    syscall
    jae  .Lok_parkumtx
    negq %rax
.Lok_parkumtx:
    ret
end;

procedure _ParkWait(AAddr: Pointer; AExpected: Integer; ATs: Pointer);
begin
  { uaddr = sizeof(struct timespec) selects the plain-timespec RELATIVE
    timeout form of _umtx_op's WAIT (uaddr2 points at the timespec). }
  _park_umtx_op(AAddr, UMTX_OP_WAIT_UINT_PRIVATE, AExpected,
    Pointer(16), ATs);
end;

procedure _ParkWake(AAddr: Pointer; ACount: Integer);
begin
  _park_umtx_op(AAddr, UMTX_OP_WAKE_PRIVATE, ACount, nil, nil);
end;

function _ClockMonotonicId: Integer;
begin
  Result := 4;
end;

function _SolSocket: Integer;    begin Result := $FFFF;     end;
function _SoReuseAddr: Integer;  begin Result := $0004;     end;
function _SoReusePort: Integer;  begin Result := $0200;     end;
function _SoError: Integer;      begin Result := $1007;     end;
function _MsgNoSignal: Integer;  begin Result := $20000;    end;
function _ONonBlock: Integer;    begin Result := $0004;     end;
function _SockNonBlock: Integer; begin Result := $20000000; end;

procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
var
  PB: ^Byte;
  PW: ^UInt16;
  PD: ^UInt32;
  I: Integer;
begin
  PB := P;
  PB^ := 16;                               { sin_len = sizeof(sockaddr_in) }
  PB := Pointer(PChar(P) + 1);
  PB^ := 2;                                { sin_family = AF_INET }
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
{ Target-guarded: on a host (Linux) build this unit is linked only for its
  class API (cp.test.platformlayout.freebsd), and its unit-init runs BEFORE
  the host layout's — an unguarded assign here would claim GPlatformLayout
  first and hand the host process FreeBSD O_* flag values (observed: every
  harness O_CREAT open failed ENOENT because FreeBSD $0200|$0400 decodes as
  Linux O_TRUNC|O_APPEND). }
{$IFDEF FREEBSD}
  AssignLayoutFreeBSD();
{$ENDIF}

end.
