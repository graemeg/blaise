{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit rtl.platform.layout.darwin;

// Darwin (macOS) arm64 struct layouts and OS constants — the concrete
// TPlatformLayout adapter for the macos-arm64 target.  Sibling of
// rtl.platform.layout.linux / .freebsd; the shared POSIX method bodies live
// in rtl.platform.posix, and only the struct stat layout plus a handful of
// constant values diverge per target.
//
// struct stat on Darwin arm64 is the 64-bit-inode layout (the ONLY layout on
// arm64 — the $INODE64 split was an x86_64 transition artefact): st_mode is a
// 16-bit mode_t at byte 4 (nlink_t occupies bytes 6-7, so a 32-bit read
// would fold nlink into the mode — StatMode reads exactly 16 bits),
// st_mtimespec.tv_sec at byte 48, st_size at byte 96, sizeof = 144.
// CONFIRM these against the SDK headers during the Phase 6 MacBook bring-up
// before trusting file sizes/dates on real hardware.
//
// The O_* creation flags share FreeBSD's values (both BSD-derived); the
// CLOCK_* ids and the socket-layer constants have Darwin-specific values.
// Darwin has NO MSG_NOSIGNAL (SIGPIPE suppression is the SO_NOSIGPIPE socket
// option) and no SOCK_NONBLOCK/accept4 — both report 0 so callers fall back
// to their portable paths (fcntl O_NONBLOCK after accept).

interface

uses
  rtl.platform;

type
  TPlatformLayoutDarwinArm64 = class(TPlatformLayout)
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

    function StatBufSize: Integer; override;
    function StatSize(Buf: Pointer):  Int64; override;
    function StatMtime(Buf: Pointer): Int64; override;
    function StatMode(Buf: Pointer):  Integer; override;
  end;

{$IFDEF DARWIN}
{ Flat function for runtime.mem: Darwin MAP_ANON = $1000 (same as FreeBSD).
  Target-guarded like every flat function here — see the rationale in
  rtl.platform.layout.linux: a host test build linking this unit for its
  class API must not define colliding flat symbols. }
function _MapAnonFlag: Integer;

{ Flat park/wake primitives for the fiber scheduler.  Darwin's kernel wait
  primitive (__ulock_wait/__ulock_wake) is PRIVATE API — rejected for the
  same reason raw syscalls are (unstable ABI).  Until a libSystem-based
  waiter lands (pthread cond or os_sync_wait_on_address once the SDK floor
  allows it), _ParkWait degrades to nanosleep of the full bounded timeout
  and _ParkWake is a no-op: park protocols must tolerate spurious wakeups
  and re-check their word, so this is correct-but-higher-latency.  Tracked
  as a Phase 6 bring-up item in macos-arm64-tasks.txt. }
procedure _ParkWait(AAddr: Pointer; AExpected: Integer; ATs: Pointer);
procedure _ParkWake(AAddr: Pointer; ACount: Integer);

{ The target's CLOCK_MONOTONIC clockid for clock_gettime: Darwin 6.
  (Linux is 1, FreeBSD 4; Darwin's 4 is CLOCK_MONOTONIC_RAW.) }
function _ClockMonotonicId: Integer;

{ Socket-layer OS constants (Net.Sockets / async.io).  Darwin values from
  sys/socket.h / sys/fcntl.h.  _MsgNoSignal and _SockNonBlock are 0 —
  Darwin has neither flag; callers detect 0 and use their portable
  fallbacks (SIGPIPE suppression via SO_NOSIGPIPE is a future seam). }
function _SolSocket: Integer;      { SOL_SOCKET   = $FFFF }
function _SoReuseAddr: Integer;    { SO_REUSEADDR = $0004 }
function _SoReusePort: Integer;    { SO_REUSEPORT = $0200 }
function _SoError: Integer;        { SO_ERROR     = $1007 }
function _MsgNoSignal: Integer;    { no MSG_NOSIGNAL on Darwin — 0 }
function _ONonBlock: Integer;      { O_NONBLOCK   = $0004 }
function _SockNonBlock: Integer;   { no SOCK_NONBLOCK/accept4 on Darwin — 0 }

{ Fill a 16-byte struct sockaddr_in at P for AF_INET.  APortN/AAddrN are
  ALREADY in network byte order.  Darwin layout matches FreeBSD: sin_len
  (u8, = 16), sin_family (u8, = AF_INET), sin_port (u16), sin_addr (u32),
  sin_zero[8]. }
procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
{$ENDIF}

implementation

const
  { Darwin arm64 struct stat field offsets (bytes) — 64-bit-inode layout. }
  STAT_OFF_MODE  = 4;    { st_mode  (mode_t, u16; nlink_t at 6) }
  STAT_OFF_MTIME = 48;   { st_mtimespec.tv_sec (Int64) }
  STAT_OFF_SIZE  = 96;   { st_size  (off_t, Int64) }
  STAT_SIZE      = 144;  { sizeof(struct stat) }

function TPlatformLayoutDarwinArm64.O_RDONLY: Integer; begin Result := 0;     end;
function TPlatformLayoutDarwinArm64.O_WRONLY: Integer; begin Result := 1;     end;
function TPlatformLayoutDarwinArm64.O_RDWR:   Integer; begin Result := 2;     end;
function TPlatformLayoutDarwinArm64.O_CREAT:  Integer; begin Result := $0200; end;
function TPlatformLayoutDarwinArm64.O_TRUNC:  Integer; begin Result := $0400; end;
function TPlatformLayoutDarwinArm64.O_APPEND: Integer; begin Result := $0008; end;

function TPlatformLayoutDarwinArm64.S_IFMT:  Integer; begin Result := $F000; end;
function TPlatformLayoutDarwinArm64.S_IFDIR: Integer; begin Result := $4000; end;

function TPlatformLayoutDarwinArm64.SEEK_SET: Integer; begin Result := 0; end;
function TPlatformLayoutDarwinArm64.SEEK_CUR: Integer; begin Result := 1; end;
function TPlatformLayoutDarwinArm64.SEEK_END: Integer; begin Result := 2; end;

function TPlatformLayoutDarwinArm64.CLOCK_REALTIME: Integer; begin Result := 0; end;
function TPlatformLayoutDarwinArm64.WNOHANG:        Integer; begin Result := 1; end;

function TPlatformLayoutDarwinArm64.StatBufSize: Integer;
begin
  Result := STAT_SIZE;
end;

function TPlatformLayoutDarwinArm64.StatSize(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_SIZE);
  Result := P^;
end;

function TPlatformLayoutDarwinArm64.StatMtime(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MTIME);
  Result := P^;
end;

function TPlatformLayoutDarwinArm64.StatMode(Buf: Pointer): Integer;
var
  P: ^UInt16;
begin
  { mode_t is 16 bits and nlink_t sits in the adjacent two bytes — a
    32-bit read here would fold the link count into the mode }
  P := Pointer(PChar(Buf) + STAT_OFF_MODE);
  Result := Integer(P^);
end;

{ Assign GPlatformLayout to the Darwin layout, once.  Called from this
  unit's initialization (for a Darwin --target) and from the weak
  _BlaisePlatformInit trampoline. }
procedure AssignLayoutDarwin;
begin
  if GPlatformLayout = nil then
    GPlatformLayout := TPlatformLayoutDarwinArm64.Create();
end;

{$IFDEF DARWIN}
{ Weak bootstrap-fallback trampoline — see the twin in
  rtl.platform.layout.linux for the full rationale.  Target-guarded like
  the flat functions above.

  The branch target is spelled '_AssignLayoutDarwin' by hand: an asm block is
  emitted VERBATIM, so the backend's Darwin underscore rule cannot reach it,
  and AssignLayoutDarwin is a plain Pascal routine whose label therefore
  carries the '_'.  Hard-coding it is safe because this block is already
  guarded by the DARWIN conditional.  _BlaisePlatformInit needs no change: its
  Pascal identifier already begins with '_', which IS the Darwin prefix. }
procedure _BlaisePlatformInit; assembler; nostackframe;
asm
    .weak _BlaisePlatformInit
    b _AssignLayoutDarwin
end;

function _MapAnonFlag: Integer;
begin
  Result := $1000;
end;

{ Bounded sleep via libSystem nanosleep — see the interface note on the
  park/wake degradation. }
function darwin_nanosleep(Req: Pointer; Rem: Pointer): Integer;
  external name 'nanosleep';

procedure _ParkWait(AAddr: Pointer; AExpected: Integer; ATs: Pointer);
begin
  darwin_nanosleep(ATs, nil);
end;

procedure _ParkWake(AAddr: Pointer; ACount: Integer);
begin
  { no-op: parked fibers wake at their bounded timeout (see interface) }
end;

function _ClockMonotonicId: Integer;
begin
  Result := 6;
end;

function _SolSocket: Integer;    begin Result := $FFFF; end;
function _SoReuseAddr: Integer;  begin Result := $0004; end;
function _SoReusePort: Integer;  begin Result := $0200; end;
function _SoError: Integer;      begin Result := $1007; end;
function _MsgNoSignal: Integer;  begin Result := 0;     end;
function _ONonBlock: Integer;    begin Result := $0004; end;
function _SockNonBlock: Integer; begin Result := 0;     end;

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
  class API, and an unguarded assign here would claim GPlatformLayout ahead
  of the host layout — see the incident note in rtl.platform.layout.freebsd. }
{$IFDEF DARWIN}
  AssignLayoutDarwin();
{$ENDIF}

end.
