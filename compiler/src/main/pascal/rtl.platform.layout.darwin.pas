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

    function SC_NPROCESSORS_ONLN: Integer; override;

    function StatBufSize: Integer; override;
    function StatSize(Buf: Pointer):  Int64; override;
    function StatMtime(Buf: Pointer): Int64; override;
    function StatMode(Buf: Pointer):  Integer; override;

    function DirentRecLen(Ent: Pointer): Integer; override;
    function DirentName(Ent: Pointer): Pointer; override;
  end;

{$IFDEF DARWIN}
{ Flat function for runtime.mem: Darwin MAP_ANON = $1000 (same as FreeBSD).
  Target-guarded like every flat function here — see the rationale in
  rtl.platform.layout.linux: a host test build linking this unit for its
  class API must not define colliding flat symbols. }
function _MapAnonFlag: Integer;

{ Flat park/wake primitives for the fiber scheduler: futex semantics (block
  while the 32-bit word at AAddr equals AExpected, for at most the RELATIVE
  timeout ATs; wake up to ACount waiters on AAddr).  Darwin's kernel wait
  primitive (__ulock_wait/__ulock_wake) is PRIVATE API — rejected for the
  same reason raw syscalls are (unstable ABI) — and os_sync_wait_on_address
  needs macOS 14.4.  So the waiter is built from public libSystem pthread
  objects: 64 hashed buckets, each a mutex + condition variable.  _ParkWait
  re-checks the word UNDER the bucket lock before waiting, and _ParkWake
  broadcasts under the same lock, so a wake that lands between the check and
  the wait cannot be lost.  A broadcast may wake waiters on other words that
  share the bucket; park protocols already tolerate spurious wakeups and
  re-check their word. }
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

  { Darwin struct dirent (64-bit-inode layout, as returned by getdirentries64):
      d_ino (8) d_seekoff (8) d_reclen (u16 @16) d_namlen (u16 @18)
      d_type (u8 @20) d_name (@21).
    Note d_namlen precedes d_type here, unlike Linux and FreeBSD. }
  DIRENT_OFF_RECLEN = 16;
  DIRENT_OFF_NAME   = 21;

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

{ Darwin sys/unistd.h — 58, as on FreeBSD, not glibc's 84. }
function TPlatformLayoutDarwinArm64.SC_NPROCESSORS_ONLN: Integer; begin Result := 58; end;

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

function TPlatformLayoutDarwinArm64.DirentRecLen(Ent: Pointer): Integer;
var
  P: ^Word;
begin
  P := Pointer(PChar(Ent) + DIRENT_OFF_RECLEN);
  Result := P^;
end;

function TPlatformLayoutDarwinArm64.DirentName(Ent: Pointer): Pointer;
begin
  Result := Pointer(PChar(Ent) + DIRENT_OFF_NAME);
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

  BOTH symbols are spelled with their Darwin prefix by hand: an asm block is
  emitted VERBATIM, so the backend's underscore rule (DarwinSym) cannot reach
  inside it.  Every name gets exactly one '_' on Darwin, so the Pascal routine
  AssignLayoutDarwin is _AssignLayoutDarwin, and this routine — whose Pascal
  identifier already starts with an underscore — is __BlaisePlatformInit.  Its
  own .weak must therefore name the DOUBLE-underscored label, or the weak
  binding applies to a symbol nothing defines and the strong RTL copy no longer
  collapses at link.  Hard-coding is safe because the block is already guarded
  by the DARWIN conditional; the linux/freebsd twins keep the bare spellings. }
procedure _BlaisePlatformInit; assembler; nostackframe;
asm
    .weak __BlaisePlatformInit
    b _AssignLayoutDarwin
end;

function _MapAnonFlag: Integer;
begin
  Result := $1000;
end;

function darwin_mutex_init(M: Pointer; Attr: Pointer): Integer;
  external name 'pthread_mutex_init';
function darwin_mutex_lock(M: Pointer): Integer;
  external name 'pthread_mutex_lock';
function darwin_mutex_unlock(M: Pointer): Integer;
  external name 'pthread_mutex_unlock';
function darwin_cond_init(C: Pointer; Attr: Pointer): Integer;
  external name 'pthread_cond_init';
function darwin_cond_wait(C: Pointer; M: Pointer): Integer;
  external name 'pthread_cond_wait';
function darwin_cond_timedwait_rel(C: Pointer; M: Pointer;
  RelTs: Pointer): Integer;
  external name 'pthread_cond_timedwait_relative_np';
function darwin_cond_broadcast(C: Pointer): Integer;
  external name 'pthread_cond_broadcast';

const
  PARK_BUCKETS = 64;
  { one wait bucket: Darwin's pthread_mutex_t (64 bytes) followed by its
    pthread_cond_t (48), padded to 128 }
  PARK_MUTEX_OFF = 0;
  PARK_COND_OFF = 64;
  PARK_BUCKET_SIZE = 128;

var
  GParkBuckets: array[0..PARK_BUCKETS * PARK_BUCKET_SIZE - 1] of Byte;

{ the bucket's base address -- plain arithmetic on the byte block, so the
  RTL stays buildable by the release bootstrap compiler }
function ParkBucketBase(AIndex: Integer): Pointer;
begin
  Result := Pointer(Int64(@GParkBuckets) + Int64(AIndex) * PARK_BUCKET_SIZE);
end;

procedure InitParkBuckets;
var
  I: Integer;
  P: Pointer;
begin
  for I := 0 to PARK_BUCKETS - 1 do
  begin
    P := ParkBucketBase(I);
    darwin_mutex_init(Pointer(Int64(P) + PARK_MUTEX_OFF), nil);
    darwin_cond_init(Pointer(Int64(P) + PARK_COND_OFF), nil);
  end;
end;

function ParkBucketOf(AAddr: Pointer): Integer;
begin
  { words are at least 4-aligned and usually live in distinct records, so
    drop the low bits before folding }
  Result := Integer((Int64(AAddr) shr 4) and (PARK_BUCKETS - 1));
end;

procedure _ParkWait(AAddr: Pointer; AExpected: Integer; ATs: Pointer);
var
  P, M, C: Pointer;
  W: ^Integer;
begin
  P := ParkBucketBase(ParkBucketOf(AAddr));
  M := Pointer(Int64(P) + PARK_MUTEX_OFF);
  C := Pointer(Int64(P) + PARK_COND_OFF);
  W := AAddr;
  darwin_mutex_lock(M);
  if W^ = AExpected then
  begin
    if ATs = nil then
      darwin_cond_wait(C, M)
    else
      darwin_cond_timedwait_rel(C, M, ATs);
  end;
  darwin_mutex_unlock(M);
end;

procedure _ParkWake(AAddr: Pointer; ACount: Integer);
var
  P, M: Pointer;
begin
  { ACount is advisory: a broadcast wakes every waiter in the bucket, and
    each re-checks its own word }
  P := ParkBucketBase(ParkBucketOf(AAddr));
  M := Pointer(Int64(P) + PARK_MUTEX_OFF);
  darwin_mutex_lock(M);
  darwin_cond_broadcast(Pointer(Int64(P) + PARK_COND_OFF));
  darwin_mutex_unlock(M);
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
  InitParkBuckets();
{$ENDIF}

end.
