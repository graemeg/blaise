{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.errno.linux;

// errno classification for the dynamic (libc) Linux profile — the P3
// prerequisite of docs/async-networking-design.adoc.
//
// The readiness loops of the fiber I/O layer branch on "would this call have
// blocked?", but the two build profiles report that condition differently:
//
//   * libc build (this unit) — a failing call returns -1 and sets glibc's
//     errno, which is *__errno_location() (a TLS-indirect call).  WouldBlock
//     therefore tests N = -1 and reads EAGAIN through __errno_location.
//   * static build (runtime.errno.static.linux) — the raw syscall leaves
//     return -errno directly; there is no errno variable at all.
//
// BuildRTLUnitList (blaise.codegen.driver) swaps the matching variant in at
// link time, exactly like the runtime.start / runtime.start.static.<os> swap.
// Shared code binds the bare symbols via `external name` so it has one call
// site and never names a profile-specific unit:
//
//   function WouldBlock(N: Int64): Boolean; external name 'WouldBlock';
//
// On Linux EWOULDBLOCK = EAGAIN (11), so one comparison covers both names.

interface

{ True when N is the return value of a call that failed because it would have
  blocked (EAGAIN/EWOULDBLOCK). }
function WouldBlock(N: Int64): Boolean;

{ True when N is the return value of a call interrupted by a signal (EINTR). }
function Interrupted(N: Int64): Boolean;

{ True when N is the return value of a call that failed because the process
  (EMFILE) or the whole system (ENFILE) is out of file descriptors.  The fiber
  accept/socket paths back off on this instead of busy-retrying a call that
  cannot succeed until an fd is freed. }
function FdExhausted(N: Int64): Boolean;

{ The current thread's errno value.  Returns 0 in the static profile (raw
  syscalls carry the errno in their negative return instead). }
function GetOsErrno: Integer;

implementation

const
  EINTR = 4;
  EAGAIN = 11;   { EWOULDBLOCK = EAGAIN on Linux }
  EMFILE = 24;   { per-process fd limit reached }
  ENFILE = 23;   { system-wide fd limit reached }

type
  PInteger = ^Integer;

function __errno_location: Pointer; external name '__errno_location';

function GetOsErrno: Integer;
var
  P: PInteger;
begin
  P := __errno_location();
  Result := P^;
end;

function WouldBlock(N: Int64): Boolean;
begin
  Result := (N = -1) and (GetOsErrno() = EAGAIN);
end;

function FdExhausted(N: Int64): Boolean;
begin
  Result := (N = -1) and ((GetOsErrno() = EMFILE) or (GetOsErrno() = ENFILE));
end;

function Interrupted(N: Int64): Boolean;
begin
  Result := (N = -1) and (GetOsErrno() = EINTR);
end;

end.
