{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.errno.darwin;

// errno classification for the Darwin (macOS) profile — sibling of
// runtime.errno.linux / .freebsd.  macOS has exactly one profile: dynamic
// against libSystem (raw syscalls are private, unstable ABI — there is no
// static variant of this unit).
//
// Darwin's errno accessor is __error() (libSystem); EAGAIN = EWOULDBLOCK
// = 35, EINTR = 4.

interface

{ True when N is the return value of a call that failed because it would
  have blocked (EAGAIN/EWOULDBLOCK). }
function WouldBlock(N: Int64): Boolean;

{ True when N is the return value of a call interrupted by a signal. }
function Interrupted(N: Int64): Boolean;

{ True when N is the return value of a call that failed because the process
  (EMFILE) or the whole system (ENFILE) is out of file descriptors. }
function FdExhausted(N: Int64): Boolean;

{ The current thread's errno value. }
function GetOsErrno: Integer;

implementation

const
  EINTR = 4;
  EAGAIN = 35;   { EWOULDBLOCK = EAGAIN on Darwin }
  EMFILE = 24;   { per-process fd limit reached }
  ENFILE = 23;   { system-wide fd limit reached }

type
  PInteger = ^Integer;

function __error: Pointer; external name '__error';

function GetOsErrno: Integer;
var
  P: PInteger;
begin
  P := __error();
  Result := P^;
end;

function WouldBlock(N: Int64): Boolean;
begin
  Result := (N = -1) and (GetOsErrno() = EAGAIN);
end;

function Interrupted(N: Int64): Boolean;
begin
  Result := (N = -1) and (GetOsErrno() = EINTR);
end;

function FdExhausted(N: Int64): Boolean;
begin
  Result := (N = -1) and ((GetOsErrno() = EMFILE) or (GetOsErrno() = ENFILE));
end;

end.
