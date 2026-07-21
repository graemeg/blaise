{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.errno.static.freebsd;

// errno classification for the --static (libc-free) FreeBSD profile — the P3
// prerequisite of docs/async-networking-design.adoc.  The FreeBSD raw syscall
// leaves (runtime.syscall.freebsd) translate the kernel's carry-flag error
// convention to Linux-style -errno returns, so the classification here tests
// the negative return value, with FreeBSD's errno numbers (EAGAIN = 35).
// See runtime.errno.static.linux for the full rationale.

interface

{ True when N is the return value of a call that failed because it would have
  blocked (EAGAIN/EWOULDBLOCK — both 35 on FreeBSD). }
function WouldBlock(N: Int64): Boolean;

{ True when N is the return value of a call interrupted by a signal (EINTR). }
function Interrupted(N: Int64): Boolean;

{ True when N is the return value of a call that failed because the process
  (EMFILE) or the whole system (ENFILE) is out of file descriptors. }
function FdExhausted(N: Int64): Boolean;

{ No errno variable exists in this profile; always 0.  Present so shared code
  binding the symbol links in both profiles. }
function GetOsErrno: Integer;

implementation

const
  EINTR = 4;
  EAGAIN = 35;   { EWOULDBLOCK = EAGAIN on FreeBSD }
  EMFILE = 24;   { per-process fd limit reached }
  ENFILE = 23;   { system-wide fd limit reached }

function WouldBlock(N: Int64): Boolean;
begin
  Result := N = -EAGAIN;
end;

function Interrupted(N: Int64): Boolean;
begin
  Result := N = -EINTR;
end;

function FdExhausted(N: Int64): Boolean;
begin
  Result := (N = -EMFILE) or (N = -ENFILE);
end;

function GetOsErrno: Integer;
begin
  Result := 0;
end;

end.
