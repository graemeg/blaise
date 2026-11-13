{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit runtime.errno.windows;
// Error classification for Windows: the same bare symbols as
// runtime.errno.linux (BuildRTLUnitList swaps the unit per target), over
// GetLastError and WSAGetLastError.  A failing call returns -1, as in the libc
// profiles.
//
// The Windows socket layer arrives with the networking work (M7); until then
// GetLastError is the only error source, and the socket-specific questions
// (would-block, connect pending) answer from the WinSock codes it would set.

interface

{ True when N is the return value of a call that failed because it would have
  blocked (WSAEWOULDBLOCK). }
function WouldBlock(N: Int64): Boolean;
{ True when N is the return value of an interrupted call (WSAEINTR). }
function Interrupted(N: Int64): Boolean;
{ True when N is the return value of a call that failed for want of
  descriptors (WSAEMFILE, or ERROR_TOO_MANY_OPEN_FILES). }
function FdExhausted(N: Int64): Boolean;
{ True when N is the return value of a non-blocking connect that is still
  completing (WSAEWOULDBLOCK, as WinSock reports it, or WSAEINPROGRESS). }
function ConnectPending(N: Int64): Boolean;
{ The POSIX errno behind N, a failed call's return value, mapped from the
  Win32 error (EIO for one with no POSIX counterpart); 0 when N is not a
  failure.  The stdlib reads errno numbers (IO.Files' error texts and
  ENOENT/EEXIST/EXDEV tests), so the mapping keeps them meaning the same on
  every target.  The would-block and interrupted questions above read the
  raw Win32 and WinSock codes. }
function OsErrorOf(N: Int64): Int;
{ The calling thread's last error code. }
function GetOsErrno: Int;

implementation

function GetLastError: UInt32; external 'kernel32' name 'GetLastError';

const
  ERROR_TOO_MANY_OPEN_FILES = 4;
  WSAEINTR = 10004;
  WSAEMFILE = 10024;
  WSAEWOULDBLOCK = 10035;
  WSAEINPROGRESS = 10036;

function GetOsErrno: Int;
begin
  Result := Int(GetLastError());
end;

function WouldBlock(N: Int64): Boolean;
begin
  Result := (N = -1) and (GetOsErrno() = WSAEWOULDBLOCK);
end;

function Interrupted(N: Int64): Boolean;
begin
  Result := (N = -1) and (GetOsErrno() = WSAEINTR);
end;

function FdExhausted(N: Int64): Boolean;
begin
  Result := (N = -1) and ((GetOsErrno() = WSAEMFILE) or
    (GetOsErrno() = ERROR_TOO_MANY_OPEN_FILES));
end;

function ConnectPending(N: Int64): Boolean;
begin
  Result := (N = -1) and ((GetOsErrno() = WSAEWOULDBLOCK) or
    (GetOsErrno() = WSAEINPROGRESS));
end;

{ Win32 error -> POSIX errno (the numbers Linux uses, which macOS and FreeBSD
  share below 35). }
function PosixErrno(AWin32: Int): Int;
begin
  case AWin32 of
    0: Result := 0;
    2, 3, 15, 161: Result := 2;          { ENOENT: file, path, drive, bad path }
    4: Result := 24;                     { EMFILE }
    5, 82: Result := 13;                 { EACCES; ERROR_CANNOT_MAKE }
    6: Result := 9;                      { EBADF }
    8, 14: Result := 12;                 { ENOMEM }
    17: Result := 18;                    { EXDEV: ERROR_NOT_SAME_DEVICE }
    19: Result := 30;                    { EROFS: ERROR_WRITE_PROTECT }
    32, 33: Result := 16;                { EBUSY: sharing, lock violation }
    39, 112: Result := 28;               { ENOSPC }
    80, 183: Result := 17;               { EEXIST }
    87, 123, 4390: Result := 22;         { EINVAL; bad name; not a link }
    145: Result := 39;                   { ENOTEMPTY }
    206: Result := 36;                   { ENAMETOOLONG }
    267: Result := 20;                   { ENOTDIR: ERROR_DIRECTORY }
    1314: Result := 1;                   { EPERM: privilege not held }
    1921: Result := 40;                  { ELOOP: cannot resolve the name }
  else
    Result := 5;                         { EIO }
  end;
end;

function OsErrorOf(N: Int64): Int;
begin
  if N = -1 then
    Result := PosixErrno(GetOsErrno())
  else
    Result := 0;
end;

end.
