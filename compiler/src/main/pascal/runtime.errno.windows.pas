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
{ The OS error code behind N, a failed call's return value; 0 when N is not
  a failure. }
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

function OsErrorOf(N: Int64): Int;
begin
  if N = -1 then
    Result := GetOsErrno()
  else
    Result := 0;
end;

end.
