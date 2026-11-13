{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit rtl.platform.layout.windows;
// The Windows platform layout: the initialiser main calls by name
// (rtl.platform.layout.windows_init, from PlatformLayoutInitSym), the flat
// pre-init leaf runtime.mem binds, and a TPlatformLayout.
//
// TPlatformLayout describes POSIX facts -- open(2) flags, struct stat and
// dirent layouts -- that the POSIX adapter reads.  Windows has no such
// structures: its adapter (rtl.platform.windows) calls the Win32 file API.
// The flag and whence values below are the ones the shared code passes
// through to the adapter, and the struct accessors are never reached on
// Windows; they report themselves if they are.

interface

uses
  rtl.platform;

type
  TPlatformLayoutWindows = class(TPlatformLayout)
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
    { The name sysconf in runtime.syscall.windows ignores. }
    function SC_NPROCESSORS_ONLN: Int32; override;
    function StatBufSize: Int32; override;
    function StatSize(Buf: Pointer):  Int64; override;
    function StatMtime(Buf: Pointer): Int64; override;
    function StatMode(Buf: Pointer):  Int32; override;
    function DirentRecLen(Ent: Pointer): Int32; override;
    function DirentName(Ent: Pointer): Pointer; override;
  end;

{ runtime.mem's MAP_ANONYMOUS flag.  The Windows mmap leaf maps anonymous
  memory only and ignores the flags. }
function _MapAnonFlag: Int32;

{ CLOCK_MONOTONIC for runtime.syscall.windows' clock_gettime: 1, the
  performance counter. }
function _ClockMonotonicId: Int32;

{ Park and wake for idle fibre workers (async.fibers): WaitOnAddress and
  WakeByAddressSingle/All, loaded on first use from the synchronisation API
  set so a program that never parks does not import it.  _ParkWait blocks
  while the 32-bit word at AAddr equals AExpected, at most for the relative
  struct timespec at ATs (never nil); a spurious return is allowed. }
procedure _ParkWait(AAddr: Pointer; AExpected: Int32; ATs: Pointer);
procedure _ParkWake(AAddr: Pointer; ACount: Int32);

{ The running thread's stack bounds in its thread environment block
  (NT_TIB StackBase at %gs:8, StackLimit at %gs:16), and setting them: a
  fibre switch points them at the incoming fibre's stack, which is the
  stack Windows then checks a stack address against.  DeallocationStack is
  left alone: it names the stack the system frees when the thread exits,
  which is always the thread's own. }
procedure _FiberStackBounds(out ABase, ALimit: Pointer);
procedure _FiberSetStackBounds(ABase, ALimit: Pointer);

{ Socket-layer constants (Net.Sockets, async.io), as the POSIX-named socket
  leaves in runtime.net.windows take them: Winsock's own values where
  Winsock has the option, and the fcntl vocabulary those leaves define. }
function _SolSocket: Int32;      { SOL_SOCKET   = $FFFF }
function _SoReuseAddr: Int32;    { SO_REUSEADDR = 4; the setsockopt leaf
                                   takes it as the POSIX meaning, which is
                                   Windows' default }
function _SoReusePort: Int32;    { none: an option Winsock refuses }
function _SoError: Int32;        { SO_ERROR     = $1007 }
function _MsgNoSignal: Int32;    { 0: no signals }
function _ONonBlock: Int32;      { the fcntl leaf's O_NONBLOCK = $800 }
function _SockNonBlock: Int32;   { the accept4 leaf's SOCK_NONBLOCK = $800 }
function _SoNoSigPipe: Int32;    { 0: no signals }

{ struct addrinfo (ADDRINFOA): ai_addrlen is a size_t, so ai_canonname
  comes before ai_addr, at 32.  AI_ADDRCONFIG is $0400. }
function _AddrInfoAddrOffset: Int32;
function _AiAddrConfig: Int32;

{ Fill a 16-byte struct sockaddr_in at P for AF_INET (the Linux layout: a
  u16 sin_family).  APortN/AAddrN are in network byte order. }
procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);

implementation

function _sys_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
  external name 'write';
procedure _exit(Code: Int32); external name '_exit';

function W32LoadLibraryA(AName: PChar): Pointer;
  external 'kernel32' name 'LoadLibraryA';
function W32GetProcAddress(AModule: Pointer; AName: PChar): Pointer;
  external 'kernel32' name 'GetProcAddress';
procedure W32Sleep(AMilliseconds: UInt32); external 'kernel32' name 'Sleep';

type
  TWaitOnAddress = function(AAddr: Pointer; ACompare: Pointer; ASize: UInt64;
    AMilliseconds: UInt32): Int32; cdecl;
  TWakeByAddress = procedure(AAddr: Pointer); cdecl;

var
  { 0 until the first park, then 1 (loaded) or -1 (not available: park
    falls back to a short sleep).  Racing first calls load the same module
    and store the same addresses. }
  GParkState: Int32;
  GWaitOnAddress: TWaitOnAddress;
  GWakeByAddressSingle: TWakeByAddress;
  GWakeByAddressAll: TWakeByAddress;

{ Report a POSIX layout accessor reached on Windows, and end the program. }
procedure NotOnWindows(const AName: string);
const
  Prefix = 'internal: TPlatformLayout.';
  Suffix = ' has no meaning on Windows'#13#10;
begin
  _sys_write(2, PChar(Prefix), Length(Prefix));
  _sys_write(2, PChar(AName), Length(AName));
  _sys_write(2, PChar(Suffix), Length(Suffix));
  _exit(3);
end;

function TPlatformLayoutWindows.O_RDONLY: Int32; begin Result := 0;     end;
function TPlatformLayoutWindows.O_WRONLY: Int32; begin Result := 1;     end;
function TPlatformLayoutWindows.O_RDWR:   Int32; begin Result := 2;     end;
function TPlatformLayoutWindows.O_CREAT:  Int32; begin Result := $40;   end;
function TPlatformLayoutWindows.O_TRUNC:  Int32; begin Result := $200;  end;
function TPlatformLayoutWindows.O_APPEND: Int32; begin Result := $400;  end;

function TPlatformLayoutWindows.S_IFMT:  Int32; begin Result := $F000; end;
function TPlatformLayoutWindows.S_IFDIR: Int32; begin Result := $4000; end;
function TPlatformLayoutWindows.S_IFREG: Int32; begin Result := $8000; end;
function TPlatformLayoutWindows.S_IFLNK: Int32; begin Result := $A000; end;

function TPlatformLayoutWindows.SEEK_SET: Int32; begin Result := 0; end;
function TPlatformLayoutWindows.SEEK_CUR: Int32; begin Result := 1; end;
function TPlatformLayoutWindows.SEEK_END: Int32; begin Result := 2; end;

function TPlatformLayoutWindows.CLOCK_REALTIME: Int32; begin Result := 0; end;
function TPlatformLayoutWindows.WNOHANG:        Int32; begin Result := 1; end;

function TPlatformLayoutWindows.SC_NPROCESSORS_ONLN: Int32;
begin
  Result := 0;
end;

function TPlatformLayoutWindows.StatBufSize: Int32;
begin
  NotOnWindows('StatBufSize');
  Result := 0;
end;

function TPlatformLayoutWindows.StatSize(Buf: Pointer): Int64;
begin
  NotOnWindows('StatSize');
  Result := 0;
end;

function TPlatformLayoutWindows.StatMtime(Buf: Pointer): Int64;
begin
  NotOnWindows('StatMtime');
  Result := 0;
end;

function TPlatformLayoutWindows.StatMode(Buf: Pointer): Int32;
begin
  NotOnWindows('StatMode');
  Result := 0;
end;

function TPlatformLayoutWindows.DirentRecLen(Ent: Pointer): Int32;
begin
  NotOnWindows('DirentRecLen');
  Result := 0;
end;

function TPlatformLayoutWindows.DirentName(Ent: Pointer): Pointer;
begin
  NotOnWindows('DirentName');
  Result := nil;
end;

function _MapAnonFlag: Int32;
begin
  Result := 0;
end;

function _ClockMonotonicId: Int32;
begin
  Result := 1;
end;

function ParkReady: Boolean;
var
  H: Pointer;
begin
  if GParkState = 0 then
  begin
    H := W32LoadLibraryA(PChar('api-ms-win-core-synch-l1-2-0.dll'));
    if H <> nil then
    begin
      GWaitOnAddress := TWaitOnAddress(W32GetProcAddress(H,
        PChar('WaitOnAddress')));
      GWakeByAddressSingle := TWakeByAddress(W32GetProcAddress(H,
        PChar('WakeByAddressSingle')));
      GWakeByAddressAll := TWakeByAddress(W32GetProcAddress(H,
        PChar('WakeByAddressAll')));
    end;
    if (H <> nil) and (Pointer(GWaitOnAddress) <> nil) and
       (Pointer(GWakeByAddressSingle) <> nil) and
       (Pointer(GWakeByAddressAll) <> nil) then
      GParkState := 1
    else
      GParkState := -1;
  end;
  Result := GParkState = 1;
end;

procedure _ParkWait(AAddr: Pointer; AExpected: Int32; ATs: Pointer);
var
  Ms: Int64;
  Expected: Int32;
begin
  Ms := PInt64(ATs)^ * 1000 + (PInt64(ATs + 8)^ + 999999) div 1000000;
  if Ms < 0 then
    Ms := 0;
  if Ms > $7FFFFFFF then
    Ms := $7FFFFFFF;
  if not ParkReady() then
  begin
    { no WaitOnAddress: a bounded nap, which the caller treats as a
      spurious wake }
    if Ms > 1 then
      Ms := 1;
    W32Sleep(UInt32(Ms));
    Exit;
  end;
  Expected := AExpected;
  GWaitOnAddress(AAddr, @Expected, 4, UInt32(Ms));
end;

procedure _ParkWake(AAddr: Pointer; ACount: Int32);
begin
  if not ParkReady() then
    Exit;
  if ACount <= 1 then
    GWakeByAddressSingle(AAddr)
  else
    GWakeByAddressAll(AAddr);
end;

procedure _FiberStackBounds(out ABase, ALimit: Pointer); assembler; nostackframe;
asm
    movq %gs:8, %rax
    movq %rax, (%rdi)
    movq %gs:16, %rax
    movq %rax, (%rsi)
    ret
end;

procedure _FiberSetStackBounds(ABase, ALimit: Pointer); assembler; nostackframe;
asm
    movq %rdi, %gs:8
    movq %rsi, %gs:16
    ret
end;

function _SolSocket: Int32;
begin
  Result := $FFFF;
end;

function _SoReuseAddr: Int32;
begin
  Result := 4;
end;

function _SoReusePort: Int32;
begin
  Result := $7FFF;
end;

function _SoError: Int32;
begin
  Result := $1007;
end;

function _MsgNoSignal: Int32;
begin
  Result := 0;
end;

function _ONonBlock: Int32;
begin
  Result := $800;
end;

function _SockNonBlock: Int32;
begin
  Result := $800;
end;

function _SoNoSigPipe: Int32;
begin
  Result := 0;
end;

function _AddrInfoAddrOffset: Int32;
begin
  Result := 32;
end;

function _AiAddrConfig: Int32;
begin
  Result := $0400;
end;

procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
var
  I: Int;
begin
  for I := 0 to 15 do
    PByte(P + I)^ := 0;
  PUInt16(P)^ := 2;
  PUInt16(P + 2)^ := APortN;
  PUInt32(P + 4)^ := AAddrN;
end;

initialization
  if GPlatformLayout = nil then
    GPlatformLayout := TPlatformLayoutWindows.Create();

end.
