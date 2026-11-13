{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit runtime.net.windows;
// The POSIX-named socket leaves, over Winsock.
//
// The standard library's networking units (Net.Sockets, async.io) bind the
// BSD socket calls with a library-less `external name 'socket'` and so on.
// On Linux and macOS libc supplies them and on FreeBSD the static leaves do;
// here these Blaise routines do, with POSIX behaviour, so the stdlib units
// stay the same on every target.  On Linux a program that binds them links
// against libc (and its resolver) as before.
//
// A socket is a descriptor in the runtime.syscall.windows table, flagged
// WIN_FD_SOCKET, so close(2) closes it the Winsock way and the Int32
// descriptors the stdlib passes around work unchanged.  Winsock cannot report
// whether a socket is non-blocking, so the table's WIN_FD_NONBLOCK flag
// records it for fcntl(F_GETFL).
//
// ws2_32 is loaded on the first socket call, and its routines are called
// through cdecl procedural values: every RTL unit is linked into every
// program, and a program that opens no socket should not import ws2_32.
// Winsock reports its errors through WSAGetLastError, which is
// GetLastError, so runtime.errno.windows' classifiers read them as they are.

interface

function socket(ADomain, AType, AProtocol: Int32): Int32;
function bind(AFd: Int32; AAddr: Pointer; AAddrLen: Int32): Int32;
function listen(AFd, ABacklog: Int32): Int32;
function accept(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer): Int32;
{ accept4: accept, then SOCK_NONBLOCK ($800, rtl.platform.layout.windows'
  _SockNonBlock) sets the new socket's mode; SOCK_CLOEXEC is what every
  socket here has already. }
function accept4(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer;
  AFlags: Int32): Int32;
{ pipe(2) as a connected pair of loopback TCP sockets -- AFds[0] the read
  end, AFds[1] the write end -- because WSAPoll waits only on sockets and
  the fibre reactor parks on a pipe's read end (async.io's DNS completion).
  Not for a child process's standard handles. }
function pipe(AFds: Pointer): Int32;
function connect(AFd: Int32; AAddr: Pointer; AAddrLen: Int32): Int32;
function setsockopt(AFd, ALevel, AOptName: Int32; AOptVal: Pointer;
  AOptLen: Int32): Int32;
function getsockopt(AFd, ALevel, AOptName: Int32; AOptVal: Pointer;
  AOptLen: Pointer): Int32;
function getsockname(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer): Int32;
function getpeername(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer): Int32;
function recv(AFd: Int32; ABuf: Pointer; ALen: Int64; AFlags: Int32): Int64;
function send(AFd: Int32; ABuf: Pointer; ALen: Int64; AFlags: Int32): Int64;
function shutdown(AFd, AHow: Int32): Int32;
function htons(AHostShort: UInt16): UInt16;
function ntohs(ANetShort: UInt16): UInt16;
{ fcntl is C-variadic, and its callers declare it cdecl: F_GETFL and F_SETFL
  over the non-blocking flag; F_GETFD and F_SETFD succeed and change
  nothing. }
function fcntl(AFd, ACmd, AArg: Int32): Int32; cdecl;
{ There are no signals to ignore: SIGPIPE does not exist, and a send to a
  closed peer fails with an error.  Returns SIG_DFL. }
function signal(ASignum: Int32; AHandler: Pointer): Pointer;
function getaddrinfo(ANode, AService: PChar; AHints: Pointer;
  ARes: Pointer): Int32;
procedure freeaddrinfo(AInfo: Pointer);
{ poll(2) over sockets, through WSAPoll: an array of struct pollfd (an Int32
  descriptor, Int16 events and revents, with the POSIX POLL* values).  A
  descriptor that is not a socket reports POLLNVAL. }
function poll(AFds: Pointer; ANFds: Int64; ATimeout: Int32): Int32;

implementation

{ ---- runtime.syscall.windows ---- }

function _WinHandleOfFd(Fd: Int32): Pointer; external name '_WinHandleOfFd';
function _WinFdAddFlags(AHandle: Pointer; AFlags: Int32): Int32;
  external name '_WinFdAddFlags';
function _WinFdFlags(Fd: Int32): Int32; external name '_WinFdFlags';
function _WinFdSetFlags(Fd: Int32; AFlags: Int32): Boolean;
  external name '_WinFdSetFlags';
function _WinFdClose(Fd: Int32): Int32; external name '_WinFdClose';
type
  { runtime.syscall.windows' TWinSocketCloser }
  TSocketCloser = function(AHandle: Pointer): Int32;

procedure _WinSetSocketCloser(ACloser: TSocketCloser);
  external name '_WinSetSocketCloser';

type
  { runtime.syscall.windows' TWinSocketSender }
  TSocketSender = function(AHandle: Pointer; ABuf: Pointer;
    ACount: Int64): Int64;

procedure _WinSetSocketSender(ASender: TSocketSender);
  external name '_WinSetSocketSender';
procedure _WinSetSocketReceiver(AReceiver: TSocketSender);
  external name '_WinSetSocketReceiver';
function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';

{ ---- kernel32 ---- }

function LoadLibraryA(AName: PChar): Pointer;
  external 'kernel32' name 'LoadLibraryA';
function GetProcAddress(AModule: Pointer; AName: PChar): Pointer;
  external 'kernel32' name 'GetProcAddress';
procedure SetLastError(ACode: UInt32); external 'kernel32' name 'SetLastError';
function SetHandleInformation(AHandle: Pointer; AMask,
  AFlags: UInt32): Int32; external 'kernel32' name 'SetHandleInformation';
procedure WinSleep(AMilliseconds: UInt32); external 'kernel32' name 'Sleep';
procedure AcquireSRWLockExclusive(ALock: Pointer);
  external 'kernel32' name 'AcquireSRWLockExclusive';
procedure ReleaseSRWLockExclusive(ALock: Pointer);
  external 'kernel32' name 'ReleaseSRWLockExclusive';

const
  WIN_FD_SOCKET = 1;
  WIN_FD_NONBLOCK = 2;
  INVALID_SOCKET = $FFFFFFFFFFFFFFFF;
  HANDLE_FLAG_INHERIT = 1;
  INFINITE = $FFFFFFFF;
  FIONBIO = Int32($8004667E);
  ERROR_INVALID_PARAMETER = 87;
  WSAENOTSOCK = 10038;
  WSASYSNOTREADY = 10091;
  WSANO_RECOVERY = 11003;
  { the fcntl vocabulary (rtl.platform.layout.windows' _ONonBlock) }
  F_GETFD = 1;
  F_SETFD = 2;
  F_GETFL = 3;
  F_SETFL = 4;
  O_RDWR = 2;
  O_NONBLOCK = $800;
  { POSIX poll events, and Winsock's }
  POLLIN = $0001;
  POLLOUT = $0004;
  POLLERR = $0008;
  POLLHUP = $0010;
  POLLNVAL = $0020;
  WSA_POLLRDNORM = $0100;
  WSA_POLLRDBAND = $0200;
  WSA_POLLWRNORM = $0010;
  WSA_POLLERR = $0001;
  WSA_POLLHUP = $0002;
  WSA_POLLNVAL = $0004;
  { struct pollfd, and WSAPOLLFD (a SOCKET, events and revents, and four
    bytes of padding) }
  PFD_SIZE = 8;
  WPFD_SIZE = 16;
  { WSADATA is 408 bytes on x64 }
  WSADATA_SIZE = 512;

type
  TWsStartup = function(AVersion: UInt16; AData: Pointer): Int32; cdecl;
  TWsSocket = function(AAf, AType, AProtocol: Int32): UInt64; cdecl;
  TWsAddrIn = function(S: UInt64; AAddr: Pointer; ALen: Int32): Int32; cdecl;
  TWsAddrOut = function(S: UInt64; AAddr: Pointer; ALen: Pointer): Int32; cdecl;
  TWsAccept = function(S: UInt64; AAddr: Pointer; ALen: Pointer): UInt64; cdecl;
  TWsIntArg = function(S: UInt64; AArg: Int32): Int32; cdecl;
  TWsSetOpt = function(S: UInt64; ALevel, AName: Int32; AVal: Pointer;
    ALen: Int32): Int32; cdecl;
  TWsGetOpt = function(S: UInt64; ALevel, AName: Int32; AVal: Pointer;
    ALen: Pointer): Int32; cdecl;
  TWsIo = function(S: UInt64; ABuf: Pointer; ALen, AFlags: Int32): Int32; cdecl;
  TWsClose = function(S: UInt64): Int32; cdecl;
  TWsIoctl = function(S: UInt64; ACmd: Int32; AArg: Pointer): Int32; cdecl;
  TWsPoll = function(AFds: Pointer; ACount: UInt32; ATimeout: Int32): Int32; cdecl;
  TWsGetAddrInfo = function(ANode, AService: Pointer; AHints: Pointer;
    ARes: Pointer): Int32; cdecl;
  TWsFreeAddrInfo = procedure(AInfo: Pointer); cdecl;

var
  { 0 until ws2_32 is first wanted, then 1 when it is loaded and started,
    -1 when it could not be. }
  GWsState: Int32;
  GWsLock: Pointer;
  GWsStartup: TWsStartup;
  GWsSocket: TWsSocket;
  GWsBind: TWsAddrIn;
  GWsConnect: TWsAddrIn;
  GWsListen: TWsIntArg;
  GWsShutdown: TWsIntArg;
  GWsAccept: TWsAccept;
  GWsSetOpt: TWsSetOpt;
  GWsGetOpt: TWsGetOpt;
  GWsGetSockName: TWsAddrOut;
  GWsGetPeerName: TWsAddrOut;
  GWsRecv: TWsIo;
  GWsSend: TWsIo;
  GWsCloseSocket: TWsClose;
  GWsIoctl: TWsIoctl;
  GWsPoll: TWsPoll;
  GWsGetAddrInfo: TWsGetAddrInfo;
  GWsFreeAddrInfo: TWsFreeAddrInfo;

{ The closer runtime.syscall.windows calls for a socket descriptor. }
function WsCloseHandle(AHandle: Pointer): Int32;
begin
  Result := GWsCloseSocket(UInt64(AHandle));
end;

{ Winsock counts in an int; a longer request moves part of it, as a short
  read or write does. }
function IoLength(ALen: Int64): Int32;
begin
  if ALen > $7FFFFFFF then
    Result := $7FFFFFFF
  else
    Result := Int32(ALen);
end;

{ The sender write(2) uses for a socket descriptor. }
function WsSendHandle(AHandle: Pointer; ABuf: Pointer; ACount: Int64): Int64;
begin
  Result := GWsSend(UInt64(AHandle), ABuf, IoLength(ACount), 0);
end;

{ The receiver read(2) uses for a socket descriptor. }
function WsRecvHandle(AHandle: Pointer; ABuf: Pointer; ACount: Int64): Int64;
begin
  Result := GWsRecv(UInt64(AHandle), ABuf, IoLength(ACount), 0);
end;

{ Load ws2_32 and start Winsock 2.2; False when that failed. }
function WsLoad: Boolean;
var
  H: Pointer;
  Data: array[0..WSADATA_SIZE - 1] of Byte;
begin
  Result := False;
  H := LoadLibraryA(PChar('ws2_32.dll'));
  if H = nil then
    Exit;
  GWsStartup := TWsStartup(GetProcAddress(H, PChar('WSAStartup')));
  GWsSocket := TWsSocket(GetProcAddress(H, PChar('socket')));
  GWsBind := TWsAddrIn(GetProcAddress(H, PChar('bind')));
  GWsConnect := TWsAddrIn(GetProcAddress(H, PChar('connect')));
  GWsListen := TWsIntArg(GetProcAddress(H, PChar('listen')));
  GWsShutdown := TWsIntArg(GetProcAddress(H, PChar('shutdown')));
  GWsAccept := TWsAccept(GetProcAddress(H, PChar('accept')));
  GWsSetOpt := TWsSetOpt(GetProcAddress(H, PChar('setsockopt')));
  GWsGetOpt := TWsGetOpt(GetProcAddress(H, PChar('getsockopt')));
  GWsGetSockName := TWsAddrOut(GetProcAddress(H, PChar('getsockname')));
  GWsGetPeerName := TWsAddrOut(GetProcAddress(H, PChar('getpeername')));
  GWsRecv := TWsIo(GetProcAddress(H, PChar('recv')));
  GWsSend := TWsIo(GetProcAddress(H, PChar('send')));
  GWsCloseSocket := TWsClose(GetProcAddress(H, PChar('closesocket')));
  GWsIoctl := TWsIoctl(GetProcAddress(H, PChar('ioctlsocket')));
  GWsPoll := TWsPoll(GetProcAddress(H, PChar('WSAPoll')));
  GWsGetAddrInfo := TWsGetAddrInfo(GetProcAddress(H, PChar('getaddrinfo')));
  GWsFreeAddrInfo := TWsFreeAddrInfo(GetProcAddress(H, PChar('freeaddrinfo')));
  if (Pointer(GWsStartup) = nil) or (Pointer(GWsSocket) = nil) or
     (Pointer(GWsBind) = nil) or (Pointer(GWsConnect) = nil) or
     (Pointer(GWsListen) = nil) or (Pointer(GWsShutdown) = nil) or
     (Pointer(GWsAccept) = nil) or (Pointer(GWsSetOpt) = nil) or
     (Pointer(GWsGetOpt) = nil) or (Pointer(GWsGetSockName) = nil) or
     (Pointer(GWsGetPeerName) = nil) or (Pointer(GWsRecv) = nil) or
     (Pointer(GWsSend) = nil) or (Pointer(GWsCloseSocket) = nil) or
     (Pointer(GWsIoctl) = nil) or (Pointer(GWsPoll) = nil) or
     (Pointer(GWsGetAddrInfo) = nil) or (Pointer(GWsFreeAddrInfo) = nil) then
    Exit;
  if GWsStartup($0202, @Data[0]) <> 0 then
    Exit;
  _WinSetSocketCloser(@WsCloseHandle);
  _WinSetSocketSender(@WsSendHandle);
  _WinSetSocketReceiver(@WsRecvHandle);
  Result := True;
end;

{ Whether Winsock is ready, loading it on the first call; when it is not,
  the error is WSASYSNOTREADY. }
function WsReady: Boolean;
begin
  if GWsState = 0 then
  begin
    AcquireSRWLockExclusive(@GWsLock);
    if GWsState = 0 then
    begin
      if WsLoad() then
        GWsState := 1
      else
        GWsState := -1;
    end;
    ReleaseSRWLockExclusive(@GWsLock);
  end;
  Result := GWsState = 1;
  if not Result then
    SetLastError(WSASYSNOTREADY);
end;

{ The SOCKET behind descriptor AFd, or INVALID_SOCKET with WSAENOTSOCK when
  AFd is not a socket descriptor. }
function SocketOf(AFd: Int32): UInt64;
var
  Flags: Int32;
begin
  Flags := _WinFdFlags(AFd);
  if (Flags < 0) or ((Flags and WIN_FD_SOCKET) = 0) or (GWsState <> 1) then
  begin
    SetLastError(WSAENOTSOCK);
    Exit(INVALID_SOCKET);
  end;
  Result := UInt64(_WinHandleOfFd(AFd));
end;

{ Enter socket S in the descriptor table, kept out of child processes as a
  POSIX close-on-exec descriptor would be; its descriptor, or -1. }
function DescriptorOfSocket(S: UInt64; AFlags: Int32): Int32;
begin
  SetHandleInformation(Pointer(S), HANDLE_FLAG_INHERIT, 0);
  Result := _WinFdAddFlags(Pointer(S), WIN_FD_SOCKET or AFlags);
  if Result < 0 then
    GWsCloseSocket(S);
end;

function socket(ADomain, AType, AProtocol: Int32): Int32;
var
  S: UInt64;
begin
  if not WsReady() then
    Exit(-1);
  S := GWsSocket(ADomain, AType, AProtocol);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := DescriptorOfSocket(S, 0);
end;

function bind(AFd: Int32; AAddr: Pointer; AAddrLen: Int32): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsBind(S, AAddr, AAddrLen);
end;

function listen(AFd, ABacklog: Int32): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsListen(S, ABacklog);
end;

{ The accepted socket shares the listener's properties, its blocking mode
  among them, and its descriptor records that. }
function accept(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer): Int32;
var
  S, C: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  C := GWsAccept(S, AAddr, AAddrLen);
  if C = INVALID_SOCKET then
    Exit(-1);
  Result := DescriptorOfSocket(C, _WinFdFlags(AFd) and WIN_FD_NONBLOCK);
end;

function accept4(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer;
  AFlags: Int32): Int32;
var
  Mode: UInt32;
begin
  Result := accept(AFd, AAddr, AAddrLen);
  if (Result < 0) or ((AFlags and O_NONBLOCK) = 0) then
    Exit;
  Mode := 1;
  if GWsIoctl(UInt64(_WinHandleOfFd(Result)), FIONBIO, @Mode) <> 0 then
  begin
    _WinFdClose(Result);
    Exit(-1);
  end;
  _WinFdSetFlags(Result, _WinFdFlags(Result) or WIN_FD_NONBLOCK);
end;

function pipe(AFds: Pointer): Int32;
var
  L, W, R: UInt64;
  Addr: array[0..15] of Byte;
  Len, I: Int32;
  ReadFd, WriteFd: Int32;
begin
  if not WsReady() then
    Exit(-1);
  for I := 0 to 15 do
    Addr[I] := 0;
  PUInt16(@Addr[0])^ := 2;                 { AF_INET, port 0: any free one }
  PUInt32(@Addr[4])^ := $0100007F;         { 127.0.0.1, network order }
  L := GWsSocket(2, 1, 0);
  if L = INVALID_SOCKET then
    Exit(-1);
  W := INVALID_SOCKET;
  R := INVALID_SOCKET;
  Len := 16;
  if (GWsBind(L, @Addr[0], 16) = 0) and (GWsListen(L, 1) = 0) and
     (GWsGetSockName(L, @Addr[0], @Len) = 0) then
  begin
    W := GWsSocket(2, 1, 0);
    if (W <> INVALID_SOCKET) and (GWsConnect(W, @Addr[0], 16) = 0) then
      R := GWsAccept(L, nil, nil);
  end;
  GWsCloseSocket(L);
  if R = INVALID_SOCKET then
  begin
    if W <> INVALID_SOCKET then
      GWsCloseSocket(W);
    Exit(-1);
  end;
  ReadFd := DescriptorOfSocket(R, 0);
  if ReadFd < 0 then
  begin
    GWsCloseSocket(W);
    Exit(-1);
  end;
  WriteFd := DescriptorOfSocket(W, 0);
  if WriteFd < 0 then
  begin
    _WinFdClose(ReadFd);
    Exit(-1);
  end;
  PInt32(AFds)^ := ReadFd;
  PInt32(AFds + 4)^ := WriteFd;
  Result := 0;
end;

function connect(AFd: Int32; AAddr: Pointer; AAddrLen: Int32): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsConnect(S, AAddr, AAddrLen);
end;

{ SO_REUSEADDR asks POSIX for what Windows does already -- a listener may
  bind an address whose old connections linger in TIME_WAIT -- while
  Winsock's own SO_REUSEADDR would let a second socket take over a port in
  use.  So it succeeds and is not passed on. }
function setsockopt(AFd, ALevel, AOptName: Int32; AOptVal: Pointer;
  AOptLen: Int32): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  if (ALevel = $FFFF) and (AOptName = 4) then
    Exit(0);
  Result := GWsSetOpt(S, ALevel, AOptName, AOptVal, AOptLen);
end;

function getsockopt(AFd, ALevel, AOptName: Int32; AOptVal: Pointer;
  AOptLen: Pointer): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsGetOpt(S, ALevel, AOptName, AOptVal, AOptLen);
end;

function getsockname(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsGetSockName(S, AAddr, AAddrLen);
end;

function getpeername(AFd: Int32; AAddr: Pointer; AAddrLen: Pointer): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsGetPeerName(S, AAddr, AAddrLen);
end;

function recv(AFd: Int32; ABuf: Pointer; ALen: Int64; AFlags: Int32): Int64;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsRecv(S, ABuf, IoLength(ALen), AFlags);
end;

function send(AFd: Int32; ABuf: Pointer; ALen: Int64; AFlags: Int32): Int64;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsSend(S, ABuf, IoLength(ALen), AFlags);
end;

{ SHUT_RD, SHUT_WR and SHUT_RDWR are SD_RECEIVE, SD_SEND and SD_BOTH. }
function shutdown(AFd, AHow: Int32): Int32;
var
  S: UInt64;
begin
  S := SocketOf(AFd);
  if S = INVALID_SOCKET then
    Exit(-1);
  Result := GWsShutdown(S, AHow);
end;

function htons(AHostShort: UInt16): UInt16;
begin
  Result := UInt16(((AHostShort and $FF) shl 8) or (AHostShort shr 8));
end;

function ntohs(ANetShort: UInt16): UInt16;
begin
  Result := UInt16(((ANetShort and $FF) shl 8) or (ANetShort shr 8));
end;

function fcntl(AFd, ACmd, AArg: Int32): Int32; cdecl;
var
  Flags: Int32;
  S: UInt64;
  Mode: UInt32;
begin
  Flags := _WinFdFlags(AFd);
  if Flags < 0 then
  begin
    SetLastError(WSAENOTSOCK);
    Exit(-1);
  end;
  case ACmd of
    F_GETFD, F_SETFD:
      Result := 0;
    F_GETFL:
      begin
        Result := O_RDWR;
        if (Flags and WIN_FD_NONBLOCK) <> 0 then
          Result := Result or O_NONBLOCK;
      end;
    F_SETFL:
      begin
        Result := 0;
        { only a socket has a mode to set }
        if (Flags and WIN_FD_SOCKET) <> 0 then
        begin
          S := SocketOf(AFd);
          if S = INVALID_SOCKET then
            Exit(-1);
          if (AArg and O_NONBLOCK) <> 0 then
            Mode := 1
          else
            Mode := 0;
          if GWsIoctl(S, FIONBIO, @Mode) <> 0 then
            Exit(-1);
          if Mode = 1 then
            _WinFdSetFlags(AFd, Flags or WIN_FD_NONBLOCK)
          else
            _WinFdSetFlags(AFd, Flags and not WIN_FD_NONBLOCK);
        end;
      end;
  else
    SetLastError(ERROR_INVALID_PARAMETER);
    Result := -1;
  end;
end;

function signal(ASignum: Int32; AHandler: Pointer): Pointer;
begin
  Result := nil;
end;

{ Returns 0 or a getaddrinfo error code, as POSIX does (the code is a
  Winsock error rather than an EAI_* value). }
function getaddrinfo(ANode, AService: PChar; AHints: Pointer;
  ARes: Pointer): Int32;
begin
  if not WsReady() then
    Exit(WSANO_RECOVERY);
  Result := GWsGetAddrInfo(ANode, AService, AHints, ARes);
end;

procedure freeaddrinfo(AInfo: Pointer);
begin
  if (AInfo <> nil) and (GWsState = 1) then
    GWsFreeAddrInfo(AInfo);
end;

{ The Winsock events for POSIX events AEvents. }
function WsEventsOf(AEvents: Int16): Int16;
begin
  Result := 0;
  if (AEvents and POLLIN) <> 0 then
    Result := Result or WSA_POLLRDNORM;
  if (AEvents and POLLOUT) <> 0 then
    Result := Result or WSA_POLLWRNORM;
end;

{ The POSIX events for Winsock's AEvents. }
function PosixEventsOf(AEvents: Int16): Int16;
begin
  Result := 0;
  if (AEvents and (WSA_POLLRDNORM or WSA_POLLRDBAND)) <> 0 then
    Result := Result or POLLIN;
  if (AEvents and WSA_POLLWRNORM) <> 0 then
    Result := Result or POLLOUT;
  if (AEvents and WSA_POLLERR) <> 0 then
    Result := Result or POLLERR;
  if (AEvents and WSA_POLLHUP) <> 0 then
    Result := Result or POLLHUP;
  if (AEvents and WSA_POLLNVAL) <> 0 then
    Result := Result or POLLNVAL;
end;

{ A negative descriptor is skipped, as POSIX poll skips it; one that is not
  a socket is POLLNVAL at once, and the wait does not block. }
function poll(AFds: Pointer; ANFds: Int64; ATimeout: Int32): Int32;
var
  I, N, Invalid, Ready: Int;
  Fd: Int32;
  Flags: Int32;
  Entry, WEntry, WFds: Pointer;
  Rc: Int32;
  Timeout: Int32;
begin
  Invalid := 0;
  N := 0;
  if ANFds > 0 then
    WFds := _BlaiseGetMem(ANFds * WPFD_SIZE)
  else
    WFds := nil;
  for I := 0 to ANFds - 1 do
  begin
    Entry := AFds + I * PFD_SIZE;
    PInt16(Entry + 6)^ := 0;
    Fd := PInt32(Entry)^;
    if Fd < 0 then
      Continue;
    Flags := _WinFdFlags(Fd);
    if (Flags < 0) or ((Flags and WIN_FD_SOCKET) = 0) or (GWsState <> 1) then
    begin
      PInt16(Entry + 6)^ := POLLNVAL;
      Invalid := Invalid + 1;
      Continue;
    end;
    WEntry := WFds + N * WPFD_SIZE;
    PUInt64(WEntry)^ := UInt64(_WinHandleOfFd(Fd));
    PInt16(WEntry + 8)^ := WsEventsOf(PInt16(Entry + 4)^);
    PInt16(WEntry + 10)^ := 0;
    { the entry's index in AFds, in the padding after revents }
    PInt32(WEntry + 12)^ := Int32(I);
    N := N + 1;
  end;
  Timeout := ATimeout;
  if Invalid > 0 then
    Timeout := 0;
  if N = 0 then
  begin
    if WFds <> nil then
      _BlaiseFreeMem(WFds);
    if (Invalid = 0) and (Timeout <> 0) then
    begin
      if Timeout < 0 then
        WinSleep(INFINITE)
      else
        WinSleep(UInt32(Timeout));
    end;
    Exit(Invalid);
  end;
  Rc := GWsPoll(WFds, UInt32(N), Timeout);
  if Rc < 0 then
  begin
    _BlaiseFreeMem(WFds);
    Exit(-1);
  end;
  Ready := 0;
  for I := 0 to N - 1 do
  begin
    WEntry := WFds + I * WPFD_SIZE;
    Entry := AFds + Int64(PInt32(WEntry + 12)^) * PFD_SIZE;
    PInt16(Entry + 6)^ := PosixEventsOf(PInt16(WEntry + 10)^);
    if PInt16(Entry + 6)^ <> 0 then
      Ready := Ready + 1;
  end;
  _BlaiseFreeMem(WFds);
  Result := Ready + Invalid;
end;

end.
