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
