{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - POSIX TCP sockets (IPv4).

  A thin layer over the libc sockets API (cf. java.net / System.Net.Sockets).
  Sockets are plain file descriptors (an Integer); a negative value means error.

  Two layers:

    * raw bindings — Socket / Bind / Listen / Accept / Connect / Recv / Send /
      CloseSocket / Shutdown / SetSockOpt / Htons.  These map 1:1 onto libc.

    * helpers — TcpListen / TcpListenLocal (server), TcpConnect (client),
      SendAll / RecvString (whole-buffer I/O as Blaise strings),
      MakeNonBlocking, and IgnoreSigPipe.

  IPv4 only, no TLS — suitable for a localhost service or a plain TCP server.
  Strings are treated as raw bytes for I/O.

  --- Why this binds libc (and why that is the normal choice) ---

  Opening a socket is not a computation; it is a request to the OS kernel.  A
  userspace process cannot touch the network card, allocate a port, or run TCP
  state itself — only the kernel can.  The single doorway from a process into
  the kernel is the CPU's `syscall` instruction, and libc (glibc on Linux) is
  the canonical wrapper around those syscalls: it knows the syscall numbers and
  the register ABI per architecture, handles errno and EINTR restarts, and
  gives each call a stable C name (socket/bind/recv/...).  `external name
  'socket'` simply links to that libc symbol.  This is why nearly everything on
  Linux — the FPC RTL, Python, Node, even the JVM — goes through libc.

  Every networking stack is the same three layers; only the middle "shim"
  differs by who wrote it:

    protocol logic (HTTP/WS/crypto)  - pure Pascal here, pure Java in the JDK,
                                       pure Pascal in Indy/Synapse
    socket abstraction               - this unit; Indy's TIdStack; the JDK's
                                       sun.nio.ch native methods
    OS doorway                       - libc bindings (us, Indy, FPC, Synapse)
                                       OR hand-written C in a VM (Java JNI ->
                                       still libc/Winsock underneath)
    kernel                           - syscalls (fixed; nobody reimplements it)

  Java is NOT libc-free: java.net.Socket calls `native` methods implemented in
  C inside the JVM, which call socket()/bind()/recv() in libc exactly as we do.
  Its portability comes from writing that C glue once per OS, not from avoiding
  libc.  A truly "pure Pascal" version would replace libc's job with our own
  per-arch `syscall` assembly stubs (the route Go takes) — that removes the
  libc dependency but not the kernel boundary, and trades a stable cross-OS C
  ABI for per-arch/per-OS assembly we would then maintain.  For a single Linux
  target it is a day or two of work; as a portability strategy it is MORE work
  than the per-platform binding layer noted at the PORTING BOUNDARY below. }

unit Net.Sockets;

interface

{ PORTING BOUNDARY (resolved for Linux + FreeBSD) — the OS-divergent socket
  constants and the sockaddr_in fill are supplied by the per-target
  rtl.platform.layout.<os> unit (the `_So*`/`_SockAddrIn4Fill` seam), chosen
  at link time by the resolved --target, so this unit stays IFDEF-free.
  Still pending here:
    * Windows: a separate Winsock backend (ws2_32, WSAStartup, closesocket,
      SOCKET handles, WSAGetLastError).
  The helper API (TcpListen*/TcpConnect*/AcceptConn/RecvString/SendAll/Close/
  MakeNonBlocking/FillSockAddr/IgnoreSigPipe) is the stable surface — callers
  never touch raw constants — so further ports change only the seam, not
  consumers. }

const
  { address families / socket types (identical on Linux and the BSDs) }
  AF_INET     = 2;
  SOCK_STREAM = 1;

  { shutdown(2) how }
  SHUT_RD   = 0;
  SHUT_WR   = 1;
  SHUT_RDWR = 2;

  { special IPv4 addresses, in network byte order }
  INADDR_ANY      = 0;          { 0.0.0.0  — all interfaces }
  INADDR_LOOPBACK = 16777343;   { 127.0.0.1 = htonl($7F000001) }

{ OS-divergent socket constants, resolved by the linked
  rtl.platform.layout.<os> seam (e.g. SOL_SOCKET is 1 on Linux but $FFFF on
  FreeBSD).  Functions rather than consts so ONE compiled unit serves every
  target. }
function SOL_SOCKET: Integer;   external name '_SolSocket';
function SO_REUSEADDR: Integer; external name '_SoReuseAddr';
{ SO_REUSEPORT lets several sockets bind the SAME address:port; the kernel
  load-balances incoming connections across them.  This is how NGINX/Envoy —
  and the fiber server's per-worker-listener path (design [#listener-scaling])
  — eliminate the single-acceptor bottleneck. }
function SO_REUSEPORT: Integer; external name '_SoReusePort';
{ send(2) flag: a write to a peer-closed socket returns EPIPE instead of
  raising SIGPIPE (whose default action terminates the process). }
function MSG_NOSIGNAL: Integer; external name '_MsgNoSignal';

type
  { struct sockaddr_in — exactly 16 bytes on Linux and FreeBSD.  The first two
    bytes differ per OS (Linux: u16 sin_family; BSD: u8 sin_len + u8
    sin_family), so build it with FillSockAddr below rather than assigning
    sin_family directly.  sin_port and sin_addr are in network byte order. }
  TSockAddrIn = record
    sin_family: UInt16;
    sin_port:   UInt16;
    sin_addr:   UInt32;
    sin_zero:   array[0..7] of Byte;
  end;

{ --- raw libc bindings --- }

function Socket(ADomain, AType, AProtocol: Integer): Integer;
  external name 'socket';
function Bind(AFd: Integer; AAddr: Pointer; AAddrLen: Integer): Integer;
  external name 'bind';
function Listen(AFd, ABacklog: Integer): Integer;
  external name 'listen';
function Accept(AFd: Integer; AAddr: Pointer; AAddrLen: Pointer): Integer;
  external name 'accept';
function Connect(AFd: Integer; AAddr: Pointer; AAddrLen: Integer): Integer;
  external name 'connect';
function SetSockOpt(AFd, ALevel, AOptName: Integer; AOptVal: Pointer; AOptLen: Integer): Integer;
  external name 'setsockopt';
function Recv(AFd: Integer; ABuf: Pointer; ALen: Int64; AFlags: Integer): Int64;
  external name 'recv';
function Send(AFd: Integer; ABuf: Pointer; ALen: Int64; AFlags: Integer): Int64;
  external name 'send';
function CloseSocket(AFd: Integer): Integer;
  external name 'close';
function Shutdown(AFd, AHow: Integer): Integer;
  external name 'shutdown';
function Htons(AHostShort: UInt16): UInt16;
  external name 'htons';
function Ntohs(ANetShort: UInt16): UInt16;
  external name 'ntohs';
function GetSockName(AFd: Integer; AAddr: Pointer; AAddrLen: Pointer): Integer;
  external name 'getsockname';

{ --- address helpers --- }

{ Build a network-order IPv4 address from its four octets, e.g.
  IPv4(192,168,0,1).  Suitable for the AAddr argument below. }
function IPv4(A, B, C, D: Byte): UInt32;

{ Parse a dotted-quad string ("127.0.0.1") into a network-order IPv4 address.
  Returns True on success.  Does not resolve host names (no DNS); pass a
  literal IP, or use INADDR_ANY / INADDR_LOOPBACK. }
function ParseIPv4(const AText: string; out AAddr: UInt32): Boolean;

{ Fill AAddr for AF_INET with AIp (network order) and APort (HOST order) via
  the per-OS layout seam — the only correct way to build a TSockAddrIn (see
  the type's note on the OS-divergent first two bytes). }
procedure FillSockAddr(var AAddr: TSockAddrIn; AIp: UInt32; APort: UInt16);

{ --- server / client helpers --- }

{ Open a listening TCP server socket on AAddr (network-order IPv4, e.g.
  INADDR_LOOPBACK, INADDR_ANY, or IPv4(...)) and APort.  Sets SO_REUSEADDR.
  Returns the listening fd, or -1 on failure. }
function TcpListen(AAddr: UInt32; APort: UInt16; ABacklog: Integer): Integer;

{ Convenience: TcpListen bound to 127.0.0.1 only (no external exposure). }
function TcpListenLocal(APort: UInt16; ABacklog: Integer): Integer;

{ Like TcpListen but ALSO sets SO_REUSEPORT, so several workers may each open
  their own listening socket on the same AAddr:APort and let the kernel
  load-balance accepts across them (design [#listener-scaling]).  Returns the
  listening fd, or -1 on failure. }
function TcpListenReusePort(AAddr: UInt32; APort: UInt16; ABacklog: Integer): Integer;

{ Open a listening socket on AAddr with an OS-chosen ephemeral port (bind to
  port 0), then report the actual port the kernel assigned in APort (host byte
  order).  Used by the FTP server's PASV path: the server needs a fresh data
  port per transfer and must tell the client which one.  Returns the listening
  fd, or -1 on failure (APort then 0). }
function TcpListenEphemeral(AAddr: UInt32; ABacklog: Integer; out APort: UInt16): Integer;

{ Connect to AAddr:APort (AAddr is a network-order IPv4).  Returns the
  connected fd, or -1 on failure. }
function TcpConnect(AAddr: UInt32; APort: UInt16): Integer;

{ Convenience: connect to 127.0.0.1:APort. }
function TcpConnectLocal(APort: UInt16): Integer;

{ Accept the next pending connection on a listening socket.  Returns the
  connected fd, or -1 (e.g. on a non-blocking socket with nothing waiting). }
function AcceptConn(AListenFd: Integer): Integer;

{ Receive up to AMaxBytes from AFd and return them as a string (raw bytes).
  Returns '' on EOF or error.  A short read is normal for a stream socket;
  callers needing a fixed amount must loop. }
function RecvString(AFd: Integer; AMaxBytes: Integer): string;

{ Close a socket fd. }
procedure Close(AFd: Integer);

{ Make AFd non-blocking (accept/recv return immediately when nothing waits). }
procedure MakeNonBlocking(AFd: Integer);

{ Send the whole string, looping until every byte is written.  Uses
  MSG_NOSIGNAL so a dead peer yields a False result rather than SIGPIPE.
  Returns True on success. }
function SendAll(AFd: Integer; const S: string): Boolean;

{ Convert ACount bytes at ABuf into a Blaise string (raw bytes). }
function BytesToString(ABuf: Pointer; ACount: Integer): string;

{ Ignore SIGPIPE process-wide so a write to a closed socket cannot terminate
  the process.  Call once at startup. }
procedure IgnoreSigPipe;

implementation

uses
  StrUtils;

const
  F_SETFL    = 4;
  SIGPIPE    = 13;
  SIG_IGN    = 1;      { (void*)1 }

{ fcntl is C-VARIADIC: on Apple arm64 the third argument must travel the
  variadic way (on the stack), or F_SETFL never sees O_NONBLOCK. }
function c_fcntl(AFd, ACmd: Integer): Integer; varargs; external name 'fcntl';
function c_signal(ASignum: Integer; AHandler: Pointer): Pointer; external name 'signal';

{ Per-OS layout seam: O_NONBLOCK (Linux $800, FreeBSD 4) and the sockaddr_in
  fill (the OS-divergent first two bytes). }
function _ONonBlock: Integer; external name '_ONonBlock';
procedure _SockAddrIn4Fill(P: Pointer; APortN: UInt16; AAddrN: UInt32);
  external name '_SockAddrIn4Fill';

function IPv4(A, B, C, D: Byte): UInt32;
begin
  { network byte order: a.b.c.d on the wire == a | b<<8 | c<<16 | d<<24 as a
    little-endian UInt32 (verified: IPv4(127,0,0,1) = INADDR_LOOPBACK). }
  Result := UInt32(A) or (UInt32(B) shl 8) or (UInt32(C) shl 16) or (UInt32(D) shl 24);
end;

function ParseIPv4(const AText: string; out AAddr: UInt32): Boolean;
var
  Octets: array[0..3] of Integer;
  OctIdx, Val, Digits, I, N: Integer;
  Ch: Byte;
begin
  Result := False;
  AAddr := 0;
  OctIdx := 0;
  Val := 0;
  Digits := 0;
  N := Length(AText);
  for I := 0 to N - 1 do
  begin
    Ch := Byte(AText[I]);
    if (Ch >= 48) and (Ch <= 57) then          { 0-9 }
    begin
      Val := Val * 10 + (Ch - 48);
      Digits := Digits + 1;
      if Val > 255 then Exit;
    end
    else if Ch = 46 then                        { '.' }
    begin
      if (Digits = 0) or (OctIdx >= 3) then Exit;
      Octets[OctIdx] := Val;
      OctIdx := OctIdx + 1;
      Val := 0;
      Digits := 0;
    end
    else
      Exit;                                      { invalid character }
  end;
  if (Digits = 0) or (OctIdx <> 3) then Exit;    { need exactly four octets }
  Octets[3] := Val;
  AAddr := IPv4(Octets[0], Octets[1], Octets[2], Octets[3]);
  Result := True;
end;

procedure FillSockAddr(var AAddr: TSockAddrIn; AIp: UInt32; APort: UInt16);
begin
  _SockAddrIn4Fill(@AAddr, Htons(APort), AIp);
end;

function TcpListen(AAddr: UInt32; APort: UInt16; ABacklog: Integer): Integer;
var
  Fd, One: Integer;
  SA: TSockAddrIn;
begin
  Fd := Socket(AF_INET, SOCK_STREAM, 0);
  if Fd < 0 then
  begin
    Result := -1;
    Exit;
  end;

  One := 1;
  SetSockOpt(Fd, SOL_SOCKET(), SO_REUSEADDR(), @One, 4);

  FillSockAddr(SA, AAddr, APort);
  if Bind(Fd, @SA, 16) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  if Listen(Fd, ABacklog) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  Result := Fd;
end;

function TcpListenLocal(APort: UInt16; ABacklog: Integer): Integer;
begin
  Result := TcpListen(INADDR_LOOPBACK, APort, ABacklog);
end;

function TcpListenReusePort(AAddr: UInt32; APort: UInt16; ABacklog: Integer): Integer;
var
  Fd, One: Integer;
  SA: TSockAddrIn;
begin
  Fd := Socket(AF_INET, SOCK_STREAM, 0);
  if Fd < 0 then
  begin
    Result := -1;
    Exit;
  end;

  One := 1;
  SetSockOpt(Fd, SOL_SOCKET(), SO_REUSEADDR(), @One, 4);
  SetSockOpt(Fd, SOL_SOCKET(), SO_REUSEPORT(), @One, 4);

  FillSockAddr(SA, AAddr, APort);
  if Bind(Fd, @SA, 16) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  if Listen(Fd, ABacklog) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  Result := Fd;
end;

function TcpListenEphemeral(AAddr: UInt32; ABacklog: Integer; out APort: UInt16): Integer;
var
  Fd, One: Integer;
  SA: TSockAddrIn;
  Bound: TSockAddrIn;
  Len: Integer;
begin
  APort := 0;
  Fd := Socket(AF_INET, SOCK_STREAM, 0);
  if Fd < 0 then
  begin
    Result := -1;
    Exit;
  end;

  One := 1;
  SetSockOpt(Fd, SOL_SOCKET(), SO_REUSEADDR(), @One, 4);

  FillSockAddr(SA, AAddr, 0);            { port 0 => OS picks an ephemeral port }
  if Bind(Fd, @SA, 16) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  if Listen(Fd, ABacklog) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  { read back the actual port the kernel assigned }
  Len := 16;
  if GetSockName(Fd, @Bound, @Len) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  APort := Ntohs(Bound.sin_port);
  Result := Fd;
end;

function TcpConnect(AAddr: UInt32; APort: UInt16): Integer;
var
  Fd: Integer;
  SA: TSockAddrIn;
begin
  Fd := Socket(AF_INET, SOCK_STREAM, 0);
  if Fd < 0 then
  begin
    Result := -1;
    Exit;
  end;
  FillSockAddr(SA, AAddr, APort);
  if Connect(Fd, @SA, 16) <> 0 then
  begin
    CloseSocket(Fd);
    Result := -1;
    Exit;
  end;
  Result := Fd;
end;

function TcpConnectLocal(APort: UInt16): Integer;
begin
  Result := TcpConnect(INADDR_LOOPBACK, APort);
end;

function AcceptConn(AListenFd: Integer): Integer;
begin
  Result := Accept(AListenFd, nil, nil);
end;

function RecvString(AFd: Integer; AMaxBytes: Integer): string;
var
  Buf: Pointer;
  N: Int64;
begin
  if AMaxBytes <= 0 then
  begin
    Result := '';
    Exit;
  end;
  Buf := GetMem(AMaxBytes);
  N := Recv(AFd, Buf, AMaxBytes, 0);
  if N > 0 then
    Result := BytesToString(Buf, Integer(N))
  else
    Result := '';
  FreeMem(Buf);
end;

procedure Close(AFd: Integer);
begin
  CloseSocket(AFd);
end;

procedure MakeNonBlocking(AFd: Integer);
begin
  if AFd >= 0 then
    c_fcntl(AFd, F_SETFL, _ONonBlock());
end;

function SendAll(AFd: Integer; const S: string): Boolean;
var
  Total, N: Integer;
  P: PChar;
begin
  Total := Length(S);
  if Total = 0 then
  begin
    Result := True;
    Exit;
  end;
  P := PChar(S);
  while Total > 0 do
  begin
    N := Send(AFd, P, Total, MSG_NOSIGNAL());
    if N <= 0 then
    begin
      Result := False;
      Exit;
    end;
    P := P + N;
    Total := Total - N;
  end;
  Result := True;
end;

function BytesToString(ABuf: Pointer; ACount: Integer): string;
var
  P: PChar;
  I: Integer;
  SB: TStringBuilder;
begin
  if ACount <= 0 then
  begin
    Result := '';
    Exit;
  end;
  P := ABuf;
  SB := TStringBuilder.Create();
  for I := 0 to ACount - 1 do
    SB.AppendByte(Byte(P[I]));
  Result := SB.ToString();
  SB.Free();
end;

procedure IgnoreSigPipe;
begin
  c_signal(SIGPIPE, Pointer(SIG_IGN));
end;

end.
