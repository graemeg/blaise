{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Outbound connections from a PLAIN program -- no fiber scheduler running.

  The fiber suites (NetTcp.Tests, HttpClient.Tests) dial only from inside a
  fiber and only by numeric IP, which hid two defects
  (BUG-20261106-http-client-plain-connect): a host NAME never resolved, and a
  non-blocking connect that reported EINPROGRESS was abandoned when no
  scheduler was there to wait for it.

    * TTcpDialTests  -- name resolution, connect by name and by IP, refused and
                        unresolvable targets, a whole HTTP GET against a
                        loopback server thread, and the read / connect
                        timeouts.  Loopback only.
    * TLiveNetTests  -- the same client against real hosts.  They need the
                        internet, so they run only when BLAISE_NET_TESTS=1 and
                        are ignored otherwise.

  Self-registers via the initialization section. }

unit TcpDial.Tests;

interface

uses
  blaise.testing, Classes, SysUtils, StrUtils,
  Net.Sockets, Net.Tcp, Net.Http.Client, async.fibers;

type
  TTcpDialTests = class(TTestCase)
  published
    procedure TestResolveLocalhost;
    procedure TestResolveNumericIPv4;
    procedure TestResolveUnknownHost;
    procedure TestConnectByIp_NoScheduler;
    procedure TestConnectByName_NoScheduler;
    procedure TestConnectRefused_NoScheduler;
    procedure TestConnectUnknownHost_NoScheduler;
    procedure TestHttpGetByName_NoScheduler;
    procedure TestHttpReadTimeout_NoScheduler;
    procedure TestTcpReadTimeout_NoScheduler;
  end;

  TLiveNetTests = class(TTestCase)
  published
    procedure TestLive_HttpByIp;
    procedure TestLive_HttpByName;
  end;

  { Accepts ONE connection on a listening socket, reads the request head, and
    answers with a fixed HTTP response. }
  TOneShotHttpThread = class(TThread)
  private
    FListenFd: Int;
    FRequest: string;
  protected
    procedure Execute; override;
  public
    constructor Create(AListenFd: Int);
    property Request: string read FRequest;
  end;

implementation

const
  TIMEOUT_MS = 300;

function ElapsedMs(AStartNs: Int64): Int64;
begin
  Result := (MonotonicNowNs() - AStartNs) div 1000000;
end;

{ A port with nothing listening: bind an ephemeral one, then close it. }
function ClosedPort: UInt16;
var
  Fd: Int;
begin
  Fd := TcpListenEphemeral(INADDR_LOOPBACK, 1, Result);
  Close(Fd);
end;

constructor TOneShotHttpThread.Create(AListenFd: Int);
begin
  FListenFd := AListenFd;
  FRequest := '';
  inherited Create(False);
end;

procedure TOneShotHttpThread.Execute;
var
  Fd: Int;
  Chunk: string;
begin
  Fd := AcceptConn(FListenFd);
  if Fd < 0 then
    Exit;
  while Pos(#13#10#13#10, FRequest) < 0 do
  begin
    Chunk := RecvString(Fd, 4096);
    if Chunk = '' then
      Break;
    FRequest := FRequest + Chunk;
  end;
  SendAll(Fd, 'HTTP/1.1 200 OK'#13#10'Content-Length: 5'#13#10 +
    'Connection: close'#13#10#13#10'plain');
  Close(Fd);
end;

{ ---- resolution ------------------------------------------------------------ }

procedure TTcpDialTests.TestResolveLocalhost;
var
  Addrs: TResolvedAddrs;
begin
  Addrs := ResolveHost('localhost', 80);
  AssertTrue('localhost resolves to at least one address', Length(Addrs) > 0);
  AssertTrue('a socket address is returned', Length(Addrs[0].Addr) >= 16);
end;

procedure TTcpDialTests.TestResolveNumericIPv4;
var
  Addrs: TResolvedAddrs;
begin
  Addrs := ResolveHost('127.0.0.1', 8080);
  AssertEquals('one address for a literal', 1, Length(Addrs));
  AssertEquals('IPv4 family', AF_INET, Addrs[0].Family);
end;

procedure TTcpDialTests.TestResolveUnknownHost;
begin
  { .invalid is reserved (RFC 2606): it never resolves. }
  AssertEquals('no addresses', 0, Length(ResolveHost('no-such-host.invalid', 80)));
end;

{ ---- connect ---------------------------------------------------------------- }

procedure TTcpDialTests.TestConnectByIp_NoScheduler;
var
  L, S: Int;
  Port: UInt16;
  Cli: TTcpClient;
  Conn: TTcpConn;
begin
  L := TcpListenEphemeral(INADDR_LOOPBACK, 4, Port);
  AssertTrue('listen', L >= 0);
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('127.0.0.1', Port);
  Cli.Free();
  AssertTrue('connected by IP', Conn <> nil);
  if Conn <> nil then
  begin
    S := AcceptConn(L);
    AssertTrue('server accepted', S >= 0);
    SendAll(S, 'hello');
    AssertEquals('bytes from the server', 'hello', Conn.ReadFull(5));
    Close(S);
    Conn.Free();
  end;
  Close(L);
end;

procedure TTcpDialTests.TestConnectByName_NoScheduler;
var
  L, S: Int;
  Port: UInt16;
  Cli: TTcpClient;
  Conn: TTcpConn;
begin
  { The server listens on 127.0.0.1 only.  'localhost' may resolve to ::1
    first, which is refused -- the client must go on to the next address. }
  L := TcpListenEphemeral(INADDR_LOOPBACK, 4, Port);
  AssertTrue('listen', L >= 0);
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('localhost', Port);
  Cli.Free();
  AssertTrue('connected by name', Conn <> nil);
  if Conn <> nil then
  begin
    S := AcceptConn(L);
    AssertTrue('server accepted', S >= 0);
    AssertTrue('client write', Conn.Write('ping'));
    AssertEquals('bytes from the client', 'ping', RecvString(S, 16));
    Close(S);
    Conn.Free();
  end;
  Close(L);
end;

procedure TTcpDialTests.TestConnectRefused_NoScheduler;
var
  Cli: TTcpClient;
  Conn: TTcpConn;
begin
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('127.0.0.1', ClosedPort());
  Cli.Free();
  AssertTrue('refused connection is nil', Conn = nil);
end;

procedure TTcpDialTests.TestConnectUnknownHost_NoScheduler;
var
  Cli: TTcpClient;
  Conn: TTcpConn;
begin
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('no-such-host.invalid', 80);
  Cli.Free();
  AssertTrue('unresolvable host is nil', Conn = nil);
end;

{ ---- HTTP from a plain program ---------------------------------------------- }

procedure TTcpDialTests.TestHttpGetByName_NoScheduler;
var
  L: Int;
  Port: UInt16;
  Srv: TOneShotHttpThread;
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  L := TcpListenEphemeral(INADDR_LOOPBACK, 4, Port);
  AssertTrue('listen', L >= 0);
  Srv := TOneShotHttpThread.Create(L);
  Cli := THttpClient.Create();
  Resp := Cli.Get('http://localhost:' + IntToStr(Port) + '/x');
  AssertTrue('response', Resp <> nil);
  if Resp <> nil then
  begin
    AssertEquals('status', 200, Resp.Status);
    AssertEquals('body', 'plain', Resp.Body);
    Resp.Free();
  end;
  Cli.Free();
  Srv.WaitFor();
  AssertTrue('request line seen by the server',
    StartsStr('GET /x HTTP/1.1', Srv.Request));
  Srv.Free();
  Close(L);
end;

procedure TTcpDialTests.TestHttpReadTimeout_NoScheduler;
var
  L: Int;
  Port: UInt16;
  Cli: THttpClient;
  Resp: THttpClientResponse;
  T0, Ms: Int64;
begin
  { Nothing ever accepts: the kernel completes the handshake from the backlog,
    the request is buffered, and no answer comes. }
  L := TcpListenEphemeral(INADDR_LOOPBACK, 4, Port);
  AssertTrue('listen', L >= 0);
  Cli := THttpClient.Create();
  Cli.ReadTimeoutMs := TIMEOUT_MS;
  T0 := MonotonicNowNs();
  Resp := Cli.Get('http://127.0.0.1:' + IntToStr(Port) + '/');
  Ms := ElapsedMs(T0);
  AssertTrue('no response from a silent server', Resp = nil);
  AssertTrue('gave up after the timeout (' + IntToStr(Ms) + ' ms)',
    (Ms >= TIMEOUT_MS - 50) and (Ms < 5000));
  Cli.Free();
  Close(L);
end;

procedure TTcpDialTests.TestTcpReadTimeout_NoScheduler;
var
  L: Int;
  Port: UInt16;
  Cli: TTcpClient;
  Conn: TTcpConn;
  T0, Ms: Int64;
begin
  L := TcpListenEphemeral(INADDR_LOOPBACK, 4, Port);
  AssertTrue('listen', L >= 0);
  Cli := TTcpClient.Create();
  Conn := Cli.Connect('127.0.0.1', Port);
  Cli.Free();
  AssertTrue('connected', Conn <> nil);
  if Conn <> nil then
  begin
    Conn.ReadTimeoutMs := TIMEOUT_MS;
    T0 := MonotonicNowNs();
    AssertEquals('nothing read', '', Conn.Read(16));
    Ms := ElapsedMs(T0);
    AssertTrue('read gave up after the timeout (' + IntToStr(Ms) + ' ms)',
      (Ms >= TIMEOUT_MS - 50) and (Ms < 5000));
    Conn.Free();
  end;
  Close(L);
end;

{ ---- live network (opt-in) -------------------------------------------------- }

function LiveNetEnabled: Boolean;
begin
  Result := GetEnvironmentVariable('BLAISE_NET_TESTS') = '1';
end;

procedure TLiveNetTests.TestLive_HttpByIp;
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  if not LiveNetEnabled() then begin Ignore('set BLAISE_NET_TESTS=1'); Exit; end;
  Cli := THttpClient.Create();
  Cli.MaxRedirects := 0;
  Cli.ConnectTimeoutMs := 10000;
  Cli.ReadTimeoutMs := 30000;
  Resp := Cli.Get('http://1.1.1.1/');
  AssertTrue('response', Resp <> nil);
  if Resp <> nil then
  begin
    AssertEquals('redirect to https', 301, Resp.Status);
    Resp.Free();
  end;
  Cli.Free();
end;

procedure TLiveNetTests.TestLive_HttpByName;
var
  Cli: THttpClient;
  Resp: THttpClientResponse;
begin
  if not LiveNetEnabled() then begin Ignore('set BLAISE_NET_TESTS=1'); Exit; end;
  Cli := THttpClient.Create();
  Cli.MaxRedirects := 0;
  Cli.ConnectTimeoutMs := 10000;
  Cli.ReadTimeoutMs := 30000;
  Resp := Cli.Get('http://example.com/');
  AssertTrue('response', Resp <> nil);
  if Resp <> nil then
  begin
    AssertEquals('status', 200, Resp.Status);
    Resp.Free();
  end;
  Cli.Free();
end;

initialization
  RegisterTest(TTcpDialTests);
  RegisterTest(TLiveNetTests);

end.
