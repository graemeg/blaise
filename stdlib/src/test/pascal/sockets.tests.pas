{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Net.Sockets: IPv4 address helpers and a loopback TCP round-trip.
  Self-registers via the initialization section. }

unit Sockets.Tests;

interface

uses
  blaise.testing, Classes, SysUtils, Net.Sockets;

type
  TSocketsTests = class(TTestCase)
  published
    procedure TestIPv4_Loopback;
    procedure TestIPv4_AllInterfaces;
    procedure TestParseIPv4_Valid;
    procedure TestParseIPv4_Invalid;
    procedure TestTcpRoundTrip_Local;
    procedure TestAcceptConn_BlockingFromNonBlockingListener;
    procedure TestSendAll_NonBlockingFullBuffer;
  end;

  { Reads AFd until EOF and keeps every byte, so a test can send more than the
    kernel buffers without deadlocking the sending thread. }
  TDrainThread = class(TThread)
  private
    FFd: Integer;
    FReceived: string;
  protected
    procedure Execute; override;
  public
    constructor Create(AFd: Integer);
    property Received: string read FReceived;
  end;

implementation

procedure TSocketsTests.TestIPv4_Loopback;
begin
  { IPv4(127,0,0,1) must equal the canonical INADDR_LOOPBACK constant. }
  AssertEquals('loopback', Int64(INADDR_LOOPBACK), Int64(IPv4(127, 0, 0, 1)));
end;

procedure TSocketsTests.TestIPv4_AllInterfaces;
begin
  AssertEquals('any', Int64(INADDR_ANY), Int64(IPv4(0, 0, 0, 0)));
end;

procedure TSocketsTests.TestParseIPv4_Valid;
var A: UInt32;
begin
  AssertTrue('parse ok', ParseIPv4('127.0.0.1', A));
  AssertEquals('value', Int64(IPv4(127, 0, 0, 1)), Int64(A));
  AssertTrue('parse 2', ParseIPv4('192.168.1.255', A));
  AssertEquals('value 2', Int64(IPv4(192, 168, 1, 255)), Int64(A));
end;

procedure TSocketsTests.TestParseIPv4_Invalid;
var A: UInt32;
begin
  AssertFalse('too few octets', ParseIPv4('1.2.3', A));
  AssertFalse('octet > 255',    ParseIPv4('1.2.3.256', A));
  AssertFalse('trailing dot',   ParseIPv4('1.2.3.4.', A));
  AssertFalse('letters',        ParseIPv4('a.b.c.d', A));
  AssertFalse('empty',          ParseIPv4('', A));
end;

{ A full loopback round-trip in one process: listen, connect, accept, then
  send a message client->server and read it back on the server side. }
procedure TSocketsTests.TestTcpRoundTrip_Local;
const
  PORT = 28765;
  MSG  = 'hello over tcp';
var
  Srv, Cli, Conn: Integer;
  Received: string;
begin
  Srv := TcpListenLocal(PORT, 8);
  AssertTrue('listen', Srv >= 0);

  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);

  Conn := AcceptConn(Srv);
  AssertTrue('accept', Conn >= 0);

  AssertTrue('send', SendAll(Cli, MSG));

  Received := RecvString(Conn, 256);
  AssertEquals('payload', MSG, Received);

  Close(Conn);
  Close(Cli);
  Close(Srv);
end;

constructor TDrainThread.Create(AFd: Integer);
begin
  FFd := AFd;
  FReceived := '';
  inherited Create(False);
end;

procedure TDrainThread.Execute;
var
  SB: TStringBuilder;
  Chunk: string;
begin
  SB := TStringBuilder.Create();
  repeat
    Chunk := RecvString(FFd, 65536);
    SB.Append(Chunk);
  until Chunk = '';
  FReceived := SB.ToString();
  SB.Free();
end;

{ A distinctive, non-repeating-at-a-glance payload: a truncated or reordered
  transfer cannot compare equal. }
function PatternBytes(ACount: Integer): string;
var
  SB: TStringBuilder;
  I: Integer;
begin
  SB := TStringBuilder.Create();
  for I := 0 to ACount - 1 do
    SB.AppendByte(Byte((I * 7 + I div 251) mod 256));
  Result := SB.ToString();
  SB.Free();
end;

{ On macOS and the BSDs accept(2) copies O_NONBLOCK from the listening socket;
  Linux does not.  AcceptConn hands back a blocking fd on every platform, so a
  server that made its listener non-blocking (to poll for connections) still
  gets the blocking connection its read and write loops assume. }
procedure TSocketsTests.TestAcceptConn_BlockingFromNonBlockingListener;
const
  PORT = 28766;
var
  Srv, Cli, Conn, Tries: Integer;
begin
  Srv := TcpListenLocal(PORT, 8);
  AssertTrue('listen', Srv >= 0);
  MakeNonBlocking(Srv);
  AssertTrue('listener non-blocking', IsNonBlocking(Srv));

  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);
  { The listener is non-blocking, and the handshake may not have reached the
    accept queue the instant connect returns, so poll briefly. }
  Tries := 0;
  Conn := AcceptConn(Srv);
  while (Conn < 0) and (Tries < 1000) do
  begin
    Sleep(1);
    Tries := Tries + 1;
    Conn := AcceptConn(Srv);
  end;
  AssertTrue('accept', Conn >= 0);
  AssertFalse('accepted connection is blocking', IsNonBlocking(Conn));
  AssertTrue('listener still non-blocking', IsNonBlocking(Srv));

  Close(Conn);
  Close(Cli);
  Close(Srv);
end;

{ SendAll on a NON-blocking socket must still deliver every byte.  4 MB is far
  more than a loopback send buffer, so send(2) reports EAGAIN part-way; that
  means "try again", not failure.  The socket's own mode is left as found. }
procedure TSocketsTests.TestSendAll_NonBlockingFullBuffer;
const
  PORT = 28767;
  SIZE = 4 * 1024 * 1024;
var
  Srv, Cli, Conn: Integer;
  Payload: string;
  Drain: TDrainThread;
begin
  Srv := TcpListenLocal(PORT, 8);
  AssertTrue('listen', Srv >= 0);
  Cli := TcpConnectLocal(PORT);
  AssertTrue('connect', Cli >= 0);
  Conn := AcceptConn(Srv);
  AssertTrue('accept', Conn >= 0);

  Payload := PatternBytes(SIZE);
  MakeNonBlocking(Cli);
  Drain := TDrainThread.Create(Conn);
  AssertTrue('SendAll delivers a body larger than the send buffer',
    SendAll(Cli, Payload));
  AssertTrue('socket mode restored', IsNonBlocking(Cli));
  Shutdown(Cli, SHUT_WR);
  Drain.WaitFor();

  AssertEquals('byte count', SIZE, Length(Drain.Received));
  AssertTrue('every byte intact', Drain.Received = Payload);

  Drain := nil;
  Close(Conn);
  Close(Cli);
  Close(Srv);
end;

initialization
  RegisterTest(TSocketsTests);

end.
