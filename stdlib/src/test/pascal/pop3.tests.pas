{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for L5 Net.Pop3 (POP3 client, RFC 1939).  A MOCK POP3 server runs as a
  fiber on Net.Tcp inside the test-runner process:

    +OK greeting, +OK to USER/PASS, '+OK n size' to STAT, a dot-terminated
    (and dot-stuffed) message body to RETR, +OK to DELE, +OK to QUIT.

  The client-driving fiber asserts USER/PASS auth, STAT parse, RETR returns the
  dot-UNstuffed body, DELE, and QUIT.  Plaintext (internal linker).

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit Pop3.Tests;

interface

uses
  blaise.testing, SysUtils, Net.Tcp, Net.Pop3, Net.Mail.Reply,
  async.fibers, Net.Sockets;

type
  TPop3Tests = class(TTestCase)
  published
    procedure TestAuthStatRetrDeleQuit;
  end;

implementation

var
  GServer: TTcpServer;
  GHandler: IConnHandler;
  GPort: UInt16;
  GUserOk: Boolean;
  GPassOk: Boolean;
  GStatCount: Int;
  GStatSize: Int;
  GRetr: string;
  GDeleOk: Boolean;
  GQuitOk: Boolean;

type
  TMockPop3Handler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

procedure TMockPop3Handler.Handle(AConn: TTcpConn);
var
  Line, U: string;
begin
  AConn.Write('+OK POP3 mock ready' + CRLF);
  while AConn.ReadLine(Line) do
  begin
    U := UpperCase(Line);
    if Copy(U, 0, 4) = 'USER' then
      AConn.Write('+OK user accepted' + CRLF)
    else if Copy(U, 0, 4) = 'PASS' then
      AConn.Write('+OK mailbox ready' + CRLF)
    else if U = 'STAT' then
      AConn.Write('+OK 2 3200' + CRLF)
    else if Copy(U, 0, 4) = 'RETR' then
    begin
      AConn.Write('+OK 120 octets' + CRLF);
      AConn.Write('Subject: hello' + CRLF);
      AConn.Write('' + CRLF);
      AConn.Write('First body line' + CRLF);
      { a body line that itself is '.' must be dot-stuffed on the wire as '..' }
      AConn.Write('..' + CRLF);
      AConn.Write('Last line' + CRLF);
      AConn.Write('.' + CRLF);      { terminator }
    end
    else if Copy(U, 0, 4) = 'DELE' then
      AConn.Write('+OK deleted' + CRLF)
    else if U = 'QUIT' then
    begin
      AConn.Write('+OK bye' + CRLF);
      Break;
    end
    else
      AConn.Write('-ERR unknown' + CRLF);
  end;
end;

procedure ServerFiber(AArg: Pointer);
begin
  GServer.Serve(GHandler);
end;

procedure ClientFiber(AArg: Pointer);
var
  Cli: TPop3Client;
begin
  FiberSleep(2);
  Cli := TPop3Client.Create();
  if Cli.Connect('127.0.0.1', GPort) then
  begin
    GUserOk := Cli.User('alice');
    GPassOk := Cli.Pass('secret');
    Cli.Stat(GStatCount, GStatSize);
    Cli.Retr(1, GRetr);
    GDeleOk := Cli.Dele(1);
    GQuitOk := Cli.Quit();
  end;
  Cli.Free();
  GServer.Stop();
end;

procedure TPop3Tests.TestAuthStatRetrDeleQuit;
const
  PORT = 29601;
begin
  GServer := TTcpServer.Create(PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TMockPop3Handler.Create();
  GPort := PORT;
  GUserOk := False;
  GPassOk := False;
  GStatCount := -1;
  GStatSize := -1;
  GRetr := '';
  GDeleOk := False;
  GQuitOk := False;

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@ClientFiber, nil);
  RunScheduler();

  AssertTrue('USER accepted', GUserOk);
  AssertTrue('PASS accepted', GPassOk);
  AssertEquals('STAT count parsed', 2, GStatCount);
  AssertEquals('STAT size parsed', 3200, GStatSize);
  AssertTrue('RETR carried the subject header',
    Pos('Subject: hello', GRetr) >= 0);
  AssertTrue('RETR carried the first body line',
    Pos('First body line', GRetr) >= 0);
  AssertTrue('RETR carried the last body line',
    Pos('Last line', GRetr) >= 0);
  { the wire '..' line must be un-dot-stuffed back to a single '.' }
  AssertTrue('dot-unstuffed line present as .',
    Pos(#10 + '.' + #10, #10 + GRetr + #10) >= 0);
  AssertFalse('no double-dot leaked through', Pos('..', GRetr) >= 0);
  AssertTrue('DELE accepted', GDeleOk);
  AssertTrue('QUIT accepted', GQuitOk);

  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

initialization
  RegisterTest(TPop3Tests);

end.
