{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for L5 Net.Imap (IMAP4rev1 client, core subset).  A MOCK IMAP server
  runs as a fiber on Net.Tcp inside the test-runner process, speaking tagged
  responses:

    * OK greeting; tagged OK to LOGIN; SELECT emits '* n EXISTS'/'* n RECENT'
    then tagged OK; FETCH emits a literal-octet-count body then tagged OK;
    SEARCH emits '* SEARCH ...'; LOGOUT emits '* BYE' then tagged OK.

  The client-driving fiber asserts LOGIN tagged-OK, SELECT parses EXISTS,
  FETCH parses the literal body, SEARCH parses ids, and LOGOUT.  Plaintext
  (internal linker).

  NATIVE BACKEND ONLY.  Self-registers via the initialization section. }

unit Imap.Tests;

interface

uses
  blaise.testing, SysUtils, Net.Tcp, Net.Imap, Net.Mail.Reply,
  async.fibers, Net.Sockets, Generics.Collections;

type
  TImapTests = class(TTestCase)
  published
    procedure TestLoginSelectFetchSearchLogout;
  end;

implementation

const
  LITERAL_BODY = 'Subject: Test' + CRLF + CRLF + 'Hello IMAP body';

var
  GServer: TTcpServer;
  GHandler: IConnHandler;
  GPort: UInt16;
  GLoginOk: Boolean;
  GSelectOk: Boolean;
  GExists: Int;
  GFetchOk: Boolean;
  GFetchBody: string;
  GSearchOk: Boolean;
  GSearchCount: Int;
  GSearchFirst: Int;
  GLogoutOk: Boolean;

type
  TMockImapHandler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

{ Extract the tag (first token) of an IMAP command line. }
function TagOf(const ALine: string): string;
var
  I, Len: Int;
begin
  Result := '';
  Len := Length(ALine);
  I := 0;
  while (I < Len) and (Byte(ALine[I]) <> 32) do
    I := I + 1;
  Result := Copy(ALine, 0, I);
end;

procedure TMockImapHandler.Handle(AConn: TTcpConn);
var
  Line, U, Tag: string;
begin
  AConn.Write('* OK [CAPABILITY IMAP4rev1] mock ready' + CRLF);
  while AConn.ReadLine(Line) do
  begin
    Tag := TagOf(Line);
    U := UpperCase(Line);
    if Pos(' LOGIN ', U) >= 0 then
      AConn.Write(Tag + ' OK LOGIN completed' + CRLF)
    else if Pos(' SELECT', U) >= 0 then
    begin
      AConn.Write('* 3 EXISTS' + CRLF);
      AConn.Write('* 1 RECENT' + CRLF);
      AConn.Write('* FLAGS (\Seen \Deleted)' + CRLF);
      AConn.Write(Tag + ' OK [READ-WRITE] SELECT completed' + CRLF);
    end
    else if Pos(' FETCH ', U) >= 0 then
    begin
      // untagged FETCH with a literal-octet-count body
      AConn.Write('* 1 FETCH (RFC822 {' + IntToStr(Length(LITERAL_BODY)) + '}'
        + CRLF);
      AConn.Write(LITERAL_BODY);         { exactly nnn octets, no extra CRLF }
      AConn.Write(')' + CRLF);           { the FETCH response wrapper close }
      AConn.Write(Tag + ' OK FETCH completed' + CRLF);
    end
    else if Pos(' SEARCH ', U) >= 0 then
    begin
      AConn.Write('* SEARCH 2 4 6' + CRLF);
      AConn.Write(Tag + ' OK SEARCH completed' + CRLF);
    end
    else if Pos(' LOGOUT', U) >= 0 then
    begin
      AConn.Write('* BYE mock logging out' + CRLF);
      AConn.Write(Tag + ' OK LOGOUT completed' + CRLF);
      Break;
    end
    else
      AConn.Write(Tag + ' BAD unrecognised' + CRLF);
  end;
end;

procedure ServerFiber(AArg: Pointer);
begin
  GServer.Serve(GHandler);
end;

procedure ClientFiber(AArg: Pointer);
var
  Cli: TImapClient;
  Ids: TList<Int>;
begin
  FiberSleep(2);
  Cli := TImapClient.Create();
  Ids := TList<Int>.Create();
  if Cli.Connect('127.0.0.1', GPort) then
  begin
    GLoginOk := Cli.Login('alice', 'secret');
    GSelectOk := Cli.Select('INBOX');
    GExists := Cli.Exists;
    GFetchOk := Cli.Fetch(1, 'RFC822', GFetchBody);
    GSearchOk := Cli.Search('UNSEEN', Ids);
    GSearchCount := Ids.Count;
    if Ids.Count > 0 then
      GSearchFirst := Ids[0];
    GLogoutOk := Cli.Logout();
  end;
  Ids.Free();
  Cli.Free();
  GServer.Stop();
end;

procedure TImapTests.TestLoginSelectFetchSearchLogout;
const
  PORT = 29701;
begin
  GServer := TTcpServer.Create(PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TMockImapHandler.Create();
  GPort := PORT;
  GLoginOk := False;
  GSelectOk := False;
  GExists := -1;
  GFetchOk := False;
  GFetchBody := '';
  GSearchOk := False;
  GSearchCount := -1;
  GSearchFirst := -1;
  GLogoutOk := False;

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@ClientFiber, nil);
  RunScheduler();

  AssertTrue('LOGIN tagged OK', GLoginOk);
  AssertTrue('SELECT tagged OK', GSelectOk);
  AssertEquals('SELECT parsed EXISTS', 3, GExists);
  AssertTrue('FETCH tagged OK', GFetchOk);
  AssertTrue('FETCH {literal} body carried the subject',
    Pos('Subject: Test', GFetchBody) >= 0);
  AssertTrue('FETCH {literal} body carried the text',
    Pos('Hello IMAP body', GFetchBody) >= 0);
  AssertTrue('SEARCH tagged OK', GSearchOk);
  AssertEquals('SEARCH parsed three ids', 3, GSearchCount);
  AssertEquals('SEARCH first id', 2, GSearchFirst);
  AssertTrue('LOGOUT tagged OK', GLogoutOk);

  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

initialization
  RegisterTest(TImapTests);

end.
