{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for L5 Net.Nntp (NNTP client + server, RFC 3977 / RFC 977).

  TNntpClientTests drives TNntpClient against a MOCK NNTP server fiber running
  on Net.Tcp inside the test-runner process.  The mock speaks:
    200 greeting, 211 to GROUP (count/first/last/name), a dot-terminated
    ARTICLE body, 215 + a dot-terminated LIST, 340->240 for POST (capturing the
    dot-unstuffed article it received), 205 to QUIT.
  Assertions: GROUP parses count/first/last, ARTICLE returns the dot-unstuffed
  body byte-exact, POST delivers a correctly dot-stuffed article intact, LIST
  parses entries.

  TNntpServerTests drives the real TNntpClient <-> TNntpServer over loopback
  under the scheduler, backed by an in-memory INntpStore: select a group, fetch
  an article byte-exact, POST an article then fetch it back to prove the
  round-trip, and LIST shows the group.

  Plaintext (internal linker).  NATIVE BACKEND ONLY.  Self-registers via the
  initialization section. }

unit Nntp.Tests;

interface

uses
  blaise.testing, SysUtils, Net.Tcp, Net.Nntp, Net.Nntp.Server, Net.Mail.Reply,
  async.fibers, async.io, Net.Sockets, Generics.Collections;

type
  TNntpClientTests = class(TTestCase)
  published
    procedure TestGroupArticleListPost;
  end;

  { Client <-> real TNntpServer round-trip. }
  TNntpServerTests = class(TTestCase)
  published
    procedure TestClientServerRoundTrip;
  end;

implementation

const
  MOCK_PORT = 29671;
  { The article body the mock serves for ARTICLE.  Includes a line that starts
    with '.' so dot-stuffing/unstuffing is exercised, plus a CRLF and a NUL to
    prove the transfer is byte-exact and binary-clean once reassembled. }
  ART_BODY = 'Subject: hi' + #10 + #10 + 'first body line' + #10
    + '.hidden dotted line' + #10 + 'tail' + #0 + 'byte';
  { The article the client POSTs (leading-dot line included). }
  POST_ART = 'Subject: greetings' + #10 + 'From: alice' + #10 + #10
    + 'body one' + #10 + '.dotstart' + #10 + 'last';

var
  GServer: TTcpServer;
  GHandler: IConnHandler;
  { results captured by the client fiber }
  GConnOk: Boolean;
  GModeOk: Boolean;
  GGroupOk: Boolean;
  GGCount: Int;
  GGFirst: Int;
  GGLast: Int;
  GArtOk: Boolean;
  GArt: string;
  GListOk: Boolean;
  GListCount: Int;
  GListHas: Boolean;
  GPostOk: Boolean;
  GQuitOk: Boolean;
  { what the mock received via POST (dot-unstuffed) }
  GPosted: string;

type
  TMockNntpHandler = class(IConnHandler)
    procedure Handle(AConn: TTcpConn);
  end;

{ Read a dot-terminated block from AConn, un-dot-stuffing each line, join with
  LF.  (The mirror of the client's ReadMultiline, used by the mock to receive
  the POSTed article.) }
function ReadDotBlock(AConn: TTcpConn): string;
var
  Line, R: string;
begin
  R := '';
  while AConn.ReadLine(Line) do
  begin
    if Line = '.' then
      Break;
    if R <> '' then
      R := R + #10;
    R := R + UnDotStuff(Line);
  end;
  Result := R;
end;

procedure TMockNntpHandler.Handle(AConn: TTcpConn);
var
  Line, U: string;
begin
  AConn.Write('200 mock NNTP ready (posting allowed)' + CRLF);
  while AConn.ReadLine(Line) do
  begin
    U := UpperCase(Line);
    if U = 'MODE READER' then
      AConn.Write('200 reader mode' + CRLF)
    else if Copy(U, 0, 5) = 'GROUP' then
      { 211 count first last name }
      AConn.Write('211 42 100 141 comp.lang.pascal' + CRLF)
    else if Copy(U, 0, 7) = 'ARTICLE' then
    begin
      AConn.Write('220 0 <mock@id> article follows' + CRLF);
      { send the body dot-stuffed + dot-terminated }
      AConn.Write(DotStuffBody(ART_BODY));
    end
    else if U = 'LIST' then
    begin
      AConn.Write('215 list of newsgroups follows' + CRLF);
      AConn.Write('comp.lang.pascal 141 100 y' + CRLF);
      AConn.Write('comp.lang.blaise 5 1 y' + CRLF);
      AConn.Write('.' + CRLF);
    end
    else if U = 'POST' then
    begin
      AConn.Write('340 send article' + CRLF);
      GPosted := ReadDotBlock(AConn);
      AConn.Write('240 article received' + CRLF);
    end
    else if U = 'QUIT' then
    begin
      AConn.Write('205 bye' + CRLF);
      Break;
    end
    else
      AConn.Write('500 unknown command' + CRLF);
  end;
end;

procedure ServerFiber(AArg: Pointer);
begin
  GServer.Serve(GHandler);
end;

procedure ClientFiber(AArg: Pointer);
var
  Cli: TNntpClient;
  Groups: TList<string>;
  I: Int;
begin
  FiberSleep(2);
  Cli := TNntpClient.Create();
  GConnOk := Cli.Connect('127.0.0.1', MOCK_PORT);
  if GConnOk then
  begin
    GModeOk := Cli.ModeReader();
    GGroupOk := Cli.SelectGroup('comp.lang.pascal', GGCount, GGFirst, GGLast);
    GArtOk := Cli.FetchArticle('100', GArt);
    if Cli.ListGroups(Groups) then
    begin
      GListOk := True;
      GListCount := Groups.Count;
      GListHas := False;
      for I := 0 to Groups.Count - 1 do
        if Pos('comp.lang.pascal', Groups[I]) >= 0 then
          GListHas := True;
    end;
    Groups.Free();
    GPostOk := Cli.Post(POST_ART);
    GQuitOk := Cli.Quit();
  end;
  Cli.Free();
  GServer.Stop();
end;

procedure TNntpClientTests.TestGroupArticleListPost;
begin
  GServer := TTcpServer.Create(MOCK_PORT);
  AssertTrue('server start', GServer.Start());
  GHandler := TMockNntpHandler.Create();
  GConnOk := False;
  GModeOk := False;
  GGroupOk := False;
  GGCount := 0;
  GGFirst := 0;
  GGLast := 0;
  GArtOk := False;
  GArt := '';
  GListOk := False;
  GListCount := 0;
  GListHas := False;
  GPostOk := False;
  GQuitOk := False;
  GPosted := '';

  SpawnFiber(@ServerFiber, nil);
  SpawnFiber(@ClientFiber, nil);
  RunScheduler();

  AssertTrue('connect', GConnOk);
  AssertTrue('mode reader', GModeOk);
  AssertTrue('group ok', GGroupOk);
  AssertEquals('group count', 42, GGCount);
  AssertEquals('group first', 100, GGFirst);
  AssertEquals('group last', 141, GGLast);
  AssertTrue('article ok', GArtOk);
  AssertEquals('article byte-exact', ART_BODY, GArt);
  AssertTrue('list ok', GListOk);
  AssertEquals('list entry count', 2, GListCount);
  AssertTrue('list has group', GListHas);
  AssertTrue('post ok', GPostOk);
  AssertEquals('posted article byte-exact', POST_ART, GPosted);
  AssertTrue('quit', GQuitOk);

  ResetScheduler();
  GServer.Free();
  GHandler := nil;
end;

{ ---------------------------------------------------------------------------
  Client <-> real TNntpServer round-trip
  --------------------------------------------------------------------------- }

const
  SRV_PORT = 29681;
  { The article stored + fetched back.  Leading-dot line + NUL prove dot-stuffing
    and binary-clean byte-exact round-trip. }
  RT_ART = 'Subject: roundtrip' + #10 + 'From: bob' + #10 + #10
    + 'para one' + #10 + '.leading dot' + #10 + 'x' + #0 + 'y' + #10 + 'end';

type
  { A trivial in-memory news store: a single group with numbered articles. }
  TMemNntpStore = class(INntpStore)
  private
    FGroup: string;
    FArticles: TList<string>;   { article body per index; number = index+1 }
  public
    constructor Create(const AGroup: string);
    destructor Destroy; override;
    function ListGroups: string;
    function SelectGroup(const AName: string; out ACount: Int;
      out AFirst: Int; out ALast: Int): Boolean;
    function GetArticle(const AGroup: string; ANumber: Int;
      out AArticle: string): Boolean;
    function PostArticle(const AArticle: string; out ANumber: Int): Boolean;
  end;

constructor TMemNntpStore.Create(const AGroup: string);
begin
  FGroup := AGroup;
  FArticles := TList<string>.Create();
end;

destructor TMemNntpStore.Destroy;
begin
  FArticles.Free();
  inherited Destroy();
end;

function TMemNntpStore.ListGroups: string;
var
  Cnt: Int;
begin
  Cnt := FArticles.Count;
  { 'name last first flag' per RFC LIST ACTIVE }
  Result := FGroup + ' ' + IntToStr(Cnt) + ' 1 y';
end;

function TMemNntpStore.SelectGroup(const AName: string; out ACount: Int;
  out AFirst: Int; out ALast: Int): Boolean;
begin
  if AName <> FGroup then
  begin
    ACount := 0;
    AFirst := 0;
    ALast := 0;
    Exit(False);
  end;
  ACount := FArticles.Count;
  if FArticles.Count = 0 then
  begin
    AFirst := 0;
    ALast := 0;
  end
  else
  begin
    AFirst := 1;
    ALast := FArticles.Count;
  end;
  Result := True;
end;

function TMemNntpStore.GetArticle(const AGroup: string; ANumber: Int;
  out AArticle: string): Boolean;
begin
  if (ANumber < 1) or (ANumber > FArticles.Count) then
  begin
    AArticle := '';
    Exit(False);
  end;
  AArticle := FArticles[ANumber - 1];
  Result := True;
end;

function TMemNntpStore.PostArticle(const AArticle: string;
  out ANumber: Int): Boolean;
begin
  FArticles.Add(AArticle);
  ANumber := FArticles.Count;
  Result := True;
end;

var
  GSrv: TNntpServer;
  GStore: INntpStore;
  GRtConnOk: Boolean;
  GRtGroupOk: Boolean;
  GRtCount0: Int;
  GRtPostOk: Boolean;
  GRtGroupOk2: Boolean;
  GRtCount1: Int;
  GRtLast1: Int;
  GRtFetch: string;
  GRtFetchOk: Boolean;
  GRtList: string;
  GRtListOk: Boolean;
  GRtQuitOk: Boolean;

procedure SrvServeFiber(AArg: Pointer);
begin
  GSrv.Serve(GStore);
end;

procedure RtClientFiber(AArg: Pointer);
var
  Cli: TNntpClient;
  Groups: TList<string>;
  Cnt, First, Last: Int;
  I: Int;
begin
  FiberSleep(2);
  Cli := TNntpClient.Create();
  GRtConnOk := Cli.Connect('127.0.0.1', SRV_PORT);
  if GRtConnOk then
  begin
    Cli.ModeReader();
    { group is empty at first }
    GRtGroupOk := Cli.SelectGroup('comp.test', Cnt, First, Last);
    GRtCount0 := Cnt;
    { post an article }
    GRtPostOk := Cli.Post(RT_ART);
    { re-select: now has one article }
    GRtGroupOk2 := Cli.SelectGroup('comp.test', Cnt, First, Last);
    GRtCount1 := Cnt;
    GRtLast1 := Last;
    { fetch it back }
    GRtFetchOk := Cli.FetchArticle(IntToStr(Last), GRtFetch);
    { LIST shows the group }
    if Cli.ListGroups(Groups) then
    begin
      GRtListOk := True;
      GRtList := '';
      for I := 0 to Groups.Count - 1 do
        GRtList := GRtList + Groups[I] + #10;
    end;
    Groups.Free();
    GRtQuitOk := Cli.Quit();
  end;
  Cli.Free();
  GSrv.Stop();
end;

procedure TNntpServerTests.TestClientServerRoundTrip;
begin
  GSrv := TNntpServer.Create(SRV_PORT);
  AssertTrue('server start', GSrv.Start());
  GStore := TMemNntpStore.Create('comp.test');
  GRtConnOk := False;
  GRtGroupOk := False;
  GRtCount0 := -1;
  GRtPostOk := False;
  GRtGroupOk2 := False;
  GRtCount1 := -1;
  GRtLast1 := -1;
  GRtFetch := '';
  GRtFetchOk := False;
  GRtList := '';
  GRtListOk := False;
  GRtQuitOk := False;

  SpawnFiber(@SrvServeFiber, nil);
  SpawnFiber(@RtClientFiber, nil);
  RunScheduler();

  AssertTrue('connect', GRtConnOk);
  AssertTrue('group (empty) ok', GRtGroupOk);
  AssertEquals('count before post', 0, GRtCount0);
  AssertTrue('post ok', GRtPostOk);
  AssertTrue('group (after post) ok', GRtGroupOk2);
  AssertEquals('count after post', 1, GRtCount1);
  AssertEquals('last after post', 1, GRtLast1);
  AssertTrue('fetch ok', GRtFetchOk);
  AssertEquals('POST-then-fetch byte-exact', RT_ART, GRtFetch);
  AssertTrue('list ok', GRtListOk);
  AssertTrue('list shows group', Pos('comp.test', GRtList) >= 0);
  AssertTrue('quit', GRtQuitOk);

  ResetScheduler();
  GSrv.Free();
  GStore := nil;
end;

initialization
  RegisterTest(TNntpClientTests);
  RegisterTest(TNntpServerTests);

end.
