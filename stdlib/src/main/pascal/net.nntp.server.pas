{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Nntp.Server;

// L5 NEWS wave: an NNTP SERVER (RFC 3977 / RFC 977) over Net.Tcp.  TNntpServer
// runs the fiber-per-connection accept loop of Net.Tcp.TTcpServer; each
// connection gets a session fiber that:
//
//   * writes the 200 greeting (posting allowed),
//   * MODE READER -> 200,
//   * LIST -> 215 + a dot-terminated newsgroup listing from the store,
//   * GROUP <name> -> 211 <count> <first> <last> <name> (and remembers the
//     selected group + current-article pointer as per-session locals),
//   * ARTICLE / HEAD / BODY <n or message-id> -> serve the article from the
//     store, dot-stuffed + dot-terminated (HEAD/BODY split at the first blank
//     line),
//   * POST -> 340, read the dot-stuffed article until CRLF.CRLF, un-stuff, hand
//     it to the store, 240,
//   * QUIT -> 205, close.
//
// The article/group backing store is behind INntpStore so the application (or a
// test) supplies any implementation - an in-memory map, a real spool, etc.
//
// Plaintext (internal linker); NNTPS deferred.  AUTHINFO / DNS deferred.
// NATIVE BACKEND ONLY.

interface

uses
  SysUtils, Net.Tcp, async.fibers;

type
  { The application-supplied news store.  Article numbers are 1-based within a
    group (the NNTP wire convention); an article is the full RFC 5322 text
    (headers, a blank line, then the body) as a single LF- or CRLF-delimited
    string. }
  INntpStore = interface
    { One 'name last first flag' line per group (LF-separated), for LIST. }
    function ListGroups: string;
    { Select AName: on success set ACount/AFirst/ALast and return True; False
      for an unknown group. }
    function SelectGroup(const AName: string; out ACount: Int;
      out AFirst: Int; out ALast: Int): Boolean;
    { Fetch article ANumber in AGroup; True if it exists. }
    function GetArticle(const AGroup: string; ANumber: Int;
      out AArticle: string): Boolean;
    { Store a posted article; True on success, ANumber = its assigned number. }
    function PostArticle(const AArticle: string; out ANumber: Int): Boolean;
  end;

  { A fiber-per-connection NNTP server.  Start binds+listens; Serve runs the
    accept loop until Stop.  Drive Serve from inside a fiber. }
  TNntpServer = class
  private
    FPort: UInt16;
    FServer: TTcpServer;      { ARC-owned; freed in Destroy }
    FStore: INntpStore;
  public
    constructor Create(APort: UInt16);
    destructor Destroy; override;

    { Bind + listen on 127.0.0.1:Port.  Returns False on failure. }
    function Start: Boolean;

    { Run the accept loop, spawning a session handler fiber per connection, each
      backed by AStore.  Returns when Stop is called. }
    procedure Serve(AStore: INntpStore);

    { Stop the accept loop and close the listen socket. }
    procedure Stop;

    property Port: UInt16 read FPort;
  end;

implementation

uses
  Net.Mail.Reply;

type
  { The IConnHandler run per connection.  Holds the store ref (which outlives
    every connection via the server) and drives one NNTP session.  Per-session
    mutable state lives in locals inside Handle - the one handler instance is
    reused for every connection fiber. }
  TNntpSessionHandler = class(IConnHandler)
  private
    FStore: INntpStore;
  public
    constructor Create(AStore: INntpStore);
    procedure Handle(AConn: TTcpConn);
  end;

constructor TNntpSessionHandler.Create(AStore: INntpStore);
begin
  FStore := AStore;
end;

{ Extract the argument after the command word (everything past the first run of
  spaces).  Returns '' when the command has no argument. }
function CmdArg(const ALine: string): string;
var
  I, Len: Int;
begin
  Result := '';
  Len := Length(ALine);
  I := 0;
  while (I < Len) and (Byte(ALine[I]) <> 32) do
    I := I + 1;
  while (I < Len) and (Byte(ALine[I]) = 32) do
    I := I + 1;
  if I < Len then
    Result := Copy(ALine, I, Len - I);
end;

{ Parse a leading run of ASCII digits into an integer (0 if none). }
function ParseUInt(const S: string): Int;
var
  I, Len, V: Int;
  B: Byte;
begin
  V := 0;
  Len := Length(S);
  I := 0;
  while I < Len do
  begin
    B := Byte(S[I]);
    if (B < 48) or (B > 57) then
      Break;
    V := V * 10 + (B - 48);
    I := I + 1;
  end;
  Result := V;
end;

{ Convert an LF-joined listing into a dot-terminated multi-line block: each line
  dot-stuffed and CRLF-terminated, plus the final '.' CRLF.  (DotStuffBody does
  exactly this framing.) }
function ListingToBlock(const AListing: string): string;
begin
  Result := DotStuffBody(AListing);
end;

{ Split an article into its head (up to but excluding the first blank line) or
  its body (after the first blank line).  AWantHead True -> head, False -> body.
  A "blank line" is an empty line (LF LF, i.e. an empty segment). }
function HeadOrBody(const AArticle: string; AWantHead: Boolean): string;
var
  I, Len, LineStart: Int;
begin
  Len := Length(AArticle);
  LineStart := 0;
  I := 0;
  while I <= Len do
  begin
    if (I = Len) or (Byte(AArticle[I]) = 10) then
    begin
      { the segment [LineStart, I) is one line }
      if I = LineStart then
      begin
        { blank line found at LineStart }
        if AWantHead then
          Exit(Copy(AArticle, 0, LineStart))
        else
        begin
          { body starts just after the blank line's LF }
          if I + 1 <= Len then
            Exit(Copy(AArticle, I + 1, Len - I - 1))
          else
            Exit('');
        end;
      end;
      LineStart := I + 1;
      if I = Len then
        Break;
    end;
    I := I + 1;
  end;
  { no blank line: whole thing is head, empty body }
  if AWantHead then
    Result := AArticle
  else
    Result := '';
end;

{ Read the POSTed article: dot-terminated, un-dot-stuffed, LF-joined. }
function ReadPostedArticle(AConn: TTcpConn): string;
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

procedure TNntpSessionHandler.Handle(AConn: TTcpConn);
var
  Line, U, Arg, CurGroup, Article, Payload: string;
  Num, Cnt, First, Last, PostNum: Int;
begin
  CurGroup := '';
  AConn.Write('200 Blaise NNTP server ready (posting allowed)' + CRLF);
  while AConn.ReadLine(Line) do
  begin
    U := UpperCase(Line);
    Arg := CmdArg(Line);
    if U = 'MODE READER' then
      AConn.Write('200 reader mode' + CRLF)
    else if U = 'LIST' then
    begin
      AConn.Write('215 list of newsgroups follows' + CRLF);
      AConn.Write(ListingToBlock(FStore.ListGroups()));
    end
    else if Copy(U, 0, 5) = 'GROUP' then
    begin
      if FStore.SelectGroup(Arg, Cnt, First, Last) then
      begin
        CurGroup := Arg;
        AConn.Write('211 ' + IntToStr(Cnt) + ' ' + IntToStr(First) + ' '
          + IntToStr(Last) + ' ' + Arg + CRLF);
      end
      else
        AConn.Write('411 no such news group' + CRLF);
    end
    else if (Copy(U, 0, 7) = 'ARTICLE') or (Copy(U, 0, 4) = 'HEAD')
         or (Copy(U, 0, 4) = 'BODY') then
    begin
      if CurGroup = '' then
        AConn.Write('412 no newsgroup selected' + CRLF)
      else
      begin
        Num := ParseUInt(Arg);
        if FStore.GetArticle(CurGroup, Num, Article) then
        begin
          if Copy(U, 0, 4) = 'HEAD' then
          begin
            AConn.Write('221 ' + IntToStr(Num) + ' article head follows' + CRLF);
            Payload := HeadOrBody(Article, True);
          end
          else if Copy(U, 0, 4) = 'BODY' then
          begin
            AConn.Write('222 ' + IntToStr(Num) + ' article body follows' + CRLF);
            Payload := HeadOrBody(Article, False);
          end
          else
          begin
            AConn.Write('220 ' + IntToStr(Num) + ' article follows' + CRLF);
            Payload := Article;
          end;
          AConn.Write(DotStuffBody(Payload));
        end
        else
          AConn.Write('423 no such article number in this group' + CRLF);
      end;
    end
    else if U = 'POST' then
    begin
      AConn.Write('340 send article to be posted' + CRLF);
      Article := ReadPostedArticle(AConn);
      if FStore.PostArticle(Article, PostNum) then
        AConn.Write('240 article received' + CRLF)
      else
        AConn.Write('441 posting failed' + CRLF);
    end
    else if U = 'QUIT' then
    begin
      AConn.Write('205 closing connection' + CRLF);
      Break;
    end
    else
      AConn.Write('500 unknown command' + CRLF);
  end;
  { The TCP server's connection trampoline closes+frees AConn after we return. }
end;

{ ---- TNntpServer ---- }

constructor TNntpServer.Create(APort: UInt16);
begin
  FPort := APort;
  FServer := TTcpServer.Create(APort);
  FStore := nil;
end;

destructor TNntpServer.Destroy;
begin
  if FServer <> nil then
  begin
    FServer.Free();
    FServer := nil;
  end;
  inherited Destroy();
end;

function TNntpServer.Start: Boolean;
begin
  Result := FServer.Start();
end;

procedure TNntpServer.Serve(AStore: INntpStore);
var
  H: IConnHandler;
begin
  FStore := AStore;
  H := TNntpSessionHandler.Create(AStore);
  FServer.Serve(H);
end;

procedure TNntpServer.Stop;
begin
  FServer.Stop();
end;

end.
