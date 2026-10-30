{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Imap;

// L5 MAIL wave: an IMAP4rev1 CLIENT (RFC 3501, core subset) over Net.Tcp.
//
// Every command carries a unique tag (A001, A002, ...).  The server replies with
// zero or more untagged lines (each begins '* ') carrying the requested data,
// then a single tagged completion line 'A001 OK ...' / 'A001 NO ...' /
// 'A001 BAD ...'.  TImapClient sends a command, collects the untagged lines up
// to its own tag, and returns the tagged result.
//
//   Connect(host, port)   read the '* OK' greeting
//   Login(user, pass)     LOGIN
//   Select(mailbox)       parse EXISTS / RECENT counts
//   List(ref, pattern)    untagged LIST lines
//   Fetch(n, item)        FETCH — parses the {nnn} literal octet-count syntax
//                         and reads exactly nnn following octets as the body
//   Search(criteria)      SEARCH — parses the '* SEARCH n n n' id list
//   Logout                LOGOUT
//
// Literal syntax: an untagged line ending in '{nnn}' means the next nnn octets
// (which may span several physical lines and include CRLFs) are literal data;
// after them the response text continues on the same logical line.  Fetch reads
// the literal with ReadFull so the body is captured verbatim.
//
// DEFERRED (documented, not implemented): IDLE, UID commands, extensions
// (CONDSTORE/QRESYNC/MOVE), STARTTLS, and MIME/body-structure parsing.  Implicit
// TLS on 993 (IMAPS) lives in Net.Imap.Tls (needs --linker external).
//
// NATIVE BACKEND ONLY (Net.Tcp -> async.io).

interface

uses
  SysUtils, Net.Tcp, Net.Mail.Reply, Generics.Collections;

type
  EImapError = class(Exception);

  { The tagged completion status of a command. }
  TImapStatus = (isOk, isNo, isBad, isNone);

  TImapClient = class
  private
    FConn: TTcpConn;
    FTagSeq: Int;
    FLastTag: string;
    FLastStatus: TImapStatus;
    FLastText: string;               { text after the tagged status word }
    FUntagged: TList<string>;        { untagged '*' data lines of the last cmd }
    FExists: Int;
    FRecent: Int;
    function NextTag: string;
    // Read one physical response line, resolving a trailing literal octet-count
    // marker by appending the literal octets + the continuation.  False on EOF.
    function ReadResponseLine(out ALine: string): Boolean;
    { Send ACmd under a fresh tag and collect untagged lines until the tagged
      completion; fills FUntagged, FLastStatus, FLastText.  Returns the status. }
    function RunCommand(const ACmd: string): TImapStatus;
    function ParseStatusWord(const AWord: string): TImapStatus;
  public
    constructor Create;
    destructor Destroy; override;

    function Connect(const AHostIp: string; APort: UInt16): Boolean;
    procedure Attach(AConn: TTcpConn);

    function Login(const AUser, APass: string): Boolean;

    { SELECT mailbox: on OK, Exists/Recent are populated from the untagged
      '* n EXISTS' / '* n RECENT' lines. }
    function Select(const AMailbox: string): Boolean;

    { LIST reference pattern: untagged LIST lines land in Untagged. }
    function List(const ARef, APattern: string): Boolean;

    { FETCH n item (e.g. 'RFC822', 'BODY[]').  On OK, ABody holds the literal
      octets of the fetched item (empty if the item was not a literal). }
    function Fetch(AMsg: Int; const AItem: string; out ABody: string): Boolean;

    { SEARCH criteria: fills AIds with the returned message numbers. }
    function Search(const ACriteria: string; AIds: TList<Int>): Boolean;

    function Logout: Boolean;

    property Exists: Int read FExists;
    property Recent: Int read FRecent;
    property LastStatus: TImapStatus read FLastStatus;
    property LastText: string read FLastText;
    property Untagged: TList<string> read FUntagged;
    property Conn: TTcpConn read FConn write FConn;
  end;

implementation

{ Parse the leading run of ASCII digits in S (from offset AStart) into an
  integer; stops at the first non-digit.  Returns 0 for no digits. }
function ParseIntAt(const S: string; AStart: Int): Int;
var
  I, Len, V: Int;
  B: Byte;
begin
  V := 0;
  Len := Length(S);
  I := AStart;
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

// If ALine ends in a literal octet-count marker (an open brace, digits, a close
// brace), return the count via ACount and True; otherwise False.
function ParseLiteralMarker(const ALine: string; out ACount: Int): Boolean;
var
  Len, I: Int;
begin
  ACount := 0;
  Len := Length(ALine);
  if (Len < 3) or (Byte(ALine[Len - 1]) <> 125) then   // must end in close brace
    Exit(False);
  // find the matching open brace
  I := Len - 2;
  while (I >= 0) and (Byte(ALine[I]) <> 123) do
    I := I - 1;
  if I < 0 then
    Exit(False);
  ACount := ParseIntAt(ALine, I + 1);
  Result := True;
end;

constructor TImapClient.Create;
begin
  FConn := nil;
  FTagSeq := 0;
  FLastTag := '';
  FLastStatus := isNone;
  FLastText := '';
  FUntagged := TList<string>.Create();
  FExists := 0;
  FRecent := 0;
end;

destructor TImapClient.Destroy;
begin
  FUntagged.Free();
  if FConn <> nil then
  begin
    FConn.Free();
    FConn := nil;
  end;
  inherited Destroy();
end;

function TImapClient.NextTag: string;
begin
  FTagSeq := FTagSeq + 1;
  { A001, A002, ... zero-padded to 3 digits for the common case. }
  if FTagSeq < 10 then
    Result := 'A00' + IntToStr(FTagSeq)
  else if FTagSeq < 100 then
    Result := 'A0' + IntToStr(FTagSeq)
  else
    Result := 'A' + IntToStr(FTagSeq);
end;

function TImapClient.ReadResponseLine(out ALine: string): Boolean;
var
  Line, Cont: string;
  Lit: Int;
begin
  if not FConn.ReadLine(Line) then
  begin
    ALine := '';
    Exit(False);
  end;
  // Resolve any trailing literal marker by reading exactly Lit octets, then the
  // remainder of the logical line (which follows the literal).
  while ParseLiteralMarker(Line, Lit) do
  begin
    // splice the literal octets in after the marker line, read verbatim
    Cont := FConn.ReadFull(Lit);
    { after the literal, the rest of the logical line continues; read it }
    Line := Line + #10 + Cont;
    { read the continuation line (may itself carry another literal) }
    if not FConn.ReadLine(Cont) then
      Break;
    Line := Line + Cont;
  end;
  ALine := Line;
  Result := True;
end;

function TImapClient.ParseStatusWord(const AWord: string): TImapStatus;
var
  U: string;
begin
  U := UpperCase(AWord);
  if U = 'OK' then
    Result := isOk
  else if U = 'NO' then
    Result := isNo
  else if U = 'BAD' then
    Result := isBad
  else
    Result := isNone;
end;

function TImapClient.RunCommand(const ACmd: string): TImapStatus;
var
  Tag, Line, Rest, Word2: string;
  Len, I, SpacePos: Int;
begin
  FUntagged.Clear();
  FLastStatus := isNone;
  FLastText := '';
  Tag := Self.NextTag();
  FLastTag := Tag;
  if not FConn.Write(Tag + ' ' + ACmd + CRLF) then
    Exit(isNone);
  while Self.ReadResponseLine(Line) do
  begin
    if (Length(Line) >= 2) and (Byte(Line[0]) = 42) and (Byte(Line[1]) = 32) then
    begin
      { untagged '* ...' data line }
      FUntagged.Add(Copy(Line, 2, Length(Line) - 2));
      Continue;
    end;
    { tagged completion: starts with our tag }
    Len := Length(Tag);
    if (Length(Line) > Len) and (Copy(Line, 0, Len) = Tag) then
    begin
      Rest := Copy(Line, Len + 1, Length(Line) - Len - 1);
      { skip a leading space }
      while (Length(Rest) > 0) and (Byte(Rest[0]) = 32) do
        Rest := Copy(Rest, 1, Length(Rest) - 1);
      { the next token is the status word }
      SpacePos := -1;
      for I := 0 to Length(Rest) - 1 do
        if Byte(Rest[I]) = 32 then
        begin
          SpacePos := I;
          Break;
        end;
      if SpacePos >= 0 then
      begin
        Word2 := Copy(Rest, 0, SpacePos);
        FLastText := Copy(Rest, SpacePos + 1, Length(Rest) - SpacePos - 1);
      end
      else
        Word2 := Rest;
      FLastStatus := Self.ParseStatusWord(Word2);
      Exit(FLastStatus);
    end;
    { a continuation '+ ...' or anything else: ignore for the core subset }
  end;
  Result := FLastStatus;
end;

function TImapClient.Connect(const AHostIp: string; APort: UInt16): Boolean;
var
  Cli: TTcpClient;
  C: TTcpConn;
  Greeting: string;
begin
  Cli := TTcpClient.Create();
  C := Cli.Connect(AHostIp, APort);
  Cli.Free();
  if C = nil then
    Exit(False);
  FConn := C;
  { greeting: '* OK ...' }
  if not FConn.ReadLine(Greeting) then
    Exit(False);
  Result := (Length(Greeting) >= 4) and (Copy(Greeting, 0, 4) = '* OK');
end;

procedure TImapClient.Attach(AConn: TTcpConn);
begin
  FConn := AConn;
end;

function TImapClient.Login(const AUser, APass: string): Boolean;
begin
  Result := Self.RunCommand('LOGIN ' + AUser + ' ' + APass) = isOk;
end;

function TImapClient.Select(const AMailbox: string): Boolean;
var
  I: Int;
  U, DataLine: string;
begin
  FExists := 0;
  FRecent := 0;
  Result := Self.RunCommand('SELECT ' + AMailbox) = isOk;
  if not Result then
    Exit;
  { untagged lines like 'n EXISTS', 'n RECENT' }
  for I := 0 to FUntagged.Count - 1 do
  begin
    DataLine := FUntagged[I];
    U := UpperCase(DataLine);
    if Pos(' EXISTS', U) >= 0 then
      FExists := ParseIntAt(DataLine, 0)
    else if Pos(' RECENT', U) >= 0 then
      FRecent := ParseIntAt(DataLine, 0);
  end;
end;

function TImapClient.List(const ARef, APattern: string): Boolean;
begin
  Result := Self.RunCommand('LIST "' + ARef + '" "' + APattern + '"') = isOk;
end;

function TImapClient.Fetch(AMsg: Int; const AItem: string;
  out ABody: string): Boolean;
var
  I, NlPos: Int;
  DataLine: string;
begin
  ABody := '';
  Result := Self.RunCommand('FETCH ' + IntToStr(AMsg) + ' ' + AItem) = isOk;
  if not Result then
    Exit;
  // A FETCH untagged line looks like:  n FETCH (RFC822 <marker><LF><octets>)
  // ReadResponseLine has already inlined the literal after an LF, so the data
  // line contains the literal payload after the first embedded LF.
  for I := 0 to FUntagged.Count - 1 do
  begin
    DataLine := FUntagged[I];
    if Pos('FETCH', UpperCase(DataLine)) >= 0 then
    begin
      { the literal payload begins after the first LF we spliced in }
      NlPos := Pos(#10, DataLine);
      if NlPos >= 0 then
      begin
        ABody := Copy(DataLine, NlPos + 1, Length(DataLine) - NlPos - 1);
        { strip a trailing ')' left by the FETCH response wrapper }
        if (Length(ABody) > 0)
          and (Byte(ABody[Length(ABody) - 1]) = 41) then
          ABody := Copy(ABody, 0, Length(ABody) - 1);
      end;
      Exit;
    end;
  end;
end;

function TImapClient.Search(const ACriteria: string;
  AIds: TList<Int>): Boolean;
var
  I, J, Len: Int;
  DataLine, U: string;
  B: Byte;
  Cur, Have: Int;
begin
  AIds.Clear();
  Result := Self.RunCommand('SEARCH ' + ACriteria) = isOk;
  if not Result then
    Exit;
  { untagged '* SEARCH id id id' -> stored (without the '*') as 'SEARCH id...' }
  for I := 0 to FUntagged.Count - 1 do
  begin
    DataLine := FUntagged[I];
    U := UpperCase(DataLine);
    if Copy(U, 0, 6) = 'SEARCH' then
    begin
      Len := Length(DataLine);
      J := 6;
      Cur := 0;
      Have := 0;
      while J <= Len do
      begin
        if J < Len then
          B := Byte(DataLine[J])
        else
          B := 32;
        if (B >= 48) and (B <= 57) then
        begin
          Cur := Cur * 10 + (B - 48);
          Have := 1;
        end
        else
        begin
          if Have = 1 then
          begin
            AIds.Add(Cur);
            Cur := 0;
            Have := 0;
          end;
        end;
        J := J + 1;
      end;
    end;
  end;
end;

function TImapClient.Logout: Boolean;
begin
  Result := Self.RunCommand('LOGOUT') = isOk;
  if FConn <> nil then
    FConn.Close();
end;

end.
