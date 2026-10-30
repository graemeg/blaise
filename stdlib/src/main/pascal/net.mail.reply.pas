{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Mail.Reply;

// Shared helper for the L5 MAIL wave (SMTP / POP3 / IMAP clients).  These three
// text protocols share a line-based request/response shape over Net.Tcp:
//   * SMTP replies are a 3-digit code, a separator ('-' continues, ' ' ends the
//     reply), then text.  ReadSmtpReply loops the continuation lines and returns
//     the final code plus the joined text.
//   * POP3 replies begin '+OK' or '-ERR' on the status line; a data command's
//     body is a sequence of lines terminated by a line that is just '.', with
//     dot-stuffing ('..' at line start -> '.') undone by UnDotStuff.
//   * A message body to be sent (SMTP DATA) is dot-stuffed by DotStuffBody: any
//     line starting with '.' gets a leading '.' added, and the whole is framed
//     by a terminating CRLF.CRLF.
//
// NATIVE BACKEND ONLY (pulls in Net.Tcp -> async.io).

interface

uses
  SysUtils, Net.Tcp;

const
  CRLF = #13#10;

{ Read one SMTP-style reply (possibly multi-line).  Returns the 3-digit code as
  an integer (-1 on protocol/connection error), and in AText the concatenated
  text of every line (each continuation joined with LF).  ARaw, if the caller
  passes it, receives every raw line joined by LF for diagnostics. }
function ReadSmtpReply(AConn: TTcpConn; out ACode: Int;
  out AText: string): Boolean;

{ Dot-stuff and frame a message body for SMTP DATA.  Every CRLF-or-LF-delimited
  line beginning with '.' gets an extra leading '.'; lines are re-joined with
  CRLF and the terminating CRLF.CRLF is appended.  Bare LF line endings in the
  input are normalised to CRLF on output. }
function DotStuffBody(const ABody: string): string;

{ Undo dot-stuffing on a received multi-line body line: a leading '..' becomes
  '.'.  (The lone '.' terminator is handled by the caller, not here.) }
function UnDotStuff(const ALine: string): string;

implementation

function ReadSmtpReply(AConn: TTcpConn; out ACode: Int;
  out AText: string): Boolean;
var
  Line: string;
  Sep: Byte;
begin
  ACode := -1;
  AText := '';
  while True do
  begin
    if not AConn.ReadLine(Line) then
    begin
      { EOF before a complete reply. }
      Result := False;
      Exit;
    end;
    if Length(Line) < 3 then
    begin
      Result := False;
      Exit;
    end;
    { First three bytes are the status code. }
    ACode := (Byte(Line[0]) - 48) * 100
           + (Byte(Line[1]) - 48) * 10
           + (Byte(Line[2]) - 48);
    if Length(Line) > 3 then
    begin
      if AText <> '' then
        AText := AText + #10;
      AText := AText + Copy(Line, 4, Length(Line) - 4);
      Sep := Byte(Line[3]);
    end
    else
      Sep := 32;
    { '-' (45) continues; ' ' (32) or nothing ends the reply. }
    if Sep <> 45 then
    begin
      Result := True;
      Exit;
    end;
  end;
end;

function DotStuffBody(const ABody: string): string;
var
  I, Start, Len: Int;
  Line: string;
  R: string;
begin
  R := '';
  Len := Length(ABody);
  Start := 0;
  I := 0;
  while I <= Len do
  begin
    if (I = Len) or (Byte(ABody[I]) = 10) then
    begin
      Line := Copy(ABody, Start, I - Start);
      { strip a trailing CR from the extracted line }
      if (Length(Line) > 0) and (Byte(Line[Length(Line) - 1]) = 13) then
        Line := Copy(Line, 0, Length(Line) - 1);
      { dot-stuff: a line starting with '.' gets an extra leading '.' }
      if (Length(Line) > 0) and (Byte(Line[0]) = 46) then
        Line := '.' + Line;
      R := R + Line + CRLF;
      Start := I + 1;
      if I = Len then
        Break;
    end;
    I := I + 1;
  end;
  { terminator }
  R := R + '.' + CRLF;
  Result := R;
end;

function UnDotStuff(const ALine: string): string;
begin
  if (Length(ALine) >= 2) and (Byte(ALine[0]) = 46) and (Byte(ALine[1]) = 46) then
    Result := Copy(ALine, 1, Length(ALine) - 1)
  else
    Result := ALine;
end;

end.
