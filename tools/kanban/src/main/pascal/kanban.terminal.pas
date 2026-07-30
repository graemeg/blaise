{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit kanban.terminal;

interface

const
  KEY_NONE      = -1;
  KEY_ENTER     = 13;
  KEY_ESCAPE    = 27;
  KEY_BACKSPACE = 127;
  KEY_UP        = 1000;
  KEY_DOWN      = 1001;
  KEY_LEFT      = 1002;
  KEY_RIGHT     = 1003;
  KEY_HOME      = 1004;
  KEY_END       = 1005;
  KEY_TAB       = 9;

  COLOR_RESET   = 0;
  COLOR_RED     = 31;
  COLOR_GREEN   = 32;
  COLOR_YELLOW  = 33;
  COLOR_BLUE    = 34;
  COLOR_MAGENTA = 35;
  COLOR_CYAN    = 36;
  COLOR_WHITE   = 37;
  COLOR_GREY    = 90;

  STDIN_FD  = 0;
  STDOUT_FD = 1;

  { ---- Platform-specific terminal constants ---- }
{$IFDEF FREEBSD}
  { FreeBSD ioctl commands for termios (from sys/ttycom.h). }
  TIOCGETA   = $402C7413;   { _IOR('t', 19, struct termios) — get termios }
  TIOCSETA   = $802C7414;   { _IOW('t', 20, struct termios) — set (TCSANOW) }
  TIOCSETAW  = $802C7415;   { _IOW('t', 21, struct termios) — set (TCSADRAIN) }
  TIOCSETAF  = $802C7416;   { _IOW('t', 22, struct termios) — set (TCSAFLUSH) }
  TIOCGWINSZ = $40087468;   { _IOR('t', 104, struct winsize) }

  ECHO_  = 8;
  ICANON = 256;
  ISIG   = 128;
  IEXTEN = 1024;
  ICRNL  = 256;
  IXON   = 512;

  VMIN_IDX  = 16;
  VTIME_IDX = 17;
  NCCS_SIZE = 20;
{$ENDIF}
{$IFDEF LINUX}
  { Linux ioctl commands for termios (from asm-generic/ioctls.h). }
  TCGETS     = $5401;
  TCSETSF    = $5404;       { set + flush (TCSAFLUSH) }
  TIOCGWINSZ = $5413;

  ECHO_  = 8;
  ICANON = 2;
  ISIG   = 1;
  IEXTEN = 32768;
  ICRNL  = 256;
  IXON   = 1024;

  VMIN_IDX  = 6;
  VTIME_IDX = 5;
  NCCS_SIZE = 32;
{$ENDIF}

  IFLAG_MASK = ICRNL or IXON;
  LFLAG_MASK = ECHO_ or ICANON or ISIG or IEXTEN;

type
  TTermios = record
    IFlag:  Integer;
    OFlag:  Integer;
    CFlag:  Integer;
    LFlag:  Integer;
{$IFDEF LINUX}
    Line:   Byte;
{$ENDIF}
    CC:     array[0..NCCS_SIZE - 1] of Byte;
    ISpeed: Integer;
    OSpeed: Integer;
  end;
  PTermios = ^TTermios;

  TWinSize = record
    Row:    Word;
    Col:    Word;
    XPixel: Word;
    YPixel: Word;
  end;
  PWinSize = ^TWinSize;

{ ioctl is a direct syscall provided by the runtime. }
function sys_ioctl(Fd: Integer; Request: Int64; Arg: Pointer): Integer;
  external name 'ioctl';
function libc_read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
  external name 'read';

{ tcgetattr / tcsetattr implemented as ioctl wrappers (see implementation). }
function tcgetattr(Fd: Integer; T: PTermios): Integer;
function tcsetattr(Fd: Integer; Action: Integer; T: PTermios): Integer;
function term_ioctl(Fd: Integer; Request: Int64; Arg: Pointer): Integer;

type
  TTerminal = class
    FRows: Integer;
    FCols: Integer;
    FBuf: string;
    FSaved: Boolean;
    procedure EnableRawMode;
    procedure DisableRawMode;
    procedure QuerySize;
    function ReadByte: Integer;
    function ReadKey: Integer;
    procedure BufClear;
    procedure BufWrite(const S: string);
    procedure BufFlush;
    procedure HideCursor;
    procedure ShowCursor;
    procedure MoveTo(Row, Col: Integer);
    procedure ClearScreen;
    procedure SetFg(Color: Integer);
    procedure SetBg(Color: Integer);
    procedure SetBold;
    procedure ResetAttr;
    procedure DrawBox(Row, Col, Width, Height, Color: Integer; const Title: string);
    procedure DrawHLine(Row, Col, Width: Integer);
    property Rows: Integer read FRows;
    property Cols: Integer read FCols;
  end;

implementation

uses StrUtils;

{ tcgetattr: get terminal attributes via ioctl. }
function tcgetattr(Fd: Integer; T: PTermios): Integer;
begin
{$IFDEF FREEBSD}
  Result := sys_ioctl(Fd, TIOCGETA, T);
{$ENDIF}
{$IFDEF LINUX}
  Result := sys_ioctl(Fd, TCGETS, T);
{$ENDIF}
end;

{ tcsetattr: set terminal attributes via ioctl.
  Action is ignored — we always use TCSAFLUSH (the only mode the kanban app
  needs).  If other modes are needed later, map Action 0/1/2 to the
  corresponding platform ioctl. }
function tcsetattr(Fd: Integer; Action: Integer; T: PTermios): Integer;
begin
{$IFDEF FREEBSD}
  Result := sys_ioctl(Fd, TIOCSETAF, T);
{$ENDIF}
{$IFDEF LINUX}
  Result := sys_ioctl(Fd, TCSETSF, T);
{$ENDIF}
end;

{ Thin wrapper so the TTerminal class can call ioctl for TIOCGWINSZ. }
function term_ioctl(Fd: Integer; Request: Int64; Arg: Pointer): Integer;
begin
  Result := sys_ioctl(Fd, Request, Arg);
end;

var
  GOrigTermios: TTermios;

procedure TTerminal.EnableRawMode;
var
  Raw: TTermios;
  P: PChar;
begin
  if not FSaved then
  begin
    tcgetattr(STDIN_FD, @GOrigTermios);
    FSaved := True
  end;
  Raw := GOrigTermios;
  Raw.IFlag := Raw.IFlag and (IFLAG_MASK xor -1);
  Raw.LFlag := Raw.LFlag and (LFLAG_MASK xor -1);
  P := PChar(@Raw.CC);
  P[VMIN_IDX] := #0;
  P[VTIME_IDX] := #1;
  tcsetattr(STDIN_FD, 0, @Raw)
end;

procedure TTerminal.DisableRawMode;
begin
  if FSaved then
    tcsetattr(STDIN_FD, 0, @GOrigTermios)
end;

procedure TTerminal.QuerySize;
var
  WS: TWinSize;
begin
  if term_ioctl(STDOUT_FD, TIOCGWINSZ, @WS) = 0 then
  begin
    FRows := WS.Row;
    FCols := WS.Col
  end
  else
  begin
    FRows := 24;
    FCols := 80
  end
end;

function TTerminal.ReadByte: Integer;
var
  Ch: Byte;
  N: Int64;
begin
  N := libc_read(STDIN_FD, @Ch, 1);
  if N <= 0 then
    Result := -1
  else
    Result := Ch
end;

function TTerminal.ReadKey: Integer;
var
  B1, B2, B3: Integer;
begin
  B1 := Self.ReadByte();
  if B1 = KEY_NONE then Exit(KEY_NONE);

  if B1 <> 27 then Exit(B1);

  B2 := Self.ReadByte();
  if B2 = KEY_NONE then Exit(KEY_ESCAPE);

  if B2 = 91 then
  begin
    B3 := Self.ReadByte();
    if B3 = 65 then Exit(KEY_UP);
    if B3 = 66 then Exit(KEY_DOWN);
    if B3 = 67 then Exit(KEY_RIGHT);
    if B3 = 68 then Exit(KEY_LEFT);
    if B3 = 72 then Exit(KEY_HOME);
    if B3 = 70 then Exit(KEY_END)
  end;

  Result := KEY_ESCAPE
end;

procedure TTerminal.BufClear;
begin
  FBuf := ''
end;

procedure TTerminal.BufWrite(const S: string);
begin
  FBuf := FBuf + S
end;

procedure TTerminal.BufFlush;
begin
  if Length(FBuf) > 0 then
    Write(FBuf);
  FBuf := ''
end;

procedure TTerminal.HideCursor;
begin
  Self.BufWrite(Chr(27) + '[?25l')
end;

procedure TTerminal.ShowCursor;
begin
  Self.BufWrite(Chr(27) + '[?25h')
end;

procedure TTerminal.MoveTo(Row, Col: Integer);
begin
  Self.BufWrite(Chr(27) + '[' + IntToStr(Row) + ';' + IntToStr(Col) + 'H')
end;

procedure TTerminal.ClearScreen;
begin
  Self.BufWrite(Chr(27) + '[2J');
  Self.BufWrite(Chr(27) + '[H')
end;

procedure TTerminal.SetFg(Color: Integer);
begin
  Self.BufWrite(Chr(27) + '[' + IntToStr(Color) + 'm')
end;

procedure TTerminal.SetBg(Color: Integer);
begin
  Self.BufWrite(Chr(27) + '[' + IntToStr(Color + 10) + 'm')
end;

procedure TTerminal.SetBold;
begin
  Self.BufWrite(Chr(27) + '[1m')
end;

procedure TTerminal.ResetAttr;
begin
  Self.BufWrite(Chr(27) + '[0m')
end;

procedure TTerminal.DrawBox(Row, Col, Width, Height, Color: Integer; const Title: string);
var
  I: Integer;
  TitleStr: string;
begin
  Self.SetFg(Color);
  Self.MoveTo(Row, Col);
  Self.BufWrite(Chr(226) + Chr(149) + Chr(173));
  I := 0;
  while I < Width - 2 do
  begin
    Self.BufWrite(Chr(226) + Chr(148) + Chr(128));
    I := I + 1
  end;
  Self.BufWrite(Chr(226) + Chr(149) + Chr(174));

  if Length(Title) > 0 then
  begin
    TitleStr := ' ' + Title + ' ';
    Self.MoveTo(Row, Col + 2);
    Self.SetBold();
    Self.BufWrite(TitleStr);
    Self.ResetAttr();
    Self.SetFg(Color)
  end;

  I := 1;
  while I < Height - 1 do
  begin
    Self.MoveTo(Row + I, Col);
    Self.BufWrite(Chr(226) + Chr(148) + Chr(130));
    Self.MoveTo(Row + I, Col + Width - 1);
    Self.BufWrite(Chr(226) + Chr(148) + Chr(130));
    I := I + 1
  end;

  Self.MoveTo(Row + Height - 1, Col);
  Self.BufWrite(Chr(226) + Chr(149) + Chr(176));
  I := 0;
  while I < Width - 2 do
  begin
    Self.BufWrite(Chr(226) + Chr(148) + Chr(128));
    I := I + 1
  end;
  Self.BufWrite(Chr(226) + Chr(149) + Chr(175));
  Self.ResetAttr()
end;

procedure TTerminal.DrawHLine(Row, Col, Width: Integer);
var
  I: Integer;
begin
  Self.MoveTo(Row, Col);
  I := 0;
  while I < Width do
  begin
    Self.BufWrite(Chr(226) + Chr(148) + Chr(128));
    I := I + 1
  end
end;

end.
