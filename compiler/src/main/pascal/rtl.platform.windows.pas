{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit rtl.platform.windows;
// The Windows platform adapter: TRtlPlatformWindows, and the flat functions
// that belong to an adapter rather than to rtl.platform.abi (_SetArgs,
// _EnvVector, _PathStat, _SysWritePChar).
//
// Milestone M3 implements what the core runtime and console programs need:
// the console writes (WriteLn ends a line with CR LF, design decision D4),
// the program's parameters, Halt, the process id and Sleep.  The file,
// directory, time and process operations are milestone M4; until then each
// reports itself by name and ends the program, rather than returning
// something plausible.

interface

uses
  rtl.platform;

type
  TRtlPlatformWindows = class(TRtlPlatform)
  public
    function FileExists(const APath: string): Boolean; override;
    procedure DeleteFile(const APath: string); override;
    function RenameFile(const AOldPath, ANewPath: string): Boolean; override;
    function ReadFile(const APath: string): string; override;
    procedure WriteFile(const APath, AContent: string); override;
    procedure AppendFile(const APath, AContent: string); override;
    function FileAge(const APath: string): Int64; override;
    function DirectoryExists(const APath: string): Boolean; override;
    function PathKind(const APath: string; AFollowLinks: Boolean): Int32; override;
    function ForceDirectories(const APath: string): Boolean; override;
    function RemoveDir(const APath: string): Boolean; override;
    function GetCurrentDir: string; override;
    function SetCurrentDir(const APath: string): Boolean; override;
    function ListDir(const APath: string): string; override;
    function GetTempDir: string; override;
    function GetTempFileName(const ADir, APrefix: string): string; override;
    function GetProcessID: Int32; override;
    function GetEnvVar(const AName: string): string; override;
    procedure Sleep(AMilliseconds: Int32); override;
    procedure Halt(AExitCode: Int32); override;
    function Exec(const ACmd: string): Int32; override;
    function ParamCount: Int32; override;
    function ParamStr(AIndex: Int32): string; override;
    procedure SysWriteStr(Fd: Int32; S: Pointer); override;
    procedure SysWriteInt(Fd: Int32; N: Int32); override;
    procedure SysWriteInt64(Fd: Int32; N: Int64); override;
    procedure SysWriteUInt64(Fd: Int32; N: UInt64); override;
    procedure SysWriteDouble(Fd: Int32; V: Float64); override;
    procedure SysWriteSingle(Fd: Int32; V: Float32); override;
    procedure SysWriteBool(Fd: Int32; B: Boolean); override;
    procedure SysWriteNewline(Fd: Int32); override;
    function FdOpenRead(Path: Pointer): Int32; override;
    function FdOpenWrite(Path: Pointer): Int32; override;
    function FdOpenAppend(Path: Pointer): Int32; override;
    function FdRead(Fd: Int32; Buf: Pointer; Count: Int): Int; override;
    function FdWrite(Fd: Int32; Buf: Pointer; Count: Int): Int; override;
    function FdSeek(Fd: Int32; Offset: Int64; Origin: Int32): Int64; override;
    function FdSize(Fd: Int32): Int64; override;
    procedure FdClose(Fd: Int32); override;
    function TimeNow: Int64; override;
    function TimeLocalOffsetSecs: Int32; override;
    procedure TimeSplit(Nanos: Int64; out Year, Month, Day, Hour, Min, Sec, NSec: Int32); override;
    function TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec: Int32): Int64; override;
    function TimeIsLeapYear(Year: Int32): Int32; override;
    function TimeDaysInMonth(Year, Month: Int32): Int32; override;
    function ProcessCreate: Pointer; override;
    procedure ProcessSetExe(Proc: Pointer; ExeStr: Pointer); override;
    procedure ProcessAddArg(Proc: Pointer; ArgStr: Pointer); override;
    procedure ProcessExecute(Proc: Pointer); override;
    function ProcessRunning(Proc: Pointer): Int32; override;
    function ProcessReadOutput(Proc: Pointer): Pointer; override;
    procedure ProcessWaitOnExit(Proc: Pointer); override;
    function ProcessExitCode(Proc: Pointer): Int32; override;
    procedure ProcessFree(Proc: Pointer); override;
  end;

{ argc/argv as runtime.start.windows built them, UTF-8; creates the platform
  object. }
procedure _SetArgs(Argc: Int32; Argv: Pointer);
{ The POSIX environment vector has no Windows counterpart: nil. }
function _EnvVector: Pointer;
{ stdlib's IO.Files stat; Windows file metadata is milestone M4. }
function _PathStat(const Path: string; FollowLinks: Int32; AOut: Pointer): Int64;
procedure _SysWritePChar(Fd: Int32; P: PChar);

implementation

function _sys_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
  external name 'write';
procedure _exit_running_handlers(Code: Int32); external name 'exit';
function _IntToStr(N: Int32): Pointer;   external name '_IntToStr';
function _Int64ToStr(N: Int64): Pointer;   external name '_Int64ToStr';
function _UInt64ToStr(N: UInt64): Pointer; external name '_UInt64ToStr';
function _DoubleToStr(V: Float64): Pointer; external name '_DoubleToStr';
function _SingleToStr(V: Float32): Pointer; external name '_SingleToStr';
procedure _StringAddRef(Ptr: Pointer);      external name '_StringAddRef';
procedure _StringRelease(Ptr: Pointer);     external name '_StringRelease';

function GetCurrentProcessId: UInt32;
  external 'kernel32' name 'GetCurrentProcessId';
procedure Win32Sleep(AMilliseconds: UInt32); external 'kernel32' name 'Sleep';

const
  { A Blaise string's length precedes its data. }
  STR_LEN_OFS = -8;

type
  PInt64 = ^Int64;
  PPChar = ^PChar;

var
  GArgC: Int32;
  GArgV: Pointer;

{ The bytes of string data S, from the length in its header. }
function StrBytes(S: Pointer): Int64;
begin
  if S = nil then
    Exit(0);
  Result := PInt64(S + STR_LEN_OFS)^;
end;

procedure WriteAll(Fd: Int32; P: PChar; Len: Int64);
var
  Done: Int64;
begin
  while Len > 0 do
  begin
    Done := _sys_write(Fd, P, Len);
    if Done <= 0 then Exit;
    P := P + Done;
    Len := Len - Done;
  end;
end;

{ Write a string made by one of the _XxxToStr helpers, then release it. }
procedure WriteOwned(Fd: Int32; S: Pointer);
begin
  _StringAddRef(S);
  WriteAll(Fd, PChar(S), StrBytes(S));
  _StringRelease(S);
end;

{ An operation of milestone M4 reached early: say which, and end. }
procedure NotYet(const AName: string);
const
  Prefix = 'TRtlPlatform.';
  Suffix = ' is not implemented on Windows yet'#13#10;
begin
  WriteAll(2, PChar(Prefix), Length(Prefix));
  WriteAll(2, PChar(AName), Length(AName));
  WriteAll(2, PChar(Suffix), Length(Suffix));
  _exit_running_handlers(3);
end;

{ ---- implemented ---- }

procedure TRtlPlatformWindows.SysWriteStr(Fd: Int32; S: Pointer);
begin
  WriteAll(Fd, PChar(S), StrBytes(S));
end;

procedure TRtlPlatformWindows.SysWriteInt(Fd: Int32; N: Int32);
begin
  WriteOwned(Fd, _IntToStr(N));
end;

procedure TRtlPlatformWindows.SysWriteInt64(Fd: Int32; N: Int64);
begin
  WriteOwned(Fd, _Int64ToStr(N));
end;

procedure TRtlPlatformWindows.SysWriteUInt64(Fd: Int32; N: UInt64);
begin
  WriteOwned(Fd, _UInt64ToStr(N));
end;

procedure TRtlPlatformWindows.SysWriteDouble(Fd: Int32; V: Float64);
begin
  WriteOwned(Fd, _DoubleToStr(V));
end;

procedure TRtlPlatformWindows.SysWriteSingle(Fd: Int32; V: Float32);
begin
  WriteOwned(Fd, _SingleToStr(V));
end;

procedure TRtlPlatformWindows.SysWriteBool(Fd: Int32; B: Boolean);
const
  STrue = 'True';
  SFalse = 'False';
begin
  if B then
    WriteAll(Fd, PChar(STrue), Length(STrue))
  else
    WriteAll(Fd, PChar(SFalse), Length(SFalse));
end;

{ D4: a line ends with CR LF on Windows. }
procedure TRtlPlatformWindows.SysWriteNewline(Fd: Int32);
const
  CRLF = #13#10;
begin
  WriteAll(Fd, PChar(CRLF), 2);
end;

function TRtlPlatformWindows.FdWrite(Fd: Int32; Buf: Pointer; Count: Int): Int;
begin
  Result := _sys_write(Fd, Buf, Count);
end;

procedure TRtlPlatformWindows.Halt(AExitCode: Int32);
begin
  _exit_running_handlers(AExitCode);
end;

function TRtlPlatformWindows.ParamCount: Int32;
begin
  if GArgC > 0 then
    Result := GArgC - 1
  else
    Result := 0;
end;

function TRtlPlatformWindows.ParamStr(AIndex: Int32): string;
var
  Slot: PPChar;
begin
  if (GArgV = nil) or (AIndex < 0) or (AIndex >= GArgC) then
    Exit('');
  Slot := PPChar(GArgV + AIndex * SizeOf(Pointer));
  Result := string(Slot^);
end;

function TRtlPlatformWindows.GetProcessID: Int32;
begin
  Result := Int32(GetCurrentProcessId());
end;

procedure TRtlPlatformWindows.Sleep(AMilliseconds: Int32);
begin
  Win32Sleep(UInt32(AMilliseconds));
end;

{ ---- milestone M4 ---- }

function TRtlPlatformWindows.FileExists(const APath: string): Boolean;
begin
  NotYet('FileExists');
  Result := False;
end;

procedure TRtlPlatformWindows.DeleteFile(const APath: string);
begin
  NotYet('DeleteFile');
end;

function TRtlPlatformWindows.RenameFile(const AOldPath, ANewPath: string): Boolean;
begin
  NotYet('RenameFile');
  Result := False;
end;

function TRtlPlatformWindows.ReadFile(const APath: string): string;
begin
  NotYet('ReadFile');
  Result := '';
end;

procedure TRtlPlatformWindows.WriteFile(const APath, AContent: string);
begin
  NotYet('WriteFile');
end;

procedure TRtlPlatformWindows.AppendFile(const APath, AContent: string);
begin
  NotYet('AppendFile');
end;

function TRtlPlatformWindows.FileAge(const APath: string): Int64;
begin
  NotYet('FileAge');
  Result := 0;
end;

function TRtlPlatformWindows.DirectoryExists(const APath: string): Boolean;
begin
  NotYet('DirectoryExists');
  Result := False;
end;

function TRtlPlatformWindows.PathKind(const APath: string; AFollowLinks: Boolean): Int32;
begin
  NotYet('PathKind');
  Result := 0;
end;

function TRtlPlatformWindows.ForceDirectories(const APath: string): Boolean;
begin
  NotYet('ForceDirectories');
  Result := False;
end;

function TRtlPlatformWindows.RemoveDir(const APath: string): Boolean;
begin
  NotYet('RemoveDir');
  Result := False;
end;

function TRtlPlatformWindows.GetCurrentDir: string;
begin
  NotYet('GetCurrentDir');
  Result := '';
end;

function TRtlPlatformWindows.SetCurrentDir(const APath: string): Boolean;
begin
  NotYet('SetCurrentDir');
  Result := False;
end;

function TRtlPlatformWindows.ListDir(const APath: string): string;
begin
  NotYet('ListDir');
  Result := '';
end;

function TRtlPlatformWindows.GetTempDir: string;
begin
  NotYet('GetTempDir');
  Result := '';
end;

function TRtlPlatformWindows.GetTempFileName(const ADir, APrefix: string): string;
begin
  NotYet('GetTempFileName');
  Result := '';
end;

function TRtlPlatformWindows.GetEnvVar(const AName: string): string;
begin
  NotYet('GetEnvVar');
  Result := '';
end;

function TRtlPlatformWindows.Exec(const ACmd: string): Int32;
begin
  NotYet('Exec');
  Result := 0;
end;

function TRtlPlatformWindows.FdOpenRead(Path: Pointer): Int32;
begin
  NotYet('FdOpenRead');
  Result := 0;
end;

function TRtlPlatformWindows.FdOpenWrite(Path: Pointer): Int32;
begin
  NotYet('FdOpenWrite');
  Result := 0;
end;

function TRtlPlatformWindows.FdOpenAppend(Path: Pointer): Int32;
begin
  NotYet('FdOpenAppend');
  Result := 0;
end;

function TRtlPlatformWindows.FdRead(Fd: Int32; Buf: Pointer; Count: Int): Int;
begin
  NotYet('FdRead');
  Result := 0;
end;

function TRtlPlatformWindows.FdSeek(Fd: Int32; Offset: Int64; Origin: Int32): Int64;
begin
  NotYet('FdSeek');
  Result := 0;
end;

function TRtlPlatformWindows.FdSize(Fd: Int32): Int64;
begin
  NotYet('FdSize');
  Result := 0;
end;

procedure TRtlPlatformWindows.FdClose(Fd: Int32);
begin
  NotYet('FdClose');
end;

function TRtlPlatformWindows.TimeNow: Int64;
begin
  NotYet('TimeNow');
  Result := 0;
end;

function TRtlPlatformWindows.TimeLocalOffsetSecs: Int32;
begin
  NotYet('TimeLocalOffsetSecs');
  Result := 0;
end;

procedure TRtlPlatformWindows.TimeSplit(Nanos: Int64; out Year, Month, Day, Hour, Min, Sec, NSec: Int32);
begin
  NotYet('TimeSplit');
end;

function TRtlPlatformWindows.TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec: Int32): Int64;
begin
  NotYet('TimeJoin');
  Result := 0;
end;

function TRtlPlatformWindows.TimeIsLeapYear(Year: Int32): Int32;
begin
  NotYet('TimeIsLeapYear');
  Result := 0;
end;

function TRtlPlatformWindows.TimeDaysInMonth(Year, Month: Int32): Int32;
begin
  NotYet('TimeDaysInMonth');
  Result := 0;
end;

function TRtlPlatformWindows.ProcessCreate: Pointer;
begin
  NotYet('ProcessCreate');
  Result := nil;
end;

procedure TRtlPlatformWindows.ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
begin
  NotYet('ProcessSetExe');
end;

procedure TRtlPlatformWindows.ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
begin
  NotYet('ProcessAddArg');
end;

procedure TRtlPlatformWindows.ProcessExecute(Proc: Pointer);
begin
  NotYet('ProcessExecute');
end;

function TRtlPlatformWindows.ProcessRunning(Proc: Pointer): Int32;
begin
  NotYet('ProcessRunning');
  Result := 0;
end;

function TRtlPlatformWindows.ProcessReadOutput(Proc: Pointer): Pointer;
begin
  NotYet('ProcessReadOutput');
  Result := nil;
end;

procedure TRtlPlatformWindows.ProcessWaitOnExit(Proc: Pointer);
begin
  NotYet('ProcessWaitOnExit');
end;

function TRtlPlatformWindows.ProcessExitCode(Proc: Pointer): Int32;
begin
  NotYet('ProcessExitCode');
  Result := 0;
end;

procedure TRtlPlatformWindows.ProcessFree(Proc: Pointer);
begin
  NotYet('ProcessFree');
end;

{ ---- flat functions ---- }

procedure _SetArgs(Argc: Int32; Argv: Pointer);
begin
  GArgC := Argc;
  GArgV := Argv;
  if GRtlPlatform = nil then
    GRtlPlatform := TRtlPlatformWindows.Create();
end;

function _EnvVector: Pointer;
begin
  Result := nil;
end;

function _PathStat(const Path: string; FollowLinks: Int32; AOut: Pointer): Int64;
begin
  NotYet('_PathStat');
  Result := -1;
end;

procedure _SysWritePChar(Fd: Int32; P: PChar);
var
  Len: Int64;
begin
  if P = nil then Exit;
  Len := 0;
  while P[Len] <> #0 do
    Len := Len + 1;
  WriteAll(Fd, P, Len);
end;

end.
