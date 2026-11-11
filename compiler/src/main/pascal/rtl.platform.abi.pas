{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit rtl.platform.abi;
// Blaise RTL -- the flat platform ABI.
//
// The compiler emits calls to these underscore functions (_SysWriteStr,
// _FileExists, _TimeNow, ...), and stdlib units bind some of them through
// `external name`.  Each one delegates to the platform object GRtlPlatform, so
// none of them knows which OS it runs on: the same unit serves every target,
// and a new target supplies only its TRtlPlatform subclass.  They lived in
// rtl.platform.posix until the Windows target needed them without the POSIX
// adapter.
//
// The flat functions that are not plain delegations stay with their adapter:
// _SetArgs (it creates the adapter's platform object), _EnvVector and
// _PathStat (POSIX layouts), and _SysWritePChar.

interface

uses
  rtl.platform;

function  _ParamCount: Int32;
function  _ParamStr(Index: Int32): Pointer;

{ File operations }
function  _FileExists(const Path: string): Int32;
procedure _DeleteFile(const Path: string);
function  _RenameFile(const OldPath, NewPath: string): Int32;
function  _ReadFile(const Path: string): Pointer;
procedure _WriteFile(const Path, Content: string);
procedure _AppendFile(const Path, Content: string);
function  _FileAge(const Path: string): Int64;

{ Directory operations }
function  _DirectoryExists(const Path: string): Int32;
{ Not a compiler builtin: stdlib's IO.Files imports it via `external name`. }
function  _PathKind(const Path: string; FollowLinks: Int32): Int32;
function  _ForceDirectories(const Path: string): Int32;
procedure _RemoveDir(const Path: string);
function  _GetCurrentDir: Pointer;
function  _SetCurrentDir(const Path: string): Int32;
function  _ListDir(const Path: string): Pointer;

{ OS utilities }
function  _GetTempDir: Pointer;
function  _GetTempFileName(const Dir, Prefix: string): Pointer;
function  _GetProcessID: Int32;
function  _GetEnvVar(const Name: string): Pointer;
procedure _Sleep(Ms: Int32);
procedure _Halt(Code: Int32);
function  _Exec(const Cmd: string): Int32;

{ Console I/O }
procedure _SysWriteStr(Fd: Int32; S: Pointer);
procedure _SysWriteInt(Fd: Int32; N: Int32);
procedure _SysWriteInt64(Fd: Int32; N: Int64);
procedure _SysWriteUInt64(Fd: Int32; N: UInt64);
procedure _SysWriteDouble(Fd: Int32; V: Float64);
procedure _SysWriteSingle(Fd: Int32; V: Float32);
procedure _SysWriteBool(Fd: Int32; B: Boolean);
procedure _SysWriteNewline(Fd: Int32);

{ File-descriptor primitives }
function  _FdOpenRead(Path: Pointer): Int32;
function  _FdOpenWrite(Path: Pointer): Int32;
function  _FdOpenAppend(Path: Pointer): Int32;
function  _FdRead(Fd: Int32; Buf: Pointer; Count: Int): Int;
function  _FdWrite(Fd: Int32; Buf: Pointer; Count: Int): Int;
function  _FdSeek(Fd: Int32; Offset: Int64; Origin: Int32): Int64;
function  _FdSize(Fd: Int32): Int64;
procedure _FdClose(Fd: Int32);

{ Date/Time }
function  _TimeNow: Int64;
function  _TimeLocalOffsetSecs: Int32;
procedure _TimeSplit(Nanos: Int64;
  out Year, Month, Day, Hour, Min, Sec, NSec: Int32);
function  _TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec: Int32): Int64;
function  _TimeIsLeapYear(Year: Int32): Int32;
function  _TimeDaysInMonth(Year, Month: Int32): Int32;

{ Process management }
function  _ProcessCreate: Pointer;
procedure _ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
procedure _ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
procedure _ProcessExecute(Proc: Pointer);
function  _ProcessRunning(Proc: Pointer): Int32;
function  _ProcessReadOutput(Proc: Pointer): Pointer;
procedure _ProcessWaitOnExit(Proc: Pointer);
function  _ProcessExitCode(Proc: Pointer): Int32;
procedure _ProcessFree(Proc: Pointer);

implementation

function _ParamCount: Int32;
begin
  Result := GRtlPlatform.ParamCount();
end;

function _ParamStr(Index: Int32): Pointer;
begin
  Result := Pointer(GRtlPlatform.ParamStr(Index));
end;

function _FileExists(const Path: string): Int32;
begin
  if GRtlPlatform.FileExists(Path) then Result := 1 else Result := 0;
end;

procedure _DeleteFile(const Path: string);
begin
  GRtlPlatform.DeleteFile(Path);
end;

function _RenameFile(const OldPath, NewPath: string): Int32;
begin
  if GRtlPlatform.RenameFile(OldPath, NewPath) then Result := 1 else Result := 0;
end;

function _ReadFile(const Path: string): Pointer;
begin
  Result := Pointer(GRtlPlatform.ReadFile(Path));
end;

procedure _WriteFile(const Path, Content: string);
begin
  GRtlPlatform.WriteFile(Path, Content);
end;

procedure _AppendFile(const Path, Content: string);
begin
  GRtlPlatform.AppendFile(Path, Content);
end;

function _FileAge(const Path: string): Int64;
begin
  Result := GRtlPlatform.FileAge(Path);
end;

function _DirectoryExists(const Path: string): Int32;
begin
  if GRtlPlatform.DirectoryExists(Path) then Result := 1 else Result := 0;
end;

function _PathKind(const Path: string; FollowLinks: Int32): Int32;
begin
  Result := GRtlPlatform.PathKind(Path, FollowLinks <> 0);
end;

function _ForceDirectories(const Path: string): Int32;
begin
  if GRtlPlatform.ForceDirectories(Path) then Result := 1 else Result := 0;
end;

procedure _RemoveDir(const Path: string);
begin
  GRtlPlatform.RemoveDir(Path);
end;

function _GetCurrentDir: Pointer;
begin
  Result := Pointer(GRtlPlatform.GetCurrentDir());
end;

function _SetCurrentDir(const Path: string): Int32;
begin
  if GRtlPlatform.SetCurrentDir(Path) then Result := 1 else Result := 0;
end;

function _ListDir(const Path: string): Pointer;
begin
  Result := Pointer(GRtlPlatform.ListDir(Path));
end;

function _GetTempDir: Pointer;
begin
  Result := Pointer(GRtlPlatform.GetTempDir());
end;

function _GetTempFileName(const Dir, Prefix: string): Pointer;
begin
  Result := Pointer(GRtlPlatform.GetTempFileName(Dir, Prefix));
end;

function _GetProcessID: Int32;
begin
  Result := GRtlPlatform.GetProcessID();
end;

function _GetEnvVar(const Name: string): Pointer;
begin
  Result := Pointer(GRtlPlatform.GetEnvVar(Name));
end;

procedure _Sleep(Ms: Int32);
begin
  GRtlPlatform.Sleep(Ms);
end;

procedure _Halt(Code: Int32);
begin
  GRtlPlatform.Halt(Code);
end;

function _Exec(const Cmd: string): Int32;
begin
  Result := GRtlPlatform.Exec(Cmd);
end;

procedure _SysWriteStr(Fd: Int32; S: Pointer);
begin
  GRtlPlatform.SysWriteStr(Fd, S);
end;

{ Write/WriteLn of a PChar: the bytes up to its NUL.  A PChar need not point
  into a Blaise string, so there is no length header in front of it to read
  (that is _SysWriteStr's contract). }
procedure _SysWriteInt(Fd: Int32; N: Int32);
begin
  GRtlPlatform.SysWriteInt(Fd, N);
end;

procedure _SysWriteInt64(Fd: Int32; N: Int64);
begin
  GRtlPlatform.SysWriteInt64(Fd, N);
end;

procedure _SysWriteUInt64(Fd: Int32; N: UInt64);
begin
  GRtlPlatform.SysWriteUInt64(Fd, N);
end;

procedure _SysWriteDouble(Fd: Int32; V: Float64);
begin
  GRtlPlatform.SysWriteDouble(Fd, V);
end;

procedure _SysWriteSingle(Fd: Int32; V: Float32);
begin
  GRtlPlatform.SysWriteSingle(Fd, V);
end;

procedure _SysWriteBool(Fd: Int32; B: Boolean);
begin
  GRtlPlatform.SysWriteBool(Fd, B);
end;

procedure _SysWriteNewline(Fd: Int32);
begin
  GRtlPlatform.SysWriteNewline(Fd);
end;

function _FdOpenRead(Path: Pointer): Int32;
begin
  Result := GRtlPlatform.FdOpenRead(Path);
end;

function _FdOpenWrite(Path: Pointer): Int32;
begin
  Result := GRtlPlatform.FdOpenWrite(Path);
end;

function _FdOpenAppend(Path: Pointer): Int32;
begin
  Result := GRtlPlatform.FdOpenAppend(Path);
end;

function _FdRead(Fd: Int32; Buf: Pointer; Count: Int): Int;
begin
  Result := GRtlPlatform.FdRead(Fd, Buf, Count);
end;

function _FdWrite(Fd: Int32; Buf: Pointer; Count: Int): Int;
begin
  Result := GRtlPlatform.FdWrite(Fd, Buf, Count);
end;

function _FdSeek(Fd: Int32; Offset: Int64; Origin: Int32): Int64;
begin
  Result := GRtlPlatform.FdSeek(Fd, Offset, Origin);
end;

function _FdSize(Fd: Int32): Int64;
begin
  Result := GRtlPlatform.FdSize(Fd);
end;

procedure _FdClose(Fd: Int32);
begin
  GRtlPlatform.FdClose(Fd);
end;

function _TimeNow: Int64;
begin
  Result := GRtlPlatform.TimeNow();
end;

function _TimeLocalOffsetSecs: Int32;
begin
  Result := GRtlPlatform.TimeLocalOffsetSecs();
end;

procedure _TimeSplit(Nanos: Int64;
  out Year, Month, Day, Hour, Min, Sec, NSec: Int32);
begin
  GRtlPlatform.TimeSplit(Nanos, Year, Month, Day, Hour, Min, Sec, NSec);
end;

function _TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec: Int32): Int64;
begin
  Result := GRtlPlatform.TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec);
end;

function _TimeIsLeapYear(Year: Int32): Int32;
begin
  Result := GRtlPlatform.TimeIsLeapYear(Year);
end;

function _TimeDaysInMonth(Year, Month: Int32): Int32;
begin
  Result := GRtlPlatform.TimeDaysInMonth(Year, Month);
end;

function _ProcessCreate: Pointer;
begin
  Result := GRtlPlatform.ProcessCreate();
end;

procedure _ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
begin
  GRtlPlatform.ProcessSetExe(Proc, ExeStr);
end;

procedure _ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
begin
  GRtlPlatform.ProcessAddArg(Proc, ArgStr);
end;

procedure _ProcessExecute(Proc: Pointer);
begin
  GRtlPlatform.ProcessExecute(Proc);
end;

function _ProcessRunning(Proc: Pointer): Int32;
begin
  Result := GRtlPlatform.ProcessRunning(Proc);
end;

function _ProcessReadOutput(Proc: Pointer): Pointer;
begin
  Result := GRtlPlatform.ProcessReadOutput(Proc);
end;

procedure _ProcessWaitOnExit(Proc: Pointer);
begin
  GRtlPlatform.ProcessWaitOnExit(Proc);
end;

function _ProcessExitCode(Proc: Pointer): Int32;
begin
  Result := GRtlPlatform.ProcessExitCode(Proc);
end;

procedure _ProcessFree(Proc: Pointer);
begin
  GRtlPlatform.ProcessFree(Proc);
end;

end.
