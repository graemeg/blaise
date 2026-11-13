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
// Every operation calls the Win32 W APIs: a path or other string crosses the
// boundary as NUL-terminated UTF-16, converted from and back to the RTL's
// UTF-8 here (docs/language-rationale.adoc, "Windows Win32 / GDI").  Both '/'
// and '\' separate path components on input; paths the adapter makes, such
// as GetCurrentDir and GetTempDir, use '\'.  WriteLn ends a line with CR LF
// (design decision D4).
//
// A file the adapter opens is a descriptor from runtime.syscall.windows's
// table, so FdRead, FdWrite and the rest take the same Int32 descriptors as
// on POSIX.  A child process's standard output and error share one pipe, as
// on POSIX; Exec runs its command through cmd.exe /c.

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
    function ReadLink(const APath: string): string; override;
    function MakeExecutable(const APath: string): Boolean; override;
    function RandomBytes(ABuf: Pointer; ACount: Int): Boolean; override;
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
    function FsClose(Fd: Int32): Int32; override;
    function FsUnlink(const APath: string): Int32; override;
    function FsRmdir(const APath: string): Int32; override;
    function FsMkdir(const APath: string; AMode: Int32): Int32; override;
    function FsRename(const AOldPath, ANewPath: string): Int32; override;
    function FsChmod(const APath: string; AMode: Int32): Int32; override;
    function FsSymlink(const ATarget, ALinkPath: string): Int32; override;
    function FsReadlink(const APath: string; ABuf: Pointer; ASize: Int64): Int64; override;
    function FsAccess(const APath: string; AMode: Int32): Int32; override;
    function FsSetModified(const APath: string; ASec, ANSec: Int64): Int32; override;
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
{ The environment as a nil-terminated array of 'NAME=VALUE' UTF-8 C strings,
  built from GetEnvironmentStringsW on first use.  The per-drive entries
  Windows keeps (their names start with '=') are left out. }
function _EnvVector: Pointer;
{ stdlib's IO.Files stat, filled as rtl.platform.posix fills it.  Mode is
  0755 for a directory, 0444 for a read-only file and 0644 otherwise. }
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
function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);       external name '_BlaiseFreeMem';
function _WinHandleOfFd(Fd: Int32): Pointer;  external name '_WinHandleOfFd';
function _WinFdAdd(AHandle: Pointer): Int32;  external name '_WinFdAdd';
function _WinFdRemove(Fd: Int32): Pointer;    external name '_WinFdRemove';
function _WinFdClose(Fd: Int32): Int32;       external name '_WinFdClose';
function _DaysFromCivil(Y, M, D: Int64): Int64; external name '_DaysFromCivil';
procedure _CivilFromDays(Z: Int64; var Y, M, D: Int64);
  external name '_CivilFromDays';

{ ---- bcrypt ---- }

function W32BCryptGenRandom(AAlgorithm: Pointer; ABuf: Pointer; ACount: UInt32;
  AFlags: UInt32): Int32; external 'bcrypt' name 'BCryptGenRandom';

const
  BCRYPT_USE_SYSTEM_PREFERRED_RNG = 2;

{ ---- kernel32 ---- }

function W32GetCurrentProcessId: UInt32;
  external 'kernel32' name 'GetCurrentProcessId';
procedure W32Sleep(AMilliseconds: UInt32); external 'kernel32' name 'Sleep';
function W32GetLastError: UInt32; external 'kernel32' name 'GetLastError';
function W32MultiByteToWideChar(ACodePage, AFlags: UInt32; AMulti: Pointer;
  AMultiCount: Int32; AWide: Pointer; AWideCount: Int32): Int32;
  external 'kernel32' name 'MultiByteToWideChar';
function W32WideCharToMultiByte(ACodePage, AFlags: UInt32; AWide: Pointer;
  AWideCount: Int32; AMulti: Pointer; AMultiSize: Int32; ADefault: Pointer;
  AUsedDefault: Pointer): Int32; external 'kernel32' name 'WideCharToMultiByte';
function W32CreateFileW(AName: Pointer; AAccess, AShare: UInt32;
  ASecurity: Pointer; ADisposition, AFlags: UInt32;
  ATemplate: Pointer): Pointer; external 'kernel32' name 'CreateFileW';
function W32ReadFile(AFile: Pointer; ABuffer: Pointer; ACount: UInt32;
  ARead: Pointer; AOverlapped: Pointer): Int32;
  external 'kernel32' name 'ReadFile';
function W32WriteFile(AFile: Pointer; ABuffer: Pointer; ACount: UInt32;
  AWritten: Pointer; AOverlapped: Pointer): Int32;
  external 'kernel32' name 'WriteFile';
function W32CloseHandle(AHandle: Pointer): Int32;
  external 'kernel32' name 'CloseHandle';
function W32GetFileSizeEx(AFile: Pointer; ASize: Pointer): Int32;
  external 'kernel32' name 'GetFileSizeEx';
function W32SetFilePointerEx(AFile: Pointer; ADistance: Int64;
  ANewPos: Pointer; AMethod: UInt32): Int32;
  external 'kernel32' name 'SetFilePointerEx';
function W32DeleteFileW(AName: Pointer): Int32;
  external 'kernel32' name 'DeleteFileW';
function W32MoveFileExW(AOld, ANew: Pointer; AFlags: UInt32): Int32;
  external 'kernel32' name 'MoveFileExW';
function W32GetFileAttributesW(AName: Pointer): UInt32;
  external 'kernel32' name 'GetFileAttributesW';
function W32GetFileAttributesExW(AName: Pointer; ALevel: Int32;
  AInfo: Pointer): Int32; external 'kernel32' name 'GetFileAttributesExW';
function W32GetFileInformationByHandle(AFile: Pointer; AInfo: Pointer): Int32;
  external 'kernel32' name 'GetFileInformationByHandle';
function W32CreateDirectoryW(AName: Pointer; ASecurity: Pointer): Int32;
  external 'kernel32' name 'CreateDirectoryW';
function W32RemoveDirectoryW(AName: Pointer): Int32;
  external 'kernel32' name 'RemoveDirectoryW';
function W32GetCurrentDirectoryW(ASize: UInt32; ABuffer: Pointer): UInt32;
  external 'kernel32' name 'GetCurrentDirectoryW';
function W32SetCurrentDirectoryW(AName: Pointer): Int32;
  external 'kernel32' name 'SetCurrentDirectoryW';
function W32FindFirstFileW(AName: Pointer; AData: Pointer): Pointer;
  external 'kernel32' name 'FindFirstFileW';
function W32FindNextFileW(AFind: Pointer; AData: Pointer): Int32;
  external 'kernel32' name 'FindNextFileW';
function W32FindClose(AFind: Pointer): Int32;
  external 'kernel32' name 'FindClose';
function W32GetEnvironmentVariableW(AName: Pointer; ABuffer: Pointer;
  ASize: UInt32): UInt32; external 'kernel32' name 'GetEnvironmentVariableW';
function W32GetEnvironmentStringsW: Pointer;
  external 'kernel32' name 'GetEnvironmentStringsW';
function W32GetTempPathW(ASize: UInt32; ABuffer: Pointer): UInt32;
  external 'kernel32' name 'GetTempPathW';
procedure W32GetSystemTimePreciseAsFileTime(ATime: Pointer);
  external 'kernel32' name 'GetSystemTimePreciseAsFileTime';
function W32GetTimeZoneInformation(AInfo: Pointer): UInt32;
  external 'kernel32' name 'GetTimeZoneInformation';
function W32QueryPerformanceCounter(ACount: Pointer): Int32;
  external 'kernel32' name 'QueryPerformanceCounter';
function W32GetStdHandle(AStdHandle: UInt32): Pointer;
  external 'kernel32' name 'GetStdHandle';
function W32CreatePipe(ARead, AWrite: Pointer; ASecurity: Pointer;
  ASize: UInt32): Int32; external 'kernel32' name 'CreatePipe';
function W32SetHandleInformation(AHandle: Pointer; AMask,
  AFlags: UInt32): Int32; external 'kernel32' name 'SetHandleInformation';
function W32CreateProcessW(AApplication: Pointer; ACommandLine: Pointer;
  AProcessAttributes, AThreadAttributes: Pointer; AInheritHandles: Int32;
  ACreationFlags: UInt32; AEnvironment: Pointer; ACurrentDirectory: Pointer;
  AStartupInfo: Pointer; AProcessInfo: Pointer): Int32;
  external 'kernel32' name 'CreateProcessW';
function W32WaitForSingleObject(AHandle: Pointer; AMilliseconds: UInt32): UInt32;
  external 'kernel32' name 'WaitForSingleObject';
function W32GetExitCodeProcess(AProcess: Pointer; ACode: Pointer): Int32;
  external 'kernel32' name 'GetExitCodeProcess';
procedure W32SetLastError(ACode: UInt32); external 'kernel32' name 'SetLastError';
function W32SetFileAttributesW(AName: Pointer; AAttrs: UInt32): Int32;
  external 'kernel32' name 'SetFileAttributesW';
{ Returns a BOOLEAN (one byte), not a BOOL. }
function W32CreateSymbolicLinkW(ALink, ATarget: Pointer; AFlags: UInt32): Byte;
  external 'kernel32' name 'CreateSymbolicLinkW';
function W32DeviceIoControl(ADevice: Pointer; ACode: UInt32; AIn: Pointer;
  AInSize: UInt32; AOut: Pointer; AOutSize: UInt32; AReturned: Pointer;
  AOverlapped: Pointer): Int32; external 'kernel32' name 'DeviceIoControl';
function W32SetFileTime(AFile: Pointer; ACreation, AAccess,
  AWrite: Pointer): Int32; external 'kernel32' name 'SetFileTime';

const
  CP_UTF8 = 65001;
  GENERIC_READ = $80000000;
  GENERIC_WRITE = $40000000;
  FILE_APPEND_DATA = $0004;
  SYNCHRONIZE = $00100000;
  FILE_SHARE_ALL = $0007;         { read, write and delete }
  CREATE_NEW = 1;
  CREATE_ALWAYS = 2;
  OPEN_EXISTING = 3;
  OPEN_ALWAYS = 4;
  FILE_ATTRIBUTE_READONLY = $0001;
  FILE_ATTRIBUTE_DIRECTORY = $0010;
  FILE_ATTRIBUTE_NORMAL = $0080;
  FILE_ATTRIBUTE_REPARSE_POINT = $0400;
  FILE_FLAG_BACKUP_SEMANTICS = $02000000;
  FILE_FLAG_OPEN_REPARSE_POINT = $00200000;
  FILE_WRITE_ATTRIBUTES = $0100;
  SYMBOLIC_LINK_FLAG_DIRECTORY = $1;
  SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE = $2;
  FSCTL_GET_REPARSE_POINT = $000900A8;
  IO_REPARSE_TAG_MOUNT_POINT = $A0000003;
  IO_REPARSE_TAG_SYMLINK = $A000000C;
  { MAXIMUM_REPARSE_DATA_BUFFER_SIZE }
  REPARSE_BUF_SIZE = 16384;
  ERROR_ACCESS_DENIED = 5;
  ERROR_INVALID_PARAMETER = 87;
  ERROR_NOT_A_REPARSE_POINT = 4390;
  INVALID_FILE_ATTRIBUTES = $FFFFFFFF;
  MOVEFILE_REPLACE_EXISTING = $0001;
  MOVEFILE_COPY_ALLOWED = $0002;
  ERROR_HANDLE_EOF = 38;
  ERROR_FILE_EXISTS = 80;
  ERROR_BROKEN_PIPE = 109;
  ERROR_ALREADY_EXISTS = 183;
  STD_INPUT_HANDLE = UInt32(-10);
  STD_OUTPUT_HANDLE = UInt32(-11);
  STD_ERROR_HANDLE = UInt32(-12);
  HANDLE_FLAG_INHERIT = $0001;
  STARTF_USESTDHANDLES = $0100;
  INFINITE = $FFFFFFFF;
  WAIT_TIMEOUT = 258;
  TIME_ZONE_ID_STANDARD = 1;
  TIME_ZONE_ID_DAYLIGHT = 2;
  { One ReadFile or WriteFile moves at most this many bytes. }
  MAX_IO_CHUNK = $40000000;
  { 100 ns intervals between 1601-01-01, the FILETIME epoch, and 1970-01-01. }
  FILETIME_UNIX_EPOCH = 116444736000000000;
  NS_PER_SEC = 1000000000;
  { The exit code of a child that could not be started, as a shell reports a
    command it cannot find. }
  EXIT_NOT_STARTED = 127;

  { WIN32_FILE_ATTRIBUTE_DATA, filled by GetFileAttributesExW. }
  FAD_SIZE = 36;
  FAD_ATTRS = 0;
  FAD_WRITE_TIME = 20;
  FAD_SIZE_HIGH = 28;
  FAD_SIZE_LOW = 32;
  { BY_HANDLE_FILE_INFORMATION. }
  BHI_SIZE = 52;
  BHI_ATTRS = 0;
  BHI_WRITE_TIME = 20;
  BHI_SIZE_HIGH = 32;
  BHI_SIZE_LOW = 36;
  { WIN32_FIND_DATAW: the name is 260 UTF-16 units at offset 44. }
  FIND_DATA_SIZE = 592;
  FIND_DATA_NAME = 44;
  { TIME_ZONE_INFORMATION. }
  TZI_SIZE = 172;
  TZI_BIAS = 0;
  TZI_STANDARD_BIAS = 84;
  TZI_DAYLIGHT_BIAS = 168;
  { STARTUPINFOW and PROCESS_INFORMATION. }
  SI_SIZE = 104;
  SI_FLAGS = 60;
  SI_STD_INPUT = 80;
  SI_STD_OUTPUT = 88;
  SI_STD_ERROR = 96;
  PI_SIZE = 24;
  PI_PROCESS = 0;
  PI_THREAD = 8;
  { SECURITY_ATTRIBUTES. }
  SA_SIZE = 24;
  SA_INHERIT = 16;

  { String header layout, as every RTL unit that builds strings declares it
    (see rtl.platform.posix).  Offsets are from the data pointer. }
  STR_HDR_SIZE = 24;
  STR_RC_OFS = -12;
  STR_LEN_OFS = -8;
  STR_CAP_OFS = -24;

type
  PInt32 = ^Int32;
  PUInt32 = ^UInt32;
  PInt64 = ^Int64;
  PUInt16 = ^UInt16;
  PPointer = ^Pointer;
  PPChar = ^PChar;

  { A child process.  Args holds the arguments, each after a space and
    quoted as CommandLineToArgvW splits them. }
  TWinProcess = record
    Exe: string;
    Args: string;
    Process: Pointer;
    Pipe: Pointer;
    ExitCode: Int32;
    Waited: Int32;
  end;
  PWinProcess = ^TWinProcess;

var
  GArgC: Int32;
  GArgV: Pointer;
  GEnvVector: Pointer;
  { Mixed into temporary file names, so two names made in one clock tick
    differ. }
  GTempCounter: Int64;

{ ---- strings ---- }

{ The bytes of string data S, from the length in its header. }
function StrBytes(S: Pointer): Int64;
begin
  if S = nil then
    Exit(0);
  Result := PInt64(S + STR_LEN_OFS)^;
end;

{ A new string buffer of Len bytes, reference count 0, NUL-terminated. }
function StrAlloc(Len: Int64): PChar;
var
  Base: Pointer;
begin
  Base := _BlaiseGetMem(STR_HDR_SIZE + Len + 1);
  if Base = nil then
    Exit(nil);
  Result := PChar(Base + STR_HDR_SIZE);
  PInt32(Pointer(Result) + STR_RC_OFS)^ := 0;
  PInt64(Pointer(Result) + STR_LEN_OFS)^ := Len;
  PInt64(Pointer(Result) + STR_CAP_OFS)^ := Len;
  Result[Len] := #0;
end;

{ Make buffer P, fresh from StrAlloc, the result string without copying it. }
function StrAdopt(P: PChar): string;
var
  Slot: PPointer;
begin
  Result := '';
  if P = nil then
    Exit;
  PInt32(Pointer(P) + STR_RC_OFS)^ := 1;
  Slot := PPointer(@Result);
  Slot^ := Pointer(P);
end;

{ The string whose data S points at, copied by its header length. }
function StrOfData(S: Pointer): string;
var
  Len, I: Int64;
  R: PChar;
begin
  Len := StrBytes(S);
  if Len = 0 then
    Exit('');
  R := StrAlloc(Len);
  for I := 0 to Len - 1 do
    R[I] := PChar(S)[I];
  Result := StrAdopt(R);
end;

{ S as NUL-terminated UTF-16, for a W API.  The caller frees it. }
function WideZ(const S: string): Pointer;
var
  Len, N: Int32;
begin
  Len := Int32(Length(S));
  N := 0;
  if Len > 0 then
    N := W32MultiByteToWideChar(CP_UTF8, 0, PChar(S), Len, nil, 0);
  Result := _BlaiseGetMem((Int64(N) + 1) * 2);
  if N > 0 then
    W32MultiByteToWideChar(CP_UTF8, 0, PChar(S), Len, Result, N);
  PUInt16(Result + Int64(N) * 2)^ := 0;
end;

{ The UTF-16 units of NUL-terminated W before the NUL. }
function WideLen(W: Pointer): Int32;
begin
  Result := 0;
  if W = nil then
    Exit;
  while PUInt16(W + Int64(Result) * 2)^ <> 0 do
    Result := Result + 1;
end;

{ AUnits UTF-16 units at W as a UTF-8 string. }
function FromWide(W: Pointer; AUnits: Int32): string;
var
  N: Int32;
  R: PChar;
begin
  if (W = nil) or (AUnits <= 0) then
    Exit('');
  N := W32WideCharToMultiByte(CP_UTF8, 0, W, AUnits, nil, 0, nil, nil);
  R := StrAlloc(N);
  if R = nil then
    Exit('');
  W32WideCharToMultiByte(CP_UTF8, 0, W, AUnits, R, N, nil, nil);
  Result := StrAdopt(R);
end;

{ Whether byte I of P separates path components. }
function IsSeparator(P: PChar; I: Int): Boolean;
begin
  Result := (P[I] = '/') or (P[I] = '\');
end;

{ ADir and AName joined by one separator. }
function JoinPath(const ADir, AName: string): string;
begin
  if (Length(ADir) = 0) or IsSeparator(PChar(ADir), Length(ADir) - 1) then
    Result := ADir + AName
  else
    Result := ADir + '\' + AName;
end;

{ ---- console writes ---- }

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

{ ---- handles and metadata ---- }

{ Open APath through CreateFileW; INVALID_HANDLE_VALUE when that fails. }
function OpenPath(const APath: string; AAccess, ADisposition,
  AFlags: UInt32): Pointer;
var
  W: Pointer;
begin
  W := WideZ(APath);
  Result := W32CreateFileW(W, AAccess, FILE_SHARE_ALL, nil, ADisposition,
    AFlags, nil);
  _BlaiseFreeMem(W);
end;

function IsValidHandle(H: Pointer): Boolean;
begin
  Result := (H <> nil) and (H <> Pointer(-1));
end;

{ Write all of AContent to handle H. }
procedure WriteAllToHandle(H: Pointer; const AContent: string);
var
  P: PChar;
  Left: Int64;
  Chunk, Done: UInt32;
begin
  P := PChar(AContent);
  Left := Length(AContent);
  while Left > 0 do
  begin
    if Left > MAX_IO_CHUNK then
      Chunk := MAX_IO_CHUNK
    else
      Chunk := UInt32(Left);
    Done := 0;
    if (W32WriteFile(H, P, Chunk, @Done, nil) = 0) or (Done = 0) then
      Exit;
    P := P + Done;
    Left := Left - Done;
  end;
end;

{ What APath is, the way stat (AFollowLinks) or lstat sees it: its
  attributes, size, and last-write time as a FILETIME.  False when it does
  not exist, or is a link whose target does not. }
function QueryPath(const APath: string; AFollowLinks: Boolean;
  out AAttrs: UInt32; out ASize: Int64; out AWriteTime: Int64): Boolean;
var
  W, H: Pointer;
  Data: array[0..FAD_SIZE - 1] of Byte;
  Info: array[0..BHI_SIZE - 1] of Byte;
begin
  AAttrs := 0;
  ASize := 0;
  AWriteTime := 0;
  W := WideZ(APath);
  Result := W32GetFileAttributesExW(W, 0, @Data[0]) <> 0;
  _BlaiseFreeMem(W);
  if not Result then
    Exit;
  AAttrs := PUInt32(@Data[FAD_ATTRS])^;
  ASize := Int64(PUInt32(@Data[FAD_SIZE_HIGH])^) shl 32
    + Int64(PUInt32(@Data[FAD_SIZE_LOW])^);
  AWriteTime := PInt64(@Data[FAD_WRITE_TIME])^;
  if AFollowLinks and ((AAttrs and FILE_ATTRIBUTE_REPARSE_POINT) <> 0) then
  begin
    { the target's metadata, through a handle the open resolves }
    H := OpenPath(APath, 0, OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS);
    if not IsValidHandle(H) then
      Exit(False);
    Result := W32GetFileInformationByHandle(H, @Info[0]) <> 0;
    W32CloseHandle(H);
    if not Result then
      Exit;
    AAttrs := PUInt32(@Info[BHI_ATTRS])^;
    ASize := Int64(PUInt32(@Info[BHI_SIZE_HIGH])^) shl 32
      + Int64(PUInt32(@Info[BHI_SIZE_LOW])^);
    AWriteTime := PInt64(@Info[BHI_WRITE_TIME])^;
  end;
end;

{ APath's attributes, or INVALID_FILE_ATTRIBUTES. }
function PathAttributes(const APath: string): UInt32;
var
  W: Pointer;
begin
  W := WideZ(APath);
  Result := W32GetFileAttributesW(W);
  _BlaiseFreeMem(W);
end;

function KindOfAttributes(AAttrs: UInt32; AFollowLinks: Boolean): Int32;
begin
  if (not AFollowLinks) and ((AAttrs and FILE_ATTRIBUTE_REPARSE_POINT) <> 0) then
    Result := 3
  else if (AAttrs and FILE_ATTRIBUTE_DIRECTORY) <> 0 then
    Result := 2
  else
    Result := 1;
end;

{ A FILETIME as whole seconds since 1970 and the nanoseconds past them. }
procedure SplitFileTime(AFileTime: Int64; out ASec, ANSec: Int64);
var
  T: Int64;
begin
  T := AFileTime - FILETIME_UNIX_EPOCH;
  ASec := T div 10000000;
  ANSec := (T mod 10000000) * 100;
  if ANSec < 0 then
  begin
    ASec := ASec - 1;
    ANSec := ANSec + NS_PER_SEC;
  end;
end;

{ ---- child processes ---- }

{ A as one argument of a command line that CommandLineToArgvW splits back
  into A: quoted when it is empty or holds a space, tab or quote, with the
  backslashes before a quote, or before the closing quote, doubled. }
function QuoteArg(const A: string): string;
var
  I, K, Slashes: Int;
  P: PChar;
  NeedQuote: Boolean;
begin
  P := PChar(A);
  NeedQuote := Length(A) = 0;
  for I := 0 to Length(A) - 1 do
    if (P[I] = ' ') or (P[I] = #9) or (P[I] = '"') then
      NeedQuote := True;
  if not NeedQuote then
    Exit(A);
  Result := '"';
  Slashes := 0;
  for I := 0 to Length(A) - 1 do
  begin
    if P[I] = '\' then
      Slashes := Slashes + 1
    else if P[I] = '"' then
    begin
      for K := 1 to Slashes * 2 + 1 do
        Result := Result + '\';
      Result := Result + '"';
      Slashes := 0;
    end
    else
    begin
      for K := 1 to Slashes do
        Result := Result + '\';
      Result := Result + Chr(Ord(P[I]));
      Slashes := 0;
    end;
  end;
  for K := 1 to Slashes * 2 do
    Result := Result + '\';
  Result := Result + '"';
end;

{ Start ACmdLine with the given standard handles; the process handle, or
  nil when it cannot be started.  The handles must be inheritable. }
function StartProcess(const ACmdLine: string;
  AStdIn, AStdOut, AStdErr: Pointer): Pointer;
var
  Startup: array[0..SI_SIZE - 1] of Byte;
  Info: array[0..PI_SIZE - 1] of Byte;
  W: Pointer;
  I: Int;
  Ok: Int32;
begin
  for I := 0 to SI_SIZE - 1 do
    Startup[I] := 0;
  for I := 0 to PI_SIZE - 1 do
    Info[I] := 0;
  PUInt32(@Startup[0])^ := SI_SIZE;
  PUInt32(@Startup[SI_FLAGS])^ := STARTF_USESTDHANDLES;
  PPointer(@Startup[SI_STD_INPUT])^ := AStdIn;
  PPointer(@Startup[SI_STD_OUTPUT])^ := AStdOut;
  PPointer(@Startup[SI_STD_ERROR])^ := AStdErr;
  W := WideZ(ACmdLine);
  Ok := W32CreateProcessW(nil, W, nil, nil, 1, 0, nil, nil, @Startup[0],
    @Info[0]);
  _BlaiseFreeMem(W);
  if Ok = 0 then
    Exit(nil);
  W32CloseHandle(PPointer(@Info[PI_THREAD])^);
  Result := PPointer(@Info[PI_PROCESS])^;
end;

{ Standard handle AWhich, marked inheritable so a child can be given it. }
function InheritableStdHandle(AWhich: UInt32): Pointer;
begin
  Result := W32GetStdHandle(AWhich);
  if IsValidHandle(Result) then
    W32SetHandleInformation(Result, HANDLE_FLAG_INHERIT, HANDLE_FLAG_INHERIT);
end;

function ExitCodeOf(AProcess: Pointer): Int32;
var
  Code: UInt32;
begin
  Code := 0;
  W32GetExitCodeProcess(AProcess, @Code);
  Result := Int32(Code);
end;

{ ================================================================== }
{ Console I/O                                                          }
{ ================================================================== }

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

{ ================================================================== }
{ Files                                                                }
{ ================================================================== }

function TRtlPlatformWindows.FileExists(const APath: string): Boolean;
begin
  Result := PathAttributes(APath) <> INVALID_FILE_ATTRIBUTES;
end;

procedure TRtlPlatformWindows.DeleteFile(const APath: string);
var
  W: Pointer;
begin
  W := WideZ(APath);
  W32DeleteFileW(W);
  _BlaiseFreeMem(W);
end;

{ rename(2) replaces an existing target, and so does this. }
function TRtlPlatformWindows.RenameFile(const AOldPath, ANewPath: string): Boolean;
var
  WOld, WNew: Pointer;
begin
  WOld := WideZ(AOldPath);
  WNew := WideZ(ANewPath);
  Result := W32MoveFileExW(WOld, WNew,
    MOVEFILE_REPLACE_EXISTING or MOVEFILE_COPY_ALLOWED) <> 0;
  _BlaiseFreeMem(WOld);
  _BlaiseFreeMem(WNew);
end;

function TRtlPlatformWindows.ReadFile(const APath: string): string;
var
  H: Pointer;
  Size, Got: Int64;
  Chunk, Done: UInt32;
  R: PChar;
begin
  Result := '';
  H := OpenPath(APath, GENERIC_READ, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL);
  if not IsValidHandle(H) then
    Exit;
  Size := 0;
  if (W32GetFileSizeEx(H, @Size) = 0) or (Size < 0) then
  begin
    W32CloseHandle(H);
    Exit;
  end;
  R := StrAlloc(Size);
  if R = nil then
  begin
    W32CloseHandle(H);
    Exit;
  end;
  Got := 0;
  while Got < Size do
  begin
    if Size - Got > MAX_IO_CHUNK then
      Chunk := MAX_IO_CHUNK
    else
      Chunk := UInt32(Size - Got);
    Done := 0;
    if (W32ReadFile(H, R + Got, Chunk, @Done, nil) = 0) or (Done = 0) then
      Break;
    Got := Got + Done;
  end;
  W32CloseHandle(H);
  PInt64(Pointer(R) + STR_LEN_OFS)^ := Got;
  R[Got] := #0;
  Result := StrAdopt(R);
end;

procedure TRtlPlatformWindows.WriteFile(const APath, AContent: string);
var
  H: Pointer;
begin
  H := OpenPath(APath, GENERIC_WRITE, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL);
  if not IsValidHandle(H) then
    Exit;
  WriteAllToHandle(H, AContent);
  W32CloseHandle(H);
end;

procedure TRtlPlatformWindows.AppendFile(const APath, AContent: string);
var
  H: Pointer;
begin
  { append-only access: every write lands at the end, as with O_APPEND }
  H := OpenPath(APath, FILE_APPEND_DATA or SYNCHRONIZE, OPEN_ALWAYS,
    FILE_ATTRIBUTE_NORMAL);
  if not IsValidHandle(H) then
    Exit;
  WriteAllToHandle(H, AContent);
  W32CloseHandle(H);
end;

function TRtlPlatformWindows.FileAge(const APath: string): Int64;
var
  Attrs: UInt32;
  Size, WriteTime, Sec, NSec: Int64;
begin
  if not QueryPath(APath, True, Attrs, Size, WriteTime) then
    Exit(-1);
  SplitFileTime(WriteTime, Sec, NSec);
  Result := Sec;
end;

{ ================================================================== }
{ Directories                                                          }
{ ================================================================== }

function TRtlPlatformWindows.DirectoryExists(const APath: string): Boolean;
var
  Attrs: UInt32;
begin
  Attrs := PathAttributes(APath);
  Result := (Attrs <> INVALID_FILE_ATTRIBUTES)
    and ((Attrs and FILE_ATTRIBUTE_DIRECTORY) <> 0);
end;

{ A reparse point -- a symbolic link or a junction -- is the link kind. }
function TRtlPlatformWindows.PathKind(const APath: string; AFollowLinks: Boolean): Int32;
var
  Attrs: UInt32;
  Size, WriteTime: Int64;
begin
  if not QueryPath(APath, AFollowLinks, Attrs, Size, WriteTime) then
    Exit(0);
  Result := KindOfAttributes(Attrs, AFollowLinks);
end;

function TRtlPlatformWindows.ForceDirectories(const APath: string): Boolean;
var
  Len, I, Start, Seps: Int;
  P: PChar;
  Prefix: string;
  Attrs: UInt32;
  W: Pointer;
begin
  Len := Length(APath);
  if Len = 0 then
    Exit(False);
  P := PChar(APath);
  { a UNC path's \\server\share is not created: start past it }
  Start := 1;
  if (Len > 1) and IsSeparator(P, 0) and IsSeparator(P, 1) then
  begin
    Seps := 0;
    Start := 2;
    while (Start < Len) and (Seps < 2) do
    begin
      if IsSeparator(P, Start) then
        Seps := Seps + 1;
      Start := Start + 1;
    end;
  end;
  for I := Start to Len do
    if (I = Len) or IsSeparator(P, I) then
    begin
      Prefix := Copy(APath, 0, I);
      { a drive or a trailing separator names nothing new }
      if (Length(Prefix) = 0) or IsSeparator(PChar(Prefix), Length(Prefix) - 1)
        or ((Length(Prefix) = 2) and (PChar(Prefix)[1] = ':')) then
        Continue;
      Attrs := PathAttributes(Prefix);
      if Attrs = INVALID_FILE_ATTRIBUTES then
      begin
        W := WideZ(Prefix);
        if (W32CreateDirectoryW(W, nil) = 0)
          and (W32GetLastError() <> ERROR_ALREADY_EXISTS) then
        begin
          _BlaiseFreeMem(W);
          Exit(False);
        end;
        _BlaiseFreeMem(W);
      end
      else if (Attrs and FILE_ATTRIBUTE_DIRECTORY) = 0 then
        Exit(False);
    end;
  Result := True;
end;

{ As on POSIX, the result does not report whether the directory went. }
function TRtlPlatformWindows.RemoveDir(const APath: string): Boolean;
var
  W: Pointer;
begin
  W := WideZ(APath);
  W32RemoveDirectoryW(W);
  _BlaiseFreeMem(W);
  Result := True;
end;

{ The current directory, ending in a separator. }
function TRtlPlatformWindows.GetCurrentDir: string;
var
  Units, Got: UInt32;
  Buf: Pointer;
begin
  Units := W32GetCurrentDirectoryW(0, nil);
  if Units = 0 then
    Exit('');
  Buf := _BlaiseGetMem(Int64(Units) * 2);
  Got := W32GetCurrentDirectoryW(Units, Buf);
  Result := FromWide(Buf, Int32(Got));
  _BlaiseFreeMem(Buf);
  if (Length(Result) > 0) and not IsSeparator(PChar(Result), Length(Result) - 1) then
    Result := Result + '\';
end;

function TRtlPlatformWindows.SetCurrentDir(const APath: string): Boolean;
var
  W: Pointer;
begin
  W := WideZ(APath);
  Result := W32SetCurrentDirectoryW(W) <> 0;
  _BlaiseFreeMem(W);
end;

function TRtlPlatformWindows.ListDir(const APath: string): string;
var
  Data: array[0..FIND_DATA_SIZE - 1] of Byte;
  W, Find, Name: Pointer;
  N: Int32;
  Entry: string;
begin
  Result := '';
  W := WideZ(JoinPath(APath, '*'));
  Find := W32FindFirstFileW(W, @Data[0]);
  _BlaiseFreeMem(W);
  if not IsValidHandle(Find) then
    Exit;
  repeat
    Name := @Data[FIND_DATA_NAME];
    N := WideLen(Name);
    Entry := FromWide(Name, N);
    if (Entry <> '.') and (Entry <> '..') and (Entry <> '') then
    begin
      if Result = '' then
        Result := Entry
      else
        Result := Result + #10 + Entry;
    end;
  until W32FindNextFileW(Find, @Data[0]) = 0;
  W32FindClose(Find);
end;

{ ================================================================== }
{ OS utilities                                                         }
{ ================================================================== }

{ GetTempPathW's directory, which ends in a separator. }
function TRtlPlatformWindows.GetTempDir: string;
var
  Units, Got: UInt32;
  Buf: Pointer;
begin
  Units := W32GetTempPathW(0, nil);
  if Units = 0 then
    Exit('');
  Buf := _BlaiseGetMem(Int64(Units + 1) * 2);
  Got := W32GetTempPathW(Units + 1, Buf);
  Result := FromWide(Buf, Int32(Got));
  _BlaiseFreeMem(Buf);
end;

{ As mkstemp: ADir (the temporary directory when empty), APrefix and six
  random letters and digits, created empty so no other caller gets the
  name. }
function TRtlPlatformWindows.GetTempFileName(const ADir, APrefix: string): string;
const
  Alphabet = 'abcdefghijklmnopqrstuvwxyz0123456789';
var
  Dir, Name: string;
  Seed: Int64;
  Tries, I: Int;
  H: Pointer;
begin
  if Length(ADir) = 0 then
    Dir := Self.GetTempDir()
  else
    Dir := ADir;
  Result := '';
  for Tries := 1 to 100 do
  begin
    Seed := 0;
    W32QueryPerformanceCounter(@Seed);
    GTempCounter := GTempCounter + 1;
    Seed := Seed xor (GTempCounter * 7919) xor (Int64(W32GetCurrentProcessId()) shl 20);
    if Seed < 0 then
      Seed := -Seed;
    Name := APrefix;
    for I := 1 to 6 do
    begin
      Name := Name + Chr(Ord(PChar(Alphabet)[Seed mod 36]));
      Seed := Seed div 36 + Seed mod 7 * 104729;
    end;
    Result := JoinPath(Dir, Name);
    H := OpenPath(Result, GENERIC_WRITE, CREATE_NEW, FILE_ATTRIBUTE_NORMAL);
    if IsValidHandle(H) then
    begin
      W32CloseHandle(H);
      Exit;
    end;
    if W32GetLastError() <> ERROR_FILE_EXISTS then
      Exit;
  end;
end;

function TRtlPlatformWindows.GetProcessID: Int32;
begin
  Result := Int32(W32GetCurrentProcessId());
end;

{ A Windows symbolic link is a reparse point that the file APIs follow; the
  compiler asks only to find its own installation, which ParamStr(0)
  already names in full here, so no link target is reported. }
function TRtlPlatformWindows.ReadLink(const APath: string): string;
begin
  Result := '';
end;

{ The system's preferred RNG (no algorithm handle), in chunks a UInt32 can
  count. }
function TRtlPlatformWindows.RandomBytes(ABuf: Pointer; ACount: Int): Boolean;
var
  Done, N: Int;
begin
  Done := 0;
  while Done < ACount do
  begin
    N := ACount - Done;
    if N > $40000000 then
      N := $40000000;
    if W32BCryptGenRandom(nil, ABuf + Done, UInt32(N),
       BCRYPT_USE_SYSTEM_PREFERRED_RNG) <> 0 then
      Exit(False);
    Done := Done + N;
  end;
  Result := True;
end;

{ A file is executable by its extension; nothing to mark. }
function TRtlPlatformWindows.MakeExecutable(const APath: string): Boolean;
begin
  Result := Self.FileExists(APath);
end;

function TRtlPlatformWindows.GetEnvVar(const AName: string): string;
var
  W, Buf: Pointer;
  Units, Got: UInt32;
begin
  W := WideZ(AName);
  Units := W32GetEnvironmentVariableW(W, nil, 0);
  if Units = 0 then
  begin
    _BlaiseFreeMem(W);
    Exit('');
  end;
  Buf := _BlaiseGetMem(Int64(Units) * 2);
  Got := W32GetEnvironmentVariableW(W, Buf, Units);
  Result := FromWide(Buf, Int32(Got));
  _BlaiseFreeMem(Buf);
  _BlaiseFreeMem(W);
end;

procedure TRtlPlatformWindows.Sleep(AMilliseconds: Int32);
begin
  W32Sleep(UInt32(AMilliseconds));
end;

procedure TRtlPlatformWindows.Halt(AExitCode: Int32);
begin
  _exit_running_handlers(AExitCode);
end;

{ ACmd through cmd.exe /c (/d: no AutoRun commands; /s: the outer quotes are
  removed and the rest is kept as written).  The command's exit code, or
  127 when cmd.exe cannot be started. }
function TRtlPlatformWindows.Exec(const ACmd: string): Int32;
var
  Shell: string;
  H: Pointer;
begin
  Shell := Self.GetEnvVar('ComSpec');
  if Shell = '' then
    Shell := 'cmd.exe';
  H := StartProcess(QuoteArg(Shell) + ' /d /s /c "' + ACmd + '"',
    InheritableStdHandle(STD_INPUT_HANDLE),
    InheritableStdHandle(STD_OUTPUT_HANDLE),
    InheritableStdHandle(STD_ERROR_HANDLE));
  if H = nil then
    Exit(EXIT_NOT_STARTED);
  W32WaitForSingleObject(H, INFINITE);
  Result := ExitCodeOf(H);
  W32CloseHandle(H);
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

{ ================================================================== }
{ File-descriptor primitives                                           }
{ ================================================================== }

{ Enter a handle CreateFileW returned in the descriptor table. }
function DescriptorOf(H: Pointer): Int32;
begin
  if not IsValidHandle(H) then
    Exit(-1);
  Result := _WinFdAdd(H);
  if Result < 0 then
    W32CloseHandle(H);
end;

function TRtlPlatformWindows.FdOpenRead(Path: Pointer): Int32;
begin
  Result := DescriptorOf(OpenPath(StrOfData(Path), GENERIC_READ,
    OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL));
end;

function TRtlPlatformWindows.FdOpenWrite(Path: Pointer): Int32;
begin
  Result := DescriptorOf(OpenPath(StrOfData(Path), GENERIC_WRITE,
    CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL));
end;

function TRtlPlatformWindows.FdOpenAppend(Path: Pointer): Int32;
begin
  Result := DescriptorOf(OpenPath(StrOfData(Path),
    FILE_APPEND_DATA or SYNCHRONIZE, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL));
end;

{ A pipe whose writer has gone reads as the end of the data, as on POSIX. }
function TRtlPlatformWindows.FdRead(Fd: Int32; Buf: Pointer; Count: Int): Int;
var
  H: Pointer;
  Chunk, Done: UInt32;
  Err: UInt32;
begin
  if (Fd < 0) or (Count <= 0) then
    Exit(0);
  H := _WinHandleOfFd(Fd);
  if H = nil then
    Exit(-1);
  if Count > MAX_IO_CHUNK then
    Chunk := MAX_IO_CHUNK
  else
    Chunk := UInt32(Count);
  Done := 0;
  if W32ReadFile(H, Buf, Chunk, @Done, nil) = 0 then
  begin
    Err := W32GetLastError();
    if (Err = ERROR_BROKEN_PIPE) or (Err = ERROR_HANDLE_EOF) then
      Exit(0);
    Exit(-1);
  end;
  Result := Done;
end;

function TRtlPlatformWindows.FdWrite(Fd: Int32; Buf: Pointer; Count: Int): Int;
begin
  if (Fd < 0) or (Count <= 0) then
    Exit(0);
  Result := _sys_write(Fd, Buf, Count);
end;

{ Origin 0, 1 and 2 are FILE_BEGIN, FILE_CURRENT and FILE_END. }
function TRtlPlatformWindows.FdSeek(Fd: Int32; Offset: Int64; Origin: Int32): Int64;
var
  H: Pointer;
  NewPos: Int64;
  Method: UInt32;
begin
  H := _WinHandleOfFd(Fd);
  if H = nil then
    Exit(-1);
  if (Origin = 1) or (Origin = 2) then
    Method := UInt32(Origin)
  else
    Method := 0;
  NewPos := 0;
  if W32SetFilePointerEx(H, Offset, @NewPos, Method) = 0 then
    Exit(-1);
  Result := NewPos;
end;

function TRtlPlatformWindows.FdSize(Fd: Int32): Int64;
var
  H: Pointer;
  Size: Int64;
begin
  H := _WinHandleOfFd(Fd);
  Size := 0;
  if (H = nil) or (W32GetFileSizeEx(H, @Size) = 0) then
    Exit(-1);
  Result := Size;
end;

{ The standard descriptors stay open; a socket closes the Winsock way. }
procedure TRtlPlatformWindows.FdClose(Fd: Int32);
begin
  if Fd >= 0 then
    _WinFdClose(Fd);
end;

{ ================================================================== }
{ POSIX-shaped file-system calls                                       }
{ ================================================================== }
{ Each fails with -1 and the Win32 error left for GetLastError, which
  runtime.errno.windows' OsErrorOf maps to the POSIX errno.  Where POSIX and
  Windows differ, these follow POSIX: a read-only file can be deleted and
  replaced (its directory's permissions decide that on POSIX, not its own),
  and a directory replaces an empty directory. }

const
  CH_SLASH = $2F;
  CH_BACKSLASH = $5C;
  CH_COLON = $3A;

{ Fail with ACode as the last error. }
function FailWith(ACode: UInt32): Int32;
begin
  W32SetLastError(ACode);
  Result := -1;
end;

{ ACall's BOOL result as the POSIX 0 or -1. }
function PosixResult(ACall: Int32): Int32;
begin
  if ACall <> 0 then
    Result := 0
  else
    Result := -1;
end;

{ Clear READONLY on the entry at wide path W, whose attributes are AAttrs;
  True when it was set (and so must be put back if the call it made way for
  fails). }
function DropReadOnly(W: Pointer; AAttrs: UInt32): Boolean;
begin
  Result := (AAttrs <> INVALID_FILE_ATTRIBUTES) and
    ((AAttrs and FILE_ATTRIBUTE_READONLY) <> 0) and
    ((AAttrs and FILE_ATTRIBUTE_DIRECTORY) = 0);
  if Result then
    W32SetFileAttributesW(W, AAttrs and not FILE_ATTRIBUTE_READONLY);
end;

{ After a failed call: put READONLY back if DropReadOnly took it, keeping the
  call's error. }
procedure RestoreReadOnly(W: Pointer; AAttrs: UInt32; ADropped: Boolean);
var
  Err: UInt32;
begin
  if not ADropped then
    Exit;
  Err := W32GetLastError();
  W32SetFileAttributesW(W, AAttrs);
  W32SetLastError(Err);
end;

{ Replace each UTF-16 unit AFrom in NUL-terminated W with ATo. }
procedure ReplaceWide(W: Pointer; AFrom, ATo: UInt16);
var
  P: PUInt16;
begin
  P := PUInt16(W);
  while P^ <> 0 do
  begin
    if P^ = AFrom then
      P^ := ATo;
    P := PUInt16(Pointer(P) + 2);
  end;
end;

{ The attributes of a link's target WTarget, read relative to the directory
  of the link WLink when it is a relative path, as the link will resolve
  it. }
function LinkTargetAttributes(WLink, WTarget: Pointer): UInt32;
var
  First, Second: UInt16;
  LinkLen, TargetLen, DirLen, I: Int32;
  W: Pointer;
begin
  First := PUInt16(WTarget)^;
  Second := 0;
  if First <> 0 then
    Second := PUInt16(WTarget + 2)^;
  if (First = CH_SLASH) or (First = CH_BACKSLASH) or (Second = CH_COLON) then
    Exit(W32GetFileAttributesW(WTarget));
  LinkLen := WideLen(WLink);
  DirLen := 0;
  for I := 0 to LinkLen - 1 do
    if (PUInt16(WLink + Int64(I) * 2)^ = CH_SLASH) or
       (PUInt16(WLink + Int64(I) * 2)^ = CH_BACKSLASH) then
      DirLen := I + 1;
  TargetLen := WideLen(WTarget);
  W := _BlaiseGetMem((Int64(DirLen) + TargetLen + 1) * 2);
  for I := 0 to DirLen - 1 do
    PUInt16(W + Int64(I) * 2)^ := PUInt16(WLink + Int64(I) * 2)^;
  for I := 0 to TargetLen - 1 do
    PUInt16(W + Int64(DirLen + I) * 2)^ := PUInt16(WTarget + Int64(I) * 2)^;
  PUInt16(W + Int64(DirLen + TargetLen) * 2)^ := 0;
  Result := W32GetFileAttributesW(W);
  _BlaiseFreeMem(W);
end;

{ Whether APath names a program by its extension, as cmd.exe would run it. }
function HasProgramExtension(const APath: string): Boolean;
var
  P: PChar;
  N, I: Int;
  Ext: string;
  B: Int;
begin
  Result := False;
  N := Length(APath);
  if N < 4 then
    Exit;
  P := PChar(APath);
  if P[N - 4] <> '.' then
    Exit;
  Ext := '';
  for I := N - 3 to N - 1 do
  begin
    B := Ord(P[I]);
    if (B >= Ord('A')) and (B <= Ord('Z')) then
      B := B + 32;
    Ext := Ext + Chr(B);
  end;
  Result := (Ext = 'exe') or (Ext = 'com') or (Ext = 'bat') or (Ext = 'cmd');
end;

function TRtlPlatformWindows.FsClose(Fd: Int32): Int32;
begin
  Result := _WinFdClose(Fd);
end;

{ A link to a directory is a directory entry on Windows, removed with
  RemoveDirectoryW; a real directory is refused, as unlink(2) refuses it. }
function TRtlPlatformWindows.FsUnlink(const APath: string): Int32;
var
  W: Pointer;
  Attrs: UInt32;
  Dropped: Boolean;
begin
  W := WideZ(APath);
  Attrs := W32GetFileAttributesW(W);
  if Attrs = INVALID_FILE_ATTRIBUTES then
    Result := -1
  else if (Attrs and FILE_ATTRIBUTE_DIRECTORY) <> 0 then
  begin
    if (Attrs and FILE_ATTRIBUTE_REPARSE_POINT) <> 0 then
      Result := PosixResult(W32RemoveDirectoryW(W))
    else
      Result := FailWith(ERROR_ACCESS_DENIED);
  end
  else
  begin
    Dropped := DropReadOnly(W, Attrs);
    Result := PosixResult(W32DeleteFileW(W));
    if Result <> 0 then
      RestoreReadOnly(W, Attrs, Dropped);
  end;
  _BlaiseFreeMem(W);
end;

function TRtlPlatformWindows.FsRmdir(const APath: string): Int32;
var
  W: Pointer;
begin
  W := WideZ(APath);
  Result := PosixResult(W32RemoveDirectoryW(W));
  _BlaiseFreeMem(W);
end;

{ Windows has no mode bits; AMode is not used. }
function TRtlPlatformWindows.FsMkdir(const APath: string; AMode: Int32): Int32;
var
  W: Pointer;
begin
  W := WideZ(APath);
  Result := PosixResult(W32CreateDirectoryW(W, nil));
  _BlaiseFreeMem(W);
end;

{ Across volumes MoveFileExW fails with ERROR_NOT_SAME_DEVICE (EXDEV), as
  rename(2) does; the caller copies. }
function TRtlPlatformWindows.FsRename(const AOldPath, ANewPath: string): Int32;
var
  WOld, WNew: Pointer;
  OldAttrs, NewAttrs: UInt32;
  Dropped: Boolean;
begin
  WOld := WideZ(AOldPath);
  WNew := WideZ(ANewPath);
  Dropped := False;
  Result := 0;
  OldAttrs := W32GetFileAttributesW(WOld);
  NewAttrs := W32GetFileAttributesW(WNew);
  if OldAttrs = INVALID_FILE_ATTRIBUTES then
    Result := -1
  else if (NewAttrs <> INVALID_FILE_ATTRIBUTES) and
          ((NewAttrs and FILE_ATTRIBUTE_DIRECTORY) <> 0) and
          ((NewAttrs and FILE_ATTRIBUTE_REPARSE_POINT) = 0) then
  begin
    { A directory replaces an empty directory; nothing else replaces one. }
    if (OldAttrs and FILE_ATTRIBUTE_DIRECTORY) = 0 then
      Result := FailWith(ERROR_ACCESS_DENIED)
    else
      Result := PosixResult(W32RemoveDirectoryW(WNew));
  end
  else
    Dropped := DropReadOnly(WNew, NewAttrs);
  if Result = 0 then
  begin
    Result := PosixResult(W32MoveFileExW(WOld, WNew, MOVEFILE_REPLACE_EXISTING));
    if Result <> 0 then
      RestoreReadOnly(WNew, NewAttrs, Dropped);
  end;
  _BlaiseFreeMem(WOld);
  _BlaiseFreeMem(WNew);
end;

{ The owner-write bit decides READONLY, the one permission a file carries;
  a directory's READONLY has no such meaning, so a directory is left as it
  is. }
function TRtlPlatformWindows.FsChmod(const APath: string; AMode: Int32): Int32;
var
  W: Pointer;
  Attrs, Want: UInt32;
begin
  W := WideZ(APath);
  Attrs := W32GetFileAttributesW(W);
  if Attrs = INVALID_FILE_ATTRIBUTES then
    Result := -1
  else if (Attrs and FILE_ATTRIBUTE_DIRECTORY) <> 0 then
    Result := 0
  else
  begin
    if (AMode and $80) <> 0 then
      Want := Attrs and not FILE_ATTRIBUTE_READONLY
    else
      Want := Attrs or FILE_ATTRIBUTE_READONLY;
    if Want = Attrs then
      Result := 0
    else
      Result := PosixResult(W32SetFileAttributesW(W, Want));
  end;
  _BlaiseFreeMem(W);
end;

{ A link that needs no privilege (Developer Mode, or an elevated process
  otherwise), marked a directory link when its target is a directory now.
  The target's '/' separators are stored as '\', which the link resolution
  needs; FsReadlink turns them back. }
function TRtlPlatformWindows.FsSymlink(const ATarget, ALinkPath: string): Int32;
var
  WTarget, WLink: Pointer;
  Attrs, Flags: UInt32;
begin
  WTarget := WideZ(ATarget);
  WLink := WideZ(ALinkPath);
  ReplaceWide(WTarget, CH_SLASH, CH_BACKSLASH);
  Flags := SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE;
  Attrs := LinkTargetAttributes(WLink, WTarget);
  if (Attrs <> INVALID_FILE_ATTRIBUTES) and
     ((Attrs and FILE_ATTRIBUTE_DIRECTORY) <> 0) then
    Flags := Flags or SYMBOLIC_LINK_FLAG_DIRECTORY;
  if W32CreateSymbolicLinkW(WLink, WTarget, Flags) <> 0 then
    Result := 0
  else
    Result := -1;
  _BlaiseFreeMem(WTarget);
  _BlaiseFreeMem(WLink);
end;

{ The link's print name (its target as written), else its substitute name
  without the NT '\??\' prefix; a junction reads like a symbolic link.  As
  readlink(2), the result is not NUL-terminated and is cut at ASize. }
function TRtlPlatformWindows.FsReadlink(const APath: string; ABuf: Pointer;
  ASize: Int64): Int64;
var
  H, Buf, Names: Pointer;
  Returned, Tag, Err: UInt32;
  Ofs, Len: Int32;
  W: Pointer;
  Target: string;
  Src, Dst: PChar;
  I: Int64;
begin
  H := OpenPath(APath, 0, OPEN_EXISTING,
    FILE_FLAG_OPEN_REPARSE_POINT or FILE_FLAG_BACKUP_SEMANTICS);
  if not IsValidHandle(H) then
    Exit(-1);
  Buf := _BlaiseGetMem(REPARSE_BUF_SIZE);
  Returned := 0;
  if W32DeviceIoControl(H, FSCTL_GET_REPARSE_POINT, nil, 0, Buf,
     REPARSE_BUF_SIZE, @Returned, nil) = 0 then
  begin
    Err := W32GetLastError();
    W32CloseHandle(H);
    _BlaiseFreeMem(Buf);
    Exit(FailWith(Err));
  end;
  W32CloseHandle(H);
  Tag := PUInt32(Buf)^;
  if Tag = IO_REPARSE_TAG_SYMLINK then
    Names := Buf + 20
  else if Tag = IO_REPARSE_TAG_MOUNT_POINT then
    Names := Buf + 16
  else
  begin
    _BlaiseFreeMem(Buf);
    Exit(FailWith(ERROR_NOT_A_REPARSE_POINT));
  end;
  Ofs := PUInt16(Buf + 12)^;
  Len := PUInt16(Buf + 14)^ div 2;
  if Len = 0 then
  begin
    Ofs := PUInt16(Buf + 8)^;
    Len := PUInt16(Buf + 10)^ div 2;
    W := Names + Ofs;
    if (Len >= 4) and (PUInt16(W)^ = CH_BACKSLASH) and
       (PUInt16(W + 2)^ = Ord('?')) and (PUInt16(W + 4)^ = Ord('?')) and
       (PUInt16(W + 6)^ = CH_BACKSLASH) then
    begin
      Ofs := Ofs + 8;
      Len := Len - 4;
    end;
  end;
  Target := FromWide(Names + Ofs, Len);
  _BlaiseFreeMem(Buf);
  Result := Length(Target);
  if Result > ASize then
    Result := ASize;
  Src := PChar(Target);
  Dst := PChar(ABuf);
  for I := 0 to Result - 1 do
  begin
    if Src[I] = '\' then
      Dst[I] := '/'
    else
      Dst[I] := Src[I];
  end;
end;

{ From the attributes: every entry is readable, a READONLY file is not
  writable, and a file is executable by its extension (a directory always
  is, as search permission). }
function TRtlPlatformWindows.FsAccess(const APath: string; AMode: Int32): Int32;
var
  Attrs: UInt32;
  IsDir: Boolean;
begin
  Attrs := PathAttributes(APath);
  if Attrs = INVALID_FILE_ATTRIBUTES then
    Exit(-1);
  IsDir := (Attrs and FILE_ATTRIBUTE_DIRECTORY) <> 0;
  if ((AMode and 2) <> 0) and (not IsDir) and
     ((Attrs and FILE_ATTRIBUTE_READONLY) <> 0) then
    Exit(FailWith(ERROR_ACCESS_DENIED));
  if ((AMode and 1) <> 0) and (not IsDir) and
     (not HasProgramExtension(APath)) then
    Exit(FailWith(ERROR_ACCESS_DENIED));
  Result := 0;
end;

{ Through a handle with only FILE_WRITE_ATTRIBUTES, which a read-only file
  grants, and backup semantics, which opens a directory. }
function TRtlPlatformWindows.FsSetModified(const APath: string;
  ASec, ANSec: Int64): Int32;
var
  H: Pointer;
  WriteTime: Int64;
  Err: UInt32;
begin
  H := OpenPath(APath, FILE_WRITE_ATTRIBUTES, OPEN_EXISTING,
    FILE_FLAG_BACKUP_SEMANTICS);
  if not IsValidHandle(H) then
    Exit(-1);
  WriteTime := ASec * 10000000 + ANSec div 100 + FILETIME_UNIX_EPOCH;
  Result := PosixResult(W32SetFileTime(H, nil, nil, @WriteTime));
  Err := W32GetLastError();
  W32CloseHandle(H);
  if Result <> 0 then
    W32SetLastError(Err);
end;

{ ================================================================== }
{ Date/Time                                                            }
{ ================================================================== }

function TRtlPlatformWindows.TimeNow: Int64;
var
  FT: Int64;
begin
  FT := 0;
  W32GetSystemTimePreciseAsFileTime(@FT);
  Result := (FT - FILETIME_UNIX_EPOCH) * 100;
end;

{ Seconds east of UTC now: the bias Windows reports is minutes west. }
function TRtlPlatformWindows.TimeLocalOffsetSecs: Int32;
var
  Info: array[0..TZI_SIZE - 1] of Byte;
  Zone: UInt32;
  Bias: Int32;
begin
  Zone := W32GetTimeZoneInformation(@Info[0]);
  Bias := PInt32(@Info[TZI_BIAS])^;
  if Zone = TIME_ZONE_ID_DAYLIGHT then
    Bias := Bias + PInt32(@Info[TZI_DAYLIGHT_BIAS])^
  else if Zone = TIME_ZONE_ID_STANDARD then
    Bias := Bias + PInt32(@Info[TZI_STANDARD_BIAS])^;
  Result := -Bias * 60;
end;

procedure TRtlPlatformWindows.TimeSplit(Nanos: Int64; out Year, Month, Day, Hour, Min, Sec, NSec: Int32);
var
  WholeSec, NanoPart, Days, Secs, Y, M, D: Int64;
begin
  WholeSec := Nanos div NS_PER_SEC;
  NanoPart := Nanos mod NS_PER_SEC;
  if NanoPart < 0 then
  begin
    WholeSec := WholeSec - 1;
    NanoPart := NanoPart + NS_PER_SEC;
  end;
  Days := WholeSec div 86400;
  Secs := WholeSec - Days * 86400;
  if Secs < 0 then
  begin
    Secs := Secs + 86400;
    Days := Days - 1;
  end;
  _CivilFromDays(Days, Y, M, D);
  Year := Int32(Y);
  Month := Int32(M);
  Day := Int32(D);
  Hour := Int32(Secs div 3600);
  Min := Int32((Secs div 60) mod 60);
  Sec := Int32(Secs mod 60);
  NSec := Int32(NanoPart);
end;

function TRtlPlatformWindows.TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec: Int32): Int64;
var
  Epoch: Int64;
begin
  Epoch := _DaysFromCivil(Year, Month, Day) * 86400 + Int64(Hour) * 3600
    + Int64(Min) * 60 + Sec;
  Result := Epoch * NS_PER_SEC + Int64(NSec);
end;

function TRtlPlatformWindows.TimeIsLeapYear(Year: Int32): Int32;
begin
  if (Year mod 4 = 0) and ((Year mod 100 <> 0) or (Year mod 400 = 0)) then
    Result := 1
  else
    Result := 0;
end;

function TRtlPlatformWindows.TimeDaysInMonth(Year, Month: Int32): Int32;
const
  Days: array[1..12] of Int32 = (31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31);
begin
  if (Month = 2) and (Self.TimeIsLeapYear(Year) = 1) then
    Result := 29
  else
    Result := Days[Month];
end;

{ ================================================================== }
{ Process management                                                   }
{ ================================================================== }

function TRtlPlatformWindows.ProcessCreate: Pointer;
var
  P: PWinProcess;
  B: PChar;
  I: Int;
begin
  P := PWinProcess(_BlaiseGetMem(SizeOf(TWinProcess)));
  if P = nil then
    Exit(nil);
  B := PChar(P);
  for I := 0 to SizeOf(TWinProcess) - 1 do
    B[I] := #0;
  Result := P;
end;

procedure TRtlPlatformWindows.ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
begin
  PWinProcess(Proc)^.Exe := StrOfData(ExeStr);
end;

procedure TRtlPlatformWindows.ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
var
  P: PWinProcess;
begin
  P := PWinProcess(Proc);
  P^.Args := P^.Args + ' ' + QuoteArg(StrOfData(ArgStr));
end;

{ The program is found as CreateProcessW finds the first word of a command
  line, which includes trying it with .exe appended.  Its standard output
  and error both go into one pipe; it shares this program's standard input.
  A program that cannot be started exits with 127, as from execvp. }
procedure TRtlPlatformWindows.ProcessExecute(Proc: Pointer);
var
  P: PWinProcess;
  Security: array[0..SA_SIZE - 1] of Byte;
  ReadEnd, WriteEnd: Pointer;
  I: Int;
begin
  P := PWinProcess(Proc);
  for I := 0 to SA_SIZE - 1 do
    Security[I] := 0;
  PUInt32(@Security[0])^ := SA_SIZE;
  PInt32(@Security[SA_INHERIT])^ := 1;
  ReadEnd := nil;
  WriteEnd := nil;
  if W32CreatePipe(@ReadEnd, @WriteEnd, @Security[0], 0) = 0 then
    Exit;
  { only the child's end is inherited }
  W32SetHandleInformation(ReadEnd, HANDLE_FLAG_INHERIT, 0);
  P^.Process := StartProcess(QuoteArg(P^.Exe) + P^.Args,
    InheritableStdHandle(STD_INPUT_HANDLE), WriteEnd, WriteEnd);
  W32CloseHandle(WriteEnd);
  if P^.Process = nil then
  begin
    W32CloseHandle(ReadEnd);
    P^.ExitCode := EXIT_NOT_STARTED;
    P^.Waited := 1;
    Exit;
  end;
  P^.Pipe := ReadEnd;
  P^.Waited := 0;
end;

function TRtlPlatformWindows.ProcessRunning(Proc: Pointer): Int32;
var
  P: PWinProcess;
begin
  P := PWinProcess(Proc);
  if (P^.Waited <> 0) or (P^.Process = nil) then
    Exit(0);
  if W32WaitForSingleObject(P^.Process, 0) = WAIT_TIMEOUT then
    Exit(1);
  P^.ExitCode := ExitCodeOf(P^.Process);
  P^.Waited := 1;
  Result := 0;
end;

{ The next piece of the child's output, or '' once it is all read. }
function TRtlPlatformWindows.ProcessReadOutput(Proc: Pointer): Pointer;
var
  P: PWinProcess;
  Buf: array[0..4095] of Byte;
  Done: UInt32;
  R: PChar;
  I: Int;
begin
  P := PWinProcess(Proc);
  if P^.Pipe = nil then
    Exit(StrAlloc(0));
  Done := 0;
  if (W32ReadFile(P^.Pipe, @Buf[0], 4096, @Done, nil) = 0) or (Done = 0) then
  begin
    W32CloseHandle(P^.Pipe);
    P^.Pipe := nil;
    Exit(StrAlloc(0));
  end;
  R := StrAlloc(Done);
  if R <> nil then
    for I := 0 to Int(Done) - 1 do
      R[I] := Chr(Buf[I]);
  Result := R;
end;

procedure TRtlPlatformWindows.ProcessWaitOnExit(Proc: Pointer);
var
  P: PWinProcess;
begin
  P := PWinProcess(Proc);
  if (P^.Waited <> 0) or (P^.Process = nil) then
    Exit;
  W32WaitForSingleObject(P^.Process, INFINITE);
  P^.ExitCode := ExitCodeOf(P^.Process);
  P^.Waited := 1;
end;

{ A child ended by an exception reports its code, 0xC0000005 for an access
  violation (design decision D7). }
function TRtlPlatformWindows.ProcessExitCode(Proc: Pointer): Int32;
begin
  Result := PWinProcess(Proc)^.ExitCode;
end;

procedure TRtlPlatformWindows.ProcessFree(Proc: Pointer);
var
  P: PWinProcess;
begin
  P := PWinProcess(Proc);
  if P = nil then
    Exit;
  if P^.Pipe <> nil then
    W32CloseHandle(P^.Pipe);
  if P^.Process <> nil then
    W32CloseHandle(P^.Process);
  P^.Exe := '';
  P^.Args := '';
  _BlaiseFreeMem(P);
end;

{ ================================================================== }
{ Flat functions                                                       }
{ ================================================================== }

procedure _SetArgs(Argc: Int32; Argv: Pointer);
begin
  GArgC := Argc;
  GArgV := Argv;
  if GRtlPlatform = nil then
    GRtlPlatform := TRtlPlatformWindows.Create();
end;

{ A NUL-terminated copy of S that lives as long as the process. }
function LastingCStr(const S: string): PChar;
var
  I: Int;
begin
  Result := PChar(_BlaiseGetMem(Length(S) + 1));
  for I := 0 to Length(S) - 1 do
    Result[I] := PChar(S)[I];
  Result[Length(S)] := #0;
end;

function _EnvVector: Pointer;
var
  Block, Entry: Pointer;
  Count, I, N: Int;
  Units: Int32;
  Vec: Pointer;
begin
  if GEnvVector <> nil then
    Exit(GEnvVector);
  Block := W32GetEnvironmentStringsW();
  if Block = nil then
    Exit(nil);
  { the block is NUL-terminated entries, ended by an empty one }
  Count := 0;
  Entry := Block;
  while PUInt16(Entry)^ <> 0 do
  begin
    Count := Count + 1;
    Entry := Entry + (Int64(WideLen(Entry)) + 1) * 2;
  end;
  Vec := _BlaiseGetMem((Count + 1) * SizeOf(Pointer));
  N := 0;
  Entry := Block;
  for I := 1 to Count do
  begin
    Units := WideLen(Entry);
    if PUInt16(Entry)^ <> Ord('=') then
    begin
      PPointer(Vec + N * SizeOf(Pointer))^ := LastingCStr(FromWide(Entry, Units));
      N := N + 1;
    end;
    Entry := Entry + (Int64(Units) + 1) * 2;
  end;
  PPointer(Vec + N * SizeOf(Pointer))^ := nil;
  GEnvVector := Vec;
  Result := Vec;
end;

function _PathStat(const Path: string; FollowLinks: Int32; AOut: Pointer): Int64;
var
  Attrs: UInt32;
  Size, WriteTime, Sec, NSec: Int64;
  Mode: Int32;
begin
  if not QueryPath(Path, FollowLinks <> 0, Attrs, Size, WriteTime) then
    Exit(-1);
  { The mode a POSIX reader expects: READONLY clears the write bits, and a
    program (by its extension, as FsAccess decides) has the execute bits. }
  if (Attrs and FILE_ATTRIBUTE_DIRECTORY) <> 0 then
    Mode := $1ED
  else if (Attrs and FILE_ATTRIBUTE_READONLY) <> 0 then
    Mode := $124
  else
    Mode := $1A4;
  if ((Attrs and FILE_ATTRIBUTE_DIRECTORY) = 0) and HasProgramExtension(Path) then
    Mode := Mode or $49;
  SplitFileTime(WriteTime, Sec, NSec);
  PInt32(AOut)^ := KindOfAttributes(Attrs, FollowLinks <> 0);
  PInt32(AOut + 4)^ := Mode;
  PInt64(AOut + 8)^ := Size;
  PInt64(AOut + 16)^ := Sec;
  PInt64(AOut + 24)^ := NSec;
  Result := 0;
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
