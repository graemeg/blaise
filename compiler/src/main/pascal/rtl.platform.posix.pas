{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit rtl.platform.posix;

// Blaise RTL — POSIX implementation of the platform abstraction layer.
//
// This unit consolidates all platform-specific runtime code for
// Linux/FreeBSD (and eventually macOS).  All OS operations are
// implemented as methods on TRtlPlatformPosix, which overrides the
// abstract TRtlPlatform base class.
//
// The underscore ABI functions (_FileExists, _SysWriteStr, _TimeNow,
// _ProcessCreate, etc.) are thin stubs that delegate to GRtlPlatform.
// They exist because the compiler codegen emits calls to these symbols
// directly.  When a second platform is added, only a new TRtlPlatformXxx
// subclass is needed — the ABI stubs and codegen remain unchanged.
//
// All external libc bindings are in the interface section (Blaise
// requirement: external declarations with a nil body must not appear in
// the implementation section to avoid codegen crashes).

interface

uses
  rtl.platform;
  { NOTE: the concrete TPlatformLayout adapter (rtl.platform.layout.<os>) is
    deliberately NOT imported here.  It is selected and linked by the driver
    for the runtime --target (BuildRTLUnitList), and its GPlatformLayout
    assignment runs via the bare `_BlaisePlatformInit` symbol that `main` calls
    at startup — a link-time swap, not a compile-time `uses`.  Importing a
    concrete layout would hard-wire one OS into this shared POSIX unit. }

type
  TRtlPlatformPosix = class(TRtlPlatform)
  public
    { File operations }
    function FileExists(const APath: string): Boolean; override;
    procedure DeleteFile(const APath: string); override;
    function RenameFile(const AOldPath, ANewPath: string): Boolean; override;
    function ReadFile(const APath: string): string; override;
    procedure WriteFile(const APath, AContent: string); override;
    procedure AppendFile(const APath, AContent: string); override;
    function FileAge(const APath: string): Int64; override;

    { Directory operations }
    function DirectoryExists(const APath: string): Boolean; override;
    function PathKind(const APath: string; AFollowLinks: Boolean): Int32; override;
    function ForceDirectories(const APath: string): Boolean; override;
    function RemoveDir(const APath: string): Boolean; override;
    function GetCurrentDir: string; override;
    function SetCurrentDir(const APath: string): Boolean; override;
    function ListDir(const APath: string): string; override;

    { OS utilities }
    function GetTempDir: string; override;
    function GetTempFileName(const ADir, APrefix: string): string; override;
    function GetProcessID: Int32; override;
    function ReadLink(const APath: string): string; override;
    function MakeExecutable(const APath: string): Boolean; override;
    function RandomBytes(ABuf: Pointer; ACount: Int): Boolean; override;
    function GetEnvVar(const AName: string): string; override;
    procedure Sleep(AMilliseconds: Int32); override;
    procedure Halt(AExitCode: Int32); override;

    { Process }
    function Exec(const ACmd: string): Int32; override;
    function ParamCount: Int32; override;
    function ParamStr(AIndex: Int32): string; override;

    { Console I/O }
    procedure SysWriteStr(Fd: Int32; S: Pointer); override;
    procedure SysWriteInt(Fd: Int32; N: Int32); override;
    procedure SysWriteInt64(Fd: Int32; N: Int64); override;
    procedure SysWriteUInt64(Fd: Int32; N: UInt64); override;
    procedure SysWriteDouble(Fd: Int32; V: Float64); override;
    procedure SysWriteSingle(Fd: Int32; V: Float32); override;
    procedure SysWriteBool(Fd: Int32; B: Boolean); override;
    procedure SysWriteNewline(Fd: Int32); override;

    { File-descriptor primitives }
    function FdOpenRead(Path: Pointer): Int32; override;
    function FdOpenWrite(Path: Pointer): Int32; override;
    function FdOpenAppend(Path: Pointer): Int32; override;
    function FdRead(Fd: Int32; Buf: Pointer; Count: Int): Int; override;
    function FdWrite(Fd: Int32; Buf: Pointer; Count: Int): Int; override;
    function FdSeek(Fd: Int32; Offset: Int64; Origin: Int32): Int64; override;
    function FdSize(Fd: Int32): Int64; override;
    procedure FdClose(Fd: Int32); override;

    { POSIX-shaped file-system calls: the libc calls themselves }
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

    { Date/Time }
    function TimeNow: Int64; override;
    function TimeLocalOffsetSecs: Int32; override;
    procedure TimeSplit(Nanos: Int64;
      out Year, Month, Day, Hour, Min, Sec, NSec: Int32); override;
    function TimeJoin(Year, Month, Day,
      Hour, Min, Sec, NSec: Int32): Int64; override;
    function TimeIsLeapYear(Year: Int32): Int32; override;
    function TimeDaysInMonth(Year, Month: Int32): Int32; override;

    { Process management }
    function ProcessCreate: Pointer; override;
    procedure ProcessSetExe(Proc: Pointer; ExeStr: Pointer); override;
    procedure ProcessAddArg(Proc: Pointer; ArgStr: Pointer); override;
    procedure ProcessExecute(Proc: Pointer); override;
    function ProcessRunning(Proc: Pointer): Int32; override;
    function ProcessReadOutput(Proc: Pointer): Pointer; override;
    procedure ProcessWaitOnExit(Proc: Pointer); override;
    function ProcessExitCode(Proc: Pointer): Int32; override;
    procedure ProcessFree(Proc: Pointer); override;
    function ProcSpawn(const AExe, AArgs, AEnv, ACwd: string; AUseEnv: Int32;
      AFds, AChild: Pointer): Int32; override;
    function ProcWait(AChild: Int64; ABlock: Int32; AExitCode: Pointer): Int32; override;
    function ProcSignal(AChild: Int64; AForce: Int32): Int32; override;
    function ProcPid(AChild: Int64): Int32; override;
    procedure ProcRelease(AChild: Int64); override;
    function ProcPollRead(AFds: Pointer; ACount, ATimeoutMs: Int32;
      AReady: Pointer): Int32; override;
  end;

{ ------------------------------------------------------------------ }
{ POSIX libc bindings                                                  }
{ ------------------------------------------------------------------ }

type
  { Opaque struct stat buffer.  The kernel fills it; the field offsets and the
    true size are target-specific (Linux 144 bytes, FreeBSD larger), so the RTL
    never names the fields directly — it sizes the buffer generously and reads
    Size/Mtime/Mode through GPlatformLayout.StatSize/StatMtime/StatMode at the
    target's offsets.  256 bytes covers every supported target's struct stat. }
  TStatBuf = array[0..255] of Byte;
  PStatBuf = ^TStatBuf;

  TTimeSpec = record
    Sec:  Int64;
    NSec: Int64;
  end;

  TTm = record
    Sec:     Int32;
    Min:     Int32;
    Hour:    Int32;
    MDay:    Int32;
    Mon:     Int32;
    Year:    Int32;
    WDay:    Int32;
    YDay:    Int32;
    IsDST:   Int32;
    GmtOff:  Int64;
    Zone:    Pointer;
  end;
  PTm = ^TTm;

  TPCharArray = ^PChar;

{ Memory }
function  _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);          external name '_BlaiseFreeMem';
{ Bootstrap fallback for GPlatformLayout: defined WEAK by the linked target's
  concrete layout unit (rtl.platform.layout.<os>).  The current codegen assigns
  GPlatformLayout by calling that unit's init directly from main, so this call
  is redundant then (idempotent).  It only matters for a binary built by an
  older codegen that does not yet emit the direct main-call — there it is the
  sole path that initialises the layout. }
procedure _BlaisePlatformInit;                    external name '_BlaisePlatformInit';

{ String ARC }
function  _IntToStr(N: Int32): Pointer;   external name '_IntToStr';
function  _Int64ToStr(N: Int64): Pointer;   external name '_Int64ToStr';
function  _UInt64ToStr(N: UInt64): Pointer; external name '_UInt64ToStr';
function  _DoubleToStr(V: Float64): Pointer; external name '_DoubleToStr';
function  _SingleToStr(V: Float32): Pointer; external name '_SingleToStr';
procedure _StringAddRef(Ptr: Pointer);      external name '_StringAddRef';
procedure _StringRelease(Ptr: Pointer);     external name '_StringRelease';

{ POSIX libc — file I/O }
{ open(2) is VARIADIC in C — `int open(const char *, int, ...)` — and the
  mode is a variadic argument.  The declaration must say so: Apple's arm64
  ABI passes variadic arguments ON THE STACK (never x2-x7), so a fixed
  3-arg declaration put the mode in x2 and libSystem read garbage off the
  stack — files were created with mode 0111 on the M1
  (SMOKE_MAC_VARIADIC_ABI_HANDOVER.md).  On Linux x86-64 the register
  assignment happens to coincide, which is why this only bit on macOS. }
function  libc_open(Path: PChar; Flags: Int32): Int32; cdecl; varargs; external name 'open';
function  libc_open2(Path: PChar; Flags: Int32): Int32;                 external name 'open';
function  libc_read(Fd: Int32; Buf: Pointer; Count: Int64): Int64;        external name 'read';
function  libc_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;       external name 'write';
function  libc_lseek(Fd: Int32; Offset: Int64; Whence: Int32): Int64;   external name 'lseek';
function  libc_close(Fd: Int32): Int32;                                  external name 'close';
function  libc_fstat(Fd: Int32; Buf: Pointer): Int32;                   external name 'fstat';
function  libc_stat(Path: PChar; Buf: Pointer): Int32;                    external name 'stat';
function  libc_lstat(Path: PChar; Buf: Pointer): Int32;                   external name 'lstat';
function  libc_mkdir(Path: PChar; Mode: Int32): Int32;                   external name 'mkdir';
function  libc_rmdir(Path: PChar): Int32;                                  external name 'rmdir';
function  libc_readlink(Path: PChar; Buf: PChar; Size: Int64): Int64; external name 'readlink';
function  libc_chmod(Path: PChar; Mode: Int32): Int32; external name 'chmod';
function  libc_getentropy(Buf: Pointer; Len: Int64): Int32; external name 'getentropy';
function  libc_unlink(Path: PChar): Int32;                                 external name 'unlink';
function  libc_rename(OldPath, NewPath: PChar): Int32;                     external name 'rename';
function  libc_symlink(Target, LinkPath: PChar): Int32; external name 'symlink';
function  libc_access(Path: PChar; Mode: Int32): Int32; external name 'access';
function  libc_futimens(Fd: Int32; Times: Pointer): Int32; external name 'futimens';
{ UTIME_OMIT for this target (rtl.platform.layout.<os>). }
function  _UtimeOmit: Int64; external name '_UtimeOmit';
function  libc_getcwd(Buf: PChar; Size: Int64): PChar;                       external name 'getcwd';
{ getdirentries(3) is the one directory-reading spelling libc provides on all
  three POSIX targets (glibc >= 2.2.5, FreeBSD, macOS); the freestanding
  syscall leaves define the same symbol, so this single binding serves the
  libc and --static paths alike.  Returns bytes written into Buf, 0 at end of
  directory, negative on error.

  Darwin is the exception: its plain getdirentries is the LEGACY 32-bit-inode
  call (d_reclen @4, d_name @8), while the Darwin layout unit reads the
  64-bit-inode dirent (d_reclen @16, d_name @21) -- so every name lost its
  first character.  __getdirentries64 (libsystem_kernel, same arguments)
  returns the layout the unit expects. }
{$IFDEF DARWIN}
function  libc_getdirentries(Fd: Int32; Buf: Pointer; NBytes: Int64;
                             Basep: Pointer): Int64;                          external name '__getdirentries64';
{$ELSE}
function  libc_getdirentries(Fd: Int32; Buf: Pointer; NBytes: Int64;
                             Basep: Pointer): Int64;                          external name 'getdirentries';
{$ENDIF}
function  libc_chdir(Path: PChar): Int32;                                  external name 'chdir';
function  libc_getenv(Name: PChar): PChar;                                   external name 'getenv';
function  libc_mkstemp(Template: PChar): Int32;                            external name 'mkstemp';
function  libc_nanosleep(Req: Pointer; Rem: Pointer): Int32;               external name 'nanosleep';
function  libc_getpid: Int32;                                               external name 'getpid';
function  libc_system(Cmd: PChar): Int32;                                  external name 'system';
procedure libc_exit(Code: Int32);                                          external name 'exit';
function  libc_strlen(S: PChar): Int64;                                      external name 'strlen';

{ POSIX libc — date/time }
function  libc_clock_gettime(ClockId: Int32; Ts: Pointer): Int32; external name 'clock_gettime';
function  libc_time(T: Pointer): Int64;                                external name 'time';
function  libc_localtime_r(T: Pointer; Tm: PTm): PTm;                 external name 'localtime_r';
function  libc_gmtime_r(T: Pointer; Tm: PTm): PTm;                    external name 'gmtime_r';
function  libc_timegm(Tm: PTm): Int64;                                 external name 'timegm';

{ POSIX libc — process management }
function  libc_fork: Int32;                              external name 'fork';
function  libc_execvp(File_: PChar; Argv: Pointer): Int32; external name 'execvp';
procedure libc__exit(Code: Int32);                       external name '_exit';
function  libc_waitpid(Pid: Int32; Status: Pointer; Options: Int32): Int32; external name 'waitpid';
function  libc_pipe(Fds: Pointer): Int32;                external name 'pipe';
function  libc_dup2(OldFd, NewFd: Int32): Int32;       external name 'dup2';
function  libc_execve(Path: PChar; Argv, Envp: Pointer): Int32; external name 'execve';
function  libc_kill(Pid, Sig: Int32): Int32; external name 'kill';
function  libc_poll(Fds: Pointer; NFds: Int64; Timeout: Int32): Int32; external name 'poll';
{ fcntl is C-variadic: the third argument must travel the variadic way. }
function  libc_fcntl(Fd, Cmd: Int32): Int32; cdecl; varargs; external name 'fcntl';
function  libc_signal(Signum: Int32; Handler: Pointer): Pointer; external name 'signal';
{ errno, per build profile (runtime.errno.*, chosen at link time): the
  freestanding profile has no errno variable; its calls return -errno. }
function  errno_GetOsErrno: Int; external name 'GetOsErrno';
function  errno_Interrupted(N: Int64): Boolean; external name 'Interrupted';

{ ------------------------------------------------------------------ }
{ Underscore ABI stubs                                                 }
{ ------------------------------------------------------------------ }

{ argc/argv — _SetArgs is called before GRtlPlatform is initialised,
  so it stores directly into module globals rather than delegating. }
procedure _SetArgs(Argc: Int32; Argv: Pointer);
{ The environment the program was started with: a nil-terminated array of
  'NAME=VALUE' C strings.  The kernel lays it out directly after argv's
  terminating nil on every POSIX target Blaise supports (Linux, FreeBSD,
  macOS), so it is found from the argv _SetArgs keeps.  nil before
  _SetArgs.  SysUtils.GetEnvironmentString reads it. }
function _EnvVector: Pointer;


{ Not a compiler builtin: stdlib's IO.Files imports it via `external name`.
  stat(2) (FollowLinks <> 0) or lstat(2) of Path into AOut, a record laid out
  as: Kind Int32 (as _PathKind), Mode Int32 (the permission bits, 12 low
  bits of st_mode), Size Int64, MtimeSec Int64, MtimeNsec Int64.  Returns the
  call's result: 0 on success, else the failure (-1 with errno, or -errno in
  the freestanding profile); AOut is untouched on failure. }
function  _PathStat(const Path: string; FollowLinks: Int32; AOut: Pointer): Int64;


procedure _SysWritePChar(Fd: Int32; P: PChar);


implementation

{ ------------------------------------------------------------------ }
{ Constants                                                            }
{ ------------------------------------------------------------------ }

{ String and dynamic-array header layout.  Every RTL unit that reads or
  writes a header declares this same block (the RTL units cannot share a
  unit of constants: a new RTL unit is unknown to the previous compiler's
  BuildRTLUnitList), so a layout change edits each copy alike.  Offsets are
  from the data pointer. }
const
  { String: Capacity, pad, RefCount, Length; data 8-aligned }
  STR_HDR_SIZE = 24;
  STR_RC_OFS   = -12;  { Int32; -1 = immortal }
  STR_LEN_OFS  = -8;
  STR_CAP_OFS  = -24;
  { Dynamic array: pad, element hook, pad, RefCount, Length; elements stay
    16-aligned }
  DA_HDR_SIZE  = 32;
  DA_HOOK_OFS  = -24;
  DA_RC_OFS    = -12;  { Int32; -1 = immortal }
  DA_LEN_OFS   = -8;
type
  TStrLen = Int64;     { the width of a string header's Length and Capacity }
  PStrLen = ^TStrLen;
  TDaLen  = Int64;     { the width of a dynamic-array header's Length }
  PDaLen  = ^TDaLen;

const
  NS_PER_SEC = 1000000000;

  { O_* / S_* / SEEK_* / CLOCK_REALTIME / WNOHANG and the struct stat layout
    live in GPlatformLayout (rtl.platform.layout.<os>) — their values/offsets
    differ across POSIX targets.  See docs/native-target-architecture.adoc. }

{ ------------------------------------------------------------------ }
{ Shared string helpers                                                }
{ ------------------------------------------------------------------ }

function StrAlloc(Len: Int64): Pointer;
var
  Base:       PChar;
  RC:         ^Int32;
  LN, CP:     PStrLen;
  NulPtr:     PChar;
begin
  Base := _BlaiseGetMem(STR_HDR_SIZE + Len + 1);
  if Base = nil then begin Result := nil; Exit end;
  NulPtr := PChar(Base + STR_HDR_SIZE);
  RC  := Pointer(NulPtr) + STR_RC_OFS;   RC^ := 0;
  LN  := Pointer(NulPtr) + STR_LEN_OFS;  LN^ := Len;
  CP  := Pointer(NulPtr) + STR_CAP_OFS;  CP^ := Len;
  NulPtr[Len] := #0;
  Result := NulPtr;
end;

function StrFromCStr(S: PChar): Pointer;
var
  Len: Int64;
  R:   PChar;
  I:   Int64;
begin
  if S = nil then begin Result := StrAlloc(0); Exit end;
  Len := libc_strlen(S);
  R := StrAlloc(Len);
  if (R <> nil) and (Len > 0) then
    for I := 0 to Len - 1 do R[I] := S[I];
  Result := R;
end;

{ Make a freshly built rc = 0 string buffer (StrAlloc, StrFromCStr) the
  function's string result WITHOUT copying it.  string(PChar(P)) is a
  conversion: it copies up to the first NUL, which truncated binary file
  content, and it leaked P.  The result is the caller's one reference. }
function StrAdopt(P: Pointer): string;
var
  RC: ^Int32;
  Slot: ^Pointer;
begin
  Result := '';
  if P = nil then Exit;
  RC := Pointer(P) + STR_RC_OFS;
  RC^ := 1;
  Slot := Pointer(@Result);
  Slot^ := P;
end;

function StrLen(DataPtr: Pointer): Int64;
var
  LPtr: PStrLen;
begin
  if DataPtr = nil then begin Result := 0; Exit end;
  LPtr := DataPtr + STR_LEN_OFS;
  Result := LPtr^;
end;

function StrData(DataPtr: Pointer): PChar;
begin
  if DataPtr = nil then Result := nil else Result := PChar(DataPtr);
end;

function StrDup(S: PChar): PChar;
var
  Len: Int;
  Buf: PChar;
  I:   Int;
begin
  if S = nil then begin Result := nil; Exit end;
  Len := Int32(libc_strlen(S));
  Buf := _BlaiseGetMem(Len + 1);
  if Buf = nil then begin Result := nil; Exit end;
  for I := 0 to Len do Buf[I] := S[I];
  Result := Buf;
end;

procedure WriteAllToFd(Fd: Int; Data: PChar; Len: Int64);
var
  P: PChar;
  Rem: Int64;
  Written: Int64;
begin
  P := Data;
  Rem := Len;
  while Rem > 0 do
  begin
    Written := libc_write(Fd, P, Rem);
    if Written <= 0 then Break;
    P := P + Written;
    Rem := Rem - Written;
  end;
end;

{ ------------------------------------------------------------------ }
{ Global argc/argv                                                     }
{ ------------------------------------------------------------------ }

var
  GArgC: Int;
  GArgV: TPCharArray;

function ArgvGet(Arr: TPCharArray; Index: Int): PChar;
var
  Slot: TPCharArray;
begin
  Slot := Arr + (Index * SizeOf(Pointer));
  Result := Slot^;
end;

procedure ArgvSet(Arr: TPCharArray; Index: Int; Val: Pointer);
var
  Slot: TPCharArray;
begin
  Slot := Arr + (Index * SizeOf(Pointer));
  Slot^ := PChar(Val);
end;

{ ------------------------------------------------------------------ }
{ Process record type                                                  }
{ ------------------------------------------------------------------ }

type
  TBlaiseProcess = record
    Exe:      PChar;
    Argv:     TPCharArray;
    ArgC:     Int32;
    ArgVCap:  Int32;
    Pid:      Int32;
    PipeFd:   Int32;
    ExitCode: Int32;
    Waited:   Int32;
  end;
  PBlaiseProcess = ^TBlaiseProcess;

{ ================================================================== }
{ TRtlPlatformPosix — File operations                                 }
{ ================================================================== }

function TRtlPlatformPosix.FileExists(const APath: string): Boolean;
var
  Fd: Int;
begin
  Fd := libc_open2(StrData(Pointer(APath)), GPlatformLayout.O_RDONLY());
  if Fd < 0 then begin Result := False; Exit end;
  libc_close(Fd);
  Result := True;
end;

procedure TRtlPlatformPosix.DeleteFile(const APath: string);
begin
  libc_unlink(StrData(Pointer(APath)));
end;

function TRtlPlatformPosix.RenameFile(const AOldPath, ANewPath: string): Boolean;
begin
  Result := libc_rename(StrData(Pointer(AOldPath)), StrData(Pointer(ANewPath))) = 0;
end;

function TRtlPlatformPosix.ReadFile(const APath: string): string;
var
  Fd:   Int;
  St:   TStatBuf;
  Sz:   Int64;
  R:    PChar;
  Got, N: Int64;
  LPtr: PStrLen;
begin
  Fd := libc_open2(StrData(Pointer(APath)), GPlatformLayout.O_RDONLY());
  if Fd < 0 then begin Result := ''; Exit end;
  if libc_fstat(Fd, @St) < 0 then begin libc_close(Fd); Result := ''; Exit end;
  Sz := GPlatformLayout.StatSize(@St);
  if Sz < 0 then begin libc_close(Fd); Result := ''; Exit end;
  R := StrAlloc(Sz);
  if R = nil then begin libc_close(Fd); Result := ''; Exit end;
  { one read() may return less than asked (Linux caps a call near 2 GiB) }
  Got := 0;
  while Got < Sz do
  begin
    N := libc_read(Fd, R + Got, Sz - Got);
    if N <= 0 then Break;
    Got := Got + N;
  end;
  libc_close(Fd);
  LPtr  := Pointer(R) + STR_LEN_OFS;  LPtr^ := Got;
  LPtr  := Pointer(R) + STR_CAP_OFS;  LPtr^ := Got;
  R[Got] := #0;
  Result := StrAdopt(R);
end;

procedure TRtlPlatformPosix.WriteFile(const APath, AContent: string);
var
  Fd:  Int;
  Len: Int64;
begin
  Fd := libc_open(StrData(Pointer(APath)), GPlatformLayout.O_WRONLY() or GPlatformLayout.O_CREAT() or GPlatformLayout.O_TRUNC(), 420);
  if Fd < 0 then Exit;
  Len := StrLen(Pointer(AContent));
  if Len > 0 then
    WriteAllToFd(Fd, StrData(Pointer(AContent)), Len);
  libc_close(Fd);
end;

procedure TRtlPlatformPosix.AppendFile(const APath, AContent: string);
var
  Fd:  Int;
  Len: Int64;
begin
  Fd := libc_open(StrData(Pointer(APath)), GPlatformLayout.O_WRONLY() or GPlatformLayout.O_CREAT() or GPlatformLayout.O_APPEND(), 420);
  if Fd < 0 then Exit;
  Len := StrLen(Pointer(AContent));
  if Len > 0 then
    WriteAllToFd(Fd, StrData(Pointer(AContent)), Len);
  libc_close(Fd);
end;

function TRtlPlatformPosix.FileAge(const APath: string): Int64;
var
  St: TStatBuf;
begin
  if libc_stat(StrData(Pointer(APath)), @St) <> 0 then begin Result := -1; Exit end;
  Result := GPlatformLayout.StatMtime(@St);
end;

{ ================================================================== }
{ TRtlPlatformPosix — Directory operations                            }
{ ================================================================== }

function TRtlPlatformPosix.DirectoryExists(const APath: string): Boolean;
var
  St: TStatBuf;
begin
  if libc_stat(StrData(Pointer(APath)), @St) <> 0 then begin Result := False; Exit end;
  Result := (GPlatformLayout.StatMode(@St) and GPlatformLayout.S_IFMT()) = GPlatformLayout.S_IFDIR();
end;

function TRtlPlatformPosix.PathKind(const APath: string; AFollowLinks: Boolean): Int32;
var
  St:   TStatBuf;
  Rc:   Int;
  Mode: Int;
begin
  if AFollowLinks then
    Rc := libc_stat(StrData(Pointer(APath)), @St)
  else
    Rc := libc_lstat(StrData(Pointer(APath)), @St);
  if Rc <> 0 then begin Result := 0; Exit end;
  Mode := GPlatformLayout.StatMode(@St) and GPlatformLayout.S_IFMT();
  if Mode = GPlatformLayout.S_IFREG() then
    Result := 1
  else if Mode = GPlatformLayout.S_IFDIR() then
    Result := 2
  else if Mode = GPlatformLayout.S_IFLNK() then
    Result := 3
  else
    Result := 4;
end;

function TRtlPlatformPosix.ForceDirectories(const APath: string): Boolean;
var
  P:     PChar;
  Buf:   array[0..4095] of Byte;
  BufP:  PChar;
  Len:   Int;
  I:     Int;
  Saved: Byte;
  St:    TStatBuf;
begin
  P := StrData(Pointer(APath));
  if (P = nil) or (P[0] = #0) then begin Result := False; Exit end;
  Len := Int32(libc_strlen(P));
  if Len >= 4096 then begin Result := False; Exit end;
  BufP := PChar(@Buf[0]);
  for I := 0 to Len do BufP[I] := P[I];
  I := 1;
  while I <= Len do
  begin
    if (BufP[I] = '/') or (BufP[I] = #0) then
    begin
      Saved := Byte(BufP[I]);
      BufP[I] := #0;
      if libc_stat(BufP, @St) <> 0 then
      begin
        if libc_mkdir(BufP, 493) <> 0 then
        begin
          Result := False; Exit;
        end;
      end else if (GPlatformLayout.StatMode(@St) and GPlatformLayout.S_IFMT()) <> GPlatformLayout.S_IFDIR() then
      begin
        Result := False; Exit;
      end;
      BufP[I] := Chr(Saved);
    end;
    Inc(I);
  end;
  Result := True;
end;

function TRtlPlatformPosix.RemoveDir(const APath: string): Boolean;
begin
  libc_rmdir(StrData(Pointer(APath)));
  Result := True;
end;

function TRtlPlatformPosix.GetCurrentDir: string;
var
  Buf:       array[0..4095] of Byte;
  CWD:       PChar;
  Len:       Int;
  NeedSlash: Int;
  R:         PChar;
  I:         Int;
begin
  CWD := libc_getcwd(PChar(@Buf[0]), 4096);
  if CWD = nil then begin Result := ''; Exit end;
  Len := Int32(libc_strlen(CWD));
  if (Len > 0) and (CWD[Len - 1] <> '/') then NeedSlash := 1 else NeedSlash := 0;
  R := StrAlloc(Len + NeedSlash);
  if R = nil then begin Result := ''; Exit end;
  for I := 0 to Len - 1 do R[I] := CWD[I];
  if NeedSlash = 1 then R[Len] := '/';
  Result := StrAdopt(R);
end;

function TRtlPlatformPosix.SetCurrentDir(const APath: string): Boolean;
begin
  Result := libc_chdir(StrData(Pointer(APath))) = 0;
end;

function TRtlPlatformPosix.ListDir(const APath: string): string;
const
  BufSize = 32768;
var
  Buf:      array[0..BufSize - 1] of Byte;
  Fd:       Int;
  Got:      Int64;
  Pos:      Int64;
  Ent:      Pointer;
  RecLen:   Int;
  Nm:       PChar;
  NmLen:    Int;
  Total:    Int;
  Count:    Int;
  R:        PChar;
  W:        Int;
  I:        Int;
  Pass:     Int;
  Skip:     Boolean;
  { glibc's getdirentries(3) writes through basep unconditionally, so it must
    point at real storage — passing nil segfaults inside libc.  (The
    freestanding syscall leaf ignores it, which is why only the libc-linked
    build crashed.)  The value itself is never read. }
  Basep:    Int64;
begin
  Result := '';
  Basep  := 0;
  Fd := libc_open2(StrData(Pointer(APath)), GPlatformLayout.O_RDONLY());
  if Fd < 0 then Exit;

  { Two passes over the directory: the first measures, the second fills the
    exact-sized buffer.  The directory is re-read (lseek back to 0) rather
    than buffered in a growable list because the RTL has no list type — and
    a short second read is harmless, the writer is bounded by Total. }
  Total := 0;
  Count := 0;
  R     := nil;
  W     := 0;

  for Pass := 0 to 1 do
  begin
    if Pass = 1 then
    begin
      if Count = 0 then begin libc_close(Fd); Exit end;
      { Total name bytes + (Count - 1) separators. }
      R := StrAlloc(Total + Count - 1);
      if R = nil then begin libc_close(Fd); Exit end;
      libc_lseek(Fd, 0, GPlatformLayout.SEEK_SET());
    end;

    repeat
      Got := libc_getdirentries(Fd, @Buf[0], BufSize, @Basep);
      if Got <= 0 then Break;
      Pos := 0;
      while Pos < Got do
      begin
        Ent    := Pointer(PChar(@Buf[0]) + Pos);
        RecLen := GPlatformLayout.DirentRecLen(Ent);
        { A zero/negative reclen would not advance Pos — bail out rather
          than spin forever on a malformed buffer. }
        if RecLen <= 0 then Break;
        Nm    := PChar(GPlatformLayout.DirentName(Ent));
        NmLen := Int32(libc_strlen(Nm));
        { Skip '.' and '..'. }
        Skip := ((NmLen = 1) and (Nm[0] = '.'))
             or ((NmLen = 2) and (Nm[0] = '.') and (Nm[1] = '.'));
        { A deleted-but-still-listed entry has an empty name on some
          filesystems; nothing useful to return for it. }
        if NmLen = 0 then Skip := True;
        if not Skip then
        begin
          if Pass = 0 then
          begin
            Total := Total + NmLen;
            Count := Count + 1
          end
          else
          begin
            if W > 0 then
            begin
              if W >= Total + Count - 1 then Break;
              R[W] := #10;
              W    := W + 1
            end;
            for I := 0 to NmLen - 1 do
            begin
              if W >= Total + Count - 1 then Break;
              R[W] := Nm[I];
              W    := W + 1
            end
          end
        end;
        Pos := Pos + RecLen
      end
    until False
  end;

  libc_close(Fd);
  if R <> nil then
    Result := StrAdopt(R)
end;

{ ================================================================== }
{ TRtlPlatformPosix — OS utilities                                    }
{ ================================================================== }

function TRtlPlatformPosix.GetTempDir: string;
var
  Tmp:       PChar;
  Len:       Int;
  NeedSlash: Int;
  R:         PChar;
  I:         Int;
begin
  Tmp := libc_getenv(StrData('TMPDIR'));
  if (Tmp = nil) or (Tmp[0] = #0) then Tmp := StrData('/tmp');
  Len := Int32(libc_strlen(Tmp));
  if (Len > 0) and (Tmp[Len - 1] <> '/') then NeedSlash := 1 else NeedSlash := 0;
  R := StrAlloc(Len + NeedSlash);
  if R = nil then begin Result := ''; Exit end;
  for I := 0 to Len - 1 do R[I] := Tmp[I];
  if NeedSlash = 1 then R[Len] := '/';
  Result := StrAdopt(R);
end;

function TRtlPlatformPosix.GetTempFileName(const ADir, APrefix: string): string;
var
  DStr:      PChar;
  PStr:      PChar;
  DLen:      Int;
  PLen:      Int;
  NeedSlash: Int;
  TmplLen:   Int;
  Tmpl:      PChar;
  Tmp:       PChar;
  TmpLen:    Int;
  Fd:        Int;
  I:         Int;
begin
  DStr := StrData(Pointer(ADir));
  PStr := StrData(Pointer(APrefix));
  if DStr = nil then DLen := 0 else DLen := Int32(libc_strlen(DStr));
  if PStr = nil then PLen := 0 else PLen := Int32(libc_strlen(PStr));

  if DLen = 0 then
  begin
    Tmp := libc_getenv(StrData('TMPDIR'));
    if (Tmp = nil) or (Tmp[0] = #0) then Tmp := StrData('/tmp');
    TmpLen := Int32(libc_strlen(Tmp));
    NeedSlash := 0;
    if (TmpLen > 0) and (Tmp[TmpLen - 1] <> '/') then NeedSlash := 1;
    TmplLen := TmpLen + NeedSlash + PLen + 6;
    Tmpl := _BlaiseGetMem(TmplLen + 1);
    if Tmpl = nil then begin Result := StrAdopt(StrFromCStr(StrData('/tmp/blaise_XXXXXX'))); Exit end;
    for I := 0 to TmpLen - 1 do Tmpl[I] := Tmp[I];
    if NeedSlash = 1 then Tmpl[TmpLen] := '/';
    for I := 0 to PLen - 1 do Tmpl[TmpLen + NeedSlash + I] := PStr[I];
    for I := 0 to 5 do Tmpl[TmpLen + NeedSlash + PLen + I] := 'X';
    Tmpl[TmplLen] := #0;
  end else
  begin
    NeedSlash := 0;
    if DStr[DLen - 1] <> '/' then NeedSlash := 1;
    TmplLen := DLen + NeedSlash + PLen + 6;
    Tmpl := _BlaiseGetMem(TmplLen + 1);
    if Tmpl = nil then begin Result := StrAdopt(StrFromCStr(StrData('/tmp/blaise_XXXXXX'))); Exit end;
    for I := 0 to DLen - 1 do Tmpl[I] := DStr[I];
    if NeedSlash = 1 then Tmpl[DLen] := '/';
    for I := 0 to PLen - 1 do Tmpl[DLen + NeedSlash + I] := PStr[I];
    for I := 0 to 5 do Tmpl[DLen + NeedSlash + PLen + I] := 'X';
    Tmpl[TmplLen] := #0;
  end;

  Fd := libc_mkstemp(Tmpl);
  if Fd >= 0 then libc_close(Fd);
  Result := StrAdopt(StrFromCStr(Tmpl));
  _BlaiseFreeMem(Tmpl);
end;

function TRtlPlatformPosix.GetProcessID: Int32;
begin
  Result := libc_getpid();
end;

function TRtlPlatformPosix.ReadLink(const APath: string): string;
var
  Buf: array[0..4095] of Byte;
  N: Int64;
begin
  Result := '';
  N := libc_readlink(StrData(Pointer(APath)), PChar(@Buf[0]), 4095);
  if N <= 0 then
    Exit;
  Buf[N] := 0;
  Result := string(PChar(@Buf[0]));
end;

{ getentropy is the one CSPRNG call every POSIX target has (glibc 2.25+,
  FreeBSD 12+, macOS 10.12+, and the static leaves); it fills at most 256
  bytes a call. }
function TRtlPlatformPosix.RandomBytes(ABuf: Pointer; ACount: Int): Boolean;
var
  Done, N: Int;
begin
  Done := 0;
  while Done < ACount do
  begin
    N := ACount - Done;
    if N > 256 then
      N := 256;
    if libc_getentropy(ABuf + Done, N) <> 0 then
      Exit(False);
    Done := Done + N;
  end;
  Result := True;
end;

function TRtlPlatformPosix.MakeExecutable(const APath: string): Boolean;
begin
  { 0o755: rwxr-xr-x }
  Result := libc_chmod(StrData(Pointer(APath)), 493) = 0;
end;

function TRtlPlatformPosix.GetEnvVar(const AName: string): string;
var
  Val: PChar;
begin
  Val := libc_getenv(StrData(Pointer(AName)));
  if Val = nil then begin Result := ''; Exit end;
  Result := StrAdopt(StrFromCStr(Val));
end;

procedure TRtlPlatformPosix.Sleep(AMilliseconds: Int32);
var
  Ts: TTimeSpec;
begin
  Ts.Sec  := AMilliseconds div 1000;
  Ts.NSec := Int64(AMilliseconds mod 1000) * 1000000;
  libc_nanosleep(@Ts, nil);
end;

procedure TRtlPlatformPosix.Halt(AExitCode: Int32);
begin
  libc_exit(AExitCode);
end;

function TRtlPlatformPosix.Exec(const ACmd: string): Int32;
var
  Status: Int32;
begin
  { system() -- libc's, or the static leaves' fork/execve/wait4 -- returns
    a wait status; Exec returns the command's exit code, as on Windows: the
    code of a normal exit, 128 + the signal of one that was killed (the
    shell's convention), -1 when no shell could be started }
  Status := libc_system(StrData(Pointer(ACmd)));
  if Status = -1 then
    Result := -1
  else if (Status and $7F) = 0 then
    Result := (Status shr 8) and $FF
  else
    Result := 128 + (Status and $7F);
end;

function TRtlPlatformPosix.ParamCount: Int32;
begin
  if GArgC > 0 then
    Result := GArgC - 1
  else
    Result := 0;
end;

function TRtlPlatformPosix.ParamStr(AIndex: Int32): string;
var
  Slot: TPCharArray;
begin
  if (GArgV = nil) or (AIndex < 0) or (AIndex >= GArgC) then
    begin Result := ''; Exit end;
  Slot := GArgV + (AIndex * SizeOf(Pointer));
  Result := StrAdopt(StrFromCStr(Slot^));
end;

{ ================================================================== }
{ TRtlPlatformPosix — Console I/O                                     }
{ ================================================================== }

procedure TRtlPlatformPosix.SysWriteStr(Fd: Int32; S: Pointer);
var
  Len: Int64;
begin
  if S = nil then Exit;
  Len := StrLen(S);
  if Len = 0 then Exit;
  WriteAllToFd(Fd, PChar(S), Len);
end;

procedure TRtlPlatformPosix.SysWriteNewline(Fd: Int32);
var
  NL: array[0..0] of Byte;
begin
  NL[0] := 10;
  WriteAllToFd(Fd, PChar(@NL[0]), 1);
end;

procedure TRtlPlatformPosix.SysWriteInt(Fd: Int32; N: Int32);
var
  S: Pointer;
  Len: Int64;
begin
  S := _IntToStr(N);
  _StringAddRef(S);
  Len := StrLen(S);
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteInt64(Fd: Int32; N: Int64);
var
  S: Pointer;
  Len: Int64;
begin
  S := _Int64ToStr(N);
  _StringAddRef(S);
  Len := StrLen(S);
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteUInt64(Fd: Int32; N: UInt64);
var
  S: Pointer;
  Len: Int64;
begin
  S := _UInt64ToStr(N);
  _StringAddRef(S);
  Len := StrLen(S);
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteDouble(Fd: Int32; V: Float64);
var
  S: Pointer;
  Len: Int64;
begin
  S := _DoubleToStr(V);
  _StringAddRef(S);
  Len := StrLen(S);
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteSingle(Fd: Int32; V: Float32);
var
  S: Pointer;
  Len: Int64;
begin
  S := _SingleToStr(V);
  _StringAddRef(S);
  Len := StrLen(S);
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteBool(Fd: Int32; B: Boolean);
var
  Buf: array[0..4] of Byte;
begin
  if B then
  begin
    Buf[0] := 84;  Buf[1] := 114; Buf[2] := 117; Buf[3] := 101;
    WriteAllToFd(Fd, PChar(@Buf[0]), 4);
  end
  else
  begin
    Buf[0] := 70;  Buf[1] := 97;  Buf[2] := 108; Buf[3] := 115; Buf[4] := 101;
    WriteAllToFd(Fd, PChar(@Buf[0]), 5);
  end;
end;

{ ================================================================== }
{ TRtlPlatformPosix — File-descriptor primitives                      }
{ ================================================================== }

function TRtlPlatformPosix.FdOpenRead(Path: Pointer): Int32;
begin
  Result := libc_open2(StrData(Path), GPlatformLayout.O_RDONLY());
end;

function TRtlPlatformPosix.FdOpenWrite(Path: Pointer): Int32;
begin
  Result := libc_open(StrData(Path), GPlatformLayout.O_WRONLY() or GPlatformLayout.O_CREAT() or GPlatformLayout.O_TRUNC(), 420);
end;

function TRtlPlatformPosix.FdOpenAppend(Path: Pointer): Int32;
begin
  Result := libc_open(StrData(Path), GPlatformLayout.O_WRONLY() or GPlatformLayout.O_CREAT() or GPlatformLayout.O_APPEND(), 420);
end;

function TRtlPlatformPosix.FdRead(Fd: Int32; Buf: Pointer; Count: Int): Int;
begin
  if (Fd < 0) or (Count <= 0) then begin Result := 0; Exit end;
  Result := libc_read(Fd, Buf, Count);
end;

function TRtlPlatformPosix.FdWrite(Fd: Int32; Buf: Pointer; Count: Int): Int;
begin
  if (Fd < 0) or (Count <= 0) then begin Result := 0; Exit end;
  Result := libc_write(Fd, Buf, Count);
end;

function TRtlPlatformPosix.FdSeek(Fd: Int32; Offset: Int64; Origin: Int32): Int64;
var
  Whence: Int;
begin
  case Origin of
    1: Whence := GPlatformLayout.SEEK_CUR();
    2: Whence := GPlatformLayout.SEEK_END();
  else
    Whence := GPlatformLayout.SEEK_SET();
  end;
  Result := libc_lseek(Fd, Offset, Whence);
end;

function TRtlPlatformPosix.FdSize(Fd: Int32): Int64;
var
  St: TStatBuf;
begin
  if libc_fstat(Fd, @St) <> 0 then begin Result := -1; Exit end;
  Result := GPlatformLayout.StatSize(@St);
end;

procedure TRtlPlatformPosix.FdClose(Fd: Int32);
begin
  if Fd >= 0 then libc_close(Fd);
end;

{ ================================================================== }
{ TRtlPlatformPosix — POSIX-shaped file-system calls                  }
{ ================================================================== }

function TRtlPlatformPosix.FsClose(Fd: Int32): Int32;
begin
  Result := libc_close(Fd);
end;

function TRtlPlatformPosix.FsUnlink(const APath: string): Int32;
begin
  Result := libc_unlink(StrData(Pointer(APath)));
end;

function TRtlPlatformPosix.FsRmdir(const APath: string): Int32;
begin
  Result := libc_rmdir(StrData(Pointer(APath)));
end;

function TRtlPlatformPosix.FsMkdir(const APath: string; AMode: Int32): Int32;
begin
  Result := libc_mkdir(StrData(Pointer(APath)), AMode);
end;

function TRtlPlatformPosix.FsRename(const AOldPath, ANewPath: string): Int32;
begin
  Result := libc_rename(StrData(Pointer(AOldPath)), StrData(Pointer(ANewPath)));
end;

function TRtlPlatformPosix.FsChmod(const APath: string; AMode: Int32): Int32;
begin
  Result := libc_chmod(StrData(Pointer(APath)), AMode);
end;

function TRtlPlatformPosix.FsSymlink(const ATarget, ALinkPath: string): Int32;
begin
  Result := libc_symlink(StrData(Pointer(ATarget)), StrData(Pointer(ALinkPath)));
end;

function TRtlPlatformPosix.FsReadlink(const APath: string; ABuf: Pointer;
  ASize: Int64): Int64;
begin
  Result := libc_readlink(StrData(Pointer(APath)), PChar(ABuf), ASize);
end;

function TRtlPlatformPosix.FsAccess(const APath: string; AMode: Int32): Int32;
begin
  Result := libc_access(StrData(Pointer(APath)), AMode);
end;

{ futimens on a read-only descriptor: setting times needs ownership, not
  write permission, and a directory opens read-only too.  A failing futimens
  result is returned after the close, which leaves its errno alone on
  success. }
function TRtlPlatformPosix.FsSetModified(const APath: string;
  ASec, ANSec: Int64): Int32;
var
  Fd: Int32;
  Times: array[0..1] of TTimeSpec;
begin
  Fd := libc_open2(StrData(Pointer(APath)), GPlatformLayout.O_RDONLY());
  if Fd < 0 then
    Exit(Fd);
  Times[0].Sec := 0;
  Times[0].NSec := _UtimeOmit();
  Times[1].Sec := ASec;
  Times[1].NSec := ANSec;
  Result := libc_futimens(Fd, @Times[0]);
  libc_close(Fd);
end;

{ ================================================================== }
{ TRtlPlatformPosix — Date/Time                                       }
{ ================================================================== }

function TRtlPlatformPosix.TimeNow: Int64;
var
  Ts: TTimeSpec;
begin
  libc_clock_gettime(GPlatformLayout.CLOCK_REALTIME(), @Ts);
  Result := Ts.Sec * NS_PER_SEC + Ts.NSec;
end;

function TRtlPlatformPosix.TimeLocalOffsetSecs: Int32;
var
  T:  Int64;
  Lt: TTm;
begin
  T := libc_time(nil);
  libc_localtime_r(@T, @Lt);
  Result := Int32(Lt.GmtOff);
end;

procedure TRtlPlatformPosix.TimeSplit(Nanos: Int64;
  out Year, Month, Day, Hour, Min, Sec, NSec: Int32);
var
  WholeSec: Int64;
  NanoPart: Int;
  T:        Int64;
  Tm:       TTm;
begin
  WholeSec := Nanos div NS_PER_SEC;
  NanoPart := Int32(Nanos mod NS_PER_SEC);
  if NanoPart < 0 then
  begin
    Dec(WholeSec);
    Inc(NanoPart, Int32(NS_PER_SEC));
  end;
  T := WholeSec;
  libc_gmtime_r(@T, @Tm);
  Year  := Tm.Year + 1900;
  Month := Tm.Mon  + 1;
  Day   := Tm.MDay;
  Hour  := Tm.Hour;
  Min   := Tm.Min;
  Sec   := Tm.Sec;
  NSec  := NanoPart;
end;

function TRtlPlatformPosix.TimeJoin(Year, Month, Day,
  Hour, Min, Sec, NSec: Int32): Int64;
var
  Tm:    TTm;
  Epoch: Int64;
  I:     Int;
  TB:    PChar;
begin
  TB := PChar(@Tm);
  for I := 0 to SizeOf(TTm) - 1 do TB[I] := #0;
  Tm.Year  := Year  - 1900;
  Tm.Mon   := Month - 1;
  Tm.MDay  := Day;
  Tm.Hour  := Hour;
  Tm.Min   := Min;
  Tm.Sec   := Sec;
  Epoch := libc_timegm(@Tm);
  Result := Epoch * NS_PER_SEC + Int64(NSec);
end;

function TRtlPlatformPosix.TimeIsLeapYear(Year: Int32): Int32;
begin
  if ((Year mod 4 = 0) and ((Year mod 100 <> 0) or (Year mod 400 = 0))) then
    Result := 1
  else
    Result := 0;
end;

function TRtlPlatformPosix.TimeDaysInMonth(Year, Month: Int32): Int32;
const
  Days: array[1..12] of Int32 = (31,28,31,30,31,30,31,31,30,31,30,31);
begin
  if (Month = 2) and (Self.TimeIsLeapYear(Year) = 1) then
    Result := 29
  else
    Result := Days[Month];
end;

{ ================================================================== }
{ TRtlPlatformPosix — Process management                              }
{ ================================================================== }

function TRtlPlatformPosix.ProcessCreate: Pointer;
var
  P:    PBlaiseProcess;
  PB:   PChar;
  I:    Int;
begin
  P := _BlaiseGetMem(SizeOf(TBlaiseProcess));
  if P = nil then begin Result := nil; Exit end;
  PB := PChar(P);
  for I := 0 to SizeOf(TBlaiseProcess) - 1 do
    PB[I] := #0;
  P^.PipeFd := -1;
  Result := P;
end;

procedure TRtlPlatformPosix.ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
var
  P: PBlaiseProcess;
begin
  P := Proc;
  if P^.Exe <> nil then _BlaiseFreeMem(P^.Exe);
  P^.Exe := StrDup(StrData(ExeStr));
end;

procedure TRtlPlatformPosix.ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
var
  P:       PBlaiseProcess;
  NewCap:  Int;
  NewArgv: TPCharArray;
  I:       Int;
begin
  P := Proc;
  if P^.ArgC + 2 >= P^.ArgVCap then
  begin
    if P^.ArgVCap = 0 then NewCap := 8 else NewCap := P^.ArgVCap * 2;
    NewArgv := _BlaiseGetMem(NewCap * SizeOf(Pointer));
    if NewArgv = nil then Exit;
    for I := 0 to P^.ArgC - 1 do
      ArgvSet(NewArgv, I, ArgvGet(P^.Argv, I));
    if P^.Argv <> nil then _BlaiseFreeMem(P^.Argv);
    P^.Argv    := NewArgv;
    P^.ArgVCap := NewCap;
  end;
  ArgvSet(P^.Argv, P^.ArgC, StrDup(StrData(ArgStr)));
  Inc(P^.ArgC);
end;

procedure TRtlPlatformPosix.ProcessExecute(Proc: Pointer);
var
  P:     PBlaiseProcess;
  Fds:   array[0..1] of Int32;
  Total: Int;
  Argv:  TPCharArray;
  I:     Int;
  Pid:   Int;
begin
  P := Proc;
  Fds[0] := -1;
  Fds[1] := -1;
  if libc_pipe(@Fds[0]) < 0 then Exit;

  Total := P^.ArgC + 2;
  Argv  := _BlaiseGetMem(Total * SizeOf(Pointer));
  if Argv = nil then begin libc_close(Fds[0]); libc_close(Fds[1]); Exit end;
  if P^.Exe <> nil then ArgvSet(Argv, 0, P^.Exe)
  else ArgvSet(Argv, 0, nil);
  for I := 0 to P^.ArgC - 1 do
    ArgvSet(Argv, I + 1, ArgvGet(P^.Argv, I));
  ArgvSet(Argv, Total - 1, nil);

  Pid := libc_fork();
  if Pid < 0 then
  begin
    _BlaiseFreeMem(Argv);
    libc_close(Fds[0]);
    libc_close(Fds[1]);
    Exit;
  end;

  if Pid = 0 then
  begin
    libc_close(Fds[0]);
    libc_dup2(Fds[1], 1);
    libc_dup2(Fds[1], 2);
    libc_close(Fds[1]);
    libc_execvp(ArgvGet(Argv, 0), Argv);
    libc__exit(127);
  end;

  _BlaiseFreeMem(Argv);
  libc_close(Fds[1]);
  P^.Pid    := Pid;
  P^.PipeFd := Fds[0];
  P^.Waited := 0;
end;

function TRtlPlatformPosix.ProcessRunning(Proc: Pointer): Int32;
var
  P:      PBlaiseProcess;
  Status: Int;
  R:      Int;
begin
  P := Proc;
  if (P^.Waited <> 0) or (P^.Pid = 0) then begin Result := 0; Exit end;
  Status := 0;
  R := libc_waitpid(P^.Pid, @Status, GPlatformLayout.WNOHANG());
  if R = P^.Pid then
  begin
    if (Status and $7F) = 0 then
      P^.ExitCode := (Status shr 8) and $FF
    else
      { killed by a signal: 128 + the signal number, as a shell reports it
        -- a bare 1 made a crash indistinguishable from an ordinary failure }
      P^.ExitCode := 128 + (Status and $7F);
    P^.Waited := 1;
    Result := 0;
  end else if R = 0 then
    Result := 1
  else
    Result := 0;
end;

function TRtlPlatformPosix.ProcessReadOutput(Proc: Pointer): Pointer;
var
  P:   PBlaiseProcess;
  Buf: array[0..4095] of Byte;
  N:   Int64;
  R:   PChar;
  I:   Int;
begin
  P := Proc;
  if P^.PipeFd < 0 then begin Result := StrAlloc(0); Exit end;
  N := libc_read(P^.PipeFd, @Buf[0], 4096);
  if N <= 0 then
  begin
    libc_close(P^.PipeFd);
    P^.PipeFd := -1;
    Exit(StrAlloc(0));
  end;
  R := StrAlloc(Int32(N));
  if R <> nil then
    for I := 0 to Int32(N) - 1 do R[I] := Chr(Buf[I]);
  Result := R;
end;

procedure TRtlPlatformPosix.ProcessWaitOnExit(Proc: Pointer);
var
  P:      PBlaiseProcess;
  Status: Int;
begin
  P := Proc;
  if (P^.Waited <> 0) or (P^.Pid = 0) then Exit;
  Status := 0;
  libc_waitpid(P^.Pid, @Status, 0);
  if (Status and $7F) = 0 then
    P^.ExitCode := (Status shr 8) and $FF
  else
    P^.ExitCode := 128 + (Status and $7F);   { a signal death, as above }
  P^.Waited := 1;
end;

function TRtlPlatformPosix.ProcessExitCode(Proc: Pointer): Int32;
begin
  Result := PBlaiseProcess(Proc)^.ExitCode;
end;

procedure TRtlPlatformPosix.ProcessFree(Proc: Pointer);
var
  P:    PBlaiseProcess;
  I:    Int;
  Slot: PChar;
begin
  P := Proc;
  if P = nil then Exit;
  if P^.PipeFd >= 0 then libc_close(P^.PipeFd);
  if P^.Exe <> nil then _BlaiseFreeMem(P^.Exe);
  if P^.Argv <> nil then
  begin
    for I := 0 to P^.ArgC - 1 do
    begin
      Slot := ArgvGet(P^.Argv, I);
      if Slot <> nil then _BlaiseFreeMem(Slot);
    end;
    _BlaiseFreeMem(P^.Argv);
  end;
  _BlaiseFreeMem(P);
end;

{ ================================================================== }
{ TRtlPlatformPosix — child processes with three pipes (IO.Process)   }
{ ================================================================== }

{ The child between fork and exec calls only async-signal-safe routines, on
  data prepared before the fork, so starting a process from a
  multi-threaded program is safe. }

const
  { The same numbers on Linux, FreeBSD and macOS. }
  SPAWN_ENOENT = 2;
  SPAWN_EIO = 5;
  SPAWN_EACCES = 13;
  SPAWN_ENOTDIR = 20;
  SPAWN_SIGKILL = 9;
  SPAWN_SIGPIPE = 13;
  SPAWN_SIGTERM = 15;
  SPAWN_F_SETFD = 2;
  SPAWN_FD_CLOEXEC = 1;
  SPAWN_POLLIN = $0001;
  SPAWN_POLLERR = $0008;
  SPAWN_POLLHUP = $0010;
  SPAWN_POLLNVAL = $0020;
  SPAWN_POLLFD_SIZE = 8;

type
  PSpawnInt32 = ^Int32;
  PSpawnInt16 = ^Int16;
  PSpawnInt64 = ^Int64;

{ The errno of a call that failed with result R, in either profile. }
function SpawnErrno(R: Int64): Int32;
begin
  Result := Int32(errno_GetOsErrno());
  if (Result = 0) and (R < 0) then
    Result := Int32(-R);
  if Result = 0 then
    Result := SPAWN_EIO;
end;

{ A nil-terminated array of C strings, one per #0-ended item of the ALen
  bytes at AText, in one heap block -- the pointers, then a copy of the
  text -- which one _BlaiseFreeMem frees. }
function ZListBlock(AText: PChar; ALen: Int): TPCharArray;
var
  N, I, K, Start: Int;
  Text: PChar;
begin
  N := 0;
  for I := 0 to ALen - 1 do
    if AText[I] = #0 then
      N := N + 1;
  Result := _BlaiseGetMem((N + 1) * SizeOf(Pointer) + ALen + 1);
  if Result = nil then
    Exit;
  Text := PChar(Pointer(Result) + (N + 1) * SizeOf(Pointer));
  for I := 0 to ALen - 1 do
    Text[I] := AText[I];
  Text[ALen] := #0;
  K := 0;
  Start := 0;
  for I := 0 to ALen - 1 do
    if Text[I] = #0 then
    begin
      ArgvSet(Result, K, Text + Start);
      K := K + 1;
      Start := I + 1;
    end;
  ArgvSet(Result, N, nil);
end;

{ The paths execve tries in turn for program AExe under the environment
  AEnv (#0-ended NAME=VALUE entries), as execvp searches: AExe itself when
  it holds a '/', else AExe in each directory of AEnv's PATH (/usr/bin:/bin
  when it has none; an empty entry is the current directory).  A block as
  ZListBlock makes. }
function ExecCandidates(AExe: PChar; AExeLen: Int; AEnv: PChar;
  AEnvLen: Int): TPCharArray;
const
  DEFAULT_PATH = '/usr/bin:/bin';
var
  Def: string;
  PathP, Text: PChar;
  PathLen, I, J, Start, Dirs, W: Int;
  HasSlash, Found: Boolean;
begin
  HasSlash := False;
  for I := 0 to AExeLen - 1 do
    if AExe[I] = '/' then
      HasSlash := True;
  if HasSlash then
    Exit(ZListBlock(AExe, AExeLen + 1));
  Def := DEFAULT_PATH;
  PathP := StrData(Pointer(Def));
  PathLen := StrLen(Pointer(Def));
  Found := False;
  Start := 0;
  for I := 0 to AEnvLen - 1 do
    if AEnv[I] = #0 then
    begin
      if (not Found) and (I - Start >= 5) and (AEnv[Start] = 'P') and
         (AEnv[Start + 1] = 'A') and (AEnv[Start + 2] = 'T') and
         (AEnv[Start + 3] = 'H') and (AEnv[Start + 4] = '=') then
      begin
        PathP := AEnv + Start + 5;
        PathLen := I - Start - 5;
        Found := True;
      end;
      Start := I + 1;
    end;
  Dirs := 1;
  for I := 0 to PathLen - 1 do
    if PathP[I] = ':' then
      Dirs := Dirs + 1;
  { each candidate: the directory (or '.'), '/', the name and its #0 }
  Text := _BlaiseGetMem(PathLen + Dirs * (AExeLen + 3));
  if Text = nil then
    Exit(nil);
  W := 0;
  Start := 0;
  for I := 0 to PathLen do
    if (I = PathLen) or (PathP[I] = ':') then
    begin
      if I = Start then
      begin
        Text[W] := '.';
        W := W + 1;
      end;
      for J := Start to I - 1 do
      begin
        Text[W] := PathP[J];
        W := W + 1;
      end;
      Text[W] := '/';
      W := W + 1;
      for J := 0 to AExeLen - 1 do
      begin
        Text[W] := AExe[J];
        W := W + 1;
      end;
      Text[W] := #0;
      W := W + 1;
      Start := I + 1;
    end;
  Result := ZListBlock(Text, W);
  _BlaiseFreeMem(Text);
end;

{ The child between fork and exec.  Never returns.  With AEnvp nil the
  child keeps the parent's environment and execvp searches the parent's
  PATH; otherwise AEnvp is its whole environment and APaths the candidate
  paths, tried in turn as execvp would: a missing file goes on to the next,
  a permission error is remembered, anything else stops the search.  A
  failure's errno goes to the parent through the AStatus pipe. }
procedure SpawnChild(AStdin, AStdout, AStderr, AStatus: Int32;
  ACwd: PChar; AArgv, AEnvp, APaths: TPCharArray);
var
  E, R, Saved: Int32;
  I: Int;
  Cand: PChar;
begin
  libc_dup2(AStdin, 0);
  libc_dup2(AStdout, 1);
  libc_dup2(AStderr, 2);
  R := 0;
  if ACwd <> nil then
    R := libc_chdir(ACwd);
  if R <> 0 then
  begin
    E := SpawnErrno(R);
    libc_write(AStatus, @E, 4);
    libc__exit(127);
  end;
  if AEnvp = nil then
  begin
    R := libc_execvp(ArgvGet(AArgv, 0), AArgv);
    E := SpawnErrno(R);
  end
  else
  begin
    Saved := SPAWN_ENOENT;
    I := 0;
    while APaths <> nil do
    begin
      Cand := ArgvGet(APaths, I);
      if Cand = nil then
        Break;
      R := libc_execve(Cand, AArgv, AEnvp);
      E := SpawnErrno(R);
      if E = SPAWN_EACCES then
        Saved := SPAWN_EACCES
      else if (E <> SPAWN_ENOENT) and (E <> SPAWN_ENOTDIR) then
      begin
        Saved := E;
        Break;
      end;
      I := I + 1;
    end;
    E := Saved;
  end;
  libc_write(AStatus, @E, 4);
  libc__exit(127);
end;

{ Pipes holds the read and write ends of the child's stdin, stdout, stderr
  and the status pipe, in that order.  The parent's ends, and both ends of
  the status pipe, are close-on-exec: a stdin write end leaked into another
  child would keep this one from ever seeing the end of its input, and
  end-of-file on the status pipe is how the parent learns exec succeeded. }
function TRtlPlatformPosix.ProcSpawn(const AExe, AArgs, AEnv, ACwd: string;
  AUseEnv: Int32; AFds, AChild: Pointer): Int32;
var
  Pipes: array[0..7] of Int32;
  I, Opened, ExeLen, ArgsLen, EnvLen: Int;
  ExeP, ArgsP, EnvData, ArgText, CwdP: PChar;
  Argv, Envp, Paths: TPCharArray;
  Pid, E, R, Status: Int32;
  N: Int64;
begin
  { a write to the stdin of a child that has gone must fail, not kill us }
  libc_signal(SPAWN_SIGPIPE, Pointer(1));
  Opened := 0;
  while Opened < 4 do
  begin
    R := libc_pipe(@Pipes[Opened * 2]);
    if R <> 0 then
    begin
      E := SpawnErrno(R);
      for I := 0 to Opened * 2 - 1 do
        libc_close(Pipes[I]);
      Exit(E);
    end;
    Opened := Opened + 1;
  end;
  libc_fcntl(Pipes[1], SPAWN_F_SETFD, SPAWN_FD_CLOEXEC);
  libc_fcntl(Pipes[2], SPAWN_F_SETFD, SPAWN_FD_CLOEXEC);
  libc_fcntl(Pipes[4], SPAWN_F_SETFD, SPAWN_FD_CLOEXEC);
  libc_fcntl(Pipes[6], SPAWN_F_SETFD, SPAWN_FD_CLOEXEC);
  libc_fcntl(Pipes[7], SPAWN_F_SETFD, SPAWN_FD_CLOEXEC);

  ExeP := StrData(Pointer(AExe));
  ExeLen := StrLen(Pointer(AExe));
  ArgsP := StrData(Pointer(AArgs));
  ArgsLen := StrLen(Pointer(AArgs));
  ArgText := _BlaiseGetMem(ExeLen + 1 + ArgsLen + 1);
  for I := 0 to ExeLen - 1 do
    ArgText[I] := ExeP[I];
  ArgText[ExeLen] := #0;
  for I := 0 to ArgsLen - 1 do
    ArgText[ExeLen + 1 + I] := ArgsP[I];
  Argv := ZListBlock(ArgText, ExeLen + 1 + ArgsLen);
  _BlaiseFreeMem(ArgText);
  CwdP := nil;
  if StrLen(Pointer(ACwd)) > 0 then
    CwdP := StrDup(StrData(Pointer(ACwd)));
  Envp := nil;
  Paths := nil;
  if AUseEnv <> 0 then
  begin
    EnvData := StrData(Pointer(AEnv));
    EnvLen := StrLen(Pointer(AEnv));
    Envp := ZListBlock(EnvData, EnvLen);
    Paths := ExecCandidates(ExeP, ExeLen, EnvData, EnvLen);
  end;

  Pid := libc_fork();
  if Pid = 0 then
    SpawnChild(Pipes[0], Pipes[3], Pipes[5], Pipes[7], CwdP, Argv, Envp,
      Paths);
  E := 0;
  if Pid < 0 then
    E := SpawnErrno(Pid);
  libc_close(Pipes[0]);
  libc_close(Pipes[3]);
  libc_close(Pipes[5]);
  libc_close(Pipes[7]);
  _BlaiseFreeMem(Argv);
  if CwdP <> nil then
    _BlaiseFreeMem(CwdP);
  if Envp <> nil then
    _BlaiseFreeMem(Envp);
  if Paths <> nil then
    _BlaiseFreeMem(Paths);
  if Pid > 0 then
  begin
    { four bytes on the status pipe are the errno of a failed chdir or
      exec; the end of it means exec succeeded }
    repeat
      N := libc_read(Pipes[6], @E, 4);
    until not errno_Interrupted(N);
    if N <> 4 then
      E := 0
    else
      libc_waitpid(Pid, @Status, 0);
  end;
  libc_close(Pipes[6]);
  if E <> 0 then
  begin
    libc_close(Pipes[1]);
    libc_close(Pipes[2]);
    libc_close(Pipes[4]);
    Exit(E);
  end;
  PSpawnInt32(AFds)^ := Pipes[1];
  PSpawnInt32(AFds + 4)^ := Pipes[2];
  PSpawnInt32(AFds + 8)^ := Pipes[4];
  PSpawnInt64(AChild)^ := Pid;
  Result := 0;
end;

function TRtlPlatformPosix.ProcWait(AChild: Int64; ABlock: Int32;
  AExitCode: Pointer): Int32;
var
  Status, R, Options: Int32;
begin
  Options := GPlatformLayout.WNOHANG();
  if ABlock <> 0 then
    Options := 0;
  repeat
    Status := 0;
    R := libc_waitpid(Int32(AChild), @Status, Options);
  until (R >= 0) or not errno_Interrupted(R);
  if R = 0 then
    Exit(0);
  if R <> Int32(AChild) then
    Exit(-1);
  if (Status and $7F) = 0 then
    PSpawnInt32(AExitCode)^ := (Status shr 8) and $FF
  else
    PSpawnInt32(AExitCode)^ := 128 + (Status and $7F);
  Result := 1;
end;

function TRtlPlatformPosix.ProcSignal(AChild: Int64; AForce: Int32): Int32;
begin
  if AForce <> 0 then
    Result := libc_kill(Int32(AChild), SPAWN_SIGKILL)
  else
    Result := libc_kill(Int32(AChild), SPAWN_SIGTERM);
end;

function TRtlPlatformPosix.ProcPid(AChild: Int64): Int32;
begin
  Result := Int32(AChild);
end;

{ A process id holds nothing to let go of. }
procedure TRtlPlatformPosix.ProcRelease(AChild: Int64);
begin
end;

function TRtlPlatformPosix.ProcPollRead(AFds: Pointer; ACount,
  ATimeoutMs: Int32; AReady: Pointer): Int32;
var
  Pfds: Pointer;
  I: Int;
  Ev: Int16;
begin
  Pfds := _BlaiseGetMem(Int64(ACount) * SPAWN_POLLFD_SIZE + SPAWN_POLLFD_SIZE);
  if Pfds = nil then
    Exit(-1);
  for I := 0 to ACount - 1 do
  begin
    PSpawnInt32(Pfds + I * SPAWN_POLLFD_SIZE)^ := PSpawnInt32(AFds + I * 4)^;
    PSpawnInt16(Pfds + I * SPAWN_POLLFD_SIZE + 4)^ := SPAWN_POLLIN;
    PSpawnInt16(Pfds + I * SPAWN_POLLFD_SIZE + 6)^ := 0;
  end;
  Result := libc_poll(Pfds, ACount, ATimeoutMs);
  if Result < 0 then
    Result := -1;
  for I := 0 to ACount - 1 do
  begin
    Ev := PSpawnInt16(Pfds + I * SPAWN_POLLFD_SIZE + 6)^;
    if (Result > 0) and ((Ev and (SPAWN_POLLIN or SPAWN_POLLERR or
       SPAWN_POLLHUP or SPAWN_POLLNVAL)) <> 0) then
      PSpawnInt32(AReady + I * 4)^ := 1
    else
      PSpawnInt32(AReady + I * 4)^ := 0;
  end;
  _BlaiseFreeMem(Pfds);
end;

{ ================================================================== }
{ Underscore ABI stubs                                                 }
{ ================================================================== }

procedure _SetArgs(Argc: Int32; Argv: Pointer);
begin
  GArgC := Argc;
  GArgV := TPCharArray(Argv);
  { GPlatformLayout is assigned by the target's concrete layout unit
    (rtl.platform.layout.<os>).  The current codegen calls that unit's init
    directly from main (by-name, for the compile-time --target); this weak
    _BlaisePlatformInit call is the bootstrap fallback for an older codegen that
    does not.  Idempotent.  This shared POSIX unit references no concrete layout
    class, so it stays OS-agnostic. }
  _BlaisePlatformInit();
  if GRtlPlatform = nil then
    GRtlPlatform := TRtlPlatformPosix.Create();
end;

function _EnvVector: Pointer;
begin
  if Pointer(GArgV) = nil then
    Exit(nil);
  Result := Pointer(UInt(Pointer(GArgV)) + UInt((GArgC + 1) * SizeOf(Pointer)));
end;

function _StatMtimeNsec(Buf: Pointer): Int64; external name '_StatMtimeNsec';

function _PathStat(const Path: string; FollowLinks: Int32; AOut: Pointer): Int64;
var
  St: TStatBuf;
  Mode, Fmt, Kind: Int32;
  PI: ^Int32;
  PL: ^Int64;
begin
  if FollowLinks <> 0 then
    Result := libc_stat(StrData(Pointer(Path)), @St)
  else
    Result := libc_lstat(StrData(Pointer(Path)), @St);
  if Result <> 0 then
    Exit;
  Mode := GPlatformLayout.StatMode(@St);
  Fmt := Mode and GPlatformLayout.S_IFMT();
  if Fmt = GPlatformLayout.S_IFREG() then
    Kind := 1
  else if Fmt = GPlatformLayout.S_IFDIR() then
    Kind := 2
  else if Fmt = GPlatformLayout.S_IFLNK() then
    Kind := 3
  else
    Kind := 4;
  PI := AOut;
  PI^ := Kind;
  PI := Pointer(PChar(AOut) + 4);
  PI^ := Mode and $FFF;
  PL := Pointer(PChar(AOut) + 8);
  PL^ := GPlatformLayout.StatSize(@St);
  PL := Pointer(PChar(AOut) + 16);
  PL^ := GPlatformLayout.StatMtime(@St);
  PL := Pointer(PChar(AOut) + 24);
  PL^ := _StatMtimeNsec(@St);
end;

procedure _SysWritePChar(Fd: Int32; P: PChar);
var
  Len: Int;
begin
  if P = nil then Exit;
  Len := Int32(libc_strlen(P));
  if Len > 0 then
    WriteAllToFd(Fd, P, Len);
end;

initialization
  if GRtlPlatform = nil then
    GRtlPlatform := TRtlPlatformPosix.Create();

end.
