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
    function ForceDirectories(const APath: string): Boolean; override;
    function RemoveDir(const APath: string): Boolean; override;
    function GetCurrentDir: string; override;
    function SetCurrentDir(const APath: string): Boolean; override;
    function ListDir(const APath: string): string; override;

    { OS utilities }
    function GetTempDir: string; override;
    function GetTempFileName(const ADir, APrefix: string): string; override;
    function GetProcessID: Integer; override;
    function GetEnvVar(const AName: string): string; override;
    procedure Sleep(AMilliseconds: Integer); override;
    procedure Halt(AExitCode: Integer); override;

    { Process }
    function Exec(const ACmd: string): Integer; override;
    function ParamCount: Integer; override;
    function ParamStr(AIndex: Integer): string; override;

    { Console I/O }
    procedure SysWriteStr(Fd: Integer; S: Pointer); override;
    procedure SysWriteInt(Fd: Integer; N: Integer); override;
    procedure SysWriteInt64(Fd: Integer; N: Int64); override;
    procedure SysWriteUInt64(Fd: Integer; N: UInt64); override;
    procedure SysWriteDouble(Fd: Integer; V: Double); override;
    procedure SysWriteSingle(Fd: Integer; V: Single); override;
    procedure SysWriteBool(Fd: Integer; B: Boolean); override;
    procedure SysWriteNewline(Fd: Integer); override;

    { File-descriptor primitives }
    function FdOpenRead(Path: Pointer): Integer; override;
    function FdOpenWrite(Path: Pointer): Integer; override;
    function FdOpenAppend(Path: Pointer): Integer; override;
    function FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer; override;
    function FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer; override;
    function FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64; override;
    function FdSize(Fd: Integer): Int64; override;
    procedure FdClose(Fd: Integer); override;

    { Date/Time }
    function TimeNow: Int64; override;
    function TimeLocalOffsetSecs: Integer; override;
    procedure TimeSplit(Nanos: Int64;
      out Year, Month, Day, Hour, Min, Sec, NSec: Integer); override;
    function TimeJoin(Year, Month, Day,
      Hour, Min, Sec, NSec: Integer): Int64; override;
    function TimeIsLeapYear(Year: Integer): Integer; override;
    function TimeDaysInMonth(Year, Month: Integer): Integer; override;

    { Process management }
    function ProcessCreate: Pointer; override;
    procedure ProcessSetExe(Proc: Pointer; ExeStr: Pointer); override;
    procedure ProcessAddArg(Proc: Pointer; ArgStr: Pointer); override;
    procedure ProcessExecute(Proc: Pointer); override;
    function ProcessRunning(Proc: Pointer): Integer; override;
    function ProcessReadOutput(Proc: Pointer): Pointer; override;
    procedure ProcessWaitOnExit(Proc: Pointer); override;
    function ProcessExitCode(Proc: Pointer): Integer; override;
    procedure ProcessFree(Proc: Pointer); override;
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
    Sec:     Integer;
    Min:     Integer;
    Hour:    Integer;
    MDay:    Integer;
    Mon:     Integer;
    Year:    Integer;
    WDay:    Integer;
    YDay:    Integer;
    IsDST:   Integer;
    GmtOff:  Int64;
    Zone:    Pointer;
  end;
  PTm = ^TTm;

  TPCharArray = ^PChar;

{ Memory }
function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);          external name '_BlaiseFreeMem';
{ Bootstrap fallback for GPlatformLayout: defined WEAK by the linked target's
  concrete layout unit (rtl.platform.layout.<os>).  The current codegen assigns
  GPlatformLayout by calling that unit's init directly from main, so this call
  is redundant then (idempotent).  It only matters for a binary built by an
  older codegen that does not yet emit the direct main-call — there it is the
  sole path that initialises the layout. }
procedure _BlaisePlatformInit;                    external name '_BlaisePlatformInit';

{ String ARC }
function  _IntToStr(N: Integer): Pointer;   external name '_IntToStr';
function  _Int64ToStr(N: Int64): Pointer;   external name '_Int64ToStr';
function  _UInt64ToStr(N: UInt64): Pointer; external name '_UInt64ToStr';
function  _DoubleToStr(V: Double): Pointer; external name '_DoubleToStr';
function  _SingleToStr(V: Single): Pointer; external name '_SingleToStr';
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
function  libc_open(Path: PChar; Flags: Integer): Integer; varargs;       external name 'open';
function  libc_open2(Path: PChar; Flags: Integer): Integer;                 external name 'open';
function  libc_read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;        external name 'read';
function  libc_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64;       external name 'write';
function  libc_lseek(Fd: Integer; Offset: Int64; Whence: Integer): Int64;   external name 'lseek';
function  libc_close(Fd: Integer): Integer;                                  external name 'close';
function  libc_fstat(Fd: Integer; Buf: Pointer): Integer;                   external name 'fstat';
function  libc_stat(Path: PChar; Buf: Pointer): Integer;                    external name 'stat';
function  libc_mkdir(Path: PChar; Mode: Integer): Integer;                   external name 'mkdir';
function  libc_rmdir(Path: PChar): Integer;                                  external name 'rmdir';
function  libc_unlink(Path: PChar): Integer;                                 external name 'unlink';
function  libc_rename(OldPath, NewPath: PChar): Integer;                     external name 'rename';
function  libc_getcwd(Buf: PChar; Size: Int64): PChar;                       external name 'getcwd';
{ getdirentries(3) is the one directory-reading spelling libc provides on all
  three POSIX targets (glibc >= 2.2.5, FreeBSD, macOS); the freestanding
  syscall leaves define the same symbol, so this single binding serves the
  libc and --static paths alike.  Returns bytes written into Buf, 0 at end of
  directory, negative on error. }
function  libc_getdirentries(Fd: Integer; Buf: Pointer; NBytes: Int64;
                             Basep: Pointer): Int64;                          external name 'getdirentries';
function  libc_chdir(Path: PChar): Integer;                                  external name 'chdir';
function  libc_getenv(Name: PChar): PChar;                                   external name 'getenv';
function  libc_mkstemp(Template: PChar): Integer;                            external name 'mkstemp';
function  libc_nanosleep(Req: Pointer; Rem: Pointer): Integer;               external name 'nanosleep';
function  libc_getpid: Integer;                                               external name 'getpid';
function  libc_system(Cmd: PChar): Integer;                                  external name 'system';
procedure libc_exit(Code: Integer);                                          external name 'exit';
function  libc_strlen(S: PChar): Int64;                                      external name 'strlen';

{ POSIX libc — date/time }
function  libc_clock_gettime(ClockId: Integer; Ts: Pointer): Integer; external name 'clock_gettime';
function  libc_time(T: Pointer): Int64;                                external name 'time';
function  libc_localtime_r(T: Pointer; Tm: PTm): PTm;                 external name 'localtime_r';
function  libc_gmtime_r(T: Pointer; Tm: PTm): PTm;                    external name 'gmtime_r';
function  libc_timegm(Tm: PTm): Int64;                                 external name 'timegm';

{ POSIX libc — process management }
function  libc_fork: Integer;                              external name 'fork';
function  libc_execvp(File_: PChar; Argv: Pointer): Integer; external name 'execvp';
procedure libc__exit(Code: Integer);                       external name '_exit';
function  libc_waitpid(Pid: Integer; Status: Pointer; Options: Integer): Integer; external name 'waitpid';
function  libc_pipe(Fds: Pointer): Integer;                external name 'pipe';
function  libc_dup2(OldFd, NewFd: Integer): Integer;       external name 'dup2';

{ ------------------------------------------------------------------ }
{ Underscore ABI stubs                                                 }
{ ------------------------------------------------------------------ }

{ argc/argv — _SetArgs is called before GRtlPlatform is initialised,
  so it stores directly into module globals rather than delegating. }
procedure _SetArgs(Argc: Integer; Argv: Pointer);
function  _ParamCount: Integer;
function  _ParamStr(Index: Integer): Pointer;

{ File operations }
function  _FileExists(Path: Pointer): Integer;
procedure _DeleteFile(Path: Pointer);
function  _RenameFile(OldPath, NewPath: Pointer): Integer;
function  _ReadFile(Path: Pointer): Pointer;
procedure _WriteFile(Path, Content: Pointer);
procedure _AppendFile(Path, Content: Pointer);
function  _FileAge(Path: Pointer): Int64;

{ Directory operations }
function  _DirectoryExists(Path: Pointer): Integer;
function  _ForceDirectories(Path: Pointer): Integer;
procedure _RemoveDir(Path: Pointer);
function  _GetCurrentDir: Pointer;
function  _SetCurrentDir(Path: Pointer): Integer;
function  _ListDir(Path: Pointer): Pointer;

{ OS utilities }
function  _GetTempDir: Pointer;
function  _GetTempFileName(Dir, Prefix: Pointer): Pointer;
function  _GetProcessID: Integer;
function  _GetEnvVar(Name: Pointer): Pointer;
procedure _Sleep(Ms: Integer);
procedure _Halt(Code: Integer);
function  _Exec(Cmd: Pointer): Integer;

{ Console I/O }
procedure _SysWriteStr(Fd: Integer; S: Pointer);
procedure _SysWriteInt(Fd: Integer; N: Integer);
procedure _SysWriteInt64(Fd: Integer; N: Int64);
procedure _SysWriteUInt64(Fd: Integer; N: UInt64);
procedure _SysWriteDouble(Fd: Integer; V: Double);
procedure _SysWriteSingle(Fd: Integer; V: Single);
procedure _SysWriteBool(Fd: Integer; B: Boolean);
procedure _SysWriteNewline(Fd: Integer);

{ File-descriptor primitives }
function  _FdOpenRead(Path: Pointer): Integer;
function  _FdOpenWrite(Path: Pointer): Integer;
function  _FdOpenAppend(Path: Pointer): Integer;
function  _FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
function  _FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
function  _FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64;
function  _FdSize(Fd: Integer): Int64;
procedure _FdClose(Fd: Integer);

{ Date/Time }
function  _TimeNow: Int64;
function  _TimeLocalOffsetSecs: Integer;
procedure _TimeSplit(Nanos: Int64;
  out Year, Month, Day, Hour, Min, Sec, NSec: Integer);
function  _TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec: Integer): Int64;
function  _TimeIsLeapYear(Year: Integer): Integer;
function  _TimeDaysInMonth(Year, Month: Integer): Integer;

{ Process management }
function  _ProcessCreate: Pointer;
procedure _ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
procedure _ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
procedure _ProcessExecute(Proc: Pointer);
function  _ProcessRunning(Proc: Pointer): Integer;
function  _ProcessReadOutput(Proc: Pointer): Pointer;
procedure _ProcessWaitOnExit(Proc: Pointer);
function  _ProcessExitCode(Proc: Pointer): Integer;
procedure _ProcessFree(Proc: Pointer);

implementation

{ ------------------------------------------------------------------ }
{ Constants                                                            }
{ ------------------------------------------------------------------ }

const
  BLAISE_STR_HDR = 12;

  NS_PER_SEC = 1000000000;

  { O_* / S_* / SEEK_* / CLOCK_REALTIME / WNOHANG and the struct stat layout
    live in GPlatformLayout (rtl.platform.layout.<os>) — their values/offsets
    differ across POSIX targets.  See docs/native-target-architecture.adoc. }

{ ------------------------------------------------------------------ }
{ Shared string helpers                                                }
{ ------------------------------------------------------------------ }

function StrAlloc(Len: Integer): Pointer;
var
  Base:       PChar;
  RC, LN, CP: ^Integer;
  NulPtr:     PChar;
begin
  Base := _BlaiseGetMem(BLAISE_STR_HDR + Len + 1);
  if Base = nil then begin Result := nil; Exit end;
  RC  := Pointer(Base);      RC^ := 0;
  LN  := Pointer(Base + 4);  LN^ := Len;
  CP  := Pointer(Base + 8);  CP^ := Len;
  NulPtr := PChar(Base + BLAISE_STR_HDR);
  NulPtr[Len] := #0;
  Result := Base + BLAISE_STR_HDR;
end;

function StrFromCStr(S: PChar): Pointer;
var
  Len: Integer;
  R:   PChar;
  I:   Integer;
begin
  if S = nil then begin Result := StrAlloc(0); Exit end;
  Len := Integer(libc_strlen(S));
  R := StrAlloc(Len);
  if (R <> nil) and (Len > 0) then
    for I := 0 to Len - 1 do R[I] := S[I];
  Result := R;
end;

function StrLen(DataPtr: Pointer): Integer;
var
  LPtr: ^Integer;
begin
  if DataPtr = nil then begin Result := 0; Exit end;
  LPtr := Pointer(PChar(DataPtr) - 8);
  Result := LPtr^;
end;

function StrData(DataPtr: Pointer): PChar;
begin
  if DataPtr = nil then Result := nil else Result := PChar(DataPtr);
end;

function StrDup(S: PChar): PChar;
var
  Len: Integer;
  Buf: PChar;
  I:   Integer;
begin
  if S = nil then begin Result := nil; Exit end;
  Len := Integer(libc_strlen(S));
  Buf := _BlaiseGetMem(Len + 1);
  if Buf = nil then begin Result := nil; Exit end;
  for I := 0 to Len do Buf[I] := S[I];
  Result := Buf;
end;

procedure WriteAllToFd(Fd: Integer; Data: PChar; Len: Integer);
var
  P: PChar;
  Rem: Int64;
  Written: Int64;
begin
  P := Data;
  Rem := Int64(Len);
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
  GArgC: Integer;
  GArgV: TPCharArray;

function ArgvGet(Arr: TPCharArray; Index: Integer): PChar;
var
  Slot: TPCharArray;
begin
  Slot := Arr + (Index * SizeOf(Pointer));
  Result := Slot^;
end;

procedure ArgvSet(Arr: TPCharArray; Index: Integer; Val: Pointer);
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
    ArgC:     Integer;
    ArgVCap:  Integer;
    Pid:      Integer;
    PipeFd:   Integer;
    ExitCode: Integer;
    Waited:   Integer;
  end;
  PBlaiseProcess = ^TBlaiseProcess;

{ ================================================================== }
{ TRtlPlatformPosix — File operations                                 }
{ ================================================================== }

function TRtlPlatformPosix.FileExists(const APath: string): Boolean;
var
  Fd: Integer;
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
  Fd:   Integer;
  St:   TStatBuf;
  Sz:   Int64;
  R:    PChar;
  Got:  Int64;
  LPtr: ^Integer;
begin
  Fd := libc_open2(StrData(Pointer(APath)), GPlatformLayout.O_RDONLY());
  if Fd < 0 then begin Result := string(PChar(StrAlloc(0))); Exit end;
  if libc_fstat(Fd, @St) < 0 then begin libc_close(Fd); Result := string(PChar(StrAlloc(0))); Exit end;
  Sz := GPlatformLayout.StatSize(@St);
  if Sz < 0 then begin libc_close(Fd); Result := string(PChar(StrAlloc(0))); Exit end;
  R := StrAlloc(Integer(Sz));
  if R = nil then begin libc_close(Fd); Result := ''; Exit end;
  Got := libc_read(Fd, R, Sz);
  libc_close(Fd);
  LPtr  := Pointer(PChar(R) - 8);  LPtr^ := Integer(Got);
  LPtr  := Pointer(PChar(R) - 4);  LPtr^ := Integer(Got);
  R[Integer(Got)] := #0;
  Result := string(R);
end;

procedure TRtlPlatformPosix.WriteFile(const APath, AContent: string);
var
  Fd:  Integer;
  Len: Integer;
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
  Fd:  Integer;
  Len: Integer;
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

function TRtlPlatformPosix.ForceDirectories(const APath: string): Boolean;
var
  P:     PChar;
  Buf:   array[0..4095] of Byte;
  BufP:  PChar;
  Len:   Integer;
  I:     Integer;
  Saved: Byte;
  St:    TStatBuf;
begin
  P := StrData(Pointer(APath));
  if (P = nil) or (P[0] = #0) then begin Result := False; Exit end;
  Len := Integer(libc_strlen(P));
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
  Len:       Integer;
  NeedSlash: Integer;
  R:         PChar;
  I:         Integer;
begin
  CWD := libc_getcwd(PChar(@Buf[0]), 4096);
  if CWD = nil then begin Result := string(PChar(StrAlloc(0))); Exit end;
  Len := Integer(libc_strlen(CWD));
  if (Len > 0) and (CWD[Len - 1] <> '/') then NeedSlash := 1 else NeedSlash := 0;
  R := StrAlloc(Len + NeedSlash);
  if R = nil then begin Result := ''; Exit end;
  for I := 0 to Len - 1 do R[I] := CWD[I];
  if NeedSlash = 1 then R[Len] := '/';
  Result := string(R);
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
  Fd:       Integer;
  Got:      Int64;
  Pos:      Int64;
  Ent:      Pointer;
  RecLen:   Integer;
  Nm:       PChar;
  NmLen:    Integer;
  Total:    Integer;
  Count:    Integer;
  R:        PChar;
  W:        Integer;
  I:        Integer;
  Pass:     Integer;
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
        NmLen := Integer(libc_strlen(Nm));
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
    Result := string(R)
end;

{ ================================================================== }
{ TRtlPlatformPosix — OS utilities                                    }
{ ================================================================== }

function TRtlPlatformPosix.GetTempDir: string;
var
  Tmp:       PChar;
  Len:       Integer;
  NeedSlash: Integer;
  R:         PChar;
  I:         Integer;
begin
  Tmp := libc_getenv(StrData('TMPDIR'));
  if (Tmp = nil) or (Tmp[0] = #0) then Tmp := StrData('/tmp');
  Len := Integer(libc_strlen(Tmp));
  if (Len > 0) and (Tmp[Len - 1] <> '/') then NeedSlash := 1 else NeedSlash := 0;
  R := StrAlloc(Len + NeedSlash);
  if R = nil then begin Result := ''; Exit end;
  for I := 0 to Len - 1 do R[I] := Tmp[I];
  if NeedSlash = 1 then R[Len] := '/';
  Result := string(R);
end;

function TRtlPlatformPosix.GetTempFileName(const ADir, APrefix: string): string;
var
  DStr:      PChar;
  PStr:      PChar;
  DLen:      Integer;
  PLen:      Integer;
  NeedSlash: Integer;
  TmplLen:   Integer;
  Tmpl:      PChar;
  Tmp:       PChar;
  TmpLen:    Integer;
  Fd:        Integer;
  I:         Integer;
begin
  DStr := StrData(Pointer(ADir));
  PStr := StrData(Pointer(APrefix));
  if DStr = nil then DLen := 0 else DLen := Integer(libc_strlen(DStr));
  if PStr = nil then PLen := 0 else PLen := Integer(libc_strlen(PStr));

  if DLen = 0 then
  begin
    Tmp := libc_getenv(StrData('TMPDIR'));
    if (Tmp = nil) or (Tmp[0] = #0) then Tmp := StrData('/tmp');
    TmpLen := Integer(libc_strlen(Tmp));
    NeedSlash := 0;
    if (TmpLen > 0) and (Tmp[TmpLen - 1] <> '/') then NeedSlash := 1;
    TmplLen := TmpLen + NeedSlash + PLen + 6;
    Tmpl := _BlaiseGetMem(TmplLen + 1);
    if Tmpl = nil then begin Result := string(PChar(StrFromCStr(StrData('/tmp/blaise_XXXXXX')))); Exit end;
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
    if Tmpl = nil then begin Result := string(PChar(StrFromCStr(StrData('/tmp/blaise_XXXXXX')))); Exit end;
    for I := 0 to DLen - 1 do Tmpl[I] := DStr[I];
    if NeedSlash = 1 then Tmpl[DLen] := '/';
    for I := 0 to PLen - 1 do Tmpl[DLen + NeedSlash + I] := PStr[I];
    for I := 0 to 5 do Tmpl[DLen + NeedSlash + PLen + I] := 'X';
    Tmpl[TmplLen] := #0;
  end;

  Fd := libc_mkstemp(Tmpl);
  if Fd >= 0 then libc_close(Fd);
  Result := string(PChar(StrFromCStr(Tmpl)));
  _BlaiseFreeMem(Tmpl);
end;

function TRtlPlatformPosix.GetProcessID: Integer;
begin
  Result := libc_getpid();
end;

function TRtlPlatformPosix.GetEnvVar(const AName: string): string;
var
  Val: PChar;
begin
  Val := libc_getenv(StrData(Pointer(AName)));
  if Val = nil then begin Result := string(PChar(StrAlloc(0))); Exit end;
  Result := string(PChar(StrFromCStr(Val)));
end;

procedure TRtlPlatformPosix.Sleep(AMilliseconds: Integer);
var
  Ts: TTimeSpec;
begin
  Ts.Sec  := AMilliseconds div 1000;
  Ts.NSec := Int64(AMilliseconds mod 1000) * 1000000;
  libc_nanosleep(@Ts, nil);
end;

procedure TRtlPlatformPosix.Halt(AExitCode: Integer);
begin
  libc_exit(AExitCode);
end;

function TRtlPlatformPosix.Exec(const ACmd: string): Integer;
begin
  Result := libc_system(StrData(Pointer(ACmd)));
end;

function TRtlPlatformPosix.ParamCount: Integer;
begin
  if GArgC > 0 then
    Result := GArgC - 1
  else
    Result := 0;
end;

function TRtlPlatformPosix.ParamStr(AIndex: Integer): string;
var
  Slot: TPCharArray;
begin
  if (GArgV = nil) or (AIndex < 0) or (AIndex >= GArgC) then
    begin Result := string(PChar(StrAlloc(0))); Exit end;
  Slot := GArgV + (AIndex * SizeOf(Pointer));
  Result := string(PChar(StrFromCStr(Slot^)));
end;

{ ================================================================== }
{ TRtlPlatformPosix — Console I/O                                     }
{ ================================================================== }

procedure TRtlPlatformPosix.SysWriteStr(Fd: Integer; S: Pointer);
var
  LPtr: ^Integer;
  Len: Integer;
begin
  if S = nil then Exit;
  LPtr := S - 8;
  Len := LPtr^;
  if Len = 0 then Exit;
  WriteAllToFd(Fd, PChar(S), Len);
end;

procedure TRtlPlatformPosix.SysWriteNewline(Fd: Integer);
var
  NL: array[0..0] of Byte;
begin
  NL[0] := 10;
  WriteAllToFd(Fd, PChar(@NL[0]), 1);
end;

procedure TRtlPlatformPosix.SysWriteInt(Fd: Integer; N: Integer);
var
  S: Pointer;
  LPtr: ^Integer;
  Len: Integer;
begin
  S := _IntToStr(N);
  _StringAddRef(S);
  LPtr := S - 8;
  Len := LPtr^;
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteInt64(Fd: Integer; N: Int64);
var
  S: Pointer;
  LPtr: ^Integer;
  Len: Integer;
begin
  S := _Int64ToStr(N);
  _StringAddRef(S);
  LPtr := S - 8;
  Len := LPtr^;
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteUInt64(Fd: Integer; N: UInt64);
var
  S: Pointer;
  LPtr: ^Integer;
  Len: Integer;
begin
  S := _UInt64ToStr(N);
  _StringAddRef(S);
  LPtr := S - 8;
  Len := LPtr^;
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteDouble(Fd: Integer; V: Double);
var
  S: Pointer;
  LPtr: ^Integer;
  Len: Integer;
begin
  S := _DoubleToStr(V);
  _StringAddRef(S);
  LPtr := S - 8;
  Len := LPtr^;
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteSingle(Fd: Integer; V: Single);
var
  S: Pointer;
  LPtr: ^Integer;
  Len: Integer;
begin
  S := _SingleToStr(V);
  _StringAddRef(S);
  LPtr := S - 8;
  Len := LPtr^;
  WriteAllToFd(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure TRtlPlatformPosix.SysWriteBool(Fd: Integer; B: Boolean);
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

function TRtlPlatformPosix.FdOpenRead(Path: Pointer): Integer;
begin
  Result := libc_open2(StrData(Path), GPlatformLayout.O_RDONLY());
end;

function TRtlPlatformPosix.FdOpenWrite(Path: Pointer): Integer;
begin
  Result := libc_open(StrData(Path), GPlatformLayout.O_WRONLY() or GPlatformLayout.O_CREAT() or GPlatformLayout.O_TRUNC(), 420);
end;

function TRtlPlatformPosix.FdOpenAppend(Path: Pointer): Integer;
begin
  Result := libc_open(StrData(Path), GPlatformLayout.O_WRONLY() or GPlatformLayout.O_CREAT() or GPlatformLayout.O_APPEND(), 420);
end;

function TRtlPlatformPosix.FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
begin
  if (Fd < 0) or (Count <= 0) then begin Result := 0; Exit end;
  Result := Integer(libc_read(Fd, Buf, Int64(Count)));
end;

function TRtlPlatformPosix.FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
begin
  if (Fd < 0) or (Count <= 0) then begin Result := 0; Exit end;
  Result := Integer(libc_write(Fd, Buf, Int64(Count)));
end;

function TRtlPlatformPosix.FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64;
var
  Whence: Integer;
begin
  case Origin of
    1: Whence := GPlatformLayout.SEEK_CUR();
    2: Whence := GPlatformLayout.SEEK_END();
  else
    Whence := GPlatformLayout.SEEK_SET();
  end;
  Result := libc_lseek(Fd, Offset, Whence);
end;

function TRtlPlatformPosix.FdSize(Fd: Integer): Int64;
var
  St: TStatBuf;
begin
  if libc_fstat(Fd, @St) <> 0 then begin Result := -1; Exit end;
  Result := GPlatformLayout.StatSize(@St);
end;

procedure TRtlPlatformPosix.FdClose(Fd: Integer);
begin
  if Fd >= 0 then libc_close(Fd);
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

function TRtlPlatformPosix.TimeLocalOffsetSecs: Integer;
var
  T:  Int64;
  Lt: TTm;
begin
  T := libc_time(nil);
  libc_localtime_r(@T, @Lt);
  Result := Integer(Lt.GmtOff);
end;

procedure TRtlPlatformPosix.TimeSplit(Nanos: Int64;
  out Year, Month, Day, Hour, Min, Sec, NSec: Integer);
var
  WholeSec: Int64;
  NanoPart: Integer;
  T:        Int64;
  Tm:       TTm;
begin
  WholeSec := Nanos div NS_PER_SEC;
  NanoPart := Integer(Nanos mod NS_PER_SEC);
  if NanoPart < 0 then
  begin
    Dec(WholeSec);
    Inc(NanoPart, Integer(NS_PER_SEC));
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
  Hour, Min, Sec, NSec: Integer): Int64;
var
  Tm:    TTm;
  Epoch: Int64;
  I:     Integer;
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

function TRtlPlatformPosix.TimeIsLeapYear(Year: Integer): Integer;
begin
  if ((Year mod 4 = 0) and ((Year mod 100 <> 0) or (Year mod 400 = 0))) then
    Result := 1
  else
    Result := 0;
end;

function TRtlPlatformPosix.TimeDaysInMonth(Year, Month: Integer): Integer;
const
  Days: array[1..12] of Integer = (31,28,31,30,31,30,31,31,30,31,30,31);
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
  I:    Integer;
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
  NewCap:  Integer;
  NewArgv: TPCharArray;
  I:       Integer;
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
  Fds:   array[0..1] of Integer;
  Total: Integer;
  Argv:  TPCharArray;
  I:     Integer;
  Pid:   Integer;
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

function TRtlPlatformPosix.ProcessRunning(Proc: Pointer): Integer;
var
  P:      PBlaiseProcess;
  Status: Integer;
  R:      Integer;
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
      P^.ExitCode := 1;
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
  I:   Integer;
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
  R := StrAlloc(Integer(N));
  if R <> nil then
    for I := 0 to Integer(N) - 1 do R[I] := Chr(Buf[I]);
  Result := R;
end;

procedure TRtlPlatformPosix.ProcessWaitOnExit(Proc: Pointer);
var
  P:      PBlaiseProcess;
  Status: Integer;
begin
  P := Proc;
  if (P^.Waited <> 0) or (P^.Pid = 0) then Exit;
  Status := 0;
  libc_waitpid(P^.Pid, @Status, 0);
  if (Status and $7F) = 0 then
    P^.ExitCode := (Status shr 8) and $FF
  else
    P^.ExitCode := 1;
  P^.Waited := 1;
end;

function TRtlPlatformPosix.ProcessExitCode(Proc: Pointer): Integer;
begin
  Result := PBlaiseProcess(Proc)^.ExitCode;
end;

procedure TRtlPlatformPosix.ProcessFree(Proc: Pointer);
var
  P:    PBlaiseProcess;
  I:    Integer;
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
{ Underscore ABI stubs                                                 }
{ ================================================================== }

procedure _SetArgs(Argc: Integer; Argv: Pointer);
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

function _ParamCount: Integer;
begin
  Result := GRtlPlatform.ParamCount();
end;

function _ParamStr(Index: Integer): Pointer;
begin
  Result := Pointer(GRtlPlatform.ParamStr(Index));
end;

function _FileExists(Path: Pointer): Integer;
begin
  if GRtlPlatform.FileExists(string(PChar(Path))) then Result := 1 else Result := 0;
end;

procedure _DeleteFile(Path: Pointer);
begin
  GRtlPlatform.DeleteFile(string(PChar(Path)));
end;

function _RenameFile(OldPath, NewPath: Pointer): Integer;
begin
  if GRtlPlatform.RenameFile(string(PChar(OldPath)), string(PChar(NewPath))) then Result := 1 else Result := 0;
end;

function _ReadFile(Path: Pointer): Pointer;
begin
  Result := Pointer(GRtlPlatform.ReadFile(string(PChar(Path))));
end;

procedure _WriteFile(Path, Content: Pointer);
begin
  GRtlPlatform.WriteFile(string(PChar(Path)), string(PChar(Content)));
end;

procedure _AppendFile(Path, Content: Pointer);
begin
  GRtlPlatform.AppendFile(string(PChar(Path)), string(PChar(Content)));
end;

function _FileAge(Path: Pointer): Int64;
begin
  Result := GRtlPlatform.FileAge(string(PChar(Path)));
end;

function _DirectoryExists(Path: Pointer): Integer;
begin
  if GRtlPlatform.DirectoryExists(string(PChar(Path))) then Result := 1 else Result := 0;
end;

function _ForceDirectories(Path: Pointer): Integer;
begin
  if GRtlPlatform.ForceDirectories(string(PChar(Path))) then Result := 1 else Result := 0;
end;

procedure _RemoveDir(Path: Pointer);
begin
  GRtlPlatform.RemoveDir(string(PChar(Path)));
end;

function _GetCurrentDir: Pointer;
begin
  Result := Pointer(GRtlPlatform.GetCurrentDir());
end;

function _SetCurrentDir(Path: Pointer): Integer;
begin
  if GRtlPlatform.SetCurrentDir(string(PChar(Path))) then Result := 1 else Result := 0;
end;

function _ListDir(Path: Pointer): Pointer;
begin
  Result := Pointer(GRtlPlatform.ListDir(string(PChar(Path))));
end;

function _GetTempDir: Pointer;
begin
  Result := Pointer(GRtlPlatform.GetTempDir());
end;

function _GetTempFileName(Dir, Prefix: Pointer): Pointer;
begin
  Result := Pointer(GRtlPlatform.GetTempFileName(string(PChar(Dir)), string(PChar(Prefix))));
end;

function _GetProcessID: Integer;
begin
  Result := GRtlPlatform.GetProcessID();
end;

function _GetEnvVar(Name: Pointer): Pointer;
begin
  Result := Pointer(GRtlPlatform.GetEnvVar(string(PChar(Name))));
end;

procedure _Sleep(Ms: Integer);
begin
  GRtlPlatform.Sleep(Ms);
end;

procedure _Halt(Code: Integer);
begin
  GRtlPlatform.Halt(Code);
end;

function _Exec(Cmd: Pointer): Integer;
begin
  Result := GRtlPlatform.Exec(string(PChar(Cmd)));
end;

procedure _SysWriteStr(Fd: Integer; S: Pointer);
begin
  GRtlPlatform.SysWriteStr(Fd, S);
end;

procedure _SysWriteInt(Fd: Integer; N: Integer);
begin
  GRtlPlatform.SysWriteInt(Fd, N);
end;

procedure _SysWriteInt64(Fd: Integer; N: Int64);
begin
  GRtlPlatform.SysWriteInt64(Fd, N);
end;

procedure _SysWriteUInt64(Fd: Integer; N: UInt64);
begin
  GRtlPlatform.SysWriteUInt64(Fd, N);
end;

procedure _SysWriteDouble(Fd: Integer; V: Double);
begin
  GRtlPlatform.SysWriteDouble(Fd, V);
end;

procedure _SysWriteSingle(Fd: Integer; V: Single);
begin
  GRtlPlatform.SysWriteSingle(Fd, V);
end;

procedure _SysWriteBool(Fd: Integer; B: Boolean);
begin
  GRtlPlatform.SysWriteBool(Fd, B);
end;

procedure _SysWriteNewline(Fd: Integer);
begin
  GRtlPlatform.SysWriteNewline(Fd);
end;

function _FdOpenRead(Path: Pointer): Integer;
begin
  Result := GRtlPlatform.FdOpenRead(Path);
end;

function _FdOpenWrite(Path: Pointer): Integer;
begin
  Result := GRtlPlatform.FdOpenWrite(Path);
end;

function _FdOpenAppend(Path: Pointer): Integer;
begin
  Result := GRtlPlatform.FdOpenAppend(Path);
end;

function _FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
begin
  Result := GRtlPlatform.FdRead(Fd, Buf, Count);
end;

function _FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
begin
  Result := GRtlPlatform.FdWrite(Fd, Buf, Count);
end;

function _FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64;
begin
  Result := GRtlPlatform.FdSeek(Fd, Offset, Origin);
end;

function _FdSize(Fd: Integer): Int64;
begin
  Result := GRtlPlatform.FdSize(Fd);
end;

procedure _FdClose(Fd: Integer);
begin
  GRtlPlatform.FdClose(Fd);
end;

function _TimeNow: Int64;
begin
  Result := GRtlPlatform.TimeNow();
end;

function _TimeLocalOffsetSecs: Integer;
begin
  Result := GRtlPlatform.TimeLocalOffsetSecs();
end;

procedure _TimeSplit(Nanos: Int64;
  out Year, Month, Day, Hour, Min, Sec, NSec: Integer);
begin
  GRtlPlatform.TimeSplit(Nanos, Year, Month, Day, Hour, Min, Sec, NSec);
end;

function _TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec: Integer): Int64;
begin
  Result := GRtlPlatform.TimeJoin(Year, Month, Day, Hour, Min, Sec, NSec);
end;

function _TimeIsLeapYear(Year: Integer): Integer;
begin
  Result := GRtlPlatform.TimeIsLeapYear(Year);
end;

function _TimeDaysInMonth(Year, Month: Integer): Integer;
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

function _ProcessRunning(Proc: Pointer): Integer;
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

function _ProcessExitCode(Proc: Pointer): Integer;
begin
  Result := GRtlPlatform.ProcessExitCode(Proc);
end;

procedure _ProcessFree(Proc: Pointer);
begin
  GRtlPlatform.ProcessFree(Proc);
end;

initialization
  if GRtlPlatform = nil then
    GRtlPlatform := TRtlPlatformPosix.Create();

end.
