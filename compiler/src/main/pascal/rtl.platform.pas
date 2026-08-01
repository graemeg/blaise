{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit rtl.platform;

// Blaise RTL — platform abstraction layer.
//
// TRtlPlatform is the abstract base class defining all OS-level operations.
// No {$IFDEF} directives appear in the CLASS APIs of this unit or its concrete
// implementations.  Platform-specific behaviour is expressed by subclassing
// TRtlPlatform and assigning the instance to GRtlPlatform at program start.
// One carve-out: link-level FLAT functions in the concrete layout units
// (pre-init leaves like _MapAnonFlag, imported via `external name`) share one
// global symbol name across every layout unit, so each is guarded by its
// target define — otherwise a host build that imports a foreign layout unit
// for its class API (e.g. cp.test.platformlayout.freebsd) links two
// definitions and the wrong OS's value can win.
//
// Each supported platform provides a single concrete subclass:
//   - TRtlPlatformPosix  (Linux, FreeBSD)
//   - TRtlPlatformDarwin (macOS)  — future
//   - TRtlPlatformWin32  (Windows) — future

interface

type
  TRtlPlatform = class
  public
    { File operations }
    function FileExists(const APath: string): Boolean; virtual; abstract;
    procedure DeleteFile(const APath: string); virtual; abstract;
    function RenameFile(const AOldPath, ANewPath: string): Boolean; virtual; abstract;
    function ReadFile(const APath: string): string; virtual; abstract;
    procedure WriteFile(const APath, AContent: string); virtual; abstract;
    procedure AppendFile(const APath, AContent: string); virtual; abstract;
    function FileAge(const APath: string): Int64; virtual; abstract;

    { Directory operations }
    function DirectoryExists(const APath: string): Boolean; virtual; abstract;
    function ForceDirectories(const APath: string): Boolean; virtual; abstract;
    function RemoveDir(const APath: string): Boolean; virtual; abstract;
    function GetCurrentDir: string; virtual; abstract;
    function SetCurrentDir(const APath: string): Boolean; virtual; abstract;

    { OS utilities }
    function GetTempDir: string; virtual; abstract;
    function GetTempFileName(const ADir, APrefix: string): string; virtual; abstract;
    function GetProcessID: Integer; virtual; abstract;
    function GetEnvVar(const AName: string): string; virtual; abstract;
    procedure Sleep(AMilliseconds: Integer); virtual; abstract;
    procedure Halt(AExitCode: Integer); virtual; abstract;

    { Process }
    function Exec(const ACmd: string): Integer; virtual; abstract;
    function ParamCount: Integer; virtual; abstract;
    function ParamStr(AIndex: Integer): string; virtual; abstract;

    { Console I/O — used by compiler-emitted WriteLn/Write }
    procedure SysWriteStr(Fd: Integer; S: Pointer); virtual; abstract;
    procedure SysWriteInt(Fd: Integer; N: Integer); virtual; abstract;
    procedure SysWriteInt64(Fd: Integer; N: Int64); virtual; abstract;
    procedure SysWriteUInt64(Fd: Integer; N: UInt64); virtual; abstract;
    procedure SysWriteDouble(Fd: Integer; V: Double); virtual; abstract;
    procedure SysWriteSingle(Fd: Integer; V: Single); virtual; abstract;
    procedure SysWriteBool(Fd: Integer; B: Boolean); virtual; abstract;
    procedure SysWriteNewline(Fd: Integer); virtual; abstract;

    { File-descriptor primitives — used by streams }
    function FdOpenRead(Path: Pointer): Integer; virtual; abstract;
    function FdOpenWrite(Path: Pointer): Integer; virtual; abstract;
    function FdOpenAppend(Path: Pointer): Integer; virtual; abstract;
    function FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer; virtual; abstract;
    function FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer; virtual; abstract;
    function FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64; virtual; abstract;
    function FdSize(Fd: Integer): Int64; virtual; abstract;
    procedure FdClose(Fd: Integer); virtual; abstract;

    { Date/Time }
    function TimeNow: Int64; virtual; abstract;
    function TimeLocalOffsetSecs: Integer; virtual; abstract;
    procedure TimeSplit(Nanos: Int64;
      out Year, Month, Day, Hour, Min, Sec, NSec: Integer); virtual; abstract;
    function TimeJoin(Year, Month, Day,
      Hour, Min, Sec, NSec: Integer): Int64; virtual; abstract;
    function TimeIsLeapYear(Year: Integer): Integer; virtual; abstract;
    function TimeDaysInMonth(Year, Month: Integer): Integer; virtual; abstract;

    { Process management — fork/exec/pipe }
    function ProcessCreate: Pointer; virtual; abstract;
    procedure ProcessSetExe(Proc: Pointer; ExeStr: Pointer); virtual; abstract;
    procedure ProcessAddArg(Proc: Pointer; ArgStr: Pointer); virtual; abstract;
    procedure ProcessExecute(Proc: Pointer); virtual; abstract;
    function ProcessRunning(Proc: Pointer): Integer; virtual; abstract;
    function ProcessReadOutput(Proc: Pointer): Pointer; virtual; abstract;
    procedure ProcessWaitOnExit(Proc: Pointer); virtual; abstract;
    function ProcessExitCode(Proc: Pointer): Integer; virtual; abstract;
    procedure ProcessFree(Proc: Pointer); virtual; abstract;
  end;

  { Per-target struct layouts and OS constant values.
    (docs/native-target-architecture.adoc)

    Two things diverge across POSIX targets and both live here so the platform
    methods stay layout-agnostic:

    * OS integer constants — the open()/lseek() flag bits, clock id, and
      waitpid option whose numeric values differ between Linux and FreeBSD.

    * struct stat — its field OFFSETS differ (FreeBSD's stat is a different
      shape and size than Linux's).  Rather than a shared TStatBuf record that
      bakes in one layout, the buffer is an opaque byte block sized by
      StatBufSize, and the three fields the RTL reads are pulled out by
      StatSize / StatMtime / StatMode at the target's offsets.

    struct tm is intentionally NOT abstracted: the fields the RTL uses
    (tm_year/mon/mday/hour/min/sec/gmtoff) share an identical layout on Linux
    and FreeBSD amd64, so TRtlPlatformPosix keeps a shared TTm record.

    The concrete layout is selected at startup alongside GRtlPlatform; nothing
    here uses conditional compilation. }
  TPlatformLayout = class
  public
    { ---- open() / file flags ---- }
    function O_RDONLY: Integer; virtual; abstract;
    function O_WRONLY: Integer; virtual; abstract;
    function O_RDWR:   Integer; virtual; abstract;
    function O_CREAT:  Integer; virtual; abstract;
    function O_TRUNC:  Integer; virtual; abstract;
    function O_APPEND: Integer; virtual; abstract;

    { ---- stat mode bits ---- }
    function S_IFMT:  Integer; virtual; abstract;
    function S_IFDIR: Integer; virtual; abstract;

    { ---- lseek whence ---- }
    function SEEK_SET: Integer; virtual; abstract;
    function SEEK_CUR: Integer; virtual; abstract;
    function SEEK_END: Integer; virtual; abstract;

    { ---- clock_gettime / waitpid ---- }
    function CLOCK_REALTIME: Integer; virtual; abstract;
    function WNOHANG:        Integer; virtual; abstract;

    { ---- sysconf(3) names ---- }
    { The online-processor count.  Linux numbers it 84, FreeBSD and Darwin 58 —
      and neither rejects the other's number: FreeBSD's 84 is
      _SC_THREAD_CPUTIME, which answers 200112 (the POSIX option version).  So
      passing the wrong name yields a plausible-looking Int64 rather than -1,
      and GetCPUCount silently reports 200112 CPUs to whoever sizes a thread
      pool from it. }
    function SC_NPROCESSORS_ONLN: Integer; virtual; abstract;

    { ---- struct stat: opaque buffer sized for the target, fields pulled at
      the target's offsets ---- }
    function StatBufSize: Integer; virtual; abstract;
    function StatSize(Buf: Pointer):  Int64; virtual; abstract;
    function StatMtime(Buf: Pointer): Int64; virtual; abstract;
    function StatMode(Buf: Pointer):  Integer; virtual; abstract;
  end;

var
  GRtlPlatform: TRtlPlatform;
  GPlatformLayout: TPlatformLayout;

implementation

end.
