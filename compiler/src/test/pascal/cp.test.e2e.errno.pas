{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.errno;

{ E2E tests for the errno-classification leaf (P3 of
  docs/async-networking-design.adoc): the WouldBlock/Interrupted/GetOsErrno
  symbols provided by runtime.errno.<os> (libc profile) and
  runtime.errno.static.<os> (--static profile).

  The two profiles report "would block" differently — libc returns -1 and sets
  *__errno_location(); the raw syscall leaves return -EAGAIN directly — so the
  SAME test program is run in both profiles and must classify identically:

  * the libc arm compiles in-process and links blaise_rtl.a (both backends);
  * the static arm shells out to the CLI compiler with --static, so the
    link-time swap in BuildRTLUnitList (runtime.errno.static.linux plus the
    raw fcntl/read leaves) is exercised for real. }

interface

uses
  SysUtils, Classes, Process, blaise.testing, cp.test.e2e.base,
  blaise.codegen.target;

type
  TErrnoE2ETests = class(TE2ETestCase)
  private
    function BlaisePath(): string;
    function RunBlaise(const AArgs: array of string;
                       out AStdout: string): Integer;
    function RunBinary(const AExe: string; out AStdout: string): Integer;
  protected
    procedure SetUp; override;
  published
    procedure TestWouldBlock_LibcProfile_NonblockingPipe;
    procedure TestWouldBlock_StaticProfile_RawNegativeErrno;
  end;

implementation

const
  { Read from an empty O_NONBLOCK pipe, then classify the return value.  In
    the libc profile read() returns -1 with errno = EAGAIN; in the static
    profile the raw syscall leaf returns -11.  WouldBlock must be true for
    both, Interrupted false, and a success value (0) must never classify. }
  ProbeSrc =
    '''
    program errnoprobe;

    function pipe(Fds: Pointer): Integer; external name 'pipe';
    { fcntl is VARIADIC in C: declared as a plain 3-argument function, Apple
      arm64 passes Arg in x2 where fcntl reads its variadic slot from the
      stack -- F_SETFL got garbage flags and the read blocked forever.  On
      System V the two conventions coincide, which is why this only bit on
      macOS. }
    function fcntl(Fd, Cmd: Integer): Integer; cdecl; varargs; external name 'fcntl';
    function xread(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
      external name 'read';
    function WouldBlock(N: Int64): Boolean; external name 'WouldBlock';
    function Interrupted(N: Int64): Boolean; external name 'Interrupted';

    var
      Fds: array[0..1] of Integer;
      Buf: array[0..7] of Byte;
      Flags: Integer;
      N: Int64;
    begin
      if pipe(@Fds[0]) <> 0 then
      begin
        WriteLn('pipe failed');
        Halt(1);
      end;
      Flags := fcntl(Fds[0], 3, 0);           { F_GETFL }
      { F_SETFL, O_NONBLOCK: Linux $800, FreeBSD $4.  Both bits are set so the
        probe is host-portable: the foreign bit is not a settable status flag
        on the other OS (FreeBSD $800 = O_EXCL, Linux $4 = unused) and F_SETFL
        ignores it. }
      fcntl(Fds[0], 4, Flags or 2048 or 4);
      N := xread(Fds[0], @Buf[0], 8);
      if WouldBlock(N) then WriteLn('WOULDBLOCK') else WriteLn('NOTWB');
      if Interrupted(N) then WriteLn('INTR') else WriteLn('NOINTR');
      if WouldBlock(0) then WriteLn('BAD0') else WriteLn('OK0');
    end.
    ''';

  ProbeExpected = 'WOULDBLOCK' + LineEnding + 'NOINTR' + LineEnding +
    'OK0' + LineEnding;

procedure TErrnoE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-errno')
end;

function TErrnoE2ETests.BlaisePath(): string;
var
  Root: string;
begin
  Root := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Root <> '' then
    Result := IncludeTrailingPathDelimiter(Root) + 'compiler/target/blaise'
  else
    Result := ExtractFilePath(ParamStr(0)) + 'blaise'
end;

function TErrnoE2ETests.RunBlaise(const AArgs: array of string;
                                  out AStdout: string): Integer;
var
  Proc: TProcess;
  I: Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := BlaisePath();
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TErrnoE2ETests.RunBinary(const AExe: string;
                                  out AStdout: string): Integer;
var
  Proc: TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

procedure TErrnoE2ETests.TestWouldBlock_LibcProfile_NonblockingPipe;
begin
  { libc profile: read() -> -1 + errno; WouldBlock reads __errno_location.
    Runs on both backends — the classification is backend-invariant. }
  AssertRunsOnAll(ProbeSrc, ProbeExpected, 0)
end;

procedure TErrnoE2ETests.TestWouldBlock_StaticProfile_RawNegativeErrno;
var
  ProgPas, ProgBin: string;
  Captured, Output: string;
  Rc: Integer;
begin
  { --static is the Linux freestanding profile; macOS binaries are always
    dynamic against libSystem and the compiler rejects --static there. }
  if HostTarget().OS = osMacOS then
  begin
    Ignore('--static has no macOS profile (always dynamic against libSystem)');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  ProgPas := FScratch + '/errnoprobe_static.pas';
  ProgBin := FScratch + '/errnoprobe_static';
  WriteFile(ProgPas, ProbeSrc);

  { --static swaps in runtime.errno.static.linux and the raw syscall leaves:
    read returns -EAGAIN directly and there is no errno variable. }
  Rc := RunBlaise(['--source', ProgPas, '--static', '--output', ProgBin],
    Captured);
  AssertEquals('blaise --static exit code (output: ' + Captured + ')', 0, Rc);
  AssertTrue('static binary exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Output);
  AssertEquals('[static] stdout', ProbeExpected, Output);
  AssertEquals('[static] exit code', 0, Rc)
end;

initialization
  RegisterTest(TErrnoE2ETests);

end.
