{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for IO.Process: separate stdout/stderr pipes, stdin, the working
  directory, exit codes and signals, start failures, and reading both pipes
  without deadlock.  Children are /bin/sh scripts.

  Self-registers via the initialization section. }

unit IOProcess.Tests;

interface

uses
  blaise.testing, SysUtils, Generics.Collections, IO.Process;

type
  TIOProcessTests = class(TTestCase)
  private
    function Shell(const AScript: string): TSubprocess;
  published
    procedure TestSeparateOutputAndError;
    procedure TestExitCode;
    procedure TestStdinRoundTrip;
    procedure TestWorkingDirectory;
    procedure TestStartFailureRaises;
    procedure TestTerminate;
    procedure TestLargeOutputOnBothPipes;
    procedure TestReadTimesOut;
    procedure TestRunHelper;
    { TSubprocess.Environment and the SysUtils environment listing }
    procedure TestEnvironmentReplacesTheParents;
    procedure TestEnvironmentStartsAsTheParents;
    procedure TestEnvironmentPathFindsTheProgram;
    procedure TestEnvironmentMissingProgramRaises;
    procedure TestListEnvironment;
  end;

implementation

function TIOProcessTests.Shell(const AScript: string): TSubprocess;
begin
  Result := TSubprocess.Create('/bin/sh');
  Result.Args.Add('-c');
  Result.Args.Add(AScript);
end;

procedure TIOProcessTests.TestSeparateOutputAndError;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  P := Shell('echo out; echo err 1>&2');
  P.Start();
  P.ReadToEnd(Out_, Err);
  AssertEquals('out' + #10, Out_);
  AssertEquals('err' + #10, Err);
  AssertEquals(0, P.WaitForExit());
end;

procedure TIOProcessTests.TestExitCode;
var
  P: TSubprocess;
begin
  P := Shell('exit 3');
  P.Start();
  AssertEquals(3, P.WaitForExit());
  AssertEquals(3, P.ExitCode);
  AssertFalse(P.Running());
end;

procedure TIOProcessTests.TestStdinRoundTrip;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  P := TSubprocess.Create('cat');
  P.Start();
  AssertTrue(P.WriteInput('hello' + #10));
  AssertTrue(P.WriteInput('world' + #10));
  P.CloseInput();
  P.ReadToEnd(Out_, Err);
  AssertEquals('hello' + #10 + 'world' + #10, Out_);
  AssertEquals(0, P.WaitForExit());
end;

procedure TIOProcessTests.TestWorkingDirectory;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  P := Shell('pwd');
  P.WorkingDirectory := '/';
  P.Start();
  P.ReadToEnd(Out_, Err);
  AssertEquals('/' + #10, Out_);
end;

procedure TIOProcessTests.TestStartFailureRaises;
var
  P: TSubprocess;
  Raised: Boolean;
begin
  P := TSubprocess.Create('/no/such/program-xyz');
  Raised := False;
  try
    P.Start();
  except
    on E: EProcessStartError do
    begin
      Raised := True;
      AssertTrue(E.Message, Pos('No such file or directory', E.Message) >= 0);
    end;
  end;
  AssertTrue('a missing program raises', Raised);
  P := Shell('true');
  P.WorkingDirectory := '/no/such/dir-xyz';
  Raised := False;
  try
    P.Start();
  except
    on E: EProcessStartError do
      Raised := True;
  end;
  AssertTrue('a missing working directory raises', Raised);
end;

procedure TIOProcessTests.TestTerminate;
var
  P: TSubprocess;
begin
  P := Shell('sleep 30');
  P.Start();
  AssertTrue(P.Running());
  P.Terminate();
  AssertEquals('128 + SIGTERM', 143, P.WaitForExit());
end;

procedure TIOProcessTests.TestLargeOutputOnBothPipes;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  { 200 KB on each pipe: more than either pipe buffer holds, so reading one
    pipe to its end before the other would deadlock. }
  P := Shell('i=0; while [ $i -lt 2000 ]; do ' +
    'echo 0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789; ' +
    'echo 0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789 1>&2; ' +
    'i=$((i+1)); done');
  P.Start();
  P.ReadToEnd(Out_, Err);
  AssertEquals(2000 * 101, Length(Out_));
  AssertEquals(2000 * 101, Length(Err));
  AssertEquals(0, P.WaitForExit());
end;

procedure TIOProcessTests.TestReadTimesOut;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  P := Shell('sleep 30');
  P.Start();
  AssertTrue('still open', P.Read(50, Out_, Err));
  AssertEquals('', Out_);
  AssertEquals('', Err);
  P.Terminate();
  P.WaitForExit();
end;

{ Environment, once used, is exactly what the child gets: cleared and
  given one variable, env prints that one variable alone. }
procedure TIOProcessTests.TestEnvironmentReplacesTheParents;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  P := TSubprocess.Create('/usr/bin/env');
  P.Environment.Clear();
  P.Environment['FACET_TEST'] := 'one two';
  P.Start();
  P.ReadToEnd(Out_, Err);
  AssertEquals(0, P.WaitForExit());
  AssertEquals('FACET_TEST=one two' + #10, Out_);
end;

{ Its first use copies the parent's environment in, so a child given one
  extra variable still sees the parent's. }
procedure TIOProcessTests.TestEnvironmentStartsAsTheParents;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  AssertEquals('copied PATH', GetEnvironmentVariable('PATH'),
    TSubprocess.Create('x').Environment['PATH']);
  P := Shell('echo "$HOME|$EXTRA"');
  P.Environment['EXTRA'] := 'added';
  P.Start();
  P.ReadToEnd(Out_, Err);
  AssertEquals(0, P.WaitForExit());
  AssertEquals(GetEnvironmentVariable('HOME') + '|added' + #10, Out_);
end;

{ A bare program name is found on the PATH of the child's environment. }
procedure TIOProcessTests.TestEnvironmentPathFindsTheProgram;
var
  P: TSubprocess;
  Out_, Err: string;
begin
  P := TSubprocess.Create('sh');
  P.Args.Add('-c');
  P.Args.Add('echo "$X"');
  P.Environment.Clear();
  P.Environment['PATH'] := '/nonexistent:/bin:/usr/bin';
  P.Environment['X'] := 'found';
  P.Start();
  P.ReadToEnd(Out_, Err);
  AssertEquals(0, P.WaitForExit());
  AssertEquals('found' + #10, Out_);
end;

{ A program not on that PATH cannot start, as without Environment. }
procedure TIOProcessTests.TestEnvironmentMissingProgramRaises;
var
  P: TSubprocess;
  Raised: Boolean;
begin
  P := TSubprocess.Create('sh');
  P.Environment.Clear();
  P.Environment['PATH'] := '/nonexistent';
  Raised := False;
  try
    P.Start();
  except
    on E: EProcessStartError do
      Raised := Pos('No such file', E.Message) >= 0;
  end;
  AssertTrue('EProcessStartError, no such file', Raised);
end;

{ SysUtils lists the start-up environment: every entry is NAME=VALUE and
  agrees with GetEnvironmentVariable; past the end is ''. }
procedure TIOProcessTests.TestListEnvironment;
var
  I, N, Eq: Int;
  Entry: string;
  SawPath: Boolean;
begin
  N := GetEnvironmentVariableCount();
  AssertTrue('some variables', N > 0);
  SawPath := False;
  for I := 0 to N - 1 do
  begin
    Entry := GetEnvironmentString(I);
    Eq := Pos('=', Entry);
    AssertTrue('NAME=VALUE: ' + Entry, Eq > 0);
    if Copy(Entry, 0, Eq) = 'PATH' then
    begin
      SawPath := True;
      AssertEquals('PATH=' + GetEnvironmentVariable('PATH'), Entry);
    end;
  end;
  AssertTrue('PATH listed', SawPath);
  AssertEquals('', GetEnvironmentString(N));
  AssertEquals('', GetEnvironmentString(-1));
end;

procedure TIOProcessTests.TestRunHelper;
var
  R: TProcessOutput;
begin
  R := RunProcess('/bin/sh', ['-c', 'printf x; printf y 1>&2; exit 4'], '');
  AssertEquals('x', R.Output);
  AssertEquals('y', R.Error);
  AssertEquals(4, R.ExitCode);
end;

initialization
  RegisterTest(TIOProcessTests);
end.
