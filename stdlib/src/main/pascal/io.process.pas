{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ IO.Process: child processes with their own stdin, stdout and stderr pipes
  and a working directory, for programs that talk to a child (a debugger
  adapter, a language server) or must tell its output from its errors.

  Process.TProcess (one merged output pipe, no stdin) stays for simple
  uses; TSubprocess differs in that:

  * stdout and stderr are separate pipes, and Read polls both, so a child
    that fills one while the parent waits on the other cannot deadlock;
  * stdin is a pipe: WriteInput, then CloseInput for end-of-file;
  * WorkingDirectory is entered by the child before exec;
  * a program that cannot be started (missing, not executable, a bad
    working directory) raises EProcessStartError from Start, rather than
    looking like exit code 127: the child reports exec's errno through a
    close-on-exec pipe, which the parent reads before Start returns;
  * a signalled child's exit code is 128 + the signal, as in a shell.

  Usage:

    P := TSubprocess.Create('pdr-dap');
    P.Args.Add('--stdio');
    P.WorkingDirectory := ProjectDir;
    P.Start();
    P.WriteInput(Request);
    while P.Read(100, Out_, Err) do ...;   // False once both pipes close
    Code := P.WaitForExit();

  The child inherits the parent's environment.  Between fork and exec the
  child calls only async-signal-safe libc routines on data prepared before
  the fork, so starting a process from a multi-threaded program is safe. }

unit IO.Process;

interface

uses
  SysUtils, StrUtils, Generics.Collections;

type
  EProcessStartError = class(Exception);

  TSubprocess = class
  private
    FExecutable: string;
    FArgs: TList<string>;
    FWorkingDirectory: string;
    FPid: Int32;
    FIn, FOut, FErr: Int32;
    FExited: Boolean;
    FExitCode: Int32;
    procedure Reap(AStatus: Int32);
  public
    constructor Create(const AExecutable: string);
    destructor Destroy; override;
    { Start the child.  Raises EProcessStartError when it cannot run. }
    procedure Start();
    { Write AData to the child's stdin; False once the child has closed it
      (or CloseInput was called). }
    function WriteInput(const AData: string): Boolean;
    { Close the child's stdin (it then reads end-of-file). }
    procedure CloseInput();
    { Wait up to ATimeoutMs (-1: no limit) for output on either pipe and
      return what one read of each ready pipe gives.  False once both pipes
      have reached end-of-file. }
    function Read(ATimeoutMs: Int32; out AOutput, AError: string): Boolean;
    { Read both pipes to end-of-file. }
    procedure ReadToEnd(out AOutput, AError: string);
    function Running(): Boolean;
    { Wait for the child to exit and return its exit code. }
    function WaitForExit(): Int32;
    { Send SIGTERM (Terminate) or SIGKILL (Kill). }
    procedure Terminate();
    procedure Kill();
    function Pid(): Int32;
    property Executable: string read FExecutable;
    property Args: TList<string> read FArgs;
    property WorkingDirectory: string read FWorkingDirectory write FWorkingDirectory;
    property ExitCode: Int32 read FExitCode;
  end;

  TProcessOutput = record
    Output, Error: string;
    ExitCode: Int32;
  end;

{ Run AExecutable with AArgs in AWorkingDirectory ('' = the current one) to
  completion, with no input.  Raises EProcessStartError. }
function RunProcess(const AExecutable: string; const AArgs: array of string;
  const AWorkingDirectory: string): TProcessOutput;

implementation

const
  SIGKILL = 9;
  SIGTERM = 15;
  SIGPIPE = 13;
  F_SETFD = 2;
  FD_CLOEXEC = 1;
  POLLIN = 1;
  POLLERR = 8;
  POLLHUP = 16;
  ReadChunk = 65536;

type
  PInt32 = ^Int32;
  PByte = ^Byte;
  PPointer = ^Pointer;

  TPollFd = record
    Fd: Int32;
    Events: Int16;
    REvents: Int16;
  end;

function c_fork(): Int32; external name 'fork';
function c_execvp(AFile: Pointer; AArgv: Pointer): Int32; external name 'execvp';
procedure c__exit(ACode: Int32); external name '_exit';
function c_waitpid(APid: Int32; AStatus: Pointer; AOptions: Int32): Int32; external name 'waitpid';
function c_pipe(AFds: Pointer): Int32; external name 'pipe';
function c_dup2(AOld, ANew: Int32): Int32; external name 'dup2';
function c_close(AFd: Int32): Int32; external name 'close';
function c_chdir(APath: Pointer): Int32; external name 'chdir';
function c_read(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64; external name 'read';
function c_write(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64; external name 'write';
function c_kill(APid, ASig: Int32): Int32; external name 'kill';
function c_poll(AFds: Pointer; ANFds: Int64; ATimeout: Int32): Int32; external name 'poll';
{ fcntl is C-variadic: the third argument must travel the variadic way. }
function c_fcntl(AFd, ACmd: Int32): Int32; varargs; external name 'fcntl';
function c_signal(ASignum: Int32; AHandler: Pointer): Pointer; external name 'signal';
{ errno, per build profile (runtime.errno.*, chosen at link time): the
  static, libc-free profile has no errno variable; its calls return -errno. }
function Interrupted(N: Int64): Boolean; external name 'Interrupted';
function GetOsErrno(): Int; external name 'GetOsErrno';

{ The errno of a call that failed with result R, in either profile. }
function FailureErrno(R: Int64): Int32;
begin
  Result := Int32(GetOsErrno());
  if (Result = 0) and (R < 0) then
    Result := Int32(-R);
end;

{ The text of the errors exec and chdir report; the numbers are the same on
  Linux, FreeBSD and macOS.  strerror is not available without libc. }
function ErrorText(AErr: Int32): string;
begin
  case AErr of
    1: Result := 'Operation not permitted';
    2: Result := 'No such file or directory';
    5: Result := 'Input/output error';
    7: Result := 'Argument list too long';
    8: Result := 'Exec format error';
    12: Result := 'Cannot allocate memory';
    13: Result := 'Permission denied';
    20: Result := 'Not a directory';
    21: Result := 'Is a directory';
    26: Result := 'Text file busy';
  else
    Result := 'error ' + IntToStr(AErr);
  end;
end;

{ A NUL-terminated copy of S on the heap. }
function CString(const S: string): Pointer;
var
  I: Int;
begin
  Result := GetMem(Length(S) + 1);
  for I := 0 to Length(S) - 1 do
    PByte(UInt(Result) + UInt(I))^ := S[I];
  PByte(UInt(Result) + UInt(Length(S)))^ := 0;
end;

function BufToString(ABuf: Pointer; ACount: Int): string;
var
  I: Int;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  for I := 0 to ACount - 1 do
    SB.AppendByte(PByte(UInt(ABuf) + UInt(I))^);
  Result := SB.ToString();
end;

procedure SetCloseOnExec(AFd: Int32);
begin
  c_fcntl(AFd, F_SETFD, FD_CLOEXEC);
end;

function MakePipe(out ARead, AWrite: Int32): Boolean;
var
  Fds: array[0..1] of Int32;
begin
  Result := c_pipe(@Fds[0]) = 0;
  if Result then
  begin
    ARead := Fds[0];
    AWrite := Fds[1];
  end;
end;

{ The child between fork and exec: async-signal-safe calls only, on data
  prepared by the parent.  Never returns. }
procedure ChildExec(AStdin, AStdout, AStderr, AStatus: Int32; ACwd, AFile, AArgv: Pointer);
var
  E, R: Int32;
begin
  c_dup2(AStdin, 0);
  c_dup2(AStdout, 1);
  c_dup2(AStderr, 2);
  R := 0;
  if ACwd <> nil then
    R := c_chdir(ACwd);
  if R <> 0 then
  begin
    E := FailureErrno(R);
    c_write(AStatus, @E, 4);
    c__exit(127);
  end;
  R := c_execvp(AFile, AArgv);
  E := FailureErrno(R);
  c_write(AStatus, @E, 4);
  c__exit(127);
end;

{ ---------------------------------------------------------------------------
  TSubprocess
  --------------------------------------------------------------------------- }

constructor TSubprocess.Create(const AExecutable: string);
begin
  FExecutable := AExecutable;
  FArgs := TList<string>.Create();
  FPid := -1;
  FIn := -1;
  FOut := -1;
  FErr := -1;
end;

destructor TSubprocess.Destroy;
begin
  CloseInput();
  if FOut >= 0 then c_close(FOut);
  if FErr >= 0 then c_close(FErr);
  { Reap a child that has already gone, so it does not linger as a zombie;
    a running child is left running. }
  if FPid > 0 then
    Running();
  inherited Destroy();
end;

procedure TSubprocess.Start();
var
  InR, InW, OutR, OutW, ErrR, ErrW, StR, StW: Int32;
  Argv, FileP, CwdP: Pointer;
  I: Int;
  Pid, E, Got: Int32;
  N: Int64;
  Reason: string;
begin
  if FPid > 0 then
    raise EProcessStartError.Create('process already started');
  { A write to the stdin of a child that has exited must fail, not kill us. }
  c_signal(SIGPIPE, Pointer(1));
  if not MakePipe(InR, InW) then
    raise EProcessStartError.Create('cannot create a pipe');
  if not MakePipe(OutR, OutW) then
    raise EProcessStartError.Create('cannot create a pipe');
  if not MakePipe(ErrR, ErrW) then
    raise EProcessStartError.Create('cannot create a pipe');
  if not MakePipe(StR, StW) then
    raise EProcessStartError.Create('cannot create a pipe');
  { The parent's ends must not leak into other children (a leaked stdin
    write end would keep this child from ever seeing end-of-file). }
  SetCloseOnExec(InW);
  SetCloseOnExec(OutR);
  SetCloseOnExec(ErrR);
  SetCloseOnExec(StR);
  SetCloseOnExec(StW);

  FileP := CString(FExecutable);
  Argv := GetMem((FArgs.Count + 2) * SizeOf(Pointer));
  PPointer(Argv)^ := FileP;
  for I := 0 to FArgs.Count - 1 do
    PPointer(UInt(Argv) + UInt((I + 1) * SizeOf(Pointer)))^ := CString(FArgs[I]);
  PPointer(UInt(Argv) + UInt((FArgs.Count + 1) * SizeOf(Pointer)))^ := nil;
  CwdP := nil;
  if FWorkingDirectory <> '' then
    CwdP := CString(FWorkingDirectory);

  Pid := c_fork();
  if Pid = 0 then
    ChildExec(InR, OutW, ErrW, StW, CwdP, FileP, Argv);

  c_close(InR);
  c_close(OutW);
  c_close(ErrW);
  c_close(StW);
  for I := 0 to FArgs.Count do
    FreeMem(PPointer(UInt(Argv) + UInt(I * SizeOf(Pointer)))^);
  FreeMem(Argv);
  if CwdP <> nil then
    FreeMem(CwdP);
  if Pid < 0 then
  begin
    c_close(InW);
    c_close(OutR);
    c_close(ErrR);
    c_close(StR);
    raise EProcessStartError.Create('cannot fork to start ' + FExecutable);
  end;

  { End-of-file on the status pipe means exec succeeded (close-on-exec
    closed it); four bytes are the errno of a failed chdir or exec. }
  E := 0;
  repeat
    N := c_read(StR, @E, 4);
  until not Interrupted(N);
  c_close(StR);
  if N = 4 then
  begin
    c_close(InW);
    c_close(OutR);
    c_close(ErrR);
    c_waitpid(Pid, @Got, 0);
    Reason := ErrorText(E);
    if (FWorkingDirectory <> '') and (E = 2) then
      Reason := Reason + ' (program or working directory ' + FWorkingDirectory + ')';
    raise EProcessStartError.Create('cannot start ' + FExecutable + ': ' + Reason);
  end;
  FPid := Pid;
  FIn := InW;
  FOut := OutR;
  FErr := ErrR;
  FExited := False;
end;

function TSubprocess.WriteInput(const AData: string): Boolean;
var
  P: Pointer;
  Left, N: Int64;
begin
  if FIn < 0 then
    Exit(False);
  Left := Length(AData);
  if Left = 0 then
    Exit(True);
  P := PChar(AData);
  while Left > 0 do
  begin
    N := c_write(FIn, P, Left);
    if N > 0 then
    begin
      P := Pointer(UInt(P) + UInt(N));
      Left := Left - N;
    end
    else if not Interrupted(N) then
      Exit(False);
  end;
  Result := True;
end;

procedure TSubprocess.CloseInput();
begin
  if FIn >= 0 then
  begin
    c_close(FIn);
    FIn := -1;
  end;
end;

function TSubprocess.Read(ATimeoutMs: Int32; out AOutput, AError: string): Boolean;
var
  Fds: array[0..1] of TPollFd;
  Map: array[0..1] of Int32;   { 0 = stdout, 1 = stderr }
  Count, I, R: Int32;
  Buf: Pointer;
  N: Int64;
begin
  AOutput := '';
  AError := '';
  Count := 0;
  if FOut >= 0 then
  begin
    Fds[Count].Fd := FOut;
    Fds[Count].Events := POLLIN;
    Fds[Count].REvents := 0;
    Map[Count] := 0;
    Count := Count + 1;
  end;
  if FErr >= 0 then
  begin
    Fds[Count].Fd := FErr;
    Fds[Count].Events := POLLIN;
    Fds[Count].REvents := 0;
    Map[Count] := 1;
    Count := Count + 1;
  end;
  if Count = 0 then
    Exit(False);
  Result := True;
  R := c_poll(@Fds[0], Count, ATimeoutMs);
  if R <= 0 then
    Exit;   { timeout, or EINTR: the caller polls again }
  Buf := GetMem(ReadChunk);
  for I := 0 to Count - 1 do
    if (Fds[I].REvents and (POLLIN or POLLHUP or POLLERR)) <> 0 then
    begin
      repeat
        N := c_read(Fds[I].Fd, Buf, ReadChunk);
      until not Interrupted(N);
      if N > 0 then
      begin
        if Map[I] = 0 then
          AOutput := BufToString(Buf, N)
        else
          AError := BufToString(Buf, N);
      end
      else
      begin
        { End-of-file (or an error): this pipe is done. }
        c_close(Fds[I].Fd);
        if Map[I] = 0 then
          FOut := -1
        else
          FErr := -1;
      end;
    end;
  FreeMem(Buf);
  Result := (FOut >= 0) or (FErr >= 0) or (AOutput <> '') or (AError <> '');
end;

procedure TSubprocess.ReadToEnd(out AOutput, AError: string);
var
  O, E: string;
  SO, SE: TStringBuilder;
begin
  SO := TStringBuilder.Create();
  SE := TStringBuilder.Create();
  while Read(-1, O, E) do
  begin
    SO.Append(O);
    SE.Append(E);
  end;
  AOutput := SO.ToString();
  AError := SE.ToString();
end;

procedure TSubprocess.Reap(AStatus: Int32);
begin
  FExited := True;
  if (AStatus and $7F) = 0 then
    FExitCode := (AStatus shr 8) and $FF
  else
    FExitCode := 128 + (AStatus and $7F);
end;

function TSubprocess.Running(): Boolean;
var
  Status, R: Int32;
begin
  if (FPid <= 0) or FExited then
    Exit(False);
  Status := 0;
  R := c_waitpid(FPid, @Status, 1);   { WNOHANG }
  if R = FPid then
  begin
    Reap(Status);
    Exit(False);
  end;
  Result := R = 0;
end;

function TSubprocess.WaitForExit(): Int32;
var
  Status, R: Int32;
begin
  if (FPid > 0) and not FExited then
  begin
    CloseInput();
    repeat
      Status := 0;
      R := c_waitpid(FPid, @Status, 0);
    until (R = FPid) or ((R < 0) and not Interrupted(R));
    if R = FPid then
      Reap(Status)
    else
      FExited := True;
  end;
  Result := FExitCode;
end;

procedure TSubprocess.Terminate();
begin
  if (FPid > 0) and not FExited then
    c_kill(FPid, SIGTERM);
end;

procedure TSubprocess.Kill();
begin
  if (FPid > 0) and not FExited then
    c_kill(FPid, SIGKILL);
end;

function TSubprocess.Pid(): Int32;
begin
  Result := FPid;
end;

function RunProcess(const AExecutable: string; const AArgs: array of string;
  const AWorkingDirectory: string): TProcessOutput;
var
  P: TSubprocess;
  I: Int;
  O, E: string;
begin
  P := TSubprocess.Create(AExecutable);
  for I := 0 to Length(AArgs) - 1 do
    P.Args.Add(AArgs[I]);
  P.WorkingDirectory := AWorkingDirectory;
  P.Start();
  P.CloseInput();
  P.ReadToEnd(O, E);
  Result.Output := O;
  Result.Error := E;
  Result.ExitCode := P.WaitForExit();
end;

end.
