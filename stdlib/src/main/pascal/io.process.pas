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

  * stdout and stderr are separate pipes, and Read waits on both, so a
    child that fills one while the parent waits on the other cannot
    deadlock;
  * stdin is a pipe: WriteInput, then CloseInput for end-of-file;
  * WorkingDirectory is the directory the child starts in;
  * a program that cannot be started (missing, not executable, a bad
    working directory) raises EProcessStartError from Start, rather than
    looking like exit code 127;
  * a child a signal ended exits with 128 + the signal, as in a shell.  On
    Windows, Terminate and Kill end the child with 143 and 137, the codes
    SIGTERM and SIGKILL give.

  Usage:

    P := TSubprocess.Create('pdr-dap');
    P.Args.Add('--stdio');
    P.WorkingDirectory := ProjectDir;
    P.Start();
    P.WriteInput(Request);
    while P.Read(100, Out_, Err) do ...;   // False once both pipes close
    Code := P.WaitForExit();

  The child inherits the parent's environment unless Environment is used:
  its first use fills it with the parent's (start-up) environment, which
  can then be changed, cleared or replaced, and the child gets exactly
  what it holds.  A program named without a directory is then looked up on
  the PATH in that environment, as 'env -i NAME=VALUE ... program' does:
  on POSIX a ':' separated list (/usr/bin:/bin when there is none), on
  Windows a ';' separated one, where NAME.exe and NAME.com are tried too.

    P.Environment.Clear();
    P.Environment['HOME'] := Home;

  The child is started through the platform port (rtl.platform,
  TRtlPlatform.ProcSpawn): fork and exec on POSIX, where the child calls
  only async-signal-safe routines between the two, so starting a process
  from a multi-threaded program is safe; CreateProcessW on Windows. }

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
    FEnvironment: TDictionary<string, string>;
    FStarted: Boolean;
    { the platform port's handle on the child: its pid on POSIX, its process
      handle on Windows }
    FChild: Int64;
    FIn, FOut, FErr: Int32;
    FExited: Boolean;
    FExitCode: Int32;
    function GetEnvironment(): TDictionary<string, string>;
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
    { Send SIGTERM (Terminate) or SIGKILL (Kill); on Windows, end the child
      with exit code 143 or 137. }
    procedure Terminate();
    procedure Kill();
    function Pid(): Int32;
    property Executable: string read FExecutable;
    property Args: TList<string> read FArgs;
    property WorkingDirectory: string read FWorkingDirectory write FWorkingDirectory;
    { The child's environment.  Untouched, the child inherits the parent's;
      the first use copies the parent's start-up environment in, and from
      then on the child gets exactly this (see the unit comment). }
    property Environment: TDictionary<string, string> read GetEnvironment;
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
  ENOENT = 2;
  ReadChunk = 65536;

type
  PByte = ^Byte;

{ The platform port's child processes and descriptors (rtl.platform.abi). }
function _ProcSpawn(const AExe, AArgs, AEnv, ACwd: string; AUseEnv: Int32;
  AFds, AChild: Pointer): Int32; external name '_ProcSpawn';
function _ProcWait(AChild: Int64; ABlock: Int32; AExitCode: Pointer): Int32;
  external name '_ProcWait';
function _ProcSignal(AChild: Int64; AForce: Int32): Int32;
  external name '_ProcSignal';
function _ProcPid(AChild: Int64): Int32; external name '_ProcPid';
procedure _ProcRelease(AChild: Int64); external name '_ProcRelease';
function _ProcPollRead(AFds: Pointer; ACount, ATimeoutMs: Int32;
  AReady: Pointer): Int32; external name '_ProcPollRead';
function _FdRead(AFd: Int32; ABuf: Pointer; ACount: Int): Int;
  external name '_FdRead';
function _FdWrite(AFd: Int32; ABuf: Pointer; ACount: Int): Int;
  external name '_FdWrite';
function _FsClose(AFd: Int32): Int32; external name '_FsClose';
{ errno, per build profile (runtime.errno.*, chosen at link time). }
function Interrupted(N: Int64): Boolean; external name 'Interrupted';

{ The text of the errors a start reports; the numbers are the POSIX ones
  on every target.  strerror is not available without libc. }
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
    24: Result := 'Too many open files';
    26: Result := 'Text file busy';
  else
    Result := 'error ' + IntToStr(AErr);
  end;
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

{ ---------------------------------------------------------------------------
  TSubprocess
  --------------------------------------------------------------------------- }

constructor TSubprocess.Create(const AExecutable: string);
begin
  FExecutable := AExecutable;
  FArgs := TList<string>.Create();
  FStarted := False;
  FIn := -1;
  FOut := -1;
  FErr := -1;
end;

function TSubprocess.GetEnvironment(): TDictionary<string, string>;
var
  I, Eq: Int;
  Entry: string;
begin
  if FEnvironment = nil then
  begin
    FEnvironment := TDictionary<string, string>.Create();
    for I := 0 to GetEnvironmentVariableCount() - 1 do
    begin
      Entry := GetEnvironmentString(I);
      Eq := Pos('=', Entry);
      if Eq > 0 then
        FEnvironment.SetItem(Copy(Entry, 0, Eq),
          Copy(Entry, Eq + 1, Length(Entry) - Eq - 1));
    end;
  end;
  Result := FEnvironment;
end;

destructor TSubprocess.Destroy;
begin
  CloseInput();
  if FOut >= 0 then _FsClose(FOut);
  if FErr >= 0 then _FsClose(FErr);
  { Reap a child that has already gone, so it does not linger as a zombie;
    a running child is left running. }
  if FStarted then
  begin
    Running();
    _ProcRelease(FChild);
  end;
  inherited Destroy();
end;

procedure TSubprocess.Start();
var
  Args, Env: TStringBuilder;
  Key, Reason: string;
  I: Int;
  UseEnv, E: Int32;
  Fds: array[0..2] of Int32;
  Child: Int64;
begin
  if FStarted then
    raise EProcessStartError.Create('process already started');
  { the arguments, then the environment, as #0-ended items }
  Args := TStringBuilder.Create();
  for I := 0 to FArgs.Count - 1 do
  begin
    Args.Append(FArgs[I]);
    Args.AppendByte(0);
  end;
  Env := TStringBuilder.Create();
  UseEnv := 0;
  if FEnvironment <> nil then
  begin
    UseEnv := 1;
    for Key in FEnvironment.Keys() do
    begin
      Env.Append(Key + '=' + FEnvironment[Key]);
      Env.AppendByte(0);
    end;
  end;
  Child := 0;
  E := _ProcSpawn(FExecutable, Args.ToString(), Env.ToString(),
    FWorkingDirectory, UseEnv, @Fds[0], @Child);
  if E <> 0 then
  begin
    Reason := ErrorText(E);
    if (FWorkingDirectory <> '') and (E = ENOENT) then
      Reason := Reason + ' (program or working directory ' + FWorkingDirectory + ')';
    raise EProcessStartError.Create('cannot start ' + FExecutable + ': ' + Reason);
  end;
  FStarted := True;
  FChild := Child;
  FIn := Fds[0];
  FOut := Fds[1];
  FErr := Fds[2];
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
    N := _FdWrite(FIn, P, Left);
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
    _FsClose(FIn);
    FIn := -1;
  end;
end;

function TSubprocess.Read(ATimeoutMs: Int32; out AOutput, AError: string): Boolean;
var
  Fds: array[0..1] of Int32;
  Ready: array[0..1] of Int32;
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
    Fds[Count] := FOut;
    Map[Count] := 0;
    Count := Count + 1;
  end;
  if FErr >= 0 then
  begin
    Fds[Count] := FErr;
    Map[Count] := 1;
    Count := Count + 1;
  end;
  if Count = 0 then
    Exit(False);
  Result := True;
  R := _ProcPollRead(@Fds[0], Count, ATimeoutMs, @Ready[0]);
  if R <= 0 then
    Exit;   { timeout, or EINTR: the caller polls again }
  Buf := GetMem(ReadChunk);
  for I := 0 to Count - 1 do
    if Ready[I] <> 0 then
    begin
      repeat
        N := _FdRead(Fds[I], Buf, ReadChunk);
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
        _FsClose(Fds[I]);
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

function TSubprocess.Running(): Boolean;
var
  Code, R: Int32;
begin
  if (not FStarted) or FExited then
    Exit(False);
  Code := 0;
  R := _ProcWait(FChild, 0, @Code);
  if R = 1 then
  begin
    FExited := True;
    FExitCode := Code;
    Exit(False);
  end;
  Result := R = 0;
end;

function TSubprocess.WaitForExit(): Int32;
var
  Code: Int32;
begin
  if FStarted and not FExited then
  begin
    CloseInput();
    Code := 0;
    if _ProcWait(FChild, 1, @Code) = 1 then
      FExitCode := Code;
    FExited := True;
  end;
  Result := FExitCode;
end;

procedure TSubprocess.Terminate();
begin
  if FStarted and not FExited then
    _ProcSignal(FChild, 0);
end;

procedure TSubprocess.Kill();
begin
  if FStarted and not FExited then
    _ProcSignal(FChild, 1);
end;

function TSubprocess.Pid(): Int32;
begin
  Result := -1;
  if FStarted then
    Result := _ProcPid(FChild);
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
