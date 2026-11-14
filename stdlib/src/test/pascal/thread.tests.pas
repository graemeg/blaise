{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Classes.TThread: its lifetime rule (releasing the last reference
  terminates and joins a running thread; FreeOnTerminate opts into the
  thread holding its own reference) and the misuse it reports.  The
  end-to-end runs, including the destroy-on-the-worker path, are in the
  compiler's cp.test.e2e.threading.  Self-registers via the initialization
  section. }

unit Thread.Tests;

interface

uses
  blaise.testing, Classes, SysUtils;

type
  TThreadTests = class(TTestCase)
  published
    procedure TestFreeOnTerminate_DefaultsToFalse;
    procedure TestFreeOnTerminate_SetBeforeStart_Accepted;
    procedure TestFreeOnTerminate_SetAfterStart_Raises;
    procedure TestFreeOnTerminate_SetInSubclassConstructor_Accepted;
    procedure TestWaitFor_FromTheThreadItself_Raises;
    procedure TestRelease_AfterExecuteBegan_TerminatesAndJoins;
  end;

implementation

type
  TIdleThread = class(TThread)
  protected
    procedure Execute; override;
  end;

  { Calls WaitFor on itself and records whether it raised. }
  TSelfWaitThread = class(TThread)
  protected
    procedure Execute; override;
  public
    Raised: Boolean;
  end;

  { Loops until Terminated; reports through globals, since the instance is
    gone by the time the test looks. }
  TLoopThread = class(TThread)
  protected
    procedure Execute; override;
  end;

  { The Delphi idiom: FreeOnTerminate set in the constructor, after
    inherited Create(False) -- the thread has not started yet then. }
  TSelfFreeingThread = class(TThread)
  protected
    procedure Execute; override;
  public
    Accepted: Boolean;
    constructor Create;
  end;

var
  SelfFreeingDone: Boolean;
  LoopStarted: Boolean;
  LoopSawTerminated: Boolean;

procedure TIdleThread.Execute;
begin
end;

procedure TSelfWaitThread.Execute;
begin
  try
    Self.WaitFor();
  except
    on E: Exception do
      Self.Raised := True
  end
end;

constructor TSelfFreeingThread.Create;
begin
  inherited Create(False);
  try
    Self.FreeOnTerminate := True;
    Self.Accepted := True
  except
    on E: Exception do
      Self.Accepted := False
  end
end;

procedure TSelfFreeingThread.Execute;
begin
  SelfFreeingDone := Self.Accepted
end;

procedure TLoopThread.Execute;
var
  I: Int;
begin
  LoopStarted := True;
  I := 0;
  while not Self.Terminated do
  begin
    I := I + 1;
    if I > 2000000000 then
      break
  end;
  LoopSawTerminated := Self.Terminated
end;

procedure TThreadTests.TestFreeOnTerminate_DefaultsToFalse;
var
  T: TIdleThread;
begin
  T := TIdleThread.Create(True);
  AssertFalse('default', T.FreeOnTerminate)
end;

procedure TThreadTests.TestFreeOnTerminate_SetBeforeStart_Accepted;
var
  T: TIdleThread;
begin
  T := TIdleThread.Create(True);
  T.FreeOnTerminate := True;
  AssertTrue('set', T.FreeOnTerminate);
  T.FreeOnTerminate := False;
  AssertFalse('cleared', T.FreeOnTerminate)
end;

procedure TThreadTests.TestFreeOnTerminate_SetAfterStart_Raises;
var
  T: TIdleThread;
  Raised: Boolean;
begin
  T := TIdleThread.Create(False);
  Raised := False;
  try
    T.FreeOnTerminate := True
  except
    on E: Exception do
      Raised := True
  end;
  AssertTrue('raised', Raised);
  AssertFalse('unchanged', T.FreeOnTerminate)
end;

procedure TThreadTests.TestFreeOnTerminate_SetInSubclassConstructor_Accepted;
var
  T: TSelfFreeingThread;
  I: Int;
begin
  SelfFreeingDone := False;
  T := TSelfFreeingThread.Create();
  T := nil;
  { the thread frees itself; wait for it to report, up to two seconds }
  I := 0;
  while (not SelfFreeingDone) and (I < 200) do
  begin
    Sleep(10);
    I := I + 1
  end;
  AssertTrue('accepted in the constructor', SelfFreeingDone)
end;

procedure TThreadTests.TestWaitFor_FromTheThreadItself_Raises;
var
  T: TSelfWaitThread;
begin
  T := TSelfWaitThread.Create(False);
  T.WaitFor();
  AssertTrue('raised', T.Raised)
end;

procedure TThreadTests.TestRelease_AfterExecuteBegan_TerminatesAndJoins;
var
  T: TLoopThread;
begin
  LoopStarted := False;
  LoopSawTerminated := False;
  T := TLoopThread.Create(False);
  while not LoopStarted do ;
  { the last reference: Destroy terminates the loop and joins the thread,
    so its result is visible once the assignment returns }
  T := nil;
  AssertTrue('terminated and joined', LoopSawTerminated)
end;

initialization
  RegisterTest(TThreadTests);

end.
