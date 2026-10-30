{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tqueue;

{ E2E tests for TQueue<T>: compile -> QBE -> cc -> run, assert on stdout.
  Verifies FIFO ordering, Peek, Count tracking, and correct behaviour
  after Grow (circular buffer wrap). }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EQueueTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TQueue_EnqueueDequeueFIFO;
    procedure TestRun_TQueue_PeekDoesNotRemove;
    procedure TestRun_TQueue_CountTracking;
    procedure TestRun_TQueue_GrowBeyondInitialCapacity;
  end;

implementation

const
  QueueSrc =
    '''
    program P;
    type
      TQueue = class
        FData:     ^Int;
        FCount:    Int;
        FCapacity: Int;
        FHead:     Int;
        FTail:     Int;
        procedure Grow;
        var NewCap, OldCap, I: Int; NewData, Src, Dst: ^Int;
        begin
          OldCap  := Self.FCapacity;
          if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;
          NewData := GetMem(NewCap * SizeOf(Int));
          ZeroMem(NewData, NewCap * SizeOf(Int));
          I := 0;
          while I < Self.FCount do
          begin
            Src  := Self.FData + ((Self.FHead + I) mod OldCap) * SizeOf(Int);
            Dst  := NewData + I * SizeOf(Int);
            Dst^ := Src^;
            I    := I + 1
          end;
          FreeMem(Self.FData);
          Self.FData     := NewData;
          Self.FHead     := 0;
          Self.FTail     := Self.FCount;
          Self.FCapacity := NewCap
        end;
        procedure Enqueue(Value: Int);
        var Dest: ^Int;
        begin
          if Self.FCount = Self.FCapacity then Self.Grow();
          Dest        := Self.FData + Self.FTail * SizeOf(Int);
          Dest^       := Value;
          Self.FTail  := (Self.FTail + 1) mod Self.FCapacity;
          Self.FCount := Self.FCount + 1
        end;
        function Dequeue: Int;
        var Src: ^Int;
        begin
          Src         := Self.FData + Self.FHead * SizeOf(Int);
          Result      := Src^;
          Self.FHead  := (Self.FHead + 1) mod Self.FCapacity;
          Self.FCount := Self.FCount - 1
        end;
        function Peek: Int;
        var Src: ^Int;
        begin
          Src    := Self.FData + Self.FHead * SizeOf(Int);
          Result := Src^
        end;
        property Count: Int read FCount;
      end;
    ''';

  SrcFIFO =
    QueueSrc +
    '''
    var Q: TQueue;
    begin
      Q := TQueue.Create();
      Q.Enqueue(10);
      Q.Enqueue(20);
      Q.Enqueue(30);
      WriteLn(Q.Dequeue());
      WriteLn(Q.Dequeue());
      WriteLn(Q.Dequeue())
    end.
    ''';

  SrcPeekNoRemove =
    QueueSrc +
    '''
    var Q: TQueue;
    begin
      Q := TQueue.Create();
      Q.Enqueue(7);
      WriteLn(Q.Peek());
      WriteLn(Q.Peek());
      WriteLn(Q.Count)
    end.
    ''';

  SrcCountTracking =
    QueueSrc +
    '''
    var Q: TQueue;
    begin
      Q := TQueue.Create();
      WriteLn(Q.Count);
      Q.Enqueue(1);
      Q.Enqueue(2);
      WriteLn(Q.Count);
      Q.Dequeue();
      WriteLn(Q.Count)
    end.
    ''';

  SrcGrowBeyond =
    QueueSrc +
    '''
    var Q: TQueue; I: Int;
    begin
      Q := TQueue.Create();
      I := 1;
      while I <= 8 do begin Q.Enqueue(I); I := I + 1 end;
      WriteLn(Q.Count);
      WriteLn(Q.Dequeue());
      WriteLn(Q.Dequeue())
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EQueueTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-tqueue')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EQueueTests.TestRun_TQueue_EnqueueDequeueFIFO;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcFIFO, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Dequeue returns 10 first (FIFO)', Pos('10', Output) >= 0);
  AssertTrue('Dequeue returns 20 second',        Pos('20', Output) >= 0);
  AssertTrue('Dequeue returns 30 last',          Pos('30', Output) >= 0);
end;

procedure TE2EQueueTests.TestRun_TQueue_PeekDoesNotRemove;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcPeekNoRemove, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Peek returns 7', Pos('7', Output) >= 0);
  AssertTrue('Count remains 1', Pos('1', Output) >= 0);
end;

procedure TE2EQueueTests.TestRun_TQueue_CountTracking;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcCountTracking, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('starts at 0', Pos('0', Output) >= 0);
  AssertTrue('2 after two enqueues', Pos('2', Output) >= 0);
end;

procedure TE2EQueueTests.TestRun_TQueue_GrowBeyondInitialCapacity;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcGrowBeyond, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count=8', Pos('8', Output) >= 0);
  AssertTrue('first dequeue=1', Pos('1', Output) >= 0);
  AssertTrue('second dequeue=2', Pos('2', Output) >= 0);
end;

initialization
  RegisterTest(TE2EQueueTests);

end.
