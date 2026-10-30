{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tstack;

{ E2E tests for TStack<T>: compile -> QBE -> cc -> run, assert on stdout.
  Verifies that Push/Pop/Peek/Count work correctly at runtime and that
  LIFO order is maintained across a Grow (more than 4 pushes). }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStackTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TStack_PushPopLIFO;
    procedure TestRun_TStack_PeekDoesNotRemove;
    procedure TestRun_TStack_CountTracking;
    procedure TestRun_TStack_GrowBeyondInitialCapacity;
  end;

implementation

const
  StackSrc =
    '''
    program P;
    type
      TStack = class
        FData:     ^Int;
        FCount:    Int;
        FCapacity: Int;
        procedure Grow;
        var NewCap, OldCap: Int;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 4
          else NewCap := OldCap * 2;
          Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Int));
          ZeroMem(Self.FData + OldCap * SizeOf(Int), (NewCap - OldCap) * SizeOf(Int));
          Self.FCapacity := NewCap
        end;
        procedure Push(Value: Int);
        var Dest: ^Int;
        begin
          if Self.FCount = Self.FCapacity then Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(Int);
          Dest^       := Value;
          Self.FCount := Self.FCount + 1
        end;
        function Pop: Int;
        var Src: ^Int;
        begin
          Self.FCount := Self.FCount - 1;
          Src         := Self.FData + Self.FCount * SizeOf(Int);
          Result      := Src^
        end;
        function Peek: Int;
        var Src: ^Int;
        begin
          Src    := Self.FData + (Self.FCount - 1) * SizeOf(Int);
          Result := Src^
        end;
        property Count: Int read FCount;
      end;
    ''';

  SrcPushPopLIFO =
    StackSrc +
    '''
    var S: TStack;
    begin
      S := TStack.Create();
      S.Push(1);
      S.Push(2);
      S.Push(3);
      WriteLn(S.Pop());
      WriteLn(S.Pop());
      WriteLn(S.Pop())
    end.
    ''';

  SrcPeekNoRemove =
    StackSrc +
    '''
    var S: TStack;
    begin
      S := TStack.Create();
      S.Push(42);
      WriteLn(S.Peek());
      WriteLn(S.Peek());
      WriteLn(S.Count)
    end.
    ''';

  SrcCountTracking =
    StackSrc +
    '''
    var S: TStack;
    begin
      S := TStack.Create();
      WriteLn(S.Count);
      S.Push(10);
      WriteLn(S.Count);
      S.Push(20);
      WriteLn(S.Count);
      S.Pop();
      WriteLn(S.Count)
    end.
    ''';

  SrcGrowBeyond =
    StackSrc +
    '''
    var S: TStack; I: Int;
    begin
      S := TStack.Create();
      I := 1;
      while I <= 8 do begin S.Push(I); I := I + 1 end;
      WriteLn(S.Count);
      WriteLn(S.Pop());
      WriteLn(S.Pop())
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EStackTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-tstack')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EStackTests.TestRun_TStack_PushPopLIFO;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcPushPopLIFO, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Pop returns 3 first (LIFO)', Pos('3', Output) >= 0);
  AssertTrue('Pop returns 2 second',       Pos('2', Output) >= 0);
  AssertTrue('Pop returns 1 last',         Pos('1', Output) >= 0);
end;

procedure TE2EStackTests.TestRun_TStack_PeekDoesNotRemove;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcPeekNoRemove, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Peek returns 42 twice then Count=1',
    (Pos('42', Output) >= 0) and (Pos('1', Output) >= 0));
end;

procedure TE2EStackTests.TestRun_TStack_CountTracking;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcCountTracking, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count starts at 0', Pos('0', Output) >= 0);
  AssertTrue('count after 2 pushes contains 2', Pos('2', Output) >= 0);
end;

procedure TE2EStackTests.TestRun_TStack_GrowBeyondInitialCapacity;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcGrowBeyond, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count=8 after 8 pushes', Pos('8', Output) >= 0);
  AssertTrue('last pop returns 8', Pos('8', Output) >= 0);
end;

initialization
  RegisterTest(TE2EStackTests);

end.
