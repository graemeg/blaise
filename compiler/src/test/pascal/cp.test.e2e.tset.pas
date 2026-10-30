{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tset;

{ E2E tests for TSet<T>: compile -> QBE -> cc -> run, assert on stdout.
  Verifies that Include deduplicates, Exclude removes, Contains tests
  membership, and Count tracks correctly. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ESetTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TSet_IncludeDeduplicates;
    procedure TestRun_TSet_ExcludeRemoves;
    procedure TestRun_TSet_ContainsMembership;
    procedure TestRun_TSet_CountTracking;
  end;

implementation

const
  SetSrc =
    '''
    program P;
    type
      TSet = class
        FData:     ^Int;
        FCount:    Int;
        FCapacity: Int;
        procedure Grow;
        var NewCap, OldCap: Int;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;
          Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Int));
          ZeroMem(Self.FData + OldCap * SizeOf(Int), (NewCap - OldCap) * SizeOf(Int));
          Self.FCapacity := NewCap
        end;
        function IndexOf(Value: Int): Int;
        var I: Int; Ptr: ^Int;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do
          begin
            Ptr := Self.FData + I * SizeOf(Int);
            if Ptr^ = Value then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure Include(Value: Int);
        var Dest: ^Int;
        begin
          if Self.IndexOf(Value) >= 0 then Exit;
          if Self.FCount = Self.FCapacity then Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(Int);
          Dest^       := Value;
          Self.FCount := Self.FCount + 1
        end;
        procedure Exclude(Value: Int);
        var Idx, I: Int; Dst, Src: ^Int;
        begin
          Idx := Self.IndexOf(Value);
          if Idx < 0 then Exit;
          I := Idx;
          while I < Self.FCount - 1 do
          begin
            Dst  := Self.FData + I * SizeOf(Int);
            Src  := Self.FData + (I + 1) * SizeOf(Int);
            Dst^ := Src^;
            I    := I + 1
          end;
          Self.FCount := Self.FCount - 1
        end;
        function Contains(Value: Int): Boolean;
        begin
          Result := Self.IndexOf(Value) >= 0
        end;
        property Count: Int read FCount;
      end;
    ''';

  SrcDeduplicate =
    SetSrc +
    '''
    var S: TSet;
    begin
      S := TSet.Create();
      S.Include(5); S.Include(5); S.Include(5);
      WriteLn(S.Count)
    end.
    ''';

  SrcExclude =
    SetSrc +
    '''
    var S: TSet;
    begin
      S := TSet.Create();
      S.Include(1); S.Include(2); S.Include(3);
      S.Exclude(2);
      WriteLn(S.Count);
      WriteLn(S.Contains(2))
    end.
    ''';

  SrcContains =
    SetSrc +
    '''
    var S: TSet;
    begin
      S := TSet.Create();
      S.Include(42);
      WriteLn(S.Contains(42));
      WriteLn(S.Contains(99))
    end.
    ''';

  SrcCountTracking =
    SetSrc +
    '''
    var S: TSet;
    begin
      S := TSet.Create();
      WriteLn(S.Count);
      S.Include(10); S.Include(20); S.Include(30);
      WriteLn(S.Count);
      S.Exclude(20);
      WriteLn(S.Count)
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2ESetTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-tset')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2ESetTests.TestRun_TSet_IncludeDeduplicates;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcDeduplicate, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count=1 after three identical includes', Pos('1', Output) >= 0);
end;

procedure TE2ESetTests.TestRun_TSet_ExcludeRemoves;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcExclude, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count=2 after exclude', Pos('2', Output) >= 0);
  { Boolean false prints as False in Blaise }
  AssertTrue('contains returns false (False)', Pos('False', Output) >= 0);
end;

procedure TE2ESetTests.TestRun_TSet_ContainsMembership;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcContains, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  { Boolean true prints as True, false as False in Blaise }
  AssertTrue('contains 42 -> true (True)',  Pos('True', Output) >= 0);
  AssertTrue('contains 99 -> false (False)', Pos('False', Output) >= 0);
end;

procedure TE2ESetTests.TestRun_TSet_CountTracking;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcCountTracking, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('starts at 0', Pos('0', Output) >= 0);
  AssertTrue('3 after three includes', Pos('3', Output) >= 0);
  AssertTrue('2 after exclude', Pos('2', Output) >= 0);
end;

initialization
  RegisterTest(TE2ESetTests);

end.
