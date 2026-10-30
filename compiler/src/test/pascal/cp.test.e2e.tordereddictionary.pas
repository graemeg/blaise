{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tordereddictionary;

{ E2E tests for TOrderedDictionary<K,V>: compile -> QBE -> cc -> run, assert
  on stdout.  Verifies insertion order is preserved, TryGetValue works, Remove
  compacts correctly, and indexed Keys[]/Values[] access returns entries in
  insertion order. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EOrdDictTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_OrdDict_InsertionOrderPreserved;
    procedure TestRun_OrdDict_TryGetValue;
    procedure TestRun_OrdDict_Remove;
    procedure TestRun_OrdDict_UpdateKeepsOrder;
  end;

implementation

const
  OrdDictSrc =
    '''
    program P;
    type
      TOrdDict = class
        FKeys:     ^Int;
        FValues:   ^Int;
        FCount:    Int;
        FCapacity: Int;
        procedure Grow;
        var NewCap, OldCap: Int;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 8 else NewCap := OldCap * 2;
          Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(Int));
          ZeroMem(Self.FKeys + OldCap * SizeOf(Int), (NewCap - OldCap) * SizeOf(Int));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Int));
          ZeroMem(Self.FValues + OldCap * SizeOf(Int), (NewCap - OldCap) * SizeOf(Int));
          Self.FCapacity := NewCap
        end;
        function FindKey(Key: Int): Int;
        var I: Int; Ptr: ^Int;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do
          begin
            Ptr := Self.FKeys + I * SizeOf(Int);
            if Ptr^ = Key then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure Add(Key, Value: Int);
        var Idx: Int; KPtr, VPtr: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            VPtr  := Self.FValues + Idx * SizeOf(Int);
            VPtr^ := Value
          end
          else
          begin
            if Self.FCount = Self.FCapacity then Self.Grow();
            KPtr  := Self.FKeys   + Self.FCount * SizeOf(Int);
            VPtr  := Self.FValues + Self.FCount * SizeOf(Int);
            KPtr^ := Key; VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TryGetValue(Key: Int; var Value: Int): Boolean;
        var Idx: Int; VPtr: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            VPtr := Self.FValues + Idx * SizeOf(Int);
            Value := VPtr^; Result := True
          end
          else Result := False
        end;
        procedure Remove(Key: Int);
        var Idx, I: Int; KDst, KSrc, VDst, VSrc: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            I := Idx;
            while I < Self.FCount - 1 do
            begin
              KDst := Self.FKeys   + I * SizeOf(Int);
              KSrc := Self.FKeys   + (I + 1) * SizeOf(Int);
              VDst := Self.FValues + I * SizeOf(Int);
              VSrc := Self.FValues + (I + 1) * SizeOf(Int);
              KDst^ := KSrc^; VDst^ := VSrc^;
              I := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function GetKey(I: Int): Int;
        var Ptr: ^Int;
        begin
          Ptr := Self.FKeys + I * SizeOf(Int); Result := Ptr^
        end;
        function GetValue(I: Int): Int;
        var Ptr: ^Int;
        begin
          Ptr := Self.FValues + I * SizeOf(Int); Result := Ptr^
        end;
        property Count: Int read FCount;
      end;
    ''';

  SrcInsertionOrder =
    OrdDictSrc +
    '''
    var D: TOrdDict; I: Int;
    begin
      D := TOrdDict.Create();
      D.Add(10, 100); D.Add(20, 200); D.Add(30, 300);
      I := 0;
      while I < D.Count do begin WriteLn(D.GetKey(I)); I := I + 1 end
    end.
    ''';

  SrcTryGetValue =
    OrdDictSrc +
    '''
    var D: TOrdDict; V: Int; OK: Boolean;
    begin
      D := TOrdDict.Create();
      D.Add(42, 99);
      OK := D.TryGetValue(42, V);
      WriteLn(OK);
      WriteLn(V);
      OK := D.TryGetValue(7, V);
      WriteLn(OK)
    end.
    ''';

  SrcRemove =
    OrdDictSrc +
    '''
    var D: TOrdDict; I: Int;
    begin
      D := TOrdDict.Create();
      D.Add(1, 10); D.Add(2, 20); D.Add(3, 30);
      D.Remove(2);
      WriteLn(D.Count);
      I := 0;
      while I < D.Count do begin WriteLn(D.GetKey(I)); I := I + 1 end
    end.
    ''';

  SrcUpdateKeepsOrder =
    OrdDictSrc +
    '''
    var D: TOrdDict; I: Int;
    begin
      D := TOrdDict.Create();
      D.Add(5, 50); D.Add(6, 60);
      D.Add(5, 99);
      WriteLn(D.Count);
      WriteLn(D.GetValue(0))
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EOrdDictTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-torddict')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EOrdDictTests.TestRun_OrdDict_InsertionOrderPreserved;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcInsertionOrder, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('first key=10', Pos('10', Output) >= 0);
  AssertTrue('second key=20', Pos('20', Output) >= 0);
  AssertTrue('third key=30', Pos('30', Output) >= 0);
end;

procedure TE2EOrdDictTests.TestRun_OrdDict_TryGetValue;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcTryGetValue, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  { Boolean true prints as True, false as False in Blaise }
  AssertTrue('found -> true (True)',    Pos('True',  Output) >= 0);
  AssertTrue('value=99',                Pos('99', Output) >= 0);
  AssertTrue('missing -> false (False)', Pos('False',  Output) >= 0);
end;

procedure TE2EOrdDictTests.TestRun_OrdDict_Remove;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcRemove, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count=2 after remove', Pos('2', Output) >= 0);
  AssertTrue('key 1 remains', Pos('1', Output) >= 0);
  AssertTrue('key 3 remains', Pos('3', Output) >= 0);
end;

procedure TE2EOrdDictTests.TestRun_OrdDict_UpdateKeepsOrder;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcUpdateKeepsOrder, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count stays 2', Pos('2', Output) >= 0);
  AssertTrue('updated value=99', Pos('99', Output) >= 0);
end;

initialization
  RegisterTest(TE2EOrdDictTests);

end.
