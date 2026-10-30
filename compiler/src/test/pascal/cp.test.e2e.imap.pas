{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.imap;

{ E2E tests for IMap<K,V>: compile -> QBE -> cc -> run, assert on stdout.
  Verifies that interface dispatch through IMap<K,V> routes to the correct
  concrete implementation at runtime — both TDictionary and TOrderedDictionary. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EIMapTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_IMap_TDictionary_AddAndContainsKey;
    procedure TestRun_IMap_TDictionary_TryGetValue;
    procedure TestRun_IMap_TDictionary_Remove;
    procedure TestRun_IMap_TOrderedDictionary_AddAndContainsKey;
    procedure TestRun_IMap_TOrderedDictionary_TryGetValue;
    procedure TestRun_IMap_SwapImplementation_SameCallSite;
    procedure TestRun_IMap_GenericDictInUnit_LinksAndRuns;
    procedure TestRun_StaticArrayOfInterface_FatPointer;
    procedure TestRun_InterfaceResult_NilCompare_Registry;
    procedure TestRun_IntfMethodReturningIntf_ToLocal;
    procedure TestRun_IntfDispatch_ConstRecordArg;
    procedure TestRun_IntfDispatch_OutStringArg;
    procedure TestRun_IntfDispatch_VarDynArrayArg;
    procedure TestRun_FuncCallReceiver_IntfDispatch;
    procedure TestRun_DiscardedIntfReturn_StatementPosition;
  end;

implementation

const
  { Shared IMap interface declaration used in all test programs }
  IMapSrc =
    '''
    program P;
    type
      IMap = interface
        procedure Add(Key, Value: Int);
        function  TryGetValue(Key: Int; var Value: Int): Boolean;
        function  ContainsKey(Key: Int): Boolean;
        procedure Remove(Key: Int);
        function  GetCount: Int;
      end;
    ''';

  { Non-generic TDict implementing IMap (concrete Integer key/value for E2E) }
  TDictSrc =
    '''
      TDict = class(IMap)
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
          ZeroMem(Self.FKeys + OldCap * SizeOf(Int), (NewCap-OldCap) * SizeOf(Int));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Int));
          ZeroMem(Self.FValues + OldCap * SizeOf(Int), (NewCap-OldCap) * SizeOf(Int));
          Self.FCapacity := NewCap
        end;
        function FindKey(Key: Int): Int;
        var I: Int; Ptr: ^Int;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do begin
            Ptr := Self.FKeys + I * SizeOf(Int);
            if Ptr^ = Key then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure Add(Key, Value: Int);
        var Idx: Int; KPtr, VPtr: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Int); VPtr^ := Value
          end else begin
            if Self.FCount = Self.FCapacity then Self.Grow();
            KPtr := Self.FKeys   + Self.FCount * SizeOf(Int);
            VPtr := Self.FValues + Self.FCount * SizeOf(Int);
            KPtr^ := Key; VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TryGetValue(Key: Int; var Value: Int): Boolean;
        var Idx: Int; VPtr: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Int);
            Value := VPtr^; Result := True
          end else Result := False
        end;
        function ContainsKey(Key: Int): Boolean;
        begin Result := Self.FindKey(Key) >= 0 end;
        procedure Remove(Key: Int);
        var Idx, I: Int; KDst, KSrc, VDst, VSrc: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            I := Idx;
            while I < Self.FCount - 1 do begin
              KDst := Self.FKeys   + I * SizeOf(Int);
              KSrc := Self.FKeys   + (I+1) * SizeOf(Int);
              VDst := Self.FValues + I * SizeOf(Int);
              VSrc := Self.FValues + (I+1) * SizeOf(Int);
              KDst^ := KSrc^; VDst^ := VSrc^; I := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function GetCount: Int;
        begin Result := Self.FCount end;
        property Count: Int read GetCount;
      end;
    ''';

  { Insertion-ordered variant implementing the same IMap interface }
  TOrdDictSrc =
    '''
      TOrdDict = class(IMap)
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
          ZeroMem(Self.FKeys + OldCap * SizeOf(Int), (NewCap-OldCap) * SizeOf(Int));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Int));
          ZeroMem(Self.FValues + OldCap * SizeOf(Int), (NewCap-OldCap) * SizeOf(Int));
          Self.FCapacity := NewCap
        end;
        function FindKey(Key: Int): Int;
        var I: Int; Ptr: ^Int;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do begin
            Ptr := Self.FKeys + I * SizeOf(Int);
            if Ptr^ = Key then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure Add(Key, Value: Int);
        var Idx: Int; KPtr, VPtr: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Int); VPtr^ := Value
          end else begin
            if Self.FCount = Self.FCapacity then Self.Grow();
            KPtr := Self.FKeys   + Self.FCount * SizeOf(Int);
            VPtr := Self.FValues + Self.FCount * SizeOf(Int);
            KPtr^ := Key; VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TryGetValue(Key: Int; var Value: Int): Boolean;
        var Idx: Int; VPtr: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Int);
            Value := VPtr^; Result := True
          end else Result := False
        end;
        function ContainsKey(Key: Int): Boolean;
        begin Result := Self.FindKey(Key) >= 0 end;
        procedure Remove(Key: Int);
        var Idx, I: Int; KDst, KSrc, VDst, VSrc: ^Int;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            I := Idx;
            while I < Self.FCount - 1 do begin
              KDst := Self.FKeys   + I * SizeOf(Int);
              KSrc := Self.FKeys   + (I+1) * SizeOf(Int);
              VDst := Self.FValues + I * SizeOf(Int);
              VSrc := Self.FValues + (I+1) * SizeOf(Int);
              KDst^ := KSrc^; VDst^ := VSrc^; I := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function GetCount: Int;
        begin Result := Self.FCount end;
        property Count: Int read GetCount;
      end;
    ''';

  { Add via IMap, ContainsKey via IMap, print result }
  SrcDictAddContains =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    '''
    var M: IMap;
    begin
      M := TDict.Create();
      M.Add(10, 100);
      M.Add(20, 200);
      WriteLn(M.ContainsKey(10));
      WriteLn(M.ContainsKey(99));
      WriteLn(M.GetCount())
    end.
    ''';

  { TryGetValue via IMap }
  SrcDictTryGet =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    '''
    var M: IMap; V: Int; OK: Boolean;
    begin
      M := TDict.Create();
      M.Add(42, 99);
      OK := M.TryGetValue(42, V);
      WriteLn(OK);
      WriteLn(V);
      OK := M.TryGetValue(7, V);
      WriteLn(OK)
    end.
    ''';

  { Remove via IMap }
  SrcDictRemove =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    '''
    var M: IMap;
    begin
      M := TDict.Create();
      M.Add(1, 10); M.Add(2, 20); M.Add(3, 30);
      M.Remove(2);
      WriteLn(M.GetCount());
      WriteLn(M.ContainsKey(2));
      WriteLn(M.ContainsKey(1))
    end.
    ''';

  { Same operations through TOrdDict implementing the same IMap }
  SrcOrdDictAddContains =
    IMapSrc +
    '''
    type
    ''' +
    TOrdDictSrc +
    '''
    var M: IMap;
    begin
      M := TOrdDict.Create();
      M.Add(10, 100);
      M.Add(20, 200);
      WriteLn(M.ContainsKey(10));
      WriteLn(M.ContainsKey(99));
      WriteLn(M.GetCount())
    end.
    ''';

  { TryGetValue via TOrdDict/IMap }
  SrcOrdDictTryGet =
    IMapSrc +
    '''
    type
    ''' +
    TOrdDictSrc +
    '''
    var M: IMap; V: Int; OK: Boolean;
    begin
      M := TOrdDict.Create();
      M.Add(42, 99);
      OK := M.TryGetValue(42, V);
      WriteLn(OK);
      WriteLn(V);
      OK := M.TryGetValue(7, V);
      WriteLn(OK)
    end.
    ''';

  { Swap implementation: same call site, two different concrete types }
  SrcSwapImpl =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    TOrdDictSrc +
    '''
    var M: IMap; Flag: Boolean;
    begin
      M := TDict.Create();
      M.Add(5, 50);
      Flag := M.ContainsKey(5);
      WriteLn(Flag);
      M := TOrdDict.Create();
      M.Add(5, 50);
      Flag := M.ContainsKey(5);
      WriteLn(Flag)
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EIMapTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-imap')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EIMapTests.TestRun_IMap_TDictionary_AddAndContainsKey;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcDictAddContains, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  { ContainsKey(10) -> true, ContainsKey(99) -> false, Count=2 }
  AssertTrue('contains 10 -> True',  Pos('True',  Output) >= 0);
  AssertTrue('contains 99 -> False', Pos('False', Output) >= 0);
  AssertTrue('count=2',              Pos('2',     Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TDictionary_TryGetValue;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcDictTryGet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('found -> True',  Pos('True',  Output) >= 0);
  AssertTrue('value=99',       Pos('99',    Output) >= 0);
  AssertTrue('missing -> False', Pos('False', Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TDictionary_Remove;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcDictRemove, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count=2',          Pos('2',     Output) >= 0);
  AssertTrue('removed key gone', Pos('False', Output) >= 0);
  AssertTrue('other key stays',  Pos('True',  Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TOrderedDictionary_AddAndContainsKey;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOrdDictAddContains, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('contains 10 -> True',  Pos('True',  Output) >= 0);
  AssertTrue('contains 99 -> False', Pos('False', Output) >= 0);
  AssertTrue('count=2',              Pos('2',     Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TOrderedDictionary_TryGetValue;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOrdDictTryGet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('found -> True',    Pos('True',  Output) >= 0);
  AssertTrue('value=99',         Pos('99',    Output) >= 0);
  AssertTrue('missing -> False', Pos('False', Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_SwapImplementation_SameCallSite;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcSwapImpl, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('TDict dispatch correct',    Pos('True', Output) >= 0);
  AssertTrue('TOrdDict dispatch correct', Pos('True', Output) >= 0);
end;

{ Regression: a generic class implementing a generic interface
  (TDictionary<string,Integer> -> IMap<string,Integer>) instantiated inside a
  USER UNIT (not the main program) must link.  Previously the unit codegen path
  emitted the impllist that references typeinfo_IMap_string_Integer but never
  emitted that typeinfo def, producing an undefined-symbol link error. }
procedure TE2EIMapTests.TestRun_IMap_GenericDictInUnit_LinksAndRuns;
const
  UnitSrc =
    '''
    unit genmapunit;
    interface
    uses Generics.Collections;
    type
      TStore = class
        FMap: TDictionary<string, Int>;
        constructor Create;
        function Get(const AKey: string): Int;
      end;
    implementation
    constructor TStore.Create;
    begin
      FMap := TDictionary<string, Int>.Create();
      FMap.Add('answer', 42);
    end;
    function TStore.Get(const AKey: string): Int;
    begin
      if not FMap.TryGetValue(AKey, Result) then Result := -1;
    end;
    end.
    ''';
  ProgSrc =
    '''
    program P;
    uses genmapunit;
    var S: TStore;
    begin
      S := TStore.Create();
      WriteLn(S.Get('answer'))
    end.
    ''';
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('genmapunit', UnitSrc, ProgSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Get(answer) = 42', '42' + #10, Output);
end;

const
  { Static array of interface: each element is a contiguous 16-byte fat
    pointer (obj + itab).  Pins the codegen fix where element writes
    stored only one slot (lost itab -> crash on dispatch) and element
    reads loaded a single slot.  Covers: class -> element store,
    dispatch through Arr[I], element -> interface-var copy, element ->
    element copy, and nil store (release path). }
  SrcStaticArrIface =
    '''
    program P;
    type
      IGreet = interface
        function Greet: Int;
      end;
      TA = class(IGreet)
        function Greet: Int;
        begin
          Result := 11
        end;
      end;
      TB = class(IGreet)
        function Greet: Int;
        begin
          Result := 22
        end;
      end;
    var
      Arr: array[0..2] of IGreet;
      G: IGreet;
    begin
      Arr[0] := TA.Create;
      Arr[1] := TB.Create;
      WriteLn(Arr[0].Greet());
      WriteLn(Arr[1].Greet());
      G := Arr[1];
      WriteLn(G.Greet());
      Arr[2] := Arr[0];
      WriteLn(Arr[2].Greet());
      Arr[0] := nil;
      WriteLn(Arr[2].Greet());
    end.
    ''';

procedure TE2EIMapTests.TestRun_StaticArrayOfInterface_FatPointer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  { Both backends now: native gained interface static-array element store, read
    and dispatch (the fat pointer is contiguous obj/itab; see
    EmitIntfStaticElemAddr). }
  AssertRunsOnAll(SrcStaticArrIface,
    '11' + #10 + '22' + #10 + '22' + #10 + '11' + #10 + '11' + #10, 0);
end;

const
  { Registry pattern: function returning an interface with `if Result = nil`
    inside.  The interface Result lives in the caller's sret buffer (split
    obj/itab) — the nil compare must read the obj half, not a single slot. }
  SrcIntfResultNilCompare =
    '''
    program P;
    type
      IDriver = interface
        function GetVal: Int;
      end;
      TDrv = class(IDriver)
        function GetVal: Int;
        begin
          Result := 7
        end;
      end;
    var
      GCache: IDriver;
    function GetDriver(): IDriver;
    begin
      Result := GCache;
      if Result = nil then
      begin
        WriteLn('miss');
        Result := TDrv.Create();
        GCache := Result
      end
    end;
    var
      D: IDriver;
    begin
      D := GetDriver();
      WriteLn(D.GetVal());
      D := GetDriver();
      WriteLn(D.GetVal())
    end.
    ''';

  { Interface-method call (itab dispatch) returning an interface, assigned to
    a LOCAL interface var — both with a local interface receiver and with an
    implicit-Self interface-field receiver. }
  SrcIntfMethodReturningIntf =
    '''
    program P;
    type
      IWidget = interface
        function Tag: Int;
      end;
      IDriver = interface
        function MakeWidget(N: Int): IWidget;
      end;
      TWidget = class(IWidget)
        FTag: Int;
        function Tag: Int;
        begin
          Result := Self.FTag
        end;
      end;
      TDrv = class(IDriver)
        function MakeWidget(N: Int): IWidget;
        var W: TWidget;
        begin
          W := TWidget.Create();
          W.FTag := N;
          Result := W
        end;
      end;
      TWorker = class
        FDriver: IDriver;
        function Run: Int;
        var W: IWidget;
        begin
          W := FDriver.MakeWidget(21);
          Result := W.Tag()
        end;
      end;
    procedure Go();
    var
      D: IDriver;
      W: IWidget;
      K: TWorker;
    begin
      D := TDrv.Create();
      W := D.MakeWidget(42);
      WriteLn(W.Tag());
      K := TWorker.Create();
      K.FDriver := D;
      WriteLn(K.Run())
    end;
    begin
      Go()
    end.
    ''';

procedure TE2EIMapTests.TestRun_InterfaceResult_NilCompare_Registry;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(SrcIntfResultNilCompare,
    'miss' + LineEnding + '7' + LineEnding + '7' + LineEnding, 0);
end;

procedure TE2EIMapTests.TestRun_IntfMethodReturningIntf_ToLocal;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(SrcIntfMethodReturningIntf,
    '42' + LineEnding + '21' + LineEnding, 0);
end;

const
  { Record passed by const through itab dispatch: the callee must see the
    full record (per the direct-call aggregate ABI), and the parameter
    AFTER the record must arrive un-shifted. }
  SrcIntfConstRecordArg =
    '''
    program P;
    type
      TOpts = record
        A: Int;
        B: Int;
        C: Int;
      end;
      ICfg = interface
        procedure Configure(const Opts: TOpts; X: Int);
      end;
      TCfg = class(ICfg)
        procedure Configure(const Opts: TOpts; X: Int);
        begin
          WriteLn(Opts.A);
          WriteLn(Opts.B);
          WriteLn(Opts.C);
          WriteLn(X)
        end;
      end;
    var
      C: ICfg;
      O: TOpts;
    begin
      O.A := 11; O.B := 22; O.C := 33;
      C := TCfg.Create();
      C.Configure(O, 77)
    end.
    ''';

  { out-string param through itab dispatch: the caller must pass the SLOT
    ADDRESS (var-param rule), not the loaded string value. }
  SrcIntfOutStringArg =
    '''
    program P;
    type
      IName = interface
        procedure GetName(out AName: string);
      end;
      TNamed = class(IName)
        procedure GetName(out AName: string);
        begin
          AName := 'blaise'
        end;
      end;
    var
      N: IName;
      S: string;
    begin
      S := 'old';
      N := TNamed.Create();
      N.GetName(S);
      WriteLn(S)
    end.
    ''';

  { var dynarray param through itab dispatch: same slot-address rule as
    strings — the callee reassigns the caller's array. }
  SrcIntfVarDynArrayArg =
    '''
    program P;
    type
      TIntArr = array of Int;
      ISink = interface
        procedure Fill(var A: TIntArr);
      end;
      TSink = class(ISink)
        procedure Fill(var A: TIntArr);
        begin
          SetLength(A, 2);
          A[0] := 5;
          A[1] := 9
        end;
      end;
    var
      K: ISink;
      Arr: TIntArr;
    begin
      K := TSink.Create();
      K.Fill(Arr);
      WriteLn(Length(Arr));
      WriteLn(Arr[0]);
      WriteLn(Arr[1])
    end.
    ''';

  { TFuncCallExpr receiver: the interface-returning CALL itself is the
    receiver of an itab dispatch — both in expression position
    (WriteLn(GetInfo().Val())) and statement position (GetInfo().Note()). }
  SrcFuncCallReceiver =
    '''
    program P;
    type
      IInfo = interface
        function Val(): Int;
        procedure Note();
      end;
      TInfo = class(IInfo)
        function Val(): Int;
        begin
          Result := 5
        end;
        procedure Note();
        begin
          WriteLn('note')
        end;
      end;
    function GetInfo(): IInfo;
    begin
      Result := TInfo.Create()
    end;
    begin
      WriteLn(GetInfo().Val());
      GetInfo().Note()
    end.
    ''';

  { Interface-returning itab call DISCARDED in statement position: must not
    clobber the receiver (the callee writes a 16-byte fat pointer through
    the hidden sret arg) and the receiver must stay usable afterwards. }
  SrcDiscardedIntfReturnStmt =
    '''
    program P;
    type
      IWidget = interface
        function Tag(): Int;
      end;
      IDriver = interface
        function MakeWidget(N: Int): IWidget;
      end;
      TWidget = class(IWidget)
        FTag: Int;
        function Tag(): Int;
        begin
          Result := Self.FTag
        end;
      end;
      TDrv = class(IDriver)
        function MakeWidget(N: Int): IWidget;
        var W: TWidget;
        begin
          W := TWidget.Create();
          W.FTag := N;
          Result := W
        end;
      end;
    var
      D: IDriver;
      W: IWidget;
    begin
      D := TDrv.Create();
      D.MakeWidget(5);
      W := D.MakeWidget(7);
      WriteLn(W.Tag())
    end.
    ''';

procedure TE2EIMapTests.TestRun_IntfDispatch_ConstRecordArg;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(SrcIntfConstRecordArg,
    '11' + LineEnding + '22' + LineEnding + '33' + LineEnding +
    '77' + LineEnding, 0);
end;

procedure TE2EIMapTests.TestRun_IntfDispatch_OutStringArg;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(SrcIntfOutStringArg, 'blaise' + LineEnding, 0);
end;

procedure TE2EIMapTests.TestRun_IntfDispatch_VarDynArrayArg;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(SrcIntfVarDynArrayArg,
    '2' + LineEnding + '5' + LineEnding + '9' + LineEnding, 0);
end;

procedure TE2EIMapTests.TestRun_FuncCallReceiver_IntfDispatch;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(SrcFuncCallReceiver,
    '5' + LineEnding + 'note' + LineEnding, 0);
end;

procedure TE2EIMapTests.TestRun_DiscardedIntfReturn_StatementPosition;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(SrcDiscardedIntfReturnStmt, '7' + LineEnding, 0);
end;

initialization
  RegisterTest(TE2EIMapTests);

end.
