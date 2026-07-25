{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.gaps;

{ E2E tests to close coverage gaps found during the IR-emit audit:
  packed records, sar (arithmetic shift right), UInt64 operations,
  and [Unretained] attribute.  All run on both backends. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EGapTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Boolean xor (GitHub #123) }
    procedure TestRun_BoolXor_TrueXorTrue_IsFalse;
    procedure TestRun_BoolXor_AllCombinations;

    { Packed records }
    procedure TestRun_PackedRecord_ByteIntOffsets;
    procedure TestRun_PackedRecord_SizeOfPacked;

    { Arithmetic shift right (sar) }
    procedure TestRun_Sar_NegativeInt64_PreservesSign;
    procedure TestRun_Shr_NegativeInt64_ZeroExtends;
    procedure TestRun_Sar_PositiveInteger;

    { UInt64 operations }
    procedure TestRun_UInt64_RoundTrip;
    procedure TestRun_UInt64_LargeLiteral;
    procedure TestRun_UInt64_UnsignedCompare;
    procedure TestRun_UInt64_Arithmetic;
    procedure TestRun_UInt64_DivMod_HighBitSet_SignedLiteral;
    procedure TestRun_UInt32_DivMod_HighBitSet;

    { [Unretained] attribute }
    procedure TestRun_Unretained_BackRef_NoLeak;
    procedure TestRun_Unretained_AssignAndReadBack;

    { Generic records }
    procedure TestRun_GenericRecord_FieldAccess;
    procedure TestRun_GenericRecord_MethodCall;

    { TDictionary default property d[key] }
    procedure TestRun_TDictionary_DefaultProp_IntKeys;
    procedure TestRun_TDictionary_DefaultProp_StringKeys;
    procedure TestRun_TDictionary_DefaultProp_Update;

    { Published RTTI + MethodAddress }
    procedure TestRun_PublishedRTTI_MethodAddress;

    { HasClassAttribute attribute RTTI query: a plain class reports False, a
      [Threaded]-marked class reports True.  Regression: the native backend
      emitted no call (result = low byte of the metaclass address, a false
      positive) and emitted no attribute table in typeinfo. }
    procedure TestRun_HasClassAttribute_PlainAndMarked;

    { Named-type alias array const (GitHub #113) }
    procedure TestRun_NamedArrayAlias_IntConst;

    { Boolean / enum / named-const array-const elements fold to ordinals }
    procedure TestRun_BoolArrayConst_FoldsToOrdinals;
    procedure TestRun_EnumArrayConst_FoldsToOrdinals;
    { Array-const element widths: Byte/Int64/Word stride matches the read }
    procedure TestRun_ArrayConst_ElementWidths;
    procedure TestRun_ArrayConst_NegativeInts;
    procedure TestRun_ArrayConst_EnumIndexedBool;
    { Enum-indexed multi-dimensional arrays (GitHub #128) }
    procedure TestRun_EnumBidimArray_Const;
    procedure TestRun_EnumBidimArray_MixedDims;
    procedure TestRun_EnumBidimArray_TypeAndVar;
    procedure TestRun_EnumBidimArray_ThreeDims;

    { Static array return by value (GitHub #112) }
    procedure TestRun_StaticArrayReturn_12Bytes;
    procedure TestRun_StaticArrayReturn_16Bytes;

    { Pointer deref field subscript (GitHub #118) }
    procedure TestRun_DerefFieldSubscript_Write;
    procedure TestRun_DerefFieldSubscript_ReadAndWrite;

    { Generic record type alias specialisation (GitHub #124) }
    procedure TestRun_GenericRecordAlias_MethodCall;

    { Multi-arg WriteLn }
    procedure TestRun_WriteLn_MultipleArgs_MixedTypes;

    { Interface-returning method with >5 args (native sret spill) }
    procedure TestRun_IntfSret_SixArgs_DirectClassCall;
    procedure TestRun_IntfSret_SixArgs_InterfaceDispatch;
    procedure TestRun_IntfSret_SevenArgs_InterfaceDispatch;

    { Interface-returning call result passed positionally as an arg }
    procedure TestRun_IntfArg_CallResult_AsParam;

    { Record-returning call result passed as a record-by-value arg (the hoist
      must keep %rsp 16-aligned) }
    procedure TestRun_RecordCallResult_AsValueArg;
  end;

implementation

procedure TE2EGapTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-gaps');
end;

{ ---- Boolean xor ---- }

procedure TE2EGapTests.TestRun_BoolXor_TrueXorTrue_IsFalse;
const Src = '''
    program T;
    var A, B: Boolean;
    begin
      A := True;
      B := True;
      WriteLn(A xor B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'False' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_BoolXor_AllCombinations;
const Src = '''
    program T;
    var A, B: Boolean;
    begin
      A := False; B := False; WriteLn(A xor B);
      A := False; B := True;  WriteLn(A xor B);
      A := True;  B := False; WriteLn(A xor B);
      A := True;  B := True;  WriteLn(A xor B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'False' + Chr(10) + 'True' + Chr(10) +
                       'True' + Chr(10) + 'False' + Chr(10), 0);
end;

{ ---- Packed records ---- }

procedure TE2EGapTests.TestRun_PackedRecord_ByteIntOffsets;
const Src = '''
    program T;
    type
      TPacked = packed record
        A: Byte;
        B: Integer;
      end;
    var R: TPacked;
    begin
      R.A := 1;
      R.B := 1000;
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1' + Chr(10) + '1000' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_PackedRecord_SizeOfPacked;
const Src = '''
    program T;
    type
      TPacked = packed record
        A: Byte;
        B: Integer;
      end;
      TNormal = record
        A: Byte;
        B: Integer;
      end;
    begin
      WriteLn(SizeOf(TPacked));
      WriteLn(SizeOf(TNormal))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '5' + Chr(10) + '8' + Chr(10), 0);
end;

{ ---- Arithmetic shift right ---- }

procedure TE2EGapTests.TestRun_Sar_NegativeInt64_PreservesSign;
const Src = '''
    program T;
    var V: Int64;
    begin
      V := -16;
      WriteLn(V sar 2)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '-4' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_Shr_NegativeInt64_ZeroExtends;
const Src = '''
    program T;
    var V: Int64;
    begin
      V := -1;
      { shr on Int64 zero-extends: -1 shr 63 = 1 (not -1) }
      WriteLn(V shr 63)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_Sar_PositiveInteger;
const Src = '''
    program T;
    var V: Integer;
    begin
      V := 100;
      WriteLn(V sar 2)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '25' + Chr(10), 0);
end;

{ ---- UInt64 operations ---- }

procedure TE2EGapTests.TestRun_UInt64_RoundTrip;
const Src = '''
    program T;
    var U: UInt64;
    begin
      U := 42;
      WriteLn(U)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_UInt64_LargeLiteral;
const Src = '''
    program T;
    var U: UInt64;
    begin
      U := 18446744073709551615;
      if U > 0 then
        WriteLn('positive')
      else
        WriteLn('BUG')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'positive' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_UInt64_UnsignedCompare;
const Src = '''
    program T;
    var A, B: UInt64;
    begin
      A := 18446744073709551615;
      B := 1;
      if A > B then
        WriteLn('ok')
      else
        WriteLn('BUG')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'ok' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_UInt64_Arithmetic;
const Src = '''
    program T;
    var U: UInt64;
    begin
      U := 10;
      WriteLn(U * 3);
      WriteLn(U div 3);
      WriteLn(U mod 3)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '30' + Chr(10) + '3' + Chr(10) + '1' + Chr(10), 0);
end;

{ GH #196: a UInt64 value with bit 63 set, divided by a *signed* integer
  literal.  The native backend chose signed idivq whenever either operand
  was not itself unsigned, so `U div 16` on a high-bit-set value treated
  the operand as negative and produced garbage.  Signedness must follow the
  expression's result type (as the QBE backend already does), not the
  conjunction of both operand types. }
procedure TE2EGapTests.TestRun_UInt64_DivMod_HighBitSet_SignedLiteral;
const Src = '''
    program T;
    var U: UInt64;
    begin
      U := 9259542123273814144;
      WriteLn(U div 16);
      WriteLn(U mod 16);
      WriteLn((U div 16) mod 16)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '578721382704613384' + Chr(10) + '0' + Chr(10) +
    '8' + Chr(10), 0);
end;

{ Sibling of the above in the QBE backend's 32-bit arm: a UInt32 result with
  bit 31 set divided as signed produced a negative quotient.  Signedness must
  follow the result type on the w-typed path too. }
procedure TE2EGapTests.TestRun_UInt32_DivMod_HighBitSet;
const Src = '''
    program T;
    var C: UInt32;
    begin
      C := 4000000000;
      WriteLn(C div 7);
      WriteLn(C mod 7)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '571428571' + Chr(10) + '3' + Chr(10), 0);
end;

{ ---- [Unretained] attribute ---- }

procedure TE2EGapTests.TestRun_Unretained_BackRef_NoLeak;
const Src = '''
    program T;
    type
      TOwner = class(TObject)
        Name: string;
      end;
      TChild = class(TObject)
        [Unretained] Owner: TOwner;
      end;
    var
      O: TOwner;
      C: TChild;
    begin
      O := TOwner.Create();
      O.Name := 'parent';
      C := TChild.Create();
      C.Owner := O;
      WriteLn(C.Owner.Name);
      C.Free();
      O.Free();
      WriteLn('done')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'parent' + Chr(10) + 'done' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_Unretained_AssignAndReadBack;
const Src = '''
    program T;
    type
      TNode = class(TObject)
        Value: Integer;
        [Unretained] Next: TNode;
      end;
    var
      A, B: TNode;
    begin
      A := TNode.Create();
      A.Value := 1;
      B := TNode.Create();
      B.Value := 2;
      A.Next := B;
      WriteLn(A.Next.Value);
      B.Free();
      A.Free();
      WriteLn('ok')
    end.
    ''';
begin
  AssertRunsOnAll(Src, '2' + Chr(10) + 'ok' + Chr(10), 0);
end;

{ ---- TDictionary default property ---- }

procedure TE2EGapTests.TestRun_TDictionary_DefaultProp_IntKeys;
const Src = '''
    program T;
    type
      TMap<K, V> = class
        FKeys:     ^K;
        FValues:   ^V;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        function  FindKey(Key: K): Integer;
        procedure Add(Key: K; Value: V);
        function  GetItem(Key: K): V;
        procedure SetItem(Key: K; Value: V);
        property Items[Key: K]: V read GetItem write SetItem; default;
      end;
    procedure TMap<K, V>.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 8
      else NewCap := Self.FCapacity * 2;
      Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
      Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
      Self.FCapacity := NewCap
    end;
    function TMap<K, V>.FindKey(Key: K): Integer;
    var I: Integer; Ptr: ^K;
    begin
      Result := -1;
      I := 0;
      while I < Self.FCount do
      begin
        Ptr := Self.FKeys + I * SizeOf(K);
        if Ptr^ = Key then begin Result := I; I := Self.FCount end
        else I := I + 1
      end
    end;
    procedure TMap<K, V>.Add(Key: K; Value: V);
    var Idx: Integer; KPtr: ^K; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value end
      else begin
        if Self.FCount = Self.FCapacity then Self.Grow();
        KPtr := Self.FKeys + Self.FCount * SizeOf(K);
        VPtr := Self.FValues + Self.FCount * SizeOf(V);
        KPtr^ := Key; VPtr^ := Value;
        Self.FCount := Self.FCount + 1
      end
    end;
    function TMap<K, V>.GetItem(Key: K): V;
    var Idx: Integer; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); Result := VPtr^ end
      else Halt(1)
    end;
    procedure TMap<K, V>.SetItem(Key: K; Value: V);
    begin Self.Add(Key, Value) end;
    var D: TMap<Integer, Integer>;
    begin
      D := TMap<Integer, Integer>.Create();
      D[1] := 100;
      D[2] := 200;
      WriteLn(D[1]);
      WriteLn(D[2]);
      D.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '100' + Chr(10) + '200' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_TDictionary_DefaultProp_StringKeys;
const Src = '''
    program T;
    type
      TMap<K, V> = class
        FKeys:     ^K;
        FValues:   ^V;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        function  FindKey(Key: K): Integer;
        procedure Add(Key: K; Value: V);
        function  GetItem(Key: K): V;
        procedure SetItem(Key: K; Value: V);
        property Items[Key: K]: V read GetItem write SetItem; default;
      end;
    procedure TMap<K, V>.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 8
      else NewCap := Self.FCapacity * 2;
      Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
      Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
      Self.FCapacity := NewCap
    end;
    function TMap<K, V>.FindKey(Key: K): Integer;
    var I: Integer; Ptr: ^K;
    begin
      Result := -1;
      I := 0;
      while I < Self.FCount do
      begin
        Ptr := Self.FKeys + I * SizeOf(K);
        if Ptr^ = Key then begin Result := I; I := Self.FCount end
        else I := I + 1
      end
    end;
    procedure TMap<K, V>.Add(Key: K; Value: V);
    var Idx: Integer; KPtr: ^K; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value end
      else begin
        if Self.FCount = Self.FCapacity then Self.Grow();
        KPtr := Self.FKeys + Self.FCount * SizeOf(K);
        VPtr := Self.FValues + Self.FCount * SizeOf(V);
        KPtr^ := Key; VPtr^ := Value;
        Self.FCount := Self.FCount + 1
      end
    end;
    function TMap<K, V>.GetItem(Key: K): V;
    var Idx: Integer; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); Result := VPtr^ end
      else Halt(1)
    end;
    procedure TMap<K, V>.SetItem(Key: K; Value: V);
    begin Self.Add(Key, Value) end;
    var D: TMap<string, Integer>;
    begin
      D := TMap<string, Integer>.Create();
      D['one'] := 1;
      D['two'] := 2;
      WriteLn(D['one']);
      WriteLn(D['two']);
      D.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1' + Chr(10) + '2' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_TDictionary_DefaultProp_Update;
const Src = '''
    program T;
    type
      TMap<K, V> = class
        FKeys:     ^K;
        FValues:   ^V;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        function  FindKey(Key: K): Integer;
        procedure Add(Key: K; Value: V);
        function  GetItem(Key: K): V;
        procedure SetItem(Key: K; Value: V);
        property Items[Key: K]: V read GetItem write SetItem; default;
      end;
    procedure TMap<K, V>.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 8
      else NewCap := Self.FCapacity * 2;
      Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
      Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
      Self.FCapacity := NewCap
    end;
    function TMap<K, V>.FindKey(Key: K): Integer;
    var I: Integer; Ptr: ^K;
    begin
      Result := -1;
      I := 0;
      while I < Self.FCount do
      begin
        Ptr := Self.FKeys + I * SizeOf(K);
        if Ptr^ = Key then begin Result := I; I := Self.FCount end
        else I := I + 1
      end
    end;
    procedure TMap<K, V>.Add(Key: K; Value: V);
    var Idx: Integer; KPtr: ^K; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value end
      else begin
        if Self.FCount = Self.FCapacity then Self.Grow();
        KPtr := Self.FKeys + Self.FCount * SizeOf(K);
        VPtr := Self.FValues + Self.FCount * SizeOf(V);
        KPtr^ := Key; VPtr^ := Value;
        Self.FCount := Self.FCount + 1
      end
    end;
    function TMap<K, V>.GetItem(Key: K): V;
    var Idx: Integer; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); Result := VPtr^ end
      else Halt(1)
    end;
    procedure TMap<K, V>.SetItem(Key: K; Value: V);
    begin Self.Add(Key, Value) end;
    var D: TMap<string, Integer>;
    begin
      D := TMap<string, Integer>.Create();
      D['x'] := 10;
      D['x'] := 42;
      WriteLn(D['x']);
      D.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10), 0);
end;

{ ---- Generic records ---- }

procedure TE2EGapTests.TestRun_GenericRecord_FieldAccess;
const Src = '''
    program T;
    type
      TPair<K, V> = record
        Key: K;
        Value: V;
      end;
    var P: TPair<Integer, string>;
    begin
      P.Key := 42;
      P.Value := 'hello';
      WriteLn(P.Key);
      WriteLn(P.Value)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10) + 'hello' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_GenericRecord_MethodCall;
const Src = '''
    program T;
    type
      TBox<T> = record
        Data: T;
        function GetData: T;
      end;
    function TBox<T>.GetData: T;
    begin
      Result := Self.Data
    end;
    var B: TBox<Integer>;
    begin
      B.Data := 99;
      WriteLn(B.GetData())
    end.
    ''';
begin
  AssertRunsOnAll(Src, '99' + Chr(10), 0);
end;

{ ---- Published RTTI + MethodAddress ---- }

procedure TE2EGapTests.TestRun_PublishedRTTI_MethodAddress;
const Src = '''
    program T;
    type
      TMyObj = class(TObject)
      published
        procedure Greet;
      end;
    procedure TMyObj.Greet;
    begin
      WriteLn('hello from published')
    end;
    var
      Obj: TMyObj;
      Addr: Pointer;
    begin
      Obj := TMyObj.Create();
      Addr := MethodAddress(Obj, 'Greet');
      if Addr <> nil then
        WriteLn('found')
      else
        WriteLn('BUG');
      Obj.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'found' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_HasClassAttribute_PlainAndMarked;
const Src = '''
    program T;
    uses blaise.testing;
    type
      TPlain = class(TTestCase) published procedure M; end;
      [Threaded]
      TMarked = class(TTestCase) published procedure M; end;
    procedure TPlain.M; begin end;
    procedure TMarked.M; begin end;
    begin
      WriteLn(HasClassAttribute(TPlain, ThreadedAttribute));
      WriteLn(HasClassAttribute(TMarked, ThreadedAttribute))
    end.
    ''';
begin
  { Uses blaise.testing (stdlib), so the RTL+stdlib search-path helper. }
  AssertRTLRunsOnAll(Src, 'False' + Chr(10) + 'True' + Chr(10), 0);
end;

{ ---- Multi-arg WriteLn ---- }

procedure TE2EGapTests.TestRun_StaticArrayReturn_12Bytes;
const
  Src =
    '''
    program P;
    type TVec3 = array[0..2] of Integer;
    function MakeVec(A, B, C: Integer): TVec3;
    begin
      Result[0] := A;
      Result[1] := B;
      Result[2] := C
    end;
    var V: TVec3;
    begin
      V := MakeVec(10, 20, 30);
      WriteLn(V[0]);
      WriteLn(V[1]);
      WriteLn(V[2])
    end.
    ''';
begin
  AssertRunsOnAll(Src, '10' + Chr(10) + '20' + Chr(10) + '30' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_StaticArrayReturn_16Bytes;
const
  Src =
    '''
    program P;
    type TPair = array[0..1] of Int64;
    function MakePair(A, B: Int64): TPair;
    begin
      Result[0] := A;
      Result[1] := B
    end;
    var P2: TPair;
    begin
      P2 := MakePair(111, 222);
      WriteLn(P2[0]);
      WriteLn(P2[1])
    end.
    ''';
begin
  AssertRunsOnAll(Src, '111' + Chr(10) + '222' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_DerefFieldSubscript_Write;
const
  Src =
    '''
    program P;
    type
      PRec = ^TRec;
      TRec = record
        DA: array of Integer;
      end;
    var
      Ptr: PRec;
      R: TRec;
    begin
      Ptr := @R;
      SetLength(R.DA, 3);
      R.DA[0] := 10;
      Ptr^.DA[1] := 20;
      Ptr^.DA[2] := 30;
      WriteLn(R.DA[0]);
      WriteLn(R.DA[1]);
      WriteLn(R.DA[2])
    end.
    ''';
begin
  AssertRunsOnAll(Src, '10' + Chr(10) + '20' + Chr(10) + '30' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_DerefFieldSubscript_ReadAndWrite;
const
  Src =
    '''
    program P;
    type
      PRec = ^TRec;
      TRec = record
        DA: array of Integer;
      end;
    var
      Ptr: PRec;
      R: TRec;
      I: Integer;
    begin
      Ptr := @R;
      SetLength(R.DA, 2);
      Ptr^.DA[0] := 100;
      Ptr^.DA[1] := 200;
      I := Ptr^.DA[0] + Ptr^.DA[1];
      WriteLn(I)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '300' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_GenericRecordAlias_MethodCall;
const
  Src =
    '''
    program P;
    type
      THolder<T> = record
        FVal: T;
        procedure SetVal(AVal: T);
      end;
      TIntHolder = THolder<Integer>;
      procedure THolder<T>.SetVal(AVal: T);
      begin
        FVal := AVal
      end;
    var H: TIntHolder;
    begin
      H.SetVal(54);
      WriteLn(H.FVal)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '54' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_WriteLn_MultipleArgs_MixedTypes;
const Src = '''
    program T;
    var
      S: string;
      I: Integer;
      B: Boolean;
    begin
      S := 'val';
      I := 42;
      B := True;
      WriteLn(S, '=', I);
      WriteLn('ok:', B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'val=42' + Chr(10) + 'ok:True' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_NamedArrayAlias_IntConst;
const
  Src =
    '''
    program P;
    type TArr = array[0..2] of Integer;
    const Vals: TArr = (10, 20, 30);
    var I: Integer;
    begin
      for I := 0 to 2 do
        WriteLn(Vals[I])
    end.
    ''';
begin
  AssertRunsOnAll(Src, '10' + Chr(10) + '20' + Chr(10) + '30' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_BoolArrayConst_FoldsToOrdinals;
{ Boolean literals as array-const elements were emitted as symbol references
  (undefined `False'/`True' at link time on native; "unknown keyword False" on
  QBE) and at the wrong element width.  Now folded to 0/1 with 1-byte stride. }
const
  Src =
    '''
    program P;
    const Flags: array[0..3] of Boolean = (False, True, False, True);
    var I: Integer;
    begin
      for I := 0 to 3 do
        if Flags[I] then WriteLn('T') else WriteLn('F')
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    'F' + Chr(10) + 'T' + Chr(10) + 'F' + Chr(10) + 'T' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_EnumArrayConst_FoldsToOrdinals;
{ Enum members and named integer constants as array-const elements fold to their
  ordinal/value rather than emitting a symbol reference. }
const
  Src =
    '''
    program P;
    type TColor = (Red, Green, Blue);
    const N = 7;
    const
      Palette: array[0..2] of TColor = (Blue, Red, Green);
      WithConst: array[0..1] of Integer = (N, 99);
    var I: Integer;
    begin
      for I := 0 to 2 do WriteLn(Integer(Palette[I]));
      WriteLn(WithConst[0]);
      WriteLn(WithConst[1])
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '2' + Chr(10) + '0' + Chr(10) + '1' + Chr(10) +
    '7' + Chr(10) + '99' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_ArrayConst_ElementWidths;
{ Edge case: non-4-byte element widths must emit the matching stride.  Byte (1),
  Word (2) and Int64 (8) all read back correctly — a fixed .long/w stride would
  scramble these. }
const
  Src =
    '''
    program P;
    const
      B: array[0..2] of Byte = (0, 255, 128);
      W: array[0..2] of Word = (1, 65535, 256);
      L: array[0..1] of Int64 = (9000000000, 5);
    var I: Integer;
    begin
      for I := 0 to 2 do WriteLn(B[I]);
      for I := 0 to 2 do WriteLn(W[I]);
      WriteLn(L[0]);
      WriteLn(L[1])
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '0' + Chr(10) + '255' + Chr(10) + '128' + Chr(10) +
    '1' + Chr(10) + '65535' + Chr(10) + '256' + Chr(10) +
    '9000000000' + Chr(10) + '5' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_ArrayConst_NegativeInts;
{ Edge case: negative integer literals in an array const pass through the
  element-folding unchanged (they are not identifiers). }
const
  Src =
    '''
    program P;
    const Vals: array[0..2] of Integer = (-1, -100, 42);
    var I: Integer;
    begin
      for I := 0 to 2 do WriteLn(Vals[I])
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '-1' + Chr(10) + '-100' + Chr(10) + '42' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_ArrayConst_EnumIndexedBool;
{ Edge case: a Boolean array INDEXED BY an enum — combines enum-indexing with
  Boolean element folding + 1-byte stride. }
const
  Src =
    '''
    program P;
    type TDay = (Mon, Tue, Wed);
    const Open: array[TDay] of Boolean = (True, False, True);
    var D: TDay;
    begin
      for D := Mon to Wed do
        if Open[D] then WriteLn('open') else WriteLn('closed')
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    'open' + Chr(10) + 'closed' + Chr(10) + 'open' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_EnumBidimArray_Const;
{ GitHub #128: a 2-D array const indexed by an enum in both dimensions —
  array[TEnum, TEnum] — previously failed to parse ("Expected '..' but got
  ','"). }
const
  Src =
    '''
    program P;
    type TEnum = (one, two);
    const d: array[TEnum, TEnum] of byte = ((1, 2), (3, 4));
    begin
      WriteLn(d[one, one]);
      WriteLn(d[one, two]);
      WriteLn(d[two, one]);
      WriteLn(d[two, two])
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '1' + Chr(10) + '2' + Chr(10) + '3' + Chr(10) + '4' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_EnumBidimArray_MixedDims;
{ Mixed dimensions: an enum dimension and an integer-range dimension together,
  in both orders. }
const
  Src =
    '''
    program P;
    type TE = (a, b);
    const
      e: array[TE, 0..1] of byte = ((5, 6), (7, 8));
      f: array[0..1, TE] of byte = ((10, 20), (30, 40));
    begin
      WriteLn(e[a, 0]);
      WriteLn(e[b, 1]);
      WriteLn(f[0, a]);
      WriteLn(f[1, b])
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '5' + Chr(10) + '8' + Chr(10) + '10' + Chr(10) + '40' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_EnumBidimArray_TypeAndVar;
{ The same enum-indexed multi-dim form in a type declaration and a var. }
const
  Src =
    '''
    program P;
    type
      TE = (a, b, c);
      TGrid = array[TE, TE] of byte;
    var g: TGrid;
    begin
      g[a, c] := 5;
      g[c, a] := 9;
      WriteLn(g[a, c]);
      WriteLn(g[c, a])
    end.
    ''';
begin
  AssertRunsOnAll(Src, '5' + Chr(10) + '9' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_EnumBidimArray_ThreeDims;
{ Three dimensions, enum + range + enum. }
const
  Src =
    '''
    program P;
    type TE = (a, b);
    const m: array[TE, 0..1, TE] of byte =
      (((1,2),(3,4)), ((5,6),(7,8)));
    begin
      WriteLn(m[a, 0, a]);
      WriteLn(m[b, 1, b])
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1' + Chr(10) + '8' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_IntfSret_SixArgs_DirectClassCall;
{ Class instance whose method returns an interface and takes 6 Integer args.
  On native this is the class-sret interface call path (>4 user arg slots);
  it must spill the overflow args to the stack rather than raising. }
const
  Src =
    '''
    program P;
    type
      IFoo = interface
        function Make(a, b, c, d, e, f: Integer): IFoo;
        function Sum: Integer;
      end;
      TFoo = class(TObject, IFoo)
        FTotal: Integer;
        function Make(a, b, c, d, e, f: Integer): IFoo;
        function Sum: Integer;
      end;
    function TFoo.Make(a, b, c, d, e, f: Integer): IFoo;
    begin
      FTotal := a + b + c + d + e + f;
      Result := Self;
    end;
    function TFoo.Sum: Integer;
    begin
      Result := FTotal;
    end;
    var
      F: TFoo;
      R: IFoo;
    begin
      F := TFoo.Create();
      R := F.Make(1, 2, 3, 4, 5, 6);
      WriteLn(R.Sum)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '21' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_IntfSret_SixArgs_InterfaceDispatch;
{ Same method called through an interface reference — the interface-dispatch
  sret path (receiver + sret buffer + 6 args overflow the registers). }
const
  Src =
    '''
    program P;
    type
      IFoo = interface
        function Make(a, b, c, d, e, f: Integer): IFoo;
        function Sum: Integer;
      end;
      TFoo = class(TObject, IFoo)
        FTotal: Integer;
        function Make(a, b, c, d, e, f: Integer): IFoo;
        function Sum: Integer;
      end;
    function TFoo.Make(a, b, c, d, e, f: Integer): IFoo;
    begin
      FTotal := a + b + c + d + e + f;
      Result := Self;
    end;
    function TFoo.Sum: Integer;
    begin
      Result := FTotal;
    end;
    var
      F: IFoo;
      R: IFoo;
    begin
      F := TFoo.Create();
      R := F.Make(10, 20, 30, 40, 50, 60);
      WriteLn(R.Sum)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '210' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_IntfSret_SevenArgs_InterfaceDispatch;
{ Seven args through an interface reference — two overflow slots. }
const
  Src =
    '''
    program P;
    type
      IFoo = interface
        function Make(a, b, c, d, e, f, g: Integer): IFoo;
        function Sum: Integer;
      end;
      TFoo = class(TObject, IFoo)
        FTotal: Integer;
        function Make(a, b, c, d, e, f, g: Integer): IFoo;
        function Sum: Integer;
      end;
    function TFoo.Make(a, b, c, d, e, f, g: Integer): IFoo;
    begin
      FTotal := a + b + c + d + e + f + g;
      Result := Self;
    end;
    function TFoo.Sum: Integer;
    begin
      Result := FTotal;
    end;
    var
      F: IFoo;
      R: IFoo;
    begin
      F := TFoo.Create();
      R := F.Make(1, 2, 3, 4, 5, 6, 7);
      WriteLn(R.Sum)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '28' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_IntfArg_CallResult_AsParam;
{ Passing an interface-returning function's result directly as an interface
  argument (Show(MakeFoo(42))) — native previously raised "unsupported
  interface argument expression" for this positional call-result form. }
const
  Src =
    '''
    program P;
    type
      IFoo = interface
        function Val: Integer;
      end;
      TFoo = class(TObject, IFoo)
        FN: Integer;
        function Val: Integer;
      end;
    function TFoo.Val: Integer;
    begin Result := FN end;
    function MakeFoo(N: Integer): IFoo;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.FN := N;
      Result := F
    end;
    procedure Show(F: IFoo);
    begin
      WriteLn(F.Val())
    end;
    begin
      Show(MakeFoo(42))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_RecordCallResult_AsValueArg;
{ A record-returning function's result passed directly as a record-by-value
  argument to another function — Use(Make(10), 16.0).  The native arg-hoist
  materialises Make's result into a stack buffer and saves a pointer; that
  region must stay a multiple of 16 bytes or %rsp drifts off 16-alignment and a
  later SSE op (here Sqrt) — or a libm routine using movdqa — faults.  This
  regressed DateAddDays(MakeDate(...), 5). }
const
  Src =
    '''
    program P;
    type
      TR = record
        A, B, C: Integer;
      end;
    function Make(N: Integer): TR;
    begin
      Result.A := N; Result.B := N + 1; Result.C := N + 2
    end;
    function Use(R: TR; D: Double): Double;
    begin
      Result := Sqrt(D) + R.A + R.B + R.C
    end;
    var X: Double;
    begin
      X := Use(Make(10), 16.0);
      WriteLn(X)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '37' + Chr(10), 0);
end;

initialization
  RegisterTest(TE2EGapTests);

end.
