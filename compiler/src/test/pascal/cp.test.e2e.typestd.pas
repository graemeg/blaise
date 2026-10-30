{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.typestd;

{ End-to-end tests for the type-standardisation names (Phase 1 of
  docs/type-standardisation-design.adoc): storage width, arithmetic,
  conversions, overload selection and const-array data through each new
  spelling, compiled, linked and run on every ISA the host can execute. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2ETypeStdTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { SizeOf, wrap-around and signedness of every new integer name }
    procedure TestRun_IntegerNames_WidthAndArithmetic;
    { Float is Float64 (full double precision), Float32 rounds to single }
    procedure TestRun_FloatNames_Precision;
    { casts through the new names convert at their width }
    procedure TestRun_NewNames_Casts;
    { overload selection by the new names: Int32 / Int (= Int64) / Float32 /
      Float64 each reach their own body }
    procedure TestRun_NewNames_OverloadSelection;
    { const arrays of the new names store elements at the true width }
    procedure TestRun_NewNames_ConstArrays;
    { an Int8 reads back sign-extended from every place it can live: local,
      global, record and class field, static and dynamic array element, var
      parameter, function result and const array }
    procedure TestRun_Int8_SignExtendsEverywhere;
    { Int8 arithmetic wraps at 8 bits on store; comparison, division and
      Low/High are signed; casts and constant casts truncate to 8 bits }
    procedure TestRun_Int8_SignedSemantics;
    { Int8 crosses a unit boundary: exported routines, a record of Int8
      fields, a typed constant, a global set in the unit's initialization,
      and an Int8 / Byte overload pair }
    procedure TestRun_Int8_AcrossUnitInterface;
    { a narrow argument reaches the CLOSEST wider overload: Int8 / Byte /
      SmallInt reach Integer over Int64 and Double, a Byte reaches Word over
      SmallInt, an Integer reaches Int64 over Double -- routines and methods }
    procedure TestRun_NarrowArg_ReachesClosestOverload;
    { Phase 4.2: Format('%u') prints its argument unsigned, so a UInt64
      above High(Int64) and a UInt32 above High(Int32) format correctly;
      %d of the same UInt64 shows why it is needed }
    procedure TestRun_Format_U_Unsigned;
    { Phase 4.3 (D4): an unhinted integer literal, and an untyped integer
      constant, is Int.  F(42) against an Int32 / Int64 pair reaches Int64,
      1 shl 31 is positive and -1 shr 1 shifts 64 bits; a literal with a
      hint (typed operand, parameter, assignment target) keeps that type }
    procedure TestRun_UnhintedLiteral_IsInt;
    { Phase 4.3: a constant adapts to its context -- a non-negative constant
      to UInt64 (assignment, argument, operand); among integer overloads the
      one closest to the constant's own type, never one too narrow for it;
      vtInteger in an 'array of const'; and an Integer compared with a
      literal on either side }
    procedure TestRun_Constants_AdaptToContext;
    { Phase 4.3: a bracket literal of Int constants reaches an 'array of
      Integer' formal at 4 bytes an element through every call shape --
      routine, method, constructor, nested procedure (in a routine and in a
      method) and nested function.  x86-64 lays the elements out at the
      literal's own width unless the literal is retyped to the formal. }
    procedure TestRun_OpenArrayLiteral_EveryCallShape;
    { Phase 4.4 (D5): Length, Pos, PosEx, SizeOf, Ord and the index-bound
      High/Low are Int, so each reaches F(Int64) over F(Integer) with its
      value intact: Pos's -1, Ord of a negative Integer, High of an empty
      string.  Copy and SetLength take an Int count without truncating it. }
    procedure TestRun_BuiltinResults_AreInt;
    { Phase 4.5: the headers store 64-bit lengths, so a dynamic array and
      a string above 2^31 elements are built, indexed past 2^31, measured
      and released }
    procedure TestRun_LengthAboveInt32_Works;
    { Phase 4.4: Length, SizeOf and Ord of an unsigned ordinal cannot be
      negative, so they mix with a UInt64 without a cast, as the Integer
      they were did -- an FNV-1a hash over Ord of each character }
    procedure TestRun_NonNegativeInt_MixesWithUInt64;
    { Phase 4.5: a string above 1 GiB is built, written and released; the
      release's header sanity check rejected any length above 1 GiB as a
      corrupted header }
    procedure TestRun_StringAbove1GiB_Releases;
    { Phase 4.6: the collections' Count, Capacity, indices and index
      parameters are Int -- each result reaches the Int64 overload, a var
      index is declared Int, and a Count above 2^31 reads back whole }
    procedure TestRun_CollectionCounts_AreInt;
    { Phase 4.7: MaxInt is High(Int), reaches the Int64 overload, and still
      means "to the end" as a Copy or Delete count }
    procedure TestRun_MaxInt_IsHighInt;
    procedure TestRun_ImplementsGenericInterface_AliasArgument;
    procedure TestRun_GenericReceiver_AliasArgument;
  end;

implementation

procedure TE2ETypeStdTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-typestd');
end;

procedure TE2ETypeStdTests.TestRun_IntegerNames_WidthAndArithmetic;
const
  Src = '''
    program P;
    var
      N: Int; U: UInt; I32: Int32; U8: UInt8;
    begin
      WriteLn(SizeOf(Int), ' ', SizeOf(UInt), ' ', SizeOf(Int32), ' ',
        SizeOf(UInt8));
      N := 5000000000;
      WriteLn(N * 2);
      U := 18000000000000000000;
      WriteLn(UInt64ToStr(U));
      I32 := 2147483647;
      I32 := I32 + 1;
      WriteLn(I32);
      U8 := 250;
      U8 := U8 + 10;
      WriteLn(U8)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '8 8 4 1' + #10 +
    '10000000000' + #10 +
    '18000000000000000000' + #10 +
    '-2147483648' + #10 +
    '4' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_FloatNames_Precision;
const
  Src = '''
    program P;
    var
      F: Float; F64: Float64; F32: Float32;
    begin
      WriteLn(SizeOf(Float), ' ', SizeOf(Float64), ' ', SizeOf(Float32));
      F := 1.0;
      F := F / 3.0;
      F64 := F;
      F32 := F;
      WriteLn(F:0:15);
      WriteLn(F64:0:15);
      WriteLn(F32:0:15)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '8 8 4' + #10 +
    '0.333333333333333' + #10 +
    '0.333333333333333' + #10 +
    '0.333333343267441' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_NewNames_Casts;
const
  Src = '''
    program P;
    var
      I: Integer; L: Int64;
    begin
      I := 7;
      WriteLn(Float64(I) / 2:0:1);
      WriteLn(Float32(I) / 4:0:2);
      L := 300;
      WriteLn(UInt8(L));
      L := 4294967295;
      WriteLn(Int32(L));
      I := -1;
      WriteLn(Int(I))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '3.5' + #10 + '1.75' + #10 + '44' + #10 + '-1' + #10 + '-1' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_NewNames_OverloadSelection;
const
  Src = '''
    program P;
    procedure F(X: Int32); overload; begin WriteLn('Int32 ', X) end;
    procedure F(X: Int); overload; begin WriteLn('Int ', X) end;
    procedure G(X: Float32); overload; begin WriteLn('Float32') end;
    procedure G(X: Float64); overload; begin WriteLn('Float64') end;
    var
      A: Int32; B: Int; C: Float32; D: Float;
    begin
      A := 1; B := 2; C := 0.5; D := 0.25;
      F(A); F(B); G(C); G(D)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Int32 1' + #10 + 'Int 2' + #10 + 'Float32' + #10 + 'Float64' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_NewNames_ConstArrays;
const
  Src = '''
    program P;
    const
      A: array[0..2] of Int = (1, -2, 5000000000);
      B: array[0..2] of UInt8 = (7, 8, 255);
      C: array[0..2] of Int32 = (10, -20, 30);
      D: array[0..2] of Float64 = (0.5, 1.5, 2.5);
      E: array[0..2] of Float32 = (0.25, 0.75, 1.25);
    var I: Integer;
    begin
      for I := 1 to 2 do
        WriteLn(A[I], ' ', B[I], ' ', C[I], ' ', D[I]:0:1, ' ', E[I]:0:2)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '-2 8 -20 1.5 0.75' + #10 + '5000000000 255 30 2.5 1.25' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_Int8_SignExtendsEverywhere;
const
  Src = '''
    program P;
    type
      TRec = record
        Pad: Byte;
        V: Int8;
        W: Int8;
      end;
      TObj = class
        V: Int8;
      end;
    const
      CA: array[0..2] of Int8 = (-1, 100, -128);
    var
      G: Int8;
      R: TRec;
      O: TObj;
      SA: array[0..3] of Int8;
      DA: array of Int8;
      L: Int8;
      I: Integer;

    procedure Neg(var X: Int8);
    begin
      X := -X
    end;

    function MinusTwo: Int8;
    begin
      Result := -2
    end;

    begin
      L := -3;
      G := -4;
      R.Pad := 255; R.V := -5; R.W := 6;
      O := TObj.Create;
      O.V := -7;
      SA[2] := -8;
      SetLength(DA, 3);
      DA[1] := -9;
      Neg(R.W);
      I := 1;
      WriteLn(L, ' ', G, ' ', R.V, ' ', R.W, ' ', O.V, ' ', SA[2], ' ',
        DA[I], ' ', MinusTwo(), ' ', CA[0], ' ', CA[I], ' ', CA[2]);
      WriteLn(SizeOf(Int8), ' ', SizeOf(TRec), ' ', R.Pad);
      O.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '-3 -4 -5 -6 -7 -8 -9 -2 -1 100 -128' + #10 +
    '1 3 255' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_Int8_SignedSemantics;
const
  Src = '''
    program P;
    uses SysUtils;
    const
      K = Int8(200);
    var
      A, B: Int8;
      L: Int64;
    begin
      A := 127;
      A := A + 1;
      WriteLn(A);
      B := -1;
      WriteLn(B < 0, ' ', B < A, ' ', B > A);
      A := -100;
      WriteLn(A div 7, ' ', A mod 7);
      WriteLn(Low(Int8), ' ', High(Int8));
      L := 200;
      WriteLn(Int8(L), ' ', K);
      WriteLn(IntToStr(B), ' ', Format('%d', [B]))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '-128' + #10 +
    'True False True' + #10 +
    '-14 -2' + #10 +
    '-128 127' + #10 +
    '-56 -56' + #10 +
    '-1 -1' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_Int8_AcrossUnitInterface;
const
  UnitSrc = '''
    unit u8;
    interface
    type
      TPair8 = record A, B: Int8; end;
    const
      KMin: Int8 = -100;
    var
      G8: Int8;
    function Neg8(X: Int8): Int8;
    function MakePair(A, B: Int8): TPair8;
    procedure F(X: Int8); overload;
    procedure F(X: Byte); overload;
    implementation
    function Neg8(X: Int8): Int8; begin Result := -X end;
    function MakePair(A, B: Int8): TPair8; begin Result.A := A; Result.B := B end;
    procedure F(X: Int8); begin WriteLn('i8 ', X) end;
    procedure F(X: Byte); begin WriteLn('u8 ', X) end;
    initialization
      G8 := -42;
    end.
    ''';
  Src = '''
    program P;
    uses u8;
    var Pr: TPair8; X: Int8; Y: Byte;
    begin
      Pr := MakePair(-3, 4);
      X := -5; Y := 250;
      WriteLn(Neg8(7), ' ', G8, ' ', KMin, ' ', Pr.A, ' ', Pr.B);
      F(X); F(Y)
    end.
    ''';
var
  Output: string;
  RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithUnit('u8', UnitSrc, Src, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('output',
    '-7 -42 -100 -3 4' + #10 + 'i8 -5' + #10 + 'u8 250' + #10, Output);
end;

procedure TE2ETypeStdTests.TestRun_NarrowArg_ReachesClosestOverload;
const
  Src = '''
    program P;
    procedure A(X: Integer); overload; begin WriteLn('Integer') end;
    procedure A(X: Int64); overload; begin WriteLn('Int64') end;
    procedure A(X: Double); overload; begin WriteLn('Double') end;
    procedure W(X: Word); overload; begin WriteLn('Word') end;
    procedure W(X: SmallInt); overload; begin WriteLn('SmallInt') end;
    procedure L(X: Int64); overload; begin WriteLn('Int64') end;
    procedure L(X: Double); overload; begin WriteLn('Double') end;
    type
      TC = class
        procedure B(X: Int64); overload;
        procedure B(X: Integer); overload;
      end;
    procedure TC.B(X: Int64); begin WriteLn('m Int64') end;
    procedure TC.B(X: Integer); begin WriteLn('m Integer ', X) end;
    var
      V8: Int8; VB: Byte; VS: SmallInt; VI: Integer; O: TC;
    begin
      V8 := -1; VB := 2; VS := 3; VI := 4;
      A(V8); A(VB); A(VS);
      W(VB);
      L(VI);
      O := TC.Create();
      O.B(V8);
      O.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Integer' + #10 + 'Integer' + #10 + 'Integer' + #10 +
    'Word' + #10 + 'Int64' + #10 + 'm Integer -1' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_Format_U_Unsigned;
const
  Src = '''
    program P;
    uses SysUtils;
    var Q: UInt64; U: UInt32; I: Integer;
    begin
      Q := High(UInt64);
      U := High(UInt32);
      I := 42;
      WriteLn(Format('%u', [Q]));
      WriteLn(Format('%d', [Q]));
      WriteLn(Format('[%u] [%5u] [%-5u]', [U, I, I]));
      WriteLn(Format('%u%%', [I]))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '18446744073709551615' + #10 +
    '-1' + #10 +
    '[4294967295] [   42] [42   ]' + #10 +
    '42%' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_UnhintedLiteral_IsInt;
const
  Src = '''
    program P;
    const
      N = 42;
    procedure F(X: Integer); overload; begin WriteLn('Integer ', X) end;
    procedure F(X: Int64); overload; begin WriteLn('Int64 ', X) end;
    procedure G(X: Byte); begin WriteLn('Byte ', X) end;
    var
      I: Integer; B: Byte;
    begin
      F(42);
      F(N);
      WriteLn(SizeOf(N));
      WriteLn(1 shl 31);
      WriteLn(-1 shr 1);
      I := 7;
      F(I);
      G(200);
      B := 255;
      WriteLn(B + 1);
      F(High(Integer));
      WriteLn(I + 1 = 8)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Int64 42' + #10 +
    'Int64 42' + #10 +
    '8' + #10 +
    '2147483648' + #10 +
    '9223372036854775807' + #10 +
    'Integer 7' + #10 +
    'Byte 200' + #10 +
    '256' + #10 +
    'Integer 2147483647' + #10 +
    'True' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_Constants_AdaptToContext;
const
  Src = '''
    program P;
    const
      Buckets = 4096;
    procedure Q(X: UInt64); begin WriteLn('Q ', X) end;
    procedure F(X: Byte); overload; begin WriteLn('Byte ', X) end;
    procedure F(X: Integer); overload; begin WriteLn('Integer ', X) end;
    procedure Pair(const S: string; A, B: Integer); overload;
    begin WriteLn(S, ' Integer ', A + B) end;
    procedure Pair(const S: string; A, B: Int64); overload;
    begin WriteLn(S, ' Int64 ', A + B) end;
    procedure Tags(const Args: array of const);
    var I: Integer;
    begin
      for I := 0 to High(Args) do
        if Args[I].VType = vtInteger then
          Write(Integer(Args[I].VValue), ' ')
        else
          Write('tag', Args[I].VType, ' ');
      WriteLn()
    end;
    var
      U: UInt64; V: UInt64; I, K: Integer;
    begin
      U := 1;
      V := UInt64(1) shl 40 + 4097;
      WriteLn(U, ' ', V and (Buckets - 1), ' ', U + 2);
      Q(5);
      Q(Buckets);
      F(5);
      F(300);
      K := 7;
      Pair('mixed', 1, K);
      Tags([42, -1, Buckets, 5000000000]);
      I := ($FE shl 24) or $ED;
      WriteLn(I = -33554195, ' ', -33554195 = I, ' ', I < 0, ' ', 0 > I)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1 1 3' + #10 +
    'Q 5' + #10 +
    'Q 4096' + #10 +
    'Integer 5' + #10 +
    'Integer 300' + #10 +
    'mixed Integer 8' + #10 +
    '42 -1 4096 tag16 ' + #10 +
    'True True True True' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_OpenArrayLiteral_EveryCallShape;
const
  Src = '''
    program P;
    function Total(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do Result := Result * 10 + A[I]
    end;
    type
      TC = class
        S: Integer;
        constructor Create(const A: array of Integer);
        function Sum(const A: array of Integer): Integer;
        procedure Run;
      end;
    constructor TC.Create(const A: array of Integer);
    begin S := Total(A) end;
    function TC.Sum(const A: array of Integer): Integer;
    begin Result := Total(A) end;
    procedure TC.Run;
      procedure Show(const AName: string; const A: array of Integer);
      begin WriteLn(AName, ' ', Total(A)) end;
    begin
      Show('nested-in-method', [1, 2, 3])
    end;
    procedure Outer;
      procedure Show(const A: array of Integer);
      begin WriteLn('nested-proc ', Total(A)) end;
      function Calc(const A: array of Integer): Integer;
      begin Result := Total(A) end;
    begin
      Show([4, 5, 6]);
      WriteLn('nested-func ', Calc([7, 8, 9]))
    end;
    var O: TC;
    begin
      WriteLn('routine ', Total([1, 2, 3]));
      O := TC.Create([3, 2, 1]);
      WriteLn('ctor ', O.S, ' method ', O.Sum([6, 5, 4]));
      O.Run();
      O.Free();
      Outer()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'routine 123' + #10 +
    'ctor 321 method 654' + #10 +
    'nested-in-method 123' + #10 +
    'nested-proc 456' + #10 +
    'nested-func 789' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_BuiltinResults_AreInt;
const
  Src = '''
    program P;
    type
      TE = (eA, eB, eC);
      TN = (nNeg = -3, nZero = 0);
    procedure F(X: Integer); overload; begin WriteLn('Integer ', X) end;
    procedure F(X: Int64); overload; begin WriteLn('Int64 ', X) end;
    procedure OA(const X: array of Integer);
    begin
      F(Length(X));
      F(High(X))
    end;
    var
      S, Empty: string; A: array of Integer; SA: array[1..5] of Byte;
      I: Integer; B: Byte; E: TE; EN: TN; L, N: Int64;
    begin
      S := 'hello';
      Empty := '';
      SetLength(A, 3);
      F(Length(S));
      F(Length(A));
      F(Length(SA));
      F(High(S));
      F(High(Empty));
      F(High(A));
      F(Low(SA));
      F(Pos('l', S));
      F(Pos('z', S));
      F(PosEx('l', S, 3));
      F(PosEx('z', S, 0));
      F(SizeOf(I));
      I := -5;
      F(Ord(I));
      B := 200;
      F(Ord(B));
      E := eC;
      F(Ord(E));
      EN := nNeg;
      F(Ord(EN));
      F(Ord(True));
      OA([1, 2, 3]);
      F(High(Integer));
      L := Ord(I) * 1000000000;
      WriteLn(L);
      N := (Int64(1) shl 32) + 2;
      WriteLn(Copy(S, 1, N));
      N := 4;
      SetLength(A, N);
      WriteLn(Length(A));
      SetLength(S, N);
      WriteLn(Length(S))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Int64 5' + #10 +
    'Int64 3' + #10 +
    'Int64 5' + #10 +
    'Int64 4' + #10 +
    'Int64 -1' + #10 +
    'Int64 2' + #10 +
    'Int64 1' + #10 +
    'Int64 2' + #10 +
    'Int64 -1' + #10 +
    'Int64 3' + #10 +
    'Int64 -1' + #10 +
    'Int64 4' + #10 +
    'Int64 -5' + #10 +
    'Int64 200' + #10 +
    'Int64 2' + #10 +
    'Int64 -3' + #10 +
    'Int64 1' + #10 +
    'Int64 3' + #10 +
    'Int64 2' + #10 +
    'Integer 2147483647' + #10 +
    '-5000000000' + #10 +
    'ello' + #10 +
    '4' + #10 +
    '4' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_LengthAboveInt32_Works;
const
  Src = '''
    program P;
    var A: array of Byte; S: string; N: Int64;
    begin
      N := (Int64(1) shl 31) + 16;
      SetLength(A, N);
      A[N - 1] := 7;
      WriteLn(Length(A), ' ', High(A), ' ', A[High(A)], ' ', A[0]);
      SetLength(A, 0);
      SetLength(S, N);
      S[N - 1] := 'y';
      WriteLn(Length(S), ' ', Copy(S, N - 1, 1));
      S := '';
      WriteLn('released')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2147483664 2147483663 7 0' + #10 +
    '2147483664 y' + #10 +
    'released' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_NonNegativeInt_MixesWithUInt64;
const
  Src = '''
    program P;
    type
      TE = (eA, eB, eC);
    procedure Q(X: UInt64); begin WriteLn('Q ', X) end;
    var
      H: UInt64; S: string; I: Integer; B: Byte; E: TE; A: array of Word;
    begin
      S := 'hello';
      H := 14695981039346656037;
      for I := 0 to Length(S) - 1 do
        H := (H xor Ord(S[I])) * 1099511628211;
      WriteLn(H);
      B := 200;
      H := Ord(B) + H;
      WriteLn(H);
      E := eC;
      H := Ord(E);
      WriteLn(H);
      SetLength(A, 3);
      H := Length(A);
      H := H + SizeOf(I);
      WriteLn(H);
      Q(Length(S));
      WriteLn(H > Length(S))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '11831194018420276491' + #10 +
    '11831194018420276691' + #10 +
    '2' + #10 +
    '7' + #10 +
    'Q 5' + #10 +
    'True' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_StringAbove1GiB_Releases;
const
  Src = '''
    program P;
    var S: string;
    begin
      SetLength(S, 1100000000);
      S[High(S)] := 'x';
      WriteLn(Length(S));
      WriteLn(S[High(S)] = 'x');
      S := '';
      WriteLn('released ', Length(S))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '1100000000' + #10 + 'True' + #10 + 'released 0' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_CollectionCounts_AreInt;
const
  Src = '''
    program P;
    uses Generics.Collections, Classes, contnrs;
    procedure F(X: Integer); overload; begin WriteLn('Integer ', X) end;
    procedure F(X: Int64); overload; begin WriteLn('Int ', X) end;
    var
      L: TList<Integer>; St: TStack<Integer>; Q: TQueue<Integer>;
      S: TSet<Integer>; D: TDictionary<string, Integer>;
      OD: TOrderedDictionary<string, Integer>; M: IMap<string, Integer>;
      SL: TStringList; OL: TObjectList; C: TComponent; Idx: Int;
    begin
      L := TList<Integer>.Create;
      L.Add(3); L.Add(5);
      F(L.Count);
      F(L.IndexOf(5));
      if L.BinarySearch(5, (A, B) -> A - B, Idx) then F(Idx);
      L.FCount := 5000000000;
      WriteLn(L.Count);
      L.FCount := 2;
      St := TStack<Integer>.Create; St.Push(1);
      F(St.Count);
      Q := TQueue<Integer>.Create; Q.Enqueue(1);
      F(Q.Count);
      S := TSet<Integer>.Create; S.Include(1);
      F(S.Count);
      D := TDictionary<string, Integer>.Create; D.Add('a', 1);
      F(D.Count);
      M := D;
      F(M.GetCount);
      OD := TOrderedDictionary<string, Integer>.Create; OD.Add('a', 1);
      F(OD.Count);
      SL := TStringList.Create;
      F(SL.Add('b'));
      F(SL.Count);
      F(SL.IndexOf('b'));
      SL.Sorted := True;
      if SL.Find('b', Idx) then F(Idx);
      OL := TObjectList.Create(False);
      F(OL.Add(nil));
      F(OL.Count);
      C := TComponent.Create(nil);
      F(C.ComponentCount)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Int 2' + #10 + 'Int 1' + #10 + 'Int 1' + #10 + '5000000000' + #10 +
    'Int 1' + #10 + 'Int 1' + #10 + 'Int 1' + #10 + 'Int 1' + #10 +
    'Int 1' + #10 + 'Int 1' + #10 +
    'Int 0' + #10 + 'Int 1' + #10 + 'Int 0' + #10 + 'Int 0' + #10 +
    'Int 0' + #10 + 'Int 1' + #10 + 'Int 0' + #10, 0);
end;

procedure TE2ETypeStdTests.TestRun_MaxInt_IsHighInt;
const
  Src = '''
    program P;
    procedure F(X: Integer); overload; begin WriteLn('Integer ', X) end;
    procedure F(X: Int64); overload; begin WriteLn('Int ', X) end;
    var S: string;
    begin
      WriteLn(MaxInt);
      WriteLn(MaxInt = High(Int));
      F(MaxInt);
      S := 'abcdef';
      WriteLn(Copy(S, 2, MaxInt));
      Delete(S, 3, MaxInt);
      WriteLn(S)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '9223372036854775807' + #10 + 'True' + #10 +
    'Int 9223372036854775807' + #10 + 'cdef' + #10 + 'abc' + #10, 0);
end;

{ A class implementing a generic interface may spell the type argument with
  any alias of it: IEq<Int32> is IEq<Integer>, whichever is written first. }
procedure TE2ETypeStdTests.TestRun_ImplementsGenericInterface_AliasArgument;
const
  Src = '''
    program P;
    type
      IEq<T> = interface
        function Same(A, B: T): Boolean;
      end;
      TIntEq = class(IEq<Int32>)
        function Same(A, B: Int32): Boolean;
      end;
      TFloatEq = class(TObject, IEq<Float64>)
        function Same(A, B: Float64): Boolean;
      end;
    function TIntEq.Same(A, B: Int32): Boolean;
    begin
      Result := A = B
    end;
    function TFloatEq.Same(A, B: Float64): Boolean;
    begin
      Result := A = B
    end;
    var
      EI: IEq<Integer>;
      EF: IEq<Double>;
    begin
      EI := TIntEq.Create();
      EF := TFloatEq.Create();
      WriteLn(EI.Same(3, 3), ' ', EI.Same(3, 4));
      WriteLn(EF.Same(1.5, 1.5))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True False' + #10 + 'True' + #10, 0);
end;

{ A generic instance spelt with an alias argument, at any depth, is a valid
  receiver: TBox<TBox<Int32>>.Create() and TBox<Int32>.Create() resolve to
  the instances of TBox<TBox<Integer>> and TBox<Integer>. }
procedure TE2ETypeStdTests.TestRun_GenericReceiver_AliasArgument;
const
  Src = '''
    program P;
    type
      TBox<T> = class
        V: T;
      end;
    var
      B: TBox<TBox<Int32>>;
    begin
      B := TBox<TBox<Int32>>.Create();
      B.V := TBox<Int32>.Create();
      B.V.V := 41;
      WriteLn(B.V.V + 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + #10, 0);
end;

initialization
  RegisterTest(TE2ETypeStdTests);

end.
