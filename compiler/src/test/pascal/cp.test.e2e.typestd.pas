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
  RCode: Integer;
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

initialization
  RegisterTest(TE2ETypeStdTests);

end.
