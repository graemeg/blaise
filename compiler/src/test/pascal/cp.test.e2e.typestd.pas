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

initialization
  RegisterTest(TE2ETypeStdTests);

end.
