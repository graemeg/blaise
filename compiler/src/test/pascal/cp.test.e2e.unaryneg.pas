{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.unaryneg;

{ E2E tests for unary minus (TNegExpr).

  IEEE 754 negation flips the sign bit, so -(+0.0) is -0.0 and 1 / -(+0.0)
  is -inf.  The old 0 - X desugaring computed 0.0 - 0.0 = +0.0 and lost the
  sign (BUG-20261026-float-neg-signed-zero).  Only a running program shows
  the sign of a zero, so the float cases live here; the integer matrix
  guards that the new lowering is bit-identical to the subtraction it
  replaced at every boundary of every integer kind.  Records exercise the
  `class operator Negative` lowering through both record-return routes
  (registers and the hidden sret pointer). }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EUnaryNegTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { -Z of a +0.0 Double is -0.0: local, global, parameter, field, literal }
    procedure TestRun_Neg_Double_SignedZero;
    procedure TestRun_Neg_Single_SignedZero;
    { negating twice restores +0.0; ordinary values negate as before }
    procedure TestRun_Neg_Float_Values;
    { a NaN's sign bit flips too }
    procedure TestRun_Neg_NaN_SignFlips;
    { -S of a Single picks the Single overload (it used to type as Double) }
    procedure TestRun_Neg_Single_PicksSingleOverload;
    { every integer kind at its boundaries, matching 0 - X exactly }
    procedure TestRun_Neg_IntegerMatrix;
    { negation of a call result, a captured local and an inline body }
    procedure TestRun_Neg_CallCaptureInline;
    { constant contexts: case labels, loop bounds, a negated default from a
      separately compiled unit }
    procedure TestRun_Neg_ConstContexts;
    procedure TestRun_Neg_DefaultFromUnit;
    { class operator Negative: register-return and sret records }
    procedure TestRun_Neg_RecordOperator_RegisterReturn;
    procedure TestRun_Neg_RecordOperator_ManagedField_Sret;
  end;

implementation

const
  LE = #10;

procedure TE2EUnaryNegTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-unaryneg');
end;

procedure TE2EUnaryNegTests.TestRun_Neg_Double_SignedZero;
const
  Src = '''
    program P;
    type
      TBox = record
        D: Float64;
      end;
    var
      G, R: Float64;
      B: TBox;
    function NegOf(X: Float64): Float64;
    begin
      Result := -X
    end;
    procedure Local;
    var Z, N: Float64;
    begin
      Z := 0.0;
      N := -Z;
      WriteLn('local ', N, ' ', 1.0 / N)
    end;
    begin
      Local();
      G := 0.0;
      R := -G;
      WriteLn('global ', R, ' ', 1.0 / R);
      R := NegOf(0.0);
      WriteLn('param ', R, ' ', 1.0 / R);
      B.D := 0.0;
      R := -B.D;
      WriteLn('field ', R, ' ', 1.0 / R);
      R := -0.0;
      WriteLn('literal ', R, ' ', 1.0 / R);
      WriteLn('inline ', 1.0 / -G)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'local -0 -inf' + LE +
    'global -0 -inf' + LE +
    'param -0 -inf' + LE +
    'field -0 -inf' + LE +
    'literal -0 -inf' + LE +
    'inline -inf' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_Single_SignedZero;
const
  Src = '''
    program P;
    var
      Z, N: Float32;
      B: UInt32;
    begin
      Z := 0.0;
      N := -Z;
      Move(N, B, 4);
      WriteLn(N, ' ', B);
      N := -N;
      Move(N, B, 4);
      WriteLn(N, ' ', B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '-0 2147483648' + LE + '0 0' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_Float_Values;
const
  Src = '''
    program P;
    var
      D, E: Float64;
      S, T: Float32;
    begin
      D := 0.0;
      E := -(-D);
      WriteLn(E, ' ', 1.0 / E);
      D := 2.5;
      WriteLn(-D, ' ', -(-D), ' ', 1.0 - -D);
      D := -1.25;
      WriteLn(-D);
      S := 1.5;
      T := -S * 2.0;
      WriteLn(T, ' ', -S)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0 inf' + LE +
    '-2.5 2.5 3.5' + LE +
    '1.25' + LE +
    '-3 -1.5' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_NaN_SignFlips;
const
  Src = '''
    program P;
    var
      Z, Q, N: Float64;
      A, B: Int64;
    begin
      Z := 0.0;
      Q := Z / Z;
      N := -Q;
      Move(Q, A, 8);
      Move(N, B, 8);
      WriteLn((A < 0) <> (B < 0));
      WriteLn((A xor B) = Low(Int64))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE + 'True' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_Single_PicksSingleOverload;
const
  Src = '''
    program P;
    procedure Show(X: Float32); overload;
    begin
      WriteLn('Float32 ', X)
    end;
    procedure Show(X: Float64); overload;
    begin
      WriteLn('Float64 ', X)
    end;
    var
      S: Float32;
      D: Float64;
    begin
      S := 1.5;
      D := 2.5;
      Show(-S);
      Show(-D)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'Float32 -1.5' + LE + 'Float64 -2.5' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_IntegerMatrix;
const
  { Expected values are what 0 - X gave: narrow kinds widen to Integer,
    Int64 / UInt64 keep their type and wrap at the boundary. }
  Src = '''
    program P;
    var
      I8: Int8; U8: Byte; I16: Int16; U16: UInt16;
      I32: Int32; U32: UInt32; I64: Int64; U64: UInt64;
      R: Int32; R64: Int64; RU: UInt64;
    procedure Neg8(var V: Int8);
    begin
      V := -V
    end;
    begin
      I8 := Low(Int8);   R := -I8;  WriteLn('i8 ', R);
      I8 := High(Int8);  R := -I8;  WriteLn('i8 ', R);
      U8 := High(Byte);  R := -U8;  WriteLn('u8 ', R);
      I16 := Low(Int16); R := -I16; WriteLn('i16 ', R);
      U16 := High(UInt16); R := -U16; WriteLn('u16 ', R);
      I32 := High(Int32); R := -I32; WriteLn('i32 ', R);
      I32 := Low(Int32);  R := -I32; WriteLn('i32 ', R);
      U32 := 1; R := -U32; WriteLn('u32 ', R);
      I64 := High(Int64); R64 := -I64; WriteLn('i64 ', R64);
      I64 := Low(Int64);  R64 := -I64; WriteLn('i64 ', R64);
      U64 := 1; RU := -U64; WriteLn('u64 ', RU);
      U64 := High(UInt64); RU := -U64; WriteLn('u64 ', RU);
      I8 := 5; Neg8(I8); WriteLn('var ', I8);
      I32 := 7; WriteLn('expr ', -I32 + 10, ' ', 3 - -I32, ' ', -I32 div 2, ' ',
        -I32 mod 4)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'i8 128' + LE +
    'i8 -127' + LE +
    'u8 -255' + LE +
    'i16 32768' + LE +
    'u16 -65535' + LE +
    'i32 -2147483647' + LE +
    'i32 -2147483648' + LE +
    'u32 -1' + LE +
    'i64 -9223372036854775807' + LE +
    'i64 -9223372036854775808' + LE +
    'u64 18446744073709551615' + LE +
    'u64 1' + LE +
    'var -5' + LE +
    'expr 3 10 -3 -3' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_CallCaptureInline;
const
  Src = '''
    program P;
    type
      TFn = reference to function: Float64;
    function Five: Int;
    begin
      Result := 5
    end;
    function NegInl(X: Int): Int; inline;
    begin
      Result := -X
    end;
    procedure Outer;
    var
      K: Int;
      Z: Float64;
      F: TFn;
      procedure Inner;
      begin
        WriteLn('nested ', -K)
      end;
    begin
      K := 9;
      Z := 0.0;
      Inner();
      F := function: Float64
        begin
          Result := -Z
        end;
      WriteLn('closure ', 1.0 / F())
    end;
    begin
      WriteLn('call ', -Five(), ' ', -(Five() * 2));
      WriteLn('inline ', NegInl(4));
      Outer()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'call -5 -10' + LE +
    'inline -4' + LE +
    'nested -9' + LE +
    'closure -inf' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_ConstContexts;
const
  Src = '''
    program P;
    const
      K = 3;
    var
      I, N: Int;
      A: array[-2..2] of Int;
    procedure Show(X: Int = -1);
    begin
      Write(X, ' ')
    end;
    begin
      for I := -2 to 2 do
        A[I] := I * 10;
      for I := -K + 1 to -K + 3 do
        Write(I, ' ');
      WriteLn();
      WriteLn(A[-2], ' ', A[-1]);
      for N := -3 to 1 do
        case N of
          -3: Write('a ');
          -2, -1: Write('b ');
          -K + 3: Write('z ');
        else
          Write('o ')
        end;
      WriteLn();
      Show();
      Show(-K);
      WriteLn()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '-2 -1 0 ' + LE +
    '-20 -10' + LE +
    'a b b z o ' + LE +
    '-1 -3 ' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_DefaultFromUnit;
const
  UnitSrc = '''
    unit negdefs;
    interface
    procedure ShowInt(A: Int = -7);
    procedure ShowZero(B: Float64 = -0.0);
    implementation
    procedure ShowInt(A: Int);
    begin
      WriteLn('int ', A)
    end;
    procedure ShowZero(B: Float64);
    begin
      WriteLn('zero ', B, ' ', 1.0 / B)
    end;
    end.
    ''';
  Src = '''
    program P;
    uses negdefs;
    begin
      ShowInt();
      ShowZero()
    end.
    ''';
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile + run',
    CompileAndRunWithUnit('negdefs', UnitSrc, Src, Output, RCode));
  AssertEquals('output', 'int -7' + LE + 'zero -0 -inf' + LE, Output);
  AssertEquals('exit code', 0, RCode);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_RecordOperator_RegisterReturn;
const
  Src = '''
    program P;
    type
      TVec = record
        X, Y: Int;
        class operator Negative(const A: TVec): TVec;
        class operator Add(const A, B: TVec): TVec;
      end;
    class operator TVec.Negative(const A: TVec): TVec;
    begin
      Result.X := -A.X;
      Result.Y := -A.Y
    end;
    class operator TVec.Add(const A, B: TVec): TVec;
    begin
      Result.X := A.X + B.X;
      Result.Y := A.Y + B.Y
    end;
    var V, W: TVec;
    begin
      V.X := 3; V.Y := -4;
      W := -V;
      WriteLn(W.X, ' ', W.Y);
      W := -(-V);
      WriteLn(W.X, ' ', W.Y);
      W := V + -V;
      WriteLn(W.X, ' ', W.Y)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '-3 4' + LE + '3 -4' + LE + '0 0' + LE, 0);
end;

procedure TE2EUnaryNegTests.TestRun_Neg_RecordOperator_ManagedField_Sret;
const
  Src = '''
    program P;
    type
      TTagged = record
        Name: string;
        N: Int;
        class operator Negative(const A: TTagged): TTagged;
      end;
    class operator TTagged.Negative(const A: TTagged): TTagged;
    begin
      Result.Name := 'neg(' + A.Name + ')';
      Result.N := -A.N
    end;
    procedure Show(const T: TTagged);
    begin
      WriteLn(T.Name, ' ', T.N)
    end;
    var
      A, B: TTagged;
      I: Int;
    begin
      A.Name := 'a';
      A.N := 2;
      B := -A;
      Show(B);
      Show(-B);
      for I := 1 to 3 do
        B := -B;
      Show(B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'neg(a) -2' + LE +
    'neg(neg(a)) 2' + LE +
    'neg(neg(neg(neg(a)))) 2' + LE, 0);
end;

initialization
  RegisterTest(TE2EUnaryNegTests);

end.
