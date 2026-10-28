{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.numerics.decimal;

{ E2E tests for the Numerics.Decimal stdlib unit (TDecimal).

  These compile -> assemble -> link -> run real programs that use TDecimal and
  assert on stdout/exit code, on BOTH backends (CompileAndRunWithRTL runs QBE
  and native and requires parity).  The IR-only harness cannot see RTL contract
  or ABI issues, so the e2e layer is mandatory for this unit.

  Phase 0 coverage: construction (DecFromInt / DecFromInt64 / DecFromStr),
  ToString / ToPlainString (scale-preserving, never scientific), Scale, IsZero,
  Sign. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EDecimalTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { --- Construction + ToString round-trips --- }
    procedure TestRun_FromStr_RoundTrip_TwoDp;
    procedure TestRun_FromStr_NegativeFraction;
    procedure TestRun_FromStr_WholeNumber;
    procedure TestRun_FromStr_LeadingZeroFraction;
    procedure TestRun_FromStr_PreservesTrailingZeros;
    procedure TestRun_FromStr_PlusSign;

    { --- Scale --- }
    procedure TestRun_Scale_TwoDp;
    procedure TestRun_Scale_WholeNumberIsZero;

    { --- IsZero / Sign --- }
    procedure TestRun_IsZero_True;
    procedure TestRun_IsZero_FalseForSmallFraction;
    procedure TestRun_Sign_Negative;
    procedure TestRun_Sign_PositiveAndZero;

    { --- Integer construction --- }
    procedure TestRun_FromInt;
    procedure TestRun_FromInt64_Large;

    { --- ToPlainString never scientific --- }
    procedure TestRun_ToPlainString_NoExponent;

    { --- Value equality (the Java pitfall fix) --- }
    procedure TestRun_Equals_DifferentScale_True;
    procedure TestRun_Compare_OrdersByValue;
    procedure TestRun_Compare_NegativeOrdering;
    procedure TestRun_Hash_ValueEqualHashesMatch;
    procedure TestRun_Equals_ZeroScaleInsensitive;

    { --- Arithmetic --- }
    procedure TestRun_Add_SameScale;
    procedure TestRun_Add_MixedScale_ResultMaxScale;
    procedure TestRun_Subtract_Basic;
    procedure TestRun_Subtract_ToNegative;
    procedure TestRun_Negate;
    procedure TestRun_Abs_Negative;

    { --- Multiply + arbitrary precision (dual-backend) --- }
    procedure TestRun_Multiply_ScalesAdd;
    procedure TestRun_Multiply_Squared;
    procedure TestRun_Multiply_NegativeTimesPositive;
    procedure TestRun_FromStr_LargeValue_RoundTrip;
    procedure TestRun_Add_OverflowsInt64_Inflates;
    procedure TestRun_Multiply_BigProduct;

    { --- Division + rounding (dual-backend) --- }
    procedure TestRun_Divide_ExactToScale;
    procedure TestRun_Divide_NonTerminating_HalfEven;
    procedure TestRun_Divide_BankersRoundsToEven;
    procedure TestRun_Divide_HalfUp;
    procedure TestRun_RoundTo_HalfEven;
    procedure TestRun_RoundTo_IncreaseScaleIsExact;
    procedure TestRun_CustomStrategy_Truncates;
    procedure TestRun_Divide_ByZero_Raises;
    procedure TestRun_Money_TaxThenRound;

    { --- Float conversion + strip + out-conversions (dual-backend) --- }
    procedure TestRun_DecFromFloat_Safe;
    procedure TestRun_DecFromFloatExact_ShowsBinaryError;
    procedure TestRun_StripTrailingZeros_Fraction;
    procedure TestRun_StripTrailingZeros_KeepsIntegerZeros;
    procedure TestRun_ToInt64_TruncatesTowardZero;

    { --- Operators (dual-backend) --- }
    procedure TestRun_Operators_Arithmetic;
    procedure TestRun_Operators_Comparisons;
  end;

implementation

procedure TE2EDecimalTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-numerics-decimal');
end;

{ ------------------------------------------------------------------ }
{ Construction + ToString round-trips                                 }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_FromStr_RoundTrip_TwoDp;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('19.99'); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('19.99', '19.99', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_FromStr_NegativeFraction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('-0.0001'); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('-0.0001', '-0.0001', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_FromStr_WholeNumber;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('600'); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('600', '600', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_FromStr_LeadingZeroFraction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('0.50'); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('0.50', '0.50', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_FromStr_PreservesTrailingZeros;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Scale is retained for formatting; '4.0000' must NOT collapse to '4'. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('4.0000'); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('4.0000', '4.0000', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_FromStr_PlusSign;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('+5'); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('+5 -> 5', '5', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Scale                                                               }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_Scale_TwoDp;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('19.99'); WriteLn(IntToStr(A.Scale())) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('scale of 19.99', '2', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Scale_WholeNumberIsZero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('42'); WriteLn(IntToStr(A.Scale())) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('scale of 42', '0', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ IsZero / Sign                                                       }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_IsZero_True;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal, SysUtils;
    var A: TDecimal;
    begin A := DecFromInt(0); WriteLn(BoolToStr(A.IsZero(), True)) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('IsZero(0)', 'True', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_IsZero_FalseForSmallFraction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal, SysUtils;
    var A: TDecimal;
    begin A := DecFromStr('0.0001'); WriteLn(BoolToStr(A.IsZero(), True)) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('IsZero(0.0001)', 'False', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Sign_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromInt64(-42); WriteLn(IntToStr(A.Sign())) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Sign(-42)', '-1', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Sign_PositiveAndZero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B: TDecimal;
    begin
      A := DecFromStr('3.14');
      B := DecFromInt(0);
      WriteLn(IntToStr(A.Sign()), ' ', IntToStr(B.Sign()))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Sign(+) Sign(0)', '1 0', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Integer construction                                                }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_FromInt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromInt(12345); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('12345', '12345', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_FromInt64_Large;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromInt64(9223372036854775807); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('max int64', '9223372036854775807', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ ToPlainString never scientific                                      }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_ToPlainString_NoExponent;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromStr('0.00007'); WriteLn(A.ToPlainString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('no exponent', '0.00007', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Value equality (2.0 = 2.00) — the Java BigDecimal pitfall fix        }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_Equals_DifferentScale_True;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal, SysUtils;
    var A, B: TDecimal;
    begin
      A := DecFromStr('2.0');
      B := DecFromStr('2.00');
      WriteLn(BoolToStr(A.Equals(B), True))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('2.0 = 2.00', 'True', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Compare_OrdersByValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B: TDecimal;
    begin
      A := DecFromStr('2.0');
      B := DecFromStr('2.5');
      WriteLn(IntToStr(A.Compare(B)), ' ', IntToStr(B.Compare(A)), ' ',
              IntToStr(A.Compare(A)))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('lt gt eq', '-1 1 0', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Compare_NegativeOrdering;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B: TDecimal;
    begin
      A := DecFromStr('-1.5');
      B := DecFromStr('-2.0');
      WriteLn(IntToStr(A.Compare(B)))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('-1.5 > -2.0', '1', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Hash_ValueEqualHashesMatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Value-equal decimals must hash identically (safe as dictionary keys). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal, SysUtils;
    var A, B: TDecimal;
    begin
      A := DecFromStr('2.0');
      B := DecFromStr('2.00');
      WriteLn(BoolToStr(A.GetHashCode() = B.GetHashCode(), True))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('hash(2.0)=hash(2.00)', 'True', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Equals_ZeroScaleInsensitive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal, SysUtils;
    var A, B: TDecimal;
    begin
      A := DecFromStr('0.00');
      B := DecFromInt(0);
      WriteLn(BoolToStr(A.Equals(B), True))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('0.00 = 0', 'True', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Arithmetic                                                          }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_Add_SameScale;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('19.99'); B := DecFromStr('0.01');
      C := A.Add(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('19.99 + 0.01', '20.00', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Add_MixedScale_ResultMaxScale;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Result scale is max of the two operand scales (the exact-arithmetic rule). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('10'); B := DecFromStr('3.5');
      C := A.Add(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('10 + 3.5', '13.5', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Subtract_Basic;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('19.99'); B := DecFromStr('0.01');
      C := A.Subtract(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('19.99 - 0.01', '19.98', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Subtract_ToNegative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('1.5'); B := DecFromStr('2.25');
      C := A.Subtract(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.5 - 2.25', '-0.75', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Negate;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, C: TDecimal;
    begin
      A := DecFromStr('5.00'); C := A.Negate(); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('neg 5.00', '-5.00', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Abs_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, C: TDecimal;
    begin
      A := DecFromStr('-7.25'); C := A.Abs(); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('abs -7.25', '7.25', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Multiply + arbitrary precision (dual-backend)                       }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_Multiply_ScalesAdd;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Result scale = sum of operand scales: 2 + 2 = 4. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('19.99'); B := DecFromStr('0.20');
      C := A.Multiply(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('19.99 * 0.20', '3.9980', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Multiply_Squared;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('1.5'); B := DecFromStr('1.5');
      C := A.Multiply(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.5 * 1.5', '2.25', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Multiply_NegativeTimesPositive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('-3'); B := DecFromStr('7');
      C := A.Multiply(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('-3 * 7', '-21', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_FromStr_LargeValue_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 20 nines: exceeds Int64, must inflate and round-trip exactly. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin
      A := DecFromStr('99999999999999999999'); WriteLn(A.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('20 nines', '99999999999999999999', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Add_OverflowsInt64_Inflates;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 9e18 + 9e18 = 1.8e19 overflows Int64 and must inflate. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('9000000000000000000');
      B := DecFromStr('9000000000000000000');
      C := A.Add(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('9e18 + 9e18', '18000000000000000000', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Multiply_BigProduct;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('1000000000000'); B := DecFromStr('1000000000000');
      C := A.Multiply(B); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1e12 * 1e12', '1000000000000000000000000', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Division + rounding (dual-backend)                                   }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_Divide_ExactToScale;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('10'); B := DecFromStr('4');
      C := A.Divide(B, 2, rmHalfEven); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('10/4 @2', '2.50', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Divide_NonTerminating_HalfEven;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1/3 never terminates — must round at the target scale, never throw. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('1'); B := DecFromStr('3');
      C := A.Divide(B, 4, rmHalfEven); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1/3 @4', '0.3333', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Divide_BankersRoundsToEven;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 2.5 -> 2 and 3.5 -> 4 under banker's rounding (ties to even). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, One, C: TDecimal;
    begin
      One := DecFromStr('1');
      A := DecFromStr('2.5'); C := A.Divide(One, 0, rmHalfEven); Write(C.ToString(), ' ');
      A := DecFromStr('3.5'); C := A.Divide(One, 0, rmHalfEven); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('2.5->2 3.5->4', '2 4', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Divide_HalfUp;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, One, C: TDecimal;
    begin
      One := DecFromStr('1');
      A := DecFromStr('2.5'); C := A.Divide(One, 0, rmHalfUp); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('2.5 half-up', '3', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_RoundTo_HalfEven;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, C: TDecimal;
    begin
      A := DecFromStr('3.14159'); C := A.RoundTo(2, rmHalfEven); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('pi @2', '3.14', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_RoundTo_IncreaseScaleIsExact;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, C: TDecimal;
    begin
      A := DecFromStr('1.5'); C := A.RoundTo(4, rmHalfEven); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.5 @4', '1.5000', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_CustomStrategy_Truncates;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Inject a user IRoundingStrategy that always truncates: 2/3 @2 -> 0.66. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    type
      TTrunc = class(TObject, IRoundingStrategy)
        function RoundIncrement(Negative: Boolean; LastKeptDigit: Integer;
          DiscardedCompareHalf: Integer; AnyDiscarded: Boolean): Boolean;
      end;
    function TTrunc.RoundIncrement(Negative: Boolean; LastKeptDigit: Integer;
      DiscardedCompareHalf: Integer; AnyDiscarded: Boolean): Boolean;
    begin Result := False end;
    var A, B, C: TDecimal; S: IRoundingStrategy;
    begin
      S := TTrunc.Create();
      A := DecFromStr('2'); B := DecFromStr('3');
      C := A.Divide(B, 2, S); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('2/3 truncated @2', '0.66', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Divide_ByZero_Raises;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Division by zero raises EDivByZero -> non-zero exit. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('1'); B := DecFromStr('0');
      C := A.Divide(B, 2, rmHalfEven); WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertTrue('nonzero exit on div-by-zero', RCode <> 0);
end;

procedure TE2EDecimalTests.TestRun_Money_TaxThenRound;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 19.99 * 0.20 = 3.9980 exact; rounded to cents (banker's) = 4.00. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var Price, Rate, Tax, Rounded: TDecimal;
    begin
      Price := DecFromStr('19.99'); Rate := DecFromStr('0.20');
      Tax := Price.Multiply(Rate);
      Rounded := Tax.RoundTo(2, rmHalfEven);
      WriteLn(Tax.ToString(), ' ', Rounded.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('tax exact + rounded', '3.9980 4.00', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Float conversion + strip + out-conversions (dual-backend)           }
{ ------------------------------------------------------------------ }

procedure TE2EDecimalTests.TestRun_DecFromFloat_Safe;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Safe conversion takes the shortest decimal: 0.1 stays 0.1 (the Java trap fix). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin A := DecFromFloat(0.1); WriteLn(A.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('safe 0.1', '0.1', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_DecFromFloatExact_ShowsBinaryError;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { The exact path exposes the binary tail — it must NOT equal a clean 0.1. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, Clean: TDecimal;
    begin
      A := DecFromFloatExact(0.1);
      Clean := DecFromStr('0.1');
      WriteLn(BoolToStr(A.Equals(Clean), True))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('exact 0.1 <> clean 0.1', 'False', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_StripTrailingZeros_Fraction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, C: TDecimal;
    begin A := DecFromStr('1.2300'); C := A.StripTrailingZeros(); WriteLn(C.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.2300 stripped', '1.23', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_StripTrailingZeros_KeepsIntegerZeros;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 600 must stay 600 (never 6E+2) — integer-part zeros are not stripped. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, C: TDecimal;
    begin A := DecFromStr('600'); C := A.StripTrailingZeros(); WriteLn(C.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('600 stays 600', '600', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_ToInt64_TruncatesTowardZero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A: TDecimal;
    begin
      A := DecFromStr('42.99'); Write(Int64ToStr(A.ToInt64()), ' ');
      A := DecFromStr('-7.5');  WriteLn(Int64ToStr(A.ToInt64()))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('trunc toward zero', '42 -7', Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Operators_Arithmetic;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Each operator matches the method it delegates to.  The self-assigning
    and accumulating forms (S := S + A) are the common use. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, S: TDecimal; I: Integer;
    begin
      A := DecFromStr('1.25');
      B := DecFromStr('0.5');
      WriteLn((A + B).ToString(), ' ', (A - B).ToString(), ' ',
              (A * B).ToString(), ' ', (-A).ToString());
      WriteLn((A * 3).ToString(), ' ', (3 * A).ToString(), ' ',
              (A + B * DecFromInt(2)).ToString());
      S := DecFromInt(0);
      for I := 1 to 4 do
        S := S + A;
      S := S * S;
      WriteLn(S.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('arithmetic',
    '1.75 0.75 0.625 -1.25' + #10 + '3.75 3.75 2.25' + #10 + '25.0000',
    Trim(Output));
end;

procedure TE2EDecimalTests.TestRun_Operators_Comparisons;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Comparison is by value: 2.0 and 2.00 are equal. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Decimal;
    var A, B, C: TDecimal;
    begin
      A := DecFromStr('2.0');
      B := DecFromStr('2.00');
      C := DecFromStr('-3');
      WriteLn(A = B, ' ', A <> B, ' ', C < A, ' ', C > A, ' ',
              A <= B, ' ', A >= C, ' ', A < B)
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('comparisons', 'TRUE FALSE TRUE FALSE TRUE TRUE FALSE',
    UpperCase(Trim(Output)));
end;

initialization
  RegisterTest(TE2EDecimalTests);

end.
