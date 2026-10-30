{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.numerics.money;

{ E2E tests for the Numerics.Money stdlib unit (TMoney).

  These compile -> assemble -> link -> run real programs that use TMoney and
  assert on stdout/exit code, on BOTH backends (CompileAndRunWithRTL runs QBE
  and native and requires parity).  TMoney wraps TDecimal, so these also serve
  as end-to-end coverage of the nested-managed-record return + interface-param
  + record-copy paths that TDecimal exercises.

  Coverage: construction + currency normalisation (per-currency scale, banker's
  rounding), case-insensitive currency codes, ToString, arithmetic
  (Add/Subtract/Negate/Multiply/MultiplyInt), currency-mismatch raising,
  Compare/Equals, IsZero/Sign, and the CurrencyScale registry. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EMoneyTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { --- Construction + normalisation --- }
    procedure TestRun_FromStr_TwoDp;
    procedure TestRun_FromStr_BankersRoundsHalfToEven;
    procedure TestRun_FromStr_CurrencyCodeUppercased;
    procedure TestRun_FromStr_JPY_ZeroScale;
    procedure TestRun_FromStr_KWD_ThreeScale;
    procedure TestRun_FromStr_UnknownCurrency_DefaultScale;
    procedure TestRun_FromInt;
    procedure TestRun_Zero;

    { --- ToString / AmountString --- }
    procedure TestRun_ToString_WithCode;
    procedure TestRun_AmountString_NoCode;

    { --- Arithmetic (same currency) --- }
    procedure TestRun_Add_SameCurrency;
    procedure TestRun_Subtract_SameCurrency;
    procedure TestRun_Negate;
    procedure TestRun_MultiplyInt_Quantity;
    procedure TestRun_Multiply_TaxRate_BankersRound;

    { --- Currency mismatch raises --- }
    procedure TestRun_Add_MismatchRaises;
    procedure TestRun_Subtract_MismatchRaises;
    procedure TestRun_Compare_MismatchRaises;

    { --- Compare / Equals / IsZero / Sign --- }
    procedure TestRun_Compare_OrdersByAmount;
    procedure TestRun_Equals_DifferentScaleSameValue;
    procedure TestRun_Equals_DifferentCurrency_False;
    procedure TestRun_IsZero_And_Sign;

    { --- Configurable rounding (mode + custom strategy overloads) --- }
    procedure TestRun_FromStr_RoundingMode_HalfUp;
    procedure TestRun_FromStr_RoundingMode_Down;
    procedure TestRun_FromStr_RoundingMode_Ceiling;
    procedure TestRun_FromDecimal_RoundingMode;
    procedure TestRun_Add_RoundingMode;
    procedure TestRun_Multiply_RoundingMode_Ceiling;
    procedure TestRun_FromStr_CustomStrategy_Truncates;
    procedure TestRun_DefaultIsBankers;

    { --- Registry --- }
    procedure TestRun_CurrencyScale_Registry;

    { --- A small realistic flow --- }
    procedure TestRun_Invoice_LineItemsAndTax;

    { --- Operators --- }
    procedure TestRun_Operators_Arithmetic;
    procedure TestRun_Operators_Comparisons;
    procedure TestRun_Operators_MismatchRaises;
    procedure TestRun_Operators_Invoice;
  end;

implementation

procedure TE2EMoneyTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-numerics-money');
end;

{ ------------------------------------------------------------------ }
{ Construction + normalisation                                        }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_FromStr_TwoDp;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyFromStr('19.99', 'USD'); WriteLn(M.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('19.99 USD', '19.99 USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_BankersRoundsHalfToEven;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1.005 at 2dp, banker's: ties to even -> 1.00 (not 1.01). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyFromStr('1.005', 'USD'); WriteLn(M.AmountString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.005 -> 1.00', '1.00', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_CurrencyCodeUppercased;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyFromStr('5.00', 'usd'); WriteLn(M.CurrencyCode()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('lowercase -> USD', 'USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_JPY_ZeroScale;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { JPY has scale 0 — a fractional input rounds to a whole number. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyFromStr('199.6', 'JPY'); WriteLn(M.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('200 JPY', '200 JPY', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_KWD_ThreeScale;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { KWD has scale 3 — banker's at the 4th digit: 1.2345 -> 1.234. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyFromStr('1.2345', 'KWD'); WriteLn(M.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.234 KWD', '1.234 KWD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_UnknownCurrency_DefaultScale;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { An unknown code is accepted at the fallback scale of 2. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyFromStr('3.456', 'ZZZ'); WriteLn(M.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('3.46 ZZZ', '3.46 ZZZ', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromInt;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyFromInt(5, 'EUR'); WriteLn(M.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('5.00 EUR', '5.00 EUR', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Zero;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var M: TMoney;
    begin M := MoneyZero('GBP'); WriteLn(M.ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('0.00 GBP', '0.00 GBP', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ ToString / AmountString                                            }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_ToString_WithCode;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin WriteLn(MoneyFromStr('-0.5', 'USD').ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('-0.50 USD', '-0.50 USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_AmountString_NoCode;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin WriteLn(MoneyFromStr('42', 'USD').AmountString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('42.00', '42.00', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Arithmetic (same currency)                                         }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_Add_SameCurrency;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B, C: TMoney;
    begin
      A := MoneyFromStr('19.99', 'USD');
      B := MoneyFromStr('0.01', 'USD');
      C := A.Add(B);
      WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('20.00 USD', '20.00 USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Subtract_SameCurrency;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B, C: TMoney;
    begin
      A := MoneyFromStr('5.00', 'USD');
      B := MoneyFromStr('7.25', 'USD');
      C := A.Subtract(B);
      WriteLn(C.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('-2.25 USD', '-2.25 USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Negate;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin WriteLn(MoneyFromStr('3.50', 'USD').Negate().ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('-3.50 USD', '-3.50 USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_MultiplyInt_Quantity;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Unit price * quantity. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin WriteLn(MoneyFromStr('19.99', 'USD').MultiplyInt(3).ToString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('59.97 USD', '59.97 USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Multiply_TaxRate_BankersRound;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 19.99 * 1.08 = 21.5892 -> 21.59 at 2dp (banker's). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    var M: TMoney;
    begin
      M := MoneyFromStr('19.99', 'USD').Multiply(DecFromStr('1.08'));
      WriteLn(M.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('21.59 USD', '21.59 USD', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Currency mismatch raises                                           }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_Add_MismatchRaises;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B, C: TMoney;
    begin
      A := MoneyFromStr('1.00', 'USD');
      B := MoneyFromStr('100', 'JPY');
      try
        C := A.Add(B);
        WriteLn('no-raise')
      except
        on E: EMoneyMismatch do WriteLn('mismatch')
      end
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('raises', 'mismatch', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Subtract_MismatchRaises;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B, C: TMoney;
    begin
      A := MoneyFromStr('5.00', 'EUR');
      B := MoneyFromStr('1.00', 'USD');
      try
        C := A.Subtract(B);
        WriteLn('no-raise')
      except
        on E: EMoneyMismatch do WriteLn('mismatch')
      end
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('raises', 'mismatch', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Compare_MismatchRaises;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B: TMoney; R: Int;
    begin
      A := MoneyFromStr('5.00', 'EUR');
      B := MoneyFromStr('5.00', 'USD');
      try
        R := A.Compare(B);
        WriteLn('no-raise ', R)
      except
        on E: EMoneyMismatch do WriteLn('mismatch')
      end
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('raises', 'mismatch', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Compare / Equals / IsZero / Sign                                  }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_Compare_OrdersByAmount;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B: TMoney;
    begin
      A := MoneyFromStr('19.99', 'USD');
      B := MoneyFromStr('20.00', 'USD');
      WriteLn(A.Compare(B), ' ', B.Compare(A), ' ', A.Compare(A))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('-1 1 0', '-1 1 0', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Equals_DifferentScaleSameValue;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 2 and 2.00 in the same currency are equal (value-based, like TDecimal). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin
      WriteLn(MoneyFromStr('2', 'USD').Equals(MoneyFromStr('2.00', 'USD')))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('equal', 'True', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Equals_DifferentCurrency_False;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Same amount, different currency -> not equal (and does NOT raise). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin
      WriteLn(MoneyFromStr('2.00', 'USD').Equals(MoneyFromStr('2.00', 'EUR')))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('not equal', 'False', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_IsZero_And_Sign;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin
      WriteLn(MoneyZero('USD').IsZero(), ' ',
              MoneyFromStr('-1.00', 'USD').Sign(), ' ',
              MoneyFromStr('1.00', 'USD').Sign())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('True -1 1', 'True -1 1', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Configurable rounding                                              }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_FromStr_RoundingMode_HalfUp;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { rmHalfUp rounds the 1.005 tie up, unlike the banker's default (1.00). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin WriteLn(MoneyFromStr('1.005', 'USD', rmHalfUp).AmountString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.005 halfUp -> 1.01', '1.01', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_RoundingMode_Down;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { rmDown truncates toward zero: 1.999 -> 1.99. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin WriteLn(MoneyFromStr('1.999', 'USD', rmDown).AmountString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.999 down -> 1.99', '1.99', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_RoundingMode_Ceiling;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { rmCeiling rounds toward +infinity: 1.991 -> 1.99? no — 1.991 -> 2.00 only at
    scale 0; at scale 2 the third digit 1 rounds up to 1.992... use a clearer
    case: 1.001 ceiling at 2dp -> 1.01. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin WriteLn(MoneyFromStr('1.001', 'USD', rmCeiling).AmountString()) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.001 ceiling -> 1.01', '1.01', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromDecimal_RoundingMode;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    var M: TMoney;
    begin
      M := MoneyFromDecimal(DecFromStr('2.345'), 'USD', rmHalfUp);
      WriteLn(M.AmountString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('2.345 halfUp -> 2.35', '2.35', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Add_RoundingMode;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Two values whose common scale exceeds the currency scale; rmHalfUp on Add. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    var A, C: TMoney;
    begin
      A := MoneyFromDecimal(DecFromStr('1.004'), 'USD', rmDown);  { 1.00 }
      C := A.Add(MoneyFromDecimal(DecFromStr('2.005'), 'USD', rmDown), rmHalfUp);
      WriteLn(C.AmountString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  { A=1.00; the addend is normalised by rmDown to 2.00, so 1.00+2.00 = 3.00. }
  AssertEquals('add @halfUp', '3.00', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Multiply_RoundingMode_Ceiling;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 10.00 * 1.0851 = 10.851 -> ceiling at 2dp -> 10.86. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    var M: TMoney;
    begin
      M := MoneyFromStr('10.00', 'USD').Multiply(DecFromStr('1.0851'), rmCeiling);
      WriteLn(M.AmountString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('mul @ceiling', '10.86', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_FromStr_CustomStrategy_Truncates;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A custom IRoundingStrategy that always truncates (never increments). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    type
      TTrunc = class(TObject, IRoundingStrategy)
        function RoundIncrement(Negative: Boolean; LastKeptDigit: Int;
          DiscardedCompareHalf: Int; AnyDiscarded: Boolean): Boolean;
      end;
    function TTrunc.RoundIncrement(Negative: Boolean; LastKeptDigit: Int;
      DiscardedCompareHalf: Int; AnyDiscarded: Boolean): Boolean;
    begin Result := False end;
    var M: TMoney; S: IRoundingStrategy;
    begin
      S := TTrunc.Create;
      M := MoneyFromStr('9.999', 'USD', S);
      WriteLn(M.AmountString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('custom truncate -> 9.99', '9.99', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_DefaultIsBankers;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { The no-mode overloads keep banker's: 2.5 and 3.5 at scale 0 -> 2 and 4. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin
      WriteLn(MoneyFromStr('2.5', 'JPY').AmountString(), ' ',
              MoneyFromStr('3.5', 'JPY').AmountString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('banker default', '2 4', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Registry                                                          }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_CurrencyScale_Registry;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    begin
      WriteLn(CurrencyScale('JPY'), ' ', CurrencyScale('USD'), ' ',
              CurrencyScale('KWD'), ' ', CurrencyScale('zzz'))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('0 2 3 2', '0 2 3 2', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ A small realistic flow                                            }
{ ------------------------------------------------------------------ }

procedure TE2EMoneyTests.TestRun_Invoice_LineItemsAndTax;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 2 x 9.99 + 1 x 4.50 = 24.48; +8% tax = 26.4384 -> 26.44.
    Note: each step writes a DISTINCT variable — never `M := M.Method(...)` —
    because self-assigning a record-method result aliases Self (see bugs.txt). }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    var LineA, Subtotal, Total: TMoney;
    begin
      LineA := MoneyFromStr('9.99', 'USD').MultiplyInt(2);
      Subtotal := LineA.Add(MoneyFromStr('4.50', 'USD'));
      WriteLn('subtotal ', Subtotal.ToString());
      Total := Subtotal.Multiply(DecFromStr('1.08'));
      WriteLn('total ', Total.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('invoice',
    'subtotal 24.48 USD' + #10 + 'total 26.44 USD', Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Operators_Arithmetic;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 2.50 x 4 = 10.00; 10% off = 9.00; 3 x 2.50 + 0.10 x 2.50 = 7.75;
    accumulating 0.25 three times = 0.75. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    var Price, Gross, Net, Q, Total: TMoney; R: TDecimal; I: Int;
    begin
      Price := MoneyFromStr('2.50', 'GBP');
      R := DecFromStr('0.10');
      Gross := Price * 4;
      Net := Gross - Gross * R;
      WriteLn(Gross.ToString(), ' ', Net.ToString());
      Q := 3 * Price + R * Price;
      WriteLn(Q.ToString(), ' ', (-Q).ToString());
      Total := MoneyZero('GBP');
      for I := 1 to 3 do
        Total := Total + MoneyFromStr('0.25', 'GBP');
      Total := Total - Price * R;
      WriteLn(Total.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('arithmetic',
    '10.00 GBP 9.00 GBP' + #10 + '7.75 GBP -7.75 GBP' + #10 + '0.50 GBP',
    Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Operators_Comparisons;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { = and <> compare currency and amount and never raise; the ordering
    operators compare amounts in one currency. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B, U: TMoney;
    begin
      A := MoneyFromStr('1.00', 'USD');
      B := MoneyFromStr('2.50', 'USD');
      U := MoneyFromStr('1.00', 'EUR');
      WriteLn(A = MoneyFromStr('1', 'USD'), ' ', A <> B, ' ', A < B, ' ',
              A > B, ' ', A <= A, ' ', B >= A);
      WriteLn(A = U, ' ', A <> U)
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('comparisons',
    'TRUE TRUE TRUE FALSE TRUE TRUE' + #10 + 'FALSE TRUE',
    UpperCase(Trim(Output)));
end;

procedure TE2EMoneyTests.TestRun_Operators_MismatchRaises;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money;
    var A, B, C: TMoney; Q: Boolean;
    begin
      A := MoneyFromStr('1.00', 'USD');
      B := MoneyFromStr('100', 'JPY');
      try
        C := A + B;
        WriteLn('no-raise')
      except
        on E: EMoneyMismatch do WriteLn('add mismatch')
      end;
      try
        C := A - B;
        WriteLn('no-raise')
      except
        on E: EMoneyMismatch do WriteLn('subtract mismatch')
      end;
      try
        Q := A < B;
        WriteLn('no-raise')
      except
        on E: EMoneyMismatch do WriteLn('compare mismatch')
      end
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('raises',
    'add mismatch' + #10 + 'subtract mismatch' + #10 + 'compare mismatch',
    Trim(Output));
end;

procedure TE2EMoneyTests.TestRun_Operators_Invoice;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { TestRun_Invoice_LineItemsAndTax with operators: same results. }
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Numerics.Money, Numerics.Decimal;
    var Subtotal, Total: TMoney;
    begin
      Subtotal := MoneyFromStr('9.99', 'USD') * 2 + MoneyFromStr('4.50', 'USD');
      WriteLn('subtotal ', Subtotal.ToString());
      Total := Subtotal * DecFromStr('1.08');
      WriteLn('total ', Total.ToString())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('invoice',
    'subtotal 24.48 USD' + #10 + 'total 26.44 USD', Trim(Output));
end;

initialization
  RegisterTest(TE2EMoneyTests);

end.
