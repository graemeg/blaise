{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Numerics.Money;

{ Blaise StdLib — currency-aware monetary amounts.

  TMoney is a thin VALUE-TYPE wrapper that layers an ISO-4217 currency tag onto
  an exact TDecimal amount (see Numerics.Decimal).  It is the money type; the
  numeric core (TDecimal) stays currency- and locale-agnostic, matching the
  universal pattern of Moneta (Java), the money gem (Ruby) and rusty-money
  (Rust), each of which wraps a decimal rather than baking currency into the
  numeric type.  See docs/language-rationale.adoc.

  Design:

    - Currency is an ISO-4217 alphabetic code held as a string ('USD', 'JPY',
      'KWD').  This is open-ended: a code the built-in registry does not know is
      still accepted and uses the fallback scale (2).  The code is upper-cased
      on construction so 'usd' and 'USD' are the same currency.

    - Each currency has a default minor-unit scale: JPY 0, USD 2, KWD 3, and a
      fallback of 2 for unknown codes.  Every TMoney is NORMALISED to its
      currency's scale on construction and after every arithmetic operation.
      The default rounding is banker's (rmHalfEven) — the recommended money
      default — so MoneyFromStr('1.005', 'USD') stores 1.00 and a JPY amount
      never carries a fraction.  Each constructor and rounding-sensitive
      operation also has overloads taking an explicit TRoundingMode or a custom
      IRoundingStrategy (the same eight modes + extension point as TDecimal), so
      the rounding policy can be swapped per call — e.g. rmHalfUp for a
      jurisdiction that rounds halves up, or an IRoundingStrategy implementing
      Swedish/Swiss 0.05 cash rounding.

    - Mismatched-currency arithmetic RAISES EMoneyMismatch.  Add, Subtract and
      Compare across different currencies are programming errors, not silent
      conversions (there is no exchange-rate concept here — that is a higher
      policy layer).

    - Immutable value semantics: every operation returns a fresh TMoney and
      never mutates Self.  Scaling by a quantity (Multiply) keeps the same
      currency and re-normalises to its scale.

  Construction uses free functions (MoneyFromStr / MoneyFromDecimal /
  MoneyFromInt / MoneyZero), following the Numerics.Decimal and DateUtils
  house style.  Queries and arithmetic are record methods; the arithmetic
  and comparisons are also available as operators (Total := Price * 2 + Fee),
  which delegate to those methods. }

interface

uses
  SysUtils, Numerics.Decimal;

type
  { Base class for all errors raised by this unit. }
  EMoneyError = class(Exception);

  { Raised when an operation combines two TMoney values of different
    currencies (e.g. USD + JPY). }
  EMoneyMismatch = class(EMoneyError);

  { ------------------------------------------------------------------ }
  { TMoney — a decimal amount tagged with an ISO-4217 currency          }
  { ------------------------------------------------------------------ }

  { A monetary amount in a single currency.  See the unit header for the
    design rationale.  The amount is always held at the currency's default
    scale (banker's-rounded on every operation). }
  TMoney = record
    { The exact amount, normalised to the currency's default scale. }
    FAmount:   TDecimal;
    { ISO-4217 alphabetic currency code, upper-case (e.g. 'USD'). }
    FCurrency: string;

    { The amount as an exact TDecimal (at the currency scale).
      @returns the monetary amount. }
    function Amount: TDecimal;

    { The ISO-4217 currency code (upper-case).
      @returns the currency code string. }
    function CurrencyCode: string;

    { Tests whether the amount is exactly zero.
      @returns True iff the amount is zero. }
    function IsZero: Boolean;

    { Sign of the amount.
      @returns -1 if negative, 0 if zero, +1 if positive. }
    function Sign: Int;

    { Sum of Self and B.  Both must be the same currency; the result is in that
      currency, normalised to its scale.  The no-mode form uses banker's
      rounding (rmHalfEven); the others let the caller pick the rounding mode or
      a custom strategy for the (rare) case where the addends' common scale
      exceeds the currency scale.
      @param B the amount to add.
      @returns Self + B.
      @raises EMoneyMismatch if the currencies differ. }
    function Add(const B: TMoney): TMoney; overload;
    function Add(const B: TMoney; Mode: TRoundingMode): TMoney; overload;
    function Add(const B: TMoney; const Strategy: IRoundingStrategy): TMoney; overload;

    { Difference Self - B.  Both must be the same currency.  Rounding control as
      for Add.
      @param B the amount to subtract.
      @returns Self - B.
      @raises EMoneyMismatch if the currencies differ. }
    function Subtract(const B: TMoney): TMoney; overload;
    function Subtract(const B: TMoney; Mode: TRoundingMode): TMoney; overload;
    function Subtract(const B: TMoney; const Strategy: IRoundingStrategy): TMoney; overload;

    { Arithmetic negation (-Self), same currency and scale.  Exact — no rounding.
      @returns the amount with opposite sign. }
    function Negate: TMoney;

    { Scales the amount by a dimensionless TDecimal factor (e.g. unit price *
      quantity, or amount * tax-rate), re-normalising to the currency scale.
      The no-mode form uses banker's rounding (rmHalfEven); the others take an
      explicit rounding mode or custom strategy.  The currency is preserved.
      @param Factor the multiplier.
      @returns Self * Factor at the currency scale. }
    function Multiply(const Factor: TDecimal): TMoney; overload;
    function Multiply(const Factor: TDecimal; Mode: TRoundingMode): TMoney; overload;
    function Multiply(const Factor: TDecimal; const Strategy: IRoundingStrategy): TMoney; overload;

    { Scales the amount by an integer quantity.  Exact at the currency scale (an
      integer multiply introduces no new fraction digits), so no rounding mode is
      needed.  The currency is preserved.
      @param Quantity the integer multiplier.
      @returns Self * Quantity. }
    function MultiplyInt(Quantity: Int): TMoney;

    { Three-way comparison by amount.  Both must be the same currency.
      @param B the amount to compare against.
      @returns -1 if Self < B, 0 if equal, +1 if Self > B.
      @raises EMoneyMismatch if the currencies differ. }
    function Compare(const B: TMoney): Int32;

    { Value equality: same currency AND equal amount.  Unlike Compare, this does
      NOT raise on a currency mismatch — two amounts in different currencies are
      simply not equal.
      @param B the amount to compare against.
      @returns True iff same currency and equal amount. }
    function Equals(const B: TMoney): Boolean;

    { The bare amount as a plain decimal string at the currency scale, with no
      currency code (e.g. '19.99').  Never scientific notation.
      @returns the amount string. }
    function AmountString: string;

    { Amount followed by a space and the currency code (e.g. '19.99 USD').
      @returns the formatted monetary string. }
    function ToString: string;

    { Operators.  Each delegates to the method of the same meaning, with
      banker's rounding where the method takes a rounding mode; use the
      methods for any other mode or strategy.
        + -              same currency, else EMoneyMismatch (as Add/Subtract)
        unary -          Negate
        *                by a TDecimal factor or an Integer quantity, either
                         order (as Multiply / MultiplyInt)
        < > <= >=        same currency, else EMoneyMismatch (as Compare)
        = <>             currency AND amount; never raise (as Equals)
      There is no `/`: splitting an amount needs an explicit rounding policy,
      and adding a bare number to an amount has no currency. }
    class operator Add(const A, B: TMoney): TMoney;
    class operator Subtract(const A, B: TMoney): TMoney;
    class operator Negative(const A: TMoney): TMoney;
    class operator Multiply(const A: TMoney; const B: TDecimal): TMoney;
    class operator Multiply(const A: TDecimal; const B: TMoney): TMoney;
    class operator Multiply(const A: TMoney; B: Int): TMoney;
    class operator Multiply(A: Int; const B: TMoney): TMoney;
    class operator Equal(const A, B: TMoney): Boolean;
    class operator NotEqual(const A, B: TMoney): Boolean;
    class operator LessThan(const A, B: TMoney): Boolean;
    class operator GreaterThan(const A, B: TMoney): Boolean;
    class operator LessThanOrEqual(const A, B: TMoney): Boolean;
    class operator GreaterThanOrEqual(const A, B: TMoney): Boolean;
  end;

{ ------------------------------------------------------------------ }
{ Construction (free functions, house style)                          }
{ ------------------------------------------------------------------ }

{ Builds a TMoney from a decimal literal string and a currency code.  The
  amount is parsed exactly (see DecFromStr) then normalised to the currency's
  default scale.  The no-mode form uses banker's rounding (rmHalfEven); the
  others take an explicit rounding mode or a custom strategy.
  @param AAmount  the decimal literal (e.g. '19.99', '-0.005').
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @param Mode      the rounding mode (mode overload).
  @param Strategy  the rounding strategy (strategy overload).
  @returns the money value.
  @raises EDecimalParse if AAmount is malformed. }
function MoneyFromStr(const AAmount, ACurrency: string): TMoney; overload;
function MoneyFromStr(const AAmount, ACurrency: string;
                      Mode: TRoundingMode): TMoney; overload;
function MoneyFromStr(const AAmount, ACurrency: string;
                      const Strategy: IRoundingStrategy): TMoney; overload;

{ Builds a TMoney from an existing TDecimal amount and a currency code,
  normalised to the currency's default scale (banker's rounding by default; the
  mode/strategy overloads override it).
  @param AAmount  the decimal amount.
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @param Mode      the rounding mode (mode overload).
  @param Strategy  the rounding strategy (strategy overload).
  @returns the money value. }
function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string): TMoney; overload;
function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string;
                          Mode: TRoundingMode): TMoney; overload;
function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string;
                          const Strategy: IRoundingStrategy): TMoney; overload;

{ Builds a TMoney from a whole-unit integer amount and a currency code
  (e.g. MoneyFromInt(5, 'USD') = 5.00 USD).  An integer is exact at any
  currency scale, so no rounding mode is needed.
  @param AAmount  the whole-unit integer amount.
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @returns the money value. }
function MoneyFromInt(AAmount: Int; const ACurrency: string): TMoney;

{ A zero amount in the given currency, at the currency scale.
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @returns zero money in that currency. }
function MoneyZero(const ACurrency: string): TMoney;

{ ------------------------------------------------------------------ }
{ Currency registry                                                   }
{ ------------------------------------------------------------------ }

{ The default minor-unit scale (number of fraction digits) for a currency code.
  Known: JPY 0, USD/EUR/GBP/AUD/CAD/CHF/CNY 2, KWD/BHD/OMR 3.  Unknown codes
  return the fallback scale 2.  The lookup is case-insensitive.
  @param ACurrency the ISO-4217 code.
  @returns the default fraction-digit count for that currency. }
function CurrencyScale(const ACurrency: string): Int;

implementation

const
  { Fallback minor-unit scale for currencies the registry does not list. }
  cDefaultScale = 2;

function CurrencyScale(const ACurrency: string): Int;
var
  C: string;
begin
  C := UpperCase(ACurrency);
  { Zero-decimal currencies. }
  if (C = 'JPY') or (C = 'KRW') or (C = 'CLP') or (C = 'ISK') or
     (C = 'VND') or (C = 'XAF') or (C = 'XOF') or (C = 'PYG') then
    Result := 0
  { Three-decimal currencies. }
  else if (C = 'KWD') or (C = 'BHD') or (C = 'OMR') or (C = 'TND') or
          (C = 'JOD') or (C = 'IQD') or (C = 'LYD') then
    Result := 3
  { Everything else (USD, EUR, GBP, ...) uses two. }
  else
    Result := cDefaultScale;
end;

{ Normalises ADec to ACurrency's scale with the given rounding strategy and
  pairs it with the upper-cased code.  Central constructor used by every public
  builder so the invariant "FAmount is always at the currency scale" holds in
  one place. }
function MakeMoneyS(const ADec: TDecimal; const ACurrency: string;
                    const AStrategy: IRoundingStrategy): TMoney;
var
  Code: string;
  Norm: TDecimal;
begin
  Code := UpperCase(ACurrency);
  Norm := ADec.RoundTo(CurrencyScale(Code), AStrategy);
  Result.FAmount := Norm;
  Result.FCurrency := Code;
end;

{ As MakeMoneyS but selecting one of the eight standard rounding modes. }
function MakeMoneyM(const ADec: TDecimal; const ACurrency: string;
                    AMode: TRoundingMode): TMoney;
begin
  Result := MakeMoneyS(ADec, ACurrency, StandardRounding(AMode));
end;

{ Default normalisation: banker's rounding (rmHalfEven). }
function MakeMoney(const ADec: TDecimal; const ACurrency: string): TMoney;
begin
  Result := MakeMoneyM(ADec, ACurrency, rmHalfEven);
end;

function MoneyFromStr(const AAmount, ACurrency: string): TMoney;
begin
  Result := MakeMoney(DecFromStr(AAmount), ACurrency);
end;

function MoneyFromStr(const AAmount, ACurrency: string;
                      Mode: TRoundingMode): TMoney;
begin
  Result := MakeMoneyM(DecFromStr(AAmount), ACurrency, Mode);
end;

function MoneyFromStr(const AAmount, ACurrency: string;
                      const Strategy: IRoundingStrategy): TMoney;
begin
  Result := MakeMoneyS(DecFromStr(AAmount), ACurrency, Strategy);
end;

function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string): TMoney;
begin
  Result := MakeMoney(AAmount, ACurrency);
end;

function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string;
                          Mode: TRoundingMode): TMoney;
begin
  Result := MakeMoneyM(AAmount, ACurrency, Mode);
end;

function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string;
                          const Strategy: IRoundingStrategy): TMoney;
begin
  Result := MakeMoneyS(AAmount, ACurrency, Strategy);
end;

function MoneyFromInt(AAmount: Int; const ACurrency: string): TMoney;
begin
  Result := MakeMoney(DecFromInt(AAmount), ACurrency);
end;

function MoneyZero(const ACurrency: string): TMoney;
begin
  Result := MakeMoney(DecFromInt(0), ACurrency);
end;

{ Raises EMoneyMismatch when A and B are different currencies.  AOp names the
  operation for the message. }
procedure RequireSameCurrency(const A, B: TMoney; const AOp: string);
begin
  if A.FCurrency <> B.FCurrency then
    raise EMoneyMismatch.Create('Numerics.Money: cannot ' + AOp +
      ' different currencies (' + A.FCurrency + ' and ' + B.FCurrency + ')');
end;

function TMoney.Amount: TDecimal;
begin
  Result := Self.FAmount;
end;

function TMoney.CurrencyCode: string;
begin
  Result := Self.FCurrency;
end;

function TMoney.IsZero: Boolean;
begin
  Result := Self.FAmount.IsZero();
end;

function TMoney.Sign: Int;
begin
  Result := Self.FAmount.Sign();
end;

function TMoney.Add(const B: TMoney; const Strategy: IRoundingStrategy): TMoney;
var
  Sum: TDecimal;
begin
  RequireSameCurrency(Self, B, 'add');
  Sum := Self.FAmount.Add(B.FAmount);
  Result := MakeMoneyS(Sum, Self.FCurrency, Strategy);
end;

function TMoney.Add(const B: TMoney; Mode: TRoundingMode): TMoney;
begin
  Result := Self.Add(B, StandardRounding(Mode));
end;

function TMoney.Add(const B: TMoney): TMoney;
begin
  Result := Self.Add(B, StandardRounding(rmHalfEven));
end;

function TMoney.Subtract(const B: TMoney; const Strategy: IRoundingStrategy): TMoney;
var
  Diff: TDecimal;
begin
  RequireSameCurrency(Self, B, 'subtract');
  Diff := Self.FAmount.Subtract(B.FAmount);
  Result := MakeMoneyS(Diff, Self.FCurrency, Strategy);
end;

function TMoney.Subtract(const B: TMoney; Mode: TRoundingMode): TMoney;
begin
  Result := Self.Subtract(B, StandardRounding(Mode));
end;

function TMoney.Subtract(const B: TMoney): TMoney;
begin
  Result := Self.Subtract(B, StandardRounding(rmHalfEven));
end;

function TMoney.Negate: TMoney;
var
  Neg: TDecimal;
begin
  Neg := Self.FAmount.Negate();
  Result := MakeMoney(Neg, Self.FCurrency);
end;

function TMoney.Multiply(const Factor: TDecimal; const Strategy: IRoundingStrategy): TMoney;
var
  Prod: TDecimal;
begin
  Prod := Self.FAmount.Multiply(Factor);
  Result := MakeMoneyS(Prod, Self.FCurrency, Strategy);
end;

function TMoney.Multiply(const Factor: TDecimal; Mode: TRoundingMode): TMoney;
begin
  Result := Self.Multiply(Factor, StandardRounding(Mode));
end;

function TMoney.Multiply(const Factor: TDecimal): TMoney;
begin
  Result := Self.Multiply(Factor, StandardRounding(rmHalfEven));
end;

function TMoney.MultiplyInt(Quantity: Int): TMoney;
var
  Prod: TDecimal;
begin
  Prod := Self.FAmount.Multiply(DecFromInt(Quantity));
  Result := MakeMoney(Prod, Self.FCurrency);
end;

function TMoney.Compare(const B: TMoney): Int32;
begin
  RequireSameCurrency(Self, B, 'compare');
  Result := Self.FAmount.Compare(B.FAmount);
end;

function TMoney.Equals(const B: TMoney): Boolean;
begin
  if Self.FCurrency <> B.FCurrency then
    Result := False
  else
    Result := Self.FAmount.Equals(B.FAmount);
end;

function TMoney.AmountString: string;
begin
  Result := Self.FAmount.ToString();
end;

function TMoney.ToString: string;
begin
  Result := Self.FAmount.ToString() + ' ' + Self.FCurrency;
end;

{ ------------------------------------------------------------------ }
{ Operators                                                            }
{ ------------------------------------------------------------------ }

class operator TMoney.Add(const A, B: TMoney): TMoney;
begin
  Result := A.Add(B);
end;

class operator TMoney.Subtract(const A, B: TMoney): TMoney;
begin
  Result := A.Subtract(B);
end;

class operator TMoney.Negative(const A: TMoney): TMoney;
begin
  Result := A.Negate();
end;

class operator TMoney.Multiply(const A: TMoney; const B: TDecimal): TMoney;
begin
  Result := A.Multiply(B);
end;

class operator TMoney.Multiply(const A: TDecimal; const B: TMoney): TMoney;
begin
  Result := B.Multiply(A);
end;

class operator TMoney.Multiply(const A: TMoney; B: Int): TMoney;
begin
  Result := A.MultiplyInt(B);
end;

class operator TMoney.Multiply(A: Int; const B: TMoney): TMoney;
begin
  Result := B.MultiplyInt(A);
end;

class operator TMoney.Equal(const A, B: TMoney): Boolean;
begin
  Result := A.Equals(B);
end;

class operator TMoney.NotEqual(const A, B: TMoney): Boolean;
begin
  Result := not A.Equals(B);
end;

class operator TMoney.LessThan(const A, B: TMoney): Boolean;
begin
  Result := A.Compare(B) < 0;
end;

class operator TMoney.GreaterThan(const A, B: TMoney): Boolean;
begin
  Result := A.Compare(B) > 0;
end;

class operator TMoney.LessThanOrEqual(const A, B: TMoney): Boolean;
begin
  Result := A.Compare(B) <= 0;
end;

class operator TMoney.GreaterThanOrEqual(const A, B: TMoney): Boolean;
begin
  Result := A.Compare(B) >= 0;
end;

end.
