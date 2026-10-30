{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Numerics.Decimal;

{ Blaise StdLib — arbitrary-precision exact decimal arithmetic.

  TDecimal is a single exact base-10 number for FINANCIAL and exact-decimal use:
  money, billing, tax, currency conversion, and any value that is decimal by
  definition and where rounding error would be a correctness bug.  It deliberately
  replaces the historical proliferation of fixed types (Delphi/FPC Currency, Comp)
  with one type, mirroring the string-consolidation philosophy of the language
  (one `string`, not a family).  See docs/language-rationale.adoc for the full
  rationale and the comparison against Java's java.math.BigDecimal.

  NOT for scientific / engineering computing.  Use Double (with the Math unit)
  for that: floating point runs on hardware, is far faster, and is the natural
  domain of transcendental functions (Sin/Cos/Sqrt/Ln) whose results are
  irrational anyway, so exact decimal representation buys nothing.  TDecimal
  deliberately offers no such functions.  "High precision" here means an
  arbitrary number of exact DECIMAL places, not more significant binary digits
  (it is not an Extended/quad-float replacement).

  Design decisions (and how they improve on Java's BigDecimal):

    - Value = unscaled / 10^Scale.  Scale is a signed Integer (a negative scale
      represents tens/hundreds, e.g. 6E+2 = unscaled 6, scale -2).

    - Hybrid representation: the common case (money, anything fitting in an
      Int64 unscaled value) is held inline in a single Int64 with zero heap
      allocation; only genuinely large / high-precision values inflate to a
      little-endian array-of-UInt32 magnitude.  This gives fixed-point speed for
      the common path and arbitrary range for the tail.

    - Immutable VALUE semantics.  Every operation returns a fresh TDecimal and
      never mutates Self.  Because TDecimal is a value-type record (not a heap
      object like Java's BigDecimal), the common path allocates nothing — the
      immutability comes for free without per-operation garbage.

    - Value-based equality.  2.0 and 2.00 compare EQUAL (Java's BigDecimal makes
      them unequal under equals(), which silently breaks hash containers).  The
      scale is retained for formatting only, not for identity.

    - Mandatory rounding on division.  Unlike BigDecimal.divide, there is no
      overload that throws on a non-terminating quotient (1/3) or silently
      truncates — division always carries an explicit target scale and rounding
      mode/strategy.

  Construction uses free functions (DecFromInt / DecFromInt64 / DecFromStr /
  DecFromFloat) following the DateUtils house style.  Arithmetic and queries are
  record methods. }

interface

uses
  SysUtils;

type
  { Arbitrary-precision magnitude: decimal digits (each 0..9), little-endian
    (least-significant digit at index 0), canonical (no trailing zero digits;
    empty = zero).  Used only on the inflated path. }
  TDigitMag = array of UInt32;

  { Base class for all errors raised by this unit. }
  EDecimalError = class(Exception);

  { Raised by DecFromStr when the input is not a valid decimal literal. }
  EDecimalParse = class(EDecimalError);

  { Raised when a value would exceed an internal bound (reserved). }
  EDecimalOverflow = class(EDecimalError);

  { Raised when rmUnnecessary rounding is requested but rounding is actually
    needed (i.e. the operation could not be performed exactly at the target
    scale). }
  EDecimalRounding = class(EDecimalError);

  { The eight standard rounding modes, matching IEEE 754 / Java RoundingMode /
    .NET MidpointRounding.  rmHalfEven (banker's rounding) is the recommended
    default for money: it removes the upward bias of always rounding ties up.

      rmUp          away from zero
      rmDown        toward zero (truncate)
      rmCeiling     toward +infinity
      rmFloor       toward -infinity
      rmHalfUp      nearest; ties away from zero
      rmHalfDown    nearest; ties toward zero
      rmHalfEven    nearest; ties to the even neighbour (banker's)
      rmUnnecessary assert exactness; raises EDecimalRounding if rounding needed }
  TRoundingMode = (rmUp, rmDown, rmCeiling, rmFloor,
                   rmHalfUp, rmHalfDown, rmHalfEven, rmUnnecessary);

  { Strategy interface for injecting a custom rounding algorithm into Divide /
    RoundTo / SetScale.  The eight TRoundingMode values are themselves provided
    as ready-made strategies via StandardRounding, so the enum is sugar over
    this interface (one code path).  Implement this to add custom rounding —
    e.g. Swedish/Swiss 0.05 cash rounding, or currency-specific tie rules —
    without changing the library.

    The method is told everything needed to decide whether to round the
    truncated magnitude AWAY from zero by one unit in the last kept place:

      Negative          sign of the value being rounded.
      LastKeptDigit     the final retained digit (0..9) — needed for ties-to-even.
      DiscardedCompareHalf
                        sign of (discarded fraction - 1/2): -1 below half,
                        0 exactly half, +1 above half.
      AnyDiscarded      True if any nonzero digit was discarded at all.

    Return True to increment the magnitude (round away from zero), False to keep
    the truncated value. }
  IRoundingStrategy = interface
    function RoundIncrement(Negative: Boolean; LastKeptDigit: Integer;
                            DiscardedCompareHalf: Integer;
                            AnyDiscarded: Boolean): Boolean;
  end;

  { Concrete IRoundingStrategy for the eight standard TRoundingMode behaviours;
    obtained via StandardRounding(Mode).  Exposed so it can be subclassed or
    referenced, though most users go through the enum overloads. }
  TStandardRounding = class(TObject, IRoundingStrategy)
    FMode: TRoundingMode;
    constructor Create(AMode: TRoundingMode);
    function RoundIncrement(Negative: Boolean; LastKeptDigit: Integer;
                            DiscardedCompareHalf: Integer;
                            AnyDiscarded: Boolean): Boolean;
  end;

  { ------------------------------------------------------------------ }
  { TDecimal — exact arbitrary-precision decimal                        }
  { ------------------------------------------------------------------ }

  { An exact base-10 number.  See the unit header for the design rationale.

    Phase 0 surface (this file currently implements construction, formatting and
    queries on the inline/compact path only).  Arithmetic, value equality,
    inflation to the limb array and rounding land in later phases. }
  TDecimal = record
    { Unscaled value when the number fits in an Int64 (the common path). }
    FCompact:  Int64;
    { Little-endian decimal-digit magnitude; empty unless FInflated is True. }
    FMag:      TDigitMag;
    { Fraction-digit count.  SIGNED: a negative scale multiplies by 10^-Scale,
      e.g. unscaled 6 with scale -2 is the value 600.  value = unscaled*10^-Scale. }
    FScale:    Integer;
    { Sign of the magnitude when FInflated is True (FCompact carries its own
      sign on the compact path). }
    FNegative: Boolean;
    { False => the value lives in FCompact; True => it lives in FMag/FNegative. }
    FInflated: Boolean;

    { Number of fraction digits (the stored scale).  May be negative.
      @returns the signed scale. }
    function Scale: Integer;

    { Tests whether this value is exactly zero (any scale).
      @returns True iff the numeric value is zero. }
    function IsZero: Boolean;

    { Sign of the value.
      @returns -1 if negative, 0 if zero, +1 if positive. }
    function Sign: Integer;

    { Sum of Self and B.  The result scale is max(Self.Scale, B.Scale) — the
      exact-arithmetic rule (no rounding, no precision loss).  Addends are
      aligned to the common scale first.
      @param B the value to add.
      @returns Self + B.
      @raises EDecimalOverflow if the exact result exceeds the compact range
                              (limb-array support lands in a later phase). }
    function Add(const B: TDecimal): TDecimal;

    { Difference Self - B.  Result scale is max(Self.Scale, B.Scale).
      @param B the value to subtract.
      @returns Self - B.
      @raises EDecimalOverflow if the exact result exceeds the compact range. }
    function Subtract(const B: TDecimal): TDecimal;

    { Exact product Self * B.  The result scale is Self.Scale + B.Scale (the
      exact-arithmetic rule for multiplication — scales add).  No rounding is
      applied; use RoundTo afterwards to pin a fixed result scale.
      @param B the multiplicand.
      @returns the exact product. }
    function Multiply(const B: TDecimal): TDecimal;

    { Arithmetic negation (-Self).  The scale is preserved.
      @returns the value with opposite sign. }
    function Negate: TDecimal;

    { Absolute value (|Self|).  The scale is preserved.
      @returns the non-negative magnitude. }
    function Abs: TDecimal;

    { Divides Self by B, producing a result with exactly TargetScale fraction
      digits, rounded according to Mode.

      Unlike Java's BigDecimal.divide there is no overload that throws on a
      non-terminating quotient (e.g. 1/3) or silently truncates — division
      always carries an explicit target scale and rounding mode/strategy.

      @param B           the divisor; dividing by zero raises EDivByZero.
      @param TargetScale fraction digits in the result (signed).
      @param Mode        rounding mode for the dropped remainder.  rmHalfEven
                         (banker's) is the recommended money default.
      @returns           the quotient at TargetScale.
      @raises EDivByZero       if B is zero.
      @raises EDecimalRounding if Mode is rmUnnecessary and rounding was needed. }
    function Divide(const B: TDecimal; TargetScale: Integer;
                    Mode: TRoundingMode): TDecimal; overload;

    { As above, but rounding is delegated to a custom strategy (the extension
      point for cash rounding and currency-specific rules).
      @param B           the divisor; zero raises EDivByZero.
      @param TargetScale fraction digits in the result.
      @param Strategy    the rounding strategy to apply.
      @returns           the quotient at TargetScale. }
    function Divide(const B: TDecimal; TargetScale: Integer;
                    const Strategy: IRoundingStrategy): TDecimal; overload;

    { Returns Self rounded to NewScale fraction digits using Mode.  Increasing
      the scale pads with zeros (exact); decreasing it rounds.
      @param NewScale the target fraction-digit count.
      @param Mode     the rounding mode.
      @returns        Self at NewScale.
      @raises EDecimalRounding if Mode is rmUnnecessary and rounding was needed. }
    function RoundTo(NewScale: Integer; Mode: TRoundingMode): TDecimal; overload;

    { As above, with a custom rounding strategy.
      @param NewScale the target fraction-digit count.
      @param Strategy the rounding strategy.
      @returns        Self at NewScale. }
    function RoundTo(NewScale: Integer;
                     const Strategy: IRoundingStrategy): TDecimal; overload;

    { Alias of RoundTo(NewScale, Mode), named for parity with .NET/Java setScale.
      @param NewScale the target fraction-digit count.
      @param Mode     the rounding mode.
      @returns        Self at NewScale. }
    function SetScale(NewScale: Integer; Mode: TRoundingMode): TDecimal;

    { Three-way VALUE comparison.  The two operands are aligned to a common
      scale before comparing, so 2.0 and 2.00 compare equal — the scale does NOT
      participate in ordering (this is the deliberate fix for Java BigDecimal's
      scale-sensitive equals/compareTo split).
      @param B the value to compare against.
      @returns -1 if Self < B, 0 if Self = B, +1 if Self > B. }
    function Compare(const B: TDecimal): Integer;

    { Value equality.  2.0 equals 2.00 (contrast Java, where they are unequal).
      @param B the value to compare against.
      @returns True iff Self and B have the same numeric value. }
    function Equals(const B: TDecimal): Boolean;

    { Hash code consistent with Equals: two value-equal decimals (e.g. 2.0 and
      2.00) hash the same, because the hash is computed over the value with
      trailing zeros removed.  This makes TDecimal safe as a dictionary key,
      unlike Java's BigDecimal whose hashCode folds in the scale.
      @returns a hash of the numeric value. }
    function GetHashCode: Integer;

    { Canonical decimal text, scale-preserving, NEVER in scientific notation.
      A value with scale 4 always renders with four fraction digits
      (e.g. '4.0000'); a negative scale renders the trailing zeros as integer
      digits (e.g. unscaled 6 scale -2 renders '600').
      @returns the plain decimal string. }
    function ToString: string;

    { Identical to ToString.  Named for parity with Java's toPlainString and to
      document the guarantee that no exponent form is ever produced.
      @returns the plain decimal string. }
    function ToPlainString: string;

    { Returns a value EQUAL to Self with trailing fraction zeros removed (the
      minimal scale that still represents the value exactly).  E.g. 4.0000 ->
      4 (scale 0), 1.2300 -> 1.23.  Never produces scientific notation, unlike
      Java's stripTrailingZeros (which can yield 6E+2 for 600).
      @returns the value with minimal scale. }
    function StripTrailingZeros: TDecimal;

    { Converts to the nearest Double.  Lossy: a Double cannot represent most
      decimals exactly, so use this only at the boundary with floating-point
      APIs, never for further exact arithmetic.
      @returns the closest Double. }
    function ToDouble: Float64;

    { Truncates toward zero to a 64-bit integer (drops any fraction).
      @returns the integer part.
      @raises EDecimalOverflow if the integer part does not fit in Int64. }
    function ToInt64: Int64;

    { Operators.  Each delegates to the method of the same meaning, so the
      two forms always agree: A + B is A.Add(B), A < B is A.Compare(B) < 0.
      Comparison is by value (2.0 = 2.00), as Compare and Equals are.
      There is deliberately no `/`: a division needs an explicit target scale
      and rounding mode, so it stays the Divide method. }
    class operator Add(const A, B: TDecimal): TDecimal;
    class operator Subtract(const A, B: TDecimal): TDecimal;
    class operator Multiply(const A, B: TDecimal): TDecimal;
    class operator Multiply(const A: TDecimal; B: Integer): TDecimal;
    class operator Multiply(A: Integer; const B: TDecimal): TDecimal;
    class operator Negative(const A: TDecimal): TDecimal;
    class operator Equal(const A, B: TDecimal): Boolean;
    class operator NotEqual(const A, B: TDecimal): Boolean;
    class operator LessThan(const A, B: TDecimal): Boolean;
    class operator GreaterThan(const A, B: TDecimal): Boolean;
    class operator LessThanOrEqual(const A, B: TDecimal): Boolean;
    class operator GreaterThanOrEqual(const A, B: TDecimal): Boolean;
  end;

{ ------------------------------------------------------------------ }
{ Construction (free functions, DateUtils house style)                }
{ ------------------------------------------------------------------ }

{ Builds a TDecimal from a 32-bit signed integer (scale 0).
  @param V the integer value.
  @returns the exact decimal V. }
function DecFromInt(V: Integer): TDecimal;

{ Builds a TDecimal from a 64-bit signed integer (scale 0).
  @param V the integer value.
  @returns the exact decimal V. }
function DecFromInt64(V: Int64): TDecimal;

{ Parses an exact decimal from its textual form.  This is the recommended way
  to introduce a decimal literal because it is exact — there is no binary-float
  rounding on the path (contrast DecFromFloat).

  Accepts an optional leading '+' or '-', a run of digits, and an optional
  single '.' followed by more digits (e.g. '-19.99', '0.0001', '600', '+5').
  The scale of the result is the number of digits after the point.  Values too
  large for the Int64 compact path automatically inflate — there is no size
  limit beyond available memory.

  @param S the decimal literal.
  @returns the exact decimal value.
  @raises EDecimalParse if S is empty or malformed. }
function DecFromStr(const S: string): TDecimal;

{ Builds a TDecimal from a Double using its SHORTEST decimal representation —
  the value you would see printed (DecFromFloat(0.1) is exactly 0.1, NOT the
  0.1000000000000000055... that the raw binary holds).  This is the safe, almost
  always intended conversion, and the deliberate fix for Java BigDecimal's
  double-constructor trap.
  @param V the Double value.
  @returns the shortest exact decimal equal to V's printed form. }
function DecFromFloat(V: Float64): TDecimal;

{ Builds a TDecimal from the Double's binary value to high precision, exposing
  the representation error (DecFromFloatExact(0.1) carries the 0.100000...005...
  tail).  This is almost never what you want — it is provided, explicitly named,
  so the dangerous path is opt-in rather than the default.
  @param V the Double value.
  @returns the high-precision decimal of V's actual binary value. }
function DecFromFloatExact(V: Float64): TDecimal;

{ ------------------------------------------------------------------ }
{ Rounding                                                            }
{ ------------------------------------------------------------------ }

{ Returns a ready-made IRoundingStrategy implementing one of the eight standard
  TRoundingMode behaviours.  This is how the enum overloads of Divide/RoundTo
  delegate to the single strategy-based code path.
  @param Mode the standard rounding mode.
  @returns a strategy object implementing that mode. }
function StandardRounding(Mode: TRoundingMode): IRoundingStrategy;

implementation

const
  { Largest magnitude an Int64 can hold; used for compact-path overflow checks.
    Declared as a typed Int64 constant (NOT the Int64(...) value-cast form, which
    the QBE backend mis-lowers for large literals). }
  cMaxInt64Div10: Int64 = 922337203685477580;    { High(Int64) div 10 }
  cMaxInt64Mod10: Integer = 7;                    { High(Int64) mod 10 }

{ ------------------------------------------------------------------ }
{ Standard rounding strategy                                          }
{ ------------------------------------------------------------------ }

constructor TStandardRounding.Create(AMode: TRoundingMode);
begin
  FMode := AMode
end;

function TStandardRounding.RoundIncrement(Negative: Boolean;
                                          LastKeptDigit: Integer;
                                          DiscardedCompareHalf: Integer;
                                          AnyDiscarded: Boolean): Boolean;
begin
  { No discarded digits => the result is exact, never round. }
  if not AnyDiscarded then
  begin
    Result := False;
    Exit
  end;

  case FMode of
    rmUp:
      Result := True;                         { away from zero }
    rmDown:
      Result := False;                        { toward zero (truncate) }
    rmCeiling:
      Result := not Negative;                 { toward +inf }
    rmFloor:
      Result := Negative;                     { toward -inf }
    rmHalfUp:
      Result := DiscardedCompareHalf >= 0;    { ties away from zero }
    rmHalfDown:
      Result := DiscardedCompareHalf > 0;     { ties toward zero }
    rmHalfEven:
      begin
        if DiscardedCompareHalf > 0 then
          Result := True
        else if DiscardedCompareHalf < 0 then
          Result := False
        else
          Result := (LastKeptDigit mod 2) = 1   { exactly half: round to even }
      end;
    rmUnnecessary:
      raise EDecimalRounding.Create(
        'TDecimal: rounding required but rmUnnecessary was specified');
    else
      Result := False
  end
end;

function StandardRounding(Mode: TRoundingMode): IRoundingStrategy;
begin
  Result := TStandardRounding.Create(Mode)
end;

{ ------------------------------------------------------------------ }
{ Internal helpers                                                     }
{ ------------------------------------------------------------------ }

{ Appends the decimal digits of a NON-negative Int64 to Buf (no sign). }
function DigitsOf(V: Int64): string;
begin
  { Int64ToStr already produces the minimal digit string; for non-negative V
    there is no sign to strip. }
  Result := Int64ToStr(V)
end;

{ Renders a value given its magnitude digit string (no sign, no leading zeros),
  a sign, and a scale, as plain decimal text — scale-preserving, never
  scientific.  Shared by the compact and inflated paths. }
function FormatValue(const Digits: string; Neg: Boolean; AScale: Integer): string;
var
  DLen:   Integer;
  IntPart: string;
  FracPart: string;
  PointPos: Integer;
  I: Integer;
  AllZero: Boolean;
begin
  DLen := Length(Digits);

  if AScale <= 0 then
  begin
    { Whole number; a negative scale appends |scale| trailing zeros. }
    Result := Digits;
    I := 0;
    while I < -AScale do
    begin
      Result := Result + '0';
      I := I + 1
    end;
  end
  else
  begin
    { Positive scale: place the point so that AScale digits follow it,
      left-padding the integer part with zeros when the value is < 1. }
    if DLen > AScale then
    begin
      PointPos := DLen - AScale;
      IntPart := Copy(Digits, 0, PointPos);
      FracPart := Copy(Digits, PointPos, AScale);
      Result := IntPart + '.' + FracPart
    end
    else
    begin
      { 0.00..digits — need (AScale - DLen) leading fraction zeros. }
      FracPart := '';
      I := 0;
      while I < (AScale - DLen) do
      begin
        FracPart := FracPart + '0';
        I := I + 1
      end;
      Result := '0.' + FracPart + Digits
    end
  end;

  { Suppress a sign on zero. }
  AllZero := True;
  I := 0;
  while I < DLen do
  begin
    if OrdAt(Digits, I) <> Ord('0') then begin AllZero := False; I := DLen end
    else I := I + 1
  end;

  if Neg and not AllZero then
    Result := '-' + Result
end;

{ Renders the compact-path value (FCompact, FScale) as plain decimal text. }
function FormatCompact(AUnscaled: Int64; AScale: Integer): string;
var
  Neg: Boolean;
  Mag: Int64;
begin
  Neg := AUnscaled < 0;
  if Neg then Mag := -AUnscaled else Mag := AUnscaled;
  Result := FormatValue(DigitsOf(Mag), Neg, AScale)
end;

{ ------------------------------------------------------------------ }
{ TDecimal methods                                                    }
{ ------------------------------------------------------------------ }

function TDecimal.Scale: Integer;
begin
  Result := FScale
end;

function TDecimal.IsZero: Boolean;
begin
  if FInflated then
    Result := Length(FMag) = 0
  else
    Result := FCompact = 0
end;

function TDecimal.Sign: Integer;
begin
  if FInflated then
  begin
    if Length(FMag) = 0 then
      Result := 0
    else if FNegative then
      Result := -1
    else
      Result := 1
  end
  else
  begin
    if FCompact > 0 then
      Result := 1
    else if FCompact < 0 then
      Result := -1
    else
      Result := 0
  end
end;

{ Builds a compact TDecimal from a signed unscaled value and scale. }
function MakeCompact(AUnscaled: Int64; AScale: Integer): TDecimal;
begin
  Result.FCompact := AUnscaled;
  Result.FScale := AScale;
  Result.FNegative := AUnscaled < 0;
  Result.FInflated := False
end;

{ Signed Int64 addition with overflow detection.  Returns False (and leaves AOut
  undefined) if A + B overflows Int64. }
function TryAddInt64(A, B: Int64; out AOut: Int64): Boolean;
begin
  { Overflow iff both operands share a sign and the sum's sign differs. }
  AOut := A + B;
  if ((A >= 0) and (B >= 0) and (AOut < 0)) or
     ((A < 0) and (B < 0) and (AOut >= 0)) then
    Result := False
  else
    Result := True
end;

{ ================================================================== }
{ Arbitrary-precision magnitude (the inflated path)                    }
{ ------------------------------------------------------------------- }
{ A magnitude is an `array of UInt32` of DECIMAL digits (each 0..9),   }
{ stored little-endian (least-significant digit at index 0), with no   }
{ trailing zero digits.  An empty array is the value zero.  This is a  }
{ base-10 bignum: simple and exact.  (A base-2^32 limb packing is a    }
{ future optimisation that needs no change to the public API.)         }
{ ================================================================== }

{ Strips trailing zero digits (most-significant end) so the magnitude is
  canonical; an all-zero magnitude becomes the empty array. }
procedure NormaliseMag(var M: TDigitMag; var Len: Integer);
begin
  while (Len > 0) and (M[Len - 1] = 0) do
    Len := Len - 1
end;

{ Builds a digit magnitude from a string of ASCII digits (most-significant
  first, as written).  Leading zeros are ignored.  Empty / all-zero -> zero. }
function MagFromDigits(const S: string): TDigitMag;
var
  L, I, N: Integer;
begin
  L := Length(S);
  SetLength(Result, L);
  N := 0;
  { Store reversed (little-endian). }
  I := L - 1;
  while I >= 0 do
  begin
    Result[N] := OrdAt(S, I) - Ord('0');
    N := N + 1;
    I := I - 1
  end;
  NormaliseMag(Result, N);
  SetLength(Result, N)
end;

{ Renders a digit magnitude as a string of ASCII digits (most-significant
  first), with no leading zeros.  The empty magnitude renders as '0'. }
function MagToDigits(const M: TDigitMag): string;
var
  I: Integer;
begin
  if Length(M) = 0 then
  begin
    Result := '0';
    Exit
  end;
  Result := '';
  I := Length(M) - 1;
  while I >= 0 do
  begin
    Result := Result + Chr(Ord('0') + M[I]);
    I := I - 1
  end
end;

{ Compares two digit magnitudes: -1 if A<B, 0 if equal, +1 if A>B. }
function MagCompare(const A, B: TDigitMag): Integer;
var
  I: Integer;
begin
  if Length(A) <> Length(B) then
  begin
    if Length(A) < Length(B) then Result := -1 else Result := 1;
    Exit
  end;
  I := Length(A) - 1;
  while I >= 0 do
  begin
    if A[I] <> B[I] then
    begin
      if A[I] < B[I] then Result := -1 else Result := 1;
      Exit
    end;
    I := I - 1
  end;
  Result := 0
end;

{ Schoolbook addition of two digit magnitudes. }
function MagAdd(const A, B: TDigitMag): TDigitMag;
var
  MaxLen, I, Carry, Da, Db, Sum: Integer;
begin
  if Length(A) >= Length(B) then MaxLen := Length(A) else MaxLen := Length(B);
  SetLength(Result, MaxLen + 1);
  Carry := 0;
  I := 0;
  while I < MaxLen do
  begin
    if I < Length(A) then Da := A[I] else Da := 0;
    if I < Length(B) then Db := B[I] else Db := 0;
    Sum := Da + Db + Carry;
    Result[I] := Sum mod 10;
    Carry := Sum div 10;
    I := I + 1
  end;
  Result[MaxLen] := Carry;
  I := MaxLen + 1;
  NormaliseMag(Result, I);
  SetLength(Result, I)
end;

{ Schoolbook subtraction A - B, where A >= B is REQUIRED (caller guarantees). }
function MagSub(const A, B: TDigitMag): TDigitMag;
var
  I, Borrow, Da, Db, Diff, Len: Integer;
begin
  SetLength(Result, Length(A));
  Borrow := 0;
  I := 0;
  while I < Length(A) do
  begin
    Da := A[I];
    if I < Length(B) then Db := B[I] else Db := 0;
    Diff := Da - Db - Borrow;
    if Diff < 0 then
    begin
      Diff := Diff + 10;
      Borrow := 1
    end
    else
      Borrow := 0;
    Result[I] := Diff;
    I := I + 1
  end;
  Len := Length(A);
  NormaliseMag(Result, Len);
  SetLength(Result, Len)
end;

{ Schoolbook long multiplication of two digit magnitudes.  Accumulates directly
  into the result digit-array (a single dynamic array — deliberately no second
  local `array of Integer`, which the native backend currently mis-compiles). }
function MagMul(const A, B: TDigitMag): TDigitMag;
var
  I, J, Carry, Prod, Len: Integer;
begin
  if (Length(A) = 0) or (Length(B) = 0) then
  begin
    SetLength(Result, 0);
    Exit
  end;
  SetLength(Result, Length(A) + Length(B));
  I := 0;
  while I < Length(Result) do begin Result[I] := 0; I := I + 1 end;
  I := 0;
  while I < Length(A) do
  begin
    Carry := 0;
    J := 0;
    while J < Length(B) do
    begin
      Prod := Result[I + J] + A[I] * B[J] + Carry;
      Result[I + J] := Prod mod 10;
      Carry := Prod div 10;
      J := J + 1
    end;
    Result[I + Length(B)] := Result[I + Length(B)] + Carry;
    I := I + 1
  end;
  Len := Length(Result);
  NormaliseMag(Result, Len);
  SetLength(Result, Len)
end;

{ Returns an independent copy of a magnitude.  Needed because Blaise dynamic
  arrays are reference types: `X := Y` aliases the same buffer, so any helper
  that would otherwise return one of its inputs directly must copy instead. }
function MagCopy(const A: TDigitMag): TDigitMag;
var I: Integer;
begin
  SetLength(Result, Length(A));
  I := 0;
  while I < Length(A) do begin Result[I] := A[I]; I := I + 1 end
end;

{ Multiplies a digit magnitude by a single digit D (0..9). }
function MagMulSmall(const A: TDigitMag; D: Integer): TDigitMag;
var
  I, Carry, Prod, Len: Integer;
begin
  if (D = 0) or (Length(A) = 0) then
  begin
    SetLength(Result, 0);
    Exit
  end;
  SetLength(Result, Length(A) + 1);
  Carry := 0;
  I := 0;
  while I < Length(A) do
  begin
    Prod := A[I] * D + Carry;
    Result[I] := Prod mod 10;
    Carry := Prod div 10;
    I := I + 1
  end;
  Result[Length(A)] := Carry;
  Len := Length(A) + 1;
  NormaliseMag(Result, Len);
  SetLength(Result, Len)
end;

{ Adds 1 to a digit magnitude. }
function MagIncrement(const A: TDigitMag): TDigitMag;
var
  I, Carry, Sum: Integer;
begin
  SetLength(Result, Length(A) + 1);
  Carry := 1;
  I := 0;
  while I < Length(A) do
  begin
    Sum := A[I] + Carry;
    Result[I] := Sum mod 10;
    Carry := Sum div 10;
    I := I + 1
  end;
  Result[Length(A)] := Carry;
  I := Length(A) + 1;
  NormaliseMag(Result, I);
  SetLength(Result, I)
end;

{ Schoolbook long division of magnitude A by magnitude B (B must be non-zero).
  Returns the quotient; the remainder is returned via ARem.  Processes the
  dividend most-significant digit first, maintaining a running remainder. }
function MagDivMod(const A, B: TDigitMag; out ARem: TDigitMag): TDigitMag;
var
  ALen, I, Q, Cmp: Integer;
  Cur: TDigitMag;     { running remainder (a magnitude) }
  Trial: TDigitMag;
  QDigits: TDigitMag; { quotient digits, most-significant first during build }
  QLen: Integer;
  Shifted: TDigitMag;
  J: Integer;
begin
  ALen := Length(A);
  if ALen = 0 then
  begin
    SetLength(Result, 0);
    SetLength(ARem, 0);
    Exit
  end;

  SetLength(QDigits, ALen);
  QLen := 0;
  SetLength(Cur, 0);    { running remainder starts empty (zero) }

  { Bring down digits from most-significant to least-significant. }
  I := ALen - 1;
  while I >= 0 do
  begin
    { Cur := Cur * 10 + A[I]  (shift remainder up one place, append next digit).
      Build into a FRESH array — dynamic arrays are reference types in Blaise, so
      Cur and Shifted must not alias the same buffer. }
    SetLength(Shifted, Length(Cur) + 1);
    Shifted[0] := A[I];
    J := 0;
    while J < Length(Cur) do begin Shifted[J + 1] := Cur[J]; J := J + 1 end;
    { Normalise (drop high zero limbs) before adopting as the new Cur. }
    J := Length(Shifted);
    NormaliseMag(Shifted, J);
    SetLength(Shifted, J);
    { Independent copy into Cur so the next iteration's SetLength(Shifted,...)
      cannot disturb Cur. }
    SetLength(Cur, Length(Shifted));
    J := 0;
    while J < Length(Shifted) do begin Cur[J] := Shifted[J]; J := J + 1 end;

    { Find the largest Q in 0..9 with B*Q <= Cur (Blaise has no break: gate the
      loop on a flag instead). }
    Q := 0;
    Cmp := 0;
    while (Q < 9) and (Cmp = 0) do
    begin
      Trial := MagMulSmall(B, Q + 1);
      if MagCompare(Trial, Cur) <= 0 then
        Q := Q + 1
      else
        Cmp := 1   { stop: B*(Q+1) exceeds Cur }
    end;

    { Cur := Cur - B*Q }
    if Q > 0 then
    begin
      Trial := MagMulSmall(B, Q);
      Cur := MagSub(Cur, Trial)
    end;

    QDigits[QLen] := Q;   { store most-significant first }
    QLen := QLen + 1;
    I := I - 1
  end;

  { QDigits currently holds digits most-significant first; reverse into the
    little-endian Result. }
  SetLength(Result, QLen);
  J := 0;
  while J < QLen do
  begin
    Result[J] := QDigits[QLen - 1 - J];
    J := J + 1
  end;
  I := QLen;
  NormaliseMag(Result, I);
  SetLength(Result, I);

  ARem := MagCopy(Cur)
end;

{ Returns the unscaled MAGNITUDE (no sign) of a TDecimal as a digit string,
  whether it is stored compact or inflated. }
function UnscaledDigits(const D: TDecimal): string;
var
  Mag: Int64;
begin
  if D.FInflated then
    Result := MagToDigits(D.FMag)
  else
  begin
    if D.FCompact < 0 then Mag := -D.FCompact else Mag := D.FCompact;
    Result := Int64ToStr(Mag)
  end
end;

{ True if D is negative (works for both representations). }
function IsNeg(const D: TDecimal): Boolean;
begin
  if D.FInflated then
    Result := D.FNegative and (Length(D.FMag) > 0)
  else
    Result := D.FCompact < 0
end;

{ Builds a TDecimal from a magnitude digit string, a sign and a scale, choosing
  the compact representation when the unscaled value fits in Int64 and inflating
  otherwise.  Leading zeros in ADigits are tolerated. }
function MakeFromMagDigits(const ADigits: string; ANeg: Boolean;
                           AScale: Integer): TDecimal;
var
  Mag: TDigitMag;
  AsI64: Int64;
  I, Ch, DLen: Integer;
  Overflow: Boolean;
begin
  Mag := MagFromDigits(ADigits);
  if Length(Mag) = 0 then
  begin
    { Zero — always compact, sign normalised away. }
    Result := MakeCompact(0, AScale);
    Exit
  end;

  { Try to pack into Int64. }
  DLen := Length(Mag);
  Overflow := DLen > 19;   { 19 digits may or may not fit; check carefully }
  AsI64 := 0;
  if not Overflow then
  begin
    I := DLen - 1;          { most-significant first }
    while I >= 0 do
    begin
      Ch := Mag[I];
      if (AsI64 > cMaxInt64Div10) or
         ((AsI64 = cMaxInt64Div10) and (Ch > cMaxInt64Mod10)) then
      begin
        Overflow := True;
        I := -1               { stop }
      end
      else
      begin
        AsI64 := AsI64 * 10 + Ch;
        I := I - 1
      end
    end
  end;

  if Overflow then
  begin
    Result.FCompact := 0;
    Result.FMag := Mag;
    Result.FScale := AScale;
    Result.FNegative := ANeg;
    Result.FInflated := True
  end
  else
  begin
    if ANeg then AsI64 := -AsI64;
    Result := MakeCompact(AsI64, AScale)
  end
end;

{ Multiplies AValue by 10^APow without overflowing: returns False if the result
  would exceed Int64 range, True (with the product in AOut) otherwise. }
function TryScaleUp(AValue: Int64; APow: Integer; out AOut: Int64): Boolean;
var
  I: Integer;
  Neg: Boolean;
  Mag: Int64;
begin
  Neg := AValue < 0;
  if Neg then
    Mag := -AValue
  else
    Mag := AValue;
  I := 0;
  while I < APow do
  begin
    if Mag > cMaxInt64Div10 then
    begin
      Result := False;
      AOut := 0;
      Exit
    end;
    Mag := Mag * 10;
    I := I + 1
  end;
  if Neg then
    AOut := -Mag
  else
    AOut := Mag;
  Result := True
end;

{ Strips a leading sign and trailing fraction zeros from a plain decimal string,
  returning a canonical "<sign><digits>[.<digits>]" with no trailing fraction
  zeros and no trailing bare point.  Used to derive a scale-independent hash key
  and a normalised magnitude for the string-fallback comparison. }
function NormalisePlain(const S: string): string;
var
  L: Integer;
  DotPos: Integer;
  EndPos: Integer;
begin
  Result := S;
  L := Length(Result);
  if L = 0 then Exit;

  { Find a decimal point, if any. }
  DotPos := Pos('.', Result);
  if DotPos < 0 then Exit;   { 0-based Pos: <0 means not found }

  { Trim trailing zeros after the point. }
  EndPos := L - 1;
  while (EndPos > DotPos) and (OrdAt(Result, EndPos) = Ord('0')) do
    EndPos := EndPos - 1;
  { If everything after the point was zero, drop the point too. }
  if EndPos = DotPos then
    EndPos := DotPos - 1;
  Result := Copy(Result, 0, EndPos + 1)
end;

{ Returns the integer-part length (count of digits before any '.') of S starting
  at the 0-based cursor Start. }
function IntPartLen(const S: string; Start: Integer): Integer;
var P: Integer;
begin
  P := Start;
  while (P < Length(S)) and (OrdAt(S, P) <> Ord('.')) do
    P := P + 1;
  Result := P - Start
end;

{ 0-based offset of the first fraction digit of S (after the '.'), or Length(S)
  if there is no fraction, scanning from cursor Start. }
function FracStart(const S: string; Start: Integer): Integer;
var P: Integer;
begin
  P := Start;
  while (P < Length(S)) and (OrdAt(S, P) <> Ord('.')) do
    P := P + 1;
  if P < Length(S) then
    Result := P + 1   { skip the '.' }
  else
    Result := Length(S)
end;

{ Compares the magnitudes (sign ignored) of two plain decimal strings, each from
  its own cursor (Xi / Yi point past any sign). }
function CompareMagnitude(const X: string; Xi: Integer;
                          const Y: string; Yi: Integer): Integer;
var
  XiLen, YiLen: Integer;
  XfStart, YfStart: Integer;
  XfLen, YfLen: Integer;
  K, MaxF: Integer;
  Xd, Yd: Integer;
begin
  XiLen := IntPartLen(X, Xi);
  YiLen := IntPartLen(Y, Yi);
  { Plain decimal integer parts have no leading zeros (except a lone '0'), so a
    longer integer part means a larger magnitude. }
  if XiLen <> YiLen then
  begin
    if XiLen < YiLen then Result := -1 else Result := 1;
    Exit
  end;
  K := 0;
  while K < XiLen do
  begin
    Xd := OrdAt(X, Xi + K);
    Yd := OrdAt(Y, Yi + K);
    if Xd <> Yd then
    begin
      if Xd < Yd then Result := -1 else Result := 1;
      Exit
    end;
    K := K + 1
  end;
  { Integer parts equal — compare fraction digits, padding the shorter with 0. }
  XfStart := FracStart(X, Xi);
  YfStart := FracStart(Y, Yi);
  XfLen := Length(X) - XfStart;
  YfLen := Length(Y) - YfStart;
  if XfLen >= YfLen then MaxF := XfLen else MaxF := YfLen;
  K := 0;
  while K < MaxF do
  begin
    if K < XfLen then Xd := OrdAt(X, XfStart + K) else Xd := Ord('0');
    if K < YfLen then Yd := OrdAt(Y, YfStart + K) else Yd := Ord('0');
    if Xd <> Yd then
    begin
      if Xd < Yd then Result := -1 else Result := 1;
      Exit
    end;
    K := K + 1
  end;
  Result := 0
end;

{ Compares two plain decimal strings (which carry the SAME sign) by numeric
  value.  Used only on the overflow fallback path, so it need not be fast. }
function CompareDecimalText(const A, B: string): Integer;
var
  NegA: Boolean;
  Ai, Bi: Integer;
  MagResult: Integer;
begin
  NegA := (Length(A) > 0) and (OrdAt(A, 0) = Ord('-'));
  if NegA then Ai := 1 else Ai := 0;
  if (Length(B) > 0) and (OrdAt(B, 0) = Ord('-')) then Bi := 1 else Bi := 0;

  MagResult := CompareMagnitude(A, Ai, B, Bi);
  { Both share the sign; for negatives the magnitude order inverts. }
  if NegA then
    Result := -MagResult
  else
    Result := MagResult
end;

{ Returns D's unscaled magnitude as a digit-array, scaled UP to ATargetScale
  (which must be >= D.Scale): i.e. the magnitude with (ATargetScale - D.Scale)
  zero digits appended at the least-significant end. }
function ScaledMag(const D: TDecimal; ATargetScale: Integer): TDigitMag;
var
  Base: TDigitMag;
  Pad, I, BLen: Integer;
begin
  Base := MagFromDigits(UnscaledDigits(D));
  Pad := ATargetScale - D.FScale;
  if Length(Base) = 0 then
  begin
    SetLength(Result, 0);   { zero stays zero }
    Exit
  end;
  BLen := Length(Base);
  SetLength(Result, BLen + Pad);
  { Shift left by Pad (append Pad zero digits at the low end). }
  I := 0;
  while I < Pad do begin Result[I] := 0; I := I + 1 end;
  I := 0;
  while I < BLen do begin Result[Pad + I] := Base[I]; I := I + 1 end
end;

{ Shared add/subtract core: aligns both operands to the larger scale, then does
  signed magnitude add/subtract.  BNeg flips B's sign (for Subtract).  Works for
  both compact and inflated operands; the result is re-packed to compact when it
  fits, otherwise stays inflated. }
function AddCore(const A, B: TDecimal; BNeg: Boolean): TDecimal;
var
  MaxScale: Integer;
  MA, MB, MR: TDigitMag;
  SignA, SignB: Integer;
  ResNeg: Boolean;
  Cmp: Integer;
begin
  if A.FScale >= B.FScale then MaxScale := A.FScale else MaxScale := B.FScale;

  MA := ScaledMag(A, MaxScale);
  MB := ScaledMag(B, MaxScale);

  SignA := A.Sign();
  SignB := B.Sign();
  if BNeg then SignB := -SignB;

  { Combine signed magnitudes. }
  if (SignA >= 0) and (SignB >= 0) then
  begin
    MR := MagAdd(MA, MB);
    ResNeg := False
  end
  else if (SignA < 0) and (SignB < 0) then
  begin
    MR := MagAdd(MA, MB);
    ResNeg := True
  end
  else
  begin
    { Opposite signs: subtract smaller magnitude from larger. }
    Cmp := MagCompare(MA, MB);
    if Cmp = 0 then
    begin
      SetLength(MR, 0);
      ResNeg := False
    end
    else if Cmp > 0 then
    begin
      MR := MagSub(MA, MB);
      ResNeg := SignA < 0    { |A| larger: result takes A's sign }
    end
    else
    begin
      MR := MagSub(MB, MA);
      ResNeg := SignB < 0    { |B| larger: result takes B's sign }
    end
  end;

  Result := MakeFromMagDigits(MagToDigits(MR), ResNeg, MaxScale)
end;

function TDecimal.Add(const B: TDecimal): TDecimal;
begin
  Result := AddCore(Self, B, False)
end;

function TDecimal.Subtract(const B: TDecimal): TDecimal;
begin
  Result := AddCore(Self, B, True)
end;

function TDecimal.Negate: TDecimal;
begin
  if FInflated then
    Result := MakeFromMagDigits(MagToDigits(FMag), not FNegative, FScale)
  else
    Result := MakeCompact(-FCompact, FScale)
end;

function TDecimal.Abs: TDecimal;
begin
  if FInflated then
    Result := MakeFromMagDigits(MagToDigits(FMag), False, FScale)
  else if FCompact < 0 then
    Result := MakeCompact(-FCompact, FScale)
  else
    Result := MakeCompact(FCompact, FScale)
end;

function TDecimal.Multiply(const B: TDecimal): TDecimal;
var
  MR: TDigitMag;
  ResNeg: Boolean;
begin
  { Exact product: magnitudes multiply, scales add, signs xor. }
  MR := MagMul(MagFromDigits(UnscaledDigits(Self)),
               MagFromDigits(UnscaledDigits(B)));
  ResNeg := IsNeg(Self) <> IsNeg(B);
  Result := MakeFromMagDigits(MagToDigits(MR), ResNeg, Self.FScale + B.FScale)
end;

{ Appends N zero digits at the least-significant end of a magnitude (multiply by
  10^N).  N must be >= 0.  An empty (zero) magnitude stays empty. }
function MagShift(const A: TDigitMag; N: Integer): TDigitMag;
var
  I: Integer;
begin
  if (Length(A) = 0) or (N <= 0) then
  begin
    if N <= 0 then Result := MagCopy(A) else SetLength(Result, 0);
    Exit
  end;
  SetLength(Result, Length(A) + N);
  I := 0;
  while I < N do begin Result[I] := 0; I := I + 1 end;
  I := 0;
  while I < Length(A) do begin Result[N + I] := A[I]; I := I + 1 end
end;

{ Drops the N least-significant digits of a magnitude (integer divide by 10^N).
  Caller guarantees 0 <= N <= Length(A). }
function MagShiftRightDrop(const A: TDigitMag; N: Integer): TDigitMag;
var
  I, Len: Integer;
begin
  if N >= Length(A) then
  begin
    SetLength(Result, 0);
    Exit
  end;
  SetLength(Result, Length(A) - N);
  I := 0;
  while I < Length(Result) do begin Result[I] := A[N + I]; I := I + 1 end;
  Len := Length(Result);
  NormaliseMag(Result, Len);
  SetLength(Result, Len)
end;

function TDecimal.Divide(const B: TDecimal; TargetScale: Integer;
                         const Strategy: IRoundingStrategy): TDecimal;
var
  NumMag, DenMag, Dividend, Divisor, Q, R, TwoR: TDigitMag;
  Shift: Integer;
  ResNeg: Boolean;
  LastDigit, HalfCmp: Integer;
  AnyDisc: Boolean;
begin
  if B.IsZero() then
    raise EDivByZero.Create('TDecimal.Divide: division by zero');
  if Self.IsZero() then
  begin
    Result := MakeCompact(0, TargetScale);
    Exit
  end;

  NumMag := MagFromDigits(UnscaledDigits(Self));
  DenMag := MagFromDigits(UnscaledDigits(B));

  { dividend / divisor = selfMag * 10^(TargetScale + Bscale - Selfscale) / Bmag. }
  Shift := TargetScale + B.FScale - Self.FScale;
  if Shift >= 0 then
  begin
    Dividend := MagShift(NumMag, Shift);
    Divisor := DenMag
  end
  else
  begin
    Dividend := NumMag;
    Divisor := MagShift(DenMag, -Shift)
  end;

  Q := MagDivMod(Dividend, Divisor, R);

  { Rounding context. }
  ResNeg := IsNeg(Self) <> IsNeg(B);
  AnyDisc := Length(R) > 0;
  if Length(Q) > 0 then LastDigit := Q[0] else LastDigit := 0;

  { Compare the discarded fraction R/Divisor against 1/2 via 2*R vs Divisor. }
  if AnyDisc then
  begin
    TwoR := MagMulSmall(R, 2);
    HalfCmp := MagCompare(TwoR, Divisor)    { -1 below, 0 exactly, +1 above half }
  end
  else
    HalfCmp := -1;

  if Strategy.RoundIncrement(ResNeg, LastDigit, HalfCmp, AnyDisc) then
    Q := MagIncrement(Q);

  Result := MakeFromMagDigits(MagToDigits(Q), ResNeg, TargetScale)
end;

function TDecimal.Divide(const B: TDecimal; TargetScale: Integer;
                         Mode: TRoundingMode): TDecimal;
begin
  Result := Self.Divide(B, TargetScale, StandardRounding(Mode))
end;

function TDecimal.RoundTo(NewScale: Integer;
                          const Strategy: IRoundingStrategy): TDecimal;
var
  Mag, Keep, Drop, TwoDrop, DropBase: TDigitMag;
  DropCount, I, LastDigit, HalfCmp: Integer;
  AnyDisc: Boolean;
begin
  if NewScale >= Self.FScale then
  begin
    { Increasing (or equal) scale is exact: pad with zeros. }
    Mag := MagShift(MagFromDigits(UnscaledDigits(Self)), NewScale - Self.FScale);
    Result := MakeFromMagDigits(MagToDigits(Mag), IsNeg(Self), NewScale);
    Exit
  end;

  { Decreasing scale: drop (Self.FScale - NewScale) least-significant digits,
    rounding.  Mag is little-endian, so the dropped digits are the low end. }
  Mag := MagFromDigits(UnscaledDigits(Self));
  DropCount := Self.FScale - NewScale;

  { Split Mag into kept (high) and dropped (low) digit runs. }
  if DropCount >= Length(Mag) then
  begin
    { Everything is dropped — kept part is zero, dropped is the whole magnitude
      conceptually padded out to DropCount places. }
    SetLength(Keep, 0);
    DropBase := Mag   { DropCount is unchanged: the half comparison below uses 10^DropCount }
  end
  else
  begin
    SetLength(Keep, Length(Mag) - DropCount);
    I := 0;
    while I < Length(Keep) do begin Keep[I] := Mag[DropCount + I]; I := I + 1 end;
    SetLength(DropBase, DropCount);
    I := 0;
    while I < DropCount do begin DropBase[I] := Mag[I]; I := I + 1 end
  end;
  I := Length(Keep); NormaliseMag(Keep, I); SetLength(Keep, I);
  I := Length(DropBase); NormaliseMag(DropBase, I); SetLength(DropBase, I);

  AnyDisc := Length(DropBase) > 0;
  if Length(Keep) > 0 then LastDigit := Keep[0] else LastDigit := 0;

  { Half here is 5 * 10^(DropCount-1), i.e. compare 2*dropped vs 10^DropCount. }
  if AnyDisc then
  begin
    Drop := DropBase;
    TwoDrop := MagMulSmall(Drop, 2);
    HalfCmp := MagCompare(TwoDrop, MagShift(MagFromDigits('1'), DropCount))
  end
  else
    HalfCmp := -1;

  if Strategy.RoundIncrement(IsNeg(Self), LastDigit, HalfCmp, AnyDisc) then
    Keep := MagIncrement(Keep);

  Result := MakeFromMagDigits(MagToDigits(Keep), IsNeg(Self), NewScale)
end;

function TDecimal.RoundTo(NewScale: Integer; Mode: TRoundingMode): TDecimal;
begin
  Result := Self.RoundTo(NewScale, StandardRounding(Mode))
end;

function TDecimal.SetScale(NewScale: Integer; Mode: TRoundingMode): TDecimal;
begin
  Result := Self.RoundTo(NewScale, Mode)
end;

function TDecimal.Compare(const B: TDecimal): Integer;
var
  SignA, SignB: Integer;
  MaxScale: Integer;
  UA, UB: Int64;
  OkA, OkB: Boolean;
  PlainA, PlainB: string;
begin
  { Fast sign discrimination first. }
  SignA := Self.Sign();
  SignB := B.Sign();
  if SignA <> SignB then
  begin
    if SignA < SignB then Result := -1 else Result := 1;
    Exit
  end;
  if SignA = 0 then
  begin
    Result := 0;
    Exit
  end;

  { Same sign, both non-zero.  Inflated operands go straight to the string
    compare (their FCompact is not meaningful). }
  if Self.FInflated or B.FInflated then
  begin
    PlainA := NormalisePlain(Self.ToString());
    PlainB := NormalisePlain(B.ToString());
    Result := CompareDecimalText(PlainA, PlainB);
    Exit
  end;

  { Both compact: align to the larger scale and compare unscaled values; fall
    back to a normalised-string compare if scaling overflows. }
  if Self.FScale >= B.FScale then
    MaxScale := Self.FScale
  else
    MaxScale := B.FScale;

  OkA := TryScaleUp(Self.FCompact, MaxScale - Self.FScale, UA);
  OkB := TryScaleUp(B.FCompact, MaxScale - B.FScale, UB);

  if OkA and OkB then
  begin
    if UA < UB then
      Result := -1
    else if UA > UB then
      Result := 1
    else
      Result := 0;
    Exit
  end;

  { Overflow during alignment — compare the canonical decimal texts.  Both have
    the same sign here. }
  PlainA := NormalisePlain(Self.ToString());
  PlainB := NormalisePlain(B.ToString());
  Result := CompareDecimalText(PlainA, PlainB)
end;

function TDecimal.Equals(const B: TDecimal): Boolean;
begin
  Result := Self.Compare(B) = 0
end;

function TDecimal.GetHashCode: Integer;
var
  Norm: string;
  I: Integer;
  H: Integer;
begin
  { Hash the scale-normalised text so value-equal decimals (2.0 / 2.00) hash
    identically.  Simple polynomial rolling hash over the canonical bytes. }
  Norm := NormalisePlain(Self.ToString());
  H := 0;
  I := 0;
  while I < Length(Norm) do
  begin
    H := H * 31 + OrdAt(Norm, I);
    I := I + 1
  end;
  Result := H
end;

function TDecimal.ToString: string;
begin
  if FInflated then
    Result := FormatValue(MagToDigits(FMag), FNegative, FScale)
  else
    Result := FormatCompact(FCompact, FScale)
end;

function TDecimal.ToPlainString: string;
begin
  Result := Self.ToString()
end;

function TDecimal.StripTrailingZeros: TDecimal;
var
  Mag: TDigitMag;
  NewScale, Drop: Integer;
begin
  if Self.IsZero() then
  begin
    Result := MakeCompact(0, 0);   { canonical zero, scale 0 }
    Exit
  end;
  Mag := MagFromDigits(UnscaledDigits(Self));
  NewScale := Self.FScale;
  { Remove low-end zero digits while the scale is still positive (we only strip
    FRACTION zeros, never integer-part zeros — 600 keeps scale 0, stays 600). }
  Drop := 0;
  while (NewScale - Drop > 0) and (Drop < Length(Mag)) and (Mag[Drop] = 0) do
    Drop := Drop + 1;
  if Drop > 0 then
  begin
    Mag := MagShiftRightDrop(Mag, Drop);
    NewScale := NewScale - Drop
  end;
  Result := MakeFromMagDigits(MagToDigits(Mag), IsNeg(Self), NewScale)
end;

function TDecimal.ToDouble: Float64;
begin
  Result := StrToDouble(Self.ToString())
end;

function TDecimal.ToInt64: Int64;
var
  Truncated: TDecimal;
  S: string;
begin
  { Truncate toward zero, then parse the integer text. }
  Truncated := Self.RoundTo(0, rmDown);
  S := Truncated.ToString();
  Result := StrToInt64(S)
end;

{ ------------------------------------------------------------------ }
{ Construction                                                         }
{ ------------------------------------------------------------------ }

function DecFromInt(V: Integer): TDecimal;
begin
  Result.FCompact := V;
  Result.FScale := 0;
  Result.FNegative := V < 0;
  Result.FInflated := False
end;

function DecFromInt64(V: Int64): TDecimal;
begin
  Result.FCompact := V;
  Result.FScale := 0;
  Result.FNegative := V < 0;
  Result.FInflated := False
end;

function DecFromFloat(V: Float64): TDecimal;
begin
  { Shortest decimal: DoubleToStr is the Grisu shortest-round-trip formatter, so
    0.1 comes back as '0.1', not the binary tail. }
  Result := DecFromStr(DoubleToStr(V))
end;

function DecFromFloatExact(V: Float64): TDecimal;
var
  S: string;
begin
  { High-precision %f exposes the representation error.  (This captures the
    Double's value to ~full double precision; the true infinite binary->decimal
    expansion is deliberately not pursued — this path exists to demonstrate and
    permit the dangerous conversion, not to be the default.) }
  S := Format('%.30f', [V]);
  Result := DecFromStr(S)
end;

function DecFromStr(const S: string): TDecimal;
var
  Pos:      Integer;
  Len:      Integer;
  Neg:      Boolean;
  Ch:       Integer;
  MagStr:   string;     { accumulated unscaled magnitude digits (any length) }
  Scale:    Integer;
  SeenDot:  Boolean;
  AnyDigit: Boolean;
begin
  Len := Length(S);
  if Len = 0 then
    raise EDecimalParse.Create('DecFromStr: empty string');

  Pos := 0;
  Neg := False;
  Ch := OrdAt(S, Pos);
  if Ch = Ord('+') then
    Pos := Pos + 1
  else if Ch = Ord('-') then
  begin
    Neg := True;
    Pos := Pos + 1
  end;

  MagStr := '';
  Scale := 0;
  SeenDot := False;
  AnyDigit := False;

  while Pos < Len do
  begin
    Ch := OrdAt(S, Pos);
    if Ch = Ord('.') then
    begin
      if SeenDot then
        raise EDecimalParse.Create('DecFromStr: multiple decimal points');
      SeenDot := True;
      Pos := Pos + 1
    end
    else if (Ch >= Ord('0')) and (Ch <= Ord('9')) then
    begin
      MagStr := MagStr + Chr(Ch);
      AnyDigit := True;
      if SeenDot then
        Scale := Scale + 1;
      Pos := Pos + 1
    end
    else
      raise EDecimalParse.Create('DecFromStr: invalid character');
  end;

  if not AnyDigit then
    raise EDecimalParse.Create('DecFromStr: no digits');

  { MakeFromMagDigits picks compact vs inflated and tolerates leading zeros. }
  Result := MakeFromMagDigits(MagStr, Neg, Scale)
end;

{ ------------------------------------------------------------------ }
{ Operators                                                            }
{ ------------------------------------------------------------------ }

class operator TDecimal.Add(const A, B: TDecimal): TDecimal;
begin
  Result := A.Add(B);
end;

class operator TDecimal.Subtract(const A, B: TDecimal): TDecimal;
begin
  Result := A.Subtract(B);
end;

class operator TDecimal.Multiply(const A, B: TDecimal): TDecimal;
begin
  Result := A.Multiply(B);
end;

class operator TDecimal.Multiply(const A: TDecimal; B: Integer): TDecimal;
begin
  Result := A.Multiply(DecFromInt(B));
end;

class operator TDecimal.Multiply(A: Integer; const B: TDecimal): TDecimal;
begin
  Result := DecFromInt(A).Multiply(B);
end;

class operator TDecimal.Negative(const A: TDecimal): TDecimal;
begin
  Result := A.Negate();
end;

class operator TDecimal.Equal(const A, B: TDecimal): Boolean;
begin
  Result := A.Equals(B);
end;

class operator TDecimal.NotEqual(const A, B: TDecimal): Boolean;
begin
  Result := not A.Equals(B);
end;

class operator TDecimal.LessThan(const A, B: TDecimal): Boolean;
begin
  Result := A.Compare(B) < 0;
end;

class operator TDecimal.GreaterThan(const A, B: TDecimal): Boolean;
begin
  Result := A.Compare(B) > 0;
end;

class operator TDecimal.LessThanOrEqual(const A, B: TDecimal): Boolean;
begin
  Result := A.Compare(B) <= 0;
end;

class operator TDecimal.GreaterThanOrEqual(const A, B: TDecimal): Boolean;
begin
  Result := A.Compare(B) >= 0;
end;

end.
