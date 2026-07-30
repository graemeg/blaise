{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL -- transcendental and rounding math (pure Pascal, no libm)

  This unit is the runtime behind the float-math builtins (Sin, Cos, Tan,
  ArcSin, ArcCos, ArcTan, ArcTan2, Ln, Log2, Log10, Power, Sinh, Cosh,
  Tanh, Sqrt, Floor, Ceil, Round) so that Blaise binaries have NO libm
  dependency: the whole of libm that Blaise uses lives here, in Pascal.

  The implementations are ports of musl libc's math sources (MIT licence),
  which are themselves derived from FDLIBM 5.3 (Sun Microsystems, freely
  redistributable).  Function by function:

    _BlaiseSin/_BlaiseCos/_BlaiseTan     musl sin.c/cos.c/tan.c +
                                         __sin.c/__cos.c/__tan.c kernels
    RemPio2/RemPio2Large                 musl __rem_pio2.c/__rem_pio2_large.c
                                         (Payne-Hanek reduction, double-only:
                                         prec is fixed at 1, jk at 4)
    _BlaiseArcSin/_BlaiseArcCos          musl asin.c/acos.c
    _BlaiseArcTan/_BlaiseArcTan2         musl atan.c/atan2.c
    _BlaiseExp/_BlaiseExpm1              musl v1.1.16 exp.c / expm1.c
    _BlaiseLn/_BlaiseLog2/_BlaiseLog10   musl v1.1.16 log.c/log2.c/log10.c
    _BlaisePow                           musl v1.1.16 pow.c
    _BlaiseSinh/_BlaiseCosh/_BlaiseTanh  musl sinh.c/cosh.c/tanh.c + __expo2.c
    _BlaiseSqrtD                         musl sqrt.c (fdlibm bit-by-bit,
                                         correctly rounded)
    _BlaiseFloorD/_BlaiseCeilD           musl floor.c/ceil.c
    _BlaiseRoundD                        musl round.c (half away from zero,
                                         the documented Blaise Round rule)
    _BlaiseFabs/_BlaiseScalbn            musl fabs.c/scalbn.c

  Porting rules used throughout (read this before touching a function):

  * Every port follows its C original statement by statement; the original
    file names are cited above so a suspect function can be diffed against
    its source.  Do not "improve" the floating-point expressions: the
    grouping and evaluation order ARE the algorithm (hi/lo compensation
    terms cancel exactly only in the written order).
  * C uint32 variables are held in Int64 and masked with `and $FFFFFFFF`
    after any operation that can carry past bit 31; C int32 variables are
    held in Int64 and kept in range by construction (asserted per function).
  * GET_HIGH_WORD / SET_LOW_WORD and friends map to the HiU/HiS/LoU/
    ComposeD/SetHiW/SetLoW helpers below.
  * FORCE_EVAL calls (which only raise IEEE exception flags) are dropped:
    Blaise does not expose the FP status word.
  * Tiny "+ 0x1p-120" inexact-signal terms are dropped for the same reason;
    they never change the rounded result.
  * Float literals are copied verbatim from musl (21 significant digits,
    with the intended bit pattern in a comment).  Literal text flows
    through codegen into the assembler's strtod, so the conversion is
    correctly rounded on both backends.

  Accuracy: within 1 ulp of correctly rounded for the fdlibm-derived
  functions (sqrt, floor, ceil, round and fabs are exact); the punit suite
  runtime/src/test/pascal/test_blaise_math.pas pins ~190 reference vectors
  computed with glibc to a 2 ulp tolerance.

  Single-precision note: there are deliberately no float kernels here.
  The backends compute Single trig/exp/log by widening to Double, calling
  these functions and narrowing the result -- for every function in this
  unit that is accurate to well under Single's 0.5 ulp (double rounding is
  harmless at 29 extra mantissa bits).
}

unit runtime.math;

interface

function _BlaiseSin(X: Double): Double;
function _BlaiseCos(X: Double): Double;
function _BlaiseTan(X: Double): Double;
function _BlaiseArcSin(X: Double): Double;
function _BlaiseArcCos(X: Double): Double;
function _BlaiseArcTan(X: Double): Double;
function _BlaiseArcTan2(Y, X: Double): Double;
function _BlaiseExp(X: Double): Double;
function _BlaiseExpm1(X: Double): Double;
function _BlaiseLn(X: Double): Double;
function _BlaiseLog2(X: Double): Double;
function _BlaiseLog10(X: Double): Double;
function _BlaisePow(X, Y: Double): Double;
function _BlaiseSinh(X: Double): Double;
function _BlaiseCosh(X: Double): Double;
function _BlaiseTanh(X: Double): Double;
function _BlaiseSqrtD(X: Double): Double;
function _BlaiseFloorD(X: Double): Double;
function _BlaiseCeilD(X: Double): Double;
function _BlaiseRoundD(X: Double): Double;
function _BlaiseFabs(X: Double): Double;
function _BlaiseScalbn(X: Double; N: Integer): Double;

implementation

{ ------------------------------------------------------------------ }
{ IEEE-754 binary64 word access (fdlibm GET/SET_*_WORD equivalents)    }
{ ------------------------------------------------------------------ }

function DoubleBits(V: Double): Int64;
var
  P: ^Int64;
begin
  P := Pointer(@V);
  Result := P^;
end;

function BitsToDouble(Bits: Int64): Double;
var
  P: ^Double;
begin
  P := Pointer(@Bits);
  Result := P^;
end;

{ High 32 bits as an unsigned value in 0..$FFFFFFFF. }
function HiU(V: Double): Int64;
begin
  Result := (DoubleBits(V) shr 32) and $FFFFFFFF;
end;

{ High 32 bits sign-extended (C's signed int32 high word). }
function HiS(V: Double): Int64;
begin
  Result := HiU(V);
  if Result >= $80000000 then
    Result := Result - $100000000;
end;

{ Low 32 bits as an unsigned value. }
function LoU(V: Double): Int64;
begin
  Result := DoubleBits(V) and $FFFFFFFF;
end;

{ Truncate an Int64 to its low 32 bits (unsigned view). }
function U32(V: Int64): Int64;
begin
  Result := V and $FFFFFFFF;
end;

{ INSERT_WORDS: build a double from 32-bit high and low halves. }
function ComposeD(Hi, Lo: Int64): Double;
begin
  Result := BitsToDouble(((Hi and $FFFFFFFF) shl 32) or (Lo and $FFFFFFFF));
end;

{ SET_HIGH_WORD: replace the high 32 bits, keep the low ones. }
procedure SetHiW(var V: Double; Hi: Int64);
begin
  V := BitsToDouble(((Hi and $FFFFFFFF) shl 32) or (DoubleBits(V) and $FFFFFFFF));
end;

{ SET_LOW_WORD: replace the low 32 bits, keep the high ones. }
procedure SetLoW(var V: Double; Lo: Int64);
begin
  V := BitsToDouble((DoubleBits(V) and (not $FFFFFFFF)) or (Lo and $FFFFFFFF));
end;

function IsNaND(V: Double): Boolean;
var
  B: Int64;
begin
  B := DoubleBits(V) and $7FFFFFFFFFFFFFFF;
  Result := B > $7FF0000000000000;
end;

{ ------------------------------------------------------------------ }
{ fabs / scalbn                                                        }
{ ------------------------------------------------------------------ }

function _BlaiseFabs(X: Double): Double;
begin
  Result := BitsToDouble(DoubleBits(X) and $7FFFFFFFFFFFFFFF);
end;

function _BlaiseScalbn(X: Double; N: Integer): Double;
var
  Y: Double;
begin
  Y := X;
  if N > 1023 then
  begin
    Y := Y * 8.98846567431157953865e+307;  { 0x1p1023 }
    N := N - 1023;
    if N > 1023 then
    begin
      Y := Y * 8.98846567431157953865e+307;
      N := N - 1023;
      if N > 1023 then
        N := 1023;
    end;
  end
  else if N < -1022 then
  begin
    Y := Y * 2.22507385850720138309e-308;  { 0x1p-1022 }
    N := N + 1022;
    if N < -1022 then
    begin
      Y := Y * 2.22507385850720138309e-308;
      N := N + 1022;
      if N < -1022 then
        N := -1022;
    end;
  end;
  Result := Y * BitsToDouble(Int64($3FF + N) shl 52);
end;

{ ------------------------------------------------------------------ }
{ floor / ceil / round (musl floor.c, ceil.c, round.c)                 }
{ ------------------------------------------------------------------ }

const
  { 1/DBL_EPSILON = 2^52; adding then subtracting it rounds to integer }
  TOINT_D = 4503599627370496.0;

function _BlaiseFloorD(X: Double): Double;
var
  B: Int64;
  E: Integer;
  Y: Double;
begin
  B := DoubleBits(X);
  E := ((B shr 52) and $7FF);
  if (E >= $3FF + 52) or (X = 0.0) then
    Exit(X);
  { y = int(x) - x, where int(x) is an integer neighbour of x }
  if B < 0 then
    Y := X - TOINT_D + TOINT_D - X
  else
    Y := X + TOINT_D - TOINT_D - X;
  if E <= $3FF - 1 then
  begin
    if B < 0 then
      Exit(-1.0);
    Exit(0.0);
  end;
  if Y > 0.0 then
    Exit(X + Y - 1.0);
  Result := X + Y;
end;

function _BlaiseCeilD(X: Double): Double;
var
  B: Int64;
  E: Integer;
  Y: Double;
begin
  B := DoubleBits(X);
  E := ((B shr 52) and $7FF);
  if (E >= $3FF + 52) or (X = 0.0) then
    Exit(X);
  if B < 0 then
    Y := X - TOINT_D + TOINT_D - X
  else
    Y := X + TOINT_D - TOINT_D - X;
  if E <= $3FF - 1 then
  begin
    if B < 0 then
      Exit(BitsToDouble(Int64($8000000000000000)))  { -0.0 }
    else
      Exit(1.0);
  end;
  if Y < 0.0 then
    Exit(X + Y + 1.0);
  Result := X + Y;
end;

{ Round half away from zero -- C99 round(), which is the documented
  semantics of the Blaise Round builtin (NOT banker's rounding). }
function _BlaiseRoundD(X: Double): Double;
var
  B: Int64;
  E: Integer;
  Y: Double;
begin
  B := DoubleBits(X);
  E := ((B shr 52) and $7FF);
  if E >= $3FF + 52 then
    Exit(X);
  if B < 0 then
    X := -X;
  if E < $3FF - 1 then
    { multiply keeps the sign of the original argument: 0 * -0.3 = -0.0 }
    Exit(0.0 * BitsToDouble(B));
  Y := X + TOINT_D - TOINT_D - X;
  if Y > 0.5 then
    Y := Y + X - 1.0
  else if Y <= -0.5 then
    Y := Y + X + 1.0
  else
    Y := Y + X;
  if B < 0 then
    Y := -Y;
  Result := Y;
end;

{ ------------------------------------------------------------------ }
{ sqrt (musl sqrt.c -- fdlibm bit-by-bit, correctly rounded)           }
{ ------------------------------------------------------------------ }

function _BlaiseSqrtD(X: Double): Double;
var
  Z: Double;
  Ix0, S0, Q, M, T, I: Int64;   { C int32 range by construction }
  R, T1, S1, Ix1, Q1: Int64;    { C uint32: masked after carrying ops }
  Tiny: Double;
begin
  Tiny := 1.0e-300;
  Ix0 := HiS(X);
  Ix1 := LoU(X);

  { Inf and NaN }
  if (Ix0 and $7FF00000) = $7FF00000 then
    Exit(X * X + X);
  { zero and negatives }
  if Ix0 <= 0 then
  begin
    if ((Ix0 and $7FFFFFFF) or Ix1) = 0 then
      Exit(X);                      { sqrt(+-0) = +-0 }
    if Ix0 < 0 then
      Exit((X - X) / (X - X));      { sqrt(-ve) = NaN }
  end;
  { normalize x }
  M := Ix0 shr 20;
  if M = 0 then
  begin
    { subnormal x }
    while Ix0 = 0 do
    begin
      M := M - 21;
      Ix0 := Ix0 or (Ix1 shr 11);
      Ix1 := U32(Ix1 shl 21);
    end;
    I := 0;
    while (Ix0 and $00100000) = 0 do
    begin
      Ix0 := Ix0 shl 1;
      I := I + 1;
    end;
    M := M - (I - 1);
    Ix0 := Ix0 or (Ix1 shr (32 - I));
    Ix1 := U32(Ix1 shl I);
  end;
  M := M - 1023;
  Ix0 := (Ix0 and $000FFFFF) or $00100000;
  if (M and 1) = 1 then
  begin
    { odd m, double x to make it even }
    Ix0 := Ix0 + Ix0 + ((Ix1 and $80000000) shr 31);
    Ix1 := U32(Ix1 + Ix1);
  end;
  { m >>= 1 with C arithmetic-shift semantics: FLOOR division.  m stays
    odd for odd exponents (the m&1 step above doubles the mantissa, not
    m), so truncating division would be off by one for negative m --
    that emerges as a result exactly 2x too large for tiny inputs. }
  if M >= 0 then
    M := M shr 1
  else
    M := (M - 1) div 2;

  { generate sqrt(x) bit by bit }
  Ix0 := Ix0 + Ix0 + ((Ix1 and $80000000) shr 31);
  Ix1 := U32(Ix1 + Ix1);
  Q := 0;
  Q1 := 0;
  S0 := 0;
  S1 := 0;
  R := $00200000;

  while R <> 0 do
  begin
    T := S0 + R;
    if T <= Ix0 then
    begin
      S0 := T + R;
      Ix0 := Ix0 - T;
      Q := Q + R;
    end;
    Ix0 := Ix0 + Ix0 + ((Ix1 and $80000000) shr 31);
    Ix1 := U32(Ix1 + Ix1);
    R := R shr 1;
  end;

  R := $80000000;
  while R <> 0 do
  begin
    T1 := U32(S1 + R);
    T := S0;
    if (T < Ix0) or ((T = Ix0) and (T1 <= Ix1)) then
    begin
      S1 := U32(T1 + R);
      if ((T1 and $80000000) = $80000000) and ((S1 and $80000000) = 0) then
        S0 := S0 + 1;
      Ix0 := Ix0 - T;
      if Ix1 < T1 then
        Ix0 := Ix0 - 1;
      Ix1 := U32(Ix1 - T1);
      Q1 := U32(Q1 + R);
    end;
    Ix0 := Ix0 + Ix0 + ((Ix1 and $80000000) shr 31);
    Ix1 := U32(Ix1 + Ix1);
    R := R shr 1;
  end;

  { use floating add to find out rounding direction }
  if (Ix0 or Ix1) <> 0 then
  begin
    Z := 1.0 - Tiny;  { trigger inexact; detects rounding mode }
    if Z >= 1.0 then
    begin
      Z := 1.0 + Tiny;
      if Q1 = $FFFFFFFF then
      begin
        Q1 := 0;
        Q := Q + 1;
      end
      else if Z > 1.0 then
      begin
        if Q1 = $FFFFFFFE then
          Q := Q + 1;
        Q1 := U32(Q1 + 2);
      end
      else
        Q1 := Q1 + (Q1 and 1);
    end;
  end;
  Ix0 := (Q shr 1) + $3FE00000;
  Ix1 := Q1 shr 1;
  if (Q and 1) = 1 then
    Ix1 := Ix1 or $80000000;
  Ix0 := Ix0 + (M shl 20);
  Result := ComposeD(Ix0, Ix1);
end;

{ ------------------------------------------------------------------ }
{ exp / expm1 (musl v1.1.16 exp.c, expm1.c)                            }
{ ------------------------------------------------------------------ }

const
  EXP_LN2HI = 6.93147180369123816490e-01;  { 0x3fe62e42, 0xfee00000 }
  EXP_LN2LO = 1.90821492927058770002e-10;  { 0x3dea39ef, 0x35793c76 }
  EXP_INVLN2 = 1.44269504088896338700e+00; { 0x3ff71547, 0x652b82fe }
  EXP_P1 =  1.66666666666666019037e-01;    { 0x3FC55555, 0x5555553E }
  EXP_P2 = -2.77777777770155933842e-03;    { 0xBF66C16C, 0x16BEBD93 }
  EXP_P3 =  6.61375632143793436117e-05;    { 0x3F11566A, 0xAF25DE2C }
  EXP_P4 = -1.65339022054652515390e-06;    { 0xBEBBBD41, 0xC5D26BF1 }
  EXP_P5 =  4.13813679705723846039e-08;    { 0x3E663769, 0x72BEA4D0 }

function _BlaiseExp(X: Double): Double;
var
  Hi, Lo, C, XX, Y: Double;
  K: Integer;
  Sign: Integer;
  Hx: Int64;
begin
  Hx := HiU(X);
  Sign := Hx shr 31;
  Hx := Hx and $7FFFFFFF;

  { special cases }
  if Hx >= $4086232B then
  begin
    { |x| >= 708.39... }
    if IsNaND(X) then
      Exit(X);
    if X > 709.782712893383973096 then
      { overflow (also inf): scale up out of range }
      Exit(X * 8.98846567431157953865e+307);  { 0x1p1023 }
    if X < -708.39641853226410622 then
      if X < -745.13321910194110842 then
        Exit(0.0);
  end;

  { argument reduction }
  if Hx > $3FD62E42 then
  begin
    { |x| > 0.5 ln2 }
    if Hx >= $3FF0A2B2 then
    begin
      { |x| >= 1.5 ln2 }
      if Sign = 0 then
        K := Trunc(EXP_INVLN2 * X + 0.5)
      else
        K := Trunc(EXP_INVLN2 * X - 0.5);
    end
    else
      K := 1 - Sign - Sign;
    Hi := X - K * EXP_LN2HI;  { k*ln2hi is exact here }
    Lo := K * EXP_LN2LO;
    X := Hi - Lo;
  end
  else if Hx > $3E300000 then
  begin
    { |x| > 2**-28 }
    K := 0;
    Hi := X;
    Lo := 0.0;
  end
  else
    Exit(1.0 + X);

  { x is now in primary range }
  XX := X * X;
  C := X - XX * (EXP_P1 + XX * (EXP_P2 + XX * (EXP_P3 + XX * (EXP_P4 + XX * EXP_P5))));
  Y := 1.0 + (X * C / (2.0 - C) - Lo + Hi);
  if K = 0 then
    Exit(Y);
  Result := _BlaiseScalbn(Y, K);
end;

const
  EM1_OTHRESH = 7.09782712893383973096e+02;  { 0x40862E42, 0xFEFA39EF }
  EM1_Q1 = -3.33333333333331316428e-02;      { BFA11111 111110F4 }
  EM1_Q2 =  1.58730158725481460165e-03;      { 3F5A01A0 19FE5585 }
  EM1_Q3 = -7.93650757867487942473e-05;      { BF14CE19 9EAADBB7 }
  EM1_Q4 =  4.00821782732936239552e-06;      { 3ED0CFCA 86E65239 }
  EM1_Q5 = -2.01099218183624371326e-07;      { BE8AFDB7 6E09C32D }

function _BlaiseExpm1(X: Double): Double;
var
  Y, Hi, Lo, C, T, E, Hxs, Hfx, R1, Twopk: Double;
  K, Sign: Integer;
  Hx: Int64;
begin
  Hx := HiU(X) and $7FFFFFFF;
  Sign := HiU(X) shr 31;
  C := 0.0;

  { filter out huge and non-finite argument }
  if Hx >= $4043687A then
  begin
    { |x| >= 56*ln2 }
    if IsNaND(X) then
      Exit(X);
    if Sign = 1 then
      Exit(-1.0);
    if X > EM1_OTHRESH then
      Exit(X * 8.98846567431157953865e+307);  { overflow to inf }
  end;

  { argument reduction }
  if Hx > $3FD62E42 then
  begin
    { |x| > 0.5 ln2 }
    if Hx < $3FF0A2B2 then
    begin
      { and |x| < 1.5 ln2 }
      if Sign = 0 then
      begin
        Hi := X - EXP_LN2HI;
        Lo := EXP_LN2LO;
        K := 1;
      end
      else
      begin
        Hi := X + EXP_LN2HI;
        Lo := -EXP_LN2LO;
        K := -1;
      end;
    end
    else
    begin
      if Sign = 0 then
        K := Trunc(EXP_INVLN2 * X + 0.5)
      else
        K := Trunc(EXP_INVLN2 * X - 0.5);
      T := K;
      Hi := X - T * EXP_LN2HI;  { t*ln2hi is exact here }
      Lo := T * EXP_LN2LO;
    end;
    X := Hi - Lo;
    C := (Hi - X) - Lo;
  end
  else if Hx < $3C900000 then
    { |x| < 2**-54 }
    Exit(X)
  else
    K := 0;

  { x is now in primary range }
  Hfx := 0.5 * X;
  Hxs := X * Hfx;
  R1 := 1.0 + Hxs * (EM1_Q1 + Hxs * (EM1_Q2 + Hxs * (EM1_Q3 + Hxs * (EM1_Q4 + Hxs * EM1_Q5))));
  T := 3.0 - R1 * Hfx;
  E := Hxs * ((R1 - T) / (6.0 - X * T));
  if K = 0 then
    Exit(X - (X * E - Hxs));  { c is 0 }
  E := X * (E - C) - C;
  E := E - Hxs;
  if K = -1 then
    Exit(0.5 * (X - E) - 0.5);
  if K = 1 then
  begin
    if X < -0.25 then
      Exit(-2.0 * (E - (X + 0.5)));
    Exit(1.0 + 2.0 * (X - E));
  end;
  Twopk := BitsToDouble(Int64($3FF + K) shl 52);  { 2^k }
  if (K < 0) or (K > 56) then
  begin
    { suffice to return exp(x)-1 }
    Y := X - E + 1.0;
    if K = 1024 then
      Y := Y * 2.0 * 8.98846567431157953865e+307
    else
      Y := Y * Twopk;
    Exit(Y - 1.0);
  end;
  if K < 20 then
    Y := (X - E + (1.0 - BitsToDouble(Int64($3FF - K) shl 52))) * Twopk
  else
    Y := (X - (E + BitsToDouble(Int64($3FF - K) shl 52)) + 1.0) * Twopk;
  Result := Y;
end;

{ ------------------------------------------------------------------ }
{ log / log2 / log10 (musl v1.1.16 log.c, log2.c, log10.c)             }
{ ------------------------------------------------------------------ }

const
  LOG_LG1 = 6.666666666666735130e-01;   { 3FE55555 55555593 }
  LOG_LG2 = 3.999999999940941908e-01;   { 3FD99999 9997FA04 }
  LOG_LG3 = 2.857142874366239149e-01;   { 3FD24924 94229359 }
  LOG_LG4 = 2.222219843214978396e-01;   { 3FCC71C5 1D8E78AF }
  LOG_LG5 = 1.818357216161805012e-01;   { 3FC74664 96CB03DE }
  LOG_LG6 = 1.531383769920937332e-01;   { 3FC39A09 D078C69F }
  LOG_LG7 = 1.479819860511658591e-01;   { 3FC2F112 DF3E5244 }

{ Shared head of the three logarithms: filters specials, reduces x into
  [sqrt(2)/2, sqrt(2)] and computes f, hfsq, s, R and k.  Returns True
  when the caller must return ASpecial immediately. }
function LogReduce(var X: Double; var K: Integer;
                   var F, Hfsq, S, R: Double;
                   var ASpecial: Double): Boolean;
var
  Bits: Int64;
  Hx: Int64;
  Z, W, T1, T2: Double;
begin
  Bits := DoubleBits(X);
  Hx := (Bits shr 32) and $FFFFFFFF;
  K := 0;
  if (Hx < $00100000) or ((Hx shr 31) = 1) then
  begin
    if (Bits shl 1) = 0 then
    begin
      ASpecial := -1.0 / (X * X);   { log(+-0) = -inf }
      Exit(True);
    end;
    if (Hx shr 31) = 1 then
    begin
      ASpecial := (X - X) / 0.0;    { log(-#) = NaN }
      Exit(True);
    end;
    { subnormal number, scale x up }
    K := K - 54;
    X := X * 18014398509481984.0;   { 0x1p54 }
    Bits := DoubleBits(X);
    Hx := (Bits shr 32) and $FFFFFFFF;
  end
  else if Hx >= $7FF00000 then
  begin
    ASpecial := X;
    Exit(True);
  end
  else if (Hx = $3FF00000) and ((Bits shl 32) = 0) then
  begin
    ASpecial := 0.0;
    Exit(True);
  end;

  { reduce x into [sqrt(2)/2, sqrt(2)] }
  Hx := Hx + ($3FF00000 - $3FE6A09E);
  K := K + ((Hx shr 20) - $3FF);
  Hx := (Hx and $000FFFFF) + $3FE6A09E;
  X := BitsToDouble((Hx shl 32) or (DoubleBits(X) and $FFFFFFFF));

  F := X - 1.0;
  Hfsq := 0.5 * F * F;
  S := F / (2.0 + F);
  Z := S * S;
  W := Z * Z;
  T1 := W * (LOG_LG2 + W * (LOG_LG4 + W * LOG_LG6));
  T2 := Z * (LOG_LG1 + W * (LOG_LG3 + W * (LOG_LG5 + W * LOG_LG7)));
  R := T2 + T1;
  Result := False;
end;

function _BlaiseLn(X: Double): Double;
const
  Ln2Hi = 6.93147180369123816490e-01;  { 3fe62e42 fee00000 }
  Ln2Lo = 1.90821492927058770002e-10;  { 3dea39ef 35793c76 }
var
  K: Integer;
  F, Hfsq, S, R, Dk, Special: Double;
begin
  if LogReduce(X, K, F, Hfsq, S, R, Special) then
    Exit(Special);
  Dk := K;
  Result := S * (Hfsq + R) + Dk * Ln2Lo - Hfsq + F + Dk * Ln2Hi;
end;

function _BlaiseLog2(X: Double): Double;
const
  IvLn2Hi = 1.44269504072144627571e+00;  { 0x3ff71547, 0x65200000 }
  IvLn2Lo = 1.67517131648865118353e-10;  { 0x3de705fc, 0x2eefa200 }
var
  K: Integer;
  F, Hfsq, S, R, Special: Double;
  Hi, Lo, ValHi, ValLo, W, Y: Double;
begin
  if LogReduce(X, K, F, Hfsq, S, R, Special) then
    Exit(Special);

  { hi+lo = f - hfsq + s*(hfsq+R) ~ log(1+f) }
  Hi := F - Hfsq;
  Hi := BitsToDouble(DoubleBits(Hi) and (not $FFFFFFFF));
  Lo := F - Hi - Hfsq + S * (Hfsq + R);

  ValHi := Hi * IvLn2Hi;
  ValLo := (Lo + Hi) * IvLn2Lo + Lo * IvLn2Hi;

  { spadd(val_hi, val_lo, y) }
  Y := K;
  W := Y + ValHi;
  ValLo := ValLo + ((Y - W) + ValHi);
  ValHi := W;

  Result := ValLo + ValHi;
end;

function _BlaiseLog10(X: Double): Double;
const
  IvLn10Hi = 4.34294481878168880939e-01;   { 0x3fdbcb7b, 0x15200000 }
  IvLn10Lo = 2.50829467116452752298e-11;   { 0x3dbb9438, 0xca9aadd5 }
  Log102Hi = 3.01029995663611771306e-01;   { 0x3FD34413, 0x509F6000 }
  Log102Lo = 3.69423907715893078616e-13;   { 0x3D59FEF3, 0x11F12B36 }
var
  K: Integer;
  F, Hfsq, S, R, Special: Double;
  Hi, Lo, ValHi, ValLo, Dk, W, Y: Double;
begin
  if LogReduce(X, K, F, Hfsq, S, R, Special) then
    Exit(Special);

  Hi := F - Hfsq;
  Hi := BitsToDouble(DoubleBits(Hi) and (not $FFFFFFFF));
  Lo := F - Hi - Hfsq + S * (Hfsq + R);

  ValHi := Hi * IvLn10Hi;
  Dk := K;
  Y := Dk * Log102Hi;
  ValLo := Dk * Log102Lo + (Lo + Hi) * IvLn10Lo + Lo * IvLn10Hi;

  W := Y + ValHi;
  ValLo := ValLo + ((Y - W) + ValHi);
  ValHi := W;

  Result := ValLo + ValHi;
end;

{ ------------------------------------------------------------------ }
{ Payne-Hanek argument reduction (musl __rem_pio2_large.c)             }
{ ------------------------------------------------------------------ }

const
  { 24-bit chunks of 2/pi after the binary point: chunk i holds bits
    24i..24i+23.  66 terms cover every finite double (e0 <= 1000 needs
    (e0-3)/24 + jk + margin ~ 50 terms). }
  IPIO2: array[0..65] of Integer = (
    $A2F983, $6E4E44, $1529FC, $2757D1, $F534DD, $C0DB62,
    $95993C, $439041, $FE5163, $ABDEBB, $C561B7, $246E3A,
    $424DD2, $E00649, $2EEA09, $D1921C, $FE1DEB, $1CB129,
    $A73EE8, $8235F5, $2EBB44, $84E99C, $7026B4, $5F7E41,
    $3991D6, $398353, $39F49C, $845F8B, $BDF928, $3B1FF8,
    $97FFDE, $05980F, $EF2F11, $8B5A0A, $6D1F6D, $367ECF,
    $27CB09, $B74F46, $3F669E, $5FEA2D, $7527BA, $C7EBE5,
    $F17B3D, $0739F7, $8A5292, $EA6BFB, $5FB11F, $8D5D08,
    $560330, $46FC7B, $6BABF0, $CFBC20, $9AF436, $1DA9E3,
    $91615E, $E61B08, $659985, $5F14A0, $68408D, $FFD880,
    $4D7327, $310606, $1556CA, $73A8C9, $60E27B, $C08C6B);

  { pi/2 cut into 24-bit chunks }
  PIO2S: array[0..7] of Double = (
    1.57079625129699707031e+00,  { 0x3FF921FB, 0x40000000 }
    7.54978941586159635335e-08,  { 0x3E74442D, 0x00000000 }
    5.39030252995776476554e-15,  { 0x3CF84698, 0x80000000 }
    3.28200341580791294123e-22,  { 0x3B78CC51, 0x60000000 }
    1.27065575308067607349e-29,  { 0x39F01B83, 0x80000000 }
    1.22933308981111328932e-36,  { 0x387A2520, 0x40000000 }
    2.73370053816464559624e-44,  { 0x36E38222, 0x80000000 }
    2.16741683877804819444e-51); { 0x3569F31D, 0x00000000 }

  TWO24_D = 16777216.0;                    { 0x1p24 }
  TWOM24_D = 5.96046447753906250000e-08;   { 0x1p-24 }

{ Double-precision-only port of __rem_pio2_large (prec fixed at 1, so
  jk = 4 and the result is Y0+Y1).  AX0..AX2 hold the input broken into
  24-bit chunks (ANx of them, passed as three plain doubles because the
  AArch64 backend does not lower var static-array parameters yet), AE0
  is the scaled exponent of AX0. }
function RemPio2Large(AX0, AX1, AX2: Double; var Y0, Y1: Double;
                      AE0, ANx: Integer): Integer;
const
  JK = 4;   { init_jk[1]: double precision }
var
  Jz, Jx, Jv, Jp, Carry, N, I, J, K, M, Q0, Ih: Integer;
  Z, Fw: Double;
  AX: array[0..2] of Double;
  F, Fq, Q: array[0..19] of Double;
  Iq: array[0..19] of Integer;
  NeedRecompute: Boolean;
begin
  AX[0] := AX0;
  AX[1] := AX1;
  AX[2] := AX2;
  Jp := JK;

  { determine jx,jv,q0, note that 3>q0 }
  Jx := ANx - 1;
  Jv := (AE0 - 3) div 24;
  if Jv < 0 then
    Jv := 0;
  Q0 := AE0 - 24 * (Jv + 1);

  { set up f[0] to f[jx+jk] where f[jx+jk] = ipio2[jv+jk] }
  J := Jv - Jx;
  M := Jx + JK;
  for I := 0 to M do
  begin
    if J < 0 then
      F[I] := 0.0
    else
      F[I] := IPIO2[J];
    J := J + 1;
  end;

  { compute q[0],q[1],...q[jk] }
  for I := 0 to JK do
  begin
    Fw := 0.0;
    for J := 0 to Jx do
      Fw := Fw + AX[J] * F[Jx + I - J];
    Q[I] := Fw;
  end;

  Jz := JK;
  repeat
    NeedRecompute := False;

    { distill q[] into iq[] reversingly }
    I := 0;
    J := Jz;
    Z := Q[Jz];
    while J > 0 do
    begin
      Fw := Trunc(TWOM24_D * Z);
      Iq[I] := Trunc(Z - TWO24_D * Fw);
      Z := Q[J - 1] + Fw;
      I := I + 1;
      J := J - 1;
    end;

    { compute n }
    Z := _BlaiseScalbn(Z, Q0);
    Z := Z - 8.0 * _BlaiseFloorD(Z * 0.125);  { trim off integer >= 8 }
    N := Trunc(Z);
    Z := Z - N;
    Ih := 0;
    if Q0 > 0 then
    begin
      { need iq[jz-1] to determine n }
      I := Iq[Jz - 1] shr (24 - Q0);
      N := N + I;
      Iq[Jz - 1] := Iq[Jz - 1] - (I shl (24 - Q0));
      Ih := Iq[Jz - 1] shr (23 - Q0);
    end
    else if Q0 = 0 then
      Ih := Iq[Jz - 1] shr 23
    else if Z >= 0.5 then
      Ih := 2;

    if Ih > 0 then
    begin
      { q > 0.5 }
      N := N + 1;
      Carry := 0;
      for I := 0 to Jz - 1 do
      begin
        { compute 1-q }
        J := Iq[I];
        if Carry = 0 then
        begin
          if J <> 0 then
          begin
            Carry := 1;
            Iq[I] := $1000000 - J;
          end;
        end
        else
          Iq[I] := $FFFFFF - J;
      end;
      if Q0 > 0 then
      begin
        { rare case: chance is 1 in 12 }
        if Q0 = 1 then
          Iq[Jz - 1] := Iq[Jz - 1] and $7FFFFF
        else if Q0 = 2 then
          Iq[Jz - 1] := Iq[Jz - 1] and $3FFFFF;
      end;
      if Ih = 2 then
      begin
        Z := 1.0 - Z;
        if Carry <> 0 then
          Z := Z - _BlaiseScalbn(1.0, Q0);
      end;
    end;

    { check if recomputation is needed }
    if Z = 0.0 then
    begin
      J := 0;
      for I := Jz - 1 downto JK do
        J := J or Iq[I];
      if J = 0 then
      begin
        { need recomputation }
        K := 1;
        while Iq[JK - K] = 0 do
          K := K + 1;
        for I := Jz + 1 to Jz + K do
        begin
          { add q[jz+1] to q[jz+k] }
          F[Jx + I] := IPIO2[Jv + I];
          Fw := 0.0;
          for J := 0 to Jx do
            Fw := Fw + AX[J] * F[Jx + I - J];
          Q[I] := Fw;
        end;
        Jz := Jz + K;
        NeedRecompute := True;
      end;
    end;
  until not NeedRecompute;

  { chop off zero terms }
  if Z = 0.0 then
  begin
    Jz := Jz - 1;
    Q0 := Q0 - 24;
    while Iq[Jz] = 0 do
    begin
      Jz := Jz - 1;
      Q0 := Q0 - 24;
    end;
  end
  else
  begin
    { break z into 24-bit if necessary }
    Z := _BlaiseScalbn(Z, -Q0);
    if Z >= TWO24_D then
    begin
      Fw := Trunc(TWOM24_D * Z);
      Iq[Jz] := Trunc(Z - TWO24_D * Fw);
      Jz := Jz + 1;
      Q0 := Q0 + 24;
      Iq[Jz] := Trunc(Fw);
    end
    else
      Iq[Jz] := Trunc(Z);
  end;

  { convert integer "bit" chunk to floating-point value }
  Fw := _BlaiseScalbn(1.0, Q0);
  for I := Jz downto 0 do
  begin
    Q[I] := Fw * Iq[I];
    Fw := Fw * TWOM24_D;
  end;

  { compute PIo2[0,...,jp]*q[jz,...,0] }
  for I := Jz downto 0 do
  begin
    Fw := 0.0;
    K := 0;
    while (K <= Jp) and (K <= Jz - I) do
    begin
      Fw := Fw + PIO2S[K] * Q[I + K];
      K := K + 1;
    end;
    Fq[Jz - I] := Fw;
  end;

  { compress fq[] into y[] (prec = 1: two doubles) }
  Fw := 0.0;
  for I := Jz downto 0 do
    Fw := Fw + Fq[I];
  if Ih = 0 then
    Y0 := Fw
  else
    Y0 := -Fw;
  Fw := Fq[0] - Fw;
  for I := 1 to Jz do
    Fw := Fw + Fq[I];
  if Ih = 0 then
    Y1 := Fw
  else
    Y1 := -Fw;

  Result := N and 7;
end;

{ ------------------------------------------------------------------ }
{ __rem_pio2 (musl __rem_pio2.c)                                       }
{ ------------------------------------------------------------------ }

const
  RP_TOINT = 6755399441055744.0;             { 1.5/DBL_EPSILON = 1.5*2^52 }
  RP_INVPIO2 = 6.36619772367581382433e-01;   { 0x3FE45F30, 0x6DC9C883 }
  RP_PIO2_1 = 1.57079632673412561417e+00;    { 0x3FF921FB, 0x54400000 }
  RP_PIO2_1T = 6.07710050650619224932e-11;   { 0x3DD0B461, 0x1A626331 }
  RP_PIO2_2 = 6.07710050630396597660e-11;    { 0x3DD0B461, 0x1A600000 }
  RP_PIO2_2T = 2.02226624879595063154e-21;   { 0x3BA3198A, 0x2E037073 }
  RP_PIO2_3 = 2.02226624871116645580e-21;    { 0x3BA3198A, 0x2E000000 }
  RP_PIO2_3T = 8.47842766036889956997e-32;   { 0x397B839A, 0x252049C1 }

{ The medium-size path: n = rint(x/(pi/2)) and a 2-3 round compensated
  subtraction.  Factored out because the C original reaches it by goto
  from the small-multiple fast paths on cancellation-risky inputs. }
function RemPio2Medium(X: Double; Ix: Int64; var Y0, Y1: Double): Integer;
var
  Fn, R, W, T: Double;
  N, Ex, Ey: Integer;
begin
  { rint(x/(pi/2)); assumes round-to-nearest }
  Fn := X * RP_INVPIO2 + RP_TOINT - RP_TOINT;
  N := Trunc(Fn);
  R := X - Fn * RP_PIO2_1;
  W := Fn * RP_PIO2_1T;  { 1st round, good to 85 bits }
  Y0 := R - W;
  Ey := (DoubleBits(Y0) shr 52) and $7FF;
  Ex := Ix shr 20;
  if Ex - Ey > 16 then
  begin
    { 2nd round, good to 118 bits }
    T := R;
    W := Fn * RP_PIO2_2;
    R := T - W;
    W := Fn * RP_PIO2_2T - ((T - R) - W);
    Y0 := R - W;
    Ey := (DoubleBits(Y0) shr 52) and $7FF;
    if Ex - Ey > 49 then
    begin
      { 3rd round, good to 151 bits, covers all cases }
      T := R;
      W := Fn * RP_PIO2_3;
      R := T - W;
      W := Fn * RP_PIO2_3T - ((T - R) - W);
      Y0 := R - W;
    end;
  end;
  Y1 := (R - Y0) - W;
  Result := N;
end;

{ Reduce x mod pi/2: result in Y0+Y1, returns n (quadrant count).
  Caller must handle |x| ~<= pi/4 itself. }
function RemPio2(X: Double; var Y0, Y1: Double): Integer;
var
  Ix: Int64;
  Sign: Integer;
  Z, W: Double;
  Tx: array[0..2] of Double;
  N, I: Integer;
  Bits: Int64;
begin
  Bits := DoubleBits(X);
  Sign := (Bits shr 63) and 1;
  Ix := (Bits shr 32) and $7FFFFFFF;
  if Ix <= $400F6A7A then
  begin
    { |x| ~<= 5pi/4 }
    if (Ix and $FFFFF) = $921FB then
      { |x| ~= pi/2 or 2pi/2 -- cancellation: use medium path }
      Exit(RemPio2Medium(X, Ix, Y0, Y1));
    if Ix <= $4002D97C then
    begin
      { |x| ~<= 3pi/4 }
      if Sign = 0 then
      begin
        Z := X - RP_PIO2_1;  { one round good to 85 bits }
        Y0 := Z - RP_PIO2_1T;
        Y1 := (Z - Y0) - RP_PIO2_1T;
        Exit(1);
      end
      else
      begin
        Z := X + RP_PIO2_1;
        Y0 := Z + RP_PIO2_1T;
        Y1 := (Z - Y0) + RP_PIO2_1T;
        Exit(-1);
      end;
    end
    else
    begin
      if Sign = 0 then
      begin
        Z := X - 2 * RP_PIO2_1;
        Y0 := Z - 2 * RP_PIO2_1T;
        Y1 := (Z - Y0) - 2 * RP_PIO2_1T;
        Exit(2);
      end
      else
      begin
        Z := X + 2 * RP_PIO2_1;
        Y0 := Z + 2 * RP_PIO2_1T;
        Y1 := (Z - Y0) + 2 * RP_PIO2_1T;
        Exit(-2);
      end;
    end;
  end;
  if Ix <= $401C463B then
  begin
    { |x| ~<= 9pi/4 }
    if Ix <= $4015FDBC then
    begin
      { |x| ~<= 7pi/4 }
      if Ix = $4012D97C then
        { |x| ~= 3pi/2 }
        Exit(RemPio2Medium(X, Ix, Y0, Y1));
      if Sign = 0 then
      begin
        Z := X - 3 * RP_PIO2_1;
        Y0 := Z - 3 * RP_PIO2_1T;
        Y1 := (Z - Y0) - 3 * RP_PIO2_1T;
        Exit(3);
      end
      else
      begin
        Z := X + 3 * RP_PIO2_1;
        Y0 := Z + 3 * RP_PIO2_1T;
        Y1 := (Z - Y0) + 3 * RP_PIO2_1T;
        Exit(-3);
      end;
    end
    else
    begin
      if Ix = $401921FB then
        { |x| ~= 4pi/2 }
        Exit(RemPio2Medium(X, Ix, Y0, Y1));
      if Sign = 0 then
      begin
        Z := X - 4 * RP_PIO2_1;
        Y0 := Z - 4 * RP_PIO2_1T;
        Y1 := (Z - Y0) - 4 * RP_PIO2_1T;
        Exit(4);
      end
      else
      begin
        Z := X + 4 * RP_PIO2_1;
        Y0 := Z + 4 * RP_PIO2_1T;
        Y1 := (Z - Y0) + 4 * RP_PIO2_1T;
        Exit(-4);
      end;
    end;
  end;
  if Ix < $413921FB then
    { |x| ~< 2^20*(pi/2), medium size }
    Exit(RemPio2Medium(X, Ix, Y0, Y1));

  { all other (large) arguments }
  if Ix >= $7FF00000 then
  begin
    { x is inf or NaN }
    Y0 := X - X;
    Y1 := Y0;
    Exit(0);
  end;
  { set z = scalbn(|x|, -ilogb(x)+23) }
  Z := BitsToDouble((Bits and $000FFFFFFFFFFFFF) or (Int64($3FF + 23) shl 52));
  for I := 0 to 1 do
  begin
    Tx[I] := Trunc(Z);
    Z := (Z - Tx[I]) * TWO24_D;
  end;
  Tx[2] := Z;
  I := 2;
  { skip zero terms, first term is non-zero }
  while Tx[I] = 0.0 do
    I := I - 1;
  N := RemPio2Large(Tx[0], Tx[1], Tx[2], Y0, Y1,
                    (Ix shr 20) - ($3FF + 23), I + 1);
  if Sign = 1 then
  begin
    W := -Y0;
    Y0 := W;
    Y1 := -Y1;
    Exit(-N);
  end;
  Result := N;
end;

{ ------------------------------------------------------------------ }
{ sin/cos/tan kernels (musl __sin.c, __cos.c, __tan.c)                 }
{ ------------------------------------------------------------------ }

const
  KS_S1 = -1.66666666666666324348e-01;  { 0xBFC55555, 0x55555549 }
  KS_S2 =  8.33333333332248946124e-03;  { 0x3F811111, 0x1110F8A6 }
  KS_S3 = -1.98412698298579493134e-04;  { 0xBF2A01A0, 0x19C161D5 }
  KS_S4 =  2.75573137070700676789e-06;  { 0x3EC71DE3, 0x57B1FE7D }
  KS_S5 = -2.50507602534068634195e-08;  { 0xBE5AE5E6, 0x8A2B9CEB }
  KS_S6 =  1.58969099521155010221e-10;  { 0x3DE5D93A, 0x5ACFD57C }

{ kernel sin on ~[-pi/4, pi/4]; y is the tail of x, iy=0 means y is 0 }
function KernSin(X, Y: Double; Iy: Integer): Double;
var
  Z, R, V, W: Double;
begin
  Z := X * X;
  W := Z * Z;
  R := KS_S2 + Z * (KS_S3 + Z * KS_S4) + Z * W * (KS_S5 + Z * KS_S6);
  V := Z * X;
  if Iy = 0 then
    Result := X + V * (KS_S1 + Z * R)
  else
    Result := X - ((Z * (0.5 * Y - V * R) - Y) - V * KS_S1);
end;

const
  KC_C1 =  4.16666666666666019037e-02;  { 0x3FA55555, 0x5555554C }
  KC_C2 = -1.38888888888741095749e-03;  { 0xBF56C16C, 0x16C15177 }
  KC_C3 =  2.48015872894767294178e-05;  { 0x3EFA01A0, 0x19CB1590 }
  KC_C4 = -2.75573143513906633035e-07;  { 0xBE927E4F, 0x809C52AD }
  KC_C5 =  2.08757232129817482790e-09;  { 0x3E21EE9E, 0xBDB4B1C4 }
  KC_C6 = -1.13596475577881948265e-11;  { 0xBDA8FAE9, 0xBE8838D4 }

{ kernel cos on [-pi/4, pi/4]; y is the tail of x }
function KernCos(X, Y: Double): Double;
var
  Hz, Z, R, W: Double;
begin
  Z := X * X;
  W := Z * Z;
  R := Z * (KC_C1 + Z * (KC_C2 + Z * KC_C3)) + W * W * (KC_C4 + Z * (KC_C5 + Z * KC_C6));
  Hz := 0.5 * Z;
  W := 1.0 - Hz;
  Result := W + (((1.0 - W) - Hz) + (Z * R - X * Y));
end;

const
  KT_T0 =  3.33333333333334091986e-01;   { 3FD55555, 55555563 }
  KT_T1 =  1.33333333333201242699e-01;   { 3FC11111, 1110FE7A }
  KT_T2 =  5.39682539762260521377e-02;   { 3FABA1BA, 1BB341FE }
  KT_T3 =  2.18694882948595424599e-02;   { 3F9664F4, 8406D637 }
  KT_T4 =  8.86323982359930005737e-03;   { 3F8226E3, E96E8493 }
  KT_T5 =  3.59207910759131235356e-03;   { 3F6D6D22, C9560328 }
  KT_T6 =  1.45620945432529025516e-03;   { 3F57DBC8, FEE08315 }
  KT_T7 =  5.88041240820264096874e-04;   { 3F4344D8, F2F26501 }
  KT_T8 =  2.46463134818469906812e-04;   { 3F3026F7, 1A8D1068 }
  KT_T9 =  7.81794442939557092300e-05;   { 3F147E88, A03792A6 }
  KT_T10 =  7.14072491382608190305e-05;  { 3F12B80F, 32F0A7E9 }
  KT_T11 = -1.85586374855275456654e-05;  { BEF375CB, DB605373 }
  KT_T12 =  2.59073051863633712884e-05;  { 3EFB2A70, 74BF7AD4 }
  KT_PIO4 = 7.85398163397448278999e-01;  { 3FE921FB, 54442D18 }
  KT_PIO4LO = 3.06161699786838301793e-17; { 3C81A626, 33145C07 }

{ kernel tan on ~[-pi/4, pi/4]; returns tan when Odd=0, -1/tan when Odd=1 }
function KernTan(X, Y: Double; Odd: Integer): Double;
var
  Z, R, V, W, S, A: Double;
  W0, A0: Double;
  Hx: Int64;
  Big, Sign: Integer;
begin
  Hx := HiU(X);
  Sign := 0;
  if (Hx and $7FFFFFFF) >= $3FE59428 then
    Big := 1   { |x| >= 0.6744 }
  else
    Big := 0;
  if Big = 1 then
  begin
    Sign := Hx shr 31;
    if Sign = 1 then
    begin
      X := -X;
      Y := -Y;
    end;
    X := (KT_PIO4 - X) + (KT_PIO4LO - Y);
    Y := 0.0;
  end;
  Z := X * X;
  W := Z * Z;
  R := KT_T1 + W * (KT_T3 + W * (KT_T5 + W * (KT_T7 + W * (KT_T9 + W * KT_T11))));
  V := Z * (KT_T2 + W * (KT_T4 + W * (KT_T6 + W * (KT_T8 + W * (KT_T10 + W * KT_T12)))));
  S := Z * X;
  R := Y + Z * (S * (R + V) + Y) + S * KT_T0;
  W := X + R;
  if Big = 1 then
  begin
    S := 1 - 2 * Odd;
    V := S - 2.0 * (X + (R - W * W / (W + S)));
    if Sign = 1 then
      Exit(-V);
    Exit(V);
  end;
  if Odd = 0 then
    Exit(W);
  { -1.0/(x+r) has up to 2ulp error, so compute it accurately }
  W0 := W;
  SetLoW(W0, 0);
  V := R - (W0 - X);  { w0+v = r+x }
  A := -1.0 / W;
  A0 := A;
  SetLoW(A0, 0);
  Result := A0 + A * (1.0 + A0 * W0 + A0 * V);
end;

{ ------------------------------------------------------------------ }
{ sin / cos / tan drivers (musl sin.c, cos.c, tan.c)                   }
{ ------------------------------------------------------------------ }

function _BlaiseSin(X: Double): Double;
var
  Y0, Y1: Double;
  Ix: Int64;
  N: Integer;
begin
  Ix := HiU(X) and $7FFFFFFF;

  { |x| ~< pi/4 }
  if Ix <= $3FE921FB then
  begin
    if Ix < $3E500000 then
      { |x| < 2**-26 }
      Exit(X);
    Exit(KernSin(X, 0.0, 0));
  end;

  { sin(Inf or NaN) is NaN }
  if Ix >= $7FF00000 then
    Exit(X - X);

  { argument reduction needed }
  Y0 := 0.0;
  Y1 := 0.0;
  N := RemPio2(X, Y0, Y1);
  case N and 3 of
    0: Result := KernSin(Y0, Y1, 1);
    1: Result := KernCos(Y0, Y1);
    2: Result := -KernSin(Y0, Y1, 1);
  else
    Result := -KernCos(Y0, Y1);
  end;
end;

function _BlaiseCos(X: Double): Double;
var
  Y0, Y1: Double;
  Ix: Int64;
  N: Integer;
begin
  Ix := HiU(X) and $7FFFFFFF;

  { |x| ~< pi/4 }
  if Ix <= $3FE921FB then
  begin
    if Ix < $3E46A09E then
      { |x| < 2**-27 * sqrt(2) }
      Exit(1.0);
    Exit(KernCos(X, 0.0));
  end;

  { cos(Inf or NaN) is NaN }
  if Ix >= $7FF00000 then
    Exit(X - X);

  Y0 := 0.0;
  Y1 := 0.0;
  N := RemPio2(X, Y0, Y1);
  case N and 3 of
    0: Result := KernCos(Y0, Y1);
    1: Result := -KernSin(Y0, Y1, 1);
    2: Result := -KernCos(Y0, Y1);
  else
    Result := KernSin(Y0, Y1, 1);
  end;
end;

function _BlaiseTan(X: Double): Double;
var
  Y0, Y1: Double;
  Ix: Int64;
  N: Integer;
begin
  Ix := HiU(X) and $7FFFFFFF;

  { |x| ~< pi/4 }
  if Ix <= $3FE921FB then
  begin
    if Ix < $3E400000 then
      { |x| < 2**-27 }
      Exit(X);
    Exit(KernTan(X, 0.0, 0));
  end;

  { tan(Inf or NaN) is NaN }
  if Ix >= $7FF00000 then
    Exit(X - X);

  Y0 := 0.0;
  Y1 := 0.0;
  N := RemPio2(X, Y0, Y1);
  Result := KernTan(Y0, Y1, N and 1);
end;

{ ------------------------------------------------------------------ }
{ asin / acos (musl asin.c, acos.c)                                    }
{ ------------------------------------------------------------------ }

const
  AS_PIO2HI = 1.57079632679489655800e+00;  { 0x3FF921FB, 0x54442D18 }
  AS_PIO2LO = 6.12323399573676603587e-17;  { 0x3C91A626, 0x33145C07 }
  AS_PS0 =  1.66666666666666657415e-01;    { 0x3FC55555, 0x55555555 }
  AS_PS1 = -3.25565818622400915405e-01;    { 0xBFD4D612, 0x03EB6F7D }
  AS_PS2 =  2.01212532134862925881e-01;    { 0x3FC9C155, 0x0E884455 }
  AS_PS3 = -4.00555345006794114027e-02;    { 0xBFA48228, 0xB5688F3B }
  AS_PS4 =  7.91534994289814532176e-04;    { 0x3F49EFE0, 0x7501B288 }
  AS_PS5 =  3.47933107596021167570e-05;    { 0x3F023DE1, 0x0DFDF709 }
  AS_QS1 = -2.40339491173441421878e+00;    { 0xC0033A27, 0x1C8A2D4B }
  AS_QS2 =  2.02094576023350569471e+00;    { 0x40002AE5, 0x9C598AC8 }
  AS_QS3 = -6.88283971605453293030e-01;    { 0xBFE6066C, 0x1B8D0159 }
  AS_QS4 =  7.70381505559019352791e-02;    { 0x3FB3B8C5, 0xB12E9282 }

{ rational approximation of (asin(x)-x)/x^3, shared by asin and acos }
function ArcR(Z: Double): Double;
var
  P, Q: Double;
begin
  P := Z * (AS_PS0 + Z * (AS_PS1 + Z * (AS_PS2 + Z * (AS_PS3 + Z * (AS_PS4 + Z * AS_PS5)))));
  Q := 1.0 + Z * (AS_QS1 + Z * (AS_QS2 + Z * (AS_QS3 + Z * AS_QS4)));
  Result := P / Q;
end;

function _BlaiseArcSin(X: Double): Double;
var
  Z, R, S, F, C: Double;
  Hx, Ix, Lx: Int64;
begin
  Hx := HiU(X);
  Ix := Hx and $7FFFFFFF;
  { |x| >= 1 or nan }
  if Ix >= $3FF00000 then
  begin
    Lx := LoU(X);
    if ((Ix - $3FF00000) or Lx) = 0 then
      { asin(1) = +-pi/2 }
      Exit(X * AS_PIO2HI);
    Exit((X - X) / (X - X));   { NaN for |x| > 1 }
  end;
  { |x| < 0.5 }
  if Ix < $3FE00000 then
  begin
    if (Ix < $3E500000) and (Ix >= $00100000) then
      Exit(X);
    Exit(X + X * ArcR(X * X));
  end;
  { 1 > |x| >= 0.5 }
  Z := (1.0 - _BlaiseFabs(X)) * 0.5;
  S := _BlaiseSqrtD(Z);
  R := ArcR(Z);
  if Ix >= $3FEF3333 then
    { |x| > 0.975 }
    X := AS_PIO2HI - (2 * (S + S * R) - AS_PIO2LO)
  else
  begin
    { f+c = sqrt(z) }
    F := S;
    SetLoW(F, 0);
    C := (Z - F * F) / (S + F);
    X := 0.5 * AS_PIO2HI - (2 * S * R - (AS_PIO2LO - 2 * C) - (0.5 * AS_PIO2HI - 2 * F));
  end;
  if (Hx shr 31) = 1 then
    Exit(-X);
  Result := X;
end;

function _BlaiseArcCos(X: Double): Double;
var
  Z, W, S, C, Df: Double;
  Hx, Ix, Lx: Int64;
begin
  Hx := HiU(X);
  Ix := Hx and $7FFFFFFF;
  { |x| >= 1 or nan }
  if Ix >= $3FF00000 then
  begin
    Lx := LoU(X);
    if ((Ix - $3FF00000) or Lx) = 0 then
    begin
      { acos(1)=0, acos(-1)=pi }
      if (Hx shr 31) = 1 then
        Exit(2 * AS_PIO2HI);
      Exit(0.0);
    end;
    Exit((X - X) / (X - X));
  end;
  { |x| < 0.5 }
  if Ix < $3FE00000 then
  begin
    if Ix <= $3C600000 then
      { |x| < 2**-57 }
      Exit(AS_PIO2HI);
    Exit(AS_PIO2HI - (X - (AS_PIO2LO - X * ArcR(X * X))));
  end;
  { x < -0.5 }
  if (Hx shr 31) = 1 then
  begin
    Z := (1.0 + X) * 0.5;
    S := _BlaiseSqrtD(Z);
    W := ArcR(Z) * S - AS_PIO2LO;
    Exit(2 * (AS_PIO2HI - (S + W)));
  end;
  { x > 0.5 }
  Z := (1.0 - X) * 0.5;
  S := _BlaiseSqrtD(Z);
  Df := S;
  SetLoW(Df, 0);
  C := (Z - Df * Df) / (S + Df);
  W := ArcR(Z) * S + C;
  Result := 2 * (Df + W);
end;

{ ------------------------------------------------------------------ }
{ atan / atan2 (musl atan.c, atan2.c)                                  }
{ ------------------------------------------------------------------ }

const
  AT_HI: array[0..3] of Double = (
    4.63647609000806093515e-01,  { atan(0.5)hi 0x3FDDAC67, 0x0561BB4F }
    7.85398163397448278999e-01,  { atan(1.0)hi 0x3FE921FB, 0x54442D18 }
    9.82793723247329054082e-01,  { atan(1.5)hi 0x3FEF730B, 0xD281F69B }
    1.57079632679489655800e+00); { atan(inf)hi 0x3FF921FB, 0x54442D18 }
  AT_LO: array[0..3] of Double = (
    2.26987774529616870924e-17,  { atan(0.5)lo 0x3C7A2B7F, 0x222F65E2 }
    3.06161699786838301793e-17,  { atan(1.0)lo 0x3C81A626, 0x33145C07 }
    1.39033110312309984516e-17,  { atan(1.5)lo 0x3C700788, 0x7AF0CBBD }
    6.12323399573676603587e-17); { atan(inf)lo 0x3C91A626, 0x33145C07 }
  AT_T: array[0..10] of Double = (
    3.33333333333329318027e-01,  { 0x3FD55555, 0x5555550D }
   -1.99999999998764832476e-01,  { 0xBFC99999, 0x9998EBC4 }
    1.42857142725034663711e-01,  { 0x3FC24924, 0x920083FF }
   -1.11111104054623557880e-01,  { 0xBFBC71C6, 0xFE231671 }
    9.09088713343650656196e-02,  { 0x3FB745CD, 0xC54C206E }
   -7.69187620504482999495e-02,  { 0xBFB3B0F2, 0xAF749A6D }
    6.66107313738753120669e-02,  { 0x3FB10D66, 0xA0D03D51 }
   -5.83357013379057348645e-02,  { 0xBFADDE2D, 0x52DEFD9A }
    4.97687799461593236017e-02,  { 0x3FA97B4B, 0x24760DEB }
   -3.65315727442169155270e-02,  { 0xBFA2B444, 0x2C6A6C2F }
    1.62858201153657823623e-02); { 0x3F90AD3A, 0xE322DA11 }

function _BlaiseArcTan(X: Double): Double;
var
  W, S1, S2, Z: Double;
  Ix, Sign: Int64;
  Id: Integer;
begin
  Ix := HiU(X);
  Sign := Ix shr 31;
  Ix := Ix and $7FFFFFFF;
  if Ix >= $44100000 then
  begin
    { |x| >= 2^66 }
    if IsNaND(X) then
      Exit(X);
    Z := AT_HI[3];
    if Sign = 1 then
      Exit(-Z);
    Exit(Z);
  end;
  if Ix < $3FDC0000 then
  begin
    { |x| < 0.4375 }
    if Ix < $3E400000 then
      { |x| < 2^-27 }
      Exit(X);
    Id := -1;
  end
  else
  begin
    X := _BlaiseFabs(X);
    if Ix < $3FF30000 then
    begin
      { |x| < 1.1875 }
      if Ix < $3FE60000 then
      begin
        { 7/16 <= |x| < 11/16 }
        Id := 0;
        X := (2.0 * X - 1.0) / (2.0 + X);
      end
      else
      begin
        { 11/16 <= |x| < 19/16 }
        Id := 1;
        X := (X - 1.0) / (X + 1.0);
      end;
    end
    else
    begin
      if Ix < $40038000 then
      begin
        { |x| < 2.4375 }
        Id := 2;
        X := (X - 1.5) / (1.0 + 1.5 * X);
      end
      else
      begin
        { 2.4375 <= |x| < 2^66 }
        Id := 3;
        X := -1.0 / X;
      end;
    end;
  end;
  { end of argument reduction }
  Z := X * X;
  W := Z * Z;
  { break the polynomial sum into odd and even parts }
  S1 := Z * (AT_T[0] + W * (AT_T[2] + W * (AT_T[4] + W * (AT_T[6] + W * (AT_T[8] + W * AT_T[10])))));
  S2 := W * (AT_T[1] + W * (AT_T[3] + W * (AT_T[5] + W * (AT_T[7] + W * AT_T[9]))));
  if Id < 0 then
    Exit(X - X * (S1 + S2));
  Z := AT_HI[Id] - (X * (S1 + S2) - AT_LO[Id] - X);
  if Sign = 1 then
    Exit(-Z);
  Result := Z;
end;

function _BlaiseArcTan2(Y, X: Double): Double;
const
  A2_PI = 3.1415926535897931160e+00;     { 0x400921FB, 0x54442D18 }
  A2_PILO = 1.2246467991473531772e-16;   { 0x3CA1A626, 0x33145C07 }
var
  Z: Double;
  M, Lx, Ly, Ix, Iy: Int64;
begin
  if IsNaND(X) or IsNaND(Y) then
    Exit(X + Y);
  Ix := HiU(X);
  Lx := LoU(X);
  Iy := HiU(Y);
  Ly := LoU(Y);
  if ((Ix - $3FF00000) or Lx) = 0 then
    { x = 1.0 }
    Exit(_BlaiseArcTan(Y));
  M := ((Iy shr 31) and 1) or ((Ix shr 30) and 2);  { 2*sign(x)+sign(y) }
  Ix := Ix and $7FFFFFFF;
  Iy := Iy and $7FFFFFFF;

  { when y = 0 }
  if (Iy or Ly) = 0 then
  begin
    case M of
      0, 1: Exit(Y);           { atan(+-0,+anything)=+-0 }
      2: Exit(A2_PI);          { atan(+0,-anything) = pi }
      3: Exit(-A2_PI);         { atan(-0,-anything) =-pi }
    end;
  end;
  { when x = 0 }
  if (Ix or Lx) = 0 then
  begin
    if (M and 1) = 1 then
      Exit(-A2_PI / 2);
    Exit(A2_PI / 2);
  end;
  { when x is INF }
  if Ix = $7FF00000 then
  begin
    if Iy = $7FF00000 then
    begin
      case M of
        0: Exit(A2_PI / 4);        { atan(+INF,+INF) }
        1: Exit(-A2_PI / 4);       { atan(-INF,+INF) }
        2: Exit(3.0 * A2_PI / 4);  { atan(+INF,-INF) }
      else
        Exit(-3.0 * A2_PI / 4);    { atan(-INF,-INF) }
      end;
    end
    else
    begin
      case M of
        0: Exit(0.0);
        1: Exit(BitsToDouble(Int64($8000000000000000)));  { -0.0 }
        2: Exit(A2_PI);
      else
        Exit(-A2_PI);
      end;
    end;
  end;
  { |y/x| > 0x1p64 }
  if (Ix + (64 shl 20) < Iy) or (Iy = $7FF00000) then
  begin
    if (M and 1) = 1 then
      Exit(-A2_PI / 2);
    Exit(A2_PI / 2);
  end;

  { z = atan(|y/x|) without spurious underflow }
  if ((M and 2) = 2) and (Iy + (64 shl 20) < Ix) then
    { |y/x| < 0x1p-64, x < 0 }
    Z := 0.0
  else
    Z := _BlaiseArcTan(_BlaiseFabs(Y / X));
  case M of
    0: Result := Z;                    { atan(+,+) }
    1: Result := -Z;                   { atan(-,+) }
    2: Result := A2_PI - (Z - A2_PILO);{ atan(+,-) }
  else
    Result := (Z - A2_PILO) - A2_PI;   { atan(-,-) }
  end;
end;

{ ------------------------------------------------------------------ }
{ sinh / cosh / tanh (musl sinh.c, cosh.c, tanh.c, __expo2.c)          }
{ ------------------------------------------------------------------ }

{ exp(x)/2 for x >= log(DBL_MAX): exp(x - k*ln2) * 2^(k-1) with k=2043 }
function Expo2(X: Double): Double;
const
  KLN2 = 1.41609968988396826717e+03;  { 0x1.62066151add8bp+10 }
var
  Scale: Double;
begin
  { 2^((k-1)/2) squared = 2^(k-1); k odd, scale*scale overflows alone }
  Scale := ComposeD(($3FF + 2043 div 2) shl 20, 0);
  Result := _BlaiseExp(X - KLN2) * Scale * Scale;
end;

function _BlaiseSinh(X: Double): Double;
var
  H, T, AbsX: Double;
  W: Int64;
  Neg: Boolean;
begin
  Neg := DoubleBits(X) < 0;
  H := 0.5;
  if Neg then
    H := -0.5;
  AbsX := _BlaiseFabs(X);
  W := HiU(AbsX);

  { |x| < log(DBL_MAX) }
  if W < $40862E42 then
  begin
    T := _BlaiseExpm1(AbsX);
    if W < $3FF00000 then
    begin
      if W < $3FF00000 - (26 shl 20) then
        Exit(X);
      Exit(H * (2 * T - T * T / (T + 1.0)));
    end;
    Exit(H * (T + T / (T + 1.0)));
  end;

  { |x| > log(DBL_MAX) or nan }
  Result := 2 * H * Expo2(AbsX);
end;

function _BlaiseCosh(X: Double): Double;
var
  T: Double;
  W: Int64;
begin
  X := _BlaiseFabs(X);
  W := HiU(X);

  { |x| < log(2) }
  if W < $3FE62E42 then
  begin
    if W < $3FF00000 - (26 shl 20) then
      Exit(1.0);
    T := _BlaiseExpm1(X);
    Exit(1.0 + T * T / (2 * (1.0 + T)));
  end;

  { |x| < log(DBL_MAX) }
  if W < $40862E42 then
  begin
    T := _BlaiseExp(X);
    Exit(0.5 * (T + 1.0 / T));
  end;

  { |x| > log(DBL_MAX) or nan }
  Result := Expo2(X);
end;

function _BlaiseTanh(X: Double): Double;
var
  T, AbsX: Double;
  W: Int64;
  Neg: Boolean;
begin
  Neg := DoubleBits(X) < 0;
  AbsX := _BlaiseFabs(X);
  W := HiU(AbsX);

  if W > $3FE193EA then
  begin
    { |x| > log(3)/2 ~= 0.5493 or nan }
    if W > $40340000 then
      { |x| > 20 or nan }
      T := 1.0 - 0.0 / AbsX
    else
    begin
      T := _BlaiseExpm1(2 * AbsX);
      T := 1.0 - 2.0 / (T + 2.0);
    end;
  end
  else if W > $3FD058AE then
  begin
    { |x| > log(5/3)/2 ~= 0.2554 }
    T := _BlaiseExpm1(2 * AbsX);
    T := T / (T + 2.0);
  end
  else if W >= $00100000 then
  begin
    { |x| >= 0x1p-1022 }
    T := _BlaiseExpm1(-2 * AbsX);
    T := -T / (T + 2.0);
  end
  else
    { |x| is subnormal }
    T := AbsX;
  if Neg then
    Exit(-T);
  Result := T;
end;

{ ------------------------------------------------------------------ }
{ pow (musl v1.1.16 pow.c)                                             }
{ ------------------------------------------------------------------ }

const
  PW_DPH1 = 5.84962487220764160156e-01;  { 0x3FE2B803, 0x40000000 }
  PW_DPL1 = 1.35003920212974897128e-08;  { 0x3E4CFDEB, 0x43CFD006 }
  PW_TWO53 = 9007199254740992.0;         { 0x43400000, 0x00000000 }
  PW_HUGE = 1.0e300;
  PW_TINY = 1.0e-300;
  { poly coefs for (3/2)*(log(x)-2s-2/3*s**3 }
  PW_L1 = 5.99999999999994648725e-01;    { 0x3FE33333, 0x33333303 }
  PW_L2 = 4.28571428578550184252e-01;    { 0x3FDB6DB6, 0xDB6FABFF }
  PW_L3 = 3.33333329818377432918e-01;    { 0x3FD55555, 0x518F264D }
  PW_L4 = 2.72728123808534006489e-01;    { 0x3FD17460, 0xA91D4101 }
  PW_L5 = 2.30660745775561754067e-01;    { 0x3FCD864A, 0x93C9DB65 }
  PW_L6 = 2.06975017800338417784e-01;    { 0x3FCA7E28, 0x4A454EEF }
  PW_LG2 = 6.93147180559945286227e-01;   { 0x3FE62E42, 0xFEFA39EF }
  PW_LG2H = 6.93147182464599609375e-01;  { 0x3FE62E43, 0x00000000 }
  PW_LG2L = -1.90465429995776804525e-09; { 0xBE205C61, 0x0CA86C39 }
  PW_OVT = 8.0085662595372944372e-017;   { -(1024-log2(ovfl+.5ulp)) }
  PW_CP = 9.61796693925975554329e-01;    { 0x3FEEC709, 0xDC3A03FD = 2/(3ln2) }
  PW_CPH = 9.61796700954437255859e-01;   { 0x3FEEC709, 0xE0000000 }
  PW_CPL = -7.02846165095275826516e-09;  { 0xBE3E2FE0, 0x145B01F5 }
  PW_IVLN2 = 1.44269504088896338700e+00; { 0x3FF71547, 0x652B82FE }
  PW_IVLN2H = 1.44269502162933349609e+00;{ 0x3FF71547, 0x60000000 }
  PW_IVLN2L = 1.92596299112661746887e-08;{ 0x3E54AE0B, 0xF85DDF44 }

function _BlaisePow(X, Y: Double): Double;
var
  Z, Ax, Zh, Zl, Ph, Pl: Double;
  Y1, T1, T2, R, S, T, U, V, W: Double;
  Ss, S2, Sh, Sl, Th, Tl: Double;
  I, J, K, Yisint, N: Int64;    { C int32 -- ranges asserted per site }
  Hx, Hy, Ix, Iy: Int64;        { signed high words }
  Lx, Ly: Int64;                { unsigned low words }
  Bp, DpH, DpL: Double;
begin
  Hx := HiS(X);
  Lx := LoU(X);
  Hy := HiS(Y);
  Ly := LoU(Y);
  Ix := Hx and $7FFFFFFF;
  Iy := Hy and $7FFFFFFF;

  { x**0 = 1, even if x is NaN }
  if (Iy or Ly) = 0 then
    Exit(1.0);
  { 1**y = 1, even if y is NaN }
  if (Hx = $3FF00000) and (Lx = 0) then
    Exit(1.0);
  { NaN if either arg is NaN }
  if (Ix > $7FF00000) or ((Ix = $7FF00000) and (Lx <> 0)) or
     (Iy > $7FF00000) or ((Iy = $7FF00000) and (Ly <> 0)) then
    Exit(X + Y);

  { determine if y is an odd int when x < 0:
    yisint = 0 ... y is not an integer
    yisint = 1 ... y is an odd int
    yisint = 2 ... y is an even int }
  Yisint := 0;
  if Hx < 0 then
  begin
    if Iy >= $43400000 then
      Yisint := 2
    else if Iy >= $3FF00000 then
    begin
      K := (Iy shr 20) - $3FF;
      if K > 20 then
      begin
        J := Ly shr (52 - K);
        if (J shl (52 - K)) = Ly then
          Yisint := 2 - (J and 1);
      end
      else if Ly = 0 then
      begin
        J := Iy shr (20 - K);
        if (J shl (20 - K)) = Iy then
          Yisint := 2 - (J and 1);
      end;
    end;
  end;

  { special value of y }
  if Ly = 0 then
  begin
    if Iy = $7FF00000 then
    begin
      { y is +-inf }
      if ((Ix - $3FF00000) or Lx) = 0 then
        Exit(1.0)          { (-1)**+-inf is 1 }
      else if Ix >= $3FF00000 then
      begin
        { (|x|>1)**+-inf = inf,0 }
        if Hy >= 0 then
          Exit(Y);
        Exit(0.0);
      end
      else
      begin
        { (|x|<1)**+-inf = 0,inf }
        if Hy >= 0 then
          Exit(0.0);
        Exit(-Y);
      end;
    end;
    if Iy = $3FF00000 then
    begin
      { y is +-1 }
      if Hy >= 0 then
        Exit(X);
      Exit(1.0 / X);
    end;
    if Hy = $40000000 then
      Exit(X * X);         { y is 2 }
    if Hy = $3FE00000 then
      { y is 0.5 }
      if Hx >= 0 then
        Exit(_BlaiseSqrtD(X));
  end;

  Ax := _BlaiseFabs(X);
  { special value of x }
  if Lx = 0 then
  begin
    if (Ix = $7FF00000) or (Ix = 0) or (Ix = $3FF00000) then
    begin
      { x is +-0, +-inf, +-1 }
      Z := Ax;
      if Hy < 0 then
        Z := 1.0 / Z;
      if Hx < 0 then
      begin
        if ((Ix - $3FF00000) or Yisint) = 0 then
          Z := (Z - Z) / (Z - Z)  { (-1)**non-int is NaN }
        else if Yisint = 1 then
          Z := -Z;                { (x<0)**odd = -(|x|**odd) }
      end;
      Exit(Z);
    end;
  end;

  S := 1.0;  { sign of result }
  if Hx < 0 then
  begin
    if Yisint = 0 then
      Exit((X - X) / (X - X));  { (x<0)**(non-int) is NaN }
    if Yisint = 1 then
      S := -1.0;
  end;

  { |y| is huge }
  if Iy > $41E00000 then
  begin
    { |y| > 2**31 }
    if Iy > $43F00000 then
    begin
      { |y| > 2**64, must over/underflow }
      if Ix <= $3FEFFFFF then
      begin
        if Hy < 0 then
          Exit(PW_HUGE * PW_HUGE);
        Exit(PW_TINY * PW_TINY);
      end;
      if Ix >= $3FF00000 then
      begin
        if Hy > 0 then
          Exit(PW_HUGE * PW_HUGE);
        Exit(PW_TINY * PW_TINY);
      end;
    end;
    { over/underflow if x is not close to one }
    if Ix < $3FEFFFFF then
    begin
      if Hy < 0 then
        Exit(S * PW_HUGE * PW_HUGE);
      Exit(S * PW_TINY * PW_TINY);
    end;
    if Ix > $3FF00000 then
    begin
      if Hy > 0 then
        Exit(S * PW_HUGE * PW_HUGE);
      Exit(S * PW_TINY * PW_TINY);
    end;
    { now |1-x| is tiny <= 2**-20, sufficient to compute
      log(x) by x - x^2/2 + x^3/3 - x^4/4 }
    T := Ax - 1.0;  { t has 20 trailing zeros }
    W := (T * T) * (0.5 - T * (0.3333333333333333333333 - T * 0.25));
    U := PW_IVLN2H * T;  { ivln2_h has 21 sig. bits }
    V := T * PW_IVLN2L - W * PW_IVLN2;
    T1 := U + V;
    SetLoW(T1, 0);
    T2 := V - (T1 - U);
  end
  else
  begin
    N := 0;
    { take care of subnormal numbers }
    if Ix < $00100000 then
    begin
      Ax := Ax * PW_TWO53;
      N := N - 53;
      Ix := HiS(Ax);
    end;
    N := N + (Ix shr 20) - $3FF;
    J := Ix and $000FFFFF;
    { determine interval }
    Ix := J or $3FF00000;  { normalize ix }
    if J <= $3988E then
      K := 0                { |x| < sqrt(3/2) }
    else if J < $BB67A then
      K := 1                { |x| < sqrt(3) }
    else
    begin
      K := 0;
      N := N + 1;
      Ix := Ix - $00100000;
    end;
    SetHiW(Ax, Ix);
    if K = 0 then
    begin
      Bp := 1.0;
      DpH := 0.0;
      DpL := 0.0;
    end
    else
    begin
      Bp := 1.5;
      DpH := PW_DPH1;
      DpL := PW_DPL1;
    end;

    { compute ss = s_h+s_l = (x-1)/(x+1) or (x-1.5)/(x+1.5) }
    U := Ax - Bp;
    V := 1.0 / (Ax + Bp);
    Ss := U * V;
    Sh := Ss;
    SetLoW(Sh, 0);
    { t_h = ax + bp[k] High }
    Th := 0.0;
    SetHiW(Th, ((Ix shr 1) or $20000000) + $00080000 + (K shl 18));
    Tl := Ax - (Th - Bp);
    Sl := V * ((U - Sh * Th) - Sh * Tl);
    { compute log(ax) }
    S2 := Ss * Ss;
    R := S2 * S2 * (PW_L1 + S2 * (PW_L2 + S2 * (PW_L3 + S2 * (PW_L4 + S2 * (PW_L5 + S2 * PW_L6)))));
    R := R + Sl * (Sh + Ss);
    S2 := Sh * Sh;
    Th := 3.0 + S2 + R;
    SetLoW(Th, 0);
    Tl := R - ((Th - 3.0) - S2);
    { u+v = ss*(1+...) }
    U := Sh * Th;
    V := Sl * Th + Tl * Ss;
    { 2/(3log2)*(ss+...) }
    Ph := U + V;
    SetLoW(Ph, 0);
    Pl := V - (Ph - U);
    Zh := PW_CPH * Ph;  { cp_h+cp_l = 2/(3*log2) }
    Zl := PW_CPL * Ph + Pl * PW_CP + DpL;
    { log2(ax) = (ss+..)*2/(3*log2) = n + dp_h + z_h + z_l }
    T := N;
    T1 := ((Zh + Zl) + DpH) + T;
    SetLoW(T1, 0);
    T2 := Zl - (((T1 - T) - DpH) - Zh);
  end;

  { split up y into y1+y2 and compute (y1+y2)*(t1+t2) }
  Y1 := Y;
  SetLoW(Y1, 0);
  Pl := (Y - Y1) * T1 + Y * T2;
  Ph := Y1 * T1;
  Z := Pl + Ph;
  J := HiS(Z);
  I := LoU(Z);
  if J >= $40900000 then
  begin
    { z >= 1024 }
    if ((J - $40900000) or I) <> 0 then
      Exit(S * PW_HUGE * PW_HUGE);  { overflow }
    if Pl + PW_OVT > Z - Ph then
      Exit(S * PW_HUGE * PW_HUGE);  { overflow }
  end
  else if (J and $7FFFFFFF) >= $4090CC00 then
  begin
    { z <= -1075 }
    { j - (int32)0xc090cc00: 0xc090cc00 as a signed int32 is -1064252416 }
    if ((J + 1064252416) or I) <> 0 then
      Exit(S * PW_TINY * PW_TINY);  { underflow }
    if Pl <= Z - Ph then
      Exit(S * PW_TINY * PW_TINY);  { underflow }
  end;

  { compute 2**(p_h+p_l) }
  I := J and $7FFFFFFF;
  K := (I shr 20) - $3FF;
  N := 0;
  if I > $3FE00000 then
  begin
    { if |z| > 0.5, set n = [z+0.5] }
    N := J + ($00100000 shr (K + 1));
    K := ((N and $7FFFFFFF) shr 20) - $3FF;  { new k for n }
    T := 0.0;
    SetHiW(T, N and (not ($000FFFFF shr K)));
    N := ((N and $000FFFFF) or $00100000) shr (20 - K);
    if J < 0 then
      N := -N;
    Ph := Ph - T;
  end;
  T := Pl + Ph;
  SetLoW(T, 0);
  U := T * PW_LG2H;
  V := (Pl - (T - Ph)) * PW_LG2 + T * PW_LG2L;
  Z := U + V;
  W := V - (Z - U);
  T := Z * Z;
  T1 := Z - T * (EXP_P1 + T * (EXP_P2 + T * (EXP_P3 + T * (EXP_P4 + T * EXP_P5))));
  R := (Z * T1) / (T1 - 2.0) - (W + Z * W);
  Z := 1.0 - (R - Z);
  J := HiS(Z);
  J := J + (N shl 20);
  { (j >> 20) <= 0 with C arithmetic-shift semantics: true for j < 2^20,
    including all negative j -- integer div matches that test exactly }
  if (J div $100000) <= 0 then
    Z := _BlaiseScalbn(Z, N)   { subnormal output }
  else
    SetHiW(Z, J);
  Result := S * Z;
end;

end.
