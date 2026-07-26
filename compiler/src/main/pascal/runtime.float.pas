{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — float support functions (pure Pascal, no libc dependency)

  _DoubleToStr / _SingleToStr : convert float to Blaise string (ARC heap).
  _StrToDouble                : convert Blaise string to double.
  _AbsInt / _AbsInt64         : absolute value for integer types.

  Float-to-string uses a simplified Grisu1 algorithm (Florian Loitsch, 2010)
  targeting IEEE-754 binary64 only.  String-to-float uses a scaled-integer
  approach with the same cached power-of-10 table.

  String memory layout (same as all other Blaise strings):
    data_ptr - 12 : refcount  (int32)
    data_ptr -  8 : length    (int32)
    data_ptr -  4 : capacity  (int32)
    data_ptr +  0 : char data + NUL
}

unit runtime.float;

interface

function _DoubleToStr(V: Double): Pointer;
function _SingleToStr(V: Single): Pointer;
function _StrToDouble(S: Pointer): Double;
function _AbsInt(N: Integer): Integer;
function _AbsInt64(N: Int64): Int64;

{ Render V according to a printf-style float conversion for Format().
    Spec : ASCII code of the conversion letter — 'f'/'F', 'e'/'E', 'g'/'G'.
    Prec : number of digits after the point (f/e) or significant digits (g);
           -1 selects the conversion's default precision.
  Returns a freshly-allocated Blaise string (refcount = 1). }
function _FormatFloatSpec(V: Double; Spec: Integer; Prec: Integer): Pointer;

implementation

const
  BLAISE_STR_HDR = 12;

function _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';
procedure libc_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

function BlaiseAllocStr(Src: PChar; Len: Integer): Pointer;
var
  Cap: Integer;
  Base: Pointer;
  RC, LN, CP: ^Integer;
  Data: PChar;
begin
  Cap := Len + 1;
  Base := _BlaiseGetMem(BLAISE_STR_HDR + Cap);
  if Base = nil then
  begin
    Exit(nil);
  end;
  RC := Base;        RC^ := 1;
  LN := Base + 4;    LN^ := Len;
  CP := Base + 8;    CP^ := Cap;
  Data := PChar(Base + BLAISE_STR_HDR);
  if Len > 0 then
    libc_memcpy(Data, Src, Len);
  Data[Len] := 0;
  Result := Pointer(Data);
end;

{ --- IEEE-754 binary64 bit manipulation via pointer aliasing --- }

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

{ --- 64-bit unsigned helpers using signed Int64 + shr (logical in QBE) --- }

function Hi32(X: Int64): Int64;
begin
  Result := (X shr 32) and $FFFFFFFF;
end;

function Lo32(X: Int64): Int64;
begin
  Result := X and $FFFFFFFF;
end;

{ Multiply two 64-bit values and return the upper 64 bits of the 128-bit
  product, with rounding.  All values are treated as unsigned (QBE shr is
  logical).  Uses the standard 4-way 32-bit cross-multiplication. }
function MulHi64(A, B: Int64): Int64;
var
  AH, AL, BH, BL: Int64;
  AC, BC, AD, BD, T1: Int64;
begin
  AH := Hi32(A);  AL := Lo32(A);
  BH := Hi32(B);  BL := Lo32(B);
  AC := AH * BH;
  BC := AL * BH;
  AD := AH * BL;
  BD := AL * BL;
  T1 := Int64($80000000)
      + Hi32(BD) + Lo32(BC) + Lo32(AD);
  Result := AC + Hi32(AD) + Hi32(BC) + Hi32(T1);
end;

{ Count leading zeros of a 64-bit value (treated as unsigned). }
function CLZ64(X: Int64): Integer;
var
  N: Integer;
begin
  if X = 0 then
  begin
    Exit(64);
  end;
  N := 0;
  if (X shr 32) = 0 then begin N := N + 32; X := X shl 32; end;
  if (X shr 48) = 0 then begin N := N + 16; X := X shl 16; end;
  if (X shr 56) = 0 then begin N := N +  8; X := X shl  8; end;
  if (X shr 60) = 0 then begin N := N +  4; X := X shl  4; end;
  if (X shr 62) = 0 then begin N := N +  2; X := X shl  2; end;
  if (X shr 63) = 0 then N := N + 1;
  Result := N;
end;

{ --- DIY floating point: (mantissa, exponent) pair --- }

type
  TDIY = record
    F: Int64;
    E: Integer;
  end;

function DIYMul(X, Y: TDIY): TDIY;
begin
  Result.F := MulHi64(X.F, Y.F);
  Result.E := X.E + Y.E + 64;
  if (Result.F shr 63) = 0 then
  begin
    Result.F := Result.F shl 1;
    Result.E := Result.E - 1;
  end;
end;

{ --- Cached normalised powers of 10 for Grisu1 (IEEE-754 double range) ---
  Three parallel arrays: mantissa (F), binary exponent (E), decimal
  exponent (E10).  Coverage: 10^-348 .. 10^+340, step = 8 (87 entries). }

const
  POW10_COUNT = 87;
  POW10_MIN = -348;
  POW10_STEP = 8;

var
  Pow10F: array[0..86] of Int64;
  Pow10E: array[0..86] of Integer;
  Pow10E10: array[0..86] of Integer;
  Pow10CacheReady: Integer;

procedure SetP(I: Integer; AF: Int64; AE: Integer; AE10: Integer);
begin
  Pow10F[I] := AF;
  Pow10E[I] := AE;
  Pow10E10[I] := AE10;
end;

procedure InitPow10Cache;
begin
  SetP( 0, Int64($FA8FD5A0081C0288), -1220, -348);
  SetP( 1, Int64($BAAEE17FA23EBF76), -1193, -340);
  SetP( 2, Int64($8B16FB203055AC76), -1166, -332);
  SetP( 3, Int64($CF42894A5DCE35EA), -1140, -324);
  SetP( 4, Int64($9A6BB0AA55653B2D), -1113, -316);
  SetP( 5, Int64($E61ACF033D1A45DF), -1087, -308);
  SetP( 6, Int64($AB70FE17C79AC6CA), -1060, -300);
  SetP( 7, Int64($FF77B1FCBEBCDC4F), -1034, -292);
  SetP( 8, Int64($BE5691EF416BD60C), -1007, -284);
  SetP( 9, Int64($8DD01FAD907FFC3C),  -980, -276);
  SetP(10, Int64($D3515C2831559A83),  -954, -268);
  SetP(11, Int64($9D71AC8FADA6C9B5),  -927, -260);
  SetP(12, Int64($EA9C227723EE8BCB),  -901, -252);
  SetP(13, Int64($AECC49914078536D),  -874, -244);
  SetP(14, Int64($823C12795DB6CE57),  -847, -236);
  SetP(15, Int64($C21094364DFB5637),  -821, -228);
  SetP(16, Int64($9096EA6F3848984F),  -794, -220);
  SetP(17, Int64($D77485CB25823AC7),  -768, -212);
  SetP(18, Int64($A086CFCD97BF97F4),  -741, -204);
  SetP(19, Int64($EF340A98172AACE5),  -715, -196);
  SetP(20, Int64($B23867FB2A35B28E),  -688, -188);
  SetP(21, Int64($84C8D4DFD2C63F3B),  -661, -180);
  SetP(22, Int64($C5DD44271AD3CDBA),  -635, -172);
  SetP(23, Int64($936B9FCEBB25C996),  -608, -164);
  SetP(24, Int64($DBAC6C247D62A584),  -582, -156);
  SetP(25, Int64($A3AB66580D5FDAF6),  -555, -148);
  SetP(26, Int64($F3E2F893DEC3F126),  -529, -140);
  SetP(27, Int64($B5B5ADA8AAFF80B8),  -502, -132);
  SetP(28, Int64($87625F056C7C4A8B),  -475, -124);
  SetP(29, Int64($C9BCFF6034C13053),  -449, -116);
  SetP(30, Int64($964E858C91BA2655),  -422, -108);
  SetP(31, Int64($DFF9772470297EBD),  -396, -100);
  SetP(32, Int64($A6DFBD9FB8E5B88F),  -369,  -92);
  SetP(33, Int64($F8A95FCF88747D94),  -343,  -84);
  SetP(34, Int64($B94470938FA89BCF),  -316,  -76);
  SetP(35, Int64($8A08F0F8BF0F156B),  -289,  -68);
  SetP(36, Int64($CDB02555653131B6),  -263,  -60);
  SetP(37, Int64($993FE2C6D07B7FAC),  -236,  -52);
  SetP(38, Int64($E45C10C42A2B3B06),  -210,  -44);
  SetP(39, Int64($AA242499697392D3),  -183,  -36);
  SetP(40, Int64($FD87B5F28300CA0E),  -157,  -28);
  SetP(41, Int64($BCE5086492111AEB),  -130,  -20);
  SetP(42, Int64($8CBCCC096F5088CC),  -103,  -12);
  SetP(43, Int64($D1B71758E219652C),   -77,   -4);
  SetP(44, Int64($9C40000000000000),   -50,    4);
  SetP(45, Int64($E8D4A51000000000),   -24,   12);
  SetP(46, Int64($AD78EBC5AC620000),     3,   20);
  SetP(47, Int64($813F3978F8940984),    30,   28);
  SetP(48, Int64($C097CE7BC90715B3),    56,   36);
  SetP(49, Int64($8F7E32CE7BEA5C70),    83,   44);
  SetP(50, Int64($D5D238A4ABE98068),   109,   52);
  SetP(51, Int64($9F4F2726179A2245),   136,   60);
  SetP(52, Int64($ED63A231D4C4FB27),   162,   68);
  SetP(53, Int64($B0DE65388CC8ADA8),   189,   76);
  SetP(54, Int64($83C7088E1AAB65DB),   216,   84);
  SetP(55, Int64($C45D1DF942711D9A),   242,   92);
  SetP(56, Int64($924D692CA61BE758),   269,  100);
  SetP(57, Int64($DA01EE641A708DEA),   295,  108);
  SetP(58, Int64($A26DA3999AEF774A),   322,  116);
  SetP(59, Int64($F209787BB47D6B85),   348,  124);
  SetP(60, Int64($B454E4A179DD1877),   375,  132);
  SetP(61, Int64($865B86925B9BC5C2),   402,  140);
  SetP(62, Int64($C83553C5C8965D3D),   428,  148);
  SetP(63, Int64($952AB45CFA97A0B3),   455,  156);
  SetP(64, Int64($DE469FBD99A05FE3),   481,  164);
  SetP(65, Int64($A59BC234DB398C25),   508,  172);
  SetP(66, Int64($F6C69A72A3989F5C),   534,  180);
  SetP(67, Int64($B7DCBF5354E9BECE),   561,  188);
  SetP(68, Int64($88FCF317F22241E2),   588,  196);
  SetP(69, Int64($CC20CE9BD35C78A5),   614,  204);
  SetP(70, Int64($98165AF37B2153DF),   641,  212);
  SetP(71, Int64($E2A0B5DC971F303A),   667,  220);
  SetP(72, Int64($A8D9D1535CE3B396),   694,  228);
  SetP(73, Int64($FB9B7CD9A4A7443C),   720,  236);
  SetP(74, Int64($BB764C4CA7A44410),   747,  244);
  SetP(75, Int64($8BAB8EEFB6409C1A),   774,  252);
  SetP(76, Int64($D01FEF10A657842C),   800,  260);
  SetP(77, Int64($9B10A4E5E9913129),   827,  268);
  SetP(78, Int64($E7109BFBA19C0C9D),   853,  276);
  SetP(79, Int64($AC2820D9623BF429),   880,  284);
  SetP(80, Int64($80444B5E7AA7CF85),   907,  292);
  SetP(81, Int64($BF21E44003ACDD2D),   933,  300);
  SetP(82, Int64($8E679C2F5E44FF8F),   960,  308);
  SetP(83, Int64($D433179D9C8CB841),   986,  316);
  SetP(84, Int64($9E19DB92B4E31BA9),  1013,  324);
  SetP(85, Int64($EB96BF6EBADF77D9),  1039,  332);
  SetP(86, Int64($AF87023B9BF0EE6B),  1066,  340);
end;

procedure EnsurePow10;
begin
  if Pow10CacheReady = 0 then
  begin
    InitPow10Cache();
    Pow10CacheReady := 1;
  end;
end;

function FindCachedPow10(TargetE10: Integer): Integer;
var
  I: Integer;
begin
  I := (TargetE10 - POW10_MIN) div POW10_STEP;
  if I < 0 then I := 0;
  if I >= POW10_COUNT then I := POW10_COUNT - 1;
  while (Pow10E10[I] < TargetE10) and (I + 1 < POW10_COUNT) do
    I := I + 1;
  Result := I;
end;

{ --- Grisu1 core: double -> decimal digits --- }

const
  DBL_FRAC_BITS = 52;
  DBL_EXP_BIAS = 1023;
  DBL_EXP_SPECIAL = 2047;
  GRISU_ALPHA = -61;

procedure DoubleToDigits(V: Double; Digits: PChar;
  out NDigits: Integer; out DecExp: Integer; out Negative: Boolean);
var
  Bits: Int64;
  BExp: Integer;
  Frac: Int64;
  W, CMK, Scaled: TDIY;
  One: TDIY;
  Integ, FracPart: Int64;
  FMask: Int64;
  K, Idx, N, Pos: Integer;
  D, Z: Int64;
begin
  EnsurePow10();

  Bits := DoubleBits(V);
  Negative := (Bits shr 63) <> 0;
  BExp := Integer((Bits shr 52) and $7FF);
  Frac := Bits and $000FFFFFFFFFFFFF;

  { Normalise: subnormals have BExp=0, normals have implicit bit }
  if BExp = 0 then
  begin
    W.F := Frac;
    W.E := 1 - DBL_EXP_BIAS - DBL_FRAC_BITS;
    N := CLZ64(Frac);
    W.F := W.F shl N;
    W.E := W.E - N;
  end
  else
  begin
    W.F := Frac or (Int64(1) shl DBL_FRAC_BITS);
    W.E := BExp - DBL_EXP_BIAS - DBL_FRAC_BITS;
    W.F := W.F shl 11;
    W.E := W.E - 11;
  end;

  { k_comp: mk = ceil((alpha - w.e) * log10(2))
    Integer approx: ceil(x * 0.30103) ~ (x * 78913 + 2^18 - 1) >> 18
    Then find cached power with e10 >= mk. }
  K := GRISU_ALPHA - W.E;
  if K >= 0 then
    Idx := (K * 78913 + 262143) shr 18
  else
    Idx := -((-K * 78913) shr 18);
  Idx := FindCachedPow10(Idx);
  CMK.F := Pow10F[Idx];
  CMK.E := Pow10E[Idx];

  { Multiply W by the cached power }
  Scaled := DIYMul(W, CMK);

  { Decimal exponent: the cached entry represents 10^e10, so the
    number is approximately Scaled.F * 2^Scaled.E, and the decimal
    point sits at -Pow10E10[Idx].  We extract digits from Scaled
    using integer/fraction split at the "one" boundary. }
  One.F := Int64(1) shl (-Scaled.E);
  One.E := Scaled.E;
  FMask := One.F - 1;

  Integ := Scaled.F shr (-Scaled.E);
  FracPart := Scaled.F and FMask;

  { Generate integer-part digits }
  Pos := 0;
  if Integ > 0 then
  begin
    { Count digits in Integ }
    N := 0;
    D := Integ;
    while D > 0 do
    begin
      N := N + 1;
      D := D div 10;
    end;
    { Write digits in order }
    D := Integ;
    K := N - 1;
    while K >= 0 do
    begin
      Z := D div 10;
      Digits[Pos + K] := Integer(D - Z * 10) + 48;
      D := Z;
      K := K - 1;
    end;
    Pos := N;
  end
  else
    N := 0;

  { Generate fraction-part digits (up to 18 total) }
  while (Pos < 18) and (FracPart > 0) do
  begin
    FracPart := FracPart * 10;
    D := FracPart shr (-One.E);
    Digits[Pos] := Integer(D) + 48;
    FracPart := FracPart and FMask;
    Pos := Pos + 1;
  end;

  NDigits := Pos;
  DecExp := N - Pow10E10[Idx];

  { Strip trailing zeros }
  while (NDigits > 1) and (Digits[NDigits - 1] = 48) do
    NDigits := NDigits - 1;
end;

{ --- Format digits into %.15g / %.7g style output --- }

function FormatFloat(V: Double; MaxSigDigits: Integer): Pointer;
var
  Bits: Int64;
  BExp: Integer;
  Frac: Int64;
  Negative: Boolean;
  Digits: PChar;
  Buf: PChar;
  NDigits, DecExp, Pos, I: Integer;
begin
  Bits := DoubleBits(V);
  BExp := Integer((Bits shr 52) and $7FF);
  Frac := Bits and $000FFFFFFFFFFFFF;
  Negative := (Bits shr 63) <> 0;

  { Handle special values }
  if BExp = DBL_EXP_SPECIAL then
  begin
    if Frac <> 0 then
    begin
      if Negative then
        Result := BlaiseAllocStr(PChar('-nan'), 4)
      else
        Result := BlaiseAllocStr(PChar('nan'), 3);
      Exit;
    end;
    if Negative then
      Result := BlaiseAllocStr(PChar('-inf'), 4)
    else
      Result := BlaiseAllocStr(PChar('inf'), 3);
    Exit;
  end;

  { Handle zero }
  if (BExp = 0) and (Frac = 0) then
  begin
    if Negative then
      Result := BlaiseAllocStr(PChar('-0'), 2)
    else
      Result := BlaiseAllocStr(PChar('0'), 1);
    Exit;
  end;

  Digits := PChar(_BlaiseGetMem(32));
  Buf := PChar(_BlaiseGetMem(64));

  DoubleToDigits(V, Digits, NDigits, DecExp, Negative);

  { Clamp to requested significant digits }
  if NDigits > MaxSigDigits then
  begin
    { Round }
    if Digits[MaxSigDigits] >= 53 then
    begin
      I := MaxSigDigits - 1;
      while I >= 0 do
      begin
        Digits[I] := Digits[I] + 1;
        if Digits[I] <= 57 then
          Break;
        Digits[I] := 48;
        if I = 0 then
        begin
          { Overflow: all digits became 0, prepend 1 }
          Digits[0] := 49;
          NDigits := 1;
          DecExp := DecExp + 1;
          I := -1;
          Break;
        end;
        I := I - 1;
      end;
    end;
    NDigits := MaxSigDigits;
    { Strip new trailing zeros }
    while (NDigits > 1) and (Digits[NDigits - 1] = 48) do
      NDigits := NDigits - 1;
  end;

  { Choose fixed or exponential notation (%.g rules):
    use fixed if DecExp-1 >= -4 and DecExp-1 < MaxSigDigits,
    i.e. the exponent would be in [-4, MaxSigDigits). }
  Pos := 0;
  if Negative then
  begin
    Buf[0] := 45;
    Pos := 1;
  end;

  if (DecExp >= 1) and (DecExp <= MaxSigDigits) then
  begin
    { Fixed notation, decimal point within or after digits }
    if DecExp >= NDigits then
    begin
      { All digits before the decimal point, no dot needed }
      I := 0;
      while I < NDigits do
      begin
        Buf[Pos] := Digits[I];
        Pos := Pos + 1;
        I := I + 1;
      end;
      I := NDigits;
      while I < DecExp do
      begin
        Buf[Pos] := 48;
        Pos := Pos + 1;
        I := I + 1;
      end;
    end
    else
    begin
      { Decimal point in the middle }
      I := 0;
      while I < DecExp do
      begin
        Buf[Pos] := Digits[I];
        Pos := Pos + 1;
        I := I + 1;
      end;
      Buf[Pos] := 46;
      Pos := Pos + 1;
      while I < NDigits do
      begin
        Buf[Pos] := Digits[I];
        Pos := Pos + 1;
        I := I + 1;
      end;
    end;
  end
  else if (DecExp <= 0) and (DecExp > -4) then
  begin
    { Fixed notation with leading "0.000..." }
    Buf[Pos] := 48;
    Pos := Pos + 1;
    Buf[Pos] := 46;
    Pos := Pos + 1;
    I := 0;
    while I < -DecExp do
    begin
      Buf[Pos] := 48;
      Pos := Pos + 1;
      I := I + 1;
    end;
    I := 0;
    while I < NDigits do
    begin
      Buf[Pos] := Digits[I];
      Pos := Pos + 1;
      I := I + 1;
    end;
  end
  else
  begin
    { Exponential notation }
    Buf[Pos] := Digits[0];
    Pos := Pos + 1;
    if NDigits > 1 then
    begin
      Buf[Pos] := 46;
      Pos := Pos + 1;
      I := 1;
      while I < NDigits do
      begin
        Buf[Pos] := Digits[I];
        Pos := Pos + 1;
        I := I + 1;
      end;
    end;
    Buf[Pos] := 101;
    Pos := Pos + 1;
    { Exponent value = DecExp - 1 }
    I := DecExp - 1;
    if I < 0 then
    begin
      Buf[Pos] := 45;
      Pos := Pos + 1;
      I := -I;
    end
    else
    begin
      Buf[Pos] := 43;
      Pos := Pos + 1;
    end;
    { Write exponent digits (up to 3) }
    if I >= 100 then
    begin
      Buf[Pos] := (I div 100) + 48;
      Pos := Pos + 1;
      I := I mod 100;
      Buf[Pos] := (I div 10) + 48;
      Pos := Pos + 1;
      Buf[Pos] := (I mod 10) + 48;
      Pos := Pos + 1;
    end
    else if I >= 10 then
    begin
      Buf[Pos] := (I div 10) + 48;
      Pos := Pos + 1;
      Buf[Pos] := (I mod 10) + 48;
      Pos := Pos + 1;
    end
    else
    begin
      Buf[Pos] := I + 48;
      Pos := Pos + 1;
    end;
  end;

  Buf[Pos] := 0;
  Result := BlaiseAllocStr(Buf, Pos);
  _BlaiseFreeMem(Buf);
  _BlaiseFreeMem(Digits);
end;

{ --- printf-style float formatting for Format() (%f / %e / %g) --- }

{ Round the decimal digit buffer Digits[0..NDigits-1] so that only Keep
  significant digits remain, applying round-half-up on the first dropped
  digit.  Adjusts NDigits and DecExp in place.  Keep <= 0 collapses the
  value to zero (NDigits := 1, Digits[0] := '0').  On all-nines carry the
  result becomes a single leading '1' with DecExp incremented. }
procedure RoundDigits(Digits: PChar; var NDigits: Integer;
  var DecExp: Integer; Keep: Integer);
var
  I: Integer;
begin
  if Keep >= NDigits then
    Exit;
  if Keep < 0 then
    Keep := 0;
  if Keep = 0 then
  begin
    { Everything is dropped; the leading dropped digit decides 0 vs 1. }
    if Digits[0] >= 53 then  { '5' }
    begin
      Digits[0] := 49;       { '1' }
      NDigits := 1;
      DecExp := DecExp + 1;
    end
    else
    begin
      Digits[0] := 48;       { '0' }
      NDigits := 1;
    end;
    Exit;
  end;
  if Digits[Keep] >= 53 then  { round half up }
  begin
    I := Keep - 1;
    while I >= 0 do
    begin
      Digits[I] := Digits[I] + 1;
      if Digits[I] <= 57 then  { '9' }
        Break;
      Digits[I] := 48;
      if I = 0 then
      begin
        { Carry past the most-significant digit: 999.. → 1000.. }
        Digits[0] := 49;
        NDigits := 1;
        DecExp := DecExp + 1;
        Exit;
      end;
      I := I - 1;
    end;
  end;
  NDigits := Keep;
end;

{ Write the absolute integer N (>= 0) as decimal digits into Buf at Pos,
  zero-padded to at least MinW characters.  Returns the new Pos. }
function PutPaddedInt(Buf: PChar; Pos, N, MinW: Integer): Integer;
var
  Tmp: array[0..15] of Byte;
  TmpLen, I: Integer;
begin
  TmpLen := 0;
  if N = 0 then
  begin
    Tmp[0] := 48;
    TmpLen := 1;
  end
  else
    while N > 0 do
    begin
      Tmp[TmpLen] := (N mod 10) + 48;
      TmpLen := TmpLen + 1;
      N := N div 10;
    end;
  while TmpLen < MinW do
  begin
    Tmp[TmpLen] := 48;
    TmpLen := TmpLen + 1;
  end;
  I := TmpLen - 1;
  while I >= 0 do
  begin
    Buf[Pos] := Tmp[I];
    Pos := Pos + 1;
    I := I - 1;
  end;
  Result := Pos;
end;

{ Render in fixed notation: Digits/NDigits/DecExp already rounded to Prec
  fraction digits.  Emits sign, integer part, '.', and Prec fraction digits.
  Returns characters written (Buf has room: header callers size it). }
function RenderFixed(Buf: PChar; Pos: Integer; Digits: PChar;
  NDigits, DecExp, Prec: Integer; Negative: Boolean): Integer;
var
  I, FracEmitted, SrcIdx: Integer;
begin
  if Negative then
  begin
    Buf[Pos] := 45;  { '-' }
    Pos := Pos + 1;
  end;
  { Integer part }
  if DecExp <= 0 then
  begin
    Buf[Pos] := 48;  { '0' }
    Pos := Pos + 1;
  end
  else
  begin
    I := 0;
    while I < DecExp do
    begin
      if I < NDigits then
        Buf[Pos] := Digits[I]
      else
        Buf[Pos] := 48;
      Pos := Pos + 1;
      I := I + 1;
    end;
  end;
  if Prec > 0 then
  begin
    Buf[Pos] := 46;  { '.' }
    Pos := Pos + 1;
    FracEmitted := 0;
    { Leading zeros for values < 1 (when DecExp < 0). }
    while (FracEmitted < Prec) and (DecExp + FracEmitted < 0) do
    begin
      Buf[Pos] := 48;
      Pos := Pos + 1;
      FracEmitted := FracEmitted + 1;
    end;
    { Significant fraction digits. }
    if DecExp >= 0 then
      SrcIdx := DecExp
    else
      SrcIdx := 0;
    while FracEmitted < Prec do
    begin
      if SrcIdx < NDigits then
        Buf[Pos] := Digits[SrcIdx]
      else
        Buf[Pos] := 48;
      Pos := Pos + 1;
      SrcIdx := SrcIdx + 1;
      FracEmitted := FracEmitted + 1;
    end;
  end;
  Result := Pos;
end;

{ Renamed from FormatFloatSpec: on Darwin the backend prefixes a Pascal
  routine label with '_' and leaves an already-underscored one alone, so a
  private 'X' beside a public '_X' in the SAME unit collapsed onto one symbol
  (internal assembler: duplicate label _FormatFloatSpec).  The two names must
  differ by more than the leading underscore. }
function FormatFloatSpecCore(V: Double; Spec: Integer; Prec: Integer): Pointer;
var
  Bits: Int64;
  BExp: Integer;
  Frac: Int64;
  Negative: Boolean;
  Digits: PChar;
  Buf: PChar;
  NDigits, DecExp, Pos, I, ExpVal: Integer;
  IsZero: Boolean;
  UpperExp: Boolean;
  ExpChar: Integer;
begin
  Bits := DoubleBits(V);
  BExp := Integer((Bits shr 52) and $7FF);
  Frac := Bits and $000FFFFFFFFFFFFF;
  Negative := (Bits shr 63) <> 0;
  IsZero := (BExp = 0) and (Frac = 0);

  { Special values: inf / nan ignore precision and width. }
  if BExp = DBL_EXP_SPECIAL then
  begin
    if Frac <> 0 then
    begin
      if Negative then
        Result := BlaiseAllocStr(PChar('-nan'), 4)
      else
        Result := BlaiseAllocStr(PChar('nan'), 3);
      Exit;
    end;
    if Negative then
      Result := BlaiseAllocStr(PChar('-inf'), 4)
    else
      Result := BlaiseAllocStr(PChar('inf'), 3);
    Exit;
  end;

  { Generous scratch: 32 raw digits, 64-byte output is enough for any
    double in f/e/g with reasonable precision; clamp precision below. }
  if Prec > 40 then
    Prec := 40;
  Digits := PChar(_BlaiseGetMem(48));
  Buf := PChar(_BlaiseGetMem(96));

  UpperExp := (Spec = 69) or (Spec = 71);  { 'E' or 'G' }
  if UpperExp then
    ExpChar := 69
  else
    ExpChar := 101;

  if IsZero then
  begin
    NDigits := 1;
    Digits[0] := 48;
    DecExp := 1;
  end
  else
    DoubleToDigits(V, Digits, NDigits, DecExp, Negative);

  Pos := 0;

  if (Spec = 102) or (Spec = 70) then          { 'f' / 'F' }
  begin
    if Prec < 0 then Prec := 2;
    if not IsZero then
      RoundDigits(Digits, NDigits, DecExp, DecExp + Prec);
    Pos := RenderFixed(Buf, Pos, Digits, NDigits, DecExp, Prec, Negative);
  end
  else if (Spec = 101) or (Spec = 69) then     { 'e' / 'E' }
  begin
    if Prec < 0 then Prec := 6;
    if not IsZero then
      RoundDigits(Digits, NDigits, DecExp, Prec + 1);
    if Negative then
    begin
      Buf[Pos] := 45;
      Pos := Pos + 1;
    end;
    if NDigits > 0 then
      Buf[Pos] := Digits[0]
    else
      Buf[Pos] := 48;
    Pos := Pos + 1;
    if Prec > 0 then
    begin
      Buf[Pos] := 46;
      Pos := Pos + 1;
      I := 1;
      while I <= Prec do
      begin
        if I < NDigits then
          Buf[Pos] := Digits[I]
        else
          Buf[Pos] := 48;
        Pos := Pos + 1;
        I := I + 1;
      end;
    end;
    Buf[Pos] := ExpChar;
    Pos := Pos + 1;
    if IsZero then
      ExpVal := 0
    else
      ExpVal := DecExp - 1;
    if ExpVal < 0 then
    begin
      Buf[Pos] := 45;
      Pos := Pos + 1;
      ExpVal := -ExpVal;
    end
    else
    begin
      Buf[Pos] := 43;
      Pos := Pos + 1;
    end;
    { Exponent: at least two digits (printf convention). }
    Pos := PutPaddedInt(Buf, Pos, ExpVal, 2);
  end
  else                                          { 'g' / 'G' (default) }
  begin
    if Prec < 0 then Prec := 6;
    if Prec = 0 then Prec := 1;
    if not IsZero then
      RoundDigits(Digits, NDigits, DecExp, Prec);
    { Strip trailing zeros for %g. }
    while (NDigits > 1) and (Digits[NDigits - 1] = 48) do
      NDigits := NDigits - 1;
    { %g picks exponential when DecExp-1 < -4 or DecExp-1 >= Prec. }
    ExpVal := DecExp - 1;
    if (ExpVal < -4) or (ExpVal >= Prec) then
    begin
      { Exponential form, no trailing zeros. }
      if Negative then
      begin
        Buf[Pos] := 45;
        Pos := Pos + 1;
      end;
      Buf[Pos] := Digits[0];
      Pos := Pos + 1;
      if NDigits > 1 then
      begin
        Buf[Pos] := 46;
        Pos := Pos + 1;
        I := 1;
        while I < NDigits do
        begin
          Buf[Pos] := Digits[I];
          Pos := Pos + 1;
          I := I + 1;
        end;
      end;
      Buf[Pos] := ExpChar;
      Pos := Pos + 1;
      if ExpVal < 0 then
      begin
        Buf[Pos] := 45;
        Pos := Pos + 1;
        ExpVal := -ExpVal;
      end
      else
      begin
        Buf[Pos] := 43;
        Pos := Pos + 1;
      end;
      Pos := PutPaddedInt(Buf, Pos, ExpVal, 2);
    end
    else
    begin
      { Fixed form: emit only the significant digits (no padding zeros
        after the point, matching %g). }
      if Negative then
      begin
        Buf[Pos] := 45;
        Pos := Pos + 1;
      end;
      if DecExp <= 0 then
      begin
        Buf[Pos] := 48;
        Pos := Pos + 1;
        Buf[Pos] := 46;
        Pos := Pos + 1;
        I := 0;
        while I < -DecExp do
        begin
          Buf[Pos] := 48;
          Pos := Pos + 1;
          I := I + 1;
        end;
        I := 0;
        while I < NDigits do
        begin
          Buf[Pos] := Digits[I];
          Pos := Pos + 1;
          I := I + 1;
        end;
      end
      else if DecExp >= NDigits then
      begin
        I := 0;
        while I < NDigits do
        begin
          Buf[Pos] := Digits[I];
          Pos := Pos + 1;
          I := I + 1;
        end;
        I := NDigits;
        while I < DecExp do
        begin
          Buf[Pos] := 48;
          Pos := Pos + 1;
          I := I + 1;
        end;
      end
      else
      begin
        I := 0;
        while I < DecExp do
        begin
          Buf[Pos] := Digits[I];
          Pos := Pos + 1;
          I := I + 1;
        end;
        Buf[Pos] := 46;
        Pos := Pos + 1;
        while I < NDigits do
        begin
          Buf[Pos] := Digits[I];
          Pos := Pos + 1;
          I := I + 1;
        end;
      end;
    end;
  end;

  Buf[Pos] := 0;
  Result := BlaiseAllocStr(Buf, Pos);
  _BlaiseFreeMem(Buf);
  _BlaiseFreeMem(Digits);
end;

function _FormatFloatSpec(V: Double; Spec: Integer; Prec: Integer): Pointer;
begin
  Result := FormatFloatSpecCore(V, Spec, Prec);
end;

function _DoubleToStr(V: Double): Pointer;
begin
  Result := FormatFloat(V, 15);
end;

function _SingleToStr(V: Single): Pointer;
var
  D: Double;
begin
  D := V;
  Result := FormatFloat(D, 7);
end;

{ --- String to Double (pure Pascal) --- }

function Pow10Dbl(E: Integer): Double;
var
  R: Double;
  Base: Double;
  N: Integer;
begin
  if E = 0 then
  begin
    Exit(1.0);
  end;
  if E < 0 then
    N := -E
  else
    N := E;
  Base := 10.0;
  R := 1.0;
  while N > 0 do
  begin
    if (N and 1) = 1 then
      R := R * Base;
    Base := Base * Base;
    N := N shr 1;
  end;
  if E < 0 then
    Result := 1.0 / R
  else
    Result := R;
end;

function _StrToDouble(S: Pointer): Double;
var
  P: PChar;
  Neg: Boolean;
  I, C: Integer;
  Mantissa: Int64;
  DigCount: Integer;
  Exp10: Integer;
  SeenDot: Boolean;
  ExpNeg: Boolean;
  ExpVal: Integer;
  Bits: Int64;
begin
  if S = nil then
  begin
    Exit(0.0);
  end;
  P := PChar(S);
  I := 0;
  Neg := False;

  { Skip whitespace }
  while P[I] = 32 do
    I := I + 1;

  { Sign }
  if P[I] = 45 then
  begin
    Neg := True;
    I := I + 1;
  end
  else if P[I] = 43 then
    I := I + 1;

  { Handle special values }
  C := P[I];
  if (C = 105) or (C = 73) then
  begin
    if Neg then
      Bits := Int64($FFF0000000000000)
    else
      Bits := Int64($7FF0000000000000);
    Exit(BitsToDouble(Bits));
  end;
  if (C = 110) or (C = 78) then
  begin
    Bits := Int64($7FF8000000000000);
    Exit(BitsToDouble(Bits));
  end;

  { Parse mantissa digits }
  Mantissa := 0;
  DigCount := 0;
  Exp10 := 0;
  SeenDot := False;

  C := P[I];
  while (C <> 0) and (((C >= 48) and (C <= 57)) or (C = 46)) do
  begin
    if C = 46 then
    begin
      SeenDot := True;
      I := I + 1;
      C := P[I];
    end
    else
    begin
      if DigCount < 19 then
      begin
        Mantissa := Mantissa * 10 + Int64(C - 48);
        if SeenDot then
          Exp10 := Exp10 - 1;
      end
      else
      begin
        if not SeenDot then
          Exp10 := Exp10 + 1;
      end;
      if (Mantissa <> 0) or (C <> 48) then
        DigCount := DigCount + 1;
      I := I + 1;
      C := P[I];
    end;
  end;

  { Parse exponent }
  if (C = 101) or (C = 69) then
  begin
    I := I + 1;
    ExpNeg := False;
    if P[I] = 45 then
    begin
      ExpNeg := True;
      I := I + 1;
    end
    else if P[I] = 43 then
      I := I + 1;
    ExpVal := 0;
    C := P[I];
    while (C >= 48) and (C <= 57) do
    begin
      if ExpVal < 100000 then
        ExpVal := ExpVal * 10 + (C - 48);
      I := I + 1;
      C := P[I];
    end;
    if ExpNeg then
      Exp10 := Exp10 - ExpVal
    else
      Exp10 := Exp10 + ExpVal;
  end;

  { Zero mantissa }
  if Mantissa = 0 then
  begin
    if Neg then
      Result := BitsToDouble(Int64(1) shl 63)
    else
      Result := 0.0;
    Exit;
  end;

  { Convert mantissa to double, then scale by 10^Exp10.
    Split large exponents to avoid intermediate overflow/underflow. }
  Result := Mantissa * 1.0;
  if Exp10 <> 0 then
  begin
    if (Exp10 >= -22) and (Exp10 <= 22) then
      Result := Result * Pow10Dbl(Exp10)
    else if Exp10 > 0 then
    begin
      if Exp10 > 22 then
      begin
        Result := Result * Pow10Dbl(22);
        Exp10 := Exp10 - 22;
      end;
      Result := Result * Pow10Dbl(Exp10);
    end
    else
    begin
      if Exp10 < -22 then
      begin
        Result := Result * Pow10Dbl(-22);
        Exp10 := Exp10 + 22;
      end;
      Result := Result * Pow10Dbl(Exp10);
    end;
  end;
  if Neg then
    Result := -Result;
end;

{ --- Abs for integer types --- }

function _AbsInt(N: Integer): Integer;
begin
  if N < 0 then
    Result := -N
  else
    Result := N;
end;

function _AbsInt64(N: Int64): Int64;
begin
  if N < 0 then
    Result := -N
  else
    Result := N;
end;

end.
