{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Math;

// Blaise RTL — Math unit.
//
// Provides numeric utilities for integer and floating-point types.
//
// Six math routines are compiler builtins, available without this unit,
// because the compiler does what a routine cannot: Abs (one name for every
// numeric type), Sqrt, Trunc, Round, Floor and Ceil (single instructions or
// fixed Int64 results).  Everything else is declared here.
//
// This unit provides:
//   Exp, Expm1, Ln, Log2, Log10, Power
//   Sin, Cos, Tan, ArcSin, ArcCos, ArcTan, ArcTan2, Sinh, Cosh, Tanh
//   IsNaN, IsInfinite
//   Min, Max (Integer / Int64 / Double overloads)
//   Sign (Integer / Int64 / Double overloads)
//   DivMod
//   InRange, EnsureRange (Integer / Double overloads)
//   Frac, DegToRad, RadToDeg (Float32 / Float64 overloads)
//   Random, TRandom (pseudo-random numbers)
//   Pi constant
//
// There is no FMod: the mod operator takes float operands (X mod Y is
// C fmod), and no float-valued Int: use Trunc, or X - Frac(X).

interface

uses
  SysUtils;   { Exception }

const
  Pi: Float64 = 3.14159265358979323846;

{ ------------------------------------------------------------------ }
{ Exponentials and logarithms                                          }
{ ------------------------------------------------------------------ }

{ The Float64 forms bind straight to the pure-Pascal runtime.math kernels
  (no libm is ever linked); the Float32 forms compute in Float64 and
  round once, which is correctly rounded for every function here.  An
  integer argument widens to Float64. }

{ e^X.  Overflows to +Inf, underflows to +0; NaN gives NaN. }
function Exp(X: Float64): Float64; overload; external name '_BlaiseExp';
function Exp(X: Float32): Float32; overload;
{ e^X - 1, accurate for X near zero where Exp(X) - 1 cancels }
function Expm1(X: Float64): Float64; overload; external name '_BlaiseExpm1';
function Expm1(X: Float32): Float32; overload;

{ The logarithms and Power always return Float64. }
{ natural logarithm; Ln(0) = -Inf, a negative X gives NaN }
function Ln(X: Float64): Float64; external name '_BlaiseLn';
function Log2(X: Float64): Float64; external name '_BlaiseLog2';
function Log10(X: Float64): Float64; external name '_BlaiseLog10';
{ Base raised to Exponent }
function Power(Base, Exponent: Float64): Float64; external name '_BlaisePow';

{ ------------------------------------------------------------------ }
{ Trigonometric and hyperbolic functions (angles in radians)           }
{ ------------------------------------------------------------------ }

function Sin(X: Float64): Float64; overload; external name '_BlaiseSin';
function Sin(X: Float32): Float32; overload;
function Cos(X: Float64): Float64; overload; external name '_BlaiseCos';
function Cos(X: Float32): Float32; overload;
function Tan(X: Float64): Float64; overload; external name '_BlaiseTan';
function Tan(X: Float32): Float32; overload;
function ArcSin(X: Float64): Float64; overload; external name '_BlaiseArcSin';
function ArcSin(X: Float32): Float32; overload;
function ArcCos(X: Float64): Float64; overload; external name '_BlaiseArcCos';
function ArcCos(X: Float32): Float32; overload;
function ArcTan(X: Float64): Float64; overload; external name '_BlaiseArcTan';
function ArcTan(X: Float32): Float32; overload;
{ the angle of the point (X, Y), in -Pi..Pi }
function ArcTan2(Y, X: Float64): Float64; overload; external name '_BlaiseArcTan2';
function ArcTan2(Y, X: Float32): Float32; overload;
function Sinh(X: Float64): Float64; overload; external name '_BlaiseSinh';
function Sinh(X: Float32): Float32; overload;
function Cosh(X: Float64): Float64; overload; external name '_BlaiseCosh';
function Cosh(X: Float32): Float32; overload;
function Tanh(X: Float64): Float64; overload; external name '_BlaiseTanh';
function Tanh(X: Float32): Float32; overload;

{ ------------------------------------------------------------------ }
{ Classification                                                       }
{ ------------------------------------------------------------------ }

{ A Float32 argument widens exactly, keeping NaN and infinity. }
function IsNaN(X: Float64): Boolean;
function IsInfinite(X: Float64): Boolean;

{ ------------------------------------------------------------------ }
{ Min / Max                                                            }
{ ------------------------------------------------------------------ }

function Min(A, B: Int32): Int32; overload;
function Max(A, B: Int32): Int32; overload;

function Min(A, B: Int64): Int64; overload;
function Max(A, B: Int64): Int64; overload;

function Min(A, B: Float64): Float64; overload;
function Max(A, B: Float64): Float64; overload;

{ ------------------------------------------------------------------ }
{ Sign                                                                 }
{ ------------------------------------------------------------------ }

{ Returns -1, 0, or 1 depending on the sign of the argument. }
function Sign(X: Int32): Int32; overload;
function Sign(X: Int64): Int32; overload;
function Sign(X: Float64): Int; overload;

{ ------------------------------------------------------------------ }
{ DivMod                                                               }
{ ------------------------------------------------------------------ }

{ Computes quotient and remainder of integer division in one call. }
procedure DivMod(Dividend, Divisor: Int; out Quotient, Remainder: Int);

{ ------------------------------------------------------------------ }
{ InRange                                                              }
{ ------------------------------------------------------------------ }

{ Returns True when Value lies within [Low..High] (both inclusive). }
function InRange(Value, Low, High: Int): Boolean; overload;
function InRange(Value, Low, High: Float64): Boolean; overload;

{ ------------------------------------------------------------------ }
{ EnsureRange                                                          }
{ ------------------------------------------------------------------ }

{ Returns Value clamped to [Low..High] (both inclusive). }
function EnsureRange(Value, Low, High: Int): Int; overload;
function EnsureRange(Value, Low, High: Float64): Float64; overload;

{ ------------------------------------------------------------------ }
{ Frac                                                                 }
{ ------------------------------------------------------------------ }

{ Returns the fractional part of X, with the sign of X:
  Frac(2.75) = 0.75, Frac(-2.75) = -0.75.  X = Trunc(X) + Frac(X) for
  every finite X, and the result is exact.  Frac of an infinity or a NaN
  is NaN.  There is deliberately no float-returning Int(X): Trunc says
  what it does, and the integral part is X - Frac(X). }
function Frac(X: Float64): Float64; overload;
function Frac(X: Float32): Float32; overload;

{ ------------------------------------------------------------------ }
{ DegToRad / RadToDeg                                                  }
{ ------------------------------------------------------------------ }

{ Converts an angle from degrees to radians, and back. }
function DegToRad(Degrees: Float64): Float64; overload;
function DegToRad(Degrees: Float32): Float32; overload;
function RadToDeg(Radians: Float64): Float64; overload;
function RadToDeg(Radians: Float32): Float32; overload;

{ ------------------------------------------------------------------ }
{ Random numbers                                                       }
{ ------------------------------------------------------------------ }

type
  { Raised for an empty range (Next(0), Next(5, 4)), or when the operating
    system cannot supply a seed. }
  ERandomError = class(Exception);

  { A pseudo-random number generator with its own state.

      R := TRandom.Create(LevelSeed);   // the same level every time
      X := R.Next(1, 6);                 // a die roll: 1..6 inclusive

    TRandom.Create(Seed) repeats its sequence exactly: the same seed gives
    the same numbers on every platform and in every Blaise version (the
    algorithm is part of the contract).  TRandom.Create() seeds itself
    from the operating system and records the seed it chose in Seed, so
    a run can be logged and replayed.

    TRandom is a record: copying it snapshots the stream, and the copy
    continues with the same numbers.  It is not thread-safe; give each
    thread its own.  It is NOT cryptographically secure: use SysUtils's
    SecureRandomBytes for keys, tokens and nonces.

    The generator is xoshiro256** (Blackman and Vigna), seeded through
    SplitMix64; Next draws without modulo bias; NextFloat uses the top 53
    bits; Gaussian is Box-Muller, one pair of draws per value. }
  TRandom = record
  private
    FS0, FS1, FS2, FS3: UInt64;
    FSeed: UInt64;
    function Bounded(ABound: UInt64): UInt64;
  public
    { a generator that repeats the same sequence for the same seed }
    static function Create(ASeed: UInt64): TRandom; overload;
    { a generator seeded from the operating system; Seed reports it }
    static function Create(): TRandom; overload;
    { the next 64 random bits }
    function NextUInt64(): UInt64;
    { an integer in 0..N-1; N must be positive }
    function Next(N: Int): Int; overload;
    { an integer in Lo..Hi, both inclusive; Lo must not exceed Hi }
    function Next(Lo, Hi: Int): Int; overload;
    { a Float64 in [0, 1) }
    function NextFloat(): Float64;
    { a normally distributed Float64 }
    function Gaussian(Mean, StdDev: Float64): Float64;
    { the seed this generator started from }
    property Seed: UInt64 read FSeed;
  end;

{ The global generator: auto-seeded from the operating system on first
  use, one per thread, so there is nothing to call first and no shared
  state between threads.  For a repeatable sequence use a TRandom. }

{ a Float64 in [0, 1) }
function Random(): Float64; overload;
{ an integer in 0..N-1; N must be positive }
function Random(N: Int): Int; overload;
{ an integer in Lo..Hi, both inclusive; Lo must not exceed Hi }
function Random(Lo, Hi: Int): Int; overload;

implementation

{ ------------------------------------------------------------------ }
{ Float32 forms of the transcendental functions                        }
{ ------------------------------------------------------------------ }

function Exp(X: Float32): Float32; begin Result := Exp(Float64(X)); end;
function Expm1(X: Float32): Float32; begin Result := Expm1(Float64(X)); end;
function Sin(X: Float32): Float32; begin Result := Sin(Float64(X)); end;
function Cos(X: Float32): Float32; begin Result := Cos(Float64(X)); end;
function Tan(X: Float32): Float32; begin Result := Tan(Float64(X)); end;
function ArcSin(X: Float32): Float32; begin Result := ArcSin(Float64(X)); end;
function ArcCos(X: Float32): Float32; begin Result := ArcCos(Float64(X)); end;
function ArcTan(X: Float32): Float32; begin Result := ArcTan(Float64(X)); end;
function ArcTan2(Y, X: Float32): Float32;
begin
  Result := ArcTan2(Float64(Y), Float64(X));
end;
function Sinh(X: Float32): Float32; begin Result := Sinh(Float64(X)); end;
function Cosh(X: Float32): Float32; begin Result := Cosh(Float64(X)); end;
function Tanh(X: Float32): Float32; begin Result := Tanh(Float64(X)); end;

{ ------------------------------------------------------------------ }
{ Classification                                                       }
{ ------------------------------------------------------------------ }

{ a NaN is the one value unordered with itself }
function IsNaN(X: Float64): Boolean;
begin
  Result := X <> X;
end;

{ X - X is 0 for a finite X and NaN for an infinity or a NaN }
function IsInfinite(X: Float64): Boolean;
begin
  Result := (X = X) and ((X - X) <> (X - X));
end;

{ ------------------------------------------------------------------ }
{ Min / Max                                                            }
{ ------------------------------------------------------------------ }

function Min(A, B: Int32): Int32;
begin
  if A < B then Result := A else Result := B
end;

function Max(A, B: Int32): Int32;
begin
  if A > B then Result := A else Result := B
end;

function Min(A, B: Int64): Int64;
begin
  if A < B then Result := A else Result := B
end;

function Max(A, B: Int64): Int64;
begin
  if A > B then Result := A else Result := B
end;

function Min(A, B: Float64): Float64;
begin
  if A < B then Result := A else Result := B
end;

function Max(A, B: Float64): Float64;
begin
  if A > B then Result := A else Result := B
end;

{ ------------------------------------------------------------------ }
{ Sign                                                                 }
{ ------------------------------------------------------------------ }

function Sign(X: Int32): Int32;
begin
  if X > 0 then Result := 1
  else if X < 0 then Result := -1
  else Result := 0
end;

function Sign(X: Int64): Int32;
begin
  if X > 0 then Result := 1
  else if X < 0 then Result := -1
  else Result := 0
end;

function Sign(X: Float64): Int;
begin
  if X > 0.0 then Result := 1
  else if X < 0.0 then Result := -1
  else Result := 0
end;

{ ------------------------------------------------------------------ }
{ DivMod                                                               }
{ ------------------------------------------------------------------ }

procedure DivMod(Dividend, Divisor: Int; out Quotient, Remainder: Int);
begin
  Quotient := Dividend div Divisor;
  Remainder := Dividend mod Divisor
end;

{ ------------------------------------------------------------------ }
{ InRange                                                              }
{ ------------------------------------------------------------------ }

function InRange(Value, Low, High: Int): Boolean;
begin
  Result := (Value >= Low) and (Value <= High)
end;

function InRange(Value, Low, High: Float64): Boolean;
begin
  Result := (Value >= Low) and (Value <= High)
end;

{ ------------------------------------------------------------------ }
{ EnsureRange                                                          }
{ ------------------------------------------------------------------ }

function EnsureRange(Value, Low, High: Int): Int;
begin
  if Value < Low then Result := Low
  else if Value > High then Result := High
  else Result := Value
end;

function EnsureRange(Value, Low, High: Float64): Float64;
begin
  if Value < Low then Result := Low
  else if Value > High then Result := High
  else Result := Value
end;


{ ------------------------------------------------------------------ }
{ Frac                                                                 }
{ ------------------------------------------------------------------ }

const
  { 2^52: every Float64 of at least this magnitude is an integer }
  TwoPow52 = 4503599627370496.0;

function Frac(X: Float64): Float64;
begin
  { Past 2^52 there is no fraction, and Trunc would overflow Int64 past
    2^63; X - X is 0 for a finite X and NaN for an infinity or a NaN.
    The test is written so that a NaN takes this branch too. }
  if not (Abs(X) < TwoPow52) then
    Exit(X - X);
  { exact: X and its integral part share an exponent range }
  Result := X - Trunc(X);
end;

{ A Float32 widens to Float64 exactly, and its fraction is representable
  in Float32, so narrowing the Float64 result loses nothing. }
function Frac(X: Float32): Float32;
begin
  Result := Frac(Float64(X));
end;

{ ------------------------------------------------------------------ }
{ DegToRad / RadToDeg                                                  }
{ ------------------------------------------------------------------ }

function DegToRad(Degrees: Float64): Float64;
begin
  Result := Degrees * (Pi / 180.0);
end;

function DegToRad(Degrees: Float32): Float32;
begin
  Result := DegToRad(Float64(Degrees));
end;

function RadToDeg(Radians: Float64): Float64;
begin
  Result := Radians * (180.0 / Pi);
end;

function RadToDeg(Radians: Float32): Float32;
begin
  Result := RadToDeg(Float64(Radians));
end;


{ ------------------------------------------------------------------ }
{ TRandom                                                              }
{ ------------------------------------------------------------------ }

function RotL(X: UInt64; K: Int): UInt64;
begin
  Result := (X shl K) or (X shr (64 - K));
end;

{ SplitMix64 (Steele, Lea and Flood): expands one 64-bit seed into the
  four state words, so that close seeds give unrelated streams }
function SplitMix64(var AState: UInt64): UInt64;
var
  Z: UInt64;
begin
  AState := AState + UInt64($9E3779B97F4A7C15);
  Z := AState;
  Z := (Z xor (Z shr 30)) * UInt64($BF58476D1CE4E5B9);
  Z := (Z xor (Z shr 27)) * UInt64($94D049BB133111EB);
  Result := Z xor (Z shr 31);
end;

static function TRandom.Create(ASeed: UInt64): TRandom;
var
  SM: UInt64;
begin
  SM := ASeed;
  Result.FS0 := SplitMix64(SM);
  Result.FS1 := SplitMix64(SM);
  Result.FS2 := SplitMix64(SM);
  Result.FS3 := SplitMix64(SM);
  Result.FSeed := ASeed;
end;

static function TRandom.Create(): TRandom;
var
  S: UInt64;
begin
  if not SecureRandomBytes(@S, SizeOf(S)) then
    raise ERandomError.Create(
      'TRandom.Create: the operating system could not supply a seed');
  Result := TRandom.Create(S);
end;

{ xoshiro256** 1.0 }
function TRandom.NextUInt64(): UInt64;
var
  T: UInt64;
begin
  Result := RotL(FS1 * 5, 7) * 9;
  T := FS1 shl 17;
  FS2 := FS2 xor FS0;
  FS3 := FS3 xor FS1;
  FS1 := FS1 xor FS2;
  FS0 := FS0 xor FS3;
  FS2 := FS2 xor T;
  FS3 := RotL(FS3, 45);
end;

{ A value in 0..ABound-1 with no modulo bias: draws below 2^64 mod ABound
  are rejected, so every residue has the same number of draws behind it
  (the OpenBSD arc4random_uniform method).  ABound > 0. }
function TRandom.Bounded(ABound: UInt64): UInt64;
var
  Threshold, X: UInt64;
begin
  Threshold := (UInt64(0) - ABound) mod ABound;
  repeat
    X := NextUInt64();
  until X >= Threshold;
  Result := X mod ABound;
end;

function TRandom.Next(N: Int): Int;
begin
  if N <= 0 then
    raise ERandomError.Create(
      'TRandom.Next: N must be positive, got ' + IntToStr(N));
  Result := Int(Bounded(UInt64(N)));
end;

function TRandom.Next(Lo, Hi: Int): Int;
var
  Span: UInt64;
begin
  if Lo > Hi then
    raise ERandomError.Create(
      'TRandom.Next: empty range ' + IntToStr(Lo) + '..' + IntToStr(Hi));
  { the span wraps to 0 only for the full Int64 range }
  Span := UInt64(Hi) - UInt64(Lo) + 1;
  if Span = 0 then
    Exit(Int(NextUInt64()));
  Result := Int(UInt64(Lo) + Bounded(Span));
end;

function TRandom.NextFloat(): Float64;
begin
  { the top 53 bits, scaled by 2^-53: every value is a multiple of 2^-53 }
  Result := Float64(Int64(NextUInt64() shr 11)) * (1.0 / 9007199254740992.0);
end;

function TRandom.Gaussian(Mean, StdDev: Float64): Float64;
var
  U1, U2: Float64;
begin
  { U1 in (0, 1], so Ln(U1) is finite }
  U1 := 1.0 - NextFloat();
  U2 := NextFloat();
  Result := Mean + StdDev * Sqrt(-2.0 * Ln(U1)) * Cos(2.0 * Pi * U2);
end;

{ ------------------------------------------------------------------ }
{ The global generator                                                 }
{ ------------------------------------------------------------------ }

threadvar
  GRandom: TRandom;
  GRandomSeeded: Boolean;

procedure EnsureSeeded;
begin
  if not GRandomSeeded then
  begin
    GRandom := TRandom.Create();
    GRandomSeeded := True;
  end;
end;

function Random(): Float64;
begin
  EnsureSeeded();
  Result := GRandom.NextFloat();
end;

function Random(N: Int): Int;
begin
  EnsureSeeded();
  Result := GRandom.Next(N);
end;

function Random(Lo, Hi: Int): Int;
begin
  EnsureSeeded();
  Result := GRandom.Next(Lo, Hi);
end;

end.
