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
// The following are implemented as compiler builtins (in uSemantic.pas +
// the native code generators) and therefore do NOT appear in this unit's
// interface:
//   Abs, Sqrt, Ceil, Floor, Round, Trunc, Ln, Exp, Expm1, Log2, Log10,
//   Power, Sin, Cos, Tan, ArcTan, ArcTan2, IsNaN, IsInfinite.
//
// This unit provides only the functions that are implemented in pure
// Blaise Pascal with no special codegen requirements:
//   Min, Max (Integer / Int64 / Double overloads)
//   Sign (Integer / Int64 / Double overloads)
//   DivMod
//   InRange, EnsureRange (Integer / Double overloads)
//   Frac, DegToRad, RadToDeg (Float32 / Float64 overloads)
//   Pi constant
//
// There is no FMod: the mod operator takes float operands (X mod Y is
// C fmod), and no float-valued Int: use Trunc, or X - Frac(X).

interface

const
  Pi: Float64 = 3.14159265358979323846;

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

implementation

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

end.
