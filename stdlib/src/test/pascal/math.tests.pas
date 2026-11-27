{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Math.Tests;

{ Random and TRandom.  The golden values pin the seed -> sequence
  contract: a seed gives the same numbers on every platform and in every
  future Blaise version, so a saved seed (a game level, a test fixture)
  can always be replayed.  They were computed with an independent Python
  implementation of SplitMix64 seeding + xoshiro256**, the unbiased
  bounded draw and the 53-bit float.  If one of them changes, the
  generator broke its contract -- do not just update the number. }

interface

uses
  blaise.testing, Math;

type
  TMathRandomTests = class(TTestCase)
  published
    { the seed -> sequence contract }
    procedure TestSeeded_GoldenUInt64;
    procedure TestSeeded_GoldenUInt64_SeedZero;
    procedure TestSeeded_GoldenNext;
    procedure TestSeeded_GoldenNextRange;
    procedure TestSeeded_GoldenNextFloat;
    procedure TestSeeded_GoldenFullInt64Range;
    procedure TestSameSeed_SameSequence;
    procedure TestCopy_SnapshotsTheStream;
    { an unseeded generator draws its seed from the OS and reports it, so
      the run can be replayed }
    procedure TestUnseeded_SeedReplaysTheSequence;
    procedure TestUnseeded_SeedsDiffer;
    { bounds }
    procedure TestNext_StaysBelowN;
    procedure TestNext_OneIsAlwaysZero;
    procedure TestNext_HitsEveryValue;
    procedure TestNext_LargestN;
    procedure TestNextRange_IsInclusive;
    procedure TestNextRange_SingleValue;
    procedure TestNextFloat_HalfOpen;
    procedure TestNext_NonPositive_Raises;
    procedure TestNextRange_Reversed_Raises;
    { Gaussian: deterministic for a seed, with the requested mean and
      standard deviation }
    procedure TestGaussian_SameSeedSameValues;
    procedure TestGaussian_MeanAndStdDev;
    { the global, auto-seeded functions }
    procedure TestRandom_Float;
    procedure TestRandom_N;
    procedure TestRandom_Range;
    procedure TestRandom_NotConstant;
  end;

implementation

procedure TMathRandomTests.TestSeeded_GoldenUInt64;
var
  R: TRandom;
begin
  R := TRandom.Create(42);
  AssertTrue('1st', R.NextUInt64() = UInt64($15780B2E0C2EC716));
  AssertTrue('2nd', R.NextUInt64() = UInt64($6104D9866D113A7E));
  AssertTrue('3rd', R.NextUInt64() = UInt64($AE17533239E499A1));
  AssertTrue('4th', R.NextUInt64() = UInt64($ECB8AD4703B360A1));
end;

procedure TMathRandomTests.TestSeeded_GoldenUInt64_SeedZero;
var
  R: TRandom;
begin
  R := TRandom.Create(0);
  AssertTrue('1st', R.NextUInt64() = UInt64($99EC5F36CB75F2B4));
  AssertTrue('2nd', R.NextUInt64() = UInt64($BF6E1F784956452A));
end;

procedure TMathRandomTests.TestSeeded_GoldenNext;
var
  R: TRandom;
begin
  R := TRandom.Create(12345);
  AssertEquals('1', 83, R.Next(100));
  AssertEquals('2', 98, R.Next(100));
  AssertEquals('3', 56, R.Next(100));
  AssertEquals('4', 95, R.Next(100));
  AssertEquals('5', 44, R.Next(100));
  AssertEquals('6', 96, R.Next(100));
  AssertEquals('7', 9, R.Next(100));
  AssertEquals('8', 10, R.Next(100));
end;

procedure TMathRandomTests.TestSeeded_GoldenNextRange;
var
  R: TRandom;
begin
  R := TRandom.Create(12345);
  AssertEquals('1', -2, R.Next(-5, 5));
  AssertEquals('2', 3, R.Next(-5, 5));
  AssertEquals('3', -5, R.Next(-5, 5));
  AssertEquals('4', -3, R.Next(-5, 5));
  AssertEquals('5', 0, R.Next(-5, 5));
  AssertEquals('6', 3, R.Next(-5, 5));
  AssertEquals('7', 1, R.Next(-5, 5));
  AssertEquals('8', 0, R.Next(-5, 5));
end;

procedure TMathRandomTests.TestSeeded_GoldenNextFloat;
var
  R: TRandom;
begin
  R := TRandom.Create(7);
  { exact: each literal round-trips to the generated Float64 }
  AssertTrue('1', R.NextFloat() = 0.7005764821796896);
  AssertTrue('2', R.NextFloat() = 0.2787512294737843);
  AssertTrue('3', R.NextFloat() = 0.8396274618764198);
end;

procedure TMathRandomTests.TestSeeded_GoldenFullInt64Range;
var
  R: TRandom;
begin
  R := TRandom.Create(2026);
  AssertEquals('1', Int64(-7863265874657366507), R.Next(Low(Int64), High(Int64)));
  AssertEquals('2', Int64(5232962402658359512), R.Next(Low(Int64), High(Int64)));
end;

procedure TMathRandomTests.TestSameSeed_SameSequence;
var
  A, B: TRandom;
  I: Int;
begin
  A := TRandom.Create(987654321);
  B := TRandom.Create(987654321);
  for I := 0 to 999 do
    AssertEquals('draw ' + IntToStr(I), A.Next(1000000), B.Next(1000000));
end;

procedure TMathRandomTests.TestCopy_SnapshotsTheStream;
var
  A, B: TRandom;
  I: Int;
begin
  A := TRandom.Create(5);
  A.Next(10);
  B := A;
  for I := 0 to 99 do
    AssertEquals('copy continues identically', A.Next(1000), B.Next(1000));
end;

procedure TMathRandomTests.TestUnseeded_SeedReplaysTheSequence;
var
  A, B: TRandom;
  I: Int;
begin
  A := TRandom.Create();
  B := TRandom.Create(A.Seed);
  AssertTrue('the recorded seed', A.Seed = B.Seed);
  for I := 0 to 99 do
    AssertEquals('replayed draw', A.Next(1000000), B.Next(1000000));
end;

procedure TMathRandomTests.TestUnseeded_SeedsDiffer;
var
  A, B: TRandom;
begin
  A := TRandom.Create();
  B := TRandom.Create();
  { two 64-bit seeds from the OS collide with probability 2^-64 }
  AssertTrue('different seeds', A.Seed <> B.Seed);
end;

procedure TMathRandomTests.TestNext_StaysBelowN;
var
  R: TRandom;
  I, V: Int;
begin
  R := TRandom.Create(1);
  for I := 0 to 9999 do
  begin
    V := R.Next(7);
    AssertTrue('in 0..6', (V >= 0) and (V <= 6));
  end;
end;

procedure TMathRandomTests.TestNext_OneIsAlwaysZero;
var
  R: TRandom;
  I: Int;
begin
  R := TRandom.Create(1);
  for I := 0 to 99 do
    AssertEquals('Next(1)', 0, R.Next(1));
end;

procedure TMathRandomTests.TestNext_HitsEveryValue;
var
  R: TRandom;
  Seen: array[0..5] of Boolean;
  I: Int;
begin
  R := TRandom.Create(3);
  for I := 0 to 5 do
    Seen[I] := False;
  for I := 0 to 599 do
    Seen[R.Next(6)] := True;
  for I := 0 to 5 do
    AssertTrue('face ' + IntToStr(I + 1), Seen[I]);
end;

procedure TMathRandomTests.TestNext_LargestN;
var
  R: TRandom;
  I, V: Int;
begin
  R := TRandom.Create(9);
  for I := 0 to 99 do
  begin
    V := R.Next(High(Int64));
    AssertTrue('in 0..High-1', (V >= 0) and (V < High(Int64)));
  end;
end;

procedure TMathRandomTests.TestNextRange_IsInclusive;
var
  R: TRandom;
  I, V: Int;
  SawLo, SawHi: Boolean;
begin
  R := TRandom.Create(11);
  SawLo := False;
  SawHi := False;
  for I := 0 to 999 do
  begin
    V := R.Next(1, 6);
    AssertTrue('in 1..6', (V >= 1) and (V <= 6));
    if V = 1 then SawLo := True;
    if V = 6 then SawHi := True;
  end;
  AssertTrue('reaches Lo', SawLo);
  AssertTrue('reaches Hi', SawHi);
end;

procedure TMathRandomTests.TestNextRange_SingleValue;
var
  R: TRandom;
begin
  R := TRandom.Create(1);
  AssertEquals('Next(4, 4)', 4, R.Next(4, 4));
end;

procedure TMathRandomTests.TestNextFloat_HalfOpen;
var
  R: TRandom;
  I: Int;
  F: Float64;
begin
  R := TRandom.Create(13);
  for I := 0 to 9999 do
  begin
    F := R.NextFloat();
    AssertTrue('in [0, 1)', (F >= 0.0) and (F < 1.0));
  end;
end;

procedure TMathRandomTests.TestNext_NonPositive_Raises;
var
  R: TRandom;
begin
  R := TRandom.Create(1);
  AssertRaises('Next(0)', 'ERandomError',
    procedure begin R.Next(0); end);
  AssertRaises('Next(-3)', 'ERandomError',
    procedure begin R.Next(-3); end);
  AssertRaises('Random(0)', 'ERandomError',
    procedure begin Random(0); end);
end;

procedure TMathRandomTests.TestNextRange_Reversed_Raises;
var
  R: TRandom;
begin
  R := TRandom.Create(1);
  AssertRaises('Next(5, 4)', 'ERandomError',
    procedure begin R.Next(5, 4); end);
  AssertRaises('Random(5, 4)', 'ERandomError',
    procedure begin Random(5, 4); end);
end;

procedure TMathRandomTests.TestGaussian_SameSeedSameValues;
var
  A, B: TRandom;
  I: Int;
begin
  A := TRandom.Create(77);
  B := TRandom.Create(77);
  for I := 0 to 99 do
    AssertTrue('same Gaussian draw', A.Gaussian(10.0, 2.0) = B.Gaussian(10.0, 2.0));
end;

procedure TMathRandomTests.TestGaussian_MeanAndStdDev;
const
  N = 20000;
var
  R: TRandom;
  I: Int;
  V, Sum, SumSq, Mean, Sd: Float64;
begin
  R := TRandom.Create(31337);
  Sum := 0.0;
  SumSq := 0.0;
  for I := 0 to N - 1 do
  begin
    V := R.Gaussian(10.0, 2.0);
    Sum := Sum + V;
    SumSq := SumSq + V * V;
  end;
  Mean := Sum / N;
  Sd := Sqrt(SumSq / N - Mean * Mean);
  { the standard error of the mean is 2 / Sqrt(20000) ~ 0.014 }
  AssertEquals('mean', 10.0, Mean, 0.06);
  AssertEquals('standard deviation', 2.0, Sd, 0.06);
end;

procedure TMathRandomTests.TestRandom_Float;
var
  I: Int;
  F: Float64;
begin
  for I := 0 to 999 do
  begin
    F := Random();
    AssertTrue('in [0, 1)', (F >= 0.0) and (F < 1.0));
  end;
end;

procedure TMathRandomTests.TestRandom_N;
var
  I, V: Int;
begin
  for I := 0 to 999 do
  begin
    V := Random(10);
    AssertTrue('in 0..9', (V >= 0) and (V <= 9));
  end;
end;

procedure TMathRandomTests.TestRandom_Range;
var
  I, V: Int;
begin
  for I := 0 to 999 do
  begin
    V := Random(-3, 3);
    AssertTrue('in -3..3', (V >= -3) and (V <= 3));
  end;
end;

procedure TMathRandomTests.TestRandom_NotConstant;
var
  I, First: Int;
  Varied: Boolean;
begin
  First := Random(1000000);
  Varied := False;
  for I := 0 to 99 do
    if Random(1000000) <> First then
      Varied := True;
  AssertTrue('the global generator varies', Varied);
end;

initialization
  RegisterTest(TMathRandomTests);

end.
