{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ punit tests for runtime.math -- the pure-Pascal libm replacement.

  Reference values were computed with glibc libm (via python3) and are
  embedded as IEEE-754 bit patterns, so the test needs no float parsing
  and no libm at run time.  Each row is (function id, argument A bits,
  argument B bits, expected bits, tolerance in ulps).  glibc results are
  correctly rounded to within 1 ulp, our fdlibm-derived port is accurate
  to about 1 ulp, so a 2 ulp tolerance proves the port is sound while
  never flaking.  Rows with tolerance 0 must match bit-exactly (sqrt,
  floor, ceil, round, fabs and all special values).

  Build (the compiler source-builds and links the RTL -- no blaise_rtl.a):
    blaise --source runtime/src/test/pascal/test_blaise_math.pas \
           --unit-path compiler/src/main/pascal \
           --unit-path runtime/src/test/pascal \
           --output /tmp/test_math
    /tmp/test_math -v
}

program test_blaise_math;

uses
  punit, runtime.math;

const
  VEC_COUNT = 188;
  VecFn: array[0..187] of Integer = (
    1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 3, 3,
    3, 3, 3, 3, 3, 3,
    3, 3, 4, 4, 4, 4,
    4, 4, 4, 4, 5, 5,
    5, 5, 5, 5, 5, 5,
    6, 6, 6, 6, 6, 6,
    6, 7, 7, 7, 7, 7,
    7, 7, 7, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 9, 9, 9, 9,
    9, 9, 9, 9, 10, 10,
    10, 10, 10, 10, 10, 10,
    11, 11, 11, 11, 11, 11,
    11, 11, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    13, 13, 13, 13, 13, 13,
    13, 14, 14, 14, 14, 14,
    14, 14, 15, 15, 15, 15,
    15, 15, 15, 16, 16, 16,
    16, 16, 16, 16, 16, 17,
    17, 17, 17, 17, 17, 17,
    17, 17, 17, 18, 18, 18,
    18, 18, 18, 18, 18, 18,
    19, 19, 19, 19, 19, 19,
    19, 19, 19, 19, 19, 20,
    20, 20, 20, 20, 21, 21,
    21, 21, 21, 21, 21, 8,
    8, 12, 12, 13, 15, 16,
    9, 9);
  VecA: array[0..187] of Int64 = (
    4602678819172646912, 4607182418800017408, -4611010478483282330, 4681608360884174848, 4756540486875873280, 9094988921128908188,
    4609753056924675352, 4158027847206421152, 4636754883540680704, 4613937818241073152, -4618122579557470952, 4612488097114038738,
    4602678819172646912, 4607182418800017408, -4611010478483282330, 4681608360884174848, 4756540486875873280, 9094988921128908188,
    4609753056924675352, 4158027847206421152, 4636754883540680704, 4613937818241073152, 4602678819172646912, 4607182418800017408,
    -4611010478483282330, 4681608360884174848, 4756540486875873280, 9094988921128908188, 4609753056924675352, 4158027847206421152,
    4636754883540680704, 4604480259023595110, 4591870180066957722, -4631501856787818086, 4604480259023595110, -4618891777831180698,
    4607182418800017408, -4616189618054758400, 4607182409792818153, 4457293557087583675, 4591870180066957722, -4631501856787818086,
    4604480259023595110, -4618891777831180698, 4607182418800017408, -4616189618054758400, 4607182409792818153, 0,
    4599075939470750515, 4617315517961601024, 9094988921128908188, -4616189618054758400, 4472406533629990549, -4541763675970600960,
    4606281698874543309, 4607182418800017408, 4607182418800017408, -4616189618054758400, -4616189618054758400, 0,
    4613937818241073152, -4606056518893174784, 118622047889322841, 4607182418800017408, -4616189618054758400, 4547007122018943789,
    4621819117588971520, 4649368480934526976, -4574003555920248832, 4649454530587146734, -4573607731734249472, 4602678819172646912,
    -4623457102168704530, 4612811918334230528, 118622047889322841, 4602678819172646912, 4607182418800017408, 4611686018427387904,
    4621819117588971520, 9094988921128908188, 4613303445314885481, 4607182417899297483, 118622047889322841, 4602678819172646912,
    4607182418800017408, 4611686018427387904, 4621819117588971520, 9094988921128908188, 4652218415073722368, 4613937818241073152,
    118622047889322841, 4602678819172646912, 4607182418800017408, 4611686018427387904, 4621819117588971520, 9094988921128908188,
    4652007308841189376, 4613937818241073152, 4611686018427387904, 4611686018427387904, 4621819117588971520, 4607182419250377371,
    -4611686018427387904, 0, 4611686018427387904, 4609434218613702656, 4606281698874543309, -4613937818241073152,
    4602678819172646912, -4609434218613702656, 4626322717216342016, 4649368480934526976, -4574003555920248832, 4382569440205035030,
    4606281698874543309, 4602678819172646912, -4609434218613702656, 4626322717216342016, 4649368480934526976, -4574003555920248832,
    4382569440205035030, 4606281698874543309, 4602678819172646912, -4609434218613702656, 4626322717216342016, -4592545720011063296,
    4382569440205035030, 4606281698874543309, -4625196817309499392, 4611686018427387904, 4616189618054758400, 2024,
    4598175219545276416, 4621256167635550208, 9094988921128908188, 118622047889322841, 4613937818241073152, 4602678819172646912,
    -4620693217682128896, 4612811918334230528, -4610560118520545280, 4613937818241073152, -4609434218613702656, 4861130398305394688,
    -4362241638549381120, 4602678819172646911, -9223372036854775808, 4602678819172646912, -4620693217682128896, 4612811918334230528,
    -4610560118520545280, 4613937818241073152, -4609434218613702656, 4861130398305394688, -4362241638549381120, 4602678819172646911,
    4602678819172646912, -4620693217682128896, 4612811918334230528, -4610560118520545280, 4613937818241073152, 4602678819172646911,
    -4620693217682128897, 4861130398305394688, 4616752568008179712, -4606619468846596096, 4612586738352862003, 4602678819172646912,
    -4620693217682128896, -9223372036854775808, 9094988921128908188, -9223372036854773784, 4602678819172646912, -4620693217682128896,
    4457293557087583675, -4594234569871327232, 4629137466983448576, 4649368480934526976, 4607182418800017408, 4650248090236747776,
    -4573123946618028032, 4607182418800017408, 9218868437227405312, 4650248090236747776, 4630826316843712512, -4616189618054758400,
    0, -4616189618054758400);
  VecB: array[0..187] of Int64 = (
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 4607182418800017408, -4616189618054758400, 4607182418800017408, -4616189618054758400, -4616189618054758400,
    4616189618054758400, 0, 9094988921128908188, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 4621819117588971520, 4602678819172646912, -4609434218613702656, 4711630319722168320,
    4613937818241073152, 0, -4570933719455498240, 4649368480934526976, 4666723172467343360, -4609434218613702656,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 9221120237041090560, 0, 0, 0, 0,
    0, 0);
  VecE: array[0..187] of Int64 = (
    4602308182625945072, 4605754516372524270, -4618480101878124764, 4585312765779017366, -4620918289125169949, -4617829991960222843,
    4607182418800017408, 4158027847206421152, -4624705333060844708, 4594252404416238939, -4618827765636973620, 4604544271217802189,
    4606079780542709072, 4603041830072026764, -4619195536427175967, -4616195375389524569, 4606039581959951130, -4620014199950687039,
    4364452196894661639, 4607182418800017408, 4606829231486709996, -4616279757631920686, 4603095874924660554, 4609692760021066662,
    4607719309312508727, -4638055975884738243, -4620167650867921072, 4609080455566175351, 4849535219099880885, 4158027847206421152,
    -4624501473825861233, 4605761878818060462, 4591882244033050756, -4631489792821725052, 4605159379298876821, -4618212657555898987,
    4609753056924675352, -4613618979930100456, 4609746687872471981, 4457293557087583675, 4609301942964057488, 4610204170885293217,
    4605339535295732891, 4612465577614431729, 0, 4614256656552045848, 4564164732355194646, 4609753056924675352,
    4598922038761926406, 4608864066354890839, 4609753056924675352, -4618122579557470952, 4472406533629990549, -4613619024966096728,
    4604775831183950782, 4605249457297304856, 4612488097114038738, -4618122579557470952, -4610883939740737070, 4614256656552045848,
    4603971362252824289, -4613618979930100456, 0, 4613303445314885481, 4600298746774613816, 4607182869182498894,
    4671783802770883936, 9155136748776909966, 58915316498509951, 9218868437227404074, 1, 4610103999673009820,
    4604544271217802189, 4623047752462491835, -4574084695234936907, -4618953502541334033, 0, 4604418534313441775,
    4612367379483415830, 4649287341619838901, 4607182418800017408, -4721223821992617057, -4571394824475079799, -4616189618054758400,
    0, 4607182418800017408, 4614662735865160561, 4651977212379696009, 4621819117588971520, 4609816855700290920,
    -4579386764849840128, -4624277542631671297, 0, 4599094494223104511, 4607182418800017408, 4643985272004935680,
    4613937818241073152, 4602266672337769981, 4652218415073722368, 4609047870845172685, 4562254508917369340, 4613303445012408050,
    -4602678819172646912, 4607182418800017408, 1, 6450905282920839172, 0, -4624362817378504856,
    4602868828792568727, -4601542856576251474, 4732415730390722564, 9150633149149539470, -72738887705236338, 4382569440205035030,
    4607301839516035832, 4607757195049363664, 4621857207906343006, 4732415730390722564, 9150633149149539470, 9150633149149539470,
    4607182418800017408, 4609132866484143744, 4601996382546856691, -4616234160873665792, 4607182418800017408, -4616189618054758400,
    4382569440205035030, 4604627057187905629, -4625379891790340986, 4609047870845172685, 4611686018427387904, 2213095440444558963,
    4602678819172646912, 4613937818241073152, 6850974717710472879, 2362753625475748981, 4610479282544200874, 0,
    -4616189618054758400, 4611686018427387904, -4609434218613702656, 4613937818241073152, -4609434218613702656, 4861130398305394688,
    -4362241638549381120, 0, 0, 4607182418800017408, 0, 4613937818241073152,
    -4611686018427387904, 4613937818241073152, -4609434218613702656, 4861130398305394688, -4362241638549381120, 4607182418800017408,
    4607182418800017408, -4616189618054758400, 4613937818241073152, -4609434218613702656, 4613937818241073152, 0,
    0, 4861130398305394688, 4617315517961601024, -4606056518893174784, 4611686018427387904, 4602678819172646912,
    4602678819172646912, 0, 9094988921128908188, 2024, 4604018381291261240, -4622612303439670292,
    4457293557087970531, -4616189618054759243, 4801805078135318253, 9155136748776909966, 4610417272575012562, 9218868437227405312,
    0, 4607182418800017408, 4607182418800017408, 9218868437227405312, 4607182418800017408, 9221120237041090560,
    -4503599627370496, 9221120237041090560);
  VecTol: array[0..187] of Integer = (
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2,
    2, 2, 2, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 2, 2,
    2, 2, 2, 2, 2, 0,
    0, 0, 0, 0, 0, 0,
    0, 0);

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

function IsNaNBits(B: Int64): Boolean;
begin
  Result := ((B and $7FF0000000000000) = $7FF0000000000000) and
            ((B and $000FFFFFFFFFFFFF) <> 0);
end;

{ Map a double bit pattern onto a monotonically ordered signed scale so
  the ulp distance between two doubles is a plain integer subtraction.
  Negative doubles (sign bit set) map below positives; -0 and +0 map to
  adjacent values, which is what an ulp comparison wants. }
function OrderedBits(B: Int64): Int64;
begin
  if B < 0 then
    Result := Int64($8000000000000000) - B
  else
    Result := B;
end;

function UlpDiff(A, B: Int64): Int64;
var
  OA, OB: Int64;
begin
  if A = B then Exit(0);
  if IsNaNBits(A) and IsNaNBits(B) then Exit(0);
  if IsNaNBits(A) or IsNaNBits(B) then Exit($7FFFFFFFFFFFFFFF);
  OA := OrderedBits(A);
  OB := OrderedBits(B);
  if OA > OB then
    Result := OA - OB
  else
    Result := OB - OA;
end;

function EvalVector(FnCode: Integer; A, B: Double): Double;
begin
  case FnCode of
    1: Result := _BlaiseSin(A);
    2: Result := _BlaiseCos(A);
    3: Result := _BlaiseTan(A);
    4: Result := _BlaiseArcSin(A);
    5: Result := _BlaiseArcCos(A);
    6: Result := _BlaiseArcTan(A);
    7: Result := _BlaiseArcTan2(A, B);
    8: Result := _BlaiseExp(A);
    9: Result := _BlaiseLn(A);
    10: Result := _BlaiseLog2(A);
    11: Result := _BlaiseLog10(A);
    12: Result := _BlaisePow(A, B);
    13: Result := _BlaiseSinh(A);
    14: Result := _BlaiseCosh(A);
    15: Result := _BlaiseTanh(A);
    16: Result := _BlaiseSqrtD(A);
    17: Result := _BlaiseFloorD(A);
    18: Result := _BlaiseCeilD(A);
    19: Result := _BlaiseRoundD(A);
    20: Result := _BlaiseFabs(A);
    21: Result := _BlaiseExpm1(A);
  else
    Result := 0.0;
  end;
end;

{ Run every vector row whose function id is AFnCode; returns '' on pass. }
function RunVectors(AFnCode: Integer; const AName: string): string;
var
  I: Integer;
  R: Double;
  RB, D: Int64;
  Fails: Integer;
begin
  Fails := 0;
  for I := 0 to VEC_COUNT - 1 do
  begin
    if VecFn[I] <> AFnCode then Continue;
    R := EvalVector(AFnCode, BitsToDouble(VecA[I]), BitsToDouble(VecB[I]));
    RB := DoubleBits(R);
    D := UlpDiff(RB, VecE[I]);
    if D > VecTol[I] then
    begin
      Fails := Fails + 1;
      WriteLn('  ', AName, ' vector ', IntToStr(I), ': arg bits ',
        IntToStr(VecA[I]), ' got bits ', IntToStr(RB), ' want bits ',
        IntToStr(VecE[I]), ' (ulp diff ', IntToStr(D), ', tol ',
        IntToStr(VecTol[I]), ')');
    end;
  end;
  AssertEquals(AName + ': all vectors within tolerance', 0, Fails);
  Result := '';
end;

function Test_Sin: string;
begin
  Result := RunVectors(1, 'Sin');
end;

function Test_Cos: string;
begin
  Result := RunVectors(2, 'Cos');
end;

function Test_Tan: string;
begin
  Result := RunVectors(3, 'Tan');
end;

function Test_ArcSin: string;
begin
  Result := RunVectors(4, 'ArcSin');
end;

function Test_ArcCos: string;
begin
  Result := RunVectors(5, 'ArcCos');
end;

function Test_ArcTan: string;
begin
  Result := RunVectors(6, 'ArcTan');
end;

function Test_ArcTan2: string;
begin
  Result := RunVectors(7, 'ArcTan2');
end;

function Test_Exp: string;
begin
  Result := RunVectors(8, 'Exp');
end;

function Test_Ln: string;
begin
  Result := RunVectors(9, 'Ln');
end;

function Test_Log2: string;
begin
  Result := RunVectors(10, 'Log2');
end;

function Test_Log10: string;
begin
  Result := RunVectors(11, 'Log10');
end;

function Test_Pow: string;
begin
  Result := RunVectors(12, 'Pow');
end;

function Test_Sinh: string;
begin
  Result := RunVectors(13, 'Sinh');
end;

function Test_Cosh: string;
begin
  Result := RunVectors(14, 'Cosh');
end;

function Test_Tanh: string;
begin
  Result := RunVectors(15, 'Tanh');
end;

function Test_SqrtD: string;
begin
  Result := RunVectors(16, 'SqrtD');
end;

function Test_FloorD: string;
begin
  Result := RunVectors(17, 'FloorD');
end;

function Test_CeilD: string;
begin
  Result := RunVectors(18, 'CeilD');
end;

function Test_RoundD: string;
begin
  Result := RunVectors(19, 'RoundD');
end;

function Test_Fabs: string;
begin
  Result := RunVectors(20, 'Fabs');
end;

function Test_Expm1: string;
begin
  Result := RunVectors(21, 'Expm1');
end;

{ Sign-preservation and exact-identity checks that bit-table rows cannot
  express readably. }
function Test_SignedZero: string;
begin
  AssertEquals('fabs(-0) is +0', 0, DoubleBits(_BlaiseFabs(BitsToDouble(Int64($8000000000000000)))));
  AssertEquals('round(-0) keeps -0', Int64($8000000000000000), DoubleBits(_BlaiseRoundD(BitsToDouble(Int64($8000000000000000)))));
  AssertEquals('sin(-0) keeps -0', Int64($8000000000000000), DoubleBits(_BlaiseSin(BitsToDouble(Int64($8000000000000000)))));
  AssertEquals('sqrt(-0) keeps -0', Int64($8000000000000000), DoubleBits(_BlaiseSqrtD(BitsToDouble(Int64($8000000000000000)))));
  Result := '';
end;

function Test_PowExact: string;
begin
  AssertEquals('pow(2,10) = 1024 exactly', DoubleBits(1024.0), DoubleBits(_BlaisePow(2.0, 10.0)));
  AssertEquals('pow(-2,3) = -8 exactly', DoubleBits(-8.0), DoubleBits(_BlaisePow(-2.0, 3.0)));
  AssertEquals('pow(x,0) = 1', DoubleBits(1.0), DoubleBits(_BlaisePow(123.456, 0.0)));
  AssertEquals('pow(0,0) = 1', DoubleBits(1.0), DoubleBits(_BlaisePow(0.0, 0.0)));
  Result := '';
end;

function Test_SqrtExact: string;
var
  I: Integer;
  V: Double;
begin
  { sqrt of perfect squares must be exact }
  for I := 1 to 100 do
  begin
    V := I;
    AssertEquals('sqrt(I*I) = I', DoubleBits(V), DoubleBits(_BlaiseSqrtD(V * V)));
  end;
  Result := '';
end;

begin
  AddSuite('blaise_math', nil);
  AddTest('Sin_Vectors', @Test_Sin, 'blaise_math');
  AddTest('Cos_Vectors', @Test_Cos, 'blaise_math');
  AddTest('Tan_Vectors', @Test_Tan, 'blaise_math');
  AddTest('ArcSin_Vectors', @Test_ArcSin, 'blaise_math');
  AddTest('ArcCos_Vectors', @Test_ArcCos, 'blaise_math');
  AddTest('ArcTan_Vectors', @Test_ArcTan, 'blaise_math');
  AddTest('ArcTan2_Vectors', @Test_ArcTan2, 'blaise_math');
  AddTest('Exp_Vectors', @Test_Exp, 'blaise_math');
  AddTest('Ln_Vectors', @Test_Ln, 'blaise_math');
  AddTest('Log2_Vectors', @Test_Log2, 'blaise_math');
  AddTest('Log10_Vectors', @Test_Log10, 'blaise_math');
  AddTest('Pow_Vectors', @Test_Pow, 'blaise_math');
  AddTest('Sinh_Vectors', @Test_Sinh, 'blaise_math');
  AddTest('Cosh_Vectors', @Test_Cosh, 'blaise_math');
  AddTest('Tanh_Vectors', @Test_Tanh, 'blaise_math');
  AddTest('SqrtD_Vectors', @Test_SqrtD, 'blaise_math');
  AddTest('FloorD_Vectors', @Test_FloorD, 'blaise_math');
  AddTest('CeilD_Vectors', @Test_CeilD, 'blaise_math');
  AddTest('RoundD_Vectors', @Test_RoundD, 'blaise_math');
  AddTest('Fabs_Vectors', @Test_Fabs, 'blaise_math');
  AddTest('Expm1_Vectors', @Test_Expm1, 'blaise_math');
  AddTest('SignedZero', @Test_SignedZero, 'blaise_math');
  AddTest('PowExact', @Test_PowExact, 'blaise_math');
  AddTest('SqrtExact', @Test_SqrtExact, 'blaise_math');
  RunAllSysTests();
end.
