{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ punit tests for _StrToDouble -- decimal-to-binary conversion must be
  CORRECTLY ROUNDED (round-to-nearest-even), bit-exact against reference
  values computed with CPython's David-Gay-derived parser.

  This is not cosmetic: the internal assembler converts every float
  literal in every Blaise program through _StrToDouble (.double text in
  the emitted assembly), so a 1-ulp parsing error miscompiles user
  constants -- and a >19-significant-digit literal used to come out
  NEGATIVE (Int64 mantissa overflow).

  Build:
    blaise --source runtime/src/test/pascal/test_blaise_strtod.pas \
           --unit-path compiler/src/main/pascal \
           --unit-path runtime/src/test/pascal \
           --output /tmp/test_strtod
}

program test_blaise_strtod;

uses
  punit;

function _StrToDouble(S: Pointer): Double; external name '_StrToDouble';

function DB(V: Double): Int64;
var
  P: ^Int64;
begin
  P := Pointer(@V);
  Result := P^;
end;

function Test_Vectors: string;
var
  Fails: Integer;
  R: Double;
begin
  Fails := 0;
  R := _StrToDouble(PChar('9.61796693925975554329e-01'));
  if DB(R) <> Int64(4606838314010018813) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 0 FAIL: got ', IntToStr(DB(R)), ' want 4606838314010018813');
  end;
  R := _StrToDouble(PChar('9.61796700954437255859e-01'));
  if DB(R) <> Int64(4606838314073325568) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 1 FAIL: got ', IntToStr(DB(R)), ' want 4606838314073325568');
  end;
  R := _StrToDouble(PChar('-7.02846165095275826516e-09'));
  if DB(R) <> -4738297118486494731 then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 2 FAIL: got ', IntToStr(DB(R)), ' want -4738297118486494731');
  end;
  R := _StrToDouble(PChar('1.35003920212974897128e-08'));
  if DB(R) <> Int64(4489242115478376454) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 3 FAIL: got ', IntToStr(DB(R)), ' want 4489242115478376454');
  end;
  R := _StrToDouble(PChar('8.0085662595372944372e-017'));
  if DB(R) <> Int64(4365981760143196926) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 4 FAIL: got ', IntToStr(DB(R)), ' want 4365981760143196926');
  end;
  R := _StrToDouble(PChar('0.1'));
  if DB(R) <> Int64(4591870180066957722) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 5 FAIL: got ', IntToStr(DB(R)), ' want 4591870180066957722');
  end;
  R := _StrToDouble(PChar('0.25'));
  if DB(R) <> Int64(4598175219545276416) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 6 FAIL: got ', IntToStr(DB(R)), ' want 4598175219545276416');
  end;
  R := _StrToDouble(PChar('3.141592653589793'));
  if DB(R) <> Int64(4614256656552045848) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 7 FAIL: got ', IntToStr(DB(R)), ' want 4614256656552045848');
  end;
  R := _StrToDouble(PChar('2.718281828459045'));
  if DB(R) <> Int64(4613303445314885481) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 8 FAIL: got ', IntToStr(DB(R)), ' want 4613303445314885481');
  end;
  R := _StrToDouble(PChar('2.2250738585072011e-308'));
  if DB(R) <> Int64(4503599627370495) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 9 FAIL: got ', IntToStr(DB(R)), ' want 4503599627370495');
  end;
  R := _StrToDouble(PChar('2.2250738585072014e-308'));
  if DB(R) <> Int64(4503599627370496) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 10 FAIL: got ', IntToStr(DB(R)), ' want 4503599627370496');
  end;
  R := _StrToDouble(PChar('5e-324'));
  if DB(R) <> 1 then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 11 FAIL: got ', IntToStr(DB(R)), ' want 1');
  end;
  R := _StrToDouble(PChar('4.9406564584124654e-324'));
  if DB(R) <> 1 then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 12 FAIL: got ', IntToStr(DB(R)), ' want 1');
  end;
  R := _StrToDouble(PChar('2.4703282292062327e-324'));
  if DB(R) <> 0 then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 13 FAIL: got ', IntToStr(DB(R)), ' want 0');
  end;
  R := _StrToDouble(PChar('1.7976931348623157e308'));
  if DB(R) <> Int64(9218868437227405311) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 14 FAIL: got ', IntToStr(DB(R)), ' want 9218868437227405311');
  end;
  R := _StrToDouble(PChar('1.7976931348623159e308'));
  if DB(R) <> Int64(9218868437227405312) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 15 FAIL: got ', IntToStr(DB(R)), ' want 9218868437227405312');
  end;
  R := _StrToDouble(PChar('1e309'));
  if DB(R) <> Int64(9218868437227405312) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 16 FAIL: got ', IntToStr(DB(R)), ' want 9218868437227405312');
  end;
  R := _StrToDouble(PChar('-1e309'));
  if DB(R) <> -4503599627370496 then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 17 FAIL: got ', IntToStr(DB(R)), ' want -4503599627370496');
  end;
  R := _StrToDouble(PChar('0.000000000000000000000000000001'));
  if DB(R) <> Int64(4158027847206421152) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 18 FAIL: got ', IntToStr(DB(R)), ' want 4158027847206421152');
  end;
  R := _StrToDouble(PChar('123456789012345678901234567890'));
  if DB(R) <> Int64(5042042089369253694) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 19 FAIL: got ', IntToStr(DB(R)), ' want 5042042089369253694');
  end;
  R := _StrToDouble(PChar('1.00000000000000011102230246251565404236316680908203125'));
  if DB(R) <> Int64(4607182418800017408) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 20 FAIL: got ', IntToStr(DB(R)), ' want 4607182418800017408');
  end;
  R := _StrToDouble(PChar('1.00000000000000011102230246251565404236316680908203126'));
  if DB(R) <> Int64(4607182418800017409) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 21 FAIL: got ', IntToStr(DB(R)), ' want 4607182418800017409');
  end;
  R := _StrToDouble(PChar('9007199254740993'));
  if DB(R) <> Int64(4845873199050653696) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 22 FAIL: got ', IntToStr(DB(R)), ' want 4845873199050653696');
  end;
  R := _StrToDouble(PChar('-0.0'));
  if DB(R) <> Int64($8000000000000000) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 23 FAIL: got ', IntToStr(DB(R)), ' want -9223372036854775808');
  end;
  R := _StrToDouble(PChar('1e22'));
  if DB(R) <> Int64(4936209963552724370) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 24 FAIL: got ', IntToStr(DB(R)), ' want 4936209963552724370');
  end;
  R := _StrToDouble(PChar('1e23'));
  if DB(R) <> Int64(4950912855330343670) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 25 FAIL: got ', IntToStr(DB(R)), ' want 4950912855330343670');
  end;
  R := _StrToDouble(PChar('7.2057594037927933e16'));
  if DB(R) <> Int64(4859383997932765184) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 26 FAIL: got ', IntToStr(DB(R)), ' want 4859383997932765184');
  end;
  R := _StrToDouble(PChar('1.41609968988396826717e+03'));
  if DB(R) <> Int64(4653942887746821515) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 27 FAIL: got ', IntToStr(DB(R)), ' want 4653942887746821515');
  end;
  R := _StrToDouble(PChar('6.36619772367581382433e-01'));
  if DB(R) <> Int64(4603909380684499075) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 28 FAIL: got ', IntToStr(DB(R)), ' want 4603909380684499075');
  end;
  R := _StrToDouble(PChar('3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196'));
  if DB(R) <> Int64(4614256656552045848) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 29 FAIL: got ', IntToStr(DB(R)), ' want 4614256656552045848');
  end;
  R := _StrToDouble(PChar('0'));
  if DB(R) <> 0 then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 30 FAIL: got ', IntToStr(DB(R)), ' want 0');
  end;
  R := _StrToDouble(PChar('42'));
  if DB(R) <> Int64(4631107791820423168) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 31 FAIL: got ', IntToStr(DB(R)), ' want 4631107791820423168');
  end;
  R := _StrToDouble(PChar('-13.75'));
  if DB(R) <> -4599441856940474368 then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 32 FAIL: got ', IntToStr(DB(R)), ' want -4599441856940474368');
  end;
  R := _StrToDouble(PChar('6250000000000000000'));
  if DB(R) <> Int64(4888005511694617664) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 33 FAIL: got ', IntToStr(DB(R)), ' want 4888005511694617664');
  end;
  R := _StrToDouble(PChar('9999999999999999999'));
  if DB(R) <> Int64(4891288408196988160) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 34 FAIL: got ', IntToStr(DB(R)), ' want 4891288408196988160');
  end;
  R := _StrToDouble(PChar('1.0000000000000002'));
  if DB(R) <> Int64(4607182418800017409) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 35 FAIL: got ', IntToStr(DB(R)), ' want 4607182418800017409');
  end;
  R := _StrToDouble(PChar('0.5000000000000001'));
  if DB(R) <> Int64(4602678819172646913) then
  begin
    Fails := Fails + 1;
    WriteLn('  strtod vector 36 FAIL: got ', IntToStr(DB(R)), ' want 4602678819172646913');
  end;
  AssertEquals('all strtod vectors bit-exact', 0, Fails);
  Result := '';
end;

function Test_Specials: string;
var
  R: Double;
begin
  R := _StrToDouble(PChar('inf'));
  AssertEquals('inf', Int64(9218868437227405312), DB(R));
  R := _StrToDouble(PChar('-inf'));
  AssertEquals('-inf', -4503599627370496, DB(R));
  R := _StrToDouble(PChar('nan'));
  AssertTrue('nan', (DB(R) and Int64(9218868437227405312)) = Int64(9218868437227405312));
  Result := '';
end;

begin
  AddSuite('blaise_strtod', nil);
  AddTest('Vectors', @Test_Vectors, 'blaise_strtod');
  AddTest('Specials', @Test_Specials, 'blaise_strtod');
  RunAllSysTests();
end.
