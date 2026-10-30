{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Comprehensive punit exercise — adapted from the FPC original for Blaise.
  Changes vs. original testpunit2.pp:
    * AssertEqual  → AssertEquals  (Blaise punit uses the 's' suffix)
    * AnsiString   → string
    * QWord        → Int64         (Blaise lacks QWord)
    * Smallint / Shortint / Word / Longint  → Integer (Blaise narrows these)
    * Test8: .Active field dropped; use PTest result + Options directly
    * DoTest23-25: TClass uses Pointer (Blaise typeinfo pointers)
    * DoTest21: now a proper must-fail test — InheritsFrom detects class mismatch
}

program testpunit2;

uses punit;

type
  EError = class(TObject);

function DoTest1 : string;
begin
  Result := 'Error in test';
end;

function DoTest2 : string;
begin
  { OK if RequirePassed=False, Unimplemented if RequirePassed=True }
  Result := '';
end;

function DoTest3 : string;
begin
  Fail('Must fail: Failed through Fail()');
  Result := '';
end;

function DoTest4 : string;
begin
  FailExit('Must fail: Failed through FailExit()');
  Result := 'Nono';  { not reached }
end;

function DoTest5 : string;
begin
  Fail('Must fail: Failed through Fail()');
  Result := 'Failed through default';  { ignored }
end;

function DoTest6 : string;
begin
  AssertTrue('Some message', True);
  Result := '';
end;

function DoTest7 : string;
begin
  if not AssertTrue('Must fail: AssertTrue with False', False) then
    exit;
end;

function DoTest9 : string;
begin
  if not AssertEquals('Must fail: Strings equal',
    'Expected result string', 'Actual result string') then
    exit;
end;

function DoTest10 : string;
var
  O1, O2 : Integer;
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Integers equal', O1, O2) then
    exit;
end;

function DoTest11 : string;
var
  O1, O2 : Integer;   { was Smallint — narrowed to Integer in Blaise punit }
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Integers equal (was Smallint)', O1, O2) then
    exit;
end;

function DoTest12 : string;
var
  O1, O2 : Integer;   { was Longint — same type in Blaise }
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Integers equal (was Longint)', O1, O2) then
    exit;
end;

function DoTest13 : string;
var
  O1, O2 : Byte;
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Bytes equal', O1, O2) then
    exit;
end;

function DoTest14 : string;
var
  O1, O2 : Integer;   { was Shortint — narrowed to Integer in Blaise punit }
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Integers equal (was Shortint)', O1, O2) then
    exit;
end;

function DoTest15 : string;
var
  O1, O2 : UInt32;
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Cardinals equal', O1, O2) then
    exit;
end;

function DoTest16 : string;
var
  O1, O2 : Int64;
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Int64s equal', O1, O2) then
    exit;
end;

function DoTest17 : string;
var
  O1, O2 : Int64;    { was QWord — Blaise lacks QWord; using Int64 }
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Int64s equal (was QWord)', O1, O2) then
    exit;
end;

function DoTest18 : string;
var
  O1, O2 : Pointer;
begin
  O1 := Pointer(1);
  O2 := Pointer(2);
  if not AssertEquals('Must fail: Pointers equal', O1, O2) then
    exit;
end;

function DoTest19 : string;
var
  O1, O2 : Integer;   { was Word — narrowed to Integer in Blaise punit }
begin
  O1 := 1;
  O2 := 2;
  if not AssertEquals('Must fail: Integers equal (was Word)', O1, O2) then
    exit;
end;

function DoTest20 : string;
begin
  { ExpectException set but no exception raised → should fail }
  ExpectException('Must fail: Expected EError but none raised', EError);
end;

function DoTest21 : string;
begin
  { Must fail: ExpectException declared EError but EFail raised — class
    mismatch detected by InheritsFrom check in RunTestHandler. }
  ExpectException('Must fail: expected EError but raised EFail', EError);
  raise EFail.Create('Expected');
end;

function DoTest22 : string;
begin
  { Correct class: EFail expected and EFail raised — should pass. }
  ExpectException('Expect exception EFail', EFail);
  raise EFail.Create('Expected');
end;

{ DoTest23–25 exercise AssertEquals on class references.  Blaise uses
  Pointer for TClass; typeinfo pointers are comparable via AssertEquals(Pointer). }

function DoTest23 : string;
begin
  { Must fail: EError ≠ EFail as pointer values }
  AssertEquals('Must fail: class pointers differ', Pointer(EError), Pointer(EFail));
end;

function DoTest24 : string;
begin
  { Must fail: nil ≠ EFail }
  AssertEquals('Must fail: nil vs EFail class pointer', Pointer(nil), Pointer(EFail));
end;

function DoTest25 : string;
begin
  { Must fail: EFail ≠ nil }
  AssertEquals('Must fail: EFail class pointer vs nil', Pointer(EFail), Pointer(nil));
end;

function DoTest26 : string;
var
  A, B : TObject;
begin
  A := EFail.Create('');
  B := EError.Create();
  try
    AssertSame('Must fail: Instances differ', A, B);
  finally
    A.Free();
    B.Free();
  end;
end;

function DoTest27 : string;
var
  A : TObject;
begin
  A := EFail.Create('');
  try
    AssertSame('Must fail: Instances differ (actual nil)', A, nil);
  finally
    A.Free();
  end;
end;

function DoTest28 : string;
var
  A : TObject;
begin
  A := EFail.Create('');
  try
    AssertSame('Must fail: Instances differ (expected nil)', nil, A);
  finally
    A.Free();
  end;
end;

function DoTest29 : string;
var
  A, B : TObject;
begin
  A := EFail.Create('');
  try
    B := A;
    AssertSame('Instances equal', B, A);
  finally
    A.Free();
  end;
end;

function DoTest30 : string;
var
  A, B : Float64;
begin
  A := 1.2;
  B := 3.4;
  AssertEquals('Must fail: Doubles not within delta', B, A);
end;

function DoTest31 : string;
var
  A, B : Float64;
begin
  A := 1.2;
  B := 1.2 + (DefaultDoubleDelta / 2);
  AssertEquals('Doubles within delta', B, A);
end;

function DoTest32 : string;
var
  A, B : Float64;
begin
  A := 1.2;
  B := 3.4;
  AssertEquals('Doubles within explicit delta of 1', B, A, 1);
end;

var
  T8 : PTest;

begin
  RequirePassed := True;
  AddTest('Test1',  @DoTest1);
  AddTest('Test2',  @DoTest2);
  AddTest('Test3',  @DoTest3);
  AddTest('Test4',  @DoTest4);
  AddTest('Test5',  @DoTest5);
  AddTest('Test6',  @DoTest6);
  AddTest('Test7',  @DoTest7);
  { Test8 is the same function as Test7 but marked inactive.
    Original used .Active := False; Blaise punit uses Options + Include. }
  T8 := AddTest('Test8', @DoTest7);
  if T8 <> nil then
    Include(T8^.Options, toInactive);
  AddTest('Test9',  @DoTest9);
  AddTest('Test10', @DoTest10);
  AddTest('Test11', @DoTest11);
  AddTest('Test12', @DoTest12);
  AddTest('Test13', @DoTest13);
  AddTest('Test14', @DoTest14);
  AddTest('Test15', @DoTest15);
  AddTest('Test16', @DoTest16);
  AddTest('Test17', @DoTest17);
  AddTest('Test18', @DoTest18);
  AddTest('Test19', @DoTest19);
  AddTest('Test20', @DoTest20);
  AddTest('Test21', @DoTest21);
  AddTest('Test22', @DoTest22);
  AddTest('Test23', @DoTest23);
  AddTest('Test24', @DoTest24);
  AddTest('Test25', @DoTest25);
  AddTest('Test26', @DoTest26);
  AddTest('Test27', @DoTest27);
  AddTest('Test28', @DoTest28);
  AddTest('Test29', @DoTest29);
  AddTest('Test30', @DoTest30);
  AddTest('Test31', @DoTest31);
  AddTest('Test32', @DoTest32);
  RunAllSysTests();
end.
