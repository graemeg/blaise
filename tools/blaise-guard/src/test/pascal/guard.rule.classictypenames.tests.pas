{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-2006 ClassicTypeNames (token path, end-to-end). }

unit Guard.Rule.ClassicTypeNames.Tests;

interface

uses
  blaise.testing;

type
  TClassicTypeNamesTests = class(TTestCase)
  published
    { every classic name used as a type is reported, case-insensitively }
    procedure TestFlagsEveryClassicName;
    { the finding names the replacement and carries it as a quick-fix }
    procedure TestSuggestsReplacement;
    { Extended warns that x87 80-bit precision does not carry over }
    procedure TestExtendedWarnsAboutPrecision;
    { modern names and Byte are not reported }
    procedure TestModernNamesAreSilent;
    { a member access or a declaration of the same name is not a type use }
    procedure TestNonTypeUsesAreSilent;
    { a file's own variable that happens to carry a classic name (a local
      called Comp) is not a type use anywhere it appears }
    procedure TestOwnIdentifierIsSilentEverywhere;
    { a classic name in a typed constant, a typed array constant or a default
      parameter -- followed by '=' but in a type position -- is still
      reported, and does not hide the file's other uses }
    procedure TestTypedConstAndDefaultParamAreReported;
  end;

implementation

uses
  Guard.Config,
  Guard.Domain,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-2006';

function RunCT(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TClassicTypeNamesTests.TestFlagsEveryClassicName;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                                          + NL +
    'var'                                                 + NL +
    '  a: Integer; b: Cardinal; c: SmallInt; d: Word;'    + NL +
    '  e: QWord; f: PtrUInt; g: Single; h: Double;'       + NL +
    '  i: LongInt; j: LongWord; k: ShortInt; l: Real;'    + NL +
    '  m: Extended; n: Comp; o: NativeInt; p: NativeUInt;' + NL +
    '  q: PtrInt; r: integer;'                            + NL +
    'begin'                                               + NL +
    'end.'                                                + NL;
  R := RunCT(Src);
  AssertEquals('eighteen classic type uses', 18, CountForRule(R, RULE_ID));
end;

procedure TClassicTypeNamesTests.TestSuggestsReplacement;
var
  R: TReport;
  D: TDiagnostic;
begin
  R := RunCT(
    'program T;'            + NL +
    'var'                   + NL +
    '  a: Cardinal;'        + NL +
    'begin'                 + NL +
    'end.'                  + NL);
  D := FirstForRule(R, RULE_ID);
  AssertNotNull('reported', D);
  AssertTrue('message names the replacement: ' + D.Message,
    Pos('UInt32', D.Message) >= 0);
  AssertNotNull('has a quick-fix', D.Fix);
  AssertTrue('quick-fix replaces the name', D.Fix.HasReplacement);
  AssertEquals('replacement', 'UInt32', D.Fix.Replacement);
  AssertEquals('reported at the name', 3, D.Location.Line);
end;

procedure TClassicTypeNamesTests.TestExtendedWarnsAboutPrecision;
var
  R: TReport;
  D: TDiagnostic;
begin
  R := RunCT(
    'program T;'            + NL +
    'var'                   + NL +
    '  x: Extended;'        + NL +
    'begin'                 + NL +
    'end.'                  + NL);
  D := FirstForRule(R, RULE_ID);
  AssertNotNull('reported', D);
  AssertTrue('suggests Float64: ' + D.Message, Pos('Float64', D.Message) >= 0);
  AssertTrue('mentions the precision change: ' + D.Message,
    Pos('80-bit', D.Message) >= 0);
end;

procedure TClassicTypeNamesTests.TestModernNamesAreSilent;
var
  R: TReport;
begin
  R := RunCT(
    'program T;'                                       + NL +
    'var'                                              + NL +
    '  a: Int32; b: UInt32; c: Int; d: UInt; e: Int8;' + NL +
    '  f: Float; g: Float64; h: Float32; i: Byte;'     + NL +
    'begin'                                            + NL +
    'end.'                                             + NL);
  AssertEquals('nothing to flag', 0, CountForRule(R, RULE_ID));
end;

procedure TClassicTypeNamesTests.TestNonTypeUsesAreSilent;
var
  R: TReport;
begin
  R := RunCT(
    'program T;'                      + NL +
    'type'                            + NL +
    '  Real = Float64;'               + NL +
    '  TRec = record'                 + NL +
    '    Word: Int32;'                + NL +
    '  end;'                          + NL +
    'var'                             + NL +
    '  R: TRec;'                      + NL +
    '  X: Int32;'                     + NL +
    'begin'                           + NL +
    '  X := R.Word;'                  + NL +
    'end.'                            + NL);
  AssertEquals('declarations and member access', 0,
    CountForRule(R, RULE_ID));
end;

procedure TClassicTypeNamesTests.TestOwnIdentifierIsSilentEverywhere;
var
  R: TReport;
begin
  R := RunCT(
    'program T;'                      + NL +
    'type'                            + NL +
    '  TBox = class'                  + NL +
    '    N: Int32;'                   + NL +
    '  end;'                          + NL +
    'var'                             + NL +
    '  Comp: TBox;'                   + NL +
    '  X: Int32;'                     + NL +
    'begin'                           + NL +
    '  Comp := TBox.Create();'        + NL +
    '  X := Comp.N;'                  + NL +
    'end.'                            + NL);
  AssertEquals('a variable called Comp', 0, CountForRule(R, RULE_ID));
end;

procedure TClassicTypeNamesTests.TestTypedConstAndDefaultParamAreReported;
var
  R: TReport;
begin
  R := RunCT(
    'program T;'                                       + NL +
    'const'                                            + NL +
    '  K: Integer = 5;'                                + NL +
    '  A: array[0..1] of Double = (1.0, 2.0);'         + NL +
    'procedure F(A: Double = 0.5);'                    + NL +
    'begin'                                            + NL +
    'end;'                                             + NL +
    'var'                                              + NL +
    '  X: Integer; Y: Double;'                         + NL +
    'begin'                                            + NL +
    'end.'                                             + NL);
  AssertEquals('all five type uses', 5, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TClassicTypeNamesTests);

end.
