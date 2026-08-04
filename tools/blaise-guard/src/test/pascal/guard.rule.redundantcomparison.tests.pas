{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-1005 RedundantComparison (AST path, end-to-end).

  TestNilComparisonIsSilent pins a deliberate NON-feature: fpsonar reports
  `= nil` in favour of Assigned(), but that check fired 3242 times against
  compiler/src/main/pascal, where `= nil` is the house idiom.  The rule must
  stay silent on it. }

unit Guard.Rule.RedundantComparison.Tests;

interface

uses
  blaise.testing;

type
  TRedundantComparisonTests = class(TTestCase)
  published
    procedure TestFlagsBooleanLiteralCompare;
    procedure TestFlagsSelfAssignment;
    procedure TestNilComparisonIsSilent;
    procedure TestOrdinaryCompareIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-1005';

function RunRC(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TRedundantComparisonTests.TestFlagsBooleanLiteralCompare;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'            + NL +
    'var'                   + NL +
    '  b: Boolean;'         + NL +
    'begin'                 + NL +
    '  b := True;'          + NL +
    '  if b = True then'    + NL +
    '    WriteLn(1);'       + NL +
    'end.'                  + NL;
  R := RunRC(Src);
  AssertEquals('= True is redundant', 1, CountForRule(R, RULE_ID));
end;

procedure TRedundantComparisonTests.TestFlagsSelfAssignment;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'            + NL +
    'var'                   + NL +
    '  n: Integer;'         + NL +
    'begin'                 + NL +
    '  n := 1;'             + NL +
    '  n := n;'             + NL +
    '  WriteLn(n);'         + NL +
    'end.'                  + NL;
  R := RunRC(Src);
  AssertEquals('self-assignment', 1, CountForRule(R, RULE_ID));
end;

procedure TRedundantComparisonTests.TestNilComparisonIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { Deliberately NOT flagged — see the unit header. }
  Src :=
    'program T;'            + NL +
    'type'                  + NL +
    '  TC = class'          + NL +
    '  end;'                + NL +
    'var'                   + NL +
    '  o: TC;'              + NL +
    'begin'                 + NL +
    '  o := nil;'           + NL +
    '  if o = nil then'     + NL +
    '    WriteLn(1);'       + NL +
    'end.'                  + NL;
  R := RunRC(Src);
  AssertEquals('= nil is the house idiom', 0, CountForRule(R, RULE_ID));
end;

procedure TRedundantComparisonTests.TestOrdinaryCompareIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'            + NL +
    'var'                   + NL +
    '  a, b: Integer;'      + NL +
    'begin'                 + NL +
    '  a := 1;'             + NL +
    '  b := 2;'             + NL +
    '  if a = b then'       + NL +
    '    WriteLn(1);'       + NL +
    'end.'                  + NL;
  R := RunRC(Src);
  AssertEquals('ordinary comparison', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TRedundantComparisonTests);

end.
