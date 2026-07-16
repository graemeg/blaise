{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-1001 MaxLineLength, driven end-to-end through the engine. }

unit Guard.Rule.MaxLineLength.Tests;

interface

uses
  blaise.testing;

type
  TMaxLineLengthTests = class(TTestCase)
  published
    procedure TestFlagsLongLine;
    procedure TestRespectsThreshold;
    procedure TestReportsCorrectLine;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Domain,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-1001';

{ Line 1 = 4 chars, line 2 = 16 chars.  Content is irrelevant to a line rule,
  so it need not be valid Blaise. }
function TwoLineSource: string;
begin
  Result := 'aaaa' + NL + 'bbbbbbbbbbbbbbbb' + NL;
end;

function RunWithMax(AMax: Integer): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Cfg.RuleConfig(RULE_ID).SetParam('maxLength', IntToStr(AMax));
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', TwoLineSource());
end;

procedure TMaxLineLengthTests.TestFlagsLongLine;
var
  R: TReport;
begin
  R := RunWithMax(10);
  AssertEquals('one line over 10', 1, CountForRule(R, RULE_ID));
end;

procedure TMaxLineLengthTests.TestRespectsThreshold;
var
  R: TReport;
begin
  { With a 100-char limit neither line is too long. }
  R := RunWithMax(100);
  AssertEquals('nothing over 100', 0, CountForRule(R, RULE_ID));
end;

procedure TMaxLineLengthTests.TestReportsCorrectLine;
var
  R: TReport;
  D: TDiagnostic;
begin
  R := RunWithMax(10);
  D := FirstForRule(R, RULE_ID);
  AssertNotNull('diagnostic present', D);
  AssertEquals('offending line is 2', 2, D.Location.Line);
end;

initialization
  RegisterTest(TMaxLineLengthTests);

end.
