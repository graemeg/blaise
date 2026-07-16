{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-1002 MaxFunctionLines (AST path, end-to-end). }

unit Guard.Rule.MaxFunctionLines.Tests;

interface

uses
  blaise.testing;

type
  TMaxFunctionLinesTests = class(TTestCase)
  published
    procedure TestFlagsLongRoutine;
    procedure TestAllowsShortRoutine;
  end;

implementation

uses
  SysUtils,
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-1002';

function Run(const ASource: string; AMaxLines: Integer): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Cfg.RuleConfig(RULE_ID).SetParam('maxLines', IntToStr(AMaxLines));
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

function LongProc: string;
begin
  Result :=
    'program T;'    + NL +   { 1 }
    'procedure Foo;'+ NL +   { 2 }
    'begin'         + NL +   { 3 }
    '  a := 1;'     + NL +   { 4 }
    '  b := 2;'     + NL +   { 5 }
    '  c := 3;'     + NL +   { 6 }
    '  d := 4;'     + NL +   { 7 }
    'end;'          + NL +   { 8 }
    'begin'         + NL +
    'end.'          + NL;
end;

procedure TMaxFunctionLinesTests.TestFlagsLongRoutine;
var
  R: TReport;
begin
  { Foo spans ~6 lines; a limit of 3 must flag it exactly once. }
  R := Run(LongProc(), 3);
  AssertEquals('one long routine', 1, CountForRule(R, RULE_ID));
end;

procedure TMaxFunctionLinesTests.TestAllowsShortRoutine;
var
  R: TReport;
begin
  { Same routine, generous limit -> nothing flagged. }
  R := Run(LongProc(), 15);
  AssertEquals('within limit', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TMaxFunctionLinesTests);

end.
