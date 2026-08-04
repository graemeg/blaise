{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-1003 DeepNesting - exercises the AST path (real parse + walk)
  end-to-end through the engine. }

unit Guard.Rule.DeepNesting.Tests;

interface

uses
  blaise.testing;

type
  TDeepNestingTests = class(TTestCase)
  published
    procedure TestFlagsTooDeep;
    procedure TestAllowsWithinLimit;
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
  RULE_ID = 'BL-1003';

function RunDN(const ASource: string; AMaxDepth: Integer): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Cfg.RuleConfig(RULE_ID).SetParam('maxDepth', IntToStr(AMaxDepth));
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TDeepNestingTests.TestFlagsTooDeep;
var
  Src: string;
  R:   TReport;
begin
  { Four nested ifs: the fourth (depth 4) breaks a max of 3. }
  Src :=
    'program T;'          + NL +
    'var'                 + NL +
    '  a: Integer;'       + NL +
    'begin'               + NL +
    '  a := 0;'           + NL +
    '  if a = 0 then'     + NL +
    '    if a = 0 then'   + NL +
    '      if a = 0 then' + NL +
    '        if a = 0 then' + NL +
    '          a := 1;'   + NL +
    'end.'                + NL;
  R := RunDN(Src, 3);
  AssertEquals('one over-nested construct', 1, CountForRule(R, RULE_ID));
end;

procedure TDeepNestingTests.TestAllowsWithinLimit;
var
  Src: string;
  R:   TReport;
begin
  { Two nested ifs - well within a max of 3. }
  Src :=
    'program T;'        + NL +
    'var'               + NL +
    '  a: Integer;'     + NL +
    'begin'             + NL +
    '  a := 0;'         + NL +
    '  if a = 0 then'   + NL +
    '    if a = 0 then' + NL +
    '      a := 1;'     + NL +
    'end.'              + NL;
  R := RunDN(Src, 3);
  AssertEquals('nothing flagged', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TDeepNestingTests);

end.
