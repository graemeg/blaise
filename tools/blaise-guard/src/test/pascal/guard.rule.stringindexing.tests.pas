{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-2003 StringIndexing (token path, end-to-end). }

unit Guard.Rule.StringIndexing.Tests;

interface

uses
  blaise.testing;

type
  TStringIndexingTests = class(TTestCase)
  published
    procedure TestFlagsOneBasedSubscript;
    procedure TestZeroBasedIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-2003';

function Run(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TStringIndexingTests.TestFlagsOneBasedSubscript;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'      + NL +
    'var'             + NL +
    '  s: string;'    + NL +
    'begin'           + NL +
    '  s := ''x'';'   + NL +
    '  if s[1] = 65 then' + NL +
    '    s := ''y'';' + NL +
    'end.'            + NL;
  R := Run(Src);
  AssertEquals('one 1-based subscript', 1, CountForRule(R, RULE_ID));
end;

procedure TStringIndexingTests.TestZeroBasedIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'      + NL +
    'var'             + NL +
    '  s: string;'    + NL +
    'begin'           + NL +
    '  s := ''x'';'   + NL +
    '  if s[0] = 65 then' + NL +
    '    s := ''y'';' + NL +
    'end.'            + NL;
  R := Run(Src);
  AssertEquals('0-based is fine', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TStringIndexingTests);

end.
