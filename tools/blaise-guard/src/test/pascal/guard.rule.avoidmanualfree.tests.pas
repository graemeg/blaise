{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-2001 AvoidManualFree (AST path, end-to-end). }

unit Guard.Rule.AvoidManualFree.Tests;

interface

uses
  blaise.testing;

type
  TAvoidManualFreeTests = class(TTestCase)
  published
    procedure TestFlagsFreeCall;
    procedure TestCleanCodeIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-2001';

function RunAF(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TAvoidManualFreeTests.TestFlagsFreeCall;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    { Parens are REQUIRED: Blaise rejects a bare parameterless call, so the
      old `o.Free;` spelling stopped parsing and this test was asserting
      against a source the frontend never got past — the finding it counted
      had become BL-0000 (ParseError), not BL-2001. }
    'program T;'      + NL +
    'var'             + NL +
    '  o: TObject;'   + NL +
    'begin'           + NL +
    '  o.Free();'     + NL +
    'end.'            + NL;
  R := RunAF(Src);
  AssertEquals('one manual free', 1, CountForRule(R, RULE_ID));
end;

procedure TAvoidManualFreeTests.TestCleanCodeIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'      + NL +
    'var'             + NL +
    '  a: Integer;'   + NL +
    'begin'           + NL +
    '  a := 1;'       + NL +
    'end.'            + NL;
  R := RunAF(Src);
  AssertEquals('nothing to flag', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TAvoidManualFreeTests);

end.
