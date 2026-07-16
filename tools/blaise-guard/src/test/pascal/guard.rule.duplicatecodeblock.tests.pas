{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-3001 DuplicateCodeBlock.  Exercises the cross-file lifecycle
  (Reset -> per-file accumulate -> Finalize) via AnalyseSourceText, which runs
  the full lifecycle on a single in-memory source; within-file duplication is
  detected by the same accumulate/finalize machinery used across files. }

unit Guard.Rule.DuplicateCodeBlock.Tests;

interface

uses
  blaise.testing;

type
  TDuplicateCodeBlockTests = class(TTestCase)
  published
    procedure TestFlagsRepeatedBlock;
    procedure TestDistinctCodeIsSilent;
    procedure TestResetIsolatesRuns;
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
  RULE_ID = 'BL-3001';

function Run(const ASource: string; AMinTokens: Integer): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Cfg.RuleConfig(RULE_ID).SetParam('minTokens', IntToStr(AMinTokens));
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

{ '1 + 2 + 3' is a 5-token run that appears twice verbatim. }
function DuplicatedSource: string;
begin
  Result :=
    'program T;'          + NL +
    'begin'               + NL +
    '  a := 1 + 2 + 3;'   + NL +
    '  b := 1 + 2 + 3;'   + NL +
    'end.'                + NL;
end;

procedure TDuplicateCodeBlockTests.TestFlagsRepeatedBlock;
var
  R: TReport;
begin
  R := Run(DuplicatedSource(), 5);
  AssertTrue('repeated block flagged', CountForRule(R, RULE_ID) >= 1);
end;

procedure TDuplicateCodeBlockTests.TestDistinctCodeIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'   + NL +
    'begin'        + NL +
    '  a := 1;'    + NL +
    '  b := 2;'    + NL +
    'end.'         + NL;
  R := Run(Src, 5);
  AssertEquals('no duplication', 0, CountForRule(R, RULE_ID));
end;

procedure TDuplicateCodeBlockTests.TestResetIsolatesRuns;
var
  R1, R2: TReport;
begin
  { Two independent runs of the same engine setup must not accumulate state:
    the second run should see exactly what the first did, not double. }
  R1 := Run(DuplicatedSource(), 5);
  R2 := Run(DuplicatedSource(), 5);
  AssertEquals('run is reproducible',
    CountForRule(R1, RULE_ID), CountForRule(R2, RULE_ID));
end;

initialization
  RegisterTest(TDuplicateCodeBlockTests);

end.
