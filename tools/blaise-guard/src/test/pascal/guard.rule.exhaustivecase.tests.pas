{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-3002 ExhaustiveCase (AST path, end-to-end).

  The negative cases matter as much as the positive one: this rule matches a
  case statement to an enum by its branch LABELS (there is no semantic pass to
  resolve the selector type), so it must stay silent whenever that match is
  not certain. }

unit Guard.Rule.ExhaustiveCase.Tests;

interface

uses
  blaise.testing;

type
  TExhaustiveCaseTests = class(TTestCase)
  published
    procedure TestFlagsMissingMember;
    procedure TestExhaustiveIsSilent;
    procedure TestElseClauseIsSilent;
    procedure TestIntegerCaseIsSilent;
    procedure TestUnknownEnumIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-3002';

function RunEC(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TExhaustiveCaseTests.TestFlagsMissingMember;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                  + NL +
    'type'                        + NL +
    '  EK = (ekA, ekB, ekC);'     + NL +
    'var'                         + NL +
    '  k: EK;'                    + NL +
    'begin'                       + NL +
    '  k := ekA;'                 + NL +
    '  case k of'                 + NL +
    '    ekA: WriteLn(1);'        + NL +
    '    ekB: WriteLn(2);'        + NL +
    '  end;'                      + NL +
    'end.'                        + NL;
  R := RunEC(Src);
  AssertEquals('ekC missing, no else', 1, CountForRule(R, RULE_ID));
end;

procedure TExhaustiveCaseTests.TestExhaustiveIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                  + NL +
    'type'                        + NL +
    '  EK = (ekA, ekB);'          + NL +
    'var'                         + NL +
    '  k: EK;'                    + NL +
    'begin'                       + NL +
    '  k := ekA;'                 + NL +
    '  case k of'                 + NL +
    '    ekA: WriteLn(1);'        + NL +
    '    ekB: WriteLn(2);'        + NL +
    '  end;'                      + NL +
    'end.'                        + NL;
  R := RunEC(Src);
  AssertEquals('all members covered', 0, CountForRule(R, RULE_ID));
end;

procedure TExhaustiveCaseTests.TestElseClauseIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { An else clause makes the statement total regardless of coverage. }
  Src :=
    'program T;'                  + NL +
    'type'                        + NL +
    '  EK = (ekA, ekB, ekC);'     + NL +
    'var'                         + NL +
    '  k: EK;'                    + NL +
    'begin'                       + NL +
    '  k := ekA;'                 + NL +
    '  case k of'                 + NL +
    '    ekA: WriteLn(1);'        + NL +
    '  else'                      + NL +
    '    WriteLn(9);'             + NL +
    '  end;'                      + NL +
    'end.'                        + NL;
  R := RunEC(Src);
  AssertEquals('else covers the rest', 0, CountForRule(R, RULE_ID));
end;

procedure TExhaustiveCaseTests.TestIntegerCaseIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { Integer labels are not identifiers, so no enum can be matched — the rule
    must not guess. }
  Src :=
    'program T;'                  + NL +
    'type'                        + NL +
    '  EK = (ekA, ekB, ekC);'     + NL +
    'var'                         + NL +
    '  n: Integer;'               + NL +
    'begin'                       + NL +
    '  n := 1;'                   + NL +
    '  case n of'                 + NL +
    '    1: WriteLn(1);'          + NL +
    '    2: WriteLn(2);'          + NL +
    '  end;'                      + NL +
    'end.'                        + NL;
  R := RunEC(Src);
  AssertEquals('integer case is not an enum case', 0, CountForRule(R, RULE_ID));
end;

procedure TExhaustiveCaseTests.TestUnknownEnumIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { Labels that match no enum declared IN THIS FILE (the enum would live in
    another unit) must not report — single-file analysis cannot know the
    member set. }
  Src :=
    'program T;'                  + NL +
    'var'                         + NL +
    '  k: Integer;'               + NL +
    'begin'                       + NL +
    '  k := 0;'                   + NL +
    '  case k of'                 + NL +
    '    someLabel: WriteLn(1);'  + NL +
    '  end;'                      + NL +
    'end.'                        + NL;
  R := RunEC(Src);
  AssertEquals('no enum declared here', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TExhaustiveCaseTests);

end.
