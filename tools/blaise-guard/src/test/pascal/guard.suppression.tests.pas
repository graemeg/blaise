{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for inline suppression (`blaise-guard: ignore` / `ignore-file`).

  The negative cases carry the weight here: a suppression mechanism that
  over-suppresses is worse than none at all, because it hides findings
  silently.  Each test therefore pins BOTH that the intended finding goes away
  AND that a neighbouring one does not. }

unit Guard.Suppression.Tests;

interface

uses
  blaise.testing;

type
  TSuppressionTests = class(TTestCase)
  published
    procedure TestSameLineSuppresses;
    procedure TestPreviousLineSuppresses;
    procedure TestBareIgnoreSuppressesAnyRule;
    procedure TestWrongRuleIdDoesNotSuppress;
    procedure TestReasonTextIsNotParsedAsRuleIds;
    procedure TestFileScopeInHeaderSuppressesAll;
    procedure TestFileScopeOnCodeLineDoesNotApply;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-1005';   { RedundantComparison — easy to trigger twice }

function RunSp(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

{ Two `= True` comparisons; the first carries a directive, the second does
  not.  Exactly one finding must survive. }
procedure TSuppressionTests.TestSameLineSuppresses;
var
  R: TReport;
begin
  R := RunSp(
    'program T;'                                        + NL +
    'var b: Boolean;'                                   + NL +
    'begin'                                             + NL +
    '  b := True;'                                      + NL +
    '  if b = True then   // blaise-guard: ignore BL-1005' + NL +
    '    WriteLn(1);'                                   + NL +
    '  if b = True then'                                + NL +
    '    WriteLn(2);'                                   + NL +
    'end.'                                              + NL);
  AssertEquals('only the un-annotated one survives', 1, CountForRule(R, RULE_ID));
end;

procedure TSuppressionTests.TestPreviousLineSuppresses;
var
  R: TReport;
begin
  { The directive on its own line covers the line below — for findings that
    point at a construct's first line, where a trailing comment is awkward. }
  R := RunSp(
    'program T;'                                   + NL +
    'var b: Boolean;'                              + NL +
    'begin'                                        + NL +
    '  b := True;'                                 + NL +
    '  // blaise-guard: ignore BL-1005'            + NL +
    '  if b = True then'                           + NL +
    '    WriteLn(1);'                              + NL +
    'end.'                                         + NL);
  AssertEquals('previous-line directive applies', 0, CountForRule(R, RULE_ID));
end;

procedure TSuppressionTests.TestBareIgnoreSuppressesAnyRule;
var
  R: TReport;
begin
  R := RunSp(
    'program T;'                              + NL +
    'var b: Boolean;'                         + NL +
    'begin'                                   + NL +
    '  b := True;'                            + NL +
    '  if b = True then   // blaise-guard: ignore' + NL +
    '    WriteLn(1);'                         + NL +
    'end.'                                    + NL);
  AssertEquals('unqualified ignore covers every rule', 0, CountForRule(R, RULE_ID));
end;

procedure TSuppressionTests.TestWrongRuleIdDoesNotSuppress;
var
  R: TReport;
begin
  { The most important negative: naming a DIFFERENT rule must not silently
    suppress this one. }
  R := RunSp(
    'program T;'                                        + NL +
    'var b: Boolean;'                                   + NL +
    'begin'                                             + NL +
    '  b := True;'                                      + NL +
    '  if b = True then   // blaise-guard: ignore BL-9999' + NL +
    '    WriteLn(1);'                                   + NL +
    'end.'                                              + NL);
  AssertEquals('a different rule id does not suppress', 1, CountForRule(R, RULE_ID));
end;

procedure TSuppressionTests.TestReasonTextIsNotParsedAsRuleIds;
var
  R: TReport;
begin
  { The reason after ' - ' is prose.  An id-looking word inside it must not
    widen the suppression: here the directive names BL-9999 (not our rule) and
    only MENTIONS BL-1005 in the reason, so the finding must survive. }
  R := RunSp(
    'program T;'                                                     + NL +
    'var b: Boolean;'                                                + NL +
    'begin'                                                          + NL +
    '  b := True;'                                                   + NL +
    '  if b = True then   // blaise-guard: ignore BL-9999 - unlike BL-1005' + NL +
    '    WriteLn(1);'                                                + NL +
    'end.'                                                           + NL);
  AssertEquals('reason text is not a rule list', 1, CountForRule(R, RULE_ID));
end;

procedure TSuppressionTests.TestFileScopeInHeaderSuppressesAll;
var
  R: TReport;
begin
  { One directive in the preamble covers every finding in the file — the
    escape hatch for a whole-file false positive (e.g. an operand array the
    token rules cannot tell from a string). }
  R := RunSp(
    '{ blaise-guard: ignore-file BL-1005 }'  + NL +
    'program T;'                             + NL +
    'var b: Boolean;'                        + NL +
    'begin'                                  + NL +
    '  b := True;'                           + NL +
    '  if b = True then'                     + NL +
    '    WriteLn(1);'                        + NL +
    '  if b = True then'                     + NL +
    '    WriteLn(2);'                        + NL +
    'end.'                                   + NL);
  AssertEquals('file scope covers every finding', 0, CountForRule(R, RULE_ID));
end;

procedure TSuppressionTests.TestFileScopeOnCodeLineDoesNotApply;
var
  R: TReport;
begin
  { `ignore-file` is only honoured in the PREAMBLE.  Written against a code
    line it must NOT acquire file scope — otherwise a stray directive halfway
    down a unit would silence everything above and below it.  Note it does not
    act as a line directive either: 'ignore' is a prefix of 'ignore-file', and
    the two are deliberately kept distinct. }
  R := RunSp(
    'program T;'                                          + NL +
    'var b: Boolean;'                                     + NL +
    'begin'                                               + NL +
    '  b := True;'                                        + NL +
    '  if b = True then   // blaise-guard: ignore-file BL-1005' + NL +
    '    WriteLn(1);'                                     + NL +
    '  if b = True then'                                  + NL +
    '    WriteLn(2);'                                     + NL +
    'end.'                                                + NL);
  AssertEquals('file scope does not apply mid-file', 2, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TSuppressionTests);

end.
