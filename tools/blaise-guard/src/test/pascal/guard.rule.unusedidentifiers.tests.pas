{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-1004 UnusedIdentifiers (AST path via the expression walker). }

unit Guard.Rule.UnusedIdentifiers.Tests;

interface

uses
  blaise.testing;

type
  TUnusedIdentifiersTests = class(TTestCase)
  published
    procedure TestFlagsUnusedLocal;
    procedure TestUsedLocalIsSilent;
    procedure TestParamsOffByDefault;
    procedure TestParamsCheckedWhenEnabled;
  end;

implementation

uses
  SysUtils,
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Domain,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-1004';

function Run(const ASource: string; ACheckParams: Boolean): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  if ACheckParams then
    Cfg.RuleConfig(RULE_ID).SetParam('checkParameters', 'true');
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TUnusedIdentifiersTests.TestFlagsUnusedLocal;
var
  Src: string;
  R:   TReport;
  D:   TDiagnostic;
begin
  { y is declared but never referenced; x is written and read. }
  Src :=
    'program T;'       + NL +
    'procedure Foo;'   + NL +
    'var'              + NL +
    '  x: Integer;'    + NL +
    '  y: Integer;'    + NL +
    'begin'            + NL +
    '  x := 1;'        + NL +
    '  WriteLn(x);'    + NL +
    'end;'             + NL +
    'begin'            + NL +
    'end.'             + NL;
  R := Run(Src, False);
  AssertEquals('one unused local', 1, CountForRule(R, RULE_ID));
  D := FirstForRule(R, RULE_ID);
  AssertNotNull('has diagnostic', D);
  AssertContains('names y', 'y', D.Message);
end;

procedure TUnusedIdentifiersTests.TestUsedLocalIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'       + NL +
    'procedure Foo;'   + NL +
    'var'              + NL +
    '  x: Integer;'    + NL +
    'begin'            + NL +
    '  x := 1;'        + NL +
    '  WriteLn(x);'    + NL +
    'end;'             + NL +
    'begin'            + NL +
    'end.'             + NL;
  R := Run(Src, False);
  AssertEquals('nothing unused', 0, CountForRule(R, RULE_ID));
end;

procedure TUnusedIdentifiersTests.TestParamsOffByDefault;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                 + NL +
    'procedure Foo(a: Integer);' + NL +
    'begin'                      + NL +
    'end;'                       + NL +
    'begin'                      + NL +
    'end.'                       + NL;
  R := Run(Src, False);
  AssertEquals('params not checked by default', 0, CountForRule(R, RULE_ID));
end;

procedure TUnusedIdentifiersTests.TestParamsCheckedWhenEnabled;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                 + NL +
    'procedure Foo(a: Integer);' + NL +
    'begin'                      + NL +
    'end;'                       + NL +
    'begin'                      + NL +
    'end.'                       + NL;
  R := Run(Src, True);
  AssertEquals('unused param flagged', 1, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TUnusedIdentifiersTests);

end.
