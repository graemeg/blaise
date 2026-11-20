{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-1007 DeclarationParentheses (token path, end-to-end). }

unit Guard.Rule.DeclarationParentheses.Tests;

interface

uses
  blaise.testing;

type
  TDeclarationParenthesesTests = class(TTestCase)
  published
    { every parameterless routine heading without () is reported: standalone,
      class members, qualified method bodies, constructors, destructors }
    procedure TestFlagsHeadingsWithoutParentheses;
    { headings that already carry () -- empty or with parameters -- are silent }
    procedure TestHeadingsWithParenthesesAreSilent;
    { the finding sits on the routine name and offers Name() as a quick-fix }
    procedure TestSuggestsParentheses;
    { a generic routine gets a finding but no textual replacement, because
      the () goes after the type-parameter list, not after the name }
    procedure TestGenericHeadingHasNoReplacement;
    { procedural types and anonymous methods are not routine headings }
    procedure TestProceduralTypesAndAnonymousMethodsAreSilent;
    { the rule ships disabled: the default config leaves it off }
    procedure TestOffByDefault;
  end;

implementation

uses
  Guard.Config,
  Guard.Domain,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-1007';

function RunDP(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TDeclarationParenthesesTests.TestFlagsHeadingsWithoutParentheses;
var
  R: TReport;
begin
  R := RunDP(
    'program T;'                                      + NL +
    'type'                                            + NL +
    '  TC = class'                                    + NL +
    '    constructor Create;'                         + NL +
    '    destructor Destroy; override;'               + NL +
    '    procedure Foo;'                              + NL +
    '    function Bar: Int32;'                        + NL +
    '    class procedure Baz;'                        + NL +
    '  end;'                                          + NL +
    'constructor TC.Create; begin end;'               + NL +
    'destructor TC.Destroy; begin end;'               + NL +
    'procedure TC.Foo; begin end;'                    + NL +
    'function TC.Bar: Int32; begin Result := 1; end;' + NL +
    'class procedure TC.Baz; begin end;'              + NL +
    'procedure Aaa; begin end;'                       + NL +
    'function Bbb: Int32; begin Result := 2; end;'    + NL +
    'begin'                                           + NL +
    'end.'                                            + NL);
  AssertEquals('twelve headings without ()', 12, CountForRule(R, RULE_ID));
end;

procedure TDeclarationParenthesesTests.TestHeadingsWithParenthesesAreSilent;
var
  R: TReport;
begin
  R := RunDP(
    'program T;'                                          + NL +
    'type'                                                + NL +
    '  TC = class'                                        + NL +
    '    constructor Create();'                           + NL +
    '    procedure Foo();'                                + NL +
    '    function Bar(A: Int32): Int32;'                  + NL +
    '  end;'                                              + NL +
    'constructor TC.Create(); begin end;'                 + NL +
    'procedure TC.Foo(); begin end;'                      + NL +
    'function TC.Bar(A: Int32): Int32; begin Result := A; end;' + NL +
    'procedure Aaa(); begin end;'                         + NL +
    'function Gen<T>(A: T): T; begin Result := A; end;'   + NL +
    'begin'                                               + NL +
    'end.'                                                + NL);
  AssertEquals('nothing to flag', 0, CountForRule(R, RULE_ID));
end;

procedure TDeclarationParenthesesTests.TestSuggestsParentheses;
var
  R: TReport;
  D: TDiagnostic;
begin
  R := RunDP(
    'program T;'                  + NL +
    'procedure TC.Foo; begin end;' + NL +
    'begin'                       + NL +
    'end.'                        + NL);
  D := FirstForRule(R, RULE_ID);
  AssertNotNull('reported', D);
  AssertTrue('message names the routine: ' + D.Message,
    Pos('Foo', D.Message) >= 0);
  AssertEquals('reported on line 2', 2, D.Location.Line);
  AssertEquals('reported at the routine name, not the class', 14,
    D.Location.Col);
  AssertNotNull('has a quick-fix', D.Fix);
  AssertTrue('quick-fix replaces the name', D.Fix.HasReplacement);
  AssertEquals('replacement', 'Foo()', D.Fix.Replacement);
end;

procedure TDeclarationParenthesesTests.TestGenericHeadingHasNoReplacement;
var
  R: TReport;
  D: TDiagnostic;
begin
  R := RunDP(
    'program T;'                                      + NL +
    'function Make<T>: T; begin Result := Default(T); end;' + NL +
    'begin'                                           + NL +
    'end.'                                            + NL);
  AssertEquals('one finding', 1, CountForRule(R, RULE_ID));
  D := FirstForRule(R, RULE_ID);
  AssertNotNull('has a quick-fix', D.Fix);
  AssertFalse('no textual replacement', D.Fix.HasReplacement);
end;

procedure TDeclarationParenthesesTests.TestProceduralTypesAndAnonymousMethodsAreSilent;
var
  R: TReport;
begin
  R := RunDP(
    'program T;'                                   + NL +
    'type'                                         + NL +
    '  TProc = procedure;'                         + NL +
    '  TFunc = function: Int32;'                   + NL +
    '  TMeth = procedure of object;'               + NL +
    '  TRef = reference to procedure;'             + NL +
    'var'                                          + NL +
    '  P: TRef;'                                   + NL +
    'begin'                                        + NL +
    '  P := procedure begin end;'                  + NL +
    'end.'                                         + NL);
  AssertEquals('no routine headings', 0, CountForRule(R, RULE_ID));
end;

procedure TDeclarationParenthesesTests.TestOffByDefault;
var
  Cfg: TGuardConfig;
begin
  Cfg := TGuardConfig.Default();
  AssertFalse('built-in default', Cfg.IsEnabled(RULE_ID));
  Cfg := TGuardConfig.LoadFromString(
    '{ "rules": { "BL-1001": { "enabled": true } } }');
  AssertFalse('unlisted in a config file', Cfg.IsEnabled(RULE_ID));
  Cfg := TGuardConfig.LoadFromString(
    '{ "rules": { "BL-1007": { "enabled": true } } }');
  AssertTrue('a config file can turn it on', Cfg.IsEnabled(RULE_ID));
end;

initialization
  RegisterTest(TDeclarationParenthesesTests);

end.
