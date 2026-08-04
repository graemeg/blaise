{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-2004 OrdSubscript (token path, end-to-end). }

unit Guard.Rule.OrdSubscript.Tests;

interface

uses
  blaise.testing;

type
  TOrdSubscriptTests = class(TTestCase)
  published
    procedure TestFlagsOrdOfSubscript;
    procedure TestStrAtIsSilent;
    procedure TestPlainOrdIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-2004';

function RunOS(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TOrdSubscriptTests.TestFlagsOrdOfSubscript;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'          + NL +
    'var'                 + NL +
    '  s: string;'        + NL +
    '  c: Integer;'       + NL +
    'begin'               + NL +
    '  s := ''x'';'       + NL +
    '  c := Ord(s[0]);'   + NL +
    '  WriteLn(c);'       + NL +
    'end.'                + NL;
  R := RunOS(Src);
  AssertEquals('Ord of a subscript', 1, CountForRule(R, RULE_ID));
end;

procedure TOrdSubscriptTests.TestStrAtIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { The prescribed form. }
  Src :=
    'program T;'          + NL +
    'var'                 + NL +
    '  s: string;'        + NL +
    '  c: Integer;'       + NL +
    'begin'               + NL +
    '  s := ''x'';'       + NL +
    '  c := StrAt(s, 0);' + NL +
    '  WriteLn(c);'       + NL +
    'end.'                + NL;
  R := RunOS(Src);
  AssertEquals('StrAt is the prescribed form', 0, CountForRule(R, RULE_ID));
end;

procedure TOrdSubscriptTests.TestPlainOrdIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { Ord of a non-subscript operand is ordinary and must not report. }
  Src :=
    'program T;'          + NL +
    'var'                 + NL +
    '  b: Boolean;'       + NL +
    '  c: Integer;'       + NL +
    'begin'               + NL +
    '  b := True;'        + NL +
    '  c := Ord(b);'      + NL +
    '  WriteLn(c);'       + NL +
    'end.'                + NL;
  R := RunOS(Src);
  AssertEquals('plain Ord is fine', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TOrdSubscriptTests);

end.
