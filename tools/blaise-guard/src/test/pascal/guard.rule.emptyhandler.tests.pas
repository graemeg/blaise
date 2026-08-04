{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-2005 EmptyHandler (AST path, end-to-end). }

unit Guard.Rule.EmptyHandler.Tests;

interface

uses
  blaise.testing;

type
  TEmptyHandlerTests = class(TTestCase)
  published
    procedure TestFlagsEmptyExcept;
    procedure TestFlagsEmptyFinally;
    procedure TestNonEmptyExceptIsSilent;
    procedure TestNonEmptyFinallyIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-2005';

function RunEH(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TEmptyHandlerTests.TestFlagsEmptyExcept;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'        + NL +
    'begin'             + NL +
    '  try'             + NL +
    '    WriteLn(1);'   + NL +
    '  except'          + NL +
    '  end;'            + NL +
    'end.'              + NL;
  R := RunEH(Src);
  AssertEquals('swallowed exception', 1, CountForRule(R, RULE_ID));
end;

procedure TEmptyHandlerTests.TestFlagsEmptyFinally;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'        + NL +
    'begin'             + NL +
    '  try'             + NL +
    '    WriteLn(1);'   + NL +
    '  finally'         + NL +
    '  end;'            + NL +
    'end.'              + NL;
  R := RunEH(Src);
  AssertEquals('empty finally', 1, CountForRule(R, RULE_ID));
end;

procedure TEmptyHandlerTests.TestNonEmptyExceptIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'        + NL +
    'begin'             + NL +
    '  try'             + NL +
    '    WriteLn(1);'   + NL +
    '  except'          + NL +
    '    WriteLn(2);'   + NL +
    '  end;'            + NL +
    'end.'              + NL;
  R := RunEH(Src);
  AssertEquals('handler does something', 0, CountForRule(R, RULE_ID));
end;

procedure TEmptyHandlerTests.TestNonEmptyFinallyIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'        + NL +
    'begin'             + NL +
    '  try'             + NL +
    '    WriteLn(1);'   + NL +
    '  finally'         + NL +
    '    WriteLn(2);'   + NL +
    '  end;'            + NL +
    'end.'              + NL;
  R := RunEH(Src);
  AssertEquals('finally does something', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TEmptyHandlerTests);

end.
