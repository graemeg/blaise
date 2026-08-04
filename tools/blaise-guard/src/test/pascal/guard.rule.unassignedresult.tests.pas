{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-1006 UnassignedResult (AST path, end-to-end).

  The silent cases encode the exemptions that took the false-positive count on
  compiler/src/main/pascal from 108 to 0: SetLength(Result, N) and friends
  write the result through a var parameter, and an asm body returns through
  the ABI register without touching the Result slot. }

unit Guard.Rule.UnassignedResult.Tests;

interface

uses
  blaise.testing;

type
  TUnassignedResultTests = class(TTestCase)
  published
    procedure TestFlagsNeverAssigned;
    procedure TestDirectAssignIsSilent;
    procedure TestExitValueIsSilent;
    procedure TestSetLengthIsSilent;
    procedure TestProcedureIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-1006';

function RunUR(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TUnassignedResultTests.TestFlagsNeverAssigned;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                       + NL +
    'function F(x: Integer): Integer;' + NL +
    'begin'                            + NL +
    '  if x > 0 then'                  + NL +
    '    WriteLn(x);'                  + NL +
    'end;'                             + NL +
    'begin'                            + NL +
    '  WriteLn(F(1));'                 + NL +
    'end.'                             + NL;
  R := RunUR(Src);
  AssertEquals('never assigns Result', 1, CountForRule(R, RULE_ID));
end;

procedure TUnassignedResultTests.TestDirectAssignIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                       + NL +
    'function F(x: Integer): Integer;' + NL +
    'begin'                            + NL +
    '  Result := x;'                   + NL +
    'end;'                             + NL +
    'begin'                            + NL +
    '  WriteLn(F(1));'                 + NL +
    'end.'                             + NL;
  R := RunUR(Src);
  AssertEquals('assigns Result', 0, CountForRule(R, RULE_ID));
end;

procedure TUnassignedResultTests.TestExitValueIsSilent;
var
  Src: string;
  R:   TReport;
begin
  Src :=
    'program T;'                       + NL +
    'function F(x: Integer): Integer;' + NL +
    'begin'                            + NL +
    '  Exit(x);'                       + NL +
    'end;'                             + NL +
    'begin'                            + NL +
    '  WriteLn(F(1));'                 + NL +
    'end.'                             + NL;
  R := RunUR(Src);
  AssertEquals('Exit(value) assigns', 0, CountForRule(R, RULE_ID));
end;

procedure TUnassignedResultTests.TestSetLengthIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { SetLength(Result, N) writes Result through a var parameter — this shape
    accounted for most of the rule's initial false positives. }
  Src :=
    'program T;'                       + NL +
    'type'                             + NL +
    '  TSA = array of string;'         + NL +
    'function F: TSA;'                 + NL +
    'begin'                            + NL +
    '  SetLength(Result, 1);'          + NL +
    '  Result[0] := ''x'';'            + NL +
    'end;'                             + NL +
    'begin'                            + NL +
    '  WriteLn(F()[0]);'               + NL +
    'end.'                             + NL;
  R := RunUR(Src);
  AssertEquals('SetLength writes Result', 0, CountForRule(R, RULE_ID));
end;

procedure TUnassignedResultTests.TestProcedureIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { A procedure has no Result at all. }
  Src :=
    'program T;'            + NL +
    'procedure P;'          + NL +
    'begin'                 + NL +
    '  WriteLn(1);'         + NL +
    'end;'                  + NL +
    'begin'                 + NL +
    '  P();'                + NL +
    'end.'                  + NL;
  R := RunUR(Src);
  AssertEquals('procedures have no Result', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TUnassignedResultTests);

end.
