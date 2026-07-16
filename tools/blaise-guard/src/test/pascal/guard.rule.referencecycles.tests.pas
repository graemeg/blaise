{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for BL-2002 ReferenceCycles.  Exercises the cross-file lifecycle
  (Reset/Analyse/Finalize) and the [Weak]-from-raw-attributes detection via
  AnalyseSourceText. }

unit Guard.Rule.ReferenceCycles.Tests;

interface

uses
  blaise.testing;

type
  TReferenceCyclesTests = class(TTestCase)
  published
    procedure TestFlagsStrongCycle;
    procedure TestWeakBreaksCycle;
    procedure TestAcyclicIsSilent;
  end;

implementation

uses
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL      = #10;
  RULE_ID = 'BL-2002';

function Run(const ASource: string): TReport;
var
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
begin
  Cfg := IsolatedConfig(RULE_ID);
  Eng := TAnalysisEngine.Create(Cfg);
  Result := Eng.AnalyseSourceText('t.pas', ASource);
end;

procedure TReferenceCyclesTests.TestFlagsStrongCycle;
var
  Src: string;
  R:   TReport;
begin
  { TA <-> TB, both edges strong: a leak under ARC. }
  Src :=
    'program T;'      + NL +
    'type'            + NL +
    '  TA = class'    + NL +
    '    B: TB;'      + NL +
    '  end;'          + NL +
    '  TB = class'    + NL +
    '    A: TA;'      + NL +
    '  end;'          + NL +
    'begin'           + NL +
    'end.'            + NL;
  R := Run(Src);
  AssertEquals('one strong cycle', 1, CountForRule(R, RULE_ID));
end;

procedure TReferenceCyclesTests.TestWeakBreaksCycle;
var
  Src: string;
  R:   TReport;
begin
  { The TA -> TB edge is [Weak], so the cycle is broken. }
  Src :=
    'program T;'         + NL +
    'type'               + NL +
    '  TA = class'       + NL +
    '    [Weak] B: TB;'  + NL +
    '  end;'             + NL +
    '  TB = class'       + NL +
    '    A: TA;'         + NL +
    '  end;'             + NL +
    'begin'              + NL +
    'end.'               + NL;
  R := Run(Src);
  AssertEquals('weak edge breaks it', 0, CountForRule(R, RULE_ID));
end;

procedure TReferenceCyclesTests.TestAcyclicIsSilent;
var
  Src: string;
  R:   TReport;
begin
  { TA -> TB, TB references only a non-class type: no cycle. }
  Src :=
    'program T;'      + NL +
    'type'            + NL +
    '  TA = class'    + NL +
    '    B: TB;'      + NL +
    '  end;'          + NL +
    '  TB = class'    + NL +
    '    N: Integer;' + NL +
    '  end;'          + NL +
    'begin'           + NL +
    'end.'            + NL;
  R := Run(Src);
  AssertEquals('acyclic graph', 0, CountForRule(R, RULE_ID));
end;

initialization
  RegisterTest(TReferenceCyclesTests);

end.
