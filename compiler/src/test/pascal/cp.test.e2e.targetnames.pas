{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.targetnames;

{ TargetOS / TargetCPU end to end: the compiled program prints the
  target it was built for.  The expected strings come from the same
  TargetName() the compiler uses, applied to the target the e2e harness
  compiles for. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.e2e.base, blaise.codegen.target;

type
  TE2ETargetNamesTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_PrintsOwnTarget;
    procedure TestRun_InConstAndConcatenation;
    { A unit may declare a routine, variable or type named like a System
      constant; a program that uses the unit sees the unit's declaration. }
    procedure TestRun_UnitDeclarations_ShadowSystemConstants;
    { A unit that does not use the shadowing unit still sees System's
      constant -- cold, and again when the units load from the cache. }
    procedure TestRun_UnitNotUsingShadower_SeesSystemConstant;
  end;

implementation

procedure TE2ETargetNamesTests.SetUp;
begin
  inherited SetUp();
  Self.SetUpScratch('compiler/target/test-e2e-targetnames');
end;

procedure TE2ETargetNamesTests.TestRun_PrintsOwnTarget;
const
  Src =
    'program p;'#10 +
    'begin'#10 +
    '  WriteLn(TargetOS, ''-'', TargetCPU);'#10 +
    'end.'#10;
var
  Output: string;
  RCode: Int;
  OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  OK := CompileAndRun(Src, Output, RCode);
  AssertTrue('compile+run: ' + Output, OK);
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('the target the program was built for',
    TargetName(E2ETargetDesc()) + LineEnding, Output);
end;

procedure TE2ETargetNamesTests.TestRun_InConstAndConcatenation;
const
  Src =
    'program p;'#10 +
    'const Tag = ''on '' + TargetOS;'#10 +
    'function Describe(): string;'#10 +
    'begin'#10 +
    '  Result := Tag + '' '' + TargetCPU;'#10 +
    'end;'#10 +
    'begin'#10 +
    '  WriteLn(Describe());'#10 +
    'end.'#10;
var
  Output: string;
  RCode: Int;
  OK: Boolean;
  Full: string;
  Dash: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  OK := CompileAndRun(Src, Output, RCode);
  AssertTrue('compile+run: ' + Output, OK);
  AssertEquals('exit 0', 0, RCode);
  Full := TargetName(E2ETargetDesc());
  Dash := Pos('-', Full);
  AssertEquals('const + concatenation fold per target',
    'on ' + Copy(Full, 0, Dash) + ' ' + Copy(Full, Dash + 1, Length(Full) - Dash - 1) + LineEnding,
    Output);
end;

{ The target's OS token: the part of TargetName before the dash. }
function TargetOSPart: string;
var
  Full: string;
begin
  Full := TargetName(E2ETargetDesc());
  Result := Copy(Full, 0, Pos('-', Full));
end;

procedure TE2ETargetNamesTests.TestRun_UnitDeclarations_ShadowSystemConstants;
const
  UnitR =
    'unit shadowr;'#10 +
    'interface'#10 +
    'function TargetOS: string;'#10 +
    'var TargetCPU: string;'#10 +
    'implementation'#10 +
    'function TargetOS: string;'#10 +
    'begin'#10 +
    '  Result := ''routine'';'#10 +
    'end;'#10 +
    'end.'#10;
  UnitT =
    'unit shadowt;'#10 +
    'interface'#10 +
    'type DirectorySeparator = Int32;'#10 +
    'implementation'#10 +
    'end.'#10;
  Src =
    'program p;'#10 +
    'uses shadowr, shadowt;'#10 +
    'var X: DirectorySeparator;'#10 +
    'begin'#10 +
    '  TargetCPU := ''variable'';'#10 +
    '  X := 7;'#10 +
    '  WriteLn(TargetOS(), '' '', TargetCPU, '' '', X);'#10 +
    '  WriteLn(System.TargetOS, ''-'', System.TargetCPU);'#10 +
    'end.'#10;
var
  Output: string;
  RCode: Int;
  OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  OK := CompileAndRunWithUnits(UnitR, UnitT, Src, Output, RCode);
  AssertTrue('compile+run: ' + Output, OK);
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('the unit''s declarations win; System.X still reaches System',
    'routine variable 7' + LineEnding + TargetName(E2ETargetDesc()) +
    LineEnding, Output);
end;

procedure TE2ETargetNamesTests.TestRun_UnitNotUsingShadower_SeesSystemConstant;
const
  { ua is analysed first, so its names hold the flat slots while ub, which
    does not use it, is analysed }
  UnitA =
    'unit shadowa;'#10 +
    'interface'#10 +
    'const TargetCPU = ''cpu-a'';'#10 +
    'function TargetOS: string;'#10 +
    'implementation'#10 +
    'function TargetOS: string;'#10 +
    'begin'#10 +
    '  Result := ''os-a'';'#10 +
    'end;'#10 +
    'end.'#10;
  UnitB =
    'unit shadowb;'#10 +
    'interface'#10 +
    'function BSees: string;'#10 +
    'implementation'#10 +
    'function BSees: string;'#10 +
    'begin'#10 +
    '  Result := TargetOS + ''/'' + TargetCPU;'#10 +
    'end;'#10 +
    'end.'#10;
  Src =
    'program p;'#10 +
    'uses shadowa, shadowb;'#10 +
    'begin'#10 +
    '  WriteLn(TargetOS(), '' '', TargetCPU);'#10 +
    '  WriteLn(BSees());'#10 +
    'end.'#10;
var
  Output, Expected: string;
  RCode, Pass: Int;
  OK: Boolean;
  Full: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Full := TargetName(E2ETargetDesc());
  Expected := 'os-a cpu-a' + LineEnding +
    TargetOSPart() + '/' + Copy(Full, Pos('-', Full) + 1, Length(Full) - Pos('-', Full) - 1) +
    LineEnding;
  { pass 0 compiles the units from source, pass 1 loads them from the cache }
  for Pass := 0 to 1 do
  begin
    OK := CompileAndRunWithUnits(UnitA, UnitB, Src, Output, RCode);
    AssertTrue('pass ' + IntToStr(Pass) + ' compile+run: ' + Output, OK);
    AssertEquals('pass ' + IntToStr(Pass) + ' exit 0', 0, RCode);
    AssertEquals('pass ' + IntToStr(Pass) +
      ': shadowb sees System, the program sees shadowa', Expected, Output);
  end;
end;

initialization
  RegisterTest(TE2ETargetNamesTests);

end.
