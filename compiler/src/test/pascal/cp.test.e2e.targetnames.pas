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

initialization
  RegisterTest(TE2ETargetNamesTests);

end.
