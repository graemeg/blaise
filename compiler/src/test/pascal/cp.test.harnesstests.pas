{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.harnesstests;

{ Tests for the shared unit-test harness (cp.test.harness). }

interface

uses
  SysUtils, blaise.testing, uAST, uSemantic, cp.test.harness;

type
  THarnessTests = class(TTestCase)
  published
    procedure TestAnalyse_ReturnsAnnotatedProgram;
    procedure TestAnalyse_SemanticError_Raises;
    procedure TestSemanticError_AcceptedProgram_IsEmpty;
    procedure TestSemanticError_ReportsTheMessage;
    procedure TestGenAsm_X86_64_EmitsX86;
    procedure TestGenAsm_Arm64_EmitsArm64;
    procedure TestGenAsm_UnknownTarget_Raises;
    procedure TestGenAsmDebug_KeepsLocalsInSlots;
    procedure TestGenAsmWithUnit_BothTargets;
    procedure TestAsmMissing_BothPresent_IsEmpty;
    procedure TestAsmMissing_NamesEachMissingTarget;
  end;

implementation

const
  SrcHello = '''
    program P;
    var X: Integer;
    begin
      X := 41;
      WriteLn(X + 1)
    end.
    ''';

procedure THarnessTests.TestAnalyse_ReturnsAnnotatedProgram;
var
  Prog: TProgram;
begin
  Prog := Analyse(SrcHello);
  try
    AssertTrue('program returned', Prog <> nil);
    AssertTrue('symbol table attached', Prog.SymbolTable <> nil);
  finally
    Prog.Free();
  end;
end;

procedure THarnessTests.TestAnalyse_SemanticError_Raises;
var
  Raised: Boolean;
  Prog: TProgram;
begin
  Raised := False;
  try
    Prog := Analyse('program P; var x: Foobar; begin end.');
    Prog.Free();
  except
    on E: ESemanticError do
      Raised := True;
  end;
  AssertTrue('ESemanticError raised', Raised);
end;

procedure THarnessTests.TestSemanticError_AcceptedProgram_IsEmpty;
begin
  AssertEquals('no error', '', SemanticError(SrcHello));
end;

procedure THarnessTests.TestSemanticError_ReportsTheMessage;
var
  Msg: string;
begin
  Msg := SemanticError('program P; var x: Foobar; begin end.');
  AssertTrue('names the unknown type: ' + Msg, Pos('Foobar', Msg) >= 0);
end;

procedure THarnessTests.TestGenAsm_X86_64_EmitsX86;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcHello, TargetX86_64);
  AssertTrue('x86-64 frame register', Pos('%rbp', AsmT) >= 0);
  AssertTrue('no arm64 frame record', Pos('x29', AsmT) < 0);
end;

procedure THarnessTests.TestGenAsm_Arm64_EmitsArm64;
var
  AsmT: string;
begin
  AsmT := GenAsm(SrcHello, TargetArm64);
  AssertTrue('arm64 frame record', Pos('x29', AsmT) >= 0);
  AssertTrue('no x86-64 registers', Pos('%rbp', AsmT) < 0);
end;

procedure THarnessTests.TestGenAsm_UnknownTarget_Raises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    GenAsm(SrcHello, 'plan9-mips');
  except
    on E: Exception do
      Raised := Pos('plan9-mips', E.Message) >= 0;
  end;
  AssertTrue('unknown target rejected by name', Raised);
end;

procedure THarnessTests.TestGenAsmDebug_KeepsLocalsInSlots;
const
  { A hot loop whose locals the optimising build promotes to callee-saved
    registers; a debug build keeps them in their frame slots. }
  Src = '''
    program P;
    function Sum(N: Integer): Integer;
    var I, S: Integer;
    begin
      S := 0;
      for I := 1 to N do
        S := S + I;
      Result := S
    end;
    begin
      WriteLn(Sum(10))
    end.
    ''';
begin
  AssertTrue('debug output differs from the optimised output',
    GenAsmDebug(Src, TargetX86_64) <> GenAsm(Src, TargetX86_64));
end;

procedure THarnessTests.TestGenAsmWithUnit_BothTargets;
const
  UnitSrc = '''
    unit mathu;
    interface
    function AddTwo(A, B: Int64): Int64;
    implementation
    function AddTwo(A, B: Int64): Int64;
    begin
      Result := A + B
    end;
    end.
    ''';
  ProgSrc = '''
    program P;
    uses mathu;
    begin
      WriteLn(AddTwo(20, 22))
    end.
    ''';
var
  AsmT: string;
begin
  AsmT := GenAsmWithUnit(UnitSrc, ProgSrc, TargetX86_64);
  AssertTrue('x86-64: unit routine defined', Pos('mathu_AddTwo:', AsmT) >= 0);
  AssertTrue('x86-64: cross-unit call', Pos('call', AsmT) >= 0);
  AsmT := GenAsmWithUnit(UnitSrc, ProgSrc, TargetArm64);
  AssertTrue('arm64: unit routine defined', Pos('mathu_AddTwo:', AsmT) >= 0);
  AssertTrue('arm64: cross-unit call', Pos(#9'bl _mathu_AddTwo', AsmT) >= 0);
end;

procedure THarnessTests.TestAsmMissing_BothPresent_IsEmpty;
begin
  AssertEquals('both patterns present', '',
    AsmMissing(SrcHello, '%rbp', 'x29'));
end;

procedure THarnessTests.TestAsmMissing_NamesEachMissingTarget;
var
  Msg: string;
begin
  Msg := AsmMissing(SrcHello, 'no-such-x86', 'x29');
  AssertEquals('only x86-64 missing',
    'linux-x86_64 lacks [no-such-x86]', Msg);
  Msg := AsmMissing(SrcHello, 'no-such-x86', 'no-such-arm');
  AssertEquals('both missing',
    'linux-x86_64 lacks [no-such-x86]; macos-arm64 lacks [no-such-arm]', Msg);
end;

initialization
  RegisterTest(THarnessTests);

end.
