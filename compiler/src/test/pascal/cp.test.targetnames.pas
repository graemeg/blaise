{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.targetnames;

{ TargetOS / TargetCPU: string constants of the implicit System unit,
  folded by the compiler from the compilation target (--target), so a program
  can describe the platform it was built for without conditional compilation.

  The values are the canonical spellings of blaise.codegen.target.TargetName:
  OS in linux / freebsd / windows / macos, CPU in x86_64 / i386 / arm64.
  A cross-compiled program reports its TARGET, not the machine it was built
  on.  These tests pin the assembly (the literal is folded, nothing is looked
  up at run time); cp.test.e2e.targetnames runs the program. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.harness;

type
  TTargetNamesTests = class(TTestCase)
  published
    procedure TestConstants_AreStrings;
    procedure TestConstants_AreReadOnly;
    procedure TestOSName_FoldedFromTarget;
    procedure TestCPUName_FoldedFromTarget;
    procedure TestOSName_FreeBSDTarget;
    procedure TestOSName_WindowsTarget;
    procedure TestNames_UsableInConstExpression;
    { A declaration may reuse the name of a System constant: the program's
      own routine, type or variable shadows it, as a constant already did. }
    procedure TestProgramRoutine_ShadowsSystemConstant;
    procedure TestProgramType_ShadowsSystemConstant;
    procedure TestNestedRoutine_ShadowsSystemConstant;
    { ... but not a built-in routine (its calls are dispatched as
      intrinsics), not True/False, and not the program's own name. }
    procedure TestProgramRoutine_CannotShadowBuiltinRoutine;
    procedure TestProgramRoutine_CannotShadowTrue;
    procedure TestProgramRoutine_AfterOwnConst_IsDuplicate;
  end;

implementation

const
  SrcOS =
    'program p;'#10 +
    'begin'#10 +
    '  WriteLn(TargetOS);'#10 +
    'end.'#10;
  SrcCPU =
    'program p;'#10 +
    'begin'#10 +
    '  WriteLn(TargetCPU);'#10 +
    'end.'#10;

procedure TTargetNamesTests.TestConstants_AreStrings;
begin
  AssertEquals('', SemanticError(
    'program p;'#10 +
    'var S: string;'#10 +
    'begin'#10 +
    '  S := TargetOS;'#10 +
    '  S := TargetCPU + ''/'' + TargetOS;'#10 +
    'end.'#10));
end;

procedure TTargetNamesTests.TestConstants_AreReadOnly;
begin
  AssertTrue('assigning to TargetOS is rejected',
    SemanticError(
      'program p;'#10 +
      'begin'#10 +
      '  TargetOS := ''x'';'#10 +
      'end.'#10) <> '');
end;

procedure TTargetNamesTests.TestOSName_FoldedFromTarget;
begin
  { x86-64 asm is generated for linux-x86_64, arm64 for macos-arm64 }
  AssertEquals('', AsmMissing(SrcOS, '.ascii "linux"', '.ascii "macos"'));
end;

procedure TTargetNamesTests.TestCPUName_FoldedFromTarget;
begin
  AssertEquals('', AsmMissing(SrcCPU, '.ascii "x86_64"', '.ascii "arm64"'));
end;

procedure TTargetNamesTests.TestOSName_FreeBSDTarget;
begin
  AssertTrue('freebsd-x86_64 folds "freebsd"',
    Pos('.ascii "freebsd"', GenAsm(SrcOS, 'freebsd-x86_64')) >= 0);
end;

procedure TTargetNamesTests.TestOSName_WindowsTarget;
begin
  AssertTrue('windows-x86_64 folds "windows"',
    Pos('"windows"', GenAsm(SrcOS, 'windows-x86_64')) >= 0);
end;

procedure TTargetNamesTests.TestNames_UsableInConstExpression;
begin
  AssertEquals('', SemanticError(
    'program p;'#10 +
    'const Platform = TargetOS + ''-'' + TargetCPU;'#10 +
    'begin'#10 +
    '  WriteLn(Platform);'#10 +
    'end.'#10));
end;

procedure TTargetNamesTests.TestProgramRoutine_ShadowsSystemConstant;
begin
  AssertEquals('', SemanticError(
    'program p;'#10 +
    'function TargetOS: string;'#10 +
    'begin'#10 +
    '  Result := ''mine'';'#10 +
    'end;'#10 +
    'procedure TargetCPU;'#10 +
    'begin'#10 +
    'end;'#10 +
    'var S: string;'#10 +
    'begin'#10 +
    '  S := TargetOS();'#10 +
    '  TargetCPU();'#10 +
    'end.'#10));
end;

procedure TTargetNamesTests.TestProgramType_ShadowsSystemConstant;
begin
  AssertEquals('', SemanticError(
    'program p;'#10 +
    'type TargetCPU = Int32;'#10 +
    'var X: TargetCPU;'#10 +
    'begin'#10 +
    '  X := 3;'#10 +
    'end.'#10));
end;

procedure TTargetNamesTests.TestNestedRoutine_ShadowsSystemConstant;
begin
  AssertEquals('', SemanticError(
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  function TargetOS: Int32;'#10 +
    '  begin'#10 +
    '    Result := 1;'#10 +
    '  end;'#10 +
    'var N: Int32;'#10 +
    'begin'#10 +
    '  N := TargetOS();'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    'end.'#10));
end;

procedure TTargetNamesTests.TestProgramRoutine_CannotShadowBuiltinRoutine;
begin
  AssertTrue('a built-in routine stays reserved',
    Pos('Duplicate identifier ''WriteLn''', SemanticError(
      'program p;'#10 +
      'procedure WriteLn;'#10 +
      'begin'#10 +
      'end;'#10 +
      'begin'#10 +
      'end.'#10)) >= 0);
end;

procedure TTargetNamesTests.TestProgramRoutine_CannotShadowTrue;
begin
  AssertTrue('True stays reserved',
    Pos('Duplicate identifier ''True''', SemanticError(
      'program p;'#10 +
      'function True: Boolean;'#10 +
      'begin'#10 +
      '  Result := False;'#10 +
      'end;'#10 +
      'begin'#10 +
      'end.'#10)) >= 0);
end;

procedure TTargetNamesTests.TestProgramRoutine_AfterOwnConst_IsDuplicate;
begin
  AssertTrue('the program''s own constant is not a System name',
    Pos('Duplicate identifier ''Tag''', SemanticError(
      'program p;'#10 +
      'const Tag = ''x'';'#10 +
      'function Tag: string;'#10 +
      'begin'#10 +
      '  Result := ''y'';'#10 +
      'end;'#10 +
      'begin'#10 +
      'end.'#10)) >= 0);
end;

initialization
  RegisterTest(TTargetNamesTests);

end.
