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

initialization
  RegisterTest(TTargetNamesTests);

end.
