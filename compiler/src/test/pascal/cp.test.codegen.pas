{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.codegen;

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.harness;

type
  TCodeGenTests = class(TTestCase)
  private
    function GenerateNativeAsm(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    { Data sections }

    { Main function structure }
    procedure TestMain_Native_CallsBlaiseInit;

    { x86-64 float comparisons are IEEE-correct with a NaN operand: = also
      requires parity clear, <> also accepts parity set, and < / <= compare
      the swapped operands with above / above-or-equal -- in a value and in
      a branch condition }
    procedure TestFloatCompare_X86_NaNSafe;

    { WriteLn }

    { Variables and assignment }

    { Arithmetic }

    { Header comment }

    { String equality }

    { True / False built-in constants }

    { Case-insensitive identifier normalisation }

    { Int64 to Double conversion }

    { Integer → Double/Single implicit assignment }

    { Integer→float conversion on a CLASS-FIELD store target (not just a
      simple variable).  Regression: the field-store path emitted a bare
      integer store into the float slot. }
  end;

implementation

function TCodeGenTests.GenerateNativeAsm(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenNative;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenNative.Create();
  try
    CG.SetTarget(HostTarget());
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TCodeGenTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) >= 0;
end;

{ The native backend must also emit the _BlaiseInit call (right after
  _SetArgs, which it must follow because _BlaiseInit clobbers the SysV arg
  registers).  Guards against a backend skew where only one backend wires
  up the RTL startup hook. }
procedure TCodeGenTests.TestMain_Native_CallsBlaiseInit;
var
  Asm_: string;
  Call: string;
begin
  Asm_ := GenerateNativeAsm('program P; begin end.');
  { GenerateNativeAsm targets the HOST, so the call mnemonic is the host's:
    x86-64 emits `callq _Sym`, arm64 `bl _Sym`.  Asserting one host's syntax
    made this fail on macOS arm64 for no reason — the invariant under test is
    that main calls both, in that order, and that holds on either.  Select the
    mnemonic from the host target rather than gating the test away, so arm64
    keeps the coverage. }
  if HostTarget().CPU = cpuArm64 then
    Call := 'bl '
  else
    Call := 'callq ';
  { The PREFIX follows the target OS, not the CPU.  These RTL routines are named
    _BlaiseInit / _SetArgs in Pascal, and on Darwin every symbol takes one more
    '_' (Apple's C prefix, uniform with QBE), so the label is __BlaiseInit
    there and _BlaiseInit on ELF. }
  if HostTarget().OS = osMacOS then
    Call := Call + '__'
  else
    Call := Call + '_';
  AssertTrue('native main calls _BlaiseInit',
    IRContains(Asm_, Call + 'BlaiseInit'));
  AssertTrue('native main calls _SetArgs',
    IRContains(Asm_, Call + 'SetArgs'));
  { _SetArgs must precede _BlaiseInit. }
  AssertTrue('_SetArgs precedes _BlaiseInit',
    Pos(Call + 'SetArgs', Asm_) < Pos(Call + 'BlaiseInit', Asm_));
end;

{ Header comment }

procedure TCodeGenTests.TestFloatCompare_X86_NaNSafe;
const
  SrcValue = '''
    program P;
    var A, B: Float64; E, N, L, LE: Boolean;
    begin
      E := A = B; N := A <> B; L := A < B; LE := A <= B
    end.
    ''';
  SrcBranch = '''
    program P;
    var A, B: Float64;
    begin
      if A = B then WriteLn(1);
      if A <> B then WriteLn(2);
      if A < B then WriteLn(3)
    end.
    ''';
var
  V, Br: string;
begin
  V := GenAsm(SrcValue, TargetX86_64);
  AssertTrue('= is ZF and not PF', Pos(#9'sete %al' + #10 + #9'setnp %cl' +
    #10 + #9'andl %ecx, %eax', V) >= 0);
  AssertTrue('<> is not ZF or PF', Pos(#9'setne %al' + #10 + #9'setp %cl' +
    #10 + #9'orl %ecx, %eax', V) >= 0);
  AssertTrue('< and <= compare the swapped operands',
    Pos(#9'ucomisd %xmm1, %xmm0' + #10 + #9'seta %al', V) >= 0);
  AssertTrue('no setb / setbe: they are true when unordered',
    (Pos(#9'setb %al', V) < 0) and (Pos(#9'setbe %al', V) < 0));
  Br := GenAsm(SrcBranch, TargetX86_64);
  AssertTrue('= branches false on parity first', Pos(#9'jp .L', Br) >= 0);
  AssertTrue('no jb / jbe on a float compare',
    (Pos(#9'jb .L', Br) < 0) and (Pos(#9'jbe .L', Br) < 0));
end;

initialization
  RegisterTest(TCodeGenTests);

end.
