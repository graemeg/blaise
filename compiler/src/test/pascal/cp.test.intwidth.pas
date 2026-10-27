{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.intwidth;

{ Integer expression width (BUG-20261027-int32-overflow-not-wrapped).

  Arithmetic (+ - * div mod, unary minus) and the bitwise and/or/xor on two
  operands narrower than 64 bits are promoted: evaluated in, and typed,
  Int64, so High(Integer) + 1 is 2147483648 whatever consumes it.  A
  constant expression is typed by magnitude, like a literal.  The shifts
  promote an 8- or 16-bit left operand to 32 bits and otherwise keep its
  type, wrapping at that width; not keeps its operand's type.  See
  docs/language-rationale.adoc, "Integer expression width".  The run-time
  values are in cp.test.e2e.intwidth. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat, uAST, cp.test.harness;

type
  TIntWidthTests = class(TTestCase)
  private
    function TypeOf(const AExpr: string; const ATarget: string = 'Int64'): string;
  published
    procedure TestSemantic_IntegerPlusInteger_IsInt64;
    procedure TestSemantic_BytePlusByte_IsInt64;
    procedure TestSemantic_UInt32TimesUInt32_IsInt64;
    procedure TestSemantic_IntegerDivInteger_IsInt64;
    procedure TestSemantic_NegInteger_IsInt64;
    procedure TestSemantic_NegLiteral_IsInteger;
    procedure TestSemantic_ConstExpr_TypedByMagnitude;
    procedure TestSemantic_IntegerAndUInt32_IsInt64;
    procedure TestSemantic_Int64Operand_Unchanged;
    procedure TestSemantic_UInt64Operand_Unchanged;
    procedure TestSemantic_ByteShl_IsUInt32;
    procedure TestSemantic_Int8Shl_IsInteger;
    procedure TestSemantic_IntegerShl_KeepsInteger;
    procedure TestSemantic_UInt32Shr_KeepsUInt32;
    procedure TestSemantic_NotByte_IsByte;
    procedure TestSemantic_NotUInt32_IsUInt32;
    procedure TestAsm_IntegerShr_ZeroExtendsFirst;
    procedure TestAsm_IntegerShl_ResultSignExtended;
    procedure TestAsm_NotByte_ResultZeroExtended;
  end;

implementation

function TIntWidthTests.TypeOf(const AExpr: string; const ATarget: string): string;
var
  Prog: TProgram;
begin
  Prog := Analyse(
    'program P; var I, J: Integer; U, V: UInt32; B, C: Byte; K: Int8; ' +
    'L: Int64; Q: UInt64; R: ' + ATarget + '; ' +
    'begin I := 1; J := 2; U := 1; V := 2; B := 1; C := 2; K := 1; ' +
    'L := 1; Q := 1; R := ' + AExpr + ' end.');
  Result := TAssignment(Prog.Block.Stmts[Prog.Block.Stmts.Count - 1]).Expr.
    ResolvedType.Name;
end;

procedure TIntWidthTests.TestSemantic_IntegerPlusInteger_IsInt64;
begin
  AssertEquals('Int64', TypeOf('I + J'));
  AssertEquals('Int64', TypeOf('I + 1'));
  AssertEquals('Int64', TypeOf('I - J'));
end;

procedure TIntWidthTests.TestSemantic_BytePlusByte_IsInt64;
begin
  AssertEquals('Int64', TypeOf('B + C'));
  AssertEquals('Int64', TypeOf('B + I'));
end;

procedure TIntWidthTests.TestSemantic_UInt32TimesUInt32_IsInt64;
begin
  AssertEquals('Int64', TypeOf('U * V'));
end;

procedure TIntWidthTests.TestSemantic_IntegerDivInteger_IsInt64;
begin
  AssertEquals('Int64', TypeOf('I div J'));
  AssertEquals('Int64', TypeOf('I mod J'));
end;

procedure TIntWidthTests.TestSemantic_NegInteger_IsInt64;
begin
  AssertEquals('Int64', TypeOf('-I'));
end;

procedure TIntWidthTests.TestSemantic_NegLiteral_IsInteger;
begin
  AssertEquals('Integer', TypeOf('-5'));
end;

procedure TIntWidthTests.TestSemantic_ConstExpr_TypedByMagnitude;
begin
  AssertEquals('fits Integer', 'Integer', TypeOf('5 - 1'));
  AssertEquals('does not fit', 'Int64', TypeOf('2147483647 + 1'));
end;

procedure TIntWidthTests.TestSemantic_IntegerAndUInt32_IsInt64;
begin
  AssertEquals('Int64', TypeOf('I and U'));
  AssertEquals('Int64', TypeOf('U or V'));
end;

procedure TIntWidthTests.TestSemantic_Int64Operand_Unchanged;
begin
  AssertEquals('Int64', TypeOf('L + I'));
end;

procedure TIntWidthTests.TestSemantic_UInt64Operand_Unchanged;
begin
  AssertEquals('UInt64', TypeOf('Q + U', 'UInt64'));
end;

procedure TIntWidthTests.TestSemantic_ByteShl_IsUInt32;
begin
  AssertEquals('UInt32', TypeOf('B shl 8'));
end;

procedure TIntWidthTests.TestSemantic_Int8Shl_IsInteger;
begin
  AssertEquals('Integer', TypeOf('K shl 8'));
end;

procedure TIntWidthTests.TestSemantic_IntegerShl_KeepsInteger;
begin
  AssertEquals('Integer', TypeOf('I shl 31'));
end;

procedure TIntWidthTests.TestSemantic_UInt32Shr_KeepsUInt32;
begin
  AssertEquals('UInt32', TypeOf('U shr 1'));
end;

procedure TIntWidthTests.TestSemantic_NotByte_IsByte;
begin
  AssertEquals('Byte', TypeOf('not B'));
end;

procedure TIntWidthTests.TestSemantic_NotUInt32_IsUInt32;
begin
  AssertEquals('UInt32', TypeOf('not U'));
end;

procedure TIntWidthTests.TestAsm_IntegerShr_ZeroExtendsFirst;
const
  Src = 'program P; var I, N: Integer; begin I := -1; N := 1; ' +
    'WriteLn(I shr N) end.';
begin
  AssertEquals('a 32-bit shr zero-extends its operand first', '',
    AsmMissing(Src, 'movl %eax, %eax'#10#9'shrq %cl, %rax',
      'mov w0, w0'#10#9'lsr x0, x0, x1'));
end;

procedure TIntWidthTests.TestAsm_IntegerShl_ResultSignExtended;
const
  Src = 'program P; var I, N: Integer; begin I := 1; N := 31; ' +
    'WriteLn(I shl N) end.';
begin
  AssertEquals('a 32-bit shl result is re-extended from 32 bits', '',
    AsmMissing(Src, 'shlq %cl, %rax'#10#9'movslq %eax, %rax',
      'lsl x0, x0, x1'#10#9'sxtw x0, w0'));
end;

procedure TIntWidthTests.TestAsm_NotByte_ResultZeroExtended;
const
  Src = 'program P; var B: Byte; begin B := 200; WriteLn(not B) end.';
begin
  AssertEquals('not of a Byte is re-extended from 8 bits', '',
    AsmMissing(Src, 'notl %eax'#10#9'movzbq %al, %rax',
      'eor x0, x0, x1'#10#9'lsl x0, x0, #56'#10#9'lsr x0, x0, #56'));
end;

initialization
  RegisterTest(TIntWidthTests);

end.
