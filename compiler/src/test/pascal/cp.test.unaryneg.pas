{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.unaryneg;

{ Unary minus as its own AST node, TNegExpr.

  The parser used to desugar -A into the binary expression 0 - A.  For
  integers the two agree, but IEEE 754 negation flips the sign bit while
  0.0 - 0.0 is +0.0, so -Z lost the sign of a zero (and of a NaN)
  (BUG-20261026-float-neg-signed-zero).  The desugaring also typed -S of a
  Single as Double (Integer - Single promotes), and left the reserved
  `class operator Negative` unreachable: a record operand arrived as a
  subtraction from an Integer.

  These tests pin the node shape, its typing, the Negative operator
  lowering, the constant evaluators and the per-ISA lowering.  The run-time
  behaviour is in cp.test.e2e.unaryneg. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uUnitInterface,
  uSemanticExport, uUnitInterfaceIO, cp.test.harness;

type
  TUnaryNegTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AssignedExpr(AProg: TProgram; const AName: string): TASTExpr;
    function NegType(const AVarType: string): string;
  published
    { --- parser --- }
    procedure TestParse_UnaryMinus_IsNegExpr;
    { -a * b is (-a) * b and a - -b subtracts a negation, as before }
    procedure TestParse_UnaryMinus_Precedence;
    { --- semantic typing --- }
    { the result type matches what 0 - X gave for every integer kind, and a
      Single stays Single instead of promoting to Double }
    procedure TestSem_Neg_ResultTypes;
    procedure TestSem_Neg_NonNumeric_Rejected;
    { --- class operator Negative --- }
    procedure TestSem_Neg_Record_LowersToNegative;
    procedure TestSem_Neg_Record_WithoutOperator_Rejected;
    { --- constant evaluation --- }
    procedure TestSem_Neg_ConstIndex_OutOfRange_Rejected;
    procedure TestSem_Neg_ConstSubrangeStore_OutOfRange_Rejected;
    { a negated literal or named constant is a legal default value; it was
      rejected as a non-literal while it parsed as 0 - X }
    procedure TestSem_Neg_DefaultValue_Accepted;
    { --- .bif round trip of a negated default value --- }
    procedure TestRoundTrip_NegDefaultValue_Preserved;
    { --- lowering, both ISAs --- }
    procedure TestAsm_NegDouble_FlipsSignBit;
    procedure TestAsm_NegSingle_FlipsSignBit;
    procedure TestAsm_NegInteger_Negates;
    procedure TestAsm_NegInt64_Negates;
  end;

implementation

function TUnaryNegTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

{ The right-hand side of the first assignment to AName in the main block. }
function TUnaryNegTests.AssignedExpr(AProg: TProgram;
  const AName: string): TASTExpr;
var
  I: Int;
  S: TObject;
begin
  Result := nil;
  for I := 0 to AProg.Block.Stmts.Count - 1 do
  begin
    S := TObject(AProg.Block.Stmts.Items[I]);
    if (S is TAssignment) and SameText(TAssignment(S).Name, AName) then
      Exit(TAssignment(S).Expr);
  end;
end;

{ The resolved type name of -V for a variable V of AVarType. }
function TUnaryNegTests.NegType(const AVarType: string): string;
var
  Prog: TProgram;
  E:    TASTExpr;
begin
  Result := '<none>';
  Prog := Analyse('program P; var V: ' + AVarType + '; ' +
    'begin V := -V end.');
  try
    E := Self.AssignedExpr(Prog, 'V');
    if (E <> nil) and (E.ResolvedType <> nil) then
      Result := E.ResolvedType.Name;
  finally
    Prog.Free();
  end;
end;

procedure TUnaryNegTests.TestParse_UnaryMinus_IsNegExpr;
var
  Prog: TProgram;
  E:    TASTExpr;
begin
  Prog := Self.ParseSrc('program P; var X, N: Integer; begin N := -X end.');
  try
    E := Self.AssignedExpr(Prog, 'N');
    AssertTrue('-X is a TNegExpr, not 0 - X', E is TNegExpr);
    AssertTrue('operand is X', TNegExpr(E).Expr is TIdentExpr);
    AssertEquals('operand name', 'X', TIdentExpr(TNegExpr(E).Expr).Name);
  finally
    Prog.Free();
  end;
end;

procedure TUnaryNegTests.TestParse_UnaryMinus_Precedence;
var
  Prog: TProgram;
  E:    TASTExpr;
begin
  Prog := Self.ParseSrc(
    'program P; var A, B, N, M: Integer; begin N := -A * B; M := A - -B end.');
  try
    E := Self.AssignedExpr(Prog, 'N');
    AssertTrue('-A * B is a multiplication', E is TBinaryExpr);
    AssertEquals('op', Ord(boMul), Ord(TBinaryExpr(E).Op));
    AssertTrue('its left is -A', TBinaryExpr(E).Left is TNegExpr);
    E := Self.AssignedExpr(Prog, 'M');
    AssertTrue('A - -B is a subtraction', E is TBinaryExpr);
    AssertEquals('op', Ord(boSub), Ord(TBinaryExpr(E).Op));
    AssertTrue('its right is -B', TBinaryExpr(E).Right is TNegExpr);
  finally
    Prog.Free();
  end;
end;

procedure TUnaryNegTests.TestSem_Neg_ResultTypes;
begin
  { narrow operands are promoted, as 0 - X is (see "Integer Expression
    Width") }
  AssertEquals('Integer', 'Int64', Self.NegType('Integer'));
  AssertEquals('Byte', 'Int64', Self.NegType('Byte'));
  AssertEquals('Int8', 'Int64', Self.NegType('Int8'));
  AssertEquals('SmallInt', 'Int64', Self.NegType('SmallInt'));
  AssertEquals('Word', 'Int64', Self.NegType('Word'));
  AssertEquals('UInt32', 'Int64', Self.NegType('UInt32'));
  AssertEquals('Int64', 'Int64', Self.NegType('Int64'));
  AssertEquals('UInt64', 'UInt64', Self.NegType('UInt64'));
  AssertEquals('Double', 'Double', Self.NegType('Double'));
  AssertEquals('Single stays Single', 'Single', Self.NegType('Single'));
end;

procedure TUnaryNegTests.TestSem_Neg_NonNumeric_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError(
    'program P; var S, T: string; begin T := -S end.');
  AssertTrue('a string operand is rejected: ' + Msg,
    Pos('unary ''-''', Msg) >= 0);
  AssertTrue('the message names the type: ' + Msg, Pos('string', Msg) >= 0);
end;

procedure TUnaryNegTests.TestSem_Neg_Record_LowersToNegative;
const
  Src = '''
    program P;
    type
      TVec = record
        X, Y: Int;
        class operator Negative(const A: TVec): TVec;
      end;
    class operator TVec.Negative(const A: TVec): TVec;
    begin
      Result.X := -A.X;
      Result.Y := -A.Y
    end;
    var V, W: TVec;
    begin
      W := -V
    end.
    ''';
var
  Prog: TProgram;
  E:    TASTExpr;
  Call: TMethodCallExpr;
  MD:   TMethodDecl;
begin
  Prog := Analyse(Src);
  try
    E := Self.AssignedExpr(Prog, 'W');
    AssertTrue('-V lowered to a method call', E is TMethodCallExpr);
    Call := TMethodCallExpr(E);
    AssertEquals('receiver is the owner type', 'TVec', Call.ObjectName);
    AssertEquals('method is the operator', 'Negative', Call.Name);
    AssertTrue('static call', Call.IsStaticCall);
    AssertEquals('one argument', 1, Call.Args.Count);
    MD := TMethodDecl(Call.ResolvedMethod);
    AssertNotNull('resolved method', MD);
    AssertTrue('resolved to okNegative', MD.OperatorKind = okNegative);
    AssertEquals('result type', 'TVec', Call.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TUnaryNegTests.TestSem_Neg_Record_WithoutOperator_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    type
      TVec = record
        X: Int;
        class operator Subtract(const A: Int; const B: TVec): TVec;
      end;
    class operator TVec.Subtract(const A: Int; const B: TVec): TVec;
    begin
      Result.X := A - B.X
    end;
    var V, W: TVec;
    begin
      W := -V
    end.
    ''');
  { -V means Negative; the old desugaring silently ran Subtract(0, V) }
  AssertTrue('no Negative operator is an error: ' + Msg,
    Pos('Negative', Msg) >= 0);
  AssertTrue('the message names the type: ' + Msg, Pos('TVec', Msg) >= 0);
end;

procedure TUnaryNegTests.TestSem_Neg_ConstIndex_OutOfRange_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError(
    'program P; var A: array[0..3] of Integer; begin A[-1] := 0 end.');
  AssertTrue('a negated constant index is still range-checked: ' + Msg,
    Msg <> '');
  AssertEquals('an in-range index is fine', '', SemanticError(
    'program P; var A: array[-2..3] of Integer; begin A[-2] := 0 end.'));
end;

procedure TUnaryNegTests.TestSem_Neg_ConstSubrangeStore_OutOfRange_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError(
    'program P; type TS = 0..10; var S: TS; begin S := -1 end.');
  AssertTrue('a negated constant is range-checked on a subrange store: ' + Msg,
    Msg <> '');
  AssertEquals('-(-3) folds to 3, in range', '', SemanticError(
    'program P; type TS = 0..10; var S: TS; begin S := -(-3) end.'));
end;

procedure TUnaryNegTests.TestSem_Neg_DefaultValue_Accepted;
var
  Msg: string;
begin
  AssertEquals('negated literals and a named constant', '', SemanticError(
    'program P; const K = 4; ' +
    'procedure F(A: Integer = -1; B: Double = -0.5; C: Integer = -K); ' +
    'begin end; begin F() end.'));
  Msg := SemanticError(
    'program P; var V: Integer; ' +
    'procedure F(A: Integer = -V); begin end; begin F() end.');
  AssertTrue('a negated variable is still not a default value: ' + Msg,
    Pos('Default value', Msg) >= 0);
end;

procedure TUnaryNegTests.TestRoundTrip_NegDefaultValue_Preserved;
const
  Src = '''
    unit U;
    interface
    procedure F(A: Int = -1; B: Float64 = -0.0);
    implementation
    procedure F(A: Int; B: Float64); begin end;
    end.
    ''';
var
  Lex:    TLexer;
  Parser: TParser;
  AUnit:  TUnit;
  Iface:  TUnitInterface;
  Back:   TUnitInterface;
  Sig:    TRoutineSig;
  Text:   string;
begin
  Lex := TLexer.Create(Src, '<test>');
  Parser := TParser.Create(Lex);
  AUnit := Parser.ParseUnit();
  try
    Iface := ExportUnitInterface(AUnit, nil);
    try
      Text := WriteUnitInterface(Iface);
    finally
      Iface.Free();
    end;
  finally
    AUnit.Free();
    Parser.Free();
    Lex.Free();
  end;
  Back := ReadUnitInterface(Text);
  try
    Sig := TRoutineSig(Back.Routines.Items[0]);
    AssertTrue('A default is -1 as a negation',
      TMethodParam(Sig.Params.Items[0]).DefaultValue is TNegExpr);
    AssertTrue('B default is -0.0 as a negation',
      TMethodParam(Sig.Params.Items[1]).DefaultValue is TNegExpr);
    AssertTrue('the operand survives',
      TNegExpr(TMethodParam(Sig.Params.Items[1]).DefaultValue).Expr
        is TFloatLiteral);
  finally
    Back.Free();
  end;
end;

procedure TUnaryNegTests.TestAsm_NegDouble_FlipsSignBit;
const
  Src = 'program P; var Z, N: Double; begin Z := 0.0; N := -Z end.';
begin
  AssertEquals('Double negation flips bit 63, never 0.0 - x', '',
    AsmMissing(Src, 'xorq %rcx, %rax', 'fneg d0, d0'));
  AssertTrue('x86-64: no subtraction',
    Pos('subsd', GenAsm(Src, TargetX86_64)) < 0);
  AssertTrue('arm64: no subtraction',
    Pos('fsub', GenAsm(Src, TargetArm64)) < 0);
end;

procedure TUnaryNegTests.TestAsm_NegSingle_FlipsSignBit;
const
  Src = 'program P; var Z, N: Single; begin Z := 0.0; N := -Z end.';
begin
  AssertEquals('Single negation flips bit 31', '',
    AsmMissing(Src, 'xorl $-2147483648, %eax', 'fneg d0, d0'));
  AssertTrue('x86-64: no subtraction',
    Pos('subs', GenAsm(Src, TargetX86_64)) < 0);
end;

procedure TUnaryNegTests.TestAsm_NegInteger_Negates;
const
  Src = 'program P; var X, N: Integer; begin X := 5; N := -X end.';
begin
  AssertEquals('integer negation is a neg', '',
    AsmMissing(Src, 'negq %rax', 'neg x0, x0'));
end;

procedure TUnaryNegTests.TestAsm_NegInt64_Negates;
const
  Src = 'program P; var X, N: Int64; begin X := 5; N := -X end.';
begin
  AssertEquals('Int64 negation is a 64-bit neg', '',
    AsmMissing(Src, 'negq %rax', 'neg x0, x0'));
end;

initialization
  RegisterTest(TUnaryNegTests);

end.
