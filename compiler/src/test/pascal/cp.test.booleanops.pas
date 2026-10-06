{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.booleanops;

{ Tests for the AND / OR / NOT logical operators on Boolean operands. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TBooleanOpsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestLexer_And_Keyword;
    procedure TestLexer_Or_Keyword;
    procedure TestLexer_Not_Keyword;
    procedure TestParse_And_IsBinaryExpr;
    procedure TestParse_Or_IsBinaryExpr;
    procedure TestParse_Not_IsNotExpr;
    procedure TestSemantic_And_TypeIsBoolean;
    procedure TestSemantic_Or_TypeIsBoolean;
    procedure TestSemantic_Not_TypeIsBoolean;
    procedure TestSemantic_And_IntOperand_RaisesError;
    procedure TestSemantic_Not_IntOperand_TypeIsInteger;
    procedure TestSemantic_Not_Int64Operand_TypeIsInt64;
    procedure TestSemantic_Not_ByteOperand_TypeIsInteger;
    procedure TestSemantic_Not_FloatOperand_RaisesError;
    procedure TestSemantic_Xor_TypeIsBoolean;
  end;

implementation

function TBooleanOpsTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try Result := P.Parse(); finally P.Free(); L.Free(); end;
end;

function TBooleanOpsTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try A.Analyse(Result); finally A.Free(); end;
end;

procedure TBooleanOpsTests.AnalyseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

const
  SrcAnd =
    '''
        program P;
        var A, B: Boolean; C: Boolean;
        begin
          A := True;
          B := False;
          C := A and B
        end.
        ''';

  SrcOr =
    '''
        program P;
        var A, B: Boolean; C: Boolean;
        begin
          A := True;
          B := False;
          C := A or B
        end.
        ''';

  SrcNot =
    '''
        program P;
        var A: Boolean; C: Boolean;
        begin
          A := True;
          C := not A
        end.
        ''';

procedure TBooleanOpsTests.TestLexer_And_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('and');
  try T := L.Next(); AssertEquals(Ord(tkAnd), Ord(T.Kind)); finally L.Free(); end;
end;

procedure TBooleanOpsTests.TestLexer_Or_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('or');
  try T := L.Next(); AssertEquals(Ord(tkOr), Ord(T.Kind)); finally L.Free(); end;
end;

procedure TBooleanOpsTests.TestLexer_Not_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('not');
  try T := L.Next(); AssertEquals(Ord(tkNot), Ord(T.Kind)); finally L.Free(); end;
end;

procedure TBooleanOpsTests.TestParse_And_IsBinaryExpr;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := ParseSrc(SrcAnd);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertTrue('and is binary expr', Assn.Expr is TBinaryExpr);
    AssertEquals('and op', Ord(boAnd), Ord(TBinaryExpr(Assn.Expr).Op));
  finally Prog.Free(); end;
end;

procedure TBooleanOpsTests.TestParse_Or_IsBinaryExpr;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := ParseSrc(SrcOr);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertTrue(Assn.Expr is TBinaryExpr);
    AssertEquals(Ord(boOr), Ord(TBinaryExpr(Assn.Expr).Op));
  finally Prog.Free(); end;
end;

procedure TBooleanOpsTests.TestParse_Not_IsNotExpr;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := ParseSrc(SrcNot);
  try
    Assn := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('not is TNotExpr', Assn.Expr is TNotExpr);
  finally Prog.Free(); end;
end;

procedure TBooleanOpsTests.TestSemantic_And_TypeIsBoolean;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc(SrcAnd);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertEquals(Ord(tyBoolean), Ord(Assn.Expr.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TBooleanOpsTests.TestSemantic_Or_TypeIsBoolean;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc(SrcOr);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertEquals(Ord(tyBoolean), Ord(Assn.Expr.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TBooleanOpsTests.TestSemantic_Not_TypeIsBoolean;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc(SrcNot);
  try
    Assn := TAssignment(Prog.Block.Stmts[1]);
    AssertEquals(Ord(tyBoolean), Ord(Assn.Expr.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TBooleanOpsTests.TestSemantic_And_IntOperand_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var I, J: Integer; C: Boolean;
        begin
          I := 1; J := 2;
          C := I and J
        end.
        ''');
end;

procedure TBooleanOpsTests.TestSemantic_Not_IntOperand_TypeIsInteger;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc('''
      program P;
      var I, R: Integer;
      begin
        I := 1;
        R := not I
      end.
      ''');
  Assn := TAssignment(Prog.Block.Stmts[1]);
  AssertTrue('RHS is TNotExpr', Assn.Expr is TNotExpr);
  AssertEquals('type is Integer', 'Integer',
    TNotExpr(Assn.Expr).ResolvedType.Name);
end;

procedure TBooleanOpsTests.TestSemantic_Not_Int64Operand_TypeIsInt64;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc('''
      program P;
      var I, R: Int64;
      begin
        I := 1;
        R := not I
      end.
      ''');
  Assn := TAssignment(Prog.Block.Stmts[1]);
  AssertEquals('type is Int64', 'Int64',
    TNotExpr(Assn.Expr).ResolvedType.Name);
end;

procedure TBooleanOpsTests.TestSemantic_Not_ByteOperand_TypeIsInteger;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc('''
      program P;
      var B: Byte; R: Integer;
      begin
        B := 1;
        R := not B
      end.
      ''');
  Assn := TAssignment(Prog.Block.Stmts[1]);
  AssertEquals('type is Integer', 'Integer',
    TNotExpr(Assn.Expr).ResolvedType.Name);
end;

procedure TBooleanOpsTests.TestSemantic_Not_FloatOperand_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var D: Double; R: Double;
        begin
          D := 1.0;
          R := not D
        end.
        ''');
end;

procedure TBooleanOpsTests.TestSemantic_Xor_TypeIsBoolean;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(
      '''
      program P;
      var A, B, R: Boolean;
      begin
        A := True;
        B := True;
        R := A xor B
      end.
      ''');
  Prog.Free();
end;

initialization
  RegisterTest(TBooleanOpsTests);

end.
