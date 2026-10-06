{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.control;

{ Tests for control flow: if/else, comparison operators, compound statements.
  Future: while, repeat, for. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TControlTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_If_Keyword;
    procedure TestLexer_Then_Keyword;
    procedure TestLexer_Else_Keyword;
    procedure TestLexer_Equals_CompareOp;
    procedure TestLexer_NotEquals;
    procedure TestLexer_LessThan;
    procedure TestLexer_GreaterThan;
    procedure TestLexer_LessEqual;
    procedure TestLexer_GreaterEqual;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_If_IsIfStmt;
    procedure TestParse_If_HasCondition;
    procedure TestParse_If_ConditionIsBinaryExpr;
    procedure TestParse_If_NoElse;
    procedure TestParse_IfElse_HasElseStmt;
    procedure TestParse_If_ThenIsAssignment;
    procedure TestParse_IfElse_ElseIsAssignment;
    procedure TestParse_Compound_IsCompoundStmt;
    procedure TestParse_Compound_StmtCount;
    procedure TestParse_If_ThenIsCompound;
    procedure TestParse_IfElse_ElseIsCompound;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_If_Resolves;
    procedure TestSemantic_IfElse_Resolves;
    procedure TestSemantic_Comparison_EQ_TypeIsBoolean;
    procedure TestSemantic_Comparison_NE_TypeIsBoolean;
    procedure TestSemantic_Comparison_LT_TypeIsBoolean;
    procedure TestSemantic_Comparison_GT_TypeIsBoolean;
    procedure TestSemantic_Comparison_LE_TypeIsBoolean;
    procedure TestSemantic_Comparison_GE_TypeIsBoolean;
    procedure TestSemantic_Comparison_TypeMismatch_RaisesError;
    procedure TestSemantic_If_NonBooleanCondition_RaisesError;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { While loops                                                          }
    { ------------------------------------------------------------------ }
    procedure TestLexer_While_Keyword;
    procedure TestLexer_Do_Keyword;
    procedure TestParse_While_IsWhileStmt;
    procedure TestParse_While_HasCondition;
    procedure TestParse_While_BodyIsAssignment;
    procedure TestParse_While_CompoundBody;
    procedure TestSemantic_While_Resolves;
    procedure TestSemantic_While_NonBooleanCondition_RaisesError;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TControlTests.ParseSrc(const ASrc: string): TProgram;
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

function TControlTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

procedure TControlTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcIfOnly =
    '''
        program P;
        var N: Integer;
        begin
          N := 5;
          if N = 5 then
            N := 1
        end.
        ''';

  SrcIfElse =
    '''
        program P;
        var N: Integer;
        begin
          N := 3;
          if N > 0 then
            N := 1
          else
            N := 0
        end.
        ''';

  SrcCompound =
    '''
        program P;
        var N: Integer;
        begin
          N := 10;
          if N > 5 then
          begin
            WriteLn(N);
            N := 0
          end
          else
          begin
            N := 1
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                         }
{ ------------------------------------------------------------------ }

procedure TControlTests.TestLexer_If_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('if');
  try
    T := L.Next();
    AssertEquals('if token', Ord(tkIf), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_Then_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('then');
  try
    T := L.Next();
    AssertEquals('then token', Ord(tkThen), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_Else_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('else');
  try
    T := L.Next();
    AssertEquals('else token', Ord(tkElse), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_Equals_CompareOp;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('=');
  try
    T := L.Next();
    AssertEquals('equals token', Ord(tkEquals), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_NotEquals;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('<>');
  try
    T := L.Next();
    AssertEquals('<> token', Ord(tkNotEquals), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_LessThan;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('<');
  try
    T := L.Next();
    AssertEquals('< token', Ord(tkLessThan), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_GreaterThan;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('>');
  try
    T := L.Next();
    AssertEquals('> token', Ord(tkGreaterThan), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_LessEqual;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('<=');
  try
    T := L.Next();
    AssertEquals('<= token', Ord(tkLessEqual), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_GreaterEqual;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('>=');
  try
    T := L.Next();
    AssertEquals('>= token', Ord(tkGreaterEqual), Ord(T.Kind));
  finally L.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                        }
{ ------------------------------------------------------------------ }

procedure TControlTests.TestParse_If_IsIfStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcIfOnly);
  try
    AssertTrue('second stmt is TIfStmt', Prog.Block.Stmts[1] is TIfStmt);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_If_HasCondition;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcIfOnly);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertNotNull('condition not nil', S.Condition);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_If_ConditionIsBinaryExpr;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcIfOnly);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertTrue('condition is TBinaryExpr', S.Condition is TBinaryExpr);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_If_NoElse;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcIfOnly);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertNull('no else stmt', S.ElseStmt);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_IfElse_HasElseStmt;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcIfElse);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertNotNull('else stmt present', S.ElseStmt);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_If_ThenIsAssignment;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcIfOnly);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertTrue('then is TAssignment', S.ThenStmt is TAssignment);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_IfElse_ElseIsAssignment;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcIfElse);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertTrue('else is TAssignment', S.ElseStmt is TAssignment);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_Compound_IsCompoundStmt;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcCompound);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertTrue('then is TCompoundStmt', S.ThenStmt is TCompoundStmt);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_Compound_StmtCount;
var Prog: TProgram; S: TIfStmt; C: TCompoundStmt;
begin
  Prog := ParseSrc(SrcCompound);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    C := TCompoundStmt(S.ThenStmt);
    AssertEquals('two stmts in then block', 2, C.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_If_ThenIsCompound;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcCompound);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertTrue('then is TCompoundStmt', S.ThenStmt is TCompoundStmt);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_IfElse_ElseIsCompound;
var Prog: TProgram; S: TIfStmt;
begin
  Prog := ParseSrc(SrcCompound);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertTrue('else is TCompoundStmt', S.ElseStmt is TCompoundStmt);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TControlTests.TestSemantic_If_Resolves;
begin
  AnalyseSrc(SrcIfOnly).Free();
end;

procedure TControlTests.TestSemantic_IfElse_Resolves;
begin
  AnalyseSrc(SrcIfElse).Free();
end;

procedure TControlTests.TestSemantic_Comparison_EQ_TypeIsBoolean;
var
  Prog: TProgram;
  S:    TIfStmt;
begin
  Prog := AnalyseSrc(SrcIfOnly);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertNotNull('condition resolved type', S.Condition.ResolvedType);
    AssertEquals('condition is Boolean',
      Ord(tyBoolean), Ord(S.Condition.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TControlTests.TestSemantic_Comparison_NE_TypeIsBoolean;
var
  Prog: TProgram;
  S:    TIfStmt;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        var N: Integer;
        begin
          N := 1;
          if N <> 0 then
            N := 0
        end.
        ''');
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertEquals('NE result is Boolean',
      Ord(tyBoolean), Ord(S.Condition.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TControlTests.TestSemantic_Comparison_LT_TypeIsBoolean;
var
  Prog: TProgram;
  S:    TIfStmt;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        var N: Integer;
        begin
          N := 1;
          if N < 5 then
            N := 0
        end.
        ''');
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertEquals('LT result is Boolean',
      Ord(tyBoolean), Ord(S.Condition.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TControlTests.TestSemantic_Comparison_GT_TypeIsBoolean;
var
  Prog: TProgram;
  S:    TIfStmt;
begin
  Prog := AnalyseSrc(SrcIfElse);
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertEquals('GT result is Boolean',
      Ord(tyBoolean), Ord(S.Condition.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TControlTests.TestSemantic_Comparison_LE_TypeIsBoolean;
var
  Prog: TProgram;
  S:    TIfStmt;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        var N: Integer;
        begin
          N := 1;
          if N <= 5 then
            N := 0
        end.
        ''');
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertEquals('LE result is Boolean',
      Ord(tyBoolean), Ord(S.Condition.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TControlTests.TestSemantic_Comparison_GE_TypeIsBoolean;
var
  Prog: TProgram;
  S:    TIfStmt;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        var N: Integer;
        begin
          N := 1;
          if N >= 1 then
            N := 0
        end.
        ''');
  try
    S := TIfStmt(Prog.Block.Stmts[1]);
    AssertEquals('GE result is Boolean',
      Ord(tyBoolean), Ord(S.Condition.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TControlTests.TestSemantic_Comparison_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        begin
          N := 1;
          if N = 'hello' then
            N := 0
        end.
        ''');
end;

procedure TControlTests.TestSemantic_If_NonBooleanCondition_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        begin
          N := 1;
          if N then
            N := 0
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ Code generation tests                                               }
{ ------------------------------------------------------------------ }

{ How if/else, comparisons and while lower is checked by running programs:
  TE2EControlFlowTests.TestRun_IfElse_TakesEachBranch,
  TestRun_IntegerCompare_Signed and TestRun_While_PrintsRange.  An IR or
  asm substring check adds nothing a wrong lowering could get past those. }

{ ------------------------------------------------------------------ }
{ While loop tests                                                    }
{ ------------------------------------------------------------------ }

const
  SrcWhile =
    '''
        program P;
        var N: Integer;
        begin
          N := 5;
          while N > 0 do
            N := N - 1
        end.
        ''';

  SrcWhileCompound =
    '''
        program P;
        var N, S: Integer;
        begin
          N := 3;
          S := 0;
          while N > 0 do
          begin
            S := S + N;
            N := N - 1
          end
        end.
        ''';

procedure TControlTests.TestLexer_While_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('while');
  try
    T := L.Next();
    AssertEquals('while token', Ord(tkWhile), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestLexer_Do_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('do');
  try
    T := L.Next();
    AssertEquals('do token', Ord(tkDo), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TControlTests.TestParse_While_IsWhileStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcWhile);
  try
    AssertTrue('second stmt is TWhileStmt', Prog.Block.Stmts[1] is TWhileStmt);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_While_HasCondition;
var Prog: TProgram; S: TWhileStmt;
begin
  Prog := ParseSrc(SrcWhile);
  try
    S := TWhileStmt(Prog.Block.Stmts[1]);
    AssertNotNull('condition not nil', S.Condition);
    AssertTrue('condition is TBinaryExpr', S.Condition is TBinaryExpr);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_While_BodyIsAssignment;
var Prog: TProgram; S: TWhileStmt;
begin
  Prog := ParseSrc(SrcWhile);
  try
    S := TWhileStmt(Prog.Block.Stmts[1]);
    AssertTrue('body is TAssignment', S.Body is TAssignment);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestParse_While_CompoundBody;
var Prog: TProgram; S: TWhileStmt;
begin
  Prog := ParseSrc(SrcWhileCompound);
  try
    S := TWhileStmt(Prog.Block.Stmts[2]);
    AssertTrue('body is TCompoundStmt', S.Body is TCompoundStmt);
    AssertEquals('two stmts in body', 2,
      TCompoundStmt(S.Body).Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TControlTests.TestSemantic_While_Resolves;
begin
  AnalyseSrc(SrcWhile).Free();
end;

procedure TControlTests.TestSemantic_While_NonBooleanCondition_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        begin
          N := 1;
          while N do
            N := N - 1
        end.
        ''');
end;

initialization
  RegisterTest(TControlTests);

end.
