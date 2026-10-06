{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.forloop;

{ Tests for for-loop: to and downto forms. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TForTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_For_Keyword;
    procedure TestLexer_To_Keyword;
    procedure TestLexer_Downto_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_For_IsTForStmt;
    procedure TestParse_For_VarName;
    procedure TestParse_For_IsUpward;
    procedure TestParse_Downto_IsDownward;
    procedure TestParse_For_StartIsIntLiteral;
    procedure TestParse_For_EndIsIntLiteral;
    procedure TestParse_For_BodyIsAssignment;
    procedure TestParse_For_CompoundBody;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_For_Upward_OK;
    procedure TestSemantic_For_Downto_OK;
    procedure TestSemantic_For_NonOrdinalVar_RaisesError;
    procedure TestSemantic_For_StartTypeMismatch_RaisesError;
    procedure TestSemantic_For_EndTypeMismatch_RaisesError;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TForTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
end;

function TForTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

procedure TForTests.AnalyseExpectError(const ASrc: string);
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

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcForUpward =
    '''
        program P;
        var I: Integer;
        var S: Integer;
        begin
          S := 0;
          for I := 1 to 5 do
            S := S + I
        end.
        ''';

  SrcForDownto =
    '''
        program P;
        var I: Integer;
        var S: Integer;
        begin
          S := 0;
          for I := 5 downto 1 do
            S := S + I
        end.
        ''';

  SrcForCompound =
    '''
        program P;
        var I: Integer;
        var S: Integer;
        begin
          S := 0;
          for I := 1 to 3 do
          begin
            S := S + I;
            S := S + 1
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TForTests.TestLexer_For_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('for');
  try
    T := L.Next();
    AssertEquals('for token', Ord(tkFor), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TForTests.TestLexer_To_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('to');
  try
    T := L.Next();
    AssertEquals('to token', Ord(tkTo), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TForTests.TestLexer_Downto_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('downto');
  try
    T := L.Next();
    AssertEquals('downto token', Ord(tkDownto), Ord(T.Kind));
  finally L.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TForTests.TestParse_For_IsTForStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    { second stmt (index 1): for I := 1 to 5 do ... }
    AssertTrue('stmt is TForStmt', Prog.Block.Stmts[1] is TForStmt);
  finally Prog.Free(); end;
end;

procedure TForTests.TestParse_For_VarName;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertEquals('loop var is I', 'I', FS.VarName);
  finally Prog.Free(); end;
end;

procedure TForTests.TestParse_For_IsUpward;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertFalse('to loop: IsDownTo is False', FS.IsDownTo);
  finally Prog.Free(); end;
end;

procedure TForTests.TestParse_Downto_IsDownward;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForDownto);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('downto loop: IsDownTo is True', FS.IsDownTo);
  finally Prog.Free(); end;
end;

procedure TForTests.TestParse_For_StartIsIntLiteral;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('start is TIntLiteral', FS.StartExpr is TIntLiteral);
    AssertEquals('start value = 1', 1, TIntLiteral(FS.StartExpr).Value);
  finally Prog.Free(); end;
end;

procedure TForTests.TestParse_For_EndIsIntLiteral;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('end is TIntLiteral', FS.EndExpr is TIntLiteral);
    AssertEquals('end value = 5', 5, TIntLiteral(FS.EndExpr).Value);
  finally Prog.Free(); end;
end;

procedure TForTests.TestParse_For_BodyIsAssignment;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('body is TAssignment', FS.Body is TAssignment);
  finally Prog.Free(); end;
end;

procedure TForTests.TestParse_For_CompoundBody;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForCompound);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('body is TCompoundStmt', FS.Body is TCompoundStmt);
    AssertEquals('compound body has 2 stmts', 2,
      TCompoundStmt(FS.Body).Stmts.Count);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TForTests.TestSemantic_For_Upward_OK;
begin
  AnalyseSrc(SrcForUpward).Free();
end;

procedure TForTests.TestSemantic_For_Downto_OK;
begin
  AnalyseSrc(SrcForDownto).Free();
end;

procedure TForTests.TestSemantic_For_NonOrdinalVar_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var S: string;
        begin
          for S := 1 to 5 do
            S := S
        end.
        ''');
end;

procedure TForTests.TestSemantic_For_StartTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var I: Integer;
        var S: string;
        begin
          for I := S to 5 do
            I := I
        end.
        ''');
end;

procedure TForTests.TestSemantic_For_EndTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var I: Integer;
        var S: string;
        begin
          for I := 1 to S do
            I := I
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

initialization
  RegisterTest(TForTests);

end.
