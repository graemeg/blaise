{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.methods;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TMethodTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Procedure_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_Method_InClass;
    procedure TestParse_Method_Name;
    procedure TestParse_Method_NoParams;
    procedure TestParse_Method_WithParams;
    procedure TestParse_Method_ParamName;
    procedure TestParse_Method_ParamTypeName;
    procedure TestParse_Method_Body_HasStmt;
    procedure TestParse_MethodCall_Stmt;
    procedure TestParse_MethodCall_WithArgs;
    procedure TestParse_MethodCall_NoArgs;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_MethodCall_Resolves;
    procedure TestSemantic_MethodCall_UnknownMethod_RaisesError;
    procedure TestSemantic_MethodCall_ArgTypeMismatch_RaisesError;
    procedure TestSemantic_MethodCall_WrongArgCount_RaisesError;
    procedure TestSemantic_Method_SelfIsClassType;
    procedure TestSemantic_Method_SelfFieldWrite_OK;
    procedure TestSemantic_Method_ParamResolved;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TMethodTests.ParseSrc(const ASrc: string): TProgram;
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

function TMethodTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TMethodTests.AnalyseExpectError(const ASrc: string);
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
  SrcCounter =
    '''
        program P;
        type
          TCounter = class
            Value: Integer;
            procedure SetValue(AVal: Integer);
            begin
              Self.Value := AVal
            end;
          end;
        var C: TCounter;
        begin
          C := TCounter.Create();
          C.SetValue(42)
        end.
        ''';

  SrcNoParamMethod =
    '''
        program P;
        type
          TFoo = class
            X: Integer;
            procedure Reset;
            begin
              Self.X := 0
            end;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.Reset()
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Lexer                                                               }
{ ------------------------------------------------------------------ }

procedure TMethodTests.TestLexer_Procedure_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('procedure');
  try
    T := L.Next();
    AssertEquals('procedure token', Ord(tkProcedure), Ord(T.Kind));
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TMethodTests.TestParse_Method_InClass;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcCounter);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one method', 1, CD.Methods.Count);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_Method_Name;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcCounter);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[0]);
    AssertEquals('method name', 'SetValue', MD.Name);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_Method_NoParams;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcNoParamMethod);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[0]);
    AssertEquals('zero params', 0, MD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_Method_WithParams;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcCounter);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[0]);
    AssertEquals('one param', 1, MD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_Method_ParamName;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcCounter);
  try
    CD  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD  := TMethodDecl(CD.Methods[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param name', 'AVal', Par.ParamName);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_Method_ParamTypeName;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcCounter);
  try
    CD  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD  := TMethodDecl(CD.Methods[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param type', 'Integer', Par.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_Method_Body_HasStmt;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcCounter);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[0]);
    AssertEquals('body has 1 stmt', 1, MD.Body.Stmts.Count);
    AssertTrue('stmt is TFieldAssignment', MD.Body.Stmts[0] is TFieldAssignment);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_MethodCall_Stmt;
var
  Prog: TProgram;
  Stmt: TMethodCallStmt;
begin
  Prog := ParseSrc(SrcCounter);
  try
    { second stmt after C := TCounter.Create }
    AssertTrue('second stmt is TMethodCallStmt',
      Prog.Block.Stmts[1] is TMethodCallStmt);
    Stmt := TMethodCallStmt(Prog.Block.Stmts[1]);
    AssertEquals('object name', 'C', Stmt.ObjectName);
    AssertEquals('method name', 'SetValue', Stmt.Name);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_MethodCall_WithArgs;
var
  Prog: TProgram;
  Stmt: TMethodCallStmt;
begin
  Prog := ParseSrc(SrcCounter);
  try
    Stmt := TMethodCallStmt(Prog.Block.Stmts[1]);
    AssertEquals('one arg', 1, Stmt.Args.Count);
    AssertTrue('arg is TIntLiteral', Stmt.Args[0] is TIntLiteral);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestParse_MethodCall_NoArgs;
var
  Prog: TProgram;
  Stmt: TMethodCallStmt;
begin
  Prog := ParseSrc(SrcNoParamMethod);
  try
    Stmt := TMethodCallStmt(Prog.Block.Stmts[1]);
    AssertEquals('method name', 'Reset', Stmt.Name);
    AssertEquals('zero args', 0, Stmt.Args.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TMethodTests.TestSemantic_MethodCall_Resolves;
begin
  AnalyseSrc(SrcCounter).Free();
end;

procedure TMethodTests.TestSemantic_MethodCall_UnknownMethod_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.NoSuchMethod()
        end.
        ''');
end;

procedure TMethodTests.TestSemantic_MethodCall_ArgTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
            procedure SetX(AVal: Integer);
            begin
              Self.X := AVal
            end;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.SetX('not an int')
        end.
        ''');
end;

procedure TMethodTests.TestSemantic_MethodCall_WrongArgCount_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
            procedure SetX(AVal: Integer);
            begin
              Self.X := AVal
            end;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.SetX(1, 2)
        end.
        ''');
end;

procedure TMethodTests.TestSemantic_Method_SelfIsClassType;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
  Stmt: TFieldAssignment;
begin
  Prog := AnalyseSrc(SrcCounter);
  try
    CD   := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD   := TMethodDecl(CD.Methods[0]);
    Stmt := TFieldAssignment(MD.Body.Stmts[0]);
    AssertTrue('Self.Value is class access', Stmt.IsClassAccess);
  finally
    Prog.Free();
  end;
end;

procedure TMethodTests.TestSemantic_Method_SelfFieldWrite_OK;
begin
  AnalyseSrc(SrcCounter).Free();
end;

procedure TMethodTests.TestSemantic_Method_ParamResolved;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := AnalyseSrc(SrcCounter);
  try
    CD  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD  := TMethodDecl(CD.Methods[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertNotNull('param type resolved', Par.ResolvedType);
    AssertEquals('param type is Integer',
      Ord(tyInteger), Ord(Par.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TMethodTests);

end.
