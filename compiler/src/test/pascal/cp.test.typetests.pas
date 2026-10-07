{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.typetests;

{ Tests for the 'is' and 'as' type-test operators. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TTypeTestTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Is_Keyword;
    procedure TestLexer_As_Keyword;

    { ------------------------------------------------------------------ }
    { Parser — is                                                          }
    { ------------------------------------------------------------------ }
    procedure TestParse_IsExpr_NodeKind;
    procedure TestParse_IsExpr_TypeName;

    { ------------------------------------------------------------------ }
    { Parser — as                                                          }
    { ------------------------------------------------------------------ }
    procedure TestParse_AsExpr_NodeKind;
    procedure TestParse_AsExpr_TypeName;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IsExpr_ClassInstance_OK;
    procedure TestSemantic_IsExpr_ResultIsBoolean;
    procedure TestSemantic_IsExpr_NonClass_RaisesError;
    procedure TestSemantic_AsExpr_ClassInstance_OK;
    procedure TestSemantic_AsExpr_ResultType_IsTargetClass;
    procedure TestSemantic_AsExpr_NonClass_RaisesError;

    { ------------------------------------------------------------------ }
    { Codegen — typeinfo data sections                                     }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Codegen — is / as expressions                                        }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { ClassType / TClass intrinsic                                         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ClassType_OK;
    procedure TestSemantic_ClassType_ResolvesToPointer;
    procedure TestSemantic_TClass_AliasIsPointer;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  { Base class with one virtual method — has a vtable/vptr }
  SrcBase =
    '''
        program P;
        type
          TAnimal = class
            procedure Speak; virtual; begin end;
          end;
        var A: TAnimal;
            R: Boolean;
        begin
          A := TAnimal.Create();
          R := A is TAnimal
        end.
        ''';

  SrcAsExpr =
    '''
        program P;
        type
          TAnimal = class
            procedure Speak; virtual; begin end;
          end;
          TDog = class(TAnimal)
            procedure Speak; override; begin end;
          end;
        var A: TAnimal;
            D: TDog;
        begin
          A := TDog.Create();
          D := A as TDog
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TTypeTestTests.ParseSrc(const ASrc: string): TProgram;
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

function TTypeTestTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TTypeTestTests.AnalyseExpectError(const ASrc: string);
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
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestLexer_Is_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('is');
  try
    T := L.Next();
    AssertEquals('is token', Ord(tkIs), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TTypeTestTests.TestLexer_As_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('as');
  try
    T := L.Next();
    AssertEquals('as token', Ord(tkAs), Ord(T.Kind));
  finally L.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser — is                                                          }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestParse_IsExpr_NodeKind;
var Prog: TProgram; Stmt: TAssignment;
begin
  Prog := ParseSrc(SrcBase);
  try
    Stmt := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('is expr node kind', Stmt.Expr is TIsExpr);
  finally Prog.Free(); end;
end;

procedure TTypeTestTests.TestParse_IsExpr_TypeName;
var Prog: TProgram; IE: TIsExpr;
begin
  Prog := ParseSrc(SrcBase);
  try
    IE := TIsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertEquals('is type name', 'TAnimal', IE.TypeName);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser — as                                                          }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestParse_AsExpr_NodeKind;
var Prog: TProgram; Stmt: TAssignment;
begin
  Prog := ParseSrc(SrcAsExpr);
  try
    Stmt := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('as expr node kind', Stmt.Expr is TAsExpr);
  finally Prog.Free(); end;
end;

procedure TTypeTestTests.TestParse_AsExpr_TypeName;
var Prog: TProgram; AE: TAsExpr;
begin
  Prog := ParseSrc(SrcAsExpr);
  try
    AE := TAsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertEquals('as type name', 'TDog', AE.TypeName);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestSemantic_IsExpr_ClassInstance_OK;
begin
  AnalyseSrc(SrcBase).Free();
end;

procedure TTypeTestTests.TestSemantic_IsExpr_ResultIsBoolean;
var Prog: TProgram; IE: TIsExpr;
begin
  Prog := AnalyseSrc(SrcBase);
  try
    IE := TIsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('is-expr resolved type', IE.ResolvedType);
    AssertEquals('is-expr result is Boolean', Ord(tyBoolean), Ord(IE.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TTypeTestTests.TestSemantic_IsExpr_NonClass_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var X: Integer;
            R: Boolean;
        begin
          R := X is Integer
        end.
        ''');
end;

procedure TTypeTestTests.TestSemantic_AsExpr_ClassInstance_OK;
begin
  AnalyseSrc(SrcAsExpr).Free();
end;

procedure TTypeTestTests.TestSemantic_AsExpr_ResultType_IsTargetClass;
var Prog: TProgram; AE: TAsExpr;
begin
  Prog := AnalyseSrc(SrcAsExpr);
  try
    AE := TAsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('as-expr resolved type', AE.ResolvedType);
    AssertEquals('as-expr result is target class', 'TDog', AE.ResolvedType.Name);
  finally Prog.Free(); end;
end;

procedure TTypeTestTests.TestSemantic_AsExpr_NonClass_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var X: Integer;
            Y: Integer;
        begin
          Y := X as Integer
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ ClassType / TClass intrinsic                                         }
{ ------------------------------------------------------------------ }

const
  SrcClassType =
    '''
        program P;
        type
          TFoo = class end;
        var F: TFoo; CT: Pointer;
        begin
          F := TFoo.Create();
          CT := F.ClassType
        end.
        ''';

procedure TTypeTestTests.TestSemantic_ClassType_OK;
var P: TProgram;
begin
  P := AnalyseSrc(SrcClassType);
  P.Free();
end;

procedure TTypeTestTests.TestSemantic_ClassType_ResolvesToPointer;
var
  P: TProgram;
  Assign: TAssignment;
  Access: TFieldAccessExpr;
begin
  P := AnalyseSrc(SrcClassType);
  try
    { last stmt is the assignment to CT }
    Assign := TAssignment(P.Block.Stmts[1]);
    Access := TFieldAccessExpr(Assign.Expr);
    AssertTrue('IsClassTypeAccess set', Access.IsClassTypeAccess);
    AssertEquals('resolved type kind = tyPointer',
      Ord(tyPointer), Ord(Access.ResolvedType.Kind));
  finally
    P.Free();
  end;
end;

procedure TTypeTestTests.TestSemantic_TClass_AliasIsPointer;
var P: TProgram;
begin
  { TClass declared as a built-in alias of Pointer — using it for a
    var declaration must succeed. }
  P := AnalyseSrc(
    '''
        program P; var C: TClass;
        begin C := nil end.
        ''');
  P.Free();
end;

initialization
  RegisterTest(TTypeTestTests);

end.
