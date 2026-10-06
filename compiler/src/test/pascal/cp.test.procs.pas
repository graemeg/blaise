{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.procs;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TProcFuncTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_StandaloneProc_InProcDecls;
    procedure TestParse_StandaloneProc_Name;
    procedure TestParse_StandaloneProc_Params;
    procedure TestParse_StandaloneProc_ParamName;
    procedure TestParse_StandaloneProc_ParamTypeName;
    procedure TestParse_StandaloneProc_Body;
    procedure TestParse_StandaloneFunc_InProcDecls;
    procedure TestParse_StandaloneFunc_Name;
    procedure TestParse_StandaloneFunc_ReturnTypeName;
    procedure TestParse_ProcCall_IsTProcCall;
    procedure TestParse_FuncCall_Expr_IsTFuncCallExpr;
    procedure TestParse_FuncCall_Expr_Name;
    procedure TestParse_FuncCall_Expr_ArgCount;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StandaloneProc_Resolves;
    procedure TestSemantic_StandaloneFunc_Resolves;
    procedure TestSemantic_ProcCall_WrongArgCount_RaisesError;
    procedure TestSemantic_ProcCall_ArgTypeMismatch_RaisesError;
    procedure TestSemantic_FuncCall_ReturnsCorrectType;
    procedure TestSemantic_StandaloneFunc_ResultVar_Available;
    procedure TestSemantic_UnknownProc_RaisesError;
    procedure TestSemantic_Proc_CanCallOtherProc;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_StandaloneFunc_EmitsFunctionWithRetType;
    procedure TestCodegen_StandaloneFunc_HasResultVar;

    { Regression: float-typed parameter spill must use stored/stores
      (matching the QBE 'd'/'s' parameter type), not storel — QBE
      rejects 'storel %_par_D' for a 'd %_par_D' parameter. }

    { Nested procedures }
    procedure TestCodegen_NestedProc_IsEmittedBeforeOuter;
    { Same as above but the nested routines are FUNCTIONS called as
      expressions (Helper(X) inside WriteLn), which exercises
      AnalyseFuncCallExpr rather than AnalyseProcCall.  The func-call path
      previously consulted only the global FProcIndex and errored with
      "Cannot find declaration for function 'Helper'". }
    { Two sibling METHOD bodies each declaring a same-named nested function.
      Nested-in-method decls were registered in the global overload index
      (the registration guard only excluded nested-in-standalone-proc decls),
      so they collided as "Ambiguous overload".  They must be scoped to their
      enclosing method body like nested-in-proc decls. }
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TProcFuncTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcFuncTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TProcFuncTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.AnalyseExpectError(const ASrc: string);
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
  SrcWithProc =
    '''
        program P;
        var N: Integer;
        procedure PrintIt(X: Integer);
        begin
          WriteLn(X)
        end;
        begin
          N := 7;
          PrintIt(N)
        end.
        ''';

  SrcWithFunc =
    '''
        program P;
        var N: Integer;
        function Add(A, B: Integer): Integer;
        var Tmp: Integer;
        begin
          Tmp := A + B;
          Result := Tmp
        end;
        begin
          N := Add(3, 4)
        end.
        ''';

  SrcTwoProcs =
    '''
        program P;
        var N: Integer;
        procedure Inner(X: Integer);
        begin
          WriteLn(X)
        end;
        procedure Outer(Y: Integer);
        begin
          Inner(Y)
        end;
        begin
          N := 1;
          Outer(N)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser tests                                                        }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestParse_StandaloneProc_InProcDecls;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    AssertEquals('one proc decl', 1, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Name;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('proc name', 'PrintIt', MD.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Params;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('one param', 1, MD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_ParamName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD  := TMethodDecl(Prog.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param name', 'X', Par.ParamName);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_ParamTypeName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD  := TMethodDecl(Prog.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param type', 'Integer', Par.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Body;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertNotNull('body exists', MD.Body);
    AssertEquals('body has 1 stmt', 1, MD.Body.Stmts.Count);
    AssertTrue('stmt is TProcCall', MD.Body.Stmts[0] is TProcCall);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_InProcDecls;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    AssertEquals('one proc decl', 1, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_Name;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('func name', 'Add', MD.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_ReturnTypeName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('return type', 'Integer', MD.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_ProcCall_IsTProcCall;
var
  Prog: TProgram;
  Stmt: TASTStmt;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    { second stmt in main body: PrintIt(N) }
    Stmt := TASTStmt(Prog.Block.Stmts[1]);
    AssertTrue('stmt is TProcCall', Stmt is TProcCall);
    AssertEquals('proc name', 'PrintIt', TProcCall(Stmt).Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_IsTFuncCallExpr;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    { N := Add(3, 4) }
    AssertTrue('stmt is TAssignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TFuncCallExpr', Assign.Expr is TFuncCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_Name;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('func name', 'Add', FCall.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_ArgCount;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('two args', 2, FCall.Args.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestSemantic_StandaloneProc_Resolves;
begin
  AnalyseSrc(SrcWithProc).Free();
end;

procedure TProcFuncTests.TestSemantic_StandaloneFunc_Resolves;
begin
  AnalyseSrc(SrcWithFunc).Free();
end;

procedure TProcFuncTests.TestSemantic_ProcCall_WrongArgCount_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        procedure Foo(X: Integer);
        begin
          WriteLn(X)
        end;
        begin
          Foo(1, 2)
        end.
        ''');
end;

procedure TProcFuncTests.TestSemantic_ProcCall_ArgTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        procedure Foo(X: Integer);
        begin
          WriteLn(X)
        end;
        begin
          Foo('not an int')
        end.
        ''');
end;

procedure TProcFuncTests.TestSemantic_FuncCall_ReturnsCorrectType;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := AnalyseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertNotNull('expr has resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type is Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestSemantic_StandaloneFunc_ResultVar_Available;
begin
  { Result := A + B inside the function body must not raise an error }
  AnalyseSrc(SrcWithFunc).Free();
end;

procedure TProcFuncTests.TestSemantic_UnknownProc_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        begin
          NoSuchProc(1)
        end.
        ''');
end;

procedure TProcFuncTests.TestSemantic_Proc_CanCallOtherProc;
begin
  AnalyseSrc(SrcTwoProcs).Free();
end;

{ ------------------------------------------------------------------ }
{ Code generation tests                                               }
{ ------------------------------------------------------------------ }

{ QBE-only (delete with the backend, Phase 2): pins QBE syntax with no
  behaviour behind it. }
procedure TProcFuncTests.TestCodegen_StandaloneFunc_EmitsFunctionWithRetType;
var
  IR: string;
begin
  IR := GenIR(SrcWithFunc);
  AssertTrue('emits $Add function', Pos('$Add', IR) > 0);
  { function has return type: 'function w $Add(' }
  AssertTrue('function has return qtype', Pos('function w $Add', IR) > 0);
end;

{ QBE-only (delete with the backend, Phase 2): pins QBE syntax with no
  behaviour behind it. }
procedure TProcFuncTests.TestCodegen_StandaloneFunc_HasResultVar;
var
  IR: string;
begin
  IR := GenIR(SrcWithFunc);
  AssertTrue('Result variable slot emitted', Pos('%_var_Result', IR) > 0);
end;

{ QBE-only (delete with the backend, Phase 2): pins QBE syntax with no
  behaviour behind it. }
procedure TProcFuncTests.TestCodegen_NestedProc_IsEmittedBeforeOuter;
const
  Src =
    '''
        program P;
        procedure Outer;
          procedure Inner;
          begin
          end;
        begin
          Inner();
        end;
        begin
          Outer();
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('Outer_Inner symbol present',
    StrPos('$Outer_Inner', IR) >= 0);
  AssertTrue('Inner appears before Outer in IR',
    StrPos('$Outer_Inner', IR) < StrPos('$Outer(', IR));
end;

initialization
  RegisterTest(TProcFuncTests);

end.
