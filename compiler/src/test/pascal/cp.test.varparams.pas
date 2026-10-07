{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.varparams;

{ Tests for var parameters: pass-by-reference semantics across
  lexer, parser, semantic analysis, and code generation. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TVarParamTests = class(TTestCase)
  private
    function  ParseSrc(const ASrc: string): TProgram;
    function  AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_VarParam_IsVarParam;
    procedure TestParse_VarParam_MultiInGroup;
    procedure TestParse_VarParam_Mixed_VarAndValue;
    procedure TestParse_VarParam_ValueParam_IsNotVar;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_VarParam_OK;
    procedure TestSemantic_VarParam_NonVariable_RaisesError;
    procedure TestSemantic_VarParam_TypeMismatch_RaisesError;
    { BUG-011: method-call var args were not lvalue-checked in the semantic
      pass, so a non-lvalue passed to a method's var param slipped through and
      crashed codegen ("var/out argument must be a variable or field").  Now a
      clean semantic error, consistent with standalone-proc calls. }
    procedure TestSemantic_MethodVarParam_NonLValueStmt_RaisesError;
    procedure TestSemantic_MethodVarParam_NonLValueExpr_RaisesError;
    procedure TestSemantic_MethodVarParam_Variable_OK;
    { BUG-011 follow-up: further call paths that also skipped the lvalue
      check — metaclass-var constructor dispatch (statement form), inherited
      calls (statement + expression), a standalone function called in
      expression position, and a generic method instance.  Each must raise a
      semantic error for a non-lvalue actual, and still accept a variable. }
    procedure TestSemantic_MetaclassCtorVarParam_NonLValueStmt_RaisesError;
    procedure TestSemantic_InheritedVarParam_NonLValueStmt_RaisesError;
    procedure TestSemantic_InheritedVarParam_NonLValueExpr_RaisesError;
    procedure TestSemantic_StandaloneFuncVarParam_NonLValueExpr_RaisesError;
    procedure TestSemantic_GenericMethodVarParam_NonLValueExpr_RaisesError;
    procedure TestSemantic_IntfVarParam_NonLValueStmt_RaisesError;
    procedure TestSemantic_IntfVarParam_NonLValueExpr_RaisesError;
    procedure TestSemantic_IntfVarParam_Variable_OK;
    procedure TestSemantic_NewPathsVarParam_Variable_OK;

    { L-value var args beyond simple identifiers: a record-field access
      (R.F) and a pointer-deref-then-field (P^.F) must both be accepted
      where the parameter is var-typed. }
    procedure TestSemantic_VarParam_FieldAccess_OK;
    procedure TestSemantic_VarParam_DerefField_OK;

    { Var-param call where the actual argument is a CLASS field
      (C.Field where C is a class reference, not a record).  The address
      must be computed as (loadl C) + offset, not (&C + offset), because
      the variable holding the class reference stores a pointer to the
      heap object — adding the offset to the variable's address points
      at unrelated memory.  See BUG-001 in bugs.txt. }
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TVarParamTests.ParseSrc(const ASrc: string): TProgram;
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

function TVarParamTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TVarParamTests.AnalyseExpectError(const ASrc: string);
var P: TProgram;
begin
  try
    P := AnalyseSrc(ASrc);
    P.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcVarSet =
    '''
        program VarTest;
        procedure SetVal(var X: Integer);
        begin
          X := 42
        end;
        var V: Integer;
        begin
          V := 0;
          SetVal(V)
        end.
        ''';

  SrcVarSwap =
    '''
        program SwapTest;
        procedure Swap(var A, B: Integer);
        var T: Integer;
        begin
          T := A;
          A := B;
          B := T
        end;
        var X, Y: Integer;
        begin
          X := 1;
          Y := 2;
          Swap(X, Y)
        end.
        ''';

  SrcMixed =
    '''
        program MixedTest;
        procedure P(var A: Integer; B: Integer);
        begin
          A := B
        end;
        var X: Integer;
        begin
          P(X, 5)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestParse_VarParam_IsVarParam;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(SrcVarSet);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);  { SetVal }
    Par := TMethodParam(MD.Params[0]);         { var X }
    AssertTrue('X is var param', Par.IsVarParam);
  finally P.Free(); end;
end;

procedure TVarParamTests.TestParse_VarParam_MultiInGroup;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(SrcVarSwap);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);  { Swap }
    AssertTrue('A is var param', TMethodParam(MD.Params[0]).IsVarParam);
    AssertTrue('B is var param', TMethodParam(MD.Params[1]).IsVarParam);
  finally P.Free(); end;
end;

procedure TVarParamTests.TestParse_VarParam_Mixed_VarAndValue;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(SrcMixed);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);  { P(var A; B) }
    AssertTrue('A is var param',    TMethodParam(MD.Params[0]).IsVarParam);
    AssertFalse('B is value param', TMethodParam(MD.Params[1]).IsVarParam);
  finally P.Free(); end;
end;

procedure TVarParamTests.TestParse_VarParam_ValueParam_IsNotVar;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(
    '''
        program T;
        procedure Q(X: Integer);
        begin end;
        begin end.
        ''');
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);
    AssertFalse('X is not var param', TMethodParam(MD.Params[0]).IsVarParam);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestSemantic_VarParam_OK;
begin
  AnalyseSrc(SrcVarSet).Free();
end;

procedure TVarParamTests.TestSemantic_VarParam_NonVariable_RaisesError;
begin
  AnalyseExpectError(
    'program Bad;' + #10 +
    'procedure Inc(var X: Integer);' + #10 +
    'begin X := X + 1 end;' + #10 +
    'begin' + #10 +
    '  Inc(42)'                                     + #10 +  { literal, not a variable }
    'end.');
end;

procedure TVarParamTests.TestSemantic_VarParam_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program Bad;' + #10 +
    'procedure SetI(var X: Integer);' + #10 +
    'begin X := 1 end;' + #10 +
    'var B: Boolean;' + #10 +
    'begin' + #10 +
    '  SetI(B)'                                     + #10 +  { wrong type }
    'end.');
end;

const
  SrcMethodVarParamHeader =
    'program Bad;' + #10 +
    'type' + #10 +
    '  TThing = class' + #10 +
    '    procedure MStmt(var X: Integer);' + #10 +
    '    function MExpr(var X: Integer): Integer;' + #10 +
    '  end;' + #10 +
    'procedure TThing.MStmt(var X: Integer); begin X := X + 1 end;' + #10 +
    'function TThing.MExpr(var X: Integer): Integer;' + #10 +
    'begin X := X + 1; Result := X end;' + #10 +
    'function GetVal: Integer; begin Result := 5 end;' + #10 +
    'var t: TThing; r: Integer;' + #10 +
    'begin' + #10 +
    '  t := TThing.Create();' + #10;

procedure TVarParamTests.TestSemantic_MethodVarParam_NonLValueStmt_RaisesError;
begin
  { A function-call result (non-lvalue) passed to a method's var param, in
    statement position, must raise instead of crashing codegen. }
  AnalyseExpectError(SrcMethodVarParamHeader +
    '  t.MStmt(GetVal())' + #10 +
    'end.');
end;

procedure TVarParamTests.TestSemantic_MethodVarParam_NonLValueExpr_RaisesError;
begin
  { Same, in expression position (method used as the RHS of an assignment). }
  AnalyseExpectError(SrcMethodVarParamHeader +
    '  r := t.MExpr(GetVal())' + #10 +
    'end.');
end;

procedure TVarParamTests.TestSemantic_MethodVarParam_Variable_OK;
var P: TProgram;
begin
  { A real variable passed to a method var param must still analyse cleanly. }
  P := AnalyseSrc(SrcMethodVarParamHeader +
    '  r := 5;' + #10 +
    '  t.MStmt(r);' + #10 +
    '  r := t.MExpr(r)' + #10 +
    'end.');
  AssertTrue('legitimate method var arg analyses', P <> nil);
  P.Free();
end;

const
  { Shared fixture for the BUG-011 follow-up paths: an inheritance pair with
    var-param methods, a var-param constructor + metaclass, a standalone
    var-param function, and a generic var-param method. }
  SrcVarParamPathsHeader =
    'program Bad;' + #10 +
    'type' + #10 +
    '  TBase = class' + #10 +
    '    procedure M(var X: Integer); virtual;' + #10 +
    '    function F(var X: Integer): Integer; virtual;' + #10 +
    '  end;' + #10 +
    '  TChild = class(TBase)' + #10 +
    '    procedure M(var X: Integer); override;' + #10 +
    '    function F(var X: Integer): Integer; override;' + #10 +
    '  end;' + #10 +
    '  TCtor = class' + #10 +
    '    constructor Create(var X: Integer);' + #10 +
    '  end;' + #10 +
    '  TCtorClass = class of TCtor;' + #10 +
    '  TBox = class' + #10 +
    '    function Pick<T>(var A: T): T;' + #10 +
    '  end;' + #10 +
    'procedure TBase.M(var X: Integer); begin X := X + 1 end;' + #10 +
    'function TBase.F(var X: Integer): Integer;' + #10 +
    'begin X := X + 1; Result := X end;' + #10 +
    'constructor TCtor.Create(var X: Integer); begin X := X + 1 end;' + #10 +
    'function TBox.Pick<T>(var A: T): T; begin Result := A end;' + #10 +
    'function GetVal: Integer; begin Result := 5 end;' + #10 +
    'function Bump(var X: Integer): Integer;' + #10 +
    'begin X := X + 1; Result := X end;' + #10;

procedure TVarParamTests.TestSemantic_MetaclassCtorVarParam_NonLValueStmt_RaisesError;
begin
  AnalyseExpectError(SrcVarParamPathsHeader +
    'procedure TChild.M(var X: Integer); begin end;' + #10 +
    'function TChild.F(var X: Integer): Integer; begin Result := 0 end;' + #10 +
    'var c: TCtorClass;' + #10 +
    'begin' + #10 +
    '  c := TCtor;' + #10 +
    '  c.Create(GetVal())' + #10 +
    'end.');
end;

procedure TVarParamTests.TestSemantic_InheritedVarParam_NonLValueStmt_RaisesError;
begin
  AnalyseExpectError(SrcVarParamPathsHeader +
    'procedure TChild.M(var X: Integer);' + #10 +
    'begin inherited M(GetVal()) end;' + #10 +
    'function TChild.F(var X: Integer): Integer; begin Result := 0 end;' + #10 +
    'begin end.');
end;

procedure TVarParamTests.TestSemantic_InheritedVarParam_NonLValueExpr_RaisesError;
begin
  AnalyseExpectError(SrcVarParamPathsHeader +
    'procedure TChild.M(var X: Integer); begin end;' + #10 +
    'function TChild.F(var X: Integer): Integer;' + #10 +
    'begin Result := inherited F(GetVal()) end;' + #10 +
    'begin end.');
end;

procedure TVarParamTests.TestSemantic_StandaloneFuncVarParam_NonLValueExpr_RaisesError;
begin
  AnalyseExpectError(SrcVarParamPathsHeader +
    'procedure TChild.M(var X: Integer); begin end;' + #10 +
    'function TChild.F(var X: Integer): Integer; begin Result := 0 end;' + #10 +
    'var r: Integer;' + #10 +
    'begin' + #10 +
    '  r := Bump(GetVal())' + #10 +
    'end.');
end;

procedure TVarParamTests.TestSemantic_GenericMethodVarParam_NonLValueExpr_RaisesError;
begin
  AnalyseExpectError(SrcVarParamPathsHeader +
    'procedure TChild.M(var X: Integer); begin end;' + #10 +
    'function TChild.F(var X: Integer): Integer; begin Result := 0 end;' + #10 +
    'var b: TBox; r: Integer;' + #10 +
    'begin' + #10 +
    '  b := TBox.Create();' + #10 +
    '  r := b.Pick<Integer>(GetVal())' + #10 +
    'end.');
end;

const
  { Interface dispatch records per-param var flags on the descriptor (no
    TMethodDecl at the call site), so the lvalue constraint is enforced from
    those flags.  The second G param exercises flag/arg index alignment. }
  SrcIntfVarParamHeader =
    'program Bad;' + #10 +
    'type' + #10 +
    '  IThing = interface' + #10 +
    '    procedure M(var X: Integer);' + #10 +
    '    function G(A: Integer; var X: Integer): Integer;' + #10 +
    '  end;' + #10 +
    '  TThing = class(TObject, IThing)' + #10 +
    '    procedure M(var X: Integer);' + #10 +
    '    function G(A: Integer; var X: Integer): Integer;' + #10 +
    '  end;' + #10 +
    'procedure TThing.M(var X: Integer); begin X := X + 1 end;' + #10 +
    'function TThing.G(A: Integer; var X: Integer): Integer;' + #10 +
    'begin X := X + A; Result := X end;' + #10 +
    'function GetVal: Integer; begin Result := 5 end;' + #10 +
    'var i: IThing; r: Integer;' + #10 +
    'begin' + #10 +
    '  i := TThing.Create();' + #10;

procedure TVarParamTests.TestSemantic_IntfVarParam_NonLValueStmt_RaisesError;
begin
  AnalyseExpectError(SrcIntfVarParamHeader +
    '  i.M(GetVal())' + #10 +
    'end.');
end;

procedure TVarParamTests.TestSemantic_IntfVarParam_NonLValueExpr_RaisesError;
begin
  AnalyseExpectError(SrcIntfVarParamHeader +
    '  r := i.G(1, GetVal())' + #10 +
    'end.');
end;

procedure TVarParamTests.TestSemantic_IntfVarParam_Variable_OK;
var P: TProgram;
begin
  P := AnalyseSrc(SrcIntfVarParamHeader +
    '  r := 5;' + #10 +
    '  i.M(r);' + #10 +
    '  r := i.G(GetVal(), r)' + #10 +   { non-var pos 0 stays unconstrained }
    'end.');
  AssertTrue('legitimate interface var args analyse', P <> nil);
  P.Free();
end;

procedure TVarParamTests.TestSemantic_NewPathsVarParam_Variable_OK;
var P: TProgram;
begin
  { A real variable must still be accepted on every newly checked path. }
  P := AnalyseSrc(SrcVarParamPathsHeader +
    'procedure TChild.M(var X: Integer);' + #10 +
    'begin inherited M(X) end;' + #10 +
    'function TChild.F(var X: Integer): Integer;' + #10 +
    'begin Result := inherited F(X) end;' + #10 +
    'var c: TCtorClass; t: TChild; b: TBox; r: Integer;' + #10 +
    'begin' + #10 +
    '  r := 5;' + #10 +
    '  c := TCtor;' + #10 +
    '  c.Create(r);' + #10 +
    '  t := TChild.Create();' + #10 +
    '  t.M(r);' + #10 +
    '  r := t.F(r);' + #10 +
    '  r := Bump(r);' + #10 +
    '  b := TBox.Create();' + #10 +
    '  r := b.Pick<Integer>(r)' + #10 +
    'end.');
  AssertTrue('legitimate var args analyse on all new paths', P <> nil);
  P.Free();
end;

procedure TVarParamTests.TestSemantic_VarParam_FieldAccess_OK;
var
  Prog: TProgram;
begin
  { Pass R.Count (a field access expression) as a var argument.
    Must analyse without error — field accesses are L-values. }
  Prog := AnalyseSrc(
    '''
        program Prg;
        type
          TRec = record Count: Integer; end;
        procedure Bump(var N: Integer);
        begin Inc(N) end;
        var R: TRec;
        begin
          R.Count := 0;
          Bump(R.Count)
        end.
        ''');
  Prog.Free();
end;

procedure TVarParamTests.TestSemantic_VarParam_DerefField_OK;
var
  Prog: TProgram;
begin
  { Pass P^.Count (pointer deref + field) as a var argument. }
  Prog := AnalyseSrc(
    '''
        program Prg;
        type
          TRec = record Count: Integer; end;
          PRec = ^TRec;
        procedure Bump(var N: Integer);
        begin Inc(N) end;
        var P: PRec; R: TRec;
        begin
          P := @R;
          P^.Count := 0;
          Bump(P^.Count)
        end.
        ''');
  Prog.Free();
end;

initialization
  RegisterTest(TVarParamTests);

end.
