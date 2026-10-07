{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.proctypes;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable, cp.test.harness;

type
  TProcTypesTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function FindTypeDecl(AProg: TProgram; const AName: string): TTypeDecl;
  published
    { Parser — bare procedural type declarations }
    procedure TestParse_NoArgFunc_KindIsProcedural;
    procedure TestParse_NoArgFunc_ReturnTypeIsInteger;
    procedure TestParse_FuncWithParams_ParamCount;
    procedure TestParse_FuncWithParams_FirstParamName;
    procedure TestParse_FuncWithParams_ConstParamFlag;
    procedure TestParse_NoArgProc_KindIsProcedural;
    procedure TestParse_NoArgProc_NoReturnType;
    procedure TestParse_ProcWithVarParam_VarParamFlag;

    { Semantic — type assignability }
    procedure TestSemantic_AssignCompatibleFunc_OK;
    procedure TestSemantic_AssignWrongReturnType_Fails;
    procedure TestSemantic_AssignWrongParamCount_Fails;

    { Semantic — indirect-call argument type checking.
      Calls through a procedural-typed variable must validate each
      argument's type against the signature, not just the arg count. }
    procedure TestSemantic_IndirectCallStmt_WrongArgType_Fails;
    procedure TestSemantic_IndirectCallExpr_WrongArgType_Fails;
    { The same checks for a QUALIFIED procedural-field call (Obj.FP(..)),
      which used to bind the field and skip argument checking entirely.
      BUG-20260722-procfield-set-literal-arg. }
    procedure TestSemantic_QualifiedProcFieldCall_WrongArgCount_Fails;
    procedure TestSemantic_QualifiedProcFieldCallExpr_WrongArgType_Fails;

    { Codegen — emission }
    { BUG-20260923-qbe-implicit-self-ref-field-call: an unqualified call to a
      'reference to' field must pass the closure env (Data half) first. }
    { A procedural-typed class field called through a receiver as an
      expression (Result := Self.FFn(S)) must type to the field's return
      type and dispatch through the loaded pointer, not a direct call. }
    { BUG-20260722-closure-record-field-direct-call: a proc-field call on a
      RECORD variable must use the record's ADDRESS as the base.  Both
      backends loaded the slot's CONTENTS (the class-receiver convention),
      so the record's first 8 bytes were dispatched through as if they were
      an instance pointer.  ResolvedMethod is nil for a proc-field call, so
      every record arm gated on MDecl.IsRecordMethod was skipped. }
    { An unqualified procedural-field call via implicit Self (Result := FFn(S),
      no 'Self.' prefix) must resolve and dispatch through Self's field. }
    { BUG-20260923-closure-call-via-byval-record-param: a BY-VALUE record
      parameter is passed BY REFERENCE, so its slot holds the caller's record
      ADDRESS — exactly like a var param.  The five method-call STATEMENT
      sites in uSemantic used the narrow `Kind = skVarParameter` test, while
      every expression / field-access site already used the full predicate
      that also covers a by-value record or static-array parameter.  The
      call path therefore treated the parameter SLOT as the record base. }
    { BUG-20260923-addr-of-openarray-proc: an open-array (or array of const)
      param of a procedural type must stay an open array -- it resolved as
      its element type -- so @Proc is assignable, a scalar arg is rejected,
      and an indirect call passes the array as its (data, high) pair. }
    procedure TestSemantic_AddrOfOpenArrayProc_Assignable;
    procedure TestSemantic_AddrOfOpenArrayProc_ElementMismatch_Fails;
    procedure TestSemantic_ProcTypeOpenArrayParam_ScalarArg_Fails;
  end;

implementation

function TProcTypesTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcTypesTests.FindTypeDecl(AProg: TProgram; const AName: string): TTypeDecl;
var
  I: Integer;
  TD: TTypeDecl;
begin
  Result := nil;
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if SameText(TD.Name, AName) then
    begin
      Result := TD;
      Exit;
    end;
  end;
end;

{ ── Parser tests ─────────────────────────────────────────────────────────── }

procedure TProcTypesTests.TestParse_NoArgFunc_KindIsProcedural;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        begin
        end.
        '''
  );
  try
    TD := FindTypeDecl(Prog, 'TIntFn');
    AssertNotNull('Should find type decl TIntFn', TD);
    AssertTrue('Def should be a TProceduralTypeDef',
      TD.Def is TProceduralTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgFunc_ReturnTypeIsInteger;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TIntFn');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('IsFunction should be True', True, Def.IsFunction);
    AssertEquals('ReturnTypeName should be Integer', 'Integer', Def.ReturnTypeName);
    AssertEquals('Should have 0 params', 0, Def.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_ParamCount;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TBinFn = function(A: Integer; B: Integer): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TBinFn');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('Should have 2 params', 2, Def.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_FirstParamName;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TBinFn = function(A: Integer; B: Integer): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TBinFn');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertEquals('First param name', 'A', P1.ParamName);
    AssertEquals('First param type', 'Integer', P1.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_ConstParamFlag;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TStrFn = function(const S: string): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TStrFn');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertEquals('Param name', 'S', P1.ParamName);
    AssertTrue('IsConstParam should be True', P1.IsConstParam);
    AssertFalse('IsVarParam should be False', P1.IsVarParam);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgProc_KindIsProcedural;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TVoidProc = procedure;
        begin
        end.
        '''
  );
  try
    TD := FindTypeDecl(Prog, 'TVoidProc');
    AssertNotNull('Should find type decl TVoidProc', TD);
    AssertTrue('Def should be a TProceduralTypeDef',
      TD.Def is TProceduralTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgProc_NoReturnType;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TVoidProc = procedure;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TVoidProc');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('IsFunction should be False', False, Def.IsFunction);
    AssertEquals('ReturnTypeName should be empty', '', Def.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_ProcWithVarParam_VarParamFlag;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIncProc = procedure(var X: Integer);
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TIncProc');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertTrue('IsVarParam should be True', P1.IsVarParam);
    AssertFalse('IsConstParam should be False', P1.IsConstParam);
  finally
    Prog.Free();
  end;
end;

{ ── Semantic tests ───────────────────────────────────────────────────────── }

procedure TProcTypesTests.TestSemantic_AssignCompatibleFunc_OK;
begin
  { Should not raise. Assigning @MyFn to a TIntFn variable type-checks. }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TIntFn = function: Integer;
        function MyFn: Integer;
        begin
          Result := 42;
        end;
        var F: TIntFn;
        begin
          F := @MyFn;
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_AssignWrongReturnType_Fails;
begin
  AssertTrue('Should raise on incompatible return type',
    SemanticError(
      '''
          program Test;
          type
            TIntFn = function: Integer;
          function MyFn: string;
          begin
            Result := 'nope';
          end;
          var F: TIntFn;
          begin
            F := @MyFn;
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_AssignWrongParamCount_Fails;
begin
  AssertTrue('Should raise on incompatible param count',
    SemanticError(
      '''
          program Test;
          type
            TIntFn = function: Integer;
          function MyFn(X: Integer): Integer;
          begin
            Result := X;
          end;
          var F: TIntFn;
          begin
            F := @MyFn;
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_QualifiedProcFieldCall_WrongArgCount_Fails;
begin
  AssertTrue('Qualified proc-field call must reject a wrong arg count',
    SemanticError(
      '''
          program Test;
          type
            TP = procedure(A, B: Integer);
            TBox = class
              FP: TP;
            end;
          var X: TBox;
          begin
            X.FP(1)
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_QualifiedProcFieldCallExpr_WrongArgType_Fails;
begin
  AssertTrue('Qualified proc-field call expr must reject string where Integer expected',
    SemanticError(
      '''
          program Test;
          type
            TF = function(N: Integer): Integer;
            TBox = class
              FF: TF;
            end;
          var X: TBox; R: Integer;
          begin
            R := X.FF('oops')
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_IndirectCallStmt_WrongArgType_Fails;
begin
  { Statement-form indirect call: H('s') where H expects Integer must
    be rejected at semantic time, not silently miscompiled. }
  AssertTrue('Indirect call statement should reject string where Integer expected',
    SemanticError(
      '''
          program Test;
          type
            THandler = procedure(N: Integer);
          procedure DoIt(N: Integer);
          begin
          end;
          var H: THandler;
          begin
            H := @DoIt;
            H('oops')
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_IndirectCallExpr_WrongArgType_Fails;
begin
  { Expression-form indirect call: R := F('s') where F expects Integer
    must also be rejected at semantic time. }
  AssertTrue('Indirect call expression should reject string where Integer expected',
    SemanticError(
      '''
          program Test;
          type
            TIntFn = function(N: Integer): Integer;
          function Square(N: Integer): Integer;
          begin
            Result := N * N
          end;
          var F: TIntFn; R: Integer;
          begin
            F := @Square;
            R := F('oops')
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_AddrOfOpenArrayProc_Assignable;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TCnt = function(const A: array of Integer): Integer;
          TFmt = procedure(const S: string; const Args: array of const);
        function Cnt(const A: array of Integer): Integer;
        begin
          Result := Length(A)
        end;
        procedure Fmt(const S: string; const Args: array of const);
        begin
        end;
        var
          C: TCnt;
          F: TFmt;
        begin
          C := @Cnt;
          F := @Fmt
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_AddrOfOpenArrayProc_ElementMismatch_Fails;
begin
  AssertTrue('array of Byte routine must not match an array of Integer signature',
    SemanticError(
      '''
          program Test;
          type
            TCnt = function(const A: array of Integer): Integer;
          function Cnt(const A: array of Byte): Integer;
          begin
            Result := Length(A)
          end;
          var C: TCnt;
          begin
            C := @Cnt
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_ProcTypeOpenArrayParam_ScalarArg_Fails;
begin
  AssertTrue('an Integer is not an array of Integer',
    SemanticError(
      '''
          program Test;
          type
            TCnt = function(const A: array of Integer): Integer;
          var
            C: TCnt;
            N: Integer;
          begin
            N := C(5)
          end.
          ''') <> '');
end;

initialization
  RegisterTest(TProcTypesTests);

end.
