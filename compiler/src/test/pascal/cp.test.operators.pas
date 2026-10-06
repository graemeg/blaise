{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.operators;

{ Parser + semantic + IR tests for operator overloading (`class operator`).

  Phase 1 covers the declaration form only: `class operator Add(const A, B:
  TFoo): TFoo;` inside a record or a class body parses into an ordinary
  TMethodDecl carrying IsOperator = True, OperatorKind = okAdd and
  IsStatic = True — so every downstream path (mangling, .bif, codegen)
  treats it as a static method.

  Phase 2 adds semantic resolution: when no built-in rule applies and an
  operand is a record or class, AnalyseBinaryExpr resolves the operator on
  the union of both operand types and LOWERS the binary expression into a
  synthesised TMethodCallExpr (TBinaryExpr.LoweredCall), so the record /
  sret / ARC machinery is reached through the normal method-call path. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TOperatorTests = class(TTestCase)
  private
    function  ParseSrc(const ASrc: string): TProgram;
    function  AnalyseSrc(const ASrc: string): TProgram;
    procedure ParseExpectError(const ASrc: string);
    procedure AnalyseExpectError(const ASrc: string);
    { Locate the type declaration named AName in the program block and return
      the method decl at index AIdx of its Methods list. }
    function  FindMethod(AProg: TProgram; const ATypeName, AMethodName: string): TMethodDecl;
  published
    { --- Phase 1: parser --- }
    procedure TestParse_RecordOperator_Add;
    procedure TestParse_ClassOperator_Add;
    procedure TestParse_RecordOperator_Negative_UnaryArity;
    procedure TestParse_AllOperatorNames;
    procedure TestParse_OutOfLineBody_Program;
    procedure TestParse_OutOfLineBody_UnitImplSection;
    procedure TestParse_UnknownOperatorName_Rejected;
    procedure TestParse_BinaryOperator_WrongArity_Rejected;
    procedure TestParse_UnaryOperator_WrongArity_Rejected;
    procedure TestParse_OperatorInGenericRecord_Rejected;
    procedure TestParse_OperatorInGenericClass_Rejected;
    procedure TestParse_FieldNamedOperator_StillParses;
    { --- Phase 2: semantic resolution --- }
    procedure TestSem_RecordAdd_Resolves;
    procedure TestSem_RecordAdd_LoweredCallSet;
    procedure TestSem_NoOperator_StillErrors;
    procedure TestSem_BuiltinSet_Unaffected;
    procedure TestSem_ClassIdentityEqual_Preserved;
    { --- Phase 2: IR --- }
  end;

implementation

const
  LE = #10;

function TOperatorTests.ParseSrc(const ASrc: string): TProgram;
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

function TOperatorTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := Self.ParseSrc(ASrc);
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Result);
    finally
      A.Free();
    end;
  except
    Result.Free();
    raise;
  end;
end;

procedure TOperatorTests.ParseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := Self.ParseSrc(ASrc);
    Prog.Free();
    Fail('Expected EParseError');
  except
    on E: EParseError do ; { expected }
  end;
end;

procedure TOperatorTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := Self.AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

function TOperatorTests.FindMethod(AProg: TProgram; const ATypeName, AMethodName: string): TMethodDecl;
var
  I, J:  Integer;
  TD:    TTypeDecl;
  RD:    TRecordTypeDef;
  CD:    TClassTypeDef;
  Meths: TObjectList;
  MD:    TMethodDecl;
begin
  Result := nil;
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not SameText(TD.Name, ATypeName) then Continue;
    Meths := nil;
    if TD.Def is TRecordTypeDef then
    begin
      RD := TRecordTypeDef(TD.Def);
      Meths := RD.Methods;
    end
    else if TD.Def is TClassTypeDef then
    begin
      CD := TClassTypeDef(TD.Def);
      Meths := CD.Methods;
    end;
    if Meths = nil then Continue;
    for J := 0 to Meths.Count - 1 do
    begin
      MD := TMethodDecl(Meths.Items[J]);
      if SameText(MD.Name, AMethodName) then
        Exit(MD);
    end;
  end;
end;

{ ------------------------------------------------------------------ }
{ Phase 1 — parser                                                    }
{ ------------------------------------------------------------------ }

procedure TOperatorTests.TestParse_RecordOperator_Add;
const
  Src = '''
      program P;
      type
        TFoo = record
          X: Integer;
          class operator Add(const A, B: TFoo): TFoo;
        end;
      begin
      end.
      ''';
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := Self.ParseSrc(Src);
  try
    MD := Self.FindMethod(Prog, 'TFoo', 'Add');
    AssertNotNull('operator Add parsed', MD);
    AssertTrue('IsOperator', MD.IsOperator);
    AssertTrue('OperatorKind = okAdd', MD.OperatorKind = okAdd);
    AssertTrue('IsStatic', MD.IsStatic);
    AssertEquals('param count', 2, MD.Params.Count);
    AssertEquals('return type', 'TFoo', MD.ReturnTypeName);
    AssertEquals('param 0 type', 'TFoo', TMethodParam(MD.Params.Items[0]).TypeName);
    AssertTrue('param 0 is const', TMethodParam(MD.Params.Items[0]).IsConstParam);
  finally
    Prog.Free();
  end;
end;

procedure TOperatorTests.TestParse_ClassOperator_Add;
const
  Src = '''
      program P;
      type
        TBar = class
          X: Integer;
          class operator Add(const A, B: TBar): TBar;
        end;
      begin
      end.
      ''';
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := Self.ParseSrc(Src);
  try
    MD := Self.FindMethod(Prog, 'TBar', 'Add');
    AssertNotNull('operator Add parsed on class', MD);
    AssertTrue('IsOperator', MD.IsOperator);
    AssertTrue('OperatorKind = okAdd', MD.OperatorKind = okAdd);
    AssertTrue('IsStatic', MD.IsStatic);
    AssertEquals('param count', 2, MD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TOperatorTests.TestParse_RecordOperator_Negative_UnaryArity;
const
  Src = '''
      program P;
      type
        TFoo = record
          X: Integer;
          class operator Negative(const A: TFoo): TFoo;
        end;
      begin
      end.
      ''';
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := Self.ParseSrc(Src);
  try
    MD := Self.FindMethod(Prog, 'TFoo', 'Negative');
    AssertNotNull('operator Negative parsed', MD);
    AssertTrue('OperatorKind = okNegative', MD.OperatorKind = okNegative);
    AssertEquals('param count', 1, MD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TOperatorTests.TestParse_AllOperatorNames;
const
  Src = '''
      program P;
      type
        TFoo = record
          X: Integer;
          class operator Add(const A, B: TFoo): TFoo;
          class operator Subtract(const A, B: TFoo): TFoo;
          class operator Multiply(const A, B: TFoo): TFoo;
          class operator Divide(const A, B: TFoo): TFoo;
          class operator Equal(const A, B: TFoo): Boolean;
          class operator NotEqual(const A, B: TFoo): Boolean;
          class operator LessThan(const A, B: TFoo): Boolean;
          class operator GreaterThan(const A, B: TFoo): Boolean;
          class operator LessThanOrEqual(const A, B: TFoo): Boolean;
          class operator GreaterThanOrEqual(const A, B: TFoo): Boolean;
          class operator Negative(const A: TFoo): TFoo;
        end;
      begin
      end.
      ''';
var
  Prog: TProgram;
begin
  Prog := Self.ParseSrc(Src);
  try
    AssertTrue('Subtract', Self.FindMethod(Prog, 'TFoo', 'Subtract').OperatorKind = okSubtract);
    AssertTrue('Multiply', Self.FindMethod(Prog, 'TFoo', 'Multiply').OperatorKind = okMultiply);
    AssertTrue('Divide',   Self.FindMethod(Prog, 'TFoo', 'Divide').OperatorKind = okDivide);
    AssertTrue('Equal',    Self.FindMethod(Prog, 'TFoo', 'Equal').OperatorKind = okEqual);
    AssertTrue('NotEqual', Self.FindMethod(Prog, 'TFoo', 'NotEqual').OperatorKind = okNotEqual);
    AssertTrue('LessThan', Self.FindMethod(Prog, 'TFoo', 'LessThan').OperatorKind = okLessThan);
    AssertTrue('GreaterThan',
      Self.FindMethod(Prog, 'TFoo', 'GreaterThan').OperatorKind = okGreaterThan);
    AssertTrue('LessThanOrEqual',
      Self.FindMethod(Prog, 'TFoo', 'LessThanOrEqual').OperatorKind = okLessThanOrEqual);
    AssertTrue('GreaterThanOrEqual',
      Self.FindMethod(Prog, 'TFoo', 'GreaterThanOrEqual').OperatorKind = okGreaterThanOrEqual);
    AssertTrue('Negative', Self.FindMethod(Prog, 'TFoo', 'Negative').OperatorKind = okNegative);
  finally
    Prog.Free();
  end;
end;

procedure TOperatorTests.TestParse_OutOfLineBody_Program;
const
  Src = '''
      program P;
      type
        TFoo = record
          X: Integer;
          class operator Add(const A, B: TFoo): TFoo;
        end;
      class operator TFoo.Add(const A, B: TFoo): TFoo;
      begin
        Result.X := A.X + B.X
      end;
      begin
      end.
      ''';
var
  Prog: TProgram;
  I:    Integer;
  MD:   TMethodDecl;
  Seen: Boolean;
begin
  Prog := Self.ParseSrc(Src);
  try
    Seen := False;
    for I := 0 to Prog.Block.ProcDecls.Count - 1 do
    begin
      MD := TMethodDecl(Prog.Block.ProcDecls.Items[I]);
      if SameText(MD.Name, 'Add') and SameText(MD.OwnerTypeName, 'TFoo') then
      begin
        AssertTrue('out-of-line body IsOperator', MD.IsOperator);
        AssertTrue('out-of-line body OperatorKind', MD.OperatorKind = okAdd);
        AssertTrue('out-of-line body IsStatic', MD.IsStatic);
        AssertNotNull('out-of-line body present', MD.Body);
        Seen := True;
      end;
    end;
    AssertTrue('out-of-line operator body found', Seen);
  finally
    Prog.Free();
  end;
end;

procedure TOperatorTests.TestParse_OutOfLineBody_UnitImplSection;
const
  Src = '''
      unit u;
      interface
      type
        TFoo = record
          X: Integer;
          class operator Add(const A, B: TFoo): TFoo;
        end;
      implementation
      class operator TFoo.Add(const A, B: TFoo): TFoo;
      begin
        Result.X := A.X + B.X
      end;
      end.
      ''';
var
  L:    TLexer;
  P:    TParser;
  U:    TUnit;
  I:    Integer;
  MD:   TMethodDecl;
  Seen: Boolean;
begin
  L := TLexer.Create(Src);
  P := TParser.Create(L);
  try
    U := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
  try
    Seen := False;
    for I := 0 to U.ImplBlock.ProcDecls.Count - 1 do
    begin
      MD := TMethodDecl(U.ImplBlock.ProcDecls.Items[I]);
      if SameText(MD.Name, 'Add') and SameText(MD.OwnerTypeName, 'TFoo') then
      begin
        AssertTrue('impl-section IsOperator', MD.IsOperator);
        AssertTrue('impl-section IsStatic', MD.IsStatic);
        AssertNotNull('impl-section body', MD.Body);
        Seen := True;
      end;
    end;
    AssertTrue('impl-section operator body found', Seen);
  finally
    U.Free();
  end;
end;

procedure TOperatorTests.TestParse_UnknownOperatorName_Rejected;
const
  Src = '''
      program P;
      type
        TFoo = record
          X: Integer;
          class operator Frobnicate(const A, B: TFoo): TFoo;
        end;
      begin
      end.
      ''';
begin
  Self.ParseExpectError(Src);
end;

procedure TOperatorTests.TestParse_BinaryOperator_WrongArity_Rejected;
const
  Src = '''
      program P;
      type
        TFoo = record
          X: Integer;
          class operator Add(const A: TFoo): TFoo;
        end;
      begin
      end.
      ''';
begin
  Self.ParseExpectError(Src);
end;

procedure TOperatorTests.TestParse_UnaryOperator_WrongArity_Rejected;
const
  Src = '''
      program P;
      type
        TFoo = record
          X: Integer;
          class operator Negative(const A, B: TFoo): TFoo;
        end;
      begin
      end.
      ''';
begin
  Self.ParseExpectError(Src);
end;

procedure TOperatorTests.TestParse_OperatorInGenericRecord_Rejected;
const
  Src = '''
      program P;
      type
        TVec<T> = record
          X: T;
          class operator Add(const A, B: TVec<T>): TVec<T>;
        end;
      begin
      end.
      ''';
begin
  Self.ParseExpectError(Src);
end;

procedure TOperatorTests.TestParse_OperatorInGenericClass_Rejected;
const
  Src = '''
      program P;
      type
        TBox<T> = class
          X: T;
          class operator Add(const A, B: TBox<T>): TBox<T>;
        end;
      begin
      end.
      ''';
begin
  Self.ParseExpectError(Src);
end;

{ `operator` is a CONTEXTUAL identifier: it is only special after `class`.
  A record field literally named Operator must still parse. }
procedure TOperatorTests.TestParse_FieldNamedOperator_StillParses;
const
  Src = '''
      program P;
      type
        TFoo = record
          Operator: Integer;
        end;
      var F: TFoo;
      begin
        F.Operator := 3
      end.
      ''';
var
  Prog: TProgram;
begin
  Prog := Self.ParseSrc(Src);
  Prog.Free();
end;

{ ------------------------------------------------------------------ }
{ Phase 2 — semantic resolution                                       }
{ ------------------------------------------------------------------ }

const
  RectSrc = '''
      program P;
      type
        TRect = record
          L, T, R, B: Integer;
          class operator Add(const A, C: TRect): TRect;
        end;
      class operator TRect.Add(const A, C: TRect): TRect;
      begin
        Result.L := A.L + C.L;
        Result.T := A.T + C.T;
        Result.R := A.R + C.R;
        Result.B := A.B + C.B
      end;
      var X, Y, Z: TRect;
      begin
        X.L := 1; Y.L := 2;
        Z := X + Y;
        WriteLn(Z.L)
      end.
      ''';

procedure TOperatorTests.TestSem_RecordAdd_Resolves;
var
  Prog: TProgram;
begin
  Prog := Self.AnalyseSrc(RectSrc);
  Prog.Free();
end;

{ The resolved operator must be LOWERED into a TMethodCallExpr: the record /
  sret / ARC machinery in all three backends keys on NODE CLASS
  (`Asgn.Expr is TMethodCallExpr`, EmitRecordCallSretAt's dispatch, ...), not
  on a flag, so the binary wrapper is dropped and the owning slot is rebound
  to the synthesised static call. }
procedure TOperatorTests.TestSem_RecordAdd_LoweredCallSet;
var
  Prog:  TProgram;
  I:     Integer;
  Asgn:  TAssignment;
  Call:  TMethodCallExpr;
  MD:    TMethodDecl;
  Found: Boolean;
begin
  Prog := Self.AnalyseSrc(RectSrc);
  try
    Found := False;
    for I := 0 to Prog.Block.Stmts.Count - 1 do
    begin
      if not (TObject(Prog.Block.Stmts.Items[I]) is TAssignment) then Continue;
      Asgn := TAssignment(Prog.Block.Stmts.Items[I]);
      if not SameText(Asgn.Name, 'Z') then Continue;
      AssertTrue('operator lowered to a method call', Asgn.Expr is TMethodCallExpr);
      Call := TMethodCallExpr(Asgn.Expr);
      AssertEquals('receiver is the owner type', 'TRect', Call.ObjectName);
      AssertEquals('method is the operator name', 'Add', Call.Name);
      AssertTrue('static call (no Self)', Call.IsStaticCall);
      AssertEquals('two arguments', 2, Call.Args.Count);
      AssertNotNull('resolved method', TObject(Call.ResolvedMethod));
      MD := TMethodDecl(Call.ResolvedMethod);
      AssertTrue('resolved to an operator', MD.IsOperator);
      AssertTrue('resolved to okAdd', MD.OperatorKind = okAdd);
      AssertNotNull('result type', Call.ResolvedType);
      AssertEquals('result type', 'TRect', Call.ResolvedType.Name);
      Found := True;
    end;
    AssertTrue('lowered assignment found', Found);
  finally
    Prog.Free();
  end;
end;

procedure TOperatorTests.TestSem_NoOperator_StillErrors;
const
  Src = '''
      program P;
      type
        TRect = record
          L: Integer;
        end;
      var X, Y, Z: TRect;
      begin
        Z := X + Y
      end.
      ''';
begin
  Self.AnalyseExpectError(Src);
end;

procedure TOperatorTests.TestSem_BuiltinSet_Unaffected;
const
  Src = '''
      program P;
      type
        TCol = (cRed, cGreen, cBlue);
        TCols = set of TCol;
      var A, B, C: TCols;
      begin
        A := [cRed];
        B := [cBlue];
        C := A + B;
        if cRed in C then WriteLn('yes')
      end.
      ''';
var
  Prog: TProgram;
begin
  Prog := Self.AnalyseSrc(Src);
  Prog.Free();
end;

{ Blaise keeps reference identity for class '=' — the built-in rule is tried
  first, so declaring an Equal operator does not silently change identity
  comparisons (a deliberate divergence from Delphi). }
procedure TOperatorTests.TestSem_ClassIdentityEqual_Preserved;
const
  Src = '''
      program P;
      type
        TBar = class
          X: Integer;
          class operator Equal(const A, B: TBar): Boolean;
        end;
      class operator TBar.Equal(const A, B: TBar): Boolean;
      begin
        Result := A.X = B.X
      end;
      var P1, P2: TBar;
      begin
        P1 := TBar.Create();
        P2 := P1;
        if P1 = P2 then WriteLn('same')
      end.
      ''';
var
  Prog: TProgram;
  I:    Integer;
  Stmt: TObject;
  Bin:  TBinaryExpr;
  Checked: Boolean;
begin
  Prog := Self.AnalyseSrc(Src);
  try
    Checked := False;
    for I := 0 to Prog.Block.Stmts.Count - 1 do
    begin
      Stmt := TObject(Prog.Block.Stmts.Items[I]);
      if not (Stmt is TIfStmt) then Continue;
      if not (TIfStmt(Stmt).Condition is TBinaryExpr) then Continue;
      Bin := TBinaryExpr(TIfStmt(Stmt).Condition);
      AssertNull('class = keeps identity (no operator lowering)', Bin.LoweredCall);
      Checked := True;
    end;
    AssertTrue('identity comparison found', Checked);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Phase 2 — IR                                                        }
{ ------------------------------------------------------------------ }

initialization
  RegisterTest(TOperatorTests);

end.
