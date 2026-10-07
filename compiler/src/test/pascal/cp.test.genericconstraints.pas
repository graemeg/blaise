{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.genericconstraints;

{ Tests for generic type parameter constraints:
    <T: class>        — T must be a class type
    <T: record>       — T must be a value type
    <T: SomeTypeName> — T must be that type (or subclass / implementor). }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TGenericConstraintTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestParse_GenericType_ClassConstraint;
    procedure TestParse_GenericType_RecordConstraint;
    procedure TestParse_GenericType_NamedConstraint;
    procedure TestParse_GenericType_TwoParamsWithMixedConstraints;
    procedure TestParse_GenericFunc_ClassConstraint;
    procedure TestParse_GenericFunc_NamedConstraint;
    procedure TestSemantic_GenericFunc_ClassConstraint_Violation;
    procedure TestSemantic_GenericFunc_ClassConstraint_Satisfied;
    procedure TestSemantic_GenericType_ClassConstraint_Violation;
    procedure TestSemantic_GenericFunc_NamedConstraint_Violation;
    procedure TestSemantic_GenericFunc_NamedConstraint_Satisfied;
  end;

implementation

function TGenericConstraintTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try Result := P.Parse(); finally P.Free(); L.Free(); end;
end;

function TGenericConstraintTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try A.Analyse(Result); finally A.Free(); end;
end;

procedure TGenericConstraintTests.AnalyseExpectError(const ASrc: string);
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

procedure TGenericConstraintTests.TestParse_GenericType_ClassConstraint;
var Prog: TProgram; TD: TTypeDecl; GD: TGenericTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Prg;
        type
          TBox<T: class> = class
            FItem: Integer;
          end;
        begin end.
        ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertTrue(TD.Def is TGenericTypeDef);
    GD := TGenericTypeDef(TD.Def);
    AssertEquals(1, GD.ParamNames.Count);
    AssertEquals('T', GD.ParamNames[0]);
    AssertEquals('class', GD.ParamConstraints[0]);
  finally Prog.Free(); end;
end;

procedure TGenericConstraintTests.TestParse_GenericType_RecordConstraint;
var Prog: TProgram; TD: TTypeDecl; GD: TGenericTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Prg;
        type
          TBox<T: record> = class
            FItem: Integer;
          end;
        begin end.
        ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    GD := TGenericTypeDef(TD.Def);
    AssertEquals('record', GD.ParamConstraints[0]);
  finally Prog.Free(); end;
end;

procedure TGenericConstraintTests.TestParse_GenericType_NamedConstraint;
var Prog: TProgram; TD: TTypeDecl; GD: TGenericTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Prg;
        type
          TAnimal = class(TObject) X: Integer; end;
          TPen<T: TAnimal> = class
            FCount: Integer;
          end;
        begin end.
        ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[1]);
    GD := TGenericTypeDef(TD.Def);
    AssertEquals('TAnimal', GD.ParamConstraints[0]);
  finally Prog.Free(); end;
end;

procedure TGenericConstraintTests.TestParse_GenericType_TwoParamsWithMixedConstraints;
var Prog: TProgram; TD: TTypeDecl; GD: TGenericTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Prg;
        type
          TPair<K, V: class> = class
            FKey: Integer;
          end;
        begin end.
        ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    GD := TGenericTypeDef(TD.Def);
    AssertEquals(2, GD.ParamNames.Count);
    AssertEquals('', GD.ParamConstraints[0]);  { K unconstrained }
    AssertEquals('class', GD.ParamConstraints[1]);
  finally Prog.Free(); end;
end;

procedure TGenericConstraintTests.TestParse_GenericFunc_ClassConstraint;
var Prog: TProgram; MD: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Prg;
        function Id<T: class>(A: T): T;
        begin Result := A end;
        begin end.
        ''');
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertNotNull(MD.TypeParams);
    AssertEquals('class', MD.TypeParamConstraints[0]);
  finally Prog.Free(); end;
end;

procedure TGenericConstraintTests.TestParse_GenericFunc_NamedConstraint;
var Prog: TProgram; MD: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Prg;
        type TAnimal = class(TObject) X: Integer; end;
        function Box<T: TAnimal>(A: T): Integer;
        begin Result := 0 end;
        begin end.
        ''');
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('TAnimal', MD.TypeParamConstraints[0]);
  finally Prog.Free(); end;
end;

procedure TGenericConstraintTests.TestSemantic_GenericFunc_ClassConstraint_Violation;
begin
  { Integer is not a class — must raise }
  AnalyseExpectError(
    '''
        program Prg;
        function Id<T: class>(A: T): T;
        begin Result := A end;
        var N: Integer;
        begin
          N := Id<Integer>(5)
        end.
        ''');
end;

procedure TGenericConstraintTests.TestSemantic_GenericFunc_ClassConstraint_Satisfied;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(
    '''
        program Prg;
        type TAnimal = class(TObject) X: Integer; end;
        function Id<T: class>(A: T): T;
        begin Result := A end;
        var A: TAnimal;
        begin
          A := TAnimal.Create();
          A := Id<TAnimal>(A);
          A.Free()
        end.
        ''');
  try AssertNotNull(Prog); finally Prog.Free(); end;
end;

procedure TGenericConstraintTests.TestSemantic_GenericType_ClassConstraint_Violation;
begin
  AnalyseExpectError(
    '''
        program Prg;
        type
          TBox<T: class> = class
            FItem: Integer;
          end;
        var B: TBox<Integer>;
        begin end.
        ''');
end;

procedure TGenericConstraintTests.TestSemantic_GenericFunc_NamedConstraint_Violation;
begin
  { TCat does not inherit from TDog → must raise }
  AnalyseExpectError(
    '''
        program Prg;
        type
          TDog = class(TObject) X: Integer; end;
          TCat = class(TObject) Y: Integer; end;
        function Use<T: TDog>(A: T): Integer;
        begin Result := 0 end;
        var C: TCat; N: Integer;
        begin
          C := TCat.Create();
          N := Use<TCat>(C);
          C.Free()
        end.
        ''');
end;

procedure TGenericConstraintTests.TestSemantic_GenericFunc_NamedConstraint_Satisfied;
var Prog: TProgram;
begin
  { TPuppy inherits from TDog → OK }
  Prog := AnalyseSrc(
    '''
        program Prg;
        type
          TDog = class(TObject) X: Integer; end;
          TPuppy = class(TDog) Y: Integer; end;
        function Use<T: TDog>(A: T): Integer;
        begin Result := 0 end;
        var P: TPuppy; N: Integer;
        begin
          P := TPuppy.Create();
          N := Use<TPuppy>(P);
          P.Free()
        end.
        ''');
  try AssertNotNull(Prog); finally Prog.Free(); end;
end;

initialization
  RegisterTest(TGenericConstraintTests);

end.
