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
  Classes, SysUtils, uStrCompat, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TGenericConstraintTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
    procedure AssertIntfConstraintAccepted(const ABody: string);
    procedure AssertIntfConstraintRejected(const ABody, AArg: string);
    procedure AssertConstraintErrorAt(const ABody: string; ABodyLine: Int);
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
    { Interface constraints, <T: IShape>.  A type satisfies one exactly when
      a value of it converts to the interface: the class lists it, an
      ancestor class lists it, or it lists an interface inheriting from it. }
    procedure TestSemantic_IntfConstraint_DirectImplementor_Satisfied;
    procedure TestSemantic_IntfConstraint_NonImplementor_Violation;
    procedure TestSemantic_IntfConstraint_AncestorImplementor_Satisfied;
    procedure TestSemantic_IntfConstraint_DerivedIntfImplementor_Satisfied;
    procedure TestSemantic_IntfConstraint_InterfaceItself_Satisfied;
    procedure TestSemantic_IntfConstraint_DerivedInterface_Satisfied;
    procedure TestSemantic_IntfConstraint_UnrelatedInterface_Violation;
    procedure TestSemantic_IntfConstraint_GenericClass_Satisfied;
    procedure TestSemantic_IntfConstraint_GenericClass_Violation;
    procedure TestSemantic_IntfConstraint_GenericMethod_Violation;
    { A constraint violation names the line of the instantiating use
      (BUG-20261120-constraint-error-no-location). }
    procedure TestSemantic_ConstraintError_ExplicitCall_HasLocation;
    procedure TestSemantic_ConstraintError_InferredCall_HasLocation;
    procedure TestSemantic_ConstraintError_GenericMethod_HasLocation;
    procedure TestSemantic_ConstraintError_VarDecl_HasLocation;
    procedure TestSemantic_ConstraintError_TypeDecl_HasLocation;
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
            FItem: Int;
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
            FItem: Int;
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
          TAnimal = class(TObject) X: Int; end;
          TPen<T: TAnimal> = class
            FCount: Int;
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
            FKey: Int;
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
        type TAnimal = class(TObject) X: Int; end;
        function Box<T: TAnimal>(A: T): Int;
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
        var N: Int;
        begin
          N := Id<Int>(5)
        end.
        ''');
end;

procedure TGenericConstraintTests.TestSemantic_GenericFunc_ClassConstraint_Satisfied;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(
    '''
        program Prg;
        type TAnimal = class(TObject) X: Int; end;
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
            FItem: Int;
          end;
        var B: TBox<Int>;
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
          TDog = class(TObject) X: Int; end;
          TCat = class(TObject) Y: Int; end;
        function Use<T: TDog>(A: T): Int;
        begin Result := 0 end;
        var C: TCat; N: Int;
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
          TDog = class(TObject) X: Int; end;
          TPuppy = class(TDog) Y: Int; end;
        function Use<T: TDog>(A: T): Int;
        begin Result := 0 end;
        var P: TPuppy; N: Int;
        begin
          P := TPuppy.Create();
          N := Use<TPuppy>(P);
          P.Free()
        end.
        ''');
  try AssertNotNull(Prog); finally Prog.Free(); end;
end;

const
  { Shared declarations for the interface-constraint tests.  TBigSquare
    implements IShape only through its ancestor TSquare; TCube only through
    ISolid = interface(IShape); TPlain implements nothing; IOther is
    unrelated to IShape. }
  IntfConstraintDecls = '''
    program Prg;
    type
      IShape = interface
        function Area: Int;
      end;
      ISolid = interface(IShape)
        function Volume: Int;
      end;
      IOther = interface
        function Other: Int;
      end;
      TSquare = class(TObject, IShape)
        function Area: Int;
      end;
      TBigSquare = class(TSquare)
      end;
      TCube = class(TObject, ISolid)
        function Area: Int;
        function Volume: Int;
      end;
      TPlain = class(TObject)
      end;
      THolder<T: IShape> = class
        FItem: T;
      end;
      TUtil = class
        function Measure<T: IShape>(const S: T): Int;
      end;
    function TSquare.Area: Int; begin Result := 4 end;
    function TCube.Area: Int; begin Result := 6 end;
    function TCube.Volume: Int; begin Result := 1 end;
    function TUtil.Measure<T>(const S: T): Int; begin Result := 0 end;
    function AreaOf<T: IShape>(const S: T): Int; begin Result := S.Area() end;

    ''';

{ Analyses IntfConstraintDecls followed by ABody as the main program block
  and fails unless it is accepted. }
procedure TGenericConstraintTests.AssertIntfConstraintAccepted(const ABody: string);
var
  Msg: string;
begin
  Msg := SemanticError(IntfConstraintDecls + ABody);
  AssertEquals('expected the program to be accepted', '', Msg);
end;

{ As above, but the program must be rejected with the constraint diagnostic
  naming AArg. }
procedure TGenericConstraintTests.AssertIntfConstraintRejected(const ABody, AArg: string);
var
  Msg: string;
begin
  Msg := SemanticError(IntfConstraintDecls + ABody);
  AssertTrue('names the unsatisfied constraint: ' + Msg,
    Pos('''' + AArg + ''' does not implement ''IShape'' (constraint ''T: IShape'')', Msg) >= 0);
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_DirectImplementor_Satisfied;
begin
  AssertIntfConstraintAccepted('''
    var S: TSquare; N: Int;
    begin
      S := TSquare.Create();
      N := AreaOf<TSquare>(S)
    end.
    ''');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_NonImplementor_Violation;
begin
  AssertIntfConstraintRejected('''
    var P: TPlain; N: Int;
    begin
      P := TPlain.Create();
      N := AreaOf<TPlain>(P)
    end.
    ''', 'TPlain');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_AncestorImplementor_Satisfied;
begin
  { TBigSquare inherits TSquare's IShape implementation }
  AssertIntfConstraintAccepted('''
    var B: TBigSquare; N: Int;
    begin
      B := TBigSquare.Create();
      N := AreaOf<TBigSquare>(B)
    end.
    ''');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_DerivedIntfImplementor_Satisfied;
begin
  { TCube implements ISolid, and every ISolid is an IShape }
  AssertIntfConstraintAccepted('''
    var C: TCube; N: Int;
    begin
      C := TCube.Create();
      N := AreaOf<TCube>(C)
    end.
    ''');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_InterfaceItself_Satisfied;
begin
  AssertIntfConstraintAccepted('''
    var I: IShape; N: Int;
    begin
      I := TSquare.Create();
      N := AreaOf<IShape>(I)
    end.
    ''');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_DerivedInterface_Satisfied;
begin
  AssertIntfConstraintAccepted('''
    var I: ISolid; N: Int;
    begin
      I := TCube.Create();
      N := AreaOf<ISolid>(I)
    end.
    ''');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_UnrelatedInterface_Violation;
begin
  AssertIntfConstraintRejected('''
    var I: IOther; N: Int;
    begin
      N := AreaOf<IOther>(I)
    end.
    ''', 'IOther');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_GenericClass_Satisfied;
begin
  AssertIntfConstraintAccepted('''
    var H: THolder<TBigSquare>;
    begin
      H := THolder<TBigSquare>.Create()
    end.
    ''');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_GenericClass_Violation;
begin
  AssertIntfConstraintRejected('''
    var H: THolder<TPlain>;
    begin
    end.
    ''', 'TPlain');
end;

procedure TGenericConstraintTests.TestSemantic_IntfConstraint_GenericMethod_Violation;
begin
  AssertIntfConstraintRejected('''
    var U: TUtil; P: TPlain; N: Int;
    begin
      U := TUtil.Create();
      P := TPlain.Create();
      N := U.Measure<TPlain>(P)
    end.
    ''', 'TPlain');
end;

{ The constraint diagnostic for ABody must give the source line that holds
  the instantiating use: ABodyLine counts from 1 at ABody's first line. }
procedure TGenericConstraintTests.AssertConstraintErrorAt(const ABody: string;
  ABodyLine: Int);
var
  Msg: string;
  DeclLines: Int;
  I: Int;
begin
  DeclLines := 0;
  for I := 0 to Length(IntfConstraintDecls) - 1 do
    if StrAt(IntfConstraintDecls, I) = 10 then
      Inc(DeclLines);
  Msg := SemanticError(IntfConstraintDecls + ABody);
  AssertTrue('names the unsatisfied constraint: ' + Msg,
    Pos('does not implement ''IShape''', Msg) >= 0);
  AssertTrue('gives the instantiating line: ' + Msg,
    Pos(Format(' at line %d col ', [DeclLines + ABodyLine]), Msg) >= 0);
end;

procedure TGenericConstraintTests.TestSemantic_ConstraintError_ExplicitCall_HasLocation;
begin
  AssertConstraintErrorAt('''
    var P: TPlain; N: Int;
    begin
      P := TPlain.Create();
      N := AreaOf<TPlain>(P)
    end.
    ''', 4);
end;

procedure TGenericConstraintTests.TestSemantic_ConstraintError_InferredCall_HasLocation;
begin
  AssertConstraintErrorAt('''
    var P: TPlain; N: Int;
    begin
      P := TPlain.Create();

      N := AreaOf(P)
    end.
    ''', 5);
end;

procedure TGenericConstraintTests.TestSemantic_ConstraintError_GenericMethod_HasLocation;
begin
  AssertConstraintErrorAt('''
    var U: TUtil; P: TPlain; N: Int;
    begin
      U := TUtil.Create();
      P := TPlain.Create();
      N := U.Measure<TPlain>(P)
    end.
    ''', 5);
end;

procedure TGenericConstraintTests.TestSemantic_ConstraintError_VarDecl_HasLocation;
begin
  AssertConstraintErrorAt('''
    var
      N: Int;
      H: THolder<TPlain>;
    begin
      N := 0
    end.
    ''', 3);
end;

procedure TGenericConstraintTests.TestSemantic_ConstraintError_TypeDecl_HasLocation;
begin
  AssertConstraintErrorAt('''
    type
      TAlias = class
        FH: THolder<TPlain>;
      end;
    begin
    end.
    ''', 3);
end;

initialization
  RegisterTest(TGenericConstraintTests);

end.
