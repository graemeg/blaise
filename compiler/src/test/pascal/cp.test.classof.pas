{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.classof;

{ Tests for 'class of TFoo' metaclass type support — Step 11a. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TClassOfTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
    procedure AnalyseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
  published
    { M[I] := TB stores the class's typeinfo word into a metaclass array
      element (arm64 stopped with 'array element of this type') }
    procedure TestCodegen_MetaclassArrayElementStore;
    { Parser }
    procedure TestParse_ClassOf_AsAlias;
    procedure TestParse_ClassOf_VarDecl;
    procedure TestParse_ClassOf_FieldType;

    { Semantic }
    procedure TestSemantic_ClassOf_TypeIsMetaClass;
    procedure TestSemantic_ClassOf_BaseClass;
    procedure TestSemantic_AssignClassIdent_ToMetaClass;
    procedure TestSemantic_AssignDescendant_ToBaseMetaClass;
    procedure TestSemantic_RejectUnrelatedClass_ToMetaClass;
    procedure TestSemantic_RejectClassOf_Nonclass;
    procedure TestSemantic_MetaClass_AcceptedAsPointerArg;
    procedure TestSemantic_CompareTwoMetaClassValues;

    { Codegen }

    { ClassCreate builtin (Step 11e): runtime construction via a
      metaclass value.  Lowers to '_ClassCreate(Cls)' followed by a
      static call to the resolved constructor. }
    procedure TestSemantic_ClassCreate_RejectsNonMetaclassFirstArg;

    { Metaclass-var dispatch: C.Create() emits _ClassCreate + indirect
      ctor call via vtable, not a static call to the base Create. }
    procedure TestSemantic_MetaclassVar_Create_Accepted;

    { Bare 'C.Create' (no parens) on a metaclass variable must give the
      mandatory-parentheses diagnostic, not the misleading
      'is not a record or class' error. }
    procedure TestSemantic_MetaclassVar_BareCreate_RequiresParens;

    { Create through a class reference that is not a plain variable -- a
      field of Self, a field, an element, a call result -- in statement and
      expression position: metaclass dispatch on the receiver expression
      (all of these were rejected) }
    procedure TestSemantic_MetaclassExprReceiver_Create_Accepted;
  end;

implementation

function TClassOfTests.ParseSrc(const ASrc: string): TProgram;
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

function TClassOfTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TClassOfTests.AnalyseExpectError(const ASrc: string);
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

procedure TClassOfTests.AnalyseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do
      AssertTrue('error message contains "' + AExpectedSubstr + '" (got: ' +
        E.Message + ')', Pos(AExpectedSubstr, E.Message) >= 0);
  end;
end;

{ ------------------------------------------------------------------ }
{  Parser                                                             }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestParse_ClassOf_AsAlias;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
          TBaseClass = class of TBase;
        begin end.
        ''';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('two type decls', 2, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestParse_ClassOf_VarDecl;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin end.
        ''';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestParse_ClassOf_FieldType;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
          TWrap = class(TObject)
            Cls: class of TBase;
          end;
        begin end.
        ''';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('two type decls', 2, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestSemantic_ClassOf_TypeIsMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin end.
        ''';
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(Src);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertEquals('var type kind is tyMetaClass',
      Ord(tyMetaClass), Ord(VD.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_ClassOf_BaseClass;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin end.
        ''';
var
  Prog: TProgram;
  VD:   TVarDecl;
  MC:   TMetaClassTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    MC := TMetaClassTypeDesc(VD.ResolvedType);
    AssertNotNull('metaclass has BaseClass', MC.BaseClass);
    AssertEquals('BaseClass is TBase', 'TBase', MC.BaseClass.Name);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_AssignClassIdent_ToMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin
          C := TBase
        end.
        ''';
var Prog: TProgram;
begin
  { Should analyse without error. }
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_AssignDescendant_ToBaseMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase    = class(TObject) end;
          TDerived = class(TBase) end;
        var C: class of TBase;
        begin
          C := TDerived
        end.
        ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_RejectUnrelatedClass_ToMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase  = class(TObject) end;
          TOther = class(TObject) end;
        var C: class of TBase;
        begin
          C := TOther
        end.
        ''';
begin
  AnalyseExpectError(Src);
end;

procedure TClassOfTests.TestSemantic_RejectClassOf_Nonclass;
const
  Src =
    '''
        program P;
        type
          TInt = class of Integer;
        begin end.
        ''';
begin
  AnalyseExpectError(Src);
end;

procedure TClassOfTests.TestSemantic_MetaClass_AcceptedAsPointerArg;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        procedure Take(const P: Pointer);
        begin end;
        begin
          Take(TBase)
        end.
        ''';
var Prog: TProgram;
begin
  { A metaclass-typed value passes through an untyped Pointer arg. }
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_CompareTwoMetaClassValues;
const
  Src =
    '''
        program P;
        type
          TBase    = class(TObject) end;
          TDerived = class(TBase) end;
        var B: Boolean;
        begin
          B := TBase = TDerived
        end.
        ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ ClassCreate builtin                                                  }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestSemantic_ClassCreate_RejectsNonMetaclassFirstArg;
begin
  AnalyseExpectError(
    '''
        program P;
        type TFoo = class(TObject) end;
        var F: TFoo;
        begin
          F := ClassCreate(F)
        end.
        '''
  );
end;

{ ---------- Metaclass-var C.Create() dispatch tests ---------- }

procedure TClassOfTests.TestSemantic_MetaclassVar_Create_Accepted;
const Src = '''
    program P;
    type
      TFoo = class(TObject)
        constructor Create;
      end;
    constructor TFoo.Create; begin end;
    var C: class of TFoo; F: TFoo;
    begin
      C := TFoo;
      F := C.Create()
    end.
    ''';
begin
  AnalyseSrc(Src);
end;

procedure TClassOfTests.TestSemantic_MetaclassExprReceiver_Create_Accepted;
const Src = '''
    program P;
    type
      TFoo = class(TObject)
        constructor Create(N: Integer);
      end;
      TFooClass = class of TFoo;
      THolder = class
        FCls: TFooClass;
        procedure Run();
      end;
    constructor TFoo.Create(N: Integer); begin end;
    function GetCls(): TFooClass; begin Result := TFoo end;
    procedure THolder.Run();
    var F: TFoo;
    begin
      FCls.Create(1);
      F := FCls.Create(2)
    end;
    var H: THolder; A: array of TFooClass; F: TFoo;
    begin
      H.FCls.Create(3);
      A[0].Create(4);
      GetCls().Create(5);
      F := H.FCls.Create(6);
      F := A[0].Create(7);
      F := GetCls().Create(8)
    end.
    ''';
var
  Prog: TProgram;
  I: Integer;
  S: TMethodCallStmt;
  E: TMethodCallExpr;
begin
  Prog := AnalyseSrc(Src);
  try
    for I := 0 to 2 do
    begin
      S := TMethodCallStmt(Prog.Block.Stmts.Items[I]);
      AssertTrue('statement ' + IntToStr(I) + ' dispatches on the receiver',
        S.IsConstructorCall and S.IsMetaclassDispatch and (S.ObjExpr <> nil));
    end;
    for I := 3 to 5 do
    begin
      E := TMethodCallExpr(TAssignment(Prog.Block.Stmts.Items[I]).Expr);
      AssertTrue('expression ' + IntToStr(I) + ' dispatches on the receiver',
        E.IsConstructorCall and E.IsMetaclassDispatch and (E.ObjExpr <> nil));
    end;
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_MetaclassVar_BareCreate_RequiresParens;
const Src = '''
    program P;
    type
      TFoo = class(TObject)
        constructor Create;
      end;
    constructor TFoo.Create; begin end;
    var C: class of TFoo; F: TFoo;
    begin
      C := TFoo;
      F := C.Create
    end.
    ''';
begin
  AnalyseExpectErrorMsg(Src, 'requires () for a call');
end;

procedure TClassOfTests.TestCodegen_MetaclassArrayElementStore;
const
  Src = '''
      program P;
      type
        TA = class end;
        TB = class(TA) end;
        TAC = class of TA;
      var M: array[0..1] of TAC;
      begin
        M[1] := TB
      end.
      ''';
begin
  AssertEquals('the typeinfo word is stored', '',
    AsmMissing(Src, 'leaq typeinfo_TB(%rip)', 'adrp x0, _typeinfo_TB@PAGE'));
end;

initialization
  RegisterTest(TClassOfTests);
end.
