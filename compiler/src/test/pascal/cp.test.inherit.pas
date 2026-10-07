{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.inherit;

{ Tests for class inheritance, self-referential types, and nil. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TInheritTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
    procedure ParseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
  published
    { ------------------------------------------------------------------ }
    { nil literal                                                          }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Nil_Keyword;
    procedure TestParse_Nil_IsTNilLiteral;
    procedure TestSemantic_Nil_AssignToClassVar_OK;
    procedure TestSemantic_Nil_AssignToIntVar_RaisesError;
    procedure TestSemantic_Nil_CompareWithClassVar_OK;

    { ------------------------------------------------------------------ }
    { Self-referential types                                               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SelfRef_DoesNotRaiseError;
    procedure TestSemantic_SelfRef_FieldTypeIsClass;
    procedure TestCodegen_SelfRef_Create_AllocatesCorrectSize;

    { ------------------------------------------------------------------ }
    { Class inheritance — fields                                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Inherit_ParentFieldVisible;
    procedure TestSemantic_Inherit_ChildFieldVisible;
    procedure TestSemantic_Inherit_TotalSizeIncludesParent;
    procedure TestCodegen_Inherit_Create_AllocatesTotalSize;

    { ------------------------------------------------------------------ }
    { Class inheritance — methods                                          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Inherit_MethodCallOnChild_Resolves;
    procedure TestSemantic_Inherit_UnknownMethod_RaisesError;

    { ------------------------------------------------------------------ }
    { 'inherited' keyword                                                  }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Inherited_IsOwnToken;
    procedure TestParse_Inherited_NoArgs_CreatesNode;
    procedure TestSemantic_Inherited_NoArgs_OK;
    procedure TestSemantic_Inherited_WithArgs_OK;

    { Mandatory parentheses: a bare 'inherited Method' (no parens) is a
      call and must carry (), in both statement and expression position. }
    procedure TestParse_Inherited_BareStmt_RequiresParens;
    procedure TestParse_Inherited_BareExpr_RequiresParens;

    { ------------------------------------------------------------------ }
    { TObject.InheritsFrom                                                 }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_InheritsFrom_OnPointerVar_OK;
    procedure TestSemantic_InheritsFrom_OnClassInstance_OK;
    procedure TestSemantic_InheritsFrom_ReturnsBoolean;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TInheritTests.ParseSrc(const ASrc: string): TProgram;
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

function TInheritTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TInheritTests.AnalyseExpectError(const ASrc: string);
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

procedure TInheritTests.ParseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
var Prog: TProgram;
begin
  try
    Prog := ParseSrc(ASrc);
    Prog.Free();
    Fail('Expected EParseError');
  except
    on E: EParseError do
      AssertTrue('error message contains "' + AExpectedSubstr + '" (got: ' +
        E.Message + ')', Pos(AExpectedSubstr, E.Message) >= 0);
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcSelfRef =
    '''
        program P;
        type
          TNode = class
            Value: Integer;
            Next:  TNode;
          end;
        var N: TNode;
        begin
          N := TNode.Create();
          N.Value := 1;
          N.Next := nil
        end.
        ''';

  SrcInherit =
    '''
        program P;
        type
          TAnimal = class
            Age: Integer;
          end;
          TDog = class(TAnimal)
            Legs: Integer;
          end;
        var D: TDog;
        begin
          D := TDog.Create();
          D.Age := 3;
          D.Legs := 4
        end.
        ''';

  SrcInheritMethod =
    '''
        program P;
        type
          TBase = class
            X: Integer;
            procedure SetX(V: Integer);
            begin
              Self.X := V
            end;
          end;
          TChild = class(TBase)
            Y: Integer;
          end;
        var C: TChild;
        begin
          C := TChild.Create();
          C.SetX(10);
          C.Y := 20
        end.
        ''';

{ ------------------------------------------------------------------ }
{ nil literal tests                                                   }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestLexer_Nil_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('nil');
  try
    T := L.Next();
    AssertEquals('nil token', Ord(tkNil), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TInheritTests.TestParse_Nil_IsTNilLiteral;
var
  Prog:   TProgram;
  Assign: TFieldAssignment;
begin
  Prog := ParseSrc(SrcSelfRef);
  try
    { third stmt: N.Next := nil }
    AssertTrue('stmt is TFieldAssignment', Prog.Block.Stmts[2] is TFieldAssignment);
    Assign := TFieldAssignment(Prog.Block.Stmts[2]);
    AssertTrue('rhs is TNilLiteral', Assign.Expr is TNilLiteral);
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestSemantic_Nil_AssignToClassVar_OK;
begin
  AnalyseSrc(SrcSelfRef).Free();
end;

procedure TInheritTests.TestSemantic_Nil_AssignToIntVar_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        begin
          N := nil
        end.
        ''');
end;

procedure TInheritTests.TestSemantic_Nil_CompareWithClassVar_OK;
begin
  AnalyseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        var N: Integer;
        begin
          F := TFoo.Create();
          if F = nil then
            N := 0
          else
            N := 1
        end.
        ''').Free();
end;

{ ------------------------------------------------------------------ }
{ Self-referential type tests                                         }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_SelfRef_DoesNotRaiseError;
begin
  AnalyseSrc(SrcSelfRef).Free();
end;

procedure TInheritTests.TestSemantic_SelfRef_FieldTypeIsClass;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  FD:   TFieldDecl;
begin
  Prog := AnalyseSrc(SrcSelfRef);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    CD := TClassTypeDef(TD.Def);
    { Second field: Next: TNode }
    FD := TFieldDecl(CD.Fields[1]);
    AssertNotNull('Next field resolved', FD.ResolvedType);
    AssertEquals('Next field is tyClass',
      Ord(tyClass), Ord(FD.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestCodegen_SelfRef_Create_AllocatesCorrectSize;
begin
  { TNode: vptr (8) + Integer Value @ 8 + 4-byte pad + TNode pointer @ 16
    = 24 bytes.  The Next pointer must be 8-aligned so the alignment pad
    sits between Value and Next.  Too small an allocation corrupts the heap
    without a reliable symptom, so the size is pinned in the assembly. }
  AssertEquals('_ClassAlloc of 24 bytes for TNode', '',
    AsmMissing(SrcSelfRef, 'movq $24, %rdi', 'movz x0, #24'));
end;

{ ------------------------------------------------------------------ }
{ Inheritance — field tests                                           }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_Inherit_ParentFieldVisible;
begin
  { D.Age := 3 should resolve — Age is inherited from TAnimal }
  AnalyseSrc(SrcInherit).Free();
end;

procedure TInheritTests.TestSemantic_Inherit_ChildFieldVisible;
begin
  { D.Legs := 4 should resolve — Legs is TDog's own field }
  AnalyseSrc(SrcInherit).Free();
end;

procedure TInheritTests.TestSemantic_Inherit_TotalSizeIncludesParent;
var
  Prog:  TProgram;
  Sym:   TSymbol;
  RT:    TRecordTypeDesc;
begin
  Prog := AnalyseSrc(SrcInherit);
  try
    { TAnimal: vptr (8) + Age (4) = 12 total.
      TDog: vptr (8) + Age (4) + Legs (4) = 16 total. }
    Sym := Prog.SymbolTable.Lookup('TDog');
    AssertNotNull('TDog symbol', Sym);
    RT := TRecordTypeDesc(Sym.TypeDesc);
    AssertEquals('TDog total size = 16', 16, RT.TotalSize());
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestCodegen_Inherit_Create_AllocatesTotalSize;
begin
  { TDog.Create allocates TotalSize: vptr + Age + Legs = 16 bytes }
  AssertEquals('_ClassAlloc of 16 bytes for TDog', '',
    AsmMissing(SrcInherit, 'movq $16, %rdi', 'movz x0, #16'));
end;

{ ------------------------------------------------------------------ }
{ Inheritance — method tests                                          }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_Inherit_MethodCallOnChild_Resolves;
begin
  { C.SetX(10) should resolve even though SetX is defined on TBase }
  AnalyseSrc(SrcInheritMethod).Free();
end;

procedure TInheritTests.TestSemantic_Inherit_UnknownMethod_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TBase = class
            X: Integer;
          end;
          TChild = class(TBase)
            Y: Integer;
          end;
        var C: TChild;
        begin
          C := TChild.Create();
          C.NoSuchMethod()
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ 'inherited' keyword tests                                          }
{ ------------------------------------------------------------------ }

const
  SrcInheritedNoArgs =
    '''
        program P;
        type
          TBase = class
            X: Integer;
            procedure Init;
          end;
          TChild = class(TBase)
            Y: Integer;
            procedure Init;
          end;
        procedure TBase.Init;
        begin
          Self.X := 0
        end;
        procedure TChild.Init;
        begin
          inherited Init();
          Self.Y := 0
        end;
        var C: TChild;
        begin
          C := TChild.Create()
        end.
        ''';

  SrcInheritedWithArgs =
    '''
        program P;
        type
          TBase = class
            X: Integer;
            procedure SetX(V: Integer);
          end;
          TChild = class(TBase)
            procedure SetX(V: Integer);
          end;
        procedure TBase.SetX(V: Integer);
        begin
          Self.X := V
        end;
        procedure TChild.SetX(V: Integer);
        begin
          inherited SetX(V)
        end;
        var C: TChild;
        begin
          C := TChild.Create()
        end.
        ''';

procedure TInheritTests.TestLexer_Inherited_IsOwnToken;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('inherited');
  try
    T := L.Next();
    AssertEquals('inherited token kind', Ord(tkInherited), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TInheritTests.TestParse_Inherited_NoArgs_CreatesNode;
var
  Prog:  TProgram;
  MDecl: TMethodDecl;
  Stmt:  TASTStmt;
begin
  Prog := ParseSrc(SrcInheritedNoArgs);
  try
    { TChild.Init is the second standalone proc (ProcDecls[1]) }
    AssertTrue('at least 2 ProcDecls', Prog.Block.ProcDecls.Count >= 2);
    MDecl := TMethodDecl(Prog.Block.ProcDecls[1]);
    AssertNotNull('TChild.Init() found', MDecl);
    AssertTrue('body has at least one stmt', MDecl.Body.Stmts.Count >= 1);
    Stmt := TASTStmt(MDecl.Body.Stmts[0]);
    AssertTrue('first stmt is TInheritedCallStmt', Stmt is TInheritedCallStmt);
    AssertEquals('method name is Init',
      'Init', TInheritedCallStmt(Stmt).Name);
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestSemantic_Inherited_NoArgs_OK;
begin
  AnalyseSrc(SrcInheritedNoArgs).Free();
end;

procedure TInheritTests.TestSemantic_Inherited_WithArgs_OK;
begin
  AnalyseSrc(SrcInheritedWithArgs).Free();
end;

procedure TInheritTests.TestParse_Inherited_BareStmt_RequiresParens;
const Src = '''
    program P;
    type
      TBase = class
        procedure Init;
      end;
      TChild = class(TBase)
        procedure Init;
      end;
    procedure TBase.Init;
    begin
    end;
    procedure TChild.Init;
    begin
      inherited Init
    end;
    begin
    end.
    ''';
begin
  ParseExpectErrorMsg(Src, 'requires () for a call');
end;

procedure TInheritTests.TestParse_Inherited_BareExpr_RequiresParens;
const Src = '''
    program P;
    type
      TBase = class
        function Value: Integer;
      end;
      TChild = class(TBase)
        function Value: Integer;
      end;
    function TBase.Value: Integer;
    begin
      Result := 1
    end;
    function TChild.Value: Integer;
    begin
      Result := inherited Value + 1
    end;
    begin
    end.
    ''';
begin
  ParseExpectErrorMsg(Src, 'requires () for a call');
end;

{ ------------------------------------------------------------------ }
{ TObject.InheritsFrom                                                }
{ ------------------------------------------------------------------ }

const
  SrcInheritsFromPointer =
    '''
        program P;
        var C: Pointer;
            D: Pointer;
            B: Boolean;
        begin
          B := C.InheritsFrom(D);
        end.
        ''';

  SrcInheritsFromClassInstance =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
        var Obj: TChild;
            B: Boolean;
        begin
          B := Obj.InheritsFrom(TBase);
        end.
        ''';

procedure TInheritTests.TestSemantic_InheritsFrom_OnPointerVar_OK;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcInheritsFromPointer);
  AssertNotNull('program parsed and analysed', Prog);
  Prog.Free();
end;

procedure TInheritTests.TestSemantic_InheritsFrom_OnClassInstance_OK;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcInheritsFromClassInstance);
  AssertNotNull('program parsed and analysed', Prog);
  Prog.Free();
end;

procedure TInheritTests.TestSemantic_InheritsFrom_ReturnsBoolean;
var Prog: TProgram;
    VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcInheritsFromPointer);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[2]);  { B: Boolean }
    AssertEquals('B is Boolean', 'Boolean', VD.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TInheritTests);

end.
