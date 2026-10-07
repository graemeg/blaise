{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.interfaces;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TInterfaceTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_Interface_Empty;
    procedure TestParse_Interface_WithMethods;
    procedure TestParse_Interface_WithParent;
    procedure TestParse_Class_ImplementsInterface;
    procedure TestParse_Class_ImplementsMultiple;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Interface_Registered;
    procedure TestSemantic_Interface_IsInterfaceKind;
    procedure TestSemantic_Interface_MethodsRegistered;
    procedure TestSemantic_ClassImplements_OK;
    procedure TestSemantic_ClassImplements_MissingMethod_RaisesError;
    procedure TestSemantic_ClassWithInterfaceAsFirstParent_OK;
    procedure TestSemantic_ClassWithInterfaceAsFirstParent_InheritsFromTObject;

    { ------------------------------------------------------------------ }
    { Semantic — is/as with interface types                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IsExpr_Interface_OK;
    procedure TestSemantic_IsExpr_Interface_ResultIsBoolean;
    procedure TestSemantic_AsExpr_Interface_OK;
    procedure TestSemantic_AsExpr_Interface_ResultType;

    { ------------------------------------------------------------------ }
    { Semantic — IInterface built-in                                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IInterface_Registered;
    procedure TestSemantic_IInterface_IsInterfaceKind;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { ARC on interface references                                          }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Supports() intrinsic — 2-arg and 3-arg forms                        }
    { ------------------------------------------------------------------ }
    procedure TestParse_Supports_TwoArg_ProducesSupportsExpr;
    procedure TestParse_Supports_ThreeArg_ProducesSupportsExpr;
    procedure TestSemantic_Supports_TwoArg_ResultIsBoolean;
    procedure TestSemantic_Supports_ThreeArg_ResultIsBoolean;
    procedure TestSemantic_Supports_NonInterface_RaisesError;

    { ------------------------------------------------------------------ }
    { Interface argument passing — non-identifier expressions              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Regression — interface field shadowing a same-named global          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_InterfaceField_ShadowsGlobal_OK;

    { ------------------------------------------------------------------ }
    { Interface properties                                                 }
    { ------------------------------------------------------------------ }
    procedure TestParse_Interface_WithProperty;
    procedure TestSemantic_InterfaceProperty_Registered;
    procedure TestSemantic_InterfaceProperty_UnknownAccessor_RaisesError;
    procedure TestSemantic_InterfaceProperty_WriteToReadOnly_RaisesError;
    procedure TestSemantic_InterfaceProperty_InheritedFromParent_OK;

    { ------------------------------------------------------------------ }
    { Regression — interface idents as values; interface-returning        }
    { interface-method calls                                              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Regression — itab-dispatch argument ABI; discarded sret returns     }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Forward interface declarations  (IFoo = interface;)                 }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ForwardInterface_CompletedByFullDecl;
    procedure TestSemantic_ForwardInterface_Unresolved_RaisesError;
  end;

implementation

const
  SrcInterfaceEmpty =
    '''
        program P;
        type
          IFoo = interface
          end;
        begin
        end.
        ''';

  SrcInterfaceWithMethods =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
            function GetVal: Integer;
          end;
        begin
        end.
        ''';

  SrcInterfaceWithParent =
    '''
        program P;
        type
          IBase = interface
            procedure Base;
          end;
          IChild = interface(IBase)
            procedure Child;
          end;
        begin
        end.
        ''';

  SrcClassImplements =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
            function GetVal: Integer;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
            function GetVal: Integer;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        function TFoo.GetVal: Integer;
        begin
          Result := 42
        end;
        begin
        end.
        ''';

  SrcClassImplementsMultiple =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          IBar = interface
            procedure DoBar;
          end;
          TFoo = class(TObject, IFoo, IBar)
            procedure DoIt;
            procedure DoBar;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        procedure TFoo.DoBar;
        begin
        end;
        begin
        end.
        ''';

  SrcClassMissingMethod =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
          end;
        begin
        end.
        ''';

  { TFoo = class(IFoo) — interface as sole parent; TObject must be implied }
  SrcClassInterfaceOnlyParent =
    'program P;'                               + LineEnding +
    'type'                                     + LineEnding +
    '  IFoo = interface'                       + LineEnding +
    '    procedure DoIt;'                      + LineEnding +
    '  end;'                                   + LineEnding +
    '  TFoo = class(IFoo)'                     + LineEnding +
    '    procedure DoIt;'                      + LineEnding +
    '  end;'                                   + LineEnding +
    'procedure TFoo.DoIt();'                     + LineEnding +
    'begin'                                    + LineEnding +
    'end;'                                     + LineEnding +
    'begin'                                    + LineEnding +
    'end.';

  SrcIsExprInterface =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        var
          T: TFoo;
          R: Boolean;
        begin
          T := TFoo.Create();
          R := T is IFoo
        end.
        ''';

  SrcAsExprInterface =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        var
          T: TFoo;
          F: IFoo;
        begin
          T := TFoo.Create();
          F := T as IFoo
        end.
        ''';

  { Regression (issue #64): a class has an interface-typed field 'im' AND the
    program has a same-named global variable 'im' of a different type (the
    class itself).  Inside a method body the field must shadow the global —
    `im := am` where am is Iprinter must resolve as a field assignment, not
    as an assignment to the global 'im: Tmi'. }
  SrcInterfaceFieldShadowsGlobal =
    '''
        program P;
        type
          Iprinter = interface
            procedure print;
          end;
          Toutput = class(TObject, Iprinter)
            fField: Integer;
            procedure print;
          end;
          Tmi = class
            im: Iprinter;
            constructor create(am: Iprinter);
            procedure use;
          end;
        procedure Toutput.print;
        begin
        end;
        constructor Tmi.Create(am: Iprinter);
        begin
          im := am;
        end;
        procedure Tmi.use;
        begin
          im.print();
        end;
        var
          im: Tmi;
        begin
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TInterfaceTests.ParseSrc(const ASrc: string): TProgram;
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

function TInterfaceTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA     := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

procedure TInterfaceTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(ASrc);
  SA   := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Prog);
      Fail('Expected ESemanticError but none was raised');
    except
      on E: ESemanticError do
        { expected };
    end;
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestParse_Interface_Empty;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcInterfaceEmpty);
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('name is IFoo', 'IFoo', TD.Name);
    AssertTrue('def is TInterfaceTypeDef', TD.Def is TInterfaceTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Interface_WithMethods;
var
  Prog: TProgram;
  ITD:  TInterfaceTypeDef;
begin
  Prog := ParseSrc(SrcInterfaceWithMethods);
  try
    ITD := TInterfaceTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('two methods', 2, ITD.Methods.Count);
    AssertEquals('first method DoIt',   'DoIt',   TMethodDecl(ITD.Methods[0]).Name);
    AssertEquals('second method GetVal','GetVal',  TMethodDecl(ITD.Methods[1]).Name);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Interface_WithParent;
var
  Prog:  TProgram;
  Child: TInterfaceTypeDef;
begin
  Prog := ParseSrc(SrcInterfaceWithParent);
  try
    Child := TInterfaceTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    AssertEquals('parent is IBase', 'IBase', Child.ParentName);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Class_ImplementsInterface;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcClassImplements);
  try
    { type decl index 0 = IFoo, index 1 = TFoo }
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    AssertEquals('one implements name', 1, CD.ImplementsNames.Count);
    AssertEquals('implements IFoo', 'IFoo', CD.ImplementsNames[0]);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Class_ImplementsMultiple;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcClassImplementsMultiple);
  try
    { type decl indices 0=IFoo, 1=IBar, 2=TFoo }
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[2]).Def);
    AssertEquals('two implements names', 2, CD.ImplementsNames.Count);
    AssertEquals('first is IFoo', 'IFoo', CD.ImplementsNames[0]);
    AssertEquals('second is IBar', 'IBar', CD.ImplementsNames[1]);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestSemantic_Interface_Registered;
var
  Prog: TProgram;
  Sym:  TSymbol;
begin
  Prog := AnalyseSrc(SrcInterfaceWithMethods);
  try
    Sym := Prog.SymbolTable.Lookup('IFoo');
    AssertNotNull('IFoo symbol exists', Sym);
    AssertEquals('IFoo is skType', Ord(skType), Ord(Sym.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Interface_IsInterfaceKind;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(SrcInterfaceWithMethods);
  try
    TD := Prog.SymbolTable.FindType('IFoo');
    AssertNotNull('IFoo type exists', TD);
    AssertEquals('kind is tyInterface', Ord(tyInterface), Ord(TD.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Interface_MethodsRegistered;
var
  Prog: TProgram;
  ITD:  TInterfaceTypeDesc;
begin
  Prog := AnalyseSrc(SrcInterfaceWithMethods);
  try
    ITD := TInterfaceTypeDesc(Prog.SymbolTable.FindType('IFoo'));
    AssertTrue('has DoIt',   ITD.HasMethod('DoIt'));
    AssertTrue('has GetVal', ITD.HasMethod('GetVal'));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_ClassImplements_OK;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcClassImplements);
  try
    { No exception = success }
    AssertNotNull('prog not nil', Prog);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_ClassImplements_MissingMethod_RaisesError;
begin
  AnalyseExpectError(SrcClassMissingMethod);
end;

procedure TInterfaceTests.TestSemantic_ClassWithInterfaceAsFirstParent_OK;
begin
  { TFoo = class(IFoo) should succeed: IFoo is moved to ImplementsNames and
    TObject is implicitly added as the class parent. }
  AnalyseSrc(SrcClassInterfaceOnlyParent).Free();
end;

procedure TInterfaceTests.TestSemantic_ClassWithInterfaceAsFirstParent_InheritsFromTObject;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(SrcClassInterfaceOnlyParent);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TFoo'));
    AssertNotNull('TFoo type exists', RT);
    { When interface-only parent is specified, TObject vtable must be copied
      so the vptr slot is present and field offsets start at offset 8. }
    AssertTrue('TFoo has a vtable (vptr from TObject)', RT.HasVTable());
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — is/as with interface types                                }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestSemantic_IsExpr_Interface_OK;
begin
  AnalyseSrc(SrcIsExprInterface).Free();
end;

procedure TInterfaceTests.TestSemantic_IsExpr_Interface_ResultIsBoolean;
var
  Prog: TProgram;
  IE:   TIsExpr;
begin
  Prog := AnalyseSrc(SrcIsExprInterface);
  try
    { Stmts[0] = T := TFoo.Create; Stmts[1] = R := T is IFoo }
    IE := TIsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('resolved type', IE.ResolvedType);
    AssertEquals('result is Boolean', Ord(tyBoolean), Ord(IE.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_AsExpr_Interface_OK;
begin
  AnalyseSrc(SrcAsExprInterface).Free();
end;

procedure TInterfaceTests.TestSemantic_AsExpr_Interface_ResultType;
var
  Prog: TProgram;
  AE:   TAsExpr;
begin
  Prog := AnalyseSrc(SrcAsExprInterface);
  try
    { Stmts[0] = T := TFoo.Create; Stmts[1] = F := T as IFoo }
    AE := TAsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('resolved type', AE.ResolvedType);
    AssertEquals('result kind is tyInterface', Ord(tyInterface), Ord(AE.ResolvedType.Kind));
    AssertEquals('result type name is IFoo', 'IFoo', AE.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — IInterface built-in                                       }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestSemantic_IInterface_Registered;
var
  Prog: TProgram;
  Sym:  TSymbol;
begin
  Prog := AnalyseSrc('program P; begin end.');
  try
    Sym := Prog.SymbolTable.Lookup('IInterface');
    AssertNotNull('IInterface symbol exists', Sym);
    AssertEquals('IInterface is skType', Ord(skType), Ord(Sym.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_IInterface_IsInterfaceKind;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc('program P; begin end.');
  try
    TD := Prog.SymbolTable.FindType('IInterface');
    AssertNotNull('IInterface type exists', TD);
    AssertEquals('kind is tyInterface', Ord(tyInterface), Ord(TD.Kind));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ ARC on interface references                                          }
{ ------------------------------------------------------------------ }

const
{ ------------------------------------------------------------------ }
{ Supports() intrinsic tests                                         }
{ ------------------------------------------------------------------ }

const
  SrcSupportsTwoArg =
    'program P;'                                              + #10 +
    'type'                                                    + #10 +
    '  IFoo = interface'                                      + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    '  TFoo = class(TObject, IFoo)'                           + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    'procedure TFoo.DoIt(); begin end;'                         + #10 +
    'var Obj: TObject;'                                       + #10 +
    '    B: Boolean;'                                         + #10 +
    'begin'                                                   + #10 +
    '  Obj := TFoo.Create();'                                   + #10 +
    '  B := Supports(Obj, IFoo);'                             + #10 +
    '  Obj.Free()'                                              + #10 +
    'end.';

  SrcSupportsThreeArg =
    'program P;'                                              + #10 +
    'type'                                                    + #10 +
    '  IFoo = interface'                                      + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    '  TFoo = class(TObject, IFoo)'                           + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    'procedure TFoo.DoIt(); begin end;'                         + #10 +
    'var Obj: TObject;'                                       + #10 +
    '    F: IFoo;'                                            + #10 +
    '    B: Boolean;'                                         + #10 +
    'begin'                                                   + #10 +
    '  Obj := TFoo.Create();'                                   + #10 +
    '  B := Supports(Obj, IFoo, F);'                          + #10 +
    '  Obj.Free()'                                              + #10 +
    'end.';

  SrcSupportsNonIntf =
    'program P;'                                              + #10 +
    'type'                                                    + #10 +
    '  TFoo = class(TObject)'                                 + #10 +
    '  end;'                                                  + #10 +
    'var Obj: TObject;'                                       + #10 +
    '    B: Boolean;'                                         + #10 +
    'begin'                                                   + #10 +
    '  Obj := TFoo.Create();'                                   + #10 +
    '  B := Supports(Obj, TFoo);'                             + #10 +
    '  Obj.Free()'                                              + #10 +
    'end.';

procedure TInterfaceTests.TestParse_Supports_TwoArg_ProducesSupportsExpr;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := ParseSrc(SrcSupportsTwoArg);
  try
    { assignment: B := Supports(Obj, IFoo) — index 1 (after Obj := TFoo.Create) }
    Assign := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('rhs is TSupportsExpr', Assign.Expr is TSupportsExpr);
    SE := TSupportsExpr(Assign.Expr);
    AssertEquals('interface name', 'IFoo', SE.IntfTypeName);
    AssertEquals('no out-var', '', SE.OutVarName);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Supports_ThreeArg_ProducesSupportsExpr;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := ParseSrc(SrcSupportsThreeArg);
  try
    Assign := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('rhs is TSupportsExpr', Assign.Expr is TSupportsExpr);
    SE := TSupportsExpr(Assign.Expr);
    AssertEquals('interface name', 'IFoo', SE.IntfTypeName);
    AssertEquals('out-var name', 'F', SE.OutVarName);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Supports_TwoArg_ResultIsBoolean;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := AnalyseSrc(SrcSupportsTwoArg);
  try
    Assign := TAssignment(Prog.Block.Stmts[1]);
    SE := TSupportsExpr(Assign.Expr);
    AssertTrue('ResolvedType set', SE.ResolvedType <> nil);
    AssertEquals('result is Boolean', 'Boolean', SE.ResolvedType.Name);
    AssertTrue('ResolvedIntfType set', SE.ResolvedIntfType <> nil);
    AssertEquals('intf type is IFoo', 'IFoo', SE.ResolvedIntfType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Supports_ThreeArg_ResultIsBoolean;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := AnalyseSrc(SrcSupportsThreeArg);
  try
    Assign := TAssignment(Prog.Block.Stmts[1]);
    SE := TSupportsExpr(Assign.Expr);
    AssertTrue('ResolvedType set', SE.ResolvedType <> nil);
    AssertEquals('result is Boolean', 'Boolean', SE.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Supports_NonInterface_RaisesError;
begin
  AnalyseExpectError(SrcSupportsNonIntf);
end;

{ ------------------------------------------------------------------ }
{ Interface argument passing — non-identifier expressions              }
{ ------------------------------------------------------------------ }

{ Regression (issue #64): inside a method body, an interface-typed field
  must shadow a same-named global variable.  The semantic analyser previously
  found the global 'im: Tmi' and reported a type-mismatch instead of
  recognising 'im' as the field 'im: Iprinter' of the enclosing class. }
procedure TInterfaceTests.TestSemantic_InterfaceField_ShadowsGlobal_OK;
begin
  { Must not raise ESemanticError }
  AnalyseSrc(SrcInterfaceFieldShadowsGlobal).Free();
end;

const
  SrcIntfProperty =
    '''
        program P;
        type
          IInter = interface
            function GetValue(): Integer;
            procedure SetValue(AValue: Integer);
            property Value: Integer read GetValue write SetValue;
          end;
          TFace = class(TObject, IInter)
            FVal: Integer;
            function GetValue(): Integer;
            procedure SetValue(AValue: Integer);
          end;
        function TFace.GetValue(): Integer;
        begin
          Result := FVal;
        end;
        procedure TFace.SetValue(AValue: Integer);
        begin
          FVal := AValue;
        end;
        var
          I: IInter;
        begin
          I := TFace.Create();
          I.Value := 13;
          WriteLn(I.Value);
        end.
        ''';

procedure TInterfaceTests.TestParse_Interface_WithProperty;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcIntfProperty);
  AssertNotNil('interface with property parses', Prog);
  Prog.Free();
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_Registered;
var
  Prog: TProgram;
  Sym:  TSymbol;
  Intf: TInterfaceTypeDesc;
begin
  Prog := AnalyseSrc(SrcIntfProperty);
  try
    Sym := Prog.SymbolTable.Lookup('IInter');
    AssertNotNil('IInter registered', Sym);
    Intf := TInterfaceTypeDesc(Sym.TypeDesc);
    AssertNotNil('property Value found', Intf.FindProperty('Value'));
    AssertEquals('read accessor', 'GetValue', Intf.FindProperty('Value').ReadMethod);
    AssertEquals('write accessor', 'SetValue', Intf.FindProperty('Value').WriteMethod);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_UnknownAccessor_RaisesError;
var
  Prog: TProgram;
  A:    TSemanticAnalyser;
  Got:  Boolean;
begin
  Prog := ParseSrc('''
      program P;
      type
        IInter = interface
          function GetValue(): Integer;
          property Value: Integer read NoSuchMethod;
        end;
      begin
      end.
      ''');
  A := TSemanticAnalyser.Create();
  Got := False;
  try
    try
      A.Analyse(Prog);
    except
      on E: ESemanticError do Got := True;
    end;
  finally
    A.Free();
    Prog.Free();
  end;
  AssertTrue('unknown accessor rejected', Got);
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_WriteToReadOnly_RaisesError;
var
  Prog: TProgram;
  A:    TSemanticAnalyser;
  Got:  Boolean;
begin
  Prog := ParseSrc('''
      program P;
      type
        IInter = interface
          function GetValue(): Integer;
          property Value: Integer read GetValue;
        end;
        TFace = class(TObject, IInter)
          function GetValue(): Integer;
        end;
      function TFace.GetValue(): Integer;
      begin
        Result := 1;
      end;
      var I: IInter;
      begin
        I := TFace.Create();
        I.Value := 5;
      end.
      ''');
  A := TSemanticAnalyser.Create();
  Got := False;
  try
    try
      A.Analyse(Prog);
    except
      on E: ESemanticError do Got := True;
    end;
  finally
    A.Free();
    Prog.Free();
  end;
  AssertTrue('write to read-only interface property rejected', Got);
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_InheritedFromParent_OK;
var
  Prog: TProgram;
  Sym:  TSymbol;
  Intf: TInterfaceTypeDesc;
begin
  Prog := AnalyseSrc('''
      program P;
      type
        IBase = interface
          function GetValue(): Integer;
          property Value: Integer read GetValue;
        end;
        IChild = interface(IBase)
          procedure Extra();
        end;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('IChild');
    Intf := TInterfaceTypeDesc(Sym.TypeDesc);
    AssertNotNil('child sees parent property', Intf.FindProperty('Value'));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Regression — interface idents as values; interface-returning        }
{ interface-method calls                                              }
{ ------------------------------------------------------------------ }

const
{ ------------------------------------------------------------------ }
{ Regression — itab-dispatch argument ABI; discarded sret returns     }
{ ------------------------------------------------------------------ }

const
{ ------------------------------------------------------------------ }
{ Forward interface declarations                                      }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestSemantic_ForwardInterface_CompletedByFullDecl;
var
  Prog: TProgram;
begin
  { `IFoo = interface;` forward stub completed later in the same scope. }
  Prog := AnalyseSrc(
    '''
        program P;
        type
          IFoo = interface;
          IBar = interface
            function GetFoo: IFoo;
          end;
          IFoo = interface
            function GetBar: IBar;
          end;
        begin
        end.
        ''');
  try
    AssertTrue('forward interface completed by full decl analyses OK',
      Prog <> nil);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_ForwardInterface_Unresolved_RaisesError;
begin
  { A forward interface never completed in the scope is an error. }
  AnalyseExpectError(
    '''
        program P;
        type
          IFoo = interface;
        begin
        end.
        ''');
end;

initialization
  RegisterTest(TInterfaceTests);

end.
