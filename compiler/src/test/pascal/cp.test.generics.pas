{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.generics;

{ Tests for generic type monomorphization.
  Phase 3 scope: single type-parameter classes with inline method bodies;
  standalone generic method implementations are not supported yet. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TGenericsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function AnalyseUnit(const ASrc: string): TUnit;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { array-typed fields of a generic class take the type argument: dynamic,
      static and nested }
    procedure TestSem_ArrayOfTypeParamFields_Substituted;
    { ------------------------------------------------------------------ }
    { Parser — generic type declarations                                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_Generic_TypeDecl_IsGenericTypeDef;
    procedure TestParse_Generic_ParamName;
    procedure TestParse_Generic_TwoParams;
    procedure TestParse_Generic_FieldUsesTypeParam;
    procedure TestParse_Generic_MethodReturnUsesTypeParam;
    procedure TestParse_Generic_MethodParamUsesTypeParam;

    { ------------------------------------------------------------------ }
    { Parser — generic type references                                     }
    { ------------------------------------------------------------------ }
    procedure TestParse_Generic_VarDeclTypeName;
    procedure TestParse_Generic_TwoArgVarDecl;
    procedure TestParse_Generic_ConstructorCallParsed;

    { ------------------------------------------------------------------ }
    { Semantic — generic registration and instantiation                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Generic_TemplateRegistered;
    procedure TestSemantic_Generic_TemplateNotExposedAsConcreteType;
    procedure TestSemantic_Generic_VarDecl_InstantiatesType;
    procedure TestSemantic_Generic_InstFieldType_Integer;
    procedure TestSemantic_Generic_InstFieldType_String;
    procedure TestSemantic_Generic_TwoParams_BothFieldsResolved;

    { ------------------------------------------------------------------ }
    { Semantic — generic base names are case-insensitive (GH #212)          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GenericRef_LowercaseSpelling_Resolves;
    procedure TestSemantic_GenericRef_UppercaseSpelling_Resolves;
    procedure TestSemantic_GenericAlias_LowercaseSpelling_Resolves;
    procedure TestSemantic_GenericRef_AnySpelling_SharesOneInstance;

    { ------------------------------------------------------------------ }
    { Semantic — unit-scope generic var declarations                        }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_UnitIntf_GenericVar_Resolves;
    procedure TestSemantic_UnitImpl_GenericVar_Resolves;

    { ------------------------------------------------------------------ }
    { Codegen — monomorphized types                                        }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Codegen — unit-scope generic var                                     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_UnitIntf_GenericVar_GlobalData;

    { ------------------------------------------------------------------ }
    { Codegen — generic class declared in a unit, instantiated by program  }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_UnitGeneric_InstanceSymbolsBareAndWeak;
    procedure TestCodegen_UnitGenericFunc_OneInstancePerBuffer;
    { An alias argument names the same instance as its type: Twice<Int32> is
      Twice<Integer>, B.Wrap<Int64> is B.Wrap<Int>. }
    procedure TestCodegen_GenericRoutine_AliasArgument_OneInstance;
    procedure TestSem_RecordAndFuncInstances_RecordDeclaringUnit;

    { ------------------------------------------------------------------ }
    { Bare (unmangled-unit) class data must be WEAK — an rtl.* / runtime.* }
    { class carries bare typeinfo/vtable/_FieldCleanup symbols that every  }
    { object referencing the class re-defines; with --no-incremental two   }
    { archive members both strong-define them and the link collides        }
    { (GH #174).  Emitting them WEAK lets duplicates collapse.             }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_UnmangledUnitClass_WeakSymbols;

    { ------------------------------------------------------------------ }
    { Multi-instance: same generic class with two different type args     }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Generic_TwoInstancesOfSameClass_Resolve;
    procedure TestSemantic_Generic_TwoInstances_PointerFieldDistinctTypes;

    { ------------------------------------------------------------------ }
    { Type-alias type argument resolves to one canonical instantiation    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GenericInstantiatedWithAlias_Compiles;

    { ------------------------------------------------------------------ }
    { Diamond operator: TFoo<> infers type args from LHS                  }
    { ------------------------------------------------------------------ }
    procedure TestParse_Diamond_SingleArg_Producessentinel;
    procedure TestParse_Diamond_TwoArgs_ProducesSentinel;
    procedure TestSemantic_Diamond_SingleArg_InfersType;
    procedure TestSemantic_Diamond_TwoArgs_InfersType;
    procedure TestCodegen_Diamond_SingleArg_EmitsSameIR;
    procedure TestCodegen_Diamond_TwoArgs_EmitsSameIR;
    { GH #228: a static-array type argument (TBox<array[-1..3] of Integer>)
      mangles to an assembler-safe symbol -- '[', '..', ']' and a negative
      bound's '-' became part of the instance's symbols, which the x86-64
      internal assembler rejected }
    procedure TestCodegen_StaticArrayTypeArg_MangledSymbols;
    { BUG-20261022-generic-type-method-overloads: each overload of a generic
      instance gets its own symbol, carrying the substituted signature, even
      when substitution makes two of them identical }
    procedure TestCodegen_InstanceOverloads_DistinctSymbols;
    { an override of one overload spelt without `overload` matched no slot,
      and was dropped silently }
    procedure TestSem_InstanceOverrideOfOverload_NeedsOverload;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  SrcGenericOneParam =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
          end;
        begin
        end.
        ''';

  SrcGenericTwoParams =
    '''
        program Prg;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
          end;
        begin
        end.
        ''';

  SrcGenericWithMethod =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
            function GetValue: T;
            procedure SetValue(AVal: T);
          end;
        begin
        end.
        ''';

  SrcGenericVarInteger =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
          end;
        var B: TBox<Int32>;
        begin
        end.
        ''';

  SrcGenericVarString =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
          end;
        var S: TBox<string>;
        begin
        end.
        ''';

  SrcGenericTwoParamVar =
    '''
        program Prg;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
          end;
        var P: TPair<string, Int32>;
        begin
        end.
        ''';

  SrcGenericUsage =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
            function GetValue: T;
            begin
              Result := Self.FValue
            end;
            procedure SetValue(AVal: T);
            begin
              Self.FValue := AVal
            end;
          end;
        var B: TBox<Int32>;
        begin
          B := TBox<Int32>.Create();
          B.SetValue(42);
          WriteLn(B.GetValue())
        end.
        ''';

  SrcUnitIntfGenericVar =
    '''
        unit U;
        interface
        type
          TBox<T> = class
            FValue: T;
          end;
        var
          G: TBox<Int32>;
        implementation
        end.
        ''';

  SrcUnitImplGenericVar =
    '''
        unit U;
        interface
        type
          TBox<T> = class
            FValue: T;
          end;
        implementation
        var
          G: TBox<string>;
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TGenericsTests.ParseSrc(const ASrc: string): TProgram;
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

function TGenericsTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TGenericsTests.AnalyseUnit(const ASrc: string): TUnit;
var
  L:  TLexer;
  P:  TParser;
  SA: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
  SA := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnit(Result);
  finally
    SA.Free();
  end;
end;

procedure TGenericsTests.AnalyseExpectError(const ASrc: string);
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
      on E: ESemanticError do { expected };
    end;
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser — generic type declarations                                   }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestParse_Generic_TypeDecl_IsGenericTypeDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcGenericOneParam);
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('name is TBox', 'TBox', TD.Name);
    AssertTrue('def is TGenericTypeDef', TD.Def is TGenericTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Generic_ParamName;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
begin
  Prog := ParseSrc(SrcGenericOneParam);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one param', 1, GD.ParamNames.Count);
    AssertEquals('param name is T', 'T', GD.ParamNames[0]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Generic_TwoParams;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
begin
  Prog := ParseSrc(SrcGenericTwoParams);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('two params', 2, GD.ParamNames.Count);
    AssertEquals('first param K', 'K', GD.ParamNames[0]);
    AssertEquals('second param V', 'V', GD.ParamNames[1]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Generic_FieldUsesTypeParam;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
  FD:   TFieldDecl;
begin
  Prog := ParseSrc(SrcGenericOneParam);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one field', 1, GD.ClassDef.Fields.Count);
    FD := TFieldDecl(GD.ClassDef.Fields[0]);
    AssertEquals('field type is T', 'T', FD.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Generic_MethodReturnUsesTypeParam;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGenericWithMethod);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(GD.ClassDef.Methods[0]);  { GetValue }
    AssertEquals('return type is T', 'T', MD.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Generic_MethodParamUsesTypeParam;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcGenericWithMethod);
  try
    GD  := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD  := TMethodDecl(GD.ClassDef.Methods[1]);  { SetValue }
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param type is T', 'T', Par.TypeName);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser — generic type references                                     }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestParse_Generic_VarDeclTypeName;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcGenericVarInteger);
  try
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('var type is TBox<Int>', 'TBox<Int32>', VD.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Generic_TwoArgVarDecl;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcGenericTwoParamVar);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('var type is TPair<string,Int>',
      'TPair<string,Int32>', VD.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Generic_ConstructorCallParsed;
var
  Prog:   TProgram;
  Assign: TAssignment;
  MC:     TMethodCallExpr;
begin
  Prog := ParseSrc(SrcGenericUsage);
  try
    { Stmt[0] = B := TBox<Integer>.Create() }
    AssertTrue('stmt 0 is assignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TMethodCallExpr', Assign.Expr is TMethodCallExpr);
    MC := TMethodCallExpr(Assign.Expr);
    AssertEquals('object name is TBox<Int32>', 'TBox<Int32>', MC.ObjectName);
    AssertEquals('method is Create', 'Create', MC.Name);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — generic registration and instantiation                    }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestSemantic_Generic_TemplateRegistered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericOneParam);
  try
    AssertNotNull('TBox template registered',
      Prog.SymbolTable.FindGeneric('TBox'));
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_TemplateNotExposedAsConcreteType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericOneParam);
  try
    AssertNull('TBox not a concrete type',
      Prog.SymbolTable.FindType('TBox'));
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_VarDecl_InstantiatesType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericVarInteger);
  try
    AssertNotNull('TBox<Int32> instantiated',
      Prog.SymbolTable.FindType('TBox<Int32>'));
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_InstFieldType_Integer;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FI:   TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericVarInteger);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox<Int32>'));
    FI := RT.FindField('FValue');
    AssertNotNull('FValue field exists', FI);
    AssertEquals('FValue type is tyInteger', Ord(tyInteger), Ord(FI.TypeDesc.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_InstFieldType_String;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FI:   TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericVarString);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox<string>'));
    AssertNotNull('TBox<string> instantiated', RT);
    FI := RT.FindField('FValue');
    AssertNotNull('FValue field exists', FI);
    AssertTrue('FValue type is string', FI.TypeDesc.IsString());
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_TwoParams_BothFieldsResolved;
var
  Prog:  TProgram;
  RT:    TRecordTypeDesc;
  FKey:  TFieldInfo;
  FVal:  TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericTwoParamVar);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TPair<string,Int32>'));
    AssertNotNull('TPair<string,Int32> instantiated', RT);
    FKey := RT.FindField('FKey');
    FVal := RT.FindField('FVal');
    AssertNotNull('FKey field', FKey);
    AssertNotNull('FVal field', FVal);
    AssertTrue('FKey is string', FKey.TypeDesc.IsString());
    AssertEquals('FVal is tyInteger', Ord(tyInteger), Ord(FVal.TypeDesc.Kind));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — generic base names are case-insensitive (GH #212)          }
{ ------------------------------------------------------------------ }

{ Pascal identifiers are case-insensitive, so `TBox<Integer>` and
  `tbox<Integer>` name the same generic.  The generic-template registry was the
  one lookup table in the symbol table created CaseSensitive, so a spelling
  that differed from the declaration by a single letter failed to resolve —
  reported as GH #212 against `Tdictionary<string,string>`.

  Every other name in the language already resolves case-insensitively, the
  non-generic types in the same `type` block included, which is what made the
  failure look arbitrary to the reporter. }
procedure TGenericsTests.TestSemantic_GenericRef_LowercaseSpelling_Resolves;
const
  Src =
    '''
    program Prg;
    type
      TBox<T> = class
        FValue: T;
      end;
    var B: tbox<Int32>;
    begin
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertNotNull('tbox<Int32> resolves to the TBox template',
      Prog.SymbolTable.FindType('TBox<Int32>'));
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_GenericRef_UppercaseSpelling_Resolves;
const
  Src =
    '''
    program Prg;
    type
      TBox<T> = class
        FValue: T;
      end;
    var B: TBOX<Int32>;
    begin
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertNotNull('TBOX<Int32> resolves to the TBox template',
      Prog.SymbolTable.FindType('TBox<Int32>'));
  finally
    Prog.Free();
  end;
end;

{ The reporter's own shape: the differing spelling sits in a TYPE ALIAS rather
  than a var declaration.  That is the form that produced
  "Unknown type 'Tdictionary<string,string>' in type alias". }
procedure TGenericsTests.TestSemantic_GenericAlias_LowercaseSpelling_Resolves;
const
  Src =
    '''
    program Prg;
    type
      TBox<T> = class
        FValue: T;
      end;
      TIntBox = tbox<Int32>;
    var B: TIntBox;
    begin
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertNotNull('alias to tbox<Int32> resolves',
      Prog.SymbolTable.FindType('TIntBox'));
  finally
    Prog.Free();
  end;
end;

{ Case-insensitive resolution must converge on ONE instantiation, not mint a
  second monomorphisation per spelling.  Two instances would mean two distinct
  types that Pascal considers the same type — assignment between them would
  fail, and each would emit its own copy of every method.

  The odd spelling deliberately comes FIRST here.  The original defect was
  ORDER-DEPENDENT: once any declaration had instantiated the generic under the
  template's own spelling, later differently-cased references resolved fine,
  because FindType (unlike the template registry) is case-insensitive and found
  the existing instance.  Only the FIRST reference had to match the template's
  case.  With `A` declared first this test passes even against the broken
  compiler; leading with the lowercase spelling is what gives it teeth. }
procedure TGenericsTests.TestSemantic_GenericRef_AnySpelling_SharesOneInstance;
const
  Src =
    '''
    program Prg;
    type
      TBox<T> = class
        FValue: T;
      end;
    var
      A: tbox<Int32>;
      B: TBOX<Int32>;
      C: TBox<Int32>;
    begin
    end.
    ''';
var
  Prog: TProgram;
  TA, TB, TC: TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    TA := Prog.SymbolTable.FindType('TBox<Int32>');
    AssertNotNull('TBox<Int32> instantiated', TA);
    TB := Prog.SymbolTable.FindType('tbox<Int32>');
    TC := Prog.SymbolTable.FindType('TBOX<Int32>');
    AssertSame('tbox<Int32> is the same instance', TA, TB);
    AssertSame('TBOX<Int32> is the same instance', TA, TC);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — unit-scope generic var declarations                        }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestSemantic_UnitIntf_GenericVar_Resolves;
var
  U: TUnit;
begin
  U := AnalyseUnit(SrcUnitIntfGenericVar);
  try
    AssertEquals('interface var count', 1, U.IntfBlock.Decls.Count);
    AssertTrue('resolved type not nil',
      TVarDecl(U.IntfBlock.Decls.Items[0]).ResolvedType <> nil);
    AssertEquals('resolved type name', 'TBox<Int32>',
      TVarDecl(U.IntfBlock.Decls.Items[0]).ResolvedType.Name);
  finally
    U.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_UnitImpl_GenericVar_Resolves;
var
  U: TUnit;
begin
  U := AnalyseUnit(SrcUnitImplGenericVar);
  try
    AssertEquals('impl var count', 1, U.ImplBlock.Decls.Count);
    AssertTrue('resolved type not nil',
      TVarDecl(U.ImplBlock.Decls.Items[0]).ResolvedType <> nil);
    AssertEquals('resolved type name', 'TBox<string>',
      TVarDecl(U.ImplBlock.Decls.Items[0]).ResolvedType.Name);
  finally
    U.Free();
  end;
end;

procedure TGenericsTests.TestCodegen_UnitIntf_GenericVar_GlobalData;
const
  Prog = '''
    program PU;
    uses U;
    begin
      G := TBox<Int32>.Create();
      G.FValue := 1
    end.
    ''';
var
  X86, A64: string;
begin
  { A unit's interface var of a generic instance type is a unit-mangled
    global; the instance's typeinfo is bare and weak (BUG-004). }
  X86 := GenAsmWithUnit(SrcUnitIntfGenericVar, Prog, TargetX86_64);
  AssertTrue('x86-64: global U_G defined', Pos(#10 + 'U_G:', X86) >= 0);
  AssertTrue('x86-64: weak instance typeinfo',
    Pos('.weak typeinfo_TBox_Int32', X86) >= 0);
  A64 := GenAsmWithUnit(SrcUnitIntfGenericVar, Prog, TargetArm64);
  AssertTrue('arm64: global g_U_G defined', Pos(#10 + '_g_U_G:', A64) >= 0);
  AssertTrue('arm64: weak instance typeinfo',
    Pos('.weak_definition _typeinfo_TBox_Int32', A64) >= 0);
end;

{ ------------------------------------------------------------------ }
{ Generic class declared in a unit, instantiated by program           }
{                                                                     }
{ Regression: AppendUnit used to ignore AUnit.GenericInstances, so a  }
{ generic class declared in a unit and instantiated from the program  }
{ left the constructor call site referencing undefined symbols        }
{ ($_FieldCleanup_<mangled>, $vtable_<mangled>, $typeinfo_<mangled>,  }
{ and the cloned method bodies).                                      }
{ ------------------------------------------------------------------ }

const
  { The constructor call lives inside the unit (not the program), so the
    generic instance is registered against AUnit.GenericInstances — which
    AppendUnit must walk to emit typeinfo, vtable, _FieldCleanup_, and
    the cloned method bodies for.  The constructor body is declared in
    the implementation section (not inline) so the test also exercises
    the ordering requirement that LinkGenericClassMethodImpls must run
    before any FindTypeOrInstantiate triggered by interface-section
    globals — otherwise the cloned instance method is born without a
    body and codegen emits no function. }
  SrcUnitWithGenericClass =
    '''
        unit UPair;
        interface
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
            constructor Create(AKey: K; AVal: V);
          end;
        var
          GPair: TPair<Int32, Int32>;
        procedure InitPair;
        implementation
        constructor TPair<K, V>.Create(AKey: K; AVal: V);
        begin
          Self.FKey := AKey;
          Self.FVal := AVal;
        end;
        procedure InitPair;
        begin
          GPair := TPair<Int32, Int32>.Create(10, 20);
        end;
        end.
        ''';

  SrcProgUsesUnitGeneric =
    '''
        program Prg;
        uses UPair;
        begin
          InitPair();
        end.
        ''';

function AngleBracketSymbol(const AAsm: string): Boolean;
var
  Lines: TStringList;
  I: Int;
begin
  { True when 'TPair<' appears in a line of code or a symbol directive.  The
    class-name string the typeinfo carries keeps its source spelling, so a
    string-data line is not a symbol. }
  Result := False;
  Lines := TStringList.Create();
  try
    Lines.Text := AAsm;
    for I := 0 to Lines.Count - 1 do
      if (Pos('TPair<', Lines.Strings[I]) >= 0) and
         (Pos('.ascii', Lines.Strings[I]) < 0) and
         (Pos('.string', Lines.Strings[I]) < 0) then
      begin
        Result := True;
        Exit;
      end;
  finally
    Lines.Free();
  end;
end;

procedure TGenericsTests.TestCodegen_UnitGeneric_InstanceSymbolsBareAndWeak;
const
  Syms: array[0..3] of string = ('TPair_Int32_Int32_Create',
    '_FieldCleanup_TPair_Int32_Int32', 'typeinfo_TPair_Int32_Int32',
    'vtable_TPair_Int32_Int32');
var
  X86, A64: string;
  I: Int;
begin
  { A generic class declared in a unit and instantiated by the program: the
    instance's method bodies, field-cleanup function, typeinfo and vtable
    are emitted under BARE mangled names (never unit-prefixed, never with
    the raw '<' form) and WEAK, because any compilation process may
    materialise the same instance and every copy must agree on one symbol
    and collapse at link (BUG-004).  A wrong name or a strong definition
    shows only when two separately compiled objects meet in one link. }
  X86 := GenAsmWithUnit(SrcUnitWithGenericClass, SrcProgUsesUnitGeneric,
    TargetX86_64);
  A64 := GenAsmWithUnit(SrcUnitWithGenericClass, SrcProgUsesUnitGeneric,
    TargetArm64);
  for I := 0 to 3 do
  begin
    AssertTrue('x86-64: ' + Syms[I] + ' defined',
      Pos(#10 + Syms[I] + ':', X86) >= 0);
    AssertTrue('x86-64: ' + Syms[I] + ' weak',
      Pos('.weak ' + Syms[I], X86) >= 0);
    AssertTrue('arm64: ' + Syms[I] + ' defined',
      Pos(#10 + '_' + Syms[I] + ':', A64) >= 0);
    AssertTrue('arm64: ' + Syms[I] + ' weak',
      Pos('.weak_definition _' + Syms[I], A64) >= 0);
  end;
  AssertTrue('x86-64: no unit-prefixed instance constructor',
    Pos('UPair_TPair_Int32_Int32_Create', X86) < 0);
  AssertTrue('arm64: no unit-prefixed instance constructor',
    Pos('UPair_TPair_Int32_Int32_Create', A64) < 0);
  AssertTrue('x86-64: no raw angle-bracket symbol', not AngleBracketSymbol(X86));
  AssertTrue('arm64: no raw angle-bracket symbol', not AngleBracketSymbol(A64));
end;

function CountAsmOccurrences(const AHay, ANeedle: string): Int;
var
  P: Int;
  Rest: string;
begin
  Result := 0;
  Rest := AHay;
  P := Pos(ANeedle, Rest);
  while P >= 0 do
  begin
    Inc(Result);
    Rest := Copy(Rest, P + Length(ANeedle), Length(Rest));
    P := Pos(ANeedle, Rest);
  end;
end;

procedure TGenericsTests.TestCodegen_GenericRoutine_AliasArgument_OneInstance;
const
  Src = '''
    program P;
    type
      TBox = class
        function Wrap<U>(x: U): U;
      end;
    function TBox.Wrap<U>(x: U): U; begin Result := x end;
    function Twice<T>(A: T): T; begin Result := A + A end;
    var B: TBox;
    begin
      B := TBox.Create();
      WriteLn(Twice<Int32>(1), Twice<Int32>(2), Twice<Int>(3), Twice<Int64>(4));
      WriteLn(B.Wrap<Int>(5), B.Wrap<Int64>(6))
    end.
    ''';
var
  Code: string;
  T:   Int;
begin
  for T := 0 to 1 do
  begin
    if T = 0 then Code := GenAsm(Src, TargetX86_64)
    else Code := GenAsm(Src, TargetArm64);
    AssertEquals('one 32-bit Twice instance', 1,
      CountAsmOccurrences(Code, 'Twice_Int32:'));
    AssertEquals('one 64-bit Twice instance', 1,
      CountAsmOccurrences(Code, 'Twice_Int64:') + CountAsmOccurrences(Code, 'Twice_Int:'));
    AssertEquals('one Wrap instance', 1,
      CountAsmOccurrences(Code, 'TBox_Wrap_Int64:') + CountAsmOccurrences(Code, 'TBox_Wrap_Int:'));
  end;
end;

procedure TGenericsTests.TestCodegen_UnitGenericFunc_OneInstancePerBuffer;
const
  UnitSrc = '''
    unit gfb;
    interface
    function Twice<T>(A: T): T;
    function UseOwn: Int32;
    implementation
    function Twice<T>(A: T): T; begin Result := A + A end;
    function UseOwn: Int32; begin Result := Twice<Int32>(4) end;
    end.
    ''';
  ProgSrc = '''
    program pgf;
    uses gfb;
    begin
      WriteLn(Twice<Int32>(21), UseOwn())
    end.
    ''';
var
  X86, A64: string;
begin
  { BUG-034: a unit compiled from source never registered its generic
    function templates, so neither the unit nor the program could
    instantiate them.  Both now do, each owning its own (weak) instance;
    a whole-program build appends both modules to one buffer, which must
    define the instance label once. }
  X86 := GenAsmWithUnit(UnitSrc, ProgSrc, TargetX86_64);
  A64 := GenAsmWithUnit(UnitSrc, ProgSrc, TargetArm64);
  AssertEquals('x86-64: Twice<Int32> defined once', 1,
    CountAsmOccurrences(X86, #10 + 'Twice_Int32:'));
  AssertEquals('arm64: Twice<Int32> defined once', 1,
    CountAsmOccurrences(A64, #10 + '_Twice_Int32:'));
end;

procedure TGenericsTests.TestSem_RecordAndFuncInstances_RecordDeclaringUnit;
const
  UnitSrc = '''
    unit gdecl;
    interface
    type
      TMaker<T> = record
        X: T;
        function Get(): T;
      end;
    function Twice<T>(A: T): T;
    implementation
    function TMaker<T>.Get(): T; begin Result := X end;
    function Twice<T>(A: T): T; begin Result := A + A end;
    end.
    ''';
  ProgSrc = '''
    program pdecl;
    uses gdecl;
    var M: TMaker<Int>;
    begin
      WriteLn(M.Get(), Twice<Int>(2))
    end.
    ''';
var
  L: TLexer;
  P: TParser;
  U: TUnit;
  Prog: TProgram;
  A: TSemanticAnalyser;
begin
  { BUG-014: a generic record or function instance's body is the declaring
    unit's source, so --debug leak reports must name that unit; the instance
    records it as generic class instances already did. }
  L := TLexer.Create(UnitSrc);
  P := TParser.Create(L);
  try
    U := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
  Prog := ParseSrc(ProgSrc);
  A := TSemanticAnalyser.Create();
  try
    A.AnalyseUnitForExport(U);
    A.Analyse(Prog);
    AssertEquals('record instances', 1, Prog.GenericRecordInstances.Count);
    AssertEquals('record instance declaring unit', 'gdecl',
      TGenericRecordInstance(Prog.GenericRecordInstances.Items[0]).DefUnitName);
    AssertEquals('function instances', 1, Prog.GenericFuncInstances.Count);
    AssertEquals('function instance declaring unit', 'gdecl',
      TGenericFuncInstance(Prog.GenericFuncInstances.Items[0]).DefUnitName);
  finally
    A.Free();
    Prog.Free();
    U.Free();
  end;
end;

procedure TGenericsTests.TestCodegen_UnmangledUnitClass_WeakSymbols;
{ A class declared in an rtl.* unit gets BARE typeinfo/vtable/_FieldCleanup
  symbols (IsUnmangledUnit strips the unit prefix so the whole RTL agrees on
  one name).  Because the symbol is bare, EVERY object that references the
  class re-defines it — so under --no-incremental (which inlines a source dep
  via AppendUnit) two archive members both strong-define e.g.
  typeinfo_TRtlPlatform and the link fails with a multiple-definition error
  (GH #174).  The definitions must be WEAK so duplicates collapse; a single
  strong owner (the incremental per-unit .o) still wins.  Non-RTL classes are
  immune — their symbols are unit-prefixed and referenced externally. }
const
  BareUnitSrc =
    '''
    unit rtl.testplat;
    interface
    type
      ITestPlat = interface
        function Kind: string;
      end;
      TTestPlat = class(ITestPlat)
        Name: string;
      published
        function Kind: string; virtual;
      end;
    implementation
    function TTestPlat.Kind: string;
    begin Result := 'plat' end;
    end.
    ''';
  ProgUsesBare =
    '''
    program UseBare;
    uses rtl.testplat;
    var P: TTestPlat;
    begin
      P := TTestPlat.Create();
      P.Free()
    end.
    ''';
var
  X86, A64: string;
  I: Int;
  Syms: array[0..6] of string;
begin
  Syms[0] := 'typeinfo_TTestPlat';
  Syms[1] := 'vtable_TTestPlat';
  Syms[2] := '_FieldCleanup_TTestPlat';
  Syms[3] := 'itab_TTestPlat_ITestPlat';
  Syms[4] := 'impllist_TTestPlat';
  Syms[5] := 'typeinfo_ITestPlat';
  Syms[6] := 'TTestPlat_Kind';
  X86 := GenAsmWithUnit(BareUnitSrc, ProgUsesBare, TargetX86_64);
  A64 := GenAsmWithUnit(BareUnitSrc, ProgUsesBare, TargetArm64);
  { The class data is bare (no rtl_testplat_ prefix) and every per-class
    symbol a referencing object re-defines is WEAK on both ISAs. }
  for I := 0 to 6 do
  begin
    AssertTrue('x86-64: ' + Syms[I] + ' weak',
      Pos('.weak ' + Syms[I], X86) >= 0);
    AssertTrue('arm64: ' + Syms[I] + ' weak',
      Pos('.weak_definition _' + Syms[I], A64) >= 0);
  end;
  { The published-methods table: weak on x86-64; arm64 keeps it local to the
    object (no .globl), which collapses duplicates just as well. }
  AssertTrue('x86-64: methods table weak',
    Pos('.weak methods_TTestPlat', X86) >= 0);
  AssertTrue('arm64: methods table defined',
    Pos(#10 + 'methods_TTestPlat:', A64) >= 0);
  AssertTrue('arm64: methods table not exported',
    Pos('.globl methods_TTestPlat', A64) < 0);
end;

{ ------------------------------------------------------------------ }
{ Multi-instance: same generic class with two different type args     }
{ ------------------------------------------------------------------ }

const
  { Two var decls of the same generic class with different type args.
    Used to fail with 'Type mismatch: expected ''^T'' but got ''^TObject'''
    because '^T' was cached globally under the unsubstituted name after
    the first instantiation, and the unsubstituted constructor-call
    receiver name '<T>' got mutated to '<String>' on the first analysis
    and then incorrectly re-used on the second. }
  SrcTwoInstancesSameGeneric =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
            procedure SetIt(V: T);
            begin
              Self.FValue := V
            end;
          end;
        var
          A: TBox<Int32>;
          B: TBox<String>;
        begin end.
        ''';

  SrcTwoInstancesPointerField =
    '''
        program Prg;
        type
          TCell<T> = class
            FData: ^T;
            procedure SetData(P: ^T);
            begin
              Self.FData := P
            end;
          end;
        var
          CI: TCell<Int32>;
          CS: TCell<String>;
        begin end.
        ''';

procedure TGenericsTests.TestSemantic_Generic_TwoInstancesOfSameClass_Resolve;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTwoInstancesSameGeneric);
  try
    AssertNotNull('TBox<Int32> instantiated',
      Prog.SymbolTable.FindType('TBox<Int32>'));
    AssertNotNull('TBox<string> instantiated',
      Prog.SymbolTable.FindType('TBox<string>'));
  finally
    Prog.Free();
  end;
end;

const
procedure TGenericsTests.TestSemantic_Generic_TwoInstances_PointerFieldDistinctTypes;
var
  Prog: TProgram;
  CI, CS: TRecordTypeDesc;
  FI, FS: TFieldInfo;
begin
  Prog := AnalyseSrc(SrcTwoInstancesPointerField);
  try
    CI := TRecordTypeDesc(Prog.SymbolTable.FindType('TCell<Int32>'));
    CS := TRecordTypeDesc(Prog.SymbolTable.FindType('TCell<string>'));
    AssertNotNull('TCell<Int32> instantiated', CI);
    AssertNotNull('TCell<string>  instantiated', CS);
    FI := CI.FindField('FData');
    FS := CS.FindField('FData');
    AssertNotNull('FData on TCell<Int32>', FI);
    AssertNotNull('FData on TCell<string>',  FS);
    { The two FData fields must resolve to distinct pointer types — '^T'
      must NOT be shared across instances. }
    AssertEquals('FData<Int> base type',
      '^Int32', FI.TypeDesc.Name);
    AssertEquals('FData<string>  base type',
      '^string',  FS.TypeDesc.Name);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Type-alias type argument                                          }
{ ------------------------------------------------------------------ }

const
  { Regression: a generic instantiated with a transparent type alias
    (TIntAlias = Integer) must share ONE identity with the underlying-type
    form, otherwise a generic method whose body both declares a nested
    generic return type (TInner<T>) and constructs it (TInner<T>.Create())
    sees two divergent instantiations.  Previously one path kept the alias
    spelling (TInner<TIntAlias>) while the other resolved it (TInner<Integer>),
    so the internal assignment 'Result := TInner<T>.Create()' failed with
    "Type mismatch ... expected 'TInner<TIntAlias>' but got 'TInner<Int32>'".
    The two instantiation paths must now agree. }
  SrcGenericInstantiatedWithAlias =
    '''
        program Prg;
        type
          TIntAlias = Int32;
          TInner<T> = class
            FV: T;
          end;
          TOuter<T> = class
            function Make: TInner<T>;
            begin
              Result := TInner<T>.Create()
            end;
          end;
        var
          O: TOuter<TIntAlias>;
          N: TInner<TIntAlias>;
        begin
          O := TOuter<TIntAlias>.Create();
          N := O.Make()
        end.
        ''';

procedure TGenericsTests.TestSemantic_GenericInstantiatedWithAlias_Compiles;
var
  Prog:  TProgram;
  Inner: TRecordTypeDesc;
begin
  { Analysing without a semantic error is the regression check — the buggy
    compiler raised a type-mismatch in TOuter<T>.Make's body. }
  Prog := AnalyseSrc(SrcGenericInstantiatedWithAlias);
  try
    { The alias and underlying-type forms must collapse onto one canonical
      instantiation keyed by the underlying type name (Integer). }
    Inner := TRecordTypeDesc(Prog.SymbolTable.FindType('TInner<Int32>'));
    AssertNotNull('TInner<Int32> is the canonical instantiation', Inner);
    AssertNull('no separate TInner<TIntAlias> instantiation exists',
      Prog.SymbolTable.FindType('TInner<TIntAlias>'));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Diamond operator tests                                             }
{ ------------------------------------------------------------------ }

const
  SrcDiamondSingleArg =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
            function GetValue: T;
            begin
              Result := Self.FValue
            end;
            procedure SetValue(AVal: T);
            begin
              Self.FValue := AVal
            end;
          end;
        var B: TBox<Int32>;
        begin
          B := TBox<>.Create();
          B.SetValue(42);
          WriteLn(B.GetValue())
        end.
        ''';

  SrcDiamondTwoArgs =
    '''
        program Prg;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
          end;
        var P: TPair<string, Int32>;
        begin
          P := TPair<>.Create()
        end.
        ''';

procedure TGenericsTests.TestParse_Diamond_SingleArg_Producessentinel;
var
  Prog:   TProgram;
  Assign: TAssignment;
  MC:     TMethodCallExpr;
begin
  Prog := ParseSrc(SrcDiamondSingleArg);
  try
    AssertTrue('stmt 0 is assignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TMethodCallExpr', Assign.Expr is TMethodCallExpr);
    MC := TMethodCallExpr(Assign.Expr);
    AssertEquals('diamond produces TBox<> sentinel', 'TBox<>', MC.ObjectName);
    AssertEquals('method is Create', 'Create', MC.Name);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestParse_Diamond_TwoArgs_ProducesSentinel;
var
  Prog:   TProgram;
  Assign: TAssignment;
  MC:     TMethodCallExpr;
begin
  Prog := ParseSrc(SrcDiamondTwoArgs);
  try
    AssertTrue('stmt 0 is assignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TMethodCallExpr', Assign.Expr is TMethodCallExpr);
    MC := TMethodCallExpr(Assign.Expr);
    AssertEquals('diamond produces TPair<> sentinel', 'TPair<>', MC.ObjectName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_Diamond_SingleArg_InfersType;
var
  Prog:   TProgram;
  Assign: TAssignment;
  MC:     TMethodCallExpr;
begin
  Prog := AnalyseSrc(SrcDiamondSingleArg);
  try
    AssertTrue('stmt 0 is assignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    MC := TMethodCallExpr(Assign.Expr);
    AssertEquals('diamond resolved to TBox<Int32>', 'TBox<Int32>', MC.ObjectName);
    AssertTrue('marked constructor', MC.IsConstructorCall);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestSemantic_Diamond_TwoArgs_InfersType;
var
  Prog:   TProgram;
  Assign: TAssignment;
  MC:     TMethodCallExpr;
begin
  Prog := AnalyseSrc(SrcDiamondTwoArgs);
  try
    AssertTrue('stmt 0 is assignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    MC := TMethodCallExpr(Assign.Expr);
    AssertEquals('diamond resolved to TPair<string,Int32> (no space after comma)',
      'TPair<string,Int32>', MC.ObjectName);
    AssertTrue('marked constructor', MC.IsConstructorCall);
  finally
    Prog.Free();
  end;
end;

{ Diamond inference (TBox<>.Create) must monomorphise exactly as the
  explicit spelling: identical assembly on both ISAs. }
procedure TGenericsTests.TestCodegen_Diamond_SingleArg_EmitsSameIR;
begin
  AssertEquals('x86-64: diamond asm identical to explicit',
    GenAsm(SrcGenericUsage, TargetX86_64),
    GenAsm(SrcDiamondSingleArg, TargetX86_64));
  AssertEquals('arm64: diamond asm identical to explicit',
    GenAsm(SrcGenericUsage, TargetArm64),
    GenAsm(SrcDiamondSingleArg, TargetArm64));
end;

procedure TGenericsTests.TestCodegen_Diamond_TwoArgs_EmitsSameIR;
var
  SrcExplicit: string;
begin
  SrcExplicit :=
    '''
        program Prg;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
          end;
        var P: TPair<string, Int32>;
        begin
          P := TPair<string, Int32>.Create()
        end.
        ''';
  AssertEquals('x86-64: diamond asm identical to explicit',
    GenAsm(SrcExplicit, TargetX86_64), GenAsm(SrcDiamondTwoArgs, TargetX86_64));
  AssertEquals('arm64: diamond asm identical to explicit',
    GenAsm(SrcExplicit, TargetArm64), GenAsm(SrcDiamondTwoArgs, TargetArm64));
end;

procedure TGenericsTests.TestSem_ArrayOfTypeParamFields_Substituted;
const
  Src = '''
      program P;
      type
        TBox<T> = class
          FItems: array of T;
          FFix: array[0..1] of T;
          FNest: array of array of T;
        end;
      var B: TBox<string>;
      begin
      end.
      ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := Self.AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox<string>'));
    AssertNotNull('instance', RT);
    AssertEquals('dynamic', 'array of string',
      RT.FindField('FItems').TypeDesc.Name);
    AssertEquals('static', 'array[0..1] of string',
      RT.FindField('FFix').TypeDesc.Name);
    AssertEquals('nested', 'array of array of string',
      RT.FindField('FNest').TypeDesc.Name);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestCodegen_StaticArrayTypeArg_MangledSymbols;
const
  Src = '''
    program P;
    type
      TArr = array[-1..3] of Int32;
      TBox<T> = class
        V: T;
        procedure Put(const A: T);
      end;
    procedure TBox<T>.Put(const A: T); begin V := A end;
    var B: TBox<TArr>; A: TArr;
    begin
      B := TBox<TArr>.Create();
      B.Put(A)
    end.
    ''';
var
  AsmX, AsmA: string;
begin
  AsmX := GenAsm(Src, TargetX86_64);
  AsmA := GenAsm(Src, TargetArm64);
  AssertEquals('the instance symbols use the mangled argument', '',
    AsmMissing(Src, 'TBox_array_m1_3_of_Int32_Put:',
      'TBox_array_m1_3_of_Int32_Put:'));
  AssertTrue('no bracket in an x86-64 symbol',
    Pos('TBox_array[', AsmX) < 0);
  AssertTrue('no bracket in an arm64 symbol',
    Pos('TBox_array[', AsmA) < 0);
end;

procedure TGenericsTests.TestCodegen_InstanceOverloads_DistinctSymbols;
const
  Src = '''
    program P;
    type
      TBox<T> = class
        procedure Put(A: T); overload;
        procedure Put(A: T; B: Int32); overload;
        procedure Put(A: Int32); overload;
      end;
    procedure TBox<T>.Put(A: T); begin end;
    procedure TBox<T>.Put(A: T; B: Int32); begin end;
    procedure TBox<T>.Put(A: Int32); begin end;
    var B: TBox<Int32>;
    begin
      B := TBox<Int32>.Create();
      B.Put(1, 2)
    end.
    ''';
begin
  AssertEquals('two-argument overload', '',
    AsmMissing(Src, 'TBox_Int32_Put_D_ii:', 'TBox_Int32_Put_D_ii:'));
  AssertEquals('one-argument overload', '',
    AsmMissing(Src, 'TBox_Int32_Put_D_i:', 'TBox_Int32_Put_D_i:'));
  AssertEquals('the overload identical after substitution', '',
    AsmMissing(Src, 'TBox_Int32_Put_D_i_D_2:', 'TBox_Int32_Put_D_i_D_2:'));
end;

procedure TGenericsTests.TestSem_InstanceOverrideOfOverload_NeedsOverload;
const
  Base = '''
    program P;
    type
      TBase<T> = class
        function D(): string; overload; virtual;
        function D(const S: string): string; overload; virtual;
      end;
      TKid<T> = class(TBase<T>)
        function D(const S: string): string; %s
      end;
    function TBase<T>.D(): string; begin Result := '' end;
    function TBase<T>.D(const S: string): string; begin Result := S end;
    function TKid<T>.D(const S: string): string; begin Result := S end;
    var K: TKid<Int>;
    begin
    end.
    ''';
var
  Err: string;
begin
  Err := SemanticError(Format(Base, ['override;']));
  AssertTrue('rejected: ' + Err,
    Pos('marked override but no matching virtual base method', Err) >= 0);
  AssertEquals('accepted with overload', '',
    SemanticError(Format(Base, ['overload; override;'])));
end;

initialization
  RegisterTest(TGenericsTests);

end.
