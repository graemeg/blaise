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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TGenericsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function AnalyseUnit(const ASrc: string): TUnit;
    function GenUnitIR(const ASrc: string): string;
    function GenCombinedIR(const AUnitSrc, AProgSrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
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
    procedure TestCodegen_Generic_TypeInfoEmitted;
    procedure TestCodegen_Generic_ConstructorAllocsMemory;
    procedure TestCodegen_Generic_MethodEmitted;
    procedure TestCodegen_Generic_FieldAccessWorks;

    { ------------------------------------------------------------------ }
    { Codegen — unit-scope generic var                                     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_UnitIntf_GenericVar_GlobalData;

    { ------------------------------------------------------------------ }
    { Codegen — generic class declared in a unit, instantiated by program  }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_UnitGeneric_FieldCleanupFnEmitted;
    procedure TestCodegen_UnitGeneric_VTableEmitted;
    procedure TestCodegen_UnitGeneric_TypeInfoEmitted;
    procedure TestCodegen_UnitGeneric_MethodBodyEmitted;
    procedure TestCodegen_UnitGeneric_WeakSymMarkersEmitted;

    { ------------------------------------------------------------------ }
    { Bare (unmangled-unit) class data must be WEAK — an rtl.* / runtime.* }
    { class carries bare typeinfo/vtable/_FieldCleanup symbols that every  }
    { object referencing the class re-defines; with --no-incremental two   }
    { archive members both strong-define them and the link collides        }
    { (GH #174).  Emitting them WEAK lets duplicates collapse.             }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_UnmangledUnitClass_WeakSymMarkersEmitted;

    { ------------------------------------------------------------------ }
    { Multi-instance: same generic class with two different type args     }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Generic_TwoInstancesOfSameClass_Resolve;
    procedure TestSemantic_Generic_TwoInstances_PointerFieldDistinctTypes;
    procedure TestCodegen_Generic_TwoInstances_MethodCallsResolveToOwnInstance;

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
        var B: TBox<Integer>;
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
        var P: TPair<string, Integer>;
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
        var B: TBox<Integer>;
        begin
          B := TBox<Integer>.Create();
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
          G: TBox<Integer>;
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

function TGenericsTests.GenIR(const ASrc: string): string;
var
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Prog := AnalyseSrc(ASrc);
  CG   := TCodeGenQBE.Create();
  try
    CG.Generate(Prog);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Prog.Free();
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

function TGenericsTests.GenUnitIR(const ASrc: string): string;
var
  U:  TUnit;
  CG: TCodeGenQBE;
begin
  U := AnalyseUnit(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.GenerateUnit(U);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    U.Free();
  end;
end;

function TGenericsTests.GenCombinedIR(const AUnitSrc, AProgSrc: string): string;
{ Mirrors the real driver path in Blaise.pas: analyse the unit for export,
  analyse the program against the now-populated global scope, then run the
  combined codegen via AppendUnit + AppendProgram.  Use this when the bug
  lives in the AppendUnit path (which GenUnitIR's GenerateUnit does not
  exercise). }
var
  UL:   TLexer;
  UP:   TParser;
  PL:   TLexer;
  PP:   TParser;
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
  CG:   TCodeGenQBE;
begin
  UL := TLexer.Create(AUnitSrc);
  UP := TParser.Create(UL);
  try
    U := UP.ParseUnit();
  finally
    UP.Free();
    UL.Free();
  end;

  PL := TLexer.Create(AProgSrc);
  PP := TParser.Create(PL);
  try
    Prog := PP.Parse();
  finally
    PP.Free();
    PL.Free();
  end;

  SA := TSemanticAnalyser.Create();
  CG := TCodeGenQBE.Create();
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    CG.SetSymbolTable(Prog.SymbolTable);
    CG.AppendUnit(U);
    CG.AppendProgram(Prog);
    Result := CG.GetOutput();
  finally
    CG.Free();
    SA.Free();
    Prog.Free();
    U.Free();
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
    AssertEquals('var type is TBox<Integer>', 'TBox<Integer>', VD.TypeName);
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
    AssertEquals('var type is TPair<string,Integer>',
      'TPair<string,Integer>', VD.TypeName);
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
    AssertEquals('object name is TBox<Integer>', 'TBox<Integer>', MC.ObjectName);
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
    AssertNotNull('TBox<Integer> instantiated',
      Prog.SymbolTable.FindType('TBox<Integer>'));
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
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox<Integer>'));
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
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TPair<string,Integer>'));
    AssertNotNull('TPair<string,Integer> instantiated', RT);
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
{ Codegen — monomorphized types                                        }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestCodegen_Generic_TypeInfoEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  AssertTrue('typeinfo for TBox_Integer emitted',
    Pos('$typeinfo_TBox_Integer', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_Generic_ConstructorAllocsMemory;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  AssertTrue('constructor calls _ClassAlloc',
    Pos('call $_ClassAlloc', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_Generic_MethodEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  AssertTrue('GetValue method emitted',
    Pos('TBox_Integer_GetValue', IR) > 0);
  AssertTrue('SetValue method emitted',
    Pos('TBox_Integer_SetValue', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_Generic_FieldAccessWorks;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  { SetValue stores into FValue; verify a store instruction is emitted }
  AssertTrue('method bodies emitted with stores', Pos('storew', IR) > 0);
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
    var B: tbox<Integer>;
    begin
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertNotNull('tbox<Integer> resolves to the TBox template',
      Prog.SymbolTable.FindType('TBox<Integer>'));
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
    var B: TBOX<Integer>;
    begin
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertNotNull('TBOX<Integer> resolves to the TBox template',
      Prog.SymbolTable.FindType('TBox<Integer>'));
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
      TIntBox = tbox<Integer>;
    var B: TIntBox;
    begin
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertNotNull('alias to tbox<Integer> resolves',
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
      A: tbox<Integer>;
      B: TBOX<Integer>;
      C: TBox<Integer>;
    begin
    end.
    ''';
var
  Prog: TProgram;
  TA, TB, TC: TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    TA := Prog.SymbolTable.FindType('TBox<Integer>');
    AssertNotNull('TBox<Integer> instantiated', TA);
    TB := Prog.SymbolTable.FindType('tbox<Integer>');
    TC := Prog.SymbolTable.FindType('TBOX<Integer>');
    AssertSame('tbox<Integer> is the same instance', TA, TB);
    AssertSame('TBOX<Integer> is the same instance', TA, TC);
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
    AssertEquals('resolved type name', 'TBox<Integer>',
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
var
  IR: string;
begin
  IR := GenUnitIR(SrcUnitIntfGenericVar);
  AssertTrue('global data slot for G emitted (unit-prefix mangled)',
    Pos('data $U_G', IR) > 0);
  AssertTrue('typeinfo for TBox_Integer emitted',
    Pos('$typeinfo_TBox_Integer', IR) > 0);
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
          GPair: TPair<Integer, Integer>;
        procedure InitPair;
        implementation
        constructor TPair<K, V>.Create(AKey: K; AVal: V);
        begin
          Self.FKey := AKey;
          Self.FVal := AVal;
        end;
        procedure InitPair;
        begin
          GPair := TPair<Integer, Integer>.Create(10, 20);
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

procedure TGenericsTests.TestCodegen_UnitGeneric_FieldCleanupFnEmitted;
var
  IR: string;
begin
  IR := GenCombinedIR(SrcUnitWithGenericClass, SrcProgUsesUnitGeneric);
  AssertTrue('_FieldCleanup_ function body emitted with mangled name',
    Pos('function $_FieldCleanup_TPair_Integer_Integer', IR) > 0);
  AssertTrue('no raw angle-bracket form of _FieldCleanup_',
    Pos('$_FieldCleanup_TPair<', IR) <= 0);
end;

procedure TGenericsTests.TestCodegen_UnitGeneric_VTableEmitted;
var
  IR: string;
begin
  IR := GenCombinedIR(SrcUnitWithGenericClass, SrcProgUsesUnitGeneric);
  AssertTrue('vtable data emitted for TPair_Integer_Integer',
    Pos('data $vtable_TPair_Integer_Integer', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_UnitGeneric_TypeInfoEmitted;
var
  IR: string;
begin
  IR := GenCombinedIR(SrcUnitWithGenericClass, SrcProgUsesUnitGeneric);
  AssertTrue('typeinfo data emitted for TPair_Integer_Integer',
    Pos('data $typeinfo_TPair_Integer_Integer', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_UnitGeneric_MethodBodyEmitted;
var
  IR: string;
begin
  IR := GenCombinedIR(SrcUnitWithGenericClass, SrcProgUsesUnitGeneric);
  { Generic-instance symbols are BARE — never unit-prefixed (BUG-004): the
    same instance may be materialised by any compilation process, so every
    process must agree on one symbol (deduped via weak linkage). }
  AssertTrue('constructor body emitted with bare instance name',
    Pos('function $TPair_Integer_Integer_Create', IR) > 0);
  AssertTrue('no unit-prefixed instance constructor',
    Pos('$UPair_TPair_Integer_Integer_Create', IR) < 0);
end;

procedure TGenericsTests.TestCodegen_UnitGeneric_WeakSymMarkersEmitted;
var
  IR: string;
begin
  { The QBE driver turns '# WEAKSYM <sym>' markers into '.weak <sym>'
    directives on the qbe-produced .s, giving generic-instance symbols WEAK
    binding so several objects in one link may carry the identical copy
    (BUG-004).  Assert the markers cover the method bodies, typeinfo, vtable
    and the field-cleanup fn. }
  IR := GenCombinedIR(SrcUnitWithGenericClass, SrcProgUsesUnitGeneric);
  AssertTrue('WEAKSYM marker for instance constructor',
    Pos('# WEAKSYM TPair_Integer_Integer_Create', IR) > 0);
  AssertTrue('WEAKSYM marker for instance typeinfo',
    Pos('# WEAKSYM typeinfo_TPair_Integer_Integer', IR) > 0);
  AssertTrue('WEAKSYM marker for instance vtable',
    Pos('# WEAKSYM vtable_TPair_Integer_Integer', IR) > 0);
  AssertTrue('WEAKSYM marker for instance field cleanup',
    Pos('# WEAKSYM _FieldCleanup_TPair_Integer_Integer', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_UnmangledUnitClass_WeakSymMarkersEmitted;
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
  IR: string;
begin
  IR := GenCombinedIR(BareUnitSrc, ProgUsesBare);
  { The class data is emitted bare (no rtl_testplat_ prefix) — confirm the
    bare form is what we key the weak markers on. }
  AssertTrue('bare typeinfo emitted for TTestPlat',
    Pos('data $typeinfo_TTestPlat', IR) > 0);
  { Every bare per-class data symbol a referencing object re-defines must be
    marked WEAK: typeinfo, vtable, field-cleanup, the published-methods table,
    and the interface itab / impllist. }
  AssertTrue('WEAKSYM marker for bare-unit class typeinfo',
    Pos('# WEAKSYM typeinfo_TTestPlat', IR) > 0);
  AssertTrue('WEAKSYM marker for bare-unit class vtable',
    Pos('# WEAKSYM vtable_TTestPlat', IR) > 0);
  AssertTrue('WEAKSYM marker for bare-unit class field cleanup',
    Pos('# WEAKSYM _FieldCleanup_TTestPlat', IR) > 0);
  AssertTrue('WEAKSYM marker for bare-unit class methods table',
    Pos('# WEAKSYM methods_TTestPlat', IR) > 0);
  AssertTrue('WEAKSYM marker for bare-unit class itab',
    Pos('# WEAKSYM itab_TTestPlat_ITestPlat', IR) > 0);
  AssertTrue('WEAKSYM marker for bare-unit class impllist',
    Pos('# WEAKSYM impllist_TTestPlat', IR) > 0);
  AssertTrue('WEAKSYM marker for bare-unit interface typeinfo',
    Pos('# WEAKSYM typeinfo_ITestPlat', IR) > 0);
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
          A: TBox<Integer>;
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
          CI: TCell<Integer>;
          CS: TCell<String>;
        begin end.
        ''';

procedure TGenericsTests.TestSemantic_Generic_TwoInstancesOfSameClass_Resolve;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTwoInstancesSameGeneric);
  try
    AssertNotNull('TBox<Integer> instantiated',
      Prog.SymbolTable.FindType('TBox<Integer>'));
    AssertNotNull('TBox<string> instantiated',
      Prog.SymbolTable.FindType('TBox<string>'));
  finally
    Prog.Free();
  end;
end;

const
  { Two instances of the same generic class; one method calls another method
    on the same class.  If the method body is shared across instances without
    re-analysis, the inner Self.SetValue call will resolve to the same
    instance for both — so TBox_String_Init would emit
      call $TBox_Integer_SetValue
    instead of $TBox_String_SetValue.  Per-instance AST body cloning ensures
    each instance has its own analysed body and the correct call targets. }
  SrcTwoInstancesMethodCallsOwn =
    '''
        program Prg;
        type
          TBox<T> = class
            FValue: T;
            procedure SetValue(V: T);
            begin
              Self.FValue := V
            end;
            procedure Init(V: T);
            begin
              Self.SetValue(V)
            end;
          end;
        var
          A: TBox<Integer>;
          B: TBox<String>;
        begin end.
        ''';

procedure TGenericsTests.TestSemantic_Generic_TwoInstances_PointerFieldDistinctTypes;
var
  Prog: TProgram;
  CI, CS: TRecordTypeDesc;
  FI, FS: TFieldInfo;
begin
  Prog := AnalyseSrc(SrcTwoInstancesPointerField);
  try
    CI := TRecordTypeDesc(Prog.SymbolTable.FindType('TCell<Integer>'));
    CS := TRecordTypeDesc(Prog.SymbolTable.FindType('TCell<string>'));
    AssertNotNull('TCell<Integer> instantiated', CI);
    AssertNotNull('TCell<string>  instantiated', CS);
    FI := CI.FindField('FData');
    FS := CS.FindField('FData');
    AssertNotNull('FData on TCell<Integer>', FI);
    AssertNotNull('FData on TCell<string>',  FS);
    { The two FData fields must resolve to distinct pointer types — '^T'
      must NOT be shared across instances. }
    AssertEquals('FData<Integer> base type',
      '^Integer', FI.TypeDesc.Name);
    AssertEquals('FData<string>  base type',
      '^string',  FS.TypeDesc.Name);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestCodegen_Generic_TwoInstances_MethodCallsResolveToOwnInstance;
var
  IR:        string;
  IntInit:   Integer;
  StrInit:   Integer;
  IntBody:   string;
  StrBody:   string;
begin
  IR := GenIR(SrcTwoInstancesMethodCallsOwn);

  { Locate the two Init function bodies in the IR. }
  IntInit := Pos('function $TBox_Integer_Init', IR);
  StrInit := Pos('function $TBox_String_Init', IR);
  AssertTrue('TBox_Integer_Init function emitted', IntInit > 0);
  AssertTrue('TBox_String_Init function emitted',  StrInit > 0);

  { Take a window from each function start until the next 'function ' marker
    (or end of string). }
  if IntInit < StrInit then
  begin
    IntBody := Copy(IR, IntInit, StrInit - IntInit);
    StrBody := Copy(IR, StrInit, Length(IR) - StrInit + 1);
  end
  else
  begin
    StrBody := Copy(IR, StrInit, IntInit - StrInit);
    IntBody := Copy(IR, IntInit, Length(IR) - IntInit + 1);
  end;

  AssertTrue('TBox_Integer_Init body calls $TBox_Integer_SetValue',
    Pos('call $TBox_Integer_SetValue', IntBody) > 0);
  AssertTrue('TBox_String_Init body calls $TBox_String_SetValue',
    Pos('call $TBox_String_SetValue', StrBody) > 0);
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
    "Type mismatch ... expected 'TInner<TIntAlias>' but got 'TInner<Integer>'".
    The two instantiation paths must now agree. }
  SrcGenericInstantiatedWithAlias =
    '''
        program Prg;
        type
          TIntAlias = Integer;
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
    Inner := TRecordTypeDesc(Prog.SymbolTable.FindType('TInner<Integer>'));
    AssertNotNull('TInner<Integer> is the canonical instantiation', Inner);
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
        var B: TBox<Integer>;
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
        var P: TPair<string, Integer>;
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
    AssertEquals('diamond resolved to TBox<Integer>', 'TBox<Integer>', MC.ObjectName);
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
    AssertEquals('diamond resolved to TPair<string,Integer> (no space after comma)',
      'TPair<string,Integer>', MC.ObjectName);
    AssertTrue('marked constructor', MC.IsConstructorCall);
  finally
    Prog.Free();
  end;
end;

procedure TGenericsTests.TestCodegen_Diamond_SingleArg_EmitsSameIR;
var
  IRExplicit, IRDiamond: string;
begin
  IRExplicit := GenIR(SrcGenericUsage);
  IRDiamond  := GenIR(SrcDiamondSingleArg);
  AssertEquals('diamond IR identical to explicit', IRExplicit, IRDiamond);
end;

procedure TGenericsTests.TestCodegen_Diamond_TwoArgs_EmitsSameIR;
var
  SrcExplicit: string;
  IRExplicit, IRDiamond: string;
begin
  SrcExplicit :=
    '''
        program Prg;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
          end;
        var P: TPair<string, Integer>;
        begin
          P := TPair<string, Integer>.Create()
        end.
        ''';
  IRExplicit := GenIR(SrcExplicit);
  IRDiamond  := GenIR(SrcDiamondTwoArgs);
  AssertEquals('diamond IR identical to explicit', IRExplicit, IRDiamond);
end;

initialization
  RegisterTest(TGenericsTests);

end.
