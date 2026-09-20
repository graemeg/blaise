{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.genericintfs;

{ Tests for generic interfaces: IFoo<T> = interface ... end, class implements
  IFoo<Integer>, and codegen for the resulting itab/typeinfo. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TGenericIntfTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_GenericIntf_IsGenericInterfaceDef;
    procedure TestParse_GenericIntf_ParamName;
    procedure TestParse_GenericIntf_TwoParams;
    procedure TestParse_GenericIntf_MethodUsesTypeParam;
    procedure TestParse_Class_ImplementsGenericIntf_InParenList;
    procedure TestParse_GenericIntf_GenericParent_KeepsArgs;
    procedure TestParse_GenericIntf_ConcreteParent_KeepsArgs;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GenericIntf_InstantiatesOnVarDecl;
    procedure TestSemantic_GenericIntf_InstantiatedType_IsInterface;
    procedure TestSemantic_Class_ImplementsGenericIntf_OK;
    procedure TestSemantic_GenericIntf_MethodParamsSubstituted;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_GenericIntf_TypeinfoEmitted;
    procedure TestCodegen_GenericIntf_ItabEmitted;
    procedure TestCodegen_GenericIntf_ImpllistEmitted;
    procedure TestCodegen_GenericIntf_MethodDispatch_EmitsIndirectCall;
    procedure TestCodegen_GenericIntf_NestedArg_TypeinfoNameIsMangled;
    procedure TestCodegen_GenericIntf_AliasSupports_UsesInstanceTypeinfo;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                      }
{ ------------------------------------------------------------------ }

const
  SrcGenericIntfOneParam =
    '''
        program P;
        type
          IComparer<T> = interface
            function Compare(A, B: T): Integer;
          end;
        begin end.
        ''';

  SrcGenericIntfTwoParams =
    '''
        program P;
        type
          IConverter<TIn, TOut> = interface
            function Convert(Value: TIn): TOut;
          end;
        begin end.
        ''';

  SrcEqualityComparer =
    '''
        program P;
        type
          IEqualityComparer<T> = interface
            function Equals(A, B: T): Boolean;
            function GetHashCode(Value: T): Integer;
          end;
        var C: IEqualityComparer<Integer>;
        begin end.
        ''';

  SrcClassImplementsGenericIntf =
    '''
        program P;
        type
          IEqualityComparer<T> = interface
            function Equals(A, B: T): Boolean;
            function GetHashCode(Value: T): Integer;
          end;
          TIntegerComparer = class(IEqualityComparer<Integer>)
            function Equals(A, B: Integer): Boolean;
            begin
              Result := A = B
            end;
            function GetHashCode(Value: Integer): Integer;
            begin
              Result := Value
            end;
          end;
        var
          C: IEqualityComparer<Integer>;
        begin
          C := TIntegerComparer.Create()
        end.
        ''';

  SrcGenericIntfDispatch =
    '''
        program P;
        type
          IEqualityComparer<T> = interface
            function Equals(A, B: T): Boolean;
            function GetHashCode(Value: T): Integer;
          end;
          TIntegerComparer = class(IEqualityComparer<Integer>)
            function Equals(A, B: Integer): Boolean;
            begin
              Result := A = B
            end;
            function GetHashCode(Value: Integer): Integer;
            begin
              Result := Value
            end;
          end;
        var
          C: IEqualityComparer<Integer>;
          OK: Boolean;
        begin
          C  := TIntegerComparer.Create();
          OK := C.Equals(1, 1)
        end.
        ''';

  { A generic interface instantiated with a NESTED generic argument
    (IBox<TList<Integer>>).  The instance name the semantic pass records must
    already be mangled — the inner '<'/'>' carried through as-is produced a
    DEFINITION named typeinfo_IBox_TList<Integer> while every reference went
    through the backend mangler and asked for typeinfo_IBox_TList_Integer, so
    the reference dangled at link.  A non-nested argument hides this because
    the naive concatenation happens to be already-mangled. }
  SrcGenericIntfNestedArg =
    '''
        program P;
        type
          TList<T> = class
            Item: T;
          end;
          IBox<T> = interface
            function Get: T;
          end;
          TBox = class(IBox<TList<Integer>>)
            function Get: TList<Integer>;
            begin
              Result := nil
            end;
          end;
        var
          B: IBox<TList<Integer>>;
        begin
          B := TBox.Create()
        end.
        ''';

  { A type ALIAS of a generic interface instance, queried with Supports().
    An alias IS the aliased type, so it must resolve to that instance's ONE
    typeinfo token — emitting a reference under the alias's own name leaves
    it undefined at link, and (before the link guard) silently bound it to a
    garbage address so Supports() answered False for an interface the class
    genuinely implements. }
  SrcGenericIntfAliasSupports =
    '''
        program P;
        type
          IBox<T> = interface
            function Get: T;
          end;
          IIntBox = IBox<Integer>;
          TBox = class(IBox<Integer>)
            function Get: Integer;
            begin
              Result := 7
            end;
          end;
        var
          O: TBox;
          OK: Boolean;
        begin
          O  := TBox.Create();
          OK := Supports(O, IIntBox)
        end.
        ''';

  { A generic interface inheriting from another GENERIC interface, forwarding
    its own type parameter to the parent (Delphi syntax; the class parent list
    has always accepted this shape).  The parent list used to read a bare
    identifier and then demand ')', so the '<' was a parse error. }
  SrcGenericIntfGenericParent =
    '''
        program P;
        type
          IBase<T> = interface
            function Get: T;
          end;
          IDeriv<T> = interface(IBase<T>)
            function Extra: Integer;
          end;
          TImpl = class(IDeriv<Integer>)
            function Get: Integer;
            begin
              Result := 3
            end;
            function Extra: Integer;
            begin
              Result := 4
            end;
          end;
        var
          D: IDeriv<Integer>;
        begin
          D := TImpl.Create()
        end.
        ''';

  { The parent may also be a CONCRETE instance rather than a forwarded
    parameter — IBase<Integer> here, not IBase<T>. }
  SrcGenericIntfConcreteParent =
    '''
        program P;
        type
          IBase<T> = interface
            function Get: T;
          end;
          IDeriv<T> = interface(IBase<Integer>)
            function Extra: T;
          end;
        begin
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TGenericIntfTests.ParseSrc(const ASrc: string): TProgram;
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

function TGenericIntfTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TGenericIntfTests.GenIR(const ASrc: string): string;
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

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TGenericIntfTests.TestParse_GenericIntf_IsGenericInterfaceDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcGenericIntfOneParam);
  try
    AssertEquals('One type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertTrue('Def is TGenericInterfaceDef', TD.Def is TGenericInterfaceDef);
  finally
    Prog.Free();
  end;
end;

procedure TGenericIntfTests.TestParse_GenericIntf_ParamName;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  GID: TGenericInterfaceDef;
begin
  Prog := ParseSrc(SrcGenericIntfOneParam);
  try
    TD  := TTypeDecl(Prog.Block.TypeDecls[0]);
    GID := TGenericInterfaceDef(TD.Def);
    AssertEquals('One type param', 1, GID.ParamNames.Count);
    AssertEquals('Param name is T', 'T', GID.ParamNames[0]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericIntfTests.TestParse_GenericIntf_GenericParent_KeepsArgs;
var
  Prog: TProgram;
  GID:  TGenericInterfaceDef;
begin
  Prog := ParseSrc(SrcGenericIntfGenericParent);
  try
    { second type decl is IDeriv<T> }
    GID := TGenericInterfaceDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    { The parent must survive parsing WITH its argument list — a bare 'IBase'
      would resolve to the uninstantiated template. }
    AssertEquals('Parent keeps its type argument',
      'IBase<T>', GID.IntfDef.ParentName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericIntfTests.TestParse_GenericIntf_ConcreteParent_KeepsArgs;
var
  Prog: TProgram;
  GID:  TGenericInterfaceDef;
begin
  Prog := ParseSrc(SrcGenericIntfConcreteParent);
  try
    GID := TGenericInterfaceDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    AssertEquals('Concrete parent argument preserved',
      'IBase<Integer>', GID.IntfDef.ParentName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericIntfTests.TestParse_GenericIntf_TwoParams;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  GID: TGenericInterfaceDef;
begin
  Prog := ParseSrc(SrcGenericIntfTwoParams);
  try
    TD  := TTypeDecl(Prog.Block.TypeDecls[0]);
    GID := TGenericInterfaceDef(TD.Def);
    AssertEquals('Two type params', 2, GID.ParamNames.Count);
    AssertEquals('First param', 'TIn',  GID.ParamNames[0]);
    AssertEquals('Second param', 'TOut', GID.ParamNames[1]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericIntfTests.TestParse_GenericIntf_MethodUsesTypeParam;
var
  Prog:   TProgram;
  TD:     TTypeDecl;
  GID:    TGenericInterfaceDef;
  MDecl:  TMethodDecl;
  Par:    TMethodParam;
begin
  Prog := ParseSrc(SrcGenericIntfOneParam);
  try
    TD    := TTypeDecl(Prog.Block.TypeDecls[0]);
    GID   := TGenericInterfaceDef(TD.Def);
    AssertEquals('One method', 1, GID.IntfDef.Methods.Count);
    MDecl := TMethodDecl(GID.IntfDef.Methods[0]);
    AssertEquals('Method name', 'Compare', MDecl.Name);
    AssertEquals('Two params', 2, MDecl.Params.Count);
    Par := TMethodParam(MDecl.Params[0]);
    AssertEquals('First param type is T', 'T', Par.TypeName);
    AssertEquals('Return type is Integer', 'Integer', MDecl.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericIntfTests.TestParse_Class_ImplementsGenericIntf_InParenList;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcClassImplementsGenericIntf);
  try
    { Second type decl is TIntegerComparer }
    TD := TTypeDecl(Prog.Block.TypeDecls[1]);
    AssertTrue('Is class', TD.Def is TClassTypeDef);
    CD := TClassTypeDef(TD.Def);
    { The generic interface name should appear in implements or parent }
    AssertTrue('Has IEqualityComparer<Integer>',
      (CD.ParentName = 'IEqualityComparer<Integer>') or
      (CD.ImplementsNames.IndexOf('IEqualityComparer<Integer>') >= 0));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                        }
{ ------------------------------------------------------------------ }

procedure TGenericIntfTests.TestSemantic_GenericIntf_InstantiatesOnVarDecl;
var
  Prog: TProgram;
begin
  { 'var C: IEqualityComparer<Integer>' should trigger instantiation }
  Prog := AnalyseSrc(SrcEqualityComparer);
  Prog.Free();
end;

procedure TGenericIntfTests.TestSemantic_GenericIntf_InstantiatedType_IsInterface;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcEqualityComparer);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Variable type is tyInterface',
      Ord(tyInterface), Ord(VD.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TGenericIntfTests.TestSemantic_Class_ImplementsGenericIntf_OK;
var
  Prog: TProgram;
begin
  { Should not raise — TIntegerComparer correctly implements IEqualityComparer<Integer> }
  Prog := AnalyseSrc(SrcClassImplementsGenericIntf);
  Prog.Free();
end;

procedure TGenericIntfTests.TestSemantic_GenericIntf_MethodParamsSubstituted;
var
  Prog:     TProgram;
  VD:       TVarDecl;
  IntfDesc: TInterfaceTypeDesc;
begin
  Prog := AnalyseSrc(SrcEqualityComparer);
  try
    VD       := TVarDecl(Prog.Block.Decls[0]);
    IntfDesc := TInterfaceTypeDesc(VD.ResolvedType);
    AssertEquals('Two methods', 2, IntfDesc.MethodCount());
    AssertEquals('First method is Equals',     'Equals',      IntfDesc.MethodName(0));
    AssertEquals('Second method is GetHashCode', 'GetHashCode', IntfDesc.MethodName(1));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                         }
{ ------------------------------------------------------------------ }

procedure TGenericIntfTests.TestCodegen_GenericIntf_TypeinfoEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcClassImplementsGenericIntf);
  AssertTrue('Typeinfo for IEqualityComparer_Integer emitted',
    Pos('typeinfo_IEqualityComparer_Integer', IR) > 0);
end;

procedure TGenericIntfTests.TestCodegen_GenericIntf_ItabEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcClassImplementsGenericIntf);
  AssertTrue('Itab for TIntegerComparer/IEqualityComparer_Integer emitted',
    Pos('itab_TIntegerComparer_IEqualityComparer_Integer', IR) > 0);
end;

procedure TGenericIntfTests.TestCodegen_GenericIntf_ImpllistEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcClassImplementsGenericIntf);
  AssertTrue('Impllist for TIntegerComparer emitted',
    Pos('impllist_TIntegerComparer', IR) > 0);
end;

procedure TGenericIntfTests.TestCodegen_GenericIntf_MethodDispatch_EmitsIndirectCall;
var
  IR: string;
begin
  IR := GenIR(SrcGenericIntfDispatch);
  { Interface method call goes through itab pointer — must be an indirect call }
  AssertTrue('Interface dispatch emits indirect call', Pos('call %', IR) > 0);
end;

procedure TGenericIntfTests.TestCodegen_GenericIntf_NestedArg_TypeinfoNameIsMangled;
var
  IR: string;
begin
  IR := GenIR(SrcGenericIntfNestedArg);
  { The definition must carry the MANGLED instance name, matching what every
    reference (impllist, Supports/is/as) computes through the backend mangler.
    An unmangled definition leaves the reference undefined at link. }
  AssertTrue('Typeinfo for IBox_TList_Integer emitted',
    Pos('typeinfo_IBox_TList_Integer', IR) > 0);
  { And no raw-bracket symbol survives anywhere — that name is not a legal
    symbol and is what the dangling reference was looking past. }
  AssertTrue('No unmangled typeinfo_IBox_TList<Integer> symbol',
    Pos('typeinfo_IBox_TList<', IR) < 0);
end;

procedure TGenericIntfTests.TestCodegen_GenericIntf_AliasSupports_UsesInstanceTypeinfo;
var
  IR: string;
begin
  IR := GenIR(SrcGenericIntfAliasSupports);
  { Supports(O, IIntBox) must reference the ALIASED INSTANCE's token, which
    is the one actually defined and listed in the class's impllist. }
  AssertTrue('Supports references typeinfo_IBox_Integer',
    Pos('typeinfo_IBox_Integer', IR) > 0);
  { ...and never the alias's own name, which nothing defines. }
  AssertTrue('No typeinfo_IIntBox reference',
    Pos('typeinfo_IIntBox', IR) < 0);
end;

initialization
  RegisterTest(TGenericIntfTests);

end.
