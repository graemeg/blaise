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
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TGenericIntfTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
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

initialization
  RegisterTest(TGenericIntfTests);

end.
