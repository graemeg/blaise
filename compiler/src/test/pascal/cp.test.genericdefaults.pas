{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.genericdefaults;

{ Tests for Generics.Defaults: IEqualityComparer<T>, IComparer<T>, and the
  concrete implementations TIntegerEqualityComparer and TIntegerComparer.
  Exercises generic interface parsing, semantic instantiation, and codegen. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TGenericDefaultsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_IEqualityComparer_IsGenericInterfaceDef;
    procedure TestParse_IComparer_IsGenericInterfaceDef;
    procedure TestParse_TIntegerEqualityComparer_ImplementsGenericIntf;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IEqualityComparer_Integer_Instantiates;
    procedure TestSemantic_IComparer_Integer_Instantiates;
    procedure TestSemantic_TIntegerEqualityComparer_ImplementsOK;
    procedure TestSemantic_TIntegerComparer_ImplementsOK;
    procedure TestSemantic_Var_IEqualityComparer_Integer_IsInterface;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                      }
{ ------------------------------------------------------------------ }

const
  SrcIEqualityComparerDecl =
    '''
        program P;
        type
          IEqualityComparer<T> = interface
            function Equals(A, B: T): Boolean;
            function GetHashCode(Value: T): Integer;
          end;
        begin end.
        ''';

  SrcIComparerDecl =
    '''
        program P;
        type
          IComparer<T> = interface
            function Compare(A, B: T): Integer;
          end;
        begin end.
        ''';

  SrcTIntegerEqualityComparerDecl =
    '''
        program P;
        type
          IEqualityComparer<T> = interface
            function Equals(A, B: T): Boolean;
            function GetHashCode(Value: T): Integer;
          end;
          TIntegerEqualityComparer = class(IEqualityComparer<Integer>)
            function Equals(A, B: Integer): Boolean;
            begin
              Result := A = B
            end;
            function GetHashCode(Value: Integer): Integer;
            begin
              Result := Value
            end;
          end;
        begin end.
        ''';

  SrcTIntegerComparerDecl =
    '''
        program P;
        type
          IComparer<T> = interface
            function Compare(A, B: T): Integer;
          end;
          TIntegerComparer = class(IComparer<Integer>)
            function Compare(A, B: Integer): Integer;
            begin
              if A < B then
                Result := -1
              else if A > B then
                Result := 1
              else
                Result := 0
            end;
          end;
        begin end.
        ''';

  SrcVarIEqualityComparerInteger =
    '''
        program P;
        type
          IEqualityComparer<T> = interface
            function Equals(A, B: T): Boolean;
            function GetHashCode(Value: T): Integer;
          end;
          TIntegerEqualityComparer = class(IEqualityComparer<Integer>)
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
          C  := TIntegerEqualityComparer.Create();
          OK := C.Equals(1, 1)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TGenericDefaultsTests.ParseSrc(const ASrc: string): TProgram;
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

function TGenericDefaultsTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TGenericDefaultsTests.TestParse_IEqualityComparer_IsGenericInterfaceDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcIEqualityComparerDecl);
  try
    AssertEquals('One type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertTrue('Def is TGenericInterfaceDef', TD.Def is TGenericInterfaceDef);
  finally
    Prog.Free();
  end;
end;

procedure TGenericDefaultsTests.TestParse_IComparer_IsGenericInterfaceDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcIComparerDecl);
  try
    AssertEquals('One type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertTrue('Def is TGenericInterfaceDef', TD.Def is TGenericInterfaceDef);
  finally
    Prog.Free();
  end;
end;

procedure TGenericDefaultsTests.TestParse_TIntegerEqualityComparer_ImplementsGenericIntf;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcTIntegerEqualityComparerDecl);
  try
    { Second type decl is TIntegerEqualityComparer }
    TD := TTypeDecl(Prog.Block.TypeDecls[1]);
    AssertTrue('Is class', TD.Def is TClassTypeDef);
    CD := TClassTypeDef(TD.Def);
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

procedure TGenericDefaultsTests.TestSemantic_IEqualityComparer_Integer_Instantiates;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTIntegerEqualityComparerDecl);
  Prog.Free();
end;

procedure TGenericDefaultsTests.TestSemantic_IComparer_Integer_Instantiates;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTIntegerComparerDecl);
  Prog.Free();
end;

procedure TGenericDefaultsTests.TestSemantic_TIntegerEqualityComparer_ImplementsOK;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTIntegerEqualityComparerDecl);
  Prog.Free();
end;

procedure TGenericDefaultsTests.TestSemantic_TIntegerComparer_ImplementsOK;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTIntegerComparerDecl);
  Prog.Free();
end;

procedure TGenericDefaultsTests.TestSemantic_Var_IEqualityComparer_Integer_IsInterface;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcVarIEqualityComparerInteger);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Variable type is tyInterface',
      Ord(tyInterface), Ord(VD.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TGenericDefaultsTests);

end.
