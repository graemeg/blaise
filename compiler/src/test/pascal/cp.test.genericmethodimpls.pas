{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.genericmethodimpls;

{ Tests for generic class method implementations in standalone form:
    procedure TList<T>.Add(Value: T);
    begin ... end;
  This is the standard Object Pascal unit structure where method bodies live in
  the implementation section rather than inline in the class declaration. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TGenericMethodImplTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_OwnerTypeName_SetForGenericImpl;
    procedure TestParse_OwnerTypeParams_SetForGenericImpl;
    procedure TestParse_MethodName_IsCorrect;
    procedure TestParse_TwoTypeParams_BothRecorded;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ForwardOnlyClass_WithSeparateImpl_Compiles;
    procedure TestSemantic_TwoMethods_BothLinked;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_SeparateImpl_AsmMatchesInlineVersion;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                      }
{ ------------------------------------------------------------------ }

const
  { Class with forward-only method signatures — bodies supplied separately }
  SrcForwardOnly =
    '''
        program P;
        type
          TBox<T> = class
            FVal: T;
            procedure SetVal(V: T);
            function GetVal: T;
          end;
        procedure TBox<T>.SetVal(V: T);
        begin
          Self.FVal := V
        end;
        function TBox<T>.GetVal: T;
        begin
          Result := Self.FVal
        end;
        var B: TBox<Integer>;
        begin
          B := TBox<Integer>.Create()
        end.
        ''';

  { Identical logic, but methods defined inline — used to check IR equivalence }
  SrcInline =
    '''
        program P;
        type
          TBox<T> = class
            FVal: T;
            procedure SetVal(V: T);
            begin
              Self.FVal := V
            end;
            function GetVal: T;
            begin
              Result := Self.FVal
            end;
          end;
        var B: TBox<Integer>;
        begin
          B := TBox<Integer>.Create()
        end.
        ''';

  { Two type params — exercises multi-param parsing }
  SrcTwoTypeParams =
    '''
        program P;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
            procedure Assign(AKey: K; AVal: V);
          end;
        procedure TPair<K, V>.Assign(AKey: K; AVal: V);
        begin
          Self.FKey := AKey;
          Self.FVal := AVal
        end;
        begin end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TGenericMethodImplTests.ParseSrc(const ASrc: string): TProgram;
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

function TGenericMethodImplTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TGenericMethodImplTests.TestParse_OwnerTypeName_SetForGenericImpl;
var
  Prog:  TProgram;
  MDecl: TMethodDecl;
begin
  Prog := ParseSrc(SrcForwardOnly);
  try
    AssertTrue('At least one proc decl', Prog.Block.ProcDecls.Count >= 1);
    MDecl := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('OwnerTypeName is TBox', 'TBox', MDecl.OwnerTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericMethodImplTests.TestParse_OwnerTypeParams_SetForGenericImpl;
var
  Prog:  TProgram;
  MDecl: TMethodDecl;
begin
  Prog := ParseSrc(SrcForwardOnly);
  try
    MDecl := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertTrue('OwnerTypeParams assigned', MDecl.OwnerTypeParams <> nil);
    AssertEquals('One type param', 1, MDecl.OwnerTypeParams.Count);
    AssertEquals('Param name is T', 'T', MDecl.OwnerTypeParams[0]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericMethodImplTests.TestParse_MethodName_IsCorrect;
var
  Prog:  TProgram;
  MDecl: TMethodDecl;
begin
  Prog := ParseSrc(SrcForwardOnly);
  try
    MDecl := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('Method name is SetVal', 'SetVal', MDecl.Name);
  finally
    Prog.Free();
  end;
end;

procedure TGenericMethodImplTests.TestParse_TwoTypeParams_BothRecorded;
var
  Prog:  TProgram;
  MDecl: TMethodDecl;
begin
  Prog := ParseSrc(SrcTwoTypeParams);
  try
    AssertTrue('Has proc decl', Prog.Block.ProcDecls.Count >= 1);
    MDecl := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('OwnerTypeName is TPair', 'TPair', MDecl.OwnerTypeName);
    AssertTrue('OwnerTypeParams assigned', MDecl.OwnerTypeParams <> nil);
    AssertEquals('Two type params', 2, MDecl.OwnerTypeParams.Count);
    AssertEquals('First param K', 'K', MDecl.OwnerTypeParams[0]);
    AssertEquals('Second param V', 'V', MDecl.OwnerTypeParams[1]);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                        }
{ ------------------------------------------------------------------ }

procedure TGenericMethodImplTests.TestSemantic_ForwardOnlyClass_WithSeparateImpl_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcForwardOnly);
  Prog.Free();
end;

procedure TGenericMethodImplTests.TestSemantic_TwoMethods_BothLinked;
var
  Prog:  TProgram;
  GDef:  TGenericTypeDef;
  MDecl: TMethodDecl;
  SA:    TSemanticAnalyser;
begin
  Prog := ParseSrc(SrcForwardOnly);
  try
    SA := TSemanticAnalyser.Create();
    try
      SA.Analyse(Prog);
    finally
      SA.Free();
    end;
    { Locate the generic template's method bodies directly on the AST }
    GDef := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MDecl := TMethodDecl(GDef.ClassDef.Methods[0]);  { SetVal }
    AssertTrue('SetVal body linked', MDecl.Body <> nil);
    MDecl := TMethodDecl(GDef.ClassDef.Methods[1]);  { GetVal }
    AssertTrue('GetVal body linked', MDecl.Body <> nil);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                         }
{ ------------------------------------------------------------------ }

{ A body supplied in the implementation section must lower exactly as the
  same body written inline: any difference is a monomorphisation divergence
  that a small program need not expose. }
procedure TGenericMethodImplTests.TestCodegen_SeparateImpl_AsmMatchesInlineVersion;
begin
  AssertEquals('x86-64: separate-impl asm equals inline asm',
    GenAsm(SrcInline, TargetX86_64), GenAsm(SrcForwardOnly, TargetX86_64));
  AssertEquals('arm64: separate-impl asm equals inline asm',
    GenAsm(SrcInline, TargetArm64), GenAsm(SrcForwardOnly, TargetArm64));
end;

initialization
  RegisterTest(TGenericMethodImplTests);

end.
