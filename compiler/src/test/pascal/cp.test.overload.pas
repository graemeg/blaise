{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.overload;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TOverloadTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { Phase A — arity-distinct standalone overloading }

    { Parser: 'overload' directive sets the IsOverload flag on TMethodDecl }
    procedure TestParse_OverloadDirective_SetsFlag;

    { Semantic: two same-named procs with 'overload' both keep their decls }
    procedure TestSemantic_TwoArities_BothRegistered;

    { Semantic: duplicate name without 'overload' is rejected }
    procedure TestSemantic_DuplicateWithoutOverload_RaisesError;

    { Semantic: mixing 'overload' with non-'overload' is rejected }
    procedure TestSemantic_MixingOverloadAndPlain_RaisesError;

    { Semantic: call site with no matching arity raises error }
    procedure TestSemantic_NoMatchingArity_RaisesError;

    { Codegen: each overload gets a distinct mangled QBE name }

    { Codegen: call sites resolve to the correct mangled name based on arg count }

    { Phase B — type-distinct resolution }

    { Two same-arity overloads distinguished only by parameter type }
    procedure TestSemantic_TypeDistinct_BothRegistered;

    { Codegen: per-type mangled names use the type-code scheme }

    { Resolution: exact-type match preferred over widening (Integer
      argument selects Integer overload, not Double overload) }

    { Resolution: when no exact match, widening is taken (Integer argument
      selects Double overload when no Integer overload exists) }

    { Two same-arity overloads where the argument is an exact match for
      neither but a widening match for both — must be flagged ambiguous }
    procedure TestSemantic_AmbiguousOverload_RaisesError;

    { Phase C — class method overloading }

    { Two methods sharing a name but distinguished by parameter type }
    procedure TestSemantic_ClassOverload_BothRegistered;

    { Class method dup without 'overload' rejected }
    procedure TestSemantic_ClassDupNoOverload_RaisesError;

    { virtual + overload base; override + overload descendant }

    { Overload resolution in implicit-self expression context: a 3-arg call
      to a method that has a 3-param and a 4-param (open-array) overload
      must resolve to the 3-param overload, not fail with arity mismatch. }

    { Constructor call site must use overload resolution.  When a class
      declares two same-named constructors and the higher-arity overload
      is indexed first, FindMethodDecl alone would pick it and then
      AppendDefaultArgs would fail on the unfilled parameter that has no
      default. }
    procedure TestSemantic_ConstructorOverload_PicksCorrectArity;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TOverloadTests.ParseSrc(const ASrc: string): TProgram;
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

function TOverloadTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

procedure TOverloadTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared sources                                                      }
{ ------------------------------------------------------------------ }

const
  SrcTwoArities =
    '''
        program P;
        procedure Greet; overload;
        begin
          WriteLn('hello')
        end;
        procedure Greet(N: Integer); overload;
        begin
          WriteLn(N)
        end;
        begin
          Greet();
          Greet(42)
        end.
        ''';

  SrcDupNoOverload =
    '''
        program P;
        procedure Greet;
        begin
        end;
        procedure Greet(N: Integer);
        begin
        end;
        begin
        end.
        ''';

  SrcMixedOverloadFlag =
    '''
        program P;
        procedure Greet; overload;
        begin
        end;
        procedure Greet(N: Integer);
        begin
        end;
        begin
        end.
        ''';

  SrcNoMatchingArity =
    '''
        program P;
        procedure Greet; overload;
        begin
        end;
        procedure Greet(N: Integer); overload;
        begin
        end;
        begin
          Greet(1, 2)
        end.
        ''';

  SrcTypeDistinct =
    '''
        program P;
        procedure Show(N: Integer); overload;
        begin
          WriteLn(N)
        end;
        procedure Show(S: string); overload;
        begin
          WriteLn(S)
        end;
        begin
          Show(42);
          Show('hi')
        end.
        ''';

  SrcClassOverload =
    '''
        program P;
        type
          TFoo = class
            procedure Show(N: Integer); overload;
            procedure Show(S: string); overload;
          end;
          procedure TFoo.Show(N: Integer); overload;
          begin WriteLn(N) end;
          procedure TFoo.Show(S: string); overload;
          begin WriteLn(S) end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.Show(42);
          F.Show('hi')
        end.
        ''';

  SrcClassDupNoOverload =
    '''
        program P;
        type
          TFoo = class
            procedure Show(N: Integer);
            procedure Show(S: string);
          end;
          procedure TFoo.Show(N: Integer);
          begin end;
          procedure TFoo.Show(S: string);
          begin end;
        begin end.
        ''';

  { Two same-arity overloads — Double + Single — both reachable from an
    integer literal only by widening, with equal score → ambiguous. }
  { Constructor overload where the 2-arg variant is declared first — so
    FindMethodDecl would return it for the 1-arg call site.  Without
    overload resolution at the constructor call, AppendDefaultArgs would
    fail because parameter B of the 2-arg Create has no default. }
  SrcCtorOverload =
    '''
        program P;
        type
          TFoo = class
            constructor Create(A: Integer; B: Integer); overload;
            constructor Create(A: Integer); overload;
          end;
          constructor TFoo.Create(A: Integer; B: Integer);
          begin end;
          constructor TFoo.Create(A: Integer);
          begin end;
        var F: TFoo;
        begin
          F := TFoo.Create(42);
          F.Free()
        end.
        ''';

  SrcAmbiguousOverload =
    'program P;'                                            + LineEnding +
    'procedure F(D: Double); overload;'                     + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'procedure F(S: Single); overload;'                     + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'begin'                                                 + LineEnding +
    '  F(42)'                                               + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Tests                                                               }
{ ------------------------------------------------------------------ }

procedure TOverloadTests.TestParse_OverloadDirective_SetsFlag;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcTwoArities);
  try
    AssertEquals('two procs parsed', 2, Prog.Block.ProcDecls.Count);
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertTrue('first proc has IsOverload=True', MD.IsOverload);
    MD := TMethodDecl(Prog.Block.ProcDecls[1]);
    AssertTrue('second proc has IsOverload=True', MD.IsOverload);
  finally
    Prog.Free();
  end;
end;

procedure TOverloadTests.TestSemantic_TwoArities_BothRegistered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTwoArities);
  try
    AssertEquals('both proc decls survive', 2, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TOverloadTests.TestSemantic_DuplicateWithoutOverload_RaisesError;
begin
  AnalyseExpectError(SrcDupNoOverload);
end;

procedure TOverloadTests.TestSemantic_MixingOverloadAndPlain_RaisesError;
begin
  AnalyseExpectError(SrcMixedOverloadFlag);
end;

procedure TOverloadTests.TestSemantic_NoMatchingArity_RaisesError;
begin
  AnalyseExpectError(SrcNoMatchingArity);
end;

{ ------------------------------------------------------------------ }
{ Phase B — type-distinct resolution                                  }
{ ------------------------------------------------------------------ }

procedure TOverloadTests.TestSemantic_TypeDistinct_BothRegistered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTypeDistinct);
  try
    AssertEquals('both proc decls survive', 2, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TOverloadTests.TestSemantic_AmbiguousOverload_RaisesError;
begin
  AnalyseExpectError(SrcAmbiguousOverload);
end;

{ ------------------------------------------------------------------ }
{ Phase C — class method overloading                                  }
{ ------------------------------------------------------------------ }

procedure TOverloadTests.TestSemantic_ClassOverload_BothRegistered;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := AnalyseSrc(SrcClassOverload);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('TFoo has two Show methods', 2, CD.Methods.Count);
  finally
    Prog.Free();
  end;
end;

procedure TOverloadTests.TestSemantic_ClassDupNoOverload_RaisesError;
begin
  AnalyseExpectError(SrcClassDupNoOverload);
end;

procedure TOverloadTests.TestSemantic_ConstructorOverload_PicksCorrectArity;
var
  Prog: TProgram;
begin
  { Must analyse without error.  Previously raised:
    "No default value for parameter 'B' of 'Create'" because the
    constructor call site used FindMethodDecl, which picked the 2-arg
    overload (indexed first) and then failed to fill parameter B. }
  Prog := AnalyseSrc(SrcCtorOverload);
  Prog.Free();
end;

initialization
  RegisterTest(TOverloadTests);

end.
