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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TOverloadTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { a float argument never converts to an integer formal (Trunc / Round are
      explicit), and Int64 / UInt64 need a cast -- for procedures, functions and
      methods alike; the message names the argument and both types }
    procedure TestSem_FloatArgForIntegerParam_Rejected;
    { overloads whose parameter types differ only by an alias of the same type
      (UInt32 / Cardinal) are one signature: rejected at the second
      declaration, naming both spellings, instead of reaching the assembler
      as a duplicate label -- standalone, method, unit interface (both
      analysis paths) and unit implementation-only alike }
    procedure TestSem_AliasDuplicateOverload_Standalone_Rejected;
    procedure TestSem_AliasDuplicateOverload_Method_Rejected;
    procedure TestSem_AliasDuplicateOverload_UnitInterface_Rejected;
    procedure TestSem_AliasDuplicateOverload_UnitImplOnly_Rejected;
    { a unit's interface overloads still pair with implementation bodies that
      omit the directive, and an alias spelling in the body matches }
    procedure TestSem_UnitOverloads_PairWithBodies;
    { array and metaclass parameter types spell their shape in the mangled
      signature, so overloads on distinct ones get distinct, label-safe
      labels on both ISAs (they all mangled to '?' and collided); two
      declared names of one array shape are one type and are rejected }
    procedure TestAsm_ArrayAndMetaclassOverloads_DistinctLabels;
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

procedure TOverloadTests.TestSem_FloatArgForIntegerParam_Rejected;
const
  Head = '''
      program P;
      type
        TO1 = class
          procedure M(X: Integer);
        end;
      procedure TO1.M(X: Integer);
      begin
      end;
      procedure P1(X: Integer);
      begin
      end;
      function F1(X: Int64): Int64;
      begin
        Result := X
      end;
      procedure U1(X: UInt64);
      begin
      end;
      var D: Double; I: Int64; O: TO1;
      begin
      ''';
begin
  AssertEquals('procedure', 0,
    Pos('Type mismatch in argument 1 of ''P1'': expected ''Integer'' but got ''Double''',
      SemanticError(Head + 'P1(D) end.')));
  AssertTrue('float literal',
    Pos('argument 1 of ''P1''', SemanticError(Head + 'P1(2.5) end.')) >= 0);
  AssertTrue('function',
    Pos('argument 1 of ''F1''', SemanticError(Head + 'I := F1(D) end.')) >= 0);
  AssertTrue('method',
    Pos('argument 1 of ''TO1.M''', SemanticError(Head + 'O.M(D) end.')) >= 0);
  AssertTrue('Int64 for UInt64',
    Pos('argument 1 of ''U1''', SemanticError(Head + 'U1(I) end.')) >= 0);
  AssertEquals('Integer widens to Int64 and Double still', '',
    SemanticError(Head + 'I := F1(3); D := 1 end.'));
end;

const
  AliasDupMsg = 'has the same parameter signature as the declaration at line';
  AliasDupPair = '''Cardinal'' and ''UInt32'' are the same type';

{ The semantic error raised while analysing AUnitSrc -- through AnalyseUnit
  (separate compilation) when AForExport is False, else through
  AnalyseUnitForExport ahead of a trivial program -- or '' when none. }
function UnitSemanticError(const AUnitSrc: string; AForExport: Boolean): string;
begin
  Result := '';
  try
    if AForExport then
      GenAsmWithUnit(AUnitSrc, 'program p; uses ua; begin end.', TargetX86_64)
    else
      GenUnitAsm(AUnitSrc, TargetX86_64);
  except
    on E: ESemanticError do
      Result := E.Message;
  end;
end;

procedure TOverloadTests.TestSem_AliasDuplicateOverload_Standalone_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program p;
    procedure F(X: UInt32); overload; begin end;
    procedure F(X: Cardinal); overload; begin end;
    begin
    end.
    ''');
  AssertTrue('duplicate signature reported: ' + Msg, Pos(AliasDupMsg, Msg) >= 0);
  AssertTrue('alias pair named: ' + Msg, Pos(AliasDupPair, Msg) >= 0);
  AssertTrue('reported at the second declaration: ' + Msg,
    Pos('line 3', Msg) >= 0);
end;

procedure TOverloadTests.TestSem_AliasDuplicateOverload_Method_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program p;
    type
      TC = class
        procedure F(X: UInt32); overload;
        procedure F(X: Cardinal); overload;
      end;
    procedure TC.F(X: UInt32);
    begin
    end;
    begin
    end.
    ''');
  AssertTrue('duplicate signature reported: ' + Msg, Pos(AliasDupMsg, Msg) >= 0);
  AssertTrue('alias pair named: ' + Msg, Pos(AliasDupPair, Msg) >= 0);
  AssertTrue('qualified name: ' + Msg, Pos('''TC.F''', Msg) >= 0);
end;

procedure TOverloadTests.TestSem_AliasDuplicateOverload_UnitInterface_Rejected;
const
  Src = '''
    unit ua;
    interface
    procedure F(X: UInt32); overload;
    procedure F(X: Cardinal); overload;
    implementation
    procedure F(X: UInt32);
    begin
    end;
    end.
    ''';
var
  Msg: string;
begin
  Msg := UnitSemanticError(Src, False);
  AssertTrue('AnalyseUnit: ' + Msg, Pos(AliasDupMsg, Msg) >= 0);
  AssertTrue('AnalyseUnit pair: ' + Msg, Pos(AliasDupPair, Msg) >= 0);
  Msg := UnitSemanticError(Src, True);
  AssertTrue('AnalyseUnitForExport: ' + Msg, Pos(AliasDupMsg, Msg) >= 0);
  AssertTrue('AnalyseUnitForExport pair: ' + Msg, Pos(AliasDupPair, Msg) >= 0);
end;

procedure TOverloadTests.TestSem_AliasDuplicateOverload_UnitImplOnly_Rejected;
const
  Src = '''
    unit ua;
    interface
    implementation
    procedure F(X: UInt32); overload;
    begin
    end;
    procedure F(X: Cardinal); overload;
    begin
    end;
    end.
    ''';
var
  Msg: string;
begin
  Msg := UnitSemanticError(Src, False);
  AssertTrue('AnalyseUnit: ' + Msg, Pos(AliasDupMsg, Msg) >= 0);
  Msg := UnitSemanticError(Src, True);
  AssertTrue('AnalyseUnitForExport: ' + Msg, Pos(AliasDupMsg, Msg) >= 0);
end;

procedure TOverloadTests.TestSem_UnitOverloads_PairWithBodies;
const
  Src = '''
    unit ua;
    interface
    procedure F(X: UInt32); overload;
    procedure F(X: Int64); overload;
    implementation
    procedure F(X: Cardinal);
    begin
    end;
    procedure F(X: Int64);
    begin
    end;
    end.
    ''';
begin
  AssertEquals('AnalyseUnit', '', UnitSemanticError(Src, False));
  AssertEquals('AnalyseUnitForExport', '', UnitSemanticError(Src, True));
end;

procedure TOverloadTests.TestAsm_ArrayAndMetaclassOverloads_DistinctLabels;
const
  Src = '''
    program p;
    type
      TInts = array of Integer;
      TStrs = array of string;
      TPair = array[0..1] of Integer;
      TTrio = array[0..2] of Integer;
      TA = class end;
      TAClass = class of TA;
    procedure F(const X: TInts); overload; begin end;
    procedure F(const X: TStrs); overload; begin end;
    procedure G(const X: TPair); overload; begin end;
    procedure G(const X: TTrio); overload; begin end;
    procedure H(X: TAClass); overload; begin end;
    procedure H(X: Integer); overload; begin end;
    begin
    end.
    ''';
var
  Text: string;
  Target: string;
  I: Integer;
begin
  for I := 0 to 1 do
  begin
    if I = 0 then
      Target := TargetX86_64
    else
      Target := TargetArm64;
    Text := GenAsm(Src, Target);
    AssertTrue(Target + ' F(TInts)', Pos('F_D_Yi:', Text) >= 0);
    AssertTrue(Target + ' F(TStrs)', Pos('F_D_YS:', Text) >= 0);
    AssertTrue(Target + ' G(TPair)', Pos('G_D_Z0_1_i:', Text) >= 0);
    AssertTrue(Target + ' G(TTrio)', Pos('G_D_Z0_2_i:', Text) >= 0);
    AssertTrue(Target + ' H(TAClass)', Pos('H_D_MKTA:', Text) >= 0);
    AssertTrue(Target + ' no unspellable code', Pos('_D_?', Text) < 0);
  end;
  AssertTrue('one array shape under two names is one signature',
    Pos('has the same parameter signature', SemanticError('''
      program p;
      type
        TA = array of Integer;
        TB = array of Integer;
      procedure F(const X: TA); overload; begin end;
      procedure F(const X: TB); overload; begin end;
      begin
      end.
      ''')) >= 0);
end;

initialization
  RegisterTest(TOverloadTests);

end.
