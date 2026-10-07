{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.anonmethods;

{ Tests for anonymous methods / closures — Phases 0 and 1 of
  docs/anonymous-methods-design.adoc:

    * Parser: 'reference to procedure/function' type form; anonymous
      procedure/function literals in expression position; [Weak] capture
      list storage.
    * Semantic: reference type resolution (16-byte fat value); literal
      signature checking against the target; Phase-1 capture rejection
      (an enclosing local referenced from a literal body is undeclared in
      the thunk's module-scope analysis).
    * Run time: closures, captures, arrows and adapters are exercised by
      cp.test.e2e.anonmethods. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TAnonMethodTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { Parser }
    procedure TestParse_ReferenceToProcedure_TypeDecl;
    procedure TestParse_ReferenceToFunction_ReturnType;
    procedure TestParse_AnonLiteral_InAssignment;
    procedure TestParse_AnonLiteral_WeakCaptureListStored;

    { Semantic }
    procedure TestSemantic_ReferenceType_ResolvesTo16ByteDesc;
    procedure TestSemantic_LiteralSignatureMismatch_Fails;
    procedure TestSemantic_Phase2_LocalCaptureAccepted;
    procedure TestSemantic_Phase2_VarParamCaptureRejected;
    procedure TestSemantic_Phase3_MethodLiteralCapturesSelf;
    procedure TestSemantic_Phase3_MethodPtrCoercionAccepted;
    procedure TestSemantic_Phase4_BlockVarOutOfScopeAfterBlock;
    procedure TestSemantic_Phase4_BlockVarDuplicateRejected;
    procedure TestSemantic_Phase4_MixedScopeCaptureRejected;
    procedure TestSemantic_Phase5_WeakNonSelfRejected;
    procedure TestSemantic_NestedRoutineInMethod_ImplicitSelfAccepted;
    procedure TestSemantic_NestedRoutineInMethod_SelfContainedAccepted;
    procedure TestSemantic_Phase9a_ArrowWithoutTarget_Rejected;
    procedure TestSemantic_Phase6_GenericRefAlias_InstantiatesAtInteger;
    procedure TestSemantic_Phase6_GenericRefAlias_InstantiatesAtString;

    { Codegen }

    { End-to-end }
    { Phase 9a — terse '->' lambdas (desugared to TAnonMethodExpr). }
    { Phase 9b — two-phase deferred inference: lambdas in ARGUMENT position. }
    { ... and through a procedural-typed VARIABLE or FIELD (implicit-Self and
      qualified), whose single signature types the lambda. }
    procedure TestSemantic_Arrow_ArgPosition_ProcTypeCalls_Inferred;
    { Phase 10 gate — a generic METHOD with its own type param on a generic
      class monomorphises and runs (TBox<T>.MapTo<R>, two different R's). }
  end;

implementation

function TAnonMethodTests.ParseSrc(const ASrc: string): TProgram;
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

function TAnonMethodTests.AnalyseSrc(const ASrc: string): TProgram;
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

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TAnonMethodTests.TestParse_ReferenceToProcedure_TypeDecl;
const
  Src =
    '''
    program P;
    type
      TProc = reference to procedure(AValue: Integer);
    begin end.
    ''';
var
  Prog: TProgram;
  PD:   TProceduralTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    AssertTrue('def is TProceduralTypeDef',
      TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def is TProceduralTypeDef);
    PD := TProceduralTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertTrue('IsReference set', PD.IsReference);
    AssertFalse('IsMethodPtr not set', PD.IsMethodPtr);
    AssertFalse('is a procedure', PD.IsFunction);
    AssertEquals('one param', 1, PD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestParse_ReferenceToFunction_ReturnType;
const
  Src =
    '''
    program P;
    type
      TThunk = reference to function(const A, B: Integer): Integer;
    begin end.
    ''';
var
  Prog: TProgram;
  PD:   TProceduralTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    PD := TProceduralTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertTrue('IsReference set', PD.IsReference);
    AssertTrue('is a function', PD.IsFunction);
    AssertEquals('return type', 'Integer', PD.ReturnTypeName);
    AssertEquals('two params', 2, PD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestParse_AnonLiteral_InAssignment;
const
  Src =
    '''
    program P;
    type
      TIntProc = reference to procedure(AValue: Integer);
    var
      V: TIntProc;
    begin
      V := procedure(AValue: Integer)
      begin
        WriteLn(AValue)
      end
    end.
    ''';
var
  Prog: TProgram;
  Asn:  TAssignment;
  AME:  TAnonMethodExpr;
begin
  Prog := ParseSrc(Src);
  try
    Asn := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertTrue('RHS is an anonymous-method literal',
      Asn.Expr is TAnonMethodExpr);
    AME := TAnonMethodExpr(Asn.Expr);
    AssertNotNull('literal decl present', AME.Decl);
    AssertEquals('one declared param', 1, AME.Decl.Params.Count);
    AssertEquals('procedure literal has no return type', '',
      AME.Decl.ReturnTypeName);
    AssertNotNull('body present', AME.Decl.Body);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestParse_AnonLiteral_WeakCaptureListStored;
const
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    var
      V: TProc;
    begin
      V := procedure [Weak A, B]
      begin
      end
    end.
    ''';
var
  Prog: TProgram;
  AME:  TAnonMethodExpr;
begin
  Prog := ParseSrc(Src);
  try
    AME := TAnonMethodExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertNotNull('weak capture list stored', AME.WeakCaptures);
    AssertEquals('two names', 2, AME.WeakCaptures.Count);
    AssertEquals('first', 'A', AME.WeakCaptures.Strings[0]);
    AssertEquals('second', 'B', AME.WeakCaptures.Strings[1]);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TAnonMethodTests.TestSemantic_ReferenceType_ResolvesTo16ByteDesc;
const
  Src =
    '''
    program P;
    type
      TProc = reference to procedure(AValue: Integer);
    var
      V: TProc;
    begin
      V := nil
    end.
    ''';
var
  Prog: TProgram;
  Desc: TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    Desc := Prog.SymbolTable.FindType('TProc');
    AssertNotNull('TProc resolved', Desc);
    AssertTrue('procedural desc', Desc is TProceduralTypeDesc);
    AssertTrue('IsReference on desc', TProceduralTypeDesc(Desc).IsReference);
    AssertEquals('16-byte fat value', 16, Desc.ByteSize());
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestSemantic_LiteralSignatureMismatch_Fails;
const
  Src =
    '''
    program P;
    type
      TIntProc = reference to procedure(AValue: Integer);
    var
      V: TIntProc;
    begin
      V := procedure(AValue: string)
      begin
      end
    end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: TObject do OK := True;
  end;
  AssertTrue('literal with mismatched signature is rejected', OK);
end;

procedure TAnonMethodTests.TestSemantic_Phase2_LocalCaptureAccepted;
const
  { Phase 2: the literal references the enclosing routine's local 'Outer'.
    Capture promotion accepts it and records the captured name on the lifted
    thunk so codegen can redirect through the environment record. }
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    procedure Run;
    var
      Outer: Integer;
      V: TProc;
    begin
      Outer := 1;
      V := procedure
      begin
        WriteLn(Outer)
      end;
      V()
    end;
    begin
      Run()
    end.
    ''';
var
  Prog:  TProgram;
  MD:    TMethodDecl;
  Thunk: TMethodDecl;
  I:     Integer;
begin
  Prog := AnalyseSrc(Src);
  try
    { Find the lifted thunk appended to the module's ProcDecls. }
    Thunk := nil;
    for I := 0 to Prog.Block.ProcDecls.Count - 1 do
    begin
      MD := TMethodDecl(Prog.Block.ProcDecls.Items[I]);
      if MD.Name = '__closure_1' then Thunk := MD;
    end;
    AssertNotNull('lifted thunk registered', Thunk);
    AssertNotNull('thunk records env captures', Thunk.EnvCaptured);
    AssertEquals('one captured name', 1, Thunk.EnvCaptured.Count);
    AssertEquals('captured name', 'Outer', Thunk.EnvCaptured.Strings[0]);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestSemantic_Phase2_VarParamCaptureRejected;
const
  { Capturing a var/out parameter is rejected in Phase 2: the env would have
    to store the CALLER frame's address, which dangles once the closure
    escapes (design doc, Risks).  A clear diagnostic is required. }
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    procedure Run(var X: Integer);
    var
      V: TProc;
    begin
      V := procedure
      begin
        WriteLn(X)
      end;
      V()
    end;
    var N: Integer;
    begin
      N := 5;
      Run(N)
    end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: TObject do OK := True;
  end;
  AssertTrue('capturing a var parameter is rejected', OK);
end;

procedure TAnonMethodTests.TestSemantic_Phase3_MethodLiteralCapturesSelf;
const
  { Phase 3: a literal inside an INSTANCE method body captures the method's
    locals AND Self (conservatively), so implicit and explicit member access
    work through the env.  The lifted thunk's EnvCaptured must list both. }
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
      TCounter = class
        FCount: Integer;
        procedure Bump;
      end;
    procedure TCounter.Bump;
    var
      Step: Integer;
      V: TProc;
    begin
      Step := 2;
      V := procedure
      begin
        FCount := FCount + Step
      end;
      V()
    end;
    var C: TCounter;
    begin
      C := TCounter.Create();
      C.Bump();
      WriteLn(C.FCount)
    end.
    ''';
var
  Prog:  TProgram;
  MD:    TMethodDecl;
  Thunk: TMethodDecl;
  I:     Integer;
begin
  Prog := AnalyseSrc(Src);
  try
    Thunk := nil;
    for I := 0 to Prog.Block.ProcDecls.Count - 1 do
    begin
      MD := TMethodDecl(Prog.Block.ProcDecls.Items[I]);
      if MD.Name = '__closure_1' then Thunk := MD;
    end;
    AssertNotNull('lifted thunk registered', Thunk);
    AssertNotNull('thunk records env captures', Thunk.EnvCaptured);
    AssertTrue('Step captured', Thunk.EnvCaptured.IndexOf('Step') >= 0);
    AssertTrue('Self captured', Thunk.EnvCaptured.IndexOf('Self') >= 0);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestSemantic_Phase4_BlockVarOutOfScopeAfterBlock;
const
  { A block-scoped var is invisible after its enclosing block ends. }
  Src =
    '''
    program P;
    procedure Run;
    begin
      begin
        var X: Integer := 1;
        WriteLn(X)
      end;
      WriteLn(X)
    end;
    begin
      Run()
    end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: TObject do OK := True;
  end;
  AssertTrue('block var out of scope after the block', OK);
end;

procedure TAnonMethodTests.TestSemantic_Phase4_BlockVarDuplicateRejected;
const
  { v1 restriction: a block var may not shadow an existing local. }
  Src =
    '''
    program P;
    procedure Run;
    var
      X: Integer;
    begin
      X := 1;
      begin
        var X: Integer := 2;
        WriteLn(X)
      end
    end;
    begin
      Run()
    end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: TObject do OK := True;
  end;
  AssertTrue('shadowing block var is rejected', OK);
end;

procedure TAnonMethodTests.TestSemantic_Phase4_MixedScopeCaptureRejected;
const
  { v1 restriction: one closure may not capture BOTH a block-scoped var and
    a routine-level var (environment chaining is deferred). }
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    var G: TProc;
    procedure Run;
    var
      Outer: Integer;
    begin
      Outer := 1;
      begin
        var Inner: Integer := 2;
        G := procedure
        begin
          WriteLn(Outer + Inner)
        end
      end
    end;
    begin
      Run();
      G()
    end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: TObject do OK := True;
  end;
  AssertTrue('mixed-scope capture is rejected in v1', OK);
end;

procedure TAnonMethodTests.TestSemantic_Phase5_WeakNonSelfRejected;
const
  { v1: [Weak] capture is supported for Self only (the cycle-breaking use
    case); weak capture of ordinary variables is a later extension. }
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    procedure Run;
    var
      Outer: Integer;
      V: TProc;
    begin
      Outer := 1;
      V := procedure [Weak Outer]
      begin
        WriteLn(Outer)
      end;
      V()
    end;
    begin
      Run()
    end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: TObject do OK := True;
  end;
  AssertTrue('[Weak] on a non-Self capture is rejected', OK);
end;

procedure TAnonMethodTests.TestSemantic_Phase3_MethodPtrCoercionAccepted;
const
  { Phase 3: an 'of object' method-pointer value coerces into a
    'reference to' slot of the same signature (Env := receiver,
    strong-retained). }
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
      TObj = class
        procedure Ping;
      end;
    procedure TObj.Ping;
    begin
      WriteLn('ping')
    end;
    var
      O: TObj;
      V: TProc;
    begin
      O := TObj.Create();
      V := @O.Ping;
      V()
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);   { must not raise }
  Prog.Free();
end;

{ ------------------------------------------------------------------ }
{ Phase 6 — generics: reference-to aliases + closures in generic bodies }
{ ------------------------------------------------------------------ }

const
  Phase6AliasSrc =
    '''
    program P;
    type
      TGetter<T> = reference to function(): T;
    var
      GI: TGetter<Integer>;
      GS: TGetter<string>;
    begin
    end.
    ''';

procedure TAnonMethodTests.TestSemantic_NestedRoutineInMethod_ImplicitSelfAccepted;
const
  Src =
    '''
    program P;
    type
      TC = class
        FVal: Integer;
        procedure Helper();
        procedure M();
      end;
    procedure TC.Helper();
    begin
    end;
    procedure TC.M();
      procedure Inner();
      begin
        FVal := FVal + 1;
        Helper()
      end;
    begin
      Inner()
    end;
    begin
    end.
    ''';
begin
  { BUG-008: a nested routine inside a METHOD body captures the method's
    Self like any other outer variable — implicit member access (bare field
    names, bare method calls) resolves against the enclosing class. }
  AnalyseSrc(Src).Free()
end;

procedure TAnonMethodTests.TestSemantic_NestedRoutineInMethod_SelfContainedAccepted;
const
  Src =
    '''
    program P;
    type
      TC = class
        procedure M();
      end;
    procedure TC.M();
    var X: Integer;
      procedure Inner(K: Integer);
      begin
        WriteLn(X + K)
      end;
    begin
      X := 1;
      Inner(2)
    end;
    begin
    end.
    ''';
begin
  { Self-contained nested routines (and captures of the method's LOCALS)
    are supported — only Self access is not (BUG-008). }
  AnalyseSrc(Src).Free()
end;


procedure TAnonMethodTests.TestSemantic_Phase6_GenericRefAlias_InstantiatesAtInteger;
var
  Prog: TProgram;
  TD:   TTypeDesc;
  PD:   TProceduralTypeDesc;
begin
  Prog := AnalyseSrc(Phase6AliasSrc);
  try
    TD := Prog.SymbolTable.FindType('TGetter<Integer>');
    AssertNotNull('TGetter<Integer> instantiated', TD);
    AssertTrue('is procedural', TD is TProceduralTypeDesc);
    PD := TProceduralTypeDesc(TD);
    AssertTrue('IsReference set', PD.IsReference);
    AssertNotNull('return type resolved', PD.ReturnType);
    AssertEquals('return type is Integer', 'Integer', PD.ReturnType.Name)
  finally
    Prog.Free()
  end
end;

procedure TAnonMethodTests.TestSemantic_Phase6_GenericRefAlias_InstantiatesAtString;
var
  Prog: TProgram;
  TD:   TTypeDesc;
  PD:   TProceduralTypeDesc;
begin
  Prog := AnalyseSrc(Phase6AliasSrc);
  try
    TD := Prog.SymbolTable.FindType('TGetter<string>');
    AssertNotNull('TGetter<string> instantiated', TD);
    PD := TProceduralTypeDesc(TD);
    AssertTrue('IsReference set', PD.IsReference);
    AssertEquals('return type is string', 'string', PD.ReturnType.Name)
  finally
    Prog.Free()
  end
end;

{ ------------------------------------------------------------------ }
{ Phase 9a — arrow lambdas                                            }
{ ------------------------------------------------------------------ }

procedure TAnonMethodTests.TestSemantic_Phase9a_ArrowWithoutTarget_Rejected;
const
  Src =
    '''
    program P;
    var X: Integer;
    begin
      X := ((A) -> A + 1)(1)
    end.
    ''';
var
  Caught: Boolean;
begin
  { An arrow with no 'reference to' target context cannot be typed —
    reject with a directed diagnostic (argument-position inference is
    Phase 9b). }
  Caught := False;
  try
    AnalyseSrc(Src).Free()
  except
    on E: Exception do
    begin
      Caught := True;
      AssertTrue('diagnostic mentions inference: ' + E.Message,
        Pos('Cannot infer', E.Message) >= 0)
    end
  end;
  AssertTrue('arrow without target rejected', Caught)
end;

{ ------------------------------------------------------------------ }
{ Phase 9b — deferred inference in argument position                  }
{ ------------------------------------------------------------------ }

const
  SrcArrowProcTypeCalls =
    '''
    program P;
    type
      TSel = reference to function(N: Integer): Integer;
      TRun = reference to procedure(N: Integer; F: TSel);
      TApply = reference to function(N: Integer; F: TSel): Integer;
      TBox = class
      public
        FRun: TRun;
        FApply: TApply;
        procedure Drv();
      end;
    procedure TBox.Drv();
    begin
      FRun(1, X -> X + 10);
      WriteLn(FApply(2, X -> X * 3))
    end;
    var
      Run: TRun;
      Apply: TApply;
      B: TBox;
    begin
      Run := procedure(N: Integer; F: TSel)
        begin
          WriteLn(F(N))
        end;
      Apply := function(N: Integer; F: TSel): Integer
        begin
          Result := F(N)
        end;
      Run(4, X -> X + 1);
      WriteLn(Apply(5, X -> X * 2));
      B := TBox.Create();
      B.FRun := Run;
      B.FApply := Apply;
      B.Drv();
      B.FRun(6, X -> X - 1);
      WriteLn(B.FApply(7, X -> X + 100));
      B.Free()
    end.
    ''';

procedure TAnonMethodTests.TestSemantic_Arrow_ArgPosition_ProcTypeCalls_Inferred;
begin
  { Proc-variable and implicit-Self proc-field calls (statement + expression)
    used to reject the arrow with "Cannot infer": their hand-copied arg loops
    never inferred a pending lambda from the 'reference to' param.  They now
    share AnalyseProcTypeCallArgs with the qualified arms. }
  AnalyseSrc(SrcArrowProcTypeCalls).Free()
end;

initialization
  RegisterTest(TAnonMethodTests);

end.
