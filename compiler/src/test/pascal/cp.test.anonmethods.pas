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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

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

    { A call through a captured closure PARAMETER inside an anonymous
      method (G() in function(...) begin Result := G() end) was
      'Undeclared function': the capture walker runs before the body is
      analysed, so it never saw the call as a use of G. }
    procedure TestSemantic_CallThroughCapturedClosureParam_Accepted;

    { A literal nested in another literal that captures nothing is an
      ordinary closure value; it was rejected as "capturing variables of an
      enclosing anonymous method" before its captures were even collected.
      Capturing the enclosing literal's names still needs environment
      chaining and stays a clear error. }
    procedure TestSemantic_NestedLiteral_NoCaptures_Accepted;
    procedure TestSemantic_NestedLiteral_CapturingOuterLiteral_Rejected;
    { A literal inside a STATIC method: there is no Self to capture, and the
      conservative instance-method Self capture failed with "Cannot resolve
      captured variable 'Self'". }
    procedure TestSemantic_StaticMethodLiteral_CapturesNoSelf;

    { A call through the procedural value an element or a dereference holds,
      as a STATEMENT: A[I](args); and P^(args);  The parser read a subscript
      in statement position as the start of an assignment or member access
      ("Expected '.' or ':=' after subscript"). }
    procedure TestParse_ExprCallStmt_ElementAndDeref;
    procedure TestParse_ExprCallStmt_BareElementWithoutParens_Rejected;
    { ...and through the value a CALL returns: GetFn()(X); and
      GetMaker()(X).Run();  The statement parser stopped at the first call
      ("Expected 'end' but got '('"). }
    procedure TestParse_ExprCallStmt_CallResultCallee;
    { Codegen }
    { Use(MakeFn()): the closure a call returns lands in a per-site scratch
      whose ADDRESS is the argument; x86-64 passed the Code word as the
      pair's address (a crash), arm64 refused the form. }
    procedure TestCodegen_ClosureCallResultArg_PassesScratchAddress;
    { an interface parameter captured by an anonymous method: both 8-byte
      halves into the env, plus the env's own reference; x86-64 copied the
      obj word only (the closure dispatched through a nil itab), arm64
      refused the form }
    procedure TestCodegen_CapturedIntfParam_CopiesBothHalves;
    { F := MakeFn() over a live closure: the call fills a scratch, the pair
      moves in and the old Env is released after the store; x86-64 zeroed
      the target first, leaking the old Env (and handing F := Wrap(F) a nil
      F) }
    procedure TestCodegen_ClosureReassignFromCall_ReleasesOldEnv;
    { F() for an env-hoisted F (assigned inside a closure) calls through
      the capture pointer, not the declaring frame's idle slot }
    procedure TestCodegen_CallThroughEnvHoistedClosure_UsesCapture;
    procedure TestCodegen_ExprCallStmt_CallsThroughElement;

    { End-to-end }
    { Phase 9a — terse '->' lambdas (desugared to TAnonMethodExpr). }
    { Phase 9b — two-phase deferred inference: lambdas in ARGUMENT position. }
    { ... and through a procedural-typed VARIABLE or FIELD (implicit-Self and
      qualified), whose single signature types the lambda. }
    procedure TestSemantic_Arrow_ArgPosition_ProcTypeCalls_Inferred;
    procedure TestCodegen_CapturedWeakLocal_ClosureBodyRegistersSlot;
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

procedure TAnonMethodTests.TestSemantic_NestedLiteral_NoCaptures_Accepted;
const
  Src =
    '''
    program P;
    type
      TKFn = reference to function(A: Integer): Integer;
      TCFn = reference to function(): TKFn;
    function GetC(): TCFn;
    begin
      Result := function(): TKFn
        begin
          Result := function(A: Integer): Integer begin Result := A + 1000; end;
        end;
    end;
    begin
      WriteLn(GetC()()(5))
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  Prog.Free();
end;

procedure TAnonMethodTests.TestSemantic_NestedLiteral_CapturingOuterLiteral_Rejected;
const
  Src =
    '''
    program P;
    type
      TKFn = reference to function(A: Integer): Integer;
      TCFn = reference to function(B: Integer): TKFn;
    function GetC(): TCFn;
    begin
      Result := function(B: Integer): TKFn
        begin
          Result := function(A: Integer): Integer begin Result := A + B; end;
        end;
    end;
    begin
      WriteLn(GetC()(1)(5))
    end.
    ''';
begin
  AssertTrue('capturing the enclosing literal''s parameter is rejected',
    Pos('enclosing anonymous method', SemanticError(Src)) >= 0);
end;

procedure TAnonMethodTests.TestSemantic_StaticMethodLiteral_CapturesNoSelf;
const
  Src =
    '''
    program P;
    type
      TKFn = reference to function(A: Integer): Integer;
      TC = class
        static function MakeFn(N: Integer): TKFn;
      end;
    static function TC.MakeFn(N: Integer): TKFn;
    begin
      Result := function(A: Integer): Integer begin Result := A * N; end;
    end;
    begin
      WriteLn(TC.MakeFn(3)(7))
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
    AssertTrue('N captured', Thunk.EnvCaptured.IndexOf('N') >= 0);
    AssertTrue('no Self in a static method',
      Thunk.EnvCaptured.IndexOf('Self') < 0);
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

procedure TAnonMethodTests.TestSemantic_CallThroughCapturedClosureParam_Accepted;
const
  Src = '''
    program Prg;
    type
      TF = reference to function: Integer;
    function Wrap(G: TF): TF;
    begin
      Result := function: Integer begin Result := G() + 100 end
    end;
    begin
    end.
    ''';
var
  Prog: TProgram;
  I: Integer;
  MD: TMethodDecl;
  Found: Boolean;
begin
  Prog := AnalyseSrc(Src);
  try
    Found := False;
    for I := 0 to Prog.Block.ProcDecls.Count - 1 do
    begin
      MD := TMethodDecl(Prog.Block.ProcDecls.Items[I]);
      if SameText(MD.Name, 'Wrap') and (MD.EnvCaptured <> nil) and
         (MD.EnvCaptured.IndexOf('G') >= 0) then
        Found := True;
    end;
    AssertTrue('G is promoted into Wrap''s closure env', Found);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestCodegen_ClosureCallResultArg_PassesScratchAddress;
const
  Src = '''
    program Prg;
    type TF = reference to function: Integer;
    function Plain: TF; begin Result := function: Integer begin Result := 3 end end;
    function Use(E: TF): Integer; begin Result := E() end;
    begin
      WriteLn(Use(Plain()))
    end.
    ''';
begin
  AssertEquals('the result scratch is the argument, released at statement end', '',
    AsmMissing(Src,
      #9'movq %rax, _pendrel_0(%rip)'#10#9'movq %rax, %rdi'#10#9'callq Use',
      #9'bl _Plain'#10#9'sub x0, x29, #'));
end;

procedure TAnonMethodTests.TestCodegen_CapturedIntfParam_CopiesBothHalves;
const
  Src = '''
    program Prg;
    type
      TF = reference to function: Integer;
      IThing = interface function Get: Integer; end;
    function CapI(I: IThing): TF;
    begin
      Result := function: Integer begin Result := I.Get() end
    end;
    begin
    end.
    ''';
begin
  AssertEquals('16 bytes copied, then the env retains the obj', '',
    AsmMissing(Src,
      #9'movq $16, %rdx'#10#9'callq memcpy'#10#9'pushq %rbx'#10 +
        #9'movq -16(%rbp), %rbx'#10#9'movq (%rbx), %rdi',
      #9'bl _memcpy'#10#9'str x19, [sp, #-16]!'#10 +
        #9'ldur x19, [x29, #-16]'#10#9'ldr x0, [x19, #0]'#10#9'bl __ClassAddRef'));
end;

procedure TAnonMethodTests.TestCodegen_ClosureReassignFromCall_ReleasesOldEnv;
const
  Src = '''
    program Prg;
    type TF = reference to function: Integer;
    function Cap(K: Integer): TF; begin Result := function: Integer begin Result := K end end;
    procedure Run;
    var F: TF;
    begin
      F := Cap(1);
      F := Cap(2);
      WriteLn(F())
    end;
    begin Run() end.
    ''';
begin
  AssertEquals('the old Env is kept aside and released after the store', '',
    AsmMissing(Src,
      #9'movq %rax, 8(%rcx)'#10#9'addq $8, %rsp'#10#9'popq %rdi'#10 +
        #9'callq _ClassRelease',
      #9'bl _Cap'#10#9'sub x9, x29, #16'#10#9'ldr x0, [x9, #8]'#10#9'bl __ClassRelease'));
end;

procedure TAnonMethodTests.TestCodegen_CallThroughEnvHoistedClosure_UsesCapture;
const
  Src = '''
    program Prg;
    type
      TF = reference to function: Integer;
      TP = reference to procedure(X: Integer);
    function Cap(K: Integer): TF; begin Result := function: Integer begin Result := K end end;
    procedure Run;
    var F: TF; P: TP;
    begin
      P := procedure(X: Integer) begin F := Cap(X) end;
      P(5);
      WriteLn(F())
    end;
    begin Run() end.
    ''';
begin
  AssertEquals('F() loads the _cap_F pointer, not the frame slot', '',
    AsmMissing(Src,
      #9'movq -16(%rbp), %rbx'#10#9'leaq (%rbx), %r11',
      #9'ldur x9, [x29, #-16]'#10#9'mov x10, x9'));
end;

procedure TAnonMethodTests.TestParse_ExprCallStmt_ElementAndDeref;
const
  Src = '''
    program Prg;
    type
      TP = procedure(X: Integer);
      PP = ^TP;
    var A: array[0..1] of TP; P: PP;
    begin
      A[1](7);
      A[0]();
      P^(9)
    end.
    ''';
var
  Prog: TProgram;
  I, N: Integer;
begin
  Prog := ParseSrc(Src);
  try
    N := 0;
    for I := 0 to Prog.Block.Stmts.Count - 1 do
      if Prog.Block.Stmts.Items[I] is TExprCallStmt then
      begin
        Inc(N);
        AssertTrue('the call is an indirect call',
          TExprCallStmt(Prog.Block.Stmts.Items[I]).Call is TIndirectFuncCallExpr);
      end;
    AssertEquals('three expression-call statements', 3, N);
    AssertEquals('A[1](7) carries its argument', 1,
      TIndirectFuncCallExpr(TExprCallStmt(Prog.Block.Stmts.Items[0]).Call).Args.Count);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestParse_ExprCallStmt_CallResultCallee;
const
  Src = '''
    program Prg;
    begin
      GetFn()(7);
      GetFn()(1)(2);
      GetMaker()(3).Run(4)
    end.
    ''';
var
  Prog: TProgram;
  Ind: TIndirectFuncCallExpr;
  MC: TMethodCallStmt;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('three statements', 3, Prog.Block.Stmts.Count);
    AssertTrue('GetFn()(7) is an expression-call statement',
      Prog.Block.Stmts.Items[0] is TExprCallStmt);
    Ind := TIndirectFuncCallExpr(TExprCallStmt(Prog.Block.Stmts.Items[0]).Call);
    AssertTrue('its callee is the call GetFn()', Ind.CalleeExpr is TFuncCallExpr);
    AssertEquals('it carries its argument', 1, Ind.Args.Count);
    Ind := TIndirectFuncCallExpr(TExprCallStmt(Prog.Block.Stmts.Items[1]).Call);
    AssertTrue('GetFn()(1)(2) chains two indirect calls',
      Ind.CalleeExpr is TIndirectFuncCallExpr);
    AssertTrue('a method call ends the third chain',
      Prog.Block.Stmts.Items[2] is TMethodCallStmt);
    MC := TMethodCallStmt(Prog.Block.Stmts.Items[2]);
    AssertEquals('method name', 'Run', MC.Name);
    AssertEquals('method args', 1, MC.Args.Count);
    AssertTrue('receiver is GetMaker()(3)', MC.ObjExpr is TIndirectFuncCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TAnonMethodTests.TestParse_ExprCallStmt_BareElementWithoutParens_Rejected;
const
  Src = '''
    program Prg;
    type TP = procedure(X: Integer);
    var A: array[0..1] of TP;
    begin
      A[1]
    end.
    ''';
var
  Raised: Boolean;
begin
  Raised := False;
  try
    ParseSrc(Src).Free();
  except
    on E: EParseError do Raised := True;
  end;
  AssertTrue('calls need parentheses, as everywhere else', Raised);
end;

procedure TAnonMethodTests.TestCodegen_ExprCallStmt_CallsThroughElement;
const
  Src = '''
    program Prg;
    type TP = procedure(X: Integer);
    procedure Show(X: Integer); begin WriteLn(X) end;
    var A: array[0..1] of TP;
    begin
      A[1] := @Show;
      A[1](7)
    end.
    ''';
begin
  AssertEquals('the element value is the call target', '',
    AsmMissing(Src,
      #9'movq (%rax), %rax'#10#9'movq %rax, %rbx'#10#9'subq $16, %rsp',
      #9'ldr x0, [x0]'#10#9'stur x0, [x29, #-'));
end;

procedure TAnonMethodTests.TestCodegen_CapturedWeakLocal_ClosureBodyRegistersSlot;
const
  Src = '''
      program P;
      type
        TProc = reference to procedure;
      procedure Run();
      var [Weak] W: TObject; S: TObject; P: TProc;
      begin
        S := TObject.Create();
        P := procedure begin W := S end;
        P()
      end;
      begin
        Run()
      end.
      ''';
begin
  { the store in the closure body goes through the env slot's weak
    registration (x86-64 rejected it as not lowered; arm64 retained) }
  AssertEquals('closure body weak store', '',
    AsmMissing(Src, 'callq _WeakAssign', 'bl __WeakAssign'));
end;

initialization
  RegisterTest(TAnonMethodTests);

end.
