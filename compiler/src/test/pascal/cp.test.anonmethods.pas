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
    * Codegen (QBE): lifted '__closure_<n>' thunk with the hidden env
      first param; 16-byte fat-value materialisation; closure-dispatch
      call shape.
    * E2E: capture-free literals assigned + called; function literals;
      '@Routine' adapter coercion; nil closure assignment. }

interface

uses
  Classes, SysUtils, Process, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe,
  cp.test.rtllink, cp.test.attributes;

type
  TAnonMethodTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function CompileAndRun(const ASrc: string): string;
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
    procedure TestCodegen_NestedRoutineInMethod_SelfCapturedIR;
    procedure TestCodegen_NestedSretFuncInMethod_SelfCapturedIR;
    procedure TestSemantic_Phase9a_ArrowWithoutTarget_Rejected;
    procedure TestSemantic_Phase6_GenericRefAlias_InstantiatesAtInteger;
    procedure TestSemantic_Phase6_GenericRefAlias_InstantiatesAtString;

    { Codegen }
    procedure TestCodegen_ThunkEmitted;
    procedure TestCodegen_LiteralMaterialisesFatValue;
    procedure TestCodegen_Phase2_EnvAllocAndCleanupEmitted;
    procedure TestCodegen_Phase2_CapturedAccessRedirected;
    procedure TestCodegen_Phase2_ClosureCreationAddRefsEnv;
    procedure TestCodegen_Phase2_FrameExitReleasesEnv;
    procedure TestCodegen_Phase6_GenericBodyClosure_ThunksPerInstance;

    { End-to-end }
    procedure TestE2E_CaptureFreeLiteral_AssignAndCall;
    procedure TestE2E_FunctionLiteral_ReturnsValue;
    procedure TestE2E_AdapterFromPlainRoutine;
    procedure TestE2E_NilClosure_Assignable;
    { Phase 9a — terse '->' lambdas (desugared to TAnonMethodExpr). }
    procedure TestE2E_Arrow_ExprBody_MultiParam_Captures;
    procedure TestE2E_Arrow_SingleIdent_ProcedureTarget;
    procedure TestE2E_Arrow_BlockBody;
    procedure TestE2E_Arrow_MinusGreaterStaysDistinct;
    { Phase 9b — two-phase deferred inference: lambdas in ARGUMENT position. }
    procedure TestE2E_Arrow_ArgPosition_Standalone;
    procedure TestE2E_Arrow_ArgPosition_MethodWithCapture;
    procedure TestE2E_Arrow_ArgPosition_OverloadByShape;
    { ... and through a procedural-typed VARIABLE or FIELD (implicit-Self and
      qualified), whose single signature types the lambda. }
    procedure TestSemantic_Arrow_ArgPosition_ProcTypeCalls_Inferred;
    procedure TestE2E_Arrow_ArgPosition_ProcTypeCalls;
    { Phase 10 gate — a generic METHOD with its own type param on a generic
      class monomorphises and runs (TBox<T>.MapTo<R>, two different R's). }
    procedure TestE2E_GenericMethodOnGenericClass_Gate;
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

function TAnonMethodTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

function TAnonMethodTests.CompileAndRun(const ASrc: string): string;
var
  IR:                       string;
  Root:                     string;
  QBE, Scratch:             string;
  IRFile, AsmFile, BinFile: string;
  Lst:                      TStringList;
  Proc:                     TProcess;
  Chunk:                    string;
begin
  Result := '';
  Root   := ProjectRootAttr();
  QBE    := Root + 'vendor/qbe/qbe';
  if not RTLLinkToolchainAvailable(Root) then
  begin
    Result := '<toolchain-missing>';
    Exit;
  end;
  Scratch := Root + 'compiler/target/test-anonmethods';
  ForceDirectories(Scratch);
  IRFile  := IncludeTrailingPathDelimiter(Scratch) + 'case.ssa';
  AsmFile := IncludeTrailingPathDelimiter(Scratch) + 'case.s';
  BinFile := IncludeTrailingPathDelimiter(Scratch) + 'case.bin';

  IR := GenIR(ASrc);
  Lst := TStringList.Create();
  try
    Lst.Text := IR;
    Lst.SaveToFile(IRFile);
  finally
    Lst.Free();
  end;

  if RunCmdAttr(QBE, ['-o', AsmFile, IRFile]) <> 0 then
  begin
    Result := '<qbe-failed>';
    Exit;
  end;
  if LinkProgramWithRTL(Root, AsmFile, BinFile) <> 0 then
  begin
    Result := '<link-failed>';
    Exit;
  end;

  Proc := TProcess.Create(nil);
  try
    Proc.Executable := BinFile;
    Proc.Execute();
    Result := '';
    repeat
      Chunk := Proc.ReadOutput();
      Result := Result + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
  finally
    Proc.Free();
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
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TAnonMethodTests.TestCodegen_ThunkEmitted;
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
      end;
      V(7)
    end.
    ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('lifted thunk $__closure_1 emitted',
    Pos('$__closure_1(', IR) > 0);
end;

procedure TAnonMethodTests.TestCodegen_LiteralMaterialisesFatValue;
const
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    var
      V: TProc;
    begin
      V := procedure
      begin
      end
    end.
    ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('16-byte fat value allocated', Pos('alloc8 16', IR) > 0);
  AssertTrue('thunk address stored into the Code half',
    Pos('storel $__closure_1', IR) > 0);
end;

const
  { Shared source for the Phase-2 codegen tests: 'Run' has one captured
    local (Outer) promoted into an env record, one non-captured local, and
    a closure that both reads and writes the capture. }
  Phase2CodegenSrc =
    '''
    program P;
    type
      TProc = reference to procedure;
    procedure Run;
    var
      Outer: Integer;
      Plain: Integer;
      V: TProc;
    begin
      Outer := 1;
      Plain := 2;
      V := procedure
      begin
        Outer := Outer + 1;
        WriteLn(Outer)
      end;
      V();
      WriteLn(Outer + Plain)
    end;
    begin
      Run()
    end.
    ''';

procedure TAnonMethodTests.TestCodegen_Phase2_EnvAllocAndCleanupEmitted;
var IR: string;
begin
  IR := GenIR(Phase2CodegenSrc);
  AssertTrue('env record heap-allocated via _ClassAlloc',
    Pos('call $_ClassAlloc(', IR) > 0);
  AssertTrue('env field-cleanup function defined',
    Pos('__env_', IR) > 0);
end;

procedure TAnonMethodTests.TestCodegen_Phase2_CapturedAccessRedirected;
var IR: string;
begin
  IR := GenIR(Phase2CodegenSrc);
  AssertTrue('captured local redirected through the env pointer',
    Pos('%_env_Outer', IR) > 0);
  AssertTrue('non-captured local still a plain frame slot',
    Pos('%_var_Plain', IR) > 0);
end;

procedure TAnonMethodTests.TestCodegen_Phase2_ClosureCreationAddRefsEnv;
var IR: string;
begin
  IR := GenIR(Phase2CodegenSrc);
  AssertTrue('closure creation retains the env',
    Pos('call $_ClassAddRef(', IR) > 0);
end;

procedure TAnonMethodTests.TestCodegen_Phase2_FrameExitReleasesEnv;
var IR: string;
begin
  IR := GenIR(Phase2CodegenSrc);
  AssertTrue('enclosing frame releases its env reference on exit',
    Pos('call $_ClassRelease(', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ End-to-end tests                                                     }
{ ------------------------------------------------------------------ }

procedure TAnonMethodTests.TestE2E_CaptureFreeLiteral_AssignAndCall;
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
        WriteLn(AValue * 2)
      end;
      V(21)
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '42' + #10, Output);
end;

procedure TAnonMethodTests.TestE2E_FunctionLiteral_ReturnsValue;
const
  Src =
    '''
    program P;
    type
      TAdd = reference to function(const A, B: Integer): Integer;
    var
      F: TAdd;
    begin
      F := function(const A, B: Integer): Integer
      begin
        Result := A + B
      end;
      WriteLn(F(19, 23))
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '42' + #10, Output);
end;

procedure TAnonMethodTests.TestE2E_AdapterFromPlainRoutine;
const
  Src =
    '''
    program P;
    type
      TIntProc = reference to procedure(AValue: Integer);
    procedure Show(AValue: Integer);
    begin
      WriteLn(AValue + 1)
    end;
    var
      V: TIntProc;
    begin
      V := @Show;
      V(41)
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '42' + #10, Output);
end;

procedure TAnonMethodTests.TestE2E_NilClosure_Assignable;
const
  Src =
    '''
    program P;
    type
      TProc = reference to procedure;
    var
      V: TProc;
    begin
      V := procedure
      begin
        WriteLn('lived')
      end;
      V();
      V := nil;
      WriteLn('done')
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', 'lived' + #10 + 'done' + #10, Output);
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

procedure TAnonMethodTests.TestCodegen_NestedRoutineInMethod_SelfCapturedIR;
const
  Src =
    '''
    program P;
    type
      TC = class
        FVal: Integer;
        procedure M();
      end;
    procedure TC.M();
      procedure Inner();
      begin
        Self.FVal := 7
      end;
    begin
      Inner()
    end;
    var C: TC;
    begin
      C := TC.Create();
      C.M()
    end.
    ''';
var
  IR: string;
begin
  { BUG-008: Self is threaded into the nested routine as a hidden
    '_cap_Self' pointer param (the address of the method's Self slot); the
    call site inside the method passes %_var_Self. }
  IR := GenIR(Src);
  AssertTrue('nested func takes hidden l %_cap_Self param',
    Pos('l %_cap_Self', IR) >= 0);
  AssertTrue('call site passes the Self slot address',
    Pos('l %_var_Self', IR) >= 0)
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


procedure TAnonMethodTests.TestCodegen_NestedSretFuncInMethod_SelfCapturedIR;
const
  Src =
    '''
    program P;
    type
      TBig = record
        A: Int64;
        B: Int64;
        C: Int64;
        D: Int64;
        E: Int64;
      end;
      TC = class
        FVal: Int64;
        procedure M();
      end;
    procedure TC.M();
      function MakeBig(): TBig;
      var I: Integer;
      begin
        I := 0;
        while I < 1 do
        begin
          Result.A := Self.FVal;
          I := I + 1
        end
      end;
    var B: TBig;
    begin
      B := MakeBig();
      WriteLn(B.A)
    end;
    var C: TC;
    begin
      C := TC.Create();
      C.M()
    end.
    ''';
var
  IR: string;
begin
  { A record-returning (sret) nested function that captures Self must receive
    the hidden capture pointer at the sret call site too — the sret path has
    its own arg-assembly loop (EmitRecordCallSret), which used to omit the
    capture args entirely. }
  IR := GenIR(Src);
  AssertTrue('nested sret func takes hidden l %_cap_Self param',
    Pos('l %_cap_Self', IR) >= 0);
  AssertTrue('sret call site passes the Self slot address',
    Pos(', l %_var_Self', IR) >= 0)
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

procedure TAnonMethodTests.TestCodegen_Phase6_GenericBodyClosure_ThunksPerInstance;
const
  Src =
    '''
    program P;
    type
      TGetter<T> = reference to function(): T;
      TBox<T> = class
        FVal: T;
        function Make(): TGetter<T>;
        begin
          Result := function(): T
            begin
              Result := FVal
            end;
        end;
      end;
    var
      BI: TBox<Integer>;
      BS: TBox<string>;
      GI: TGetter<Integer>;
      GS: TGetter<string>;
    begin
      BI := TBox<Integer>.Create();
      BS := TBox<string>.Create();
      GI := BI.Make();
      GS := BS.Make();
    end.
    ''';
var
  IR: string;
begin
  { One monomorphised thunk + env per instantiation; env cleanup for the
    string instance must release the managed captured Self (both instances
    capture Self strongly), and the two instances must not share symbols. }
  IR := GenIR(Src);
  AssertTrue('Integer-instance Make body emitted',
    Pos('TBox_Integer_Make', IR) > 0);
  AssertTrue('string-instance Make body emitted',
    Pos('TBox_string_Make', IR) > 0);
  AssertTrue('closure thunk emitted for Integer instance',
    Pos('__closure', IR) > 0);
  AssertTrue('env cleanup functions emitted',
    Pos('_FieldCleanup___env_', IR) > 0)
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

procedure TAnonMethodTests.TestE2E_Arrow_ExprBody_MultiParam_Captures;
const
  Src =
    '''
    program P;
    type
      TAdd = reference to function(A, B: Integer): Integer;
    var
      F: TAdd;
      Base: Integer;
    begin
      Base := 40;
      F := (A, B) -> A + B + Base;
      WriteLn(F(1, 1))
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '42' + #10, Output)
end;

procedure TAnonMethodTests.TestE2E_Arrow_SingleIdent_ProcedureTarget;
const
  Src =
    '''
    program P;
    type
      TShow = reference to procedure(N: Integer);
    var
      P1: TShow;
    begin
      P1 := N -> WriteLn(N * 2);
      P1(21)
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '42' + #10, Output)
end;

procedure TAnonMethodTests.TestE2E_Arrow_BlockBody;
const
  Src =
    '''
    program P;
    type
      TAdd = reference to function(A, B: Integer): Integer;
    var
      F: TAdd;
    begin
      F := (A, B) -> begin
        Result := A * B
      end;
      WriteLn(F(6, 7))
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '42' + #10, Output)
end;

procedure TAnonMethodTests.TestE2E_Arrow_MinusGreaterStaysDistinct;
const
  { 'A - B' and 'A > B' around an arrow: the '->' token must not swallow a
    minus that is followed by a separate '>' comparison, and arithmetic
    minus must be unaffected. }
  Src =
    '''
    program P;
    type
      TF = reference to function(A: Integer): Integer;
    var
      F: TF;
      X: Integer;
    begin
      F := (A) -> A - 1;
      X := F(43);
      if X > 41 then
        WriteLn(X)
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '42' + #10, Output)
end;

{ ------------------------------------------------------------------ }
{ Phase 9b — deferred inference in argument position                  }
{ ------------------------------------------------------------------ }

procedure TAnonMethodTests.TestE2E_Arrow_ArgPosition_Standalone;
const
  Src =
    '''
    program P;
    type
      TSel = reference to function(N: Integer): Integer;
    function Twice(N: Integer; F: TSel): Integer;
    begin
      Result := F(F(N))
    end;
    begin
      WriteLn(Twice(10, X -> X + 6))
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '22' + #10, Output)
end;

procedure TAnonMethodTests.TestE2E_Arrow_ArgPosition_MethodWithCapture;
const
  Src =
    '''
    program P;
    type
      TPred = reference to function(N: Integer): Boolean;
      TC = class
        function CountIf(A, B, C: Integer; P: TPred): Integer;
        begin
          Result := 0;
          if P(A) then Result := Result + 1;
          if P(B) then Result := Result + 1;
          if P(C) then Result := Result + 1
        end;
      end;
    var
      C: TC;
      Limit: Integer;
    begin
      C := TC.Create();
      Limit := 10;
      WriteLn(C.CountIf(5, 11, 20, N -> N > Limit))
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', '2' + #10, Output)
end;

procedure TAnonMethodTests.TestE2E_Arrow_ArgPosition_OverloadByShape;
const
  { The lambda's SHAPE (one parameter, reference-typed formal) must steer
    overload resolution: the Integer overload wins for 7, the lambda
    overload wins for the arrow — mixing them must not regress plain args. }
  Src =
    '''
    program P;
    type
      TSel = reference to function(N: Integer): Integer;
    function Pick(N: Integer; V: Integer): string; overload;
    begin
      Result := 'int:' + IntToStr(V)
    end;
    function Pick(N: Integer; F: TSel): string; overload;
    begin
      Result := 'fn:' + IntToStr(F(N))
    end;
    begin
      WriteLn(Pick(20, 7));
      WriteLn(Pick(20, X -> X * 2 + 2))
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', 'int:7' + #10 + 'fn:42' + #10, Output)
end;

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

procedure TAnonMethodTests.TestE2E_Arrow_ArgPosition_ProcTypeCalls;
var Output: string;
begin
  Output := CompileAndRun(SrcArrowProcTypeCalls);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout',
    '5' + #10 + '10' + #10 + '11' + #10 + '6' + #10 + '5' + #10 + '107' + #10,
    Output)
end;

procedure TAnonMethodTests.TestE2E_GenericMethodOnGenericClass_Gate;
const
  Src =
    '''
    program P;
    type
      TSel<T, R> = reference to function(AVal: T): R;
      TBox<T> = class
      public
        FVal: T;
        function MapTo<R>(F: TSel<T, R>): R;
      end;
    function TBox<T>.MapTo<R>(F: TSel<T, R>): R;
    begin
      Result := F(FVal)
    end;
    var
      B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.FVal := 42;
      WriteLn(B.MapTo<string>(N -> 'v' + IntToStr(N)));
      WriteLn(B.MapTo<Integer>(N -> N + 1))
    end.
    ''';
var Output: string;
begin
  Output := CompileAndRun(Src);
  if Output = '<toolchain-missing>' then begin Ignore('toolchain unavailable'); Exit end;
  AssertEquals('stdout', 'v42' + #10 + '43' + #10, Output)
end;

initialization
  RegisterTest(TAnonMethodTests);

end.
