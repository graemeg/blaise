{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.procs;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TProcFuncTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { a nested routine capturing more variables than the integer
      registers hold: the rest of the capture pointers go on the stack,
      ahead of every other argument (both backends rejected it) }
    procedure TestCodegen_NestedCapture_SpillsPastRegisters;
    { a captured var record param is reached through its '_cap_' slot with
      ONE deref to the caller's record, a captured by-value one with none
      (arm64 had no capture arm -- NotYet -- and its read arm dereferenced a
      by-value record's first word as its address); x86-64 gives the nested
      frame a real slot holding the owner's pointer, so every var-param
      path finds it (they read a slot that frame did not have) }
    procedure TestCodegen_CapturedRecordParams_ReachTheRecord;
    { L[0] := 5 / SetLength(L, 3) on a dyn array captured from the outer
      routine: through '_cap_' (x86-64 wrote through an undefined global of
      that name) }
    procedure TestCodegen_CapturedDynArray_ElementAndSetLength;
    { a var interface parameter's slot holds the address of the caller's
      pair: passing it on reads the pair through it (x86-64 read the slot
      as an inline pair -- a crash); a captured one goes through _cap_ and
      that address (arm64: "load of variable 'V_itab'") }
    procedure TestCodegen_VarAndCapturedInterface_PairThroughPointer;
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_StandaloneProc_InProcDecls;
    procedure TestParse_StandaloneProc_Name;
    procedure TestParse_StandaloneProc_Params;
    procedure TestParse_StandaloneProc_ParamName;
    procedure TestParse_StandaloneProc_ParamTypeName;
    procedure TestParse_StandaloneProc_Body;
    procedure TestParse_StandaloneFunc_InProcDecls;
    procedure TestParse_StandaloneFunc_Name;
    procedure TestParse_StandaloneFunc_ReturnTypeName;
    procedure TestParse_ProcCall_IsTProcCall;
    procedure TestParse_FuncCall_Expr_IsTFuncCallExpr;
    procedure TestParse_FuncCall_Expr_Name;
    procedure TestParse_FuncCall_Expr_ArgCount;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StandaloneProc_Resolves;
    procedure TestSemantic_StandaloneFunc_Resolves;
    procedure TestSemantic_ProcCall_WrongArgCount_RaisesError;
    procedure TestSemantic_ProcCall_ArgTypeMismatch_RaisesError;
    procedure TestSemantic_FuncCall_ReturnsCorrectType;
    procedure TestSemantic_StandaloneFunc_ResultVar_Available;
    procedure TestSemantic_UnknownProc_RaisesError;
    procedure TestSemantic_Proc_CanCallOtherProc;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }

    { Regression: float-typed parameter spill must use stored/stores
      (matching the QBE 'd'/'s' parameter type), not storel — QBE
      rejects 'storel %_par_D' for a 'd %_par_D' parameter. }

    { Nested procedures }
    { Same as above but the nested routines are FUNCTIONS called as
      expressions (Helper(X) inside WriteLn), which exercises
      AnalyseFuncCallExpr rather than AnalyseProcCall.  The func-call path
      previously consulted only the global FProcIndex and errored with
      "Cannot find declaration for function 'Helper'". }
    { Two sibling METHOD bodies each declaring a same-named nested function.
      Nested-in-method decls were registered in the global overload index
      (the registration guard only excluded nested-in-standalone-proc decls),
      so they collided as "Ambiguous overload".  They must be scoped to their
      enclosing method body like nested-in-proc decls. }
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TProcFuncTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcFuncTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TProcFuncTests.AnalyseExpectError(const ASrc: string);
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
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcWithProc =
    '''
        program P;
        var N: Int32;
        procedure PrintIt(X: Int32);
        begin
          WriteLn(X)
        end;
        begin
          N := 7;
          PrintIt(N)
        end.
        ''';

  SrcWithFunc =
    '''
        program P;
        var N: Int32;
        function Add(A, B: Int32): Int32;
        var Tmp: Int32;
        begin
          Tmp := A + B;
          Result := Tmp
        end;
        begin
          N := Add(3, 4)
        end.
        ''';

  SrcTwoProcs =
    '''
        program P;
        var N: Int;
        procedure Inner(X: Int);
        begin
          WriteLn(X)
        end;
        procedure Outer(Y: Int);
        begin
          Inner(Y)
        end;
        begin
          N := 1;
          Outer(N)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser tests                                                        }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestParse_StandaloneProc_InProcDecls;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    AssertEquals('one proc decl', 1, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Name;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('proc name', 'PrintIt', MD.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Params;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('one param', 1, MD.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_ParamName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD  := TMethodDecl(Prog.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param name', 'X', Par.ParamName);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_ParamTypeName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD  := TMethodDecl(Prog.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param type', 'Int32', Par.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Body;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertNotNull('body exists', MD.Body);
    AssertEquals('body has 1 stmt', 1, MD.Body.Stmts.Count);
    AssertTrue('stmt is TProcCall', MD.Body.Stmts[0] is TProcCall);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_InProcDecls;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    AssertEquals('one proc decl', 1, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_Name;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('func name', 'Add', MD.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_ReturnTypeName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('return type', 'Int32', MD.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_ProcCall_IsTProcCall;
var
  Prog: TProgram;
  Stmt: TASTStmt;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    { second stmt in main body: PrintIt(N) }
    Stmt := TASTStmt(Prog.Block.Stmts[1]);
    AssertTrue('stmt is TProcCall', Stmt is TProcCall);
    AssertEquals('proc name', 'PrintIt', TProcCall(Stmt).Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_IsTFuncCallExpr;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    { N := Add(3, 4) }
    AssertTrue('stmt is TAssignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TFuncCallExpr', Assign.Expr is TFuncCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_Name;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('func name', 'Add', FCall.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_ArgCount;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('two args', 2, FCall.Args.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestSemantic_StandaloneProc_Resolves;
begin
  AnalyseSrc(SrcWithProc).Free();
end;

procedure TProcFuncTests.TestSemantic_StandaloneFunc_Resolves;
begin
  AnalyseSrc(SrcWithFunc).Free();
end;

procedure TProcFuncTests.TestSemantic_ProcCall_WrongArgCount_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Int;
        procedure Foo(X: Int);
        begin
          WriteLn(X)
        end;
        begin
          Foo(1, 2)
        end.
        ''');
end;

procedure TProcFuncTests.TestSemantic_ProcCall_ArgTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Int;
        procedure Foo(X: Int);
        begin
          WriteLn(X)
        end;
        begin
          Foo('not an int')
        end.
        ''');
end;

procedure TProcFuncTests.TestSemantic_FuncCall_ReturnsCorrectType;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := AnalyseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertNotNull('expr has resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type is Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TProcFuncTests.TestSemantic_StandaloneFunc_ResultVar_Available;
begin
  { Result := A + B inside the function body must not raise an error }
  AnalyseSrc(SrcWithFunc).Free();
end;

procedure TProcFuncTests.TestSemantic_UnknownProc_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        begin
          NoSuchProc(1)
        end.
        ''');
end;

procedure TProcFuncTests.TestSemantic_Proc_CanCallOtherProc;
begin
  AnalyseSrc(SrcTwoProcs).Free();
end;

{ ------------------------------------------------------------------ }
{ Code generation tests                                               }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestCodegen_NestedCapture_SpillsPastRegisters;
const
  Src = '''
    program P;
    procedure Outer;
    var A, B, C, D, E, F, G, H, I, J: Int;
      function Inner(K: Int): Int;
      begin Result := A + B + C + D + E + F + G + H + I + J + K end;
    begin
      A := 1; J := 10;
      WriteLn(Inner(1000))
    end;
    begin
      Outer()
    end.
    ''';
begin
  { the callee reads the seventh (x86-64) / ninth (arm64) capture pointer
    from the caller's outgoing area: x86-64 straight from the incoming slot
    at 16(%rbp), arm64 into its local slot after x7 }
  AssertEquals('captures past the registers come from the stack', '',
    AsmMissing(Src, #9'movq 16(%rbp), %rcx',
      #9'stur x7, [x29, #-64]'#10#9'ldr x9, [x29, #16]'));
end;

procedure TProcFuncTests.TestCodegen_CapturedRecordParams_ReachTheRecord;
const
  Src = '''
    program P;
    type TRec = record N: Int32; end;
    procedure Outer(var R: TRec; V: TRec; I: Int32);
      procedure Inner;
      begin
        WriteLn(R.N, V.N);
      end;
    begin
      Inner();
    end;
    var G: TRec;
    begin
      Outer(G, G, 1);
    end.
    ''';
begin
  AssertEquals('captured var record: _cap_ then one deref', '',
    AsmMissing(Src,
      #9'movq -16(%rbp), %rax' + #10 + #9'movq (%rax), %rax' + #10 +
        #9'movq %rax, -32(%rbp)',
      #9'ldur x9, [x29, #-16]' + #10 + #9'ldr x9, [x9]' + #10 +
        #9'mov x0, x9' + #10 + #9'ldrsw x0, [x0]'));
  AssertEquals('captured by-value record: the _cap_ value is its address', '',
    AsmMissing(Src,
      #9'movq -8(%rbp), %rax' + #10 + #9'movq (%rax), %rax' + #10 +
        #9'movq %rax, -24(%rbp)',
      #9'ldur x9, [x29, #-8]' + #10 + #9'mov x0, x9' + #10 +
        #9'ldrsw x0, [x0]'));
end;

procedure TProcFuncTests.TestCodegen_CapturedDynArray_ElementAndSetLength;
const
  Src = '''
    program P;
    type TDyn = array of Int;
    procedure Outer;
    var L: TDyn;
      procedure Inner;
      begin
        L[0] := 5;
        SetLength(L, 3);
      end;
    begin
      Inner();
    end;
    begin
      Outer();
    end.
    ''';
begin
  AssertEquals('element store through _cap_', '',
    AsmMissing(Src,
      #9'movq -8(%rbp), %rcx' + #10 + #9'movq (%rcx), %rcx' + #10 +
        #9'addq %rcx, %rax',
      #9'ldur x0, [x29, #-8]' + #10 + #9'ldr x0, [x0]' + #10 +
        #9'ldr x1, [sp], #16'));
  AssertEquals('SetLength through _cap_', '',
    AsmMissing(Src,
      #9'movq -8(%rbp), %rdx' + #10 + #9'pushq %rdx',
      #9'ldur x0, [x29, #-8]' + #10 + #9'str x0, [sp, #-16]!' + #10 +
        #9'ldr x0, [x0]'));
end;

procedure TProcFuncTests.TestCodegen_VarAndCapturedInterface_PairThroughPointer;
const
  Src = '''
    program P;
    type IFoo = interface function Get: Int; end;
    procedure Show(const F: IFoo); begin end;
    procedure Outer(var V: IFoo);
      procedure Inner; begin Show(V) end;
    begin
      Show(V); Inner();
    end;
    var G: IFoo;
    begin
      Outer(G);
    end.
    ''';
begin
  AssertEquals('the pair is read through the pointer', '',
    AsmMissing(Src,
      #9'movq -16(%rbp), %r11' + #10 + #9'movq (%r11), %rax' + #10 +
        #9'movq 8(%r11), %rcx',
      #9'ldur x9, [x29, #-8]' + #10 + #9'ldr x9, [x9]' + #10 +
        #9'ldp x0, x1, [x9]'));
end;

initialization
  RegisterTest(TProcFuncTests);

end.
