{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.threadvar;

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, cp.test.harness;

type
  TThreadVarTests = class(TTestCase)
  private
    function GenerateNativeAsm(const ASrc: string): string;
  published
    procedure TestParser_ThreadVarBlockParsed;
    procedure TestParser_ThreadVarIsGlobal;
    procedure TestSemantic_ThreadVarMustBeGlobalScope;
    procedure TestCodegen_ThreadVars_InThreadLocalStorage;
    { @ThreadVar must yield the PER-THREAD address (%fs:0 + @tpoff), not
      the static leaq Name(%rip).  A static address makes every thread's
      @TV identical — which silently broke the allocator's MyTid identity
      (runtime.mem) and any code holding a pointer into a threadvar. }
    procedure TestCodegenNative_AddrOfThreadVar_UsesTls;
    procedure TestCodegenNative_AddrOfPlainGlobal_StaysRipRelative;
  end;

implementation

function TThreadVarTests.GenerateNativeAsm(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenNative;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Pr := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Pr);
    finally
      A.Free();
    end;
    CG := TCodeGenNative.Create();
    try
      CG.SetTarget(LinuxX64Target());
      CG.Generate(Pr);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Pr.Free();
  end;
end;

procedure TThreadVarTests.TestParser_ThreadVarBlockParsed;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  D:  TVarDecl;
begin
  L  := TLexer.Create(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  X: Integer;' + #10 +
    'begin' + #10 +
    'end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  try
    AssertEquals(1, Pr.Block.Decls.Count);
    D := TVarDecl(Pr.Block.Decls.Items[0]);
    AssertEquals('X', D.Names.Strings[0]);
    AssertTrue(D.IsThreadVar);
  finally
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TThreadVarTests.TestParser_ThreadVarIsGlobal;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  D:  TVarDecl;
begin
  L  := TLexer.Create(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  Y: Int64;' + #10 +
    'begin' + #10 +
    'end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    D := TVarDecl(Pr.Block.Decls.Items[0]);
    AssertTrue(D.IsGlobal);
    AssertTrue(D.IsThreadVar);
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TThreadVarTests.TestSemantic_ThreadVarMustBeGlobalScope;
begin
  try
    Analyse(
      'program P;' + #10 +
      'procedure Foo;' + #10 +
      'threadvar' + #10 +
      '  Z: Integer;' + #10 +
      'begin end;' + #10 +
      'begin' + #10 +
      'end.').Free();
    Fail('Expected EParseError for threadvar inside procedure');
  except
    on E: EParseError do ;
  end;
end;

procedure TThreadVarTests.TestCodegen_ThreadVars_InThreadLocalStorage;
const
  Src = '''
    program P;
    var
      A: Integer;
    threadvar
      Counter: Integer;
      Name: String;
      Ptr: Pointer;
      Buckets: array[0..7] of Pointer;
    begin
      A := 1; Counter := 42; Name := 'hello'; Ptr := nil; Buckets[0] := nil
    end.
    ''';
var
  X86, A64: string;
  Tbss: Integer;
begin
  { threadvars live in thread-local storage at their full size; an
    ordinary global stays in ordinary data.  Per-thread isolation itself is
    run by TE2EThreadingTests; this pins where the storage is placed. }
  X86 := GenAsm(Src, TargetX86_64);
  Tbss := Pos('.section .tbss', X86);
  AssertTrue('x86-64: a .tbss section', Tbss >= 0);
  AssertTrue('x86-64: Counter in .tbss', Pos(#10 + 'Counter:', X86) > Tbss);
  AssertTrue('x86-64: Name in .tbss', Pos(#10 + 'Name:', X86) > Tbss);
  AssertTrue('x86-64: Ptr in .tbss', Pos(#10 + 'Ptr:', X86) > Tbss);
  AssertTrue('x86-64: Buckets is 64 bytes',
    Pos('Buckets:' + #10 + #9 + '.skip 64', X86) > Tbss);
  AssertTrue('x86-64: A is ordinary data', (Pos(#10 + 'A:', X86) >= 0) and
    (Pos(#10 + 'A:', X86) < Tbss));
  AssertTrue('x86-64: thread-pointer access', Pos('Counter@tpoff', X86) >= 0);
  A64 := GenAsm(Src, TargetArm64);
  AssertTrue('arm64: thread_bss section', Pos('__thread_bss', A64) >= 0);
  AssertTrue('arm64: Counter storage', Pos(#10 + '_ts_Counter:', A64) >= 0);
  AssertTrue('arm64: Counter TLV descriptor', Pos(#10 + '_tv_Counter:', A64) >= 0);
  AssertTrue('arm64: Name TLV descriptor', Pos(#10 + '_tv_Name:', A64) >= 0);
  AssertTrue('arm64: Buckets is 64 bytes',
    Pos('_ts_Buckets:' + #10 + #9 + '.zero 64', A64) >= 0);
  AssertTrue('arm64: A is ordinary data', Pos('_tv_A', A64) < 0);
end;

procedure TThreadVarTests.TestCodegenNative_AddrOfThreadVar_UsesTls;
var
  Asm_: string;
begin
  Asm_ := Self.GenerateNativeAsm(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  TV: Int64;' + #10 +
    'var' + #10 +
    '  Q: Pointer;' + #10 +
    'begin' + #10 +
    '  Q := @TV' + #10 +
    'end.');
  AssertTrue('@threadvar computes the thread pointer base (%fs:0)',
    Pos('movq %fs:0', Asm_) >= 0);
  AssertTrue('@threadvar offsets via TV@tpoff',
    Pos('TV@tpoff(', Asm_) >= 0);
  AssertTrue('@threadvar must NOT take the static address',
    Pos('leaq TV(%rip)', Asm_) < 0);
end;

procedure TThreadVarTests.TestCodegenNative_AddrOfPlainGlobal_StaysRipRelative;
var
  Asm_: string;
begin
  Asm_ := Self.GenerateNativeAsm(
    'program P;' + #10 +
    'var' + #10 +
    '  GV: Int64;' + #10 +
    '  Q: Pointer;' + #10 +
    'begin' + #10 +
    '  Q := @GV' + #10 +
    'end.');
  AssertTrue('@global stays PC-relative',
    Pos('leaq GV(%rip)', Asm_) >= 0);
  AssertTrue('@global takes no TLS path',
    Pos('GV@tpoff', Asm_) < 0);
end;

initialization
  RegisterTest(TThreadVarTests);

end.
