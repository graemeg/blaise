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
  uLexer, uParser, uAST, uSemantic, blaise.codegen.qbe,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets;

type
  TThreadVarTests = class(TTestCase)
  private
    function GenerateIR(const ASrc: string): string;
    function GenerateNativeAsm(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    procedure TestParser_ThreadVarBlockParsed;
    procedure TestParser_ThreadVarIsGlobal;
    procedure TestSemantic_ThreadVarMustBeGlobalScope;
    procedure TestCodegen_ThreadVarInteger_EmitsThreadData;
    procedure TestCodegen_ThreadVarString_EmitsThreadData;
    procedure TestCodegen_ThreadVarPointer_EmitsThreadData;
    procedure TestCodegen_RegularVar_NoThreadPrefix;
    procedure TestCodegen_MixedVarAndThreadVar;
    procedure TestCodegen_ThreadVarStaticArray_EmitsCorrectSize;
    { @ThreadVar must yield the PER-THREAD address (%fs:0 + @tpoff), not
      the static leaq Name(%rip).  A static address makes every thread's
      @TV identical — which silently broke the allocator's MyTid identity
      (runtime.mem) and any code holding a pointer into a threadvar. }
    procedure TestCodegenNative_AddrOfThreadVar_UsesTls;
    procedure TestCodegenNative_AddrOfPlainGlobal_StaysRipRelative;
  end;

implementation

function TThreadVarTests.GenerateIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

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

function TThreadVarTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) >= 0;
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
    Self.GenerateIR(
      'program P;' + #10 +
      'procedure Foo;' + #10 +
      'threadvar' + #10 +
      '  Z: Integer;' + #10 +
      'begin end;' + #10 +
      'begin' + #10 +
      'end.');
    Fail('Expected EParseError for threadvar inside procedure');
  except
    on E: EParseError do ;
  end;
end;

procedure TThreadVarTests.TestCodegen_ThreadVarInteger_EmitsThreadData;
var
  IR: string;
begin
  IR := Self.GenerateIR(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  Counter: Integer;' + #10 +
    'begin' + #10 +
    '  Counter := 42' + #10 +
    'end.');
  AssertTrue(Self.IRContains(IR, 'export thread data $Counter'));
end;

procedure TThreadVarTests.TestCodegen_ThreadVarString_EmitsThreadData;
var
  IR: string;
begin
  IR := Self.GenerateIR(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  Name: String;' + #10 +
    'begin' + #10 +
    '  Name := ''hello''' + #10 +
    'end.');
  AssertTrue(Self.IRContains(IR, 'export thread data $Name'));
end;

procedure TThreadVarTests.TestCodegen_ThreadVarPointer_EmitsThreadData;
var
  IR: string;
begin
  IR := Self.GenerateIR(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  Ptr: Pointer;' + #10 +
    'begin' + #10 +
    '  Ptr := nil' + #10 +
    'end.');
  AssertTrue(Self.IRContains(IR, 'export thread data $Ptr'));
end;

procedure TThreadVarTests.TestCodegen_RegularVar_NoThreadPrefix;
var
  IR: string;
begin
  IR := Self.GenerateIR(
    'program P;' + #10 +
    'var' + #10 +
    '  X: Integer;' + #10 +
    'begin' + #10 +
    '  X := 10' + #10 +
    'end.');
  AssertTrue(Self.IRContains(IR, 'export data $X'));
  AssertFalse(Self.IRContains(IR, 'export thread data $X'));
end;

procedure TThreadVarTests.TestCodegen_MixedVarAndThreadVar;
var
  IR: string;
begin
  IR := Self.GenerateIR(
    'program P;' + #10 +
    'var' + #10 +
    '  A: Integer;' + #10 +
    'threadvar' + #10 +
    '  B: Integer;' + #10 +
    'begin' + #10 +
    '  A := 1;' + #10 +
    '  B := 2' + #10 +
    'end.');
  AssertTrue(Self.IRContains(IR, 'export data $A'));
  AssertFalse(Self.IRContains(IR, 'export thread data $A'));
  AssertTrue(Self.IRContains(IR, 'export thread data $B'));
end;

procedure TThreadVarTests.TestCodegen_ThreadVarStaticArray_EmitsCorrectSize;
var
  IR: string;
begin
  IR := Self.GenerateIR(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  Buckets: array[0..7] of Pointer;' + #10 +
    'begin' + #10 +
    '  Buckets[0] := nil' + #10 +
    'end.');
  AssertTrue(Self.IRContains(IR, 'export thread data $Buckets'));
  AssertTrue(Self.IRContains(IR, 'z 64'));
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
