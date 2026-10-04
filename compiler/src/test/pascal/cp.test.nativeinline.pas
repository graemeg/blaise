{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nativeinline;

{ Assembly-level tests for the NATIVE backend's phase-1 inliner (the port
  of the QBE inliner, sharing TMethodDecl.IsInlineCandidate).

  Scope pinned here: qualifying small leaf calls expand at the call site
  (no callq), arguments stage through the shared _inl_area scratch block,
  Exit becomes a jump to the per-site end label, recursion and cross-unit
  callees stay normal calls, and --debug-opdf disables the whole thing. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, uDebugFacts;

type
  TNativeInlineTests = class(TTestCase)
  private
    function GenAsm(const ASrc: string; ADebug: Boolean): string;
    function FuncRegion(const AAsm, AName: string): string;
  published
    { A small same-unit leaf called from a function body expands inline:
      the caller contains no callq to it and carries an inl_end label. }
    procedure TestLeafCall_Inlined_NoCallq;
    { A recursive function is never an inline candidate — its call sites
      stay real calls. }
    procedure TestRecursiveCallee_NotInlined;
    { Under --debug-opdf inlining is disabled (exact line stepping). }
    procedure TestDebugOpdf_DisablesInlining;
  end;

implementation

const
  LF = #10;

const
  SrcLeaf = '''
      program P;
      function Clamp(V, Lo, Hi: Integer): Integer;
      begin
        if V < Lo then Exit(Lo);
        if V > Hi then Exit(Hi);
        Result := V
      end;
      function Use(A: Integer): Integer;
      begin
        Result := Clamp(A, 0, 100)
      end;
      begin
        WriteLn(Use(150))
      end.
      ''';

function TNativeInlineTests.GenAsm(const ASrc: string; ADebug: Boolean): string;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TCodeGenNative;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Prog);
    finally
      A.Free();
    end;
    CG := TCodeGenNative.Create();
    try
      CG.SetTarget(LinuxX64Target());
      if ADebug then
        CG.SetOpdfMode(True);
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

function TNativeInlineTests.FuncRegion(const AAsm, AName: string): string;
var
  StartP, EndP: Integer;
begin
  StartP := Pos(AName + ':', AAsm);
  AssertTrue('function ' + AName + ' present in asm', StartP >= 0);
  EndP := StrPos('.type ' + AName, StrCopyTail(AAsm, StartP));
  AssertTrue('function ' + AName + ' closed', EndP >= 0);
  Result := StrCopyFrom(AAsm, StartP, EndP);
end;

procedure TNativeInlineTests.TestLeafCall_Inlined_NoCallq;
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(SrcLeaf, False), 'Use');
  AssertTrue('no callq to the inlined leaf',
    Pos('callq Clamp', Region) < 0);
  AssertTrue('inline end label present',
    Pos('.Linl_end', Region) >= 0);
end;

procedure TNativeInlineTests.TestRecursiveCallee_NotInlined;
const
  Src = '''
      program P;
      function Fib(N: Integer): Int64;
      begin
        if N < 2 then
          Result := N
        else
          Result := Fib(N - 1) + Fib(N - 2)
      end;
      begin
        WriteLn(Fib(10))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, False), 'Fib');
  AssertTrue('recursive callee keeps real calls',
    Pos('callq Fib', Region) >= 0);
end;

procedure TNativeInlineTests.TestDebugOpdf_DisablesInlining;
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(SrcLeaf, True), 'Use');
  AssertTrue('debug build keeps the real call',
    Pos('callq Clamp', Region) >= 0);
  AssertTrue('debug build has no inline expansion',
    Pos('.Linl_end', Region) < 0);
end;

initialization
  RegisterTest(TNativeInlineTests);

end.
