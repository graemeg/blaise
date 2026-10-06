{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.pchar;

{ Tests for PChar type: PChar(str) cast and string(pchar) cast.
  Covers semantic analysis and QBE IR code generation. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe, cp.test.harness;

type
  TPCharTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_PChar_CastFromString;
    procedure TestSemantic_PChar_VarKind;
    procedure TestSemantic_String_CastFromPChar;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_PChar_AllocEmitted;
    procedure TestCodegen_PCharSubscript_StoresByteDirectly;
  end;

implementation

function TPCharTests.AnalyseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser; A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TPCharTests.GenIR(const ASrc: string): string;
var P: TProgram; CG: TCodeGenQBE;
begin
  P := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(P);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    P.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                              }
{ ------------------------------------------------------------------ }

const
  SrcPCharCast =
    '''
        program PC;
        procedure Foo(s: string);
        var p: PChar;
        begin
          p := PChar(s)
        end;
        begin end.
        ''';

  SrcStringCast =
    '''
        program PC;
        function Bar(p: PChar): string;
        begin
          Result := string(p)
        end;
        begin end.
        ''';

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TPCharTests.TestSemantic_PChar_CastFromString;
var P: TProgram; MDecl: TMethodDecl; Assign: TAssignment;
begin
  P := AnalyseSrc(SrcPCharCast);
  try
    MDecl  := TMethodDecl(P.Block.ProcDecls[0]);
    Assign := TAssignment(MDecl.Body.Stmts[0]);
    AssertNotNull('assign expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('PChar(s) resolves to tyPChar',
      Ord(tyPChar), Ord(Assign.Expr.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TPCharTests.TestSemantic_PChar_VarKind;
var P: TProgram; MDecl: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcPCharCast);
  try
    MDecl := TMethodDecl(P.Block.ProcDecls[0]);
    Decl  := TVarDecl(MDecl.Body.Decls[0]);
    AssertNotNull('ResolvedType set', Decl.ResolvedType);
    AssertEquals('var p: PChar resolves to tyPChar',
      Ord(tyPChar), Ord(Decl.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TPCharTests.TestSemantic_String_CastFromPChar;
var P: TProgram; MDecl: TMethodDecl; Assign: TAssignment;
begin
  P := AnalyseSrc(SrcStringCast);
  try
    MDecl  := TMethodDecl(P.Block.ProcDecls[0]);
    Assign := TAssignment(MDecl.Body.Stmts[0]);
    AssertNotNull('assign expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('string(p) resolves to tyString',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                       }
{ ------------------------------------------------------------------ }

{ QBE-only (delete with the backend, Phase 2): pins QBE syntax with no
  behaviour behind it. }
procedure TPCharTests.TestCodegen_PChar_AllocEmitted;
var IR: string;
begin
  IR := GenIR(SrcPCharCast);
  { var p: PChar allocates an 8-byte pointer slot }
  AssertTrue('alloc8 1 for PChar var', Pos('alloc8 1', IR) > 0);
end;

procedure TPCharTests.TestCodegen_PCharSubscript_StoresByteDirectly;
const
  { p[i] := Chr(N) and p[i] := #0 store one byte straight from an immediate:
    no call to the _Chr RTL helper, and no string literal built for the char.
    Invisible when the program runs (the byte is right either way), so this
    is an assembly check, on both ISAs. }
  Src = '''
    program PCC;
    var p: PChar;
    begin
      p := GetMem(4);
      p[0] := Chr(65);
      p[1] := #0;
      FreeMem(p)
    end.
    ''';
var
  AsmT: string;
begin
  AssertEquals('byte store', '', AsmMissing(Src, 'movb', 'strb'));
  AsmT := GenAsm(Src, TargetX86_64);
  AssertTrue('x86-64: no _Chr call', Pos('_Chr', AsmT) < 0);
  AssertTrue('x86-64: no string literal', Pos('__s0', AsmT) < 0);
  AsmT := GenAsm(Src, TargetArm64);
  AssertTrue('arm64: no _Chr call', Pos('_Chr', AsmT) < 0);
  AssertTrue('arm64: no string literal', Pos('__s0', AsmT) < 0);
end;

initialization
  RegisterTest(TPCharTests);

end.
