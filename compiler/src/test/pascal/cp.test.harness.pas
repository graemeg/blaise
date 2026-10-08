{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.harness;

{ Shared in-process harness for compiler unit tests
  (introduced while moving the test suite off QBE, v0.15.0).

  Replaces the per-class copies of GenIR / GenAsm / AnalyseSrc:

    Analyse(Src)          lex, parse and run the semantic pass; returns the
                          annotated program (caller frees) or raises the
                          parse/semantic error.  For front-end assertions:
                          assert on the AST annotation, not on generated code.
    SemanticError(Src)    the semantic error message, or '' when the program
                          is accepted.
    GenAsm(Src, Target)   native assembly for a target name such as
                          'linux-x86_64' or 'macos-arm64'.  Generating text
                          needs no toolchain, so assertions for every ISA run
                          on every host.  Code-generation assertions whose
                          lowering decision is ISA-independent check BOTH
                          TargetX86_64 and TargetArm64.
    AsmMissing(Src, X86, Arm64)
                          '' when each target's assembly contains its
                          pattern; otherwise what is missing where.

  The analyser outlives code generation and the backend is given the
  program's symbol table, as in the compiler driver: the arm64 backend's
  global-symbol lookups walk scope state the analyser's destructor tears
  down. }

interface

uses
  SysUtils, uLexer, uParser, uAST, uSemantic,
  blaise.codegen.native, blaise.codegen.target;

const
  TargetX86_64 = 'linux-x86_64';
  TargetArm64 = 'macos-arm64';

function Analyse(const ASrc: string): TProgram;
function SemanticError(const ASrc: string): string;
function GenAsm(const ASrc, ATarget: string): string;
{ As GenAsm, with OPDF debug-fact collection on (per-statement line labels). }
function GenAsmDebug(const ASrc, ATarget: string): string;
{ AUnitSrc is analysed for export and emitted ahead of the program. }
function GenAsmWithUnit(const AUnitSrc, ASrc, ATarget: string): string;
{ The object a unit compiled on its own produces (separate compilation):
  its routines, globals and init / fini, with no program. }
function GenUnitAsm(const AUnitSrc, ATarget: string): string;
{ The usual shape of a code-generation assertion: the lowering decision is
  the same on both ISAs, only the spelling differs.  Returns '' when the
  x86-64 assembly contains AX86 and the arm64 assembly contains AArm64,
  otherwise names each target whose pattern is missing.  Use as
    AssertEquals('what is pinned', '', AsmMissing(Src, 'jl ', 'cset x0, lt')); }
function AsmMissing(const ASrc, AX86, AArm64: string): string;

implementation

function ParseProgram(const ASrc: string): TProgram;
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

function ParseUnitSrc(const ASrc: string): TUnit;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
end;

function TargetByName(const AName: string): TTargetDesc;
begin
  if not ParseTargetName(AName, Result) then
    raise Exception.Create('cp.test.harness: unknown target ' + AName);
end;

function Analyse(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseProgram(ASrc);
  A := TSemanticAnalyser.Create();
  try
    try
      A.Analyse(Result);
    except
      Result.Free();
      raise;
    end;
  finally
    A.Free();
  end;
end;

function SemanticError(const ASrc: string): string;
var
  Prog: TProgram;
begin
  Result := '';
  try
    Prog := Analyse(ASrc);
    Prog.Free();
  except
    on E: ESemanticError do
      Result := E.Message;
  end;
end;

{ AUnitSrc = '' generates the program alone. }
function GenerateAsm(const AUnitSrc, ASrc, ATarget: string;
  AOpdf: Boolean): string;
var
  U: TUnit;
  Prog: TProgram;
  A: TSemanticAnalyser;
  CG: TCodeGenNative;
begin
  U := nil;
  if AUnitSrc <> '' then
    U := ParseUnitSrc(AUnitSrc);
  try
    Prog := ParseProgram(ASrc);
    try
      A := TSemanticAnalyser.Create();
      try
        if U <> nil then
          A.AnalyseUnitForExport(U);
        A.Analyse(Prog);
        CG := TCodeGenNative.Create();
        try
          CG.SetTarget(TargetByName(ATarget));
          CG.SetSymbolTable(Prog.SymbolTable);
          if AOpdf then
            CG.SetOpdfMode(True);
          if U <> nil then
          begin
            CG.AppendUnit(U);
            CG.AppendProgram(Prog);
          end
          else
            CG.Generate(Prog);
          Result := CG.GetOutput();
        finally
          CG.Free();
        end;
      finally
        A.Free();
      end;
    finally
      Prog.Free();
    end;
  finally
    if U <> nil then
      U.Free();
  end;
end;

function GenAsm(const ASrc, ATarget: string): string;
begin
  Result := GenerateAsm('', ASrc, ATarget, False);
end;

function GenAsmDebug(const ASrc, ATarget: string): string;
begin
  Result := GenerateAsm('', ASrc, ATarget, True);
end;

function GenAsmWithUnit(const AUnitSrc, ASrc, ATarget: string): string;
begin
  Result := GenerateAsm(AUnitSrc, ASrc, ATarget, False);
end;

function GenUnitAsm(const AUnitSrc, ATarget: string): string;
var
  U: TUnit;
  A: TSemanticAnalyser;
  CG: TCodeGenNative;
begin
  U := ParseUnitSrc(AUnitSrc);
  try
    A := TSemanticAnalyser.Create();
    try
      A.AnalyseUnit(U);
      CG := TCodeGenNative.Create();
      try
        CG.SetTarget(TargetByName(ATarget));
        CG.SetSymbolTable(U.SymbolTable);
        CG.GenerateUnit(U);
        Result := CG.GetOutput();
      finally
        CG.Free();
      end;
    finally
      A.Free();
    end;
  finally
    U.Free();
  end;
end;

function AsmMissing(const ASrc, AX86, AArm64: string): string;
begin
  Result := '';
  if Pos(AX86, GenAsm(ASrc, TargetX86_64)) < 0 then
    Result := TargetX86_64 + ' lacks [' + AX86 + ']';
  if Pos(AArm64, GenAsm(ASrc, TargetArm64)) < 0 then
  begin
    if Result <> '' then
      Result := Result + '; ';
    Result := Result + TargetArm64 + ' lacks [' + AArm64 + ']';
  end;
end;

end.
