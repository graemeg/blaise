{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.varinit;

{ Parser and semantic tests for initialised global variables: var G: T = value.
  The initialiser is folded at compile time and emitted into the data
  section.  E2E coverage (compile -> run, both backends) lives in
  cp.test.e2e.varinit.pas. }

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable;

type
  TVarInitTests = class(TTestCase)
  private
    procedure AnalyseSrc(const ASrc: string);
    function ParseProg(const ASrc: string): TProgram;
  published
    { Parser }
    procedure TestParse_ScalarInit_AttachesInitConst;
    procedure TestParse_NoInit_InitConstNil;
    procedure TestParse_MultiName_WithInit_Rejected;

    { Semantic }
    procedure TestSemantic_TypeMismatch_StringIntoInteger_Rejected;
    procedure TestSemantic_LocalInit_Rejected;
    procedure TestSemantic_RecordInit_Rejected;
  end;

implementation

function TVarInitTests.ParseProg(const ASrc: string): TProgram;
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

{ Parse and run the semantic pass; the rejection tests expect it to raise. }
procedure TVarInitTests.AnalyseSrc(const ASrc: string);
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TVarInitTests.TestParse_ScalarInit_AttachesInitConst;
var P: TProgram; Decl: TVarDecl;
begin
  P := ParseProg('program X; var G: Integer = 42; begin end.');
  try
    Decl := TVarDecl(P.Block.Decls.Items[0]);
    AssertNotNull('InitConst attached', Decl.InitConst);
    AssertEquals('folded value 42', 42, Decl.InitConst.IntVal);
  finally P.Free(); end;
end;

procedure TVarInitTests.TestParse_NoInit_InitConstNil;
var P: TProgram; Decl: TVarDecl;
begin
  P := ParseProg('program X; var G: Integer; begin end.');
  try
    Decl := TVarDecl(P.Block.Decls.Items[0]);
    AssertNull('no initialiser', Decl.InitConst);
  finally P.Free(); end;
end;

procedure TVarInitTests.TestParse_MultiName_WithInit_Rejected;
var Raised: Boolean;
begin
  Raised := False;
  try
    ParseProg('program X; var A, B: Integer = 1; begin end.').Free();
  except
    on E: EParseError do Raised := True;
  end;
  AssertTrue('multi-name initialiser is a parse error', Raised);
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TVarInitTests.TestSemantic_TypeMismatch_StringIntoInteger_Rejected;
var Raised: Boolean;
begin
  Raised := False;
  try
    AnalyseSrc('program X; var N: Integer = ''text''; begin end.');
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('string-into-Integer rejected', Raised);
end;

procedure TVarInitTests.TestSemantic_LocalInit_Rejected;
var Raised: Boolean;
begin
  Raised := False;
  try
    AnalyseSrc('program X; procedure Q; var L: Integer = 5; begin end; begin end.');
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('local initialiser rejected', Raised);
end;

procedure TVarInitTests.TestSemantic_RecordInit_Rejected;
var Raised: Boolean;
begin
  { Records have no const-initialiser machinery yet; must fail cleanly,
    not silently mis-emit. }
  Raised := False;
  try
    AnalyseSrc('program X; type TR = record a: Integer; end; ' +
          'var R: TR = 0; begin end.');
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('record initialiser rejected', Raised);
end;

initialization
  RegisterTest(TVarInitTests);

end.
