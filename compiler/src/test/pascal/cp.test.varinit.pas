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
  Classes, SysUtils, uLexer, uParser, uAST, uSemantic, uSymbolTable;

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
    { a set initialiser folds to the bitmask (small set) or byte bitmap
      (jumbo set) of the variable's own set type; a member of another enum
      is reported (set initialisers were rejected as not yet supported) }
    procedure TestSemantic_SetInit_FoldsBitmask;
    procedure TestSemantic_SetInit_JumboFoldsBytes;
    procedure TestSemantic_SetInit_WrongEnum_Rejected;
    { nil initialises a pointer, class, interface, metaclass, procedural or
      dynamic-array variable; the variable is zeroed already, so the
      initialiser is checked and dropped.  nil into an Integer is reported. }
    procedure TestSemantic_NilInit_PointerLikeAccepted;
    procedure TestSemantic_NilInit_Integer_Rejected;
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

function VarInitOf(AProg: TProgram; const AName: string): TConstDecl;
var
  I: Int;
begin
  Result := nil;
  for I := 0 to AProg.Block.Decls.Count - 1 do
    if TVarDecl(AProg.Block.Decls.Items[I]).Names.IndexOf(AName) >= 0 then
      Exit(TVarDecl(AProg.Block.Decls.Items[I]).InitConst);
end;

function AnalysedProg(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
  A: TSemanticAnalyser;
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

procedure TVarInitTests.TestSemantic_SetInit_FoldsBitmask;
var
  Prog: TProgram;
begin
  Prog := AnalysedProg('''
    program X;
    type
      TEn = (eA, eB, eC, eD);
      TS = set of TEn;
    var
      S: TS = [eA, eC..eD];
      E: TS = [];
    begin
    end.
    ''');
  try
    AssertEquals('[eA, eC..eD] bitmask', Int64(13), VarInitOf(Prog, 'S').IntVal);
    AssertEquals('[] bitmask', Int64(0), VarInitOf(Prog, 'E').IntVal);
  finally
    Prog.Free();
  end;
end;

procedure TVarInitTests.TestSemantic_SetInit_JumboFoldsBytes;
var
  Prog: TProgram;
  CD: TConstDecl;
begin
  Prog := AnalysedProg('''
    program X;
    type
      TBig = 0..199;
      TJ = set of TBig;
    var
      J: TJ = [1, 9, 150];
    begin
    end.
    ''');
  try
    CD := VarInitOf(Prog, 'J');
    AssertTrue('byte bitmap built', CD.ConstSetBytes <> nil);
    AssertEquals('byte 0 holds member 1', '2', CD.ConstSetBytes[0]);
    AssertEquals('byte 1 holds member 9', '2', CD.ConstSetBytes[1]);
    AssertEquals('byte 18 holds member 150', '64', CD.ConstSetBytes[18]);
  finally
    Prog.Free();
  end;
end;

procedure TVarInitTests.TestSemantic_SetInit_WrongEnum_Rejected;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    AnalyseSrc('program X; type TA = (a1, a2); TB = (b1, b2); ' +
      'TSA = set of TA; var S: TSA = [b1]; begin end.');
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('member of another enum rejected', Raised);
end;

procedure TVarInitTests.TestSemantic_NilInit_PointerLikeAccepted;
var
  Prog: TProgram;
begin
  Prog := AnalysedProg('''
    program X;
    type
      TProc = procedure;
      TClassRef = class of TObject;
      IThing = interface end;
    var
      P: Pointer = nil;
      O: TObject = nil;
      C: TClassRef = nil;
      F: TProc = nil;
      I: IThing = nil;
      A: array of Integer = nil;
    begin
    end.
    ''');
  try
    AssertTrue('pointer initialiser dropped', VarInitOf(Prog, 'P') = nil);
    AssertTrue('class initialiser dropped', VarInitOf(Prog, 'O') = nil);
    AssertTrue('metaclass initialiser dropped', VarInitOf(Prog, 'C') = nil);
    AssertTrue('procedural initialiser dropped', VarInitOf(Prog, 'F') = nil);
    AssertTrue('interface initialiser dropped', VarInitOf(Prog, 'I') = nil);
    AssertTrue('dynamic array initialiser dropped', VarInitOf(Prog, 'A') = nil);
  finally
    Prog.Free();
  end;
end;

procedure TVarInitTests.TestSemantic_NilInit_Integer_Rejected;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    AnalyseSrc('program X; var N: Integer = nil; begin end.');
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('nil into an Integer rejected', Raised);
end;

initialization
  RegisterTest(TVarInitTests);

end.
