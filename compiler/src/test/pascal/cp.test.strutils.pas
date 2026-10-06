{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.strutils;

{ IR-level tests for StrUtils unit functions.
  These tests verify that the compiler resolves StrUtils identifiers and
  type-checks arguments correctly.  Since StrUtils is now implemented in
  pure Blaise Pascal (not as external C RTL calls), the codegen tests
  verify that unit-level functions are emitted in the IR rather than
  checking for specific RTL symbol names.  Runtime correctness is covered
  by cp.test.e2e.strutils. }

interface

uses
  SysUtils, Classes, contnrs, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uUnitLoader;

type
  TStrUtilsTests = class(TTestCase)
  private
    FRTLUnitPath: string;
    FStdlibUnitPath: string;
    procedure SemanticOK(const ASrc: string);
    procedure SemanticError(const ASrc: string);
  protected
    procedure SetUp; override;
  published
    { ContainsStr / ContainsText }
    procedure TestSemantic_ContainsStr_OK;
    procedure TestSemantic_ContainsText_OK;
    procedure TestSemantic_ContainsStr_ReturnsBoolean;

    { StartsStr / StartsText / EndsStr / EndsText }
    procedure TestSemantic_StartsStr_OK;
    procedure TestSemantic_StartsText_OK;
    procedure TestSemantic_EndsStr_OK;
    procedure TestSemantic_EndsText_OK;

    { LeftStr / RightStr / MidStr }
    procedure TestSemantic_LeftStr_OK;
    procedure TestSemantic_RightStr_OK;
    procedure TestSemantic_MidStr_OK;
    procedure TestSemantic_LeftStr_ReturnsString;

    { PosEx }
    procedure TestSemantic_PosEx_OK;
    procedure TestSemantic_PosEx_ReturnsInteger;

    { IndexStr / IndexText }
    procedure TestSemantic_IndexStr_OK;
    procedure TestSemantic_IndexText_OK;
    procedure TestSemantic_IndexStr_ReturnsInteger;

    { Replace / ReplaceAll }
    procedure TestSemantic_Replace_OK;
    procedure TestSemantic_ReplaceAll_OK;
    procedure TestSemantic_ReplaceAll_ReturnsString;

    { DupeString / ReverseString / StuffString }
    procedure TestSemantic_DupeString_OK;
    procedure TestSemantic_ReverseString_OK;
    procedure TestSemantic_StuffString_OK;
    procedure TestSemantic_DupeString_ReturnsString;

    { TrimLeft / TrimRight }
    procedure TestSemantic_TrimLeft_OK;
    procedure TestSemantic_TrimRight_OK;

    { PadLeft / PadRight }
    procedure TestSemantic_PadLeft_OK;
    procedure TestSemantic_PadRight_OK;
    procedure TestSemantic_PadLeft_ReturnsString;

    { CountOccurrences }
    procedure TestSemantic_CountOccurrences_OK;
    procedure TestSemantic_CountOccurrences_ReturnsInteger;

    { RemovePrefix / RemoveSuffix }
    procedure TestSemantic_RemovePrefix_OK;
    procedure TestSemantic_RemoveSuffix_OK;

    { IsEmptyOrWhitespace }
    procedure TestSemantic_IsEmptyOrWhitespace_OK;
    procedure TestSemantic_IsEmptyOrWhitespace_ReturnsBoolean;

    { JoinStr }
    procedure TestSemantic_JoinStr_OK;
    procedure TestSemantic_JoinStr_ReturnsString;

    { TStringBuilder }
    procedure TestSemantic_TStringBuilder_Append_OK;
    procedure TestSemantic_TStringBuilder_ToString_ReturnsString;
    procedure TestSemantic_TStringBuilder_Clear_OK;
    procedure TestSemantic_TStringBuilder_Length_OK;

    { Codegen — unit-level function calls appear in IR }
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.SetUp;
var
  ExeDir: string;
begin
  inherited SetUp();
  ExeDir := ExtractFilePath(ParamStr(0));
  FRTLUnitPath := ExpandFileName(ExeDir + '../../compiler/src/main/pascal');
  FStdlibUnitPath := ExpandFileName(ExeDir + '../../stdlib/src/main/pascal');
end;

procedure TStrUtilsTests.SemanticOK(const ASrc: string);
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create(ASrc);
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TStrUtilsTests.SemanticError(const ASrc: string);
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    try
      Lexer       := TLexer.Create(ASrc);
      Parser      := TParser.Create(Lexer);
      Prog        := Parser.Parse();
      Semantic    := TSemanticAnalyser.Create();
      SearchPaths := TStringList.Create();
      SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
      Loader := TUnitLoader.Create(SearchPaths);
      Units  := Loader.LoadAll(Prog.UsedUnits);
      for I := 0 to Units.Count - 1 do
        Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
      Semantic.Analyse(Prog);
      Fail('Expected ESemanticError but none was raised');
    except
      on E: ESemanticError do ;
    end;
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ ContainsStr / ContainsText                                           }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_ContainsStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Sub: string; B: Boolean;
    begin B := ContainsStr(S, Sub) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_ContainsText_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Sub: string; B: Boolean;
    begin B := ContainsText(S, Sub) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_ContainsStr_ReturnsBoolean;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create(
      'program P; uses StrUtils; var S, Sub: string; B: Boolean; begin B := ContainsStr(S, Sub) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertNotNull('expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('ContainsStr returns Boolean',
      Ord(tyBoolean), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ StartsStr / StartsText / EndsStr / EndsText                          }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_StartsStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Pre: string; B: Boolean;
    begin B := StartsStr(Pre, S) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_StartsText_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Pre: string; B: Boolean;
    begin B := StartsText(Pre, S) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_EndsStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Suf: string; B: Boolean;
    begin B := EndsStr(Suf, S) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_EndsText_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Suf: string; B: Boolean;
    begin B := EndsText(Suf, S) end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ LeftStr / RightStr / MidStr                                          }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_LeftStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := LeftStr(S, 3) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_RightStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := RightStr(S, 3) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_MidStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := MidStr(S, 2, 3) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_LeftStr_ReturnsString;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create('program P; uses StrUtils; var S, T: string; begin T := LeftStr(S, 3) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('LeftStr returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ PosEx                                                                }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_PosEx_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Sub: string; N: Integer;
    begin N := PosEx(Sub, S, 2) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_PosEx_ReturnsInteger;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create('program P; uses StrUtils; var S, Sub: string; N: Integer; begin N := PosEx(Sub, S, 2) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('PosEx returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ IndexStr / IndexText                                                  }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_IndexStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S: string; I: Integer;
    var Arr: array[0..2] of string;
    begin
      Arr[0] := 'a'; Arr[1] := 'b'; Arr[2] := 'c';
      I := IndexStr(S, Arr)
    end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_IndexText_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S: string; I: Integer;
    var Arr: array[0..2] of string;
    begin
      Arr[0] := 'a'; Arr[1] := 'b'; Arr[2] := 'c';
      I := IndexText(S, Arr)
    end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_IndexStr_ReturnsInteger;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create(
      'program P; uses StrUtils; var S: string; I: Integer; var Arr: array[0..2] of string; begin Arr[0] := ''a''; Arr[1] := ''b''; Arr[2] := ''c''; I := IndexStr(S, Arr) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[3]);
    AssertEquals('IndexStr returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Replace / ReplaceAll                                                 }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_Replace_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := Replace(S, 'x', 'y') end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_ReplaceAll_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := ReplaceAll(S, 'x', 'y') end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_ReplaceAll_ReturnsString;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create('program P; uses StrUtils; var S, T: string; begin T := ReplaceAll(S, ''x'', ''y'') end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('ReplaceAll returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ DupeString / ReverseString / StuffString                             }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_DupeString_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := DupeString(S, 3) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_ReverseString_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := ReverseString(S) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_StuffString_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := StuffString(S, 2, 3, 'XY') end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_DupeString_ReturnsString;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create('program P; uses StrUtils; var S, T: string; begin T := DupeString(S, 3) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('DupeString returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ TrimLeft / TrimRight                                                  }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_TrimLeft_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := TrimLeft(S) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_TrimRight_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := TrimRight(S) end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ PadLeft / PadRight                                                   }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_PadLeft_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := PadLeft(S, 10) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_PadRight_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := PadRight(S, 10) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_PadLeft_ReturnsString;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create('program P; uses StrUtils; var S, T: string; begin T := PadLeft(S, 10) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('PadLeft returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ CountOccurrences                                                      }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_CountOccurrences_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, Sub: string; N: Integer;
    begin N := CountOccurrences(Sub, S) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_CountOccurrences_ReturnsInteger;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create('program P; uses StrUtils; var S, Sub: string; N: Integer; begin N := CountOccurrences(Sub, S) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('CountOccurrences returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ RemovePrefix / RemoveSuffix                                           }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_RemovePrefix_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := RemovePrefix(S, 'foo') end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_RemoveSuffix_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S, T: string;
    begin T := RemoveSuffix(S, 'bar') end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ IsEmptyOrWhitespace                                                  }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_IsEmptyOrWhitespace_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var S: string; B: Boolean;
    begin B := IsEmptyOrWhitespace(S) end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_IsEmptyOrWhitespace_ReturnsBoolean;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create('program P; uses StrUtils; var S: string; B: Boolean; begin B := IsEmptyOrWhitespace(S) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('IsEmptyOrWhitespace returns Boolean',
      Ord(tyBoolean), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ JoinStr                                                              }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_JoinStr_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var T: string;
    var Parts: array[0..2] of string;
    begin
      Parts[0] := 'a'; Parts[1] := 'b'; Parts[2] := 'c';
      T := JoinStr(',', Parts)
    end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_JoinStr_ReturnsString;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create(
      'program P; uses StrUtils; var T: string; var Parts: array[0..2] of string; begin Parts[0] := ''a''; Parts[1] := ''b''; Parts[2] := ''c''; T := JoinStr('','', Parts) end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[3]);
    AssertEquals('JoinStr returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ TStringBuilder                                                        }
{ ------------------------------------------------------------------ }

procedure TStrUtilsTests.TestSemantic_TStringBuilder_Append_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder;
    begin
      SB := TStringBuilder.Create();
      SB.Append('hello');
      SB.Free()
    end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_TStringBuilder_ToString_ReturnsString;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer       := TLexer.Create(
      'program P; uses StrUtils; var SB: TStringBuilder; S: string; begin SB := TStringBuilder.Create(); SB.Append(''hi''); S := SB.ToString(); SB.Free() end.');
    Parser      := TParser.Create(Lexer);
    Prog        := Parser.Parse();
    Semantic    := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts[2]);
    AssertEquals('ToString returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TStrUtilsTests.TestSemantic_TStringBuilder_Clear_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder;
    begin
      SB := TStringBuilder.Create();
      SB.Append('hello');
      SB.Clear();
      SB.Free()
    end.
    ''');
end;

procedure TStrUtilsTests.TestSemantic_TStringBuilder_Length_OK;
begin
  SemanticOK(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder; N: Integer;
    begin
      SB := TStringBuilder.Create();
      SB.Append('hi');
      N := SB.Length;
      SB.Free()
    end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ Codegen — pure-Pascal unit functions appear in IR                    }
{ ------------------------------------------------------------------ }

initialization
  RegisterTest(TStrUtilsTests);

end.
