{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.numerics.money;

{ Semantic tests for the Numerics.Money stdlib unit (TMoney).

  These resolve Numerics.Money (and its Numerics.Decimal dependency) via
  TUnitLoader and run the semantic pass.  They cover the parser / semantic path
  for TMoney usage.  RTL-contract and runtime-behaviour issues are covered by
  cp.test.e2e.numerics.money.pas. }

interface

uses
  blaise.testing, strutils,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uUnitLoader;

type
  TMoneyIRTests = class(TTestCase)
  private
    FRTLUnitPath: string;
    FStdlibUnitPath: string;
    procedure SemanticOK(const ASrc: string);
    procedure AnalyseExpectError(const ASrc: string);
  protected
    procedure SetUp; override;
  published
    { --- Semantic resolution through the unit loader --- }
    procedure TestSemantic_FromStr_OK;
    procedure TestSemantic_FromInt_OK;
    procedure TestSemantic_FromDecimal_OK;
    procedure TestSemantic_Zero_OK;
    procedure TestSemantic_ToString_OK;
    procedure TestSemantic_AmountString_OK;
    procedure TestSemantic_CurrencyCode_ReturnsString_OK;
    procedure TestSemantic_Amount_ReturnsDecimal_OK;
    procedure TestSemantic_CurrencyScale_ReturnsInteger_OK;

    { --- Arithmetic / queries --- }
    procedure TestSemantic_Add_ReturnsMoney_OK;
    procedure TestSemantic_Subtract_ReturnsMoney_OK;
    procedure TestSemantic_Negate_ReturnsMoney_OK;
    procedure TestSemantic_Multiply_ReturnsMoney_OK;
    procedure TestSemantic_MultiplyInt_ReturnsMoney_OK;
    procedure TestSemantic_Compare_ReturnsInteger_OK;
    procedure TestSemantic_Equals_ReturnsBoolean_OK;
    procedure TestSemantic_IsZero_ReturnsBoolean_OK;
    procedure TestSemantic_Sign_ReturnsInteger_OK;

    { --- Rounding overloads --- }
    procedure TestSemantic_FromStr_RoundingMode_OK;
    procedure TestSemantic_FromStr_Strategy_OK;
    procedure TestSemantic_FromDecimal_RoundingMode_OK;
    procedure TestSemantic_Add_RoundingMode_OK;
    procedure TestSemantic_Multiply_Strategy_OK;

    { --- Type errors --- }
    procedure TestSemantic_FromStr_WrongArgType_Error;
    procedure TestSemantic_AssignMoneyToInt_Error;
  end;

implementation

procedure TMoneyIRTests.SetUp;
var
  ExeDir: string;
begin
  inherited SetUp();
  ExeDir := ExtractFilePath(ParamStr(0));
  FRTLUnitPath := ExpandFileName(ExeDir + '../../compiler/src/main/pascal');
  FStdlibUnitPath := ExpandFileName(ExeDir + '../../stdlib/src/main/pascal');
end;

procedure TMoneyIRTests.SemanticOK(const ASrc: string);
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

procedure TMoneyIRTests.AnalyseExpectError(const ASrc: string);
begin
  try
    SemanticOK(ASrc);
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic resolution                                                 }
{ ------------------------------------------------------------------ }

procedure TMoneyIRTests.TestSemantic_FromStr_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var M: TMoney; ' +
    'begin M := MoneyFromStr(''1.50'', ''USD'') end.');
end;

procedure TMoneyIRTests.TestSemantic_FromInt_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var M: TMoney; ' +
    'begin M := MoneyFromInt(5, ''USD'') end.');
end;

procedure TMoneyIRTests.TestSemantic_FromDecimal_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; var M: TMoney; ' +
    'begin M := MoneyFromDecimal(DecFromStr(''1.50''), ''USD'') end.');
end;

procedure TMoneyIRTests.TestSemantic_Zero_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var M: TMoney; ' +
    'begin M := MoneyZero(''USD'') end.');
end;

procedure TMoneyIRTests.TestSemantic_ToString_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var M: TMoney; S: string; ' +
    'begin M := MoneyFromInt(5, ''USD''); S := M.ToString() end.');
end;

procedure TMoneyIRTests.TestSemantic_AmountString_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var M: TMoney; S: string; ' +
    'begin M := MoneyFromInt(5, ''USD''); S := M.AmountString() end.');
end;

procedure TMoneyIRTests.TestSemantic_CurrencyCode_ReturnsString_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var M: TMoney; S: string; ' +
    'begin M := MoneyFromInt(5, ''USD''); S := M.CurrencyCode() end.');
end;

procedure TMoneyIRTests.TestSemantic_Amount_ReturnsDecimal_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; var M: TMoney; D: TDecimal; ' +
    'begin M := MoneyFromInt(5, ''USD''); D := M.Amount() end.');
end;

procedure TMoneyIRTests.TestSemantic_CurrencyScale_ReturnsInteger_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var I: Integer; ' +
    'begin I := CurrencyScale(''KWD'') end.');
end;

{ ------------------------------------------------------------------ }
{ Arithmetic / queries                                                }
{ ------------------------------------------------------------------ }

procedure TMoneyIRTests.TestSemantic_Add_ReturnsMoney_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A, B, C: TMoney; ' +
    'begin A := MoneyFromInt(1, ''USD''); B := MoneyFromInt(2, ''USD''); ' +
    'C := A.Add(B) end.');
end;

procedure TMoneyIRTests.TestSemantic_Subtract_ReturnsMoney_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A, B, C: TMoney; ' +
    'begin A := MoneyFromInt(1, ''USD''); B := MoneyFromInt(2, ''USD''); ' +
    'C := A.Subtract(B) end.');
end;

procedure TMoneyIRTests.TestSemantic_Negate_ReturnsMoney_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A, C: TMoney; ' +
    'begin A := MoneyFromInt(1, ''USD''); C := A.Negate() end.');
end;

procedure TMoneyIRTests.TestSemantic_Multiply_ReturnsMoney_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; var A, C: TMoney; ' +
    'begin A := MoneyFromInt(1, ''USD''); C := A.Multiply(DecFromStr(''1.08'')) end.');
end;

procedure TMoneyIRTests.TestSemantic_MultiplyInt_ReturnsMoney_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A, C: TMoney; ' +
    'begin A := MoneyFromInt(1, ''USD''); C := A.MultiplyInt(3) end.');
end;

procedure TMoneyIRTests.TestSemantic_Compare_ReturnsInteger_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A, B: TMoney; I: Integer; ' +
    'begin A := MoneyFromInt(1, ''USD''); B := MoneyFromInt(2, ''USD''); ' +
    'I := A.Compare(B) end.');
end;

procedure TMoneyIRTests.TestSemantic_Equals_ReturnsBoolean_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A, B: TMoney; X: Boolean; ' +
    'begin A := MoneyFromInt(1, ''USD''); B := MoneyFromInt(2, ''USD''); ' +
    'X := A.Equals(B) end.');
end;

procedure TMoneyIRTests.TestSemantic_IsZero_ReturnsBoolean_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A: TMoney; X: Boolean; ' +
    'begin A := MoneyFromInt(0, ''USD''); X := A.IsZero() end.');
end;

procedure TMoneyIRTests.TestSemantic_Sign_ReturnsInteger_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money; var A: TMoney; I: Integer; ' +
    'begin A := MoneyFromInt(1, ''USD''); I := A.Sign() end.');
end;

{ ------------------------------------------------------------------ }
{ Rounding overloads                                                  }
{ ------------------------------------------------------------------ }

procedure TMoneyIRTests.TestSemantic_FromStr_RoundingMode_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; var M: TMoney; ' +
    'begin M := MoneyFromStr(''1.005'', ''USD'', rmHalfUp) end.');
end;

procedure TMoneyIRTests.TestSemantic_FromStr_Strategy_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; ' +
    'var M: TMoney; S: IRoundingStrategy; ' +
    'begin S := StandardRounding(rmHalfUp); M := MoneyFromStr(''1.005'', ''USD'', S) end.');
end;

procedure TMoneyIRTests.TestSemantic_FromDecimal_RoundingMode_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; var M: TMoney; ' +
    'begin M := MoneyFromDecimal(DecFromStr(''1.005''), ''USD'', rmCeiling) end.');
end;

procedure TMoneyIRTests.TestSemantic_Add_RoundingMode_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; var A, B, C: TMoney; ' +
    'begin A := MoneyFromInt(1, ''USD''); B := MoneyFromInt(2, ''USD''); ' +
    'C := A.Add(B, rmDown) end.');
end;

procedure TMoneyIRTests.TestSemantic_Multiply_Strategy_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Money, Numerics.Decimal; ' +
    'var A, C: TMoney; S: IRoundingStrategy; ' +
    'begin A := MoneyFromInt(1, ''USD''); S := StandardRounding(rmFloor); ' +
    'C := A.Multiply(DecFromStr(''1.5''), S) end.');
end;

{ ------------------------------------------------------------------ }
{ Type errors                                                         }
{ ------------------------------------------------------------------ }

procedure TMoneyIRTests.TestSemantic_FromStr_WrongArgType_Error;
begin
  { Second argument must be a string currency code, not an integer. }
  AnalyseExpectError(
    'program P; uses Numerics.Money; var M: TMoney; ' +
    'begin M := MoneyFromStr(''1.50'', 5) end.');
end;

procedure TMoneyIRTests.TestSemantic_AssignMoneyToInt_Error;
begin
  AnalyseExpectError(
    'program P; uses Numerics.Money; var M: TMoney; I: Integer; ' +
    'begin M := MoneyFromInt(1, ''USD''); I := M end.');
end;

initialization
  RegisterTest(TMoneyIRTests);

end.
