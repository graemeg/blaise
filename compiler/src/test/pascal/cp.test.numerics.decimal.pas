{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.numerics.decimal;

{ Semantic tests for the Numerics.Decimal stdlib unit (TDecimal).

  These resolve Numerics.Decimal via TUnitLoader and run the semantic pass.
  They cover the parser / semantic path for TDecimal usage; runtime behaviour
  is covered by cp.test.e2e.numerics.decimal.pas.

  Phase 0 surface: construction (DecFromInt / DecFromInt64 / DecFromStr),
  ToString / ToPlainString, Scale, IsZero, Sign. }

interface

uses
  blaise.testing, strutils,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uUnitLoader;

type
  TDecimalIRTests = class(TTestCase)
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
    procedure TestSemantic_FromInt64_OK;
    procedure TestSemantic_ToString_OK;
    procedure TestSemantic_ToPlainString_OK;
    procedure TestSemantic_Scale_ReturnsInteger_OK;
    procedure TestSemantic_IsZero_ReturnsBoolean_OK;
    procedure TestSemantic_Sign_ReturnsInteger_OK;

    { --- Comparison / equality / hash --- }
    procedure TestSemantic_Compare_ReturnsInteger_OK;
    procedure TestSemantic_Equals_ReturnsBoolean_OK;
    procedure TestSemantic_GetHashCode_ReturnsInteger_OK;

    { --- Arithmetic (add/subtract/negate/abs) --- }
    procedure TestSemantic_Add_ReturnsDecimal_OK;
    procedure TestSemantic_Subtract_ReturnsDecimal_OK;
    procedure TestSemantic_Negate_ReturnsDecimal_OK;
    procedure TestSemantic_Abs_ReturnsDecimal_OK;
    procedure TestSemantic_Multiply_ReturnsDecimal_OK;
    procedure TestSemantic_FromStr_LargeValue_OK;

    { --- Division / rounding --- }
    procedure TestSemantic_Divide_EnumMode_OK;
    procedure TestSemantic_Divide_Strategy_OK;
    procedure TestSemantic_RoundTo_EnumMode_OK;
    procedure TestSemantic_SetScale_OK;
    procedure TestSemantic_StandardRounding_ReturnsStrategy_OK;
    procedure TestSemantic_CustomStrategy_OK;

    { --- Float conversion / strip / out-conversions --- }
    procedure TestSemantic_DecFromFloat_OK;
    procedure TestSemantic_DecFromFloatExact_OK;
    procedure TestSemantic_StripTrailingZeros_OK;
    procedure TestSemantic_ToDouble_ReturnsDouble_OK;
    procedure TestSemantic_ToInt64_ReturnsInt64_OK;

    { --- Type errors --- }
    procedure TestSemantic_FromInt_WrongArgType_Error;
    procedure TestSemantic_AssignDecimalToInt_Error;
  end;

implementation

procedure TDecimalIRTests.SetUp;
var
  ExeDir: string;
begin
  inherited SetUp();
  ExeDir := ExtractFilePath(ParamStr(0));
  FRTLUnitPath := ExpandFileName(ExeDir + '../../compiler/src/main/pascal');
  FStdlibUnitPath := ExpandFileName(ExeDir + '../../stdlib/src/main/pascal');
end;

procedure TDecimalIRTests.SemanticOK(const ASrc: string);
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

procedure TDecimalIRTests.AnalyseExpectError(const ASrc: string);
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

procedure TDecimalIRTests.TestSemantic_FromStr_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; ' +
    'begin A := DecFromStr(''1.50'') end.');
end;

procedure TDecimalIRTests.TestSemantic_FromInt_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; ' +
    'begin A := DecFromInt(5) end.');
end;

procedure TDecimalIRTests.TestSemantic_FromInt64_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; ' +
    'begin A := DecFromInt64(5) end.');
end;

procedure TDecimalIRTests.TestSemantic_ToString_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; S: string; ' +
    'begin A := DecFromInt(5); S := A.ToString() end.');
end;

procedure TDecimalIRTests.TestSemantic_ToPlainString_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; S: string; ' +
    'begin A := DecFromInt(5); S := A.ToPlainString() end.');
end;

procedure TDecimalIRTests.TestSemantic_Scale_ReturnsInteger_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; N: Integer; ' +
    'begin A := DecFromStr(''1.50''); N := A.Scale() end.');
end;

procedure TDecimalIRTests.TestSemantic_IsZero_ReturnsBoolean_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; B: Boolean; ' +
    'begin A := DecFromInt(0); B := A.IsZero() end.');
end;

procedure TDecimalIRTests.TestSemantic_Sign_ReturnsInteger_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; N: Integer; ' +
    'begin A := DecFromInt(-3); N := A.Sign() end.');
end;

procedure TDecimalIRTests.TestSemantic_Compare_ReturnsInteger_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, B: TDecimal; N: Integer; ' +
    'begin A := DecFromStr(''2.0''); B := DecFromStr(''2.00''); ' +
    'N := A.Compare(B) end.');
end;

procedure TDecimalIRTests.TestSemantic_Equals_ReturnsBoolean_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, B: TDecimal; E: Boolean; ' +
    'begin A := DecFromStr(''2.0''); B := DecFromStr(''2.00''); ' +
    'E := A.Equals(B) end.');
end;

procedure TDecimalIRTests.TestSemantic_GetHashCode_ReturnsInteger_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; H: Integer; ' +
    'begin A := DecFromStr(''2.0''); H := A.GetHashCode() end.');
end;

procedure TDecimalIRTests.TestSemantic_Add_ReturnsDecimal_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, B, C: TDecimal; ' +
    'begin A := DecFromStr(''1.5''); B := DecFromStr(''2.25''); ' +
    'C := A.Add(B) end.');
end;

procedure TDecimalIRTests.TestSemantic_Subtract_ReturnsDecimal_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, B, C: TDecimal; ' +
    'begin A := DecFromStr(''1.5''); B := DecFromStr(''2.25''); ' +
    'C := A.Subtract(B) end.');
end;

procedure TDecimalIRTests.TestSemantic_Negate_ReturnsDecimal_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, C: TDecimal; ' +
    'begin A := DecFromStr(''5.00''); C := A.Negate() end.');
end;

procedure TDecimalIRTests.TestSemantic_Abs_ReturnsDecimal_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, C: TDecimal; ' +
    'begin A := DecFromStr(''-7.25''); C := A.Abs() end.');
end;

procedure TDecimalIRTests.TestSemantic_Multiply_ReturnsDecimal_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, B, C: TDecimal; ' +
    'begin A := DecFromStr(''19.99''); B := DecFromStr(''0.20''); ' +
    'C := A.Multiply(B) end.');
end;

procedure TDecimalIRTests.TestSemantic_FromStr_LargeValue_OK;
begin
  { A 20+ digit literal exceeds Int64 and must still parse (inflated path). }
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; S: string; ' +
    'begin A := DecFromStr(''99999999999999999999''); S := A.ToString() end.');
end;

procedure TDecimalIRTests.TestSemantic_Divide_EnumMode_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, B, C: TDecimal; ' +
    'begin A := DecFromStr(''10''); B := DecFromStr(''4''); ' +
    'C := A.Divide(B, 2, rmHalfEven) end.');
end;

procedure TDecimalIRTests.TestSemantic_Divide_Strategy_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, B, C: TDecimal; S: IRoundingStrategy; ' +
    'begin A := DecFromStr(''1''); B := DecFromStr(''3''); ' +
    'S := StandardRounding(rmHalfUp); C := A.Divide(B, 4, S) end.');
end;

procedure TDecimalIRTests.TestSemantic_RoundTo_EnumMode_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, C: TDecimal; ' +
    'begin A := DecFromStr(''3.14159''); C := A.RoundTo(2, rmHalfEven) end.');
end;

procedure TDecimalIRTests.TestSemantic_SetScale_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, C: TDecimal; ' +
    'begin A := DecFromStr(''1.5''); C := A.SetScale(4, rmHalfEven) end.');
end;

procedure TDecimalIRTests.TestSemantic_StandardRounding_ReturnsStrategy_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var S: IRoundingStrategy; ' +
    'begin S := StandardRounding(rmHalfEven) end.');
end;

procedure TDecimalIRTests.TestSemantic_CustomStrategy_OK;
begin
  { A user class implementing IRoundingStrategy must satisfy the interface. }
  SemanticOK(
    'program P; uses Numerics.Decimal;' +
    'type TMy = class(TObject, IRoundingStrategy)' +
    '  function RoundIncrement(Negative: Boolean; LastKeptDigit: Integer;' +
    '    DiscardedCompareHalf: Integer; AnyDiscarded: Boolean): Boolean;' +
    'end;' +
    'function TMy.RoundIncrement(Negative: Boolean; LastKeptDigit: Integer;' +
    '  DiscardedCompareHalf: Integer; AnyDiscarded: Boolean): Boolean;' +
    'begin Result := False end;' +
    'var A, B, C: TDecimal; S: IRoundingStrategy;' +
    'begin S := TMy.Create(); A := DecFromStr(''1''); B := DecFromStr(''3'');' +
    'C := A.Divide(B, 4, S) end.');
end;

procedure TDecimalIRTests.TestSemantic_DecFromFloat_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; D: Double; ' +
    'begin D := 0.1; A := DecFromFloat(D) end.');
end;

procedure TDecimalIRTests.TestSemantic_DecFromFloatExact_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; D: Double; ' +
    'begin D := 0.1; A := DecFromFloatExact(D) end.');
end;

procedure TDecimalIRTests.TestSemantic_StripTrailingZeros_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A, C: TDecimal; ' +
    'begin A := DecFromStr(''4.0000''); C := A.StripTrailingZeros() end.');
end;

procedure TDecimalIRTests.TestSemantic_ToDouble_ReturnsDouble_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; D: Double; ' +
    'begin A := DecFromStr(''3.14''); D := A.ToDouble() end.');
end;

procedure TDecimalIRTests.TestSemantic_ToInt64_ReturnsInt64_OK;
begin
  SemanticOK(
    'program P; uses Numerics.Decimal; var A: TDecimal; N: Int64; ' +
    'begin A := DecFromStr(''42.99''); N := A.ToInt64() end.');
end;

{ ------------------------------------------------------------------ }
{ Type errors                                                         }
{ ------------------------------------------------------------------ }

procedure TDecimalIRTests.TestSemantic_FromInt_WrongArgType_Error;
begin
  { DecFromInt expects an integer, not a string. }
  AnalyseExpectError(
    'program P; uses Numerics.Decimal; var A: TDecimal; ' +
    'begin A := DecFromInt(''x'') end.');
end;

procedure TDecimalIRTests.TestSemantic_AssignDecimalToInt_Error;
begin
  { A TDecimal value is not assignable to an Integer. }
  AnalyseExpectError(
    'program P; uses Numerics.Decimal; var A: TDecimal; N: Integer; ' +
    'begin A := DecFromInt(5); N := A end.');
end;

initialization
  RegisterTest(TDecimalIRTests);

end.
