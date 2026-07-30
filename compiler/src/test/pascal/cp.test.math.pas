{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.math;

{ IR-level tests for Math unit functions and math compiler builtins.

  Builtins (handled in uSemantic + blaise.codegen.qbe, no RTL unit needed):
    Abs, Sqrt, Ceil, Floor, Round, Trunc, Ln, Log2, Log10, Power,
    Sin, Cos, Tan, ArcTan, ArcTan2, IsNaN, IsInfinite.

  RTL unit (math.pas, resolved via TUnitLoader):
    Min, Max, Sign, DivMod, InRange, EnsureRange, Pi. }

interface

uses
  SysUtils, Classes, contnrs, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe, uUnitLoader;

type
  TMathTests = class(TTestCase)
  private
    FRTLUnitPath: string;
    FStdlibUnitPath: string;
    function  GenIR(const ASrc: string): string;
    function  GenIRBuiltin(const ASrc: string): string;
    function  IRContains(const AIR, AFragment: string): Boolean;
    procedure SemanticOK(const ASrc: string);
    procedure SemanticOKBuiltin(const ASrc: string);
    procedure SemanticError(const ASrc: string);
  protected
    procedure SetUp; override;
  published
    { --- Compiler builtins: semantic type checking --- }

    { Sqrt }
    procedure TestSemantic_Sqrt_Double_OK;
    procedure TestSemantic_Sqrt_Single_OK;
    procedure TestSemantic_Sqrt_ReturnsDouble;
    procedure TestSemantic_Sqrt_IntegerArg_Accepted;

    { Ceil / Floor / Round / Trunc → Integer }
    procedure TestSemantic_Ceil_OK;
    procedure TestSemantic_Ceil_ReturnsInteger;
    procedure TestSemantic_Floor_OK;
    procedure TestSemantic_Floor_ReturnsInteger;
    procedure TestSemantic_Round_OK;
    procedure TestSemantic_Round_ReturnsInteger;
    procedure TestSemantic_Trunc_OK;
    procedure TestSemantic_Trunc_ReturnsInteger;
    procedure TestSemantic_Ceil_IntegerArg_Accepted;

    { Integer arguments to float builtins coerce to Double (FPC/Delphi
      semantics; consistent with implicit int->float assignment). }
    procedure TestSemantic_Trig_IntegerArg_Accepted;
    procedure TestSemantic_Trig_IntegerArg_ReturnsDouble;
    procedure TestCodegen_Sin_IntegerArg_CoercesToDouble;
    procedure TestCodegen_Power_IntegerArgs_CoerceToDouble;

    { Float typecasts must emit real conversions, not bit copies. }
    procedure TestCodegen_CastDoubleFromInt_EmitsConversion;
    procedure TestCodegen_CastSingleFromInt_EmitsConversion;

    { Ln / Log2 / Log10 → Double }
    procedure TestSemantic_Ln_OK;
    procedure TestSemantic_Ln_ReturnsDouble;
    procedure TestSemantic_Log2_OK;
    procedure TestSemantic_Log10_OK;

    { Power → Double }
    procedure TestSemantic_Power_OK;
    procedure TestSemantic_Power_ReturnsDouble;

    { Trig — Sin / Cos / Tan / ArcTan / ArcTan2 / ArcSin / ArcCos / Sinh / Cosh / Tanh }
    procedure TestSemantic_Sin_OK;
    procedure TestSemantic_Cos_OK;
    procedure TestSemantic_Tan_OK;
    procedure TestSemantic_ArcTan_OK;
    procedure TestSemantic_ArcTan2_OK;
    procedure TestSemantic_ArcSin_OK;
    procedure TestSemantic_ArcCos_OK;
    procedure TestSemantic_Sinh_OK;
    procedure TestSemantic_Cosh_OK;
    procedure TestSemantic_Tanh_OK;
    procedure TestSemantic_Sin_ReturnsDouble;
    procedure TestSemantic_Sin_Single_ReturnsSingle;
    procedure TestSemantic_Sinh_Single_ReturnsSingle;

    { IsNaN / IsInfinite → Boolean }
    procedure TestSemantic_IsNaN_OK;
    procedure TestSemantic_IsNaN_ReturnsBoolean;
    procedure TestSemantic_IsInfinite_OK;
    procedure TestSemantic_IsInfinite_ReturnsBoolean;

    { Codegen — builtins emit correct IR }
    procedure TestCodegen_Sqrt_EmitsSqrt;
    procedure TestCodegen_Trunc_EmitsDtosi;
    procedure TestCodegen_Ceil_EmitsCeilAndDtosi;
    procedure TestCodegen_Floor_EmitsFloorAndDtosi;
    procedure TestCodegen_Round_EmitsRoundAndDtosi;
    procedure TestCodegen_Ln_EmitsLog;
    procedure TestCodegen_Log2_EmitsLog2;
    procedure TestCodegen_Log10_EmitsLog10;
    procedure TestCodegen_Power_EmitsPow;
    procedure TestCodegen_Sin_EmitsSin;
    procedure TestCodegen_Cos_EmitsCos;
    procedure TestCodegen_Tan_EmitsTan;
    procedure TestCodegen_ArcTan_EmitsAtan;
    procedure TestCodegen_ArcTan2_EmitsAtan2;
    procedure TestCodegen_ArcSin_EmitsAsin;
    procedure TestCodegen_ArcCos_EmitsAcos;
    procedure TestCodegen_Sinh_EmitsSinh;
    procedure TestCodegen_Cosh_EmitsCosh;
    procedure TestCodegen_Tanh_EmitsTanh;
    procedure TestCodegen_Sin_Single_EmitsSinf;
    procedure TestCodegen_Sinh_Single_EmitsSinhf;
    procedure TestCodegen_ArcSin_Single_EmitsAsinf;
    procedure TestCodegen_IsNaN_EmitsIsnan;
    procedure TestCodegen_IsInfinite_EmitsIsinf;
    { QBE codegen regression guards found during the libm removal }
    procedure TestCodegen_ConstDoubleArray_EmitsFloatDataItems;
    procedure TestCodegen_VarParamDouble_LoadsWithLoadd;
    procedure TestCodegen_IndirectCall_RecordArg_UsesAggregateABI;

    { --- RTL unit: Math.pas --- }

    { Min / Max }
    procedure TestSemantic_Min_Integer_OK;
    procedure TestSemantic_Max_Integer_OK;
    procedure TestSemantic_Min_Double_OK;
    procedure TestSemantic_Max_Double_OK;
    procedure TestSemantic_Min_ReturnsInteger;
    procedure TestSemantic_Max_ReturnsDouble;

    { Sign }
    procedure TestSemantic_Sign_Integer_OK;
    procedure TestSemantic_Sign_Double_OK;
    procedure TestSemantic_Sign_ReturnsInteger;

    { DivMod }
    procedure TestSemantic_DivMod_OK;

    { InRange }
    procedure TestSemantic_InRange_Integer_OK;
    procedure TestSemantic_InRange_Double_OK;
    procedure TestSemantic_InRange_ReturnsBoolean;

    { EnsureRange }
    procedure TestSemantic_EnsureRange_Integer_OK;
    procedure TestSemantic_EnsureRange_Double_OK;
    procedure TestSemantic_EnsureRange_Integer_ReturnsInteger;

    { Pi constant }
    procedure TestSemantic_Pi_UsableInExpr;

    { Codegen — RTL functions appear in IR }
    procedure TestCodegen_Min_InIR;
    procedure TestCodegen_Max_InIR;
    procedure TestCodegen_Sign_InIR;

    { Float → Integer assignment must be rejected }
    procedure TestSemantic_Assign_DoubleToInteger_Rejected;
    procedure TestSemantic_Assign_SingleToInteger_Rejected;
    procedure TestSemantic_Assign_IntegerToDouble_OK;
    procedure TestSemantic_Assign_IntegerToSingle_OK;

    { Float ↔ Float assignment is allowed }
    procedure TestSemantic_Assign_DoubleToDouble_OK;
    procedure TestSemantic_Assign_SingleToSingle_OK;
    procedure TestSemantic_Assign_SingleToDouble_OK;

    { `/` is real division — Integer / Integer → Double }
    procedure TestSemantic_RealDiv_IntegerIntegerReturnsDouble;
    procedure TestSemantic_RealDiv_IntegerDoubleReturnsDouble;
    procedure TestSemantic_RealDiv_AsTruncArg_OK;
    procedure TestSemantic_RealDiv_AsRoundArg_OK;
    procedure TestSemantic_IntegerDiv_RejectsFloat;
    procedure TestCodegen_RealDiv_IntegerOperands_EmitsFloatDiv;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

procedure TMathTests.SetUp;
var
  ExeDir: string;
begin
  inherited SetUp();
  ExeDir := ExtractFilePath(ParamStr(0));
  FRTLUnitPath := ExpandFileName(ExeDir + '../../compiler/src/main/pascal');
  FStdlibUnitPath := ExpandFileName(ExeDir + '../../stdlib/src/main/pascal');
end;

{ Compile with RTL unit loader (for Math.pas functions). }
procedure TMathTests.SemanticOK(const ASrc: string);
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

{ Compile without RTL unit loader (for compiler builtins that need no unit). }
procedure TMathTests.SemanticOKBuiltin(const ASrc: string);
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.SemanticError(const ASrc: string);
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    try
      Lexer    := TLexer.Create(ASrc);
      Parser   := TParser.Create(Lexer);
      Prog     := Parser.Parse();
      Semantic := TSemanticAnalyser.Create();
      Semantic.Analyse(Prog);
      Fail('Expected ESemanticError but none was raised');
    except
      on E: ESemanticError do ;
    end;
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ Generate IR with RTL unit loader. }
function TMathTests.GenIR(const ASrc: string): string;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  CG:          TCodeGenQBE;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  I:           Integer;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
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
    CG := TCodeGenQBE.Create();
    CG.SetSymbolTable(Prog.SymbolTable);
    for I := 0 to Units.Count - 1 do
      CG.AppendUnit(TUnit(Units.Items[I]));
    CG.AppendProgram(Prog);
    Result := CG.GetOutput();
  finally
    CG.Free(); Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ Generate IR without RTL unit loader (for builtins). }
function TMathTests.GenIRBuiltin(const ASrc: string): string;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    CG       := TCodeGenQBE.Create();
    CG.Generate(Prog);
    Result   := CG.GetOutput();
  finally
    CG.Free(); Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

function TMathTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

{ ------------------------------------------------------------------ }
{ Sqrt                                                                 }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Sqrt_Double_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Sqrt(X) end.');
end;

procedure TMathTests.TestSemantic_Sqrt_Single_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Single; begin R := Sqrt(X) end.');
end;

procedure TMathTests.TestSemantic_Sqrt_ReturnsDouble;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X, R: Double; begin R := Sqrt(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Double', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Sqrt_IntegerArg_Accepted;
begin
  SemanticOKBuiltin('program P; var X: Integer; R: Double; begin R := Sqrt(X) end.');
end;

{ ------------------------------------------------------------------ }
{ Ceil / Floor / Round / Trunc                                         }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Ceil_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Double; R: Integer; begin R := Ceil(X) end.');
end;

procedure TMathTests.TestSemantic_Ceil_ReturnsInteger;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Double; R: Integer; begin R := Ceil(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Integer', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Floor_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Double; R: Integer; begin R := Floor(X) end.');
end;

procedure TMathTests.TestSemantic_Floor_ReturnsInteger;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Double; R: Integer; begin R := Floor(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Integer', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Round_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Double; R: Integer; begin R := Round(X) end.');
end;

procedure TMathTests.TestSemantic_Round_ReturnsInteger;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Double; R: Integer; begin R := Round(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Integer', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Trunc_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Double; R: Integer; begin R := Trunc(X) end.');
end;

procedure TMathTests.TestSemantic_Trunc_ReturnsInteger;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Double; R: Integer; begin R := Trunc(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Integer', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Ceil_IntegerArg_Accepted;
begin
  SemanticOKBuiltin('program P; var X: Integer; R: Integer; begin R := Ceil(X) end.');
end;

procedure TMathTests.TestSemantic_Trig_IntegerArg_Accepted;
begin
  SemanticOKBuiltin('program P; var I: Integer; D: Double; begin D := Tanh(I) end.');
  SemanticOKBuiltin('program P; var D: Double; begin D := Sin(12) end.');
  SemanticOKBuiltin('program P; var I: Integer; D: Double; begin D := ArcTan2(I, I) end.');
end;

procedure TMathTests.TestSemantic_Trig_IntegerArg_ReturnsDouble;
begin
  { The result of a trig builtin on an integer argument is Double — it must
    be assignable to a Double without error (and to a Single via implicit
    narrowing on assignment). }
  SemanticOKBuiltin('program P; var S: Single; begin S := Sin(12) end.');
end;

procedure TMathTests.TestCodegen_Sin_IntegerArg_CoercesToDouble;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var I: Integer; D: Double; begin I := 3; D := Sin(I) end.');
  AssertTrue('int argument converted with swtof', IRContains(IR, 'swtof'));
  AssertTrue('double sin called', IRContains(IR, 'call $_BlaiseSin('));
end;

procedure TMathTests.TestCodegen_Power_IntegerArgs_CoerceToDouble;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var D: Double; begin D := Power(2, 10) end.');
  AssertTrue('int arguments converted with swtof', IRContains(IR, 'swtof'));
  AssertTrue('pow called', IRContains(IR, 'call $_BlaisePow('));
end;

procedure TMathTests.TestCodegen_CastDoubleFromInt_EmitsConversion;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var I: Integer; D: Double; begin I := 32; D := Double(I) end.');
  AssertTrue('Double(I) emits int->float conversion', IRContains(IR, 'swtof'));
end;

procedure TMathTests.TestCodegen_CastSingleFromInt_EmitsConversion;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var I: Integer; S: Single; begin I := 32; S := Single(I) end.');
  AssertTrue('Single(I) emits int->float conversion',
    IRContains(IR, '=s swtof'));
end;

{ ------------------------------------------------------------------ }
{ Ln / Log2 / Log10                                                    }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Ln_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Ln(X) end.');
end;

procedure TMathTests.TestSemantic_Ln_ReturnsDouble;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X, R: Double; begin R := Ln(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Double', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Log2_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Log2(X) end.');
end;

procedure TMathTests.TestSemantic_Log10_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Log10(X) end.');
end;

{ ------------------------------------------------------------------ }
{ Power                                                                }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Power_OK;
begin
  SemanticOKBuiltin(
    'program P; var B, E, R: Double; begin R := Power(B, E) end.');
end;

procedure TMathTests.TestSemantic_Power_ReturnsDouble;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var B, E, R: Double; begin R := Power(B, E) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Double', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Trig                                                                 }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Sin_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Sin(X) end.');
end;

procedure TMathTests.TestSemantic_Cos_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Cos(X) end.');
end;

procedure TMathTests.TestSemantic_Tan_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Tan(X) end.');
end;

procedure TMathTests.TestSemantic_ArcTan_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := ArcTan(X) end.');
end;

procedure TMathTests.TestSemantic_ArcTan2_OK;
begin
  SemanticOKBuiltin(
    'program P; var Y, X, R: Double; begin R := ArcTan2(Y, X) end.');
end;

procedure TMathTests.TestSemantic_Sin_ReturnsDouble;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X, R: Double; begin R := Sin(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Double', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Sin_Single_ReturnsSingle;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X, R: Single; begin R := Sin(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Single', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_ArcSin_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := ArcSin(X) end.');
end;

procedure TMathTests.TestSemantic_ArcCos_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := ArcCos(X) end.');
end;

procedure TMathTests.TestSemantic_Sinh_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Sinh(X) end.');
end;

procedure TMathTests.TestSemantic_Cosh_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Cosh(X) end.');
end;

procedure TMathTests.TestSemantic_Tanh_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Double; begin R := Tanh(X) end.');
end;

procedure TMathTests.TestSemantic_Sinh_Single_ReturnsSingle;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X, R: Single; begin R := Sinh(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Single', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ IsNaN / IsInfinite                                                   }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_IsNaN_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Double; B: Boolean; begin B := IsNaN(X) end.');
end;

procedure TMathTests.TestSemantic_IsNaN_ReturnsBoolean;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Double; B: Boolean; begin B := IsNaN(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Boolean', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_IsInfinite_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Double; B: Boolean; begin B := IsInfinite(X) end.');
end;

procedure TMathTests.TestSemantic_IsInfinite_ReturnsBoolean;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Double; B: Boolean; begin B := IsInfinite(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Boolean', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen — builtins                                                   }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestCodegen_Sqrt_EmitsSqrt;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Sqrt(X) end.');
  AssertTrue('sqrt in IR', IRContains(IR, '$_BlaiseSqrtD'));
end;

procedure TMathTests.TestCodegen_Trunc_EmitsDtosi;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X: Double; R: Integer; begin R := Trunc(X) end.');
  AssertTrue('dtosi in IR', IRContains(IR, 'dtosi'));
end;

procedure TMathTests.TestCodegen_Ceil_EmitsCeilAndDtosi;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X: Double; R: Integer; begin R := Ceil(X) end.');
  AssertTrue('ceil in IR', IRContains(IR, '$_BlaiseCeilD'));
  AssertTrue('dtosi in IR', IRContains(IR, 'dtosi'));
end;

procedure TMathTests.TestCodegen_Floor_EmitsFloorAndDtosi;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X: Double; R: Integer; begin R := Floor(X) end.');
  AssertTrue('floor in IR', IRContains(IR, '$_BlaiseFloorD'));
  AssertTrue('dtosi in IR', IRContains(IR, 'dtosi'));
end;

procedure TMathTests.TestCodegen_Round_EmitsRoundAndDtosi;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X: Double; R: Integer; begin R := Round(X) end.');
  AssertTrue('round in IR', IRContains(IR, '$_BlaiseRoundD'));
  AssertTrue('dtosi in IR', IRContains(IR, 'dtosi'));
end;

procedure TMathTests.TestCodegen_Ln_EmitsLog;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Ln(X) end.');
  AssertTrue('log in IR', IRContains(IR, '$_BlaiseLn'));
end;

procedure TMathTests.TestCodegen_Log2_EmitsLog2;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Log2(X) end.');
  AssertTrue('log2 in IR', IRContains(IR, '$_BlaiseLog2'));
end;

procedure TMathTests.TestCodegen_Log10_EmitsLog10;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Log10(X) end.');
  AssertTrue('log10 in IR', IRContains(IR, '$_BlaiseLog10'));
end;

procedure TMathTests.TestCodegen_Power_EmitsPow;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var B, E, R: Double; begin R := Power(B, E) end.');
  AssertTrue('pow in IR', IRContains(IR, '$_BlaisePow'));
end;

procedure TMathTests.TestCodegen_Sin_EmitsSin;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Sin(X) end.');
  AssertTrue('sin in IR', IRContains(IR, '$_BlaiseSin'));
end;

procedure TMathTests.TestCodegen_Cos_EmitsCos;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Cos(X) end.');
  AssertTrue('cos in IR', IRContains(IR, '$_BlaiseCos'));
end;

procedure TMathTests.TestCodegen_Tan_EmitsTan;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Tan(X) end.');
  AssertTrue('tan in IR', IRContains(IR, '$_BlaiseTan'));
end;

procedure TMathTests.TestCodegen_ArcTan_EmitsAtan;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := ArcTan(X) end.');
  AssertTrue('atan in IR', IRContains(IR, '$_BlaiseArcTan'));
end;

procedure TMathTests.TestCodegen_ArcTan2_EmitsAtan2;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var Y, X, R: Double; begin R := ArcTan2(Y, X) end.');
  AssertTrue('atan2 in IR', IRContains(IR, '$_BlaiseArcTan2'));
end;

procedure TMathTests.TestCodegen_ArcSin_EmitsAsin;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := ArcSin(X) end.');
  AssertTrue('asin in IR', IRContains(IR, '$_BlaiseArcSin'));
end;

procedure TMathTests.TestCodegen_ArcCos_EmitsAcos;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := ArcCos(X) end.');
  AssertTrue('acos in IR', IRContains(IR, '$_BlaiseArcCos'));
end;

procedure TMathTests.TestCodegen_Sinh_EmitsSinh;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Sinh(X) end.');
  AssertTrue('sinh in IR', IRContains(IR, '$_BlaiseSinh'));
end;

procedure TMathTests.TestCodegen_Cosh_EmitsCosh;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Cosh(X) end.');
  AssertTrue('cosh in IR', IRContains(IR, '$_BlaiseCosh'));
end;

procedure TMathTests.TestCodegen_Tanh_EmitsTanh;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Double; begin R := Tanh(X) end.');
  AssertTrue('tanh in IR', IRContains(IR, '$_BlaiseTanh'));
end;

procedure TMathTests.TestCodegen_Sin_Single_EmitsSinf;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Single; begin R := Sin(X) end.');
  AssertTrue('widened sin call in IR', IRContains(IR, '$_BlaiseSin'));
  AssertTrue('result narrowed to single', IRContains(IR, 'truncd'));
end;

procedure TMathTests.TestCodegen_Sinh_Single_EmitsSinhf;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Single; begin R := Sinh(X) end.');
  AssertTrue('widened sinh call in IR', IRContains(IR, '$_BlaiseSinh'));
  AssertTrue('result narrowed to single', IRContains(IR, 'truncd'));
end;

procedure TMathTests.TestCodegen_ArcSin_Single_EmitsAsinf;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, R: Single; begin R := ArcSin(X) end.');
  AssertTrue('widened asin call in IR', IRContains(IR, '$_BlaiseArcSin'));
  AssertTrue('result narrowed to single', IRContains(IR, 'truncd'));
end;

procedure TMathTests.TestCodegen_IsNaN_EmitsIsnan;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X: Double; B: Boolean; begin B := IsNaN(X) end.');
  AssertTrue('inline unordered self-compare in IR', IRContains(IR, 'cuod'));
end;

procedure TMathTests.TestCodegen_IsInfinite_EmitsIsinf;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X: Double; B: Boolean; begin B := IsInfinite(X) end.');
  AssertTrue('inline |x| bit compare in IR', IRContains(IR, 'ceql'));
  AssertTrue('exponent mask in IR', IRContains(IR, '9218868437227405312'));
end;


procedure TMathTests.TestCodegen_ConstDoubleArray_EmitsFloatDataItems;
var IR: string;
begin
  { 'l 0.25' is invalid QBE (parser reads 'l 0' and chokes); Double
    elements must be 'd d_...' data items }
  IR := GenIRBuiltin(
    'program P; const C: array[0..1] of Double = (0.25, 0.5); ' +
    'var X: Double; begin X := C[0] end.');
  AssertTrue('float data item in IR', IRContains(IR, 'd d_0.25'));
end;

procedure TMathTests.TestCodegen_VarParamDouble_LoadsWithLoadd;
var IR: string;
begin
  { reading a var Double param used to emit '=w loadw' -- a 32-bit
    integer load of half the double, and invalid as a d call arg }
  IR := GenIRBuiltin(
    'program P; ' +
    'procedure Q(var V: Double); var X: Double; begin X := V end; ' +
    'var D: Double; begin Q(D) end.');
  AssertTrue('loadd for var double deref', IRContains(IR, 'loadd'));
end;

procedure TMathTests.TestCodegen_IndirectCall_RecordArg_UsesAggregateABI;
var IR: string;
begin
  { a record passed through a procedural VARIABLE must use the same
    :_ffi_<Name> aggregate ABI as a direct call -- the old bare 'l'
    pointer arg made the callee read its param registers as garbage
    (this is how punit's TRunSummary totals printed noise) }
  IR := GenIRBuiltin(
    'program P; ' +
    'type TR = record A, B: Integer; end; TH = procedure(const R: TR); ' +
    'procedure W(const R: TR); begin WriteLn(IntToStr(R.A)) end; ' +
    'var H: TH; V: TR; begin H := @W; H(V) end.');
  AssertTrue('aggregate arg on indirect call',
    IRContains(IR, '(:_ffi_TR '));
end;

{ ------------------------------------------------------------------ }
{ RTL unit — Min / Max                                                 }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Min_Integer_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Integer;
    begin R := Min(A, B) end.
    ''');
end;

procedure TMathTests.TestSemantic_Max_Integer_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Integer;
    begin R := Max(A, B) end.
    ''');
end;

procedure TMathTests.TestSemantic_Min_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Double;
    begin R := Min(A, B) end.
    ''');
end;

procedure TMathTests.TestSemantic_Max_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Double;
    begin R := Max(A, B) end.
    ''');
end;

procedure TMathTests.TestSemantic_Min_ReturnsInteger;
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
    Lexer := TLexer.Create(
      'program P; uses Math; var A, B, R: Integer; begin R := Min(A, B) end.');
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
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Integer', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Max_ReturnsDouble;
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
    Lexer := TLexer.Create(
      'program P; uses Math; var A, B, R: Double; begin R := Max(A, B) end.');
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
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Double', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ RTL unit — Sign                                                      }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Sign_Integer_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var X, R: Integer;
    begin R := Sign(X) end.
    ''');
end;

procedure TMathTests.TestSemantic_Sign_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var X: Double; R: Integer;
    begin R := Sign(X) end.
    ''');
end;

procedure TMathTests.TestSemantic_Sign_ReturnsInteger;
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
    Lexer := TLexer.Create(
      'program P; uses Math; var X: Double; R: Integer; begin R := Sign(X) end.');
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
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Integer', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ RTL unit — DivMod                                                    }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_DivMod_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var D, V, Q, R: Integer;
    begin DivMod(D, V, Q, R) end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ RTL unit — InRange                                                   }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_InRange_Integer_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var V, Lo, Hi: Integer; B: Boolean;
    begin B := InRange(V, Lo, Hi) end.
    ''');
end;

procedure TMathTests.TestSemantic_InRange_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var V, Lo, Hi: Double; B: Boolean;
    begin B := InRange(V, Lo, Hi) end.
    ''');
end;

procedure TMathTests.TestSemantic_InRange_ReturnsBoolean;
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
    Lexer := TLexer.Create(
      'program P; uses Math; var V, Lo, Hi: Integer; B: Boolean; begin B := InRange(V, Lo, Hi) end.');
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
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Boolean', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ RTL unit — EnsureRange                                               }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_EnsureRange_Integer_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var V, Lo, Hi, R: Integer;
    begin R := EnsureRange(V, Lo, Hi) end.
    ''');
end;

procedure TMathTests.TestSemantic_EnsureRange_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var V, Lo, Hi, R: Double;
    begin R := EnsureRange(V, Lo, Hi) end.
    ''');
end;

procedure TMathTests.TestSemantic_EnsureRange_Integer_ReturnsInteger;
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
    Lexer := TLexer.Create(
      'program P; uses Math; var V, Lo, Hi, R: Integer; begin R := EnsureRange(V, Lo, Hi) end.');
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
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Integer', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Pi constant                                                          }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Pi_UsableInExpr;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var R: Double;
    begin R := Pi * 2.0 end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ Codegen — RTL functions                                              }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestCodegen_Min_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P; uses Math;
    var A, B, R: Integer;
    begin R := Min(A, B) end.
    ''');
  AssertTrue('Math_Min in IR', IRContains(IR, 'Min'));
end;

procedure TMathTests.TestCodegen_Max_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P; uses Math;
    var A, B, R: Double;
    begin R := Max(A, B) end.
    ''');
  AssertTrue('Math_Max in IR', IRContains(IR, 'Max'));
end;

procedure TMathTests.TestCodegen_Sign_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P; uses Math;
    var X, R: Integer;
    begin R := Sign(X) end.
    ''');
  AssertTrue('Math_Sign in IR', IRContains(IR, 'Sign'));
end;

{ ------------------------------------------------------------------ }
{ Float ↔ Integer assignment type checking                            }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Assign_DoubleToInteger_Rejected;
begin
  SemanticError(
    '''
    program P;
    var E: Integer; D: Double;
    begin E := D end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_SingleToInteger_Rejected;
begin
  SemanticError(
    '''
    program P;
    var E: Integer; S: Single;
    begin E := S end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_IntegerToDouble_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var D: Double; I: Integer;
    begin D := I end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_IntegerToSingle_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var S: Single; I: Integer;
    begin S := I end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_DoubleToDouble_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var A, B: Double;
    begin B := A end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_SingleToSingle_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var A, B: Single;
    begin B := A end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_SingleToDouble_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var S: Single; D: Double;
    begin D := S end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ `/` is real division (Pascal-standard semantics)                    }
{ `/` always yields a float, even with Integer operands.  `div` is    }
{ the integer-division operator.                                      }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_RealDiv_IntegerIntegerReturnsDouble;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create(
      'program P; var X, Y: Integer; R: Double; begin R := Y / X end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('Y / X type', 'Double', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_RealDiv_IntegerDoubleReturnsDouble;
begin
  SemanticOKBuiltin(
    'program P; var X: Integer; Y, R: Double; begin R := X / Y end.');
end;

procedure TMathTests.TestSemantic_RealDiv_AsTruncArg_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, Y: Integer; R: Integer; begin R := Trunc(Y / X) end.');
end;

procedure TMathTests.TestSemantic_RealDiv_AsRoundArg_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, Y: Integer; R: Integer; begin R := Round(Y / X) end.');
end;

procedure TMathTests.TestSemantic_IntegerDiv_RejectsFloat;
begin
  SemanticError(
    'program P; var X, Y: Double; R: Integer; begin R := Trunc(Y div X) end.');
end;

procedure TMathTests.TestCodegen_RealDiv_IntegerOperands_EmitsFloatDiv;
var IR: string;
begin
  IR := GenIRBuiltin(
    'program P; var X, Y: Integer; R: Double; begin R := Y / X end.');
  { Float division uses QBE's `div` with type d, after promoting both Integer
    operands to Double via swtof. }
  AssertTrue('swtof in IR (integer→double promotion)', IRContains(IR, 'swtof'));
  AssertTrue('float div in IR', IRContains(IR, '=d div'));
end;

initialization
  RegisterTest(TMathTests);

end.
