{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.math;

{ IR-level tests for Math unit functions and math compiler builtins.

  Builtins (handled in uSemantic + the code generators, no RTL unit needed):
    Abs, Sqrt, Ceil, Floor, Round, Trunc, Ln, Exp, Expm1, Log2, Log10,
    Power, Sin, Cos, Tan, ArcTan, ArcTan2, IsNaN, IsInfinite.

  RTL unit (math.pas, resolved via TUnitLoader):
    Min, Max, Sign, DivMod, InRange, EnsureRange, Pi. }

interface

uses
  SysUtils, Classes, contnrs, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uUnitLoader,
  blaise.codegen.native, blaise.codegen.target, cp.test.harness;

type
  TMathTests = class(TTestCase)
  private
    FRTLUnitPath: string;
    FStdlibUnitPath: string;
    procedure SemanticOK(const ASrc: string);
    procedure SemanticOKBuiltin(const ASrc: string);
    procedure SemanticError(const ASrc: string);
    function MathResultType(const ASrc: string): string;
    function MathGenAsm(const ASrc, ATarget: string): string;
    function MathAsmMissing(const ASrc, AX86, AArm64: string): string;
  protected
    procedure SetUp; override;
  published
    { --- Builtins and the Math unit --- }
    { Sin, Ln, Power, IsNaN ... live in the Math unit: calling one without
      'uses Math' is an error that names the unit }
    procedure TestSemantic_MathRoutineWithoutUses_NamesTheUnit;
    { ...and the names are no longer reserved: a program may declare its
      own Sin, which is the one it calls }
    procedure TestSemantic_OwnSinDeclarable;
    { Sqrt and Abs remain builtins, available with no uses clause }
    procedure TestSemantic_SqrtAbs_NeedNoUnit;
    { ArcTan2 is a Float32 and a Float64 overload: two Float32 arguments
      give Float32, a mixed pair Float64 }
    procedure TestSemantic_ArcTan2_OverloadResultTypes;

    { --- Compiler builtins: semantic type checking --- }

    { Sqrt }
    procedure TestSemantic_Sqrt_Double_OK;
    procedure TestSemantic_Sqrt_Single_OK;
    procedure TestSemantic_Sqrt_ReturnsDouble;
    procedure TestSemantic_Sqrt_IntegerArg_Accepted;

    { Ceil / Floor / Round / Trunc → Int64 }
    procedure TestSemantic_Ceil_OK;
    procedure TestSemantic_Ceil_ReturnsInt64;
    procedure TestSemantic_Floor_OK;
    procedure TestSemantic_Floor_ReturnsInt64;
    procedure TestSemantic_Round_OK;
    procedure TestSemantic_Round_ReturnsInt64;
    { Round rounds half to EVEN (banker's), as Delphi and FPC do: one
      round-to-nearest conversion on each ISA, for Double and Single }
    procedure TestCodegen_Round_TiesToEvenConversion;
    { Every float math builtin dispatches through one shared helper per
      arity in the x86-64 backend, used by both the float emitter and the
      rax-value context.  A builtin wired into only one context is how
      float Abs once returned its argument unchanged. }
    procedure TestCodegen_FloatMath_SingleDispatch;
    procedure TestSemantic_Trunc_OK;
    procedure TestSemantic_Trunc_ReturnsInt64;
    procedure TestSemantic_Ceil_IntegerArg_Accepted;

    { Integer arguments to float builtins coerce to Double (FPC/Delphi
      semantics; consistent with implicit int->float assignment). }
    procedure TestSemantic_Trig_IntegerArg_Accepted;
    procedure TestSemantic_Trig_IntegerArg_ReturnsDouble;

    { Float typecasts must emit real conversions, not bit copies. }

    { Ln / Log2 / Log10 → Double }
    procedure TestSemantic_Ln_OK;
    procedure TestSemantic_Ln_ReturnsDouble;
    procedure TestSemantic_Log2_OK;
    procedure TestSemantic_Log10_OK;

    { Exp → the argument's float type (issue #252: it was missing from the
      front end while _BlaiseExp existed in runtime.math) }
    procedure TestSemantic_Exp_OK;
    procedure TestSemantic_Exp_ReturnsDouble;
    procedure TestSemantic_Exp_Single_ReturnsSingle;
    procedure TestSemantic_Exp_IntegerArg_Accepted;
    procedure TestSemantic_Exp_IntegerArg_ReturnsDouble;
    procedure TestSemantic_Exp_TwoArgs_Rejected;
    procedure TestSemantic_Exp_ZeroArgs_Rejected;
    procedure TestSemantic_Exp_StringArg_Rejected;
    { Exp lowers to the pure-Pascal _BlaiseExp on both ISAs, from the float
      emitter AND the rax-value context (float array element writes) }
    procedure TestCodegen_Exp_CallSymbolBothISAs;
    procedure TestCodegen_Exp_FloatElemStore_RaxContext;
    { Exp(Single) widens, computes in double, narrows back to Single }
    procedure TestCodegen_Exp_Single_RoundsThroughDouble;

    { Expm1 — exp(x) - 1, wired with Exp (issue #252's optional extra) }
    procedure TestSemantic_Expm1_OK;
    procedure TestSemantic_Expm1_ReturnsDouble;
    procedure TestSemantic_Expm1_Single_ReturnsSingle;
    procedure TestSemantic_Expm1_IntegerArg_Accepted;
    procedure TestSemantic_Expm1_IntegerArg_ReturnsDouble;
    procedure TestSemantic_Expm1_TwoArgs_Rejected;
    procedure TestSemantic_Expm1_ZeroArgs_Rejected;
    procedure TestSemantic_Expm1_StringArg_Rejected;
    procedure TestCodegen_Expm1_CallSymbolBothISAs;

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
    { QBE codegen regression guards found during the libm removal }

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
    procedure TestSemantic_Sign_ReturnsInt;

    { DivMod }
    procedure TestSemantic_DivMod_OK;

    { InRange }
    procedure TestSemantic_InRange_Integer_OK;
    procedure TestSemantic_InRange_Double_OK;
    procedure TestSemantic_InRange_ReturnsBoolean;

    { EnsureRange }
    procedure TestSemantic_EnsureRange_Integer_OK;
    procedure TestSemantic_EnsureRange_Double_OK;
    procedure TestSemantic_EnsureRange_Int_ReturnsInt;

    { Pi constant }
    procedure TestSemantic_Pi_UsableInExpr;

    { Frac / DegToRad / RadToDeg (GH #266): each has a Float32 and a
      Float64 overload, so the result keeps the argument's precision, and
      an integer argument widens to Float64 }
    procedure TestSemantic_Frac_Float64_ReturnsFloat64;
    procedure TestSemantic_Frac_Float32_ReturnsFloat32;
    procedure TestSemantic_Frac_IntegerArg_ReturnsFloat64;
    procedure TestSemantic_Frac_StringArg_Rejected;
    procedure TestSemantic_DegToRad_ReturnsFloat64;
    procedure TestSemantic_DegToRad_Float32_ReturnsFloat32;
    procedure TestSemantic_RadToDeg_ReturnsFloat64;
    { `mod` takes float operands (C fmod) and is typed like the other
      float arithmetic: Float32 mod Float32 is Float32, anything with a
      Float64 or an integer beside a float is Float64; integer mod stays
      integer; a float mod folds in a constant (GH #266) }
    procedure TestSemantic_FloatMod_Float64_ReturnsFloat64;
    procedure TestSemantic_FloatMod_Float32_ReturnsFloat32;
    procedure TestSemantic_FloatMod_IntAndFloat_ReturnsFloat64;
    procedure TestSemantic_IntMod_StaysInteger;
    procedure TestSemantic_FloatMod_ConstFolds;
    procedure TestSemantic_FloatMod_ConstByZero_Rejected;
    { both ISAs call the RTL kernel, for Float64 and Float32 }
    procedure TestCodegen_FloatMod_CallsFModBothISAs;

    { Codegen — RTL functions appear in IR }

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
  I:           Int;
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
  Lexer: TLexer;
  Parser: TParser;
  Prog: TProgram;
  Semantic: TSemanticAnalyser;
  Loader: TUnitLoader;
  Units: TObjectList;
  SearchPaths: TStringList;
  I: Int;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units := nil; SearchPaths := nil;
  try
    try
      Lexer := TLexer.Create(ASrc);
      Parser := TParser.Create(Lexer);
      Prog := Parser.Parse();
      Semantic := TSemanticAnalyser.Create();
      SearchPaths := TStringList.Create();
      SearchPaths.Add(FRTLUnitPath);
      SearchPaths.Add(FStdlibUnitPath);
      Loader := TUnitLoader.Create(SearchPaths);
      Units := Loader.LoadAll(Prog.UsedUnits);
      { a unit that fails to analyse is a harness failure, not the
        expected error, so it is analysed outside the expectation }
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

{ Analyses ASrc with the Math unit loaded and returns the name of the
  resolved type of the first statement, which must be an assignment. }
function TMathTests.MathResultType(const ASrc: string): string;
var
  Lexer: TLexer;
  Parser: TParser;
  Prog: TProgram;
  Semantic: TSemanticAnalyser;
  Loader: TUnitLoader;
  Units: TObjectList;
  SearchPaths: TStringList;
  Assign: TAssignment;
  I: Int;
begin
  Result := '';
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units := nil; SearchPaths := nil;
  try
    Lexer := TLexer.Create(ASrc);
    Parser := TParser.Create(Lexer);
    Prog := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    Result := Assign.Expr.ResolvedType.Name;
  finally
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ The assembly of the PROGRAM in ASrc, generated for ATarget after the
  units it uses (Math, SysUtils) are loaded and analysed from the source
  tree -- the unit-aware counterpart of the harness's GenAsm. }
function TMathTests.MathGenAsm(const ASrc, ATarget: string): string;
var
  Lexer: TLexer;
  Parser: TParser;
  Prog: TProgram;
  Semantic: TSemanticAnalyser;
  Loader: TUnitLoader;
  Units: TObjectList;
  SearchPaths: TStringList;
  CG: TCodeGenNative;
  Saved, Target: TTargetDesc;
  I: Int;
begin
  if not ParseTargetName(ATarget, Target) then
    Fail('unknown target ' + ATarget);
  Saved := GTarget;
  GTarget := Target;
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units := nil; SearchPaths := nil; CG := nil;
  try
    Lexer := TLexer.Create(ASrc);
    Parser := TParser.Create(Lexer);
    Prog := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    CG := TCodeGenNative.Create();
    CG.SetTarget(Target);
    CG.SetSymbolTable(Prog.SymbolTable);
    CG.Generate(Prog);
    Result := CG.GetOutput();
  finally
    GTarget := Saved;
    CG.Free();
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

{ '' when the program's x86-64 assembly contains AX86 and its arm64
  assembly AArm64, else the targets that lack theirs (as AsmMissing) }
function TMathTests.MathAsmMissing(const ASrc, AX86, AArm64: string): string;
begin
  Result := '';
  if Pos(AX86, MathGenAsm(ASrc, TargetX86_64)) < 0 then
    Result := TargetX86_64 + ' lacks [' + AX86 + ']';
  if Pos(AArm64, MathGenAsm(ASrc, TargetArm64)) < 0 then
  begin
    if Result <> '' then
      Result := Result + '; ';
    Result := Result + TargetArm64 + ' lacks [' + AArm64 + ']';
  end;
end;

{ ------------------------------------------------------------------ }
{ Sqrt                                                                 }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Sqrt_Double_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Float64; begin R := Sqrt(X) end.');
end;

procedure TMathTests.TestSemantic_Sqrt_Single_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, R: Float32; begin R := Sqrt(X) end.');
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
    Lexer    := TLexer.Create('program P; var X, R: Float64; begin R := Sqrt(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Float64', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Sqrt_IntegerArg_Accepted;
begin
  SemanticOKBuiltin('program P; var X: Int; R: Float64; begin R := Sqrt(X) end.');
end;

{ ------------------------------------------------------------------ }
{ Ceil / Floor / Round / Trunc                                         }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Ceil_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Float64; R: Int; begin R := Ceil(X) end.');
end;

procedure TMathTests.TestSemantic_Ceil_ReturnsInt64;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Float64; R: Int; begin R := Ceil(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Int64', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Floor_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Float64; R: Int; begin R := Floor(X) end.');
end;

procedure TMathTests.TestSemantic_Floor_ReturnsInt64;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Float64; R: Int; begin R := Floor(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Int64', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Round_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Float64; R: Int; begin R := Round(X) end.');
end;

procedure TMathTests.TestSemantic_Round_ReturnsInt64;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Float64; R: Int; begin R := Round(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Int64', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Trunc_OK;
begin
  SemanticOKBuiltin(
    'program P; var X: Float64; R: Int; begin R := Trunc(X) end.');
end;

procedure TMathTests.TestSemantic_Trunc_ReturnsInt64;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  Assign:   TAssignment;
begin
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  try
    Lexer    := TLexer.Create('program P; var X: Float64; R: Int; begin R := Trunc(X) end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type', 'Int64', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_Ceil_IntegerArg_Accepted;
begin
  SemanticOKBuiltin('program P; var X: Int; R: Int; begin R := Ceil(X) end.');
end;

procedure TMathTests.TestSemantic_Trig_IntegerArg_Accepted;
begin
  SemanticOK('program P; uses Math; var I: Int; D: Float64; begin D := Tanh(I) end.');
  SemanticOK('program P; uses Math; var D: Float64; begin D := Sin(12) end.');
  SemanticOK('program P; uses Math; var I: Int; D: Float64; begin D := ArcTan2(I, I) end.');
end;

procedure TMathTests.TestSemantic_Trig_IntegerArg_ReturnsDouble;
begin
  { The result of a trig builtin on an integer argument is Double — it must
    be assignable to a Double without error (and to a Single via implicit
    narrowing on assignment). }
  SemanticOK('program P; uses Math; var S: Float32; begin S := Sin(12) end.');
end;

{ ------------------------------------------------------------------ }
{ Ln / Log2 / Log10                                                    }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Ln_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Ln(X) end.');
end;

procedure TMathTests.TestSemantic_Ln_ReturnsDouble;
begin
  AssertEquals('return type', 'Float64', MathResultType(
    'program P; uses Math; var X, R: Float64; begin R := Ln(X) end.'));
end;

procedure TMathTests.TestSemantic_Log2_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Log2(X) end.');
end;

procedure TMathTests.TestSemantic_Log10_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Log10(X) end.');
end;

procedure TMathTests.TestSemantic_Exp_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Exp(X) end.');
end;

procedure TMathTests.TestSemantic_Exp_ReturnsDouble;
begin
  AssertEquals('return type', 'Float64', MathResultType(
    'program P; uses Math; var X, R: Float64; begin R := Exp(X) end.'));
end;

procedure TMathTests.TestSemantic_Exp_Single_ReturnsSingle;
begin
  AssertEquals('return type', 'Float32', MathResultType(
    'program P; uses Math; var X, R: Float32; begin R := Exp(X) end.'));
end;

procedure TMathTests.TestSemantic_Exp_IntegerArg_Accepted;
begin
  SemanticOK(
    'program P; uses Math; var I: Int; R: Float64; begin R := Exp(I) end.');
end;

procedure TMathTests.TestSemantic_Exp_IntegerArg_ReturnsDouble;
begin
  AssertEquals('return type', 'Float64', MathResultType(
    'program P; uses Math; var I: Int; R: Float64; begin R := Exp(I) end.'));
end;

procedure TMathTests.TestSemantic_Exp_TwoArgs_Rejected;
begin
  SemanticError(
    'program P; var X, Y, R: Float64; begin R := Exp(X, Y) end.');
end;

procedure TMathTests.TestSemantic_Exp_ZeroArgs_Rejected;
begin
  SemanticError(
    'program P; var R: Float64; begin R := Exp() end.');
end;

procedure TMathTests.TestSemantic_Exp_StringArg_Rejected;
begin
  SemanticError(
    'program P; var S: string; R: Float64; begin R := Exp(S) end.');
end;

procedure TMathTests.TestCodegen_Exp_CallSymbolBothISAs;
const
  Src = '''
    program P; uses Math;
    var X, R: Float64;
    begin
      R := Exp(X)
    end.
    ''';
begin
  { both dispatch contexts call the same helper; a float-variable
    assignment covers the float emitter }
  AssertEquals('Exp', '',
    MathAsmMissing(Src, #9'callq _BlaiseExp', #9'bl __BlaiseExp'));
end;

procedure TMathTests.TestCodegen_Exp_FloatElemStore_RaxContext;
const
  Src = '''
    program P; uses Math;
    var X: Float64; A: array[0..1] of Float64;
    begin
      A[0] := Exp(X)
    end.
    ''';
var
  X86, Arm: string;
begin
  { a float ARRAY ELEMENT STORE evaluates the RHS through the rax-value
    context: the float-math dispatch must APPROACH here too (it fell
    through to the integer path once for Abs, issue #252's wiring plan);
    the x86-64 result is spilled through %rax into %xmm0 }
  X86 := MathGenAsm(Src, TargetX86_64);
  Arm := MathGenAsm(Src, TargetArm64);
  AssertTrue('x86-64: RTL exp call', Pos(#9'callq _BlaiseExp', X86) > 0);
  AssertTrue('x86-64: float bit pattern spilled through rax',
    Pos(#9'movq %xmm0, %rax', X86) > 0);
  AssertTrue('arm64: RTL exp call', Pos(#9'bl __BlaiseExp', Arm) > 0);
end;

procedure TMathTests.TestCodegen_Exp_Single_RoundsThroughDouble;
const
  SrcS = '''
    program P; uses Math;
    var X, R: Float32;
    begin
      R := Exp(X)
    end.
    ''';
  SrcD = '''
    program P; uses Math;
    var X, R: Float64;
    begin
      R := Exp(X)
    end.
    ''';
begin
  { A Float32 argument calls Math's Float32 overload, which widens,
    calls the kernel and rounds once (TE2EMathTests.TestRun_Exp_SingleArg
    checks the value); a Float64 one calls the kernel itself, as the
    overload is bound to it by external name -- no wrapper in between. }
  AssertEquals('Float32 -> the Float32 overload', '',
    MathAsmMissing(SrcS, #9'callq Math_Exp_D_s', #9'bl _Math_Exp_D_s'));
  AssertTrue('Float32 does not call the kernel directly',
    Pos(#9'callq _BlaiseExp', MathGenAsm(SrcS, TargetX86_64)) < 0);
  AssertEquals('Float64 -> the kernel directly', '',
    MathAsmMissing(SrcD, #9'callq _BlaiseExp', #9'bl __BlaiseExp'));
end;

{ ------------------------------------------------------------------ }
{ Expm1                                                              }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Expm1_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Expm1(X) end.');
end;

procedure TMathTests.TestSemantic_Expm1_ReturnsDouble;
begin
  AssertEquals('return type', 'Float64', MathResultType(
    'program P; uses Math; var X, R: Float64; begin R := Expm1(X) end.'));
end;

procedure TMathTests.TestSemantic_Expm1_Single_ReturnsSingle;
begin
  AssertEquals('return type', 'Float32', MathResultType(
    'program P; uses Math; var X, R: Float32; begin R := Expm1(X) end.'));
end;

procedure TMathTests.TestSemantic_Expm1_IntegerArg_Accepted;
begin
  SemanticOK(
    'program P; uses Math; var I: Int; R: Float64; begin R := Expm1(I) end.');
end;

procedure TMathTests.TestSemantic_Expm1_IntegerArg_ReturnsDouble;
begin
  AssertEquals('return type', 'Float64', MathResultType(
    'program P; uses Math; var I: Int; R: Float64; begin R := Expm1(I) end.'));
end;

procedure TMathTests.TestSemantic_Expm1_TwoArgs_Rejected;
begin
  SemanticError(
    'program P; var X, Y, R: Float64; begin R := Expm1(X, Y) end.');
end;

procedure TMathTests.TestSemantic_Expm1_ZeroArgs_Rejected;
begin
  SemanticError(
    'program P; var R: Float64; begin R := Expm1() end.');
end;

procedure TMathTests.TestSemantic_Expm1_StringArg_Rejected;
begin
  SemanticError(
    'program P; var S: string; R: Float64; begin R := Expm1(S) end.');
end;

procedure TMathTests.TestCodegen_Expm1_CallSymbolBothISAs;
const
  Src = '''
    program P; uses Math;
    var X, R: Float64;
    begin
      R := Expm1(X)
    end.
    ''';
begin
  AssertEquals('Expm1', '',
    MathAsmMissing(Src, #9'callq _BlaiseExpm1', #9'bl __BlaiseExpm1'));
end;

{ ------------------------------------------------------------------ }
{ Power                                                                }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Power_OK;
begin
  SemanticOK(
    'program P; uses Math; var B, E, R: Float64; begin R := Power(B, E) end.');
end;

procedure TMathTests.TestSemantic_Power_ReturnsDouble;
begin
  AssertEquals('return type', 'Float64', MathResultType(
    'program P; uses Math; var B, E, R: Float64; begin R := Power(B, E) end.'));
end;

{ ------------------------------------------------------------------ }
{ Trig                                                                 }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Sin_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Sin(X) end.');
end;

procedure TMathTests.TestSemantic_Cos_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Cos(X) end.');
end;

procedure TMathTests.TestSemantic_Tan_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Tan(X) end.');
end;

procedure TMathTests.TestSemantic_ArcTan_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := ArcTan(X) end.');
end;

procedure TMathTests.TestSemantic_ArcTan2_OK;
begin
  SemanticOK(
    'program P; uses Math; var Y, X, R: Float64; begin R := ArcTan2(Y, X) end.');
end;

procedure TMathTests.TestSemantic_Sin_ReturnsDouble;
begin
  AssertEquals('return type', 'Float64', MathResultType(
    'program P; uses Math; var X, R: Float64; begin R := Sin(X) end.'));
end;

procedure TMathTests.TestSemantic_Sin_Single_ReturnsSingle;
begin
  AssertEquals('return type', 'Float32', MathResultType(
    'program P; uses Math; var X, R: Float32; begin R := Sin(X) end.'));
end;

procedure TMathTests.TestSemantic_ArcSin_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := ArcSin(X) end.');
end;

procedure TMathTests.TestSemantic_ArcCos_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := ArcCos(X) end.');
end;

procedure TMathTests.TestSemantic_Sinh_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Sinh(X) end.');
end;

procedure TMathTests.TestSemantic_Cosh_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Cosh(X) end.');
end;

procedure TMathTests.TestSemantic_Tanh_OK;
begin
  SemanticOK(
    'program P; uses Math; var X, R: Float64; begin R := Tanh(X) end.');
end;

procedure TMathTests.TestSemantic_Sinh_Single_ReturnsSingle;
begin
  AssertEquals('return type', 'Float32', MathResultType(
    'program P; uses Math; var X, R: Float32; begin R := Sinh(X) end.'));
end;

{ ------------------------------------------------------------------ }
{ IsNaN / IsInfinite                                                   }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_IsNaN_OK;
begin
  SemanticOK(
    'program P; uses Math; var X: Float64; B: Boolean; begin B := IsNaN(X) end.');
end;

procedure TMathTests.TestSemantic_IsNaN_ReturnsBoolean;
begin
  AssertEquals('return type', 'Boolean', MathResultType(
    'program P; uses Math; var X: Float64; B: Boolean; begin B := IsNaN(X) end.'));
end;

procedure TMathTests.TestSemantic_IsInfinite_OK;
begin
  SemanticOK(
    'program P; uses Math; var X: Float64; B: Boolean; begin B := IsInfinite(X) end.');
end;

procedure TMathTests.TestSemantic_IsInfinite_ReturnsBoolean;
begin
  AssertEquals('return type', 'Boolean', MathResultType(
    'program P; uses Math; var X: Float64; B: Boolean; begin B := IsInfinite(X) end.'));
end;

{ ------------------------------------------------------------------ }
{ Codegen — builtins                                                   }
{ ------------------------------------------------------------------ }


{ ------------------------------------------------------------------ }
{ RTL unit — Min / Max                                                 }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Min_Integer_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Int;
    begin R := Min(A, B) end.
    ''');
end;

procedure TMathTests.TestSemantic_Max_Integer_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Int;
    begin R := Max(A, B) end.
    ''');
end;

procedure TMathTests.TestSemantic_Min_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Float64;
    begin R := Min(A, B) end.
    ''');
end;

procedure TMathTests.TestSemantic_Max_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var A, B, R: Float64;
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
  I:           Int;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer := TLexer.Create(
      'program P; uses Math; var A, B, R: Int32; begin R := Min(A, B) end.');
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
    AssertEquals('return type', 'Int32', Assign.Expr.ResolvedType.Name);
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
  I:           Int;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer := TLexer.Create(
      'program P; uses Math; var A, B, R: Float64; begin R := Max(A, B) end.');
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
    AssertEquals('return type', 'Float64', Assign.Expr.ResolvedType.Name);
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
    var X, R: Int;
    begin R := Sign(X) end.
    ''');
end;

procedure TMathTests.TestSemantic_Sign_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var X: Float64; R: Int;
    begin R := Sign(X) end.
    ''');
end;

procedure TMathTests.TestSemantic_Sign_ReturnsInt;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Int;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer := TLexer.Create(
      'program P; uses Math; var X: Float64; R: Int; begin R := Sign(X) end.');
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
    AssertEquals('return type', 'Int64', Assign.Expr.ResolvedType.Name);
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
    var D, V, Q, R: Int;
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
    var V, Lo, Hi: Int; B: Boolean;
    begin B := InRange(V, Lo, Hi) end.
    ''');
end;

procedure TMathTests.TestSemantic_InRange_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var V, Lo, Hi: Float64; B: Boolean;
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
  I:           Int;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer := TLexer.Create(
      'program P; uses Math; var V, Lo, Hi: Int; B: Boolean; begin B := InRange(V, Lo, Hi) end.');
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
    var V, Lo, Hi, R: Int;
    begin R := EnsureRange(V, Lo, Hi) end.
    ''');
end;

procedure TMathTests.TestSemantic_EnsureRange_Double_OK;
begin
  SemanticOK(
    '''
    program P; uses Math;
    var V, Lo, Hi, R: Float64;
    begin R := EnsureRange(V, Lo, Hi) end.
    ''');
end;

procedure TMathTests.TestSemantic_EnsureRange_Int_ReturnsInt;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Assign:      TAssignment;
  I:           Int;
begin
  Lexer  := nil; Parser := nil; Prog := nil; Semantic := nil;
  Loader := nil; Units  := nil; SearchPaths := nil;
  try
    Lexer := TLexer.Create(
      'program P; uses Math; var V, Lo, Hi, R: Int; begin R := EnsureRange(V, Lo, Hi) end.');
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
    AssertEquals('return type', 'Int64', Assign.Expr.ResolvedType.Name);
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
    var R: Float64;
    begin R := Pi * 2.0 end.
    ''');
end;

{ ------------------------------------------------------------------ }
{ Float ↔ Integer assignment type checking                            }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Assign_DoubleToInteger_Rejected;
begin
  SemanticError(
    '''
    program P;
    var E: Int; D: Float64;
    begin E := D end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_SingleToInteger_Rejected;
begin
  SemanticError(
    '''
    program P;
    var E: Int; S: Float32;
    begin E := S end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_IntegerToDouble_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var D: Float64; I: Int;
    begin D := I end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_IntegerToSingle_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var S: Float32; I: Int;
    begin S := I end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_DoubleToDouble_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var A, B: Float64;
    begin B := A end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_SingleToSingle_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var A, B: Float32;
    begin B := A end.
    ''');
end;

procedure TMathTests.TestSemantic_Assign_SingleToDouble_OK;
begin
  SemanticOKBuiltin(
    '''
    program P;
    var S: Float32; D: Float64;
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
      'program P; var X, Y: Int; R: Float64; begin R := Y / X end.');
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNil('resolved type', Assign.Expr.ResolvedType);
    AssertEquals('Y / X type', 'Float64', Assign.Expr.ResolvedType.Name);
  finally
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free();
  end;
end;

procedure TMathTests.TestSemantic_RealDiv_IntegerDoubleReturnsDouble;
begin
  SemanticOKBuiltin(
    'program P; var X: Int; Y, R: Float64; begin R := X / Y end.');
end;

procedure TMathTests.TestSemantic_RealDiv_AsTruncArg_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, Y: Int; R: Int; begin R := Trunc(Y / X) end.');
end;

procedure TMathTests.TestSemantic_RealDiv_AsRoundArg_OK;
begin
  SemanticOKBuiltin(
    'program P; var X, Y: Int; R: Int; begin R := Round(Y / X) end.');
end;

procedure TMathTests.TestSemantic_IntegerDiv_RejectsFloat;
begin
  SemanticError(
    'program P; var X, Y: Float64; R: Int; begin R := Trunc(Y div X) end.');
end;

procedure TMathTests.TestCodegen_Round_TiesToEvenConversion;
const
  Src = '''
    program P;
    var D: Float64; S: Float32; R: Int64;
    begin
      R := Round(D);
      R := Round(S)
    end.
    ''';
begin
  AssertEquals('Float64', '', AsmMissing(Src, #9'cvtsd2si %xmm0, %rax', #9'fcvtns x0, d0'));
  AssertEquals('Float32', '', AsmMissing(Src, #9'cvtss2si %xmm0, %rax', #9'fcvtns x0, d0'));
  AssertTrue('x86-64: no half-away helper',
    Pos('_BlaiseRoundD', GenAsm(Src, TargetX86_64)) < 0);
  AssertTrue('arm64: no half-away helper',
    Pos('_BlaiseRoundD', GenAsm(Src, TargetArm64)) < 0);
end;

procedure TMathTests.TestCodegen_FloatMath_SingleDispatch;
const
  Src = '''
    program P; uses Math;
    var X, Y, R: Float64;
    begin
      R := Sin(X);
      R := Cos(X);
      R := Tan(X);
      R := ArcTan(X);
      R := ArcSin(X);
      R := ArcCos(X);
      R := Ln(X);
      R := Log2(X);
      R := Log10(X);
      R := Sinh(X);
      R := Cosh(X);
      R := Tanh(X);
      R := Abs(X);
      R := Sqrt(X);
      R := ArcTan2(X, Y);
      R := Power(X, Y)
    end.
    ''';
begin
  AssertEquals('Sin', '',
    MathAsmMissing(Src, #9'callq _BlaiseSin', #9'bl __BlaiseSin'));
  AssertEquals('Cos', '',
    MathAsmMissing(Src, #9'callq _BlaiseCos', #9'bl __BlaiseCos'));
  AssertEquals('Tan', '',
    MathAsmMissing(Src, #9'callq _BlaiseTan', #9'bl __BlaiseTan'));
  AssertEquals('ArcTan', '',
    MathAsmMissing(Src, #9'callq _BlaiseArcTan', #9'bl __BlaiseArcTan'));
  AssertEquals('ArcSin', '',
    MathAsmMissing(Src, #9'callq _BlaiseArcSin', #9'bl __BlaiseArcSin'));
  AssertEquals('ArcCos', '',
    MathAsmMissing(Src, #9'callq _BlaiseArcCos', #9'bl __BlaiseArcCos'));
  AssertEquals('Ln', '',
    MathAsmMissing(Src, #9'callq _BlaiseLn', #9'bl __BlaiseLn'));
  AssertEquals('Log2', '',
    MathAsmMissing(Src, #9'callq _BlaiseLog2', #9'bl __BlaiseLog2'));
  AssertEquals('Log10', '',
    MathAsmMissing(Src, #9'callq _BlaiseLog10', #9'bl __BlaiseLog10'));
  AssertEquals('Sinh', '',
    MathAsmMissing(Src, #9'callq _BlaiseSinh', #9'bl __BlaiseSinh'));
  AssertEquals('Cosh', '',
    MathAsmMissing(Src, #9'callq _BlaiseCosh', #9'bl __BlaiseCosh'));
  AssertEquals('Tanh', '',
    MathAsmMissing(Src, #9'callq _BlaiseTanh', #9'bl __BlaiseTanh'));
  AssertEquals('Abs', '',
    MathAsmMissing(Src, #9'callq _BlaiseFabs', #9'bl __BlaiseFabs'));
  { Sqrt is the one hardware lowering on x86-64; arm64 calls the RTL. }
  AssertEquals('Sqrt', '',
    MathAsmMissing(Src, #9'sqrtsd %xmm0, %xmm0', #9'bl __BlaiseSqrtD'));
  AssertEquals('ArcTan2', '',
    MathAsmMissing(Src, #9'callq _BlaiseArcTan2', #9'bl __BlaiseArcTan2'));
  AssertEquals('Power', '',
    MathAsmMissing(Src, #9'callq _BlaisePow', #9'bl __BlaisePow'));
end;


{ ------------------------------------------------------------------ }
{ Frac / DegToRad / RadToDeg (GH #266)                                 }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_Frac_Float64_ReturnsFloat64;
begin
  AssertEquals('Frac(Float64)', 'Float64', MathResultType(
    'program P; uses Math; var X, R: Float64; begin R := Frac(X) end.'));
end;

procedure TMathTests.TestSemantic_Frac_Float32_ReturnsFloat32;
begin
  AssertEquals('Frac(Float32)', 'Float32', MathResultType(
    'program P; uses Math; var X, R: Float32; begin R := Frac(X) end.'));
end;

procedure TMathTests.TestSemantic_Frac_IntegerArg_ReturnsFloat64;
begin
  AssertEquals('Frac(Int)', 'Float64', MathResultType(
    'program P; uses Math; var I: Int; R: Float64; begin R := Frac(I) end.'));
end;

procedure TMathTests.TestSemantic_Frac_StringArg_Rejected;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    SemanticOK('program P; uses Math; var R: Float64; begin R := Frac(''x'') end.');
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('Frac(string) is rejected', Raised);
end;

procedure TMathTests.TestSemantic_DegToRad_ReturnsFloat64;
begin
  AssertEquals('DegToRad(Float64)', 'Float64', MathResultType(
    'program P; uses Math; var X, R: Float64; begin R := DegToRad(X) end.'));
end;

procedure TMathTests.TestSemantic_DegToRad_Float32_ReturnsFloat32;
begin
  AssertEquals('DegToRad(Float32)', 'Float32', MathResultType(
    'program P; uses Math; var X, R: Float32; begin R := DegToRad(X) end.'));
end;

procedure TMathTests.TestSemantic_RadToDeg_ReturnsFloat64;
begin
  AssertEquals('RadToDeg(Float64)', 'Float64', MathResultType(
    'program P; uses Math; var X, R: Float64; begin R := RadToDeg(X) end.'));
end;

{ ------------------------------------------------------------------ }
{ Float mod (GH #266)                                                  }
{ ------------------------------------------------------------------ }

function ProgResultType(const ASrc: string): string;
var
  Prog: TProgram;
begin
  Prog := Analyse(ASrc);
  try
    Result := TAssignment(Prog.Block.Stmts.Items[0]).Expr.ResolvedType.Name;
  finally
    Prog.Free();
  end;
end;

procedure TMathTests.TestSemantic_FloatMod_Float64_ReturnsFloat64;
begin
  AssertEquals('Float64 mod Float64', 'Float64', ProgResultType(
    'program P; var X, Y, R: Float64; begin R := X mod Y end.'));
end;

procedure TMathTests.TestSemantic_FloatMod_Float32_ReturnsFloat32;
begin
  AssertEquals('Float32 mod Float32', 'Float32', ProgResultType(
    'program P; var X, Y, R: Float32; begin R := X mod Y end.'));
end;

procedure TMathTests.TestSemantic_FloatMod_IntAndFloat_ReturnsFloat64;
begin
  AssertEquals('Int mod Float32', 'Float64', ProgResultType(
    'program P; var I: Int; Y: Float32; R: Float64; begin R := I mod Y end.'));
  AssertEquals('Float64 mod literal', 'Float64', ProgResultType(
    'program P; var X, R: Float64; begin R := X mod 2 end.'));
end;

procedure TMathTests.TestSemantic_IntMod_StaysInteger;
begin
  AssertEquals('Int64 mod Int64', 'Int64', ProgResultType(
    'program P; var I, J, R: Int64; begin R := I mod J end.'));
end;

procedure TMathTests.TestSemantic_FloatMod_ConstFolds;
begin
  AssertEquals('const float mod', '', cp.test.harness.SemanticError(
    'program P; const C = 7.5 mod 2.0; D = -7.5 mod 2; ' +
    'var R: Float64; begin R := C + D end.'));
end;

procedure TMathTests.TestSemantic_FloatMod_ConstByZero_Rejected;
begin
  AssertTrue('const float mod by zero', Pos('Division by zero',
    cp.test.harness.SemanticError(
      'program P; const C = 7.5 mod 0.0; begin end.')) >= 0);
end;

procedure TMathTests.TestCodegen_FloatMod_CallsFModBothISAs;
begin
  AssertEquals('Float64 mod', '', AsmMissing(
    'program P; var X, Y, R: Float64; begin R := X mod Y end.',
    #9'callq _BlaiseFMod', #9'bl __BlaiseFMod'));
  AssertEquals('Float32 mod', '', AsmMissing(
    'program P; var X, Y, R: Float32; begin R := X mod Y end.',
    #9'callq _BlaiseFMod', #9'bl __BlaiseFMod'));
end;


{ ------------------------------------------------------------------ }
{ Builtins and the Math unit                                           }
{ ------------------------------------------------------------------ }

procedure TMathTests.TestSemantic_MathRoutineWithoutUses_NamesTheUnit;
var
  Err: string;
begin
  Err := cp.test.harness.SemanticError(
    'program P; var X: Float64; begin X := Sin(0.5) end.');
  AssertTrue('Sin: ' + Err, Pos('Undeclared function ''Sin'' (it is in unit Math: add ''uses Math'')', Err) >= 0);
  Err := cp.test.harness.SemanticError(
    'program P; var B: Boolean; begin B := IsNaN(0.5) end.');
  AssertTrue('IsNaN: ' + Err, Pos('in unit Math', Err) >= 0);
  Err := cp.test.harness.SemanticError(
    'program P; var Q, R: Int; begin DivMod(7, 2, Q, R) end.');
  AssertTrue('DivMod: ' + Err, Pos('Undeclared procedure ''DivMod'' (it is in unit Math', Err) >= 0);
  Err := cp.test.harness.SemanticError(
    'program P; var X: Float64; begin X := Sine(0.5) end.');
  AssertTrue('an unrelated name gets no hint: ' + Err, Pos('Math', Err) < 0);
end;

procedure TMathTests.TestSemantic_OwnSinDeclarable;
begin
  AssertEquals('own Sin', '', cp.test.harness.SemanticError(
    '''
    program P;
    function Sin(X: Float64): Float64;
    begin
      Result := X;
    end;
    var R: Float64;
    begin
      R := Sin(0.5)
    end.
    '''));
end;

procedure TMathTests.TestSemantic_SqrtAbs_NeedNoUnit;
begin
  AssertEquals('Sqrt, Abs, Trunc, Round, Floor, Ceil', '',
    cp.test.harness.SemanticError(
      'program P; var X: Float64; I: Int64; begin X := Sqrt(Abs(-2.0)); ' +
      'I := Trunc(X) + Round(X) + Floor(X) + Ceil(X) end.'));
end;

procedure TMathTests.TestSemantic_ArcTan2_OverloadResultTypes;
begin
  AssertEquals('Float32, Float32', 'Float32', MathResultType(
    'program P; uses Math; var Y, X, R: Float32; begin R := ArcTan2(Y, X) end.'));
  AssertEquals('Float32, Float64', 'Float64', MathResultType(
    'program P; uses Math; var Y: Float32; X, R: Float64; begin R := ArcTan2(Y, X) end.'));
end;

initialization
  RegisterTest(TMathTests);

end.
