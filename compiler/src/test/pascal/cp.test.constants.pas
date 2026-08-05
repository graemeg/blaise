{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.constants;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, blaise.codegen.qbe;

type
  TConstTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    function ParseUnit(const ASrc: string): TUnit;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    { Exported interface constant is visible in importing program }
    procedure TestExportedConstVisibleInProgram;
    { Integer constant in program scope }
    procedure TestIntConstInProgramScope;
    { Negative integer constant }
    procedure TestNegativeIntConst;
    { String constant in program scope }
    procedure TestStringConst;
    { Integer constant in unit interface section is parsed }
    procedure TestIntConstInUnitInterface;
    { Integer constant in unit implementation section is parsed }
    procedure TestIntConstInUnitImpl;
    { Implementation-section constant is usable in a method body in that unit }
    procedure TestImplConstUsableInMethodBody;
    { Constant used in assignment }
    procedure TestConstUsedInAssignment;
    { Constant used as WriteLn argument }
    procedure TestConstUsedInWriteLn;
    { Multiple constants in one const block }
    procedure TestMultipleConstsInBlock;
    { Two const blocks in same scope }
    procedure TestTwoConstBlocks;
    { Local constant inside a standalone procedure }
    procedure TestLocalConstInProcedure;
    { Local constant inside a standalone function }
    procedure TestLocalConstInFunction;
    { Local constant inside a class method }
    procedure TestLocalConstInMethod;
    { Constant in a class declaration section (class-level constant) }
    procedure TestConstInClassDeclaration;

    { Typed constants — const Name: Type = Value }
    procedure TestTypedConst_Integer;
    procedure TestTypedConst_Int64;
    procedure TestTypedConst_Double;
    procedure TestTypedConst_Single;
    procedure TestTypedConst_Boolean;
    procedure TestTypedConst_String;
    procedure TestTypedConst_TypeAnnotationPreserved;
    procedure TestTypedConst_NegativeDouble;
    procedure TestTypedConst_NegativeInteger;
    procedure TestTypedConst_InUnit;
    procedure TestTypedConst_UsedInExpression;

    { Array-of-enum typed constants }
    procedure TestArrayConst_StringElements_Parses;
    procedure TestArrayConst_IntElements_Parses;
    procedure TestArrayConst_StringElements_InIR;
    procedure TestArrayConst_IntElements_InIR;
    procedure TestArrayConst_Int64BitPattern_InIR;
    procedure TestArrayConst_IndexedByEnumVar;
    procedure TestArrayConst_WrongElementCount_Error;
    procedure TestArrayConst_InUnit;

    { Range-indexed array constants: array[Low..High] of T = (...) }
    procedure TestArrayConst_RangeIndexed_Parses;
    procedure TestArrayConst_RangeIndexed_InIR;
    procedure TestArrayConst_RangeIndexed_StringElements;
    procedure TestArrayConst_RangeIndexed_WrongCount_Error;
    procedure TestArrayConst_RangeIndexed_IndexedByVar;

    { Multi-dimensional range-indexed const arrays }
    procedure TestArrayConst_MultiDim_CommaForm_Parses;
    procedure TestArrayConst_MultiDim_NestedForm_Parses;
    procedure TestArrayConst_MultiDim_RowMajorData_InIR;
    procedure TestArrayConst_MultiDim_WrongCount_Error;

    { Named type alias array constants (issue #113) }
    procedure TestArrayConst_NamedAlias_Parses;
    procedure TestArrayConst_NamedAlias_InIR;
    procedure TestArrayConst_NamedAlias_WrongCount_Error;

    { Class-level array constants }
    procedure TestClassArrayConst_RangeIndexed_InIR;
    procedure TestClassArrayConst_EnumIndexed_InIR;

    { Function-local typed array constants — must emit a data item in the
      data section, not just reference $Name from the function body. }
    procedure TestArrayConst_LocalInFunction_EmitsDataItem;
    procedure TestArrayConst_LocalInProcedure_EmitsDataItem;
    procedure TestArrayConst_LocalInMethod_EmitsDataItem;

    { Integer-type typecast in const initialiser — TypeName(Lit) and
      TypeName(-Lit) — applies bit-width truncation with sign-extension
      for signed targets.  Both scalar and array-element positions. }
    procedure TestTypedConst_IntegerCast_NegativeSurvives;
    procedure TestTypedConst_CardinalCast_NegativeTruncatesToUnsigned;
    procedure TestTypedConst_ByteCast_NegativeOneIs255;
    procedure TestTypedConst_SmallIntCast_NegativeOneIsMinusOne;
    procedure TestTypedConst_WordCast_NegativeOneIs65535;
    procedure TestArrayConst_CardinalCastElement_TruncatesToUnsigned;

    { Bit-op chains in const initialisers — or/and/xor/shl/shr applied
      to integer literals, named constants, or a mix.  Folded to a
      single integer at semantic time. }
    procedure TestTypedConst_OrChain_AllLiterals_Folds;
    procedure TestTypedConst_OrChain_NamedConsts_Folds;
    procedure TestTypedConst_OrChain_MixedLiteralAndNamed_Folds;
    procedure TestTypedConst_AndMaskOfHexLiteral_Folds;
    procedure TestTypedConst_ShiftLeftLiteral_Folds;

    { Compile-time integer constant expressions (issue #96) — arithmetic
      operators, precedence, parentheses, and forward const references }
    procedure TestConstExpr_Multiply_Folds;
    procedure TestConstExpr_Parenthesised_Folds;
    procedure TestConstExpr_PrecedenceMulOverAdd_Folds;
    procedure TestConstExpr_ParensOverridePrecedence_Folds;
    procedure TestConstExpr_DivAndMod_Folds;
    procedure TestConstExpr_NamedConstReference_Folds;
    procedure TestConstExpr_UnaryMinus_Folds;
    procedure TestConstExpr_MixedArithAndBitwise_Folds;
    procedure TestArrayConst_OrChainElement_FoldsToFinalInteger;

    { Compile-time floating-point constant expressions (issue #108) }
    procedure TestConstExpr_FloatMultiply_Folds;
    procedure TestConstExpr_FloatDivide_Folds;
    procedure TestConstExpr_FloatAddSub_Folds;
    procedure TestConstExpr_FloatParens_Folds;
    procedure TestConstExpr_FloatMixedIntFloat_Folds;
    procedure TestConstExpr_FloatNamedConst_Folds;
    procedure TestConstExpr_NegativeFloat_Folds;
    procedure TestConstExpr_IntSlash_ProducesFloat;
    procedure TestConstExpr_TypedDoubleIntExpr_Folds;
    procedure TestVarInit_TypedDoubleIntExpr_Folds;
    { GH #195 — bit operators inside a FLOAT constant expression.  They fold
      as Int64 (not Double), which the 1 shl 53 case depends on. }
    procedure TestConstExpr_ShlInFloatExpr_FoldsAsInteger;
    procedure TestConstExpr_ShlInFloatExpr_TypecastOperand;
    procedure TestConstExpr_BitOpsInFloatExpr_AllOperators;
    procedure TestConstExpr_OrdinalCastTruncates;
  end;

implementation

function TConstTests.GenIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TConstTests.ParseUnit(const ASrc: string): TUnit;
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

function TConstTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

procedure TConstTests.TestExportedConstVisibleInProgram;
const
  UnitSrc =
    '''
        unit MyConsts;
        interface
        const
          dupAccept = 0;
          dupIgnore = 1;
          dupError  = 2;
        implementation
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses MyConsts;
        var x: Integer;
        begin
          x := dupIgnore
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
  L:    TLexer;
  P:    TParser;
begin
  L := TLexer.Create(UnitSrc);
  P := TParser.Create(L);
  U := P.ParseUnit();
  P.Free(); L.Free();

  L := TLexer.Create(ProgSrc);
  P := TParser.Create(L);
  Prog := P.Parse();
  P.Free(); L.Free();

  SA := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnitForExport(U);
    { If dupIgnore is not in global scope, Analyse will raise ESemanticError }
    SA.Analyse(Prog);
    AssertNotNull('Program should analyse without error', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
    U.Free();
  end;
end;

procedure TConstTests.TestIntConstInProgramScope;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const MaxItems = 10;
        var x: Integer;
        begin
          x := MaxItems;
        end.
        '''
  );
  AssertTrue('IR should be non-empty for program with integer const', IR <> '');
end;

procedure TConstTests.TestNegativeIntConst;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const MinVal = -1;
        var x: Integer;
        begin
          x := MinVal;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Negative const should fold to -1', IRContains(IR, '-1'));
end;

procedure TConstTests.TestStringConst;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const AppName = 'MyApp';
        begin
          WriteLn(AppName);
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('String const value should appear in IR', IRContains(IR, 'MyApp'));
end;

procedure TConstTests.TestIntConstInUnitInterface;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
        unit MyConsts;
        interface
        const
          dupAccept = 0;
          dupIgnore = 1;
          dupError  = 2;
        implementation
        end.
        '''
  );
  try
    AssertEquals('Interface const block should have 3 entries',
      3, U.IntfBlock.ConstDecls.Count);
    AssertEquals('First const name', 'dupAccept',
      TConstDecl(U.IntfBlock.ConstDecls.Items[0]).Name);
    AssertEquals('First const value', 0,
      TConstDecl(U.IntfBlock.ConstDecls.Items[0]).IntVal);
    AssertEquals('Second const name', 'dupIgnore',
      TConstDecl(U.IntfBlock.ConstDecls.Items[1]).Name);
    AssertEquals('Third const name', 'dupError',
      TConstDecl(U.IntfBlock.ConstDecls.Items[2]).Name);
    AssertEquals('Third const value', 2,
      TConstDecl(U.IntfBlock.ConstDecls.Items[2]).IntVal);
  finally
    U.Free();
  end;
end;

procedure TConstTests.TestIntConstInUnitImpl;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
        unit MyConsts;
        interface
        implementation
        const
          InternalVal = 42;
        end.
        '''
  );
  try
    AssertEquals('Impl const block should have 1 entry',
      1, U.ImplBlock.ConstDecls.Count);
    AssertEquals('Impl const name', 'InternalVal',
      TConstDecl(U.ImplBlock.ConstDecls.Items[0]).Name);
    AssertEquals('Impl const value', 42,
      TConstDecl(U.ImplBlock.ConstDecls.Items[0]).IntVal);
  finally
    U.Free();
  end;
end;

procedure TConstTests.TestImplConstUsableInMethodBody;
const
  UnitSrc =
    '''
        unit Checker;
        interface
        function GetLimit: Integer;
        implementation
        const
          Limit = 99;
        function GetLimit: Integer;
        begin
          Result := Limit
        end;
        end.
        ''';
var
  U:  TUnit;
  SA: TSemanticAnalyser;
begin
  U  := ParseUnit(UnitSrc);
  SA := TSemanticAnalyser.Create();
  try
    { AnalyseUnitForExport raises ESemanticError if Limit is not resolved }
    SA.AnalyseUnitForExport(U);
    AssertNotNull('Unit should analyse without error', U);
  finally
    SA.Free();
    U.Free();
  end;
end;

procedure TConstTests.TestConstUsedInAssignment;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const Limit = 5;
        var x: Integer;
        begin
          x := Limit;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Const value should appear in IR', IRContains(IR, '5'));
end;

procedure TConstTests.TestConstUsedInWriteLn;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const ErrCode = 42;
        begin
          WriteLn(ErrCode);
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Constant value should appear in IR', IRContains(IR, '42'));
end;

procedure TConstTests.TestMultipleConstsInBlock;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const
          A = 1;
          B = 2;
          C = 3;
        var x: Integer;
        begin
          x := A;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
end;

procedure TConstTests.TestTwoConstBlocks;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const First = 10;
        var x: Integer;
        const Second = 20;
        begin
          x := First + Second;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
end;

procedure TConstTests.TestLocalConstInProcedure;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        procedure DoWork;
        const Threshold = 7;
        var x: Integer;
        begin
          x := Threshold
        end;
        begin
          DoWork()
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Local const value should appear in IR', IRContains(IR, '7'));
end;

procedure TConstTests.TestLocalConstInFunction;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        function Compute: Integer;
        const Base = 100;
        begin
          Result := Base
        end;
        var r: Integer;
        begin
          r := Compute()
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Local const value should appear in IR', IRContains(IR, '100'));
end;

procedure TConstTests.TestLocalConstInMethod;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        type
          TFoo = class
            function Bar: Integer;
          end;
        function TFoo.Bar: Integer;
        const Magic = 55;
        begin
          Result := Magic
        end;
        var f: TFoo;
        begin
          f := TFoo.Create();
          WriteLn(f.Bar());
          f.Free()
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Local const value should appear in IR', IRContains(IR, '55'));
end;

procedure TConstTests.TestConstInClassDeclaration;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        type
          TFoo = class
          const
            MaxItems = 100;
          var
            FCount: Integer;
          end;
        var x: Integer;
        begin
          x := TFoo.MaxItems
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Class const value should appear in IR', IRContains(IR, '100'));
end;

{ ------------------------------------------------------------------ }
{ Typed constants                                                      }
{ ------------------------------------------------------------------ }

procedure TConstTests.TestTypedConst_Integer;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const MaxItems: Integer = 100;
    var x: Integer;
    begin x := MaxItems end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '100'));
end;

procedure TConstTests.TestTypedConst_Int64;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const BigVal: Int64 = 1000000000;
    var x: Int64;
    begin x := BigVal end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '1000000000'));
end;

procedure TConstTests.TestTypedConst_Double;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Pi: Double = 3.14159;
    var x: Double;
    begin x := Pi end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '3.14159'));
end;

procedure TConstTests.TestTypedConst_Single;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const E: Single = 2.71828;
    var x: Single;
    begin x := E end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '2.71828'));
end;

procedure TConstTests.TestTypedConst_Boolean;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Flag: Boolean = True;
    var b: Boolean;
    begin b := Flag end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
end;

procedure TConstTests.TestTypedConst_String;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Greeting: string = 'hello';
    begin WriteLn(Greeting) end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, 'hello'));
end;

procedure TConstTests.TestTypedConst_TypeAnnotationPreserved;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  Sym: TSymbol;
begin
  L  := TLexer.Create('program Test; const Pi: Double = 3.14; begin end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  SA := TSemanticAnalyser.Create();
  try
    SA.Analyse(Pr);
    Sym := Pr.SymbolTable.Lookup('Pi');
    AssertNotNil('Pi symbol exists', Sym);
    AssertEquals('Pi is Double', 'Double', Sym.TypeDesc.Name);
  finally
    SA.Free(); Pr.Free(); P.Free(); L.Free();
  end;
end;

procedure TConstTests.TestTypedConst_NegativeDouble;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const NegPi: Double = -3.14159;
    var x: Double;
    begin x := NegPi end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('negative value in IR', IRContains(IR, '-3.14159'));
end;

procedure TConstTests.TestTypedConst_NegativeInteger;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const MinVal: Integer = -42;
    var x: Integer;
    begin x := MinVal end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('negative value in IR', IRContains(IR, '-42'));
end;

procedure TConstTests.TestTypedConst_InUnit;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
    unit MyMath;
    interface
    const Pi: Double = 3.14159265358979;
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free();
end;

procedure TConstTests.TestTypedConst_UsedInExpression;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Scale: Double = 2.5;
    var x, y: Double;
    begin
      x := 4.0;
      y := x * Scale
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Scale value in IR', IRContains(IR, '2.5'));
end;

{ ------------------------------------------------------------------ }
{ Array-of-enum typed constants                                        }
{ ------------------------------------------------------------------ }

procedure TConstTests.TestArrayConst_StringElements_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free();
end;

procedure TConstTests.TestArrayConst_IntElements_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    type TDir = (dNorth, dSouth, dEast, dWest);
    const DirCost: array[TDir] of Integer = (1, 1, 2, 2);
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free();
end;

procedure TConstTests.TestArrayConst_StringElements_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Sunny in IR', IRContains(IR, 'Sunny'));
  AssertTrue('Cloudy in IR', IRContains(IR, 'Cloudy'));
  AssertTrue('Rainy in IR', IRContains(IR, 'Rainy'));
  AssertTrue('WeatherNames in IR', IRContains(IR, 'WeatherNames'));
end;

procedure TConstTests.TestArrayConst_IntElements_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TDir = (dNorth, dSouth, dEast, dWest);
    const DirCost: array[TDir] of Integer = (1, 1, 2, 2);
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('DirCost in IR', IRContains(IR, 'DirCost'));
end;

procedure TConstTests.TestArrayConst_Int64BitPattern_InIR;
var IR: string;
begin
  { Radix literals whose sign bit is set (above High(Int64)) are valid Int64
    bit patterns inside an array const — the same rule the scalar typed-const
    path follows since issue #133.  $8080808080808080 folds to the decimal
    bit pattern -9187201950435737472; &1000000000000000000000 (octal 2^63)
    folds to -9223372036854775808 (issue #159). }
  IR := GenIR(
    '''
    program P;
    const B: array[0..2] of Int64 = (
      $4040404040404040,
      $8080808080808080,
      &1000000000000000000000
    );
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('B in IR', IRContains(IR, 'B'));
  AssertTrue('plain element folded', IRContains(IR, '4629771061636907072'));
  AssertTrue('hex bit pattern folded', IRContains(IR, '-9187201950435737472'));
  AssertTrue('octal bit pattern folded', IRContains(IR, '-9223372036854775808'));
end;

procedure TConstTests.TestArrayConst_IndexedByEnumVar;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    var W: TWeather; S: string;
    begin
      W := wtCloudy;
      S := WeatherNames[W]
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('WeatherNames in IR', IRContains(IR, 'WeatherNames'));
end;

procedure TConstTests.TestArrayConst_WrongElementCount_Error;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L  := TLexer.Create(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy');
    begin end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse();
  SA := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Pr);
    except
      on E: ESemanticError do GotError := True;
    end;
  finally
    SA.Free(); Pr.Free(); P.Free(); L.Free();
  end;
  AssertTrue('wrong count raises error', GotError);
end;

procedure TConstTests.TestArrayConst_InUnit;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    var W: TWeather; S: string;
    begin
      W := wtRainy;
      S := WeatherNames[W];
      WriteLn(S)
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Rainy in IR', IRContains(IR, 'Rainy'));
end;

procedure TConstTests.TestArrayConst_RangeIndexed_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    const Days: array[0..6] of string = ('Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat');
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free();
end;

procedure TConstTests.TestArrayConst_RangeIndexed_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Vals: array[0..3] of Integer = (10, 20, 30, 40);
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Vals in IR', IRContains(IR, 'Vals'));
end;

procedure TConstTests.TestArrayConst_RangeIndexed_StringElements;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Days: array[0..2] of string = ('Mon', 'Tue', 'Wed');
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Mon in IR', IRContains(IR, 'Mon'));
  AssertTrue('Tue in IR', IRContains(IR, 'Tue'));
  AssertTrue('Wed in IR', IRContains(IR, 'Wed'));
end;

procedure TConstTests.TestArrayConst_RangeIndexed_WrongCount_Error;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L  := TLexer.Create(
    '''
    program P;
    const Vals: array[0..3] of Integer = (10, 20);
    begin end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse();
  SA := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Pr);
    except
      on E: ESemanticError do GotError := True;
    end;
  finally
    SA.Free(); Pr.Free(); P.Free(); L.Free();
  end;
  AssertTrue('wrong count raises error', GotError);
end;

procedure TConstTests.TestArrayConst_RangeIndexed_IndexedByVar;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Days: array[0..2] of string = ('Mon', 'Tue', 'Wed');
    var I: Integer; S: string;
    begin
      I := 1;
      S := Days[I]
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Days in IR', IRContains(IR, 'Days'));
end;

procedure TConstTests.TestArrayConst_MultiDim_CommaForm_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    const M: array[0..1, 0..2] of Integer = ((1, 2, 3), (4, 5, 6));
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  AssertEquals('six flat elements', 6,
    TConstDecl(U.IntfBlock.ConstDecls.Items[0]).ArrayElements.Count);
  AssertEquals('two dimensions', 2,
    TConstDecl(U.IntfBlock.ConstDecls.Items[0]).ArrayDimLows.Count);
  U.Free();
end;

procedure TConstTests.TestArrayConst_MultiDim_NestedForm_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    const M: array[0..1] of array[0..1] of Integer = ((10, 20), (30, 40));
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('four flat elements', 4,
    TConstDecl(U.IntfBlock.ConstDecls.Items[0]).ArrayElements.Count);
  AssertEquals('two dimensions', 2,
    TConstDecl(U.IntfBlock.ConstDecls.Items[0]).ArrayDimLows.Count);
  U.Free();
end;

procedure TConstTests.TestArrayConst_MultiDim_RowMajorData_InIR;
var IR: string;
begin
  { Comma and nested forms must lower to the same flat row-major data blob. }
  IR := GenIR(
    '''
    program P;
    const M: array[0..1, 0..1] of Integer = ((1, 2), (3, 4));
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('M in IR', IRContains(IR, 'M'));
  { Row-major: the four words appear in declaration order in one data item. }
  AssertTrue('row-major words present',
    IRContains(IR, 'w 1, w 2, w 3, w 4'));
end;

procedure TConstTests.TestArrayConst_MultiDim_WrongCount_Error;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L  := TLexer.Create(
    '''
    program P;
    const M: array[0..1, 0..1] of Integer = ((1, 2, 3), (4, 5, 6));
    begin end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse();
  SA := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Pr);
    except
      on E: ESemanticError do GotError := True;
    end;
  finally
    SA.Free(); Pr.Free(); P.Free(); L.Free();
  end;
  AssertTrue('wrong element count raises error', GotError);
end;

procedure TConstTests.TestArrayConst_NamedAlias_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    type TArr = array[0..2] of Integer;
    const A: TArr = (10, 20, 30);
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free();
end;

procedure TConstTests.TestArrayConst_NamedAlias_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TArr = array[0..2] of Integer;
    const Vals: TArr = (10, 20, 30);
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Vals in IR', IRContains(IR, 'Vals'));
end;

procedure TConstTests.TestArrayConst_NamedAlias_WrongCount_Error;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L  := TLexer.Create(
    '''
    program P;
    type TArr = array[0..3] of Integer;
    const Vals: TArr = (10, 20);
    begin end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse();
  SA := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Pr);
    except
      on E: ESemanticError do
        GotError := True;
    end;
  finally
    SA.Free(); Pr.Free(); P.Free(); L.Free();
  end;
  AssertTrue('wrong element count raises error', GotError);
end;

procedure TConstTests.TestClassArrayConst_RangeIndexed_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type
      TMyClass = class
      public
        const Items: array[0..2] of string = ('A', 'B', 'C');
      end;
    var T: TMyClass;
    begin
      T := TMyClass.Create();
      WriteLn(T.Items[1]);
      T.Free()
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Items in IR', IRContains(IR, 'Items'));
end;

procedure TConstTests.TestClassArrayConst_EnumIndexed_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type
      TColor = (Red, Green, Blue);
      TPalette = class
      public
        const Names: array[TColor] of string = ('Red', 'Green', 'Blue');
      end;
    var P2: TPalette;
    begin
      P2 := TPalette.Create();
      WriteLn(P2.Names[0]);
      P2.Free()
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Names in IR', IRContains(IR, 'Names'));
end;

{ Regression: a typed array constant declared inside a function body
  was referenced as `$Days` from the function code but no
  `data $Days = ...` item was emitted, so the linker failed with
  `undefined reference to Days`. EmitGlobalConstData was only called on
  the top-level program/unit blocks and never recursed into method
  bodies. }
procedure TConstTests.TestArrayConst_LocalInFunction_EmitsDataItem;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    function DaysInMonth(M: Integer): Integer;
    const
      Days: array[1..12] of Integer = (31,28,31,30,31,30,31,31,30,31,30,31);
    begin
      Result := Days[M]
    end;
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { Local array consts get a mangled, file-local data label ('__bac_N_Days')
    so they never collide with same-named consts elsewhere or with the RTL.
    The label must NOT be exported. }
  AssertTrue('mangled Days data item emitted',
    Pos('data $__bac_', IR) >= 0);
  AssertTrue('Days label suffix present',
    Pos('_Days =', IR) >= 0);
  AssertTrue('Days array const not exported',
    Pos('export data $__bac_', IR) < 0);
  AssertTrue('Days[M] reference uses mangled label',
    Pos('add $__bac_', IR) >= 0);
end;

procedure TConstTests.TestArrayConst_LocalInProcedure_EmitsDataItem;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    procedure Dump;
    const
      Tbl: array[0..2] of Integer = (10, 20, 30);
    begin
      WriteLn(Tbl[0])
    end;
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('mangled Tbl data item emitted',
    Pos('data $__bac_', IR) >= 0);
  AssertTrue('Tbl label suffix present',
    Pos('_Tbl =', IR) >= 0);
  AssertTrue('Tbl array const not exported',
    Pos('export data $__bac_', IR) < 0);
end;

procedure TConstTests.TestArrayConst_LocalInMethod_EmitsDataItem;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type
      TFoo = class
      public
        function Lookup(I: Integer): Integer;
      end;
    function TFoo.Lookup(I: Integer): Integer;
    const
      Vals: array[0..3] of Integer = (7, 8, 9, 10);
    begin
      Result := Vals[I]
    end;
    var F: TFoo;
    begin
      F := TFoo.Create();
      WriteLn(F.Lookup(0));
      F.Free()
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('mangled Vals data item emitted',
    Pos('data $__bac_', IR) >= 0);
  AssertTrue('Vals label suffix present',
    Pos('_Vals =', IR) >= 0);
  AssertTrue('Vals array const not exported',
    Pos('export data $__bac_', IR) < 0);
end;

procedure TConstTests.TestTypedConst_IntegerCast_NegativeSurvives;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Integer = Integer(-11);
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { Integer(-11) sign-extends back to -11 in the i32 domain. }
  AssertTrue('-11 reaches IR', IRContains(IR, '-11'));
end;

procedure TConstTests.TestTypedConst_CardinalCast_NegativeTruncatesToUnsigned;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Cardinal = Cardinal(-11);
    var v: Cardinal;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { Cardinal(-11) = $FFFFFFF5 = 4294967285. }
  AssertTrue('4294967285 reaches IR', IRContains(IR, '4294967285'));
end;

procedure TConstTests.TestTypedConst_ByteCast_NegativeOneIs255;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Byte = Byte(-1);
    var v: Byte;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('255 reaches IR', IRContains(IR, '255'));
end;

procedure TConstTests.TestTypedConst_SmallIntCast_NegativeOneIsMinusOne;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: SmallInt = SmallInt(-1);
    var v: SmallInt;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { SmallInt is signed — sign-extend back to -1. }
  AssertTrue('-1 reaches IR', IRContains(IR, '-1'));
end;

procedure TConstTests.TestTypedConst_WordCast_NegativeOneIs65535;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Word = Word(-1);
    var v: Word;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('65535 reaches IR', IRContains(IR, '65535'));
end;

procedure TConstTests.TestArrayConst_CardinalCastElement_TruncatesToUnsigned;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const T: array[0..1] of Cardinal = (Cardinal(-11), 42);
    var v: Cardinal;
    begin v := T[0] end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { Element 0 of the data item should be the truncated value 4294967285. }
  AssertTrue('4294967285 in $T data item',
    IRContains(IR, 'w 4294967285'));
end;

procedure TConstTests.TestTypedConst_OrChain_AllLiterals_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Integer = 1 or 2 or 4;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('1|2|4 = 7 in IR', IRContains(IR, '7'));
end;

procedure TConstTests.TestTypedConst_OrChain_NamedConsts_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const
      FG_BLUE  = 1;
      FG_GREEN = 2;
      X: Integer = FG_BLUE or FG_GREEN;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('FG_BLUE|FG_GREEN = 3 in IR', IRContains(IR, '3'));
end;

procedure TConstTests.TestTypedConst_OrChain_MixedLiteralAndNamed_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const
      FG_BLUE = 1;
      X: Integer = FG_BLUE or 4;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('1|4 = 5 in IR', IRContains(IR, '5'));
end;

procedure TConstTests.TestTypedConst_AndMaskOfHexLiteral_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Integer = $FF and 15;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('$FF & 15 = 15 in IR', IRContains(IR, '15'));
end;

procedure TConstTests.TestTypedConst_ShiftLeftLiteral_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Integer = 1 shl 8;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('1 shl 8 = 256 in IR', IRContains(IR, '256'));
end;

procedure TConstTests.TestConstExpr_Multiply_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = 2 * 3;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('2 * 3 = 6 in IR', IRContains(IR, '6'));
end;

procedure TConstTests.TestConstExpr_Parenthesised_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = (2 * 3);
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('(2 * 3) = 6 in IR', IRContains(IR, '6'));
end;

procedure TConstTests.TestConstExpr_PrecedenceMulOverAdd_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = 2 + 3 * 4;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { 2 + (3 * 4) = 14, not (2 + 3) * 4 = 20 }
  AssertTrue('2 + 3 * 4 = 14 in IR', IRContains(IR, '14'));
end;

procedure TConstTests.TestConstExpr_ParensOverridePrecedence_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = (2 + 3) * 4;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('(2 + 3) * 4 = 20 in IR', IRContains(IR, '20'));
end;

procedure TConstTests.TestConstExpr_DivAndMod_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Q = 100 div 7;
          R = 100 mod 7;
    var a, b: Integer;
    begin a := Q; b := R end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('100 div 7 = 14 in IR', IRContains(IR, '14'));
  AssertTrue('100 mod 7 = 2 in IR', IRContains(IR, '2'));
end;

procedure TConstTests.TestConstExpr_NamedConstReference_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Base = 10;
          Derived = Base * 2 + 1;
    var v: Integer;
    begin v := Derived end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Base * 2 + 1 = 21 in IR', IRContains(IR, '21'));
end;

procedure TConstTests.TestConstExpr_UnaryMinus_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = -5 * 3;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('-5 * 3 = -15 in IR', IRContains(IR, '-15'));
end;

procedure TConstTests.TestConstExpr_MixedArithAndBitwise_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = (1 shl 4) or 3;
    var v: Integer;
    begin v := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { (1 shl 4) or 3 = 16 or 3 = 19 }
  AssertTrue('(1 shl 4) or 3 = 19 in IR', IRContains(IR, '19'));
end;

procedure TConstTests.TestArrayConst_OrChainElement_FoldsToFinalInteger;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const
      FG_BLUE  = 1;
      FG_GREEN = 2;
      T: array[0..1] of Integer = (FG_BLUE or FG_GREEN, 99);
    var v: Integer;
    begin v := T[0] end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { Element 0 should land as 3 in the emitted $T data item. }
  AssertTrue('folded 3 in $T data item', IRContains(IR, 'w 3'));
  AssertTrue('99 also in $T data item',  IRContains(IR, 'w 99'));
end;

{ ------------------------------------------------------------------ }
{ Compile-time floating-point constant expressions (issue #108)       }
{ ------------------------------------------------------------------ }

procedure TConstTests.TestConstExpr_FloatMultiply_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = 3.0 * 2.0;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 6', IRContains(IR, 'd_6'));
end;

procedure TConstTests.TestConstExpr_FloatDivide_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = 10.0 / 4.0;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 2.5', IRContains(IR, 'd_2.5'));
end;

procedure TConstTests.TestConstExpr_FloatAddSub_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = 1.5 + 2.5;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 4', IRContains(IR, 'd_4'));
end;

procedure TConstTests.TestConstExpr_FloatParens_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = (1.0 + 2.0) * 3.0;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 9', IRContains(IR, 'd_9'));
end;

procedure TConstTests.TestConstExpr_FloatMixedIntFloat_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = 2 * 1.5;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 3', IRContains(IR, 'd_3'));
end;

procedure TConstTests.TestConstExpr_FloatNamedConst_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const
      PI = 3.14;
      TAU = PI * 2.0;
    var V: Double;
    begin V := TAU end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 6.28', IRContains(IR, 'd_6.28'));
end;

procedure TConstTests.TestConstExpr_NegativeFloat_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = -1.5 * 2.0;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to -3', IRContains(IR, 'd_-3'));
end;

procedure TConstTests.TestConstExpr_IntSlash_ProducesFloat;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X = 10 / 4;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 2.5', IRContains(IR, 'd_2.5'));
end;

procedure TConstTests.TestConstExpr_ShlInFloatExpr_FoldsAsInteger;
var IR: string;
begin
  { GH #195: `1.0 / (z shl 53)` reported "Unsupported operator in
    floating-point constant expression".  Bit ops are INTEGER operations even
    inside a float expression; folding the shift as a Double would lose
    precision at exactly 2^53, which is the value this idiom uses. }
  IR := GenIR(
    '''
    program P;
    const
      Z = 1;
      X = 1.0 / (Z shl 53);
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { 1 / 2^53 = 1.1102230246251565e-16 }
  AssertTrue('folded to the 2^-53 epsilon', IRContains(IR, 'd_1.11022302462516e-16'));
end;

procedure TConstTests.TestConstExpr_ShlInFloatExpr_TypecastOperand;
var IR: string;
begin
  { The form in the report: an ordinal TYPECAST as the shift operand.
    `UInt64(1)` parses as a one-argument call whose name is a type, not a
    distinct cast node, and failed with a different message than the plain
    form ("not a compile-time float"). }
  IR := GenIR(
    '''
    program P;
    const X = 1.0 / (UInt64(1) shl 53);
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to the 2^-53 epsilon', IRContains(IR, 'd_1.11022302462516e-16'));
end;

procedure TConstTests.TestConstExpr_BitOpsInFloatExpr_AllOperators;
var IR: string;
begin
  { and/or/xor/shr alongside shl — all six fold in FPC, so all six must here. }
  IR := GenIR(
    '''
    program P;
    const
      A = 1.0 / (255 and 15);
      B = 1.0 / (8 or 1);
      C = 1.0 / (12 xor 6);   { 10 — distinct from the or/and results }
      D = 1.0 / (1024 shr 2);
    var V: Double;
    begin V := A; V := B; V := C; V := D end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('and folded (1/15)',  IRContains(IR, 'd_0.0666666666666667'));
  AssertTrue('or folded (1/9)',    IRContains(IR, 'd_0.111111111111111'));
  AssertTrue('xor folded (1/10)',  IRContains(IR, 'd_0.1'));
  AssertTrue('shr folded (1/256)', IRContains(IR, 'd_0.00390625'));
end;

procedure TConstTests.TestConstExpr_OrdinalCastTruncates;
var IR: string;
begin
  { An ordinal cast TRUNCATES: Byte(300) is 44, so Byte(300) shl 1 is 88.
    The parser folds the bare literal form itself, but a PARENTHESISED or
    float-embedded cast routes through the semantic evaluator instead — and
    without the same masking the two disagreed (88 vs 600), i.e. the same
    expression changed value with parentheses.  Both spellings are asserted,
    and the signed case pins sign-extension (SmallInt(40000) = -25536). }
  IR := GenIR(
    '''
    program P;
    const
      A = 1.0 * (Byte(300) shl 1);
      B = 1.0 * (SmallInt(40000) shl 1);
    var V: Double;
    begin V := A; V := B end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Byte(300) truncated to 44, shl 1 = 88', IRContains(IR, 'd_88'));
  AssertTrue('SmallInt(40000) sign-extended', IRContains(IR, 'd_-51072'));
end;

procedure TConstTests.TestConstExpr_TypedDoubleIntExpr_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const X: Double = 2 * 3;
    var V: Double;
    begin V := X end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 6', IRContains(IR, 'd_6'));
end;

procedure TConstTests.TestVarInit_TypedDoubleIntExpr_Folds;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    var Y: Double = 2 * 3;
    begin WriteLn(Y) end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('folded to 6', IRContains(IR, 'd_6'));
end;

initialization
  RegisterTest(TConstTests);

end.
