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
  uLexer, uParser, uAST, uSemantic, cp.test.harness;

type
  TConstTests = class(TTestCase)
  private
    function ParseUnit(const ASrc: string): TUnit;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    { a routine-local array const is a private data item }
    procedure TestCodegen_LocalArrayConst_PrivateDataLabel;
    { Exported interface constant is visible in importing program }
    procedure TestExportedConstVisibleInProgram;
    { Integer constant in program scope }
    { Negative integer constant }
    { String constant in program scope }
    { Integer constant in unit interface section is parsed }
    procedure TestIntConstInUnitInterface;
    { Integer constant in unit implementation section is parsed }
    procedure TestIntConstInUnitImpl;
    { Implementation-section constant is usable in a method body in that unit }
    procedure TestImplConstUsableInMethodBody;
    { Constant used in assignment }
    { Constant used as WriteLn argument }
    { Multiple constants in one const block }
    { Two const blocks in same scope }
    { Local constant inside a standalone procedure }
    { Local constant inside a standalone function }
    { Local constant inside a class method }
    { Constant in a class declaration section (class-level constant) }

    { Typed constants — const Name: Type = Value }
    procedure TestTypedConst_TypeAnnotationPreserved;
    procedure TestTypedConst_InUnit;

    { Array-of-enum typed constants }
    procedure TestArrayConst_StringElements_Parses;
    procedure TestArrayConst_IntElements_Parses;
    procedure TestArrayConst_WrongElementCount_Error;

    { Range-indexed array constants: array[Low..High] of T = (...) }
    procedure TestArrayConst_RangeIndexed_Parses;
    procedure TestArrayConst_RangeIndexed_WrongCount_Error;

    { Multi-dimensional range-indexed const arrays }
    procedure TestArrayConst_MultiDim_CommaForm_Parses;
    procedure TestArrayConst_MultiDim_NestedForm_Parses;
    procedure TestArrayConst_MultiDim_WrongCount_Error;

    { Named type alias array constants (issue #113) }
    procedure TestArrayConst_NamedAlias_Parses;
    procedure TestArrayConst_NamedAlias_WrongCount_Error;

    { Class-level array constants }

    { Function-local typed array constants — must emit a data item in the
      data section, not just reference $Name from the function body. }

    { Integer-type typecast in const initialiser — TypeName(Lit) and
      TypeName(-Lit) — applies bit-width truncation with sign-extension
      for signed targets.  Both scalar and array-element positions. }

    { Bit-op chains in const initialisers — or/and/xor/shl/shr applied
      to integer literals, named constants, or a mix.  Folded to a
      single integer at semantic time. }

    { Compile-time integer constant expressions (issue #96) — arithmetic
      operators, precedence, parentheses, and forward const references }

    { Compile-time floating-point constant expressions (issue #108) }
    { GH #195 — bit operators inside a FLOAT constant expression.  They fold
      as Int64 (not Double), which the 1 shl 53 case depends on. }
  end;

implementation

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

{ ------------------------------------------------------------------ }
{ Typed constants                                                      }
{ ------------------------------------------------------------------ }

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

procedure TConstTests.TestCodegen_LocalArrayConst_PrivateDataLabel;
const
  Src = '''
    program P;
    function DayName(D: Integer): string;
    const Days: array[1..2] of string = ('Sat', 'Sun');
    begin
      Result := Days[D]
    end;
    procedure Tbl;
    const Vals: array[0..2] of Integer = (100, 200, 300);
    begin
      WriteLn(Vals[1])
    end;
    begin
      WriteLn(DayName(1));
      Tbl()
    end.
    ''';
var
  I: Integer;
  T, AsmText: string;
begin
  { Each routine-local array const gets its own mangled __bac_<n>_<Name>
    data label -- two routines may declare the same name -- and the label
    is NOT exported: only one compile unit ever references it.  A run
    cannot tell an exported label from a private one. }
  for I := 0 to 1 do
  begin
    if I = 0 then T := TargetX86_64 else T := TargetArm64;
    AsmText := GenAsm(Src, T);
    AssertTrue(T + ': Days data item', Pos('_Days:', AsmText) >= 0);
    AssertTrue(T + ': Vals data item', Pos('_Vals:', AsmText) >= 0);
    AssertTrue(T + ': mangled local label', Pos('__bac_', AsmText) >= 0);
    AssertTrue(T + ': local array const not exported',
      Pos('.globl __bac_', AsmText) < 0);
  end;
end;

initialization
  RegisterTest(TConstTests);

end.
