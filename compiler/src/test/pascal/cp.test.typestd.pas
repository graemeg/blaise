{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.typestd;

{ Type standardisation, Phase 1 (docs/type-standardisation-design.adoc): the
  platform-honest builtin type names.  Each new name is a transparent alias
  of an existing builtin type (D3) -- the same TTypeDesc, not a copy -- so it
  is interchangeable with the classic spelling everywhere, and an overload
  pair spelled with both is one signature (D12). }

interface

uses
  SysUtils, blaise.testing, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TTypeStdTests = class(TTestCase)
  published
    { every new name resolves to the type it is documented to alias }
    procedure TestSem_NewNames_AliasTheirTypes;
    { Int and Int64 are one type on every current target: an overload pair
      spelled with both is rejected at the second declaration }
    procedure TestSem_IntAndInt64Overload_Rejected;
    { a classic and a new spelling assign to one another without a cast }
    procedure TestSem_NewAndClassicNames_Interchangeable;
    { a constant typecast through a new name folds at its width }
    procedure TestSem_ConstTypecast_FoldsAtWidth;
  end;

implementation

const
  NamesSrc = '''
    program p;
    var
      A: Int; B: UInt; C: Int32; D: UInt8;
      E: Float; F: Float32; G: Float64;
    begin
    end.
    ''';

procedure TTypeStdTests.TestSem_NewNames_AliasTheirTypes;
var
  Prog: TProgram;
  T: TSymbolTable;

  procedure Check(const ANew, AClassic: string);
  begin
    AssertNotNull(ANew + ' is a type', T.FindType(ANew));
    AssertTrue(ANew + ' is the same type as ' + AClassic,
      T.FindType(ANew) = T.FindType(AClassic));
  end;

begin
  Prog := Analyse(NamesSrc);
  try
    T := Prog.SymbolTable;
    Check('Int', 'Int64');
    Check('UInt', 'UInt64');
    Check('Int32', 'Integer');
    Check('UInt8', 'Byte');
    Check('Float', 'Double');
    Check('Float32', 'Single');
    Check('Float64', 'Double');
  finally
    Prog.Free();
  end;
end;

procedure TTypeStdTests.TestSem_IntAndInt64Overload_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program p;
    procedure F(X: Int); overload; begin end;
    procedure F(X: Int64); overload; begin end;
    begin
    end.
    ''');
  AssertTrue('duplicate signature: ' + Msg,
    Pos('has the same parameter signature', Msg) >= 0);
  AssertTrue('names the pair: ' + Msg,
    Pos('''Int64'' and ''Int'' are the same type', Msg) >= 0);
  AssertEquals('Int32 / Int64 is a genuine overload pair', '',
    SemanticError('''
      program p;
      procedure F(X: Int32); overload; begin end;
      procedure F(X: Int64); overload; begin end;
      begin
      end.
      '''));
end;

procedure TTypeStdTests.TestSem_NewAndClassicNames_Interchangeable;
begin
  AssertEquals('', '', SemanticError('''
    program p;
    var
      I: Integer; I32: Int32;
      L: Int64; N: Int;
      Q: UInt64; U: UInt;
      B: Byte; U8: UInt8;
      D: Double; F: Float; F64: Float64;
      S: Single; F32: Float32;
    begin
      I32 := I; I := I32;
      N := L; L := N;
      U := Q; Q := U;
      U8 := B; B := U8;
      F := D; F64 := F; D := F64;
      F32 := S; S := F32
    end.
    '''));
end;

procedure TTypeStdTests.TestSem_ConstTypecast_FoldsAtWidth;
const
  Src = '''
    program p;
    const
      A = UInt8(300);
      B = Int32($FFFFFFFF);
      C = Int(-5);
      D = UInt(7);
    var X: Int64;
    begin
      X := A + B + C + D
    end.
    ''';
var
  Prog: TProgram;
  T: TSymbolTable;
begin
  Prog := Analyse(Src);
  try
    T := Prog.SymbolTable;
    AssertEquals('UInt8(300) truncates to 8 bits', Int64(44),
      T.Lookup('A').ConstValue);
    AssertEquals('Int32($FFFFFFFF) sign-extends', Int64(-1),
      T.Lookup('B').ConstValue);
    AssertEquals('Int(-5)', Int64(-5), T.Lookup('C').ConstValue);
    AssertEquals('UInt(7)', Int64(7), T.Lookup('D').ConstValue);
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TTypeStdTests);

end.
