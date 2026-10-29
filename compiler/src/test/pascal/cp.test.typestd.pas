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
    { Int8 is a type of its own: signed, one byte, -128..127 }
    procedure TestSem_Int8_SignedOneByte;
    { a constant assignment to Int8 follows the same rule as Byte: plain
      integer types are not range-checked (only subranges and enums are) }
    procedure TestSem_Int8_ConstAssignment_RuleMatchesByte;
    { Int8 and Byte are different types: an overload pair on them is legal }
    procedure TestSem_Int8AndByte_DistinctOverloads;
    { an Int8 read sign-extends on both ISAs (movsbq / the lsl-asr pair) }
    procedure TestAsm_Int8Read_SignExtends;
    { Phase 4.3 (D4): an unhinted literal is Int, so F(42) and F(N) with an
      untyped constant N resolve against an Int32 / Int64 pair instead of
      being ambiguous, and a lone Int32 parameter still takes the literal }
    procedure TestSem_UnhintedLiteral_ResolvesToInt;
    { Phase 4.4 (D5): Length, Pos, PosEx, SizeOf, Ord and the index-bound
      High/Low of strings and arrays are Int; the ordinal High/Low keep
      their argument's type, and Ord of a UInt64 keeps UInt64 }
    procedure TestSem_BuiltinResults_AreInt;
    { Phase 4.4: only an Int that cannot be negative (Length, SizeOf, Ord
      of an unsigned ordinal) mixes with a UInt64 without a cast; Pos and
      High may be -1, and Ord of a signed value may be negative }
    procedure TestSem_MayBeNegativeInt_NeedsCastForUInt64;
    { Phase 4.5: the allocator takes an Int64 size, so GetMem of an Integer
      extends it (x86-64 passed its low 32 bits; arm64 its register as is) }
    procedure TestAsm_GetMemSize_Extended;
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

procedure TTypeStdTests.TestSem_Int8_SignedOneByte;
var
  Prog: TProgram;
  T: TTypeDesc;
begin
  Prog := Analyse('''
    program p;
    var X: Int8;
    begin
    end.
    ''');
  try
    T := Prog.SymbolTable.FindType('Int8');
    AssertNotNull('Int8 is a type', T);
    AssertTrue('Int8 is its own kind, not Byte',
      T <> Prog.SymbolTable.FindType('Byte'));
    AssertEquals('one byte', 1, T.RawSize());
    AssertTrue('an integer', T.IsNumeric() and T.IsOrdinal() and
      (not T.IsFloat()));
  finally
    Prog.Free();
  end;
end;

procedure TTypeStdTests.TestSem_Int8_ConstAssignment_RuleMatchesByte;
const
  Src = '''
    program p;
    var X: %s;
    begin
      X := 300
    end.
    ''';
begin
  AssertEquals('Int8 is checked exactly as Byte is',
    SemanticError(Format(Src, ['Byte'])), SemanticError(Format(Src, ['Int8'])));
  AssertEquals('-128 and 127 fit', '',
    SemanticError('''
      program p;
      var X: Int8;
      begin
        X := -128;
        X := 127
      end.
      '''));
end;

procedure TTypeStdTests.TestSem_UnhintedLiteral_ResolvesToInt;
begin
  AssertEquals('F(42) and F(N) resolve', '', SemanticError('''
    program p;
    const N = 42;
    procedure F(X: Int32); overload; begin end;
    procedure F(X: Int64); overload; begin end;
    begin
      F(42);
      F(N)
    end.
    '''));
  AssertEquals('a lone Int32 parameter takes the literal', '', SemanticError('''
    program p;
    procedure G(X: Int32); begin end;
    begin
      G(42)
    end.
    '''));
end;

procedure TTypeStdTests.TestSem_BuiltinResults_AreInt;
const
  Src = '''
    program p;
    type TE = (eA, eB);
    var
      L: Int64; S: string; A: array of Byte; SA: array[1..3] of Byte;
      I: Integer; B: Byte; E: TE; U: UInt64;
    begin
      L := Length(S);
      L := Length(A);
      L := Length(SA);
      L := Pos('a', S);
      L := PosEx('a', S, 1);
      L := SizeOf(I);
      L := Ord(I);
      L := Ord(B);
      L := Ord(E);
      L := Ord(True);
      L := High(S);
      L := High(A);
      L := Low(SA);
      L := High(I);
      U := Ord(U)
    end.
    ''';
  Expected: array[0..14] of TTypeKind = (tyInt64, tyInt64, tyInt64,
    tyInt64, tyInt64, tyInt64, tyInt64, tyInt64, tyInt64, tyInt64,
    tyInt64, tyInt64, tyInt64, tyInteger, tyUInt64);
var
  Prog: TProgram;
  K: Integer;
  Asg: TAssignment;
begin
  Prog := Analyse(Src);
  try
    for K := 0 to High(Expected) do
    begin
      Asg := TAssignment(Prog.Block.Stmts.Items[K]);
      AssertEquals('statement ' + IntToStr(K + 1), Ord(Expected[K]),
        Ord(TASTExpr(Asg.Expr).ResolvedType.Kind));
    end;
  finally
    Prog.Free();
  end;
end;

procedure TTypeStdTests.TestSem_MayBeNegativeInt_NeedsCastForUInt64;

  function Probe(const AStmt: string): string;
  begin
    Result := SemanticError(
      'program p; type TN = (nNeg = -1, nZero); var H: UInt64; S: string; ' +
      'I: Integer; EN: TN; begin ' + AStmt + ' end.');
  end;

begin
  AssertTrue('Pos', Pos('Cannot mix', Probe('H := H xor Pos(''a'', S)')) >= 0);
  AssertTrue('High', Probe('H := High(S)') <> '');
  AssertTrue('Ord of an Integer', Probe('H := H + Ord(I)') <> '');
  AssertTrue('Ord of an enum with a negative ordinal',
    Probe('H := Ord(EN)') <> '');
  AssertTrue('Length - 1 may be negative', Probe('H := Length(S) - 1') <> '');
  AssertEquals('Length, SizeOf and Ord of a Char adapt', '',
    Probe('H := Length(S); H := H + SizeOf(I); H := H xor Ord(S[0])'));
end;

procedure TTypeStdTests.TestAsm_GetMemSize_Extended;
const
  Src = '''
    program p;
    var N: Integer; Q: Pointer;
    begin
      N := 64;
      Q := GetMem(N);
      FreeMem(Q)
    end.
    ''';
begin
  AssertEquals('', '', AsmMissing(Src,
    'movslq %eax, %rax'#10#9'movq %rax, %rdi'#10#9'callq _BlaiseGetMem',
    'sxtw x0, w0'#10#9'bl __BlaiseGetMem'));
end;

procedure TTypeStdTests.TestSem_Int8AndByte_DistinctOverloads;
begin
  AssertEquals('', '', SemanticError('''
    program p;
    procedure F(X: Int8); overload; begin end;
    procedure F(X: Byte); overload; begin end;
    var A: Int8; B: Byte;
    begin
      F(A); F(B)
    end.
    '''));
end;

procedure TTypeStdTests.TestAsm_Int8Read_SignExtends;
const
  Src = '''
    program p;
    var X: Int8; Y: Int64;
    begin
      X := -1;
      Y := X;
      WriteLn(Y)
    end.
    ''';
begin
  AssertEquals('', '', AsmMissing(Src, 'movsbq', 'asr x0, x0, #56'));
end;

initialization
  RegisterTest(TTypeStdTests);

end.
