{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for ClassicPascalTypes.  Self-registers via the initialization
  section. }

unit ClassicPascalTypes.Tests;

interface

uses
  blaise.testing, ClassicPascalTypes;

type
  TClassicPascalTypesTests = class(TTestCase)
  published
    { every classic name has the width of the type it maps to }
    procedure TestWidths;
    { the classic integer names keep their signedness and range }
    procedure TestSignednessAndRange;
    { a classic name IS its modern type: values move both ways uncast }
    procedure TestInterchangeableWithModernNames;
    { Real and Extended are Float64 -- full double precision, on every
      platform (Extended is not the x87 80-bit type) }
    procedure TestRealAndExtended_AreFloat64;
    { Comp is a 64-bit integer, as it always was }
    procedure TestComp_IsInt64;
    { Each classic name has its pointer alias, and it is the same type as
      the pointer to the modern name it maps to. }
    procedure TestPointerAliases;
    { The names that were builtins until type standardisation Phase 6
      (Integer, Cardinal, SmallInt, Word, QWord, PtrUInt, Single, Double) are
      declared here at their widths, with their pointer aliases. }
    procedure TestRetiredBuiltins_AreTheirWidths;
  end;

implementation

procedure TClassicPascalTypesTests.TestRetiredBuiltins_AreTheirWidths;
var
  I: Integer;
  I32: Int32;
  C: Cardinal;
  U32: UInt32;
  D: Double;
  F64: Float64;
  P: PInteger;
  Q: PInt32;
begin
  AssertEquals('Integer', 4, SizeOf(Integer));
  AssertEquals('Cardinal', 4, SizeOf(Cardinal));
  AssertEquals('SmallInt', 2, SizeOf(SmallInt));
  AssertEquals('Word', 2, SizeOf(Word));
  AssertEquals('QWord', 8, SizeOf(QWord));
  AssertEquals('PtrUInt', SizeOf(Pointer), SizeOf(PtrUInt));
  AssertEquals('Single', 4, SizeOf(Single));
  AssertEquals('Double', 8, SizeOf(Double));
  I := -7; I32 := I; I := I32;
  AssertEquals('Integer is Int32', -7, I);
  C := 4294967295; U32 := C; C := U32;
  AssertTrue('Cardinal is UInt32', C = 4294967295);
  D := 1.5; F64 := D; D := F64;
  AssertTrue('Double is Float64', D = 1.5);
  Q := @I32; P := Q; Q := P;
  AssertTrue('PInteger is PInt32', Q^ = -7);
end;

procedure TClassicPascalTypesTests.TestWidths;
begin
  AssertEquals('ShortInt', 1, SizeOf(ShortInt));
  AssertEquals('LongInt', 4, SizeOf(LongInt));
  AssertEquals('LongWord', 4, SizeOf(LongWord));
  AssertEquals('NativeInt', SizeOf(Pointer), SizeOf(NativeInt));
  AssertEquals('NativeUInt', SizeOf(Pointer), SizeOf(NativeUInt));
  AssertEquals('PtrInt', SizeOf(Pointer), SizeOf(PtrInt));
  AssertEquals('Real', 8, SizeOf(Real));
  AssertEquals('Extended', 8, SizeOf(Extended));
  AssertEquals('Comp', 8, SizeOf(Comp));
end;

procedure TClassicPascalTypesTests.TestSignednessAndRange;
var
  S: ShortInt;
  L: LongInt;
  W: LongWord;
  N: NativeInt;
begin
  S := -1;
  AssertTrue('ShortInt is signed', S < 0);
  AssertTrue('Low(ShortInt)', Low(ShortInt) = -128);
  AssertTrue('High(ShortInt)', High(ShortInt) = 127);
  L := 2147483647;
  L := L + 1;
  AssertTrue('LongInt wraps to its minimum', L < 0);
  W := 4294967295;
  AssertTrue('LongWord is unsigned', W > 0);
  N := -5;
  AssertTrue('NativeInt is signed', N < 0);
end;

procedure TClassicPascalTypesTests.TestInterchangeableWithModernNames;
var
  L: LongInt;
  I32: Int32;
  W: LongWord;
  U32: UInt32;
  S: ShortInt;
  I8: Int8;
  N: NativeInt;
  P: PtrInt;
  I: Int;
  NU: NativeUInt;
  U: UInt;
begin
  I32 := -7;
  L := I32;
  I32 := L;
  U32 := 9;
  W := U32;
  U32 := W;
  I8 := -3;
  S := I8;
  I8 := S;
  I := 5000000000;
  N := I;
  P := N;
  I := P;
  U := 6;
  NU := U;
  U := NU;
  AssertEquals('LongInt', -7, I32);
  AssertTrue('LongWord', U32 = 9);
  AssertTrue('ShortInt', I8 = -3);
  AssertTrue('NativeInt / PtrInt', I = 5000000000);
  AssertTrue('NativeUInt', U = 6);
end;

procedure TClassicPascalTypesTests.TestRealAndExtended_AreFloat64;
var
  R: Real;
  E: Extended;
  F: Float64;
  F32: Float32;
begin
  F := 1.0;
  F := F / 3.0;
  R := 1.0;
  R := R / 3.0;
  E := 1.0;
  E := E / 3.0;
  F32 := F;
  AssertTrue('Real computes as Float64', R = F);
  AssertTrue('Extended computes as Float64', E = F);
  AssertTrue('and differs from Float32', R <> F32);
end;

procedure TClassicPascalTypesTests.TestComp_IsInt64;
var
  C: Comp;
  L: Int64;
begin
  C := 5000000000;
  C := C * 2;
  L := C;
  AssertTrue('Comp holds 64-bit integers', L = 10000000000);
end;

procedure TClassicPascalTypesTests.TestPointerAliases;
var
  L: LongInt;
  S: ShortInt;
  W: LongWord;
  R: Real;
  PL: PLongInt;
  PS: PShortInt;
  PW: PLongWord;
  PR: PReal;
  PE: PExtended;
  PC: PComp;
  PN: PNativeInt;
  PNU: PNativeUInt;
  PPI: PPtrInt;
  P32: PInt32;
begin
  PL := @L; PS := @S; PW := @W; PR := @R;
  PL^ := -5; PS^ := -6; PW^ := 7; PR^ := 1.5;
  AssertEquals('PLongInt', -5, L);
  AssertEquals('PShortInt', -6, S);
  AssertEquals('PLongWord', 7, W);
  AssertTrue('PReal', R = 1.5);
  P32 := PL;          { PLongInt is ^Int32 }
  PE := PR;           { PExtended and PReal are ^Float64 }
  AssertEquals('via PInt32', -5, P32^);
  AssertTrue('via PExtended', PE^ = 1.5);
  PC := nil; PN := nil; PNU := nil; PPI := nil;
  AssertTrue('remaining aliases declared',
    (PC = nil) and (PN = nil) and (PNU = nil) and (PPI = nil));
end;

initialization
  RegisterTest(TClassicPascalTypesTests);

end.
