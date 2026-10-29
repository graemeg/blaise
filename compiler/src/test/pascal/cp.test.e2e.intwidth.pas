{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.intwidth;

{ E2E tests: integer expression width
  (BUG-20261027-int32-overflow-not-wrapped).

  With I = High(Integer), I + 1 printed -2147483648 on x86-64 and
  2147483648 on arm64, (I + 1) div 2 was 1073741824 on both, and the value
  depended on the consumer.  Arithmetic on operands narrower than 64 bits is
  now promoted to Int64; shifts wrap at 32 bits; not keeps its operand's
  width.  The expected values match FPC on a 64-bit target. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EIntWidthTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { High(Integer) + 1 has one value, whatever consumes it }
    procedure TestRun_IntegerOverflow_EveryConsumer;
    { the promotion for every narrow kind; storing back truncates }
    procedure TestRun_PromotedArithmetic_EveryKind;
    { shl/shr/sar wrap at 32 bits; narrow operands shift as 32 bits }
    procedure TestRun_Shifts_WrapAt32Bits;
    { not keeps its operand's width }
    procedure TestRun_Not_KeepsWidth;
    { a mixed Int32/UInt32 pair keeps both values }
    procedure TestRun_MixedSign_Bitwise;
    { overload resolution follows the promoted type }
    procedure TestRun_Overload_FollowsPromotedType;
    { a narrow integer compared with an Int64 / UInt64 operand, on either
      side, is extended from its own type first: x86-64 took the compare
      width from the left operand alone, so Integer < Int64 compared 32
      bits of the Int64 }
    procedure TestRun_MixedWidthCompare_ExtendsNarrowSide;
  end;

implementation

const
  LE = #10;

procedure TE2EIntWidthTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-intwidth');
end;

procedure TE2EIntWidthTests.TestRun_IntegerOverflow_EveryConsumer;
const
  Src = '''
    program P;
    uses SysUtils;
    var I, J: Integer;
    begin
      I := High(Integer);
      WriteLn(I + 1);
      WriteLn(IntToStr(I + 1));
      WriteLn(Format('%d', [I + 1]));
      WriteLn((I + 1) div 2);
      WriteLn((I + 1) shr 1);
      if I + 1 > I then WriteLn('gt') else WriteLn('le');
      J := I + 1;
      WriteLn(J);
      WriteLn(I * 2);
      WriteLn(-I - 2);
      I := Low(Integer);
      WriteLn(-I);
      WriteLn(I div -1);
      WriteLn(I - 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2147483648' + LE + '2147483648' + LE + '2147483648' + LE +
    '1073741824' + LE + '1073741824' + LE + 'gt' + LE +
    '-2147483648' + LE + '4294967294' + LE + '-2147483649' + LE +
    '2147483648' + LE + '2147483648' + LE + '-2147483649' + LE, 0);
end;

procedure TE2EIntWidthTests.TestRun_PromotedArithmetic_EveryKind;
const
  Src = '''
    program P;
    var U: UInt32; S: SmallInt; W: Word; K: Int8; B, C, B2: Byte;
    begin
      U := High(UInt32);
      WriteLn(U + 1);
      WriteLn(U * 2);
      S := High(SmallInt);
      WriteLn(S + 1);
      S := Low(SmallInt);
      WriteLn(S - 1);
      W := High(Word);
      WriteLn(W + 1);
      K := Low(Int8);
      WriteLn(K - 1);
      WriteLn(-K);
      B := 255;
      C := 1;
      WriteLn(B + C);
      WriteLn(C - B);
      B2 := B + C;
      WriteLn(B2)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '4294967296' + LE + '8589934590' + LE + '32768' + LE + '-32769' + LE +
    '65536' + LE + '-129' + LE + '128' + LE + '256' + LE + '-254' + LE +
    '0' + LE, 0);
end;

procedure TE2EIntWidthTests.TestRun_Shifts_WrapAt32Bits;
const
  Src = '''
    program P;
    var I, N: Integer; U: UInt32; B: Byte; W: Word; K: Int8;
    begin
      N := 1;
      I := -1;
      WriteLn(I shr 1);
      WriteLn(I shr N);
      WriteLn(I sar 1);
      WriteLn(I sar N);
      I := 1;
      WriteLn(I shl 31);
      I := High(Integer);
      WriteLn((I shl 1) div 2);
      WriteLn((I shl N) div 2);
      U := High(UInt32);
      WriteLn(U shl 1);
      WriteLn((U shl 1) div 2);
      WriteLn(U shr 31);
      B := 200;
      WriteLn(B shl 8);
      W := High(Word);
      WriteLn(W shl 16);
      K := -1;
      WriteLn(K shr 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2147483647' + LE + '2147483647' + LE + '-1' + LE + '-1' + LE +
    '-2147483648' + LE + '-1' + LE + '-1' + LE +
    '4294967294' + LE + '2147483647' + LE + '1' + LE +
    '51200' + LE + '4294901760' + LE + '2147483647' + LE, 0);
end;

procedure TE2EIntWidthTests.TestRun_Not_KeepsWidth;
const
  Src = '''
    program P;
    var B: Byte; W: Word; S: SmallInt; U: UInt32; I: Integer;
    begin
      B := 200;
      WriteLn(not B);
      WriteLn((not B) + 1);
      W := 0;
      WriteLn(not W);
      S := -1;
      WriteLn(not S);
      U := 0;
      WriteLn(not U);
      WriteLn((not U) div 2);
      I := 0;
      WriteLn(not I);
      WriteLn((not I) + 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '55' + LE + '56' + LE + '65535' + LE + '0' + LE + '4294967295' + LE +
    '2147483647' + LE + '-1' + LE + '0' + LE, 0);
end;

procedure TE2EIntWidthTests.TestRun_MixedSign_Bitwise;
const
  Src = '''
    program P;
    var I: Integer; U: UInt32;
    begin
      I := -1;
      U := High(UInt32);
      WriteLn(I and U);
      WriteLn(I + U);
      WriteLn(I or 0)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '4294967295' + LE + '4294967294' + LE + '-1' + LE, 0);
end;

procedure TE2EIntWidthTests.TestRun_Overload_FollowsPromotedType;
const
  Src = '''
    program P;
    procedure F(X: Integer); overload; begin WriteLn('Int32 ', X) end;
    procedure F(X: Int64); overload; begin WriteLn('Int64 ', X) end;
    var I: Integer;
    begin
      I := High(Integer);
      F(I);
      F(I + 1);
      F(5 - 1);
      F(I - 3)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { F(5 - 1) is a constant expression with no hint, so Int (D4) }
  AssertRunsOnAll(Src,
    'Int32 2147483647' + LE + 'Int64 2147483648' + LE + 'Int64 4' + LE +
    'Int64 2147483644' + LE, 0);
end;

procedure TE2EIntWidthTests.TestRun_MixedWidthCompare_ExtendsNarrowSide;
const
  Src = '''
    program P;
    var
      I: Integer; L: Int64; U: UInt32; Q: UInt64; S: SmallInt; W: Word;
      B: Byte; E: Int8;
    function Neg(X: Integer): Integer; begin Result := -X end;
    begin
      I := 0; L := Int64(1) shl 32;
      WriteLn(I < L, ' ', I = L, ' ', I <> L, ' ', L > I, ' ', L = I);
      if I < L then WriteLn('branch lt') else WriteLn('branch ge');
      if I = L then WriteLn('branch eq') else WriteLn('branch ne');
      I := Neg(5); L := -5;
      WriteLn(I = L, ' ', I < L + 1, ' ', L = I);
      I := ($FE shl 24) or $ED; L := -33554195;
      WriteLn(I = L, ' ', L = I);
      U := $FFFFFFFF; Q := UInt64(1) shl 32;
      WriteLn(U < Q, ' ', U = Q, ' ', Q > U);
      L := Int64(1) shl 40;
      S := -1; W := $FFFF; B := 255; E := -1;
      WriteLn(S < L, ' ', W < L, ' ', B < L, ' ', E < L);
      L := -1;
      WriteLn(S = L, ' ', W = L, ' ', B = L, ' ', E = L)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'True False True True False' + #10 +
    'branch lt' + #10 +
    'branch ne' + #10 +
    'True True True' + #10 +
    'True True' + #10 +
    'True False True' + #10 +
    'True True True True' + #10 +
    'True False False True' + #10, 0);
end;

initialization
  RegisterTest(TE2EIntWidthTests);
end.
