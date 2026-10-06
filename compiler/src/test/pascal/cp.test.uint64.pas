{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.uint64;

{ Unit + e2e tests for the UInt64 / QWord type.

  Coverage:
    - UInt64 and QWord both resolve to the same type descriptor.
    - SizeOf(UInt64) = SizeOf(QWord) = 8.
    - Mixing Int64 and UInt64 in an expression is a type error.
    - Comparisons use unsigned QBE comparison instructions (cugtl, cultl, ...).
    - Arithmetic uses udiv/urem for division/modulo.
    - Decimal literal in the (2^63, 2^64-1) range parses as UInt64.
    - End-to-end WriteLn / IntToStr / UInt64ToStr round-trip. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TUInt64Tests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestSemantic_UInt64_TypeRegistered;
    procedure TestSemantic_QWord_TypeRegistered;
    procedure TestSemantic_QWordIsAliasOfUInt64;
    procedure TestSemantic_PtrUInt_IsUInt64;
    procedure TestSemantic_UInt64_Plus_Int64_IsError;
    procedure TestSemantic_LargeLiteralResolvesAsUInt64;
  end;

  [Threaded]
  TUInt64E2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_UInt64_UnsignedSemantics;
    procedure TestRun_UInt64_RoundTrip;
    procedure TestRun_QWord_Alias;
    procedure TestRun_UInt64_LargeLiteral;
    procedure TestRun_UInt64_Arithmetic;
    procedure TestRun_UInt64_UnsignedCompare;
    procedure TestRun_Int64_MinValue;
    { Regression: a const declared with the value-cast form
      cMax = Int64(922337203685477580) must lower the large literal with the
      'l' (64-bit) type — through const folding, arithmetic, and argument
      positions.  The QBE backend once emitted a 'w'-typed operand here and
      QBE rejected the IR ("invalid type for first operand ... in arg"). }
    procedure TestRun_Int64_LargeLiteralCast;
    { BUG-026: an unsigned 32-bit RHS (Cardinal) stored into a 64-bit slot
      must ZERO-extend (extuw), not sign-extend — otherwise a Cardinal >= 2^31
      is smeared to a negative Int64.  Covers variable, field, array-element,
      and argument-coercion store sites (QBE previously wrong; native correct). }
    procedure TestRun_CardinalToInt64_AllStoreSites;
    { BUG-026 (expression sites): a Cardinal >= 2^31 must also keep its
      magnitude through Format args, the explicit Int64() cast, Int64
      comparisons, Int64 arithmetic, Int64 bitwise ops (QBE previously
      sign-extended each), and IntToStr (both backends previously routed
      to the signed 32-bit _IntToStr). }
    procedure TestRun_CardinalToInt64_ExprSites;
  end;

implementation

{ -------------- helpers -------------- }

function TUInt64Tests.AnalyseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
  A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

procedure TUInt64Tests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

{ -------------- semantic -------------- }

procedure TUInt64Tests.TestSemantic_UInt64_TypeRegistered;
const
  Src =
    '''
        program P;
        var X: UInt64;
        begin end.
        ''';
var
  Prog: TProgram;
  T:    TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    T := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertTrue('UInt64 resolves',     T <> nil);
    AssertEquals('Kind = tyUInt64', Ord(tyUInt64), Ord(T.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_QWord_TypeRegistered;
const
  Src =
    '''
        program P;
        var X: QWord;
        begin end.
        ''';
var
  Prog: TProgram;
  T:    TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    T := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertTrue('QWord resolves',      T <> nil);
    AssertEquals('Kind = tyUInt64', Ord(tyUInt64), Ord(T.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_QWordIsAliasOfUInt64;
const
  Src =
    '''
        program P;
        var A: UInt64;
        var B: QWord;
        begin end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertSame('UInt64 and QWord share one descriptor',
      TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType,
      TVarDecl(Prog.Block.Decls.Items[1]).ResolvedType);
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_PtrUInt_IsUInt64;
const
  Src =
    '''
        program P;
        var P1: PtrUInt;
        begin end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('PtrUInt has Kind=tyUInt64', Ord(tyUInt64),
      Ord(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_UInt64_Plus_Int64_IsError;
begin
  AnalyseExpectError(
    '''
        program P;
        var U: UInt64;
        var I: Int64;
        begin
          U := U + I
        end.
        ''');
end;

procedure TUInt64Tests.TestSemantic_LargeLiteralResolvesAsUInt64;
const
  { 18000000000000000000 is larger than MaxInt64 (9223372036854775807) but
    fits in UInt64. }
  Src =
    '''
        program P;
        var U: UInt64;
        begin
          U := 18000000000000000000
        end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  Prog.Free();
end;

{ -------------- e2e -------------- }

procedure TUInt64E2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-uint64');
end;

const
  LE = #10;

  SrcUInt64RoundTrip =
    '''
    program P;
    var U: UInt64;
    begin
      U := 42;
      WriteLn(U)
    end.
    ''';

  SrcQWordAlias =
    '''
    program P;
    var Q: QWord;
    begin
      Q := 100;
      WriteLn(Q)
    end.
    ''';

  SrcUInt64LargeLiteral =
    '''
    program P;
    var U: UInt64;
    begin
      U := 18000000000000000000;
      WriteLn(U)
    end.
    ''';

  SrcUInt64Arithmetic =
    '''
    program P;
    var A, B, S: UInt64;
    begin
      A := 1000000;
      B := 2000003;
      S := A + B;
      WriteLn(S);
      WriteLn(B div A);
      WriteLn(B mod A)
    end.
    ''';

  SrcUInt64UnsignedCompare =
    '''
    program P;
    var A, B: UInt64;
    begin
      { 17000000000000000000 > MaxInt64 — must be treated as unsigned. }
      A := 17000000000000000000;
      B := 1;
      if A > B then WriteLn('yes') else WriteLn('no')
    end.
    ''';

  { Low(Int64) = -9223372036854775808 has no positive counterpart, so a
    naive negate-then-extract-digits path overflows and prints only '-'.
    WriteDecimal must handle the most-negative value correctly. }
  SrcInt64MinValue =
    '''
    program P;
    var N: Int64;
    begin
      N := Int64(1) shl 63;
      WriteLn(N)
    end.
    ''';

  SrcInt64LargeLiteralCast =
    '''
    program P;
    const
      cMax = Int64(922337203685477580);
    procedure Show(V: Int64);
    begin WriteLn(V) end;
    var N: Int64;
    begin
      Show(cMax);
      N := cMax div 10;
      Show(N);
      WriteLn(Int64(922337203685477580))
    end.
    ''';

  { BUG-026: Cardinal 4000000000 (>= 2^31) stored into Int64 slots through
    every store site must keep its unsigned value, not become negative.
    QBE previously emitted extsw at each site and printed -294967296. }
  SrcCardinalToInt64AllSites =
    '''
    program P;
    type TRec = record V: Int64; end;
    procedure Show(N: Int64);
    begin WriteLn(N) end;
    var
      C:   Cardinal;
      V:   Int64;
      R:   TRec;
      Arr: array[0..1] of Int64;
    begin
      C := 4000000000;
      V := C;         { scalar variable store }
      WriteLn(V);
      R.V := C;       { record field store }
      WriteLn(R.V);
      Arr[0] := C;    { array-element store }
      WriteLn(Arr[0]);
      Show(C)         { argument coercion w -> l }
    end.
    ''';

  { BUG-026 expression sites: Cardinal 4000000000 through Format args, the
    Int64() cast, Int64 comparison/arithmetic/bitwise operands, and IntToStr
    must keep its unsigned magnitude on both backends. }
  SrcCardinalToInt64ExprSites =
    '''
    program P;
    uses sysutils;
    var
      C:   Cardinal;
      I64: Int64;
    begin
      C := 4000000000;
      WriteLn(Format('%d', [C]));       { Format arg boxing }
      I64 := Int64(C);                  { explicit cast }
      WriteLn(I64);
      I64 := 3999999999;
      if C > I64 then                   { comparison operand }
        WriteLn('gt-ok')
      else
        WriteLn('gt-BAD');
      I64 := 0;
      I64 := I64 + C;                   { arithmetic operand }
      WriteLn(I64);
      I64 := -1;
      I64 := I64 and C;                 { bitwise operand }
      WriteLn(I64);
      WriteLn(IntToStr(C))              { IntToStr routing }
    end.
    ''';

procedure TUInt64E2ETests.TestRun_UInt64_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64RoundTrip, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('42', '42' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_QWord_Alias;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcQWordAlias, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('100', '100' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_UInt64_LargeLiteral;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64LargeLiteral, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('large literal round-trips',
    '18000000000000000000' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_UInt64_Arithmetic;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64Arithmetic, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('sum, div, mod',
    '3000003' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_UInt64_UnsignedCompare;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64UnsignedCompare, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('17e18 > 1 unsigned',
    'yes' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_Int64_MinValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64MinValue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Low(Int64) prints in full',
    '-9223372036854775808' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_Int64_LargeLiteralCast;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInt64LargeLiteralCast,
    '922337203685477580' + LE +
    '92233720368547758' + LE +
    '922337203685477580' + LE, 0);
end;

procedure TUInt64E2ETests.TestRun_CardinalToInt64_AllStoreSites;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { All four store sites must preserve the unsigned magnitude on both backends. }
  AssertRunsOnAll(SrcCardinalToInt64AllSites,
    '4000000000' + LE +
    '4000000000' + LE +
    '4000000000' + LE +
    '4000000000' + LE, 0);
end;

procedure TUInt64E2ETests.TestRun_CardinalToInt64_ExprSites;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Every expression site must preserve the unsigned magnitude on both
    backends: Format, Int64() cast, comparison, arithmetic, bitwise,
    IntToStr. }
  AssertRunsOnAll(SrcCardinalToInt64ExprSites,
    '4000000000' + LE +
    '4000000000' + LE +
    'gt-ok' + LE +
    '4000000000' + LE +
    '4000000000' + LE +
    '4000000000' + LE, 0);
end;

procedure TUInt64E2ETests.TestRun_UInt64_UnsignedSemantics;
const
  {
    UInt64 and QWord are 8 bytes; UInt64 comparison, div and mod are UNSIGNED
    (2^63 is larger than 1); a large Int64 literal keeps all 64 bits; a Cardinal
    above 2^31 zero-extends into an Int64 variable, record field or cast; IntToStr
    formats a UInt64 unsigned.  Replaces the QBE IR
    checks in cp.test.uint64. }
  Src = '''
    program P;
    var A, B, Big: UInt64; Q: QWord; C: Cardinal; V, N: Int64; S: string;
    type TRec = record V: Int64; end;
    var R: TRec;
    begin
      WriteLn(SizeOf(UInt64), ' ', SizeOf(QWord), ' ', SizeOf(Q));
      Big := 1;
      Big := Big shl 63;
      A := Big;
      B := 1;
      WriteLn(A < B, ' ', A > B, ' ', B < A);
      A := Big + 10;
      B := 3;
      WriteLn(A div B, ' ', A mod B);
      N := Int64(922337203685477580);
      WriteLn(N);
      C := 4000000000;
      V := C;
      WriteLn(V);
      R.V := C;
      WriteLn(R.V);
      V := Int64(C);
      WriteLn(V);
      S := IntToStr(Big);
      WriteLn(S)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '8 8 8' + LE +
    'False True True' + LE +
    '3074457345618258606 0' + LE +
    '922337203685477580' + LE +
    '4000000000' + LE +
    '4000000000' + LE +
    '4000000000' + LE +
    '9223372036854775808' + LE, 0);
end;

initialization
  RegisterTest(TUInt64Tests);
  RegisterTest(TUInt64E2ETests);

end.
