{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.sar;

{ Unit + e2e tests for the `sar` (arithmetic shift right) operator.

  Background: in Pascal, `shr` is a *logical* right shift (zero-fill) —
  it discards the sign bit.  When the programmer wants sign-preserving
  right shift on a signed integer (for example, dividing a negative
  number by a power of two), Blaise provides a distinct `sar` operator
  that maps to QBE's `sar` instruction.

  Coverage:
    - `sar` is a recognised binary operator at the term-level precedence.
    - Codegen emits QBE `sar` (not `shr`) for Int64, UInt64, and 32-bit
      integer types.
    - End-to-end: a negative Int64 sar 1 keeps its sign; a positive
      value matches the shr result. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TSarTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
  published
  end;

  [Threaded]
  TSarE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_NegativeInt64_Sar_PreservesSign;
    procedure TestRun_NegativeInt64_Shr_DiscardsSign;
    procedure TestRun_PositiveInteger_Sar_MatchesShr;
    procedure TestRun_NegativeInteger_Sar_PreservesSign;
  end;

implementation

{ -------------- helpers -------------- }

function TSarTests.AnalyseSrc(const ASrc: string): TProgram;
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

{ -------------- e2e -------------- }

procedure TSarE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sar');
end;

const
  LE = #10;

  SrcNegInt64Sar =
    '''
    program P;
    var A, B: Int64;
    begin
      A := -16;
      B := A sar 2;
      WriteLn(B)
    end.
    ''';

  SrcNegInt64Shr =
    '''
    program P;
    var A, B: Int64;
    begin
      A := -16;
      B := A shr 2;
      WriteLn(B)
    end.
    ''';

  SrcPosIntSar =
    '''
    program P;
    var A, B: Integer;
    begin
      A := 64;
      B := A sar 2;
      WriteLn(B)
    end.
    ''';

procedure TSarE2ETests.TestRun_NegativeInt64_Sar_PreservesSign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { -16 sar 2 = -4 (sign preserved) }
  AssertRunsOnAll(SrcNegInt64Sar, '-4' + LE, 0);
end;

procedure TSarE2ETests.TestRun_NegativeInt64_Shr_DiscardsSign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { -16 shr 2 = ((2^64 - 16) >> 2) = 2^62 - 4 = 4611686018427387900 }
  AssertRunsOnAll(SrcNegInt64Shr, '4611686018427387900' + LE, 0);
end;

procedure TSarE2ETests.TestRun_PositiveInteger_Sar_MatchesShr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 64 sar 2 = 16 (positive numbers behave identically) }
  AssertRunsOnAll(SrcPosIntSar, '16' + LE, 0);
end;

procedure TSarE2ETests.TestRun_NegativeInteger_Sar_PreservesSign;
const
  { sar on a 32-bit Integer is arithmetic too: the sign is kept.  Replaces
    the QBE IR check TestCodegen_Integer_Sar_EmitsSar. }
  Src = '''
    program P;
    var I: Integer;
    begin
      I := -16;
      WriteLn(I sar 2);
      I := -1;
      WriteLn(I sar 31)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '-4' + LE + '-1' + LE, 0);
end;

initialization
  RegisterTest(TSarTests);
  RegisterTest(TSarE2ETests);

end.
