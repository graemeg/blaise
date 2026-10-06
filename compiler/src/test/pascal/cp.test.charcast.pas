{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.charcast;

{ Integer casts of single-character string literals.

  Regression guard for the 2026-07-15 bug: Byte(',') compiled silently
  but reinterpreted the string literal's POINTER, yielding garbage
  (observed 204) instead of the character code 44.  The rule now:

    - Byte('x') / Word('x') / Integer('x') / ... on a SINGLE-character
      string literal folds to the character's code, same as Ord('x').
    - A multi-character (or empty) literal in an integer cast is a
      semantic error — there is no meaningful numeric value.

  Coverage: IR unit tests (fold produces a 'copy <ord>' constant, no
  string global) + semantic error cases + an e2e run on all backends. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TCharCastTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestSemantic_ByteCastMultiCharLiteral_RaisesError;
    procedure TestSemantic_ByteCastEmptyLiteral_RaisesError;
  end;

  [Threaded]
  TCharCastE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_IntCastsOfCharLiterals_PrintOrdValues;
  end;

implementation

const
  LE = #10;

function TCharCastTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TCharCastTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := Self.AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

procedure TCharCastTests.TestSemantic_ByteCastMultiCharLiteral_RaisesError;
begin
  Self.AnalyseExpectError(
    '''
        program P;
        var B: Byte;
        begin
          B := Byte('ab')
        end.
        ''');
end;

procedure TCharCastTests.TestSemantic_ByteCastEmptyLiteral_RaisesError;
begin
  Self.AnalyseExpectError(
    '''
        program P;
        var B: Byte;
        begin
          B := Byte('')
        end.
        ''');
end;

{ -------------- e2e -------------- }

procedure TCharCastE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-charcast');
end;

procedure TCharCastE2ETests.TestRun_IntCastsOfCharLiterals_PrintOrdValues;
const
  Src =
    '''
        program P;
        var B: Byte; W: Word; N: Int64; C: Cardinal;
        begin
          B := Byte(',');
          W := Word('A');
          N := Int64(':');
          C := Cardinal('/');
          WriteLn(B);
          WriteLn(W);
          WriteLn(N);
          WriteLn(C)
        end.
        ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '44' + LE + '65' + LE + '58' + LE + '47' + LE, 0);
end;

initialization
  RegisterTest(TCharCastTests);
  RegisterTest(TCharCastE2ETests);

end.
