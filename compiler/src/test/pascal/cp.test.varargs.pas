{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.varargs;

{ The 'varargs' directive: C-variadic external declarations.

    function printf(AFormat: PChar): Integer; cdecl; varargs; external 'c';

  Call sites may pass extra arguments after the declared parameters.
  QBE receives the '...' marker at the fixed/variadic boundary (its
  backend then applies the C variadic ABI); the native x86_64 backend
  already passes SysV register sequences and the AL vector count for
  every call, so extras flow through unchanged.

  Semantic rules covered here:
    - varargs requires 'external'
    - varargs cannot combine with 'overload'
    - fewer args than fixed parameters is still an arity error
    - a Blaise string extra is rejected (pass PChar(...))
    - a Single extra is rejected (C promotes float to double) }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TVarArgsTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestParse_VarArgsDirective_SetsFlag;
    procedure TestSemantic_VarArgsWithoutExternal_RaisesError;
    procedure TestSemantic_TooFewArgs_RaisesError;
    procedure TestSemantic_StringExtra_RaisesError;
    procedure TestSemantic_SingleExtra_RaisesError;
  end;

  [Threaded]
  TVarArgsE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Printf_IntStringDouble;
  end;

implementation

const
  LE = #10;

function TVarArgsTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TVarArgsTests.AnalyseExpectError(const ASrc: string);
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

procedure TVarArgsTests.TestParse_VarArgsDirective_SetsFlag;
var
  Prog: TProgram;
  I: Integer;
  Found: Boolean;
begin
  Prog := Self.AnalyseSrc(
    '''
        program P;
        function printf(AFormat: PChar): Integer; cdecl; varargs; external 'c' name 'printf';
        begin
        end.
        ''');
  Found := False;
  for I := 0 to Prog.Block.ProcDecls.Count - 1 do
    if TMethodDecl(Prog.Block.ProcDecls.Items[I]).IsVarArgs then
      Found := True;
  AssertTrue('IsVarArgs set', Found);
  Prog.Free();
end;

procedure TVarArgsTests.TestSemantic_VarArgsWithoutExternal_RaisesError;
begin
  Self.AnalyseExpectError(
    '''
        program P;
        function F(A: Integer): Integer; varargs;
        begin
          Result := A
        end;
        begin
        end.
        ''');
end;

procedure TVarArgsTests.TestSemantic_TooFewArgs_RaisesError;
begin
  Self.AnalyseExpectError(
    '''
        program P;
        function xprintf(AFormat: PChar; AMode: Integer): Integer; cdecl; varargs; external 'c' name 'printf';
        begin
          xprintf(PChar('x'))
        end.
        ''');
end;

procedure TVarArgsTests.TestSemantic_StringExtra_RaisesError;
begin
  Self.AnalyseExpectError(
    '''
        program P;
        function printf(AFormat: PChar): Integer; cdecl; varargs; external 'c' name 'printf';
        var S: string;
        begin
          S := 'abc';
          printf(PChar('%s'), S)
        end.
        ''');
end;

procedure TVarArgsTests.TestSemantic_SingleExtra_RaisesError;
begin
  Self.AnalyseExpectError(
    '''
        program P;
        function printf(AFormat: PChar): Integer; cdecl; varargs; external 'c' name 'printf';
        var F: Single;
        begin
          F := 1.5;
          printf(PChar('%f'), F)
        end.
        ''');
end;

{ -------------- e2e -------------- }

procedure TVarArgsE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-varargs');
end;

procedure TVarArgsE2ETests.TestRun_Printf_IntStringDouble;
const
  Src =
    '''
        program P;
        function printf(AFormat: PChar): Integer; cdecl; varargs; external 'c' name 'printf';
        var
          N: Integer;
          D: Double;
        begin
          N := 42;
          D := 3.5;
          printf(PChar('int %d str %s float %.2f' + #10), N, PChar('hello'), D);
          printf(PChar('six %d %d %d %d %d %d' + #10), 1, 2, 3, 4, 5, 6);
          printf(PChar('plain' + #10))
        end.
        ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'int 42 str hello float 3.50' + LE + 'six 1 2 3 4 5 6' + LE +
    'plain' + LE, 0);
end;

initialization
  RegisterTest(TVarArgsTests);
  RegisterTest(TVarArgsE2ETests);

end.
