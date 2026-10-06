{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.sizeof;

{ Unit + e2e tests for the SizeOf intrinsic.

  Coverage:
    - SizeOf(TypeName) folds to a literal byte size.
    - SizeOf(variable) folds to the byte size of the variable's type.
    - SizeOf(record-field-access) folds to the field type's byte size.
    - End-to-end WriteLn(SizeOf(var)) prints the expected size. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TSizeOfTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
  published
  end;

  [Threaded]
  TSizeOfE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_SizeOf_VarsRecordsFields;
    procedure TestRun_SizeOf_Variable_PrintsTypeSize;
  end;

implementation

const
  LE = #10;

{ -------------- helpers -------------- }

function TSizeOfTests.AnalyseSrc(const ASrc: string): TProgram;
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

{ -------------- e2e tests -------------- }

procedure TSizeOfE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sizeof');
end;

procedure TSizeOfE2ETests.TestRun_SizeOf_Variable_PrintsTypeSize;
const
  Src =
    '''
        program P;
        var X: Integer; B: Byte;
        begin
          WriteLn(SizeOf(X));
          WriteLn(SizeOf(B))
        end.
        ''';
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('SizeOf(X)=4 then SizeOf(B)=1', '4' + LE + '1' + LE, Output);
end;

procedure TSizeOfE2ETests.TestRun_SizeOf_VarsRecordsFields;
const
  {
    SizeOf on a variable, a record variable (with alignment padding) and a
    record field gives its size in bytes.  Replaces the QBE IR checks in
    cp.test.sizeof. }
  Src = '''
    program P;
    type
      Trec = record a: Integer; b: Byte; c: UInt32; end;
    var X: Integer; B: Byte; Q: Int64; T: Trec;
    begin
      WriteLn(SizeOf(X), ' ', SizeOf(B), ' ', SizeOf(Q));
      WriteLn(SizeOf(T), ' ', SizeOf(T.b))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '4 1 8' + LE +
    '12 1' + LE, 0);
end;

initialization
  RegisterTest(TSizeOfTests);
  RegisterTest(TSizeOfE2ETests);

end.
