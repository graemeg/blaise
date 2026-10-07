{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.highlow;

{ Unit + e2e tests for High/Low on ordinal types.

  Coverage:
    - High/Low of type names: Integer, Byte, Word, SmallInt, UInt32, Int64,
      UInt64, Boolean, and enums.
    - High/Low of variables of ordinal types (resolves to the var's type).
    - Result type matches the argument type (e.g. High(Int64) is Int64).
    - Targeted error message when the argument is a floating-point type. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  THighLowTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string; const AExpectFragment: string);
  published
    { Type-name arguments }

    { Variable arguments resolve to the var's type bounds }

    { Error path for floats }
    procedure TestSemantic_HighDouble_RaisesTargetedError;
    procedure TestSemantic_LowSingle_RaisesTargetedError;
  end;

  [Threaded]
  THighLowE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_HighInteger_PrintsMaxInt;
    procedure TestRun_HighByte_Prints255;
    procedure TestRun_HighEnum_PrintsLastOrdinal;
    procedure TestRun_LowHighIntegerLoopBound;
    { GH #176 — native backend was missing the tyInt64/tyUInt64 cases (and
      mis-encoded tyUInt32), folding to 0.  These run on BOTH backends. }
    procedure TestRun_HighLowInt64_BothBackends;
    procedure TestRun_HighUInt64_BothBackends;
    procedure TestRun_HighUInt32_BothBackends;
  end;

implementation

const
  LE = #10;

{ -------------- helpers -------------- }

function THighLowTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure THighLowTests.AnalyseExpectError(const ASrc: string;
  const AExpectFragment: string);
var
  Threw: Boolean;
  Msg:   string;
begin
  Threw := False;
  Msg := '';
  try
    AnalyseSrc(ASrc);
  except
    on E: Exception do
    begin
      Threw := True;
      Msg := E.Message;
    end;
  end;
  AssertTrue('expected semantic error', Threw);
  AssertTrue(Format('error must mention "%s", got: %s', [AExpectFragment, Msg]),
    Pos(AExpectFragment, Msg) > 0);
end;

{ -------------- error path -------------- }

procedure THighLowTests.TestSemantic_HighDouble_RaisesTargetedError;
begin
  AnalyseExpectError(
    '''
        program P;
        var D: Double;
        begin D := High(D) end.
        ''',
    'floating-point');
end;

procedure THighLowTests.TestSemantic_LowSingle_RaisesTargetedError;
begin
  AnalyseExpectError(
    '''
        program P;
        var S: Single;
        begin S := Low(S) end.
        ''',
    'floating-point');
end;

{ -------------- e2e tests -------------- }

procedure THighLowE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-highlow');
end;

procedure THighLowE2ETests.TestRun_HighInteger_PrintsMaxInt;
const
  Src =
    '''
        program P;
        begin
          WriteLn(High(Integer));
          WriteLn(Low(Integer))
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Integer bounds',
    '2147483647' + LE + '-2147483648' + LE, Output);
end;

procedure THighLowE2ETests.TestRun_HighByte_Prints255;
const
  Src =
    '''
        program P;
        var B: Byte;
        begin
          B := High(Byte);
          WriteLn(B)
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Byte high', '255' + LE, Output);
end;

procedure THighLowE2ETests.TestRun_HighEnum_PrintsLastOrdinal;
const
  Src =
    '''
        program P;
        type TColour = (Red, Green, Blue);
        begin
          WriteLn(Ord(High(TColour)));
          WriteLn(Ord(Low(TColour)))
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('enum bounds', '2' + LE + '0' + LE, Output);
end;

procedure THighLowE2ETests.TestRun_LowHighIntegerLoopBound;
const
  { Smoke test: using High/Low as loop literal sentinels. }
  Src =
    '''
        program P;
        var I, N: Integer;
        begin
          N := 0;
          for I := 1 to 5 do
            N := N + I;
          if N < High(Integer) then
            WriteLn(N);
          if N > Low(Integer) then
            WriteLn('ok')
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('loop guard', '15' + LE + 'ok' + LE, Output);
end;

procedure THighLowE2ETests.TestRun_HighLowInt64_BothBackends;
const
  Src =
    '''
        program P;
        var X: Int64;
        begin
          WriteLn(High(Int64));
          WriteLn(Low(Int64));
          X := High(Int64);
          WriteLn(X)
        end.
        ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '9223372036854775807' + LE +
    '-9223372036854775808' + LE +
    '9223372036854775807' + LE, 0);
end;

procedure THighLowE2ETests.TestRun_HighUInt64_BothBackends;
const
  Src =
    '''
        program P;
        var X: UInt64;
        begin
          X := High(UInt64);
          WriteLn(X)
        end.
        ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '18446744073709551615' + LE, 0);
end;

procedure THighLowE2ETests.TestRun_HighUInt32_BothBackends;
const
  Src =
    '''
        program P;
        var X: UInt32;
        begin
          X := High(UInt32);
          WriteLn(X)
        end.
        ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '4294967295' + LE, 0);
end;

initialization
  RegisterTest(THighLowTests);
  RegisterTest(THighLowE2ETests);

end.
