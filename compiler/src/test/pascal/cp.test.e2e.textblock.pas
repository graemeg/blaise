{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.textblock;

{ E2E tests for text block literal syntax.

  These source constants use #39 (apostrophe) sequences rather than Pascal
  string literals to embed triple-quote delimiters, so the Blaise compiler
  does not parse them as text blocks when compiling this test unit itself. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ETextBlockTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TextBlock_BasicContent;
    procedure TestRun_TextBlock_IndentStripped;
  end;

implementation

procedure TE2ETextBlockTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-textblock');
end;

const
  LE = #10;
  Q3 = #39#39#39; // three single-quote chars used to embed text-block delimiters

  // program P;
  // var S: string;
  // begin
  //   S := '''
  //   hello
  //   ''';
  //   WriteLn(S)
  // end.
  SrcTextBlockBasic =
    'program P;' + LE +
    'var S: string;' + LE +
    'begin' + LE +
    '  S := ' + Q3 + LE +
    '  hello' + LE +
    '  ' + Q3 + ';' + LE +
    '  WriteLn(S)' + LE +
    'end.';

  // program P;
  // var S: string;
  // begin
  //   S := '''
  //     line1
  //     line2
  //     ''';
  //   WriteLn(Length(S))
  // end.
  SrcTextBlockIndent =
    'program P;' + LE +
    'var S: string;' + LE +
    'begin' + LE +
    '  S := ' + Q3 + LE +
    '    line1' + LE +
    '    line2' + LE +
    '    ' + Q3 + ';' + LE +
    '  WriteLn(Length(S))' + LE +
    'end.';

procedure TE2ETextBlockTests.TestRun_TextBlock_BasicContent;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTextBlockBasic, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  // Text block content is 'hello' + LF (newline before closing triple-quote).
  // WriteLn adds another LF, so output is hello+LF+LF.
  AssertEquals('hello+lf', 'hello' + LE + LE, Output);
end;

procedure TE2ETextBlockTests.TestRun_TextBlock_IndentStripped;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTextBlockIndent, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  // 'line1' + LF + 'line2' + LF = 12 chars after indent strip
  AssertEquals('length 12', '12' + LE, Output);
end;

initialization
  RegisterTest(TE2ETextBlockTests);

end.
