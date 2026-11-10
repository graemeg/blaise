{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the MIG-CALLCONV rule: stdcall, safecall, register and pascal in
  directive position are reported; the same words used as identifiers, in
  comments or in strings are not. }

unit Migration.Rules.Tests;

interface

uses
  blaise.testing;

type
  TCallingConventionRuleTests = class(TTestCase)
  published
    procedure TestStdcall_OnExternal_SaysCdecl;
    procedure TestSafecall_SaysCdecl;
    procedure TestRegisterAndPascal_SayDelete;
    procedure TestDirectiveAfterExternalClause_Reported;
    procedure TestMethodAndForwardDeclarations_Reported;
    procedure TestProceduralType_Reported;
    procedure TestEveryIfdefBranch_Checked;
    procedure TestPosition_LineAndColumn;
    procedure TestCdeclAndOtherDirectives_Silent;
    procedure TestIdentifierUses_Silent;
    procedure TestCommentsAndStrings_Silent;
    procedure TestAnonymousMethodBody_Silent;
    procedure TestFindingText_Format;
  end;

implementation

uses
  SysUtils, Migration.Rules;

const
  NL = #10;

function Scan(const ASource: string): TMigrationReport;
begin
  Result := TMigrationReport.Create();
  AnalyseSource(ASource, 'u.pas', Result);
end;

function CountOf(const ASource: string): Int;
var
  R: TMigrationReport;
begin
  R := Scan(ASource);
  try
    Result := R.Count();
  finally
    R.Free();
  end;
end;

function FirstMessage(const ASource: string): string;
var
  R: TMigrationReport;
begin
  R := Scan(ASource);
  try
    if R.Count() = 0 then
      Result := ''
    else
      Result := R[0].Message;
  finally
    R.Free();
  end;
end;

procedure TCallingConventionRuleTests.TestStdcall_OnExternal_SaysCdecl;
var
  Msg: string;
begin
  Msg := FirstMessage('function QueryPerformanceCounter(out C: Int64): ' +
    'Boolean; stdcall; external ''kernel32'';');
  AssertTrue('names the directive, got: ' + Msg, Pos('''stdcall''', Msg) >= 0);
  AssertTrue('replacement is cdecl, got: ' + Msg,
    Pos('replace it with ''cdecl''', Msg) >= 0);
end;

procedure TCallingConventionRuleTests.TestSafecall_SaysCdecl;
begin
  AssertTrue('safecall -> cdecl',
    Pos('replace it with ''cdecl''',
      FirstMessage('procedure P; safecall; begin end;')) >= 0);
end;

procedure TCallingConventionRuleTests.TestRegisterAndPascal_SayDelete;
begin
  AssertTrue('register -> delete',
    Pos('delete it', FirstMessage('procedure P; register; begin end;')) >= 0);
  AssertTrue('pascal -> delete',
    Pos('delete it', FirstMessage('function F: Int; pascal; begin end;')) >= 0);
  AssertTrue('case-insensitive',
    Pos('''register''', FirstMessage('procedure P; REGISTER; begin end;')) >= 0);
end;

procedure TCallingConventionRuleTests.TestDirectiveAfterExternalClause_Reported;
begin
  AssertEquals('stdcall after external ... name ...', 1,
    CountOf('function F(X: Int32): Int32; external ''c'' name ''abs''; ' +
      'stdcall;'));
  AssertEquals('two directives, one removed', 1,
    CountOf('procedure P; overload; stdcall; begin end;'));
  AssertEquals('every declaration is checked', 2,
    CountOf('procedure A; stdcall; external ''x'';' + NL +
      'procedure B; stdcall; external ''x'';'));
end;

procedure TCallingConventionRuleTests.TestMethodAndForwardDeclarations_Reported;
begin
  AssertEquals('class method and its implementation', 2,
    CountOf('type TC = class' + NL +
      '  procedure M(A: Int; B: Int); virtual; stdcall;' + NL +
      'end;' + NL +
      'procedure TC.M(A: Int; B: Int); stdcall;' + NL +
      'begin end;'));
  AssertEquals('interface forward', 1,
    CountOf('interface' + NL + 'procedure F; stdcall;' + NL +
      'implementation'));
end;

procedure TCallingConventionRuleTests.TestProceduralType_Reported;
begin
  AssertEquals('procedural type', 1,
    CountOf('type TWndProc = function(H: Pointer; M: UInt32): Int64; stdcall;'));
  AssertEquals('method pointer type', 1,
    CountOf('type TCb = procedure(S: TObject) of object; stdcall;'));
end;

procedure TCallingConventionRuleTests.TestEveryIfdefBranch_Checked;
begin
  AssertEquals('both branches', 2,
    CountOf('{$IFDEF WINDOWS}' + NL +
      'procedure P; stdcall; external ''k'';' + NL +
      '{$ELSE}' + NL +
      'procedure P; pascal; external ''k'';' + NL +
      '{$ENDIF}'));
end;

procedure TCallingConventionRuleTests.TestPosition_LineAndColumn;
var
  R: TMigrationReport;
begin
  R := Scan('unit U;' + NL + 'interface' + NL +
    'procedure P;  stdcall;' + NL + 'implementation' + NL + 'end.');
  try
    AssertEquals('one finding', 1, R.Count());
    AssertEquals('line', 3, R[0].Line);
    AssertEquals('column', 15, R[0].Col);
    AssertEquals('rule', RuleCallingConvention, R[0].RuleId);
  finally
    R.Free();
  end;
end;

procedure TCallingConventionRuleTests.TestCdeclAndOtherDirectives_Silent;
begin
  AssertEquals('cdecl and friends', 0,
    CountOf('function F(P: PChar): Int32; cdecl; varargs; external ''c'' ' +
      'name ''printf'';' + NL +
      'procedure G; inline; overload; begin end;' + NL +
      'procedure H; deprecated ''use G''; begin end;'));
end;

procedure TCallingConventionRuleTests.TestIdentifierUses_Silent;
begin
  AssertEquals('as names and statements', 0,
    CountOf('procedure Register; begin end;' + NL +
      'function Pascal(Register: Int): Int; begin Result := Register; end;' + NL +
      'var stdcall, safecall: Int;' + NL +
      'begin' + NL + '  Foo;' + NL + '  Register;' + NL +
      '  stdcall := Pascal(1);' + NL + 'end.'));
end;

procedure TCallingConventionRuleTests.TestCommentsAndStrings_Silent;
begin
  AssertEquals('comments and strings', 0,
    CountOf('procedure P; { stdcall; } // register;' + NL +
      '(* pascal; *) begin WriteLn(''stdcall;''); end;'));
end;

procedure TCallingConventionRuleTests.TestAnonymousMethodBody_Silent;
begin
  AssertEquals('a body, not a directive list', 0,
    CountOf('begin' + NL +
      '  Run(procedure begin Foo; Register; end);' + NL +
      'end.'));
end;

procedure TCallingConventionRuleTests.TestFindingText_Format;
var
  R: TMigrationReport;
begin
  R := Scan('procedure P; stdcall; begin end;');
  try
    AssertEquals('file:line:col: [RULE] message',
      'u.pas:1:14: [MIG-CALLCONV] ''stdcall'' is not a Blaise ' +
      'calling-convention directive: replace it with ''cdecl'', the only ' +
      'Blaise calling-convention directive', R[0].AsText());
  finally
    R.Free();
  end;
end;

initialization
  RegisterTest(TCallingConventionRuleTests);

end.
