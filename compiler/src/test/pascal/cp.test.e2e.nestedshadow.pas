{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.nestedshadow;

{ A nested routine named like a built-in routine runs when called
  (BUG-20261113-nested-builtin-routine-shadow-ignored): before the fix the
  built-in ran instead, with no diagnostic.  cp.test.nestedshadow pins the
  call symbol on both ISAs. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.e2e.base;

type
  TE2ENestedShadowTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_NestedRoutinesNamedLikeBuiltins_Run;
    { WriteLn(B:6) lowers to calls of the built-ins Copy and Ord; a nested
      Copy or Ord in the same routine must not capture them }
    procedure TestRun_FormattedBoolean_IgnoresNestedCopyAndOrd;
  end;

implementation

procedure TE2ENestedShadowTests.SetUp;
begin
  inherited SetUp();
  Self.SetUpScratch('compiler/target/test-e2e-nestedshadow');
end;

procedure TE2ENestedShadowTests.TestRun_NestedRoutinesNamedLikeBuiltins_Run;
const
  Src =
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  function Length(const S: string): Int32;'#10 +
    '  begin'#10 +
    '    Result := 99;'#10 +
    '  end;'#10 +
    '  function Copy(const S: string; A, B: Int32): string;'#10 +
    '  begin'#10 +
    '    Result := ''mycopy'';'#10 +
    '  end;'#10 +
    '  function Sqrt(X: Float64): Float64;'#10 +
    '  begin'#10 +
    '    Result := 42.0;'#10 +
    '  end;'#10 +
    '  function Abs(X: Int32): Int32;'#10 +
    '  begin'#10 +
    '    Result := 1000;'#10 +
    '  end;'#10 +
    '  procedure SetLength(var S: string; N: Int32);'#10 +
    '  begin'#10 +
    '    S := ''mysetlen'';'#10 +
    '  end;'#10 +
    'var'#10 +
    '  S: string;'#10 +
    '  D: Float64;'#10 +
    'begin'#10 +
    '  WriteLn(Length(''abc''));'#10 +
    '  WriteLn(Copy(''abcdef'', 1, 2));'#10 +
    '  D := Sqrt(4.0);'#10 +
    '  WriteLn(Trunc(D));'#10 +
    '  WriteLn(Abs(-3));'#10 +
    '  S := ''x'';'#10 +
    '  SetLength(S, 3);'#10 +
    '  WriteLn(S);'#10 +
    '  Copy(''discarded'', 0, 1);'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    '  WriteLn(Length(''abc''), '' '', Copy(''abcdef'', 1, 2));'#10 +
    'end.'#10;
var
  Output: string;
  RCode: Int;
  OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  OK := CompileAndRun(Src, Output, RCode);
  AssertTrue('compile+run: ' + Output, OK);
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('nested routines run; outside Outer the built-ins do',
    '99' + LineEnding + 'mycopy' + LineEnding + '42' + LineEnding +
    '1000' + LineEnding + 'mysetlen' + LineEnding + '3 bc' + LineEnding,
    Output);
end;

procedure TE2ENestedShadowTests.TestRun_FormattedBoolean_IgnoresNestedCopyAndOrd;
const
  Src =
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  function Copy(const S: string; A, B: Int32): string;'#10 +
    '  begin'#10 +
    '    Result := ''mycopy'';'#10 +
    '  end;'#10 +
    '  function Ord(B: Boolean): Int32;'#10 +
    '  begin'#10 +
    '    Result := 0;'#10 +
    '  end;'#10 +
    '  function IntToStr(N: Int32): string;'#10 +
    '  begin'#10 +
    '    Result := ''myint'';'#10 +
    '  end;'#10 +
    'var'#10 +
    '  B: Boolean;'#10 +
    '  N: Int32;'#10 +
    'begin'#10 +
    '  B := True;'#10 +
    '  N := 7;'#10 +
    '  WriteLn(''['', B:6, ''|'', N:3, '']'');'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    'end.'#10;
var
  Output: string;
  RCode: Int;
  OK: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  OK := CompileAndRun(Src, Output, RCode);
  AssertTrue('compile+run: ' + Output, OK);
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('the formatting built-ins are System''s',
    '[  True|  7]' + LineEnding, Output);
end;

initialization
  RegisterTest(TE2ENestedShadowTests);

end.
