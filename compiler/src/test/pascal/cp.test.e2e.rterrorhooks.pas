{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.rterrorhooks;

{ Runtime errors that SysUtils turns into exceptions (division by zero, a
  failed `as`, an invalid StrToInt) go through RTL hooks SysUtils installs,
  so a unit's object does not depend on the program it was compiled with
  (BUG-20261113-unit-object-depends-on-program).

  Each test compiles two programs into one output directory, so the second
  links the unit objects the first compiled.  The units never use SysUtils;
  one program does and the other does not. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.e2e.base;

type
  TE2ERtErrorHooksTests = class(TE2ETestCase)
  private
    procedure WriteUnits;
    procedure RunWithSysUtils(const AWhen: string);
    procedure RunWithoutSysUtils(const AWhen: string);
  published
    { The units are compiled for a program that uses SysUtils; a program
      without SysUtils then links their cached objects. }
    procedure TestRun_CachedForSysUtils_LinksWithout;
    { The units are compiled for a program without SysUtils; a program that
      uses SysUtils then links their cached objects and still catches every
      error they raise as its exception. }
    procedure TestRun_CachedWithout_CatchableWithSysUtils;
  end;

implementation

const
  DivUnit =
    'unit RtHookDiv;'#10 +
    'interface'#10 +
    'function Quot(A, B: Int): Int;'#10 +
    'implementation'#10 +
    'function Quot(A, B: Int): Int;'#10 +
    'begin'#10 +
    '  Result := A div B;'#10 +
    'end;'#10 +
    'end.'#10;

  CastUnit =
    'unit RtHookCast;'#10 +
    'interface'#10 +
    'type'#10 +
    '  TBar = class'#10 +
    '  end;'#10 +
    'function AsBar(O: TObject): Int;'#10 +
    'implementation'#10 +
    'function AsBar(O: TObject): Int;'#10 +
    'begin'#10 +
    '  Result := 0;'#10 +
    '  if (O as TBar) <> nil then'#10 +
    '    Result := 1;'#10 +
    'end;'#10 +
    'end.'#10;

  ConvUnit =
    'unit RtHookConv;'#10 +
    'interface'#10 +
    'function ParseInt(const S: string): Int;'#10 +
    'function ParseInt64(const S: string): Int64;'#10 +
    'implementation'#10 +
    'function ParseInt(const S: string): Int;'#10 +
    'begin'#10 +
    '  Result := StrToInt(S);'#10 +
    'end;'#10 +
    'function ParseInt64(const S: string): Int64;'#10 +
    'begin'#10 +
    '  Result := StrToInt64(S);'#10 +
    'end;'#10 +
    'end.'#10;

  WithSysUtils =
    'program withsys;'#10 +
    'uses SysUtils, RtHookDiv, RtHookCast, RtHookConv;'#10 +
    'var O: TObject;'#10 +
    'begin'#10 +
    '  WriteLn(Quot(7, 2));'#10 +
    '  try'#10 +
    '    WriteLn(Quot(1, 0));'#10 +
    '  except'#10 +
    '    on E: EDivByZero do WriteLn(''div caught'');'#10 +
    '  end;'#10 +
    '  O := TObject.Create();'#10 +
    '  try'#10 +
    '    WriteLn(AsBar(O));'#10 +
    '  except'#10 +
    '    on E: EInvalidCast do WriteLn(''cast caught'');'#10 +
    '  end;'#10 +
    '  try'#10 +
    '    WriteLn(ParseInt(''42abc''));'#10 +
    '  except'#10 +
    '    on E: EConvertError do WriteLn(''convert caught'');'#10 +
    '  end;'#10 +
    '  try'#10 +
    '    WriteLn(ParseInt64(''x''));'#10 +
    '  except'#10 +
    '    on E: EConvertError do WriteLn(''convert64 caught'');'#10 +
    '  end;'#10 +
    '  WriteLn(ParseInt(''17''), '' '', ParseInt64(''-5''));'#10 +
    'end.'#10;

  { Without SysUtils nothing is catchable, so only the error-free paths run;
    StrToInt stays lenient (it parses the leading digits). }
  WithoutSysUtils =
    'program withoutsys;'#10 +
    'uses RtHookDiv, RtHookCast, RtHookConv;'#10 +
    'begin'#10 +
    '  WriteLn(Quot(9, 2));'#10 +
    '  WriteLn(AsBar(TBar.Create()));'#10 +
    '  WriteLn(ParseInt(''42abc''), '' '', ParseInt64(''17''));'#10 +
    'end.'#10;

procedure TE2ERtErrorHooksTests.WriteUnits;
const
  Cached: array[0..5] of string = ('rthookdiv.o', 'rthookcast.o',
    'rthookconv.o', 'rthookdiv.bif', 'rthookcast.bif', 'rthookconv.bif');
var
  I: Int;
begin
  { start cold: the order the two programs fill the cache is the test }
  for I := 0 to High(Cached) do
    Self.DeleteScratchFile(Cached[I]);
  Self.WriteScratchUnit(DivUnit);
  Self.WriteScratchUnit(CastUnit);
  Self.WriteScratchUnit(ConvUnit);
end;

procedure TE2ERtErrorHooksTests.RunWithSysUtils(const AWhen: string);
var
  Output: string;
  RCode: Int;
begin
  AssertTrue(AWhen + ': compile+run with SysUtils: ' + Output,
    Self.CompileAndRunInScratch(WithSysUtils, Output, RCode));
  AssertEquals(AWhen + ': exit code: ' + Output, 0, RCode);
  AssertEquals(AWhen + ': every error caught as its exception',
    '3' + LineEnding + 'div caught' + LineEnding + 'cast caught' + LineEnding +
    'convert caught' + LineEnding + 'convert64 caught' + LineEnding +
    '17 -5' + LineEnding, Output);
end;

procedure TE2ERtErrorHooksTests.RunWithoutSysUtils(const AWhen: string);
var
  Output: string;
  RCode: Int;
begin
  AssertTrue(AWhen + ': compile+run without SysUtils: ' + Output,
    Self.CompileAndRunInScratch(WithoutSysUtils, Output, RCode));
  AssertEquals(AWhen + ': exit code: ' + Output, 0, RCode);
  AssertEquals(AWhen + ': lenient StrToInt, no SysUtils symbol needed',
    '4' + LineEnding + '1' + LineEnding + '42 17' + LineEnding, Output);
end;

procedure TE2ERtErrorHooksTests.TestRun_CachedForSysUtils_LinksWithout;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Self.SetUpScratch('compiler/target/test-e2e-rterrorhooks-a');
  Self.WriteUnits();
  Self.RunWithSysUtils('first');
  Self.RunWithoutSysUtils('second, cached units');
end;

procedure TE2ERtErrorHooksTests.TestRun_CachedWithout_CatchableWithSysUtils;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Self.SetUpScratch('compiler/target/test-e2e-rterrorhooks-b');
  Self.WriteUnits();
  Self.RunWithoutSysUtils('first');
  Self.RunWithSysUtils('second, cached units');
end;

initialization
  RegisterTest(TE2ERtErrorHooksTests);

end.
