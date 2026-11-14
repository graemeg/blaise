{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.rterrorhooks;

{ The lowering of the runtime errors SysUtils turns into exceptions:
  division by zero, a failed `as` and StrToInt's validation.  Each calls an
  RTL routine, whatever is in scope, so a unit's object never names a
  SysUtils symbol (BUG-20261113-unit-object-depends-on-program).  The RTL
  raises through the hook SysUtils installs, or keeps the old behaviour. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.harness;

type
  TRtErrorHooksTests = class(TTestCase)
  published
    { With the SysUtils exception classes in scope, nothing names SysUtils. }
    procedure TestSysUtilsInScope_NoSysUtilsSymbol;
    { The division guard calls the RTL; when it returns (no hook) the code
      still traps as it did: a zero-divisor divide on x86-64, brk on arm64. }
    procedure TestDivGuard_CallsRtlThenTraps;
    procedure TestDivGuard_SameWithoutSysUtils;
    procedure TestFailedAs_CallsRtl;
    procedure TestStrToInt_CallsValidatingRtl;
  end;

implementation

const
  { The three classes stand in for `uses SysUtils`: they are what the
    backends used to look up to choose the SysUtils routines. }
  SrcInScope = '''
    program P;
    type
      EDivByZero = class end;
      EInvalidCast = class end;
      EConvertError = class end;
      TBar = class end;
    var
      A, B: Int;
      O: TObject;
    begin
      A := 7;
      B := 0;
      WriteLn(A div B);
      WriteLn(A mod B);
      O := TObject.Create();
      if (O as TBar) <> nil then WriteLn('bar');
      WriteLn(StrToInt('42abc'));
      WriteLn(StrToInt64('99bad'))
    end.
    ''';

  SrcNoSysUtils = '''
    program P;
    var
      A, B: Int;
    begin
      A := 7;
      B := 0;
      WriteLn(A div B)
    end.
    ''';

procedure TRtErrorHooksTests.TestSysUtilsInScope_NoSysUtilsSymbol;
begin
  AssertTrue('x86-64 names no SysUtils routine',
    Pos('SysUtils__', GenAsm(SrcInScope, TargetX86_64)) < 0);
  AssertTrue('arm64 names no SysUtils routine',
    Pos('SysUtils__', GenAsm(SrcInScope, TargetArm64)) < 0);
end;

procedure TRtErrorHooksTests.TestDivGuard_CallsRtlThenTraps;
begin
  AssertEquals('guard calls the RTL, then traps with a zero divisor', '',
    AsmMissing(SrcInScope,
      #9'callq _DivByZero'#10#9'xorl %ecx, %ecx'#10,
      #9'bl __DivByZero'#10#9'brk #1'#10));
end;

procedure TRtErrorHooksTests.TestDivGuard_SameWithoutSysUtils;
begin
  AssertEquals('the guard does not depend on what is in scope', '',
    AsmMissing(SrcNoSysUtils,
      #9'callq _DivByZero'#10#9'xorl %ecx, %ecx'#10,
      #9'bl __DivByZero'#10#9'brk #1'#10));
end;

procedure TRtErrorHooksTests.TestFailedAs_CallsRtl;
begin
  AssertEquals('a failed as calls the RTL', '',
    AsmMissing(SrcInScope, 'callq _Raise_InvalidCast',
      'bl __Raise_InvalidCast'));
end;

procedure TRtErrorHooksTests.TestStrToInt_CallsValidatingRtl;
begin
  AssertEquals('StrToInt', '',
    AsmMissing(SrcInScope, 'callq _StrToIntChecked', 'bl __StrToIntChecked'));
  AssertEquals('StrToInt64', '',
    AsmMissing(SrcInScope, 'callq _StrToInt64Checked',
      'bl __StrToInt64Checked'));
end;

initialization
  RegisterTest(TRtErrorHooksTests);

end.
