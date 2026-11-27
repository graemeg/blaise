{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.rterrorhooks;

{ The lowering of the runtime errors SysUtils turns into exceptions:
  division by zero, a failed `as`, StrToInt's validation and a dynamic-array
  index out of range.  Each calls an
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
    { the failed-as call is aligned by the tracked-depth pad alone: an
      `andq $-16, %rsp` before it was undone by that pad at an odd depth }
    procedure TestFailedAs_OddDepth_CallIsAligned;
    procedure TestStrToInt_CallsValidatingRtl;
    { Every dynamic-array element access compares the index with the length
      header and calls the RTL on failure: a read, a write, the address of
      an element, a dyn-array field element and an element of an element. }
    procedure TestDynIndex_ChecksAgainstLength;
    { The check is for dynamic arrays only: static arrays, strings and open
      arrays emit none. }
    procedure TestDynIndex_NoCheckOnOtherArrays;
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

  { one access per program, so a check found is the one under test }
  SrcDynRead = '''
    program P;
    var
      A: array of Int;
      I, X: Int;
    begin
      X := A[I]
    end.
    ''';

  SrcDynWrite = '''
    program P;
    var
      A: array of Int;
      I: Int;
    begin
      A[I] := 7
    end.
    ''';

  SrcDynAddr = '''
    program P;
    var
      A: array of Int;
      I: Int;
      Q: ^Int;
    begin
      Q := @A[I]
    end.
    ''';

  SrcDynField = '''
    program P;
    type
      TRec = record
        Arr: array of Int;
      end;
    var
      R: TRec;
      I, X: Int;
    begin
      X := R.Arr[I]
    end.
    ''';

  SrcDynFieldWrite = '''
    program P;
    type
      TRec = record
        Arr: array of Int;
      end;
    var
      R: TRec;
      I: Int;
    begin
      R.Arr[I] := 3
    end.
    ''';

  SrcDynNested = '''
    program P;
    var
      M: array of array of Int;
      I, J, X: Int;
    begin
      X := M[I, J]
    end.
    ''';

  SrcOtherArrays = '''
    program P;
    var
      S: array[0..3] of Int;
      T: string;
      I, X: Int;
    procedure Open(const O: array of Int);
    begin
      X := O[I]
    end;
    begin
      S[I] := 1;
      X := S[I] + Ord(T[I]);
      Open(S)
    end.
    ''';

  { the compare against the length header (data - 8) and the failure call }
  X86Check = #9'cmpq -8(%rcx), %rax'#10#9'jb ';
  Arm64Check = #9'ldur x16, [x0, #-8]'#10#9'cmp x1, x16'#10#9'b.lo ';

function CountOf(const ASub, AText: string): Int;
var
  P: Int;
  Rest: string;
begin
  Result := 0;
  Rest := AText;
  P := Pos(ASub, Rest);
  while P >= 0 do
  begin
    Inc(Result);
    Rest := Copy(Rest, P + Length(ASub), Length(Rest));
    P := Pos(ASub, Rest);
  end;
end;

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

procedure TRtErrorHooksTests.TestDynIndex_ChecksAgainstLength;
begin
  AssertEquals('read', '', AsmMissing(SrcDynRead, X86Check, Arm64Check));
  AssertEquals('read calls the RTL', '',
    AsmMissing(SrcDynRead, 'callq _Raise_RangeError', 'bl __Raise_RangeError'));
  AssertEquals('write', '', AsmMissing(SrcDynWrite, X86Check, Arm64Check));
  AssertEquals('address of an element', '',
    AsmMissing(SrcDynAddr, X86Check, Arm64Check));
  AssertEquals('dyn-array field element', '',
    AsmMissing(SrcDynField, X86Check,
      #9'ldur x16, [x1, #-8]'#10#9'cmp x0, x16'#10#9'b.lo '));
  AssertEquals('dyn-array field element write', '',
    AsmMissing(SrcDynFieldWrite, #9'cmpq -8(%rdx), %rax'#10#9'jb ',
      Arm64Check));
  AssertEquals('x86-64: M[I, J] checks both subscripts', 2,
    CountOf('callq _Raise_RangeError', GenAsm(SrcDynNested, TargetX86_64)));
  AssertEquals('arm64: M[I, J] checks both subscripts', 2,
    CountOf('bl __Raise_RangeError', GenAsm(SrcDynNested, TargetArm64)));
end;

procedure TRtErrorHooksTests.TestDynIndex_NoCheckOnOtherArrays;
begin
  AssertTrue('x86-64: static array, string and open array are unchecked',
    Pos('_Raise_RangeError', GenAsm(SrcOtherArrays, TargetX86_64)) < 0);
  AssertTrue('arm64: static array, string and open array are unchecked',
    Pos('_Raise_RangeError', GenAsm(SrcOtherArrays, TargetArm64)) < 0);
end;


procedure TRtErrorHooksTests.TestFailedAs_OddDepth_CallIsAligned;
const
  Src = '''
    program P;
    uses SysUtils;
    type TA = class N: Int32; end; TB = class(TA) end;
    var O: TA; X, Y: Int32;
    begin
      X := Y + (Y + (O as TB).N)
    end.
    ''';
var
  A: string;
begin
  A := GenAsm(Src, TargetX86_64);
  AssertTrue('the failed-as call is reached', Pos('callq _Raise_InvalidCast', A) >= 0);
  AssertTrue('no andq before the pad: ' + A,
    Pos(#9'andq $-16, %rsp' + #10 + #9'subq $8, %rsp' + #10 +
      #9'callq _Raise_InvalidCast', A) < 0);
  AssertTrue('the odd depth is padded', Pos(#9'subq $8, %rsp' + #10 +
    #9'callq _Raise_InvalidCast', A) >= 0);
end;

initialization
  RegisterTest(TRtErrorHooksTests);

end.
