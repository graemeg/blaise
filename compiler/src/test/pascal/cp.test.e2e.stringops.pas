{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.stringops;

{ E2E tests for string operations, Int64 formatting, and string subscripting. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStringOpsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_StringOps_Length;
    procedure TestRun_StringOps_Pos;
    procedure TestRun_StringOps_Copy;
    procedure TestRun_StringOps_UpperCase;
    procedure TestRun_StringOps_SameText;
    procedure TestRun_StringOps_IntToStr;
    procedure TestRun_StringOps_StrToInt;
    procedure TestRun_StringOps_StrToInt_Hex;
    procedure TestRun_StringOps_Copy_MaxIntCount;
    procedure TestRun_Int64_PositiveAboveInt32_FormatsCorrectly;
    procedure TestRun_StringOps_Format_IntArg;
    procedure TestRun_StringOps_Format_StrArg;
    procedure TestRun_StringOps_Format_MixedArgs;
    procedure TestRun_StringOps_Format_FloatDefault;
    procedure TestRun_StringOps_Format_FloatPrecision;
    procedure TestRun_StringOps_Format_FloatWidth;
    procedure TestRun_StringOps_Format_FloatExp;
    procedure TestRun_StringOps_Format_FloatGeneral;
    procedure TestRun_StringOps_Format_FloatMixedWithIntStr;
    procedure TestRun_StringSubscript_ReadByte;
    procedure TestRun_StringSubscript_Write;
    procedure TestRun_StringSubscript_WriteCOW;
    procedure TestRun_StringSubscript_WriteVarParam;
    { BUG-20260726-arm64-field-characcess-dropped — a subscript on a STRING
      FIELD is folded into the field access (IsCharAccess), not a
      TStringSubscriptExpr, and arm64 had no arm for it: the read yielded the
      data pointer and dropped the subscript. }
    procedure TestRun_StringFieldSubscript_Read;
    procedure TestRun_StringConcat_TwoStrings;
    procedure TestRun_StringConcat_WithInt;
    procedure TestRun_StringDelete_Modifies;
    { Delete() on a non-local string receiver — class field, field-array
      element, implicit-Self field, var-param.  The native store-back was
      guarded by a bare `is TIdentExpr`, so every field receiver dropped the
      result: the field was left unchanged and the new string leaked
      (BUG-20260723-native-delete-string-field-noop). }
    procedure TestRun_StringDelete_FieldReceivers;
    procedure TestRun_StringSetLength_Truncates;
    { Relational order operators on strings (< > <= >=): QBE used to abort
      (selcmp k != Kw) and native silently compared pointers; both now route
      through _StringCompare. }
    procedure TestRun_StringRelational_Order;
    procedure TestRun_Int64_ArithmeticOverInt32;
    procedure TestRun_Int64_Comparison;
    procedure TestRun_Int64_ForLoop;
    procedure TestRun_StringLiteral_HighByteSurvives;
  end;

implementation

procedure TE2EStringOpsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-stringops');
end;

const
  LE = #10;

  SrcStringLength =
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          s := 'hello';
          n := Length(s);
          WriteLn(n)
        end.
        ''';

  SrcStringPos =
    '''
        program P;
        var s, sub: string;
        var n: Integer;
        begin
          s   := 'hello world';
          sub := 'world';
          n   := Pos(sub, s);
          WriteLn(n)
        end.
        ''';

  SrcStringCopy =
    '''
        program P;
        var s, t: string;
        begin
          s := 'hello';
          t := Copy(s, 1, 3);
          WriteLn(t)
        end.
        ''';

  SrcStringUpperCase =
    '''
        program P;
        var s, t: string;
        begin
          s := 'hello';
          t := UpperCase(s);
          WriteLn(t)
        end.
        ''';

  SrcStringSameText =
    '''
        program P;
        var s, t: string;
        var b: Boolean;
        begin
          s := 'Hello';
          t := 'hello';
          b := SameText(s, t);
          WriteLn(b)
        end.
        ''';

  SrcStringIntToStr =
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          n := 42;
          s := IntToStr(n);
          WriteLn(s)
        end.
        ''';

  SrcStringStrToInt =
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          s := '123';
          n := StrToInt(s);
          WriteLn(n)
        end.
        ''';

  SrcStringStrToIntHex =
    '''
        program P;
        var n: Integer;
        begin
          n := StrToInt('$FF');
          WriteLn(n)
        end.
        ''';

  SrcStringCopyMaxIntCount =
    '''
        program P;
        var s: string;
        begin
          s := Copy('^Integer', 1, MaxInt);
          WriteLn(s)
        end.
        ''';

  SrcInt64PositiveAboveInt32 =
    '''
        program P;
        var v: Int64;
        begin
          v := 1000000000;
          v := v + v + 166136261;
          if v < 0 then WriteLn('neg')
                  else WriteLn('pos');
          WriteLn(IntToStr(v))
        end.
        ''';

  SrcFormatIntArg =
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          n := 42;
          s := Format('val=%d', n);
          WriteLn(s)
        end.
        ''';

  SrcFormatStrArg =
    '''
        program P;
        var t: string;
        var s: string;
        begin
          t := 'world';
          s := Format('hello %s', t);
          WriteLn(s)
        end.
        ''';

  SrcFormatMixedArgs =
    '''
        program P;
        var name: string;
        var age: Integer;
        var s: string;
        begin
          name := 'Alice';
          age  := 30;
          s := Format('%s=%d', name, age);
          WriteLn(s)
        end.
        ''';

  { %f with explicit precision }
  SrcFormatFloatPrecision =
    '''
        program P;
        var x: Double;
        begin
          x := 3.14159;
          WriteLn(Format('v=%.2f', x))
        end.
        ''';

  { %f with no precision → default 2 decimal places (Delphi semantics) }
  SrcFormatFloatDefault =
    '''
        program P;
        var x: Double;
        begin
          x := 3.5;
          WriteLn(Format('v=%f', x))
        end.
        ''';

  { %f with width + precision, right-justified padding }
  SrcFormatFloatWidth =
    '''
        program P;
        var x: Double;
        begin
          x := 2.5;
          WriteLn(Format('[%8.2f]', x))
        end.
        ''';

  { %e exponential notation }
  SrcFormatFloatExp =
    '''
        program P;
        var x: Double;
        begin
          x := 12345.678;
          WriteLn(Format('%.2e', x))
        end.
        ''';

  { %g general notation }
  SrcFormatFloatGeneral =
    '''
        program P;
        var x: Double;
        begin
          x := 0.0001;
          WriteLn(Format('%g', x))
        end.
        ''';

  { float interleaved with int and string args }
  SrcFormatFloatMixed =
    '''
        program P;
        var x: Double;
        var n: Integer;
        var nm: string;
        begin
          x  := 1.5;
          n  := 7;
          nm := 'ok';
          WriteLn(Format('%s %d %.1f', nm, n, x))
        end.
        ''';

  SrcStringSubscript = '''
    program P;
    var S: string;
    begin
      S := 'ABC';
      WriteLn(S[0]);
      WriteLn(S[1]);
      WriteLn(S[2])
    end.
    ''';

  { Writable string subscript: S[I] := <byte>.  Copy-on-write must replace
    the literal-backed buffer before writing so this does not fault on the
    read-only literal.  Accepts a numeric ordinal, Chr(n), and a single-char
    literal as the RHS. }
  SrcStringSubscriptWrite = '''
    program P;
    var S: string;
    begin
      S := 'AAAAA';
      S[0] := Chr(90);
      S[2] := 67;
      S[4] := 'E';
      WriteLn(S)
    end.
    ''';

  { Copy-on-write correctness: mutating an aliased string must not disturb
    the other reference, and a reused literal must stay pristine. }
  SrcStringSubscriptCOW = '''
    program P;
    var A, B: string;
    begin
      A := 'HELLO';
      B := A;
      A[0] := Chr(74);
      WriteLn(A);
      WriteLn(B);
      B := 'WORLD';
      WriteLn(B)
    end.
    ''';

  { Writable subscript through a var-string parameter. }
  SrcStringSubscriptVarParam = '''
    program P;
    procedure PutByte(var ABuf: string; AOff: Integer; AVal: Integer);
    begin
      ABuf[AOff] := Chr(AVal)
    end;
    var S: string;
    begin
      S := 'AAAA';
      PutByte(S, 1, 66);
      WriteLn(S)
    end.
    ''';

  SrcStringConcatStr = '''
    program P;
    var A, B, C: string;
    begin
      A := 'foo';
      B := 'bar';
      C := A + B;
      WriteLn(C)
    end.
    ''';

  SrcStringDelete = '''
    program P;
    var S: string;
    begin
      S := 'Hello World';
      Delete(S, 5, 6);
      WriteLn(S)
    end.
    ''';

  SrcStringSetLength = '''
    program P;
    var S: string;
    begin
      S := 'Hello';
      SetLength(S, 3);
      WriteLn(S)
    end.
    ''';

  SrcInt64Arith = '''
    program P;
    var A, B: Int64;
    begin
      A := 3000000000;
      B := A * 2;
      WriteLn(B)
    end.
    ''';

  SrcInt64Compare = '''
    program P;
    var A: Int64;
    begin
      A := 5000000000;
      if A > 4000000000 then WriteLn('big');
      if A < 6000000000 then WriteLn('small')
    end.
    ''';

  SrcInt64ForLoop = '''
    program P;
    var I: Int64; S: Int64;
    begin
      S := 0;
      for I := 1 to 5 do
        S := S + I;
      WriteLn(S)
    end.
    ''';

procedure TE2EStringOpsTests.TestRun_StringOps_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringLength, Output, RCode));
  AssertEquals('Length(''hello'') = 5', '5', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Pos;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringPos, Output, RCode));
  AssertEquals('Pos(''world'', ''hello world'') = 6', '6', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Copy;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringCopy, Output, RCode));
  AssertEquals('Copy(''hello'', 1, 3) = ''ell''', 'ell', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_UpperCase;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringUpperCase, Output, RCode));
  AssertEquals('UpperCase(''hello'') = ''HELLO''', 'HELLO', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_SameText;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringSameText, Output, RCode));
  AssertEquals('SameText(''Hello'', ''hello'') = True', 'True', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_IntToStr;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringIntToStr, Output, RCode));
  AssertEquals('IntToStr(42) = ''42''', '42', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_StrToInt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringStrToInt, Output, RCode));
  AssertEquals('StrToInt(''123'') = 123', '123', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_StrToInt_Hex;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringStrToIntHex, Output, RCode));
  AssertEquals('StrToInt(''$FF'') = 255', '255', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Copy_MaxIntCount;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringCopyMaxIntCount, Output, RCode));
  AssertEquals('Copy(''^Integer'', 1, MaxInt) = ''Integer''', 'Integer', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_Int64_PositiveAboveInt32_FormatsCorrectly;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64PositiveAboveInt32, Output, RCode));
  AssertEquals('Int64=2166136261 compares as positive and formats correctly',
    'pos' + LE + '2166136261', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_IntArg;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatIntArg, Output, RCode));
  AssertEquals('Format int arg', 'val=42', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_StrArg;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatStrArg, Output, RCode));
  AssertEquals('Format str arg', 'hello world', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_MixedArgs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatMixedArgs, Output, RCode));
  AssertEquals('Format mixed args', 'Alice=30', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_FloatDefault;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { %f with no precision → 2 decimals (Delphi default). }
  AssertRunsOnAll(SrcFormatFloatDefault, 'v=3.50' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_FloatPrecision;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFormatFloatPrecision, 'v=3.14' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_FloatWidth;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { width 8, precision 2 → "    2.50" (right-justified in 8 columns). }
  AssertRunsOnAll(SrcFormatFloatWidth, '[    2.50]' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_FloatExp;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 12345.678 in %.2e → 1.23e+04. }
  AssertRunsOnAll(SrcFormatFloatExp, '1.23e+04' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_FloatGeneral;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 0.0001 in %g → 0.0001 (shortest round-trippable form). }
  AssertRunsOnAll(SrcFormatFloatGeneral, '0.0001' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_FloatMixedWithIntStr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFormatFloatMixed, 'ok 7 1.5' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringSubscript_ReadByte;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringSubscript, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('65 66 67', '65' + LE + '66' + LE + '67' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringSubscript_Write;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both backends: writing into a literal-backed string must copy-on-write
    rather than fault on read-only memory. }
  AssertRunsOnAll(SrcStringSubscriptWrite, 'ZACAE' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringSubscript_WriteCOW;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStringSubscriptCOW, 'JELLO' + LE + 'HELLO' + LE + 'WORLD' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringSubscript_WriteVarParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStringSubscriptVarParam, 'ABAA' + LE, 0);
end;

const
  { Every base form the IsCharAccess arm has to reach: a class field via a
    variable, via a two-level chain, through implicit Self, and a record field
    of a var parameter.  Tag/N sit before the string so a dropped subscript
    cannot coincidentally land on it. }
  SrcStringFieldSubscript = '''
    program P;
    type
      TRec = record
        N: Integer;
        S: string;
      end;
      TBox = class
        Tag: Integer;
        Data: string;
        constructor Create;
        function First: Integer;
      end;
      TOuter = class
        Pad: Integer;
        Box: TBox;
        constructor Create;
      end;
    constructor TBox.Create;
    begin inherited Create(); Tag := 7; Data := 'ABC' end;
    function TBox.First: Integer;
    begin Result := Ord(Data[0]) end;
    constructor TOuter.Create;
    begin inherited Create(); Pad := 9; Box := TBox.Create() end;
    procedure ShowVar(var R: TRec);
    begin WriteLn(Ord(R.S[1])) end;
    var
      O: TOuter;
      R: TRec;
      I: Integer;
    begin
      O := TOuter.Create();
      WriteLn(Ord(O.Box.Data[0]));
      I := 2;
      WriteLn(Ord(O.Box.Data[I]));
      WriteLn(O.Box.First());
      R.N := 1;
      R.S := 'XYZ';
      ShowVar(R);
      O := nil
    end.
    ''';

procedure TE2EStringOpsTests.TestRun_StringFieldSubscript_Read;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 'A', 'C', 'A', 'Y' }
  AssertRunsOnAll(SrcStringFieldSubscript,
    '65' + LE + '67' + LE + '65' + LE + '89' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringConcat_TwoStrings;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringConcatStr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('foobar', 'foobar' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringConcat_WithInt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun('program P; begin WriteLn(''x='' + IntToStr(7)) end.',
                  Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('x=7', 'x=7' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringDelete_Modifies;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringDelete, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello', 'Hello' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringDelete_FieldReceivers;
const Src =
  '''
  program P;
  type
    TBox = class
    public
      FS: string;
      FStrs: array[0..1] of string;
      procedure TrimTwo;
    end;
  procedure TBox.TrimTwo;
  begin
    Delete(FS, 0, 2);        { implicit-Self field }
  end;
  procedure DelVar(var S: string);
  begin
    Delete(S, 0, 1);         { var-param }
  end;
  var
    B: TBox;
    V: string;
  begin
    B := TBox.Create();
    B.FS := 'hello';
    Delete(B.FS, 0, 2);      { class field: 'llo' }
    B.FStrs[0] := 'world';
    B.FStrs[1] := 'abcdef';
    Delete(B.FStrs[1], 0, 3);{ field-array element: 'def' }
    B.TrimTwo();             { implicit-Self on B.FS: 'o' }
    V := 'xyz';
    DelVar(V);               { var-param: 'yz' }
    WriteLn(B.FS, ' ', B.FStrs[0], ' ', B.FStrs[1], ' ', V)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'o world def yz' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringSetLength_Truncates;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringSetLength, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hel', 'Hel' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_Int64_ArithmeticOverInt32;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64Arith, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('6000000000', '6000000000' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_Int64_Comparison;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64Compare, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('big small', 'big' + LE + 'small' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_Int64_ForLoop;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64ForLoop, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('15', '15' + LE, Output);
end;

const
  SrcStringRelational = '''
    program Prog;
    procedure Chk(b: Boolean; const nm: string);
    begin if b then WriteLn(nm + ':T') else WriteLn(nm + ':F') end;
    begin
      Chk('abc' < 'abd', 'lt');
      Chk('abd' < 'abc', 'lt2');
      Chk('b' > 'a', 'gt');
      Chk('a' > 'b', 'gt2');
      Chk('abc' <= 'abc', 'le');
      Chk('abc' >= 'abc', 'ge');
      Chk('' < 'a', 'empty')
    end.
    ''';

procedure TE2EStringOpsTests.TestRun_StringRelational_Order;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStringRelational,
    'lt:T' + LE + 'lt2:F' + LE + 'gt:T' + LE + 'gt2:F' + LE +
    'le:T' + LE + 'ge:T' + LE + 'empty:T' + LE, 0);
end;

procedure TE2EStringOpsTests.TestRun_StringLiteral_HighByteSurvives;
var
  Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A string literal carrying a byte outside printable ASCII must reach the
    data section intact.  The QBE backend used to render such bytes as the
    four characters '\xNN' -- QBE's data strings have no numeric escape, so
    the literal text was copied through and BOTH the bytes and the length in
    the ARC header were wrong (byte 233 read back as 205).  The native
    backend was always correct, so only the QBE arm regressed; this is an
    AssertRunsOnAll so the two stay pinned together.

    The byte is spliced into the LITERAL with Chr(233) here, at test-build
    time -- writing 'ab' + Chr(233) + 'cd' as program text instead would
    emit two plain ASCII literals and a run-time concat, exercising nothing.
    It has to be inside the quotes to reach the data section. }
  Src :=
    'program P;' + LE +
    'var S: string;' + LE +
    'begin' + LE +
    '  S := ''ab' + Chr(233) + 'cd'';' + LE +
    '  WriteLn(Length(S));' + LE +
    '  WriteLn(Ord(S[2]))' + LE +
    'end.';
  AssertRunsOnAll(Src, '5' + LE + '233' + LE, 0);
end;

initialization
  RegisterTest(TE2EStringOpsTests);

end.
