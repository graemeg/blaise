{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.external;

{ E2E tests for external/FFI declarations: narrow-int return masking,
  Single-param narrowing, record-param by-value passing, external name
  aliasing.  Compile+run on both backends. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EExternalTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Basic external call — strlen via external name }
    procedure TestRun_ExternalName_Strlen;

    { Library-qualified external — external 'c' name 'strlen': the bare library
      name is parsed and recorded (propagated via the unit's LinkLibs) while the
      symbol resolves as usual. }
    procedure TestRun_ExternalLibName_Strlen;

    { Narrow-int return masking: strlen returns size_t (64-bit) but declared
      as Byte/Word/SmallInt — upper bits must be masked/sign-extended. }
    procedure TestRun_ExternalByteReturn_MaskedCorrectly;
    procedure TestRun_ExternalWordReturn_MaskedCorrectly;
    procedure TestRun_ExternalSmallIntReturn_SignExtended;
    procedure TestRun_ExternalIntegerReturn_NoTruncation;

    { Byte return in a conditional — the classic "garbage upper bits" bug:
      if the AND mask is missing, a stale non-zero in bits 8..31 makes
      the comparison wrong. }
    procedure TestRun_ExternalByteReturn_UsedInCondition;

    { Single-param narrowing: double literal narrowed to float before call }
    procedure TestRun_ExternalSingleParam_SinfReturnsCorrectValue;
    procedure TestRun_ExternalSingleReturn_RoundTrip;

    { external name aliasing — Pascal name differs from C symbol }
    procedure TestRun_ExternalNameAlias_CallsCorrectSymbol;

    { Record passed by value to external cdecl function — uses memcpy as
      a proxy since we cannot add custom C code to the link. }
    procedure TestRun_ExternalRecordParam_ByValue;
  end;

implementation

procedure TE2EExternalTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-external');
end;

procedure TE2EExternalTests.TestRun_ExternalName_Strlen;
const Src = '''
    program T;
    function c_strlen(S: PChar): Integer; external name 'strlen';
    begin
      WriteLn(c_strlen(PChar('hello')))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '5' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalLibName_Strlen;
const Src = '''
    program T;
    function c_strlen(S: PChar): Integer; external 'c' name 'strlen';
    begin
      WriteLn(c_strlen(PChar('hello')))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '5' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalByteReturn_MaskedCorrectly;
const Src = '''
    program T;
    function c_strlen(S: PChar): Byte; external name 'strlen';
    var B: Byte;
    begin
      B := c_strlen(PChar('abc'));
      WriteLn(B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '3' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalWordReturn_MaskedCorrectly;
const Src = '''
    program T;
    function c_strlen(S: PChar): Word; external name 'strlen';
    var W: Word;
    begin
      W := c_strlen(PChar('abcdef'));
      WriteLn(W)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '6' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalSmallIntReturn_SignExtended;
const Src = '''
    program T;
    function c_atoi(S: PChar): SmallInt; external name 'atoi';
    var V: SmallInt;
    begin
      V := c_atoi(PChar('-7'));
      WriteLn(V)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '-7' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalIntegerReturn_NoTruncation;
const Src = '''
    program T;
    function c_atoi(S: PChar): Integer; external name 'atoi';
    var I: Integer;
    begin
      I := c_atoi(PChar('1000000'));
      WriteLn(I)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1000000' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalByteReturn_UsedInCondition;
const Src = '''
    program T;
    function c_strlen(S: PChar): Byte; external name 'strlen';
    begin
      if c_strlen(PChar('')) = 0 then
        WriteLn('empty')
      else
        WriteLn('BUG');
      if c_strlen(PChar('x')) <> 0 then
        WriteLn('notempty')
      else
        WriteLn('BUG')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'empty' + Chr(10) + 'notempty' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalSingleParam_SinfReturnsCorrectValue;
const Src = '''
    program T;
    function c_sinf(X: Single): Single; cdecl; external 'm' name 'sinf';
    var R: Single;
    begin
      R := c_sinf(0.0);
      if R = 0.0 then
        WriteLn('ok')
      else
        WriteLn('BUG')
    end.
    ''';
begin
  { sinf lives in libm, and BOTH arms have to be told so, by different
    routes.  The SOURCE names the library (external 'm') because the native
    arm goes through the compiler's own CLI, which links what the source
    declares and has no way to receive a harness flag.  The ['m'] argument
    is still needed because the QBE arm links via an external cc that the
    harness drives directly.  Previously the source used the bare
    `external name` form and leaned on the harness alone, which stopped
    working the moment native switched to the CLI. }
  AssertRunsOnAllLibs(Src, ['m'], 'ok' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalSingleReturn_RoundTrip;
const Src = '''
    program T;
    function c_sqrtf(X: Single): Single; cdecl; external 'm' name 'sqrtf';
    var R: Single;
    begin
      R := c_sqrtf(4.0);
      if R = 2.0 then
        WriteLn('ok')
      else
        WriteLn('BUG')
    end.
    ''';
begin
  { see the note on the sinf test — the source names libm for the native
    CLI arm, the ['m'] argument covers the QBE arm's external cc link }
  AssertRunsOnAllLibs(Src, ['m'], 'ok' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalNameAlias_CallsCorrectSymbol;
const Src = '''
    program T;
    function MyAbsFunc(N: Integer): Integer; external name 'abs';
    begin
      WriteLn(MyAbsFunc(-42))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalRecordParam_ByValue;
const Src = '''
    program T;
    type
      TPair = record
        A: Integer;
        B: Integer;
      end;
    procedure c_memcpy(Dst, Src: Pointer; N: Integer); external name 'memcpy';
    var
      R: TPair;
      Buf: array[0..7] of Byte;
      V: Integer;
    begin
      R.A := 99;
      R.B := 77;
      c_memcpy(@Buf[0], @R, 4);
      V := Buf[0] + Buf[1] * 256 + Buf[2] * 65536 + Buf[3] * 16777216;
      WriteLn(V)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '99' + Chr(10), 0);
end;

initialization
  RegisterTest(TE2EExternalTests);

end.
