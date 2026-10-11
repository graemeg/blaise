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

    { Record passed BY VALUE to a C routine: libc's inet_ntoa takes a
      4-byte struct in_addr by value, so the callee reads the record's
      bytes from the argument register.  (This test used to pass only
      pointers to memcpy, and the x86-64 backend silently passed the
      record's ADDRESS: BUG-20261007-x86-extern-record-byval.)  The second
      call passes a record-returning call's result straight through. }
    procedure TestRun_ExternalRecordParam_ByValue;

    { Record RETURNED by a C routine: libc's div and ldiv return structs in
      the integer registers (rax / x0 for 8 bytes, rax:rdx / x0:x1 for 16),
      assigned, read, passed on and discarded. }
    procedure TestRun_ExternalRecordReturn_IntegerShapes;
    { Apple's __sincos_stret returns two Doubles (arm64: a homogeneous float
      aggregate in d0:d1), __sincosf_stret two Singles (s0:s1). }
    procedure TestRun_ExternalRecordReturn_FloatPair_Arm64;
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
      TInAddr = record
        S_addr: Cardinal;
      end;
    function inet_ntoa(AIn: TInAddr): PChar; cdecl; external name 'inet_ntoa';
    function MakeAddr(A, B, C, D: Integer): TInAddr;
    begin
      { network byte order: the first octet is the lowest-addressed byte }
      Result.S_addr := Cardinal(A or (B shl 8) or (C shl 16) or (D shl 24))
    end;
    var
      Addr: TInAddr;
    begin
      Addr.S_addr := Cardinal($0403020A);
      WriteLn(string(inet_ntoa(Addr)));
      WriteLn(string(inet_ntoa(MakeAddr(192, 168, 1, 254))))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '10.2.3.4' + Chr(10) + '192.168.1.254' + Chr(10), 0);
end;

procedure TE2EExternalTests.TestRun_ExternalRecordReturn_IntegerShapes;
const
  Src = '''
    program P;
    type
      TDiv = record Quot, Rem: Integer; end;
      TLDiv = record Quot, Rem: Int64; end;
    function c_div(N, D: Integer): TDiv; external name 'div';
    function c_ldiv(N, D: Int64): TLDiv; external name 'ldiv';
    procedure Show(const D: TDiv); begin WriteLn('show ', D.Quot, ' ', D.Rem) end;
    var A: TDiv; B: TLDiv;
    begin
      A := c_div(17, 5); WriteLn(A.Quot, ' ', A.Rem);
      B := c_ldiv(100, 7); WriteLn(B.Quot, ' ', B.Rem);
      WriteLn(c_div(9, 2).Rem, ' ', c_ldiv(50, 8).Quot);
      Show(c_div(20, 6));
      c_div(1, 1);
      c_ldiv(1, 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '3 2' + #10 + '14 2' + #10 + '1 6' + #10 + 'show 3 2' + #10, 0);
end;

procedure TE2EExternalTests.TestRun_ExternalRecordReturn_FloatPair_Arm64;
{$IFDEF CPUARM64}
const
  Src = '''
    program P;
    type
      TSinCos = record S, C: Double; end;
      TSinCosF = record S, C: Single; end;
    function c_sincos(X: Double): TSinCos; external name '__sincos_stret';
    function c_sincosf(X: Single): TSinCosF; external name '__sincosf_stret';
    var D: TSinCos; F: TSinCosF;
    begin
      D := c_sincos(0.0); WriteLn(D.S:0:2, ' ', D.C:0:2);
      F := c_sincosf(0.0); WriteLn(F.S:0:2, ' ', F.C:0:2);
      WriteLn(c_sincos(0.0).C:0:2)
    end.
    ''';
{$ENDIF}
begin
{$IFDEF CPUARM64}
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0.00 1.00' + #10 + '0.00 1.00' + #10 + '1.00' + #10, 0);
{$ELSE}
  Ignore('__sincos_stret is an Apple arm64 symbol');
{$ENDIF}
end;

initialization
  RegisterTest(TE2EExternalTests);

end.
