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
  Classes, SysUtils, blaise.testing, cp.test.e2e.base;

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
    { Records by value to and from a C routine, against C compiled here with
      cc: mixed int/float records of 8 and 16 bytes, a 32-byte record (a
      private copy the callee may change), float records spilling past the
      fp registers with float and record arguments after them, double pairs
      and double+int64 halves, a mixed record pushed past the integer
      registers, and every shape returned from C and passed straight back.
      arm64 (AAPCS64: memory images, HFAs, Darwin stack packing) and x86-64
      (System V eightbyte classes) both refused or misplaced most of them.
      Needs cc. }
    procedure TestRun_ExternalRecordShapes;
    { a C routine returning the bitmap of a jumbo set (a 25-byte struct for
      set of 0..199): the members it sets are the members Blaise sees }
    procedure TestRun_ExternalJumboSetResult;
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
    function c_strlen(S: PChar): Int32; external name 'strlen';
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
    function c_strlen(S: PChar): Int32; external 'c' name 'strlen';
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
    function c_strlen(S: PChar): UInt16; external name 'strlen';
    var W: UInt16;
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
    function c_atoi(S: PChar): Int16; external name 'atoi';
    var V: Int16;
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
    function c_atoi(S: PChar): Int32; external name 'atoi';
    var I: Int;
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
    function c_sinf(X: Float32): Float32; cdecl; external 'm' name 'sinf';
    var R: Float32;
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
    function c_sqrtf(X: Float32): Float32; cdecl; external 'm' name 'sqrtf';
    var R: Float32;
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
    function MyAbsFunc(N: Int32): Int32; external name 'abs';
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
        S_addr: UInt32;
      end;
    function inet_ntoa(AIn: TInAddr): PChar; cdecl; external name 'inet_ntoa';
    function MakeAddr(A, B, C, D: Int): TInAddr;
    begin
      { network byte order: the first octet is the lowest-addressed byte }
      Result.S_addr := UInt32(A or (B shl 8) or (C shl 16) or (D shl 24))
    end;
    var
      Addr: TInAddr;
    begin
      Addr.S_addr := UInt32($0403020A);
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
      TDiv = record Quot, Rem: Int32; end;
      TLDiv = record Quot, Rem: Int64; end;
    function c_div(N, D: Int32): TDiv; external name 'div';
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
      TSinCos = record S, C: Float64; end;
      TSinCosF = record S, C: Float32; end;
    function c_sincos(X: Float64): TSinCos; external name '__sincos_stret';
    function c_sincosf(X: Float32): TSinCosF; external name '__sincosf_stret';
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


procedure TE2EExternalTests.TestRun_ExternalRecordShapes;
const
  CSrc =
    'typedef struct { int a; float f; double d; } Mixed16;' + #10 +
    'typedef struct { float x; int n; } Mixed8;' + #10 +
    'typedef struct { long a, b, c; double d; } Big32;' + #10 +
    'typedef struct { float x, y, z, w; } V4;' + #10 +
    'typedef struct { float x, y; } V2;' + #10 +
    'typedef struct { double x, y; } D2;' + #10 +
    'typedef struct { double x; long n; } DL;' + #10 +
    'double abi_d2(D2 a, D2 b) { return a.x + a.y * 10 + b.x * 100 + b.y * 1000; }' + #10 +
    'double abi_dl(DL a, int k) { return a.x + a.n * 10 + k * 100; }' + #10 +
    'long abi_ispill(long a, long b, long c, long d, long e, Mixed16 m, long g)' +
    ' { return a+b+c+d+e + m.a*1000 + (long)m.d*100 + g*10000; }' + #10 +
    'V2 abi_mkv2(float x, float y) { V2 r = { x, y }; return r; }' + #10 +
    'V4 abi_mkv4(float x, float y, float z, float w) { V4 r = { x, y, z, w };' +
    ' return r; }' + #10 +
    'D2 abi_mkd2(double x, double y) { D2 r = { x, y }; return r; }' + #10 +
    'DL abi_mkdl(double x, long n) { DL r = { x, n }; return r; }' + #10 +
    'Big32 abi_mkbig(long a, double d) { Big32 r = { a, a + 1, a + 2, d };' +
    ' return r; }' + #10 +
    'double abi_mixed16(Mixed16 m) { return m.a + m.f + m.d; }' + #10 +
    'double abi_mixed8(int k, Mixed8 m) { return k * 1000 + m.x + m.n; }' + #10 +
    'long abi_big(Big32 b, int k) { long r = b.a + b.b * 10 + b.c * 100 +' +
    ' (long)b.d * 1000 + k * 10000; b.a = 99; return r; }' + #10 +
    'double abi_v4spill(double a, double b, double c, double d, double e,' +
    ' double f, double g, V4 v, double h) { return a+b+c+d+e+f+g + v.x*1000' +
    ' + v.y*100 + v.z*10 + v.w + h*10000; }' + #10 +
    'double abi_v2spill(double a, double b, double c, double d, double e,' +
    ' double f, double g, V2 v, float h, V2 u) { return a+b+c+d+e+f+g +' +
    ' v.x*1000 + v.y*100 + h*10000 + u.x * 100000 + u.y * 1000000; }' + #10 +
    'Mixed8 abi_mk8(float x, int n) { Mixed8 r = { x, n }; return r; }' + #10 +
    'Mixed16 abi_mk16(int a, float f, double d) { Mixed16 r = { a, f, d };' +
    ' return r; }' + #10;
  Src = '''
    program T;
    type
      TMixed16 = record A: Int32; F: Float32; D: Float64; end;
      TMixed8 = record X: Float32; N: Int32; end;
      TBig32 = record A, B, C: Int64; D: Float64; end;
      TV4 = record X, Y, Z, W: Float32; end;
      TV2 = record X, Y: Float32; end;
      TD2 = record X, Y: Float64; end;
      TDL = record X: Float64; N: Int64; end;
    function abi_d2(A, B: TD2): Float64; cdecl; external 'abi';
    function abi_dl(A: TDL; K: Int32): Float64; cdecl; external 'abi';
    function abi_ispill(A, B, C, D, E: Int64; M: TMixed16; G: Int64): Int64; cdecl; external 'abi';
    function abi_mkv2(X, Y: Float32): TV2; cdecl; external 'abi';
    function abi_mkv4(X, Y, Z, W: Float32): TV4; cdecl; external 'abi';
    function abi_mkd2(X, Y: Float64): TD2; cdecl; external 'abi';
    function abi_mkdl(X: Float64; N: Int64): TDL; cdecl; external 'abi';
    function abi_mkbig(A: Int64; D: Float64): TBig32; cdecl; external 'abi';
    function abi_mixed16(M: TMixed16): Float64; cdecl; external 'abi';
    function abi_mixed8(K: Int32; M: TMixed8): Float64; cdecl; external 'abi';
    function abi_big(B: TBig32; K: Int32): Int64; cdecl; external 'abi';
    function abi_v4spill(A, B, C, D, E, F, G: Float64; V: TV4; H: Float64): Float64; cdecl; external 'abi';
    function abi_v2spill(A, B, C, D, E, F, G: Float64; V: TV2; H: Float32; U: TV2): Float64; cdecl; external 'abi';
    function abi_mk8(X: Float32; N: Int32): TMixed8; cdecl; external 'abi';
    function abi_mk16(A: Int32; F: Float32; D: Float64): TMixed16; cdecl; external 'abi';
    var M: TMixed16; M8: TMixed8; B: TBig32; V: TV4; V2, U2: TV2; D2a, D2b: TD2; DL: TDL;
    begin
      M.A := 1; M.F := 2.5; M.D := 4.25;
      WriteLn('mixed16 ', abi_mixed16(M):0:2);
      M8.X := 1.5; M8.N := 7;
      WriteLn('mixed8 ', abi_mixed8(3, M8):0:2);
      B.A := 1; B.B := 2; B.C := 3; B.D := 4.0;
      WriteLn('big ', abi_big(B, 5), ' ', B.A);
      V.X := 1; V.Y := 2; V.Z := 3; V.W := 4;
      WriteLn('v4 ', abi_v4spill(0.5, 0, 0, 0, 0, 0, 0, V, 2):0:2);
      V2.X := 1; V2.Y := 2; U2.X := 3; U2.Y := 4;
      WriteLn('v2 ', abi_v2spill(0.5, 0, 0, 0, 0, 0, 0, V2, 5, U2):0:2);
      M8 := abi_mk8(2.5, 9); WriteLn('mk8 ', M8.X:0:2, ' ', M8.N);
      M := abi_mk16(3, 1.25, 6.5); WriteLn('mk16 ', M.A, ' ', M.F:0:2, ' ', M.D:0:2);
      WriteLn('pass ', abi_mixed16(abi_mk16(1, 1, 1)):0:2);
      D2a.X := 1; D2a.Y := 2; D2b.X := 3; D2b.Y := 4;
      WriteLn('d2 ', abi_d2(D2a, D2b):0:2);
      DL.X := 0.5; DL.N := 3;
      WriteLn('dl ', abi_dl(DL, 2):0:2);
      M.A := 1; M.F := 2.5; M.D := 4.25;
      WriteLn('ispill ', abi_ispill(1, 0, 0, 0, 0, M, 2));
      V2 := abi_mkv2(1.5, 2.5); WriteLn('mkv2 ', V2.X:0:2, ' ', V2.Y:0:2);
      V := abi_mkv4(1, 2, 3, 4); WriteLn('mkv4 ', V.X:0:1, V.Y:0:1, V.Z:0:1, V.W:0:1);
      D2a := abi_mkd2(7.5, 8.5); WriteLn('mkd2 ', D2a.X:0:2, ' ', D2a.Y:0:2);
      DL := abi_mkdl(9.5, 11); WriteLn('mkdl ', DL.X:0:2, ' ', DL.N);
      B := abi_mkbig(5, 6.5); WriteLn('mkbig ', B.A, B.B, B.C, ' ', B.D:0:2);
    end.
    ''';
var
  CFile, OFile, Output, Dummy: string;
  RCode: Int;
  SL: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  if RunProc('cc', ['--version'], Dummy) <> 0 then begin Ignore('no cc'); Exit; end;
  CFile := IncludeTrailingPathDelimiter(FScratch) + 'abi.c';
  OFile := IncludeTrailingPathDelimiter(FScratch) + 'abi.o';
  SL := TStringList.Create();
  try
    SL.Text := CSrc;
    SL.SaveToFile(CFile);
  finally
    SL.Free();
  end;
  AssertEquals('cc -c', 0, RunProc('cc', ['-c', '-o', OFile, CFile], Dummy));
  AssertEquals('ar', 0, RunProc('ar', ['rcs',
    IncludeTrailingPathDelimiter(FScratch) + 'libabi.a', OFile], Dummy));
  { the C side is a static archive the external linker resolves -labi
    against (the internal Mach-O linker binds unknown libraries to
    libSystem), so the binary needs no runtime library path }
  SL := TStringList.Create();
  try
    SL.Text := Src;
    SL.SaveToFile(IncludeTrailingPathDelimiter(FScratch) + 'abi_t.pas');
  finally
    SL.Free();
  end;
  RCode := RunProc(ProjectRoot() + 'compiler/target/blaise',
    ['--source', IncludeTrailingPathDelimiter(FScratch) + 'abi_t.pas',
     '--linker', 'external', '--lib-path', FScratch,
     '--output', IncludeTrailingPathDelimiter(FScratch) + 'abi_t'], Output);
  AssertEquals('compile: ' + Output, 0, RCode);
  RCode := RunProc(IncludeTrailingPathDelimiter(FScratch) + 'abi_t', [], Output);
  AssertEquals('exit code: ' + Output, 0, RCode);
  AssertEquals('output',
    'mixed16 7.75' + #10 + 'mixed8 3008.50' + #10 + 'big 54321 1' + #10 +
    'v4 21234.50' + #10 + 'v2 4351200.50' + #10 + 'mk8 2.50 9' + #10 +
    'mk16 3 1.25 6.50' + #10 + 'pass 3.00' + #10 + 'd2 4321.00' + #10 +
    'dl 230.50' + #10 + 'ispill 21401' + #10 + 'mkv2 1.50 2.50' + #10 +
    'mkv4 1.02.03.04.0' + #10 + 'mkd2 7.50 8.50' + #10 + 'mkdl 9.50 11' + #10 +
    'mkbig 567 6.50' + #10, Output);
end;

procedure TE2EExternalTests.TestRun_ExternalJumboSetResult;
const
  CSrc =
    'typedef struct { unsigned char b[25]; } Bits200;' + #10 +
    'Bits200 abi_bits(int a, int b) { Bits200 r; int i;' +
    ' for (i = 0; i < 25; i++) r.b[i] = 0;' +
    ' r.b[a / 8] |= 1 << (a % 8); r.b[b / 8] |= 1 << (b % 8); return r; }' + #10;
  Src = '''
    program T;
    type
      TBig = 0..199;
      TJumbo = set of TBig;
    function abi_bits(A, B: Int32): TJumbo; external 'abi';
    var
      J: TJumbo;
    begin
      J := abi_bits(3, 150);
      WriteLn(3 in J, ' ', 150 in J, ' ', 4 in J, ' ', 199 in J);
      WriteLn(7 in abi_bits(7, 199), ' ', 199 in abi_bits(7, 199))
    end.
    ''';
var
  CFile, OFile, Output, Dummy: string;
  RCode: Int;
  SL: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  if RunProc('cc', ['--version'], Dummy) <> 0 then begin Ignore('no cc'); Exit; end;
  CFile := IncludeTrailingPathDelimiter(FScratch) + 'abij.c';
  OFile := IncludeTrailingPathDelimiter(FScratch) + 'abij.o';
  SL := TStringList.Create();
  try
    SL.Text := CSrc;
    SL.SaveToFile(CFile);
  finally
    SL.Free();
  end;
  AssertEquals('cc -c', 0, RunProc('cc', ['-c', '-o', OFile, CFile], Dummy));
  AssertEquals('ar', 0, RunProc('ar', ['rcs',
    IncludeTrailingPathDelimiter(FScratch) + 'libabi.a', OFile], Dummy));
  SL := TStringList.Create();
  try
    SL.Text := Src;
    SL.SaveToFile(IncludeTrailingPathDelimiter(FScratch) + 'abij_t.pas');
  finally
    SL.Free();
  end;
  RCode := RunProc(ProjectRoot() + 'compiler/target/blaise',
    ['--source', IncludeTrailingPathDelimiter(FScratch) + 'abij_t.pas',
     '--linker', 'external', '--lib-path', FScratch,
     '--output', IncludeTrailingPathDelimiter(FScratch) + 'abij_t'], Output);
  AssertEquals('compile: ' + Output, 0, RCode);
  RCode := RunProc(IncludeTrailingPathDelimiter(FScratch) + 'abij_t', [], Output);
  AssertEquals('exit code: ' + Output, 0, RCode);
  AssertEquals('output', 'True True False False' + #10 + 'True True' + #10,
    Output);
end;

initialization
  RegisterTest(TE2EExternalTests);

end.
