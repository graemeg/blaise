{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit SysUtils.Tests;

interface

uses
  blaise.testing, SysUtils;

type
  TSysUtilsTests = class(TTestCase)
  published
    { IsTerminal: no handle that cannot be open is a terminal }
    procedure TestIsTerminal_InvalidHandles;
    { GetUserDir: the home directory, with a trailing separator }
    procedure TestGetUserDir_IsHomeWithSeparator;
    { SecureRandomBytes: the operating system's CSPRNG }
    procedure TestSecureRandomBytes_FillsBuffer;
    procedure TestSecureRandomBytes_DiffersPerCall;
    { getentropy hands out at most 256 bytes per call: a larger request
      is filled to its last byte }
    procedure TestSecureRandomBytes_LargerThanOneSyscall;
    procedure TestSecureRandomBytes_ZeroCount;
  end;

implementation

function AllZero(ABuf: Pointer; ACount: Int): Boolean;
var
  P: ^Byte;
  I: Int;
begin
  P := ABuf;
  for I := 0 to ACount - 1 do
  begin
    if P^ <> 0 then
      Exit(False);
    P := P + 1;
  end;
  Result := True;
end;

procedure TSysUtilsTests.TestSecureRandomBytes_FillsBuffer;
var
  Buf: array[0..31] of Byte;
begin
  FillByte(Buf, SizeOf(Buf), 0);
  AssertTrue('succeeds', SecureRandomBytes(@Buf[0], 32));
  { 32 zero bytes from a CSPRNG has probability 2^-256 }
  AssertFalse('not all zero', AllZero(@Buf[0], 32));
end;

procedure TSysUtilsTests.TestSecureRandomBytes_DiffersPerCall;
var
  A, B: array[0..31] of Byte;
  I: Int;
  Same: Boolean;
begin
  AssertTrue('first', SecureRandomBytes(@A[0], 32));
  AssertTrue('second', SecureRandomBytes(@B[0], 32));
  Same := True;
  for I := 0 to 31 do
    if A[I] <> B[I] then
      Same := False;
  AssertFalse('two calls differ', Same);
end;

procedure TSysUtilsTests.TestSecureRandomBytes_LargerThanOneSyscall;
var
  Buf: array[0..1023] of Byte;
begin
  FillByte(Buf, SizeOf(Buf), 0);
  AssertTrue('succeeds', SecureRandomBytes(@Buf[0], 1024));
  { each 32-byte slice past the first 256 bytes was written }
  AssertFalse('bytes 256..287', AllZero(@Buf[256], 32));
  AssertFalse('bytes 992..1023', AllZero(@Buf[992], 32));
end;

procedure TSysUtilsTests.TestSecureRandomBytes_ZeroCount;
var
  Buf: array[0..3] of Byte;
begin
  FillByte(Buf, SizeOf(Buf), 0);
  AssertTrue('zero bytes succeeds', SecureRandomBytes(@Buf[0], 0));
  AssertTrue('nothing written', AllZero(@Buf[0], 4));
end;

procedure TSysUtilsTests.TestIsTerminal_InvalidHandles;
begin
  AssertFalse('negative', IsTerminal(-1));
  AssertFalse('never opened', IsTerminal(100000));
  AssertFalse('beyond Int32', IsTerminal(Int(High(Int32)) + 1));
end;

procedure TSysUtilsTests.TestGetUserDir_IsHomeWithSeparator;
var
  Home: string;
begin
  {$IFDEF WINDOWS}
  Home := GetEnvironmentVariable('USERPROFILE');
  {$ELSE}
  Home := GetEnvironmentVariable('HOME');
  {$ENDIF}
  if Home = '' then
    AssertEquals('', GetUserDir())
  else
    AssertEquals(IncludeTrailingPathDelimiter(Home), GetUserDir());
end;

initialization
  RegisterTest(TSysUtilsTests);

end.
