{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Security.Crypto (SHA-1), including the Base64-composed WebSocket
  handshake.  Self-registers via the initialization section. }

unit Crypto.Tests;

interface

uses
  blaise.testing, SysUtils, Security.Crypto, Encoding.Base64, StrUtils;

type
  TCryptoTests = class(TTestCase)
  published
    procedure TestSha1Hex_KnownVectors;
    procedure TestSha1_DigestLength;
    procedure TestSha1Base64_WebSocketHandshake;
    procedure TestSha256Hex_KnownVectors;
    procedure TestSha256_DigestLength;
    procedure TestSha256Hex_BoundaryVectors;
    procedure TestMd5Hex_KnownVectors;
    procedure TestMd5_DigestLength;
    procedure TestHmacSha256Hex_KnownVectors;
    procedure TestHmacSha256_DigestLength;
    procedure TestHmacSha256Hex_LongKey;
    procedure TestConstantTimeEqual;
    procedure TestSha512Hex_KnownVectors;
    procedure TestSha512_DigestLength;
    procedure TestSha512Hex_PaddingBoundaries;
    procedure TestDigest_ChunkedUpdatesMatchOneShot;
    procedure TestDigest_MillionAs;
    procedure TestDigest_FinishResetsForReuse;
    procedure TestDigest_UpdateFile;
    procedure TestDigest_Sizes;
  end;

implementation

procedure TCryptoTests.TestSha1Hex_KnownVectors;
begin
  { FIPS / well-known SHA-1 test vectors. }
  AssertEquals('empty', 'da39a3ee5e6b4b0d3255bfef95601890afd80709', Sha1Hex(''));
  AssertEquals('abc',   'a9993e364706816aba3e25717850c26c9cd0d89d', Sha1Hex('abc'));
  AssertEquals('quick brown fox',
    '2fd4e1c67a2d28fced849ee1bb76e7391b93eb12',
    Sha1Hex('The quick brown fox jumps over the lazy dog'));
end;

procedure TCryptoTests.TestSha1_DigestLength;
begin
  AssertEquals('raw digest is 20 bytes', 20, Length(Sha1('anything')));
end;

procedure TCryptoTests.TestSha1Base64_WebSocketHandshake;
const
  GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
begin
  { RFC 6455 example: Sec-WebSocket-Accept = base64(sha1(key + GUID)). }
  AssertEquals('ws accept',
    's3pPLMBiTxaQ9kYGzzhZRbK+xOo=',
    Base64Encode(Sha1('dGhlIHNhbXBsZSBub25jZQ==' + GUID)));
end;

procedure TCryptoTests.TestSha256Hex_KnownVectors;
begin
  { NIST CAVP / FIPS 180-4 SHA-256 test vectors. }
  AssertEquals('empty',
    'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
    Sha256Hex(''));
  AssertEquals('abc',
    'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad',
    Sha256Hex('abc'));
  AssertEquals('448-bit (56 bytes, 2-block)',
    '248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1',
    Sha256Hex('abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq'));
  AssertEquals('896-bit (112 bytes, multi-block)',
    'cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1',
    Sha256Hex('abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu'));
end;

procedure TCryptoTests.TestSha256_DigestLength;
begin
  AssertEquals('raw digest is 32 bytes', 32, Length(Sha256('anything')));
end;

procedure TCryptoTests.TestSha256Hex_BoundaryVectors;
begin
  { 55 bytes: padding (0x80 + 8-byte length = 9 bytes) fits in one 64-byte block. }
  AssertEquals('55-byte single-block boundary',
    '9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318',
    Sha256Hex('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'));
end;

procedure TCryptoTests.TestMd5Hex_KnownVectors;
begin
  { RFC 1321 Appendix A.5 — all 7 test vectors. }
  AssertEquals('empty',
    'd41d8cd98f00b204e9800998ecf8427e', Md5Hex(''));
  AssertEquals('a',
    '0cc175b9c0f1b6a831c399e269772661', Md5Hex('a'));
  AssertEquals('abc',
    '900150983cd24fb0d6963f7d28e17f72', Md5Hex('abc'));
  AssertEquals('message digest',
    'f96b697d7cb7938d525a2f31aaf161d0', Md5Hex('message digest'));
  AssertEquals('a..z',
    'c3fcd3d76192e4007dfb496cca67e13b', Md5Hex('abcdefghijklmnopqrstuvwxyz'));
  AssertEquals('A..Za..z0..9',
    'd174ab98d277d9f5a5611c2c9f419d9f',
    Md5Hex('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'));
  AssertEquals('8x 1234567890',
    '57edf4a22be3c955ac49da2e2107b67a',
    Md5Hex('12345678901234567890123456789012345678901234567890123456789012345678901234567890'));
end;

procedure TCryptoTests.TestMd5_DigestLength;
begin
  AssertEquals('raw digest is 16 bytes', 16, Length(Md5('anything')));
end;

procedure TCryptoTests.TestHmacSha256Hex_KnownVectors;
var
  KeySB, DataSB: TStringBuilder;
  I: Int;
  Key1, Data1, Key3, Data3: string;
begin
  { RFC 4231 Test Case 1: 20-byte key of 0x0b, data = "Hi There" }
  KeySB := TStringBuilder.Create();
  for I := 0 to 19 do
    KeySB.AppendByte($0b);
  Key1 := KeySB.ToString();
  KeySB.Free();
  AssertEquals('TC1',
    'b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7',
    HmacSha256Hex(Key1, 'Hi There'));

  { RFC 4231 Test Case 2: key = "Jefe", data = "what do ya want for nothing?" }
  AssertEquals('TC2',
    '5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843',
    HmacSha256Hex('Jefe', 'what do ya want for nothing?'));

  { RFC 4231 Test Case 3: 20-byte key of 0xaa, 50-byte data of 0xdd }
  KeySB := TStringBuilder.Create();
  for I := 0 to 19 do
    KeySB.AppendByte($aa);
  Key3 := KeySB.ToString();
  KeySB.Free();
  DataSB := TStringBuilder.Create();
  for I := 0 to 49 do
    DataSB.AppendByte($dd);
  Data3 := DataSB.ToString();
  DataSB.Free();
  AssertEquals('TC3',
    '773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe',
    HmacSha256Hex(Key3, Data3));
end;

procedure TCryptoTests.TestHmacSha256_DigestLength;
begin
  AssertEquals('raw HMAC is 32 bytes', 32,
    Length(HmacSha256('key', 'data')));
end;

procedure TCryptoTests.TestHmacSha256Hex_LongKey;
var
  KeySB, DataSB: TStringBuilder;
  I: Int;
  LongKey, Data: string;
begin
  { RFC 4231 Test Case 5: 131-byte key of 0xaa (> 64-byte block size),
    data = "Test Using Larger Than Block-Size Key - Hash Key First" }
  KeySB := TStringBuilder.Create();
  for I := 0 to 130 do
    KeySB.AppendByte($aa);
  LongKey := KeySB.ToString();
  KeySB.Free();
  AssertEquals('TC5 long key',
    '60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54',
    HmacSha256Hex(LongKey, 'Test Using Larger Than Block-Size Key - Hash Key First'));

  { RFC 4231 Test Case 6: same 131-byte key,
    data = "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm." }
  AssertEquals('TC6 long key+data',
    '9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2',
    HmacSha256Hex(LongKey,
      'This is a test using a larger than block-size key and a ' +
      'larger than block-size data. The key needs to be hashed ' +
      'before being used by the HMAC algorithm.'));
end;

procedure TCryptoTests.TestConstantTimeEqual;
begin
  AssertTrue('equal strings', ConstantTimeEqual('abc', 'abc'));
  AssertTrue('both empty', ConstantTimeEqual('', ''));
  AssertFalse('different content', ConstantTimeEqual('abc', 'abd'));
  AssertFalse('different lengths', ConstantTimeEqual('abc', 'ab'));
  AssertFalse('one empty', ConstantTimeEqual('abc', ''));
  AssertFalse('other empty', ConstantTimeEqual('', 'abc'));
  AssertTrue('long equal', ConstantTimeEqual(
    'The quick brown fox jumps over the lazy dog',
    'The quick brown fox jumps over the lazy dog'));
  AssertFalse('long differ last byte', ConstantTimeEqual(
    'The quick brown fox jumps over the lazy dog',
    'The quick brown fox jumps over the lazy doh'));
end;

const
  NIST_896 = 'abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno' +
    'ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu';

{ 256 distinct byte values repeated five times: exercises every byte value and
  a length (1280) that is not a multiple of any block size used here. }
function AllBytes: string;
var
  SB: TStringBuilder;
  I, R: Int;
begin
  SB := TStringBuilder.Create();
  for R := 1 to 5 do
    for I := 0 to 255 do
      SB.AppendByte(I);
  Result := SB.ToString();
  SB.Free();
end;

procedure TCryptoTests.TestSha512Hex_KnownVectors;
begin
  { FIPS 180-4 / NIST CAVP SHA-512 vectors. }
  AssertEquals('empty',
    'cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce' +
    '47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e',
    Sha512Hex(''));
  AssertEquals('abc',
    'ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a' +
    '2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f',
    Sha512Hex('abc'));
  AssertEquals('896-bit (two blocks)',
    '8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018' +
    '501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909',
    Sha512Hex(NIST_896));
  AssertEquals('all byte values',
    'c93f55ccf2fa8c82699ff9b58afe3591242b135d908a6d865e17e38adb41c21d' +
    '1d5359e51273036373d54d20b5659cc87e6e7b381ff027d33f971416cc590f90',
    Sha512Hex(AllBytes()));
end;

procedure TCryptoTests.TestSha512_DigestLength;
begin
  AssertEquals('raw digest is 64 bytes', 64, Length(Sha512('anything')));
end;

procedure TCryptoTests.TestSha512Hex_PaddingBoundaries;
begin
  { 111 bytes: the length still fits in the first block.  112 bytes: the
    128-bit length no longer fits, so padding spills into a second block. }
  AssertEquals('111 bytes',
    'fa9121c7b32b9e01733d034cfc78cbf67f926c7ed83e82200ef8681819692176' +
    '0b4beff48404df811b953828274461673c68d04e297b0eb7b2b4d60fc6b566a2',
    Sha512Hex(DupeString('a', 111)));
  AssertEquals('112 bytes',
    'c01d080efd492776a1c43bd23dd99d0a2e626d481e16782e75d54c2503b5dc32' +
    'bd05f0f1ba33e568b88fd2d970929b719ecbb152f58f130a407c8830604b70ca',
    Sha512Hex(DupeString('a', 112)));
end;

{ Feeds AData to ADigest in uneven pieces (1, 2, 3, ... bytes) so that block
  boundaries fall in the middle of an update. }
function DigestInPieces(ADigest: THashDigest; const AData: string): string;
var
  Pos, N: Int;
begin
  Pos := 0;
  N := 1;
  while Pos < Length(AData) do
  begin
    if Pos + N > Length(AData) then
      N := Length(AData) - Pos;
    ADigest.Update(Copy(AData, Pos, N));
    Pos := Pos + N;
    N := N + 1;
  end;
  Result := ADigest.FinishHex();
end;

procedure TCryptoTests.TestDigest_ChunkedUpdatesMatchOneShot;
var
  Data: string;
  D: THashDigest;
begin
  Data := AllBytes() + NIST_896;
  D := TSha1Digest.Create();
  AssertEquals('sha1', Sha1Hex(Data), DigestInPieces(D, Data));
  D.Free();
  D := TSha256Digest.Create();
  AssertEquals('sha256', Sha256Hex(Data), DigestInPieces(D, Data));
  D.Free();
  D := TSha512Digest.Create();
  AssertEquals('sha512', Sha512Hex(Data), DigestInPieces(D, Data));
  D.Free();
end;

procedure TCryptoTests.TestDigest_MillionAs;
var
  Chunk: string;
  D1, D256, D512: THashDigest;
  I: Int;
begin
  { FIPS 180 "one million 'a'" vectors, fed 1000 bytes at a time: the
    message is never held in memory whole. }
  Chunk := DupeString('a', 1000);
  D1 := TSha1Digest.Create();
  D256 := TSha256Digest.Create();
  D512 := TSha512Digest.Create();
  for I := 1 to 1000 do
  begin
    D1.Update(Chunk);
    D256.Update(Chunk);
    D512.Update(Chunk);
  end;
  AssertEquals('sha1', '34aa973cd4c4daa4f61eeb2bdbad27316534016f', D1.FinishHex());
  AssertEquals('sha256',
    'cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0',
    D256.FinishHex());
  AssertEquals('sha512',
    'e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973eb' +
    'de0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b',
    D512.FinishHex());
  D1.Free();
  D256.Free();
  D512.Free();
end;

procedure TCryptoTests.TestDigest_FinishResetsForReuse;
var
  D: THashDigest;
begin
  D := TSha256Digest.Create();
  D.Update('discarded');
  D.Finish();
  D.Update('abc');
  AssertEquals('after finish',
    'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad',
    D.FinishHex());
  D.Update('discarded');
  D.Reset();
  AssertEquals('after reset',
    'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
    D.FinishHex());
  D.Free();
end;

procedure TCryptoTests.TestDigest_UpdateFile;
var
  Path, Data: string;
  D: THashDigest;
begin
  { Larger than the internal read buffer, so the file is read in pieces. }
  Data := DupeString('x', 100000) + AllBytes();
  Path := ExcludeTrailingPathDelimiter(GetTempDir()) + '/blaise-digest-' +
    IntToStr(GetProcessID()) + '.bin';
  WriteFile(Path, Data);
  try
    D := TSha512Digest.Create();
    D.UpdateFile(Path);
    AssertEquals('sha512 of file', Sha512Hex(Data), D.FinishHex());
    D.Free();
    AssertEquals('Sha1FileHex', Sha1Hex(Data), Sha1FileHex(Path));
    AssertEquals('Sha256FileHex', Sha256Hex(Data), Sha256FileHex(Path));
    AssertEquals('Sha512FileHex', Sha512Hex(Data), Sha512FileHex(Path));
  finally
    DeleteFile(Path);
  end;
end;

procedure TCryptoTests.TestDigest_Sizes;
var
  D: THashDigest;
begin
  D := TSha1Digest.Create();
  AssertEquals('sha1 size', 20, D.DigestSize());
  AssertEquals('sha1 raw', 20, Length(D.Finish()));
  D.Free();
  D := TSha256Digest.Create();
  AssertEquals('sha256 size', 32, D.DigestSize());
  D.Free();
  D := TSha512Digest.Create();
  AssertEquals('sha512 size', 64, D.DigestSize());
  D.Free();
end;

initialization
  RegisterTest(TCryptoTests);

end.
