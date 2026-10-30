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
  blaise.testing, Security.Crypto, Encoding.Base64, StrUtils;

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

initialization
  RegisterTest(TCryptoTests);

end.
