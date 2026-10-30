{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Net.WebSockets: handshake accept key and frame encode/decode.
  Self-registers via the initialization section. }

unit WebSockets.Tests;

interface

uses
  blaise.testing, Net.WebSockets, StrUtils;

type
  TWebSocketsTests = class(TTestCase)
  published
    procedure TestAccept;
    procedure TestEncodeShortText;
    procedure TestEncode126;
    procedure TestRoundTripUnmasked;
    procedure TestRoundTripMasked;
    procedure TestPartialBufferIsInvalid;
    procedure TestEncodeMaskedRoundTrip;
    procedure TestEncodeMaskedBitSet;
    procedure TestEncodeMaskedKeysDiffer;
    procedure TestEncodeMaskedBinaryOpcode;
  end;

implementation

procedure TWebSocketsTests.TestAccept;
begin
  { RFC 6455 6.1 worked example. }
  AssertEquals('accept', 's3pPLMBiTxaQ9kYGzzhZRbK+xOo=',
    WebSocketAccept('dGhlIHNhbXBsZSBub25jZQ=='));
end;

procedure TWebSocketsTests.TestEncodeShortText;
var F: string;
begin
  F := EncodeTextFrame('hi');
  AssertEquals('len', 4, Int32(Length(F)));
  AssertEquals('b0 fin+text', $81, Int32(Byte(F[0])));
  AssertEquals('b1 len',      2,    Int32(Byte(F[1])));
  AssertEquals('payload h',   104, Int32(Byte(F[2])));   { 'h' }
end;

procedure TWebSocketsTests.TestEncode126;
var
  Payload, F: string;
  I: Int;
begin
  { 200 bytes -> extended 16-bit length form (126 marker + 2 bytes). }
  Payload := '';
  for I := 1 to 200 do Payload := Payload + 'x';
  F := EncodeTextFrame(Payload);
  AssertEquals('b1 marker', 126, Int32(Byte(F[1])));
  AssertEquals('len hi', 0,   Int32(Byte(F[2])));
  AssertEquals('len lo', 200, Int32(Byte(F[3])));
  AssertEquals('total', 4 + 200, Int32(Length(F)));
end;

procedure TWebSocketsTests.TestRoundTripUnmasked;
var
  F: string;
  D: TWsFrame;
begin
  F := EncodeTextFrame('hello world');
  D := DecodeFrame(F);
  AssertTrue('valid', D.Valid);
  AssertTrue('fin', D.Fin);
  AssertEquals('opcode', WS_OP_TEXT, D.Opcode);
  AssertEquals('payload', 'hello world', D.Payload);
  AssertEquals('consumed', Length(F), D.Consumed);
end;

procedure TWebSocketsTests.TestRoundTripMasked;
var
  Buf: string;
  D: TWsFrame;
  SB: TStringBuilder;
  Mask: array[0..3] of Byte;
  Plain: string;
  I: Int;
begin
  { Hand-build a masked client text frame "ping" (clients must mask). }
  Plain := 'ping';
  Mask[0] := 10; Mask[1] := 20; Mask[2] := 30; Mask[3] := 40;
  SB := TStringBuilder.Create();
  SB.AppendByte($81);                 { FIN + text }
  SB.AppendByte($80 or Length(Plain)); { MASK + len }
  for I := 0 to 3 do SB.AppendByte(Mask[I]);
  for I := 0 to Length(Plain) - 1 do
    SB.AppendByte(Byte(Plain[I]) xor Mask[I and 3]);
  Buf := SB.ToString();
  SB.Free();

  D := DecodeFrame(Buf);
  AssertTrue('valid', D.Valid);
  AssertEquals('unmasked payload', Plain, D.Payload);
  AssertEquals('consumed', Length(Buf), D.Consumed);
end;

procedure TWebSocketsTests.TestPartialBufferIsInvalid;
var
  F, Partial: string;
  D: TWsFrame;
begin
  F := EncodeTextFrame('hello world');
  Partial := Copy(F, 0, 3);   { header + 1 payload byte, incomplete }
  D := DecodeFrame(Partial);
  AssertFalse('not valid', D.Valid);
  AssertEquals('consumed 0', 0, D.Consumed);
end;

procedure TWebSocketsTests.TestEncodeMaskedRoundTrip;
var
  F: string;
  D: TWsFrame;
begin
  { A client-masked frame must survive DecodeFrame back to the plaintext. }
  F := EncodeMaskedTextFrame('hello world');
  D := DecodeFrame(F);
  AssertTrue('valid', D.Valid);
  AssertTrue('fin', D.Fin);
  AssertEquals('opcode', WS_OP_TEXT, D.Opcode);
  AssertEquals('payload', 'hello world', D.Payload);
  AssertEquals('consumed', Length(F), D.Consumed);
end;

procedure TWebSocketsTests.TestEncodeMaskedBitSet;
var
  F: string;
begin
  { The MASK bit (top bit of byte 1) must be set on a client frame, and the
    header must carry 4 mask bytes + payload (2 + 4 + 5 = 11 for "abcde"). }
  F := EncodeMaskedTextFrame('abcde');
  AssertTrue('mask bit set', (Byte(F[1]) and $80) <> 0);
  AssertEquals('len field', 5, Int32(Byte(F[1]) and $7F));
  AssertEquals('total len', 2 + 4 + 5, Int32(Length(F)));
end;

procedure TWebSocketsTests.TestEncodeMaskedKeysDiffer;
var
  F1, F2, K1, K2: string;
begin
  { Two successive frames must use different masking keys (bytes 2..5). }
  F1 := EncodeMaskedTextFrame('x');
  F2 := EncodeMaskedTextFrame('x');
  K1 := Copy(F1, 2, 4);
  K2 := Copy(F2, 2, 4);
  AssertTrue('per-frame keys differ', K1 <> K2);
  { Both must still decode to the same payload. }
  AssertEquals('decode f1', 'x', DecodeFrame(F1).Payload);
  AssertEquals('decode f2', 'x', DecodeFrame(F2).Payload);
end;

procedure TWebSocketsTests.TestEncodeMaskedBinaryOpcode;
var
  F: string;
  D: TWsFrame;
begin
  F := EncodeMaskedFrame(WS_OP_BINARY, 'raw');
  D := DecodeFrame(F);
  AssertTrue('valid', D.Valid);
  AssertEquals('opcode binary', WS_OP_BINARY, D.Opcode);
  AssertEquals('payload', 'raw', D.Payload);
end;

initialization
  RegisterTest(TWebSocketsTests);

end.
