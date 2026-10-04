{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - WebSocket (RFC 6455) framing and handshake helpers.

  This unit is transport-agnostic: it turns bytes into frames and back, and
  computes the handshake accept key.  It does NOT own a socket — pair it with
  Net.Sockets (or any byte stream) to drive a connection.

    * WebSocketAccept   — the Sec-WebSocket-Accept value for a client key.
    * EncodeTextFrame   — build a server->client text frame (RFC 6455 5.2),
                          unmasked, payloads up to 2^31-1.
    * DecodeFrame       — parse one frame from a buffer, unmasking the payload
                          (client->server frames are always masked).

  Server frames are sent unmasked; client frames must be masked.  DecodeFrame
  handles both.  Continuation/fragmentation is reported via the FIN flag but
  not reassembled here (callers needing message reassembly concatenate the
  payloads of a FIN=False frame followed by opcode-0 continuation frames). }

unit Net.WebSockets;

interface

const
  { RFC 6455 opcodes }
  WS_OP_CONTINUATION = $0;
  WS_OP_TEXT         = $1;
  WS_OP_BINARY       = $2;
  WS_OP_CLOSE        = $8;
  WS_OP_PING         = $9;
  WS_OP_PONG         = $A;

type
  { One decoded frame.  Payload holds the unmasked bytes (as a string). }
  TWsFrame = record
    Valid:   Boolean;   { False if the buffer held no complete frame }
    Fin:     Boolean;   { final fragment of a message }
    Opcode:  Integer;
    Payload: string;
    { Number of bytes consumed from the input buffer for this frame; callers
      streaming a socket advance their buffer by this much. }
    Consumed: Integer;
  end;

{ Compute Sec-WebSocket-Accept for a client's Sec-WebSocket-Key (the value
  echoed back in the 101 handshake response). }
function WebSocketAccept(const AKey: string): string;

{ Build an unmasked text frame carrying APayload (server->client). }
function EncodeTextFrame(const APayload: string): string;

{ Build an unmasked frame with an explicit opcode (e.g. WS_OP_BINARY,
  WS_OP_PING, WS_OP_CLOSE).  Server frames are never masked. }
function EncodeFrame(AOpcode: Integer; const APayload: string): string;

{ Build a MASKED frame with an explicit opcode (client->server).  RFC 6455 5.3
  requires every client frame to be masked: the MASK bit is set, a fresh 4-byte
  masking key is prepended, and the payload is XORed with it.  The key comes
  from the kernel CSPRNG (getrandom) so it varies per frame; the value is only
  used for framing, not confidentiality.  DecodeFrame reverses it. }
function EncodeMaskedFrame(AOpcode: Integer; const APayload: string): string;

{ Build a MASKED text frame (client->server) carrying APayload. }
function EncodeMaskedTextFrame(const APayload: string): string;

{ Parse the first frame in ABuffer.  Returns Valid=False (Consumed=0) if the
  buffer does not yet hold a complete frame — read more bytes and retry. }
function DecodeFrame(const ABuffer: string): TWsFrame;

implementation

uses
  Security.Crypto, Encoding.Base64, StrUtils;

const
  { the RFC 6455 magic GUID appended to the key before hashing }
  WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

{ getrandom(buf, buflen, flags): fill buf with buflen random bytes from the
  kernel CSPRNG.  flags=0 reads from the same pool as /dev/urandom.  Used to
  pick a per-frame masking key.  PORTING BOUNDARY: getrandom(2) is Linux/
  FreeBSD; on other targets dispatch a per-platform CSPRNG here. }
{$IFDEF DARWIN}
{ macOS has no getrandom(2); getentropy(3) draws from the same kernel CSPRNG
  for up to 256 bytes per call (every caller here asks for 16 or fewer).
  Same contract as getrandom: the byte count on success, -1 on failure. }
function c_getentropy(ABuf: Pointer; ALen: Int64): Integer;
  external name 'getentropy';

function c_getrandom(ABuf: Pointer; ALen: Int64; AFlags: Integer): Int64;
begin
  if c_getentropy(ABuf, ALen) = 0 then
    Result := ALen
  else
    Result := -1;
end;
{$ELSE}
function c_getrandom(ABuf: Pointer; ALen: Int64; AFlags: Integer): Int64;
  external name 'getrandom';
{$ENDIF}

{ A monotonically-increasing counter mixed into the masking key so that even if
  getrandom ever short-reads (it should not for 4 bytes), successive frames on a
  connection still get distinct keys. }
var
  GMaskCounter: UInt32 = $9E3779B9;   { golden-ratio seed }

function WebSocketAccept(const AKey: string): string;
begin
  Result := Base64Encode(Sha1(AKey + WS_GUID));
end;

function EncodeFrame(AOpcode: Integer; const APayload: string): string;
var
  SB: TStringBuilder;
  Len: Integer;
begin
  SB := TStringBuilder.Create();
  SB.AppendByte($80 or (AOpcode and $0F));   { FIN + opcode, unmasked }
  Len := Length(APayload);
  if Len < 126 then
    SB.AppendByte(Len)
  else if Len <= 65535 then
  begin
    SB.AppendByte(126);
    SB.AppendByte((Len shr 8) and $FF);
    SB.AppendByte(Len and $FF);
  end
  else
  begin
    { 64-bit length; top 4 bytes are 0 since strings here fit in 2^31-1. }
    SB.AppendByte(127);
    SB.AppendByte(0); SB.AppendByte(0); SB.AppendByte(0); SB.AppendByte(0);
    SB.AppendByte((Len shr 24) and $FF);
    SB.AppendByte((Len shr 16) and $FF);
    SB.AppendByte((Len shr 8) and $FF);
    SB.AppendByte(Len and $FF);
  end;
  SB.Append(APayload);
  Result := SB.ToString();
  SB.Free();
end;

function EncodeTextFrame(const APayload: string): string;
begin
  Result := EncodeFrame(WS_OP_TEXT, APayload);
end;

{ Fill AMask[0..3] with a fresh per-frame masking key.  Draws 4 bytes from the
  kernel CSPRNG and mixes in an advancing counter as a belt-and-braces fallback,
  so the key varies from frame to frame even if getrandom is unavailable. }
procedure NextMaskKey(var AMask: array of Byte);
var
  Buf: array[0..3] of Byte;
  I: Integer;
  Got: Int64;
begin
  Got := c_getrandom(@Buf[0], 4, 0);
  GMaskCounter := (GMaskCounter * 1664525) + 1013904223;   { LCG step }
  if Got <> 4 then
  begin
    { getrandom failed: derive the key entirely from the counter. }
    Buf[0] := Byte(GMaskCounter and $FF);
    Buf[1] := Byte((GMaskCounter shr 8) and $FF);
    Buf[2] := Byte((GMaskCounter shr 16) and $FF);
    Buf[3] := Byte((GMaskCounter shr 24) and $FF);
  end
  else
    { mix the counter into the random bytes so a repeated random draw still
      yields distinct keys across frames }
    Buf[0] := Buf[0] xor Byte(GMaskCounter and $FF);
  for I := 0 to 3 do
    AMask[I] := Buf[I];
end;

function EncodeMaskedFrame(AOpcode: Integer; const APayload: string): string;
var
  SB: TStringBuilder;
  Len, I: Integer;
  Mask: array[0..3] of Byte;
begin
  NextMaskKey(Mask);
  SB := TStringBuilder.Create();
  SB.AppendByte($80 or (AOpcode and $0F));   { FIN + opcode }
  Len := Length(APayload);
  if Len < 126 then
    SB.AppendByte($80 or Len)                 { MASK bit + len }
  else if Len <= 65535 then
  begin
    SB.AppendByte($80 or 126);
    SB.AppendByte((Len shr 8) and $FF);
    SB.AppendByte(Len and $FF);
  end
  else
  begin
    SB.AppendByte($80 or 127);
    SB.AppendByte(0); SB.AppendByte(0); SB.AppendByte(0); SB.AppendByte(0);
    SB.AppendByte((Len shr 24) and $FF);
    SB.AppendByte((Len shr 16) and $FF);
    SB.AppendByte((Len shr 8) and $FF);
    SB.AppendByte(Len and $FF);
  end;
  { the 4-byte masking key }
  for I := 0 to 3 do
    SB.AppendByte(Mask[I]);
  { XOR-masked payload }
  for I := 0 to Len - 1 do
    SB.AppendByte(Byte(APayload[I]) xor Mask[I and 3]);
  Result := SB.ToString();
  SB.Free();
end;

function EncodeMaskedTextFrame(const APayload: string): string;
begin
  Result := EncodeMaskedFrame(WS_OP_TEXT, APayload);
end;

function DecodeFrame(const ABuffer: string): TWsFrame;
var
  N, Pos, I: Integer;
  B0, B1: Byte;
  Masked: Boolean;
  PayLen: Int64;
  Mask: array[0..3] of Byte;
  SB: TStringBuilder;
begin
  Result.Valid := False;
  Result.Consumed := 0;
  Result.Payload := '';

  N := Length(ABuffer);
  if N < 2 then Exit;   { need at least the 2-byte header }

  B0 := Byte(ABuffer[0]);
  B1 := Byte(ABuffer[1]);
  Result.Fin    := (B0 and $80) <> 0;
  Result.Opcode := B0 and $0F;
  Masked := (B1 and $80) <> 0;
  PayLen := B1 and $7F;
  Pos := 2;

  if PayLen = 126 then
  begin
    if N < Pos + 2 then Exit;
    PayLen := (Int64(Byte(ABuffer[Pos])) shl 8) or Int64(Byte(ABuffer[Pos + 1]));
    Pos := Pos + 2;
  end
  else if PayLen = 127 then
  begin
    if N < Pos + 8 then Exit;
    { 64-bit length; we only support the low 31 bits (string length). }
    PayLen := 0;
    for I := 0 to 7 do
      PayLen := (PayLen shl 8) or Int64(Byte(ABuffer[Pos + I]));
    Pos := Pos + 8;
  end;

  if Masked then
  begin
    if N < Pos + 4 then Exit;
    for I := 0 to 3 do
      Mask[I] := Byte(ABuffer[Pos + I]);
    Pos := Pos + 4;
  end;

  if N < Pos + PayLen then Exit;   { payload not fully arrived }

  SB := TStringBuilder.Create();
  for I := 0 to Integer(PayLen) - 1 do
  begin
    if Masked then
      SB.AppendByte(Byte(ABuffer[Pos + I]) xor Mask[I and 3])
    else
      SB.AppendByte(Byte(ABuffer[Pos + I]));
  end;
  Result.Payload := SB.ToString();
  SB.Free();

  Result.Consumed := Pos + Integer(PayLen);
  Result.Valid := True;
end;

end.
