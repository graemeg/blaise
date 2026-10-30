{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - Base64 encoding (RFC 4648).

  Base64 is a general-purpose binary-to-text encoding, not a cryptographic
  primitive, so it lives here under Encoding rather than under Security.  (Java
  places it in java.util.Base64 and .NET in System.Convert, for the same
  reason.)

  Strings are treated as raw bytes in and out.  Output is accumulated through a
  TStringBuilder, so encoding/decoding large inputs is O(n). }

unit Encoding.Base64;

interface

{ Encode the raw bytes of S as standard Base64 (with '=' padding). }
function Base64Encode(const S: string): string;

{ Decode standard Base64 back to raw bytes.  Whitespace in the input is
  ignored; '=' padding is honoured.  Returns the decoded bytes; on a malformed
  character the function stops and returns what it decoded so far. }
function Base64Decode(const S: string): string;

implementation

uses
  StrUtils;

const
  ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
  { ASCII byte constants. NB: Byte('x') on a char *literal* does not yield the
    character code in this dialect (a literal is a UTF-8 string and the cast
    takes the pointer), so byte comparisons use numeric constants. A byte read
    FROM a string via S[i] does give the correct code. }
  CH_EQ    = 61;   { = }
  CH_PLUS  = 43;   { + }
  CH_SLASH = 47;   { / }
  CH_UC_A  = 65;   { A }   CH_UC_Z = 90;
  CH_LC_A  = 97;   { a }   CH_LC_Z = 122;
  CH_0     = 48;          CH_9    = 57;

function Base64Encode(const S: string): string;
var
  SB: TStringBuilder;
  I, N: Int;
  B0, B1, B2, Triple: Int;
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  I := 0;
  while I < N do
  begin
    B0 := Byte(S[I]);
    if I + 1 < N then B1 := Byte(S[I + 1]) else B1 := 0;
    if I + 2 < N then B2 := Byte(S[I + 2]) else B2 := 0;
    Triple := (B0 shl 16) or (B1 shl 8) or B2;

    { ALPHA is 0-based in Blaise, so index directly with the 6-bit groups. }
    SB.AppendByte(Byte(ALPHA[(Triple shr 18) and $3F]));
    SB.AppendByte(Byte(ALPHA[(Triple shr 12) and $3F]));
    if I + 1 < N then
      SB.AppendByte(Byte(ALPHA[(Triple shr 6) and $3F]))
    else
      SB.AppendByte(CH_EQ);
    if I + 2 < N then
      SB.AppendByte(Byte(ALPHA[Triple and $3F]))
    else
      SB.AppendByte(CH_EQ);
    I := I + 3;
  end;
  Result := SB.ToString();
  SB.Free();
end;

{ Map a Base64 character to its 6-bit value, or -1 if not a Base64 char. }
function DecodeChar(B: Byte): Int;
begin
  if (B >= CH_UC_A) and (B <= CH_UC_Z) then Result := B - CH_UC_A
  else if (B >= CH_LC_A) and (B <= CH_LC_Z) then Result := B - CH_LC_A + 26
  else if (B >= CH_0) and (B <= CH_9) then Result := B - CH_0 + 52
  else if B = CH_PLUS then Result := 62
  else if B = CH_SLASH then Result := 63
  else Result := -1;
end;

function Base64Decode(const S: string): string;
var
  SB: TStringBuilder;
  I, N, Val, Bits, Acc: Int;
  B, V: Int;
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  Acc := 0;
  Bits := 0;
  I := 0;
  while I < N do
  begin
    B := Byte(S[I]);
    I := I + 1;
    if B = CH_EQ then
      Break;                 { padding — no more data }
    { skip whitespace }
    if (B = 32) or (B = 9) or (B = 10) or (B = 13) then
      Continue;
    V := DecodeChar(B);
    if V < 0 then
      Break;                 { malformed — stop }
    Acc := (Acc shl 6) or V;
    Bits := Bits + 6;
    if Bits >= 8 then
    begin
      Bits := Bits - 8;
      Val := (Acc shr Bits) and $FF;
      SB.AppendByte(Val);
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

end.
