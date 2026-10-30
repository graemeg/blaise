{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  String helpers — 0-based string conventions.

  Blaise strings are 0-based: S[0] is the first character, Pos returns
  a 0-based index (-1 = not found), Copy takes a 0-based From argument.

  Usage:
    - Replace s[1] with StrAt(s, 0)
    - Replace Pos(sub, s) > 0  with Pos(sub, s) >= 0
    - Replace Copy(s, n, len)  with Copy(s, n, len)  (already 0-based in Blaise)
    - Use StrAt(s, i) instead of s[i+1] style char access
}

unit uStrCompat;

interface

{ StrAt: return ordinal of character at 0-based index I }
function StrAt(const S: string; I: Int): Int32;

{ StrCopyFrom: copy from 0-based position From, Count chars }
function StrCopyFrom(const S: string; From, Count: Int): string;

{ StrCopyTail: copy from 0-based position From to end of string }
function StrCopyTail(const S: string; From: Int): string;

{ StrHead: copy the first N characters (equivalent to Copy(s, 0, N)) }
function StrHead(const S: string; N: Int): string;

{ StrPos: find sub in s, return 0-based index; -1 if not found }
function StrPos(const Sub, S: string): Int;

{ StripUnderscores: return S with all '_' characters removed }
function StripUnderscores(const S: string): string;

{ ParseIntLiteral: convert a Pascal integer-literal token value to Int64.
  Accepts decimal, $hex, %binary, &octal, with optional _ separators.
  Raises EConvertError on invalid input or on values that overflow Int64. }
function ParseIntLiteral(const S: string): Int64;

{ Like ParseIntLiteral but tolerant of UInt64-range values.  AValue holds
  the resulting bit pattern (cast to Int64); AIsUInt64 is True when the
  source value exceeded MaxInt64 (i.e. the bit pattern must be interpreted
  as UInt64).  Raises EConvertError on overflow past UInt64. }
procedure ParseIntOrUInt64Literal(const S: string;
  var AValue: Int64; var AIsUInt64: Boolean);

implementation

uses
  SysUtils;   { EConvertError }

function StrAt(const S: string; I: Int): Int32;
begin
  Result := OrdAt(S, I);
end;

function StrCopyFrom(const S: string; From, Count: Int): string;
begin
  Result := Copy(S, From, Count);
end;

function StrCopyTail(const S: string; From: Int): string;
begin
  Result := Copy(S, From, MaxInt);
end;

function StrHead(const S: string; N: Int): string;
begin
  Result := Copy(S, 0, N);
end;

function StrPos(const Sub, S: string): Int;
begin
  Result := Pos(Sub, S);
end;

function StripUnderscores(const S: string): string;
var
  I: Int;
begin
  Result := '';
  for I := 0 to Length(S) - 1 do
    if StrAt(S, I) <> Ord('_') then
      Result := Result + Chr(StrAt(S, I));
end;

procedure ParseIntOrUInt64Literal(const S: string;
  var AValue: Int64; var AIsUInt64: Boolean);
var
  I, Len:    Int;
  Digits:    string;
  C:         Int;
  Prefix:    Int;
  Digit:     Int;
begin
  AValue    := 0;
  AIsUInt64 := False;
  Len := Length(S);
  if Len = 0 then
    raise EConvertError.Create('Empty integer literal');

  Prefix := StrAt(S, 0);

  { Strip underscores from digit portion, validate placement }
  Digits := '';
  if (Prefix = Ord('$')) or (Prefix = Ord('%')) or (Prefix = Ord('&')) then
    I := 1   { skip prefix char }
  else
    I := 0;

  { First digit after prefix must not be underscore }
  if (I < Len) and (StrAt(S, I) = Ord('_')) then
    raise EConvertError.Create('Invalid integer literal: underscore at start of digits in ''' + S + '''');

  while I < Len do
  begin
    C := StrAt(S, I);
    if C <> Ord('_') then
      Digits := Digits + Chr(C);
    { Trailing underscore: this is '_' and next position is end-of-string }
    if (C = Ord('_')) and (I + 1 = Len) then
      raise EConvertError.Create('Invalid integer literal: trailing underscore in ''' + S + '''');
    Inc(I);
  end;

  if Digits = '' then
    raise EConvertError.Create('Invalid integer literal: no digits in ''' + S + '''');

  AValue := 0;
  case Prefix of
    Ord('$'):
      begin
        if Length(Digits) > 16 then
          raise EConvertError.Create('Hexadecimal literal exceeds 64 bits: ''' + S + '''');
        for I := 0 to Length(Digits) - 1 do
        begin
          C := StrAt(Digits, I);
          if (C >= Ord('0')) and (C <= Ord('9')) then
            Digit := C - Ord('0')
          else if (C >= Ord('A')) and (C <= Ord('F')) then
            Digit := C - Ord('A') + 10
          else if (C >= Ord('a')) and (C <= Ord('f')) then
            Digit := C - Ord('a') + 10
          else
            raise EConvertError.Create('Invalid hexadecimal digit in ''' + S + '''');
          AValue := AValue * 16 + Int64(Digit);  { 4-bit shift never overflows when len ≤ 16 }
        end;
      end;
    Ord('%'):
      begin
        if Length(Digits) > 64 then
          raise EConvertError.Create('Binary literal exceeds 64 bits: ''' + S + '''');
        for I := 0 to Length(Digits) - 1 do
        begin
          C := StrAt(Digits, I);
          if (C <> Ord('0')) and (C <> Ord('1')) then
            raise EConvertError.Create('Invalid binary digit in ''' + S + '''');
          AValue := AValue * 2 + Int64(C - Ord('0'));
        end;
      end;
    Ord('&'):
      begin
        for I := 0 to Length(Digits) - 1 do
        begin
          C := StrAt(Digits, I);
          Digit := C - Ord('0');
          if (Digit < 0) or (Digit > 7) then
            raise EConvertError.Create('Invalid octal digit in ''' + S + '''');
          AValue := AValue * 8 + Int64(Digit);
        end;
      end;
  else
    begin
      for I := 0 to Length(Digits) - 1 do
      begin
        C := StrAt(Digits, I);
        Digit := C - Ord('0');
        if (Digit < 0) or (Digit > 9) then
          raise EConvertError.Create('Invalid decimal digit in ''' + S + '''');
        AValue := AValue * 10 + Int64(Digit);
      end;
    end;
  end;

  { When the bit pattern's sign bit is set the unsigned interpretation
    exceeds MaxInt64, so the literal should be treated as UInt64. }
  AIsUInt64 := AValue < 0;
end;

function ParseIntLiteral(const S: string): Int64;
var
  V:   Int64;
  IsU: Boolean;
begin
  ParseIntOrUInt64Literal(S, V, IsU);
  if IsU then
    raise EConvertError.Create('Integer literal exceeds Int64 range: ''' + S + '''');
  Result := V;
end;

end.
