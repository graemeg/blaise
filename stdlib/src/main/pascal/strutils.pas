{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit StrUtils;

// Blaise RTL — StrUtils unit.
//
// String indexing in Blaise is 0-based throughout:
//   - PosEx/Pos return -1 when not found, 0 for the first position.
//   - LeftStr/RightStr/MidStr are thin wrappers over the built-in Copy.
//   - IndexStr/IndexText return -1 when not found, 0 for the first element.
//
// Str vs Text naming convention (identical to Delphi/FPC):
//   xxxStr  — case-sensitive
//   xxxText — case-insensitive (ASCII fold only; no locale)
//
// All higher-level functions are implemented in pure Blaise Pascal using
// only the small set of primitives exposed by blaise_str.pas.

interface

uses
  Generics.Collections;   { TList<String> for the Split/Join helpers }


{ ------------------------------------------------------------------ }
{ Containment                                                          }
{ ------------------------------------------------------------------ }

{ Returns True if Sub appears anywhere in S (case-sensitive). }
function ContainsStr(const S, Sub: string): Boolean;

{ Returns True if Sub appears anywhere in S (case-insensitive). }
function ContainsText(const S, Sub: string): Boolean;

{ ------------------------------------------------------------------ }
{ Prefix / suffix                                                      }
{ ------------------------------------------------------------------ }

{ Returns True if S begins with Prefix (case-sensitive). }
function StartsStr(const Prefix, S: string): Boolean;

{ Returns True if S begins with Prefix (case-insensitive). }
function StartsText(const Prefix, S: string): Boolean;

{ Returns True if S ends with Suffix (case-sensitive). }
function EndsStr(const Suffix, S: string): Boolean;

{ Returns True if S ends with Suffix (case-insensitive). }
function EndsText(const Suffix, S: string): Boolean;

{ ------------------------------------------------------------------ }
{ Extraction — thin wrappers over the built-in Copy                    }
{ ------------------------------------------------------------------ }

{ Returns the first Count bytes of S. }
function LeftStr(const S: string; Count: Int): string;

{ Returns the last Count bytes of S. }
function RightStr(const S: string; Count: Int): string;

{ Returns Count bytes of S starting at 0-based position Start. }
function MidStr(const S: string; Start, Count: Int): string;

{ ------------------------------------------------------------------ }
{ Search                                                               }
{ ------------------------------------------------------------------ }

{ Note: PosEx(Sub, S, StartPos) is a compiler built-in — not declared here. }

{ Returns the 0-based index of Str in Arr (case-sensitive), or -1. }
function IndexStr(const Str: string; const Arr: array of string): Int;

{ Returns the 0-based index of Str in Arr (case-insensitive), or -1. }
function IndexText(const Str: string; const Arr: array of string): Int;

{ ------------------------------------------------------------------ }
{ Replacement                                                          }
{ ------------------------------------------------------------------ }

{ Replaces the FIRST occurrence of OldPattern with NewPattern.  Returns S
  unchanged if OldPattern is empty or not found.  Matching is case-sensitive;
  for a case-insensitive replace, lower-case the inputs as you pass them in. }
function Replace(const S, OldPattern, NewPattern: string): string;

{ Replaces ALL occurrences of OldPattern with NewPattern.  Matching is
  case-sensitive; for a case-insensitive replace, lower-case the inputs as
  you pass them in. }
function ReplaceAll(const S, OldPattern, NewPattern: string): string;

{ ------------------------------------------------------------------ }
{ Manipulation                                                         }
{ ------------------------------------------------------------------ }

{ Returns S repeated Count times. }
function DupeString(const S: string; Count: Int): string;

{ Returns S with its bytes in reverse order. }
function ReverseString(const S: string): string;

{ Deletes Len bytes at 0-based position Start and inserts Replacement. }
function StuffString(const S: string; Start, Len: Int;
                     const Replacement: string): string;

{ Returns S with leading whitespace (bytes <= 32) removed. }
function TrimLeft(const S: string): string;

{ Returns S with trailing whitespace (bytes <= 32) removed. }
function TrimRight(const S: string): string;

{ Returns S left-padded with PadByte to at least Width bytes. }
function PadLeft(const S: string; Width: Int; PadByte: Byte = 32): string;

{ Returns S right-padded with PadByte to at least Width bytes. }
function PadRight(const S: string; Width: Int; PadByte: Byte = 32): string;

{ Returns the number of non-overlapping occurrences of Sub in S. }
function CountOccurrences(const Sub, S: string): Int;

{ Returns S with a leading Prefix removed (if present). }
function RemovePrefix(const S, Prefix: string): string;

{ Returns S with a trailing Suffix removed (if present). }
function RemoveSuffix(const S, Suffix: string): string;

{ Returns True when S contains only whitespace (or is empty). }
function IsEmptyOrWhitespace(const S: string): Boolean;

{ Joins Parts with Sep between each element. }
function JoinStr(const Sep: string; const Parts: array of string): string;

{ Split S on a single delimiter byte, returning the pieces (one more piece
  than there are delimiters; empty pieces are kept).  Caller owns the list. }
function SplitChar(const S: string; ADelim: Byte): TList<String>;

{ Split S into lines on LF, tolerating CRLF (a trailing CR is stripped from
  each line).  Caller owns the list. }
function SplitLines(const S: string): TList<String>;

{ Join the items of AList with ASep between them (the list-valued inverse of
  SplitChar; cf. JoinStr for an open array).  nil yields ''. }
function JoinList(AList: TList<String>; const ASep: string): string;

{ ------------------------------------------------------------------ }
{ UTF-8 Codepoint operations                                           }
{ ------------------------------------------------------------------ }

{ Returns the byte width (1-4) of a UTF-8 sequence given its lead byte.
  For ASCII bytes (0..127) the result is always 1.  For multi-byte
  sequences the lead byte encodes the total length:
    110xxxxx = 2, 1110xxxx = 3, 11110xxx = 4. }
function CodePointSize(LeadByte: Byte): Int;

{ Returns the number of Unicode codepoints in S.  This is an O(n) scan
  over the raw UTF-8 bytes — each non-continuation byte (a byte that
  does NOT match the 10xxxxxx pattern) starts a new codepoint. }
function CodePointLength(const S: string): Int;

{ Extracts Count codepoints starting at codepoint position Index (0-based).
  Returns the corresponding UTF-8 substring.  Both Index and Count are in
  codepoint units, not bytes.  Returns an empty string if Index is beyond
  the end of the string. }
function CodePointCopy(const S: string; Index, Count: Int): string;

{ Returns the Unicode codepoint value (0..U+10FFFF) at codepoint position
  Index (0-based).  This is an O(n) operation because it must scan from
  the beginning of the string to find the Nth codepoint.  Returns -1 if
  Index is out of range. }
function CodePointAt(const S: string; Index: Int): Int;

{ Like Pos() but returns the result as a codepoint index rather than a
  byte index.  Returns -1 if Sub is not found.  Internally calls Pos()
  then counts codepoints up to the byte position. }
function CodePointPos(const Sub, S: string): Int;

{ Converts a codepoint index to a byte index.  Walks the string counting
  codepoints until CPIndex is reached, then returns the corresponding
  byte offset.  Returns -1 if CPIndex is beyond the end of the string. }
function CodePointByteIndex(const S: string; CPIndex: Int): Int;

{ Decodes the UTF-8 codepoint starting at byte position ByteIndex and
  returns its Unicode value (0..U+10FFFF).  This is an O(1) operation —
  it reads 1 to 4 bytes starting at ByteIndex.  No bounds checking is
  performed; the caller must ensure ByteIndex is within range. }
function CodePointFromByteIndex(const S: string; ByteIndex: Int): Int;

{ Encodes a single Unicode codepoint (0..U+10FFFF) as its UTF-8 byte
  sequence and returns it as a 1..4 byte string.  This is the inverse of
  CodePointAt / CodePointFromByteIndex.  It is the codepoint-aware
  replacement for the Char(n) cast found in other Pascal dialects: Chr(n)
  only writes a single raw byte, which is invalid for codepoints above 127,
  whereas CodePointToString emits the correct multi-byte form.  Out-of-range
  values (negative or above U+10FFFF) yield an empty string. }
function CodePointToString(CP: Int): string;

{ ------------------------------------------------------------------ }
{ TStringBuilder — efficient incremental string construction           }
{ ------------------------------------------------------------------ }

{ TStringBuilder avoids the O(N²) cost of repeated string concatenation
  by maintaining a raw byte buffer that grows geometrically.  Append
  operations write directly into the buffer without allocating intermediate
  ARC strings.  Call ToString to obtain a single managed string at the end.

  This mirrors the compiler's internal TIRBuffer that produced the 460×
  speedup in QBE IR generation.  The same technique is now available to
  Blaise user code. }
type
  TStringBuilder = class
  private
    FData: PChar;
    FLen:  Int;
    FCap:  Int;
    procedure Grow(ANeed: Int);
  public
    constructor Create;
    destructor  Destroy; override;
    { Append a string value. }
    procedure Append(const S: string); overload;
    { Append a single byte as a character. }
    procedure AppendByte(B: Byte); overload;
    { Append a newline (#10). }
    procedure AppendLine; overload;
    { Append a string followed by a newline. }
    procedure AppendLine(const S: string); overload;
    { Remove all content without releasing the buffer. }
    procedure Clear;
    { Truncate the content to ALen bytes (no-op when ALen >= Length or
      negative).  Used for roll-back-and-redo emission patterns: mark
      Length, append, then Truncate back to the mark to discard. }
    procedure Truncate(ALen: Int);
    { True when ANeedle occurs in the content at or after byte AFrom.
      Byte-wise scan; empty needle returns False. }
    function ContainsFrom(AFrom: Int; const ANeedle: string): Boolean;
    { Number of (non-overlapping) occurrences of ANeedle at or after
      byte AFrom; 0 for an empty needle. }
    function CountFrom(AFrom: Int; const ANeedle: string): Int;
    { Return the accumulated content as a managed string. }
    function  ToString: string;
    { Current byte length. }
    property  Length: Int read FLen;
  end;

implementation

{ ------------------------------------------------------------------ }
{ External SIMD helpers (runtime assembly)                             }
{ ------------------------------------------------------------------ }

function _Utf8CountCodePoints(Data: Pointer; Len: Int): Int; external name '_Utf8CountCodePoints';

{ ------------------------------------------------------------------ }
{ Internal helpers                                                     }
{ ------------------------------------------------------------------ }

{ ASCII case-fold: returns lowercase byte value. }
function FoldLower(C: Int): Int;
begin
  if (C >= 65) and (C <= 90) then
    Result := C + 32
  else
    Result := C;
end;

{ ------------------------------------------------------------------ }
{ Containment                                                          }
{ ------------------------------------------------------------------ }

function ContainsStr(const S, Sub: string): Boolean;
begin
  Result := Pos(Sub, S) >= 0;
end;

function ContainsText(const S, Sub: string): Boolean;
var
  SL, SubL: string;
begin
  SL   := LowerCase(S);
  SubL := LowerCase(Sub);
  Result := Pos(SubL, SL) >= 0;
end;

{ ------------------------------------------------------------------ }
{ Prefix / suffix                                                      }
{ ------------------------------------------------------------------ }

function StartsStr(const Prefix, S: string): Boolean;
var
  PLen, SLen: Int;
  SP, PP: PChar;
  I: Int;
begin
  PLen := Length(Prefix);
  SLen := Length(S);
  if PLen = 0 then begin Result := True; Exit; end;
  if PLen > SLen then begin Result := False; Exit; end;
  SP := PChar(S);
  PP := PChar(Prefix);
  for I := 0 to PLen - 1 do
    if SP[I] <> PP[I] then begin Result := False; Exit; end;
  Result := True;
end;

function StartsText(const Prefix, S: string): Boolean;
var
  PLen, SLen: Int;
  SP, PP: PChar;
  I: Int;
begin
  PLen := Length(Prefix);
  SLen := Length(S);
  if PLen = 0 then begin Result := True; Exit; end;
  if PLen > SLen then begin Result := False; Exit; end;
  SP := PChar(S);
  PP := PChar(Prefix);
  for I := 0 to PLen - 1 do
    if FoldLower(SP[I]) <> FoldLower(PP[I]) then begin Result := False; Exit; end;
  Result := True;
end;

function EndsStr(const Suffix, S: string): Boolean;
var
  SufLen, SLen: Int;
  SP, SufP: PChar;
  Offset, I: Int;
begin
  SufLen := Length(Suffix);
  SLen   := Length(S);
  if SufLen = 0 then begin Result := True; Exit; end;
  if SufLen > SLen then begin Result := False; Exit; end;
  SP     := PChar(S);
  SufP   := PChar(Suffix);
  Offset := SLen - SufLen;
  for I := 0 to SufLen - 1 do
    if SP[Offset + I] <> SufP[I] then begin Result := False; Exit; end;
  Result := True;
end;

function EndsText(const Suffix, S: string): Boolean;
var
  SufLen, SLen: Int;
  SP, SufP: PChar;
  Offset, I: Int;
begin
  SufLen := Length(Suffix);
  SLen   := Length(S);
  if SufLen = 0 then begin Result := True; Exit; end;
  if SufLen > SLen then begin Result := False; Exit; end;
  SP     := PChar(S);
  SufP   := PChar(Suffix);
  Offset := SLen - SufLen;
  for I := 0 to SufLen - 1 do
    if FoldLower(SP[Offset + I]) <> FoldLower(SufP[I]) then begin Result := False; Exit; end;
  Result := True;
end;

{ ------------------------------------------------------------------ }
{ Extraction                                                           }
{ ------------------------------------------------------------------ }

function LeftStr(const S: string; Count: Int): string;
begin
  Result := Copy(S, 0, Count);
end;

function RightStr(const S: string; Count: Int): string;
var
  Len: Int;
begin
  Len := Length(S);
  if Count >= Len then
    Result := S
  else
    Result := Copy(S, Len - Count, Count);
end;

function MidStr(const S: string; Start, Count: Int): string;
begin
  Result := Copy(S, Start, Count);
end;

{ ------------------------------------------------------------------ }
{ Search                                                               }
{ ------------------------------------------------------------------ }

{ PosEx is a compiler built-in — implementation omitted. }

function IndexStr(const Str: string; const Arr: array of string): Int;
var
  I: Int;
begin
  for I := 0 to High(Arr) do
    if Arr[I] = Str then
    begin
      Exit(I);
    end;
  Result := -1;
end;

function IndexText(const Str: string; const Arr: array of string): Int;
var
  I:   Int;
  SL:  string;
  EL:  string;
begin
  SL := LowerCase(Str);
  for I := 0 to High(Arr) do
  begin
    EL := LowerCase(Arr[I]);
    if EL = SL then
    begin
      Exit(I);
    end;
  end;
  Result := -1;
end;

{ ------------------------------------------------------------------ }
{ Replacement                                                          }
{ ------------------------------------------------------------------ }

{ Internal worker for Replace/ReplaceAll.  Matching is case-sensitive;
  FirstOnly=True stops after the first match (the rest is copied verbatim). }
function DoReplace(const S, OldP, NewP: string; FirstOnly: Boolean): string;
var
  SLen, OldLen, NewLen: Int;
  SB: TStringBuilder;
  I, J: Int;
  Match, Done: Boolean;
  SP, OP: PChar;
begin
  SLen   := Length(S);
  OldLen := Length(OldP);
  NewLen := Length(NewP);
  if (SLen = 0) or (OldLen = 0) then
  begin
    Exit(S);
  end;
  SP := PChar(S);
  OP := PChar(OldP);
  SB := TStringBuilder.Create();
  I    := 0;
  Done := False;
  while (not Done) and (I <= SLen - OldLen) do
  begin
    Match := True;
    for J := 0 to OldLen - 1 do
    begin
      if SP[I + J] <> OP[J] then begin Match := False; Break; end;
    end;
    if Match then
    begin
      if NewLen > 0 then
        SB.Append(NewP);
      I := I + OldLen;
      if FirstOnly then
        Done := True;
    end
    else
    begin
      SB.AppendByte(SP[I]);
      I := I + 1;
    end;
  end;
  { copy any remaining tail }
  while I < SLen do
  begin
    SB.AppendByte(SP[I]);
    I := I + 1;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function Replace(const S, OldPattern, NewPattern: string): string;
begin
  Result := DoReplace(S, OldPattern, NewPattern, True);
end;

function ReplaceAll(const S, OldPattern, NewPattern: string): string;
begin
  Result := DoReplace(S, OldPattern, NewPattern, False);
end;

{ ------------------------------------------------------------------ }
{ Manipulation                                                         }
{ ------------------------------------------------------------------ }

function DupeString(const S: string; Count: Int): string;
var
  SB: TStringBuilder;
  I: Int;
begin
  if (Count <= 0) or (Length(S) = 0) then
  begin
    Exit('');
  end;
  SB := TStringBuilder.Create();
  for I := 1 to Count do
    SB.Append(S);
  Result := SB.ToString();
  SB.Free();
end;

function ReverseString(const S: string): string;
var
  Len, I: Int;
  SP, RP: PChar;
begin
  Len := Length(S);
  SetLength(Result, Len);
  if Len = 0 then Exit;
  SP := PChar(S);
  RP := PChar(Result);
  for I := 0 to Len - 1 do
    RP[I] := SP[Len - 1 - I];
end;

function StuffString(const S: string; Start, Len: Int;
                     const Replacement: string): string;
var
  SLen, RepLen, ActualLen: Int;
begin
  SLen   := Length(S);
  RepLen := Length(Replacement);
  if Start < 0 then Start := 0;
  if Start > SLen then Start := SLen;
  ActualLen := Len;
  if ActualLen < 0 then ActualLen := 0;
  if Start + ActualLen > SLen then ActualLen := SLen - Start;
  { Build: head + replacement + tail }
  Result := Copy(S, 0, Start) + Replacement + Copy(S, Start + ActualLen, SLen - Start - ActualLen);
end;

function TrimLeft(const S: string): string;
var
  Len, Lo: Int;
  SP: PChar;
begin
  Len := Length(S);
  SP  := PChar(S);
  Lo  := 0;
  while Lo < Len do
  begin
    if SP[Lo] > 32 then Break;
    Lo := Lo + 1;
  end;
  Result := Copy(S, Lo, Len - Lo);
end;

function TrimRight(const S: string): string;
var
  Len, Hi: Int;
  SP: PChar;
begin
  Len := Length(S);
  SP  := PChar(S);
  Hi  := Len - 1;
  while Hi >= 0 do
  begin
    if SP[Hi] > 32 then Break;
    Hi := Hi - 1;
  end;
  Result := Copy(S, 0, Hi + 1);
end;

function PadLeft(const S: string; Width: Int; PadByte: Byte): string;
var
  Len, PadCount, I: Int;
  SB: TStringBuilder;
begin
  Len := Length(S);
  if Len >= Width then
  begin
    Exit(S);
  end;
  PadCount := Width - Len;
  SB := TStringBuilder.Create();
  for I := 1 to PadCount do
    SB.AppendByte(PadByte);
  SB.Append(S);
  Result := SB.ToString();
  SB.Free();
end;

function PadRight(const S: string; Width: Int; PadByte: Byte): string;
var
  Len, PadCount, I: Int;
  SB: TStringBuilder;
begin
  Len := Length(S);
  if Len >= Width then
  begin
    Exit(S);
  end;
  PadCount := Width - Len;
  SB := TStringBuilder.Create();
  SB.Append(S);
  for I := 1 to PadCount do
    SB.AppendByte(PadByte);
  Result := SB.ToString();
  SB.Free();
end;

function CountOccurrences(const Sub, S: string): Int;
var
  SLen, SubLen: Int;
  SP, SubP: PChar;
  I, J: Int;
  Match: Boolean;
begin
  Result := 0;
  SLen   := Length(S);
  SubLen := Length(Sub);
  if (SubLen = 0) or (SubLen > SLen) then Exit;
  SP   := PChar(S);
  SubP := PChar(Sub);
  I    := 0;
  while I <= SLen - SubLen do
  begin
    Match := True;
    for J := 0 to SubLen - 1 do
      if SP[I + J] <> SubP[J] then begin Match := False; Break; end;
    if Match then
    begin
      Result := Result + 1;
      I := I + SubLen;
    end
    else
      I := I + 1;
  end;
end;

function RemovePrefix(const S, Prefix: string): string;
var
  PLen: Int;
begin
  if StartsStr(Prefix, S) then
  begin
    PLen   := Length(Prefix);
    Result := Copy(S, PLen, Length(S) - PLen);
  end
  else
    Result := S;
end;

function RemoveSuffix(const S, Suffix: string): string;
var
  SLen, SufLen: Int;
begin
  if EndsStr(Suffix, S) then
  begin
    SLen   := Length(S);
    SufLen := Length(Suffix);
    Result := Copy(S, 0, SLen - SufLen);
  end
  else
    Result := S;
end;

function IsEmptyOrWhitespace(const S: string): Boolean;
var
  Trimmed: string;
begin
  Trimmed := TrimLeft(S);
  Result  := Length(Trimmed) = 0;
end;

function JoinStr(const Sep: string; const Parts: array of string): string;
var
  SB: TStringBuilder;
  I:  Int;
begin
  if High(Parts) < 0 then
  begin
    Exit('');
  end;
  SB := TStringBuilder.Create();
  for I := 0 to High(Parts) do
  begin
    SB.Append(Parts[I]);
    if I < High(Parts) then
      SB.Append(Sep);
  end;
  Result := SB.ToString();
  SB.Free();
end;

function SplitChar(const S: string; ADelim: Byte): TList<String>;
var
  I, N, Start: Int;
begin
  Result := TList<String>.Create();
  N := Length(S);
  Start := 0;
  I := 0;
  while I < N do
  begin
    if Byte(S[I]) = ADelim then
    begin
      Result.Add(Copy(S, Start, I - Start));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  Result.Add(Copy(S, Start, N - Start));
end;

{ Copy S[AStart..AEnd) as a line, dropping one trailing CR so a CRLF line
  yields the bare text. }
function LineSlice(const S: string; AStart, AEnd: Int): string;
begin
  if (AEnd > AStart) and (Byte(S[AEnd - 1]) = 13) then   { trailing CR }
    Result := Copy(S, AStart, AEnd - AStart - 1)
  else
    Result := Copy(S, AStart, AEnd - AStart);
end;

function SplitLines(const S: string): TList<String>;
var
  I, N, Start: Int;
begin
  Result := TList<String>.Create();
  N := Length(S);
  Start := 0;
  I := 0;
  while I < N do
  begin
    if Byte(S[I]) = 10 then   { LF }
    begin
      Result.Add(LineSlice(S, Start, I));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  Result.Add(LineSlice(S, Start, N));
end;

function JoinList(AList: TList<String>; const ASep: string): string;
var
  SB: TStringBuilder;
  I: Int;
begin
  if AList = nil then
    Exit('');
  SB := TStringBuilder.Create();
  for I := 0 to AList.Count - 1 do
  begin
    if I > 0 then
      SB.Append(ASep);
    SB.Append(AList.Get(I));
  end;
  Result := SB.ToString();
  SB.Free();
end;

{ ------------------------------------------------------------------ }
{ TStringBuilder                                                       }
{ ------------------------------------------------------------------ }

constructor TStringBuilder.Create;
begin
  inherited Create();
  Self.FCap  := 256;
  Self.FLen  := 0;
  Self.FData := GetMem(Self.FCap);
end;

destructor TStringBuilder.Destroy;
begin
  FreeMem(Self.FData);
  inherited Destroy();
end;

procedure TStringBuilder.Grow(ANeed: Int);
var
  NewCap:  Int;
  NewData: PChar;
  OldData: PChar;
  I:       Int;
begin
  NewCap  := Self.FCap;
  while NewCap < Self.FLen + ANeed do
    NewCap := NewCap * 2;
  NewData := GetMem(NewCap);
  OldData := Self.FData;
  for I := 0 to Self.FLen - 1 do
    NewData[I] := OldData[I];
  FreeMem(OldData);
  Self.FData := NewData;
  Self.FCap  := NewCap;
end;

procedure TStringBuilder.Append(const S: string);
var
  SLen:   Int;
  SP:     PChar;
  DP:     PChar;
  Offset: Int;
  I:      Int;
begin
  SLen := Length(S);
  if SLen = 0 then Exit;
  if Self.FLen + SLen > Self.FCap then Self.Grow(SLen);
  SP     := PChar(S);
  DP     := Self.FData;
  Offset := Self.FLen;
  for I := 0 to SLen - 1 do
    DP[Offset + I] := SP[I];
  Self.FLen := Self.FLen + SLen;
end;

procedure TStringBuilder.AppendByte(B: Byte);
var
  DP:  PChar;
  Pos: Int;
begin
  if Self.FLen + 1 > Self.FCap then Self.Grow(1);
  DP  := Self.FData;
  Pos := Self.FLen;
  DP[Pos] := B;
  Self.FLen := Self.FLen + 1;
end;

procedure TStringBuilder.AppendLine;
begin
  Self.AppendByte(10);
end;

procedure TStringBuilder.AppendLine(const S: string);
begin
  Self.Append(S);
  Self.AppendByte(10);
end;

procedure TStringBuilder.Clear;
begin
  Self.FLen := 0;
end;

procedure TStringBuilder.Truncate(ALen: Int);
begin
  if (ALen >= 0) and (ALen < Self.FLen) then
    Self.FLen := ALen;
end;

function TStringBuilder.CountFrom(AFrom: Int; const ANeedle: string): Int;
var
  NLen, I, J: Int;
  NP, DP: PChar;
begin
  Result := 0;
  NLen := Length(ANeedle);
  if NLen = 0 then Exit;
  if AFrom < 0 then AFrom := 0;
  NP := PChar(ANeedle);
  DP := Self.FData;
  I := AFrom;
  while I <= Self.FLen - NLen do
  begin
    J := 0;
    while (J < NLen) and (DP[I + J] = NP[J]) do
      J := J + 1;
    if J = NLen then
    begin
      Result := Result + 1;
      I := I + NLen;
    end
    else
      I := I + 1;
  end;
end;

function TStringBuilder.ContainsFrom(AFrom: Int; const ANeedle: string): Boolean;
var
  NLen, I, J: Int;
  NP, DP: PChar;
begin
  Result := False;
  NLen := Length(ANeedle);
  if NLen = 0 then Exit;
  if AFrom < 0 then AFrom := 0;
  NP := PChar(ANeedle);
  DP := Self.FData;
  I := AFrom;
  while I <= Self.FLen - NLen do
  begin
    J := 0;
    while (J < NLen) and (DP[I + J] = NP[J]) do
      J := J + 1;
    if J = NLen then
    begin
      Result := True;
      Exit;
    end;
    I := I + 1;
  end;
end;

function TStringBuilder.ToString: string;
var
  I:  Int;
  RP: PChar;
  SP: PChar;
begin
  SetLength(Result, Self.FLen);
  if Self.FLen > 0 then
  begin
    RP := PChar(Result);
    SP := Self.FData;
    for I := 0 to Self.FLen - 1 do
      RP[I] := SP[I];
  end;
end;

{ ------------------------------------------------------------------ }
{ UTF-8 Codepoint operations                                           }
{ ------------------------------------------------------------------ }

function CodePointSize(LeadByte: Byte): Int;
begin
  if LeadByte < 128 then
    Result := 1
  else if (LeadByte and $E0) = $C0 then
    Result := 2
  else if (LeadByte and $F0) = $E0 then
    Result := 3
  else
    Result := 4;
end;

function CodePointLength(const S: string): Int;
begin
  if Length(S) = 0 then
    Result := 0
  else
    Result := _Utf8CountCodePoints(PChar(S), Length(S));
end;

function CodePointByteIndex(const S: string; CPIndex: Int): Int;
var
  P: PChar;
  Len, Idx, Count: Int;
begin
  Len := Length(S);
  if CPIndex < 0 then
  begin
    Result := -1;
    Exit;
  end;
  P := PChar(S);
  Idx := 0;
  Count := 0;
  while (Idx < Len) and (Count < CPIndex) do
  begin
    Idx := Idx + CodePointSize(P[Idx]);
    Inc(Count);
  end;
  if Count = CPIndex then
    Result := Idx
  else
    Result := -1;
end;

function CodePointFromByteIndex(const S: string; ByteIndex: Int): Int;
var
  P: PChar;
  B0, B1, B2, B3: Int;
begin
  P := PChar(S);
  B0 := P[ByteIndex];
  if B0 < 128 then
    Result := B0
  else if (B0 and $E0) = $C0 then
  begin
    B1 := P[ByteIndex + 1] and $3F;
    Result := ((B0 and $1F) shl 6) or B1;
  end
  else if (B0 and $F0) = $E0 then
  begin
    B1 := P[ByteIndex + 1] and $3F;
    B2 := P[ByteIndex + 2] and $3F;
    Result := ((B0 and $0F) shl 12) or (B1 shl 6) or B2;
  end
  else
  begin
    B1 := P[ByteIndex + 1] and $3F;
    B2 := P[ByteIndex + 2] and $3F;
    B3 := P[ByteIndex + 3] and $3F;
    Result := ((B0 and $07) shl 18) or (B1 shl 12) or (B2 shl 6) or B3;
  end;
end;

function CodePointAt(const S: string; Index: Int): Int;
var
  ByteIdx: Int;
begin
  ByteIdx := CodePointByteIndex(S, Index);
  if ByteIdx < 0 then
    Result := -1
  else
    Result := CodePointFromByteIndex(S, ByteIdx);
end;

function CodePointCopy(const S: string; Index, Count: Int): string;
var
  P: PChar;
  Len, StartByte, EndByte, I: Int;
begin
  Len := Length(S);
  if (Len = 0) or (Count <= 0) then
  begin
    Result := '';
    Exit;
  end;
  StartByte := CodePointByteIndex(S, Index);
  if StartByte < 0 then
  begin
    Result := '';
    Exit;
  end;
  P := PChar(S);
  EndByte := StartByte;
  I := 0;
  while (EndByte < Len) and (I < Count) do
  begin
    EndByte := EndByte + CodePointSize(P[EndByte]);
    Inc(I);
  end;
  Result := Copy(S, StartByte, EndByte - StartByte);
end;

function CodePointPos(const Sub, S: string): Int;
var
  ByteIdx: Int;
  P: PChar;
  Len, Idx, Count: Int;
begin
  ByteIdx := Pos(Sub, S);
  if ByteIdx < 0 then
  begin
    Result := -1;
    Exit;
  end;
  P := PChar(S);
  Len := Length(S);
  Idx := 0;
  Count := 0;
  while Idx < ByteIdx do
  begin
    Idx := Idx + CodePointSize(P[Idx]);
    Inc(Count);
  end;
  Result := Count;
end;

function CodePointToString(CP: Int): string;
begin
  if (CP < 0) or (CP > $10FFFF) then
    Result := ''
  else if CP < $80 then
    Result := Chr(CP)
  else if CP < $800 then
    Result := Chr($C0 or (CP shr 6)) +
              Chr($80 or (CP and $3F))
  else if CP < $10000 then
    Result := Chr($E0 or (CP shr 12)) +
              Chr($80 or ((CP shr 6) and $3F)) +
              Chr($80 or (CP and $3F))
  else
    Result := Chr($F0 or (CP shr 18)) +
              Chr($80 or ((CP shr 12) and $3F)) +
              Chr($80 or ((CP shr 6) and $3F)) +
              Chr($80 or (CP and $3F));
end;

end.
