{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — string operation functions (Pascal port of blaise_str.c)

  String memory layout — data-pointer convention:

    Allocation:
      +--[4 bytes]--+--[4 bytes]--+--[4 bytes]--+--[N bytes]--+--[1 byte]--+
      | RefCount    | Length      | Capacity    | UTF-8 data  | NUL        |
      +-------------+-------------+-------------+-------------+------------+
      ^--- base (raw malloc result)             ^--- DATA POINTER (stored in var)

  The variable slot holds the DATA POINTER (pointing at the first character
  byte).  The 12-byte header lives immediately before it at negative offsets:

      data_ptr − 12  RefCount  (Integer, 4 bytes)
      data_ptr −  8  Length    (Integer, 4 bytes)
      data_ptr −  4  Capacity  (Integer, 4 bytes)
      data_ptr +  0  char data (Length bytes + NUL terminator)

  nil represents an empty / unassigned string.
  RefCount = -1 marks immortal (statically-allocated string literals).
}

unit runtime.str;

interface

{ ------------------------------------------------------------------ }
{ Libc bindings                                                        }
{ ------------------------------------------------------------------ }
procedure _libc_memcpy(Dst, Src: Pointer; N: Int64);                   external name 'memcpy';

{ blaise_mem bindings — link directly by symbol name.  We avoid
  'uses blaise_mem' because that would pull blaise_mem's implementation-
  section _libc_memcpy declaration into our namespace and conflict with
  the one above. }
function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);          external name '_BlaiseFreeMem';
function  _BlaiseReallocMem(Ptr: Pointer; NewSize: Integer): Pointer;
  external name '_BlaiseReallocMem';

{ ARC primitive from blaise_arc — used by _StringUnique to drop the old
  reference when copy-on-write replaces a shared/immortal string. }
procedure _StringRelease(Ptr: Pointer);                external name '_StringRelease';
{ ... and the dynamic-array release, which runs the element hook on the last
  reference (SetLength drops a shared array's reference through it). }
procedure _DynArrayRelease(Ptr: Pointer);              external name '_DynArrayRelease';

{ blaise_float binding — used by Format()'s %f/%e/%g handling. }
function  _FormatFloatSpec(V: Double; Spec: Integer; Prec: Integer): Pointer;
  external name '_FormatFloatSpec';

{ ------------------------------------------------------------------ }
{ String RTL public interface                                          }
{ ------------------------------------------------------------------ }
function  _StringLength(S: Pointer): Integer;
function  _StringPos(Sub, S: Pointer): Integer;
function  _StringPosEx(Sub, S: Pointer; StartPos: Integer): Integer;
function  _StringCopy(S: Pointer; From, Count: Integer): Pointer;
function  _StringUnique(S: Pointer): Pointer;
function  _StringDelete(S: Pointer; Idx, Count: Integer): Pointer;
function  _StringSetLength(S: Pointer; N: Integer): Pointer;
function  _StringUpperCase(S: Pointer): Pointer;
function  _StringLowerCase(S: Pointer): Pointer;
function  _StringTrim(S: Pointer): Pointer;
function  _StringSameText(S1, S2: Pointer): Integer;
function  _IntToStr(N: Integer): Pointer;
function  _Int64ToStr(N: Int64): Pointer;
function  _UInt64ToStr(N: UInt64): Pointer;
function  _StrToInt(S: Pointer): Integer;
function  _StrToInt64(S: Pointer): Int64;
function  _OrdAt(S: Pointer; I: Integer): Integer;
function  _Chr(N: Integer): Pointer;
function  _UpCase(N: Integer): Pointer;
function  _StringCompare(S1, S2: Pointer): Integer;
function  _StringCompareText(S1, S2: Pointer): Integer;
function  _StringFromPChar(P: PChar): Pointer;

{ ------------------------------------------------------------------ }
{ UTF-8 codepoint decoding                                             }
{ ------------------------------------------------------------------ }

{ Decode one UTF-8 codepoint at byte position Idx in string S.
  Returns a packed Int64: low 21 bits = codepoint value (0..U+10FFFF),
  bits 32..33 = byte count consumed (1..4).
  Caller extracts: CodePoint = Result and $1FFFFF; Advance = Result shr 32. }
function _Utf8DecodeAt(S: Pointer; Idx: Integer): Int64;

{ ------------------------------------------------------------------ }
{ Dynamic array RTL                                                    }
{ ------------------------------------------------------------------ }

{ Dynamic array memory layout — data-pointer convention:
    [refcount:4][length:4][element 0][element 1]...
  The variable slot holds the DATA POINTER (element 0 address).
  nil represents an empty / unassigned array.
  Refcount = -1 marks immortal (statically-allocated).

  _DynArraySetLengthM(OldPtr, NewLen, ElemSize, Hook) → new data pointer;
  Hook retains / releases managed elements (nil for unmanaged ones).
  _DynArraySetLength(OldPtr, NewLen, ElemSize) → the same with no hook of
  its own (the old block's is kept) -- the entry older compilers call.
  _DynArrayLength(Ptr) → length (0 for nil).
  Refcount helpers (_DynArrayAddRef / _DynArrayRelease) and the element
  hooks live in runtime.arc alongside the other ARC primitives. }
function _DynArraySetLengthM(Ptr: Pointer; NewLen, ElemSize: Integer;
  Hook: Pointer): Pointer;
function _DynArraySetLength(Ptr: Pointer; NewLen, ElemSize: Integer): Pointer;
function _DynArrayLength(Ptr: Pointer): Integer;

{ File-path manipulation — pure string operations, no OS calls }
function _ChangeFileExt(Path, Ext: Pointer): Pointer;
function _ExtractFileName(Path: Pointer): Pointer;
function _ExtractFilePath(Path: Pointer): Pointer;
function _ExtractFileDir(Path: Pointer): Pointer;
function _ExtractFileExt(Path: Pointer): Pointer;
function _IncludeTrailingPathDelimiter(Path: Pointer): Pointer;
function _ExcludeTrailingPathDelimiter(Path: Pointer): Pointer;

{ _StringFormatN — pure Pascal Format implementation.
  Args points to an array of 16-byte records: [Tag:Int64, Value:Int64].
    Tag=0 → integer (Value is the int).
    Tag=1 → string  (Value is the data pointer).
    Tag=2 → float   (Value is the IEEE-754 binary64 bit pattern).
  Specifier syntax: %[-][width][.prec]<conv>
    -      left-justify within the field width (default: right-justify).
    width  minimum field width; the rendered value is space-padded to it.
    .prec  precision — fraction digits for %f/%e, significant digits for %g.
  Conversions: d (integer), s (string), f/F/e/E/g/G (float), %% (literal %). }
function _StringFormatN(Fmt: Pointer; Args: Pointer; Count: Integer): Pointer;

{ _StringFormatVarRecs — Format() over a FORWARDED 'array of const' parameter
  (BUG-047).  VarRecs points to Count real 16-byte TVarRecs ([VType:Byte@0,
  VValue:Pointer@8], vt* discriminants).  This translates them into the
  reduced [Tag:Int64, Value:Int64] block _StringFormatN consumes (Tag 0=int,
  1=string/ptr, 2=raw binary64 bits) and calls it.  The temporary block is
  freed before return — no leak.  Used when the Format argument is a plain
  open-array reference rather than a bracket literal (the literal case boxes
  directly at the call site). }
function _StringFormatVarRecs(Fmt: Pointer; VarRecs: Pointer;
  Count: Integer): Pointer;

implementation

const
  HDR_SIZE = 12;  { 3 x 4-byte integers: RefCount, Length, Capacity }

{ ------------------------------------------------------------------ }
{ Memory helpers                                                        }
{ ------------------------------------------------------------------ }

procedure MemCopy(Dst, Src: Pointer; N: Integer);
begin
  if N > 0 then
    _libc_memcpy(Dst, Src, N);
end;

{ ------------------------------------------------------------------ }
{ Internal helpers                                                     }
{ ------------------------------------------------------------------ }

{ StrLen: Ptr is the DATA pointer; length lives at Ptr-8 }
function StrLen(Ptr: Pointer): Integer;
var
  P: ^Integer;
begin
  if Ptr = nil then
    Result := 0
  else
  begin
    P := Ptr - 8;   { Length field at data_ptr − 8 }
    Result := P^;
  end;
end;

{ StrData: data IS the pointer — identity for data-pointer convention }
function StrData(Ptr: Pointer): PChar;
begin
  Result := PChar(Ptr);
end;

{ Allocate a new Blaise string of exactly Len bytes plus NUL.
  RefCount = 0 (unowned); caller must call _StringAddRef.
  Returns DATA POINTER (= base + HDR_SIZE). }
function StrAlloc(Len: Integer): Pointer;
var
  TotalL: Int64;
  Base:   Pointer;
  RC, LN, CP: ^Integer;
  NulPtr: PChar;
begin
  TotalL := Int64(HDR_SIZE) + Int64(Len) + 1;
  Base   := _BlaiseGetMem(Integer(TotalL));
  if Base = nil then
  begin
    Exit(nil);
  end;
  RC  := Base;        { RefCount at base+0 }
  RC^ := 0;
  LN  := Base + 4;    { Length at base+4 }
  LN^ := Len;
  CP  := Base + 8;    { Capacity at base+8 }
  CP^ := Len;
  Result := Base + HDR_SIZE;   { DATA POINTER }
  NulPtr        := PChar(Result);
  NulPtr[Len]   := 0;          { NUL terminator at data+Len }
end;

{ ------------------------------------------------------------------ }
{ _StringLength                                                        }
{ ------------------------------------------------------------------ }

function _StringLength(S: Pointer): Integer;
begin
  Result := StrLen(S);
end;

{ ------------------------------------------------------------------ }
{ _StringPos(Sub, S) : Integer  — 0-based; -1 if not found           }
{ ------------------------------------------------------------------ }

function _StringPos(Sub, S: Pointer): Integer;
var
  SLen, SubLen: Integer;
  SData, SubData: PChar;
  I, J: Integer;
  Match: Boolean;
begin
  SLen   := StrLen(S);
  SubLen := StrLen(Sub);
  if SubLen = 0 then
  begin
    Exit(0);
  end;
  if SubLen > SLen then
  begin
    Exit(-1);
  end;
  SData   := StrData(S);
  SubData := StrData(Sub);
  I := 0;
  while I <= SLen - SubLen do
  begin
    Match := True;
    J := 0;
    while J < SubLen do
    begin
      if SData[I + J] <> SubData[J] then
      begin
        Match := False;
        Break;
      end;
      Inc(J);
    end;
    if Match then
    begin
      Exit(I);
    end;
    Inc(I);
  end;
  Result := -1;
end;

{ ------------------------------------------------------------------ }
{ _StringPosEx(Sub, S, StartPos) — like _StringPos but starts from   }
{ the given 0-based position.  Returns -1 if not found.              }
{ ------------------------------------------------------------------ }

function _StringPosEx(Sub, S: Pointer; StartPos: Integer): Integer;
var
  SLen, SubLen: Integer;
  SData, SubData: PChar;
  I, J: Integer;
  Match: Boolean;
begin
  SLen   := StrLen(S);
  SubLen := StrLen(Sub);
  if SubLen = 0 then
  begin
    Exit(0);
  end;
  if (SubLen > SLen) or (StartPos >= SLen) then
  begin
    Exit(-1);
  end;
  SData   := StrData(S);
  SubData := StrData(Sub);
  if StartPos < 0 then StartPos := 0;
  I := StartPos;
  while I <= SLen - SubLen do
  begin
    Match := True;
    J := 0;
    while J < SubLen do
    begin
      if SData[I + J] <> SubData[J] then
      begin
        Match := False;
        Break;
      end;
      Inc(J);
    end;
    if Match then
    begin
      Exit(I);
    end;
    Inc(I);
  end;
  Result := -1;
end;

{ ------------------------------------------------------------------ }
{ _StringCopy(S, From, Count) : string  — 0-based From               }
{ ------------------------------------------------------------------ }

function _StringCopy(S: Pointer; From, Count: Integer): Pointer;
var
  SLen:  Integer;
  Data:  PChar;
begin
  SLen := StrLen(S);
  if From < 0 then From := 0;
  if From >= SLen then
  begin
    Exit(StrAlloc(0));
  end;
  { Avoid signed overflow when Count is large (Copy(S, N, MaxInt) idiom) —
    compare Count against (SLen - From) instead of (From + Count) > SLen. }
  if (Count < 0) or (Count > SLen - From) then
    Count := SLen - From;
  Result := StrAlloc(Count);
  if (Result <> nil) and (Count > 0) then
  begin
    Data := StrData(S);
    MemCopy(StrData(Result), Data + From, Count);
  end;
end;

{ ------------------------------------------------------------------ }
{ _StringUnique(S) : string                                           }
{                                                                      }
{ Copy-on-write for in-place mutation (S[I] := ch).  Returns a string  }
{ the caller can write into safely, and which the caller's slot owns    }
{ with exactly one reference:                                          }
{   * S = nil                  → nil (the caller's index store faults,  }
{                                 same as any nil deref — not our bug). }
{   * RefCount = 1 (unique)    → S unchanged; already mutable & owned.  }
{   * RefCount = -1 (immortal) → fresh rc=1 heap copy.  Literals live   }
{     or RefCount > 1 (shared)   in read-only memory / are shared, so   }
{                                a mutation must not touch them.        }
{ When a copy is made the old S is released, so the slot that stores    }
{ the result still holds exactly one reference (no leak, no UAF).      }
{ Matches Delphi/FPC UniqueString semantics.                          }
{ ------------------------------------------------------------------ }

function _StringUnique(S: Pointer): Pointer;
var
  RC:   ^Integer;
  SLen: Integer;
begin
  if S = nil then Exit(nil);
  RC := Pointer(S) - HDR_SIZE;      { RefCount at data_ptr - 12 }
  if RC^ = 1 then Exit(S);          { already uniquely owned & mutable }

  { Immortal (-1) or shared (>1): make a private, writable rc=1 copy. }
  SLen   := StrLen(S);
  Result := StrAlloc(SLen);
  if (Result <> nil) and (SLen > 0) then
    MemCopy(StrData(Result), StrData(S), SLen);
  RC := Pointer(Result) - HDR_SIZE;
  RC^ := 1;                         { the caller's slot owns this ref }
  _StringRelease(S);                { drop the old reference }
end;

{ ------------------------------------------------------------------ }
{ _StringDelete(S, Idx, Count) : string                                }
{                                                                      }
{ Returns a new string with Count characters removed starting at Idx   }
{ (0-based).  Out-of-range Idx or non-positive Count returns a copy of }
{ the input.  Caller owns the returned string (RefCount = 0); callers  }
{ that overwrite a var-string slot must release the old value first    }
{ and addref the result, exactly as for _StringCopy.                   }
{ ------------------------------------------------------------------ }

function _StringDelete(S: Pointer; Idx, Count: Integer): Pointer;
var
  SLen, RemoveCount, NewLen: Integer;
  Data, ResData: PChar;
begin
  SLen := StrLen(S);
  if (Idx < 0) or (Idx >= SLen) or (Count <= 0) then
  begin
    Result := StrAlloc(SLen);
    if (Result <> nil) and (SLen > 0) then
      MemCopy(StrData(Result), StrData(S), SLen);
    Exit;
  end;
  RemoveCount := Count;
  if Idx + RemoveCount > SLen then
    RemoveCount := SLen - Idx;
  NewLen := SLen - RemoveCount;
  Result := StrAlloc(NewLen);
  if Result = nil then Exit;
  Data    := StrData(S);
  ResData := StrData(Result);
  if Idx > 0 then
    MemCopy(ResData, Data, Idx);
  if NewLen - Idx > 0 then
    MemCopy(ResData + Idx, Data + Idx + RemoveCount, NewLen - Idx);
end;

{ ------------------------------------------------------------------ }
{ _StringSetLength(S, N) : string                                      }
{                                                                      }
{ Returns a new string of length N.  Truncates if N <= old length;     }
{ pads with NUL bytes if N is larger.  Caller owns the result.         }
{ ------------------------------------------------------------------ }

function _StringSetLength(S: Pointer; N: Integer): Pointer;
var
  OldLen, CopyLen, I: Integer;
  Data, ResData:      PChar;
begin
  if N < 0 then N := 0;
  Result := StrAlloc(N);
  if (Result = nil) or (N = 0) then Exit;
  if S = nil then OldLen := 0 else OldLen := StrLen(S);
  if OldLen < N then CopyLen := OldLen else CopyLen := N;
  ResData := StrData(Result);
  if CopyLen > 0 then
  begin
    Data := StrData(S);
    MemCopy(ResData, Data, CopyLen);
  end;
  for I := CopyLen to N - 1 do
    ResData[I] := #0;
end;

{ ------------------------------------------------------------------ }
{ _StringUpperCase                                                     }
{ ------------------------------------------------------------------ }

function _StringUpperCase(S: Pointer): Pointer;
var
  Len:     Integer;
  SrcData: PChar;
  DstData: PChar;
  I, C:    Integer;
begin
  Len    := StrLen(S);
  Result := StrAlloc(Len);
  if Result = nil then Exit;
  SrcData := StrData(S);
  DstData := StrData(Result);
  for I := 0 to Len - 1 do
  begin
    C := SrcData[I];
    if (C >= 97) and (C <= 122) then
      DstData[I] := C - 32
    else
      DstData[I] := C;
  end;
end;

{ ------------------------------------------------------------------ }
{ _StringLowerCase                                                     }
{ ------------------------------------------------------------------ }

function _StringLowerCase(S: Pointer): Pointer;
var
  Len:     Integer;
  SrcData: PChar;
  DstData: PChar;
  I, C:    Integer;
begin
  Len    := StrLen(S);
  Result := StrAlloc(Len);
  if Result = nil then Exit;
  SrcData := StrData(S);
  DstData := StrData(Result);
  for I := 0 to Len - 1 do
  begin
    C := SrcData[I];
    if (C >= 65) and (C <= 90) then
      DstData[I] := C + 32
    else
      DstData[I] := C;
  end;
end;

{ ------------------------------------------------------------------ }
{ _StringTrim                                                          }
{ ------------------------------------------------------------------ }

function _StringTrim(S: Pointer): Pointer;
var
  Len:    Integer;
  Data:   PChar;
  Lo, Hi: Integer;
  NewLen: Integer;
begin
  Len  := StrLen(S);
  Data := StrData(S);
  Lo := 0;
  while Lo < Len do
  begin
    if Data[Lo] > 32 then Break;
    Inc(Lo);
  end;
  Hi := Len - 1;
  while Hi >= Lo do
  begin
    if Data[Hi] > 32 then Break;
    Dec(Hi);
  end;
  if Hi >= Lo then
    NewLen := Hi - Lo + 1
  else
    NewLen := 0;
  Result := StrAlloc(NewLen);
  if (Result = nil) or (NewLen = 0) then Exit;
  MemCopy(StrData(Result), Data + Lo, NewLen);
end;

{ ------------------------------------------------------------------ }
{ _StringSameText                                                      }
{ ------------------------------------------------------------------ }

function _StringSameText(S1, S2: Pointer): Integer;
var
  Len1, Len2, I: Integer;
  D1, D2:        PChar;
  C1, C2:        Integer;
begin
  Len1 := StrLen(S1);
  Len2 := StrLen(S2);
  if Len1 <> Len2 then
  begin
    Exit(0);
  end;
  D1 := StrData(S1);
  D2 := StrData(S2);
  for I := 0 to Len1 - 1 do
  begin
    C1 := D1[I];
    C2 := D2[I];
    if (C1 >= 65) and (C1 <= 90) then C1 := C1 + 32;
    if (C2 >= 65) and (C2 <= 90) then C2 := C2 + 32;
    if C1 <> C2 then
    begin
      Exit(0);
    end;
  end;
  Result := 1;
end;

{ ------------------------------------------------------------------ }
{ WriteDecimal — write N as decimal digits into Buf (no NUL).        }
{ Buf must have at least 21 bytes.  Returns character count.         }
{ ------------------------------------------------------------------ }

function WriteDecimal(N: Int64; Buf: PChar): Integer;
var
  IsNeg: Boolean;
  NegN:  Int64;
  Pos:   Integer;
  Tmp:   array[0..21] of Byte;   { stack scratch — this is the hottest
                                   integer-to-text path; no heap traffic }
  TP:    PChar;
  I, J:  Integer;
  Digit: Integer;
begin
  TP  := PChar(@Tmp[0]);
  IsNeg := N < 0;
  { Extract digits working on the negative magnitude.  The two's-complement
    negative range reaches Low(Int64) = -9223372036854775808, whereas its
    positive counterpart does not exist — negating first would overflow and
    leave the value negative, printing only the sign.  Keeping the value
    negative and negating each remainder avoids that. }
  if IsNeg then
    NegN := N
  else
    NegN := -N;
  if NegN = 0 then
  begin
    TP[0] := 48;  { '0' }
    Pos   := 1;
  end
  else
  begin
    Pos := 0;
    while NegN < 0 do
    begin
      Digit  := -Integer(NegN mod 10);
      TP[Pos] := 48 + Digit;
      NegN   := NegN div 10;
      Inc(Pos);
    end;
  end;
  I := 0;
  if IsNeg then
  begin
    Buf[0] := 45;  { '-' }
    I := 1;
  end;
  J := Pos - 1;
  while J >= 0 do
  begin
    Buf[I] := TP[J];
    Inc(I);
    Dec(J);
  end;
  Result := I;
end;

{ ------------------------------------------------------------------ }
{ _IntToStr                                                            }
{ ------------------------------------------------------------------ }

function _IntToStr(N: Integer): Pointer;
var
  Buf:     array[0..21] of Byte;
  BP:      PChar;
  Written: Integer;
begin
  BP      := PChar(@Buf[0]);
  Written := WriteDecimal(Int64(N), BP);
  Result  := StrAlloc(Written);
  if (Result <> nil) and (Written > 0) then
    MemCopy(StrData(Result), Pointer(BP), Written);
end;

{ ------------------------------------------------------------------ }
{ _Int64ToStr                                                          }
{ ------------------------------------------------------------------ }

function _Int64ToStr(N: Int64): Pointer;
var
  Buf:     array[0..21] of Byte;
  BP:      PChar;
  Written: Integer;
begin
  BP      := PChar(@Buf[0]);
  Written := WriteDecimal(N, BP);
  Result  := StrAlloc(Written);
  if (Result <> nil) and (Written > 0) then
    MemCopy(StrData(Result), Pointer(BP), Written);
end;

{ Write a UInt64 value (passed as Int64 bit pattern during bootstrap) as
  decimal digits into Buf (no NUL).  Buf must have at least 21 bytes.
  Returns character count.  Distinct from WriteDecimal because the
  magnitude can exceed Int64 range. }
function WriteDecimalU(N: UInt64; Buf: PChar): Integer;
var
  Pos:   Integer;
  Tmp:   array[0..21] of Byte;
  TP:    PChar;
  I, J:  Integer;
  Digit: Integer;
begin
  TP  := PChar(@Tmp[0]);
  if N = UInt64(0) then
  begin
    TP[0] := 48;  { '0' }
    Pos   := 1;
  end
  else
  begin
    Pos := 0;
    while N > UInt64(0) do
    begin
      Digit   := Integer(N mod UInt64(10));
      TP[Pos] := 48 + Digit;
      N       := N div UInt64(10);
      Inc(Pos);
    end;
  end;
  I := 0;
  J := Pos - 1;
  while J >= 0 do
  begin
    Buf[I] := TP[J];
    Inc(I);
    Dec(J);
  end;
  Result := I;
end;

function _UInt64ToStr(N: UInt64): Pointer;
var
  Buf:     array[0..21] of Byte;
  BP:      PChar;
  Written: Integer;
begin
  BP      := PChar(@Buf[0]);
  Written := WriteDecimalU(N, BP);
  Result  := StrAlloc(Written);
  if (Result <> nil) and (Written > 0) then
    MemCopy(StrData(Result), Pointer(BP), Written);
end;

{ ------------------------------------------------------------------ }
{ _StrToInt / _StrToInt64                                             }
{ ------------------------------------------------------------------ }

function _StrToInt(S: Pointer): Integer;
var
  Data:  PChar;
  Neg:   Boolean;
  I, C:  Integer;
  Value: Int64;
begin
  Data  := StrData(S);
  I     := 0;
  Neg   := False;
  if Data[0] = 45 then  { '-' }
  begin
    Neg := True;
    I   := 1;
  end
  else if Data[0] = 43 then  { '+' }
    I := 1;
  Value := 0;
  if Data[I] = 36 then  { '$' — hexadecimal }
  begin
    Inc(I);
    C := Data[I];
    while ((C >= 48) and (C <= 57))
       or ((C >= 65) and (C <= 70))
       or ((C >= 97) and (C <= 102)) do
    begin
      if C >= 97 then
        Value := Value * 16 + Int64(C - 87)   { 'a'..'f' → 10..15 }
      else if C >= 65 then
        Value := Value * 16 + Int64(C - 55)   { 'A'..'F' → 10..15 }
      else
        Value := Value * 16 + Int64(C - 48);  { '0'..'9' }
      Inc(I);
      C := Data[I];
    end;
  end
  else
  begin
    C := Data[I];
    while (C >= 48) and (C <= 57) do
    begin
      Value := Value * 10 + Int64(C - 48);
      Inc(I);
      C := Data[I];
    end;
  end;
  if Neg then
    Result := Integer(-Value)
  else
    Result := Integer(Value);
end;

function _StrToInt64(S: Pointer): Int64;
var
  Data:  PChar;
  Neg:   Boolean;
  I, C:  Integer;
begin
  Data  := StrData(S);
  I     := 0;
  Neg   := False;
  if Data[0] = 45 then
  begin
    Neg := True;
    I   := 1;
  end
  else if Data[0] = 43 then
    I := 1;
  Result := 0;
  if Data[I] = 36 then  { '$' — hexadecimal }
  begin
    Inc(I);
    C := Data[I];
    while ((C >= 48) and (C <= 57))
       or ((C >= 65) and (C <= 70))
       or ((C >= 97) and (C <= 102)) do
    begin
      if C >= 97 then
        Result := Result * 16 + Int64(C - 87)
      else if C >= 65 then
        Result := Result * 16 + Int64(C - 55)
      else
        Result := Result * 16 + Int64(C - 48);
      Inc(I);
      C := Data[I];
    end;
  end
  else
  begin
    C := Data[I];
    while (C >= 48) and (C <= 57) do
    begin
      Result := Result * 10 + Int64(C - 48);
      Inc(I);
      C := Data[I];
    end;
  end;
  if Neg then
    Result := -Result;
end;

{ ------------------------------------------------------------------ }
{ _OrdAt                                                               }
{ ------------------------------------------------------------------ }

function _OrdAt(S: Pointer; I: Integer): Integer;
var
  Len:  Integer;
  Data: PChar;
begin
  Len  := StrLen(S);
  if (I < 0) or (I >= Len) then
  begin
    Exit(0);
  end;
  Data   := StrData(S);
  Result := Data[I];
end;

{ ------------------------------------------------------------------ }
{ _Chr                                                                 }
{ ------------------------------------------------------------------ }

function _Chr(N: Integer): Pointer;
var
  DP: PChar;
begin
  Result := StrAlloc(1);
  if Result = nil then Exit;
  DP    := StrData(Result);
  DP[0] := N;
end;

{ ------------------------------------------------------------------ }
{ _UpCase                                                              }
{ ------------------------------------------------------------------ }

function _UpCase(N: Integer): Pointer;
var
  C: Integer;
begin
  C := N;
  if (C >= 97) and (C <= 122) then
    C := C - 32;
  Result := _Chr(C);
end;

{ ------------------------------------------------------------------ }
{ _StringCompare                                                       }
{ ------------------------------------------------------------------ }

function _StringCompare(S1, S2: Pointer): Integer;
var
  Len1, Len2, Len: Integer;
  D1, D2:          PChar;
  I, C1, C2:       Integer;
begin
  Len1 := StrLen(S1);
  Len2 := StrLen(S2);
  if Len1 < Len2 then Len := Len1 else Len := Len2;
  D1 := StrData(S1);
  D2 := StrData(S2);
  for I := 0 to Len - 1 do
  begin
    C1 := D1[I];
    C2 := D2[I];
    if C1 <> C2 then
    begin
      Exit(C1 - C2);
    end;
  end;
  Result := Len1 - Len2;
end;

{ ------------------------------------------------------------------ }
{ _StringCompareText                                                   }
{ ------------------------------------------------------------------ }

function _StringCompareText(S1, S2: Pointer): Integer;
var
  Len1, Len2, Len: Integer;
  D1, D2:          PChar;
  I, C1, C2:       Integer;
begin
  Len1 := StrLen(S1);
  Len2 := StrLen(S2);
  if Len1 < Len2 then Len := Len1 else Len := Len2;
  D1 := StrData(S1);
  D2 := StrData(S2);
  for I := 0 to Len - 1 do
  begin
    C1 := D1[I];
    C2 := D2[I];
    if (C1 >= 65) and (C1 <= 90) then C1 := C1 + 32;
    if (C2 >= 65) and (C2 <= 90) then C2 := C2 + 32;
    if C1 <> C2 then
    begin
      Exit(C1 - C2);
    end;
  end;
  Result := Len1 - Len2;
end;

{ ------------------------------------------------------------------ }
{ _StringFromPChar                                                     }
{ ------------------------------------------------------------------ }

function _StringFromPChar(P: PChar): Pointer;
var
  Len: Integer;
begin
  if P = nil then
  begin
    Exit(StrAlloc(0));
  end;
  Len := 0;
  while P[Len] <> 0 do
    Inc(Len);
  Result := StrAlloc(Len);
  if (Result <> nil) and (Len > 0) then
    MemCopy(StrData(Result), P, Len);
end;

{ ------------------------------------------------------------------ }
{ _Utf8DecodeAt                                                        }
{ ------------------------------------------------------------------ }

function _Utf8DecodeAt(S: Pointer; Idx: Integer): Int64;
var
  P: PChar;
  B0, B1, B2, B3: Integer;
  CP: Integer;
begin
  P := StrData(S);
  B0 := P[Idx];
  if B0 < 128 then
    Result := (Int64(1) shl 32) or Int64(B0)
  else if (B0 and $E0) = $C0 then
  begin
    B1 := P[Idx + 1] and $3F;
    CP := ((B0 and $1F) shl 6) or B1;
    Result := (Int64(2) shl 32) or Int64(CP);
  end
  else if (B0 and $F0) = $E0 then
  begin
    B1 := P[Idx + 1] and $3F;
    B2 := P[Idx + 2] and $3F;
    CP := ((B0 and $0F) shl 12) or (B1 shl 6) or B2;
    Result := (Int64(3) shl 32) or Int64(CP);
  end
  else
  begin
    B1 := P[Idx + 1] and $3F;
    B2 := P[Idx + 2] and $3F;
    B3 := P[Idx + 3] and $3F;
    CP := ((B0 and $07) shl 18) or (B1 shl 12) or (B2 shl 6) or B3;
    Result := (Int64(4) shl 32) or Int64(CP);
  end;
end;

{ ------------------------------------------------------------------ }
{ _StringFormat                                                        }
{ ------------------------------------------------------------------ }

{ Number of characters WriteDecimal will produce for N — used by
  _StringFormatN's sizing pass so it doesn't render the digits twice. }
function DecimalWidth(N: Int64): Integer;
var
  AbsN: Int64;
begin
  if N = 0 then
    Exit(1);
  Result := 0;
  if N < 0 then
  begin
    Result := 1;   { '-' }
    AbsN := -N;
  end
  else
    AbsN := N;
  while AbsN > 0 do
  begin
    Result := Result + 1;
    AbsN := AbsN div 10;
  end;
end;

{ Render one Format argument (without field-width padding) into a freshly
  allocated raw buffer.  Returns the buffer in OutBuf and its length as the
  function result.  The caller must _BlaiseFreeMem(OutBuf) when OutFree is
  True; when OutFree is False, OutBuf aliases an existing buffer (a string
  argument's data pointer) and must NOT be freed.
    Tag    : 0=int, 1=string, 2=float (raw double bits in Val).
    Conv   : ASCII code of the conversion letter ('d','s','f','e','g',...).
    Prec   : precision (-1 = default). }
function RenderFmtArg(Tag: Integer; Val: Int64; Conv: Integer; Prec: Integer;
  out OutBuf: PChar; out OutFree: Boolean): Integer;
var
  Buf: PChar;
  N:   Integer;
  FStr: Pointer;
  V:    Double;
  VP:   ^Double;
begin
  OutFree := True;
  if Tag = 2 then
  begin
    { Float — delegate to blaise_float, copy out, release the temp string. }
    VP := Pointer(@Val);
    V := VP^;
    FStr := _FormatFloatSpec(V, Conv, Prec);
    N := StrLen(FStr);
    Buf := PChar(_BlaiseGetMem(N + 1));
    if N > 0 then
      MemCopy(Buf, PChar(FStr), N);
    Buf[N] := 0;
    _BlaiseFreeMem(Pointer(Pointer(FStr) - HDR_SIZE));
    OutBuf := Buf;
    Exit(N);
  end;
  if Tag = 1 then
  begin
    { String — alias its data pointer, no copy, no free. }
    OutFree := False;
    OutBuf := PChar(Pointer(Val));
    Exit(StrLen(Pointer(Val)));
  end;
  { Integer (Tag = 0) — render decimal into a small heap buffer. }
  Buf := PChar(_BlaiseGetMem(24));
  N := WriteDecimal(Val, Buf);
  Buf[N] := 0;
  OutBuf := Buf;
  Result := N;
end;

{ Append Len bytes from Src into the growable output buffer described by
  Out / OutLen / OutCap, growing it as needed.  Returns the (possibly
  reallocated) buffer; the caller writes back OutLen and OutCap from the
  var parameters. }
function FmtAppend(OutB: PChar; var OutLen: Integer; var OutCap: Integer;
  Src: PChar; Len: Integer): PChar;
var
  NewCap: Integer;
begin
  if OutLen + Len > OutCap then
  begin
    NewCap := OutCap * 2;
    if NewCap < OutLen + Len then
      NewCap := OutLen + Len + 16;
    OutB := PChar(_BlaiseReallocMem(OutB, NewCap));
    OutCap := NewCap;
  end;
  if Len > 0 then
    MemCopy(OutB + OutLen, Src, Len);
  OutLen := OutLen + Len;
  Result := OutB;
end;

{ Append Count copies of byte B (used for field-width space padding). }
function FmtAppendFill(OutB: PChar; var OutLen: Integer; var OutCap: Integer;
  B: Integer; Count: Integer): PChar;
var
  K: Integer;
begin
  if OutLen + Count > OutCap then
  begin
    if OutCap < OutLen + Count then
      OutCap := OutLen + Count + 16;
    OutB := PChar(_BlaiseReallocMem(OutB, OutCap));
  end;
  K := 0;
  while K < Count do
  begin
    OutB[OutLen] := B;
    OutLen := OutLen + 1;
    K := K + 1;
  end;
  Result := OutB;
end;

function _StringFormatN(Fmt: Pointer; Args: Pointer; Count: Integer): Pointer;
var
  F, Dst:  PChar;
  FLen, I, ArgIdx, Tag: Integer;
  Val:     Int64;
  AP:      Pointer;
  TagPtr, ValPtr: ^Int64;
  OutB:    PChar;        { growable output buffer (raw bytes, no header) }
  OutLen, OutCap: Integer;
  Width, Prec, Conv: Integer;
  LeftJust: Boolean;
  ArgBuf:  PChar;
  ArgFree: Boolean;
  ArgLen, Pad: Integer;
  ByteBuf: array[0..1] of Byte;
begin
  F := StrData(Fmt);
  FLen := StrLen(Fmt);
  ArgIdx := 0;

  OutCap := FLen + 16;
  OutB := PChar(_BlaiseGetMem(OutCap));
  OutLen := 0;

  I := 0;
  while I < FLen do
  begin
    if (F[I] = 37) and (I + 1 < FLen) then  { '%' }
    begin
      Inc(I);
      { Literal '%%'. }
      if F[I] = 37 then
      begin
        ByteBuf[0] := 37;
        OutB := FmtAppend(OutB, OutLen, OutCap, PChar(@ByteBuf[0]), 1);
        Inc(I);
        Continue;
      end;

      { Parse [-][width][.prec]. }
      LeftJust := False;
      while (I < FLen) and (F[I] = 45) do  { '-' }
      begin
        LeftJust := True;
        Inc(I);
      end;
      Width := 0;
      while (I < FLen) and (F[I] >= 48) and (F[I] <= 57) do
      begin
        Width := Width * 10 + (F[I] - 48);
        Inc(I);
      end;
      Prec := -1;
      if (I < FLen) and (F[I] = 46) then  { '.' }
      begin
        Inc(I);
        Prec := 0;
        while (I < FLen) and (F[I] >= 48) and (F[I] <= 57) do
        begin
          Prec := Prec * 10 + (F[I] - 48);
          Inc(I);
        end;
      end;

      if I >= FLen then
      begin
        { Trailing '%' with no conversion: emit it verbatim. }
        ByteBuf[0] := 37;
        OutB := FmtAppend(OutB, OutLen, OutCap, PChar(@ByteBuf[0]), 1);
        Continue;
      end;

      Conv := F[I];
      Inc(I);

      { Recognised conversions consume one argument. }
      if (Conv = 100) or (Conv = 115) or          { d s }
         (Conv = 102) or (Conv = 70) or           { f F }
         (Conv = 101) or (Conv = 69) or           { e E }
         (Conv = 103) or (Conv = 71) then          { g G }
      begin
        if ArgIdx >= Count then
        begin
          { Missing argument — skip (no output). }
          Inc(ArgIdx);
          Continue;
        end;
        AP := Args + ArgIdx * 16;
        TagPtr := AP;
        ValPtr := AP + 8;
        Tag := Integer(TagPtr^);
        Val := ValPtr^;
        Inc(ArgIdx);

        ArgLen := RenderFmtArg(Tag, Val, Conv, Prec, ArgBuf, ArgFree);

        Pad := Width - ArgLen;
        if Pad < 0 then Pad := 0;
        if (Pad > 0) and (not LeftJust) then
          OutB := FmtAppendFill(OutB, OutLen, OutCap, 32, Pad);
        OutB := FmtAppend(OutB, OutLen, OutCap, ArgBuf, ArgLen);
        if (Pad > 0) and LeftJust then
          OutB := FmtAppendFill(OutB, OutLen, OutCap, 32, Pad);
        if ArgFree then
          _BlaiseFreeMem(ArgBuf);
      end
      else
      begin
        { Unknown conversion: emit '%' followed by the letter. }
        ByteBuf[0] := 37;
        ByteBuf[1] := Conv;
        OutB := FmtAppend(OutB, OutLen, OutCap, PChar(@ByteBuf[0]), 2);
      end;
    end
    else
    begin
      OutB := FmtAppend(OutB, OutLen, OutCap, F + I, 1);
      Inc(I);
    end;
  end;

  { Materialise the final Blaise string and release the scratch buffer. }
  Dst := PChar(StrAlloc(OutLen));
  if Dst <> nil then
  begin
    if OutLen > 0 then
      MemCopy(Dst, OutB, OutLen);
    Dst[OutLen] := 0;
  end;
  _BlaiseFreeMem(OutB);
  Result := Pointer(Dst);
end;

function _StringFormatVarRecs(Fmt: Pointer; VarRecs: Pointer;
  Count: Integer): Pointer;
var
  Block: Pointer;
  I: Integer;
  VRec: Pointer;
  VType: Integer;
  VTypePtr: ^Byte;
  VValPtr: ^Int64;
  VVal: Int64;
  TagPtr, ValPtr: ^Int64;
  DPtr: ^Int64;
begin
  { Translate Count real TVarRecs -> the [Tag:8][Val:8] block. }
  if Count < 0 then
    Count := 0;
  Block := _BlaiseGetMem(Count * 16 + 16);   { +16: never GetMem(0) }
  for I := 0 to Count - 1 do
  begin
    VRec := VarRecs + I * 16;      { real TVarRec: VType@0 (byte), VValue@8 }
    VTypePtr := VRec;
    VType := Integer(VTypePtr^);
    VValPtr := VRec + 8;
    VVal := VValPtr^;
    TagPtr := Block + I * 16;
    ValPtr := Block + I * 16 + 8;
    { vt* -> Format 3-tag.  vtInteger(0)/vtBoolean(1)/vtInt64(16)/vtEnum(24)
      are integers; vtAnsiString(20)/vtPointer(5)/vtObject(7) pass a pointer;
      vtExtended(3) is a HEAP-BOXED double — deref VValue for the raw bits. }
    if VType = 3 then             { vtExtended }
    begin
      TagPtr^ := 2;               { raw binary64 bits }
      DPtr := Pointer(VVal);      { VValue points at the boxed double }
      if DPtr <> nil then
        ValPtr^ := DPtr^
      else
        ValPtr^ := 0;
    end
    else if (VType = 20) or (VType = 5) or (VType = 7) then
    begin
      TagPtr^ := 1;               { string data ptr / pointer / object }
      ValPtr^ := VVal;
    end
    else
    begin
      TagPtr^ := 0;               { integer family }
      ValPtr^ := VVal;
    end;
  end;
  Result := _StringFormatN(Fmt, Block, Count);
  _BlaiseFreeMem(Block);
end;

{ ------------------------------------------------------------------ }
{ File-path manipulation                                               }
{ ------------------------------------------------------------------ }

function _ChangeFileExt(Path, Ext: Pointer): Pointer;
var
  P, E: PChar;
  PLen, ELen, I, DotPos, StemLen: Integer;
begin
  P := StrData(Path);
  E := StrData(Ext);
  PLen := StrLen(Path);
  ELen := StrLen(Ext);
  DotPos := -1;
  I := PLen - 1;
  while I >= 0 do
  begin
    if P[I] = 47 then Break;
    if P[I] = 46 then begin DotPos := I; Break end;
    Dec(I);
  end;
  if DotPos >= 0 then StemLen := DotPos else StemLen := PLen;
  Result := StrAlloc(StemLen + ELen);
  if Result = nil then Exit;
  if StemLen > 0 then MemCopy(Result, P, StemLen);
  if ELen > 0 then MemCopy(Result + StemLen, E, ELen);
end;

function _ExtractFileName(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, Start: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  Start := 0;
  for I := 0 to PLen - 1 do
    if P[I] = 47 then Start := I + 1;
  Result := StrAlloc(PLen - Start);
  if (Result <> nil) and (PLen - Start > 0) then
    MemCopy(Result, P + Start, PLen - Start);
end;

function _ExtractFilePath(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, SlashPos: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  SlashPos := -1;
  for I := 0 to PLen - 1 do
    if P[I] = 47 then SlashPos := I;
  if SlashPos < 0 then
  begin
    Exit(StrAlloc(0));
  end;
  Result := StrAlloc(SlashPos + 1);
  if Result <> nil then MemCopy(Result, P, SlashPos + 1);
end;

function _ExtractFileDir(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, SlashPos: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  SlashPos := -1;
  for I := 0 to PLen - 1 do
    if P[I] = 47 then SlashPos := I;
  if (SlashPos < 0) or (SlashPos = 0) then
  begin
    Exit(StrAlloc(0));
  end;
  Result := StrAlloc(SlashPos);
  if Result <> nil then MemCopy(Result, P, SlashPos);
end;

function _ExtractFileExt(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, LastDot, LastSep: Integer;
  ExtLen: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  LastDot := -1;
  LastSep := -1;
  for I := 0 to PLen - 1 do
  begin
    if P[I] = 47 then LastSep := I;
    if P[I] = 46 then LastDot := I;
  end;
  if (LastDot < 0) or ((LastSep >= 0) and (LastDot < LastSep)) then
  begin
    Exit(StrAlloc(0));
  end;
  ExtLen := PLen - LastDot;
  Result := StrAlloc(ExtLen);
  if (Result <> nil) and (ExtLen > 0) then
    MemCopy(Result, P + LastDot, ExtLen);
end;

function _IncludeTrailingPathDelimiter(Path: Pointer): Pointer;
var
  P, DP: PChar;
  PLen: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  if (PLen > 0) and (P[PLen - 1] = 47) then
  begin
    Result := StrAlloc(PLen);
    if Result <> nil then MemCopy(Result, P, PLen);
    Exit;
  end;
  Result := StrAlloc(PLen + 1);
  if Result = nil then Exit;
  if PLen > 0 then MemCopy(Result, P, PLen);
  DP := StrData(Result);
  DP[PLen] := 47;
end;

function _ExcludeTrailingPathDelimiter(Path: Pointer): Pointer;
var
  P: PChar;
  PLen: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  if (PLen > 0) and (P[PLen - 1] = 47) then Dec(PLen);
  Result := StrAlloc(PLen);
  if (Result <> nil) and (PLen > 0) then
    MemCopy(Result, P, PLen);
end;

{ ------------------------------------------------------------------ }
{ Dynamic array RTL                                                    }
{ ------------------------------------------------------------------ }

const
  DA_HDR = 16;  { [hook:8][refcount:4][length:4] before element 0 }

type
  TDynElemHook = procedure(Data: Pointer; Count, ARetain: Integer);

function _DynArrayLength(Ptr: Pointer): Integer;
var
  LenPtr: ^Integer;
begin
  if Ptr = nil then
  begin
    Exit(0);
  end;
  { length is stored at offset −4 from data pointer }
  LenPtr := Ptr - 4;
  Result := LenPtr^;
end;

procedure DaWriteInt32(P: ^Integer; V: Integer);
begin
  P^ := V;
end;

function _DynArraySetLengthM(Ptr: Pointer; NewLen, ElemSize: Integer;
  Hook: Pointer): Pointer;
var
  NewBase:  Pointer;
  NewData:  PChar;
  DataSz:   Integer;
  OldLen:   Integer;
  CopyLen:  Integer;
  ZI:       Integer;
  HdrPtr:   ^Integer;
  HookSlot: ^Pointer;
  RC:       ^Integer;
  Shared:   Boolean;
  H:        TDynElemHook;
begin
  { No hook of the caller's own (an unmanaged element, or code from an older
    compiler): keep the one the existing block carries. }
  if (Hook = nil) and (Ptr <> nil) then
  begin
    HookSlot := Ptr - 16;
    Hook := HookSlot^;
  end;
  { SetLength(A, 0) drops THIS reference -- other holders keep the block --
    and the last reference releases the elements. }
  if NewLen <= 0 then
  begin
    _DynArrayRelease(Ptr);
    Exit(nil);
  end;
  DataSz  := DA_HDR + NewLen * ElemSize;
  NewBase := _BlaiseGetMem(DataSz);
  HookSlot  := NewBase;
  HookSlot^ := Hook;
  HdrPtr    := NewBase + 8;
  DaWriteInt32(HdrPtr, 1);           { refcount }
  HdrPtr    := NewBase + 12;
  DaWriteInt32(HdrPtr, NewLen);      { length }
  NewData := PChar(NewBase) + DA_HDR;
  ZI := 0;
  while ZI < NewLen * ElemSize do
  begin
    NewData[ZI] := 0;
    ZI := ZI + 1;
  end;
  if Ptr <> nil then
  begin
    OldLen := _DynArrayLength(Ptr);
    if OldLen < NewLen then CopyLen := OldLen else CopyLen := NewLen;
    if CopyLen > 0 then
      MemCopy(NewData, PChar(Ptr), CopyLen * ElemSize);
    RC := Ptr - 8;
    Shared := RC^ <> 1;
    if Hook <> nil then
      H := TDynElemHook(Hook);
    if Shared then
    begin
      { copy-on-write: the other holders keep the old block, so the copied
        elements gain a reference and this holder drops its own }
      if (Hook <> nil) and (CopyLen > 0) then
        H(NewData, CopyLen, 1);
      _DynArrayRelease(Ptr);
    end
    else
    begin
      { uniquely owned: the elements MOVED; a shrink releases the tail that
        did not come along, then the old block goes without its hook }
      if (Hook <> nil) and (OldLen > NewLen) then
        H(Ptr + NewLen * ElemSize, OldLen - NewLen, 0);
      _BlaiseFreeMem(Ptr - DA_HDR);
    end;
  end;
  Result := NewData;
end;

function _DynArraySetLength(Ptr: Pointer; NewLen, ElemSize: Integer): Pointer;
begin
  Result := _DynArraySetLengthM(Ptr, NewLen, ElemSize, nil);
end;

end.
