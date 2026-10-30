{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — jumbo set operations.

  A "jumbo" set is a `set of <enum>` whose element enum has more than 64
  members (up to the 256 ceiling).  It cannot fit in a single CPU register,
  so it is represented as an inline byte-array bitmap of NBytes bytes
  (NBytes = ceil(BitCount/8), so at most 32).  Member ordinal k occupies
  bit (k and 7) of byte (k shr 3):

      byte index = k shr 3        (k div 8)
      bit  mask  = 1 shl (k and 7)

  Sets of 64 members or fewer keep the fast single-register representation
  and never reach these helpers; the codegen backends emit calls here only
  for the jumbo case.

  All set pointers are the address of the first bitmap byte.  The binary
  operators tolerate Dest aliasing A and/or B (e.g. S := S + T): the byte
  loop runs strictly forward and reads both inputs for index i before
  writing Dest[i], so full overlap is safe.
}

unit runtime.set;

interface

{ ------------------------------------------------------------------ }
{ Jumbo set RTL public interface                                      }
{ ------------------------------------------------------------------ }
function  _SetIn(S: Pointer; Ord: Int32): Int32;          { 0 or 1 }
procedure _SetInclude(S: Pointer; Ord: Int32);
procedure _SetExclude(S: Pointer; Ord: Int32);
procedure _SetUnion(Dest, A, B: Pointer; NBytes: Int32);    { Dest := A or B }
procedure _SetInter(Dest, A, B: Pointer; NBytes: Int32);    { Dest := A and B }
procedure _SetDiff(Dest, A, B: Pointer; NBytes: Int32);     { Dest := A and not B }
function  _SetEqual(A, B: Pointer; NBytes: Int32): Int32;  { 1 if equal }
function  _SetSubset(A, B: Pointer; NBytes: Int32): Int32; { 1 if A subset of B }
procedure _SetCopy(Dest, Src: Pointer; NBytes: Int32);      { byte copy }

implementation

{ Read byte i of a bitmap. }
function GetByte(S: Pointer; I: Int): Int;
var
  P: ^Byte;
begin
  P := S + I;
  Result := P^;
end;

{ Write byte i of a bitmap. }
procedure PutByte(S: Pointer; I, V: Int);
var
  P: ^Byte;
begin
  P := S + I;
  P^ := Byte(V);
end;

function _SetIn(S: Pointer; Ord: Int32): Int32;
var
  ByteIdx, BitMask, B: Int;
begin
  if S = nil then
    Exit(0);
  ByteIdx := Ord shr 3;
  BitMask := 1 shl (Ord and 7);
  B := GetByte(S, ByteIdx);
  if (B and BitMask) <> 0 then
    Result := 1
  else
    Result := 0;
end;

procedure _SetInclude(S: Pointer; Ord: Int32);
var
  ByteIdx, BitMask, B: Int;
begin
  ByteIdx := Ord shr 3;
  BitMask := 1 shl (Ord and 7);
  B := GetByte(S, ByteIdx);
  PutByte(S, ByteIdx, B or BitMask);
end;

procedure _SetExclude(S: Pointer; Ord: Int32);
var
  ByteIdx, BitMask, B: Int;
begin
  ByteIdx := Ord shr 3;
  BitMask := 1 shl (Ord and 7);
  B := GetByte(S, ByteIdx);
  PutByte(S, ByteIdx, B and (not BitMask));
end;

procedure _SetUnion(Dest, A, B: Pointer; NBytes: Int32);
var
  I: Int;
begin
  I := 0;
  while I < NBytes do
  begin
    PutByte(Dest, I, GetByte(A, I) or GetByte(B, I));
    Inc(I);
  end;
end;

procedure _SetInter(Dest, A, B: Pointer; NBytes: Int32);
var
  I: Int;
begin
  I := 0;
  while I < NBytes do
  begin
    PutByte(Dest, I, GetByte(A, I) and GetByte(B, I));
    Inc(I);
  end;
end;

procedure _SetDiff(Dest, A, B: Pointer; NBytes: Int32);
var
  I: Int;
begin
  I := 0;
  while I < NBytes do
  begin
    PutByte(Dest, I, GetByte(A, I) and (not GetByte(B, I)));
    Inc(I);
  end;
end;

function _SetEqual(A, B: Pointer; NBytes: Int32): Int32;
var
  I: Int;
begin
  I := 0;
  while I < NBytes do
  begin
    if GetByte(A, I) <> GetByte(B, I) then
      Exit(0);
    Inc(I);
  end;
  Result := 1;
end;

{ 1 if A is a subset of B (every bit set in A is also set in B), else 0. }
function _SetSubset(A, B: Pointer; NBytes: Int32): Int32;
var
  I: Int;
begin
  I := 0;
  while I < NBytes do
  begin
    { A byte of A has a bit absent from B iff (A[i] and not B[i]) <> 0. }
    if (GetByte(A, I) and not GetByte(B, I)) <> 0 then
      Exit(0);
    Inc(I);
  end;
  Result := 1;
end;

procedure _SetCopy(Dest, Src: Pointer; NBytes: Int32);
var
  I: Int;
begin
  I := 0;
  while I < NBytes do
  begin
    PutByte(Dest, I, GetByte(Src, I));
    Inc(I);
  end;
end;

end.
