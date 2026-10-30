{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.cstub;

// Freestanding C-library leaves the compiler and RTL emit calls to but which
// are not syscalls: memcpy / memmove / memset / memcmp / strlen.  In a libc-backed build
// these come from libc; in a --static build this unit supplies them so no libc
// is needed (docs/linux-syscall-migration.adoc).
//
// Architecture-neutral byte-at-a-time implementations.  Correctness over speed:
// these are the fallback for the freestanding build; if profiling shows the
// allocator/string paths need it, an SSE/AVX memcpy can replace the loop later
// (the inline-asm assembler already encodes the vector ops).
//
// Signatures match the C ABI the codegen assumes:
//   void* memcpy(void* dst, const void* src, size_t n)   - returns dst
//   void* memmove(void* dst, const void* src, size_t n)  - returns dst; overlap-safe
//   void* memset(void* dst, int c, size_t n)             - returns dst
//   int   memcmp(const void* a, const void* b, size_t n)
//   size_t strlen(const char* s)

interface

function memcpy(Dst, Src: Pointer; N: Int64): Pointer;
function memmove(Dst, Src: Pointer; N: Int64): Pointer;
function memset(Dst: Pointer; C: Integer; N: Int64): Pointer;
function memcmp(A, B: Pointer; N: Int64): Integer;
function strlen(S: PChar): Int64;

implementation

{ PChar indexing reads/writes a single byte as an Integer (see runtime.str), so
  these loops need no Char type (Blaise has none). }

function memcpy(Dst, Src: Pointer; N: Int64): Pointer;
var
  D, S: PChar;
  I: Int64;
begin
  D := PChar(Dst);
  S := PChar(Src);
  I := 0;
  while I < N do
  begin
    D[I] := S[I];
    I := I + 1;
  end;
  Result := Dst;
end;

{ Copies backwards when Dst lies above an overlapping Src, so no byte is
  overwritten before it has been read. }
function memmove(Dst, Src: Pointer; N: Int64): Pointer;
var
  D, S: PChar;
  I: Int64;
begin
  D := PChar(Dst);
  S := PChar(Src);
  if UInt(Dst) <= UInt(Src) then
  begin
    I := 0;
    while I < N do
    begin
      D[I] := S[I];
      I := I + 1;
    end;
  end
  else
  begin
    I := N - 1;
    while I >= 0 do
    begin
      D[I] := S[I];
      I := I - 1;
    end;
  end;
  Result := Dst;
end;

function memset(Dst: Pointer; C: Integer; N: Int64): Pointer;
var
  D: PChar;
  I: Int64;
  B: Integer;
begin
  D := PChar(Dst);
  B := C and $FF;
  I := 0;
  while I < N do
  begin
    D[I] := B;
    I := I + 1;
  end;
  Result := Dst;
end;

function memcmp(A, B: Pointer; N: Int64): Integer;
var
  PA, PB: PChar;
  I: Int64;
  CA, CB: Integer;
begin
  PA := PChar(A);
  PB := PChar(B);
  I := 0;
  while I < N do
  begin
    CA := PA[I] and $FF;
    CB := PB[I] and $FF;
    if CA <> CB then
    begin
      Result := CA - CB;
      Exit;
    end;
    I := I + 1;
  end;
  Result := 0;
end;

function strlen(S: PChar): Int64;
var
  I: Int64;
begin
  I := 0;
  while (S[I] and $FF) <> 0 do
    I := I + 1;
  Result := I;
end;

end.
