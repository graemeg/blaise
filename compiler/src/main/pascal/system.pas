{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit System;

// Blaise RTL — Phase 1 system unit.
//
// This unit is the implicit foundation of every Blaise program. The types
// declared here are also known intrinsically to the compiler. The procedures
// declared here are resolved as compiler built-ins in Phase 1 (the code
// generator emits direct libc printf calls without linking against this unit).
//
// Phase 2 will introduce proper unit compilation, ARC string management,
// and linking against a compiled RTL object file.
//
// NOTE: This file is compiled by the Blaise compiler, not FPC. It uses
// Blaise syntax and semantics. Do not attempt to compile it with FPC.

interface

type
  { ------------------------------------------------------------------ }
  {  Primitive integer types                                            }
  { ------------------------------------------------------------------ }

  { 32-bit signed integer. }
  Integer = Int32;

  { 64-bit signed integer. }
  Int64   = Int64;

  { 32-bit unsigned integer. }
  UInt32  = UInt32;

  { 8-bit unsigned integer. }
  Byte    = Byte;

  { ------------------------------------------------------------------ }
  {  Boolean                                                            }
  { ------------------------------------------------------------------ }

  { Boolean is an 8-bit type. False = 0, True = 1.
    Stored as a byte. Logical operators produce
    0 or 1 only — no non-zero truthiness. }
  Boolean = (False = 0, True = 1);

  { ------------------------------------------------------------------ }
  {  String                                                             }
  { ------------------------------------------------------------------ }

  { The single Blaise string type. An opaque ARC-managed pointer.
    A nil pointer represents an empty string. All string literals
    are statically allocated; user strings are heap-allocated.

    Memory layout (Phase 2+, locked before Phase 1):
      +--------+--------+----------+------------+-------+
      | refcnt | length | capacity | UTF-8 data |  NUL  |
      |  4 B   |  4 B   |   4 B    |   N bytes  |  1 B  |
      +--------+--------+----------+------------+-------+
    'length' is byte count. 'capacity' >= length.
    ARC management (_StringAddRef / _StringRelease) is inserted by
    the compiler at assignments and scope exits.
    _StringAddRef(nil) and _StringRelease(nil) are no-ops.

    Phase 1 simplification: string literals compile to raw NUL-terminated
    data without the header. The full header and ARC are Phase 2. }

  { string is declared as an intrinsic compiler type. }

  { RawBytes is identical in layout to string but the compiler does not
    insert UTF-8 validation. Conversions between string and RawBytes
    require explicit casts. Phase 2+. }

  { ------------------------------------------------------------------ }
  {  Nil                                                                }
  { ------------------------------------------------------------------ }

  { nil is the zero value for all pointer and string types. }

{ ------------------------------------------------------------------ }
{  Platform constants                                                 }
{ ------------------------------------------------------------------ }

const
  { Line ending for the current platform.  POSIX = #10, Windows = #13#10.
    Set at compile time based on the target platform. }
  LineEnding = #10;

  { Directory separator character.  POSIX = '/', Windows = '\'. }
  DirectorySeparator = '/';

  { PATH environment variable separator.  POSIX = ':', Windows = ';'. }
  PathSeparator = ':';

{ ------------------------------------------------------------------ }
{  Built-in I/O procedures                                            }
{ ------------------------------------------------------------------ }

{ Write a string to standard output without a trailing newline. }
procedure Write(const S: string); overload;

{ Write a string to standard output followed by a newline. }
procedure WriteLn(const S: string); overload;

{ Write a newline to standard output. }
procedure WriteLn; overload;

implementation

{ Phase 1: all implementations are compiler built-ins.
  The code generator emits direct calls to libc printf.
  A compiled RTL implementation will replace these in Phase 2. }

end.
