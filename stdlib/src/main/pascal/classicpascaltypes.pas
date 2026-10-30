{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - the classic Pascal type names, for code ported from Free
  Pascal or Delphi.

  Blaise's own type names state their width: Int8 .. Int64, UInt8 .. UInt64,
  Float32 / Float64, and the pointer-sized Int / UInt.  This opt-in unit
  restores the familiar FPC / Delphi spellings as transparent aliases -- each
  name IS the Blaise type it maps to, so values pass between the two
  spellings without a cast.

  The mapping is deliberately frozen-width: LongInt is Int32 because it is 32
  bits in FPC and Delphi, so ported code keeps the semantics it was written
  against.  Two names change meaning:

    Extended  is Float64.  In FPC on x86 it is the 80-bit x87 type, which
              exists on no other architecture.  Code that relied on 80-bit
              intermediate precision computes in 64-bit here.
    Real      is Float64 (it already is, in practice, in FPC and Delphi).

  Integer, Cardinal, SmallInt, Word, QWord, PtrUInt, Single and Double were
  builtin names until type standardisation Phase 6; they and their pointer
  aliases (PInteger, PCardinal, ...) are declared here now, like the rest.
  See docs/type-standardisation-design.adoc. }

unit ClassicPascalTypes;

interface

type
  Integer = Int32;
  Cardinal = UInt32;
  SmallInt = Int16;
  Word = UInt16;
  QWord = UInt64;
  PtrUInt = UInt;
  Single = Float32;
  Double = Float64;
  ShortInt = Int8;
  LongInt = Int32;
  LongWord = UInt32;
  NativeInt = Int;
  NativeUInt = UInt;
  PtrInt = Int;
  Real = Float64;
  Extended = Float64;
  Comp = Int64;

  { Their pointer aliases -- each the same type as the pointer to the Blaise
    type it maps to (PLongInt is ^Int32, so it is System's PInt32). }
  PInteger = ^Integer;
  PCardinal = ^Cardinal;
  PSmallInt = ^SmallInt;
  PWord = ^Word;
  PQWord = ^QWord;
  PPtrUInt = ^PtrUInt;
  PSingle = ^Single;
  PDouble = ^Double;
  PShortInt = ^ShortInt;
  PLongInt = ^LongInt;
  PLongWord = ^LongWord;
  PNativeInt = ^NativeInt;
  PNativeUInt = ^NativeUInt;
  PPtrInt = ^PtrInt;
  PReal = ^Real;
  PExtended = ^Extended;
  PComp = ^Comp;

implementation

end.
