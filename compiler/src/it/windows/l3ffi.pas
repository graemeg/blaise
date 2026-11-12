{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
program l3ffi;
// The Blaise side of the Layer 3 foreign-function fixture
// (docs/windows-x86_64-backend-design.adoc, "Layer 3"): calls into
// l3ffi.dll, built from l3ffi.c by mingw-w64, across every boundary case --
// each integer kind, enum and Boolean at its boundary values, results
// narrower than RAX, more than four mixed arguments, records of 1 to 16
// bytes by value and as results, variadic calls, and calls back into
// Blaise.  scripts/windows-vm.sh crosscheck compares the output with
// l3ffi.expected.

type
  TColour = (cRed, cGreen, cBlue);
  TS1 = record A: Byte; end;
  TS2 = record A, B: Byte; end;
  TS3 = record A, B, C: Byte; end;
  TS4 = record A, B: Int16; end;
  TS5 = record A, B, C, D, E: Byte; end;
  TS8 = record A, B: Int32; end;
  TS12 = record A, B, C: Int32; end;
  TS16 = record A, B: Int64; end;
  TSF2 = record X, Y: Float32; end;
  TSD2 = record X, Y: Float64; end;
  { C function pointers, and Blaise routines C calls back (M5): the C
    convention is part of each type }
  TFn2 = function(A, B: Int64): Int64; cdecl;
  TFn6 = function(A: Int32; B: Float64; C: Int32; D: Float64; E: Int32;
    F: Float64): Float64; cdecl;
  TFnU8 = function(V: UInt64): Byte; cdecl;
  TMkS8 = function(V: Int32): TS8; cdecl;
  TMkS12 = function(A, B, C: Int32): TS12; cdecl;
  TMkSD2 = function(X, Y: Float64): TSD2; cdecl;
  TCbS1 = function(V: Int32): TS1; cdecl;
  TCbS2 = function(V: Int32): TS2; cdecl;
  TCbS3 = function(V: Int32): TS3; cdecl;
  TCbS4 = function(V: Int32): TS4; cdecl;
  TCbS5 = function(V: Int32): TS5; cdecl;
  TCbS8 = function(V: Int32): TS8; cdecl;
  TCbS12 = function(V: Int32): TS12; cdecl;
  TCbS16 = function(V: Int32): TS16; cdecl;
  TCbSF2 = function(V: Int32): TSF2; cdecl;
  TCbSD2 = function(V: Int32): TSD2; cdecl;
  TCbS12Many = function(A: Int32; B: Int64; C: Float64; D: Int32;
    E: Int64): TS12; cdecl;
  TCbTake = function(X: TS8; Y: TS12; K: Int32): Int64; cdecl;

function l3_echo_i8(V: Int8): Int8; external 'l3ffi' name 'l3_echo_i8';
function l3_echo_u8(V: Byte): Byte; external 'l3ffi' name 'l3_echo_u8';
function l3_echo_i16(V: Int16): Int16; external 'l3ffi' name 'l3_echo_i16';
function l3_echo_u16(V: UInt16): UInt16; external 'l3ffi' name 'l3_echo_u16';
function l3_echo_i32(V: Int32): Int32; external 'l3ffi' name 'l3_echo_i32';
function l3_echo_u32(V: UInt32): UInt32; external 'l3ffi' name 'l3_echo_u32';
function l3_echo_i64(V: Int64): Int64; external 'l3ffi' name 'l3_echo_i64';
function l3_echo_u64(V: UInt64): UInt64; external 'l3ffi' name 'l3_echo_u64';
function l3_narrow_i8(V: UInt64): Int8; external 'l3ffi' name 'l3_narrow_i8';
function l3_narrow_u8(V: UInt64): Byte; external 'l3ffi' name 'l3_narrow_u8';
function l3_narrow_i16(V: UInt64): Int16; external 'l3ffi' name 'l3_narrow_i16';
function l3_narrow_u16(V: UInt64): UInt16; external 'l3ffi' name 'l3_narrow_u16';
function l3_narrow_i32(V: UInt64): Int32; external 'l3ffi' name 'l3_narrow_i32';
function l3_narrow_u32(V: UInt64): UInt32; external 'l3ffi' name 'l3_narrow_u32';
function l3_widen(A: Int8; B: Byte; C: Int16; D: UInt16): Int64;
  external 'l3ffi' name 'l3_widen';
function l3_not(B: Boolean): Boolean; external 'l3ffi' name 'l3_not';
function l3_enum_next(E: TColour): TColour; external 'l3ffi' name 'l3_enum_next';
function l3_mix(A: Int32; B: Float64; C: Int64; D: Float32; E: Byte; F: Float64;
  G: Int16; H: Float32): Float64; external 'l3ffi' name 'l3_mix';
function l3_floats(A, B, C, D, E, F: Float32): Float32;
  external 'l3ffi' name 'l3_floats';
function l3_take_s1(S: TS1): Int64; external 'l3ffi' name 'l3_take_s1';
function l3_take_s2(S: TS2): Int64; external 'l3ffi' name 'l3_take_s2';
function l3_take_s3(S: TS3): Int64; external 'l3ffi' name 'l3_take_s3';
function l3_take_s4(S: TS4): Int64; external 'l3ffi' name 'l3_take_s4';
function l3_take_s5(S: TS5): Int64; external 'l3ffi' name 'l3_take_s5';
function l3_take_s8(S: TS8): Int64; external 'l3ffi' name 'l3_take_s8';
function l3_take_s12(S: TS12): Int64; external 'l3ffi' name 'l3_take_s12';
function l3_take_s16(S: TS16): Int64; external 'l3ffi' name 'l3_take_s16';
function l3_take_sf2(S: TSF2): Float64; external 'l3ffi' name 'l3_take_sf2';
function l3_take_sd2(S: TSD2): Float64; external 'l3ffi' name 'l3_take_sd2';
function l3_take_many(A: Int32; B: TS12; C: TS2; D: Int64; E: TS16;
  F: TS8): Int64; external 'l3ffi' name 'l3_take_many';
function l3_make_s1(V: Int32): TS1; external 'l3ffi' name 'l3_make_s1';
function l3_make_s2(V: Int32): TS2; external 'l3ffi' name 'l3_make_s2';
function l3_make_s3(V: Int32): TS3; external 'l3ffi' name 'l3_make_s3';
function l3_make_s4(V: Int32): TS4; external 'l3ffi' name 'l3_make_s4';
function l3_make_s5(V: Int32): TS5; external 'l3ffi' name 'l3_make_s5';
function l3_make_s8(V: Int32): TS8; external 'l3ffi' name 'l3_make_s8';
function l3_make_s12(A, B, C: Int32): TS12; external 'l3ffi' name 'l3_make_s12';
function l3_make_s16(A, B: Int64): TS16; external 'l3ffi' name 'l3_make_s16';
function l3_make_sf2(X, Y: Float32): TSF2; external 'l3ffi' name 'l3_make_sf2';
function l3_make_sd2(X, Y: Float64): TSD2; external 'l3ffi' name 'l3_make_sd2';
function l3_make_s12_many(A, B, C, D, E, F: Int32): TS12;
  external 'l3ffi' name 'l3_make_s12_many';
function l3_vsum(N: Int32): Int64; varargs; external 'l3ffi' name 'l3_vsum';
function l3_vdsum(N: Int32): Float64; varargs; external 'l3ffi' name 'l3_vdsum';
function l3_apply2(F: TFn2; A, B: Int64): Int64;
  external 'l3ffi' name 'l3_apply2';
function l3_apply6(F: TFn6): Float64; external 'l3ffi' name 'l3_apply6';
function l3_get_sub2: TFn2; external 'l3ffi' name 'l3_get_sub2';
function l3_get_narrow_u8: TFnU8; external 'l3ffi' name 'l3_get_narrow_u8';
function l3_get_make_s8: TMkS8; external 'l3ffi' name 'l3_get_make_s8';
function l3_get_make_s12: TMkS12; external 'l3ffi' name 'l3_get_make_s12';
function l3_get_make_sd2: TMkSD2; external 'l3ffi' name 'l3_get_make_sd2';
function l3_cb_s1(F: TCbS1): Int64; external 'l3ffi' name 'l3_cb_s1';
function l3_cb_s2(F: TCbS2): Int64; external 'l3ffi' name 'l3_cb_s2';
function l3_cb_s3(F: TCbS3): Int64; external 'l3ffi' name 'l3_cb_s3';
function l3_cb_s4(F: TCbS4): Int64; external 'l3ffi' name 'l3_cb_s4';
function l3_cb_s5(F: TCbS5): Int64; external 'l3ffi' name 'l3_cb_s5';
function l3_cb_s8(F: TCbS8): Int64; external 'l3ffi' name 'l3_cb_s8';
function l3_cb_s12(F: TCbS12): Int64; external 'l3ffi' name 'l3_cb_s12';
function l3_cb_s16(F: TCbS16): Int64; external 'l3ffi' name 'l3_cb_s16';
function l3_cb_sf2(F: TCbSF2): Float64; external 'l3ffi' name 'l3_cb_sf2';
function l3_cb_sd2(F: TCbSD2): Float64; external 'l3ffi' name 'l3_cb_sd2';
function l3_cb_s12_many(F: TCbS12Many): Int64;
  external 'l3ffi' name 'l3_cb_s12_many';
function l3_cb_take(F: TCbTake): Int64; external 'l3ffi' name 'l3_cb_take';

{ Called from C. }
function Combine(A, B: Int64): Int64; cdecl;
begin
  Result := A * 100 + B;
end;

function Six(A: Int32; B: Float64; C: Int32; D: Float64; E: Int32;
  F: Float64): Float64; cdecl;
begin
  Result := A + B * 10 + C * 100 + D * 1000 + E * 10000 + F * 100000;
end;

{ Record results handed back to C, one per size class. }
function MkS1(V: Int32): TS1; cdecl;
begin
  Result.A := V * 30;
end;

function MkS2(V: Int32): TS2; cdecl;
begin
  Result.A := V;
  Result.B := V + 2;
end;

function MkS3(V: Int32): TS3; cdecl;
begin
  Result.A := 1;
  Result.B := V;
  Result.C := 200;
end;

function MkS4(V: Int32): TS4; cdecl;
begin
  Result.A := -V;
  Result.B := 300;
end;

function MkS5(V: Int32): TS5; cdecl;
begin
  Result.A := V;
  Result.B := V + 1;
  Result.C := V + 2;
  Result.D := V + 3;
  Result.E := V + 4;
end;

function MkS8(V: Int32): TS8; cdecl;
begin
  Result.A := V;
  Result.B := -1000;
end;

function MkS12(V: Int32): TS12; cdecl;
begin
  Result.A := V;
  Result.B := 8;
  Result.C := 9;
end;

function MkS16(V: Int32): TS16; cdecl;
begin
  Result.A := High(Int64) div 4;
  Result.B := V;
end;

function MkSF2(V: Int32): TSF2; cdecl;
begin
  Result.X := V / 2;
  Result.Y := 0.25;
end;

function MkSD2(V: Int32): TSD2; cdecl;
begin
  Result.X := V * 1.5;
  Result.Y := -0.5;
end;

function MkS12Many(A: Int32; B: Int64; C: Float64; D: Int32;
  E: Int64): TS12; cdecl;
begin
  Result.A := A + D;
  Result.B := Trunc(C * 2);
  Result.C := B * 10 + E;
end;

function TakeRecs(X: TS8; Y: TS12; K: Int32): Int64; cdecl;
begin
  Result := X.A * 1000 + X.B * 100 + Y.A * 10 + Y.B + Y.C + K;
end;

var
  Sub: TFn2;
  NarrowU8: TFnU8;
  MakeS8: TMkS8;
  MakeS12: TMkS12;
  MakeSD2: TMkSD2;
  S1: TS1; S2: TS2; S3: TS3; S4: TS4; S5: TS5; S8: TS8; S12: TS12;
  S16: TS16; SF2: TSF2; SD2: TSD2;
begin
  WriteLn('i8 ', l3_echo_i8(Low(Int8)), ' ', l3_echo_i8(High(Int8)), ' ', l3_echo_i8(-1));
  WriteLn('u8 ', l3_echo_u8(Low(Byte)), ' ', l3_echo_u8(High(Byte)));
  WriteLn('i16 ', l3_echo_i16(Low(Int16)), ' ', l3_echo_i16(High(Int16)));
  WriteLn('u16 ', l3_echo_u16(High(UInt16)));
  WriteLn('i32 ', l3_echo_i32(Low(Int32)), ' ', l3_echo_i32(High(Int32)));
  WriteLn('u32 ', l3_echo_u32(High(UInt32)));
  WriteLn('i64 ', l3_echo_i64(Low(Int64)), ' ', l3_echo_i64(High(Int64)));
  WriteLn('u64 ', l3_echo_u64(High(UInt64)), ' ', l3_echo_u64(UInt64(High(Int64)) + 1));
  WriteLn('narrow ', l3_narrow_i8($123456789ABCDE80), ' ', l3_narrow_u8($12345678ABCDEFFF), ' ',
    l3_narrow_i16($1234567800008000), ' ', l3_narrow_u16($12345678ABCDFFFF));
  WriteLn('narrow32 ', l3_narrow_i32($1234567880000000), ' ', l3_narrow_u32($12345678FFFFFFFF));
  { used directly, not through a variable: compared, added, indexed }
  WriteLn('narrowuse ', l3_narrow_u8($12345678ABCDEFFF) = 255, ' ',
    l3_narrow_i16($1234567800008000) + 1, ' ', l3_narrow_i32($1234567880000000) < 0, ' ',
    l3_narrow_u16($12345678ABCDFFFF) div 5, ' ', Int64(l3_narrow_u32($12345678FFFFFFFF)) + 1, ' ',
    l3_narrow_i8($123456789ABCDE80) * 2, ' ', l3_not(False) and True, ' ',
    Ord(l3_enum_next(cGreen)) = Ord(cBlue));
  WriteLn('widen ', l3_widen(Low(Int8), High(Byte), Low(Int16), High(UInt16)));
  WriteLn('bool ', l3_not(True), ' ', l3_not(False));
  WriteLn('enum ', Ord(l3_enum_next(cRed)), ' ', Ord(l3_enum_next(cGreen)));
  WriteLn('mix ', l3_mix(1, 2.5, 3, 4.5, 6, 7.5, -8, 9.5));
  WriteLn('floats ', l3_floats(1, 2, 3, 4, 5, 6));
  S1.A := 200;
  S2.A := 1; S2.B := 2;
  S3.A := 7; S3.B := 8; S3.C := 9;
  S4.A := -3; S4.B := 4;
  S5.A := 1; S5.B := 2; S5.C := 3; S5.D := 4; S5.E := 5;
  S8.A := -7; S8.B := 8;
  S12.A := 1; S12.B := 2; S12.C := 3;
  S16.A := High(Int64) div 4; S16.B := -1;
  SF2.X := 1.5; SF2.Y := 0.25;
  SD2.X := 2.5; SD2.Y := 0.125;
  WriteLn('take ', l3_take_s1(S1), ' ', l3_take_s2(S2), ' ', l3_take_s3(S3), ' ',
    l3_take_s4(S4), ' ', l3_take_s5(S5));
  WriteLn('take ', l3_take_s8(S8), ' ', l3_take_s12(S12), ' ', l3_take_s16(S16));
  WriteLn('takef ', l3_take_sf2(SF2), ' ', l3_take_sd2(SD2));
  WriteLn('many ', l3_take_many(10, S12, S2, 20, S16, S8));
  S1 := l3_make_s1(255);
  S2 := l3_make_s2(10);
  S3 := l3_make_s3(20);
  S4 := l3_make_s4(30000);
  S5 := l3_make_s5(250);
  WriteLn('make ', S1.A, ' ', S2.A, ',', S2.B, ' ', S3.A, ',', S3.B, ',', S3.C, ' ',
    S4.A, ',', S4.B, ' ', S5.A, ',', S5.E);
  S8 := l3_make_s8(Low(Int32) + 1);
  S12 := l3_make_s12(-1, 0, High(Int32));
  S16 := l3_make_s16(Low(Int64), High(Int64));
  WriteLn('make ', S8.A, ',', S8.B, ' ', S12.A, ',', S12.B, ',', S12.C, ' ',
    S16.A, ',', S16.B);
  SF2 := l3_make_sf2(0.5, -0.75);
  SD2 := l3_make_sd2(1.25, -2.5);
  WriteLn('makef ', SF2.X, ',', SF2.Y, ' ', SD2.X, ',', SD2.Y);
  S12 := l3_make_s12_many(1, 2, 3, 4, 5, 6);
  WriteLn('makemany ', S12.A, ',', S12.B, ',', S12.C);
  WriteLn('field ', l3_make_s12(4, 5, 6).B, ' ', l3_make_s8(9).A);
  WriteLn('vsum ', l3_vsum(5, Int64(1), Int64(2), Int64(3), Int64(4), Int64(High(Int32))));
  WriteLn('vdsum ', l3_vdsum(5, 0.5, 1.5, 2.5, 3.5, 4.5));
  WriteLn('apply2 ', l3_apply2(@Combine, 12, 34));
  WriteLn('apply6 ', l3_apply6(@Six));
  { C routines through a pointer }
  Sub := l3_get_sub2();
  NarrowU8 := l3_get_narrow_u8();
  WriteLn('ptr ', Sub(100, 58), ' ', NarrowU8($12345678ABCDEFFF), ' ',
    NarrowU8($12345678ABCDEFFF) + 1);
  MakeS8 := l3_get_make_s8();
  MakeS12 := l3_get_make_s12();
  MakeSD2 := l3_get_make_sd2();
  S8 := MakeS8(Low(Int32) + 1);
  S12 := MakeS12(-1, 0, High(Int32));
  SD2 := MakeSD2(1.25, -2.5);
  WriteLn('ptrmake ', S8.A, ',', S8.B, ' ', S12.A, ',', S12.B, ',', S12.C, ' ',
    SD2.X, ',', SD2.Y);
  { Blaise callbacks returning records }
  WriteLn('cbrec ', l3_cb_s1(@MkS1), ' ', l3_cb_s2(@MkS2), ' ', l3_cb_s3(@MkS3),
    ' ', l3_cb_s4(@MkS4), ' ', l3_cb_s5(@MkS5));
  WriteLn('cbrec ', l3_cb_s8(@MkS8), ' ', l3_cb_s12(@MkS12), ' ',
    l3_cb_s16(@MkS16));
  WriteLn('cbrecf ', l3_cb_sf2(@MkSF2), ' ', l3_cb_sd2(@MkSD2));
  WriteLn('cbmany ', l3_cb_s12_many(@MkS12Many), ' ', l3_cb_take(@TakeRecs));
end.
