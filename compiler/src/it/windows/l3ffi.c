/*
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.

  l3ffi.dll -- the C side of the Layer 3 foreign-function fixture
  (docs/windows-x86_64-backend-design.adoc, "Layer 3").  Built by
  x86_64-w64-mingw32-gcc, an independent compiler, so l3ffi.pas proves the
  Win64 lowering against code Blaise did not write.  Every routine derives
  its result from all of its arguments, so a misplaced or truncated
  argument changes what is printed.
*/
#include <stdarg.h>
#include <stdint.h>

#define L3 __declspec(dllexport)

/* ---- integer kinds, enum and Boolean ---- */

L3 int8_t   l3_echo_i8(int8_t v)    { return v; }
L3 uint8_t  l3_echo_u8(uint8_t v)   { return v; }
L3 int16_t  l3_echo_i16(int16_t v)  { return v; }
L3 uint16_t l3_echo_u16(uint16_t v) { return v; }
L3 int32_t  l3_echo_i32(int32_t v)  { return v; }
L3 uint32_t l3_echo_u32(uint32_t v) { return v; }
L3 int64_t  l3_echo_i64(int64_t v)  { return v; }
L3 uint64_t l3_echo_u64(uint64_t v) { return v; }

/* A narrow result computed from a wide value: the Win64 convention leaves
   the bits of RAX above the result undefined, and these leave them set. */
L3 int8_t   l3_narrow_i8(uint64_t v)  { return (int8_t)v; }
L3 uint8_t  l3_narrow_u8(uint64_t v)  { return (uint8_t)v; }
L3 int16_t  l3_narrow_i16(uint64_t v) { return (int16_t)v; }
L3 uint16_t l3_narrow_u16(uint64_t v) { return (uint16_t)v; }
L3 int32_t  l3_narrow_i32(uint64_t v) { return (int32_t)v; }
L3 uint32_t l3_narrow_u32(uint64_t v) { return (uint32_t)v; }

/* A narrow argument read at its own width: the bits above it are the
   caller's, and the callee must not need them. */
L3 int64_t l3_widen(int8_t a, uint8_t b, int16_t c, uint16_t d)
{
  return (int64_t)a * 1000000000LL + (int64_t)b * 1000000LL +
         (int64_t)c * 10LL + (int64_t)d;
}

L3 _Bool l3_not(_Bool b) { return !b; }
L3 int   l3_enum_next(int e) { return e + 1; }

/* ---- more than four arguments, integer and float mixed ---- */

L3 double l3_mix(int32_t a, double b, int64_t c, float d, uint8_t e,
                 double f, int16_t g, float h)
{
  return a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8;
}

L3 float l3_floats(float a, float b, float c, float d, float e, float f)
{
  return a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6;
}

/* ---- records by value ---- */

typedef struct { uint8_t a; } S1;
typedef struct { uint8_t a, b; } S2;
typedef struct { uint8_t a, b, c; } S3;
typedef struct { int16_t a, b; } S4;
typedef struct { uint8_t a, b, c, d, e; } S5;
typedef struct { int32_t a, b; } S8;
typedef struct { int32_t a, b, c; } S12;
typedef struct { int64_t a, b; } S16;
typedef struct { float x, y; } SF2;
typedef struct { double x, y; } SD2;

L3 int64_t l3_take_s1(S1 s)   { return s.a; }
L3 int64_t l3_take_s2(S2 s)   { return s.a * 1000 + s.b; }
L3 int64_t l3_take_s3(S3 s)   { return s.a * 1000000 + s.b * 1000 + s.c; }
L3 int64_t l3_take_s4(S4 s)   { return s.a * 100000 + s.b; }
L3 int64_t l3_take_s5(S5 s)   { return s.a + s.b * 2 + s.c * 3 + s.d * 4 + s.e * 5; }
L3 int64_t l3_take_s8(S8 s)   { return (int64_t)s.a * 1000000 + s.b; }
L3 int64_t l3_take_s12(S12 s) { return (int64_t)s.a * 1000000 + s.b * 1000 + s.c; }
L3 int64_t l3_take_s16(S16 s) { return s.a * 3 + s.b; }
L3 double  l3_take_sf2(SF2 s) { return s.x * 10 + s.y; }
L3 double  l3_take_sd2(SD2 s) { return s.x * 10 + s.y; }

/* Records among other arguments, past the fourth: by value and by copy. */
L3 int64_t l3_take_many(int32_t a, S12 b, S2 c, int64_t d, S16 e, S8 f)
{
  return a + l3_take_s12(b) * 2 + l3_take_s2(c) * 3 + d * 4 +
         l3_take_s16(e) * 5 + l3_take_s8(f) * 6;
}

/* ---- records returned ---- */

L3 S1  l3_make_s1(int32_t v)  { S1 s = { (uint8_t)v }; return s; }
L3 S2  l3_make_s2(int32_t v)  { S2 s = { (uint8_t)v, (uint8_t)(v + 1) }; return s; }
L3 S3  l3_make_s3(int32_t v)  { S3 s = { (uint8_t)v, (uint8_t)(v + 1), (uint8_t)(v + 2) }; return s; }
L3 S4  l3_make_s4(int32_t v)  { S4 s = { (int16_t)v, (int16_t)-v }; return s; }
L3 S5  l3_make_s5(int32_t v)  { S5 s = { 1, 2, 3, 4, (uint8_t)v }; return s; }
L3 S8  l3_make_s8(int32_t v)  { S8 s = { v, -v }; return s; }
L3 S12 l3_make_s12(int32_t a, int32_t b, int32_t c) { S12 s = { a, b, c }; return s; }
L3 S16 l3_make_s16(int64_t a, int64_t b) { S16 s = { a, b }; return s; }
L3 SF2 l3_make_sf2(float x, float y) { SF2 s = { x, y }; return s; }
L3 SD2 l3_make_sd2(double x, double y) { SD2 s = { x, y }; return s; }

/* A hidden result pointer plus five more arguments: the fifth and sixth
   are on the stack. */
L3 S12 l3_make_s12_many(int32_t a, int32_t b, int32_t c, int32_t d,
                        int32_t e, int32_t f)
{
  S12 s = { a + b, c + d, e + f };
  return s;
}

/* ---- variadic ---- */

L3 int64_t l3_vsum(int32_t n, ...)
{
  va_list ap;
  int64_t sum = 0;
  int32_t i;
  va_start(ap, n);
  for (i = 0; i < n; i++)
    sum += va_arg(ap, int64_t) * (i + 1);
  va_end(ap);
  return sum;
}

L3 double l3_vdsum(int32_t n, ...)
{
  va_list ap;
  double sum = 0;
  int32_t i;
  va_start(ap, n);
  for (i = 0; i < n; i++)
    sum += va_arg(ap, double) * (i + 1);
  va_end(ap);
  return sum;
}

/* ---- calls back into Blaise ---- */

typedef int64_t (*Fn2)(int64_t, int64_t);
typedef double (*Fn6)(int32_t, double, int32_t, double, int32_t, double);

L3 int64_t l3_apply2(Fn2 f, int64_t a, int64_t b) { return f(a, b) + 1; }

L3 double l3_apply6(Fn6 f)
{
  return f(1, 2.5, 3, 4.5, 5, 6.5);
}

/* ---- C routines called through a pointer (M5) ---- */

typedef uint8_t (*FnU8)(uint64_t);
typedef S8  (*MkS8)(int32_t);
typedef S12 (*MkS12)(int32_t, int32_t, int32_t);
typedef SD2 (*MkSD2)(double, double);

static int64_t sub2(int64_t a, int64_t b) { return a - b; }

L3 Fn2   l3_get_sub2(void)      { return sub2; }
L3 FnU8  l3_get_narrow_u8(void) { return l3_narrow_u8; }
L3 MkS8  l3_get_make_s8(void)   { return l3_make_s8; }
L3 MkS12 l3_get_make_s12(void)  { return l3_make_s12; }
L3 MkSD2 l3_get_make_sd2(void)  { return l3_make_sd2; }

/* ---- Blaise callbacks that return records (M5) ----
   Each record is read back through l3_take_*, so a byte out of place
   changes the result. */

typedef S1  (*CbS1)(int32_t);
typedef S2  (*CbS2)(int32_t);
typedef S3  (*CbS3)(int32_t);
typedef S4  (*CbS4)(int32_t);
typedef S5  (*CbS5)(int32_t);
typedef S8  (*CbS8)(int32_t);
typedef S12 (*CbS12)(int32_t);
typedef S16 (*CbS16)(int32_t);
typedef SF2 (*CbSF2)(int32_t);
typedef SD2 (*CbSD2)(int32_t);

L3 int64_t l3_cb_s1(CbS1 f)   { return l3_take_s1(f(7)); }
L3 int64_t l3_cb_s2(CbS2 f)   { return l3_take_s2(f(7)); }
L3 int64_t l3_cb_s3(CbS3 f)   { return l3_take_s3(f(7)); }
L3 int64_t l3_cb_s4(CbS4 f)   { return l3_take_s4(f(7)); }
L3 int64_t l3_cb_s5(CbS5 f)   { return l3_take_s5(f(7)); }
L3 int64_t l3_cb_s8(CbS8 f)   { return l3_take_s8(f(7)); }
L3 int64_t l3_cb_s12(CbS12 f) { return l3_take_s12(f(7)); }
L3 int64_t l3_cb_s16(CbS16 f) { return l3_take_s16(f(7)); }
L3 double  l3_cb_sf2(CbSF2 f) { return l3_take_sf2(f(7)); }
L3 double  l3_cb_sd2(CbSD2 f) { return l3_take_sd2(f(7)); }

/* A hidden result pointer and five arguments: the last two on the stack. */
typedef S12 (*CbS12Many)(int32_t, int64_t, double, int32_t, int64_t);
L3 int64_t l3_cb_s12_many(CbS12Many f) { return l3_take_s12(f(1, 2, 3.5, 4, 5)); }

/* A callback taking records: by value (S8) and as the address of a copy
   (S12). */
typedef int64_t (*CbTake)(S8, S12, int32_t);
L3 int64_t l3_cb_take(CbTake f)
{
  S8 a = { 3, -4 };
  S12 b = { 5, 6, 7 };
  return f(a, b, 8);
}
