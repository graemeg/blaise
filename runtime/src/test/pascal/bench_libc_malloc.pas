{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Same workloads as bench_blaise_mem_custom.pas but calling libc malloc
  directly via external declarations.  Used to compare blaise_mem against
  glibc malloc post-cutover (since GetMem builtin now goes through
  _BlaiseGetMem). }

program bench_libc_malloc;

function _TimeNow: Int64; external name '_TimeNow';

function  _libc_malloc(Size: Int32): Pointer;             external name 'malloc';
procedure _libc_free(Ptr: Pointer);                         external name 'free';
function  _libc_realloc(Ptr: Pointer; Size: Int32): Pointer; external name 'realloc';

var
  T0: Int64;

procedure BenchStart;
begin
  T0 := _TimeNow();
end;

function BenchElapsedMs: Int;
var
  Diff: Int64;
begin
  Diff := _TimeNow() - T0;
  Result := Int32(Diff div 1000000);
end;

procedure PrintResult(Name: string; Ms: Int);
begin
  WriteLn('  ' + Name + ': ' + IntToStr(Ms) + ' ms');
end;

const
  SMALL_COUNT   = 1000000;
  MIXED_COUNT   = 500000;
  REALLOC_COUNT = 100000;
  LARGE_COUNT   = 10000;
  RETAIN_COUNT  = 100000;

var
  I, J, Elapsed: Int;
  P: Pointer;
  Sizes: array[0..4] of Int32;
  Blocks: array[0..99999] of Pointer;

begin
  Sizes[0] := 8;
  Sizes[1] := 32;
  Sizes[2] := 128;
  Sizes[3] := 512;
  Sizes[4] := 2048;

  WriteLn('libc malloc baseline');
  WriteLn('====================');

  { 1. Small alloc/free churn }
  BenchStart();
  for I := 0 to SMALL_COUNT - 1 do
  begin
    P := _libc_malloc(32);
    _libc_free(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Small alloc/free (1M x 32B)', Elapsed);

  { 2. Mixed sizes }
  BenchStart();
  for I := 0 to MIXED_COUNT - 1 do
  begin
    J := I mod 5;
    P := _libc_malloc(Sizes[J]);
    _libc_free(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Mixed sizes (500k x 8-2048B)', Elapsed);

  { 3. Realloc growth }
  BenchStart();
  for I := 0 to REALLOC_COUNT - 1 do
  begin
    P := _libc_malloc(16);
    P := _libc_realloc(P, 32);
    P := _libc_realloc(P, 64);
    P := _libc_realloc(P, 128);
    P := _libc_realloc(P, 256);
    _libc_free(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Realloc growth (100k x 5 steps)', Elapsed);

  { 4. Large alloc/free }
  BenchStart();
  for I := 0 to LARGE_COUNT - 1 do
  begin
    P := _libc_malloc(65536);
    _libc_free(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Large alloc/free (10k x 64KB)', Elapsed);

  { 5. Alloc-retain-free-all }
  BenchStart();
  for I := 0 to RETAIN_COUNT - 1 do
    Blocks[I] := _libc_malloc(64);
  for I := 0 to RETAIN_COUNT - 1 do
    _libc_free(Blocks[I]);
  Elapsed := BenchElapsedMs();
  PrintResult('Retain+free-all (100k x 64B)', Elapsed);

  WriteLn('====================');
end.
