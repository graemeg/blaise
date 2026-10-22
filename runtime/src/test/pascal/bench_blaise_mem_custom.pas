{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Same workloads as bench_blaise_mem.pas but calling _BlaiseGetMem directly. }

program bench_blaise_mem_custom;

uses runtime.mem;

function _TimeNow: Int64; external name '_TimeNow';

var
  T0: Int64;

procedure BenchStart;
begin
  T0 := _TimeNow();
end;

function BenchElapsedMs: Integer;
var
  Diff: Int64;
begin
  Diff := _TimeNow() - T0;
  Result := Integer(Diff div 1000000);
end;

procedure PrintResult(Name: string; Ms: Integer);
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
  I, J, Elapsed: Integer;
  P: Pointer;
  Sizes: array[0..4] of Integer;
  Blocks: array[0..99999] of Pointer;

begin
  Sizes[0] := 8;
  Sizes[1] := 32;
  Sizes[2] := 128;
  Sizes[3] := 512;
  Sizes[4] := 2048;

  WriteLn('blaise_mem benchmark (custom allocator)');
  WriteLn('=======================================');

  { 1. Small alloc/free churn }
  BenchStart();
  for I := 0 to SMALL_COUNT - 1 do
  begin
    P := _BlaiseGetMem(32);
    _BlaiseFreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Small alloc/free (1M x 32B)', Elapsed);

  { 2. Mixed sizes }
  BenchStart();
  for I := 0 to MIXED_COUNT - 1 do
  begin
    J := I mod 5;
    P := _BlaiseGetMem(Sizes[J]);
    _BlaiseFreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Mixed sizes (500k x 8-2048B)', Elapsed);

  { 3. Realloc growth }
  BenchStart();
  for I := 0 to REALLOC_COUNT - 1 do
  begin
    P := _BlaiseGetMem(16);
    P := _BlaiseReallocMem(P, 32);
    P := _BlaiseReallocMem(P, 64);
    P := _BlaiseReallocMem(P, 128);
    P := _BlaiseReallocMem(P, 256);
    _BlaiseFreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Realloc growth (100k x 5 steps)', Elapsed);

  { 4. Large alloc/free }
  BenchStart();
  for I := 0 to LARGE_COUNT - 1 do
  begin
    P := _BlaiseGetMem(65536);
    _BlaiseFreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Large alloc/free (10k x 64KB)', Elapsed);

  { 5. Alloc-retain-free-all }
  BenchStart();
  for I := 0 to RETAIN_COUNT - 1 do
    Blocks[I] := _BlaiseGetMem(64);
  for I := 0 to RETAIN_COUNT - 1 do
    _BlaiseFreeMem(Blocks[I]);
  Elapsed := BenchElapsedMs();
  PrintResult('Retain+free-all (100k x 64B)', Elapsed);

  WriteLn('=======================================');
end.
