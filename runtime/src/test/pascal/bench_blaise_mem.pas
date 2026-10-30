{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  bench_blaise_mem — allocation performance benchmark.

  Fixed workload that does not change with compiler growth.  Run this
  after allocator changes to detect regressions.

  Workloads:
    1. Small alloc/free churn   — 1 000 000 x GetMem(32) + FreeMem
    2. Mixed sizes              — 500 000 x rotating 8/32/128/512/2048
    3. Realloc growth           — 100 000 x grow 16 -> 32 -> 64 -> 128 -> 256
    4. Large alloc/free         — 10 000 x GetMem(65536) + FreeMem
    5. Alloc-retain-free-all    — allocate 100 000 blocks, then free all

  Output: elapsed time in milliseconds per workload.  Compare across
  runs to detect regressions or improvements.

  Build (the compiler source-builds and links the RTL — no blaise_rtl.a):
    blaise --source runtime/src/test/pascal/bench_blaise_mem.pas \
           --unit-path compiler/src/main/pascal \
           --output /tmp/bench_mem
    /tmp/bench_mem
}

program bench_blaise_mem;

function _TimeNow: Int64; external name '_TimeNow';

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
  Result := Int32(Diff div 1_000_000);
end;

procedure PrintResult(Name: string; Ms: Int);
begin
  WriteLn('  ' + Name + ': ' + IntToStr(Ms) + ' ms');
end;

const
  SMALL_COUNT   = 1_000_000;
  MIXED_COUNT   = 500_000;
  REALLOC_COUNT = 100_000;
  LARGE_COUNT   = 10_000;
  RETAIN_COUNT  = 100_000;

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

  WriteLn('blaise_mem benchmark');
  WriteLn('====================');

  { 1. Small alloc/free churn }
  BenchStart();
  for I := 0 to SMALL_COUNT - 1 do
  begin
    P := GetMem(32);
    FreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Small alloc/free (1M x 32B)', Elapsed);

  { 2. Mixed sizes }
  BenchStart();
  for I := 0 to MIXED_COUNT - 1 do
  begin
    J := I mod 5;
    P := GetMem(Sizes[J]);
    FreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Mixed sizes (500k x 8-2048B)', Elapsed);

  { 3. Realloc growth }
  BenchStart();
  for I := 0 to REALLOC_COUNT - 1 do
  begin
    P := GetMem(16);
    P := ReallocMem(P, 32);
    P := ReallocMem(P, 64);
    P := ReallocMem(P, 128);
    P := ReallocMem(P, 256);
    FreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Realloc growth (100k x 5 steps)', Elapsed);

  { 4. Large alloc/free }
  BenchStart();
  for I := 0 to LARGE_COUNT - 1 do
  begin
    P := GetMem(65536);
    FreeMem(P);
  end;
  Elapsed := BenchElapsedMs();
  PrintResult('Large alloc/free (10k x 64KB)', Elapsed);

  { 5. Alloc-retain-free-all }
  BenchStart();
  for I := 0 to RETAIN_COUNT - 1 do
    Blocks[I] := GetMem(64);
  for I := 0 to RETAIN_COUNT - 1 do
    FreeMem(Blocks[I]);
  Elapsed := BenchElapsedMs();
  PrintResult('Retain+free-all (100k x 64B)', Elapsed);

  WriteLn('====================');
end.
