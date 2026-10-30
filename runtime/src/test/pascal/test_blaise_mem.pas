{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ punit tests for blaise_mem — the Pascal memory allocator.

  These tests exercise the allocator at the raw pointer level, below
  the string and ARC subsystems.  punit is the correct framework here
  because blaise_mem has zero dependency on stdlib or ARC.

  Build (the compiler source-builds and links the RTL — no blaise_rtl.a):
    blaise --source runtime/src/test/pascal/test_blaise_mem.pas \
           --unit-path compiler/src/main/pascal \
           --unit-path runtime/src/test/pascal \
           --output /tmp/test_mem
    /tmp/test_mem -v
}

program test_blaise_mem;

uses
  punit, runtime.mem, runtime.atomic;

{ ------------------------------------------------------------------ }
{ Test: basic GetMem returns non-nil                                   }
{ ------------------------------------------------------------------ }
function Test_GetMem_Basic: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(64);
  AssertNotNull('GetMem(64) returns non-nil', P);
  _BlaiseFreeMem(P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: GetMem(0) returns nil                                          }
{ ------------------------------------------------------------------ }
function Test_GetMem_Zero: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(0);
  AssertNull('GetMem(0) returns nil', P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: allocated memory is writable and readable                      }
{ ------------------------------------------------------------------ }
function Test_ReadWrite: string;
var
  P: PChar;
begin
  P := PChar(_BlaiseGetMem(16));
  AssertNotNull('alloc for read/write', Pointer(P));
  P[0] := 65;
  P[1] := 66;
  P[2] := 67;
  P[3] := 0;
  AssertEquals('written byte 0', 65, Int32(P[0]));
  AssertEquals('written byte 1', 66, Int32(P[1]));
  AssertEquals('written byte 2', 67, Int32(P[2]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: multiple allocations return distinct pointers                  }
{ ------------------------------------------------------------------ }
function Test_Distinct_Pointers: string;
var
  A, B, C: Pointer;
begin
  A := _BlaiseGetMem(32);
  B := _BlaiseGetMem(32);
  C := _BlaiseGetMem(32);
  AssertNotNull('A non-nil', A);
  AssertNotNull('B non-nil', B);
  AssertNotNull('C non-nil', C);
  AssertDiffers('A <> B', A, B);
  AssertDiffers('A <> C', A, C);
  AssertDiffers('B <> C', B, C);
  _BlaiseFreeMem(C);
  _BlaiseFreeMem(B);
  _BlaiseFreeMem(A);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: FreeMem(nil) is safe (no-op)                                   }
{ ------------------------------------------------------------------ }
function Test_FreeMem_Nil: string;
begin
  _BlaiseFreeMem(nil);
  AssertPassed();
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: ReallocMem grows allocation                                    }
{ ------------------------------------------------------------------ }
function Test_ReallocMem_Grow: string;
var
  P: PChar;
begin
  P := PChar(_BlaiseGetMem(8));
  AssertNotNull('initial alloc', Pointer(P));
  P[0] := 72;
  P[1] := 73;
  P := PChar(_BlaiseReallocMem(Pointer(P), 64));
  AssertNotNull('realloc result', Pointer(P));
  AssertEquals('byte 0 preserved', 72, Int32(P[0]));
  AssertEquals('byte 1 preserved', 73, Int32(P[1]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: ReallocMem(nil, N) acts like GetMem                            }
{ ------------------------------------------------------------------ }
function Test_ReallocMem_FromNil: string;
var
  P: Pointer;
begin
  P := _BlaiseReallocMem(nil, 32);
  AssertNotNull('realloc from nil', P);
  _BlaiseFreeMem(P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: ReallocMem(P, 0) acts like FreeMem                             }
{ ------------------------------------------------------------------ }
function Test_ReallocMem_ToZero: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(32);
  AssertNotNull('initial alloc', P);
  P := _BlaiseReallocMem(P, 0);
  AssertNull('realloc to 0 returns nil', P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: small allocation (8 bytes) — exercises small-block path        }
{ ------------------------------------------------------------------ }
function Test_Small_Alloc: string;
var
  P: PChar;
begin
  P := PChar(_BlaiseGetMem(8));
  AssertNotNull('small alloc', Pointer(P));
  P[0] := 42;
  AssertEquals('small alloc writable', 42, Int32(P[0]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: large allocation (1 MB) — exercises mmap direct path           }
{ ------------------------------------------------------------------ }
function Test_Large_Alloc: string;
var
  P: PChar;
  Size: Int;
begin
  Size := 1024 * 1024;
  P := PChar(_BlaiseGetMem(Size));
  AssertNotNull('large alloc', Pointer(P));
  P[0] := 1;
  P[Size - 1] := 2;
  AssertEquals('large alloc first byte', 1, Int32(P[0]));
  AssertEquals('large alloc last byte', 2, Int32(P[Size - 1]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: alloc-free-alloc reuse (freelist)                               }
{ ------------------------------------------------------------------ }
function Test_Reuse_After_Free: string;
var
  A, B: Pointer;
begin
  A := _BlaiseGetMem(64);
  _BlaiseFreeMem(A);
  B := _BlaiseGetMem(64);
  AssertNotNull('reuse alloc', B);
  _BlaiseFreeMem(B);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: many small allocations (stress test)                            }
{ ------------------------------------------------------------------ }
function Test_Many_Small_Allocs: string;
const
  Count = 1000;
var
  I: Int;
  P: Pointer;
begin
  for I := 0 to Count - 1 do
  begin
    P := _BlaiseGetMem(24);
    AssertNotNull('alloc ' + IntToStr(I), P);
    _BlaiseFreeMem(P);
  end;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: various size classes                                            }
{ ------------------------------------------------------------------ }
function Test_Size_Classes: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(1);
  AssertNotNull('1 byte', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(16);
  AssertNotNull('16 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(128);
  AssertNotNull('128 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(1024);
  AssertNotNull('1024 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(4096);
  AssertNotNull('4096 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(65536);
  AssertNotNull('65536 bytes', P);
  _BlaiseFreeMem(P);

  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: alignment — returned pointer is 8-byte aligned                 }
{ ------------------------------------------------------------------ }
function Test_Alignment: string;
var
  P: Pointer;
  Addr: UInt;
begin
  P := _BlaiseGetMem(7);
  AssertNotNull('alloc for alignment test', P);
  Addr := UInt(P);
  AssertEquals('8-byte aligned', 0, Int32(Addr and 7));
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(1);
  AssertNotNull('alloc for alignment test (1 byte)', P);
  Addr := UInt(P);
  AssertEquals('8-byte aligned (1 byte)', 0, Int32(Addr and 7));
  _BlaiseFreeMem(P);

  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Helper: fill N bytes of P with a known pattern based on Seed         }
{ ------------------------------------------------------------------ }
procedure FillPattern(P: PChar; N: Int; Seed: Int);
var
  I, V: Int;
begin
  for I := 0 to N - 1 do
  begin
    V := (I + Seed) and $FF;
    P[I] := V;
  end;
end;

{ ------------------------------------------------------------------ }
{ Helper: check first N bytes of P match the pattern                   }
{ ------------------------------------------------------------------ }
function CheckPattern(P: PChar; N: Int; Seed: Int): Int;
var
  I: Int;
begin
  Result := -1;
  for I := 0 to N - 1 do
    if Int32(P[I]) <> ((I + Seed) and $FF) then
    begin
      Result := I;
      Exit;
    end;
end;

{ ------------------------------------------------------------------ }
{ Test: size-class boundaries — every boundary, +1 over, -1 under     }
{ ------------------------------------------------------------------ }
function Test_SizeClass_Boundaries: string;
var
  Classes: array[0..7] of Int32;
  I: Int;
  P: Pointer;
  Size: Int;
begin
  Classes[0] := 16; Classes[1] := 32; Classes[2] := 64; Classes[3] := 128;
  Classes[4] := 256; Classes[5] := 512; Classes[6] := 1024; Classes[7] := 2048;
  for I := 0 to 7 do
  begin
    Size := Classes[I];
    P := _BlaiseGetMem(Size);
    AssertNotNull('exact ' + IntToStr(Size), P);
    _BlaiseFreeMem(P);

    if Size > 1 then
    begin
      P := _BlaiseGetMem(Size - 1);
      AssertNotNull('exact-1 ' + IntToStr(Size - 1), P);
      _BlaiseFreeMem(P);
    end;

    P := _BlaiseGetMem(Size + 1);
    AssertNotNull('exact+1 ' + IntToStr(Size + 1), P);
    _BlaiseFreeMem(P);
  end;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc within same size class preserves bytes and is cheap    }
{ ------------------------------------------------------------------ }
function Test_Realloc_SameClass: string;
var
  P: PChar;
  Bad: Int;
begin
  P := PChar(_BlaiseGetMem(16));
  AssertNotNull('alloc 16', Pointer(P));
  FillPattern(P, 16, 11);
  P := PChar(_BlaiseReallocMem(Pointer(P), 12));
  AssertNotNull('shrink within class', Pointer(P));
  Bad := CheckPattern(P, 12, 11);
  AssertEquals('shrink preserves bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc shrink across classes preserves bytes                  }
{ ------------------------------------------------------------------ }
function Test_Realloc_Shrink: string;
var
  P: PChar;
  Bad: Int;
begin
  P := PChar(_BlaiseGetMem(256));
  AssertNotNull('alloc 256', Pointer(P));
  FillPattern(P, 256, 7);
  P := PChar(_BlaiseReallocMem(Pointer(P), 64));
  AssertNotNull('shrink to 64', Pointer(P));
  Bad := CheckPattern(P, 64, 7);
  AssertEquals('shrink preserves first 64 bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc growth across size classes preserves bytes             }
{ ------------------------------------------------------------------ }
function Test_Realloc_Grow_Steps: string;
var
  P: PChar;
  Bad: Int;
begin
  P := PChar(_BlaiseGetMem(16));
  AssertNotNull('alloc 16', Pointer(P));
  FillPattern(P, 16, 3);

  P := PChar(_BlaiseReallocMem(Pointer(P), 32));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 16->32', -1, Bad);

  P := PChar(_BlaiseReallocMem(Pointer(P), 64));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 32->64', -1, Bad);

  P := PChar(_BlaiseReallocMem(Pointer(P), 128));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 64->128', -1, Bad);

  P := PChar(_BlaiseReallocMem(Pointer(P), 256));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 128->256', -1, Bad);

  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc small -> large crosses LARGE_THRESHOLD                 }
{ ------------------------------------------------------------------ }
function Test_Realloc_SmallToLarge: string;
var
  P: PChar;
  Bad: Int;
begin
  P := PChar(_BlaiseGetMem(1024));
  AssertNotNull('alloc 1024', Pointer(P));
  FillPattern(P, 1024, 5);
  P := PChar(_BlaiseReallocMem(Pointer(P), 8192));
  AssertNotNull('grow to 8192', Pointer(P));
  Bad := CheckPattern(P, 1024, 5);
  AssertEquals('small->large preserves first 1024 bytes', -1, Bad);
  P[8191] := 99;
  AssertEquals('last byte writable', 99, Int32(P[8191]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc large -> small crosses LARGE_THRESHOLD downward        }
{ ------------------------------------------------------------------ }
function Test_Realloc_LargeToSmall: string;
var
  P: PChar;
  Bad: Int;
begin
  P := PChar(_BlaiseGetMem(8192));
  AssertNotNull('alloc 8192', Pointer(P));
  FillPattern(P, 8192, 9);
  P := PChar(_BlaiseReallocMem(Pointer(P), 128));
  AssertNotNull('shrink to 128', Pointer(P));
  Bad := CheckPattern(P, 128, 9);
  AssertEquals('large->small preserves first 128 bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc large -> large within same page count                  }
{ ------------------------------------------------------------------ }
function Test_Realloc_Large_SamePage: string;
var
  P: PChar;
  Bad: Int;
begin
  P := PChar(_BlaiseGetMem(3000));
  AssertNotNull('alloc 3000', Pointer(P));
  FillPattern(P, 3000, 13);
  P := PChar(_BlaiseReallocMem(Pointer(P), 3500));
  AssertNotNull('grow to 3500', Pointer(P));
  Bad := CheckPattern(P, 3000, 13);
  AssertEquals('large same-page preserves bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc large -> large across page boundary (mremap path)      }
{ ------------------------------------------------------------------ }
function Test_Realloc_Large_GrowPages: string;
var
  P: PChar;
  Bad: Int;
begin
  P := PChar(_BlaiseGetMem(4000));
  AssertNotNull('alloc 4000', Pointer(P));
  FillPattern(P, 4000, 17);
  P := PChar(_BlaiseReallocMem(Pointer(P), 16384));
  AssertNotNull('grow to 16384', Pointer(P));
  Bad := CheckPattern(P, 4000, 17);
  AssertEquals('large grow-pages preserves bytes', -1, Bad);
  P[16383] := 123;
  AssertEquals('last byte writable', 123, Int32(P[16383]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: LIFO cache reuses recently freed large block                   }
{ ------------------------------------------------------------------ }
function Test_Large_Cache_Reuse: string;
var
  A, B: Pointer;
begin
  A := _BlaiseGetMem(65536);
  AssertNotNull('first large', A);
  _BlaiseFreeMem(A);
  B := _BlaiseGetMem(65536);
  AssertNotNull('second large', B);
  AssertEquals('cache returns same block', UInt(A), UInt(B));
  _BlaiseFreeMem(B);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: large cache eviction beyond LARGE_CACHE_MAX                    }
{ ------------------------------------------------------------------ }
function Test_Large_Cache_Eviction: string;
const
  Count = 64;
var
  Blocks: array[0..63] of Pointer;
  I: Int;
begin
  for I := 0 to Count - 1 do
  begin
    Blocks[I] := _BlaiseGetMem(8192);
    AssertNotNull('alloc ' + IntToStr(I), Blocks[I]);
  end;
  for I := 0 to Count - 1 do
    _BlaiseFreeMem(Blocks[I]);
  for I := 0 to Count - 1 do
  begin
    Blocks[I] := _BlaiseGetMem(8192);
    AssertNotNull('realloc ' + IntToStr(I), Blocks[I]);
  end;
  for I := 0 to Count - 1 do
    _BlaiseFreeMem(Blocks[I]);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: many small allocs retained at once (no double-handout)         }
{ ------------------------------------------------------------------ }
function Test_Retain_Many_Small: string;
const
  Count = 200;
var
  Blocks: array[0..199] of Pointer;
  I, J, V: Int;
  P: PChar;
  Bad: Int;
begin
  for I := 0 to Count - 1 do
  begin
    P := PChar(_BlaiseGetMem(32));
    AssertNotNull('alloc ' + IntToStr(I), Pointer(P));
    for J := 0 to 31 do
    begin
      V := (J + I) and $FF;
      P[J] := V;
    end;
    Blocks[I] := Pointer(P);
  end;
  Bad := -1;
  for I := 0 to Count - 1 do
  begin
    P := PChar(Blocks[I]);
    for J := 0 to 31 do
      if Int32(P[J]) <> ((J + I) and $FF) then
      begin
        Bad := I * 100 + J;
        Break;
      end;
    if Bad <> -1 then Break;
  end;
  AssertEquals('all blocks intact', -1, Bad);
  for I := 0 to Count - 1 do
    _BlaiseFreeMem(Blocks[I]);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: interleaved small + large workload                             }
{ ------------------------------------------------------------------ }
function Test_Interleaved_Mixed: string;
const
  Count = 500;
var
  Small, Large: Pointer;
  I, Sz: Int;
begin
  for I := 0 to Count - 1 do
  begin
    Sz := 8 + (I mod 64);
    Small := _BlaiseGetMem(Sz);
    AssertNotNull('small ' + IntToStr(I), Small);
    Large := _BlaiseGetMem(4096 + (I mod 7) * 1024);
    AssertNotNull('large ' + IntToStr(I), Large);
    _BlaiseFreeMem(Small);
    _BlaiseFreeMem(Large);
  end;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc churn — repeated grow+shrink                           }
{ ------------------------------------------------------------------ }
function Test_Realloc_Churn: string;
const
  Count = 200;
var
  P: PChar;
  I, Bad: Int;
begin
  P := PChar(_BlaiseGetMem(16));
  FillPattern(P, 16, 42);
  for I := 1 to Count do
  begin
    P := PChar(_BlaiseReallocMem(Pointer(P), 16 + (I mod 256)));
    AssertNotNull('churn ' + IntToStr(I), Pointer(P));
    Bad := CheckPattern(P, 16, 42);
    AssertEquals('churn ' + IntToStr(I) + ' bytes intact', -1, Bad);
  end;
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: alignment for every size class                                 }
{ ------------------------------------------------------------------ }
function Test_Alignment_All_Classes: string;
var
  Classes: array[0..7] of Int32;
  I: Int;
  P: Pointer;
  Addr: UInt;
begin
  Classes[0] := 16; Classes[1] := 32; Classes[2] := 64; Classes[3] := 128;
  Classes[4] := 256; Classes[5] := 512; Classes[6] := 1024; Classes[7] := 2048;
  for I := 0 to 7 do
  begin
    P := _BlaiseGetMem(Classes[I]);
    AssertNotNull('class ' + IntToStr(Classes[I]), P);
    Addr := UInt(P);
    AssertEquals('class ' + IntToStr(Classes[I]) + ' aligned',
                 0, Int32(Addr and 7));
    _BlaiseFreeMem(P);
  end;
  P := _BlaiseGetMem(65536);
  AssertNotNull('large alloc', P);
  AssertEquals('large aligned', 0, Int32(UInt(P) and 7));
  _BlaiseFreeMem(P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Header layout (concurrent-allocator-design.adoc, §Data structures).  }
{ These pin the 16-byte small header, the 24-byte large header, the    }
{ cross-layout Flags punning invariant, and the arena back-pointer.    }
{ ------------------------------------------------------------------ }

{ Cross-layout invariant: IsLarge/GetAllocSize classify a block by
  reading Flags through the SMALL layout regardless of the block kind,
  so Flags must sit at the same offset from the user pointer in both
  layouts: small Ptr-16+4 = Ptr-12, large Ptr-24+12 = Ptr-12. }
function Test_FlagsOffset_Invariant: string;
var
  P: Pointer;
  FlagsP: ^Int32;
begin
  P := _BlaiseGetMem(64);
  AssertNotNull('small alloc', P);
  FlagsP := Pointer(UInt(P) - 12);
  AssertEquals('small block Flags (FLAG_SMALL) at Ptr-12', 0, FlagsP^);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(8192);
  AssertNotNull('large alloc', P);
  FlagsP := Pointer(UInt(P) - 12);
  AssertEquals('large block Flags (FLAG_LARGE) at Ptr-12', 1, FlagsP^);
  _BlaiseFreeMem(P);
  Result := '';
end;

{ The small header carries the owning-arena back-pointer at offset 8
  (AllocSize:4, Flags:4, Arena:8) — i.e. at Ptr-8.  The arena record
  sits at the start of its 64 KiB mmap region, so the block must lie
  inside [Arena, Arena+65536). }
function Test_ArenaBackPointer: string;
var
  P: Pointer;
  ArenaP: ^Pointer;
  Arena: Pointer;
begin
  P := _BlaiseGetMem(48);
  AssertNotNull('small alloc', P);
  ArenaP := Pointer(UInt(P) - 8);
  Arena := ArenaP^;
  AssertNotNull('back-pointer non-nil', Arena);
  AssertTrue('block above arena base', UInt(P) > UInt(Arena));
  AssertTrue('block inside arena', UInt(P) < UInt(Arena) + 65536);
  _BlaiseFreeMem(P);
  Result := '';
end;

{ The back-pointer must survive freelist recycling: a block freed and
  reallocated in the same class keeps a valid arena back-pointer. }
function Test_ArenaBackPointer_AfterReuse: string;
var
  A, B: Pointer;
  ArenaP: ^Pointer;
  Arena: Pointer;
begin
  A := _BlaiseGetMem(32);
  AssertNotNull('first alloc', A);
  _BlaiseFreeMem(A);
  B := _BlaiseGetMem(32);
  AssertNotNull('recycled alloc', B);
  AssertEquals('freelist recycled the block', UInt(A), UInt(B));
  ArenaP := Pointer(UInt(B) - 8);
  Arena := ArenaP^;
  AssertNotNull('recycled back-pointer non-nil', Arena);
  AssertTrue('recycled block above arena base', UInt(B) > UInt(Arena));
  AssertTrue('recycled block inside arena', UInt(B) < UInt(Arena) + 65536);
  _BlaiseFreeMem(B);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Large-block owner tid (phase 4 — the munmap-on-foreign-free path).   }
{ TLargeHeader = TotalMapped:8, AllocSize:8, Pad:4, Flags:4,          }
{ OwnerTid:8 = 32 bytes; the user pointer is Base+32, so OwnerTid sits }
{ at Ptr-8.                                                            }
{ Every large-alloc path must stamp the allocating thread's tid so     }
{ LargeFreeMem can distinguish a local free (cache) from a foreign     }
{ free (munmap).                                                       }
{ ------------------------------------------------------------------ }

function Test_Large_OwnerTid_Set: string;
var
  P, Q: Pointer;
  TidP, TidQ: ^Int64;
begin
  P := _BlaiseGetMem(8192);
  AssertNotNull('large alloc', P);
  TidP := Pointer(UInt(P) - 8);
  AssertTrue('fresh large block has a non-zero owner tid', TidP^ <> 0);

  Q := _BlaiseGetMem(8192);
  AssertNotNull('second large alloc', Q);
  TidQ := Pointer(UInt(Q) - 8);
  AssertTrue('second block has a non-zero owner tid', TidQ^ <> 0);
  AssertEquals('same thread stamps the same owner tid', TidP^, TidQ^);

  _BlaiseFreeMem(Q);
  _BlaiseFreeMem(P);
  Result := '';
end;

function Test_Large_OwnerTid_AfterCacheReuse: string;
var
  A, B: Pointer;
  TidP: ^Int64;
begin
  { A local free caches the block; the cache-reuse alloc path must
    re-stamp OwnerTid (the header bytes were recycled as a free node). }
  A := _BlaiseGetMem(16384);
  AssertNotNull('first large', A);
  _BlaiseFreeMem(A);
  B := _BlaiseGetMem(16384);
  AssertNotNull('cache-reuse large', B);
  AssertEquals('cache returned the same block', UInt(A), UInt(B));
  TidP := Pointer(UInt(B) - 8);
  AssertTrue('cache-reused block has a non-zero owner tid', TidP^ <> 0);
  _BlaiseFreeMem(B);
  Result := '';
end;

function Test_Large_OwnerTid_AfterRealloc: string;
var
  P: Pointer;
  TidP: ^Int64;
begin
  { The large->large mremap realloc path must also stamp OwnerTid. }
  P := _BlaiseGetMem(4096);
  AssertNotNull('alloc 4096', P);
  P := _BlaiseReallocMem(P, 65536);
  AssertNotNull('realloc to 65536', P);
  TidP := Pointer(UInt(P) - 8);
  AssertTrue('realloc-grown block has a non-zero owner tid', TidP^ <> 0);
  _BlaiseFreeMem(P);
  Result := '';
end;

function Test_Large_LocalFree_StillCaches: string;
var
  A, B: Pointer;
begin
  { The owner-tid test must not break the local LIFO cache: a local
    free followed by a same-size alloc must return the same mapping. }
  A := _BlaiseGetMem(32768);
  AssertNotNull('alloc', A);
  _BlaiseFreeMem(A);
  B := _BlaiseGetMem(32768);
  AssertEquals('local free cached and reused the block',
               UInt(A), UInt(B));
  _BlaiseFreeMem(B);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Remote-free queue (phase 3) — single-threaded synthetic drain.       }
{ Forge a "foreign" free by planting a remote node on the owning       }
{ arena's RemoteHead directly (what RemoteFreePush does from another   }
{ thread), then allocate until the owner drains and recycles it.       }
{ Layout pinned here: TArena.OwnerTid at +24, RemoteHead at +32;       }
{ TRemoteNode.Next at +0, SizeClass at +8.                             }
{ ------------------------------------------------------------------ }

function Test_RemoteQueue_DrainRecycles: string;
const
  Sz = 2000;   { class 7 (2048) — biggest class, fills an arena fastest }
var
  P, Q, Arena: Pointer;
  ArenaP: ^Pointer;
  RemoteHeadP: ^Pointer;
  OwnerTidP: ^Int64;
  NodeNextP: ^Pointer;
  NodeClassP: ^Int32;
  I: Int;
  Found: Boolean;
begin
  P := _BlaiseGetMem(Sz);
  AssertNotNull('alloc', P);
  ArenaP := Pointer(UInt(P) - 8);
  Arena := ArenaP^;
  AssertNotNull('arena back-pointer', Arena);

  OwnerTidP := Pointer(UInt(Arena) + 24);
  AssertTrue('arena has a non-zero owner tid', OwnerTidP^ <> 0);

  { Forge the remote free: node in the block's user bytes, planted on
    the arena's RemoteHead.  (Single-threaded, so a plain store stands
    in for the producer's CAS.) }
  NodeNextP := Pointer(P);
  NodeNextP^ := nil;
  NodeClassP := Pointer(UInt(P) + 8);
  NodeClassP^ := 7;
  RemoteHeadP := Pointer(UInt(Arena) + 32);
  AssertNull('remote queue empty before forge', RemoteHeadP^);
  RemoteHeadP^ := P;

  { The owner must reclaim P: either the empty-freelist drain of the
    head arena or the drain-all on arena exhaustion files it back onto
    FreeLists[7], from where allocation returns it by pointer identity.
    Class 7 blocks are 2048+16 bytes, so well under 64 iterations force
    an arena refill even from a fresh arena. }
  Found := False;
  for I := 0 to 63 do
  begin
    Q := _BlaiseGetMem(Sz);
    AssertNotNull('drain-loop alloc ' + IntToStr(I), Q);
    if Q = P then
    begin
      Found := True;
      Break;
    end;
  end;
  AssertTrue('forged remote free was drained and recycled', Found);
  AssertNull('remote queue empty after drain', RemoteHeadP^);
  _BlaiseFreeMem(P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Atomic primitives (runtime.atomic) — single-threaded semantics.      }
{ These prove the asm bodies and the Boolean/pointer ABI before any    }
{ concurrent use (concurrent-allocator-design.adoc, §Testing).         }
{ ------------------------------------------------------------------ }

function Test_AtomicCASPtr_Success: string;
var
  Slot: Pointer;
  A, B: Int;
  Ok: Boolean;
begin
  Slot := @A;
  Ok := _AtomicCASPtr(@Slot, @A, @B);
  AssertTrue('CAS with matching expected succeeds', Ok);
  AssertEquals('CAS installed the new value', Pointer(@B), Slot);
  Result := '';
end;

function Test_AtomicCASPtr_Failure: string;
var
  Slot: Pointer;
  A, B, C: Int;
  Ok: Boolean;
begin
  Slot := @A;
  Ok := _AtomicCASPtr(@Slot, @C, @B);
  AssertFalse('CAS with mismatched expected fails', Ok);
  AssertEquals('failed CAS leaves the value unchanged', Pointer(@A), Slot);
  Result := '';
end;

function Test_AtomicCASPtr_NilTransitions: string;
var
  Slot: Pointer;
  A: Int;
  Ok: Boolean;
begin
  Slot := nil;
  Ok := _AtomicCASPtr(@Slot, nil, @A);
  AssertTrue('CAS nil -> ptr succeeds', Ok);
  AssertEquals('slot now holds ptr', Pointer(@A), Slot);
  Ok := _AtomicCASPtr(@Slot, @A, nil);
  AssertTrue('CAS ptr -> nil succeeds', Ok);
  AssertNull('slot back to nil', Slot);
  Result := '';
end;

function Test_AtomicXchgPtr: string;
var
  Slot: Pointer;
  A, B: Int;
  Old: Pointer;
begin
  Slot := @A;
  Old := _AtomicXchgPtr(@Slot, @B);
  AssertEquals('xchg returns the previous value', Pointer(@A), Old);
  AssertEquals('xchg installed the new value', Pointer(@B), Slot);
  Old := _AtomicXchgPtr(@Slot, nil);
  AssertEquals('second xchg returns prior', Pointer(@B), Old);
  AssertNull('slot drained to nil', Slot);
  Result := '';
end;

function Test_AtomicAddInt64: string;
var
  V: Int64;
  Old: Int64;
begin
  V := 10;
  Old := _AtomicAddInt64(@V, 32);
  AssertEquals('fetch-add returns previous', Int64(10), Old);
  AssertEquals('fetch-add applied delta', Int64(42), V);
  Old := _AtomicAddInt64(@V, -42);
  AssertEquals('negative delta returns previous', Int64(42), Old);
  AssertEquals('negative delta applied', Int64(0), V);
  Result := '';
end;

function Test_AtomicAddInt64_Wide: string;
var
  V: Int64;
  Old: Int64;
begin
  { A value and delta that both exceed 32 bits — proves the operation is a
    true 64-bit xadd, not a 32-bit one on the low word. }
  V := $100000000;
  Old := _AtomicAddInt64(@V, $200000004);
  AssertEquals('wide fetch-add returns previous', Int64($100000000), Old);
  AssertEquals('wide fetch-add applied', Int64($300000004), V);
  Result := '';
end;

begin
  AddSuite('blaise_mem', nil);
  AddTest('GetMem_Basic',           @Test_GetMem_Basic,           'blaise_mem');
  AddTest('GetMem_Zero',            @Test_GetMem_Zero,            'blaise_mem');
  AddTest('ReadWrite',              @Test_ReadWrite,              'blaise_mem');
  AddTest('Distinct_Pointers',      @Test_Distinct_Pointers,      'blaise_mem');
  AddTest('FreeMem_Nil',            @Test_FreeMem_Nil,            'blaise_mem');
  AddTest('ReallocMem_Grow',        @Test_ReallocMem_Grow,        'blaise_mem');
  AddTest('ReallocMem_FromNil',     @Test_ReallocMem_FromNil,     'blaise_mem');
  AddTest('ReallocMem_ToZero',      @Test_ReallocMem_ToZero,      'blaise_mem');
  AddTest('Small_Alloc',            @Test_Small_Alloc,            'blaise_mem');
  AddTest('Large_Alloc',            @Test_Large_Alloc,            'blaise_mem');
  AddTest('Reuse_After_Free',       @Test_Reuse_After_Free,       'blaise_mem');
  AddTest('Many_Small_Allocs',      @Test_Many_Small_Allocs,      'blaise_mem');
  AddTest('Size_Classes',           @Test_Size_Classes,           'blaise_mem');
  AddTest('Alignment',              @Test_Alignment,              'blaise_mem');
  AddTest('SizeClass_Boundaries',   @Test_SizeClass_Boundaries,   'blaise_mem');
  AddTest('Realloc_SameClass',      @Test_Realloc_SameClass,      'blaise_mem');
  AddTest('Realloc_Shrink',         @Test_Realloc_Shrink,         'blaise_mem');
  AddTest('Realloc_Grow_Steps',     @Test_Realloc_Grow_Steps,     'blaise_mem');
  AddTest('Realloc_SmallToLarge',   @Test_Realloc_SmallToLarge,   'blaise_mem');
  AddTest('Realloc_LargeToSmall',   @Test_Realloc_LargeToSmall,   'blaise_mem');
  AddTest('Realloc_Large_SamePage', @Test_Realloc_Large_SamePage, 'blaise_mem');
  AddTest('Realloc_Large_GrowPages',@Test_Realloc_Large_GrowPages,'blaise_mem');
  AddTest('Large_Cache_Reuse',      @Test_Large_Cache_Reuse,      'blaise_mem');
  AddTest('Large_Cache_Eviction',   @Test_Large_Cache_Eviction,   'blaise_mem');
  AddTest('Retain_Many_Small',      @Test_Retain_Many_Small,      'blaise_mem');
  AddTest('Interleaved_Mixed',      @Test_Interleaved_Mixed,      'blaise_mem');
  AddTest('Realloc_Churn',          @Test_Realloc_Churn,          'blaise_mem');
  AddTest('Alignment_All_Classes',  @Test_Alignment_All_Classes,  'blaise_mem');

  AddTest('FlagsOffset_Invariant', @Test_FlagsOffset_Invariant, 'blaise_mem');
  AddTest('ArenaBackPointer', @Test_ArenaBackPointer, 'blaise_mem');
  AddTest('ArenaBackPointer_AfterReuse', @Test_ArenaBackPointer_AfterReuse, 'blaise_mem');
  AddTest('RemoteQueue_DrainRecycles', @Test_RemoteQueue_DrainRecycles, 'blaise_mem');
  AddTest('Large_OwnerTid_Set', @Test_Large_OwnerTid_Set, 'blaise_mem');
  AddTest('Large_OwnerTid_AfterCacheReuse', @Test_Large_OwnerTid_AfterCacheReuse, 'blaise_mem');
  AddTest('Large_OwnerTid_AfterRealloc', @Test_Large_OwnerTid_AfterRealloc, 'blaise_mem');
  AddTest('Large_LocalFree_StillCaches', @Test_Large_LocalFree_StillCaches, 'blaise_mem');

  AddSuite('blaise_atomic', nil);
  AddTest('AtomicCASPtr_Success', @Test_AtomicCASPtr_Success, 'blaise_atomic');
  AddTest('AtomicCASPtr_Failure', @Test_AtomicCASPtr_Failure, 'blaise_atomic');
  AddTest('AtomicCASPtr_NilTransitions', @Test_AtomicCASPtr_NilTransitions, 'blaise_atomic');
  AddTest('AtomicXchgPtr', @Test_AtomicXchgPtr, 'blaise_atomic');
  AddTest('AtomicAddInt64', @Test_AtomicAddInt64, 'blaise_atomic');
  AddTest('AtomicAddInt64_Wide', @Test_AtomicAddInt64_Wide, 'blaise_atomic');
  RunAllSysTests();
end.
