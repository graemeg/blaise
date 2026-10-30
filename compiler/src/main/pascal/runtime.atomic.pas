{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.atomic;

// Atomic 32-bit add/sub primitives used by ARC reference counting.
//
// Inline-assembler port of runtime/src/main/asm/blaise_atomic_x86_64.s — the
// bodies are now `asm … end` routines in this Pascal unit so the RTL builds
// with Blaise's own internal assembler and needs no hand-written .s file
// (docs/inline-asm-design.adoc, §"Migration of the .s files").
//
// Each returns the PREVIOUS value at Ptr (xadd semantics).  System V AMD64:
// arg1 Ptr -> %rdi, arg2 Delta -> %esi; the 32-bit result is returned in %eax.
// `nostackframe` lets the asm body own the frame so the registers hold the
// raw incoming arguments.

interface

{ Ptr addresses a 32-bit integer.  Typed as Pointer (not a `PInteger` alias) so
  this unit does not export a type name that collides with the same alias in
  other RTL units when they are compiled together (e.g. blaise_arc's PInteger).
  The body reads/writes through %rdi regardless of the Pascal pointer type. }
function _AtomicAddInt32(Ptr: Pointer; Delta: Int32): Int32;
function _AtomicSubInt32(Ptr: Pointer; Delta: Int32): Int32;

{ Pointer-width primitives for the migration-safe allocator's remote-free
  queue (docs/concurrent-allocator-design.adoc, §"The new atomic primitives").
  All operate on a 64-bit word at Ptr^. }

{ Atomic compare-and-swap of a pointer-sized word.
  If Ptr^ = Expected, set Ptr^ := NewVal and return True; else return False.
  Ptr -> %rdi, Expected -> %rsi, NewVal -> %rdx. }
function _AtomicCASPtr(Ptr: Pointer; Expected, NewVal: Pointer): Boolean;

{ Atomic exchange of a pointer-sized word.
  Store NewVal into Ptr^ and return the previous value.
  Ptr -> %rdi, NewVal -> %rsi. }
function _AtomicXchgPtr(Ptr: Pointer; NewVal: Pointer): Pointer;

{ Atomic fetch-and-add of a 64-bit word; return the PREVIOUS value.
  Ptr -> %rdi, Delta -> %rsi. }
function _AtomicAddInt64(Ptr: Pointer; Delta: Int64): Int64;

implementation

{$IFDEF CPUARM64}
{ AArch64 bodies — LSE atomics (every Apple Silicon core implements LSE;
  a load/store-exclusive fallback can land if a pre-8.1 arm64 target ever
  does).  AAPCS64: arg1 -> x0, arg2 -> x1, arg3 -> x2.  ldaddal/swpal/
  casal are full acquire+release barriers, matching x86's locked forms. }

{ return *Ptr (old); *Ptr += Delta — atomically. }
function _AtomicAddInt32(Ptr: Pointer; Delta: Int32): Int32;
  assembler; nostackframe;
asm
    ldaddal w1, w2, [x0]
    mov w0, w2
    ret
end;

{ return *Ptr (old); *Ptr -= Delta — atomically (ldaddal of the negation). }
function _AtomicSubInt32(Ptr: Pointer; Delta: Int32): Int32;
  assembler; nostackframe;
asm
    neg w1, w1
    ldaddal w1, w2, [x0]
    mov w0, w2
    ret
end;

{ casal compares [x0] with x1 and stores x2 on match; x1 receives the OLD
  value either way, so success = (old = expected-as-saved). }
function _AtomicCASPtr(Ptr: Pointer; Expected, NewVal: Pointer): Boolean;
  assembler; nostackframe;
asm
    mov x9, x1
    casal x1, x2, [x0]
    cmp x1, x9
    cset x0, eq
    ret
end;

{ swpal swaps x1 into [x0] and returns the old value — a full barrier, so
  the drain's claim gets its acquire semantics for free. }
function _AtomicXchgPtr(Ptr: Pointer; NewVal: Pointer): Pointer;
  assembler; nostackframe;
asm
    swpal x1, x9, [x0]
    mov x0, x9
    ret
end;

{ 64-bit sibling of _AtomicAddInt32 — return *Ptr (old); *Ptr += Delta. }
function _AtomicAddInt64(Ptr: Pointer; Delta: Int64): Int64;
  assembler; nostackframe;
asm
    ldaddal x1, x9, [x0]
    mov x0, x9
    ret
end;
{$ELSE}
{ return *Ptr (old); *Ptr += Delta — atomically. }
function _AtomicAddInt32(Ptr: Pointer; Delta: Int32): Int32;
  assembler; nostackframe;
asm
    movl %esi, %eax
    lock xaddl %eax, (%rdi)
    ret
end;

{ return *Ptr (old); *Ptr -= Delta — atomically (xadd of the negated delta). }
function _AtomicSubInt32(Ptr: Pointer; Delta: Int32): Int32;
  assembler; nostackframe;
asm
    negl %esi
    movl %esi, %eax
    lock xaddl %eax, (%rdi)
    ret
end;

{ cmpxchg sets ZF on success; SETE -> AL gives the Boolean result.
  `lock cmpxchgq %rdx, (%rdi)`:
     if (%rdi) = %rax  then (%rdi) := %rdx, ZF := 1
     else %rax := (%rdi),                   ZF := 0
  Expected is loaded into %rax first (cmpxchg's implicit comparand).
  `lock cmpxchg` is a full barrier on x86-64, so the publish has release
  semantics for free (the remote-free push relies on this). }
function _AtomicCASPtr(Ptr: Pointer; Expected, NewVal: Pointer): Boolean;
  assembler; nostackframe;
asm
    movq %rsi, %rax
    lock cmpxchgq %rdx, (%rdi)
    sete %al
    movzbl %al, %eax
    ret
end;

{ xchg with a memory operand carries an implicit LOCK and is a full barrier
  (acquire semantics for free — the drain's claim relies on this).  It
  atomically swaps %rsi with (%rdi); the old value ends up in %rsi, which
  is moved to %rax to return it. }
function _AtomicXchgPtr(Ptr: Pointer; NewVal: Pointer): Pointer;
  assembler; nostackframe;
asm
    xchgq %rsi, (%rdi)
    movq %rsi, %rax
    ret
end;

{ 64-bit sibling of _AtomicAddInt32 — return *Ptr (old); *Ptr += Delta. }
function _AtomicAddInt64(Ptr: Pointer; Delta: Int64): Int64;
  assembler; nostackframe;
asm
    movq %rsi, %rax
    lock xaddq %rax, (%rdi)
    ret
end;
{$ENDIF}

end.
