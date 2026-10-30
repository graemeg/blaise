{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.setjmp;

// setjmp/longjmp for the exception runtime (try/except, try/finally).
//
// Inline-assembler port of runtime/src/main/asm/blaise_setjmp_x86_64.s — the
// bodies move into `asm … end` routines so the RTL needs no hand-written .s
// (docs/inline-asm-design.adoc, §"Migration of the .s files").
//
// The jmp_buf is a 64-byte block: callee-saved regs rbx/rbp/r12..r15 at
// 0/8/16..40, the caller's RSP at 48, and the return address at 56.
//
// System V AMD64 arg registers: Buf -> %rdi, Val -> %esi.  Both routines own
// their frame (`nostackframe`); _blaise_setjmp captures the return address off
// the stack and _blaise_longjmp restores RSP and jumps through the saved
// return address, so a compiler-generated prologue must not intervene.

interface

function  _blaise_setjmp(Buf: Pointer): Int32;
procedure _blaise_longjmp(Buf: Pointer; Val: Int32);

implementation

{$IFDEF CPUARM64}
{ AArch64 bodies.  jmp_buf layout (168 bytes used; the RTL contract
  reserves 512 in every exception frame, so there is ample headroom):
  x19..x28 at 0..72, x29 (fp) at 80, x30 (lr) at 88 (doubles as the
  resume address), sp at 96, d8..d15 at 104..160. }

{ Save the machine context into Buf; returns 0 on the direct call. }
function _blaise_setjmp(Buf: Pointer): Int32; assembler; nostackframe;
asm
    stp x19, x20, [x0]
    stp x21, x22, [x0, #16]
    stp x23, x24, [x0, #32]
    stp x25, x26, [x0, #48]
    stp x27, x28, [x0, #64]
    stp x29, x30, [x0, #80]
    mov x9, sp
    str x9, [x0, #96]
    str d8, [x0, #104]
    str d9, [x0, #112]
    str d10, [x0, #120]
    str d11, [x0, #128]
    str d12, [x0, #136]
    str d13, [x0, #144]
    str d14, [x0, #152]
    str d15, [x0, #160]
    movz x0, #0
    ret
end;

{ Restore the context saved in Buf and resume there, returning Val (or 1
  if Val is 0, mirroring C longjmp).  The final ret goes through the
  RESTORED x30 — control resumes just after the original setjmp call. }
procedure _blaise_longjmp(Buf: Pointer; Val: Int32); assembler; nostackframe;
asm
    ldp x19, x20, [x0]
    ldp x21, x22, [x0, #16]
    ldp x23, x24, [x0, #32]
    ldp x25, x26, [x0, #48]
    ldp x27, x28, [x0, #64]
    ldp x29, x30, [x0, #80]
    ldr x9, [x0, #96]
    mov sp, x9
    ldr d8, [x0, #104]
    ldr d9, [x0, #112]
    ldr d10, [x0, #120]
    ldr d11, [x0, #128]
    ldr d12, [x0, #136]
    ldr d13, [x0, #144]
    ldr d14, [x0, #152]
    ldr d15, [x0, #160]
    mov x0, x1
    cbnz x0, .Llj_nonzero
    movz x0, #1
.Llj_nonzero:
    ret
end;
{$ELSE}
{ Save the machine context into Buf; returns 0 on the direct call. }
function _blaise_setjmp(Buf: Pointer): Int32; assembler; nostackframe;
asm
    mov  %rbx,    (%rdi)
    mov  %rbp,   8(%rdi)
    mov  %r12,  16(%rdi)
    mov  %r13,  24(%rdi)
    mov  %r14,  32(%rdi)
    mov  %r15,  40(%rdi)
    lea  8(%rsp), %rax
    mov  %rax,  48(%rdi)
    mov  (%rsp), %rax
    mov  %rax,  56(%rdi)
    xor  %eax, %eax
    ret
end;

{ Restore the context saved in Buf and resume there, returning Val (or 1 if
  Val is 0, mirroring C longjmp). }
procedure _blaise_longjmp(Buf: Pointer; Val: Int32); assembler; nostackframe;
asm
    mov  %esi, %eax
    test %eax, %eax
    jnz  .Llj_nonzero
    inc  %eax
.Llj_nonzero:
    mov    (%rdi), %rbx
    mov   8(%rdi), %rbp
    mov  16(%rdi), %r12
    mov  24(%rdi), %r13
    mov  32(%rdi), %r14
    mov  40(%rdi), %r15
    mov  48(%rdi), %rsp
    jmp *56(%rdi)
end;
{$ENDIF}

end.
