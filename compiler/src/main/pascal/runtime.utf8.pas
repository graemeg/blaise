{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.utf8;

// UTF-8 code-point counter — SIMD-accelerated (AVX2 with an SSE2 fallback and
// a scalar tail), with a one-time CPUID probe for AVX2.
//
// Inline-assembler port of runtime/src/main/asm/blaise_utf8_x86_64.s — the body
// (and its threshold/flag data) move into an `asm … end` routine so the RTL
// builds with Blaise's own internal assembler and needs no hand-written .s
// (docs/inline-asm-design.adoc, §"Migration of the .s files").  This was the
// last .s file; with it gone the RTL is pure Pascal + inline asm.
//
// Counts UTF-8 code points by counting bytes that are NOT continuation bytes
// (a byte is a continuation byte iff its top two bits are 10, i.e. signed value
// in [-128,-65]); the SIMD paths compare against the threshold -65 (0xBF).
//
// System V AMD64: Data -> %rdi, Len -> %esi; result (count) in %eax.

interface

function _Utf8CountCodePoints(Data: Pointer; Len: Int): Int;

implementation

{$IFDEF CPUARM64}
{ Portable body for arm64: count the bytes that are NOT UTF-8
  continuation bytes (top two bits <> 10).  The x86-64 body below is a
  SIMD-optimised version of exactly this loop; a NEON port can follow
  once the macOS bring-up settles. }
function _Utf8CountCodePoints(Data: Pointer; Len: Int): Int;
var
  P: ^Byte;
  I, N: Int;
begin
  N := 0;
  for I := 0 to Len - 1 do
  begin
    P := Pointer(PChar(Data) + I);
    if (P^ and $C0) <> $80 then
      N := N + 1;
  end;
  Result := N;
end;
{$ELSE}
function _Utf8CountCodePoints(Data: Pointer; Len: Int): Int;
  assembler; nostackframe;
asm
    testl %esi, %esi
    jle .Lreturn_zero
    movl %esi, %ecx
    xorl %eax, %eax
    xorl %edx, %edx
    cmpl $0, .Lavx2_checked(%rip)
    jne .Lavx2_known
    call .Lcheck_avx2
    xorl %eax, %eax
.Lavx2_known:
    cmpl $0, .Lavx2_flag(%rip)
    je .Lsse2_entry
    cmpl $32, %ecx
    jb .Lsse2_entry
    vpcmpeqb %ymm2, %ymm2, %ymm2
    vpsrlw $1, %ymm2, %ymm2
    vpaddw %ymm2, %ymm2, %ymm1
    vpcmpeqb %ymm2, %ymm2, %ymm2
    vpsllw $7, %ymm2, %ymm1
    vpcmpeqb %ymm1, %ymm1, %ymm1
    vmovdqa .Lthreshold_avx(%rip), %ymm1
    vpxor %ymm3, %ymm3, %ymm3
.Lavx2_loop:
    vmovdqu (%rdi, %rdx), %ymm0
    vpcmpgtb %ymm1, %ymm0, %ymm2
    vpabsb %ymm2, %ymm2
    vpaddb %ymm2, %ymm3, %ymm3
    addl $32, %edx
    subl $32, %ecx
    cmpl $32, %ecx
    jge .Lavx2_loop
    vpxor %ymm4, %ymm4, %ymm4
    vpsadbw %ymm4, %ymm3, %ymm3
    vextracti128 $1, %ymm3, %xmm4
    vpaddq %xmm4, %xmm3, %xmm3
    vpshufd $0x0E, %xmm3, %xmm4
    vpaddq %xmm4, %xmm3, %xmm3
    vmovd %xmm3, %r8d
    addl %r8d, %eax
    vzeroupper
    jmp .Lsse2_entry
.Lsse2_entry:
    cmpl $16, %ecx
    jb .Lscalar_entry
    movdqa .Lthreshold_sse(%rip), %xmm1
    pxor %xmm3, %xmm3
.Lsse2_loop:
    movdqu (%rdi, %rdx), %xmm0
    movdqa %xmm0, %xmm2
    pcmpgtb %xmm1, %xmm2
    pabsb %xmm2, %xmm2
    paddb %xmm2, %xmm3
    addl $16, %edx
    subl $16, %ecx
    cmpl $16, %ecx
    jge .Lsse2_loop
    pxor %xmm4, %xmm4
    psadbw %xmm4, %xmm3
    movd %xmm3, %r8d
    pshufd $0x0E, %xmm3, %xmm3
    movd %xmm3, %r9d
    addl %r8d, %eax
    addl %r9d, %eax
.Lscalar_entry:
    testl %ecx, %ecx
    jle .Lreturn
.Lscalar_loop:
    movzbl (%rdi, %rdx), %r8d
    movl %r8d, %r9d
    andl $0xC0, %r9d
    cmpl $0x80, %r9d
    setne %r9b
    movzbl %r9b, %r9d
    addl %r9d, %eax
    incl %edx
    decl %ecx
    jnz .Lscalar_loop
.Lreturn:
    ret
.Lreturn_zero:
    xorl %eax, %eax
    ret
.Lcheck_avx2:
    pushq %rbx
    pushq %rcx
    pushq %rdx
    movl $7, %eax
    xorl %ecx, %ecx
    cpuid
    testl $0x20, %ebx
    setne %al
    movzbl %al, %eax
    movl %eax, .Lavx2_flag(%rip)
    movl $1, .Lavx2_checked(%rip)
    popq %rdx
    popq %rcx
    popq %rbx
    ret
.section .rodata
.balign 32
.Lthreshold_avx:
    .fill 32, 1, 0xBF
.balign 16
.Lthreshold_sse:
    .fill 16, 1, 0xBF
.section .data
.Lavx2_checked:
    .long 0
.Lavx2_flag:
    .long 0
end;
{$ENDIF}

end.
