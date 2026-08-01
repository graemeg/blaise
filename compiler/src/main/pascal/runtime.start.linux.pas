{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.start.linux;

// Program entry point for a DYNAMIC (libc-linked) Linux binary
// (x86_64, System V ABI, glibc-compatible).
//
// Per-OS because the hand-off differs: glibc exports __libc_start_main and
// expects the entry to marshal argc/argv/envp into it, whereas FreeBSD libc
// exports no such symbol and its start (runtime.start.freebsd) walks the
// initial process stack itself.  Selected at link time by BuildRTLUnitList;
// the static profile uses runtime.start.static.<os> instead.
//
// Inline-assembler port of runtime/src/main/asm/blaise_start_x86_64.s — _start
// is now an `asm … end` routine so the RTL needs no hand-written .s
// (docs/inline-asm-design.adoc, §"Migration of the .s files").
//
// This replaces the system Scrt1.o so the internal linker needs no
// gcc-provided startup object (issue #142).  The linker uses '_start' as the
// ELF entry point; an unmangled unit-level routine named _start emits exactly
// that symbol.
//
// On entry the kernel hands us the initial process stack:
//   (%rsp)   argc      8(%rsp) argv[0] ...  then NULL, envp, auxv
// and %rdx holds rtld_fini for PIE images.  We marshal these into the args
// __libc_start_main(main, argc, argv, init=NULL, fini=NULL, rtld_fini,
// stack_end) expects; glibc runs the init array, calls main(argc, argv, envp),
// then exit(main's return).  nostackframe: the body owns the whole frame.

interface

procedure _start;

implementation

procedure _start; assembler; nostackframe;
asm
    endbr64
    xor  %ebp, %ebp
    mov  %rdx, %r9
    pop  %rsi
    mov  %rsp, %rdx
    and  $0xfffffffffffffff0, %rsp
    push %rax
    push %rsp
    xor  %r8d, %r8d
    xor  %ecx, %ecx
    lea  main(%rip), %rdi
    call __libc_start_main@PLT
    hlt
end;

end.
