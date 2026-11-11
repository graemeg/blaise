# Windows milestone M2 stand-in runtime.  The Windows runtime arrives in M3;
# until then the M2 program under test (m2calls.pas) links against this
# instead: the PE entry point, and do-nothing versions of the runtime
# routines every program's main calls.  Everything here except _start uses
# the internal (System V) convention, as the real runtime will.
        .text
        .globl _start
# The loader calls _start with RSP 8 mod 16; 40 bytes realign it and give
# ExitProcess its 32 bytes of home space.
_start:
        subq $40, %rsp
        xorl %edi, %edi
        xorl %esi, %esi
        call main
        movl %eax, %ecx
        call ExitProcess
        hlt

        .globl _SetArgs
_SetArgs:
        ret
        .globl _BlaiseInit
_BlaiseInit:
        ret
        .globl _UnwindInit
_UnwindInit:
        ret
        .globl rtl.platform.layout.windows_init
rtl.platform.layout.windows_init:
        ret
        .globl _ThreadVarsRelease
_ThreadVarsRelease:
        ret
        .globl TObject_Destroy
TObject_Destroy:
        ret
        .globl TObject_ToString
TObject_ToString:
        xorl %eax, %eax
        ret

# memset(dest, byte, count), System V: the frame zeroing of large locals.
        .globl memset
memset:
        movq %rdi, %rax
        testq %rdx, %rdx
        je .Lmemset_done
.Lmemset_loop:
        movb %sil, (%rdi)
        incq %rdi
        decq %rdx
        jne .Lmemset_loop
.Lmemset_done:
        ret

        .section .blaise.imports,"",@progbits
        .ascii "ExitProcess"
        .byte 0
        .ascii "kernel32"
        .byte 0
