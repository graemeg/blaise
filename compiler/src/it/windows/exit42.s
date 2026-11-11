# Windows milestone M1 program under test: exits with code 42 through
# kernel32!ExitProcess.  Assembled to an ELF object by the internal
# assembler and linked by the PE linker (TPeLinkerTests.TestLink_Exit42Fixture
# writes compiler/target/it/windows/exit42.exe); scripts/windows-vm.sh runs it.
#
# This is Win64 code written by hand: RCX carries the first argument, and the
# caller reserves 32 bytes of shadow space with RSP 16-byte aligned at the
# call.  On entry RSP is 8 mod 16 (the loader called _start), so 40 bytes
# realigns it and covers the shadow space.
        .text
        .globl _start
_start:
        subq $40, %rsp
        movl $42, %ecx
        call ExitProcess
        hlt                     # not reached: ExitProcess does not return

# The import: symbol, then library, each NUL-terminated -- the pair the code
# generator emits for `external 'kernel32' name 'ExitProcess'`.  The Windows
# toolkit maps the library to kernel32.dll.
        .section .blaise.imports,"",@progbits
        .ascii "ExitProcess"
        .byte 0
        .ascii "kernel32"
        .byte 0
