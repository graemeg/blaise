{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.start.freebsd;

// Program entry point for a DYNAMIC (libc-linked) FreeBSD binary
// (x86_64, System V ABI).
//
// The FreeBSD sibling of runtime.start.linux.  Per-OS because the hand-off
// into libc differs: glibc exports __libc_start_main and takes the raw stack
// pointer, whereas FreeBSD libc exports __libc_start1 and expects argc/argv/
// envp already unpacked.  Selected at link time by BuildRTLUnitList; the
// static profile uses runtime.start.static.freebsd instead.
//
// VERSION FLOOR — this unit requires FreeBSD 14 or newer, and it is the ONLY
// thing in the toolchain that does.  __libc_start1 was introduced in FreeBSD
// 14's libc; on 13.x the binary dies at exec with
//     ld-elf.so.1: Undefined symbol "__libc_start1"
// (13.x crt1 calls __libc_start/_init_tls/main itself).  The struct layouts
// elsewhere are NOT the constraint — see docs/freebsd-x86_64-backend-design
// .adoc, which notes the ino_t/dev_t widening landed in 12.
//
// This matters far less than it looks, because the FREESTANDING path has no
// version floor at all: it binds the kernel syscall ABI, which is stable
// across majors, and runtime.syscall.freebsd already covers sockets, so even
// a network server links static.  A program only lands here when it truly
// needs libc (--dynamic, or a real `external '<lib>'` binding).  Verified
// 2026-09-19: a socket server cross-compiled freestanding from Linux runs on
// a FreeBSD 13.1 jail.
//
// If the dynamic path ever needs to reach 13.x, the fix is to stop calling
// __libc_start1 and do the work here: capture argc/argv/environ/__progname
// from the argument block (runtime.start.static.freebsd already does exactly
// this), call main, exit with its result.  Two facts make that tractable —
// Blaise binaries emit NO .init_array (unit init is called from main), and on
// a dynamic image rtld/libthr own the TCB, so this unit must not touch TLS.
//
// This replaces the system Scrt1.o so the internal linker needs no
// FreeBSD-provided startup object.  The linker uses '_start' as the ELF entry
// point; an unmangled unit-level routine named _start emits exactly that
// symbol.
//
// ENTRY CONTRACT (amd64).  Unlike Linux, FreeBSD does NOT hand the entry its
// argument block on %rsp alone.  sys/amd64/amd64/machdep.c's exec_setregs
// zeroes the trapframe and then sets
//     %rdi = stack                       (points at argc)
//     %rsp = ((stack - 8) & ~15) + 8     (so %rsp may sit 8 bytes BELOW argc)
//     %rsi = 0                           (no rtld cleanup for a static image)
// and rtld-elf's _rtld_start passes the same %rdi with %rsi = the rtld exit
// procedure.  So %rdi — not %rsp — is the argument block, which is why this
// unit needs none of the stack-pad probing runtime.start.static.freebsd does.
//
// libc then wants __libc_start1(argc, argv, env, cleanup, mainX): it captures
// environ/__progname, runs the init array and the ctors, calls
// mainX(argc, argv, env) and exits with its return value.
//
// TLS is NOT set up here.  On a dynamic image rtld and libthr own the thread
// pointer (they allocate the TCB before the init array runs); the sysarch(
// AMD64_SET_FSBASE) dance in runtime.start.static.freebsd exists only because
// a freestanding binary has no rtld to do it.

interface

{ libc.so.7 lists BOTH of these as UND GLOBAL and resolves them with GLOB_DAT
  relocations against the executable — on a stock toolchain crt1.o defines
  them, and here we are the crt1 replacement.  __libc_start1 assigns them from
  the argument block before anything reads them, so the initial nil is never
  observed.  TLinkTarget.CrtExports makes the internal linker publish these in
  the executable's .dynsym so rtld can find them. }
var
  environ:    Pointer;   { char **environ }
  __progname: PChar;     { basename of argv[0] }

procedure _start;

{ The libc calls whose ABI changed in FreeBSD 12 (ino64: struct stat and
  struct dirent widened; struct kevent gained ext[4]), defined HERE so a
  dynamic binary never imports them (BUG-20261106-freebsd-dynamic-compat-abi).

  libc exports each twice: the FreeBSD 11 layout as stat@FBSD_1.0 and the
  current one as stat@@FBSD_1.5.  The internal linker writes no symbol
  versions, and for an unversioned reference rtld deliberately binds the
  FIRST version a library defines (pre-versioning binaries must keep
  working) -- FBSD_1.0, the old layouts.  The RTL reads the ino64 offsets
  (rtl.platform.layout.freebsd), so sizes, modes and directory names came
  out as garbage.  Defining the symbols in the executable resolves every
  reference locally; each one makes the current-ABI syscall itself and
  reports failure the libc way, -1 with errno set.  The freestanding profile
  gets the same five from runtime.syscall.freebsd. }
function stat(Path: PChar; Buf: Pointer): Int32;
function lstat(Path: PChar; Buf: Pointer): Int32;
function fstat(Fd: Int32; Buf: Pointer): Int32;
function getdirentries(Fd: Int32; Buf: Pointer; NBytes: Int64;
  Basep: Pointer): Int64;
function kevent(Kq: Int32; ChangeList: Pointer; NChanges: Int32;
  EventList: Pointer; NEvents: Int32; Timeout: Pointer): Int32;

implementation

type
  PInt64 = ^Int64;

{ ---- current-ABI syscalls ---------------------------------------------------
  Raw kernel entries: a failure comes back as -errno (the carry flag set by the
  kernel is folded into the sign), the static profile's convention.  Liberr
  turns that into libc's. }

const
  AT_FDCWD = -100;
  AT_SYMLINK_NOFOLLOW = $200;

function __error: Pointer; external name '__error';

function SysFstatat(Fd: Int64; Path: PChar; Buf: Pointer; Flag: Int64): Int64;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $552, %rax          { SYS_fstatat (ino64) }
    syscall
    jae  .Lok_fstatat
    negq %rax
.Lok_fstatat:
    ret
end;

function SysFstat(Fd: Int64; Buf: Pointer): Int64;
  assembler; nostackframe;
asm
    movq $551, %rax          { SYS_fstat (ino64) }
    syscall
    jae  .Lok_fstat
    negq %rax
.Lok_fstat:
    ret
end;

function SysGetdirentries(Fd: Int64; Buf: Pointer; NBytes: Int64;
  Basep: Pointer): Int64;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $554, %rax          { SYS_getdirentries (ino64) }
    syscall
    jae  .Lok_getdirentries
    negq %rax
.Lok_getdirentries:
    ret
end;

function SysKevent(Kq: Int64; ChangeList: Pointer; NChanges: Int64;
  EventList: Pointer; NEvents: Int64; Timeout: Pointer): Int64;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $560, %rax          { SYS_kevent (FreeBSD 12+ struct kevent) }
    syscall
    jae  .Lok_kevent
    negq %rax
.Lok_kevent:
    ret
end;

{ -errno -> -1 with errno set; anything else passes through. }
function LibcResult(R: Int64): Int64;
var
  E: ^Int32;
begin
  if R < 0 then
  begin
    E := __error();
    E^ := Int32(-R);
    Result := -1;
  end
  else
    Result := R;
end;

function stat(Path: PChar; Buf: Pointer): Int32;
begin
  Result := Int32(LibcResult(SysFstatat(AT_FDCWD, Path, Buf, 0)));
end;

function lstat(Path: PChar; Buf: Pointer): Int32;
begin
  Result := Int32(LibcResult(SysFstatat(AT_FDCWD, Path, Buf, AT_SYMLINK_NOFOLLOW)));
end;

function fstat(Fd: Int32; Buf: Pointer): Int32;
begin
  Result := Int32(LibcResult(SysFstat(Fd, Buf)));
end;

function getdirentries(Fd: Int32; Buf: Pointer; NBytes: Int64;
  Basep: Pointer): Int64;
begin
  Result := LibcResult(SysGetdirentries(Fd, Buf, NBytes, Basep));
end;

function kevent(Kq: Int32; ChangeList: Pointer; NChanges: Int32;
  EventList: Pointer; NEvents: Int32; Timeout: Pointer): Int32;
begin
  Result := Int32(LibcResult(SysKevent(Kq, ChangeList, NChanges, EventList,
    NEvents, Timeout)));
end;

{ Tail of the hand-off: place `main` in %r8 (the 5th argument) and enter libc.
  argc/argv/env/cleanup are already in %edi/%rsi/%rdx/%rcx, so nostackframe
  keeps them untouched.  The push re-establishes 16-byte alignment for the
  call (our own entry left %rsp at 8 mod 16), mirroring what Scrt1.o does.
  __libc_start1 never returns. }
procedure LibcStart1(AArgc: Int32; AArgv, AEnvp, ACleanup: Pointer);
  assembler; nostackframe;
asm
    lea  main(%rip), %r8
    push %rbp
    call __libc_start1@PLT
    hlt
end;

{ The C-level entry.  ASP points at argc, followed by argv[0..argc-1], a NULL,
  then envp.  ACleanup is rtld's exit procedure (0 when the kernel loaded us
  directly), which libc registers with atexit. }
procedure _BlaiseStartC(ASP, ACleanup: Pointer);
var
  Argc: Int64;
  Argv, Envp: Pointer;
begin
  Argc := PInt64(ASP)^;
  Argv := Pointer(PChar(ASP) + 8);
  { envp = &argv[argc + 1] — one past the NULL that terminates argv. }
  Envp := Pointer(PChar(Argv) + (Argc + 1) * 8);
  LibcStart1(Int32(Argc), Argv, Envp, ACleanup);
end;

{ The ELF entry.  %rdi (argument block) and %rsi (rtld cleanup) are already
  the first two arguments of _BlaiseStartC, so there is nothing to marshal —
  only the frame pointer to clear and %rsp to align.  Never returns. }
procedure _start; assembler; nostackframe;
asm
    endbr64
    xor  %ebp, %ebp
    and  $0xfffffffffffffff0, %rsp
    call _BlaiseStartC
    hlt
end;

end.
