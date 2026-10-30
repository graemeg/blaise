{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.syscall.linux;

// Linux x86_64 direct-syscall kernel leaf - the libc replacement for the thin
// 1:1 syscall wrappers (docs/linux-syscall-migration.adoc).
//
// This unit DEFINES the bare POSIX names (open, read, write,  ) that
// rtl.platform.posix.pas references via `external name 'open'` etc.  When it is
// linked into a program (the --static link-time swap), those symbols resolve
// here as raw `syscall` stubs instead of being imported from libc.so.6 - so the
// resulting binary is a freestanding static ET_EXEC with no libc, no PT_INTERP.
//
// System V AMD64 -> Linux syscall ABI:
//   * syscall number in %rax; the `syscall` instruction returns in %rax.
//   * Argument registers DIFFER between the C ABI and the kernel ABI on the 4th
//     argument: C passes arg4 in %rcx, the kernel expects it in %r10 (the
//     `syscall` instruction itself clobbers %rcx).  Wrappers with >= 4 args
//     therefore `movq %rcx, %r10` first.  Args 1-3 (%rdi,%rsi,%rdx) and 5-6
//     (%r8,%r9) are already in the right registers.
//   * The kernel returns -errno on error (a small negative value).  libc would
//     translate that to a -1 return + `errno`; the existing Pascal call sites
//     test `if result < 0` / `if Fd < 0`, which a raw -errno also satisfies, so
//     no errno table is needed for these leaves.
//
// `nostackframe` lets each asm body own the frame so the registers hold the raw
// incoming arguments unmodified.

interface

{ File descriptors. }
function open(Path: PChar; Flags: Int32; Mode: Int32): Int32;
function close(Fd: Int32): Int32;
function read(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
{ `write` collides with the Write/WriteLn builtin as a Pascal identifier, so the
  Pascal name is _sys_write; the asm body additionally emits a bare `write`
  label (.globl) so the linker symbol matches rtl.platform.posix's
  `external name 'write'`.  Every other leaf's name is a valid Pascal identifier
  and needs no alias. }
function _sys_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
function lseek(Fd: Int32; Offset: Int64; Whence: Int32): Int64;

{ Filesystem. }
function fstat(Fd: Int32; Buf: Pointer): Int32;
function stat(Path: PChar; Buf: Pointer): Int32;
function lstat(Path: PChar; Buf: Pointer): Int32;
function mkdir(Path: PChar; Mode: Int32): Int32;
function rmdir(Path: PChar): Int32;
function unlink(Path: PChar): Int32;
function rename(OldPath, NewPath: PChar): Int32;
function chdir(Path: PChar): Int32;
function chmod(Path: PChar; Mode: Int32): Int32;
{ readlink(path, buf, size): the symlink's target, unterminated; returns its
  length, or -errno when Path is not a link. }
function readlink(Path: PChar; Buf: PChar; Size: Int64): Int64;
{ getdirentries(fd, buf, nbytes, basep) — read directory entries from a fd
  opened on a directory.  Packs variable-length dirent records into Buf and
  returns the number of BYTES written (0 at end of directory, -errno on
  error); the caller walks them using the per-OS offsets from TPlatformLayout.

  The BSD name is used rather than Linux's own `getdents64` because it is the
  one spelling libc provides on all three POSIX targets (glibc, FreeBSD and
  macOS), so rtl.platform.posix can bind a single `external name` that works
  on both the libc and the freestanding-static paths.  Linux has no
  getdirentries SYSCALL, so this leaf implements it over SYS_getdents64 (217)
  and simply ignores basep — the walker never seeks. }
function getdirentries(Fd: Int32; Buf: Pointer; Count: Int64;
                       Basep: Pointer): Int64;

{ Process. }
function getpid: Int32;
function dup2(OldFd, NewFd: Int32): Int32;
function pipe(Fds: Pointer): Int32;
{ fcntl(fd, cmd, arg) — needed to flip O_NONBLOCK on fds (the fiber I/O layer
  and the errno-classification tests; docs/async-networking-design.adoc P3). }
function fcntl(Fd, Cmd, Arg: Int32): Int32;
{ ioctl(fd, request, arg) — the universal device-control syscall.  Terminal
  control (tcgetattr/tcsetattr are ioctl wrappers), network interfaces, and
  many other subsystems use it.  SYS_ioctl = 16. }
function ioctl(Fd: Int32; Request: Int64; Arg: Pointer): Int32;
{ getrlimit/setrlimit(resource, rlim) — process resource limits.  The fiber
  tests size their fd budget with these (RLIMIT_NOFILE = 7 on Linux, 8 on
  FreeBSD — callers translate).  struct rlimit is two 64-bit words.
  SYS 97/160.  On the dynamic path libc binds the same names; these leaves
  give --static and freestanding builds the same surface. }
function getrlimit(Resource: Int32; Rlim: Pointer): Int32;
function setrlimit(Resource: Int32; Rlim: Pointer): Int32;
{ socketpair(domain, type, protocol, sv) — connected fd pair; the reactor and
  fiber I/O tests build their AF_UNIX plumbing with it.  SYS 53.  On the
  dynamic path libc binds the same name. }
function socketpair(Domain, Typ, Protocol: Int32; Sv: Pointer): Int32;

{ epoll + eventfd: the async reactor's readiness poller and its self-wake fd.
  Bound in async.reactor.epoll via `external name`; on the dynamic path libc
  provides them, so these definitions exist only for the --static leaf.  The
  reactor treats the epoll_event struct as an opaque Pointer, so no record is
  needed here (see async.reactor.epoll for the packed uint32/uint64 layout). }
function epoll_create1(Flags: Int32): Int32;
function epoll_ctl(EpFd, Op, Fd: Int32; Event: Pointer): Int32;
function epoll_wait(EpFd: Int32; Events: Pointer; MaxEvents, Timeout: Int32): Int32;
{ eventfd(2) with a flags arg maps to the eventfd2 syscall (the reactor passes
  EFD_CLOEXEC|EFD_NONBLOCK). }
function eventfd(InitVal, Flags: Int32): Int32;

{ Memory. }
function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Int32;
             Offset: Int64): Pointer;
function munmap(Addr: Pointer; Length: Int64): Int32;
{ mprotect(addr, len, prot) — guard pages for fiber stacks (async design L0). }
function mprotect(Addr: Pointer; Length: Int64; Prot: Int32): Int32;
{ mremap(old, oldsz, newsz, flags, newaddr) - 5 args; raw syscall. }
function mremap(OldAddr: Pointer; OldSize, NewSize: Int64; Flags: Int32;
               NewAddr: Pointer): Pointer;

{ Time. }
function nanosleep(Req, Rem: Pointer): Int32;
function clock_gettime(ClockId: Int32; Ts: Pointer): Int32;

{ Process control + raw primitives the higher-level wrappers (runtime.libc.linux)
  build on.  These are the bare syscalls; the libc-shaped versions (execvp with
  PATH search, waitpid, system,  ) live in the wrapper unit. }
function fork: Int32;
function execve(Path: PChar; Argv, Envp: Pointer): Int32;
function wait4(Pid: Int32; Status: Pointer; Options: Int32;
               Rusage: Pointer): Int32;
function sched_getaffinity(Pid: Int32; CpuSetSize: Int64;
                           Mask: Pointer): Int32;
{ futex(2): the kernel primitive the threads leaf builds mutexes and join on.
  6-arg syscall; arg4 (Timeout) arrives in %rcx -> moved to %r10.  Returns 0 or
  a count on success, -errno on error.  Op = FUTEX_WAIT(0) / FUTEX_WAKE(1). }
function futex(Uaddr: Pointer; Op, Val: Int32; Timeout: Pointer;
               Uaddr2: Pointer; Val3: Int32): Int32;
function getrandom(Buf: Pointer; Count: Int64; Flags: Int32): Int64;
function arch_prctl(Code: Int32; Addr: Pointer): Int32;
function kill(Pid, Sig: Int32): Int32;
{ Raw time(2): returns seconds since the epoch; if T is non-nil it is also
  written there.  The kernel syscall handles the out-param itself. }
function sys_time(T: Pointer): Int64;
{ Raw getcwd(2): fills Buf (up to Size), returns the length INCLUDING the NUL on
  success or -errno.  (libc's getcwd returns the buffer pointer - the wrapper in
  runtime.libc.linux adapts that.) }
function sys_getcwd(Buf: PChar; Size: Int64): Int64;

{ _exit(2) - exit_group, terminates all threads, runs NO atexit handlers.
  The bare `exit` (which DOES run atexit handlers, called by main's epilogue) is
  defined by runtime.libc2.linux alongside the registry, not here. }
procedure _exit(Code: Int32);

{ The process environment vector (NULL-terminated array of "KEY=VALUE" PChars),
  captured by the freestanding _start from the initial stack.  Lives in this
  base unit (not the higher libc wrapper) so _start can use ONLY this unit and
  avoid a diamond import; runtime.libc.linux's getenv/execvp read it. }
var
  environ: Pointer;

implementation

{ ---- Linux x86_64 syscall numbers (arch/x86/entry/syscalls). ---- }
const
  SYS_read          = 0;
  SYS_write         = 1;
  SYS_open          = 2;
  SYS_close         = 3;
  SYS_stat          = 4;
  SYS_fstat         = 5;
  SYS_lstat         = 6;
  SYS_lseek         = 8;
  SYS_mmap          = 9;
  SYS_munmap        = 11;
  SYS_pipe          = 22;
  SYS_dup2          = 33;
  SYS_nanosleep     = 35;
  SYS_getpid        = 39;
  SYS_rename        = 82;
  SYS_mkdir         = 83;
  SYS_chmod         = 90;
  SYS_readlink      = 89;
  SYS_rmdir         = 84;
  SYS_unlink        = 87;
  SYS_chdir         = 80;
  SYS_clock_gettime = 228;
  SYS_exit_group    = 231;
  SYS_mremap        = 25;
  SYS_fork          = 57;
  SYS_execve        = 59;
  SYS_wait4         = 61;
  SYS_kill          = 62;
  SYS_getcwd        = 79;
  SYS_sched_getaffinity = 204;
  SYS_futex         = 202;
  SYS_arch_prctl    = 158;
  SYS_time          = 201;
  SYS_getrandom     = 318;
  SYS_epoll_wait    = 232;   { arm64 (aarch64): epoll_pwait = 22 }
  SYS_epoll_ctl     = 233;   { arm64: 21 }
  SYS_epoll_create1 = 291;   { arm64: 20 }
  SYS_eventfd2      = 290;   { arm64: 19 }
{ The asm bodies use literal immediates (the assembler needs a literal, not a
  symbol); the const block above documents the number-to-name mapping.
  This leaf is x86-64-only today (every body is `movq $N,%rax; syscall`); the
  arm64 numbers are recorded for a future aarch64 static leaf. }

function open(Path: PChar; Flags: Int32; Mode: Int32): Int32;
  assembler; nostackframe;
asm
    movq $2, %rax        { SYS_open }
    syscall
    ret
end;

function close(Fd: Int32): Int32;
  assembler; nostackframe;
asm
    movq $3, %rax        { SYS_close }
    syscall
    ret
end;

function read(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
  assembler; nostackframe;
asm
    movq $0, %rax        { SYS_read }
    syscall
    ret
end;

function _sys_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
  assembler; nostackframe;
asm
.globl write
write:
    movq $1, %rax        { SYS_write }
    syscall
    ret
end;

function lseek(Fd: Int32; Offset: Int64; Whence: Int32): Int64;
  assembler; nostackframe;
asm
    movq $8, %rax        { SYS_lseek }
    syscall
    ret
end;

function fstat(Fd: Int32; Buf: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $5, %rax        { SYS_fstat }
    syscall
    ret
end;

function stat(Path: PChar; Buf: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $4, %rax        { SYS_stat }
    syscall
    ret
end;

function lstat(Path: PChar; Buf: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $6, %rax        { SYS_lstat }
    syscall
    ret
end;

function mkdir(Path: PChar; Mode: Int32): Int32;
  assembler; nostackframe;
asm
    movq $83, %rax       { SYS_mkdir }
    syscall
    ret
end;

function chmod(Path: PChar; Mode: Int32): Int32;
  assembler; nostackframe;
asm
    movq $90, %rax       { SYS_chmod }
    syscall
    ret
end;

{ Basep (arg4, %rcx) is deliberately unused: SYS_getdents64 takes only three
  arguments, and the directory walker never needs the seek offset. }
function getdirentries(Fd: Int32; Buf: Pointer; Count: Int64;
                       Basep: Pointer): Int64;
  assembler; nostackframe;
asm
    movq $217, %rax      { SYS_getdents64 }
    syscall
    ret
end;

function readlink(Path: PChar; Buf: PChar; Size: Int64): Int64;
  assembler; nostackframe;
asm
    movq $89, %rax       { SYS_readlink }
    syscall
    ret
end;

function rmdir(Path: PChar): Int32;
  assembler; nostackframe;
asm
    movq $84, %rax       { SYS_rmdir }
    syscall
    ret
end;

function unlink(Path: PChar): Int32;
  assembler; nostackframe;
asm
    movq $87, %rax       { SYS_unlink }
    syscall
    ret
end;

function rename(OldPath, NewPath: PChar): Int32;
  assembler; nostackframe;
asm
    movq $82, %rax       { SYS_rename }
    syscall
    ret
end;

function chdir(Path: PChar): Int32;
  assembler; nostackframe;
asm
    movq $80, %rax       { SYS_chdir }
    syscall
    ret
end;

function getpid: Int32;
  assembler; nostackframe;
asm
    movq $39, %rax       { SYS_getpid }
    syscall
    ret
end;

function dup2(OldFd, NewFd: Int32): Int32;
  assembler; nostackframe;
asm
    movq $33, %rax       { SYS_dup2 }
    syscall
    ret
end;

function pipe(Fds: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $22, %rax       { SYS_pipe }
    syscall
    ret
end;

function fcntl(Fd, Cmd, Arg: Int32): Int32;
  assembler; nostackframe;
asm
    movq $72, %rax       { SYS_fcntl }
    syscall
    ret
end;

function ioctl(Fd: Int32; Request: Int64; Arg: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $16, %rax       { SYS_ioctl }
    syscall
    ret
end;

function getrlimit(Resource: Int32; Rlim: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $97, %rax       { SYS_getrlimit }
    syscall
    ret
end;

function setrlimit(Resource: Int32; Rlim: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $160, %rax      { SYS_setrlimit }
    syscall
    ret
end;

{ 4-arg syscall: arg4 arrives in %rcx (C ABI) but the kernel wants %r10. }
function socketpair(Domain, Typ, Protocol: Int32; Sv: Pointer): Int32;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $53, %rax       { SYS_socketpair }
    syscall
    ret
end;

{ mmap has 6 args; arg4 (Flags) arrives in %rcx (C ABI) but the kernel wants it
  in %r10.  Move it before the syscall. }
function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Int32;
             Offset: Int64): Pointer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $9, %rax        { SYS_mmap }
    syscall
    ret
end;

function munmap(Addr: Pointer; Length: Int64): Int32;
  assembler; nostackframe;
asm
    movq $11, %rax       { SYS_munmap }
    syscall
    ret
end;

function mprotect(Addr: Pointer; Length: Int64; Prot: Int32): Int32;
  assembler; nostackframe;
asm
    movq $10, %rax       { SYS_mprotect }
    syscall
    ret
end;

function nanosleep(Req, Rem: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $35, %rax       { SYS_nanosleep }
    syscall
    ret
end;

function clock_gettime(ClockId: Int32; Ts: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $228, %rax      { SYS_clock_gettime }
    syscall
    ret
end;

{ mremap has 5 args; arg4 (Flags) arrives in %rcx -> move to %r10. }
function mremap(OldAddr: Pointer; OldSize, NewSize: Int64; Flags: Int32;
               NewAddr: Pointer): Pointer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $25, %rax       { SYS_mremap }
    syscall
    ret
end;

function fork: Int32;
  assembler; nostackframe;
asm
    movq $57, %rax       { SYS_fork }
    syscall
    ret
end;

function execve(Path: PChar; Argv, Envp: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $59, %rax       { SYS_execve }
    syscall
    ret
end;

{ wait4 has 4 args; arg4 (Rusage) arrives in %rcx -> move to %r10. }
function wait4(Pid: Int32; Status: Pointer; Options: Int32;
               Rusage: Pointer): Int32;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $61, %rax       { SYS_wait4 }
    syscall
    ret
end;

function epoll_create1(Flags: Int32): Int32;
  assembler; nostackframe;
asm
    movq $291, %rax      { SYS_epoll_create1 }
    syscall
    ret
end;

{ epoll_ctl has 4 args; arg4 (Event) arrives in %rcx -> move to %r10. }
function epoll_ctl(EpFd, Op, Fd: Int32; Event: Pointer): Int32;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $233, %rax      { SYS_epoll_ctl }
    syscall
    ret
end;

{ epoll_wait has 4 args; arg4 (Timeout) arrives in %rcx -> move to %r10. }
function epoll_wait(EpFd: Int32; Events: Pointer; MaxEvents, Timeout: Int32): Int32;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $232, %rax      { SYS_epoll_wait }
    syscall
    ret
end;

{ eventfd(count, flags) with a flags arg is the eventfd2 syscall (2 args in
  %rdi/%rsi, no %r10 move needed). }
function eventfd(InitVal, Flags: Int32): Int32;
  assembler; nostackframe;
asm
    movq $290, %rax      { SYS_eventfd2 }
    syscall
    ret
end;

function sched_getaffinity(Pid: Int32; CpuSetSize: Int64;
                           Mask: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $204, %rax      { SYS_sched_getaffinity }
    syscall
    ret
end;

{ futex has 6 args; arg4 (Timeout) arrives in %rcx -> move to %r10. }
function futex(Uaddr: Pointer; Op, Val: Int32; Timeout: Pointer;
               Uaddr2: Pointer; Val3: Int32): Int32;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $202, %rax      { SYS_futex }
    syscall
    ret
end;

function getrandom(Buf: Pointer; Count: Int64; Flags: Int32): Int64;
  assembler; nostackframe;
asm
    movq $318, %rax      { SYS_getrandom }
    syscall
    ret
end;

function arch_prctl(Code: Int32; Addr: Pointer): Int32;
  assembler; nostackframe;
asm
    movq $158, %rax      { SYS_arch_prctl }
    syscall
    ret
end;

function kill(Pid, Sig: Int32): Int32;
  assembler; nostackframe;
asm
    movq $62, %rax       { SYS_kill }
    syscall
    ret
end;

function sys_time(T: Pointer): Int64;
  assembler; nostackframe;
asm
    movq $201, %rax      { SYS_time }
    syscall
    ret
end;

function sys_getcwd(Buf: PChar; Size: Int64): Int64;
  assembler; nostackframe;
asm
    movq $79, %rax       { SYS_getcwd }
    syscall
    ret
end;

{ _exit(2): terminate immediately via exit_group, running no atexit handlers.
  Code arrives in %edi; exit_group reads its status from %rdi. }
procedure _exit(Code: Int32);
  assembler; nostackframe;
asm
    movq $231, %rax      { SYS_exit_group }
    syscall
    ret
end;

end.
