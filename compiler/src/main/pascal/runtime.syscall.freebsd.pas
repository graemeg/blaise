{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.syscall.freebsd;

// FreeBSD x86_64 direct-syscall kernel leaf — the libc replacement for a static,
// libc-free FreeBSD ET_EXEC (docs/freebsd-x86_64-backend-design.adoc, Step 3/4).
//
// This is the FreeBSD sibling of runtime.syscall.linux.  It DEFINES the bare
// POSIX names that rtl.platform.posix references via `external name 'write'`
// etc.; the FreeBSD RTL composition links it (the link-time swap) in place of
// the Linux leaf, so the resulting binary reaches the kernel with raw
// `syscall`s and needs no libc, no PT_INTERP.
//
// Step 4a scope: the file/process syscall leaves (open/close/read/write/lseek,
// stat/fstat/mkdir/rmdir/unlink/rename/chdir/chmod, getpid/dup2/pipe/fork/
// execve/wait4/kill/getcwd, mmap/munmap/nanosleep/clock_gettime), plus the
// pre-existing `_exit`, `_sys_write` and `environ`.  The harder leaves
// (memcpy/memset, date math, the mmap allocator, threads) grow here in Steps
// 4b/4c.
//
// System V AMD64 -> FreeBSD syscall ABI:
//   * syscall number in %rax; args in %rdi,%rsi,%rdx,%r10,%r8,%r9 (the 4th C
//     arg %rcx must be moved to %r10 — the `syscall` instruction clobbers %rcx).
//   * The syscall NUMBERS differ from Linux (exit=1, write=4, read=3, open=5,
//     close=6 — see sys/syscall.h); they are NOT Linux's.  FreeBSD 12 renumbered
//     stat/fstat/lseek/mmap for the 64-bit-inode ("ino64") ABI; this leaf uses
//     the ino64 numbers to match the FreeBSD 14 224-byte `struct stat` that the
//     rtl.platform.layout.freebsd adapter expects.
//   * ERROR CONVENTION — the key FreeBSD difference from Linux.  FreeBSD reports
//     errors via the CARRY FLAG: on error CF is set and %rax holds a POSITIVE
//     errno; on success CF is clear and %rax is the result.  The Pascal call
//     sites in rtl.platform.posix expect the Linux -errno convention (they test
//     `if Fd < 0`, `< 0`, `<> 0`).  So every leaf that can fail translates:
//     after `syscall`, `jae` past a `negq %rax` when CF is clear (success —
//     leave %rax untouched); when CF is set, `negq %rax` turns the positive
//     errno into -errno.  Each body uses a UNIQUE local label (.Lok_xxx) so the
//     forward-local jumps do not collide when the unit assembles to one object.
//
// `nostackframe` lets each asm body own the frame so the registers hold the raw
// incoming arguments unmodified.

interface

{ File descriptors. }
function open(Path: PChar; Flags: Integer; Mode: Integer): Integer;
function close(Fd: Integer): Integer;
function read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
{ `write` collides with the Write/WriteLn builtin as a Pascal identifier, so the
  Pascal name is _sys_write; the asm body additionally emits a bare `write`
  label (.globl) so the linker symbol matches rtl.platform.posix's
  `external name 'write'`.  Every other leaf's name is a valid Pascal identifier
  and needs no alias. }
function _sys_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
function lseek(Fd: Integer; Offset: Int64; Whence: Integer): Int64;

{ Filesystem. }
function fstat(Fd: Integer; Buf: Pointer): Integer;
{ FreeBSD's ino64 ABI has NO plain `stat` syscall — it is expressed as
  fstatat(AT_FDCWD, path, buf, 0).  This wrapper sets up that call so the bare
  `stat` symbol posix imports still resolves. }
function stat(Path: PChar; Buf: Pointer): Integer;
function mkdir(Path: PChar; Mode: Integer): Integer;
function rmdir(Path: PChar): Integer;
function unlink(Path: PChar): Integer;
function rename(OldPath, NewPath: PChar): Integer;
function chdir(Path: PChar): Integer;
function chmod(Path: PChar; Mode: Integer): Integer;

{ Process. }
function getpid: Integer;
function dup2(OldFd, NewFd: Integer): Integer;
{ FreeBSD deprecated the 2-arg pipe(2) (legacy 42); this calls pipe2(fds, 0). }
function pipe(Fds: Pointer): Integer;
{ fcntl(fd, cmd, arg) — raw; note FreeBSD's O_NONBLOCK is 0x4 (not Linux's
  0x800): callers must pass FreeBSD flag values, this leaf does not translate. }
function fcntl(Fd, Cmd, Arg: Integer): Integer;
{ ioctl(fd, request, arg) — the universal device-control syscall.  Terminal
  control (tcgetattr/tcsetattr are ioctl wrappers), network interfaces, and
  many other subsystems use it.  SYS_ioctl = 54. }
function ioctl(Fd: Integer; Request: Int64; Arg: Pointer): Integer;

{ Event notification — the readiness reactor's kernel surface.  The libc
  profile binds the same names in libc; these leaves give the --static
  profile the design's link-time swap (async-networking-design.adoc,
  "Freestanding (static) builds"). }
function kqueue: Integer;
{ kevent(kq, changelist, nchanges, eventlist, nevents, timeout) — the
  FreeBSD-12+ kevent (64-byte struct kevent with ext[4]). }
function kevent(Kq: Integer; Changes: Pointer; NChanges: Integer;
                Events: Pointer; NEvents: Integer; Timeout: Pointer): Integer;

{ Sockets — Net.Sockets binds these flat C names; in the libc profile libc
  provides them, here the --static profile gets raw leaves (same link-time
  swap as kqueue/kevent above).  FreeBSD has NO recv/send syscalls: libc
  defines recv(fd,buf,len,flags) = recvfrom(...,nil,nil) and send =
  sendto(...,nil,0), so those two leaves zero the address arguments before
  entering the kernel.  htons/ntohs are not syscalls at all — plain 16-bit
  byte swaps exported under their libc names. }
function socket(Domain, Typ, Protocol: Integer): Integer;
function bind(Fd: Integer; Addr: Pointer; AddrLen: Integer): Integer;
function listen(Fd, Backlog: Integer): Integer;
function accept(Fd: Integer; Addr: Pointer; AddrLen: Pointer): Integer;
{ accept4(2) — accept with flags (SOCK_NONBLOCK etc.); FreeBSD SYS 541. }
function accept4(Fd: Integer; Addr: Pointer; AddrLen: Pointer;
                 Flags: Integer): Integer;
function connect(Fd: Integer; Addr: Pointer; AddrLen: Integer): Integer;
function setsockopt(Fd, Level, OptName: Integer; OptVal: Pointer;
                    OptLen: Integer): Integer;
function getsockopt(Fd, Level, OptName: Integer; OptVal: Pointer;
                    OptLen: Pointer): Integer;
function getsockname(Fd: Integer; Addr: Pointer; AddrLen: Pointer): Integer;
function shutdown(Fd, How: Integer): Integer;
function recv(Fd: Integer; Buf: Pointer; Len: Int64; Flags: Integer): Int64;
function send(Fd: Integer; Buf: Pointer; Len: Int64; Flags: Integer): Int64;
function htons(HostShort: UInt16): UInt16;
function ntohs(NetShort: UInt16): UInt16;

{ signal(3) — libc's simplified handler install; on FreeBSD it is a wrapper
  over sigaction(2) (SYS_sigaction = 416), so the leaf builds the struct and
  returns the previous handler.  Net.Sockets binds this name for its
  process-wide SIGPIPE ignore. }
function signal(SigNum: Integer; Handler: Pointer): Pointer;

{ Memory. }
function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Integer;
             Offset: Int64): Pointer;
function munmap(Addr: Pointer; Length: Int64): Integer;
{ mprotect(addr, len, prot) — guard pages for fiber stacks (async design L0). }
function mprotect(Addr: Pointer; Length: Int64; Prot: Integer): Integer;

{ mremap(old, oldsz, newsz, flags): FreeBSD has NO in-place remap syscall, so
  this is a stub that always reports failure (MAP_FAILED = -1).  runtime.mem's
  large-realloc path already treats an mremap failure as "grow the slow way":
  it allocates a fresh region, memcpy's the old contents across, and frees the
  old one (see the MapFailed fall-through in _BlaiseReallocMem).  Exporting the
  `mremap` symbol as a failing stub therefore gives the allocator its no-mremap
  grow fallback with no allocator changes.  Signature matches the Linux leaf so
  runtime.mem's `external name 'mremap'` binds on both targets. }
function mremap(OldAddr: Pointer; OldSize, NewSize: Int64; Flags: Integer;
               NewAddr: Pointer): Pointer;

{ Time. }
function nanosleep(Req, Rem: Pointer): Integer;
function clock_gettime(ClockId: Integer; Ts: Pointer): Integer;

{ Process control + raw primitives the higher-level wrappers build on. }
function fork: Integer;
function execve(Path: PChar; Argv, Envp: Pointer): Integer;
function wait4(Pid: Integer; Status: Pointer; Options: Integer;
               Rusage: Pointer): Integer;
function kill(Pid, Sig: Integer): Integer;
{ getrandom(buf, count, flags): fill buf with count random bytes; returns the
  count written or -errno.  Used by mkstemp's random suffix. }
function getrandom(Buf: Pointer; Count: Int64; Flags: Integer): Int64;
{ Raw __getcwd(2): fills Buf (up to Size); returns 0 on success or -errno.  The
  wrapper in the posix layer adapts that to libc's buffer-pointer contract. }
function sys_getcwd(Buf: PChar; Size: Int64): Int64;

{ Raw __sysctl(2) — SYS 202.  FreeBSD's structured kernel-state query; the
  freestanding sysconf (runtime.libc.freebsd) reads hw.ncpu through it since
  FreeBSD has no sched_getaffinity.  6-arg syscall (arg4 %rcx -> %r10); returns
  0 on success or -errno (CF-translated). }
function sysctl(Name: Pointer; NameLen: Integer; OldP: Pointer;
                OldLenP: Pointer; NewP: Pointer; NewLen: Int64): Integer;

{ Threads + TLS (Step 4c) — the FreeBSD primitives runtime.thread.static.freebsd
  and runtime.start.static.freebsd build on.  These have no Linux equivalents
  (Linux uses clone/futex/arch_prctl); the numbers are FreeBSD-specific. }

{ sysarch(op, parms) — SYS 165.  The FreeBSD way to set the %fs base for TLS:
  op = AMD64_SET_FSBASE (129), parms = a POINTER to the base value (NOT the value
  itself).  Returns 0 on success or -errno (CF-translated). }
function sysarch(Op: Integer; Parms: Pointer): Integer;

{ _umtx_op(obj, op, val, uaddr, uaddr2) — SYS 454.  The FreeBSD futex analogue.
  op = UMTX_OP_WAIT_UINT_PRIVATE (15) blocks while obj^ = val (returns at once if
  obj^ <> val, like futex); op = UMTX_OP_WAKE_PRIVATE (16) wakes up to val waiters
  on obj.  5-arg syscall: arg4 (uaddr) arrives in %rcx -> moved to %r10. }
function _umtx_op(Obj: Pointer; Op, Val: Integer; Uaddr, Uaddr2: Pointer): Integer;

{ thr_new(param, param_size) — SYS 455.  Creates a new thread from a filled-in
  `struct thr_param` (param_size = sizeof = 104 on amd64).  The FreeBSD analogue
  of clone(2).  Returns 0 on success or -errno. }
function thr_new(Param: Pointer; ParamSize: Integer): Integer;

{ thr_exit(state) — SYS 431.  Terminates JUST the calling thread (NOT the whole
  process — that is exit(2)/SYS_exit).  If state is non-nil the kernel writes 1
  there and _umtx_op-wakes it; we clear/wake the join word ourselves and pass nil.
  Never returns. }
procedure thr_exit(State: Pointer);

{ _exit(2) — SYS_exit = 1.  Terminates the process; never returns.  The
  unit-level routine name `_exit` already emits the unmangled `_exit` symbol that
  satisfies posix's `external name '_exit'`. }
procedure _exit(Code: Integer);

{ The current process environment (envp), captured by _start.  rtl.platform.posix
  / getenv walk this NULL-terminated array.  Defined here (as on Linux) so the
  kernel leaf owns it. }
var
  environ: Pointer;

implementation

{ ---- FreeBSD x86_64 syscall numbers (FreeBSD 14 sys/sys/syscall.h). ----
  Verified against
  https://raw.githubusercontent.com/freebsd/freebsd-src/release/14.0.0/sys/sys/syscall.h
  ino64 variants used where FreeBSD 12 renumbered (fstat=551, lseek=478,
  mmap=477; stat has no ino64 syscall — expressed via fstatat=552). }
const
  SYS_exit          = 1;
  SYS_fork          = 2;
  SYS_read          = 3;
  SYS_write         = 4;
  SYS_open          = 5;
  SYS_close         = 6;
  SYS_wait4         = 7;
  SYS_unlink        = 10;
  SYS_chdir         = 12;
  SYS_chmod         = 15;
  SYS_getpid        = 20;
  SYS_kill          = 37;
  SYS_munmap        = 73;
  SYS_dup2          = 90;
  SYS_rename        = 128;
  SYS_mkdir         = 136;
  SYS_rmdir         = 137;
  SYS_getcwd        = 326;   { __getcwd }
  SYS_sysctl        = 202;   { __sysctl (hw.ncpu for sysconf) }
  SYS_getrandom     = 563;
  SYS_clock_gettime = 232;
  SYS_nanosleep     = 240;
  SYS_mmap          = 477;   { ino64 (legacy freebsd6 mmap = 197) }
  SYS_lseek         = 478;   { ino64 (legacy lseek = 199) }
  SYS_fstat         = 551;   { ino64 (legacy freebsd11_fstat = 189) }
  SYS_fstatat       = 552;   { ino64 (legacy freebsd11_fstatat = 493) }
  SYS_ioctl         = 54;
  SYS_pipe2         = 542;   { pipe(2) legacy 42 deprecated }
  SYS_execve        = 59;
  SYS_sysarch       = 165;   { %fs-base setup for TLS (AMD64_SET_FSBASE) }
  SYS_thr_exit      = 431;   { terminate ONE thread (NOT exit(2)) }
  SYS_umtx_op       = 454;   { the FreeBSD futex analogue }
  SYS_kqueue        = 362;
  SYS_kevent        = 560;   { FreeBSD-12+ 64-byte kevent (freebsd11_kevent = 363) }
  SYS_socket        = 97;
  SYS_bind          = 104;
  SYS_listen        = 106;
  SYS_accept        = 30;
  SYS_accept4       = 541;
  SYS_connect       = 98;
  SYS_setsockopt    = 105;
  SYS_getsockopt    = 118;
  SYS_getsockname   = 32;
  SYS_shutdown      = 134;
  SYS_recvfrom      = 29;    { recv = recvfrom with nil address }
  SYS_sendto        = 133;   { send = sendto with nil address }
  SYS_sigaction     = 416;   { signal(3) is a libc wrapper over this }
  SYS_thr_new       = 455;   { the FreeBSD clone(2) analogue }
  AT_FDCWD          = -100;  { dirfd for path-relative *at() syscalls at cwd }
{ The asm bodies use literal immediates (the assembler needs a literal, not a
  symbol); the const block above documents the number-to-name mapping. }

function open(Path: PChar; Flags: Integer; Mode: Integer): Integer;
  assembler; nostackframe;
asm
    movq $5, %rax            { SYS_open }
    syscall
    jae  .Lok_open           { CF clear = success }
    negq %rax                { CF set = error: errno -> -errno }
.Lok_open:
    ret
end;

function close(Fd: Integer): Integer;
  assembler; nostackframe;
asm
    movq $6, %rax            { SYS_close }
    syscall
    jae  .Lok_close
    negq %rax
.Lok_close:
    ret
end;

function read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
  assembler; nostackframe;
asm
    movq $3, %rax            { SYS_read }
    syscall
    jae  .Lok_read
    negq %rax
.Lok_read:
    ret
end;

{ write CAN fail; posix's write-loop expects a negative return on error, so it
  gets CF-translation too. }
function _sys_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
  assembler; nostackframe;
asm
.globl write
write:
    movq $4, %rax            { SYS_write }
    syscall
    jae  .Lok_write
    negq %rax
.Lok_write:
    ret
end;

function lseek(Fd: Integer; Offset: Int64; Whence: Integer): Int64;
  assembler; nostackframe;
asm
    movq $478, %rax          { SYS_lseek (ino64) }
    syscall
    jae  .Lok_lseek
    negq %rax
.Lok_lseek:
    ret
end;

function fstat(Fd: Integer; Buf: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $551, %rax          { SYS_fstat (ino64) }
    syscall
    jae  .Lok_fstat
    negq %rax
.Lok_fstat:
    ret
end;

{ stat(path, buf) -> fstatat(AT_FDCWD, path, buf, 0).  Incoming: %rdi=Path,
  %rsi=Buf.  Shift to the fstatat argument layout: dirfd(%rdi)=AT_FDCWD,
  path(%rsi)=Path, buf(%rdx)=Buf, flag(%r10)=0.  arg4 goes straight to %r10
  (the syscall's 4th kernel register); no %rcx move is needed since we build
  the arguments here rather than receive four C args. }
function stat(Path: PChar; Buf: Pointer): Integer;
  assembler; nostackframe;
asm
    movq %rsi, %rdx          { buf   -> arg3 }
    movq %rdi, %rsi          { path  -> arg2 }
    movq $-100, %rdi         { AT_FDCWD -> arg1 (dirfd) }
    xorq %r10, %r10          { flag = 0 -> arg4 }
    movq $552, %rax          { SYS_fstatat (ino64) }
    syscall
    jae  .Lok_stat
    negq %rax
.Lok_stat:
    ret
end;

function mkdir(Path: PChar; Mode: Integer): Integer;
  assembler; nostackframe;
asm
    movq $136, %rax          { SYS_mkdir }
    syscall
    jae  .Lok_mkdir
    negq %rax
.Lok_mkdir:
    ret
end;

function chmod(Path: PChar; Mode: Integer): Integer;
  assembler; nostackframe;
asm
    movq $15, %rax           { SYS_chmod }
    syscall
    jae  .Lok_chmod
    negq %rax
.Lok_chmod:
    ret
end;

function rmdir(Path: PChar): Integer;
  assembler; nostackframe;
asm
    movq $137, %rax          { SYS_rmdir }
    syscall
    jae  .Lok_rmdir
    negq %rax
.Lok_rmdir:
    ret
end;

function unlink(Path: PChar): Integer;
  assembler; nostackframe;
asm
    movq $10, %rax           { SYS_unlink }
    syscall
    jae  .Lok_unlink
    negq %rax
.Lok_unlink:
    ret
end;

function rename(OldPath, NewPath: PChar): Integer;
  assembler; nostackframe;
asm
    movq $128, %rax          { SYS_rename }
    syscall
    jae  .Lok_rename
    negq %rax
.Lok_rename:
    ret
end;

function chdir(Path: PChar): Integer;
  assembler; nostackframe;
asm
    movq $12, %rax           { SYS_chdir }
    syscall
    jae  .Lok_chdir
    negq %rax
.Lok_chdir:
    ret
end;

function getpid: Integer;
  assembler; nostackframe;
asm
    movq $20, %rax           { SYS_getpid }
    syscall
    ret                      { getpid never fails; no CF translation }
end;

function dup2(OldFd, NewFd: Integer): Integer;
  assembler; nostackframe;
asm
    movq $90, %rax           { SYS_dup2 }
    syscall
    jae  .Lok_dup2
    negq %rax
.Lok_dup2:
    ret
end;

{ pipe(fds) -> pipe2(fds, 0).  Incoming: %rdi=Fds; add flags=0 in %rsi. }
function pipe(Fds: Pointer): Integer;
  assembler; nostackframe;
asm
    xorq %rsi, %rsi          { flags = 0 }
    movq $542, %rax          { SYS_pipe2 }
    syscall
    jae  .Lok_pipe
    negq %rax
.Lok_pipe:
    ret
end;

{ mmap has 6 args; arg4 (Flags) arrives in %rcx (C ABI) but the kernel wants it
  in %r10.  Move it before the syscall.

  Flag translation: the shared allocator (runtime.mem) and other callers pass
  the LINUX MAP_ANONYMOUS bit (0x20); FreeBSD's MAP_ANON is 0x1000.  Without
  MAP_ANON the kernel treats the mapping as file-backed on fd -1 and fails with
  EBADF (then the caller derefs the -errno result and SIGSEGVs).  So if the
  Linux anon bit is set, clear it and set FreeBSD's — keeping runtime.mem
  OS-agnostic (it uses one canonical, Linux-shaped flag set; the per-OS leaf
  reconciles it). 0x1000 already set (e.g. from runtime.start.static.freebsd)
  passes through untouched. }
function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Integer;
             Offset: Int64): Pointer;
  assembler; nostackframe;
asm
    testl $0x20, %ecx        { Linux MAP_ANONYMOUS present? }
    jz   .Lnoanon_mmap
    andl $0xffffffdf, %ecx   { clear 0x20 }
    orl  $0x1000, %ecx       { set FreeBSD MAP_ANON }
.Lnoanon_mmap:
    movq %rcx, %r10
    movq $477, %rax          { SYS_mmap (ino64) }
    syscall
    jae  .Lok_mmap
    negq %rax
.Lok_mmap:
    ret
end;

function munmap(Addr: Pointer; Length: Int64): Integer;
  assembler; nostackframe;
asm
    movq $73, %rax           { SYS_munmap }
    syscall
    jae  .Lok_munmap
    negq %rax
.Lok_munmap:
    ret
end;

function mprotect(Addr: Pointer; Length: Int64; Prot: Integer): Integer;
  assembler; nostackframe;
asm
    movq $74, %rax           { SYS_mprotect }
    syscall
    jae  .Lok_mprotect
    negq %rax
.Lok_mprotect:
    ret
end;

function fcntl(Fd, Cmd, Arg: Integer): Integer;
  assembler; nostackframe;
asm
    movq $92, %rax           { SYS_fcntl }
    syscall
    jae  .Lok_fcntl
    negq %rax
.Lok_fcntl:
    ret
end;

function ioctl(Fd: Integer; Request: Int64; Arg: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $54, %rax           { SYS_ioctl }
    syscall
    jae  .Lok_ioctl
    negq %rax
.Lok_ioctl:
    ret
end;

function kqueue: Integer;
  assembler; nostackframe;
asm
    movq $362, %rax          { SYS_kqueue }
    syscall
    jae  .Lok_kqueue
    negq %rax
.Lok_kqueue:
    ret
end;

{ kevent has 6 args; arg4 (Events) arrives in %rcx -> move to %r10. }
function kevent(Kq: Integer; Changes: Pointer; NChanges: Integer;
                Events: Pointer; NEvents: Integer; Timeout: Pointer): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $560, %rax          { SYS_kevent (FreeBSD-12+ 64-byte struct) }
    syscall
    jae  .Lok_kevent
    negq %rax
.Lok_kevent:
    ret
end;

{ --- sockets (interface note above: the --static profile's Net.Sockets
      surface; recv/send are recvfrom/sendto with nil addresses) --- }

function socket(Domain, Typ, Protocol: Integer): Integer;
  assembler; nostackframe;
asm
    movq $97, %rax           { SYS_socket }
    syscall
    jae  .Lok_socket
    negq %rax
.Lok_socket:
    ret
end;

function bind(Fd: Integer; Addr: Pointer; AddrLen: Integer): Integer;
  assembler; nostackframe;
asm
    movq $104, %rax          { SYS_bind }
    syscall
    jae  .Lok_bind
    negq %rax
.Lok_bind:
    ret
end;

function listen(Fd, Backlog: Integer): Integer;
  assembler; nostackframe;
asm
    movq $106, %rax          { SYS_listen }
    syscall
    jae  .Lok_listen
    negq %rax
.Lok_listen:
    ret
end;

function accept(Fd: Integer; Addr: Pointer; AddrLen: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $30, %rax           { SYS_accept }
    syscall
    jae  .Lok_accept
    negq %rax
.Lok_accept:
    ret
end;

{ accept4 has 4 args; arg4 (Flags) arrives in %rcx -> move to %r10. }
function accept4(Fd: Integer; Addr: Pointer; AddrLen: Pointer;
                 Flags: Integer): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $541, %rax          { SYS_accept4 }
    syscall
    jae  .Lok_accept4
    negq %rax
.Lok_accept4:
    ret
end;

function connect(Fd: Integer; Addr: Pointer; AddrLen: Integer): Integer;
  assembler; nostackframe;
asm
    movq $98, %rax           { SYS_connect }
    syscall
    jae  .Lok_connect
    negq %rax
.Lok_connect:
    ret
end;

{ setsockopt has 5 args, all in registers already (rdi rsi rdx rcx r8);
  arg4 (OptVal) arrives in %rcx -> move to %r10. }
function setsockopt(Fd, Level, OptName: Integer; OptVal: Pointer;
                    OptLen: Integer): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $105, %rax          { SYS_setsockopt }
    syscall
    jae  .Lok_setsockopt
    negq %rax
.Lok_setsockopt:
    ret
end;

{ getsockopt has 5 args; arg4 (OptVal) arrives in %rcx -> move to %r10. }
function getsockopt(Fd, Level, OptName: Integer; OptVal: Pointer;
                    OptLen: Pointer): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $118, %rax          { SYS_getsockopt }
    syscall
    jae  .Lok_getsockopt
    negq %rax
.Lok_getsockopt:
    ret
end;

function getsockname(Fd: Integer; Addr: Pointer; AddrLen: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $32, %rax           { SYS_getsockname }
    syscall
    jae  .Lok_getsockname
    negq %rax
.Lok_getsockname:
    ret
end;

function shutdown(Fd, How: Integer): Integer;
  assembler; nostackframe;
asm
    movq $134, %rax          { SYS_shutdown }
    syscall
    jae  .Lok_shutdown
    negq %rax
.Lok_shutdown:
    ret
end;

{ recv(fd,buf,len,flags) = recvfrom(fd,buf,len,flags,nil,nil): arg4 (Flags)
  arrives in %rcx -> %r10, then zero the from-address pair (%r8/%r9). }
function recv(Fd: Integer; Buf: Pointer; Len: Int64; Flags: Integer): Int64;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    xorq %r8, %r8
    xorq %r9, %r9
    movq $29, %rax           { SYS_recvfrom }
    syscall
    jae  .Lok_recv
    negq %rax
.Lok_recv:
    ret
end;

{ send(fd,buf,len,flags) = sendto(fd,buf,len,flags,nil,0). }
function send(Fd: Integer; Buf: Pointer; Len: Int64; Flags: Integer): Int64;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    xorq %r8, %r8
    xorq %r9, %r9
    movq $133, %rax          { SYS_sendto }
    syscall
    jae  .Lok_send
    negq %rax
.Lok_send:
    ret
end;

function htons(HostShort: UInt16): UInt16;
begin
  Result := UInt16(((HostShort and $FF) shl 8) or (HostShort shr 8));
end;

function ntohs(NetShort: UInt16): UInt16;
begin
  Result := UInt16(((NetShort and $FF) shl 8) or (NetShort shr 8));
end;

{ Raw sigaction(2): sigaction(sig, act, oact). }
function _sys_sigaction(Sig: Integer; Act, OAct: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $416, %rax          { SYS_sigaction }
    syscall
    jae  .Lok_sigaction
    negq %rax
.Lok_sigaction:
    ret
end;

{ FreeBSD struct sigaction: handler @0 (8), sa_flags @8 (4), sa_mask @12
  (sigset_t = 4 x uint32).  signal(3) = sigaction with an empty mask and no
  flags; returns the previous handler (SIG_ERR = -1 cast on failure). }
type
  PPointer = ^Pointer;

function signal(SigNum: Integer; Handler: Pointer): Pointer;
var
  Act: array[0..31] of Byte;
  OAct: array[0..31] of Byte;
  I: Integer;
  P: PPointer;
begin
  for I := 0 to 31 do
  begin
    Act[I] := 0;
    OAct[I] := 0;
  end;
  P := PPointer(@Act[0]);
  P^ := Handler;
  if _sys_sigaction(SigNum, @Act[0], @OAct[0]) <> 0 then
    Exit(Pointer(-1));
  P := PPointer(@OAct[0]);
  Result := P^;
end;

{ mremap: no FreeBSD in-place-remap syscall.  Always return MAP_FAILED (-1) so
  the allocator takes its alloc-new-copy-free fallback (see the interface note). }
function mremap(OldAddr: Pointer; OldSize, NewSize: Int64; Flags: Integer;
               NewAddr: Pointer): Pointer;
begin
  Result := Pointer(-1);
end;

function nanosleep(Req, Rem: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $240, %rax          { SYS_nanosleep }
    syscall
    jae  .Lok_nanosleep
    negq %rax
.Lok_nanosleep:
    ret
end;

function clock_gettime(ClockId: Integer; Ts: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $232, %rax          { SYS_clock_gettime }
    syscall
    jae  .Lok_clock_gettime
    negq %rax
.Lok_clock_gettime:
    ret
end;

{ FreeBSD fork(2) has a two-register return the libc wrapper normalises and a
  raw syscall must replicate: the kernel returns the child pid in %rax for the
  PARENT with %edx = 0, but for the CHILD it returns the PARENT's pid in %rax
  with %edx = 1 as the child indicator.  Without zeroing the child's %eax when
  %edx != 0, the child sees a non-zero "pid" and every `if fork() = 0 then
  (child path)` check runs the PARENT branch in the child — so a spawned
  subprocess never execve's its target and the parent reaps exit 127.  Mirror
  libc: if %edx != 0, this is the child -> return 0. }
function fork: Integer;
  assembler; nostackframe;
asm
    movq $2, %rax            { SYS_fork }
    syscall
    jae  .Lok_fork
    negq %rax
    ret
.Lok_fork:
    testl %edx, %edx         { %edx = 1 in the child, 0 in the parent }
    jz   .Lparent_fork
    xorl %eax, %eax          { child: return 0 }
.Lparent_fork:
    ret
end;

function execve(Path: PChar; Argv, Envp: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $59, %rax           { SYS_execve }
    syscall
    jae  .Lok_execve
    negq %rax
.Lok_execve:
    ret
end;

{ wait4 has 4 args; arg4 (Rusage) arrives in %rcx -> move to %r10. }
function wait4(Pid: Integer; Status: Pointer; Options: Integer;
               Rusage: Pointer): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $7, %rax            { SYS_wait4 }
    syscall
    jae  .Lok_wait4
    negq %rax
.Lok_wait4:
    ret
end;

function kill(Pid, Sig: Integer): Integer;
  assembler; nostackframe;
asm
    movq $37, %rax           { SYS_kill }
    syscall
    jae  .Lok_kill
    negq %rax
.Lok_kill:
    ret
end;

function getrandom(Buf: Pointer; Count: Int64; Flags: Integer): Int64;
  assembler; nostackframe;
asm
    movq $563, %rax          { SYS_getrandom }
    syscall
    jae  .Lok_getrandom
    negq %rax
.Lok_getrandom:
    ret
end;

function sys_getcwd(Buf: PChar; Size: Int64): Int64;
  assembler; nostackframe;
asm
    movq $326, %rax          { SYS___getcwd }
    syscall
    jae  .Lok_getcwd
    negq %rax
.Lok_getcwd:
    ret
end;

{ __sysctl(name, namelen, oldp, oldlenp, newp, newlen) — 6 args; SYS 202.  arg4
  (oldlenp) arrives in %rcx and must move to %r10 (syscall clobbers %rcx). }
function sysctl(Name: Pointer; NameLen: Integer; OldP: Pointer;
                OldLenP: Pointer; NewP: Pointer; NewLen: Int64): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $202, %rax          { SYS___sysctl }
    syscall
    jae  .Lok_sysctl
    negq %rax
.Lok_sysctl:
    ret
end;

{ sysarch(op, parms) — 2 args, both in %rdi/%rsi already; SYS 165.  Used with
  AMD64_SET_FSBASE to set the %fs base to the thread pointer. }
function sysarch(Op: Integer; Parms: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $165, %rax          { SYS_sysarch }
    syscall
    jae  .Lok_sysarch
    negq %rax
.Lok_sysarch:
    ret
end;

{ _umtx_op(obj, op, val, uaddr, uaddr2) — 5 args; arg4 (uaddr) arrives in %rcx
  (C ABI) but the kernel wants it in %r10.  Move it before the syscall.  SYS 454. }
function _umtx_op(Obj: Pointer; Op, Val: Integer; Uaddr, Uaddr2: Pointer): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $454, %rax          { SYS__umtx_op }
    syscall
    jae  .Lok_umtx
    negq %rax
.Lok_umtx:
    ret
end;

{ thr_new(param, param_size) — 2 args, both in %rdi/%rsi already; SYS 455. }
function thr_new(Param: Pointer; ParamSize: Integer): Integer;
  assembler; nostackframe;
asm
    movq $455, %rax          { SYS_thr_new }
    syscall
    jae  .Lok_thr_new
    negq %rax
.Lok_thr_new:
    ret
end;

{ thr_exit(state) — SYS 431.  Terminates JUST this thread; never returns, so no
  CF translation is needed.  State arrives in %rdi (nil in our use). }
procedure thr_exit(State: Pointer); assembler; nostackframe;
asm
    movq $431, %rax          { SYS_thr_exit }
    syscall
    ret
end;

{ _exit(code) — SYS_exit = 1.  Terminates the process; never returns, so no
  CF translation is needed. }
procedure _exit(Code: Integer); assembler; nostackframe;
asm
    movq $1, %rax            { SYS_exit }
    syscall
    ret
end;

end.
