{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.thread.static.linux;

// Real POSIX threads for the --static (libc-free) build, implemented directly on
// the clone(2) and futex(2) syscalls (docs/linux-syscall-migration.adoc).  This
// is the threads leaf that lets a static binary spawn worker threads - the last
// piece needed for the compiler to self-host as a libc-free static ET_EXEC.
//
// DEFINES the bare pthread_* / sysconf names that runtime.weak, runtime.thread
// and classes.pas import via `external name`.  The non-static build resolves the
// same names from libc.so; the --static link swaps in this unit instead.
//
// Mutex: a 3-state futex mutex (Drepper, "Futexes Are Tricky").  The caller's
//   48-byte pthread_mutex_t buffer is reused as the futex word (first Integer):
//   0 = unlocked, 1 = locked (no waiters), 2 = locked (waiters present).
//
// Thread: clone(2) with CLONE_VM|FS|FILES|SIGHAND|THREAD|SYSVSEM|SETTLS plus
//   CLONE_PARENT_SETTID|CHILD_CLEARTID.  Each thread gets a fresh mmap'd stack
//   and its own TLS block (variant II) built from the startup template, so
//   threadvar access (exception frames, the allocator) is per-thread.  The
//   kernel clears the child-tid futex word on thread exit; pthread_join
//   futex-waits on it.
//
// Known limitation: a joined thread's TLS block (mmap'd by BuildThreadTLS) is
// not unmapped - freeing it from the exiting thread is unsafe (the thread runs
// on it until exit) and the join side cannot know its address.  This is a small
// bounded per-thread leak, acceptable for the finite worker pools the compiler
// spawns; a thread-registry sweep can reclaim it later if needed.

interface

uses
  runtime.syscall.linux,        { mmap, futex, clone numbers }
  runtime.start.static.linux;   { BuildThreadTLS - the per-thread TLS template }

{ Mutex - the buffer's first Integer is the futex word. }
function pthread_mutex_init(Mutex, Attr: Pointer): Integer;
function pthread_mutex_lock(Mutex: Pointer): Integer;
function pthread_mutex_unlock(Mutex: Pointer): Integer;
function pthread_mutex_destroy(Mutex: Pointer): Integer;

{ Thread create / join.  *Thread receives an opaque handle (a control-block
  pointer); pthread_join consumes it. }
function pthread_create(Thread, Attr, StartRoutine, Arg: Pointer): Integer;
function pthread_join(Thread: Int64; RetVal: Pointer): Integer;

{ C++-ABI thread-exit registration -- the name the platform layout unit's
  _BlaiseThreadAtExit imports (runtime.mem's thread-exit hook: managed
  threadvar release, then the allocator sweep).  Fn(Arg) runs when the
  calling thread exits, newest first; libc provides the same entry point
  under a dynamic link.  A static worker runs its list from the thread
  trampoline once its start routine returns.  The main thread ends with
  exit_group and never runs its list: runtime.mem covers it through
  __cxa_atexit and the program's own _ThreadVarsRelease.

  This replaced a no-op pthread_key_create / pthread_setspecific pair that
  accepted a destructor and never ran it, so a static worker's arenas were
  never swept and its managed threadvars never released. }
function __cxa_thread_atexit_impl(Fn, Arg, Dso: Pointer): Integer;

{ Run, newest first, and clear the calling thread's exit callbacks. }
procedure _StaticThreadExitRun;

{ sysconf is provided by runtime.libc.linux (sched_getaffinity + popcount); it is
  not redefined here. }

implementation

type
  PInteger = ^Integer;
  PInt64   = ^Int64;

const
  { Mutex futex states. }
  MX_UNLOCKED = 0;
  MX_LOCKED   = 1;
  MX_CONTENDED = 2;

  { futex ops. }
  FUTEX_WAIT = 0;
  FUTEX_WAKE = 1;

  { clone(2) flags for a thread sharing the address space. }
  CLONE_VM             = $00000100;
  CLONE_FS             = $00000200;
  CLONE_FILES          = $00000400;
  CLONE_SIGHAND        = $00000800;
  CLONE_THREAD         = $00010000;
  CLONE_SYSVSEM        = $00040000;
  CLONE_SETTLS         = $00080000;
  CLONE_PARENT_SETTID  = $00100000;
  CLONE_CHILD_CLEARTID = $00200000;
  THREAD_CLONE_FLAGS =
    CLONE_VM or CLONE_FS or CLONE_FILES or CLONE_SIGHAND or
    CLONE_THREAD or CLONE_SYSVSEM or CLONE_SETTLS or
    CLONE_PARENT_SETTID or CLONE_CHILD_CLEARTID;

  PROT_RW      = 3;          { PROT_READ or PROT_WRITE }
  MAP_PRIVANON = $22;        { MAP_PRIVATE or MAP_ANONYMOUS }
  STACK_SIZE   = 1024 * 1024;  { 1 MiB per worker thread }

{ The per-thread control block lives at the base of the mmap'd region.  TidWord
  is the CLONE_CHILD_CLEARTID / CLONE_PARENT_SETTID futex word (the kernel writes
  the new TID here on create and clears it on exit); MapBase/MapSize record the
  region for munmap after join. }
type
  PThreadCB = ^TThreadCB;
  TThreadCB = record
    TidWord:  Integer;
    Pad:      Integer;
    MapBase:  Pointer;
    MapSize:  Int64;
  end;

{ ------------------------------------------------------------------ }
{ Mutex - 3-state futex                                                }
{ ------------------------------------------------------------------ }

{ Atomic compare-and-swap on an Integer: if Ptr^ = Expected set it to NewVal;
  returns the value that was in Ptr^ before the attempt. }
function CAS(Ptr: Pointer; Expected, NewVal: Integer): Integer;
  assembler; nostackframe;
asm
    movl %esi, %eax        { %eax = Expected (cmpxchg compares against %eax) }
    lock cmpxchgl %edx, (%rdi)
    ret
end;

{ Atomic exchange: store NewVal into Ptr^, return the previous value. }
function Xchg(Ptr: Pointer; NewVal: Integer): Integer;
  assembler; nostackframe;
asm
    movl %esi, %eax
    xchgl %eax, (%rdi)
    ret
end;

function pthread_mutex_init(Mutex, Attr: Pointer): Integer;
var
  P: PInteger;
begin
  P := PInteger(Mutex);
  P^ := MX_UNLOCKED;
  Result := 0;
end;

function pthread_mutex_lock(Mutex: Pointer): Integer;
var
  C: Integer;
begin
  { Fast path: uncontended acquire. }
  C := CAS(Mutex, MX_UNLOCKED, MX_LOCKED);
  if C <> MX_UNLOCKED then
  begin
    { Contended.  Mark the lock contended and sleep until it is free. }
    if C <> MX_CONTENDED then
      C := Xchg(Mutex, MX_CONTENDED);
    while C <> MX_UNLOCKED do
    begin
      futex(Mutex, FUTEX_WAIT, MX_CONTENDED, nil, nil, 0);
      C := Xchg(Mutex, MX_CONTENDED);
    end;
  end;
  Result := 0;
end;

function pthread_mutex_unlock(Mutex: Pointer): Integer;
begin
  { If there were waiters (state 2), wake one after releasing. }
  if Xchg(Mutex, MX_UNLOCKED) = MX_CONTENDED then
    futex(Mutex, FUTEX_WAKE, 1, nil, nil, 0);
  Result := 0;
end;

function pthread_mutex_destroy(Mutex: Pointer): Integer;
begin
  Result := 0;
end;

{ ------------------------------------------------------------------ }
{ Thread create / join - clone(2) + futex(2)                          }
{ ------------------------------------------------------------------ }

{ Raw clone of a thread.  Returns the child TID in the parent, 0 in the child.
  The child resumes here on its own stack (ChildStack) with %rax = 0, then this
  routine, in the child branch, calls Entry(EntryArg), runs the thread's exit
  callbacks and exits the thread.

  Args (SysV): %rdi=Flags, %rsi=ChildStack(top), %rdx=ParentTid,
               %rcx=ChildTid, %r8=Tls, %r9=Entry, [stack]=EntryArg.

  The child stack is pre-seeded (below) with Entry and EntryArg so the child can
  reach them after clone without relying on register state surviving across the
  syscall: the child pops them off its own stack. }
function _clone_thread(Flags: Int64; ChildStack, ParentTid, ChildTid,
                       Tls, Entry, EntryArg: Pointer): Int64;
  assembler; nostackframe;
asm
    { Seed Entry and EntryArg onto the child stack; the 7th arg EntryArg }
    { arrived on our stack at 8(%rsp) (return addr at 0(%rsp)). }
    movq 8(%rsp), %rax        { %rax = EntryArg }
    subq $16, %rsi            { %rsi = ChildStack top; grow down for the seeds }
    movq %r9,  0(%rsi)        { [child_sp+0]  = Entry }
    movq %rax, 8(%rsi)        { [child_sp+8]  = EntryArg }

    { clone kernel ABI: arg4 (ChildTid) came in %rcx -> move to %r10. }
    movq %rcx, %r10
    movq $56, %rax            { SYS_clone }
    syscall

    testq %rax, %rax
    jnz   .Lparent            { parent: %rax = child tid }

    { child: on the new stack, %rsp = seeded child_sp. }
    popq %rax                 { %rax = Entry }
    popq %rdi                 { %rdi = EntryArg (1st arg to Entry) }
    xorq %rbp, %rbp           { terminate the call chain for unwinders }
    call *%rax               { Entry(EntryArg) }
    call _StaticThreadExitRun { this thread's exit callbacks }

    { Thread done: exit(0) this thread only (NOT exit_group). }
    xorl %edi, %edi
    movq $60, %rax            { SYS_exit }
    syscall
    hlt

.Lparent:
    ret
end;

function pthread_create(Thread, Attr, StartRoutine, Arg: Pointer): Integer;
var
  Region: Pointer;
  CB: PThreadCB;
  StackTop: Pointer;
  Tls: Pointer;
  Tid: Int64;
  HandleSlot: PInt64;
begin
  { One mapping holds the control block (at the base) and the thread stack
    (above it).  mmap zero-fills, so TidWord starts at 0. }
  Region := mmap(nil, STACK_SIZE, PROT_RW, MAP_PRIVANON, -1, 0);
  if Int64(Region) < 0 then
  begin
    Result := 11;   { EAGAIN }
    Exit;
  end;
  CB := PThreadCB(Region);
  CB^.MapBase := Region;
  CB^.MapSize := STACK_SIZE;

  { Stack grows down from the top of the region; keep it 16-byte aligned. }
  StackTop := Pointer(PChar(Region) + STACK_SIZE);
  StackTop := Pointer(Int64(StackTop) and (not Int64(15)));

  { Each thread needs its own TLS block for threadvar access. }
  Tls := BuildThreadTLS();

  Tid := _clone_thread(THREAD_CLONE_FLAGS, StackTop,
                       @CB^.TidWord,   { CLONE_PARENT_SETTID -> our TidWord }
                       @CB^.TidWord,   { CLONE_CHILD_CLEARTID -> same word }
                       Tls, StartRoutine, Arg);
  if Tid < 0 then
  begin
    munmap(Region, STACK_SIZE);
    FreeThreadTLS(Tls);   { reclaim the per-thread TLS block too }
    Result := 11;   { EAGAIN }
    Exit;
  end;

  { Hand the caller the control-block pointer as the opaque thread handle. }
  HandleSlot := PInt64(Thread);
  HandleSlot^ := Int64(CB);
  Result := 0;
end;

function pthread_join(Thread: Int64; RetVal: Pointer): Integer;
var
  CB: PThreadCB;
  Tid: Integer;
begin
  CB := PThreadCB(Pointer(Thread));
  { The kernel clears TidWord (CLONE_CHILD_CLEARTID) and futex-wakes it when the
    thread exits.  Wait until it reads 0. }
  Tid := CB^.TidWord;
  while Tid <> 0 do
  begin
    futex(@CB^.TidWord, FUTEX_WAIT, Tid, nil, nil, 0);
    Tid := CB^.TidWord;
  end;
  munmap(CB^.MapBase, CB^.MapSize);
  Result := 0;
end;

{ Per-thread exit callbacks (see the interface comment).  runtime.mem
  registers one per thread; the headroom is for callers of the C++ ABI. }
const
  MAX_THREAD_EXIT = 8;
  ENOMEM_ERR = 12;

type
  TThreadExitProc = procedure(Arg: Pointer);

threadvar
  ThreadExitFn: array[0..7] of Pointer;
  ThreadExitArg: array[0..7] of Pointer;
  ThreadExitCount: Integer;

function __cxa_thread_atexit_impl(Fn, Arg, Dso: Pointer): Integer;
begin
  if ThreadExitCount >= MAX_THREAD_EXIT then
  begin
    Result := ENOMEM_ERR;
    Exit;
  end;
  ThreadExitFn[ThreadExitCount] := Fn;
  ThreadExitArg[ThreadExitCount] := Arg;
  ThreadExitCount := ThreadExitCount + 1;
  Result := 0;
end;

procedure _StaticThreadExitRun;
var
  F: TThreadExitProc;
begin
  { a callback may register another, so the count is re-read each round }
  while ThreadExitCount > 0 do
  begin
    ThreadExitCount := ThreadExitCount - 1;
    F := TThreadExitProc(ThreadExitFn[ThreadExitCount]);
    F(ThreadExitArg[ThreadExitCount]);
  end;
end;

end.
