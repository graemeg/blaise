{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.thread.static.freebsd;

// Real POSIX threads for the FreeBSD --static (libc-free) build, implemented
// directly on the thr_new(2) and _umtx_op(2) syscalls
// (docs/freebsd-x86_64-backend-design.adoc, Step 4c).  The FreeBSD sibling of
// runtime.thread.static.linux — the threads leaf that lets a static FreeBSD
// binary spawn worker threads (the compiler's TCompileWorker = class(TThread)).
//
// DEFINES the bare pthread_* names that runtime.weak, runtime.thread and
// classes.pas import via `external name`.  The FreeBSD RTL composition links
// this unit (the link-time swap) in place of the Linux thread leaf / libc.
//
// Mutex: TARGET-INVARIANT — a 3-state futex mutex (Drepper, "Futexes Are
//   Tricky"), copied verbatim from the Linux unit.  The caller's mutex buffer is
//   reused as the wait word (first Integer): 0 = unlocked, 1 = locked (no
//   waiters), 2 = locked (waiters present).  ONLY the kernel wait/wake primitive
//   differs: Linux futex(WAIT/WAKE) -> FreeBSD _umtx_op(WAIT_UINT_PRIVATE=15 /
//   WAKE_PRIVATE=16).  WAIT_UINT returns at once if *word <> val (like futex), so
//   the loop structure is identical.
//
// Thread: thr_new(2) with a filled `struct thr_param` (amd64 sizeof = 104).  Each
//   thread gets a fresh mmap'd stack + its own variant-II TLS block (built from
//   the startup template; installed as the new thread's %fs base via thr_param's
//   tls_base) so threadvar access (exception frames, the allocator) is per-thread.
//
// JOIN — the key FreeBSD difference from Linux.  thr_new provides NO
//   CLONE_CHILD_CLEARTID-style "clear-and-wake the tid word on exit"; child_tid is
//   only written ONCE, on create, and never cleared on exit.  So we use a dedicated
//   JOIN word in the control block: the child's exit trampoline sets JoinWord = 1
//   and _umtx_op-WAKEs it as its LAST act before thr_exit; pthread_join
//   _umtx_op-WAITs on it while it reads 0.  thr_exit (SYS 431) terminates JUST the
//   thread — NOT exit(2)/SYS_exit, which would kill the whole process.
//
// Known limitation (same as the Linux leaf): a joined thread's TLS block is not
// unmapped — freeing it from the exiting thread is unsafe (the thread runs on it
// until thr_exit) and the join side cannot know its address.  A small bounded
// per-thread leak, acceptable for the finite worker pools the compiler spawns.

interface

uses
  runtime.syscall.freebsd,        { mmap, _umtx_op, thr_new, thr_exit numbers }
  runtime.start.static.freebsd;   { BuildThreadTLS - the per-thread TLS template }

{ Mutex - the buffer's first Integer is the wait word. }
function pthread_mutex_init(Mutex, Attr: Pointer): Int;
function pthread_mutex_lock(Mutex: Pointer): Int;
function pthread_mutex_unlock(Mutex: Pointer): Int;
function pthread_mutex_destroy(Mutex: Pointer): Int;

{ Thread create / join.  *Thread receives an opaque handle (a control-block
  pointer); pthread_join consumes it. }
function pthread_create(Thread, Attr, StartRoutine, Arg: Pointer): Int;
function pthread_join(Thread: Int64; RetVal: Pointer): Int;

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
function __cxa_thread_atexit_impl(Fn, Arg, Dso: Pointer): Int32;

{ Run, newest first, and clear the calling thread's exit callbacks. }
procedure _StaticThreadExitRun;

implementation

type
  PInteger = ^Int32;
  PInt64   = ^Int64;

const
  { Mutex wait-word states. }
  MX_UNLOCKED = 0;
  MX_LOCKED   = 1;
  MX_CONTENDED = 2;

  { _umtx_op operations (FreeBSD 14 sys/sys/umtx.h; verified). }
  UMTX_OP_WAIT_UINT_PRIVATE = 15;   { block while *obj = val }
  UMTX_OP_WAKE_PRIVATE      = 16;   { wake up to `val` waiters on obj }

  PROT_RW      = 3;          { PROT_READ or PROT_WRITE }
  MAP_PRIVANON = $1002;      { FreeBSD MAP_PRIVATE ($0002) or MAP_ANON ($1000) }
  STACK_SIZE   = 1024 * 1024;  { 1 MiB per worker thread }

  { struct thr_param amd64 field offsets (FreeBSD 14 sys/sys/thr.h; verified). }
  TP_START_FUNC  = 0;    { void (*)(void*) }
  TP_ARG         = 8;    { void*  }
  TP_STACK_BASE  = 16;   { char*  }
  TP_STACK_SIZE  = 24;   { size_t }
  TP_TLS_BASE    = 32;   { char*  }
  TP_TLS_SIZE    = 40;   { size_t }
  TP_CHILD_TID   = 48;   { long*  }
  TP_PARENT_TID  = 56;   { long*  }
  TP_FLAGS       = 64;   { int (+ 4 bytes pad) }
  TP_RTP         = 72;   { struct rtprio* }
  TP_SPARE0      = 80;   { void*[3] -> 80,88,96 }
  THR_PARAM_SIZE = 104;  { sizeof(struct thr_param) on amd64 }

{ The per-thread control block lives at the base of the mmap'd region.
  StartRoutine/Arg are the real entry the trampoline calls; JoinWord is the
  _umtx_op join word (child sets 1 + WAKEs on exit, parent WAITs while it reads 0);
  TidWord is thr_new's child_tid (LONG* = 8 bytes on FreeBSD, so Int64 — the
  kernel writes the 8-byte TID here on create; unlike Linux it is NOT cleared on
  exit, hence the separate JoinWord).  MapBase/MapSize record the region for
  munmap after join. }
type
  PThreadCB = ^TThreadCB;
  TThreadCB = record
    StartRoutine: Pointer;
    Arg:          Pointer;
    JoinWord:     Int32;
    Pad:          Int32;
    TidWord:      Int64;
    MapBase:      Pointer;
    MapSize:      Int64;
  end;

{ ------------------------------------------------------------------ }
{ Mutex - 3-state futex (TARGET-INVARIANT; copied from the Linux leaf) }
{ ------------------------------------------------------------------ }

{ Atomic compare-and-swap on an Integer: if Ptr^ = Expected set it to NewVal;
  returns the value that was in Ptr^ before the attempt. }
function CAS(Ptr: Pointer; Expected, NewVal: Int32): Int32;
  assembler; nostackframe;
asm
    movl %esi, %eax        { %eax = Expected (cmpxchg compares against %eax) }
    lock cmpxchgl %edx, (%rdi)
    ret
end;

{ Atomic exchange: store NewVal into Ptr^, return the previous value. }
function Xchg(Ptr: Pointer; NewVal: Int32): Int32;
  assembler; nostackframe;
asm
    movl %esi, %eax
    xchgl %eax, (%rdi)
    ret
end;

function pthread_mutex_init(Mutex, Attr: Pointer): Int;
var
  P: PInteger;
begin
  P := PInteger(Mutex);
  P^ := MX_UNLOCKED;
  Result := 0;
end;

function pthread_mutex_lock(Mutex: Pointer): Int;
var
  C: Int;
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
      { WAIT_UINT_PRIVATE blocks while *Mutex = MX_CONTENDED (returns at once if
        it already changed) — the FreeBSD analogue of FUTEX_WAIT. }
      _umtx_op(Mutex, UMTX_OP_WAIT_UINT_PRIVATE, MX_CONTENDED, nil, nil);
      C := Xchg(Mutex, MX_CONTENDED);
    end;
  end;
  Result := 0;
end;

function pthread_mutex_unlock(Mutex: Pointer): Int;
begin
  { If there were waiters (state 2), wake one after releasing. }
  if Xchg(Mutex, MX_UNLOCKED) = MX_CONTENDED then
    _umtx_op(Mutex, UMTX_OP_WAKE_PRIVATE, 1, nil, nil);
  Result := 0;
end;

function pthread_mutex_destroy(Mutex: Pointer): Int;
begin
  Result := 0;
end;

{ ------------------------------------------------------------------ }
{ Thread create / join - thr_new(2) + _umtx_op(2)                     }
{ ------------------------------------------------------------------ }

{ Call Entry(Arg) — a raw indirect call so the trampoline can invoke the
  caller-supplied StartRoutine held only as a Pointer.  Entry arrives in %rdi,
  Arg in %rsi; shuffle Arg to %rdi and call Entry. }
procedure CallEntry(Entry, Arg: Pointer); assembler; nostackframe;
asm
    movq %rdi, %r11          { Entry }
    movq %rsi, %rdi          { Arg -> first arg }
    call *%r11              { Entry(Arg) }
    ret
end;

{ The thread's entry point (thr_param.start_func).  The kernel starts the new
  thread here with %rdi = thr_param.arg (our control-block pointer), on the fresh
  stack, with the thread's own %fs already installed (tls_base).  We call the real
  StartRoutine(Arg) and the thread's exit callbacks, then set JoinWord = 1 and _umtx_op-WAKE it so pthread_join
  unblocks, then thr_exit(nil) to terminate JUST this thread. }
procedure _thr_trampoline(CBPtr: Pointer);
var
  CB: PThreadCB;
  Entry: Pointer;
begin
  CB := PThreadCB(CBPtr);
  Entry := CB^.StartRoutine;
  CallEntry(Entry, CB^.Arg);
  _StaticThreadExitRun();
  { Terminate this thread AND signal the joiner in one kernel step: pass the
    join word as thr_exit's `state`.  The kernel does `suword(state, 1)` +
    umtx-wake on it AFTER the thread has stopped executing on its stack — so the
    joiner cannot free the stack while this thread is still running on it.  (The
    previous code set JoinWord + WAKEd here, on the stack, BEFORE thr_exit, which
    let pthread_join munmap the shared stack/CB region out from under this still-
    live thread → SIGSEGV during teardown.  Never touch the stack after the wake;
    let thr_exit's kernel-side wake be the last event on this word.) }
  thr_exit(@CB^.JoinWord);
end;

{ Store an 8-byte value at Base + Offset (used to fill struct thr_param). }
procedure PokeQ(Base: Pointer; Offset: Int; Value: Int64);
var
  Slot: PInt64;
begin
  Slot := PInt64(Pointer(PChar(Base) + Offset));
  Slot^ := Value;
end;

function pthread_create(Thread, Attr, StartRoutine, Arg: Pointer): Int;
var
  Region: Pointer;
  CB: PThreadCB;
  StackTop: Pointer;
  Tls: Pointer;
  Param: array[0..THR_PARAM_SIZE - 1] of Byte;
  ParamP: Pointer;
  R: Int;
  HandleSlot: PInt64;
begin
  { One mapping holds the control block (at the base) and the thread stack
    (above it).  mmap zero-fills, so JoinWord starts at 0. }
  Region := mmap(nil, STACK_SIZE, PROT_RW, MAP_PRIVANON, -1, 0);
  if Int64(Region) < 0 then
  begin
    Result := 11;   { EAGAIN }
    Exit;
  end;
  CB := PThreadCB(Region);
  CB^.StartRoutine := StartRoutine;
  CB^.Arg := Arg;
  CB^.JoinWord := 0;
  CB^.TidWord := 0;
  CB^.MapBase := Region;
  CB^.MapSize := STACK_SIZE;

  { Stack grows down from the top of the region; keep it 16-byte aligned. }
  StackTop := Pointer(PChar(Region) + STACK_SIZE);
  StackTop := Pointer(Int64(StackTop) and (not Int64(15)));

  { Each thread needs its own TLS block for threadvar access. }
  Tls := BuildThreadTLS();

  { Fill struct thr_param on the stack (zero-init first so flags/rtp/spare = 0). }
  ParamP := @Param[0];
  PokeQ(ParamP, TP_START_FUNC, Int64(Pointer(@_thr_trampoline)));
  PokeQ(ParamP, TP_ARG,        Int64(CB));
  PokeQ(ParamP, TP_STACK_BASE, Int64(Region));
  { stack_size = distance from the region base to the aligned stack top. }
  PokeQ(ParamP, TP_STACK_SIZE, Int64(StackTop) - Int64(Region));
  PokeQ(ParamP, TP_TLS_BASE,   Int64(Tls));
  PokeQ(ParamP, TP_TLS_SIZE,   ThreadTLSSize());
  PokeQ(ParamP, TP_CHILD_TID,  Int64(@CB^.TidWord));
  PokeQ(ParamP, TP_PARENT_TID, Int64(@CB^.TidWord));
  PokeQ(ParamP, TP_FLAGS,      0);           { flags = 0 (+ pad) }
  PokeQ(ParamP, TP_RTP,        0);           { rtp = nil -> default scheduling }
  PokeQ(ParamP, TP_SPARE0,     0);
  PokeQ(ParamP, TP_SPARE0 + 8,  0);
  PokeQ(ParamP, TP_SPARE0 + 16, 0);

  R := thr_new(ParamP, THR_PARAM_SIZE);
  if R < 0 then
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

function pthread_join(Thread: Int64; RetVal: Pointer): Int;
var
  CB: PThreadCB;
  W: Int;
begin
  CB := PThreadCB(Pointer(Thread));
  { The child sets JoinWord = 1 and _umtx_op-WAKEs it as its last act before
    thr_exit.  WAIT while it still reads 0.  WAIT_UINT returns at once if the word
    already changed, so no wake can be missed. }
  W := CB^.JoinWord;
  while W = 0 do
  begin
    _umtx_op(@CB^.JoinWord, UMTX_OP_WAIT_UINT_PRIVATE, 0, nil, nil);
    W := CB^.JoinWord;
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
  ThreadExitCount: Int;

function __cxa_thread_atexit_impl(Fn, Arg, Dso: Pointer): Int32;
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
