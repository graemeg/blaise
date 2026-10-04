{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit async.fibers.context;

// L0 of the fiber runtime (docs/async-networking-design.adoc): the
// context-switch leaf, fresh-fiber bootstrap (trampoline), and guard-page
// stack allocation with a per-thread stack pool.
//
// A fiber is a stack plus a saved register context.  FiberSwapAsm saves the
// callee-saved set onto the CURRENT fiber's own stack, stores the stack
// pointer into the outgoing context, loads the incoming context's stack
// pointer and restores the same set -- the context is a single saved stack
// pointer (the Go/boost.context model), a bidirectional generalisation of
// runtime.setjmp.
//
// CPU-SPECIFIC PARTS (selected by {$IFDEF CPUARM64}): only FiberSwapAsm, the
// synthetic first frame built by FiberSpawn, and the guard-page size.
//   x86-64 (System V): rbx, rbp, r12-r15 pushed; the return address is the
//     resume point; 4 KiB pages.
//   AArch64 (AAPCS64): x19-x28, x29 (fp), x30 (lr) and d8-d15 saved in a
//     160-byte block; `ret` resumes through the restored x30; 16 KiB guard
//     page, because Apple Silicon pages are 16 KiB -- a 4 KiB guard would
//     make mprotect round up and fence off the first usable bytes.
// Everything else here is CPU-neutral.
//
// NATIVE BACKEND ONLY: the switch leaf is an inline `asm` body, which the QBE
// backend rejects with "inline asm blocks require the native backend
// (--backend native)" — that diagnostic is the compile-time guard the design
// calls for.  Programs using this unit must be built with the native backend
// (the default since v0.12.0).
//
// Stacks are mmap'd with one PROT_NONE guard page at the low end (stacks grow
// down), so overflow faults deterministically instead of silently corrupting
// a neighbouring allocation.  Retired stacks go to a per-thread free list to
// avoid mmap/munmap churn on hot spawn paths.
//
// Adding a CPU is one more {$IFDEF} arm of the three CPU-specific parts;
// nothing here is OS-specific beyond the anonymous-mmap flag, which comes
// from the _MapAnonFlag link-time seam (rtl.platform.layout.<os>) -- same as
// runtime.mem.

interface

type
  { Saved context.  SP is the register context (the callee-saved registers
    and return address live on the fiber's own stack; FiberSwapAsm reads and
    writes ONLY the SP field, which must stay first).

    ExcTop/ExcCurrent are the per-fiber snapshot of the exception machine's
    threadvars (runtime.exc g_exc_top / g_current_exception — design P1):
    those are per OS thread and shared by every fiber on it, so FiberSwitch
    saves the outgoing fiber's pair here and reinstates the incoming
    fiber's.  Without that, a try across a suspension chains frames across
    fiber stacks and a raise longjmps into a suspended or stale frame. }
  PFiberContext = ^TFiberContext;
  TFiberContext = record
    SP: Pointer;
    ExcTop: Pointer;
    ExcCurrent: Pointer;
  end;

  { Fiber entry procedure. }
  TFiberProc = procedure(AArg: Pointer);

  { Fiber control block. }
  PFiber = ^TFiber;
  TFiber = record
    Ctx: TFiberContext;
    StackBase: Pointer;    { mmap base — the guard page starts here; nil for
                             the main-context pseudo-fiber }
    StackTotal: Int64;     { total mapped bytes including the guard page }
    EntryProc: TFiberProc;
    EntryArg: Pointer;
    ReturnTo: PFiber;      { where the trampoline swaps to when EntryProc
                             returns; updated on every switch into the fiber }
    Done: Boolean;
  end;

const
  FiberDefaultStackSize = 65536;   { usable bytes; one guard page extra }
{$IFDEF CPUARM64}
  FiberPageSize = 16384;           { Apple Silicon page size (also a multiple
                                     of the 4 KiB Linux/arm64 page) }
{$ELSE}
  FiberPageSize = 4096;
{$ENDIF}

{ Wrap the calling context (usually the program's main thread) in a control
  block so it can be a FiberSwitch source/target.  Sets the current fiber. }
function FiberCreateMain: PFiber;

{ Create a fiber that will run AProc(AArg) when first switched to.
  AStackSize is the usable stack size in bytes (0 = FiberDefaultStackSize);
  it is rounded up to page granularity, and one guard page is added below.
  Returns nil if the stack cannot be mapped. }
function FiberSpawn(AProc: TFiberProc; AArg: Pointer;
  AStackSize: Int64): PFiber;

{ Save the current context into AFrom, resume ATo.  When something later
  switches back to AFrom, FiberSwitch returns normally.  Also maintains
  CurrentFiber and ATo's ReturnTo (= AFrom). }
procedure FiberSwitch(AFrom, ATo: PFiber);

{ The fiber currently executing on this thread (nil before FiberCreateMain). }
function CurrentFiber: PFiber;

{ True once the fiber's entry procedure has returned. }
function FiberIsDone(AFib: PFiber): Boolean;

{ Release a fiber's stack (to the pool) and its control block.  Never free a
  fiber that has not finished (its stack still holds live frames). }
procedure FiberFree(AFib: PFiber);

{ --- stack allocation + pool (exposed for the runtime tests) --------------- }

{ Map a stack of AUsable bytes (page-rounded) plus one PROT_NONE guard page at
  the low end.  Returns the mmap base (= guard page) and the total mapped size
  in ATotal, or nil on failure.  Serves from the per-thread pool when a stack
  of the same total size is available. }
function FiberStackAcquire(AUsable: Int64; out ATotal: Int64): Pointer;

{ Return a stack to the per-thread pool (or unmap it when the pool is full). }
procedure FiberStackReturn(ABase: Pointer; ATotal: Int64);

{ Number of stacks currently parked in this thread's pool. }
function FiberStackPoolCount: Integer;

implementation

function _libc_mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Integer;
  Offset: Int64): Pointer; external name 'mmap';
function _libc_munmap(Addr: Pointer; Length: Int64): Integer;
  external name 'munmap';
function _libc_mprotect(Addr: Pointer; Length: Int64; Prot: Integer): Integer;
  external name 'mprotect';
procedure _libc_abort; external name 'abort';

{ Per-OS anonymous-mapping flag (Linux $20, FreeBSD $1000), resolved at link
  time from rtl.platform.layout.<os> — the same seam runtime.mem uses.  The
  libc profile binds the real libc mmap, so the flag must be OS-correct here
  (the static-profile syscall leaf would translate, but libc does not). }
function _MapAnonFlag: Integer; external name '_MapAnonFlag';

{ Exception-state snapshot hooks exported by runtime.exc (design P1). }
function _ExcGetTop: Pointer; external name '_ExcGetTop';
procedure _ExcSetTop(AFrame: Pointer); external name '_ExcSetTop';
function _ExcGetCurrent: Pointer; external name '_ExcGetCurrent';
procedure _ExcSetCurrent(AExc: Pointer); external name '_ExcSetCurrent';

const
  PROT_NONE = 0;
  PROT_READ = 1;
  PROT_WRITE = 2;
  MAP_PRIVATE = 2;
  POOL_MAX = 16;

type
  PPointer = ^Pointer;
  PInt64 = ^Int64;

  { Free-list node stored INSIDE the pooled stack's usable region (just above
    the guard page — the far end from the hot stack top). }
  PStackNode = ^TStackNode;
  TStackNode = record
    Next: PStackNode;
    Total: Int64;
  end;

threadvar
  GCurrentFiber: PFiber;
  GStackPool: PStackNode;
  GStackPoolCount: Integer;

{ ---------------------------------------------------------------------------
  The context-switch leaf.  `nostackframe` so the body owns the frame,
  exactly as runtime.setjmp does.
  --------------------------------------------------------------------------- }
{$IFDEF CPUARM64}
{ x0 = ACur, x1 = ANext.  The 160-byte save block (16-byte aligned, as sp
  must always be on AArch64):
    +0..+72  x19..x28    +80 x29 (fp)   +88 x30 (lr = resume address)
    +96..+152 d8..d15 (the callee-saved low halves of v8-v15) }
procedure FiberSwapAsm(ACur, ANext: PFiberContext); assembler; nostackframe;
asm
    sub sp, sp, #160
    stp x19, x20, [sp]
    stp x21, x22, [sp, #16]
    stp x23, x24, [sp, #32]
    stp x25, x26, [sp, #48]
    stp x27, x28, [sp, #64]
    stp x29, x30, [sp, #80]
    str d8, [sp, #96]
    str d9, [sp, #104]
    str d10, [sp, #112]
    str d11, [sp, #120]
    str d12, [sp, #128]
    str d13, [sp, #136]
    str d14, [sp, #144]
    str d15, [sp, #152]
    mov x9, sp
    str x9, [x0]
    ldr x9, [x1]
    mov sp, x9
    ldp x19, x20, [sp]
    ldp x21, x22, [sp, #16]
    ldp x23, x24, [sp, #32]
    ldp x25, x26, [sp, #48]
    ldp x27, x28, [sp, #64]
    ldp x29, x30, [sp, #80]
    ldr d8, [sp, #96]
    ldr d9, [sp, #104]
    ldr d10, [sp, #112]
    ldr d11, [sp, #120]
    ldr d12, [sp, #128]
    ldr d13, [sp, #136]
    ldr d14, [sp, #144]
    ldr d15, [sp, #152]
    add sp, sp, #160
    ret
end;
{$ELSE}
{ %rdi = ACur, %rsi = ANext. }
procedure FiberSwapAsm(ACur, ANext: PFiberContext); assembler; nostackframe;
asm
    pushq %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    movq  %rsp, (%rdi)      # ACur^.SP := RSP (return addr already on stack)
    movq  (%rsi), %rsp      # RSP := ANext^.SP
    popq  %r15
    popq  %r14
    popq  %r13
    popq  %r12
    popq  %rbx
    popq  %rbp
    ret                     # jump to ANext's saved return address
end;
{$ENDIF}

{ ---------------------------------------------------------------------------
  Stack allocation + pool
  --------------------------------------------------------------------------- }

function PageRound(N: Int64): Int64;
begin
  Result := (N + Int64(FiberPageSize - 1)) and (not Int64(FiberPageSize - 1));
end;

function FiberStackAcquire(AUsable: Int64; out ATotal: Int64): Pointer;
var
  Total: Int64;
  Node: PStackNode;
  Prev: PStackNode;
  Base: Pointer;
begin
  if AUsable <= 0 then
    AUsable := FiberDefaultStackSize;
  Total := PageRound(AUsable) + FiberPageSize;
  ATotal := Total;

  { Pool hit: first node of the same total size. }
  Prev := nil;
  Node := GStackPool;
  while Node <> nil do
  begin
    if Node^.Total = Total then
    begin
      if Prev = nil then
        GStackPool := Node^.Next
      else
        Prev^.Next := Node^.Next;
      GStackPoolCount := GStackPoolCount - 1;
      { The node sits at base + one page (lowest usable bytes). }
      Exit(Pointer(Node) - FiberPageSize);
    end;
    Prev := Node;
    Node := Node^.Next;
  end;

  { Fresh mapping: RW everywhere, then revoke the low page as the guard. }
  Base := _libc_mmap(nil, Total, PROT_READ or PROT_WRITE,
    MAP_PRIVATE or _MapAnonFlag(), -1, 0);
  if (Base = nil) or (Base = Pointer(-1)) then
    Exit(nil);
  if _libc_mprotect(Base, FiberPageSize, PROT_NONE) <> 0 then
  begin
    _libc_munmap(Base, Total);
    Exit(nil);
  end;
  Result := Base;
end;

procedure FiberStackReturn(ABase: Pointer; ATotal: Int64);
var
  Node: PStackNode;
begin
  if ABase = nil then Exit;
  if GStackPoolCount >= POOL_MAX then
  begin
    _libc_munmap(ABase, ATotal);
    Exit;
  end;
  Node := PStackNode(ABase + FiberPageSize);
  Node^.Next := GStackPool;
  Node^.Total := ATotal;
  GStackPool := Node;
  GStackPoolCount := GStackPoolCount + 1;
end;

function FiberStackPoolCount: Integer;
begin
  Result := GStackPoolCount;
end;

{ ---------------------------------------------------------------------------
  Bootstrap: trampoline + synthetic first frame
  --------------------------------------------------------------------------- }

{ First code a fresh fiber runs (entered via FiberSwapAsm's `ret`).  Reads the
  entry proc + argument from the control block (inline asm cannot reference
  Pascal locals, so everything beyond the frame synthesis stays in Pascal).
  When the entry proc returns the fiber is dead: mark it and swap to whoever
  last resumed it.  A dead fiber must never be switched into again. }
procedure FiberTrampoline;
var
  F: PFiber;
  Proc: TFiberProc;
  Arg: Pointer;
begin
  F := GCurrentFiber;
  Proc := F^.EntryProc;
  Arg := F^.EntryArg;
  Proc(Arg);
  F^.Done := True;
  FiberSwitch(F, F^.ReturnTo);
  { Unreachable: nothing may resume a Done fiber. }
  _libc_abort();
end;

function FiberSpawn(AProc: TFiberProc; AArg: Pointer;
  AStackSize: Int64): PFiber;
type
  TPlainProc = procedure;
var
  F: PFiber;
  Base: Pointer;
  Total: Int64;
  Top: Pointer;
  SP: PPointer;
  Tramp: TPlainProc;
  I: Integer;
begin
  Base := FiberStackAcquire(AStackSize, Total);
  if Base = nil then
    Exit(nil);
  F := GetMem(SizeOf(TFiber));
  { Fresh fiber: empty exception chain, no current exception (P1). }
  F^.Ctx.ExcTop := nil;
  F^.Ctx.ExcCurrent := nil;
  F^.StackBase := Base;
  F^.StackTotal := Total;
  F^.EntryProc := AProc;
  F^.EntryArg := AArg;
  F^.ReturnTo := nil;
  F^.Done := False;

  Top := Base + Total;
  Top := Pointer(PtrUInt(Top) and PtrUInt($FFFFFFFFFFFFFFF0));
  Tramp := @FiberTrampoline;
{$IFDEF CPUARM64}
  { Synthetic first frame: one zeroed 160-byte save block (FiberSwapAsm's
    layout) at Top-160, with x30 = @FiberTrampoline and x29 = 0 (ends the
    frame-pointer chain).  After the restores `add sp, sp, #160` leaves
    sp = Top -- 16-byte aligned, as AAPCS64 requires at every call -- and
    `ret` branches to the trampoline through x30. }
  for I := 1 to 20 do
  begin
    SP := PPointer(Top - I * 8);
    SP^ := nil;
  end;
  SP := PPointer(Top - 160 + 88);
  SP^ := Pointer(Tramp);
  F^.Ctx.SP := Top - 160;
{$ELSE}
  { Synthetic first frame.  Layout from the 16-byte-aligned top:
      [Top-8]  0                sentinel slot; also trampoline frame padding
      [Top-16] @FiberTrampoline FiberSwapAsm's `ret` target
      [Top-64..Top-24] 0        six callee-saved slots (rbp..r15)
    SP = Top-64, so after the six pops RSP = Top-16, `ret` lands in the
    trampoline with RSP = Top-8 — i.e. RSP mod 16 = 8, the SysV call-entry
    alignment. }
  SP := PPointer(Top - 8);
  SP^ := nil;
  SP := PPointer(Top - 16);
  SP^ := Pointer(Tramp);
  for I := 3 to 8 do
  begin
    SP := PPointer(Top - I * 8);
    SP^ := nil;
  end;
  F^.Ctx.SP := Top - 64;
{$ENDIF}
  Result := F;
end;

function FiberCreateMain: PFiber;
var
  F: PFiber;
begin
  F := GetMem(SizeOf(TFiber));
  F^.Ctx.SP := nil;
  { The main context's exception snapshot is captured on its first switch
    away; start empty. }
  F^.Ctx.ExcTop := nil;
  F^.Ctx.ExcCurrent := nil;
  F^.StackBase := nil;
  F^.StackTotal := 0;
  F^.EntryProc := nil;
  F^.EntryArg := nil;
  F^.ReturnTo := nil;
  F^.Done := False;
  GCurrentFiber := F;
  Result := F;
end;

procedure FiberSwitch(AFrom, ATo: PFiber);
begin
  ATo^.ReturnTo := AFrom;
  { Per-fiber exception state (P1): the register swap alone is not the whole
    context.  Snapshot the outgoing fiber's exception-chain head + current
    exception into its control block and reinstate the incoming fiber's,
    so try/finally and raise work correctly across the suspension point. }
  AFrom^.Ctx.ExcTop := _ExcGetTop();
  AFrom^.Ctx.ExcCurrent := _ExcGetCurrent();
  _ExcSetTop(ATo^.Ctx.ExcTop);
  _ExcSetCurrent(ATo^.Ctx.ExcCurrent);
  GCurrentFiber := ATo;
  FiberSwapAsm(@AFrom^.Ctx, @ATo^.Ctx);
  { Someone switched back into AFrom: it is current again (its resumer's
    FiberSwitch already set GCurrentFiber := AFrom and reinstated AFrom's
    exception state before the swap). }
end;

function CurrentFiber: PFiber;
begin
  Result := GCurrentFiber;
end;

function FiberIsDone(AFib: PFiber): Boolean;
begin
  Result := AFib^.Done;
end;

procedure FiberFree(AFib: PFiber);
begin
  if AFib = nil then Exit;
  if AFib^.StackBase <> nil then
    FiberStackReturn(AFib^.StackBase, AFib^.StackTotal);
  FreeMem(AFib);
end;

end.
