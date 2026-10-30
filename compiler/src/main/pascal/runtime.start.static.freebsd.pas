{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.start.static.freebsd;

// Freestanding _start for a static, libc-free FreeBSD ET_EXEC (the FreeBSD
// kernel-leaf swap; docs/freebsd-x86_64-backend-design.adoc, Step 3/4c).
//
// The FreeBSD sibling of runtime.start.static.linux.  A tiny asm trampoline
// captures the initial stack pointer and tail-calls the Pascal _BlaiseStartC,
// which:
//   1. parses argc / argv / envp (the kernel's initial stack);
//   2. sets up the static TLS block and the thread pointer (%fs) — required
//      before any threadvar (%fs-relative) access, which a static binary's
//      kernel does NOT do for us;
//   3. captures `environ`;
//   4. calls main(argc, argv);
//   5. exits via the FreeBSD `exit` syscall (main itself calls exit, so this
//      is a guard).
//
// FreeBSD's process entry stack has the SAME shape as Linux: %rsp points at
// argc, followed by argv[0..argc-1], a NULL, envp[], a NULL, then the ELF auxv.
// (FreeBSD additionally passes an rtld cleanup pointer in %rdx for dynamic
// binaries; it is 0 for a static ET_EXEC and we ignore it.)
//
// TLS setup locates PT_TLS via the program headers, which SetupTLS reads
// DIRECTLY from this binary's own ELF header at the fixed non-PIE load base
// ($400000) rather than via the kernel auxv AT_PHDR entry — a non-PIE ET_EXEC
// always maps its header there, so this is exact and needs no auxv (identical
// on Linux and FreeBSD).  x86-64 TLS is variant II on both.  The ONE FreeBSD
// difference is how the %fs base is installed: Linux uses arch_prctl(
// ARCH_SET_FS, tp); FreeBSD uses sysarch(AMD64_SET_FSBASE, &tp) — note it takes
// a POINTER to the base value, not the value itself.
//
// x86-64 TLS (variant II): the thread pointer points at the TCB, which sits
// ABOVE the TLS block; threadvars are at negative offsets from the TP.  %fs:0
// must hold the TP value itself (the TCB self-pointer).  Layout we build:
//     [ TLS block: memsz bytes ][ TCB: 8-byte self-pointer ]
//   tp = block + memsz_aligned ; %fs = tp ; *(void**)tp = tp.

interface

uses
  runtime.syscall.freebsd;   { _exit, sysarch, mmap/munmap + the `environ` global }

procedure _start;

{ The static TLS template, captured from PT_TLS at startup so each spawned thread
  can build its own TLS block (runtime.thread.static.freebsd uses these via
  thr_new's tls_base parameter).  Zero TlsMemSz means the program has no
  thread-local storage. }
var
  GTlsInitAddr: Pointer;   { .tdata init image (= PT_TLS p_vaddr) }
  GTlsFileSz:   Int64;     { bytes to copy from the init image }
  GTlsMemSz:    Int64;     { total TLS size (.tdata + .tbss) }
  GTlsAlign:    Int64;     { PT_TLS alignment }

{ Build a fresh TLS block for a new thread and return its thread pointer (the
  value thr_new installs as the new thread's %fs base via tls_base).  Layout
  matches _start's SetupTLS: aligned TLS data followed by the TCB self-pointer.
  Returns nil when the program has no TLS. }
function BuildThreadTLS: Pointer;

{ Unmap a TLS block created by BuildThreadTLS, given the thread pointer it
  returned.  Used to reclaim the block when thread creation fails after the TLS
  was built (the offset from TP back to the mmap base is the same alignment math
  BuildThreadTLS used, kept here so both sides agree). }
procedure FreeThreadTLS(ATp: Pointer);

{ The total size of a per-thread TLS block (aligned memsz + the TCB slot), which
  thr_new wants as tls_size.  Returns 0 when the program has no TLS. }
function ThreadTLSSize: Int64;

implementation

type
  PPointer = ^Pointer;
  PInt64   = ^Int64;

const
  AMD64_SET_FSBASE = 129;     { sysarch op — install the %fs base (verified vs
                                FreeBSD 14 x86/include/sysarch.h) }
  PROT_RW      = 3;          { PROT_READ or PROT_WRITE }
  MAP_PRIVANON = $1002;      { FreeBSD MAP_PRIVATE ($0002) or MAP_ANON ($1000) }
  PT_TLS       = 7;

{ Our own ELF image.  A non-PIE ET_EXEC is mapped at this fixed base (the
  linker's TLinkTarget.BaseAddr), so the ELF header — and through e_phoff the
  program-header table — is readable at compile-time-known addresses without
  the kernel auxv. }
  ELF_LOAD_BASE = $400000;
  EH_PHOFF      = $20;   { e_phoff     (u64) — file offset of the phdr table }
  EH_PHENTSIZE  = $36;   { e_phentsize (u16) }
  EH_PHNUM      = $38;   { e_phnum     (u16) }

{ ELF64 Phdr field offsets. }
  PH_TYPE   = 0;    { p_type   (u32) }
  PH_OFFSET = 8;    { p_offset (u64) - file offset; == vaddr-base in our images }
  PH_VADDR  = 16;   { p_vaddr  (u64) }
  PH_FILESZ = 32;   { p_filesz (u64) }
  PH_MEMSZ  = 40;   { p_memsz  (u64) }
  PH_ALIGN  = 48;   { p_align  (u64) }

{ Round X up to the next multiple of A (A a power of two, >= 1). }
function AlignUp(X, A: Int64): Int64;
begin
  if A < 1 then A := 1;
  Result := (X + A - 1) and (not (A - 1));
end;

{ Install the %fs base to Tp.  FreeBSD: sysarch(AMD64_SET_FSBASE, &Tp) — the
  syscall takes the ADDRESS of the base value, not the value. }
procedure SetFsBase(Tp: Pointer);
var
  Base: Pointer;
begin
  Base := Tp;
  sysarch(AMD64_SET_FSBASE, @Base);
end;

{ Locate the program headers, find PT_TLS, then build the static TLS block and
  set the thread pointer.  No-op when the program has no TLS.

  We read the program-header table DIRECTLY from this binary's own ELF header,
  which sits at the fixed non-PIE load base (ELF_LOAD_BASE = $400000, the
  linker's TLinkTarget.BaseAddr): e_phoff at header offset 0x20, e_phentsize at
  0x36, e_phnum at 0x38.  A non-PIE ET_EXEC always maps its own ELF header at
  the fixed base (the first PT_LOAD covers file offset 0), so reading e_phoff
  there is exact and needs no kernel auxv — simpler and more self-contained than
  walking the auxv for AT_PHDR (which FreeBSD does supply, but relying on it
  couples startup to the auxv layout for no benefit on a non-PIE image). }
procedure SetupTLS;
var
  PhdrAddr, PhEnt, PhNum: Int64;
  EhEPhOff: PInt64;
  EhEPhEnt, EhEPhNum: ^UInt16;
  I: Int64;
  Ph: PChar;
  TlsVaddr, TlsFileSz, TlsMemSz, TlsAlign: Int64;
  PType: ^Int32;
  Block, Tp: Pointer;
  BlockSize: Int64;
  J: Int64;
  Src, Dst: PChar;
  TpSlot: PPointer;
begin
  { Read e_phoff / e_phentsize / e_phnum from our own ELF header at the load
    base.  e_phoff is a file offset; the first PT_LOAD maps file offset 0 to the
    load base, so the phdr table is at base + e_phoff. }
  EhEPhOff := PInt64(Pointer(ELF_LOAD_BASE + EH_PHOFF));
  EhEPhEnt := Pointer(ELF_LOAD_BASE + EH_PHENTSIZE);
  EhEPhNum := Pointer(ELF_LOAD_BASE + EH_PHNUM);
  PhdrAddr := ELF_LOAD_BASE + EhEPhOff^;
  PhEnt    := EhEPhEnt^;
  PhNum    := EhEPhNum^;
  if (PhdrAddr = 0) or (PhEnt = 0) or (PhNum = 0) then Exit;

  { Find PT_TLS among the program headers. }
  TlsVaddr := 0; TlsFileSz := 0; TlsMemSz := 0; TlsAlign := 8;
  I := 0;
  while I < PhNum do
  begin
    Ph := PChar(Pointer(PhdrAddr + I * PhEnt));
    PType := Pointer(Ph + PH_TYPE);
    if PType^ = PT_TLS then
    begin
      TlsVaddr  := PInt64(Pointer(Ph + PH_VADDR))^;
      TlsFileSz := PInt64(Pointer(Ph + PH_FILESZ))^;
      TlsMemSz  := PInt64(Pointer(Ph + PH_MEMSZ))^;
      TlsAlign  := PInt64(Pointer(Ph + PH_ALIGN))^;
      Break;
    end;
    I := I + 1;
  end;
  if TlsMemSz = 0 then Exit;

  { Stash the template so BuildThreadTLS can reproduce this block per thread. }
  GTlsInitAddr := Pointer(TlsVaddr);
  GTlsFileSz   := TlsFileSz;
  GTlsMemSz    := TlsMemSz;
  GTlsAlign    := TlsAlign;

  { Allocate block = aligned(memsz) + 16 (TCB self-pointer + slack).  mmap
    zero-fills. }
  BlockSize := AlignUp(TlsMemSz, TlsAlign) + 16;
  Block := mmap(nil, BlockSize, PROT_RW, MAP_PRIVANON, -1, 0);
  if Int64(Block) < 0 then Exit;

  { Copy the .tdata init image to the start of the block; .tbss stays zero. }
  Src := PChar(Pointer(TlsVaddr));
  Dst := PChar(Block);
  J := 0;
  while J < TlsFileSz do
  begin
    Dst[J] := Src[J];
    J := J + 1;
  end;

  { Thread pointer sits just past the TLS data (variant II); store the TCB
    self-pointer at *tp and set %fs. }
  Tp := Pointer(PChar(Block) + AlignUp(TlsMemSz, TlsAlign));
  TpSlot := PPointer(Tp);
  TpSlot^ := Tp;
  SetFsBase(Tp);
end;

{ Build a per-thread TLS block from the template captured at startup and return
  its thread pointer.  Mirrors SetupTLS's block construction (variant II: TLS
  data, then the TCB self-pointer at the thread pointer).  On FreeBSD the caller
  installs the returned TP as the new thread's %fs base via thr_new's tls_base. }
function BuildThreadTLS: Pointer;
var
  Block, Tp: Pointer;
  BlockSize, J: Int64;
  Src, Dst: PChar;
  TpSlot: PPointer;
begin
  Result := nil;
  if GTlsMemSz = 0 then Exit;
  BlockSize := AlignUp(GTlsMemSz, GTlsAlign) + 16;
  Block := mmap(nil, BlockSize, PROT_RW, MAP_PRIVANON, -1, 0);
  if Int64(Block) < 0 then Exit;
  Src := PChar(GTlsInitAddr);
  Dst := PChar(Block);
  J := 0;
  while J < GTlsFileSz do
  begin
    Dst[J] := Src[J];
    J := J + 1;
  end;
  Tp := Pointer(PChar(Block) + AlignUp(GTlsMemSz, GTlsAlign));
  TpSlot := PPointer(Tp);
  TpSlot^ := Tp;
  Result := Tp;
end;

procedure FreeThreadTLS(ATp: Pointer);
var
  Block: Pointer;
  BlockSize: Int64;
begin
  if (ATp = nil) or (GTlsMemSz = 0) then Exit;
  Block := Pointer(PChar(ATp) - AlignUp(GTlsMemSz, GTlsAlign));
  BlockSize := AlignUp(GTlsMemSz, GTlsAlign) + 16;
  munmap(Block, BlockSize);
end;

function ThreadTLSSize: Int64;
begin
  if GTlsMemSz = 0 then
    Result := 0
  else
    Result := AlignUp(GTlsMemSz, GTlsAlign) + 16;
end;

{ Call the program's `main(argc, argv)` (emitted by the backend) and return its
  result.  The asm thunk tail-jumps to the bare `main` symbol; argc/argv are
  already in %edi/%rsi (SysV), exactly what main expects. }
function MainTrampoline(Argc: Int32; Argv: Pointer): Int32;
  assembler; nostackframe;
asm
    jmp main
end;



{ The C-level entry.  The kernel hands us the initial process stack: argc, then
  argv[], NULL, envp[], NULL, auxv.  On FreeBSD the entry %rsp must be 16-byte
  aligned, and the kernel achieves that by inserting a ZERO PAD WORD immediately
  below argc when the argument-vector layout would otherwise leave argc at an
  8-mod-16 address (this depends on the argc+envc pointer-count parity, so it
  varies between the shell-launched top-level and an execve'd child with a
  different environment).  So argc is at [SP] usually, but at [SP+8] when a pad
  word is present.  Detect the pad: a real argc is a small non-negative count
  and the slot after it (argv[0]) is a valid pointer; a pad word reads 0.  If
  [SP] is 0 and [SP+8] is a plausible argc, skip the pad word. }
procedure _BlaiseStartC(SP: Pointer);
var
  Argc: Int64;
  Argv, Envp: Pointer;
  Ret: Int;
begin
  Argc := PInt64(SP)^;
  { Skip a kernel alignment pad word below argc, if present. }
  if Argc = 0 then
  begin
    if PInt64(Pointer(PChar(SP) + 8))^ > 0 then
      SP := Pointer(PChar(SP) + 8);
    Argc := PInt64(SP)^;
  end;
  Argv := Pointer(PChar(SP) + 8);
  { envp = &argv[argc+1] }
  Envp := Pointer(PChar(Argv) + (Argc + 1) * 8);
  environ := Envp;

  { TLS is set up by reading our own ELF program headers directly from this
    binary's ELF header at the fixed non-PIE load base (see SetupTLS).  A
    non-PIE ET_EXEC always maps its own header there, so this is exact and
    needs no kernel auxv. }
  SetupTLS();

  Ret := MainTrampoline(Int32(Argc), Argv);
  _exit(Ret);
end;

{ The kernel entry.  Capture %rsp (points at argc), align, and call the Pascal
  core.  Never returns. }
procedure _start; assembler; nostackframe;
asm
    endbr64
    xor  %ebp, %ebp
    movq %rsp, %rdi           { SP -> first arg }
    andq $0xfffffffffffffff0, %rsp
    call _BlaiseStartC
    xorl %edi, %edi
    movq $1, %rax             { SYS_exit(0) guard }
    syscall
    hlt
end;

end.
