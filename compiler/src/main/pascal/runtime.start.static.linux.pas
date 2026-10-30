{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.start.static.linux;

// Freestanding _start for a static, libc-free Linux ET_EXEC (the --static
// kernel-leaf swap; docs/linux-syscall-migration.adoc).
//
// A tiny asm trampoline captures the initial stack pointer and tail-calls the
// Pascal _BlaiseStartC, which:
//   1. parses argc / argv / envp / the auxv (the kernel's initial stack);
//   2. sets up the static TLS block and the thread pointer (%fs) - required
//      before any threadvar (%fs-relative) access, which a static binary's
//      kernel does NOT do for us;
//   3. captures `environ`;
//   4. calls main(argc, argv);
//   5. exit_group with main's return (main itself calls exit, so this is a
//      guard).
//
// x86-64 TLS (variant II): the thread pointer points at the TCB, which sits
// ABOVE the TLS block; threadvars are at negative offsets from the TP.  %fs:0
// must hold the TP value itself (the TCB self-pointer).  Layout we build:
//     [ TLS block: memsz bytes ][ TCB: 8-byte self-pointer ]
//   tp = block + memsz_aligned ; %fs = tp ; *(void**)tp = tp.

interface

uses
  runtime.syscall.linux;   { syscalls + the `environ` global }

procedure _start;

{ The static TLS template, captured from PT_TLS at startup so each spawned thread
  can build its own TLS block (runtime.thread.static.linux uses these via clone +
  CLONE_SETTLS).  Zero TlsMemSz means the program has no thread-local storage. }
var
  GTlsInitAddr: Pointer;   { .tdata init image (= PT_TLS p_vaddr) }
  GTlsFileSz:   Int64;     { bytes to copy from the init image }
  GTlsMemSz:    Int64;     { total TLS size (.tdata + .tbss) }
  GTlsAlign:    Int64;     { PT_TLS alignment }

{ Build a fresh TLS block for a new thread and return its thread pointer (the
  value to load into %fs).  Layout matches _start's SetupTLS: aligned TLS data
  followed by the TCB self-pointer.  Returns nil when the program has no TLS. }
function BuildThreadTLS: Pointer;

{ Unmap a TLS block created by BuildThreadTLS, given the thread pointer it
  returned.  Used to reclaim the block when thread creation fails after the TLS
  was built (the offset from TP back to the mmap base is the same alignment math
  BuildThreadTLS used, kept here so both sides agree). }
procedure FreeThreadTLS(ATp: Pointer);

implementation

type
  PPointer = ^Pointer;
  PInt64   = ^Int64;

const
  ARCH_SET_FS  = $1002;
  PROT_RW      = 3;          { PROT_READ or PROT_WRITE }
  MAP_PRIVANON = $22;        { MAP_PRIVATE or MAP_ANONYMOUS }
  AT_NULL      = 0;
  AT_PHDR      = 3;
  AT_PHENT     = 4;
  AT_PHNUM     = 5;
  PT_TLS       = 7;

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

{ Walk the auxv for PT_TLS via AT_PHDR/AT_PHENT/AT_PHNUM, then build the static
  TLS block and set the thread pointer.  Auxv is an array of (Int64 tag, Int64
  val) pairs terminated by AT_NULL.  No-op when the program has no TLS. }
procedure SetupTLS(Auxv: Pointer);
var
  P: PInt64;
  PhdrAddr, PhEnt, PhNum: Int64;
  I, Tag, Val: Int64;
  Ph: PChar;
  TlsVaddr, TlsFileSz, TlsMemSz, TlsAlign: Int64;
  PType: ^Int32;
  Block, Tp: Pointer;
  BlockSize: Int64;
  J: Int64;
  Src, Dst: PChar;
  TpSlot: PPointer;
begin
  PhdrAddr := 0; PhEnt := 56; PhNum := 0;
  P := PInt64(Auxv);
  while True do
  begin
    Tag := P^;
    P := PInt64(Pointer(PChar(P) + 8));
    Val := P^;
    P := PInt64(Pointer(PChar(P) + 8));
    if Tag = AT_NULL then Break;
    if Tag = AT_PHDR  then PhdrAddr := Val;
    if Tag = AT_PHENT then PhEnt := Val;
    if Tag = AT_PHNUM then PhNum := Val;
  end;
  if PhdrAddr = 0 then Exit;

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

  { Allocate block = aligned(memsz) + 8 (TCB self-pointer).  mmap zero-fills. }
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
  arch_prctl(ARCH_SET_FS, Tp);
end;

{ Build a per-thread TLS block from the template captured at startup and return
  its thread pointer.  Mirrors SetupTLS's block construction (variant II: TLS
  data, then the TCB self-pointer at the thread pointer).  The caller installs
  the returned TP into %fs (clone's CLONE_SETTLS does that for a new thread). }
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

{ Call the program's `main(argc, argv)` (emitted by the backend) and return its
  result.  The asm thunk tail-jumps to the bare `main` symbol; argc/argv are
  already in %edi/%rsi (SysV), exactly what main expects. }
function MainTrampoline(Argc: Int32; Argv: Pointer): Int32;
  assembler; nostackframe;
asm
    jmp main
end;

{ The C-level entry: SP points at the kernel's initial stack (argc at [SP]). }
procedure _BlaiseStartC(SP: Pointer);
var
  Argc: Int64;
  Argv, Envp, Auxv: Pointer;
  I: Int64;
  Ret: Int;
begin
  Argc := PInt64(SP)^;
  Argv := Pointer(PChar(SP) + 8);
  { envp = &argv[argc+1] }
  Envp := Pointer(PChar(Argv) + (Argc + 1) * 8);
  environ := Envp;
  { auxv follows envp's NULL terminator. }
  Auxv := Envp;
  I := 0;
  while PPointer(Pointer(PChar(Auxv) + I * 8))^ <> nil do
    I := I + 1;
  Auxv := Pointer(PChar(Auxv) + (I + 1) * 8);

  SetupTLS(Auxv);

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
    movq $231, %rax           { exit_group(0) guard }
    syscall
    hlt
end;

end.
