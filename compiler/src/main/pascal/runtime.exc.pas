{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — Exception frame management and type identity (pure Pascal)

  Replaces the former blaise_exc.c.  setjmp/longjmp are provided by a
  platform-specific assembly stub (blaise_setjmp_x86_64.s for x86_64)
  so the exception subsystem has zero C dependencies.

  Exception frame layout (BlaiseExcFrame): a jmp_buf followed by two
  pointers.  The two pointers MUST sit past the end of the jmp_buf, whose
  size is CPU-dependent — see OFS_EXCEPTION / OFS_PREV below:

    x86_64  jmp_buf = 64 bytes  (rbx/rbp/r12..r15, rsp@48, retaddr@56)
            offset  64: exception, offset  72: prev
    aarch64 jmp_buf = 168 bytes (x19..x28@0..72, x29@80, x30@88, sp@96,
                                 d8..d15@104..160)
            offset 168: exception, offset 176: prev

  Frame size contract: the compiler allocates 512 bytes for each try block.
  That must exceed the largest jmp_buf plus the two pointers — 184 bytes on
  aarch64 — which it comfortably does.

  Thread safety: g_exc_top and g_current_exception are declared as
  threadvar, giving each thread its own exception chain.
}

unit runtime.exc;

interface

procedure _PushExcFrame(Frame: Pointer);
procedure _PopExcFrame;

{ Per-fiber exception-state snapshot hooks (async design, P1).  The exception
  machine is rooted in the threadvars g_exc_top / g_current_exception — per
  OS thread, shared by every fiber on a worker.  A fiber switch must save the
  outgoing fiber's pair into its control block and reinstate the incoming
  fiber's, or a try across a suspension is unsound (frames chain across fiber
  stacks and a raise longjmps into a suspended/stale frame).  The fiber
  runtime (async.fibers.context) binds these by bare symbol name. }
function  _ExcGetTop: Pointer;
procedure _ExcSetTop(AFrame: Pointer);
function  _ExcGetCurrent: Pointer;
procedure _ExcSetCurrent(AExc: Pointer);
procedure _Raise(Obj: Pointer);
procedure _Reraise(Exc: Pointer);
function  _CurrentException: Pointer;
function  _CurrentExceptionMessage: Pointer;
function  _IsInstance(Obj: Pointer; Target: Pointer): Int32;
function  _ImplementsInterface(Obj: Pointer; IntfTI: Pointer): Int32;
function  _GetItab(Obj: Pointer; IntfTI: Pointer): Pointer;
procedure _Raise_InvalidCast;
procedure _CheckNil(Obj: Pointer);
{ Exception unwind cleanup (docs/exception-unwind-cleanup-design.adoc).
  Generated _main passes the bounds of the linked unwind section. }
procedure _UnwindInit(AStart, AStop: Pointer);
{ Test hook: how many Blaise frames the last raise's walk passed. }
function  _UnwindLastWalk: Int;

implementation

{ String and dynamic-array header layout.  Every RTL unit that reads or
  writes a header declares this same block (the RTL units cannot share a
  unit of constants: a new RTL unit is unknown to the previous compiler's
  BuildRTLUnitList), so a layout change edits each copy alike.  Offsets are
  from the data pointer. }
const
  { String: Capacity, pad, RefCount, Length; data 8-aligned }
  STR_HDR_SIZE = 24;
  STR_RC_OFS   = -12;  { Int32; -1 = immortal }
  STR_LEN_OFS  = -8;
  STR_CAP_OFS  = -24;
  { Dynamic array: pad, element hook, pad, RefCount, Length; elements stay
    16-aligned }
  DA_HDR_SIZE  = 32;
  DA_HOOK_OFS  = -24;
  DA_RC_OFS    = -12;  { Int32; -1 = immortal }
  DA_LEN_OFS   = -8;
type
  TStrLen = Int64;     { the width of a string header's Length and Capacity }
  PStrLen = ^TStrLen;
  TDaLen  = Int64;     { the width of a dynamic-array header's Length }
  PDaLen  = ^TDaLen;


const
  { These MUST clear the end of the target's jmp_buf (runtime.setjmp).  They
    were sized for the 64-byte x86-64 buffer and never revisited when the
    aarch64 body landed with a 168-byte one, so on arm64 offsets 64/72 fell
    inside it — precisely on the `stp x27, x28, [x0, #64]` that setjmp
    executes.  _PushExcFrame wrote the prev link and setjmp then overwrote it
    with x28 one instruction later, so the exception chain was corrupt after
    the first completed try block; the next raise longjmp'd through a stale
    frame and restored a foreign x29/x30/sp, which surfaced on device as a
    frame pointer that changed mid-function inside a routine that never
    writes x29 (macOS arm64, 2026-07-23). }
{$IFDEF CPUARM64}
  OFS_EXCEPTION = 168;
  OFS_PREV      = 176;
{$ELSE}
  OFS_EXCEPTION = 64;
  OFS_PREV      = 72;
{$ENDIF}

type
  PPointer = ^Pointer;

procedure _blaise_longjmp(Buf: Pointer; Val: Int32); external name '_blaise_longjmp';

function  _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
function  _libc_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64; external name 'write';
procedure _libc_abort; external name 'abort';

threadvar
  g_exc_top: Pointer;
  g_current_exception: Pointer;

function ExcStrEmpty: Pointer;
var
  Base: Pointer;
  RC: ^Int32;
  LN, CP: PStrLen;
  Data: PChar;
begin
  Base := _BlaiseGetMem(STR_HDR_SIZE + 1);
  if Base = nil then
  begin
    Exit(nil);
  end;
  Result := Base + STR_HDR_SIZE;
  RC := Result + STR_RC_OFS;
  RC^ := 0;
  LN := Result + STR_LEN_OFS;
  LN^ := 0;
  CP := Result + STR_CAP_OFS;
  CP^ := 0;
  Data := PChar(Result);
  Data[0] := #0;
end;

procedure _PushExcFrame(Frame: Pointer);
var
  ExcSlot: PPointer;
  PrevSlot: PPointer;
begin
  ExcSlot := Frame + OFS_EXCEPTION;
  ExcSlot^ := nil;
  PrevSlot := Frame + OFS_PREV;
  PrevSlot^ := g_exc_top;
  g_exc_top := Frame;
end;

procedure _PopExcFrame;
var
  PrevSlot: PPointer;
begin
  if g_exc_top <> nil then
  begin
    PrevSlot := g_exc_top + OFS_PREV;
    g_exc_top := PrevSlot^;
  end;
end;

function _ExcGetTop: Pointer;
begin
  Result := g_exc_top;
end;

procedure _ExcSetTop(AFrame: Pointer);
begin
  g_exc_top := AFrame;
end;

function _ExcGetCurrent: Pointer;
begin
  Result := g_current_exception;
end;

procedure _ExcSetCurrent(AExc: Pointer);
begin
  g_current_exception := AExc;
end;

{ ---- exception unwind cleanup ------------------------------------------
  docs/exception-unwind-cleanup-design.adoc.  Every object the compiler
  writes carries one unwind block; the linker gathers them into one section
  and generated _main hands its bounds to _UnwindInit.  _Raise walks the
  frame-pointer chain from the raise up to the frame of the try that will
  catch, and for each frame it passes releases what the frame's routine
  record lists.  The walker keeps its state in its own frame, allocates
  nothing and holds no managed value, so it is re-entrant and needs no
  per-fibre state.  Block layout: uUnwindFacts.pas. }

const
  UNW_MAGIC = 827807042;      { 'BUW1' }
  UNW_HDR_SIZE = 32;
  UNW_ROUTINE_SIZE = 32;
  UNW_SLOT_SIZE = 8;
  UNW_RANGE_SIZE = 16;
  UNW_STR = 1;
  UNW_CLASS = 2;
  UNW_INTF = 3;
  UNW_DYN = 4;
  UNW_REFENV = 5;
  UNW_WEAK = 6;
  UNW_AGG = 7;
  UNW_STR0 = 8;
  UNW_F_INDIRECT = 1;
  UNW_F_SPANS_TRY = 2;
  UNW_F_ABS = 4;              { location = pointer-table index of an address }
{$IFDEF CPUARM64}
  JB_FP_OFS = 80;             { x29 in the jmp_buf }
{$ELSE}
  JB_FP_OFS = 8;              { %rbp in the jmp_buf }
{$ENDIF}

type
  PUInt32 = ^UInt32;
  PInt32 = ^Int32;
  { an aggregate's release hook: releases and zeroes every managed field or
    element of the record or static array at Addr }
  TUnwAggHook = procedure(Addr: Pointer);

function _blaise_getfp: Pointer; external name '_blaise_getfp';
procedure _StringRelease(Ptr: Pointer); external name '_StringRelease';
procedure _StringAddRef(Ptr: Pointer); external name '_StringAddRef';
procedure _ClassRelease(Ptr: Pointer); external name '_ClassRelease';
procedure _DynArrayRelease(Ptr: Pointer); external name '_DynArrayRelease';
procedure _WeakClear(Slot: Pointer); external name '_WeakClear';

var
  g_unw_start: Pointer;
  g_unw_stop: Pointer;

threadvar
  g_unw_frames: Int;          { Blaise frames the last walk passed }

procedure _UnwindInit(AStart, AStop: Pointer);
begin
  g_unw_start := AStart;
  g_unw_stop := AStop;
end;

function _UnwindLastWalk: Int;
begin
  Result := g_unw_frames;
end;

{ The block whose text holds APC, or nil (a foreign frame). }
function UnwFindBlock(APC: UInt): Pointer;
var
  P, Stop: UInt;
  Bytes, TextLen: UInt;
  Anchor: UInt;
begin
  Result := nil;
  P := UInt(g_unw_start);
  Stop := UInt(g_unw_stop);
  while P + UNW_HDR_SIZE <= Stop do
  begin
    if PUInt32(Pointer(P))^ <> UNW_MAGIC then
    begin
      { alignment padding between objects' blocks }
      P := P + 8;
      Continue;
    end;
    Bytes := PUInt32(Pointer(P + 4))^;
    Anchor := UInt(PPointer(Pointer(P + 8))^);
    TextLen := PUInt32(Pointer(P + 16))^;
    if (APC >= Anchor) and (APC < Anchor + TextLen) then
      Exit(Pointer(P));
    if (Bytes < UNW_HDR_SIZE) or ((Bytes and 7) <> 0) then
      Exit;                    { not a block we understand: stop }
    P := P + Bytes;
  end;
end;

{ The innermost routine record of ABlk that contains APC, or nil. }
function UnwFindRoutine(ABlk: Pointer; APC: UInt): Pointer;
var
  Off, Start, Len, BestLen: UInt;
  N, NPtrs, I: Int;
  R: UInt;
begin
  Result := nil;
  Off := APC - UInt(PPointer(ABlk + 8)^);
  N := PUInt32(ABlk + 20)^;
  NPtrs := PUInt32(ABlk + 24)^;
  R := UInt(ABlk) + UNW_HDR_SIZE + UInt(NPtrs) * 8;
  BestLen := 0;
  for I := 0 to N - 1 do
  begin
    Start := PUInt32(Pointer(R))^;
    Len := PUInt32(Pointer(R + 4))^;
    if (Off >= Start) and (Off < Start + Len) and
       ((Result = nil) or (Len < BestLen)) then
    begin
      Result := Pointer(R);
      BestLen := Len;
    end;
    R := R + UNW_ROUTINE_SIZE;
  end;
end;

{ Release one managed value of the given kind whose storage is at A, nil
  first: a destructor this runs that raises in turn finds it already empty. }
procedure UnwReleaseAt(ABlk: Pointer; A: PPointer; W: UInt32);
var
  V: Pointer;
  Hook: TUnwAggHook;
begin
  case W and $FF of
    UNW_STR:
    begin
      V := A^; A^ := nil; _StringRelease(V);
    end;
    UNW_STR0:
    begin
      { a bare release would drive an rc = 0 buffer to -1 (immortal) }
      V := A^; A^ := nil;
      if V <> nil then
      begin
        _StringAddRef(V);
        _StringRelease(V);
      end;
    end;
    UNW_CLASS:
    begin
      V := A^; A^ := nil; _ClassRelease(V);
    end;
    UNW_DYN:
    begin
      V := A^; A^ := nil; _DynArrayRelease(V);
    end;
    UNW_INTF:
    begin
      { the obj half; the itab half is static }
      V := A^; A^ := nil;
      PPointer(Pointer(A) + 8)^ := nil;
      _ClassRelease(V);
    end;
    UNW_REFENV:
    begin
      { the Env half of a 'reference to' closure }
      V := PPointer(Pointer(A) + 8)^;
      PPointer(Pointer(A) + 8)^ := nil;
      _ClassRelease(V);
    end;
    UNW_WEAK:
      _WeakClear(A);
    UNW_AGG:
    begin
      { a by-value aggregate parameter's slot holds the address of the
        frame's copy }
      if ((W shr 8) and UNW_F_INDIRECT) <> 0 then
        A := PPointer(A^);
      Hook := TUnwAggHook(PPointer(ABlk + UNW_HDR_SIZE + (W shr 16) * 8)^);
      if A <> nil then
        Hook(Pointer(A));
    end;
  end;
end;

{ Release what AFrame owns at APC: the owned temporaries live there, in
  every frame; and, unless the frame is the target -- the frame of the try
  that catches, which carries on running -- its own slots. }
procedure UnwCleanFrame(ABlk, ARtn: Pointer; AFrame: Pointer; APC: UInt;
  AIsTarget: Boolean);
var
  Off, Lo, Hi: UInt;
  NRtn, NPtrs, NSlotsAll, First, N, I: Int;
  S: UInt;
  W: UInt32;
begin
  Off := APC - UInt(PPointer(ABlk + 8)^) - PUInt32(ARtn)^;
  NRtn := PUInt32(ABlk + 20)^;
  NPtrs := PUInt32(ABlk + 24)^;
  NSlotsAll := PUInt32(ABlk + 28)^;
  { temporaries: a range whose statement spans a try is left to that
    statement when its handler is in this very frame }
  First := PUInt32(ARtn + 20)^;
  N := PUInt32(ARtn + 28)^;
  S := UInt(ABlk) + UNW_HDR_SIZE + UInt(NPtrs) * 8 +
    UInt(NRtn) * UNW_ROUTINE_SIZE + UInt(NSlotsAll) * UNW_SLOT_SIZE +
    UInt(First) * UNW_RANGE_SIZE;
  for I := 0 to N - 1 do
  begin
    Lo := PUInt32(Pointer(S))^;
    Hi := PUInt32(Pointer(S + 4))^;
    W := PUInt32(Pointer(S + 12))^;
    if (Off >= Lo) and (Off < Hi) and
       not (AIsTarget and (((W shr 8) and UNW_F_SPANS_TRY) <> 0)) then
    begin
      if ((W shr 8) and UNW_F_ABS) <> 0 then
        { a static slot: its address is in the block's pointer table }
        UnwReleaseAt(ABlk, PPointer(PPointer(ABlk + UNW_HDR_SIZE +
          UInt(PInt32(Pointer(S + 8))^) * 8)^), W)
      else
        UnwReleaseAt(ABlk, PPointer(AFrame + PInt32(Pointer(S + 8))^), W);
    end;
    S := S + UNW_RANGE_SIZE;
  end;
  if AIsTarget then Exit;
  { the frame's own slots, if its code at APC is past the prologue's
    zeroing and before the epilogue's own release }
  if (Off < PUInt32(ARtn + 8)^) or (Off >= PUInt32(ARtn + 12)^) then Exit;
  First := PUInt32(ARtn + 16)^;
  N := PUInt32(ARtn + 24)^;
  S := UInt(ABlk) + UNW_HDR_SIZE + UInt(NPtrs) * 8 +
    UInt(NRtn) * UNW_ROUTINE_SIZE + UInt(First) * UNW_SLOT_SIZE;
  for I := 0 to N - 1 do
  begin
    UnwReleaseAt(ABlk, PPointer(AFrame + PInt32(Pointer(S))^),
      PUInt32(Pointer(S + 4))^);
    S := S + UNW_SLOT_SIZE;
  end;
end;

procedure _UnwindCleanup(ATarget: Pointer);
var
  TargetFP, Callee, FP: UInt;
  RA, PC: UInt;
  Blk, Rtn: Pointer;
begin
  g_unw_frames := 0;
  if g_unw_start = nil then Exit;
  TargetFP := UInt(PPointer(ATarget + JB_FP_OFS)^);
  { this frame, then _Raise's: the walk starts in _Raise's caller }
  Callee := UInt(_blaise_getfp());
  Callee := UInt(PPointer(Pointer(Callee))^);
  while True do
  begin
    FP := UInt(PPointer(Pointer(Callee))^);
    RA := UInt(PPointer(Pointer(Callee + 8))^);
    { a broken or foreign chain ends the walk: the frames above leak, as
      they did before the tables }
    if (FP = 0) or (FP <= Callee) or (FP > TargetFP) or ((FP and 7) <> 0) then
      Exit;
    PC := RA - 1;
    Blk := UnwFindBlock(PC);
    if Blk = nil then Exit;
    g_unw_frames := g_unw_frames + 1;
    Rtn := UnwFindRoutine(Blk, PC);
    if Rtn <> nil then
      UnwCleanFrame(Blk, Rtn, Pointer(FP), PC, FP = TargetFP);
    if FP = TargetFP then Exit;
    Callee := FP;
  end;
end;

procedure _Raise(Obj: Pointer);
var
  ExcSlot: PPointer;
begin
  if g_exc_top = nil then
    _libc_abort();
  { release what the frames between here and the handler own; a
    destructor that runs may raise and catch on its own, so the exception
    state is set afterwards }
  _UnwindCleanup(g_exc_top);
  g_current_exception := Obj;
  ExcSlot := g_exc_top + OFS_EXCEPTION;
  ExcSlot^ := Obj;
  _blaise_longjmp(g_exc_top, 1);
end;

procedure _Reraise(Exc: Pointer);
begin
  _Raise(Exc);
end;

function _CurrentException: Pointer;
begin
  Result := g_current_exception;
end;

function _CurrentExceptionMessage: Pointer;
var
  Exc: Pointer;
  MsgSlot: PPointer;
  Msg: Pointer;
begin
  Exc := g_current_exception;
  if Exc = nil then
  begin
    Exit(ExcStrEmpty());
  end;
  MsgSlot := Exc + 8;
  Msg := MsgSlot^;
  if Msg = nil then
    Result := ExcStrEmpty()
  else
    Result := Msg;
end;

{ ------------------------------------------------------------------
  Type identity — is / as operators
  ------------------------------------------------------------------

  BlaiseTypeInfo layout (matches the codegen-emitted typeinfo_ data):
    offset 0: parent    (Pointer — parent class TypeInfo, or nil for root)
    offset 8: impllist  (Pointer — nil-terminated array of (typeinfo*, itab*) pairs)
  ------------------------------------------------------------------ }

function _IsInstance(Obj: Pointer; Target: Pointer): Int32;
var
  VTable: PPointer;
  TI: Pointer;
  ParentSlot: PPointer;
begin
  Result := 0;
  if (Obj = nil) or (Target = nil) then Exit;
  VTable := PPointer(Obj)^;
  TI := VTable^;
  while TI <> nil do
  begin
    if TI = Target then
    begin
      Exit(1);
    end;
    ParentSlot := TI;
    TI := ParentSlot^;
  end;
end;

function _ImplementsInterface(Obj: Pointer; IntfTI: Pointer): Int32;
var
  VTable: PPointer;
  TI: Pointer;
  ParentSlot: PPointer;
  ImplSlot: PPointer;
  Impl: PPointer;
begin
  Result := 0;
  if (Obj = nil) or (IntfTI = nil) then Exit;
  VTable := PPointer(Obj)^;
  TI := VTable^;
  while TI <> nil do
  begin
    ImplSlot := TI + 8;
    Impl := ImplSlot^;
    while (Impl <> nil) and (Impl^ <> nil) do
    begin
      if Impl^ = IntfTI then
      begin
        Exit(1);
      end;
      Impl := Pointer(Impl) + 16;
    end;
    ParentSlot := TI;
    TI := ParentSlot^;
  end;
end;

function _GetItab(Obj: Pointer; IntfTI: Pointer): Pointer;
var
  VTable: PPointer;
  TI: Pointer;
  ParentSlot: PPointer;
  ImplSlot: PPointer;
  Impl: PPointer;
  ItabSlot: PPointer;
begin
  Result := nil;
  if (Obj = nil) or (IntfTI = nil) then Exit;
  VTable := PPointer(Obj)^;
  TI := VTable^;
  while TI <> nil do
  begin
    ImplSlot := TI + 8;
    Impl := ImplSlot^;
    while (Impl <> nil) and (Impl^ <> nil) do
    begin
      if Impl^ = IntfTI then
      begin
        ItabSlot := Pointer(Impl) + 8;
        Exit(ItabSlot^);
      end;
      Impl := Pointer(Impl) + 16;
    end;
    ParentSlot := TI;
    TI := ParentSlot^;
  end;
end;

procedure DiagAbort(Msg: Pointer; Len: Int);
var
  NL: Byte;
begin
  _libc_write(2, Msg, Int64(Len));
  NL := 10;
  _libc_write(2, @NL, 1);
  _libc_abort();
end;

procedure _Raise_InvalidCast;
begin
  DiagAbort('Runtime error: invalid typecast', 31);
end;

procedure _CheckNil(Obj: Pointer);
begin
  if Obj = nil then
    DiagAbort('Runtime error: method call on nil object', 41);
end;

end.
