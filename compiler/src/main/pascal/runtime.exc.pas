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
  runtime (async.fibers.context.<cpu>) binds these by bare symbol name. }
function  _ExcGetTop: Pointer;
procedure _ExcSetTop(AFrame: Pointer);
function  _ExcGetCurrent: Pointer;
procedure _ExcSetCurrent(AExc: Pointer);
procedure _Raise(Obj: Pointer);
procedure _Reraise(Exc: Pointer);
function  _CurrentException: Pointer;
function  _CurrentExceptionMessage: Pointer;
function  _IsInstance(Obj: Pointer; Target: Pointer): Integer;
function  _ImplementsInterface(Obj: Pointer; IntfTI: Pointer): Integer;
function  _GetItab(Obj: Pointer; IntfTI: Pointer): Pointer;
procedure _Raise_InvalidCast;
procedure _CheckNil(Obj: Pointer);

implementation

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

procedure _blaise_longjmp(Buf: Pointer; Val: Integer); external name '_blaise_longjmp';

function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
function  _libc_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64; external name 'write';
procedure _libc_abort; external name 'abort';

threadvar
  g_exc_top: Pointer;
  g_current_exception: Pointer;

function ExcStrEmpty: Pointer;
var
  Base: Pointer;
  RC, LN, CP: ^Integer;
  Data: PChar;
begin
  Base := _BlaiseGetMem(13);
  if Base = nil then
  begin
    Exit(nil);
  end;
  RC := Base;
  RC^ := 0;
  LN := Base + 4;
  LN^ := 0;
  CP := Base + 8;
  CP^ := 0;
  Data := PChar(Base + 12);
  Data[0] := #0;
  Result := Base + 12;
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

procedure _Raise(Obj: Pointer);
var
  ExcSlot: PPointer;
begin
  if g_exc_top = nil then
    _libc_abort();
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

function _IsInstance(Obj: Pointer; Target: Pointer): Integer;
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

function _ImplementsInterface(Obj: Pointer; IntfTI: Pointer): Integer;
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

procedure DiagAbort(Msg: Pointer; Len: Integer);
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
