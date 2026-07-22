{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.callalign;

{ E2E tests for call-site stack alignment (SysV: %rsp must be 16-byte
  aligned at every call instruction).

  The native backend stages call arguments with pushq; when an argument is
  itself a call, the already-pushed outer arguments stay pinned while the
  inner call's whole subtree executes.  An odd pinned slot count leaves
  %rsp = 8 (mod 16) at every call in that subtree.  Blaise-generated code
  tolerates that, so the bug is latent until a glibc callee uses movaps on
  its aligned locals — pthread_create (via __pthread_getattr_default_np ->
  pthread_attr_copy) SIGSEGVs.  These tests spawn a thread inside an
  odd-pinned nested-call argument so a misaligned subtree crashes the
  native arm; the QBE arm was never affected and must keep passing.

  See also cp.test.nativealign.pas for the asm-level mechanism tests. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ECallAlignTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { The shape that found the bug: F(a, G(...)) with ONE pinned slot and a
      pthread_create inside G's subtree. }
    procedure TestRun_OddPinnedArg_ThreadSpawnInSubtree;
    { Two nesting levels with mixed even/odd pinned counts. }
    procedure TestRun_TwoLevelNested_OddPinnedThreadSpawn;
    { Odd pinned count around a float-arg call (slot-staged, not pushed). }
    procedure TestRun_OddPinned_FloatArgCall_ThreadSpawn;
    { Odd pinned count around a >6-arg call (SysV stack arguments) whose
      last argument spawns a thread. }
    procedure TestRun_OverflowArgs_OddPinned_ThreadSpawn;
    { >8 float args: the 9th+ overflow to the stack.  The x86-64 caller used to
      drop the overflow float (BUG-20260721-x86-single-overflow-arg). }
    procedure TestRun_OverflowFloat_9Single;
    procedure TestRun_OverflowFloat_9Double;
    procedure TestRun_OverflowFloat_8Double1Single;
    procedure TestRun_OverflowFloat_11Single;
    procedure TestRun_OverflowFloat_InterspersedWithInt;
    { >8 float args at METHOD and INTERFACE-dispatch call sites: the plain-
      function path overflows floats to the stack, but the method/itab arg
      loaders either raised at compile time or silently dropped the 9th+
      float (BUG-20260721-x86-method-call-overflow-float). }
    procedure TestRun_OverflowFloat_9Double_Method;
    procedure TestRun_OverflowFloat_9Double_IntfDispatch;
    procedure TestRun_OverflowFloat_InterspersedInt_Method;
    procedure TestRun_OverflowFloat_InterspersedInt_IntfDispatch;
  end;

implementation

procedure TE2ECallAlignTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-callalign');
end;

const
  LE = #10;

  { Shared preamble: a worker thread and a function that spawns + joins it,
    returning 7. }
  ThreadPreamble =
    '''
    uses Classes;
    type
      TW = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TW.Execute;
    begin
    end;
    function SpawnJoin: Integer;
    var T: TW;
    begin
      T := TW.Create(True);
      T.Start();
      T.WaitFor();
      Result := 7
    end;
    ''';

  SrcOddPinned =
    'program P;' + LE + ThreadPreamble +
    '''
    function Add2(A, B: Integer): Integer; begin Result := A + B end;
    var X: Integer;
    begin
      X := Add2(1, SpawnJoin());
      WriteLn(X)
    end.
    ''';

  SrcTwoLevel =
    'program P;' + LE + ThreadPreamble +
    '''
    function Add2(A, B: Integer): Integer; begin Result := A + B end;
    function Add3(A, B, C: Integer): Integer; begin Result := A + B + C end;
    var X: Integer;
    begin
      X := Add3(1, 2, Add2(3, SpawnJoin()));
      WriteLn(X)
    end.
    ''';

  SrcFloatArg =
    'program P;' + LE + ThreadPreamble +
    '''
    function FAdd(D: Double; I: Integer): Integer;
    begin
      Result := Trunc(D) + I
    end;
    function Add2(A, B: Integer): Integer; begin Result := A + B end;
    var X: Integer;
    begin
      X := Add2(1, FAdd(2.0, SpawnJoin()));
      WriteLn(X)
    end.
    ''';

  SrcOverflowArgs =
    'program P;' + LE + ThreadPreamble +
    '''
    function Sum8(A, B, C, D, E, F, G, H: Integer): Integer;
    begin
      Result := A + B + C + D + E + F + G + H
    end;
    function Add2(A, B: Integer): Integer; begin Result := A + B end;
    var X: Integer;
    begin
      X := Add2(1, Sum8(1, 2, 3, 4, 5, 6, 7, SpawnJoin()));
      WriteLn(X)
    end.
    ''';

  { >8 floating-point args: the 9th onward overflow the 8 xmm registers and
    must be passed on the outgoing stack.  The x86-64 caller used to silently
    DROP the overflow float (never relocating its slot, then reclaiming it),
    so the callee read an uninitialised stack slot — garbage for BOTH Single
    and Double (BUG-20260721-x86-single-overflow-arg; not Single-specific).
    No threads here — a plain compile+run on both backends. }
  Src9Single =
    '''
    program P;
    function F(a, b, c, d, e, f, g, h, i: Single): Single;
    begin Result := i + a end;
    var r: Single;
    begin r := F(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5,9.5); WriteLn(Trunc(r*10)) end.
    ''';

  { Double control — the 9th Double overflow was ALSO garbage before the fix
    (returned 0 on native), proving the defect was not Single-specific. }
  Src9Double =
    '''
    program P;
    function F(a, b, c, d, e, f, g, h, i: Double): Double;
    begin Result := i + a end;
    var r: Double;
    begin r := F(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5,9.5); WriteLn(Trunc(r*10)) end.
    ''';

  { 9 Doubles through a class METHOD (Self occupies an integer register;
    the 9th Double must overflow to the stack, not raise or be dropped). }
  Src9DoubleMethod =
    '''
    program P;
    type
      TCalc = class
      public
        function F(a, b, c, d, e, f, g, h, i: Double): Double;
      end;
    function TCalc.F(a, b, c, d, e, f, g, h, i: Double): Double;
    begin Result := i + a end;
    var
      C: TCalc;
      r: Double;
    begin
      C := TCalc.Create();
      r := C.F(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5,9.5);
      WriteLn(Trunc(r*10))
    end.
    ''';

  { 9 Doubles through INTERFACE (itab) dispatch. }
  Src9DoubleIntf =
    '''
    program P;
    type
      ICalc = interface
        function F(a, b, c, d, e, f, g, h, i: Double): Double;
      end;
      TCalc = class(TObject, ICalc)
      public
        function F(a, b, c, d, e, f, g, h, i: Double): Double;
      end;
    function TCalc.F(a, b, c, d, e, f, g, h, i: Double): Double;
    begin Result := i + a end;
    var
      C: ICalc;
      r: Double;
    begin
      C := TCalc.Create();
      r := C.F(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5,9.5);
      WriteLn(Trunc(r*10))
    end.
    ''';

  { Interspersed integer AND float overflow at a METHOD call: Self takes the
    first integer register, n1..n5 fill the rest, so n6 is the int-overflow
    slot while s9/s10 are the float-overflow slots.  The relocated region must
    interleave them in ascending arg order (s9, n6, s10) to match the callee
    prologue's shared StackOff walk. }
  SrcInterspersedMethod =
    '''
    program P;
    type
      TCalc = class
      public
        function F(s1, s2, s3, s4, s5, s6, s7, s8: Single;
                   n1, n2, n3, n4, n5: Integer;
                   s9: Single; n6: Integer; s10: Single): Integer;
      end;
    function TCalc.F(s1, s2, s3, s4, s5, s6, s7, s8: Single;
                     n1, n2, n3, n4, n5: Integer;
                     s9: Single; n6: Integer; s10: Single): Integer;
    begin Result := Trunc((s9 + s10) * 10) + n6 end;
    var
      C: TCalc;
      r: Integer;
    begin
      C := TCalc.Create();
      r := C.F(1,2,3,4,5,6,7,8, 10,20,30,40,50, 9.5, 100, 10.5);
      WriteLn(r)
    end.
    ''';

  { Same interspersed int+float overflow shape through INTERFACE (itab)
    dispatch — exercises the EmitIntfRegArgs general branch with BOTH kinds
    of overflow slot in one OvSlots region.  Double params + float literals
    deliberately: itab call sites do not yet coerce an integer literal to a
    float param, nor narrow Double->Single, on EITHER backend
    (BUG-20260722-itab-arg-type-coercion) — that separate defect would mask
    the overflow-layout behaviour this test pins. }
  SrcInterspersedIntf =
    '''
    program P;
    type
      ICalc = interface
        function F(d1, d2, d3, d4, d5, d6, d7, d8: Double;
                   n1, n2, n3, n4, n5: Integer;
                   d9: Double; n6: Integer; d10: Double): Integer;
      end;
      TCalc = class(TObject, ICalc)
      public
        function F(d1, d2, d3, d4, d5, d6, d7, d8: Double;
                   n1, n2, n3, n4, n5: Integer;
                   d9: Double; n6: Integer; d10: Double): Integer;
      end;
    function TCalc.F(d1, d2, d3, d4, d5, d6, d7, d8: Double;
                     n1, n2, n3, n4, n5: Integer;
                     d9: Double; n6: Integer; d10: Double): Integer;
    begin Result := Trunc((d9 + d10) * 10) + n6 end;
    var
      C: ICalc;
      r: Integer;
    begin
      C := TCalc.Create();
      r := C.F(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5, 10,20,30,40,50, 9.5, 100, 10.5);
      WriteLn(r)
    end.
    ''';

  { First 8 Double (fill xmm0..7) + a 9th Single overflow — mixed-class case. }
  Src8Double1Single =
    '''
    program P;
    function F(a, b, c, d, e, f, g, h: Double; i: Single): Single;
    begin Result := i + a end;
    var r: Single;
    begin r := F(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5,9.5); WriteLn(Trunc(r*10)) end.
    ''';

  { Multiple overflow floats (9th, 10th, 11th all read). }
  Src11Single =
    '''
    program P;
    function F(a, b, c, d, e, f, g, h, i, j, k: Single): Single;
    begin Result := (i + j + k) + a end;
    var r: Single;
    begin r := F(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5,9.5,10.5,11.5); WriteLn(Trunc(r*10)) end.
    ''';

  { Interspersed integer AND float overflow — the tightest layout check: the
    caller must relocate int and float overflow slots in one argument order
    matching the callee's shared StackOff walk. }
  SrcInterspersedOverflow =
    '''
    program P;
    function F(s1, s2, s3, s4, s5, s6, s7, s8: Single;
               n1, n2, n3, n4, n5, n6: Integer;
               s9: Single; n7: Integer; s10: Single): Integer;
    begin Result := Trunc((s9 + s10) * 10) + n7 end;
    var r: Integer;
    begin
      r := F(1,2,3,4,5,6,7,8, 10,20,30,40,50,60, 9.5, 100, 10.5);
      WriteLn(r)
    end.
    ''';

procedure TE2ECallAlignTests.TestRun_OverflowFloat_9Single;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src9Single, '110' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_9Double;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src9Double, '110' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_8Double1Single;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src8Double1Single, '110' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_11Single;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src11Single, '330' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_InterspersedWithInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(SrcInterspersedOverflow, '300' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_9Double_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src9DoubleMethod, '110' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_9Double_IntfDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src9DoubleIntf, '110' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_InterspersedInt_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(SrcInterspersedMethod, '300' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowFloat_InterspersedInt_IntfDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(SrcInterspersedIntf, '300' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OddPinnedArg_ThreadSpawnInSubtree;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRTLRunsOnAll(SrcOddPinned, '8' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_TwoLevelNested_OddPinnedThreadSpawn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRTLRunsOnAll(SrcTwoLevel, '13' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OddPinned_FloatArgCall_ThreadSpawn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRTLRunsOnAll(SrcFloatArg, '10' + LE, 0)
end;

procedure TE2ECallAlignTests.TestRun_OverflowArgs_OddPinned_ThreadSpawn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRTLRunsOnAll(SrcOverflowArgs, '36' + LE, 0)
end;

initialization
  RegisterTest(TE2ECallAlignTests);

end.
