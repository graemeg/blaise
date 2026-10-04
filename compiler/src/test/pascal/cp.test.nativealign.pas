{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nativealign;

{ Assembly-level tests for call-site stack alignment in the NATIVE x86-64
  backend.

  The System V AMD64 ABI requires %rsp to be 16-byte aligned at every call
  instruction.  The native backend stages call arguments with pushq, so when
  an argument is itself a call — F(a, G(...)) — the already-pushed outer
  arguments stay pinned on the stack while G's whole subtree executes.  An
  odd number of pinned 8-byte slots leaves %rsp = 8 (mod 16) at every call
  inside that subtree; a glibc callee that uses movaps on aligned locals
  (e.g. pthread_create) then faults.

  The backend fixes this centrally: TX86_64Backend.Emit tracks the emitted
  stack depth and wraps any callq at a misaligned depth in a
  subq $8/addq $8 pad pair.  Calls that pass genuine SysV stack arguments
  (>6 integer slots) cannot be wrapped — the pad would shift the stack
  arguments — so the overflow paths copy the overflow slots into a fresh
  parity-sized region instead, making the call site aligned by construction
  (the wrap pad then never fires for them).  These tests pin both halves of
  that mechanism without needing libc. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, uDebugFacts;

type
  TNativeCallAlignTests = class(TTestCase)
  private
    function GenAsm(const ASrc: string): string;
    function FuncRegion(const AAsm, AName: string): string;
  published
    { F(1, Inner()) pins one slot: the inner call must be wrapped in a
      subq $8 / addq $8 alignment pad. }
    procedure TestOddPinnedInnerCall_PadWrapsInnerCall;
    { F(Inner(), 1) evaluates the inner call at zero pinned depth: no pad. }
    procedure TestZeroPinnedInnerCall_NoPad;
    { Add3(1, 2, Add2(3, Inner())): Inner sits under three pinned slots
      (odd — pad); the Add2 call itself sits under two (even — no pad). }
    procedure TestTwoLevelNesting_PadOnlyAtOddDepth;
    { An 8-integer-arg call under one pinned slot passes two SysV stack
      arguments.  It must NOT be wrapped in the pad (that would shift the
      stack args); instead the overflow slots are copied into a fresh
      parity-sized region so the call site is aligned by construction. }
    procedure TestOverflowArgsCall_FreshRegionNotWrapPad;
  end;

implementation

const
  LF = #10;

function TNativeCallAlignTests.GenAsm(const ASrc: string): string;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TCodeGenNative;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Prog);
    finally
      A.Free();
    end;
    CG := TCodeGenNative.Create();
    try
      CG.SetTarget(LinuxX64Target());
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

function TNativeCallAlignTests.FuncRegion(const AAsm, AName: string): string;
var
  StartP, EndP: Integer;
begin
  StartP := Pos(AName + ':', AAsm);
  AssertTrue('function ' + AName + ' present in asm', StartP >= 0);
  EndP := StrPos('.type ' + AName, StrCopyTail(AAsm, StartP));
  AssertTrue('function ' + AName + ' closed', EndP >= 0);
  Result := StrCopyFrom(AAsm, StartP, EndP);
end;

procedure TNativeCallAlignTests.TestOddPinnedInnerCall_PadWrapsInnerCall;
const
  Src = '''
      program P;
      function Inner: Integer; begin Result := 7 end;
      function Add2(A, B: Integer): Integer; begin Result := A + B end;
      var X: Integer;
      begin
        X := Add2(1, Inner())
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src), 'main');
  AssertTrue('inner call at odd pinned depth is pad-wrapped',
    Pos(#9'subq $8, %rsp' + LF + #9'callq Inner' + LF +
        #9'addq $8, %rsp', Region) >= 0);
  { The outer call happens after both slots are popped — no pad. }
  AssertTrue('outer call not pad-wrapped',
    Pos(#9'subq $8, %rsp' + LF + #9'callq Add2', Region) < 0);
end;

procedure TNativeCallAlignTests.TestZeroPinnedInnerCall_NoPad;
const
  Src = '''
      program P;
      function Inner: Integer; begin Result := 7 end;
      function Add2(A, B: Integer): Integer; begin Result := A + B end;
      var X: Integer;
      begin
        X := Add2(Inner(), 1)
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src), 'main');
  AssertTrue('inner call present', Pos('callq Inner', Region) >= 0);
  AssertTrue('inner call at aligned depth is not pad-wrapped',
    Pos(#9'subq $8, %rsp' + LF + #9'callq Inner', Region) < 0);
end;

procedure TNativeCallAlignTests.TestTwoLevelNesting_PadOnlyAtOddDepth;
const
  Src = '''
      program P;
      function Inner: Integer; begin Result := 7 end;
      function Add2(A, B: Integer): Integer; begin Result := A + B end;
      function Add3(A, B, C: Integer): Integer; begin Result := A + B + C end;
      var X: Integer;
      begin
        X := Add3(1, 2, Add2(3, Inner()))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src), 'main');
  { Inner runs under 3 pinned slots (1, 2, 3) — odd, so pad-wrapped. }
  AssertTrue('deepest call at odd pinned depth is pad-wrapped',
    Pos(#9'subq $8, %rsp' + LF + #9'callq Inner' + LF +
        #9'addq $8, %rsp', Region) >= 0);
  { Add2 is called after its own two slots are popped, under 2 pinned
    slots (1, 2) — even, so no pad. }
  AssertTrue('mid-level call at even pinned depth is not pad-wrapped',
    Pos(#9'subq $8, %rsp' + LF + #9'callq Add2', Region) < 0);
end;

procedure TNativeCallAlignTests.TestOverflowArgsCall_FreshRegionNotWrapPad;
const
  Src = '''
      program P;
      function Sum8(A, B, C, D, E, F, G, H: Integer): Integer;
      begin
        Result := A + B + C + D + E + F + G + H
      end;
      function Add2(A, B: Integer): Integer; begin Result := A + B end;
      var X: Integer;
      begin
        X := Add2(1, Sum8(1, 2, 3, 4, 5, 6, 7, 8))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src), 'main');
  AssertTrue('overflow call present', Pos('callq Sum8', Region) >= 0);
  { A call with SysV stack arguments must never get the wrap pad — it would
    shift the stack arguments out from under the callee. }
  AssertTrue('overflow call not pad-wrapped',
    Pos(#9'subq $8, %rsp' + LF + #9'callq Sum8', Region) < 0);
  { Instead the two overflow slots (source offsets 48/56 in the 64-byte slot
    block) are copied into a fresh region sized for parity: one pinned slot
    (8) + slot block (64) => fresh region of 24 bytes re-aligns the call. }
  AssertTrue('fresh parity region allocated',
    Pos(#9'subq $24, %rsp', Region) >= 0);
  AssertTrue('first overflow slot copied into fresh region',
    Pos(#9'movq 72(%rsp), %rax' + LF + #9'movq %rax, 0(%rsp)', Region) >= 0);
  AssertTrue('second overflow slot copied into fresh region',
    Pos(#9'movq 80(%rsp), %rax' + LF + #9'movq %rax, 8(%rsp)', Region) >= 0);
end;

initialization
  RegisterTest(TNativeCallAlignTests);

end.
