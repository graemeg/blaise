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
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, uDebugFacts, cp.test.harness;

type
  TNativeCallAlignTests = class(TTestCase)
  private
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
    { No red zone: nothing is kept below %rsp.  Windows may write below %rsp
      when it dispatches an exception, so the x86-64 backend must not rely
      on the System V red zone (windows-x86_64-backend-design.adoc, "No red
      zone").  Neither a negative %rsp displacement nor an %rbp slot beyond
      the frame the prologue reserved may appear. }
    procedure TestNoRedZone_NothingBelowRsp;
  end;

implementation

const
  LF = #10;

function TNativeCallAlignTests.FuncRegion(const AAsm, AName: string): string;
var
  StartP, EndP: Int;
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
      function Inner: Int; begin Result := 7 end;
      function Add2(A, B: Int): Int; begin Result := A + B end;
      var X: Int;
      begin
        X := Add2(1, Inner())
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'main');
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
      function Inner: Int; begin Result := 7 end;
      function Add2(A, B: Int): Int; begin Result := A + B end;
      var X: Int;
      begin
        X := Add2(Inner(), 1)
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'main');
  AssertTrue('inner call present', Pos('callq Inner', Region) >= 0);
  AssertTrue('inner call at aligned depth is not pad-wrapped',
    Pos(#9'subq $8, %rsp' + LF + #9'callq Inner', Region) < 0);
end;

procedure TNativeCallAlignTests.TestTwoLevelNesting_PadOnlyAtOddDepth;
const
  Src = '''
      program P;
      function Inner: Int; begin Result := 7 end;
      function Add2(A, B: Int): Int; begin Result := A + B end;
      function Add3(A, B, C: Int): Int; begin Result := A + B + C end;
      var X: Int;
      begin
        X := Add3(1, 2, Add2(3, Inner()))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'main');
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
      function Sum8(A, B, C, D, E, F, G, H: Int): Int;
      begin
        Result := A + B + C + D + E + F + G + H
      end;
      function Add2(A, B: Int): Int; begin Result := A + B end;
      var X: Int;
      begin
        X := Add2(1, Sum8(1, 2, 3, 4, 5, 6, 7, 8))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'main');
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

{ The first red-zone use in AAsm, or ''.  Per function, the frame is what
  the prologue reserves below %rbp (pushes plus the subq straight after
  `movq %rsp, %rbp`); an -K(%rbp) operand with K beyond it, or any negative
  %rsp displacement, addresses memory below the stack pointer. }
function RedZoneUse(const AAsm: string): string;
var
  Lines: TStringList;
  I, P, Q, K, Frame: Int;
  L, Fn: string;
  Framed, InProlog: Boolean;
begin
  Result := '';
  Lines := TStringList.Create();
  try
    Lines.Text := AAsm;
    Fn := '';
    Framed := False;
    InProlog := False;
    Frame := 0;
    for I := 0 to Lines.Count - 1 do
    begin
      L := Lines.Strings[I];
      if (Length(L) > 1) and (StrAt(L, 0) <> 9) and (StrAt(L, 0) <> Ord('.'))
         and (StrAt(L, Length(L) - 1) = Ord(':')) then
      begin
        Fn := L;
        Framed := False;
        Continue;
      end;
      P := Pos('(%rsp)', L);
      if (P > 0) and (Pos('-', Copy(L, 0, P)) >= 0) and
         (StrAt(L, P - 1) >= Ord('0')) and (StrAt(L, P - 1) <= Ord('9')) then
      begin
        Q := P - 1;
        while (Q > 0) and (StrAt(L, Q - 1) >= Ord('0')) and
              (StrAt(L, Q - 1) <= Ord('9')) do
          Q := Q - 1;
        if (Q > 0) and (StrAt(L, Q - 1) = Ord('-')) then
          Exit(Fn + ' negative %rsp displacement: ' + L);
      end;
      if L = #9'movq %rsp, %rbp' then
      begin
        Framed := True;
        InProlog := True;
        Frame := 0;
        Continue;
      end;
      if not Framed then Continue;
      if InProlog then
      begin
        if Pos(#9'pushq ', L) = 0 then
        begin
          Frame := Frame + 8;
          Continue;
        end;
        InProlog := False;
        if (Pos(#9'subq $', L) = 0) and (Pos(', %rsp', L) > 0) then
        begin
          Frame := Frame + StrToInt(Copy(L, 7, Pos(',', L) - 7));
          Continue;
        end;
      end;
      P := Pos('(%rbp)', L);
      while P > 0 do
      begin
        Q := P;
        while (Q > 0) and (StrAt(L, Q - 1) >= Ord('0')) and
              (StrAt(L, Q - 1) <= Ord('9')) do
          Q := Q - 1;
        if (Q > 0) and (Q < P) and (StrAt(L, Q - 1) = Ord('-')) then
        begin
          K := StrToInt(Copy(L, Q, P - Q));
          if K > Frame then
            Exit(Fn + ' -' + IntToStr(K) + '(%rbp) beyond a ' +
              IntToStr(Frame) + '-byte frame: ' + L);
        end;
        L := Copy(L, P + 6, Length(L) - P - 6);
        P := Pos('(%rbp)', L);
      end;
    end;
  finally
    Lines.Free();
  end;
end;

procedure TNativeCallAlignTests.TestNoRedZone_NothingBelowRsp;
const
  Src =
    '''
        program RedZone;
        type
          TRec = record A, B, C, D: Int64; S: string; end;
          TObj = class
            F: Int64;
            function Sum(X, Y: Int64): Int64;
          end;
        threadvar
          TV: Int64;
        var
          G: TRec;
        function TObj.Sum(X, Y: Int64): Int64;
        begin
          Result := X + Y + F;
        end;
        function Many(A, B, C, D, E, F, G2, H: Int64; X: Float64): Int64;
        var
          Buf: array[0..63] of Int64;
          I: Int;
        begin
          for I := 0 to 63 do
            Buf[I] := A + I;
          Result := Buf[7] + B + C + D + E + F + G2 + H + Trunc(X);
        end;
        function MakeRec(N: Int64): TRec;
        begin
          Result.A := N;
          Result.S := IntToStr(N);
        end;
        procedure Leaf;
        begin
          TV := TV + 1;
        end;
        var
          O: TObj;
          R: TRec;
          S: string;
        begin
          O := TObj.Create();
          try
            R := MakeRec(O.Sum(1, Many(1, 2, 3, 4, 5, 6, 7, 8, 1.5)));
            S := R.S + ' ' + IntToStr(R.A);
            Leaf();
            G := R;
          except
            WriteLn('raised');
          end;
          WriteLn(S, TV);
        end.
        ''';
var
  AsmText, Bad: string;
begin
  { the checker itself: it must see a slot below the prologue's frame }
  AssertTrue('checker flags an %rbp slot below the frame',
    RedZoneUse('f:'#10#9'pushq %rbp'#10#9'movq %rsp, %rbp'#10 +
      #9'subq $16, %rsp'#10#9'movq %rax, -24(%rbp)'#10) <> '');
  AssertTrue('checker flags a negative %rsp displacement',
    RedZoneUse('f:'#10#9'movq %rax, -8(%rsp)'#10) <> '');
  AssertEquals('checker passes a slot inside the frame', '',
    RedZoneUse('f:'#10#9'pushq %rbp'#10#9'movq %rsp, %rbp'#10 +
      #9'subq $16, %rsp'#10#9'movq %rax, -16(%rbp)'#10));
  AsmText := GenAsm(Src, TargetX86_64);
  AssertTrue('the probe has framed routines with %rbp slots',
    (Pos(#9'movq %rsp, %rbp', AsmText) >= 0) and (Pos('(%rbp)', AsmText) >= 0));
  Bad := RedZoneUse(AsmText);
  AssertEquals('no data kept below %rsp', '', Bad);
end;

initialization
  RegisterTest(TNativeCallAlignTests);

end.
