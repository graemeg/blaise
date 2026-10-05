{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nativepromo;

{ Assembly-level tests for the NATIVE x86-64 backend's stage-1 register
  promotion: hot, safe scalar locals/params live in the callee-saved
  %r14/%r15 for the whole function body instead of stack slots.

  The scheme is two-pass per function: pass 1 emits with promotion off;
  if that text contains NO %r14/%r15 (the emitter's scratch windows all
  save/restore through those registers) and candidates exist, the text is
  rolled back and re-emitted with the top candidates register-resident.
  A function whose pass-1 text DOES use %r14/%r15 keeps the unpromoted
  output — so promotion can never race the emitter's own scratch usage.

  Exclusions pinned here: address-taken locals, functions containing
  try statements (the setjmp contract requires slot storage), and
  --debug-opdf builds (pdr reads frame slots; OPDF has no register
  location expression yet). }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, uDebugFacts, cp.test.harness;

type
  TNativePromoTests = class(TTestCase)
  private
    function FuncRegion(const AAsm, AName: string): string;
  published
    { Fib-shaped function: N and Result promoted — the body performs no
      -N(%rbp) reloads of the param, and %r14/%r15 appear. }
    procedure TestHotParamAndResult_Promoted;
    { The promoted registers are saved to frame slots in the prologue and
      restored before the frame teardown. }
    procedure TestPromotion_SavesAndRestoresIncumbents;
    { A local whose address is taken via @ must stay in its slot. }
    procedure TestAddrTakenLocal_NotPromoted;
    { A function containing try/finally must not promote (setjmp). }
    procedure TestTryStmt_DisablesPromotion;
    { A function whose emitted body already uses %r14/%r15 as scratch
      (managed record local → ARC release walk) keeps the unpromoted
      pass-1 output. }
    procedure TestScratchWindowConflict_KeepsUnpromoted;
    { Byte-typed promoted var uses width-correct sub-register forms. }
    procedure TestByteVar_SubRegisterForms;
    { Under --debug-opdf promotion is fully disabled: no %r14/%r15 and
      the param still spills to its frame slot. }
    procedure TestDebugOpdf_DisablesPromotion;
    { A local passed to an INTERFACE method's out param has its address
      taken through the itab dispatch (no ResolvedMethod on the call
      node) — it must be excluded from promotion, not raise. }
    procedure TestIntfOutParam_ExcludedNotError;
    { A local passed to a var param through a procedural-typed VARIABLE
      (indirect call — signature lives on the proc type) must likewise
      be excluded from promotion. }
    procedure TestIndirectVarParam_ExcludedNotError;
    { With %r13 also proven free, the two-call binary bracket pins its
      LHS in %r13 instead of pushq/popq — the fib body carries no
      push/pop at all. }
    procedure TestCrossCallPin_UsesR13_NoPush;
    { The for-loop condition loads the end slot straight into %rcx —
      no per-iteration push/pop pair. }
    procedure TestForCond_NoPushPop;
  end;

implementation

const
  LF = #10;

const
  SrcFib = '''
      program P;
      function Fib(N: Integer): Int64;
      begin
        if N < 2 then
          Result := N
        else
          Result := Fib(N - 1) + Fib(N - 2)
      end;
      begin
        WriteLn(Fib(10))
      end.
      ''';

function TNativePromoTests.FuncRegion(const AAsm, AName: string): string;
var
  StartP, EndP: Integer;
begin
  StartP := Pos(AName + ':', AAsm);
  AssertTrue('function ' + AName + ' present in asm', StartP >= 0);
  EndP := StrPos('.type ' + AName, StrCopyTail(AAsm, StartP));
  AssertTrue('function ' + AName + ' closed', EndP >= 0);
  Result := StrCopyFrom(AAsm, StartP, EndP);
end;

procedure TNativePromoTests.TestHotParamAndResult_Promoted;
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(SrcFib, TargetX86_64), 'Fib');
  AssertTrue('promoted registers appear in the body',
    (Pos('%r14', Region) >= 0) and (Pos('%r15', Region) >= 0));
  { The param must live in a register: after the prologue there are no
    slot reloads of it.  The only -N(%rbp) traffic allowed is the
    incumbent save/restore pair. }
  AssertTrue('no movslq slot reload of the promoted param',
    Pos('movslq -', Region) < 0);
end;

procedure TNativePromoTests.TestPromotion_SavesAndRestoresIncumbents;
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(SrcFib, TargetX86_64), 'Fib');
  { Incumbent save: movq %r14, -N(%rbp) in the prologue; restore:
    movq -N(%rbp), %r14 before the frame teardown. }
  AssertTrue('incumbent %r14 saved to a frame slot',
    Pos('movq %r14, -', Region) >= 0);
  AssertTrue('incumbent %r14 restored from its frame slot',
    (Pos(', %r14' + LF, Region) >= 0) or (Pos(', %r14', Region) >= 0));
  AssertTrue('no pushq of promoted registers (frame-slot save, not push)',
    Pos(#9'pushq %r14', Region) < 0);
end;

procedure TNativePromoTests.TestAddrTakenLocal_NotPromoted;
const
  Src = '''
      program P;
      function F(N: Integer): Integer;
      var A: Integer; PA: ^Integer;
      begin
        A := N;
        PA := @A;
        A := A + A + A + A;
        Result := PA^ + A
      end;
      begin
        WriteLn(F(3))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'F');
  { A is the hottest local but its address escapes — it must stay in its
    slot so PA^ observes the stores.  N may still be promoted; assert A's
    leaq source remains a frame slot. }
  AssertTrue('address-taken local keeps a frame-slot leaq',
    Pos('leaq -', Region) >= 0);
end;

procedure TNativePromoTests.TestTryStmt_DisablesPromotion;
const
  Src = '''
      program P;
      uses SysUtils;
      function F(N: Integer): Integer;
      begin
        Result := 0;
        try
          Result := N + N + N + N
        finally
          Result := Result + 1
        end
      end;
      begin
        WriteLn(F(3))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'F');
  AssertTrue('try-containing function keeps slot-resident locals',
    Pos('%r14', Region) < 0);
end;

procedure TNativePromoTests.TestScratchWindowConflict_KeepsUnpromoted;
const
  { A local record with a NESTED record holding a string forces the
    epilogue ARC release walk to recurse — the recursion pins the nested
    base in %r14 (see EmitRecordFieldReleases) — so pass 1 text contains
    %r14 and the function must NOT be re-emitted with promotion. }
  Src = '''
      program P;
      type
        TInner = record S: String; end;
        TRec = record I: TInner; end;
      function F(N: Integer): Integer;
      var R: TRec; K: Integer;
      begin
        R.I.S := 'x';
        K := N + N + N + N;
        Result := K + N
      end;
      begin
        WriteLn(F(3))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'F');
  { The hot scalar I/N must remain slot-resident: any %r14 occurrences
    are the ARC walker's own save/restore brackets (pushq %r14), never a
    promoted-var access pattern (movq %r14, -save(%rbp)). }
  AssertTrue('scratch window present (ARC walk)',
    Pos('%r14', Region) >= 0);
  AssertTrue('no promotion incumbent save alongside scratch windows',
    Pos('movq %r14, -', Region) < 0);
end;

procedure TNativePromoTests.TestByteVar_SubRegisterForms;
const
  { The Byte param is first in declaration order, so it takes %r14: its
    incoming spill and every store use the byte sub-register, and loads
    zero-extend from it. }
  Src = '''
      program P;
      function F(B: Byte): Integer;
      begin
        B := B + 1;
        B := B + 2;
        Result := B + 3
      end;
      begin
        WriteLn(F(1))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'F');
  AssertTrue('byte param promoted', Pos('%r14', Region) >= 0);
  AssertTrue('byte-width sub-register form used', Pos('%r14b', Region) >= 0);
end;

procedure TNativePromoTests.TestDebugOpdf_DisablesPromotion;
var
  Region: string;
begin
  Region := FuncRegion(GenAsmDebug(SrcFib, TargetX86_64), 'Fib');
  AssertTrue('debug build keeps slot-resident locals (no %r14)',
    Pos('%r14', Region) < 0);
  AssertTrue('debug build keeps slot-resident locals (no %r15)',
    Pos('%r15', Region) < 0);
  AssertTrue('param spilled to its frame slot as before',
    Pos('movl %edi, -', Region) >= 0);
end;

procedure TNativePromoTests.TestIntfOutParam_ExcludedNotError;
const
  Src = '''
      program P;
      type
        IStore = interface
          function GetPair(out A: Integer; out B: Integer): Boolean;
        end;
        TStore = class(IStore)
          function GetPair(out A: Integer; out B: Integer): Boolean;
        end;
      function TStore.GetPair(out A: Integer; out B: Integer): Boolean;
      begin
        A := 7; B := 9; Result := True
      end;
      function UseIt(S: IStore): Integer;
      var X, Y: Integer;
      begin
        if S.GetPair(X, Y) then
          Result := X * 100 + Y
        else
          Result := 0
      end;
      var Obj: TStore; Itf: IStore;
      begin
        Obj := TStore.Create();
        Itf := Obj;
        WriteLn(UseIt(Itf))
      end.
      ''';
var
  Region: string;
begin
  { The generation itself must not raise; X/Y stay slot-resident. }
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'UseIt');
  AssertTrue('out-param locals keep frame-slot leaq',
    Pos('leaq -', Region) >= 0);
end;

procedure TNativePromoTests.TestIndirectVarParam_ExcludedNotError;
const
  Src = '''
      program P;
      type TBump = procedure(var N: Integer);
      procedure DoBump(var N: Integer);
      begin
        N := N + 1
      end;
      function Run: Integer;
      var P1: TBump; V: Integer;
      begin
        P1 := @DoBump;
        V := 41;
        P1(V);
        Result := V
      end;
      begin
        WriteLn(Run())
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'Run');
  AssertTrue('var-param local keeps frame-slot leaq',
    Pos('leaq -', Region) >= 0);
end;

procedure TNativePromoTests.TestCrossCallPin_UsesR13_NoPush;
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(SrcFib, TargetX86_64), 'Fib');
  AssertTrue('LHS pinned in %r13 across the second recursive call',
    Pos(#9'movq %rax, %r13', Region) >= 0);
  AssertTrue('no push/pop bracket remains in the promoted body',
    Pos(#9'pushq %rax', Region) < 0);
end;

procedure TNativePromoTests.TestForCond_NoPushPop;
const
  Src = '''
      program P;
      function SumTo(N: Integer): Int64;
      var I: Integer;
      begin
        Result := 0;
        for I := 1 to N do
          Result := Result + I
      end;
      begin
        WriteLn(SumTo(10))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'SumTo');
  AssertTrue('no push/pop in the loop condition',
    Pos(#9'pushq %rax', Region) < 0);
end;

initialization
  RegisterTest(TNativePromoTests);

end.
