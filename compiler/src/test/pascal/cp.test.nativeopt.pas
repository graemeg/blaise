{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nativeopt;

{ Assembly-level tests for the NATIVE x86-64 backend's local code-quality
  optimisations: trivial-RHS binary operands (no push/pop bracket, immediate
  forms), fused compare-and-branch conditions, small-constant materialisation
  without movabsq, and the adjacent push/pop peephole.

  These pin the *shape* of the emitted assembly for the hot integer paths that
  dominated the native-vs-QBE runtime gap (see perf-optimisation-results.txt).
  Behavioural correctness is covered by the e2e suite; these tests exist so a
  regression back to the stack-machine idiom is caught at unit-test speed. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, uDebugFacts, cp.test.harness;

type
  TNativeOptTests = class(TTestCase)
  private
    function FuncRegion(const AAsm, AName: string): string;
  published
    { Result := N - 1 with a literal RHS: the subtraction must use an
      immediate (subq $1) and the function body must not contain a
      push/pop expression bracket. }
    procedure TestLiteralRhs_ImmediateForm_NoPushPop;
    { Result := A + B with a plain local RHS: RHS is loaded straight into
      the scratch register — no push/pop bracket. }
    procedure TestVarRhs_LoadsRcx_NoPushPop;
    { if N < 2: the condition compares against an immediate and branches
      with a conditional jump — no setcc/movzbl/test materialisation. }
    procedure TestCompareBranch_Fused_ImmediateCmp;
    { Small non-negative constants materialise via movl (zero-extending),
      not a 10-byte movabsq. }
    procedure TestSmallConstant_NoMovabsq;
    { A one-argument call stages its argument with a direct register move,
      not an adjacent pushq/popq pair. }
    procedure TestSingleArgCall_PushPopFused;
    { Interface method with 6 params (Self + 6 args = 7 integer slots): the
      itab-dispatch lowering must spill the overflow slot to the stack.  It
      used to raise "register index 6 out of range" instead of generating. }
    procedure TestInterfaceCall_SevenSlots_Generates;
    { Same overflow through the implicit-Self path of a FLOAT-returning
      6-arg method call (EmitExprToXmm0's embedded call lowering). }
    procedure TestImplicitSelfFloatCall_SevenSlots_Generates;
    { Float arg through itab dispatch: pushed as an 8-byte xmm bit pattern
      and loaded into %xmm0 at the call — never an integer register.  Used
      to fail codegen outright (no float classification at itab sites). }
    procedure TestInterfaceCall_FloatArg_RoutesToXmm;
  end;

implementation

const
  LF = #10;

function TNativeOptTests.FuncRegion(const AAsm, AName: string): string;
var
  StartP, EndP: Integer;
begin
  StartP := Pos(AName + ':', AAsm);
  AssertTrue('function ' + AName + ' present in asm', StartP >= 0);
  EndP := StrPos('.type ' + AName, StrCopyTail(AAsm, StartP));
  AssertTrue('function ' + AName + ' closed', EndP >= 0);
  Result := StrCopyFrom(AAsm, StartP, EndP);
end;

procedure TNativeOptTests.TestLiteralRhs_ImmediateForm_NoPushPop;
const
  Src = '''
      program P;
      function Sub1(N: Integer): Int64;
      begin
        Result := N - 1
      end;
      begin
        WriteLn(Sub1(5))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'Sub1');
  AssertTrue('literal RHS folds to an immediate subtract',
    Pos(#9'subq $1, %rax', Region) >= 0);
  AssertTrue('no push/pop expression bracket in body',
    Pos(#9'pushq %rax', Region) < 0);
  AssertTrue('no movabsq materialisation of the literal',
    Pos('movabsq', Region) < 0);
end;

procedure TNativeOptTests.TestVarRhs_LoadsRcx_NoPushPop;
const
  Src = '''
      program P;
      function Add2(A, B: Integer): Int64;
      begin
        Result := A + B
      end;
      begin
        WriteLn(Add2(2, 3))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'Add2');
  AssertTrue('plain-local RHS loads straight into %rcx',
    Pos(', %rcx', Region) >= 0);
  AssertTrue('no push/pop expression bracket in body',
    Pos(#9'pushq %rax', Region) < 0);
  AssertTrue('operands combine with a register add',
    Pos(#9'addq %rcx, %rax', Region) >= 0);
end;

procedure TNativeOptTests.TestCompareBranch_Fused_ImmediateCmp;
const
  Src = '''
      program P;
      function Classify(N: Integer): Int64;
      begin
        if N < 2 then
          Result := 1
        else
          Result := 0
      end;
      begin
        WriteLn(Classify(7))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'Classify');
  AssertTrue('condition compares against an immediate',
    Pos(#9'cmpl $2, %eax', Region) >= 0);
  AssertTrue('condition branches with jl directly',
    Pos(#9'jl ', Region) >= 0);
  AssertTrue('no setcc materialisation of the condition',
    Pos(#9'setl %al', Region) < 0);
  AssertTrue('no test of a materialised boolean',
    Pos(#9'testq %rax, %rax', Region) < 0);
end;

procedure TNativeOptTests.TestSmallConstant_NoMovabsq;
const
  Src = '''
      program P;
      function Five: Int64;
      begin
        Result := 5
      end;
      begin
        WriteLn(Five())
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'Five');
  AssertTrue('small constant loads via movl (zero-extends to 64-bit)',
    Pos(#9'movl $5, %eax', Region) >= 0);
  AssertTrue('no movabsq for an imm32-range constant',
    Pos('movabsq', Region) < 0);
end;

procedure TNativeOptTests.TestSingleArgCall_PushPopFused;
const
  Src = '''
      program P;
      function Twice(N: Integer): Int64;
      begin
        Result := N * 2
      end;
      var X: Integer;
      begin
        X := 3;
        WriteLn(Twice(X + 1))
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src, TargetX86_64), 'main');
  AssertTrue('argument staged with a direct move',
    Pos(#9'movq %rax, %rdi', Region) >= 0);
  AssertTrue('no adjacent pushq/popq pair survives the peephole',
    Pos(#9'pushq %rax' + LF + #9'popq %rdi', Region) < 0);
end;

procedure TNativeOptTests.TestInterfaceCall_SevenSlots_Generates;
const
  Src = '''
      program P;
      type
        ISink = interface
          function Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
        end;
        TSink = class(TObject, ISink)
        public
          function Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
        end;
      function TSink.Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
      begin
        Result := AA + AB + AC + AD + AE
      end;
      var S: ISink;
      begin
        S := TSink.Create();
        WriteLn(S.Take('abc', 1, 2, 3, 4, 5))
      end.
      ''';
var
  Asm_: string;
begin
  { Red state raised ENativeCodeGenError ("register index 6 out of range")
    from the itab-dispatch pop loop; generating at all is the regression
    guard, the itab call shape pins that the dispatch path was taken. }
  Asm_ := GenAsm(Src, TargetX86_64);
  AssertTrue('itab dispatch emitted', Pos(#9'callq *%r11', Asm_) >= 0);
end;

procedure TNativeOptTests.TestImplicitSelfFloatCall_SevenSlots_Generates;
const
  Src = '''
      program P;
      type
        TCalc = class
        public
          function Mix(AA, AB, AC, AD, AE, AF: Integer): Double;
          function Run: Double;
        end;
      function TCalc.Mix(AA, AB, AC, AD, AE, AF: Integer): Double;
      begin
        Result := AA + AB + AC + AD + AE + AF
      end;
      function TCalc.Run: Double;
      begin
        { implicit-Self call in float expression position: lowered by
          EmitExprToXmm0's embedded method-call path }
        Result := Mix(1, 2, 3, 4, 5, 6) * 2.0
      end;
      var C: TCalc;
      begin
        C := TCalc.Create();
        WriteLn(C.Run() > 41.0)
      end.
      ''';
begin
  { Generating without ENativeCodeGenError is the regression guard. }
  AssertTrue('program generates', Length(GenAsm(Src, TargetX86_64)) > 0);
end;

procedure TNativeOptTests.TestInterfaceCall_FloatArg_RoutesToXmm;
const
  Src = '''
      program P;
      type
        IM = interface
          function Mix(A: Integer; X: Double; B: Integer): Integer;
        end;
        TM = class(TObject, IM)
        public
          function Mix(A: Integer; X: Double; B: Integer): Integer;
        end;
      function TM.Mix(A: Integer; X: Double; B: Integer): Integer;
      begin
        Result := A + B
      end;
      var M: IM;
      begin
        M := TM.Create();
        WriteLn(M.Mix(7, 2.5, 9))
      end.
      ''';
var
  Asm_: string;
begin
  Asm_ := GenAsm(Src, TargetX86_64);
  AssertTrue('itab dispatch emitted', Pos(#9'callq *%r11', Asm_) >= 0);
  AssertTrue('float slot loads into an xmm register',
    Pos(#9'movsd 0(%rsp), %xmm0', Asm_) >= 0);
end;

initialization
  RegisterTest(TNativeOptTests);

end.
