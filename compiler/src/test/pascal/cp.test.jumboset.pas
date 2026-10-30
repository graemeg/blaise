{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.jumboset;

{ Code-generation tests for JUMBO sets -- `set of <enum>` whose enum has more
  than 64 members (up to the 256 ceiling).  Jumbo sets are inline byte-array
  bitmaps operated on via the _Set* RTL helpers, unlike <=64-member sets which
  stay in a register.  Their run-time behaviour (membership, set operators,
  field / var-param / array-element stores, constants) is covered by
  cp.test.e2e.jumboset; what stays here is the lowering choice a running
  program cannot observe. }

interface

uses
  Classes, SysUtils, blaise.testing, cp.test.harness;

type
  TJumboSetTests = class(TTestCase)
  published
    { a DISCARDED method call returning a static array still hands the
      callee a result buffer: x8 on arm64, a frame scratch in %rdi on x86-64
      (neither got one) }
    procedure TestCodegen_DiscardedAggMethodCall_GetsBuffer;
    { x86-64: a jumbo-set call result used as an operand lives in a frame
      scratch slot, not a buffer left on the stack under a saved operand }
    procedure TestCodegen_CallResultOperand_FrameScratch;
    procedure TestSmallSet_StillUsesRegister;
    { s := V through a var jumbo-set param: the bitmap is copied into the
      caller's storage the slot points at.  arm64 refused the parameter
      ("var parameter of this type"). }
    procedure TestCodegen_VarParam_CopiesIntoCallerStorage;
  end;

implementation

const
  { An 80-member enum (b00..b79) -- clears the 64 boundary cheaply. }
  EnumDecl =
    '  TBig = (b00,b01,b02,b03,b04,b05,b06,b07,b08,b09,b10,b11,b12,b13,b14,b15,' + #10 +
    '          b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,' + #10 +
    '          b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,' + #10 +
    '          b48,b49,b50,b51,b52,b53,b54,b55,b56,b57,b58,b59,b60,b61,b62,b63,' + #10 +
    '          b64,b65,b66,b67,b68,b69,b70,b71,b72,b73,b74,b75,b76,b77,b78,b79);' + #10 +
    '  TBigSet = set of TBig;' + #10;

procedure TJumboSetTests.TestSmallSet_StillUsesRegister;
const
  SmallSrc = '''
    program P;
    type TSmall = (s0, s1, s2, s3); TSmallSet = set of TSmall;
    var s, t: TSmallSet; b: Boolean;
    begin
      s := [s1];
      t := s + [s2];
      b := s1 in t;
      WriteLn(b)
    end.
    ''';
var
  JumboSrc, Target: string;
  I: Int;
begin
  { A <=64 set must NOT use the jumbo _Set* helpers -- it stays a register
    bitmask.  The jumbo program is the control: the same shape over an
    80-member enum does call them, so the absence check is not vacuous. }
  JumboSrc := 'program P;' + #10 + 'type' + #10 + EnumDecl +
              'var s, t: TBigSet; b: Boolean;' + #10 +
              'begin s := [b01]; t := s + [b02]; b := b01 in t; WriteLn(b) end.';
  for I := 0 to 1 do
  begin
    if I = 0 then
      Target := TargetX86_64
    else
      Target := TargetArm64;
    AssertTrue(Target + ': jumbo set calls _SetIn',
      Pos('_SetIn', GenAsm(JumboSrc, Target)) >= 0);
    AssertTrue(Target + ': jumbo set calls _SetUnion',
      Pos('_SetUnion', GenAsm(JumboSrc, Target)) >= 0);
    AssertTrue(Target + ': small set does not call _SetIn',
      Pos('_SetIn', GenAsm(SmallSrc, Target)) < 0);
    AssertTrue(Target + ': small set does not call _SetUnion',
      Pos('_SetUnion', GenAsm(SmallSrc, Target)) < 0);
  end;
end;

procedure TJumboSetTests.TestCodegen_VarParam_CopiesIntoCallerStorage;
const
  Src = '''
    program Prg;
    type TB = 0..99; TBig = set of TB;
    procedure Fill(var s: TBig); begin s := [5, 70] end;
    var A: TBig;
    begin
      Fill(A);
      WriteLn(70 in A)
    end.
    ''';
begin
  AssertEquals('memcpy into the address the var slot holds', '',
    AsmMissing(Src,
      #9'movq -32(%rbp), %rdi'#10#9'movq $32, %rdx'#10#9'callq memcpy',
      #9'ldur x0, [x29, #-8]'#10#9'movz x2, #32'#10#9'bl _memcpy'));
end;

procedure TJumboSetTests.TestCodegen_CallResultOperand_FrameScratch;
var
  AsmT: string;
begin
  AsmT := GenAsm('''
    program P;
    type
      TBig = 0..199;
      TJumbo = set of TBig;
    function Mine(A, B: Integer): TJumbo; begin Result := [A, B] end;
    begin
      WriteLn(7 in Mine(7, 199))
    end.
    ''', TargetX86_64);
  AssertTrue('the result is not addressed at the stack top',
    Pos(#9'leaq (%rsp), %rax', AsmT) < 0);
  AssertTrue('the result is addressed in the frame',
    Pos(#9'leaq -', AsmT) >= 0);
end;

procedure TJumboSetTests.TestCodegen_DiscardedAggMethodCall_GetsBuffer;
const
  Src = '''
    program P;
    type
      TTri = array[0..2] of Int64;
      TBase = class
        function Tri(N: Int64): TTri;
      end;
    function TBase.Tri(N: Int64): TTri; begin Result[0] := N end;
    var K: TBase;
    begin
      K := TBase.Create();
      K.Tri(3)
    end.
    ''';
var
  A64, X86: string;
  CallPos: Int;
begin
  A64 := GenAsm(Src, TargetArm64);
  CallPos := Pos(#9'bl _TBase_Tri', A64);
  AssertTrue('arm64 calls the method', CallPos >= 0);
  AssertTrue('arm64 sets x8 before the call',
    Pos(#9'sub x8, x29, #', Copy(A64, 0, CallPos)) >= 0);
  X86 := GenAsm(Src, TargetX86_64);
  CallPos := Pos(#9'callq TBase_Tri', X86);
  AssertTrue('x86-64 calls the method', CallPos >= 0);
  AssertTrue('x86-64 passes a frame buffer before the call',
    Pos('(%rbp), %r', Copy(X86, 0, CallPos)) >= 0);
end;

initialization
  RegisterTest(TJumboSetTests);

end.
