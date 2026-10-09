{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.recordret;

{ Return-ABI coverage for records returned by value.

  Between two Blaise routines the caller and callee always agree on how a
  record comes back, so a wrong classification is invisible when the
  program runs (cp.test.e2e.recordret round-trips every class); it only
  shows at the C boundary.  These tests pin the platform ABI on both ISAs,
  which classify differently: SysV x86-64 splits an Integer + Double record
  across %rax and %xmm0, while AAPCS64 returns a mixed record in x0:x1 and
  only a homogeneous floating-point aggregate in d registers.  A managed
  field or a record over 16 bytes goes through the hidden result pointer
  (%rdi / x8) on both. }

interface

uses
  blaise.testing, cp.test.harness;

type
  TRecordReturnTests = class(TTestCase)
  private
    function Callee(const ASrc, AName, ATarget: string): string;
  published
    procedure TestReturnAbi_TwoInt64_IntegerRegisterPair;
    procedure TestReturnAbi_OneDouble_FloatRegister;
    procedure TestReturnAbi_TwoDoubles_FloatRegisterPair;
    procedure TestReturnAbi_IntegerPlusDouble_PerIsaClassification;
    procedure TestReturnAbi_ManagedField_HiddenResultPointer;
    procedure TestReturnAbi_Over16Bytes_HiddenResultPointer;
    { A discarded record-returning call on an interface FIELD of Self
      (FS.MakeRect(5); inside a method) must dispatch through the field, not
      through a global FS_obj/FS_itab pair that does not exist (x86-64). }
    procedure TestDiscardedIntfRecordCall_ImplicitSelfField_UsesTheField;
  end;

implementation

function TRecordReturnTests.Callee(const ASrc, AName, ATarget: string): string;
var
  AsmText, Lbl: string;
  P, E: Integer;
begin
  { The callee's body, from its label to its first ret.  The programs below
    have an empty main, so the patterns cannot come from a caller. }
  AsmText := GenAsm(ASrc, ATarget);
  if ATarget = TargetArm64 then
    Lbl := #10 + '_' + AName + ':'
  else
    Lbl := #10 + AName + ':';
  P := Pos(Lbl, AsmText);
  AssertTrue(ATarget + ': ' + AName + ' emitted', P >= 0);
  Result := Copy(AsmText, P, Length(AsmText) - P);
  E := Pos(#9 + 'ret', Result);
  AssertTrue(ATarget + ': ' + AName + ' returns', E >= 0);
  Result := Copy(Result, 0, E);
end;

procedure TRecordReturnTests.TestReturnAbi_TwoInt64_IntegerRegisterPair;
const
  Src = '''
    program P;
    type T2L = record A, B: Int64; end;
    function MakeL: T2L; begin Result.A := 11; Result.B := 22 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: second eightbyte in %rdx',
    Pos('movq 8(%rcx), %rdx', Callee(Src, 'MakeL', TargetX86_64)) >= 0);
  AssertTrue('arm64: second eightbyte in x1',
    Pos('ldr x1, [x9, #8]', Callee(Src, 'MakeL', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_OneDouble_FloatRegister;
const
  Src = '''
    program P;
    type T1D = record X: Double; end;
    function MakeD: T1D; begin Result.X := 1.5 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: returned in %xmm0',
    Pos('%xmm0', Callee(Src, 'MakeD', TargetX86_64)) >= 0);
  AssertTrue('arm64: returned in d0',
    Pos('ldr d0, ', Callee(Src, 'MakeD', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_TwoDoubles_FloatRegisterPair;
const
  Src = '''
    program P;
    type T2D = record X, Y: Double; end;
    function MakeD: T2D; begin Result.X := 1.5; Result.Y := 2.5 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: second double in %xmm1',
    Pos('movsd 8(%rcx), %xmm1', Callee(Src, 'MakeD', TargetX86_64)) >= 0);
  AssertTrue('arm64: homogeneous float aggregate in d0:d1',
    Pos('ldr d1, [x9, #8]', Callee(Src, 'MakeD', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_IntegerPlusDouble_PerIsaClassification;
const
  Src = '''
    program P;
    type TID = record I: Integer; D: Double; end;
    function MakeID: TID; begin Result.I := 3; Result.D := 4.5 end;
    begin end.
    ''';
var
  X86, A64: string;
begin
  X86 := Callee(Src, 'MakeID', TargetX86_64);
  AssertTrue('x86-64: INTEGER eightbyte in %rax',
    Pos('movq (%rcx), %rax', X86) >= 0);
  AssertTrue('x86-64: SSE eightbyte in %xmm0',
    Pos('movsd 8(%rcx), %xmm0', X86) >= 0);
  A64 := Callee(Src, 'MakeID', TargetArm64);
  AssertTrue('arm64: a mixed record is not an HFA -- second half in x1',
    Pos('ldr x1, [x9, #8]', A64) >= 0);
  AssertTrue('arm64: no d-register return for a mixed record',
    (Pos('ldr d0, [x9, #0]', A64) < 0) and (Pos('ldr d1, [x9, #8]', A64) < 0));
end;

procedure TRecordReturnTests.TestReturnAbi_ManagedField_HiddenResultPointer;
const
  Src = '''
    program P;
    type TS = record S: string; end;
    function MakeS: TS; begin Result.S := 'x' end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: the result pointer arrives in %rdi',
    Pos('movq %rdi, ', Callee(Src, 'MakeS', TargetX86_64)) >= 0);
  AssertTrue('arm64: the result pointer arrives in x8',
    Pos('stur x8, ', Callee(Src, 'MakeS', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_Over16Bytes_HiddenResultPointer;
const
  Src = '''
    program P;
    type T3 = record A, B, C: Int64; end;
    function Make3: T3; begin Result.A := 1; Result.C := 3 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: the result pointer arrives in %rdi',
    Pos('movq %rdi, ', Callee(Src, 'Make3', TargetX86_64)) >= 0);
  AssertTrue('arm64: the result pointer arrives in x8',
    Pos('stur x8, ', Callee(Src, 'Make3', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestDiscardedIntfRecordCall_ImplicitSelfField_UsesTheField;
const
  Src = '''
    program P;
    type
      TRect = record Name: string; N: Integer; end;
      IShape = interface
        function MakeRect(AN: Integer): TRect;
      end;
      TUser = class
        FS: IShape;
        procedure Go();
      end;
    procedure TUser.Go();
    begin
      FS.MakeRect(5)
    end;
    begin
    end.
    ''';
var
  AsmT: string;
begin
  AsmT := GenAsm(Src, TargetX86_64);
  AssertTrue('x86-64: no global FS_obj receiver', Pos('FS_obj', AsmT) < 0);
  AssertTrue('x86-64: no global FS_itab receiver', Pos('FS_itab', AsmT) < 0);
  AssertTrue('x86-64: dispatched through the itab', Pos(#9'callq *%r11', AsmT) >= 0);
end;

initialization
  RegisterTest(TRecordReturnTests);

end.
