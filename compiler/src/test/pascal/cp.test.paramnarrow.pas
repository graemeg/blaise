{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.paramnarrow;

{ A by-value parameter narrower than 64 bits is extended from its own width
  in the callee prologue (BUG-20261027-int64-arg-to-integer-param-not-narrowed).

  arm64 keeps integer locals in 8-byte slots and reads them back at full
  width, so the prologue must extend each narrow parameter before spilling
  it: the caller may pass a wider value, AAPCS64 leaves the upper bits of a
  32-bit argument unspecified, and a stack argument is loaded with a
  zero-extending ldr.  x86-64 needs nothing: its callee reads the 32-bit
  sub-register.  The run-time behaviour is in cp.test.e2e.paramnarrow. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat, cp.test.harness;

type
  TParamNarrowTests = class(TTestCase)
  published
    procedure TestAsm_IntegerParam_SignExtendedBeforeSpill;
    procedure TestAsm_ByteParam_ZeroExtendedBeforeSpill;
    procedure TestAsm_Int8StackParam_SignExtendedAfterLoad;
    procedure TestAsm_Int64Param_NotExtended;
    procedure TestAsm_WriteLnUInt32_UsesUnsignedWriter;
  end;

implementation

procedure TParamNarrowTests.TestAsm_IntegerParam_SignExtendedBeforeSpill;
const
  Src = 'program P; procedure Q(X: Integer); begin WriteLn(X) end; ' +
    'begin Q(1) end.';
begin
  AssertEquals('Integer param extended from 32 bits', '',
    AsmMissing(Src, 'movl %edi, %r14d', 'sxtw x0, w0'#10#9'stur x0'));
end;

procedure TParamNarrowTests.TestAsm_ByteParam_ZeroExtendedBeforeSpill;
const
  Src = 'program P; procedure Q(X: Byte); begin WriteLn(X) end; ' +
    'begin Q(1) end.';
begin
  AssertEquals('Byte param extended from 8 bits', '',
    AsmMissing(Src, 'movb %dil', 'lsl x0, x0, #56'#10#9'lsr x0, x0, #56'#10#9'stur x0'));
end;

procedure TParamNarrowTests.TestAsm_Int8StackParam_SignExtendedAfterLoad;
const
  Src = 'program P; ' +
    'procedure Q(A, B, C, D, E, F, G, H: Int64; X: Int8); ' +
    'begin WriteLn(X) end; ' +
    'begin Q(0, 0, 0, 0, 0, 0, 0, 0, -1) end.';
begin
  AssertTrue('arm64: the ninth argument is sign-extended from 8 bits',
    Pos('lsl x9, x9, #56'#10#9'asr x9, x9, #56'#10#9'stur x9', GenAsm(Src, TargetArm64)) >= 0);
end;

procedure TParamNarrowTests.TestAsm_Int64Param_NotExtended;
const
  Src = 'program P; procedure Q(X: Int64); begin WriteLn(X) end; ' +
    'begin Q(1) end.';
begin
  AssertTrue('arm64: an Int64 param is spilled as it arrives',
    Pos('sxtw', GenAsm(Src, TargetArm64)) < 0);
end;

procedure TParamNarrowTests.TestAsm_WriteLnUInt32_UsesUnsignedWriter;
const
  Src = 'program P; var U: UInt32; begin U := 1; WriteLn(U) end.';
begin
  AssertEquals('WriteLn(UInt32) calls the unsigned writer', '',
    AsmMissing(Src, 'SysWriteUInt64', 'SysWriteUInt64'));
end;

initialization
  RegisterTest(TParamNarrowTests);

end.
