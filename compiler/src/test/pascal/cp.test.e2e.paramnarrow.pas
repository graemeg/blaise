{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.paramnarrow;

{ E2E tests: a by-value parameter narrower than 64 bits holds a value of
  its own type, whatever the caller passed.

  arm64 keeps every integer local in an 8-byte slot and reads it back at
  full width, so the slot must hold the value already extended from the
  parameter's own width.  The callee stored the incoming register as it
  arrived: an Int64 argument passed to an Integer parameter kept all 64
  bits (BUG-20261027-int64-arg-to-integer-param-not-narrowed), and a
  negative narrow argument passed on the stack (the ninth integer argument
  onwards) arrived zero-extended, so -1 printed as 4294967295.

  The assignment I := L always truncated; these tests hold every parameter
  route to the same result.  Found alongside: arm64 WriteLn of a UInt32
  above High(Int32) printed it as a negative number. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EParamNarrowTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { an Int64 argument to each narrow kind, passed in a register }
    procedure TestRun_Int64Arg_RegisterParam_EveryKind;
    { the same through the stack: the ninth argument onwards }
    procedure TestRun_Int64Arg_StackParam_EveryKind;
    { negative narrow arguments of their own type, through the stack }
    procedure TestRun_NegativeNarrowArg_StackParam;
    { a method, a procedural variable, and the parameter read back as Result }
    procedure TestRun_Int64Arg_MethodProcVarAndResult;
    { WriteLn of a UInt32 above High(Int32) prints it unsigned (arm64
      printed it negative) }
    procedure TestRun_WriteLn_UInt32_AboveHighInt32;
  end;

implementation

const
  LE = #10;

procedure TE2EParamNarrowTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-paramnarrow');
end;

procedure TE2EParamNarrowTests.TestRun_Int64Arg_RegisterParam_EveryKind;
const
  Src = '''
    program P;
    procedure PI(X: Int32); begin WriteLn('Integer ', X) end;
    procedure PU(X: UInt32); begin WriteLn('UInt32 ', X) end;
    procedure PS(X: Int16); begin WriteLn('SmallInt ', X) end;
    procedure PW(X: UInt16); begin WriteLn('Word ', X) end;
    procedure PB(X: Byte); begin WriteLn('Byte ', X) end;
    procedure P8(X: Int8); begin WriteLn('Int8 ', X) end;
    var L: Int64;
    begin
      L := 5000131327;
      PI(L); PU(L); PS(L); PW(L); PB(L); P8(L);
      L := -5000000000;
      PI(L); PU(L); PS(L); PW(L); PB(L); P8(L)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Integer 705164031' + LE +
    'UInt32 705164031' + LE +
    'SmallInt -3329' + LE +
    'Word 62207' + LE +
    'Byte 255' + LE +
    'Int8 -1' + LE +
    'Integer -705032704' + LE +
    'UInt32 3589934592' + LE +
    'SmallInt 3584' + LE +
    'Word 3584' + LE +
    'Byte 0' + LE +
    'Int8 0' + LE, 0);
end;

procedure TE2EParamNarrowTests.TestRun_Int64Arg_StackParam_EveryKind;
const
  Src = '''
    program P;
    procedure Q(A, B, C, D, E, F, G, H: Int64;
                XI: Int32; XU: UInt32; XS: Int16; XW: UInt16;
                XB: Byte; X8: Int8);
    begin
      WriteLn(XI, ' ', XU, ' ', XS, ' ', XW, ' ', XB, ' ', X8)
    end;
    var L: Int64;
    begin
      L := 5000131327;
      Q(0, 0, 0, 0, 0, 0, 0, 0, L, L, L, L, L, L);
      L := -5000000000;
      Q(0, 0, 0, 0, 0, 0, 0, 0, L, L, L, L, L, L)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '705164031 705164031 -3329 62207 255 -1' + LE +
    '-705032704 3589934592 3584 3584 0 0' + LE, 0);
end;

procedure TE2EParamNarrowTests.TestRun_NegativeNarrowArg_StackParam;
const
  Src = '''
    program P;
    procedure Q(A, B, C, D, E, F, G, H: Int64;
                XI: Int32; XS: Int16; X8: Int8);
    begin
      WriteLn(XI, ' ', XS, ' ', X8);
      WriteLn(XI < 0, ' ', XS < 0, ' ', X8 < 0)
    end;
    var I: Int32; S: Int16; T: Int8;
    begin
      I := Low(Int32); S := Low(Int16); T := Low(Int8);
      Q(0, 0, 0, 0, 0, 0, 0, 0, I, S, T);
      Q(0, 0, 0, 0, 0, 0, 0, 0, -1, -2, -3)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '-2147483648 -32768 -128' + LE +
    'True True True' + LE +
    '-1 -2 -3' + LE +
    'True True True' + LE, 0);
end;

procedure TE2EParamNarrowTests.TestRun_Int64Arg_MethodProcVarAndResult;
const
  Src = '''
    program P;
    type
      TProcI = procedure(X: Int32);
      TObj = class
        procedure M(X: Int32; Y: Byte);
      end;
    procedure TObj.M(X: Int32; Y: Byte);
    begin
      WriteLn('method ', X, ' ', Y)
    end;
    procedure ByVar(X: Int32);
    begin
      WriteLn('procvar ', X)
    end;
    function Widen(X: Int32): Int64;
    begin
      Result := X
    end;
    var
      L: Int64;
      O: TObj;
      PV: TProcI;
    begin
      L := 5000131327;
      O := TObj.Create();
      O.M(L, L);
      PV := @ByVar;
      PV(L);
      WriteLn('result ', Widen(L), ' ', Widen(L) + 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'method 705164031 255' + LE +
    'procvar 705164031' + LE +
    'result 705164031 705164032' + LE, 0);
end;

procedure TE2EParamNarrowTests.TestRun_WriteLn_UInt32_AboveHighInt32;
const
  Src = '''
    program P;
    var U: UInt32;
    begin
      U := High(UInt32);
      WriteLn(U);
      U := 2147483648;
      WriteLn(U, ' ', U - 1);
      Write(U);
      WriteLn()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '4294967295' + LE + '2147483648 2147483647' + LE + '2147483648' + LE, 0);
end;

initialization
  RegisterTest(TE2EParamNarrowTests);
end.
