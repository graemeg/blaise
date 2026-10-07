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
    procedure TestSmallSet_StillUsesRegister;
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
  I: Integer;
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

initialization
  RegisterTest(TJumboSetTests);

end.
