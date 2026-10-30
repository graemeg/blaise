{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.containerwriter;

{ The object writers' fixed-width field writers.  A field takes any value its
  width can hold, read as signed or unsigned (-1 and $FFFFFFFF both fill a
  32-bit field); a value too wide for the field is an error, not a silent
  truncation of a count or an offset that has outgrown its field. }

interface

uses
  SysUtils, blaise.testing, blaise.container.writer, blaise.elfwriter,
  blaise.machowriter;

type
  TFieldWidthTests = class(TTestCase)
  published
    procedure TestByteBuf_FieldsTakeSignedAndUnsigned;
    procedure TestByteBuf_OverflowRaises;
    procedure TestElfWriter_OverflowRaises;
    procedure TestMachOWriter_OverflowRaises;
  end;

implementation

type
  TBufOp = (boByte, boU16, boU32);

{ True when pushing AVal as a field of AOp raises. }
function BufRaises(AOp: TBufOp; AVal: Int): Boolean;
var
  B: TByteBuf;
begin
  Result := False;
  B := TByteBuf.Create();
  try
    try
      case AOp of
        boByte: B.PushByte(AVal);
        boU16:  B.PushU16(AVal);
        boU32:  B.PushU32(AVal);
      end;
    except
      on E: Exception do Result := True;
    end;
  finally
    B.Free();
  end;
end;

procedure TFieldWidthTests.TestByteBuf_FieldsTakeSignedAndUnsigned;
var
  B: TByteBuf;
begin
  B := TByteBuf.Create();
  try
    B.PushByte(255);
    B.PushByte(-128);
    B.PushU16($FFFF);
    B.PushU16(-1);
    B.PushU32($FFFFFFFF);
    B.PushU32(-1);
    AssertEquals('bytes written', 1 + 1 + 2 + 2 + 4 + 4, B.Count);
    AssertEquals('-128 as a byte', $80, B.Bytes[1]);
    AssertEquals('$FFFFFFFF low byte', $FF, B.Bytes[6]);
    AssertEquals('-1 high byte', $FF, B.Bytes[13]);
  finally
    B.Free();
  end;
end;

procedure TFieldWidthTests.TestByteBuf_OverflowRaises;
begin
  AssertTrue('256 in a byte', BufRaises(boByte, 256));
  AssertTrue('-129 in a byte', BufRaises(boByte, -129));
  AssertTrue('$10000 in 16 bits', BufRaises(boU16, $10000));
  AssertTrue('-32769 in 16 bits', BufRaises(boU16, -32769));
  AssertTrue('$100000000 in 32 bits', BufRaises(boU32, $100000000));
  AssertTrue('-2^31-1 in 32 bits', BufRaises(boU32, -2147483649));
end;

procedure TFieldWidthTests.TestElfWriter_OverflowRaises;
var
  W:      TElfObjectWriter;
  Raised: Boolean;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendDWord(cskText, $FFFFFFFF);
    W.AppendWord(cskText, -1);
    Raised := False;
    try
      W.AppendDWord(cskText, $100000000);
    except
      on E: Exception do Raised := True;
    end;
    AssertTrue('AppendDWord of 2^32', Raised);
    Raised := False;
    try
      W.Patch32(cskText, 0, $100000000);
    except
      on E: Exception do Raised := True;
    end;
    AssertTrue('Patch32 of 2^32', Raised);
  finally
    W.Free();
  end;
end;

procedure TFieldWidthTests.TestMachOWriter_OverflowRaises;
var
  W:      TMachOObjectWriter;
  Raised: Boolean;
begin
  W := TMachOObjectWriter.Create();
  try
    W.AppendDWord(cskText, $D503201F);
    Raised := False;
    try
      W.AppendWord(cskText, 70000);
    except
      on E: Exception do Raised := True;
    end;
    AssertTrue('AppendWord of 70000', Raised);
    Raised := False;
    try
      W.AppendByte(cskText, 300);
    except
      on E: Exception do Raised := True;
    end;
    AssertTrue('AppendByte of 300', Raised);
  finally
    W.Free();
  end;
end;

initialization
  RegisterTest(TFieldWidthTests);

end.
