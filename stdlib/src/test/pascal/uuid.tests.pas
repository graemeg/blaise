{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}


unit Uuid.Tests;

interface

uses
  blaise.testing, Uuid;

type
  TUuidTests = class(TTestCase)
  published

    { TUuid }
    procedure TestUuidFormat;
    procedure TestUuidVersionAndVariant;
    procedure TestUuidRawBytes;
    procedure TestUuidUnique;
    procedure TestUuidParseKnownValue;
    procedure TestUuidParseCaseInsensitive;
    procedure TestUuidParseRoundTrip;
    procedure TestUuidTryParseRejectsBadLength;
    procedure TestUuidTryParseRejectsBadHyphen;
    procedure TestUuidTryParseRejectsNonHex;
    procedure TestUuidParseRaisesOnInvalid;
    procedure TestUuidFromBytesRoundTrip;
    procedure TestUuidFromBytesRejectsBadLength;
    procedure TestUuidEmpty;
    procedure TestUuidIsEmptyDefault;
    procedure TestUuidCompareToAndEquals;
    procedure TestUuidGetHashCodeConsistent;
    procedure TestUuidVersionMethod;
  end;

implementation

function IsHexLower(B: Byte): Boolean;
begin
  Result := ((B >= 48) and (B <= 57)) or ((B >= 97) and (B <= 102));
end;

{ ------------------------------------------------------------------ }
{ ------------------------------------------------------------------ }

{ ------------------------------------------------------------------ }
{ TUuid                                                                }
{ ------------------------------------------------------------------ }

procedure TUuidTests.TestUuidFormat;
var
  U: TUuid;
  S: string;
  I: Int;
  Ch: Byte;
begin
  U := TUuid.RandomUuid();
  S := U.ToString();
  AssertEquals('length', 36, Int32(Length(S)));
  for I := 0 to 35 do
  begin
    Ch := Byte(S[I]);
    if (I = 8) or (I = 13) or (I = 18) or (I = 23) then
      AssertEquals('hyphen at ' + IntToStr(I), 45, Int32(Ch))
    else
      AssertTrue('hex at ' + IntToStr(I), IsHexLower(Ch));
  end;
end;

procedure TUuidTests.TestUuidVersionAndVariant;
var
  U: TUuid;
  S: string;
begin
  U := TUuid.RandomUuid();
  S := U.ToString();
  AssertEquals('version 4', 52, Int32(Byte(S[14])));
  AssertTrue('variant 8/9/a/b',
    (Byte(S[19]) = 56) or (Byte(S[19]) = 57) or
    (Byte(S[19]) = 97) or (Byte(S[19]) = 98));
  AssertEquals('Version() = 4', 4, U.Version());
end;

procedure TUuidTests.TestUuidRawBytes;
var
  U: TUuid;
  R: string;
begin
  U := TUuid.RandomUuid();
  R := U.ToBytes();
  AssertEquals('16 bytes', 16, Int32(Length(R)));
  AssertEquals('raw version', $40, Int32(Byte(R[6]) and $F0));
  AssertEquals('raw variant', $80, Int32(Byte(R[8]) and $C0));
end;

procedure TUuidTests.TestUuidUnique;
var
  A, B: TUuid;
begin
  A := TUuid.RandomUuid();
  B := TUuid.RandomUuid();
  AssertTrue('two random uuids differ', not A.Equals(B));
end;

procedure TUuidTests.TestUuidParseKnownValue;
const
  KNOWN = '3f2504e0-4f89-41d3-9a0c-0305e82c3301';
var
  U: TUuid;
begin
  U := TUuid.Parse(KNOWN);
  AssertEquals('round-trips to the same canonical text', KNOWN, U.ToString());
  AssertEquals('version nibble', 4, U.Version());
end;

procedure TUuidTests.TestUuidParseCaseInsensitive;
const
  UPPER = '3F2504E0-4F89-41D3-9A0C-0305E82C3301';
  LOWER = '3f2504e0-4f89-41d3-9a0c-0305e82c3301';
var
  U: TUuid;
begin
  U := TUuid.Parse(UPPER);
  AssertEquals('canonical output is always lowercase', LOWER, U.ToString());
end;

procedure TUuidTests.TestUuidParseRoundTrip;
var
  Original, Reparsed: TUuid;
begin
  Original := TUuid.RandomUuid();
  Reparsed := TUuid.Parse(Original.ToString());
  AssertTrue('parse(x.ToString) equals x', Original.Equals(Reparsed));
end;

procedure TUuidTests.TestUuidTryParseRejectsBadLength;
var
  U: TUuid;
begin
  AssertFalse('too short', TUuid.TryParse('abc', U));
  AssertFalse('too long',
    TUuid.TryParse('3f2504e0-4f89-41d3-9a0c-0305e82c33011', U));
end;

procedure TUuidTests.TestUuidTryParseRejectsBadHyphen;
var
  U: TUuid;
begin
  { a hex digit where a hyphen is required (position 8) }
  AssertFalse('missing hyphen',
    TUuid.TryParse('3f2504e004f89-41d3-9a0c-0305e82c3301', U));
end;

procedure TUuidTests.TestUuidTryParseRejectsNonHex;
var
  U: TUuid;
begin
  AssertFalse('non-hex character',
    TUuid.TryParse('zzzzzzzz-4f89-41d3-9a0c-0305e82c3301', U));
end;

procedure TUuidTests.TestUuidParseRaisesOnInvalid;
begin
  AssertRaises('EUuidParse', procedure begin TUuid.Parse('not-a-uuid') end);
end;

procedure TUuidTests.TestUuidFromBytesRoundTrip;
var
  Original, Rebuilt: TUuid;
begin
  Original := TUuid.RandomUuid();
  Rebuilt := TUuid.FromBytes(Original.ToBytes());
  AssertTrue('FromBytes(x.ToBytes) equals x', Original.Equals(Rebuilt));
end;

procedure TUuidTests.TestUuidFromBytesRejectsBadLength;
begin
  AssertRaises('EUuidParse', procedure begin TUuid.FromBytes('too short') end);
end;

procedure TUuidTests.TestUuidEmpty;
var
  U: TUuid;
begin
  U := TUuid.Empty();
  AssertTrue('Empty().IsEmpty', U.IsEmpty());
  AssertEquals('nil UUID text',
    '00000000-0000-0000-0000-000000000000', U.ToString());
  AssertEquals('Version 0 when empty', 0, U.Version());
end;

procedure TUuidTests.TestUuidIsEmptyDefault;
var
  U: TUuid;
begin
  { a never-assigned TUuid is the nil UUID - no separate "unset" state }
  AssertTrue('default TUuid is empty', U.IsEmpty());
end;

procedure TUuidTests.TestUuidCompareToAndEquals;
var
  A, B: TUuid;
begin
  A := TUuid.Parse('3f2504e0-4f89-41d3-9a0c-0305e82c3301');
  B := TUuid.Parse('3f2504e0-4f89-41d3-9a0c-0305e82c3301');
  AssertEquals('equal values compare 0', 0, A.CompareTo(B));
  AssertTrue('equal values Equals', A.Equals(B));

  B := TUuid.Parse('3f2504e0-4f89-41d3-9a0c-0305e82c3302');
  AssertTrue('differing values do not Equals', not A.Equals(B));
  AssertTrue('A < B', A.CompareTo(B) < 0);
  AssertTrue('B > A', B.CompareTo(A) > 0);
end;

procedure TUuidTests.TestUuidGetHashCodeConsistent;
var
  A, B: TUuid;
begin
  A := TUuid.Parse('3f2504e0-4f89-41d3-9a0c-0305e82c3301');
  B := TUuid.Parse('3f2504e0-4f89-41d3-9a0c-0305e82c3301');
  AssertEquals('equal values hash equally', A.GetHashCode(), B.GetHashCode());
end;

procedure TUuidTests.TestUuidVersionMethod;
begin
  AssertEquals('random uuid is version 4', 4, TUuid.RandomUuid().Version());
end;

initialization
  RegisterTest(TUuidTests);

end.
