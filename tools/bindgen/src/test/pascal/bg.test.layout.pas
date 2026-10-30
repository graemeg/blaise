{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit bg.test.layout;

{ Tests for Bindgen.Layout — C size/alignment calculator (x86_64 SysV).

  The calculator resolves typedef chains and record layouts through the
  TCModel, so unions can be emitted with their exact byte size — a
  union used by value (XEvent!) with a wrong size corrupts the caller's
  stack. }

interface

uses
  blaise.testing,
  Bindgen.Model, Bindgen.Layout;

type
  TLayoutTests = class(TTestCase)
  private
    FModel: TCModel;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestSize_Builtins;
    procedure TestSize_Pointer;
    procedure TestSize_FixedArray;
    procedure TestSize_TypedefChain;
    procedure TestSize_Struct_WithPadding;
    procedure TestSize_Union_MaxMember;
    procedure TestSize_Unknown_ReturnsFalse;
    procedure TestSize_BitfieldStruct_MatchesC;
  end;

implementation

procedure TLayoutTests.SetUp;
var
  R: TCRecord;
begin
  FModel := TCModel.Create();
  FModel.AddTypedef(TCTypedef.Create('XID', 'unsigned long'));
  FModel.AddTypedef(TCTypedef.Create('Window', 'XID'));

  { struct of int x, unsigned long serial, const char *name — C gives
    4 (+4 pad) + 8 + 8 = 24, align 8. }
  R := TCRecord.Create('XPoint');
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('x', 'int'));
  R.Fields.Add(TCField.Create('serial', 'unsigned long'));
  R.Fields.Add(TCField.Create('name', 'const char *'));
  FModel.AddRecord(R);

  { union of int type, long pad[24] — 192 bytes, align 8. }
  R := TCRecord.Create('_XSampleEvent');
  R.IsComplete := True;
  R.IsUnion := True;
  R.Fields.Add(TCField.Create('type', 'int'));
  R.Fields.Add(TCField.Create('pad', 'long[24]'));
  FModel.AddRecord(R);
end;

procedure TLayoutTests.TearDown;
begin
  FModel := nil;
end;

procedure TLayoutTests.TestSize_Builtins;
var
  Size, Align: Int;
begin
  AssertTrue(CTypeSizeAlign(FModel, 'int', Size, Align));
  AssertEquals('int size', 4, Size);
  AssertEquals('int align', 4, Align);
  AssertTrue(CTypeSizeAlign(FModel, 'char', Size, Align));
  AssertEquals('char size', 1, Size);
  AssertTrue(CTypeSizeAlign(FModel, 'unsigned long', Size, Align));
  AssertEquals('ulong size', 8, Size);
  AssertTrue(CTypeSizeAlign(FModel, 'double', Size, Align));
  AssertEquals('double size', 8, Size);
end;

procedure TLayoutTests.TestSize_Pointer;
var
  Size, Align: Int;
begin
  AssertTrue(CTypeSizeAlign(FModel, 'const char *', Size, Align));
  AssertEquals(8, Size);
  AssertTrue(CTypeSizeAlign(FModel, 'int (*)(int, int)', Size, Align));
  AssertEquals(8, Size);
end;

procedure TLayoutTests.TestSize_FixedArray;
var
  Size, Align: Int;
begin
  AssertTrue(CTypeSizeAlign(FModel, 'long[24]', Size, Align));
  AssertEquals('array size', 192, Size);
  AssertEquals('array align = elem align', 8, Align);
  AssertTrue(CTypeSizeAlign(FModel, 'short[10]', Size, Align));
  AssertEquals(20, Size);
end;

procedure TLayoutTests.TestSize_TypedefChain;
var
  Size, Align: Int;
begin
  AssertTrue(CTypeSizeAlign(FModel, 'Window', Size, Align));
  AssertEquals('Window → XID → unsigned long', 8, Size);
end;

procedure TLayoutTests.TestSize_Struct_WithPadding;
var
  Size, Align: Int;
begin
  AssertTrue(CTypeSizeAlign(FModel, 'struct XPoint', Size, Align));
  AssertEquals('padded struct size', 24, Size);
  AssertEquals('struct align', 8, Align);
end;

procedure TLayoutTests.TestSize_Union_MaxMember;
var
  Size, Align: Int;
begin
  AssertTrue(CTypeSizeAlign(FModel, 'union _XSampleEvent', Size, Align));
  AssertEquals('union size = max member', 192, Size);
  AssertEquals('union align', 8, Align);
end;

procedure TLayoutTests.TestSize_Unknown_ReturnsFalse;
var
  Size, Align: Int;
begin
  AssertTrue(not CTypeSizeAlign(FModel, 'struct never_declared', Size, Align));
end;

procedure TLayoutTests.TestSize_BitfieldStruct_MatchesC;
var
  R: TCRecord;
  Size, Align: Int;
begin
  { After loader collapsing, the bitfield struct is uint + int + ushort:
    4 + 4 + 2 (+2 pad) = 12, align 4 — matches C sizeof. }
  R := TCRecord.Create('Flags');
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('__bits0', 'unsigned int'));
  R.Fields.Add(TCField.Create('plain', 'int'));
  R.Fields.Add(TCField.Create('__bits1', 'unsigned short'));
  FModel.AddRecord(R);
  AssertTrue(CTypeSizeAlign(FModel, 'struct Flags', Size, Align));
  AssertEquals('size', 12, Size);
  AssertEquals('align', 4, Align);
end;

initialization
  RegisterTest(TLayoutTests);

end.
