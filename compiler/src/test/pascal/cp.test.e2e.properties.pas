{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.properties;

{ End-to-end tests for properties and class-field access — compile + run on
  BOTH backends.  Grew out of the test-hardening sweep; the property tests
  were IR/semantic-only.  Also covers static-array FIELD access from inside a
  method (FD[i] via implicit Self), which a QBE codegen bug got wrong. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EPropertyTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_FieldBackedReadWrite;
    procedure TestRun_GetterSetter;
    procedure TestRun_ReadOnlyComputed;
    procedure TestRun_StringProperty;
    procedure TestRun_DefaultValueIsZero;
    procedure TestRun_InheritedProperty;
    procedure TestRun_IndexedProperty;
    { leg 18: a STRING-indexed property (key is a string, not an integer).  The
      key is passed borrowed in one register, exactly like an integer index. }
    procedure TestRun_StringIndexedProperty;
    procedure TestRun_RecordIndexedProperty;
    procedure TestRun_RecordDefaultIndexedProperty;
    { Default array property: Obj[I] sugar (read + write), string element, and
      inheritance of the default property from a base class. }
    procedure TestRun_DefaultProperty_ReadWrite;
    procedure TestRun_DefaultProperty_StringElement;
    procedure TestRun_DefaultProperty_Inherited;
    { Default array property read through a property-read result:
      Obj.Prop[I] where Prop returns a class carrying a default property. }
    procedure TestRun_DefaultProperty_ViaFieldBackedProperty;
    procedure TestRun_DefaultProperty_ViaMethodBackedProperty;
    { Write through a default array property on a member result:
      Obj.Field[I] := V and Obj.Prop[I] := V. }
    procedure TestRun_DefaultProperty_WriteThroughField;
    procedure TestRun_DefaultProperty_WriteThroughProperty;
    { Implicit-Self write/read: Field[I] := V / Field[I] inside a method, where
      Field is a class with a default array property. }
    procedure TestRun_DefaultProperty_WriteThroughImplicitSelf;
    { Static-array field accessed from inside a method (implicit Self). }
    procedure TestRun_StaticArrayField_ReadInMethod;
    procedure TestRun_StaticArrayField_WriteInMethod;
    procedure TestRun_StaticArrayField_SumInMethod;
    procedure TestRun_StaticArrayOfRecordField;
  end;

implementation

const
  LE = #10;

procedure TE2EPropertyTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-properties');
end;

const
  SrcReadWrite = '''
    program Prg;
    type TC = class FX: Integer; property X: Integer read FX write FX; end;
    var c: TC;
    begin c := TC.Create(); c.X := 17; WriteLn(c.X); c.Free() end.
    ''';

  SrcGetterSetter = '''
    program Prg;
    type TC = class
      FX: Integer;
      function GetX: Integer; begin Result := FX * 2 end;
      procedure SetX(V: Integer); begin FX := V + 1 end;
      property X: Integer read GetX write SetX;
    end;
    var c: TC;
    begin c := TC.Create(); c.X := 10; WriteLn(c.X); c.Free() end.
    ''';

  SrcReadOnly = '''
    program Prg;
    type TC = class FW, FH: Integer; function GetArea: Integer; begin Result := FW * FH end; property Area: Integer read GetArea; end;
    var c: TC;
    begin c := TC.Create(); c.FW := 4; c.FH := 5; WriteLn(c.Area); c.Free() end.
    ''';

  SrcStringProp = '''
    program Prg;
    type TC = class FName: string; property Name: string read FName write FName; end;
    var c: TC;
    begin c := TC.Create(); c.Name := 'hello'; WriteLn(c.Name); c.Free() end.
    ''';

  SrcDefaultZero = '''
    program Prg;
    type TC = class FX: Integer; property X: Integer read FX write FX; end;
    var c: TC;
    begin c := TC.Create(); WriteLn(c.X); c.Free() end.
    ''';

  SrcInherited = '''
    program Prg;
    type TBase = class FX: Integer; property X: Integer read FX write FX; end;
      TDer = class(TBase) end;
    var d: TDer;
    begin d := TDer.Create(); d.X := 55; WriteLn(d.X); d.Free() end.
    ''';

  SrcIndexed = '''
    program Prg;
    type TC = class
      FData: array[0..9] of Integer;
      function GetItem(I: Integer): Integer; begin Result := FData[I] end;
      procedure SetItem(I, V: Integer); begin FData[I] := V end;
      property Items[I: Integer]: Integer read GetItem write SetItem;
    end;
    var c: TC;
    begin c := TC.Create(); c.Items[3] := 99; WriteLn(c.Items[3]); c.Free() end.
    ''';

  SrcStringIndexed = '''
    program Prg;
    type TC = class
      FVal: Integer;
      function GetItem(const Key: string): Integer; begin Result := FVal end;
      procedure SetItem(const Key: string; V: Integer); begin FVal := V end;
      property Items[Key: string]: Integer read GetItem write SetItem;
    end;
    var c: TC;
    begin c := TC.Create(); c.Items['k'] := 88; WriteLn(c.Items['k']); c.Free() end.
    ''';

  { A RECORD value written through an indexed property setter must survive the
    round-trip on BOTH backends.  The QBE backend used to type the value arg
    with QbeTypeOf (a bare `l` pointer) instead of QbeParamTypeOf (the
    `:_ffi_<Name>` aggregate ABI), so the setter received the fields
    scattered from an un-registered struct and read garbage
    (BUG-20260720-x86-record-indexed-prop-value — filed against x86-64 but the
    actual defect was a QBE miscompile). }
  SrcRecordIndexed = '''
    program Prg;
    type
      TRec = record A: Integer; S: string; end;
      TC = class
        FA: Integer; FS: string;
        procedure SetItem(K: Integer; const R: TRec); begin FA := R.A + K; FS := R.S end;
        property Items[K: Integer]: TRec write SetItem;
      end;
    var c: TC; r: TRec;
    begin
      c := TC.Create(); r.A := 40; r.S := 'ok';
      c.Items[2] := r;
      WriteLn(c.FA, ' ', c.FS);
      c.Free()
    end.
    ''';

  { Same defect via a default array property (a distinct write site). }
  SrcRecordDefaultIndexed = '''
    program Prg;
    type
      TRec = record A: Integer; S: string; end;
      TC = class
        FA: Integer; FS: string;
        procedure SetItem(K: Integer; const R: TRec); begin FA := R.A + K; FS := R.S end;
        property Items[K: Integer]: TRec write SetItem; default;
      end;
    var c: TC; r: TRec;
    begin
      c := TC.Create(); r.A := 40; r.S := 'yo';
      c[2] := r;
      WriteLn(c.FA, ' ', c.FS);
      c.Free()
    end.
    ''';

  SrcArrFieldRead = '''
    program Prg;
    type TC = class FD: array[0..4] of Integer; function At(i: Integer): Integer; begin Result := FD[i] end; end;
    var c: TC;
    begin c := TC.Create(); c.FD[2] := 88; WriteLn(c.At(2)); c.Free() end.
    ''';

  SrcArrFieldWrite = '''
    program Prg;
    type TC = class
      FD: array[0..4] of Integer;
      procedure Init; var i: Integer; begin for i := 0 to 4 do FD[i] := i * 10 end;
      function Get(i: Integer): Integer; begin Result := FD[i] end;
    end;
    var c: TC;
    begin c := TC.Create(); c.Init(); WriteLn(c.Get(3)); c.Free() end.
    ''';

  SrcArrFieldSum = '''
    program Prg;
    type TC = class
      FD: array[0..9] of Integer;
      function Sum: Integer; var i: Integer; begin Result := 0; for i := 0 to 9 do Result := Result + FD[i] end;
    end;
    var c: TC; k: Integer;
    begin c := TC.Create(); for k := 0 to 9 do c.FD[k] := k; WriteLn(c.Sum()); c.Free() end.
    ''';

  SrcArrOfRecord = '''
    program Prg;
    type TP = record X: Integer; end;
      TC = class
        FD: array[0..2] of TP;
        function GetX(i: Integer): Integer; begin Result := FD[i].X end;
        procedure SetX(i, v: Integer); begin FD[i].X := v end;
      end;
    var c: TC;
    begin c := TC.Create(); c.SetX(1, 77); WriteLn(c.GetX(1)); c.Free() end.
    ''';

procedure TE2EPropertyTests.TestRun_FieldBackedReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcReadWrite, '17' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_GetterSetter;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGetterSetter, '22' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_ReadOnlyComputed;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcReadOnly, '20' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_StringProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStringProp, 'hello' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_DefaultValueIsZero;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultZero, '0' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_InheritedProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInherited, '55' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_IndexedProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIndexed, '99' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_StringIndexedProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStringIndexed, '88' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_RecordIndexedProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordIndexed, '42 ok' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_RecordDefaultIndexedProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordDefaultIndexed, '42 yo' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_StaticArrayField_ReadInMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArrFieldRead, '88' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_StaticArrayField_WriteInMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArrFieldWrite, '30' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_StaticArrayField_SumInMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArrFieldSum, '45' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_StaticArrayOfRecordField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArrOfRecord, '77' + LE, 0);
end;

const
  SrcDefaultRW = '''
    program P;
    type
      TVec = class
        FData: array[0..4] of Integer;
        function Get(i: Integer): Integer; begin Result := FData[i] end;
        procedure Put(i: Integer; v: Integer); begin FData[i] := v end;
        property Items[i: Integer]: Integer read Get write Put; default;
      end;
    var v: TVec;
    begin
      v := TVec.Create;
      v[0] := 10; v[1] := 20;
      WriteLn(v[0] + v[1]);
      v := nil
    end.
    ''';

  SrcDefaultStr = '''
    program P;
    type
      TBag = class
        FData: array[0..2] of string;
        function Get(i: Integer): string; begin Result := FData[i] end;
        procedure Put(i: Integer; v: string); begin FData[i] := v end;
        property Items[i: Integer]: string read Get write Put; default;
      end;
    var b: TBag;
    begin
      b := TBag.Create;
      b[0] := 'foo'; b[1] := 'bar';
      WriteLn(b[0] + b[1]);
      b := nil
    end.
    ''';

  SrcDefaultInherited = '''
    program P;
    type
      TBase = class
        FData: array[0..2] of Integer;
        function Get(i: Integer): Integer; begin Result := FData[i] end;
        procedure Put(i: Integer; v: Integer); begin FData[i] := v end;
        property Items[i: Integer]: Integer read Get write Put; default;
      end;
      TDerived = class(TBase) end;
    var d: TDerived;
    begin
      d := TDerived.Create;
      d[0] := 5; d[1] := 7;
      WriteLn(d[0] + d[1]);
      d := nil
    end.
    ''';

procedure TE2EPropertyTests.TestRun_DefaultProperty_ReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultRW, '30' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_DefaultProperty_StringElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultStr, 'foobar' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_DefaultProperty_Inherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultInherited, '12' + LE, 0);
end;

const
  { Obj.Prop[I] where Prop is a field-backed property returning a class with a
    default array property — reads through the property result. }
  SrcDefaultViaFieldProp = '''
    program P;
    type
      TVec = class
        FData: array[0..4] of Integer;
        function Get(i: Integer): Integer; begin Result := FData[i] end;
        procedure Put(i: Integer; v: Integer); begin FData[i] := v end;
        property Items[i: Integer]: Integer read Get write Put; default;
      end;
      TOwner = class
        FVec: TVec;
        constructor Create;
        property Vec: TVec read FVec;
      end;
    constructor TOwner.Create;
    begin
      inherited Create();
      FVec := TVec.Create;
      FVec.Put(0, 3); FVec.Put(1, 4);
    end;
    var o: TOwner;
    begin
      o := TOwner.Create;
      WriteLn(o.Vec[0] + o.Vec[1]);
      o := nil
    end.
    ''';

  { Same, but Prop is a method-backed (getter) property. }
  SrcDefaultViaMethodProp = '''
    program P;
    type
      TVec = class
        FData: array[0..4] of Integer;
        function Get(i: Integer): Integer; begin Result := FData[i] end;
        procedure Put(i: Integer; v: Integer); begin FData[i] := v end;
        property Items[i: Integer]: Integer read Get write Put; default;
      end;
      TOwner = class
        FVec: TVec;
        constructor Create;
        function GetVec: TVec; begin Result := FVec end;
        property Vec: TVec read GetVec;
      end;
    constructor TOwner.Create;
    begin
      inherited Create();
      FVec := TVec.Create;
      FVec.Put(0, 5); FVec.Put(1, 4);
    end;
    var o: TOwner;
    begin
      o := TOwner.Create;
      WriteLn(o.Vec[0] + o.Vec[1]);
      o := nil
    end.
    ''';

procedure TE2EPropertyTests.TestRun_DefaultProperty_ViaFieldBackedProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultViaFieldProp, '7' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_DefaultProperty_ViaMethodBackedProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultViaMethodProp, '9' + LE, 0);
end;

const
  { Write through a class field's default property: Obj.Field[I] := V. }
  SrcDefaultWriteField = '''
    program P;
    type
      TVec = class
        FData: array[0..4] of Integer;
        function Get(i: Integer): Integer; begin Result := FData[i] end;
        procedure Put(i: Integer; v: Integer); begin FData[i] := v end;
        property Items[i: Integer]: Integer read Get write Put; default;
      end;
      TOwner = class
        FVec: TVec;
        constructor Create;
        property Vec: TVec read FVec;
      end;
    constructor TOwner.Create; begin inherited Create(); FVec := TVec.Create end;
    var o: TOwner;
    begin
      o := TOwner.Create;
      o.FVec[0] := 3; o.FVec[1] := 4;
      WriteLn(o.Vec[0] + o.Vec[1]);
      o := nil
    end.
    ''';

  { Write through a read-only property's result default property:
    Obj.Prop[I] := V. }
  SrcDefaultWriteProp = '''
    program P;
    type
      TVec = class
        FData: array[0..4] of Integer;
        function Get(i: Integer): Integer; begin Result := FData[i] end;
        procedure Put(i: Integer; v: Integer); begin FData[i] := v end;
        property Items[i: Integer]: Integer read Get write Put; default;
      end;
      TOwner = class
        FVec: TVec;
        constructor Create;
        property Vec: TVec read FVec;
      end;
    constructor TOwner.Create; begin inherited Create(); FVec := TVec.Create end;
    var o: TOwner;
    begin
      o := TOwner.Create;
      o.Vec[0] := 5; o.Vec[1] := 4;
      WriteLn(o.Vec[0] + o.Vec[1]);
      o := nil
    end.
    ''';

procedure TE2EPropertyTests.TestRun_DefaultProperty_WriteThroughField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultWriteField, '7' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_DefaultProperty_WriteThroughProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultWriteProp, '9' + LE, 0);
end;

const
  { Implicit Self.Field[I] := V and Field[I] read, inside methods. }
  SrcDefaultWriteImplicitSelf = '''
    program P;
    type
      TVec = class
        FData: array[0..4] of Integer;
        function Get(i: Integer): Integer; begin Result := FData[i] end;
        procedure Put(i: Integer; v: Integer); begin FData[i] := v end;
        property Items[i: Integer]: Integer read Get write Put; default;
      end;
      TOwner = class
        FVec: TVec;
        constructor Create;
        procedure Fill;
        function Sum: Integer;
      end;
    constructor TOwner.Create; begin inherited Create(); FVec := TVec.Create end;
    procedure TOwner.Fill; begin FVec[0] := 3; FVec[1] := 4; end;
    function TOwner.Sum: Integer; begin Result := FVec[0] + FVec[1]; end;
    var o: TOwner;
    begin
      o := TOwner.Create;
      o.Fill();
      WriteLn(o.Sum());
      o := nil
    end.
    ''';

procedure TE2EPropertyTests.TestRun_DefaultProperty_WriteThroughImplicitSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultWriteImplicitSelf, '7' + LE, 0);
end;

initialization
  RegisterTest(TE2EPropertyTests);

end.
