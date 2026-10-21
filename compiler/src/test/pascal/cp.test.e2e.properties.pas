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
    { an element of the dynamic array a property returns is storage shared
      with the field, so SetLength on it resizes the field's element; a
      field-backed property passes to a var parameter }
    procedure TestRun_ElementOfPropertyValueIsResizable;
    { indexed property reads with a Double, Single or record index, through
      a variable, a call result, Self, a field of Self and the default
      property: the getter call passes the index by its ABI class }
    procedure TestRun_FloatAndRecordIndexRead;
    { Inside a method a bare element write through a field-read array property
      (AP[3] := 25, DP[1] := 'd1') writes the backing field; it was rejected as
      "Undeclared variable". }
    procedure TestRun_BareArrayPropertyElementWrite_InMethod;
    { An element write through a non-indexed array-typed property read from a
      field -- qualified, through a chained base and through an implicit-Self
      field -- writes the read field's element, whatever the write specifier (the
      setter is not called). }
    procedure TestRun_ArrayPropertyElementWrite_WritesReadField;
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
    procedure TestRun_OwnedTransientStringPropertyValue;
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
    { A.B.Field[I] — the getter's receiver is the intermediate field, two field
      steps from the base (BUG-20260725-arm64-chained-indexed-prop-base). }
    procedure TestRun_DefaultProperty_ReadThroughChainedBase;
    { Static-array field accessed from inside a method (implicit Self). }
    procedure TestRun_StaticArrayField_ReadInMethod;
    procedure TestRun_StaticArrayField_WriteInMethod;
    procedure TestRun_StaticArrayField_SumInMethod;
    procedure TestRun_StaticArrayOfRecordField;

    { Setter-backed property written through a CHAINED base (A.B.Prop := V) }
    procedure TestRun_ChainedSetterPropertyWrite;
    procedure TestRun_ChainedSetterPropertyWrite_IndexedProp;

    { Obj.Prop[I] / (Obj.Prop)[I] on a NON-indexed string / array property
      (BUG-20261011-prop-value-subscript-dropped): the index was dropped, or
      the whole value delegated as the element. }
    procedure TestRun_PropertyValueSubscript;
    { a static-array getter read as a value and as a subscript base
      (BUG-20261011-staticarray-getter-value) }
    procedure TestRun_StaticArrayGetterProperty;
    { bare property reads inside a method: record / static-array getters,
      P.Y, and a VIRTUAL getter overridden in a descendant
      (BUG-20261011-implicit-self-prop-ident) }
    procedure TestRun_ImplicitSelfPropertyReads;
    { an interface-typed property written through its setter, plain and
      indexed, from a variable, a call result and a class value
      (BUG-20261011-intf-prop-setter) }
    procedure TestRun_InterfacePropertySetter;
    { bare property writes inside a method, field- and method-backed, and a
      member of a class-typed property (BUG-20261011-implicit-self-prop-write) }
    procedure TestRun_ImplicitSelfPropertyWrites;
    { indexed-property forms (P4-7): interface-typed reads through every
      receiver shape, bare P[I] reads and writes in a method, a default
      property on a record's class FIELD, and Double / Single reads }
    procedure TestRun_IndexedPropertyForms;
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

  { An OWNED-TRANSIENT string value (a concat) written through an indexed and a
    non-indexed property setter.  The setter borrows the value; the caller must
    dispose the transient after the call.  Must round-trip and not crash/leak on
    both backends (arm64 leg 36 hardened this; QBE/native must stay correct). }
  SrcOwnedTransientStrProp = '''
    program Prg;
    type
      TC = class
        FItems: array[0..3] of string;
        FCur: string;
        procedure SetItem(K: Integer; const V: string);
        function GetItem(K: Integer): string;
        procedure SetCur(const V: string);
        property Items[K: Integer]: string read GetItem write SetItem;
        property Cur: string write SetCur;
      end;
      procedure TC.SetItem(K: Integer; const V: string); begin FItems[K] := V end;
      function TC.GetItem(K: Integer): string; begin Result := FItems[K] end;
      procedure TC.SetCur(const V: string); begin FCur := V end;
    var c: TC; a, b: string;
    begin
      c := TC.Create();
      a := 'x'; b := 'y';
      c.Items[1] := a + b;
      c.Cur := a + b;
      WriteLn(c.Items[1]);
      WriteLn(c.FCur);
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

procedure TE2EPropertyTests.TestRun_OwnedTransientStringPropertyValue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOwnedTransientStrProp, 'xy' + LE + 'xy' + LE, 0);
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

const
  { t.Mid.Vec[I] — the getter's receiver is Vec, reached by TWO field steps
    from t.  M1/T1 make Mid and Vec share an offset, which is what turned the
    missing second step into a silent wrong-object call rather than a nil deref
    (arm64 ran the getter on t.Mid).  The getter is computed and the property
    read-only, so this isolates the READ path: a chained-base indexed write and
    an implicit-Self indexed array-field write are both still NotYet on arm64.
    Base is FBase so a wrong receiver cannot accidentally produce 14. }
  SrcDefaultReadChainedBase = '''
    program P;
    type
      TVec = class
        FBase: Integer;
        constructor Create;
        function Get(i: Integer): Integer;
        property Items[i: Integer]: Integer read Get; default;
      end;
      TMid = class
        M1: Integer;
        Vec: TVec;
        constructor Create;
      end;
      TTop = class
        T1: Integer;
        Mid: TMid;
        constructor Create;
      end;
    constructor TVec.Create; begin inherited Create(); FBase := 5 end;
    function TVec.Get(i: Integer): Integer; begin Result := FBase + i * 4 end;
    constructor TMid.Create;
    begin inherited Create(); M1 := 111; Vec := TVec.Create() end;
    constructor TTop.Create;
    begin inherited Create(); T1 := 222; Mid := TMid.Create() end;
    var t: TTop;
    begin
      t := TTop.Create();
      WriteLn(t.Mid.Vec[0] + t.Mid.Vec[1]);
      t := nil
    end.
    ''';

procedure TE2EPropertyTests.TestRun_DefaultProperty_ReadThroughChainedBase;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultReadChainedBase, '14' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_ChainedSetterPropertyWrite;
begin
  { A.B.Prop := V where Prop's setter is a METHOD.  The chained-base branch
    of the field-assignment path only handled FIELD-backed properties, so
    this was rejected with "has no field 'Value'" while the matching READ
    compiled — the implicit-Self branch had handled it all along.  Found
    porting tools/blaise-guard, where `Model.Lines.Text := S` hit it. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TInner = class
        FValue: string;
        procedure SetValue(const V: string);
        property Value: string read FValue write SetValue;
      end;
      TOuter = class
        Inner: TInner;
      end;
    procedure TInner.SetValue(const V: string);
    begin
      FValue := '[' + V + ']'
    end;
    var O: TOuter;
    begin
      O := TOuter.Create();
      O.Inner := TInner.Create();
      O.Inner.Value := 'hi';
      WriteLn(O.Inner.Value)
    end.
    ''', '[hi]' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_ChainedSetterPropertyWrite_IndexedProp;
begin
  { The indexed variant of the same shape — the ported branch carries the
    index-expression handling, so an indexed setter through a chained base
    must work too rather than silently dropping the index. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TInner = class
        FA: Integer;
        FB: Integer;
        procedure SetSlot(AIndex: Integer; AValue: Integer);
        function GetSlot(AIndex: Integer): Integer;
        property Slot[AIndex: Integer]: Integer read GetSlot write SetSlot;
      end;
      TOuter = class
        Inner: TInner;
      end;
    procedure TInner.SetSlot(AIndex: Integer; AValue: Integer);
    begin
      if AIndex = 0 then FA := AValue else FB := AValue
    end;
    function TInner.GetSlot(AIndex: Integer): Integer;
    begin
      if AIndex = 0 then Result := FA else Result := FB
    end;
    var O: TOuter;
    begin
      O := TOuter.Create();
      O.Inner := TInner.Create();
      O.Inner.Slot[0] := 11;
      O.Inner.Slot[1] := 22;
      WriteLn(O.Inner.Slot[0] + O.Inner.Slot[1])
    end.
    ''', '33' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_PropertyValueSubscript;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TIntArr = array of Integer;
      TStrArr = array of string;
      THolder = class
        FS: string;
        FArr: TIntArr;
        FSA: TStrArr;
        function GetS: string;
        function GetArr: TIntArr;
        function GetSA: TStrArr;
        property S: string read GetS;
        property SF: string read FS;
        property Arr: TIntArr read GetArr;
        property AF: TIntArr read FArr;
        property SA: TStrArr read GetSA;
      end;
    function THolder.GetS: string; begin Result := FS end;
    function THolder.GetArr: TIntArr; begin Result := FArr end;
    function THolder.GetSA: TStrArr; begin Result := FSA end;
    var H: THolder; X: string;
    begin
      H := THolder.Create();
      H.FS := 'abc';
      SetLength(H.FArr, 2);
      H.FArr[1] := 9;
      SetLength(H.FSA, 2);
      H.FSA[1] := 'x' + IntToStr(5);
      WriteLn(H.S[1], ' ', H.SF[2], ' ', (H.S)[0]);
      WriteLn(H.Arr[1], ' ', H.AF[1], ' ', (H.Arr)[1]);
      X := H.SA[1];
      WriteLn(X, ' ', (H.SA)[1], ' ', H.SA[1])
    end.
    ''', '98 99 97' + LE + '9 9 9' + LE + 'x5 x5 x5' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_StaticArrayGetterProperty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TSA = array[0..2] of Integer;
      TC = class
        FSA: TSA;
        function GetSA: TSA;
        property SA: TSA read GetSA;
        property SF: TSA read FSA;
      end;
    function TC.GetSA: TSA; begin Result := FSA end;
    var O: TC; S: TSA;
    begin
      O := TC.Create();
      O.FSA[0] := 5;
      O.FSA[1] := 6;
      O.FSA[2] := 7;
      S := O.SA;
      WriteLn(S[0], ' ', S[2]);
      WriteLn(O.SA[1], ' ', (O.SA)[2], ' ', O.SF[0])
    end.
    ''', '5 7' + LE + '6 7 5' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_ImplicitSelfPropertyReads;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TPt = record X, Y, Z: Integer; end;
      TSA = array[0..2] of Integer;
      TBase = class
        FP: TPt;
        FSA: TSA;
        function GetP: TPt;
        function GetSA: TSA;
        function GetN: Integer; virtual;
        function GetStr: string; virtual;
        property P: TPt read GetP;
        property SA: TSA read GetSA;
        property N: Integer read GetN;
        property Str: string read GetStr;
        procedure Show;
      end;
      TKid = class(TBase)
        function GetN: Integer; override;
        function GetStr: string; override;
      end;
    function TBase.GetP: TPt; begin Result := FP end;
    function TBase.GetSA: TSA; begin Result := FSA end;
    function TBase.GetN: Integer; begin Result := 1 end;
    function TBase.GetStr: string; begin Result := 'base' end;
    function TKid.GetN: Integer; begin Result := 2 end;
    function TKid.GetStr: string; begin Result := 'kid' end;
    procedure TBase.Show;
    var Q: TPt; A: TSA;
    begin
      Q := P;
      A := SA;
      WriteLn(P.Y, ' ', Q.Z, ' ', A[1], ' ', SA[2]);
      WriteLn(N, ' ', Str)
    end;
    var O: TBase;
    begin
      O := TKid.Create();
      O.FP.Y := 4;
      O.FP.Z := 5;
      O.FSA[1] := 6;
      O.FSA[2] := 7;
      O.Show()
    end.
    ''', '4 5 6 7' + LE + '2 kid' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_InterfacePropertySetter;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        N: Integer;
        function Val: Integer;
      end;
      THolder = class
        FThing: IThing;
        FS0, FS1: IThing;
        procedure SetThing(V: IThing);
        function GetSlot(I: Integer): IThing;
        procedure SetSlot(I: Integer; V: IThing);
        property Thing: IThing read FThing write SetThing;
        property Slot[I: Integer]: IThing read GetSlot write SetSlot;
      end;
    function TThing.Val: Integer; begin Result := N end;
    procedure THolder.SetThing(V: IThing); begin FThing := V end;
    function THolder.GetSlot(I: Integer): IThing;
    begin
      if I = 0 then Result := FS0 else Result := FS1
    end;
    procedure THolder.SetSlot(I: Integer; V: IThing);
    begin
      if I = 0 then FS0 := V else FS1 := V
    end;
    function MakeThing(N: Integer): IThing;
    var T: TThing;
    begin
      T := TThing.Create();
      T.N := N;
      Result := T
    end;
    var H: THolder; T: IThing; C: TThing;
    begin
      H := THolder.Create();
      T := MakeThing(1);
      H.Thing := T;
      WriteLn(H.Thing.Val());
      H.Thing := MakeThing(2);
      WriteLn(H.Thing.Val());
      C := TThing.Create();
      C.N := 3;
      H.Thing := C;
      WriteLn(H.Thing.Val());
      H.Slot[1] := MakeThing(4);
      H.Slot[0] := T;
      WriteLn(H.FS0.Val(), H.FS1.Val())
    end.
    ''', '1' + LE + '2' + LE + '3' + LE + '14' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_ImplicitSelfPropertyWrites;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TInner = class
        FN: Integer;
        procedure SetN(V: Integer);
        property N: Integer read FN write SetN;
      end;
      TC = class
        FM: Integer;
        FK: Integer;
        FIn: TInner;
        procedure SetK(V: Integer); virtual;
        property K: Integer read FK write SetK;
        property M: Integer read FM write FM;
        property Inner: TInner read FIn;
        procedure Go;
      end;
      TKid = class(TC)
        procedure SetK(V: Integer); override;
      end;
    procedure TInner.SetN(V: Integer); begin FN := V * 10 end;
    procedure TC.SetK(V: Integer); begin FK := V end;
    procedure TKid.SetK(V: Integer); begin FK := V + 100 end;
    procedure TC.Go;
    begin
      K := 1;
      M := 2;
      Inner.N := 3;
      WriteLn(FK, ' ', FM, ' ', FIn.FN)
    end;
    var O: TC;
    begin
      O := TKid.Create();
      O.FIn := TInner.Create();
      O.Go()
    end.
    ''', '101 2 30' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_IndexedPropertyForms;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      IFoo = interface function Get: Integer; end;
      THold = class(TObject, IFoo)
        N: Integer;
        function Get: Integer;
      end;
      TObj = class
        FV: IFoo;
        FA: array[0..3] of Integer;
        FD: Double;
        function GetP(I: Integer): IFoo;
        function GetA(I: Integer): Integer;
        procedure SetA(I: Integer; V: Integer);
        function GetD(K: String): Double;
        function GetS(I: Integer): Single;
        property P[I: Integer]: IFoo read GetP;
        property A[I: Integer]: Integer read GetA write SetA; default;
        property D[K: String]: Double read GetD;
        property S[I: Integer]: Single read GetS;
        procedure Run;
      end;
      TRec = record O: TObj; end;
    var G: TObj;
    function THold.Get: Integer; begin Result := N end;
    function TObj.GetP(I: Integer): IFoo; begin Result := FV end;
    function TObj.GetA(I: Integer): Integer; begin Result := FA[I] end;
    procedure TObj.SetA(I: Integer; V: Integer); begin FA[I] := V end;
    function TObj.GetD(K: String): Double; begin Result := FD end;
    function TObj.GetS(I: Integer): Single; begin Result := 1.5 * I end;
    function MkObj: TObj; begin Result := G end;
    procedure TObj.Run;
    var L: IFoo;
    begin
      L := P[1];
      WriteLn(L.Get(), ' ', P[2].Get(), ' ', Self.P[3].Get());
      A[1] := 11;
      Self.A[2] := 12;
      Self[3] := 13;
      WriteLn(A[1], ' ', Self.A[2], ' ', Self[3])
    end;
    var H: THold; L: IFoo; R: TRec;
    begin
      H := THold.Create();
      H.N := 7;
      G := TObj.Create();
      G.FV := H;
      G.FD := 2.5;
      L := G.P[0];
      WriteLn(L.Get(), ' ', MkObj().P[0].Get());
      G.Run();
      R.O := G;
      R.O[0] := 10;
      WriteLn(R.O[0], ' ', R.O[3]);
      WriteLn(G.D['k']:0:1, ' ', G.S[2]:0:1)
    end.
    ''', '7 7' + LE + '7 7 7' + LE + '11 12 13' + LE + '10 13' + LE +
    '2.5 3.0' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_ArrayPropertyElementWrite_WritesReadField;
const
  Src = '''
    program BQ;
    type
      TArr = array[0..3] of Integer;
      TObj = class
      private
        FArr: TArr;
        FIn: TObj;
        procedure SetArr(const V: TArr);
      public
        property AP: TArr read FArr write FArr;
        property AW: TArr read FArr write SetArr;
        property Inner: TObj read FIn;
        procedure Show;
      end;
    procedure TObj.SetArr(const V: TArr); begin FArr := V; FArr[0] := -1; end;
    procedure TObj.Show; begin FIn.AP[2] := 7; FIn.AW[3] := 8; end;
    var O: TObj;
    begin
      O := TObj.Create(); O.FIn := TObj.Create();
      O.AP[1] := 11; O.AW[2] := 12;
      WriteLn(O.FArr[1], ' ', O.FArr[2], ' ', O.FArr[0]);
      O.Show(); WriteLn(O.FIn.FArr[2], ' ', O.FIn.FArr[3]);
      O.Inner.AP[0] := 5; WriteLn(O.FIn.FArr[0]);
      O.FIn.Free(); O.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '11 12 0' + LineEnding +
    '7 8' + LineEnding +
    '5' + LineEnding, 0);
end;

procedure TE2EPropertyTests.TestRun_BareArrayPropertyElementWrite_InMethod;
const
  Src = '''
    program BP;
    type
      TArr = array[0..3] of Integer;
      TObj = class
      private
        FArr: TArr;
        FD: array of string;
        function GetArr: TArr;
      public
        property AP: TArr read FArr write FArr;
        property DP: array of string read FD write FD;
        property AG: TArr read GetArr;
        procedure Show;
      end;
    function TObj.GetArr: TArr; begin Result := FArr; end;
    procedure TObj.Show;
    begin
      AP[3] := 25; AP[0] := AP[3] + 1;
      SetLength(FD, 2); DP[1] := 'd' + IntToStr(1);
      WriteLn(FArr[3], ' ', FArr[0], ' ', AP[3], ' ', FD[1], ' ', DP[1]);
    end;
    var O: TObj;
    begin
      O := TObj.Create(); O.Show(); O.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '25 26 25 d1 d1' + LineEnding, 0);
end;

procedure TE2EPropertyTests.TestRun_FloatAndRecordIndexRead;
const
  Src = '''
    program P;
    type
      TPair = record A, B: Int64; end;
      TV2 = record X, Y: Double; end;
      TBag = class
        FI: Integer;
        function GetD(D: Double): Integer;
        function GetP(const R: TPair): Integer;
        function GetV(const V: TV2): Double;
        function GetS(S: Single): Integer;
        procedure Show;
        property ByD[D: Double]: Integer read GetD; default;
        property ByP[const R: TPair]: Integer read GetP;
        property ByV[const V: TV2]: Double read GetV;
        property ByS[S: Single]: Integer read GetS;
      end;
      THost = class
        FBag: TBag;
        procedure Inside;
      end;
    function TBag.GetD(D: Double): Integer; begin Result := Trunc(D * 10) + FI; end;
    function TBag.GetP(const R: TPair): Integer; begin Result := R.A * 10 + R.B + FI; end;
    function TBag.GetV(const V: TV2): Double; begin Result := V.X + V.Y; end;
    function TBag.GetS(S: Single): Integer; begin Result := Trunc(S * 2); end;
    procedure TBag.Show; begin WriteLn('self ', ByD[1.5], ' ', Self[0.5]); end;
    var G: TBag;
    function MkB: TBag; begin Result := G; end;
    function MkP: TPair; begin Result.A := 3; Result.B := 4; end;
    procedure THost.Inside;
    var PR: TPair;
    begin
      PR.A := 1; PR.B := 2;
      WriteLn('in ', FBag.ByD[1.5], ' ', FBag.ByP[PR], ' ', FBag[2.5]);
    end;
    var
      B: TBag;
      H: THost;
      PR: TPair;
      V: TV2;
      D: Double;
    begin
      G := TBag.Create();
      G.FI := 1;
      B := G;
      PR.A := 5; PR.B := 6;
      V.X := 1.25; V.Y := 2.5;
      D := 0.75;
      WriteLn(B.ByD[1.25], ' ', B.ByD[D], ' ', B[3.25], ' ', B.ByD[2]);
      WriteLn(B.ByP[PR], ' ', B.ByP[MkP()], ' ', MkB().ByP[PR]);
      WriteLn(B.ByV[V]:0:2, ' ', B.ByS[1.5], ' ', MkB().ByD[0.5]);
      B.Show();
      H := THost.Create();
      H.FBag := G;
      H.Inside();
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '13 8 33 21' + LE + '57 35 57' + LE + '3.75 3 6' + LE +
    'self 16 6' + LE + 'in 16 13 26' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_ElementOfPropertyValueIsResizable;
const
  Src = '''
    program P;
    type
      TIA = array of Integer;
      TRows = array of TIA;
      TObj = class
        FRows: TRows;
        FN: Integer;
        function GetRows(): TRows;
        property Rows: TRows read GetRows;
        property NF: Integer read FN write FN;
      end;
    function TObj.GetRows(): TRows;
    begin
      Result := FRows
    end;
    procedure Bump(var X: Integer);
    begin
      X := X + 1
    end;
    var O: TObj;
    begin
      O := TObj.Create();
      SetLength(O.FRows, 2);
      SetLength(O.Rows[1], 4);
      WriteLn(Length(O.FRows[1]));
      Bump(O.NF);
      Bump(O.FN);
      WriteLn(O.FN)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '4' + LE + '2' + LE, 0);
end;

initialization
  RegisterTest(TE2EPropertyTests);

end.
