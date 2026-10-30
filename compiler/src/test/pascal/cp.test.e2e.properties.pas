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
    { properties in records (Delphi/FPC advanced records): field- and
      method-backed, string, object, Double, indexed default, float index,
      static; through a local, a global, a var parameter, a call result, a
      record held in a class field, bare and Self[I] inside a record method,
      captured by a nested routine and by a closure; a generic record }
    procedure TestRun_RecordProperties_EveryForm;
    { the same record declared in a UNIT: its properties reach the program
      through the cached interface (IFACE v26), and a static property reads
      its PRIVATE backing static var from the other unit }
    procedure TestRun_RecordProperties_InUnit;
    { F()[I] := V through the default property of what a call returns, as FPC
      and Delphi accept it: a function, a method, a call as the index and the
      value, a fresh object (freed after the statement), a managed string
      value; a record element (storage, so the write sticks) and a record
      function result (the setter runs on a discarded temporary) }
    procedure TestRun_DefaultPropWriteOnCallResult;
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
    { statements that go on past an indexed property: a call on H.Items[0],
      field and element writes through it, the same one link further down,
      and writes past array-field elements in the same chains (the property
      forms were rejected: "requires an index expression") }
    procedure TestRun_StatementChainPastIndexedProperty;
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
    type TC = class FX: Int; property X: Int read FX write FX; end;
    var c: TC;
    begin c := TC.Create(); c.X := 17; WriteLn(c.X); c.Free() end.
    ''';

  SrcGetterSetter = '''
    program Prg;
    type TC = class
      FX: Int;
      function GetX: Int; begin Result := FX * 2 end;
      procedure SetX(V: Int); begin FX := V + 1 end;
      property X: Int read GetX write SetX;
    end;
    var c: TC;
    begin c := TC.Create(); c.X := 10; WriteLn(c.X); c.Free() end.
    ''';

  SrcReadOnly = '''
    program Prg;
    type TC = class FW, FH: Int; function GetArea: Int; begin Result := FW * FH end; property Area: Int read GetArea; end;
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
    type TC = class FX: Int; property X: Int read FX write FX; end;
    var c: TC;
    begin c := TC.Create(); WriteLn(c.X); c.Free() end.
    ''';

  SrcInherited = '''
    program Prg;
    type TBase = class FX: Int; property X: Int read FX write FX; end;
      TDer = class(TBase) end;
    var d: TDer;
    begin d := TDer.Create(); d.X := 55; WriteLn(d.X); d.Free() end.
    ''';

  SrcIndexed = '''
    program Prg;
    type TC = class
      FData: array[0..9] of Int;
      function GetItem(I: Int): Int; begin Result := FData[I] end;
      procedure SetItem(I, V: Int); begin FData[I] := V end;
      property Items[I: Int]: Int read GetItem write SetItem;
    end;
    var c: TC;
    begin c := TC.Create(); c.Items[3] := 99; WriteLn(c.Items[3]); c.Free() end.
    ''';

  SrcStringIndexed = '''
    program Prg;
    type TC = class
      FVal: Int;
      function GetItem(const Key: string): Int; begin Result := FVal end;
      procedure SetItem(const Key: string; V: Int); begin FVal := V end;
      property Items[Key: string]: Int read GetItem write SetItem;
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
      TRec = record A: Int; S: string; end;
      TC = class
        FA: Int; FS: string;
        procedure SetItem(K: Int; const R: TRec); begin FA := R.A + K; FS := R.S end;
        property Items[K: Int]: TRec write SetItem;
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
        procedure SetItem(K: Int; const V: string);
        function GetItem(K: Int): string;
        procedure SetCur(const V: string);
        property Items[K: Int]: string read GetItem write SetItem;
        property Cur: string write SetCur;
      end;
      procedure TC.SetItem(K: Int; const V: string); begin FItems[K] := V end;
      function TC.GetItem(K: Int): string; begin Result := FItems[K] end;
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
      TRec = record A: Int; S: string; end;
      TC = class
        FA: Int; FS: string;
        procedure SetItem(K: Int; const R: TRec); begin FA := R.A + K; FS := R.S end;
        property Items[K: Int]: TRec write SetItem; default;
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
    type TC = class FD: array[0..4] of Int; function At(i: Int): Int; begin Result := FD[i] end; end;
    var c: TC;
    begin c := TC.Create(); c.FD[2] := 88; WriteLn(c.At(2)); c.Free() end.
    ''';

  SrcArrFieldWrite = '''
    program Prg;
    type TC = class
      FD: array[0..4] of Int;
      procedure Init; var i: Int; begin for i := 0 to 4 do FD[i] := i * 10 end;
      function Get(i: Int): Int; begin Result := FD[i] end;
    end;
    var c: TC;
    begin c := TC.Create(); c.Init(); WriteLn(c.Get(3)); c.Free() end.
    ''';

  SrcArrFieldSum = '''
    program Prg;
    type TC = class
      FD: array[0..9] of Int;
      function Sum: Int; var i: Int; begin Result := 0; for i := 0 to 9 do Result := Result + FD[i] end;
    end;
    var c: TC; k: Int;
    begin c := TC.Create(); for k := 0 to 9 do c.FD[k] := k; WriteLn(c.Sum()); c.Free() end.
    ''';

  SrcArrOfRecord = '''
    program Prg;
    type TP = record X: Int; end;
      TC = class
        FD: array[0..2] of TP;
        function GetX(i: Int): Int; begin Result := FD[i].X end;
        procedure SetX(i, v: Int); begin FD[i].X := v end;
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
        FData: array[0..4] of Int;
        function Get(i: Int): Int; begin Result := FData[i] end;
        procedure Put(i: Int; v: Int); begin FData[i] := v end;
        property Items[i: Int]: Int read Get write Put; default;
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
        function Get(i: Int): string; begin Result := FData[i] end;
        procedure Put(i: Int; v: string); begin FData[i] := v end;
        property Items[i: Int]: string read Get write Put; default;
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
        FData: array[0..2] of Int;
        function Get(i: Int): Int; begin Result := FData[i] end;
        procedure Put(i: Int; v: Int); begin FData[i] := v end;
        property Items[i: Int]: Int read Get write Put; default;
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
        FData: array[0..4] of Int;
        function Get(i: Int): Int; begin Result := FData[i] end;
        procedure Put(i: Int; v: Int); begin FData[i] := v end;
        property Items[i: Int]: Int read Get write Put; default;
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
        FData: array[0..4] of Int;
        function Get(i: Int): Int; begin Result := FData[i] end;
        procedure Put(i: Int; v: Int); begin FData[i] := v end;
        property Items[i: Int]: Int read Get write Put; default;
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
        FData: array[0..4] of Int;
        function Get(i: Int): Int; begin Result := FData[i] end;
        procedure Put(i: Int; v: Int); begin FData[i] := v end;
        property Items[i: Int]: Int read Get write Put; default;
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
        FData: array[0..4] of Int;
        function Get(i: Int): Int; begin Result := FData[i] end;
        procedure Put(i: Int; v: Int); begin FData[i] := v end;
        property Items[i: Int]: Int read Get write Put; default;
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
        FData: array[0..4] of Int;
        function Get(i: Int): Int; begin Result := FData[i] end;
        procedure Put(i: Int; v: Int); begin FData[i] := v end;
        property Items[i: Int]: Int read Get write Put; default;
      end;
      TOwner = class
        FVec: TVec;
        constructor Create;
        procedure Fill;
        function Sum: Int;
      end;
    constructor TOwner.Create; begin inherited Create(); FVec := TVec.Create end;
    procedure TOwner.Fill; begin FVec[0] := 3; FVec[1] := 4; end;
    function TOwner.Sum: Int; begin Result := FVec[0] + FVec[1]; end;
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
        FBase: Int;
        constructor Create;
        function Get(i: Int): Int;
        property Items[i: Int]: Int read Get; default;
      end;
      TMid = class
        M1: Int;
        Vec: TVec;
        constructor Create;
      end;
      TTop = class
        T1: Int;
        Mid: TMid;
        constructor Create;
      end;
    constructor TVec.Create; begin inherited Create(); FBase := 5 end;
    function TVec.Get(i: Int): Int; begin Result := FBase + i * 4 end;
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
        FA: Int;
        FB: Int;
        procedure SetSlot(AIndex: Int; AValue: Int);
        function GetSlot(AIndex: Int): Int;
        property Slot[AIndex: Int]: Int read GetSlot write SetSlot;
      end;
      TOuter = class
        Inner: TInner;
      end;
    procedure TInner.SetSlot(AIndex: Int; AValue: Int);
    begin
      if AIndex = 0 then FA := AValue else FB := AValue
    end;
    function TInner.GetSlot(AIndex: Int): Int;
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
      TIntArr = array of Int;
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
      TSA = array[0..2] of Int;
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
      TPt = record X, Y, Z: Int; end;
      TSA = array[0..2] of Int;
      TBase = class
        FP: TPt;
        FSA: TSA;
        function GetP: TPt;
        function GetSA: TSA;
        function GetN: Int; virtual;
        function GetStr: string; virtual;
        property P: TPt read GetP;
        property SA: TSA read GetSA;
        property N: Int read GetN;
        property Str: string read GetStr;
        procedure Show;
      end;
      TKid = class(TBase)
        function GetN: Int; override;
        function GetStr: string; override;
      end;
    function TBase.GetP: TPt; begin Result := FP end;
    function TBase.GetSA: TSA; begin Result := FSA end;
    function TBase.GetN: Int; begin Result := 1 end;
    function TBase.GetStr: string; begin Result := 'base' end;
    function TKid.GetN: Int; begin Result := 2 end;
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
        function Val: Int;
      end;
      TThing = class(TObject, IThing)
        N: Int;
        function Val: Int;
      end;
      THolder = class
        FThing: IThing;
        FS0, FS1: IThing;
        procedure SetThing(V: IThing);
        function GetSlot(I: Int): IThing;
        procedure SetSlot(I: Int; V: IThing);
        property Thing: IThing read FThing write SetThing;
        property Slot[I: Int]: IThing read GetSlot write SetSlot;
      end;
    function TThing.Val: Int; begin Result := N end;
    procedure THolder.SetThing(V: IThing); begin FThing := V end;
    function THolder.GetSlot(I: Int): IThing;
    begin
      if I = 0 then Result := FS0 else Result := FS1
    end;
    procedure THolder.SetSlot(I: Int; V: IThing);
    begin
      if I = 0 then FS0 := V else FS1 := V
    end;
    function MakeThing(N: Int): IThing;
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
        FN: Int;
        procedure SetN(V: Int);
        property N: Int read FN write SetN;
      end;
      TC = class
        FM: Int;
        FK: Int;
        FIn: TInner;
        procedure SetK(V: Int); virtual;
        property K: Int read FK write SetK;
        property M: Int read FM write FM;
        property Inner: TInner read FIn;
        procedure Go;
      end;
      TKid = class(TC)
        procedure SetK(V: Int); override;
      end;
    procedure TInner.SetN(V: Int); begin FN := V * 10 end;
    procedure TC.SetK(V: Int); begin FK := V end;
    procedure TKid.SetK(V: Int); begin FK := V + 100 end;
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
      IFoo = interface function Get: Int; end;
      THold = class(TObject, IFoo)
        N: Int;
        function Get: Int;
      end;
      TObj = class
        FV: IFoo;
        FA: array[0..3] of Int;
        FD: Float64;
        function GetP(I: Int): IFoo;
        function GetA(I: Int): Int;
        procedure SetA(I: Int; V: Int);
        function GetD(K: String): Float64;
        function GetS(I: Int): Float32;
        property P[I: Int]: IFoo read GetP;
        property A[I: Int]: Int read GetA write SetA; default;
        property D[K: String]: Float64 read GetD;
        property S[I: Int]: Float32 read GetS;
        procedure Run;
      end;
      TRec = record O: TObj; end;
    var G: TObj;
    function THold.Get: Int; begin Result := N end;
    function TObj.GetP(I: Int): IFoo; begin Result := FV end;
    function TObj.GetA(I: Int): Int; begin Result := FA[I] end;
    procedure TObj.SetA(I: Int; V: Int); begin FA[I] := V end;
    function TObj.GetD(K: String): Float64; begin Result := FD end;
    function TObj.GetS(I: Int): Float32; begin Result := 1.5 * I end;
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
      TArr = array[0..3] of Int;
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
      TArr = array[0..3] of Int;
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
      TV2 = record X, Y: Float64; end;
      TBag = class
        FI: Int;
        function GetD(D: Float64): Int;
        function GetP(const R: TPair): Int;
        function GetV(const V: TV2): Float64;
        function GetS(S: Float32): Int;
        procedure Show;
        property ByD[D: Float64]: Int read GetD; default;
        property ByP[const R: TPair]: Int read GetP;
        property ByV[const V: TV2]: Float64 read GetV;
        property ByS[S: Float32]: Int read GetS;
      end;
      THost = class
        FBag: TBag;
        procedure Inside;
      end;
    function TBag.GetD(D: Float64): Int; begin Result := Trunc(D * 10) + FI; end;
    function TBag.GetP(const R: TPair): Int; begin Result := R.A * 10 + R.B + FI; end;
    function TBag.GetV(const V: TV2): Float64; begin Result := V.X + V.Y; end;
    function TBag.GetS(S: Float32): Int; begin Result := Trunc(S * 2); end;
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
      D: Float64;
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
      TIA = array of Int;
      TRows = array of TIA;
      TObj = class
        FRows: TRows;
        FN: Int;
        function GetRows(): TRows;
        property Rows: TRows read GetRows;
        property NF: Int read FN write FN;
      end;
    function TObj.GetRows(): TRows;
    begin
      Result := FRows
    end;
    procedure Bump(var X: Int);
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

procedure TE2EPropertyTests.TestRun_RecordProperties_EveryForm;
const
  Src = '''
    program P;
    uses SysUtils;
    type
      TItem = class
        N: Int;
        constructor Create(AN: Int);
        destructor Destroy; override;
      end;
      TVec = record
      private
        FX, FY: Int;
        FTag: string;
        FItem: TItem;
        FD: Float64;
        function GetLen2: Int;
        procedure SetX(AV: Int);
        procedure SetItem(AV: TItem);
        function GetAt(I: Int): Int;
        procedure SetAt(I: Int; AV: Int);
        function GetScaled(F: Float64): Float64;
      private static var
        FCount: Int;
      public
        property X: Int read FX write SetX;
        property Y: Int read FY write FY;
        property Len2: Int read GetLen2;
        property Tag: string read FTag write FTag;
        property Item: TItem read FItem write SetItem;
        property D: Float64 read FD write FD;
        property At[I: Int]: Int read GetAt write SetAt; default;
        property Scaled[F: Float64]: Float64 read GetScaled;
        static property Count: Int read FCount write FCount;
        procedure Inside;
      end;
      THolder = class
        R: TVec;
      end;
      TBox<T> = record
      private
        FV: T;
        function GetV: T;
        procedure SetV(const AV: T);
      public
        property V: T read GetV write SetV;
      end;
    constructor TItem.Create(AN: Int); begin N := AN; end;
    destructor TItem.Destroy; begin WriteLn('free ', N); end;
    function TVec.GetLen2: Int; begin Result := FX * FX + FY * FY; end;
    procedure TVec.SetX(AV: Int); begin FX := AV; FCount := FCount + 1; end;
    procedure TVec.SetItem(AV: TItem); begin FItem := AV; end;
    function TVec.GetAt(I: Int): Int; begin if I = 0 then Result := FX else Result := FY; end;
    procedure TVec.SetAt(I: Int; AV: Int); begin if I = 0 then X := AV else FY := AV; end;
    function TVec.GetScaled(F: Float64): Float64; begin Result := FX * F; end;
    procedure TVec.Inside;
    begin
      X := 2;
      Y := 3;
      Self[1] := 4;
      Item := TItem.Create(10);
      WriteLn('inside ', X, ' ', Y, ' ', Len2, ' ', At[0], ' ', Item.N);
      Item := nil;
    end;
    function TBox<T>.GetV: T; begin Result := FV; end;
    procedure TBox<T>.SetV(const AV: T); begin FV := AV; end;
    function MkVec(AX, AY: Int): TVec; begin Result.FX := AX; Result.FY := AY; end;
    procedure Bump(var V: TVec); begin V.X := V.X + 1; V[1] := V[1] + 1; end;
    var
      G: TVec;
    procedure Captures;
    var
      V: TVec;
      F: reference to procedure;
      procedure Nested;
      begin
        V.X := 7;
        V.Tag := 'n' + IntToStr(V.X);
      end;
    begin
      Nested();
      F := procedure begin V[1] := 8; end;
      F();
      WriteLn('capt ', V.X, ' ', V.Y, ' ', V.Tag);
    end;
    var
      V: TVec;
      H: THolder;
      B: TBox<Int>;
      S: TBox<string>;
    begin
      V.X := 3;
      V.Y := 4;
      V.Tag := 'v' + IntToStr(V.Len2);
      V.D := 1.5;
      WriteLn(V.X, ' ', V.Y, ' ', V.Len2, ' ', V.Tag, ' ', V[0], ' ', V.At[1], ' ', V.D:0:1, ' ', V.Scaled[0.5]:0:1);
      V[0] := 6;
      V.Item := TItem.Create(1);
      V.Item := TItem.Create(2);
      WriteLn(V.Len2, ' ', MkVec(1, 2).Len2, ' ', MkVec(7, 8)[1], ' ', V.Item.N, ' ', TVec.Count);
      V.Item := nil;
      Bump(V);
      WriteLn('bump ', V.X, ' ', V.Y);
      G.X := 9;
      G[1] := 1;
      WriteLn('glob ', G.Len2);
      H := THolder.Create;
      H.R.X := 5;
      H.R[1] := 12;
      WriteLn('holder ', H.R.Len2, ' ', H.R[0]);
      V.Inside();
      Captures();
      B.V := 5;
      B.V := B.V + 1;
      S.V := 'x';
      S.V := S.V + 'y';
      TVec.Count := 0;
      WriteLn('gen ', B.V, ' ', S.V, ' ', TVec.Count);
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '3 4 25 v25 3 4 1.5 1.5' + LE +
    'free 1' + LE +
    '52 5 8 2 2' + LE +
    'free 2' + LE +
    'bump 7 5' + LE +
    'glob 82' + LE +
    'holder 169 5' + LE +
    'inside 2 4 20 2 10' + LE +
    'free 10' + LE +
    'capt 7 8 n7' + LE +
    'gen 6 xy 0' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_DefaultPropWriteOnCallResult;
const
  Src = '''
    program P;
    type
      TSHolder = class
      private
        FA: array[0..3] of string;
        FTag: string;
        function GetS(I: Int): string;
        procedure SetS(I: Int; const V: string);
      public
        constructor Create(const ATag: string);
        destructor Destroy; override;
        property S[I: Int]: string read GetS write SetS; default;
      end;
      TRec = record
        FA: array[0..3] of Int;
        function GetI(I: Int): Int;
        procedure SetI(I: Int; V: Int);
        property Items[I: Int]: Int read GetI write SetI; default;
      end;
      TFac = class
        H: TSHolder;
        function Get(): TSHolder;
      end;
    var
      G: TSHolder;
      F: TFac;
      RA: array[0..1] of TRec;
    constructor TSHolder.Create(const ATag: string); begin FTag := ATag; end;
    destructor TSHolder.Destroy; begin WriteLn('free ', FTag, ' ', FA[3]); end;
    function TSHolder.GetS(I: Int): string; begin Result := FA[I]; end;
    procedure TSHolder.SetS(I: Int; const V: string); begin FA[I] := V; end;
    function TRec.GetI(I: Int): Int; begin Result := FA[I]; end;
    procedure TRec.SetI(I: Int; V: Int); begin FA[I] := V; WriteLn('rset ', I, ' ', V); end;
    function TFac.Get(): TSHolder; begin Result := H; end;
    function MkS(): TSHolder; begin Result := G; end;
    function MkR(): TRec; begin Result.FA[0] := 0; end;
    function Idx(): Int; begin Result := 2; end;
    begin
      G := TSHolder.Create('g');
      F := TFac.Create();
      F.H := G;
      MkS()[0] := 'a' + IntToStr(Idx());
      F.Get()[1] := 'b';
      F.Get()[Idx()] := MkS()[0] + '!';
      TSHolder.Create('t')[3] := 'gone';
      WriteLn(G[0], ' ', G[1], ' ', G[2]);
      RA[1][2] := 42;
      WriteLn(RA[1][2], ' ', RA[1].FA[2]);
      MkR()[3] := 9;
      F.H := nil;
      G := nil;
      WriteLn('end');
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'free t gone' + LE +
    'a2 b a2!' + LE +
    'rset 2 42' + LE +
    '42 42' + LE +
    'rset 3 9' + LE +
    'free g ' + LE +
    'end' + LE, 0);
end;

procedure TE2EPropertyTests.TestRun_RecordProperties_InUnit;
const
  USrc = '''
    unit RProps;
    interface
    type
      TVec = record
      private
        FX, FY: Int;
        FTag: string;
        function GetLen2: Int;
        procedure SetX(AV: Int);
        function GetAt(I: Int): Int;
        procedure SetAt(I: Int; AV: Int);
      private static var
        FCount: Int;
      public
        property X: Int read FX write SetX;
        property Y: Int read FY write FY;
        property Len2: Int read GetLen2;
        property Tag: string read FTag write FTag;
        property At[I: Int]: Int read GetAt write SetAt; default;
        static property Count: Int read FCount write FCount;
      end;
    function MkVec(AX, AY: Int): TVec;
    implementation
    function TVec.GetLen2: Int; begin Result := FX * FX + FY * FY; end;
    procedure TVec.SetX(AV: Int); begin FX := AV; FCount := FCount + 1; end;
    function TVec.GetAt(I: Int): Int; begin if I = 0 then Result := FX else Result := FY; end;
    procedure TVec.SetAt(I: Int; AV: Int); begin if I = 0 then X := AV else FY := AV; end;
    function MkVec(AX, AY: Int): TVec; begin Result.FX := AX; Result.FY := AY; end;
    end.
    ''';
  Src = '''
    program P;
    uses RProps;
    var V: TVec;
    begin
      V.X := 3;
      V.Y := 4;
      V.Tag := 'v';
      WriteLn(V.X, ' ', V.Y, ' ', V.Len2, ' ', V.Tag, ' ', V[0], ' ', V[1]);
      V[1] := 5;
      V[0] := 6;
      WriteLn(V.Len2, ' ', MkVec(1, 2).Len2, ' ', MkVec(7, 8)[1], ' ', TVec.Count);
      TVec.Count := 10;
      WriteLn(TVec.Count);
    end.
    ''';
var
  LE: string;
  RunOut: string;
  Code: Int;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run: ' + RunOut,
    CompileAndRunWithUnit('RProps', USrc, Src, RunOut, Code));
  AssertEquals('exit code', 0, Code);
  AssertEquals('stdout', '3 4 25 v 3 4' + LE + '61 5 8 2' + LE + '10' + LE, RunOut);
end;

procedure TE2EPropertyTests.TestRun_StatementChainPastIndexedProperty;
const
  Src = '''
    program P;
    type
      TA = class N: Int; Arr: array[0..2] of Int; procedure Show(); end;
      TRec = record V: Int; G: array[0..1] of array[0..1] of Int; end;
      THolder = class
        FA: TA;
        Recs: array[0..1] of TRec;
        Objs: array of TA;
        Grid: array[0..1] of array[0..1] of Int;
        Sub: THolder;
        function GetItem(I: Int): TA;
        procedure SetItem(I: Int; V: TA);
        property Items[I: Int]: TA read GetItem write SetItem;
      end;
    procedure TA.Show(); begin WriteLn('show ', N, ' ', Arr[1]) end;
    function THolder.GetItem(I: Int): TA; begin Result := FA end;
    procedure THolder.SetItem(I: Int; V: TA); begin FA := V end;
    var H: THolder;
    begin
      H := THolder.Create(); H.FA := TA.Create(); H.FA.N := 5;
      H.Sub := H;
      SetLength(H.Objs, 2); H.Objs[1] := H.FA;
      H.Items[0].Show();
      H.Items[0].N := 6;
      H.Items[0].Arr[1] := 7;
      H.Items[0].Show();
      H.Sub.Items[0].N := 8;
      H.Sub.Items[1].Show();
      H.Recs[1].V := 9;
      H.Recs[1].G[1][0] := 10;
      H.Grid[1][1] := 12;
      H.Sub.Grid[1][0] := 14;
      H.Sub.Recs[0].V := 15;
      H.Objs[1].N := 16;
      H.Sub.Objs[1].Arr[1] := 17;
      H.Sub.Objs[1].Show();
      H.Items[0] := H.FA;
      H.Sub := nil;
      WriteLn(H.Recs[1].V, ' ', H.Recs[1].G[1][0], ' ', H.Grid[1][1], ' ',
        H.Grid[1][0], ' ', H.Recs[0].V)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'show 5 0' + LE + 'show 6 7' + LE + 'show 8 7' + LE + 'show 16 17' + LE +
    '9 10 12 14 15' + LE, 0);
end;

initialization
  RegisterTest(TE2EPropertyTests);

end.
