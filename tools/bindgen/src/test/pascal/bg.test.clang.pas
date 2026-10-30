{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit bg.test.clang;

{ Tests for Bindgen.Clang — clang AST JSON → C declaration model.

  Runs against src/test/fixtures/sample.json, a real clang 18 dump of
  sample.h (regenerate with gen-fixtures.sh).  Covers:
    - file filtering (decls from included headers are excluded; clang
      only emits loc.file when the file CHANGES, so the loader must
      carry it as sticky state)
    - typedef harvesting, incl. the anonymous-struct-named-by-typedef
      pattern and opaque struct typedefs
    - enum members with explicit and implicit values
    - function signatures, variadic flag, static exclusion }

interface

uses
  blaise.testing, classes,
  Bindgen.Model, Bindgen.Clang;

type
  TClangLoadTests = class(TTestCase)
  private
    FModel: TCModel;
    function LoadFixture(const AFileMatch: string): TCModel;
    function FindTypedef(AModel: TCModel; const AName: string): TCTypedef;
    function FindFunction(AModel: TCModel; const AName: string): TCFunction;
    function FindEnum(AModel: TCModel; const AName: string): TCEnum;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestLoad_FileFilter_ExcludesDepHeader;
    procedure TestLoad_NoFilter_IncludesDepHeader;
    procedure TestLoad_Typedef_XID_UnsignedLong;
    procedure TestLoad_Typedef_ChainedTypedef;
    procedure TestLoad_Enum_ExplicitAndImplicitValues;
    procedure TestLoad_AnonStruct_TakesTypedefName;
    procedure TestLoad_AnonStructTypedef_NotDuplicated;
    procedure TestLoad_OpaqueRecord_Incomplete;
    procedure TestLoad_OpaqueTypedef_Kept;
    procedure TestLoad_Function_ReturnAndParams;
    procedure TestLoad_Function_VoidNoParams;
    procedure TestLoad_Function_Variadic;
    procedure TestLoad_StaticFunction_Excluded;
    procedure TestLoad_AnonEnum_TakesTypedefName;
    procedure TestLoad_Bitfields_CollapsedIntoStorageUnits;
    procedure TestLoad_NamedUnion_Loaded;
    procedure TestLoad_AnonUnionField_LiftedAndNamed;
    procedure TestLoad_LiftedUnion_PrecedesOwnerInDecls;
    procedure TestLoad_SharedAnonStruct_BothFieldsRetyped;
  end;

implementation

function FixturePath: string;
begin
  { Tolerate the three cwds the runner is started from: the module dir
    (manual runs), the module's target dir (pasbuild test), and the
    repo root. }
  Result := 'src/test/fixtures/sample.json';
  if FileExists(Result) then Exit;
  Result := '../src/test/fixtures/sample.json';
  if FileExists(Result) then Exit;
  Result := 'tools/bindgen/src/test/fixtures/sample.json';
end;

function TClangLoadTests.LoadFixture(const AFileMatch: string): TCModel;
var
  Lines: TStringList;
begin
  Lines := TStringList.Create();
  Lines.LoadFromFile(FixturePath());
  Result := LoadClangASTText(Lines.Text, AFileMatch);
end;

function TClangLoadTests.FindTypedef(AModel: TCModel; const AName: string): TCTypedef;
var
  I: Int;
begin
  Result := nil;
  for I := 0 to AModel.Typedefs.Count - 1 do
    if AModel.Typedefs[I].Name = AName then
    begin
      Result := AModel.Typedefs[I];
      Exit;
    end;
end;

function TClangLoadTests.FindFunction(AModel: TCModel; const AName: string): TCFunction;
var
  I: Int;
begin
  Result := nil;
  for I := 0 to AModel.Functions.Count - 1 do
    if AModel.Functions[I].Name = AName then
    begin
      Result := AModel.Functions[I];
      Exit;
    end;
end;

procedure TClangLoadTests.SetUp;
begin
  FModel := Self.LoadFixture('sample.h');
end;

procedure TClangLoadTests.TearDown;
begin
  FModel := nil;
end;

procedure TClangLoadTests.TestLoad_FileFilter_ExcludesDepHeader;
begin
  AssertTrue('DepType excluded', Self.FindTypedef(FModel, 'DepType') = nil);
  AssertTrue('dep_func excluded', Self.FindFunction(FModel, 'dep_func') = nil);
end;

procedure TClangLoadTests.TestLoad_NoFilter_IncludesDepHeader;
var
  All: TCModel;
begin
  All := Self.LoadFixture('');
  AssertTrue('DepType included', Self.FindTypedef(All, 'DepType') <> nil);
  AssertTrue('dep_func included', Self.FindFunction(All, 'dep_func') <> nil);
end;

procedure TClangLoadTests.TestLoad_Typedef_XID_UnsignedLong;
var
  T: TCTypedef;
begin
  T := Self.FindTypedef(FModel, 'XID');
  AssertTrue('XID found', T <> nil);
  AssertEquals('unsigned long', T.CType);
end;

procedure TClangLoadTests.TestLoad_Typedef_ChainedTypedef;
var
  T: TCTypedef;
begin
  T := Self.FindTypedef(FModel, 'Window');
  AssertTrue('Window found', T <> nil);
  AssertEquals('XID', T.CType);
end;

procedure TClangLoadTests.TestLoad_Enum_ExplicitAndImplicitValues;
var
  E: TCEnum;
begin
  E := Self.FindEnum(FModel, 'XOrientation');
  AssertTrue('XOrientation found', E <> nil);
  AssertEquals('member count', 3, E.Members.Count);
  AssertEquals('XOrientVertical', E.Members[0].Name);
  AssertEquals('implicit first value', 0, Int32(E.Members[0].Value));
  AssertEquals('explicit value', 5, Int32(E.Members[1].Value));
  AssertEquals('implicit follows explicit', 6, Int32(E.Members[2].Value));
end;

procedure TClangLoadTests.TestLoad_AnonStruct_TakesTypedefName;
var
  R: TCRecord;
begin
  R := FModel.FindRecord('XPoint');
  AssertTrue('XPoint record found', R <> nil);
  AssertTrue('complete', R.IsComplete);
  AssertEquals('field count', 3, R.Fields.Count);
  AssertEquals('x', R.Fields[0].Name);
  AssertEquals('int', R.Fields[0].CType);
  AssertEquals('serial', R.Fields[1].Name);
  AssertEquals('unsigned long', R.Fields[1].CType);
  AssertEquals('name', R.Fields[2].Name);
  AssertEquals('const char *', R.Fields[2].CType);
end;

procedure TClangLoadTests.TestLoad_AnonStructTypedef_NotDuplicated;
begin
  { The record itself was named XPoint, so no 'XPoint = struct XPoint'
    typedef must survive — the emitter would generate a self-alias. }
  AssertTrue(Self.FindTypedef(FModel, 'XPoint') = nil);
end;

procedure TClangLoadTests.TestLoad_OpaqueRecord_Incomplete;
var
  R: TCRecord;
begin
  R := FModel.FindRecord('_XDisplay');
  AssertTrue('_XDisplay found', R <> nil);
  AssertTrue('opaque', not R.IsComplete);
end;

procedure TClangLoadTests.TestLoad_OpaqueTypedef_Kept;
var
  T: TCTypedef;
begin
  T := Self.FindTypedef(FModel, 'Display');
  AssertTrue('Display found', T <> nil);
  AssertEquals('struct _XDisplay', T.CType);
end;

procedure TClangLoadTests.TestLoad_Function_ReturnAndParams;
var
  F: TCFunction;
begin
  F := Self.FindFunction(FModel, 'XOpenDisplay');
  AssertTrue('found', F <> nil);
  AssertEquals('Display *', F.ReturnCType);
  AssertEquals('param count', 1, F.Params.Count);
  AssertEquals('display_name', F.Params[0].Name);
  AssertEquals('const char *', F.Params[0].CType);
  AssertTrue('not variadic', not F.IsVariadic);
end;

procedure TClangLoadTests.TestLoad_Function_VoidNoParams;
var
  F: TCFunction;
begin
  F := Self.FindFunction(FModel, 'XFlushNothing');
  AssertTrue('found', F <> nil);
  AssertEquals('void', F.ReturnCType);
  AssertEquals('param count', 0, F.Params.Count);
end;

procedure TClangLoadTests.TestLoad_Function_Variadic;
var
  F: TCFunction;
begin
  F := Self.FindFunction(FModel, 'XVariadicThing');
  AssertTrue('found', F <> nil);
  AssertTrue('variadic', F.IsVariadic);
end;

procedure TClangLoadTests.TestLoad_StaticFunction_Excluded;
begin
  AssertTrue(Self.FindFunction(FModel, 'hidden_helper') = nil);
end;

function TClangLoadTests.FindEnum(AModel: TCModel; const AName: string): TCEnum;
var
  I: Int;
begin
  Result := nil;
  for I := 0 to AModel.Enums.Count - 1 do
    if AModel.Enums[I].Name = AName then
    begin
      Result := AModel.Enums[I];
      Exit;
    end;
end;

procedure TClangLoadTests.TestLoad_AnonEnum_TakesTypedefName;
var
  E: TCEnum;
begin
  { 'typedef enum ... XSampleDirection;' with an anonymous enum body:
    the enum adopts the typedef name (so 'XSampleDirection = Integer;'
    is emitted) and the redundant typedef is dropped. }
  E := Self.FindEnum(FModel, 'XSampleDirection');
  AssertTrue('enum named', E <> nil);
  AssertEquals('members', 2, E.Members.Count);
  AssertEquals('explicit value', 10, Int32(E.Members[1].Value));
  AssertTrue('typedef dropped', Self.FindTypedef(FModel, 'XSampleDirection') = nil);
end;

procedure TClangLoadTests.TestLoad_Bitfields_CollapsedIntoStorageUnits;
var
  R: TCRecord;
begin
  { a:1 b:3 c:12 (one uint unit), plain, d:4 e:4 (one ushort unit)
    — C sizeof is 12, which the collapsed layout reproduces. }
  R := FModel.FindRecord('XSampleFlags');
  AssertTrue('found', R <> nil);
  AssertEquals('field count', 3, R.Fields.Count);
  AssertEquals('__bits0', R.Fields[0].Name);
  AssertEquals('unsigned int', R.Fields[0].CType);
  AssertTrue('members noted', Pos('a:1', R.Fields[0].Note) >= 0);
  AssertTrue('members noted b', Pos('b:3', R.Fields[0].Note) >= 0);
  AssertEquals('plain', R.Fields[1].Name);
  AssertEquals('__bits1', R.Fields[2].Name);
  AssertEquals('unsigned short', R.Fields[2].CType);
end;

procedure TClangLoadTests.TestLoad_NamedUnion_Loaded;
var
  R: TCRecord;
begin
  R := FModel.FindRecord('_XSampleEvent');
  AssertTrue('found', R <> nil);
  AssertTrue('is union', R.IsUnion);
  AssertTrue('complete', R.IsComplete);
  AssertEquals('members', 2, R.Fields.Count);
end;

procedure TClangLoadTests.TestLoad_AnonUnionField_LiftedAndNamed;
var
  Msg: TCRecord;
  Lifted: TCRecord;
begin
  { The anonymous union inside XSampleMessage is lifted to a named
    record 'XSampleMessage_data_t' and the field retyped to it. }
  Msg := FModel.FindRecord('XSampleMessage');
  AssertTrue('outer found', Msg <> nil);
  AssertEquals('field count', 2, Msg.Fields.Count);
  AssertEquals('data', Msg.Fields[1].Name);
  AssertEquals('XSampleMessage_data_t', Msg.Fields[1].CType);
  Lifted := FModel.FindRecord('XSampleMessage_data_t');
  AssertTrue('lifted found', Lifted <> nil);
  AssertTrue('lifted is union', Lifted.IsUnion);
  AssertEquals('lifted members', 3, Lifted.Fields.Count);
  AssertEquals('long[5]', Lifted.Fields[2].CType);
end;

procedure TClangLoadTests.TestLoad_LiftedUnion_PrecedesOwnerInDecls;
var
  I: Int;
  LiftedIdx, OwnerIdx: Int;
  D: TCDecl;
begin
  { The emitter walks Decls in order; the owner's field references the
    lifted type, so the lifted record must come first. }
  LiftedIdx := -1;
  OwnerIdx := -1;
  for I := 0 to FModel.Decls.Count - 1 do
  begin
    D := FModel.Decls[I];
    if D is TCRecord then
    begin
      if TCRecord(D).Name = 'XSampleMessage_data_t' then LiftedIdx := I;
      if TCRecord(D).Name = 'XSampleMessage' then OwnerIdx := I;
    end;
  end;
  AssertTrue('lifted present', LiftedIdx >= 0);
  AssertTrue('owner present', OwnerIdx >= 0);
  AssertTrue('lifted first', LiftedIdx < OwnerIdx);
end;

procedure TClangLoadTests.TestLoad_SharedAnonStruct_BothFieldsRetyped;
var
  R: TCRecord;
  Lifted: TCRecord;
begin
  { XSizeHints pattern: two fields declared against ONE anonymous
    struct — 'min_aspect, max_aspect' after the closing brace.  Both
    must be retyped to the same lifted record (keyed by the location-
    unique qualType); it is named after the FIRST referencing field. }
  R := FModel.FindRecord('XSampleHints');
  AssertTrue('outer found', R <> nil);
  AssertEquals('field count', 3, R.Fields.Count);
  AssertEquals('XSampleHints_min_aspect_t', R.Fields[1].CType);
  AssertEquals('both fields share the lifted type',
    'XSampleHints_min_aspect_t', R.Fields[2].CType);
  Lifted := FModel.FindRecord('XSampleHints_min_aspect_t');
  AssertTrue('lifted found', Lifted <> nil);
  AssertEquals('lifted members', 2, Lifted.Fields.Count);
end;

initialization
  RegisterTest(TClangLoadTests);

end.
