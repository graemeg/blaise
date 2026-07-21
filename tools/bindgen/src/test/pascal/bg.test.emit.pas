{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit bg.test.emit;

{ Tests for Bindgen.Emit — C declaration model → Blaise unit source.

  Assertions are substring checks on the generated source; the
  compile-the-output check lives in the e2e layer, not here. }

interface

uses
  blaise.testing, strutils,
  Bindgen.Model, Bindgen.Emit;

type
  TEmitTests = class(TTestCase)
  private
    FModel: TCModel;
    function Emit: string;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestEmit_UnitSkeleton;
    procedure TestEmit_Function_ExternalWithLibAndName;
    procedure TestEmit_Function_PointerReturnSynthesisesAlias;
    procedure TestEmit_Procedure_ForVoidReturn;
    procedure TestEmit_Typedef_MappedType;
    procedure TestEmit_Typedef_CaseInsensitiveSelfAlias_Skipped;
    procedure TestEmit_EnumAlias_AndMemberConsts;
    procedure TestEmit_Record_WithMappedFields;
    procedure TestEmit_OpaqueRecord_EmptyRecord;
    procedure TestEmit_Variadic_EmittedWithVarargs;
    procedure TestEmit_ReservedWordParam_Renamed;
    procedure TestEmit_UnnamedParam_Synthesised;
    procedure TestEmit_PtrAliases_PrecedeOtherTypes;
    procedure TestEmit_CDeclOrder_Preserved;
    procedure TestEmit_UnknownAliasTarget_DegradesToPointer;
    procedure TestEmit_UnknownTypedefRHS_DegradesToPointer;
    procedure TestEmit_Union_ExactSizeRawArray;
    procedure TestEmit_Union_Uncomputable_Placeholder;
    procedure TestEmit_UnionAccessor_InterfaceAndBody;
    procedure TestEmit_UnionAccessor_ArrayMemberSkipped;
    procedure TestEmit_UnionAccessor_UsesTypedefName;
    procedure TestEmit_FnPtrTypedef_ProceduralType;
    procedure TestEmit_InlineFnPtrParam_SynthesisedType;
    procedure TestEmit_VariadicFnPtrTypedef_DegradesToPointer;
    procedure TestEmit_UnresolvedByValueParam_FunctionSkipped;
  end;

implementation

procedure TEmitTests.SetUp;
var
  R: TCRecord;
  E: TCEnum;
  F: TCFunction;
begin
  { A miniature Xlib-flavoured model covering every emission shape. }
  FModel := TCModel.Create();

  FModel.AddTypedef(TCTypedef.Create('XID', 'unsigned long'));
  FModel.AddTypedef(TCTypedef.Create('Display', 'struct _XDisplay'));

  R := TCRecord.Create('_XDisplay');
  FModel.AddRecord(R);

  R := TCRecord.Create('XPoint');
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('x', 'int'));
  R.Fields.Add(TCField.Create('serial', 'unsigned long'));
  R.Fields.Add(TCField.Create('name', 'const char *'));
  FModel.AddRecord(R);

  E := TCEnum.Create('XOrientation');
  E.Members.Add(TCEnumMember.Create('XOrientVertical', 0));
  E.Members.Add(TCEnumMember.Create('XOrientHorizontal', 5));
  FModel.AddEnum(E);

  F := TCFunction.Create('XOpenDisplay');
  F.ReturnCType := 'Display *';
  F.Params.Add(TCParam.Create('display_name', 'const char *'));
  FModel.AddFunction(F);

  F := TCFunction.Create('XFlushNothing');
  F.ReturnCType := 'void';
  FModel.AddFunction(F);

  F := TCFunction.Create('XVariadicThing');
  F.ReturnCType := 'int';
  F.Params.Add(TCParam.Create('mode', 'int'));
  F.IsVariadic := True;
  FModel.AddFunction(F);

  F := TCFunction.Create('XReserved');
  F.ReturnCType := 'int';
  F.Params.Add(TCParam.Create('type', 'int'));
  F.Params.Add(TCParam.Create('', 'double'));
  FModel.AddFunction(F);
end;

procedure TEmitTests.TearDown;
begin
  FModel := nil;
end;

function TEmitTests.Emit: string;
begin
  Result := EmitBinding(FModel, 'x11', 'X11');
end;

procedure TEmitTests.TestEmit_UnitSkeleton;
var
  Src: string;
begin
  Src := Self.Emit();
  AssertTrue('unit clause', ContainsStr(Src, 'unit x11;'));
  AssertTrue('interface', ContainsStr(Src, 'interface'));
  AssertTrue('implementation', ContainsStr(Src, 'implementation'));
  AssertTrue('do-not-edit marker', ContainsStr(Src, 'DO NOT EDIT'));
end;

procedure TEmitTests.TestEmit_Function_ExternalWithLibAndName;
begin
  AssertTrue(ContainsStr(Self.Emit(),
    'function XOpenDisplay(display_name: PChar): PDisplay; cdecl; ' +
    'external ''X11'' name ''XOpenDisplay'';'));
end;

procedure TEmitTests.TestEmit_Function_PointerReturnSynthesisesAlias;
begin
  AssertTrue(ContainsStr(Self.Emit(), 'PDisplay = ^Display;'));
end;

procedure TEmitTests.TestEmit_Procedure_ForVoidReturn;
begin
  AssertTrue(ContainsStr(Self.Emit(),
    'procedure XFlushNothing; cdecl; external ''X11'' name ''XFlushNothing'';'));
end;

procedure TEmitTests.TestEmit_Typedef_MappedType;
begin
  AssertTrue(ContainsStr(Self.Emit(), 'XID = UInt64;'));
end;

procedure TEmitTests.TestEmit_Typedef_CaseInsensitiveSelfAlias_Skipped;
var
  R: TCRecord;
  F: TCFunction;
  Src: string;
begin
  { ncurses: 'typedef struct screen SCREEN;' — the struct tag 'screen'
    and the typedef 'SCREEN' differ only in case.  Pascal folds identifier
    case, so the opaque record already declares the name; the typedef is a
    redundant self-alias and must be skipped, not re-emitted as
    'SCREEN = screen;' (a duplicate type declaration). }
  R := TCRecord.Create('screen');
  FModel.AddRecord(R);
  FModel.AddTypedef(TCTypedef.Create('SCREEN', 'struct screen'));
  { A function taking 'SCREEN *' (ncurses' delscreen) synthesises the
    pointer alias — it must still be emitted, referencing the SCREEN name
    which folds to the opaque 'screen' record. }
  F := TCFunction.Create('delscreen');
  F.ReturnCType := 'void';
  F.Params.Add(TCParam.Create('sp', 'SCREEN *'));
  FModel.AddFunction(F);
  Src := Self.Emit();
  AssertTrue('opaque record for the tag',
    ContainsStr(Src, 'screen = record end;'));
  AssertTrue('no case-colliding self-alias',
    not ContainsStr(Src, 'SCREEN = screen;'));
  AssertTrue('pointer alias still emitted',
    ContainsStr(Src, 'PSCREEN = ^SCREEN;'));
end;

procedure TEmitTests.TestEmit_EnumAlias_AndMemberConsts;
var
  Src: string;
begin
  Src := Self.Emit();
  AssertTrue('alias', ContainsStr(Src, 'XOrientation = Integer;'));
  AssertTrue('implicit member', ContainsStr(Src, 'XOrientVertical = 0;'));
  AssertTrue('explicit member', ContainsStr(Src, 'XOrientHorizontal = 5;'));
end;

procedure TEmitTests.TestEmit_Record_WithMappedFields;
var
  Src: string;
begin
  Src := Self.Emit();
  AssertTrue('record open', ContainsStr(Src, 'XPoint = record'));
  AssertTrue('int field', ContainsStr(Src, 'x: Integer;'));
  AssertTrue('unsigned long field', ContainsStr(Src, 'serial: UInt64;'));
  AssertTrue('char* field', ContainsStr(Src, 'name: PChar;'));
end;

procedure TEmitTests.TestEmit_OpaqueRecord_EmptyRecord;
begin
  AssertTrue(ContainsStr(Self.Emit(), '_XDisplay = record end;'));
end;

procedure TEmitTests.TestEmit_Variadic_EmittedWithVarargs;
var
  Src: string;
begin
  { Since the compiler's 'varargs' directive landed, variadic functions
    are emitted as callable declarations, not skipped. }
  Src := Self.Emit();
  AssertTrue(ContainsStr(Src,
    'function XVariadicThing(mode: Integer): Integer; cdecl; varargs; ' +
    'external ''X11'' name ''XVariadicThing'';'));
end;

procedure TEmitTests.TestEmit_ReservedWordParam_Renamed;
begin
  AssertTrue(ContainsStr(Self.Emit(), 'type_: Integer'));
end;

procedure TEmitTests.TestEmit_UnnamedParam_Synthesised;
begin
  AssertTrue(ContainsStr(Self.Emit(), 'a1: Double'));
end;

procedure TEmitTests.TestEmit_PtrAliases_PrecedeOtherTypes;
var
  Src: string;
begin
  { Forward pointer declarations are legal in Blaise, so the synthetic
    aliases go first — a record field may reference one. }
  Src := Self.Emit();
  AssertTrue('alias before typedefs',
    Pos('PDisplay = ^Display;', Src) < Pos('XID = UInt64;', Src));
end;

procedure TEmitTests.TestEmit_CDeclOrder_Preserved;
var
  Src: string;
begin
  { XID was declared before XPoint in C; a field of a later record may
    reference an earlier typedef, so C order must be preserved. }
  Src := Self.Emit();
  AssertTrue('typedef before record',
    Pos('XID = UInt64;', Src) < Pos('XPoint = record', Src));
end;

procedure TEmitTests.TestEmit_UnknownAliasTarget_DegradesToPointer;
var
  F: TCFunction;
  Src: string;
begin
  { A parameter typed 'struct __va_list_tag *' synthesises an alias to
    a struct declared in a FILTERED-OUT system header.  The alias must
    degrade to an untyped Pointer, not reference an undeclared name. }
  F := TCFunction.Create('XUsesHidden');
  F.ReturnCType := 'int';
  F.Params.Add(TCParam.Create('va', 'struct __va_list_tag *'));
  FModel.AddFunction(F);
  Src := Self.Emit();
  AssertTrue('degraded', ContainsStr(Src, 'P__va_list_tag = Pointer;'));
  AssertTrue('no dangling ref', not ContainsStr(Src, '^__va_list_tag'));
end;

procedure TEmitTests.TestEmit_UnknownTypedefRHS_DegradesToPointer;
var
  Src: string;
begin
  { A typedef whose RHS names a type from a filtered-out header cannot
    be emitted verbatim — the name does not exist in the unit. }
  FModel.AddTypedef(TCTypedef.Create('MysteryHandle', 'struct hidden_tag *'));
  Src := Self.Emit();
  AssertTrue(ContainsStr(Src, 'Phidden_tag = Pointer;'));
end;

procedure TEmitTests.TestEmit_Union_ExactSizeRawArray;
var
  R: TCRecord;
  Src: string;
begin
  { XEvent-style union of int + long[24] = 192 bytes; by-value use
    demands the exact size, so it becomes a 24-element UInt64 array
    (which also carries the C union's 8-byte alignment). }
  R := TCRecord.Create('_XSampleEvent');
  R.IsUnion := True;
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('type', 'int'));
  R.Fields.Add(TCField.Create('pad', 'long[24]'));
  FModel.AddRecord(R);
  Src := Self.Emit();
  AssertTrue('record emitted', ContainsStr(Src, '_XSampleEvent = record'));
  AssertTrue('raw array', ContainsStr(Src, 'raw: array[0..23] of UInt64;'));
end;

procedure TEmitTests.TestEmit_Union_Uncomputable_Placeholder;
var
  R: TCRecord;
  Src: string;
begin
  R := TCRecord.Create('BadUnion');
  R.IsUnion := True;
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('m', 'struct never_declared'));
  FModel.AddRecord(R);
  Src := Self.Emit();
  AssertTrue(ContainsStr(Src, 'BadUnion = record end;'));
end;

procedure TEmitTests.TestEmit_UnionAccessor_InterfaceAndBody;
var
  R: TCRecord;
  Src: string;
begin
  { Blaise has no variant records, so each union member gets a typed
    accessor: XEvent_xkey(ev)^.keycode style. }
  R := TCRecord.Create('XSampleEvent');
  R.IsUnion := True;
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('kind', 'int'));
  R.Fields.Add(TCField.Create('pt', 'XPoint'));
  FModel.AddRecord(R);
  Src := Self.Emit();
  AssertTrue('scalar accessor decl', ContainsStr(Src,
    'function XSampleEvent_kind(var AUnion: XSampleEvent): PInteger;'));
  AssertTrue('record accessor decl', ContainsStr(Src,
    'function XSampleEvent_pt(var AUnion: XSampleEvent): PXPoint;'));
  AssertTrue('body cast', ContainsStr(Src, 'Result := PXPoint(@AUnion);'));
  AssertTrue('PInteger alias', ContainsStr(Src, 'PInteger = ^Integer;'));
end;

procedure TEmitTests.TestEmit_UnionAccessor_ArrayMemberSkipped;
var
  R: TCRecord;
  Src: string;
begin
  R := TCRecord.Create('XSampleEvent');
  R.IsUnion := True;
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('kind', 'int'));
  R.Fields.Add(TCField.Create('pad', 'long[24]'));
  FModel.AddRecord(R);
  Src := Self.Emit();
  AssertTrue('scalar member has accessor',
    ContainsStr(Src, 'function XSampleEvent_kind'));
  AssertTrue('array member has none',
    not ContainsStr(Src, 'function XSampleEvent_pad'));
end;

procedure TEmitTests.TestEmit_UnionAccessor_UsesTypedefName;
var
  R: TCRecord;
  Src: string;
begin
  { A union tag _XEvent typedef'd to XEvent — accessors must carry the
    friendly typedef name, not the tag. }
  R := TCRecord.Create('_XEvent');
  R.IsUnion := True;
  R.IsComplete := True;
  R.Fields.Add(TCField.Create('kind', 'int'));
  FModel.AddRecord(R);
  FModel.AddTypedef(TCTypedef.Create('XEvent', 'union _XEvent'));
  Src := Self.Emit();
  AssertTrue('typedef-named accessor', ContainsStr(Src,
    'function XEvent_kind(var AUnion: XEvent): PInteger;'));
  AssertTrue('tag-named accessor absent',
    not ContainsStr(Src, 'function _XEvent_kind'));
end;

procedure TEmitTests.TestEmit_FnPtrTypedef_ProceduralType;
var
  Src: string;
begin
  FModel.AddTypedef(TCTypedef.Create('XErrorHandler',
    'int (*)(Display *, int)'));
  Src := Self.Emit();
  AssertTrue(ContainsStr(Src,
    'XErrorHandler = function(a0: PDisplay; a1: Integer): Integer;'));
end;

procedure TEmitTests.TestEmit_InlineFnPtrParam_SynthesisedType;
var
  F: TCFunction;
  Src: string;
begin
  F := TCFunction.Create('XIfThing');
  F.ReturnCType := 'int';
  F.Params.Add(TCParam.Create('predicate', 'int (*)(Display *, XID)'));
  FModel.AddFunction(F);
  Src := Self.Emit();
  AssertTrue('synth type declared', ContainsStr(Src,
    'TXIfThing_predicate = function(a0: PDisplay; a1: XID): Integer;'));
  AssertTrue('param uses it', ContainsStr(Src,
    'XIfThing(predicate: TXIfThing_predicate)'));
end;

procedure TEmitTests.TestEmit_VariadicFnPtrTypedef_DegradesToPointer;
var
  Src: string;
begin
  FModel.AddTypedef(TCTypedef.Create('XVaHandler', 'int (*)(Display *, ...)'));
  Src := Self.Emit();
  AssertTrue(ContainsStr(Src, 'XVaHandler = Pointer;'));
end;

procedure TEmitTests.TestEmit_UnresolvedByValueParam_FunctionSkipped;
var
  F: TCFunction;
  Src: string;
begin
  { fopencookie takes cookie_io_functions_t BY VALUE — a type declared
    in a filtered-out header.  Unlike a pointer, a by-value unknown
    cannot degrade (its size/ABI class is unknown), so the function is
    skipped with a note rather than emitted broken. }
  F := TCFunction.Create('fopencookie');
  F.ReturnCType := 'int';
  F.Params.Add(TCParam.Create('io_funcs', 'cookie_io_functions_t'));
  FModel.AddFunction(F);
  Src := Self.Emit();
  AssertTrue('no declaration', not ContainsStr(Src, 'function fopencookie('));
  AssertTrue('skip note names the type',
    ContainsStr(Src, 'cookie_io_functions_t'));
end;

initialization
  RegisterTest(TEmitTests);

end.
