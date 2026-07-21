{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ bindgen — C declaration model → Blaise binding unit source.

  Emission order: a mapping pre-pass walks the whole model so the type
  mapper discovers every synthetic pointer alias, then the type section
  is emitted with those aliases FIRST (Blaise allows forward pointer
  declarations — verified) followed by the type declarations in their
  original C order, which C's declare-before-use rule makes valid
  Pascal order too.  Enum members become consts; each C function
  becomes a cdecl external routine that names both the library and the
  C symbol.

  Deliberate slice-1 gaps (marked in the output):
    - variadic functions are skipped (not callable from Blaise)
    - unions get a placeholder record usable only through pointers
    - function-pointer typedefs degrade to untyped Pointer }

unit Bindgen.Emit;

interface

uses
  SysUtils, StrUtils, generics.collections, classes,
  Bindgen.Model, Bindgen.TypeMap, Bindgen.Layout, Bindgen.Macros;

{ Render AModel as a complete Blaise unit named AUnitName whose external
  declarations link against ALibName.  The AMacros overload also emits
  harvested #define constants (integer values and simple strings) into
  the const section; macros without a folded value are skipped. }
function EmitBinding(AModel: TCModel; const AUnitName, ALibName: string): string; overload;
function EmitBinding(AModel: TCModel; const AUnitName, ALibName: string;
  AMacros: TList<TCMacro>): string; overload;

{ Make a C identifier safe as a Blaise identifier: reserved words get a
  trailing underscore; an empty name becomes 'a<index>'. }
function SanitiseIdent(const AName: string; AIndex: Integer): string;

implementation

const
  { The Blaise lexer's keyword set (uLexer.MapKeyword), plus 'string'
    and 'result' which collide with the builtin type / function-result
    variable.  Space-delimited for a simple membership test. }
  ReservedWords =
    ' PROGRAM USES VAR THREADVAR BEGIN END ASM TYPE RECORD PACKED CLASS' +
    ' PROCEDURE FUNCTION DIV MOD IF THEN ELSE WHILE DO FOR TO DOWNTO' +
    ' REPEAT UNTIL TRY FINALLY EXCEPT RAISE NIL UNIT INTERFACE' +
    ' IMPLEMENTATION VIRTUAL OVERRIDE IS AS AND OR NOT EXIT BREAK CONTINUE' +
    ' CASE OF ARRAY SET IN SHL SHR SAR XOR CONST OUT CONSTRUCTOR' +
    ' DESTRUCTOR INHERITED INITIALIZATION FINALIZATION STRING RESULT ';

function IsReservedWord(const AName: string): Boolean;
begin
  Result := Pos(' ' + UpperCase(AName) + ' ', ReservedWords) >= 0;
end;

function SanitiseIdent(const AName: string; AIndex: Integer): string;
begin
  if AName = '' then
  begin
    Result := 'a' + IntToStr(AIndex);
    Exit;
  end;
  Result := AName;
  if IsReservedWord(Result) then
    Result := Result + '_';
end;

{ The Blaise type for one function parameter.  An inline function
  pointer synthesises a named procedural type hinted by function and
  parameter name; everything else goes through plain Map.  Called from
  BOTH the pre-pass and emission so the two see identical types. }
function ParamTypeName(F: TCFunction; AIndex: Integer;
  AMapper: TTypeMapper): string;
var
  Hint: string;
begin
  if Pos('(*)', F.Params[AIndex].CType) >= 0 then
  begin
    Hint := F.Params[AIndex].Name;
    if Hint = '' then
      Hint := 'a' + IntToStr(AIndex);
    Result := AMapper.MapCallback(F.Params[AIndex].CType, F.Name + '_' + Hint);
  end
  else
    Result := AMapper.Map(F.Params[AIndex].CType);
end;

{ The Blaise right-hand side for one typedef.  A representable
  function-pointer typedef becomes an inline procedural type. }
function TypedefRhs(T: TCTypedef; AMapper: TTypeMapper): string;
begin
  if Pos('(*)', T.CType) >= 0 then
  begin
    Result := AMapper.FnPtrDecl(T.CType);
    if Result <> '' then Exit;
  end;
  Result := AMapper.Map(T.CType);
end;

{ True when a union member can get a typed accessor: its mapped type
  is a plain name (not an array or inline construct). }
function AccessibleMemberType(AMapper: TTypeMapper; const ACType: string;
  var AMapped: string): Boolean;
begin
  AMapped := AMapper.Map(ACType);
  Result := (AMapped <> '') and (Pos(' ', AMapped) < 0) and
    (Pos('(', AMapped) < 0) and (Pos('^', AMapped) < 0);
end;

procedure PreMapModel(AModel: TCModel; AMapper: TTypeMapper);
var
  I, J: Integer;
  R: TCRecord;
  F: TCFunction;
  Hint: string;
begin
  { Walk everything once so the mapper registers every pointer alias
    and synthesised procedural type before any line is emitted. }
  for I := 0 to AModel.Typedefs.Count - 1 do
    TypedefRhs(AModel.Typedefs[I], AMapper);
  for I := 0 to AModel.Records.Count - 1 do
  begin
    R := AModel.Records[I];
    for J := 0 to R.Fields.Count - 1 do
    begin
      AMapper.Map(R.Fields[J].CType);
      { Union member accessors return P<member> — register the alias
        now so it is emitted with the others. }
      if R.IsUnion and R.IsComplete and
         AccessibleMemberType(AMapper, R.Fields[J].CType, Hint) then
        AMapper.MapPointerTo(R.Fields[J].CType);
    end;
  end;
  for I := 0 to AModel.Functions.Count - 1 do
  begin
    F := AModel.Functions[I];
    if F.IsVariadic then Continue;
    AMapper.Map(F.ReturnCType);
    for J := 0 to F.Params.Count - 1 do
      ParamTypeName(F, J, AMapper);
  end;
end;

{ A C union becomes a record with a single 'raw' array of its exact
  byte size, so by-value use (XEvent!) reserves the right amount of
  stack.  UInt64 elements when the size allows carry the union's usual
  8-byte alignment.  Blaise has no variant records, so each nameable
  member additionally gets a typed accessor function —
  'XEvent_xkey(ev)^.keycode' — declared with the externals and
  implemented as a pointer cast. }
{ The name user code should see for a record: the first typedef that
  aliases its tag ('XEvent' for 'union _XEvent'), else the tag itself. }
function FriendlyRecordName(AModel: TCModel; R: TCRecord): string;
var
  I: Integer;
  T: TCTypedef;
begin
  Result := R.Name;
  for I := 0 to AModel.Typedefs.Count - 1 do
  begin
    T := AModel.Typedefs[I];
    if (T.CType = 'union ' + R.Name) or (T.CType = 'struct ' + R.Name) then
    begin
      Result := T.Name;
      Exit;
    end;
  end;
end;

procedure EmitUnion(R: TCRecord; AModel: TCModel; AMapper: TTypeMapper;
  ATypeLines, AFuncLines, AImplLines: TStringList);
var
  Size, Align: Integer;
  J: Integer;
  Members: string;
  Mapped: string;
  PtrName: string;
  AccName: string;
  ViewName: string;
begin
  if not RecordSizeAlign(AModel, R, Size, Align) then
  begin
    ATypeLines.Add('  ' + R.Name + ' = record end; { TODO: C union of ' +
      'unknown size — placeholder, only valid through pointers }');
    Exit;
  end;
  Members := '';
  for J := 0 to R.Fields.Count - 1 do
  begin
    if J > 0 then Members := Members + ', ';
    Members := Members + R.Fields[J].Name;
  end;
  ATypeLines.Add('  ' + R.Name + ' = record { C union (' +
    IntToStr(Size) + ' bytes): ' + Members + ' }');
  if (Size mod 8) = 0 then
    ATypeLines.Add('    raw: array[0..' + IntToStr((Size div 8) - 1) +
      '] of UInt64;')
  else
    ATypeLines.Add('    raw: array[0..' + IntToStr(Size - 1) + '] of Byte;');
  ATypeLines.Add('  end;');

  { Accessor declarations come after the whole type section, so the
    friendlier typedef alias (XEvent, not _XEvent) is already legal. }
  ViewName := FriendlyRecordName(AModel, R);
  for J := 0 to R.Fields.Count - 1 do
  begin
    if not AccessibleMemberType(AMapper, R.Fields[J].CType, Mapped) then
      Continue;
    PtrName := AMapper.MapPointerTo(R.Fields[J].CType);
    AccName := ViewName + '_' + SanitiseIdent(R.Fields[J].Name, J);
    AFuncLines.Add('function ' + AccName + '(var AUnion: ' + ViewName +
      '): ' + PtrName + '; { typed view of C union member ''' +
      R.Fields[J].Name + ''' }');
    AImplLines.Add('function ' + AccName + '(var AUnion: ' + ViewName +
      '): ' + PtrName + ';');
    AImplLines.Add('begin');
    AImplLines.Add('  Result := ' + PtrName + '(@AUnion);');
    AImplLines.Add('end;');
    AImplLines.Add('');
  end;
end;

procedure EmitRecord(R: TCRecord; AModel: TCModel; AMapper: TTypeMapper;
  ATypeLines, AFuncLines, AImplLines: TStringList);
var
  J: Integer;
begin
  if R.Name = '' then Exit;  { anonymous and never typedef-named }
  if not R.IsComplete then
  begin
    ATypeLines.Add('  ' + R.Name + ' = record end; { opaque }');
    Exit;
  end;
  if R.IsUnion then
  begin
    EmitUnion(R, AModel, AMapper, ATypeLines, AFuncLines, AImplLines);
    Exit;
  end;
  ATypeLines.Add('  ' + R.Name + ' = record');
  for J := 0 to R.Fields.Count - 1 do
    if R.Fields[J].Note <> '' then
      ATypeLines.Add('    ' + SanitiseIdent(R.Fields[J].Name, J) + ': ' +
        AMapper.Map(R.Fields[J].CType) + '; { ' + R.Fields[J].Note + ' }')
    else
      ATypeLines.Add('    ' + SanitiseIdent(R.Fields[J].Name, J) + ': ' +
        AMapper.Map(R.Fields[J].CType) + ';');
  ATypeLines.Add('  end;');
end;

const
  { Blaise builtin type names (uSymbolTable.RegisterBuiltins) — valid
    type references even though the unit does not declare them. }
  BuiltinTypeNames =
    ' INTEGER INT64 UINT32 CARDINAL UINT64 QWORD PTRUINT SMALLINT INT16' +
    ' WORD UINT16 BYTE BOOLEAN POINTER PCHAR DOUBLE SINGLE ';

function KnownTypeName(ADeclared: TSet<string>; const AName: string): Boolean;
begin
  Result := ADeclared.Contains(UpperCase(AName)) or
    (Pos(' ' + UpperCase(AName) + ' ', BuiltinTypeNames) >= 0);
end;

{ True when AMapped is a bare identifier (not an array/pointer form)
  that no declaration in this unit will satisfy. }
function IsUnresolvedName(ADeclared: TSet<string>; const AMapped: string): Boolean;
begin
  Result := (AMapped <> '') and (Pos(' ', AMapped) < 0) and
    (Pos('^', AMapped) < 0) and (not KnownTypeName(ADeclared, AMapped));
end;

procedure EmitTypedef(T: TCTypedef; AMapper: TTypeMapper;
  ATypeLines: TStringList; ADeclared: TSet<string>);
var
  Mapped: string;
begin
  Mapped := TypedefRhs(T, AMapper);
  if Mapped = '' then Exit;          { typedef of void — meaningless }
  { Self-alias — the record/tag already carries the name.  The compare is
    case-INSENSITIVE because Pascal folds identifier case: ncurses declares
    'typedef struct screen SCREEN;', so the opaque 'screen' record and the
    'SCREEN' typedef are the SAME Pascal identifier.  Re-emitting it as
    'SCREEN = screen;' is a duplicate type declaration (discussion #185). }
  if UpperCase(Mapped) = UpperCase(T.Name) then Exit;
  if StartsStr('function', Mapped) or StartsStr('procedure', Mapped) then
  begin
    ATypeLines.Add('  ' + T.Name + ' = ' + Mapped + ';');
    Exit;
  end;
  if IsUnresolvedName(ADeclared, Mapped) then
    ATypeLines.Add('  ' + T.Name + ' = Pointer; { unresolved C type ''' +
      T.CType + ''' — declared in a filtered-out header }')
  else if Pos('(*', T.CType) >= 0 then
    ATypeLines.Add('  ' + T.Name + ' = ' + Mapped +
      '; { C function pointer ' + T.CType + ' — variadic or ' +
      'unrepresentable, degraded }')
  else
    ATypeLines.Add('  ' + T.Name + ' = ' + Mapped + ';');
end;

procedure EmitEnum(E: TCEnum; ATypeLines, AConstLines: TStringList);
var
  J: Integer;
begin
  if E.Name <> '' then
    ATypeLines.Add('  ' + E.Name + ' = Integer;');
  for J := 0 to E.Members.Count - 1 do
    AConstLines.Add('  ' + E.Members[J].Name + ' = ' +
      IntToStr(E.Members[J].Value) + ';');
end;

procedure EmitFunction(F: TCFunction; const ALibName: string;
  AMapper: TTypeMapper; AFuncLines: TStringList; ADeclared: TSet<string>);
var
  J: Integer;
  ParamStr: string;
  Ret: string;
  Sig: string;
  Mapped: string;
begin
  { A signature referencing a type from a filtered-out header cannot be
    bound: a pointer would have degraded already, so what remains is a
    BY-VALUE use whose size/ABI class is unknown.  Skip with a note. }
  Ret := AMapper.Map(F.ReturnCType);
  if IsUnresolvedName(ADeclared, Ret) then
  begin
    AFuncLines.Add('{ ' + F.Name + ': skipped — return type ''' +
      F.ReturnCType + ''' comes from a filtered-out header }');
    Exit;
  end;
  for J := 0 to F.Params.Count - 1 do
  begin
    Mapped := ParamTypeName(F, J, AMapper);
    if IsUnresolvedName(ADeclared, Mapped) then
    begin
      AFuncLines.Add('{ ' + F.Name + ': skipped — parameter type ''' +
        F.Params[J].CType + ''' comes from a filtered-out header }');
      Exit;
    end;
  end;
  ParamStr := '';
  for J := 0 to F.Params.Count - 1 do
  begin
    if J > 0 then
      ParamStr := ParamStr + '; ';
    ParamStr := ParamStr + SanitiseIdent(F.Params[J].Name, J) + ': ' +
      ParamTypeName(F, J, AMapper);
  end;
  Ret := AMapper.Map(F.ReturnCType);
  if ParamStr <> '' then
    ParamStr := '(' + ParamStr + ')';
  if Ret = '' then
    Sig := 'procedure ' + F.Name + ParamStr
  else
    Sig := 'function ' + F.Name + ParamStr + ': ' + Ret;
  Sig := Sig + '; cdecl;';
  { A C-variadic function maps to the 'varargs' directive: call sites
    may pass extra C-passable arguments after the fixed parameters. }
  if F.IsVariadic then
    Sig := Sig + ' varargs;';
  AFuncLines.Add(Sig + ' external ''' + ALibName + ''' name ''' +
    F.Name + ''';');
end;

function EmitBinding(AModel: TCModel; const AUnitName, ALibName: string): string;
begin
  Result := EmitBinding(AModel, AUnitName, ALibName, nil);
end;

function EmitBinding(AModel: TCModel; const AUnitName, ALibName: string;
  AMacros: TList<TCMacro>): string;
var
  Mapper: TTypeMapper;
  Lines: TStringList;
  TypeLines: TStringList;
  ConstLines: TStringList;
  FuncLines: TStringList;
  ImplLines: TStringList;
  I, J: Integer;
  D: TCDecl;
  Declared: TSet<string>;
  MacroNames: TSet<string>;
  MName, MSuffix: string;
  Target: string;
begin
  Mapper := TTypeMapper.Create();
  Lines := TStringList.Create();
  TypeLines := TStringList.Create();
  ConstLines := TStringList.Create();
  FuncLines := TStringList.Create();
  ImplLines := TStringList.Create();

  PreMapModel(AModel, Mapper);

  { Every name this unit will declare (Pascal is case-insensitive). }
  Declared := TSet<string>.Create();
  for I := 0 to AModel.Records.Count - 1 do
    if AModel.Records[I].Name <> '' then
      Declared.Include(UpperCase(AModel.Records[I].Name));
  for I := 0 to AModel.Typedefs.Count - 1 do
    Declared.Include(UpperCase(AModel.Typedefs[I].Name));
  for I := 0 to AModel.Enums.Count - 1 do
    if AModel.Enums[I].Name <> '' then
      Declared.Include(UpperCase(AModel.Enums[I].Name));
  for I := 0 to Mapper.PtrAliases.Count - 1 do
    Declared.Include(UpperCase(Mapper.PtrAliases[I].Name));
  for I := 0 to Mapper.ProcTypes.Count - 1 do
    Declared.Include(UpperCase(Mapper.ProcTypes[I].Name));

  { Pointer aliases first: forward pointer declarations are legal, so
    this order is always safe regardless of where the targets sit.
    An alias whose target lives in a filtered-out header (e.g. a system
    struct) degrades to an untyped Pointer. }
  for I := 0 to Mapper.PtrAliases.Count - 1 do
  begin
    Target := Mapper.PtrAliases[I].Target;
    if KnownTypeName(Declared, Target) then
      TypeLines.Add('  ' + Mapper.PtrAliases[I].Name + ' = ^' + Target + ';')
    else
      TypeLines.Add('  ' + Mapper.PtrAliases[I].Name +
        ' = Pointer; { unresolved pointee ''' + Target + ''' }');
  end;

  { Remaining declarations in original C order (declare-before-use). }
  for I := 0 to AModel.Decls.Count - 1 do
  begin
    D := AModel.Decls[I];
    if D is TCRecord then
      EmitRecord(TCRecord(D), AModel, Mapper, TypeLines, FuncLines, ImplLines)
    else if D is TCTypedef then
      EmitTypedef(TCTypedef(D), Mapper, TypeLines, Declared)
    else if D is TCEnum then
      EmitEnum(TCEnum(D), TypeLines, ConstLines)
    else if D is TCFunction then
      EmitFunction(TCFunction(D), ALibName, Mapper, FuncLines, Declared);
  end;

  { Synthesised procedural types go LAST in the type section: they may
    reference any typedef, and only function declarations (which come
    after the whole type section) reference them. }
  for I := 0 to Mapper.ProcTypes.Count - 1 do
    TypeLines.Add('  ' + Mapper.ProcTypes[I].Name + ' = ' +
      Mapper.ProcTypes[I].Decl + ';');

  { -------- macro constants -------- }
  if AMacros <> nil then
  begin
    { Track every name the unit already uses so a macro that collides
      with a type, enum member, or function is skipped, not shadowed. }
    for I := 0 to AModel.Enums.Count - 1 do
      for J := 0 to AModel.Enums[I].Members.Count - 1 do
        Declared.Include(UpperCase(AModel.Enums[I].Members[J].Name));
    for I := 0 to AModel.Functions.Count - 1 do
      Declared.Include(UpperCase(AModel.Functions[I].Name));
    MacroNames := TSet<string>.Create();
    for I := 0 to AMacros.Count - 1 do
    begin
      { X.h defines True/False (= 1/0).  The Blaise builtins carry the
        same values, and a const would SHADOW them — 'Running := True'
        would suddenly assign an Integer.  Drop them. }
      if (UpperCase(AMacros[I].Name) = 'TRUE') or
         (UpperCase(AMacros[I].Name) = 'FALSE') then Continue;
      if not (AMacros[I].IsString or AMacros[I].HasValue) then Continue;
      MName := SanitiseIdent(AMacros[I].Name, I);
      MSuffix := '';
      if Declared.Contains(UpperCase(MName)) then
      begin
        { A case-insensitive twin (Pascal folds identifier case).  When
          the twin is another MACRO — keysymdef.h's XK_Q ($51) vs XK_q
          ($71) — the two are distinct C constants, and dropping this one
          silently rebinds its C name to the twin's value at Pascal use
          sites.  Rename it deterministically (append underscores until
          unique) and record the C name in a trailing comment.  A twin
          that is a type, enum member, or function stays skipped: there
          the macro is a redundant alias of the declaration, not a
          distinct constant. }
        if not MacroNames.Contains(UpperCase(MName)) then Continue;
        while Declared.Contains(UpperCase(MName)) do
          MName := MName + '_';
        MSuffix := '  { C name: ' + AMacros[I].Name + ' (case-collides) }';
      end;
      if AMacros[I].IsString then
        ConstLines.Add('  ' + MName + ' = ''' +
          ReplaceAll(AMacros[I].StrValue, '''', '''''') + ''';' + MSuffix)
      else
        ConstLines.Add('  ' + MName + ' = ' +
          IntToStr(AMacros[I].Value) + ';' + MSuffix);
      Declared.Include(UpperCase(MName));
      MacroNames.Include(UpperCase(MName));
    end;
  end;

  { -------- assemble -------- }
  Lines.Add('{ Unit ' + AUnitName + ' — Blaise binding for library ''' +
    ALibName + '''.');
  Lines.Add('  Generated by blaise-bindgen — DO NOT EDIT.');
  Lines.Add('  Regenerate with:  bindgen --header <header.h> --unit ' +
    AUnitName + ' --lib ' + ALibName + ' }');
  Lines.Add('');
  Lines.Add('unit ' + AUnitName + ';');
  Lines.Add('');
  Lines.Add('interface');
  Lines.Add('');
  if TypeLines.Count > 0 then
  begin
    Lines.Add('type');
    for I := 0 to TypeLines.Count - 1 do
      Lines.Add(TypeLines[I]);
    Lines.Add('');
  end;
  if ConstLines.Count > 0 then
  begin
    Lines.Add('const');
    for I := 0 to ConstLines.Count - 1 do
      Lines.Add(ConstLines[I]);
    Lines.Add('');
  end;
  for I := 0 to FuncLines.Count - 1 do
    Lines.Add(FuncLines[I]);
  Lines.Add('');
  Lines.Add('implementation');
  Lines.Add('');
  for I := 0 to ImplLines.Count - 1 do
    Lines.Add(ImplLines[I]);
  Lines.Add('end.');

  Result := Lines.Text;
end;

end.
