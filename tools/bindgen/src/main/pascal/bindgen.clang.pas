{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ bindgen — clang AST JSON → C declaration model.

  Consumes the output of
      clang -Xclang -ast-dump=json -fsyntax-only header.h
  and harvests the top-level declarations into a TCModel.

  Format notes (verified against clang 18):
    - loc.file is only present when the file CHANGES between decls;
      the loader carries it as sticky state.  Macro-expanded decls
      bury the file inside loc.expansionLoc / loc.spellingLoc.
    - A typedef of an anonymous struct body to Name emits an unnamed
      RecordDecl followed by a TypedefDecl whose underlying type is
      'struct Name' — the record adopts the typedef name and the
      redundant typedef is dropped.
    - EnumConstantDecl carries a ConstantExpr child with the value
      only when the C source has an explicit initialiser; implicit
      values continue from the previous member.
    - Function return types are recovered from the qualType prefix
      before the parameter list's opening parenthesis.  (Functions
      returning a raw function pointer would defeat this; in practice
      such returns go through a typedef name, which is fine.) }

unit Bindgen.Clang;

interface

uses
  SysUtils, StrUtils, generics.collections,
  Json.Types, Json.Reader,
  Bindgen.Model, Bindgen.TypeMap;

{ Harvest a parsed clang AST.  AFileMatch: comma-separated substrings;
  only declarations from files whose path contains at least one of them
  are kept ('zlib.h,zconf.h').  '' keeps everything.  Real headers pull
  their typedefs from sibling headers, so multiple matches are the
  norm, not the exception. }
function LoadClangAST(ARoot: TJSONData; const AFileMatch: string): TCModel;

{ Convenience wrapper: parse AJsonText then harvest. }
function LoadClangASTText(const AJsonText: string; const AFileMatch: string): TCModel;

implementation

function GetStr(AObj: TJSONObject; const AName: string): string;
var
  D: TJSONData;
begin
  Result := '';
  D := AObj.Find(AName);
  if D <> nil then
    Result := D.AsString;
end;

function GetBool(AObj: TJSONObject; const AName: string): Boolean;
var
  D: TJSONData;
begin
  Result := False;
  D := AObj.Find(AName);
  if D <> nil then
    Result := D.AsBoolean;
end;

function GetQualType(AObj: TJSONObject): string;
var
  T: TJSONData;
begin
  Result := '';
  T := AObj.Find('type');
  if T is TJSONObject then
    Result := GetStr(TJSONObject(T), 'qualType');
end;

{ Extract the file from a loc object; macro-expanded decls carry it
  inside expansionLoc/spellingLoc. }
function LocFile(ALoc: TJSONData): string;
var
  Obj: TJSONObject;
  Sub: TJSONData;
begin
  Result := '';
  if not (ALoc is TJSONObject) then Exit;
  Obj := TJSONObject(ALoc);
  Result := GetStr(Obj, 'file');
  if Result <> '' then Exit;
  Sub := Obj.Find('expansionLoc');
  if Sub <> nil then
  begin
    Result := LocFile(Sub);
    if Result <> '' then Exit;
  end;
  Sub := Obj.Find('spellingLoc');
  if Sub <> nil then
    Result := LocFile(Sub);
end;

{ Search a node's direct and nested children for the first ConstantExpr
  carrying a 'value' — how clang reports an explicit enum initialiser. }
function FindConstantValue(ANode: TJSONObject; var AValue: Int64): Boolean;
var
  Inner: TJSONData;
  Arr: TJSONArray;
  I: Int;
  Child: TJSONObject;
  ValStr: string;
begin
  Result := False;
  Inner := ANode.Find('inner');
  if not (Inner is TJSONArray) then Exit;
  Arr := TJSONArray(Inner);
  for I := 0 to Arr.Count - 1 do
  begin
    if not (Arr[I] is TJSONObject) then Continue;
    Child := TJSONObject(Arr[I]);
    if (GetStr(Child, 'kind') = 'ConstantExpr') and Child.Contains('value') then
    begin
      ValStr := GetStr(Child, 'value');
      AValue := StrToInt64Def(ValStr, 0);
      Result := True;
      Exit;
    end;
    { The initialiser can sit below an implicit cast — recurse. }
    if FindConstantValue(Child, AValue) then
    begin
      Result := True;
      Exit;
    end;
  end;
end;

{ Size in bytes of a bitfield's base type, or 0 if unknown.  Bitfield
  bases are integer builtins by C rules. }
function BitfieldUnitSize(const ACType: string): Int;
var
  S: string;
begin
  S := StripQualifiers(ACType);
  S := ReplaceAll(S, 'unsigned ', '');
  S := ReplaceAll(S, 'signed ', '');
  S := Trim(S);
  if (S = 'char') or (S = '_Bool') then Result := 1
  else if S = 'short' then Result := 2
  else if (S = 'int') or (S = 'unsigned') then Result := 4
  else if (S = 'long') or (S = 'long long') or (S = 'long int') then Result := 8
  else Result := 0;
end;

{ Collapse each run of consecutive bitfields into one synthetic field
  of the run's base type — '__bits<n>: unsigned int' — so the layout
  calculator and emitter only ever see plain fields.  A run closes on
  a non-bitfield, a base-type size change, unit overflow, or an
  explicit ':0' separator (all also unit breaks in C).  The member
  names and widths are preserved in the synthetic field's Note. }
procedure CollapseBitfields(ARec: TCRecord);
var
  OutFields: TList<TCField>;
  I: Int;
  F: TCField;
  Group: TCField;
  InGroup: Boolean;
  UnitSize: Int;
  BitsUsed: Int;
  GroupIdx: Int;
  Sz: Int;
  Any: Boolean;
begin
  { Fast path: nothing to do for the vast majority of records. }
  Any := False;
  for I := 0 to ARec.Fields.Count - 1 do
    if ARec.Fields[I].IsBitfield then
      Any := True;
  if not Any then Exit;

  OutFields := TList<TCField>.Create();
  Group := nil;
  InGroup := False;
  UnitSize := 0;
  BitsUsed := 0;
  GroupIdx := 0;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := ARec.Fields[I];
    if not F.IsBitfield then
    begin
      InGroup := False;
      OutFields.Add(F);
      Continue;
    end;
    Sz := BitfieldUnitSize(F.CType);
    if (Sz = 0) or (F.BitWidth = 0) then
    begin
      { Unknown base or a ':0' separator: close the unit.  A zero-width
        field itself is never emitted. }
      InGroup := False;
      if Sz = 0 then
        OutFields.Add(F);   { unknown base — leave visible, will surface }
      Continue;
    end;
    if InGroup and
       ((Sz <> UnitSize) or (BitsUsed + F.BitWidth > UnitSize * 8)) then
      InGroup := False;
    if not InGroup then
    begin
      Group := TCField.Create('__bits' + IntToStr(GroupIdx), F.CType);
      GroupIdx := GroupIdx + 1;
      Group.Note := 'C bitfields:';
      OutFields.Add(Group);
      InGroup := True;
      UnitSize := Sz;
      BitsUsed := 0;
    end;
    if F.Name <> '' then
      Group.Note := Group.Note + ' ' + F.Name + ':' + IntToStr(F.BitWidth)
    else
      Group.Note := Group.Note + ' (pad):' + IntToStr(F.BitWidth);
    BitsUsed := BitsUsed + F.BitWidth;
  end;
  ARec.Fields := OutFields;
end;

{ Load ARec's fields.  A nested unnamed RecordDecl (an anonymous union
  or struct used as a field's type) is LIFTED into the model as its own
  record named 'anon_<n>' — added to the model BEFORE the outer record
  so the emitter's declare-before-use order holds — and the field that
  references it (qualType contains '(unnamed' / '(anonymous') is
  retyped to the lifted name.  RenameLiftedRecords gives them readable
  names once the outer record's own name is final. }
procedure LoadRecordFields(ANode: TJSONObject; ARec: TCRecord; AModel: TCModel);
var
  Inner: TJSONData;
  Arr: TJSONArray;
  I: Int;
  Child: TJSONObject;
  QT: string;
  Lifted: TCRecord;
  LastLifted: string;
  Fld: TCField;
  Width: Int64;
  AnonByQT: TDictionary<string, string>;
  LiftedName: string;
begin
  LastLifted := '';
  AnonByQT := TDictionary<string, string>.Create();
  Inner := ANode.Find('inner');
  if not (Inner is TJSONArray) then Exit;
  Arr := TJSONArray(Inner);
  for I := 0 to Arr.Count - 1 do
  begin
    if not (Arr[I] is TJSONObject) then Continue;
    Child := TJSONObject(Arr[I]);
    if (GetStr(Child, 'kind') = 'RecordDecl') and
       GetBool(Child, 'completeDefinition') then
    begin
      { Nested record declarations are file-scope in C semantics.  A
        NAMED one (XImage's 'struct funcs') keeps its tag — the field
        references it by name; an unnamed one gets a counter name and
        the referencing field(s) are retyped to it. }
      if GetStr(Child, 'name') <> '' then
        Lifted := TCRecord.Create(GetStr(Child, 'name'))
      else
        Lifted := TCRecord.Create('anon_' + IntToStr(AModel.Records.Count));
      Lifted.IsUnion := GetStr(Child, 'tagUsed') = 'union';
      Lifted.IsComplete := True;
      LoadRecordFields(Child, Lifted, AModel);
      AModel.AddRecord(Lifted);
      if GetStr(Child, 'name') = '' then
        LastLifted := Lifted.Name;
    end
    else if GetStr(Child, 'kind') = 'FieldDecl' then
    begin
      QT := GetQualType(Child);
      if (Pos('(unnamed', QT) >= 0) or (Pos('(anonymous', QT) >= 0) then
      begin
        { The XSizeHints pattern declares SEVERAL fields against one
          anonymous struct ('min_aspect, max_aspect') — every such
          field carries the same location-unique qualType, so the
          first binds it to the freshly lifted record and the rest
          resolve through the map. }
        if LastLifted <> '' then
        begin
          AnonByQT.Add(QT, LastLifted);
          QT := LastLifted;
          LastLifted := '';
        end
        else if AnonByQT.TryGetValue(QT, LiftedName) then
          QT := LiftedName;
      end;
      Fld := TCField.Create(GetStr(Child, 'name'), QT);
      if GetBool(Child, 'isBitfield') then
      begin
        Fld.IsBitfield := True;
        Width := 0;
        if FindConstantValue(Child, Width) then
          Fld.BitWidth := Int32(Width);
      end;
      ARec.Fields.Add(Fld);
    end;
  end;
  CollapseBitfields(ARec);
end;

{ Post-pass: rename lifted 'anon_<n>' records to '<Owner>_<field>_t'
  now that owner names are final (an anonymous typedef'd struct only
  receives its name from the later TypedefDecl). }
procedure RenameLiftedRecords(AModel: TCModel);
var
  I, J: Int;
  R: TCRecord;
  Lifted: TCRecord;
  NewName: string;
  Renames: TDictionary<string, string>;
begin
  { Pass 1: rename each lifted record after the FIRST field that
    references it, recording old→new.  (Records is in lifted-before-
    owner order, so a doubly-nested anon member keeps its counter
    name — rare; still compiles.) }
  Renames := TDictionary<string, string>.Create();
  for I := 0 to AModel.Records.Count - 1 do
  begin
    R := AModel.Records[I];
    if StartsStr('anon_', R.Name) then Continue;
    for J := 0 to R.Fields.Count - 1 do
    begin
      if not StartsStr('anon_', R.Fields[J].CType) then Continue;
      if Renames.ContainsKey(R.Fields[J].CType) then Continue;
      Lifted := AModel.FindRecord(R.Fields[J].CType);
      if Lifted = nil then Continue;
      NewName := R.Name + '_' + R.Fields[J].Name + '_t';
      Renames.Add(Lifted.Name, NewName);
      Lifted.Name := NewName;
    end;
  end;
  { Pass 2: retype EVERY field that referenced a renamed record — the
    XSizeHints pattern has several fields sharing one lifted type. }
  for I := 0 to AModel.Records.Count - 1 do
  begin
    R := AModel.Records[I];
    for J := 0 to R.Fields.Count - 1 do
      if Renames.TryGetValue(R.Fields[J].CType, NewName) then
        R.Fields[J].CType := NewName;
  end;
end;

function LoadEnum(ANode: TJSONObject; AModel: TCModel): TCEnum;
var
  E: TCEnum;
  Inner: TJSONData;
  Arr: TJSONArray;
  I: Int;
  Child: TJSONObject;
  NextValue: Int64;
  Explicit: Int64;
begin
  E := TCEnum.Create(GetStr(ANode, 'name'));
  AModel.AddEnum(E);
  Result := E;
  NextValue := 0;
  Inner := ANode.Find('inner');
  if not (Inner is TJSONArray) then Exit;
  Arr := TJSONArray(Inner);
  for I := 0 to Arr.Count - 1 do
  begin
    if not (Arr[I] is TJSONObject) then Continue;
    Child := TJSONObject(Arr[I]);
    if GetStr(Child, 'kind') <> 'EnumConstantDecl' then Continue;
    Explicit := 0;
    if FindConstantValue(Child, Explicit) then
      NextValue := Explicit;
    E.Members.Add(TCEnumMember.Create(GetStr(Child, 'name'), NextValue));
    NextValue := NextValue + 1;
  end;
end;

procedure LoadFunction(ANode: TJSONObject; AModel: TCModel);
var
  F: TCFunction;
  QT: string;
  ParenPos: Int;
  Inner: TJSONData;
  Arr: TJSONArray;
  I: Int;
  Child: TJSONObject;
begin
  if GetStr(ANode, 'storageClass') = 'static' then Exit;
  F := TCFunction.Create(GetStr(ANode, 'name'));
  QT := GetQualType(ANode);
  ParenPos := Pos('(', QT);
  if ParenPos >= 0 then
    F.ReturnCType := Trim(LeftStr(QT, ParenPos))
  else
    F.ReturnCType := QT;
  F.IsVariadic := GetBool(ANode, 'variadic');
  Inner := ANode.Find('inner');
  if Inner is TJSONArray then
  begin
    Arr := TJSONArray(Inner);
    for I := 0 to Arr.Count - 1 do
    begin
      if not (Arr[I] is TJSONObject) then Continue;
      Child := TJSONObject(Arr[I]);
      if GetStr(Child, 'kind') = 'ParmVarDecl' then
        F.Params.Add(TCParam.Create(GetStr(Child, 'name'), GetQualType(Child)));
    end;
  end;
  AModel.AddFunction(F);
end;

{ Handle a TypedefDecl.  ALastAnon / ALastAnonEnum are the immediately
  preceding unnamed complete RecordDecl / EnumDecl, if any — the
  anonymous-body-typedef pattern.  clang labels the anonymous body's
  tag with the typedef's own name ('struct Name' / 'enum Name'), so a
  tag equal to the typedef name marks that pattern. }
procedure LoadTypedef(ANode: TJSONObject; AModel: TCModel;
  var ALastAnon: TCRecord; var ALastAnonEnum: TCEnum);
var
  Name: string;
  QT: string;
  Tag: string;
  R: TCRecord;
begin
  Name := GetStr(ANode, 'name');
  QT := GetQualType(ANode);
  if StartsStr('struct ', QT) or StartsStr('union ', QT) then
  begin
    Tag := QT;
    if StartsStr('struct ', Tag) then
      Tag := Trim(MidStr(Tag, 7, Length(Tag)))
    else
      Tag := Trim(MidStr(Tag, 6, Length(Tag)));
    if Tag = Name then
    begin
      { The record carries the name; the typedef is redundant. }
      R := AModel.FindRecord(Name);
      if (R = nil) and (ALastAnon <> nil) then
      begin
        ALastAnon.Name := Name;
        ALastAnon := nil;
      end;
      Exit;
    end;
  end;
  if StartsStr('enum ', QT) then
  begin
    Tag := Trim(MidStr(QT, 5, Length(QT)));
    if Tag = Name then
    begin
      { The enum adopts the name (its 'Name = Integer;' alias is
        emitted by the enum path); the typedef is redundant. }
      if ALastAnonEnum <> nil then
      begin
        ALastAnonEnum.Name := Name;
        ALastAnonEnum := nil;
      end;
      Exit;
    end;
  end;
  AModel.AddTypedef(TCTypedef.Create(Name, QT));
end;

procedure LoadRecord(ANode: TJSONObject; AModel: TCModel; var ALastAnon: TCRecord);
var
  Name: string;
  R: TCRecord;
  IsNew: Boolean;
begin
  Name := GetStr(ANode, 'name');
  R := nil;
  if Name <> '' then
    R := AModel.FindRecord(Name);
  IsNew := R = nil;
  if IsNew then
    R := TCRecord.Create(Name);
  R.IsUnion := GetStr(ANode, 'tagUsed') = 'union';
  if GetBool(ANode, 'completeDefinition') then
  begin
    R.IsComplete := True;
    R.Fields.Clear();
    { Loading fields may lift nested anonymous records into the model;
      adding R afterwards keeps them BEFORE R in declaration order. }
    LoadRecordFields(ANode, R, AModel);
  end;
  if IsNew then
    AModel.AddRecord(R);
  if (Name = '') and R.IsComplete then
    ALastAnon := R
  else
    ALastAnon := nil;
end;

function MatchesAny(const AFile: string; AMatches: TList<String>): Boolean;
var
  I: Int;
begin
  Result := AMatches.Count = 0;
  for I := 0 to AMatches.Count - 1 do
    if Pos(AMatches[I], AFile) >= 0 then
    begin
      Result := True;
      Exit;
    end;
end;

function LoadClangAST(ARoot: TJSONData; const AFileMatch: string): TCModel;
var
  Root: TJSONObject;
  Inner: TJSONData;
  Arr: TJSONArray;
  I: Int;
  Node: TJSONObject;
  Kind: string;
  CurFile: string;
  F: string;
  LastAnon: TCRecord;
  LastAnonEnum: TCEnum;
  E: TCEnum;
  Matches: TList<String>;
begin
  Result := TCModel.Create();
  if AFileMatch = '' then
    Matches := TList<String>.Create()
  else
    Matches := SplitChar(AFileMatch, Ord(','));
  if not (ARoot is TJSONObject) then Exit;
  Root := TJSONObject(ARoot);
  Inner := Root.Find('inner');
  if not (Inner is TJSONArray) then Exit;
  Arr := TJSONArray(Inner);
  CurFile := '';
  LastAnon := nil;
  LastAnonEnum := nil;
  for I := 0 to Arr.Count - 1 do
  begin
    if not (Arr[I] is TJSONObject) then Continue;
    Node := TJSONObject(Arr[I]);
    F := LocFile(Node.Find('loc'));
    if F <> '' then
      CurFile := F;
    if GetBool(Node, 'isImplicit') then Continue;
    if not MatchesAny(CurFile, Matches) then Continue;
    Kind := GetStr(Node, 'kind');
    if Kind = 'TypedefDecl' then
      LoadTypedef(Node, Result, LastAnon, LastAnonEnum)
    else if Kind = 'RecordDecl' then
    begin
      LoadRecord(Node, Result, LastAnon);
      LastAnonEnum := nil;
    end
    else if Kind = 'EnumDecl' then
    begin
      E := LoadEnum(Node, Result);
      if E.Name = '' then
        LastAnonEnum := E
      else
        LastAnonEnum := nil;
      LastAnon := nil;
    end
    else if Kind = 'FunctionDecl' then
    begin
      LoadFunction(Node, Result);
      LastAnon := nil;
      LastAnonEnum := nil;
    end;
  end;
  RenameLiftedRecords(Result);
end;

function LoadClangASTText(const AJsonText: string; const AFileMatch: string): TCModel;
var
  Root: TJSONData;
begin
  Root := GetJSON(AJsonText);
  Result := LoadClangAST(Root, AFileMatch);
end;

end.
