{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ uSemanticExport — produces a self-contained TUnitInterface from a
  source TUnit that has already had uSemantic.AnalyseUnit run on it.

  Pipeline position:
    uUnitLoader.LoadOne  → parsed TUnit
    uSemantic.AnalyseUnit → TUnit + populated TSymbolTable
    uSemanticExport.Export → TUnitInterface (this unit)

  After Export returns, the caller may free the source TUnit; the
  returned TUnitInterface is self-contained.  See uUnitInterface
  unit header for the full discipline.

  Phase 2 scope (current): structural carry-over.
    - Name / SourceFile / UsedUnits
    - Interface-section type declarations  → TTypeEntry (Def cloned)
    - Interface-section const declarations → TConstEntry
    - Interface-section free routines      → TRoutineSig

  Phase 3+ scope (not yet):
    - InstanceSize / VTableLayout / class-method export
    - Inline-body extraction (impl-side body paired with intf sig)
    - Generic-body extraction
    - Cross-unit type-ref resolution against ADeps
    - Forward-declared class impl-side completion }

unit uSemanticExport;

interface

uses
  Classes, Contnrs, uAST, uSymbolTable, uUnitInterface, uCompilerId,
  uUnitInterfaceIO, blaise.codegen;

{ Build a TUnitInterface from AUnit.  AUnit must have been semantically
  analysed already.  ADeps holds the already-exported interfaces of
  every unit listed in AUnit's interface uses clause, in any order.

  ASymbolTable is optional.  Pass the table populated by
  TSemanticAnalyser.AnalyseUnitForExport(AUnit) when you want
  VTableSlot / InstanceSize / resolved type info to flow into the
  produced TUnitInterface.  Pass nil to skip — the artifact still
  builds, just without semantic-derived fields. }
function ExportUnitInterface(AUnit:        TUnit;
                             ADeps:        TObjectList;
                             ASymbolTable: TSymbolTable = nil)
                             : TUnitInterface;

implementation

{ ----- Type-reference resolution ---------------------------------

  Given a type name appearing in a declaration, figure out which unit
  owns it.  Search order:
    1. The unit currently being exported (local types take precedence)
    2. The supplied dependencies
    3. Fall back to '$builtin'

  This is intentionally name-based for Phase 2 — no TTypeDesc
  introspection.  Good enough to populate TQualTypeRef correctly for
  the common cases; classes that need full resolution against
  TSymbolTable will revisit this in Phase 3. }

function ResolveTypeRef(const ATypeName: string;
                        AIface:          TUnitInterface;
                        ADeps:           TObjectList)
                        : TQualTypeRef;
var
  I: Integer;
begin
  if ATypeName = '' then
  begin
    Result := MakeQualRef('', '');
    Exit;
  end;

  if AIface.FindType(ATypeName) <> nil then
  begin
    Result := MakeLocalRef(ATypeName);
    Exit;
  end;

  if ADeps <> nil then
    for I := 0 to ADeps.Count - 1 do
      if TUnitInterface(ADeps.Items[I]).FindType(ATypeName) <> nil then
      begin
        Result := MakeQualRef(TUnitInterface(ADeps.Items[I]).Name, ATypeName);
        Exit;
      end;

  Result := MakeBuiltinRef(ATypeName);
end;

{ ----- Per-declaration builders ---------------------------------- }

{ Populate the class-specific fields of a TTypeEntry from its
  TClassTypeDef.  Parent and implements references are resolved
  against ADeps (and the in-progress AIface for forward-references
  inside the same unit).  Methods are exported as TRoutineSig — no
  bodies; downstream consumers re-emit them from the class
  declaration when instantiating the class. }
procedure PopulateClassEntry(AEntry:       TTypeEntry;
                             ASrc:         TClassTypeDef;
                             AIface:       TUnitInterface;
                             ADeps:        TObjectList;
                             ASymbolTable: TSymbolTable);
var
  I:        Integer;
  M:        TMethodDecl;
  Sig:      TRoutineSig;
  IRef:     TQualTypeRef;
  TypeDesc: TTypeDesc;
begin
  AEntry.ParentClass := ResolveTypeRef(ASrc.ParentName, AIface, ADeps);

  for I := 0 to ASrc.ImplementsNames.Count - 1 do
  begin
    IRef := ResolveTypeRef(ASrc.ImplementsNames.Strings[I], AIface, ADeps);
    if IRef.UnitName = '' then
      AEntry.Implements.Add(IRef.TypeName)
    else
      AEntry.Implements.Add(IRef.UnitName + '.' + IRef.TypeName);
  end;

  for I := 0 to ASrc.Attributes.Count - 1 do
    AEntry.Attributes.Add(ASrc.Attributes.Strings[I]);

  for I := 0 to ASrc.Methods.Count - 1 do
  begin
    M   := TMethodDecl(ASrc.Methods.Items[I]);
    Sig := BuildRoutineSig(M, AIface, ADeps);
    AEntry.Methods.Add(Sig);
  end;

  { InstanceSize — read the resolved TRecordTypeDesc from the
    symbol table.  Without a symbol table (parse-only export) this
    stays 0. }
  if ASymbolTable <> nil then
  begin
    TypeDesc := ASymbolTable.FindType(AEntry.Name);
    if (TypeDesc <> nil) and (TypeDesc is TRecordTypeDesc) then
      AEntry.InstanceSize := TRecordTypeDesc(TypeDesc).TotalSize();
  end;

  { VTableLayout: TRoutineSig.VTableSlot is populated by
    BuildRoutineSig from the source TMethodDecl.  Pre-semantic every
    slot is -1; once AnalyseUnitForExport has run, slot indices are
    filled in. }
end;

procedure PopulateRecordMethods(AEntry: TTypeEntry;
                                ASrc:   TRecordTypeDef;
                                AIface: TUnitInterface;
                                ADeps:  TObjectList);
var
  I:   Integer;
  M:   TMethodDecl;
  Sig: TRoutineSig;
begin
  for I := 0 to ASrc.Methods.Count - 1 do
  begin
    M   := TMethodDecl(ASrc.Methods.Items[I]);
    Sig := BuildRoutineSig(M, AIface, ADeps);
    AEntry.Methods.Add(Sig);
  end;
end;

{ Locate the enum declared in this interface that has AMember as a member.
  Returns its entry name in ATypeName and the member's ordinal in AOrdinal;
  False when no exported enum declares that member.  The base enum of an
  enum-member subrange is always declared BEFORE the subrange in the same
  interface section, so by the time the subrange's entry is built its enum
  entry is already in AIface. }
function FindEnumMemberOwner(AIface: TUnitInterface;
                             const AMember: string;
                             out ATypeName: string;
                             out AOrdinal: Int64): Boolean;
var
  I, J: Integer;
  E:    TTypeEntry;
  ED:   TEnumTypeDef;
begin
  Result    := False;
  ATypeName := '';
  AOrdinal  := 0;
  if AIface = nil then Exit;
  for I := 0 to AIface.Types.Count - 1 do
  begin
    E := TTypeEntry(AIface.Types.Items[I]);
    if not (E.Def is TEnumTypeDef) then Continue;
    ED := TEnumTypeDef(E.Def);
    for J := 0 to ED.Members.Count - 1 do
      if SameText(ED.Members.Strings[J], AMember) then
      begin
        ATypeName := E.Name;
        AOrdinal  := ED.OrdinalAt(J);
        Exit(True);
      end;
  end;
end;

{ Give an enum-member subrange alias entry a RESOLVED base: the base enum's
  name in TypeName and the members' ordinals as the bounds.  A no-op for every
  other alias form, and for a subrange whose base is not an enum exported by
  this same interface (the cold path diagnoses those).

  Resolution runs off the exported ENUM entries rather than the symbol table,
  so it does not depend on the analyser having run — which also keeps the
  .bif writer usable from a parse-only path. }
procedure ResolveEnumSubrangeAliasForExport(AEntry: TTypeEntry;
                                            AIface: TUnitInterface);
var
  AliasDef: TTypeAliasDef;
  LoName, HiName: string;
  LoOrd,  HiOrd:  Int64;
begin
  if not (AEntry.Def is TTypeAliasDef) then Exit;
  AliasDef := TTypeAliasDef(AEntry.Def);
  if not AliasDef.IsSubrange then Exit;
  { Only the enum-member form — the integer form already carries a base name
    and has round-tripped since .bif v8. }
  if AliasDef.SubrangeLowName = '' then Exit;
  if AliasDef.TypeName <> '' then Exit;

  if not FindEnumMemberOwner(AIface, AliasDef.SubrangeLowName, LoName, LoOrd) then
    Exit;
  if not FindEnumMemberOwner(AIface, AliasDef.SubrangeHighName, HiName, HiOrd) then
    Exit;
  { Bounds from two different enums, or descending, are cold-path errors —
    leave the entry unresolved rather than encode something incoherent. }
  if not SameText(LoName, HiName) then Exit;
  if HiOrd < LoOrd then Exit;

  AliasDef.TypeName     := LoName;
  AliasDef.SubrangeLow  := LoOrd;
  AliasDef.SubrangeHigh := HiOrd;
end;

function BuildTypeEntry(ASrc:         TTypeDecl;
                        AIface:       TUnitInterface;
                        ADeps:        TObjectList;
                        ASymbolTable: TSymbolTable): TTypeEntry;
var
  GenDef:   TGenericTypeDef;
  GenRecDef: TGenericRecordDef;
begin
  Result := TTypeEntry.Create();
  Result.Name := ASrc.Name;
  Result.Def  := CloneTypeDef(ASrc.Def);
  Result.IsClass   := ASrc.Def is TClassTypeDef;
  { A generic RECORD is a generic too.  Flagging only TGenericTypeDef (the
    generic CLASS form) meant a generic record template declared in a unit
    interface was exported as an ordinary type, so the consumer never
    registered it as a template and reported "Unknown type 'TPair<Integer>'"
    on the cached path (BUG-20260919-clonetypedef-generic-record-in-unit). }
  Result.IsGeneric := (ASrc.Def is TGenericTypeDef) or
                      (ASrc.Def is TGenericRecordDef);

  { An ENUM-MEMBER subrange (type TMid = eB..eC) is the one alias form the
    parser cannot give a base NAME: it leaves TypeName empty and records the
    two member names instead, which the semantic pass resolves to a base enum
    plus ordinals.  The .bif alias record has no slot for those names, so the
    consumer saw a blank base and failed with "Type alias TMid = : base not
    found" (BUG-20260922-enum-subrange-bif-import-fails).

    Resolve it HERE and write the fully-resolved form the record can already
    carry: the base ENUM's name in TypeName plus the resolved ordinal bounds.
    The member names have already done their job by this point (the cold build
    validated same-enum and ascending), so nothing checkable is lost, and no
    new .bif field is needed.  Mutating Result.Def is safe — it is a clone,
    not the AST node. }
  ResolveEnumSubrangeAliasForExport(Result, AIface);

  if ASrc.Def is TClassTypeDef then
    PopulateClassEntry(Result, TClassTypeDef(ASrc.Def), AIface, ADeps, ASymbolTable)
  else if ASrc.Def is TRecordTypeDef then
    { Record methods (instance + static) export as TRoutineSig like class
      methods — without this, cached imports lost every record method
      (BUG-043 follow-on; .bif v13). }
    PopulateRecordMethods(Result, TRecordTypeDef(ASrc.Def), AIface, ADeps)
  else if ASrc.Def is TGenericTypeDef then
  begin
    { Generic class — the class body lives inside the wrapper. }
    GenDef := TGenericTypeDef(ASrc.Def);
    if GenDef.ClassDef <> nil then
      PopulateClassEntry(Result, GenDef.ClassDef, AIface, ADeps, ASymbolTable);
  end
  else if ASrc.Def is TGenericRecordDef then
  begin
    { Generic record — the record body lives inside the wrapper, exactly as a
      generic class's does.  Without this the entry carried NO method
      signatures, so the .bif writer emitted one body per template method while
      recording zero sigs; the reader then read zero bodies and ran off the end
      of the TYPE block ("missing END marker"). }
    GenRecDef := TGenericRecordDef(ASrc.Def);
    if GenRecDef.RecordDef <> nil then
      PopulateRecordMethods(Result, GenRecDef.RecordDef, AIface, ADeps);
  end;
end;

function BuildConstEntry(ASrc:        TConstDecl;
                         AIface:      TUnitInterface;
                         ADeps: TObjectList)
                         : TConstEntry;
begin
  Result := TConstEntry.Create();
  Result.Decl    := CloneConstDecl(ASrc);
  Result.TypeRef := ResolveTypeRef(ASrc.TypeName, AIface, ADeps);
end;

{ Locate impl-section TMethodDecl whose name matches AName.
  Returns nil if not found.  Used to pair interface-section forward
  decls (which carry no body) with their implementation. }
function FindImplBody(AUnit: TUnit; const AName: string): TMethodDecl;
var
  I: Integer;
  M: TMethodDecl;
begin
  Result := nil;
  if AUnit.ImplBlock = nil then Exit;
  for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
  begin
    M := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
    if SameText(M.Name, AName) then
    begin
      Result := M;
      Exit;
    end;
  end;
end;

function BuildRoutineSig(ASrc:        TMethodDecl;
                         AIface:      TUnitInterface;
                         ADeps: TObjectList)
                         : TRoutineSig;
var
  I:      Integer;
  PSrc:   TMethodParam;
  PCopy:  TMethodParam;
begin
  Result := TRoutineSig.Create();
  Result.Name         := ASrc.Name;
  Result.IsFunction   := ASrc.ReturnTypeName <> '';
  Result.IsInline     := ASrc.IsInline or ASrc.IsInlineCandidate;
  Result.IsPublished  := ASrc.IsPublished;
  Result.VTableSlot   := ASrc.VTableSlot;
  Result.IsExternal   := ASrc.IsExternal;
  Result.IsVarArgs    := ASrc.IsVarArgs;
  Result.ExternalName := ASrc.ExternalName;
  Result.CallingConv  := ASrc.CallingConv;
  Result.ResolvedQbeName := ASrc.ResolvedQbeName;
  Result.IsVirtual    := ASrc.IsVirtual;
  Result.IsOverride   := ASrc.IsOverride;
  { Carry static-ness so a cross-unit TypeName.StaticMethod() call resolves —
    VTableSlot alone cannot distinguish a static method from a final
    non-virtual instance method (both are -1). }
  Result.IsStatic     := ASrc.IsStatic;
  { Carry the `overload` directive so a cross-unit overload set whose members
    are split across an imported class and its ancestor is not truncated by
    ResolveMethodOverload's hiding walk (which stops at a non-overload). }
  Result.IsOverload   := ASrc.IsOverload;
  { Generic-method type params survive the .bif so the importer clones a
    real template (Phase 10: TList<T>.Map<R>). }
  if ASrc.TypeParams <> nil then
  begin
    Result.TypeParams := TStringList.Create();
    Result.TypeParams.AddStrings(ASrc.TypeParams);
    if ASrc.TypeParamConstraints <> nil then
    begin
      Result.TypeParamConstraints := TStringList.Create();
      Result.TypeParamConstraints.AddStrings(ASrc.TypeParamConstraints);
    end;
  end;
  { Carry visibility so cross-unit member access enforces private/protected. }
  Result.Visibility   := ASrc.Visibility;
  Result.ReturnType   := ResolveTypeRef(ASrc.ReturnTypeName, AIface, ADeps);

  for I := 0 to ASrc.Params.Count - 1 do
  begin
    PSrc  := TMethodParam(ASrc.Params.Items[I]);
    PCopy := CloneMethodParam(PSrc);
    Result.Params.Add(PCopy);
  end;
end;

{ ----- Walk passes ----------------------------------------------- }

{ Forward-declared class merging: a `type TFoo = class;` in the
  interface section parses to a TClassTypeDef with empty Fields and
  Methods.  The full body is in the implementation section.  For
  separate compilation the exported interface must carry the full
  body — locate the impl-side completion and substitute it.

  This is the documented impl-leak (see TUnitInterface unit header). }
function FindImplClassCompletion(AUnit: TUnit;
                                 const AName: string): TClassTypeDef;
var
  I: Integer;
  D: TTypeDecl;
begin
  Result := nil;
  if AUnit.ImplBlock = nil then Exit;
  for I := 0 to AUnit.ImplBlock.TypeDecls.Count - 1 do
  begin
    D := TTypeDecl(AUnit.ImplBlock.TypeDecls.Items[I]);
    if not SameText(D.Name, AName) then Continue;
    if D.Def is TClassTypeDef then
    begin
      Result := TClassTypeDef(D.Def);
      Exit;
    end;
  end;
end;

function IsForwardClass(ADef: TClassTypeDef): Boolean;
begin
  Result := (ADef.Fields.Count = 0) and (ADef.Methods.Count = 0);
end;

procedure ExportTypes(AUnit:        TUnit;
                      AIface:       TUnitInterface;
                      ADeps:        TObjectList;
                      ASymbolTable: TSymbolTable);
var
  I:        Integer;
  Decl:     TTypeDecl;
  ClassDef: TClassTypeDef;
  ImplDef:  TClassTypeDef;
  Entry:    TTypeEntry;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
  begin
    Decl := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);

    if Decl.Def is TClassTypeDef then
    begin
      ClassDef := TClassTypeDef(Decl.Def);
      if IsForwardClass(ClassDef) then
      begin
        ImplDef := FindImplClassCompletion(AUnit, Decl.Name);
        if ImplDef <> nil then
        begin
          Entry := TTypeEntry.Create();
          Entry.Name    := Decl.Name;
          Entry.Def     := CloneClassTypeDef(ImplDef);
          Entry.IsClass := True;
          PopulateClassEntry(Entry, ImplDef, AIface, ADeps, ASymbolTable);
          AIface.AddType(Entry);
          Continue;
        end;
      end;
    end;

    AIface.AddType(BuildTypeEntry(Decl, AIface, ADeps, ASymbolTable));
  end;
end;

procedure ExportVars(AUnit:  TUnit;
                     AIface: TUnitInterface;
                     ADeps:  TObjectList);
var
  I, J:  Integer;
  Decl:  TVarDecl;
  Entry: TVarEntry;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(AUnit.IntfBlock.Decls.Items[I]);
    for J := 0 to Decl.Names.Count - 1 do
    begin
      Entry := TVarEntry.Create();
      Entry.Name        := Decl.Names.Strings[J];
      Entry.TypeRef     := ResolveTypeRef(Decl.TypeName, AIface, ADeps);
      Entry.IsThreadVar := Decl.IsThreadVar;
      AIface.AddVar(Entry);
    end;
  end;
end;

procedure ExportConsts(AUnit:       TUnit;
                       AIface:      TUnitInterface;
                       ADeps: TObjectList);
var
  I:    Integer;
  Decl: TConstDecl;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.ConstDecls.Count - 1 do
  begin
    Decl := TConstDecl(AUnit.IntfBlock.ConstDecls.Items[I]);
    AIface.AddConst(BuildConstEntry(Decl, AIface, ADeps));
  end;
end;

procedure ExportRoutines(AUnit:       TUnit;
                         AIface:      TUnitInterface;
                         ADeps: TObjectList);
var
  I:    Integer;
  Decl: TMethodDecl;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
    AIface.AddRoutine(BuildRoutineSig(Decl, AIface, ADeps));
  end;
end;

{ Pair interface-section inline routines with their impl-side body
  and stash the cloned Block as a TInlineBody. }
procedure ExportInlineBodies(AUnit: TUnit; AIface: TUnitInterface);
var
  I:        Integer;
  Decl:     TMethodDecl;
  ImplDecl: TMethodDecl;
  Body:     TInlineBody;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
    if not Decl.IsInline then Continue;
    if Decl.TypeParams <> nil then Continue;  { generic handled below }

    ImplDecl := FindImplBody(AUnit, Decl.Name);
    if ImplDecl = nil then Continue;
    if ImplDecl.Body = nil then Continue;

    Body := TInlineBody.Create();
    Body.RoutineName := Decl.Name;
    Body.Block       := CloneBlock(ImplDecl.Body);
    AIface.AddInlineBody(Body);
  end;
end;

{ Pair interface-section generic routine declarations with their
  impl-side body, and emit TGenericBody entries for generic types
  (whose Def is TGenericTypeDef). }
procedure ExportGenericBodies(AUnit: TUnit; AIface: TUnitInterface);
var
  I:        Integer;
  Decl:     TMethodDecl;
  ImplDecl: TMethodDecl;
  TDecl:    TTypeDecl;
  GenDef:   TGenericTypeDef;
  GBody:    TGenericBody;
  J:        Integer;
begin
  if AUnit.IntfBlock = nil then Exit;

  { Generic free routines. }
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
    if Decl.TypeParams = nil then Continue;

    ImplDecl := FindImplBody(AUnit, Decl.Name);
    if ImplDecl = nil then Continue;
    if ImplDecl.Body = nil then Continue;

    GBody := TGenericBody.Create();
    GBody.Name       := Decl.Name;
    GBody.IsType     := False;
    GBody.RoutineSig := BuildRoutineSig(Decl, AIface, nil);
    GBody.Body       := CloneBlock(ImplDecl.Body);
    { Clone the impl-side TMethodDecl (with body) so the AST template
      is self-contained.  CloneMethodDecl owns the body it copies. }
    GBody.MethodDecl := CloneMethodDecl(ImplDecl);
    for J := 0 to Decl.TypeParams.Count - 1 do
    begin
      GBody.TypeParams.Add(Decl.TypeParams.Strings[J]);
      if Decl.TypeParamConstraints <> nil then
        GBody.Constraints.Add(Decl.TypeParamConstraints.Strings[J])
      else
        GBody.Constraints.Add('');
    end;
    AIface.AddGenericBody(GBody);
  end;

  { Generic types — Def is already cloned into the TTypeEntry; we
    just register the parallel TGenericBody for body access. }
  for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
  begin
    TDecl := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
    if not (TDecl.Def is TGenericTypeDef) then Continue;

    GenDef := TGenericTypeDef(TDecl.Def);
    GBody := TGenericBody.Create();
    GBody.Name    := TDecl.Name;
    GBody.IsType  := True;
    GBody.TypeDef := CloneTypeDef(TDecl.Def);
    for J := 0 to GenDef.ParamNames.Count - 1 do
    begin
      GBody.TypeParams.Add(GenDef.ParamNames.Strings[J]);
      if GenDef.ParamConstraints <> nil then
        GBody.Constraints.Add(GenDef.ParamConstraints.Strings[J])
      else
        GBody.Constraints.Add('');
    end;
    AIface.AddGenericBody(GBody);
  end;
end;

procedure CopyUsedUnits(AUnit: TUnit; AIface: TUnitInterface);
var
  I: Integer;
begin
  if AUnit.UsedUnits <> nil then
    for I := 0 to AUnit.UsedUnits.Count - 1 do
      AIface.UsedUnits.Add(AUnit.UsedUnits.Strings[I]);
  if AUnit.ImplUsedUnits <> nil then
    for I := 0 to AUnit.ImplUsedUnits.Count - 1 do
      AIface.ImplUsedUnits.Add(AUnit.ImplUsedUnits.Strings[I]);
  { Link libraries — hoisted from every 'external ''lib''' decl (interface or
    implementation), deduped.  Carries the unit's link dependencies into the
    .bif even when the importing routine is implementation-private. }
  if AUnit.LinkLibs <> nil then
    for I := 0 to AUnit.LinkLibs.Count - 1 do
      if AIface.LinkLibs.IndexOf(TLinkLibDecl(AUnit.LinkLibs.Items[I]).LibName) < 0 then
        AIface.LinkLibs.Add(TLinkLibDecl(AUnit.LinkLibs.Items[I]).LibName);
  AIface.HasInitialization :=
    (AUnit.InitStmts <> nil) and (AUnit.InitStmts.Count > 0);
  { The fini flag mirrors the codegen-side emission predicate EXACTLY (shared
    UnitNeedsFini): the unit's own object exports <Unit>_fini iff this is
    True, and the driver emits the main_exit call iff this is True — one
    predicate, no drift. }
  AIface.HasFinalization := UnitNeedsFini(AUnit);
end;

{ ----- Top-level ------------------------------------------------- }

function ExportUnitInterface(AUnit:        TUnit;
                             ADeps:        TObjectList;
                             ASymbolTable: TSymbolTable): TUnitInterface;
begin
  Result := TUnitInterface.Create(AUnit.Name);
  Result.SourceFile    := AUnit.SourceFile;
  Result.CompilerId    := EffectiveCompilerId();
  { mtime + hash get populated by the iface writer once it has a
    handle on the source path on disk.  Doing it here from AUnit
    alone is unsafe — AUnit may have been parsed from a string
    source or stdin and never had a backing file. }

  CopyUsedUnits(AUnit, Result);

  { Types FIRST — subsequent passes' ResolveTypeRef calls need to be
    able to find local types in the index. }
  ExportTypes   (AUnit, Result, ADeps, ASymbolTable);
  ExportConsts  (AUnit, Result, ADeps);
  ExportVars    (AUnit, Result, ADeps);
  ExportRoutines(AUnit, Result, ADeps);

  ExportInlineBodies (AUnit, Result);
  ExportGenericBodies(AUnit, Result);
end;

end.
