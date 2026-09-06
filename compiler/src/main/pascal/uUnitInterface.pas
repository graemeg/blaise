{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ TUnitInterface — self-contained, post-semantic description of a unit's
  interface section.

  Purpose: separate compilation.  After AnalyseUnitForExport returns a
  TUnitInterface for unit U, downstream compilation (semantic + codegen
  of units that 'uses U') must be able to proceed without keeping U's
  source TUnit alive.  That property is what later lets us serialise
  TUnitInterface to disk as a .bpu and skip parsing U entirely.

  Lifecycle:
    1. Source TUnit parsed by uUnitLoader.
    2. uSemantic.AnalyseUnitForExport(Source) -> TUnitInterface.
    3. Source TUnit may be freed; the interface remains valid.
    4. Held in TUnitLoader's cache, keyed by unit name.
    5. Consumed read-only by downstream semantic + codegen.
    6. Freed at compiler exit.

  Discipline:
    * No member of TUnitInterface holds a pointer into the source TUnit.
      AST subtrees stored here (inline bodies, generic bodies, type
      defs) are deep clones via CloneBlock / CloneTypeDecl.
    * All cross-unit type references travel as TQualTypeRef (unit name
      + type name), never as raw TTypeDesc pointers.
    * Immutable after AnalyseUnitForExport returns.  Threading later
      assumes reader-side concurrency over a frozen interface.

  Not in scope yet (Phase 5+):
    * SourceHash / CompilerVersion are reserved fields, populated as
      empty strings for now.  Used for .bpu staleness + schema checks
      once binary serialisation lands. }

unit uUnitInterface;

interface

uses
  Classes, Contnrs, uAST;

const
  { Sentinel unit-name values for TQualTypeRef.UnitName. }
  QUALREF_THIS_UNIT = '';
  QUALREF_BUILTIN   = '$builtin';

type
  { Name-qualified reference to a type.  Used wherever a TUnitInterface
    member would otherwise need a raw TTypeDesc pointer.  Resolution
    back to a concrete TTypeDesc happens in the consumer's symbol
    table, after the consumer's deps have been loaded. }
  TQualTypeRef = record
    UnitName: string;
    TypeName: string;
  end;

  { Free routine signature (no body).  Bodies, when needed by the
    consumer, live in TUnitInterface.InlineBodies / GenericBodies. }
  TRoutineSig = class
  public
    Name:         string;
    IsFunction:   Boolean;
    Params:       TObjectList;   { owned TMethodParam — cloned from source }
    ReturnType:   TQualTypeRef;  { TypeName = '' for procedures }
    IsInline:     Boolean;       { → InlineBodies has matching entry }
    IsPublished:  Boolean;       { set by parser on class methods inside
                                   a 'published' section; carries through
                                   for RTL MethodAddress lookups }
    IsExternal:   Boolean;
    IsVarArgs:    Boolean;       { C-variadic external ('varargs' directive) }
    ExternalName: string;
    CallingConv:  string;        { 'cdecl', 'stdcall', '' }
    VTableSlot:   Integer;       { -1 = static; >= 0 = vtable index.
                                   Populated by ExportUnitInterface
                                   only when AnalyseUnitForExport has
                                   run first.  Pre-semantic stays -1. }
    ResolvedQbeName: string;     { mangled symbol label.  For class
                                   methods: 'ClassName_MethodName'
                                   (with optional '$sig' suffix for
                                   overloads).  For free routines:
                                   'Name' (or 'Name$sig').  Used by
                                   importers to construct vtable
                                   ImplName ('$' + ResolvedQbeName)
                                   without re-running mangling. }
    IsVirtual:    Boolean;       { virtual method that allocates a new
                                   vtable slot }
    IsOverride:   Boolean;       { override that replaces a parent slot }
    IsStatic:     Boolean;       { static (class-level) method — takes no
                                   implicit Self.  VTableSlot is -1 for both
                                   static and final non-virtual instance
                                   methods, so this is a distinct flag rather
                                   than being inferred from the slot. }
    IsOverload:   Boolean;       { declared with the `overload` directive.
                                   ResolveMethodOverload's hiding walk stops at
                                   the first non-overload candidate, so this must
                                   survive the .bif or an overload set split
                                   across an imported class and its ancestor is
                                   truncated to the more-derived level. }
    Visibility:   TMemberVisibility; { member access scope; default mvPublic }
    TypeParams:   TStringList;   { owned; nil = not a generic method.  A
                                   generic METHOD on a (possibly generic)
                                   class keeps its own type-parameter list
                                   through the .bif so the importer's
                                   instantiation clones a real template
                                   (Phase 10: TList<T>.Map<R>). }
    TypeParamConstraints: TStringList; { owned; parallel; nil when none }
    constructor Create;
    destructor Destroy; override;
  end;

  { Const entry — wraps the cloned TConstDecl plus the resolved type. }
  TConstEntry = class
  public
    Decl:    TConstDecl;         { owned, cloned from source }
    TypeRef: TQualTypeRef;
    destructor Destroy; override;
  end;

  { Interface-section var (rare). }
  TVarEntry = class
  public
    Name:        string;
    TypeRef:     TQualTypeRef;
    IsThreadVar: Boolean;
  end;

  { Type entry.  Def carries the structural shape (TRecordTypeDef,
    TClassTypeDef, TEnumTypeDef, …) cloned from source.  The semantic
    metadata that downstream units actually need (parent class,
    instance size, vtable layout) is duplicated here in
    name-qualified form. }
  TTypeEntry = class
  public
    Name:         string;
    Def:          TASTTypeDef;    { owned, cloned from source }
    IsClass:      Boolean;
    IsGeneric:    Boolean;        { → GenericBodies has matching entry }
    ParentClass:  TQualTypeRef;   { for classes; both fields '' if none }
    Implements:   TStringList;    { owned — qualified 'Unit.Name' strings,
                                    or just 'Name' when in same unit }
    InstanceSize: Int64;          { 0 until set by AnalyseUnitForExport }
    Methods:      TObjectList;    { owned TRoutineSig — class/record methods }
    VTableLayout: TObjectList;    { non-owning refs to entries in Methods,
                                    indexed by VTableSlot }
    Attributes:   TStringList;    { custom attribute class names }
    constructor Create;
    destructor Destroy; override;
  end;

  { Inline routine body — kept as AST so consumer semantic can
    re-typecheck and codegen can inline at the call site. }
  TInlineBody = class
  public
    RoutineName: string;
    Block:       TBlock;          { owned, cloned from source }
    destructor Destroy; override;
  end;

  { Generic type or routine body — instantiated per concrete type-arg
    set by the consumer. }
  TGenericBody = class
  public
    Name:         string;
    TypeParams:   TStringList;    { owned — 'T', 'K', 'V', … }
    Constraints:  TStringList;    { owned — parallel to TypeParams,
                                    '' = unconstrained }
    IsType:       Boolean;        { True = generic type, False = generic routine }
    TypeDef:      TASTTypeDef;    { owned; non-nil when IsType }
    RoutineSig:   TRoutineSig;    { owned; non-nil when not IsType }
    Body:         TBlock;         { owned; non-nil when not IsType }
    MethodDecl:   TMethodDecl;    { owned; non-nil when not IsType.  Carries
                                    the cloned TMethodDecl that
                                    uSemantic.FGenericFuncTemplates uses as
                                    its template — lets uSemanticImport
                                    plumb generic free routines through
                                    TSymbolTable.RegisterGenericRoutine
                                    without synthesising an AST node at
                                    import time. }
    constructor Create;
    destructor Destroy; override;
  end;

  { The interface itself.  See unit header for lifecycle + discipline. }
  TUnitInterface = class
  private
    FTypeIndex:    TStringList;   { Name → TTypeEntry, case-insensitive }
    FConstIndex:   TStringList;   { Name → TConstEntry }
    FRoutineIndex: TStringList;   { Name → TRoutineSig (free routines) }
    FInlineIndex:  TStringList;   { RoutineName → TInlineBody }
    FGenericIndex: TStringList;   { Name → TGenericBody }
  public
    Name:            string;
    SourceFile:      string;      { absolute path the iface was compiled from }
    SourceHash:      string;      { content hash of SourceFile at compile time;
                                    used to detect "source edited since iface
                                    written".  Empty => not populated. }
    SourceModTime:   Int64;       { mtime of SourceFile (Unix epoch seconds) at
                                    compile time.  0 => not populated. }
    CompilerId:      string;      { identifier of the compiler that wrote this
                                    iface.  When source is unavailable, an
                                    exact CompilerId match is the only signal
                                    that the iface is safe to trust. }

    UsedUnits:       TStringList; { owned — interface-section uses, in order }
    ImplUsedUnits:   TStringList; { owned — implementation-section uses, in
                                    order.  Needed so an incremental rebuild
                                    that loads this unit from its cached .bif
                                    still pulls in (and links) impl-only
                                    dependencies. }
    LinkLibs:        TStringList; { owned — bare library names this unit must be
                                    linked against (deduped), hoisted from every
                                    'external ''lib''' decl, interface OR
                                    implementation.  An implementation-private
                                    import keeps its symbol out of the .bif but
                                    its library still propagates here, so a
                                    downstream program links it (-l<name> /
                                    <name>.dll). }
    HasInitialization: Boolean;   { unit has a non-empty initialization
                                    section.  An incremental rebuild loads this
                                    unit from its cached .bif and must still
                                    emit a call to <Unit>_init at program
                                    startup, or the init section never runs. }
    HasFinalization: Boolean;     { unit exports a <Unit>_fini procedure
                                    (user finalization section and/or managed
                                    module globals released per-unit — the
                                    shared UnitNeedsFini predicate).  The
                                    incremental rebuild must emit a call to
                                    <Unit>_fini at main_exit, or the unit's
                                    finalization never runs and its globals
                                    leak. }

    { The owning-collection containers below are populated on decode via
      the Add* mutators, not by name; their element data round-trips
      through the per-entry encoders/decoders (TTypeEntry, TConstEntry,
      TVarEntry, TRoutineSig). The bif-coverage tool checks fields by name
      against the encoder/decoder text, so these are marked no-bif: the
      named field is not directly serialised, only its contents (which the
      entry-type checks already cover). }
    Types:           TObjectList; { owned TTypeEntry, no-bif }
    Consts:          TObjectList; { owned TConstEntry, no-bif }
    Vars:            TObjectList; { owned TVarEntry, no-bif }
    Routines:        TObjectList; { owned TRoutineSig free routines, no-bif }

    InlineBodies:    TObjectList; { owned TInlineBody, no-bif }
    GenericBodies:   TObjectList; { owned TGenericBody, no-bif }

    { ACaseSensitive controls all Find* lookups.  Default False
      matches Object Pascal semantics; set True for cases that need
      exact-match (e.g. external symbols, future .bpu name tables). }
    constructor Create(const AName: string;
                       ACaseSensitive: Boolean = False);
    destructor Destroy; override;

    { Mutators — used by AnalyseUnitForExport during construction.
      Each takes ownership of the passed-in entry and registers it in
      the index.  After AnalyseUnitForExport returns the caller MUST
      NOT invoke these again; the interface is intended to be frozen.
      Discipline only — not enforced (yet). }
    procedure AddType(AEntry: TTypeEntry);
    procedure AddConst(AEntry: TConstEntry);
    procedure AddVar(AEntry: TVarEntry);
    procedure AddRoutine(ASig: TRoutineSig);
    procedure AddInlineBody(ABody: TInlineBody);
    procedure AddGenericBody(ABody: TGenericBody);

    { Lookups — case-insensitive, O(log n) via sorted TStringList.
      Return nil when the name is not present. }
    function FindType(const AName: string): TTypeEntry;
    function FindConst(const AName: string): TConstEntry;
    function FindRoutine(const AName: string): TRoutineSig;
    function FindInlineBody(const ARoutineName: string): TInlineBody;
    function FindGeneric(const AName: string): TGenericBody;

    { True iff the interface exports a publicly-visible symbol of
      this name.  Probes types, consts, vars, routines, generic
      bodies, and enum-member names (each member of every enum
      type counts as its own top-level symbol — matches what
      uSemanticImport.RegisterEnum publishes).  Used by task #44
      uses-chain lookup. }
    function HasSymbol(const AName: string): Boolean;
    { True when this interface carries a generic TEMPLATE BODY that the
      consumer will clone and RE-ANALYSE in its own symbol table — a generic
      type (class/record/interface/proc) or a generic free routine.

      The loader uses this to decide whether the declaring unit's
      implementation-section dependencies must be semantically imported rather
      than merely linked: a template body can name symbols the declaring unit
      reached through its own impl-section uses, and those have to resolve in
      the consumer too (BUG-20260906-implonly-extern-lost-on-cached-iface).

      Generic TYPES are the case that matters in practice.  They travel in the
      TYPE block with TTypeEntry.IsGeneric set, NOT in GenericBodies — the
      GENROUT block deliberately writes only `not G.IsType` entries — so a
      GenericBodies-only test reads False for them on the cached path. }
    function HasGenericBodies: Boolean;
  end;

{ Helpers for TQualTypeRef. }
function MakeQualRef(const AUnit, AType: string): TQualTypeRef;
function MakeBuiltinRef(const AType: string): TQualTypeRef;
function MakeLocalRef(const AType: string): TQualTypeRef;
function IsBuiltinRef(const ARef: TQualTypeRef): Boolean;
function IsLocalRef(const ARef: TQualTypeRef): Boolean;
function QualRefIsNil(const ARef: TQualTypeRef): Boolean;
function QualRefEqual(const A, B: TQualTypeRef): Boolean;

implementation

{ ----- TQualTypeRef helpers -------------------------------------- }

function MakeQualRef(const AUnit, AType: string): TQualTypeRef;
begin
  Result.UnitName := AUnit;
  Result.TypeName := AType;
end;

function MakeBuiltinRef(const AType: string): TQualTypeRef;
begin
  Result.UnitName := QUALREF_BUILTIN;
  Result.TypeName := AType;
end;

function MakeLocalRef(const AType: string): TQualTypeRef;
begin
  Result.UnitName := QUALREF_THIS_UNIT;
  Result.TypeName := AType;
end;

function IsBuiltinRef(const ARef: TQualTypeRef): Boolean;
begin
  Result := ARef.UnitName = QUALREF_BUILTIN;
end;

function IsLocalRef(const ARef: TQualTypeRef): Boolean;
begin
  Result := ARef.UnitName = QUALREF_THIS_UNIT;
end;

function QualRefIsNil(const ARef: TQualTypeRef): Boolean;
begin
  Result := ARef.TypeName = '';
end;

function QualRefEqual(const A, B: TQualTypeRef): Boolean;
begin
  Result := (A.UnitName = B.UnitName) and (A.TypeName = B.TypeName);
end;

{ ----- TRoutineSig ----------------------------------------------- }

constructor TRoutineSig.Create;
begin
  inherited Create();
  Params := TObjectList.Create(True);
  ReturnType := MakeQualRef('', '');
  VTableSlot := -1;
end;

destructor TRoutineSig.Destroy;
begin
  Params.Free();
  inherited Destroy();
end;

{ ----- TConstEntry ----------------------------------------------- }

destructor TConstEntry.Destroy;
begin
  Decl.Free();
  inherited Destroy();
end;

{ ----- TTypeEntry ------------------------------------------------ }

constructor TTypeEntry.Create;
begin
  inherited Create();
  Implements   := TStringList.Create();
  Methods      := TObjectList.Create(True);
  VTableLayout := TObjectList.Create(False);  { non-owning }
  Attributes   := TStringList.Create();
end;

destructor TTypeEntry.Destroy;
begin
  Attributes.Free();
  VTableLayout.Free();        { non-owning — just refs into Methods }
  Methods.Free();
  Implements.Free();
  Def.Free();
  inherited Destroy();
end;

{ ----- TInlineBody ----------------------------------------------- }

destructor TInlineBody.Destroy;
begin
  Block.Free();
  inherited Destroy();
end;

{ ----- TGenericBody ---------------------------------------------- }

constructor TGenericBody.Create;
begin
  inherited Create();
  TypeParams  := TStringList.Create();
  Constraints := TStringList.Create();
end;

destructor TGenericBody.Destroy;
begin
  MethodDecl.Free();
  Body.Free();
  RoutineSig.Free();
  TypeDef.Free();
  Constraints.Free();
  TypeParams.Free();
  inherited Destroy();
end;

{ ----- TUnitInterface -------------------------------------------- }

{ Build a sorted TStringList with the requested case sensitivity. }
function MakeIndex(ACaseSensitive: Boolean): TStringList;
begin
  Result := TStringList.Create();
  Result.CaseSensitive := ACaseSensitive;
  Result.Sorted        := True;
end;

constructor TUnitInterface.Create(const AName: string;
                                  ACaseSensitive: Boolean = False);
begin
  inherited Create();
  Name      := AName;
  UsedUnits := TStringList.Create();
  ImplUsedUnits := TStringList.Create();
  LinkLibs  := TStringList.Create();

  Types         := TObjectList.Create(True);
  Consts        := TObjectList.Create(True);
  Vars          := TObjectList.Create(True);
  Routines      := TObjectList.Create(True);
  InlineBodies  := TObjectList.Create(True);
  GenericBodies := TObjectList.Create(True);

  FTypeIndex    := MakeIndex(ACaseSensitive);
  FConstIndex   := MakeIndex(ACaseSensitive);
  FRoutineIndex := MakeIndex(ACaseSensitive);
  FInlineIndex  := MakeIndex(ACaseSensitive);
  FGenericIndex := MakeIndex(ACaseSensitive);
end;

destructor TUnitInterface.Destroy;
begin
  FGenericIndex.Free();
  FInlineIndex.Free();
  FRoutineIndex.Free();
  FConstIndex.Free();
  FTypeIndex.Free();

  GenericBodies.Free();
  InlineBodies.Free();
  Routines.Free();
  Vars.Free();
  Consts.Free();
  Types.Free();

  LinkLibs.Free();
  ImplUsedUnits.Free();
  UsedUnits.Free();
  inherited Destroy();
end;

procedure TUnitInterface.AddType(AEntry: TTypeEntry);
begin
  Types.Add(AEntry);
  FTypeIndex.AddObject(AEntry.Name, AEntry);
end;

procedure TUnitInterface.AddConst(AEntry: TConstEntry);
begin
  Consts.Add(AEntry);
  FConstIndex.AddObject(AEntry.Decl.Name, AEntry);
end;

procedure TUnitInterface.AddVar(AEntry: TVarEntry);
begin
  Vars.Add(AEntry);
end;

procedure TUnitInterface.AddRoutine(ASig: TRoutineSig);
begin
  Routines.Add(ASig);
  FRoutineIndex.AddObject(ASig.Name, ASig);
end;

procedure TUnitInterface.AddInlineBody(ABody: TInlineBody);
begin
  InlineBodies.Add(ABody);
  FInlineIndex.AddObject(ABody.RoutineName, ABody);
end;

procedure TUnitInterface.AddGenericBody(ABody: TGenericBody);
begin
  GenericBodies.Add(ABody);
  FGenericIndex.AddObject(ABody.Name, ABody);
end;

function TUnitInterface.FindType(const AName: string): TTypeEntry;
var
  Idx: Integer;
begin
  Idx := FTypeIndex.IndexOf(AName);
  if Idx >= 0 then Result := TTypeEntry(FTypeIndex.Objects[Idx])
              else Result := nil;
end;

function TUnitInterface.FindConst(const AName: string): TConstEntry;
var
  Idx: Integer;
begin
  Idx := FConstIndex.IndexOf(AName);
  if Idx >= 0 then Result := TConstEntry(FConstIndex.Objects[Idx])
              else Result := nil;
end;

function TUnitInterface.FindRoutine(const AName: string): TRoutineSig;
var
  Idx: Integer;
begin
  Idx := FRoutineIndex.IndexOf(AName);
  if Idx >= 0 then Result := TRoutineSig(FRoutineIndex.Objects[Idx])
              else Result := nil;
end;

function TUnitInterface.FindInlineBody(const ARoutineName: string): TInlineBody;
var
  Idx: Integer;
begin
  Idx := FInlineIndex.IndexOf(ARoutineName);
  if Idx >= 0 then Result := TInlineBody(FInlineIndex.Objects[Idx])
              else Result := nil;
end;

function TUnitInterface.FindGeneric(const AName: string): TGenericBody;
var
  Idx: Integer;
begin
  Idx := FGenericIndex.IndexOf(AName);
  if Idx >= 0 then Result := TGenericBody(FGenericIndex.Objects[Idx])
              else Result := nil;
end;

function TUnitInterface.HasSymbol(const AName: string): Boolean;
var
  I, J: Integer;
  T:    TTypeEntry;
  V:    TVarEntry;
  EnumDef: TEnumTypeDef;
begin
  if FindType(AName) <> nil    then begin Result := True; Exit; end;
  if FindConst(AName) <> nil   then begin Result := True; Exit; end;
  if FindRoutine(AName) <> nil then begin Result := True; Exit; end;
  if FindGeneric(AName) <> nil then begin Result := True; Exit; end;

  { Vars lack an index — linear walk. }
  for I := 0 to Vars.Count - 1 do
  begin
    V := TVarEntry(Vars.Items[I]);
    if SameText(V.Name, AName) then
    begin
      Result := True;
      Exit;
    end;
  end;

  { Enum members are top-level identifiers (uSemanticImport.RegisterEnum
    Define's each as skConstant).  Walk types, look inside enum defs. }
  for I := 0 to Types.Count - 1 do
  begin
    T := TTypeEntry(Types.Items[I]);
    if T.Def is TEnumTypeDef then
    begin
      EnumDef := TEnumTypeDef(T.Def);
      for J := 0 to EnumDef.Members.Count - 1 do
        if SameText(EnumDef.Members.Strings[J], AName) then
        begin
          Result := True;
          Exit;
        end;
    end;
  end;

  Result := False;
end;

function TUnitInterface.HasGenericBodies: Boolean;
var
  I: Integer;
  T: TTypeEntry;
begin
  Result := True;
  { Generic free routines: carried in GenericBodies (the GENROUT block). }
  for I := 0 to GenericBodies.Count - 1 do
    if not TGenericBody(GenericBodies.Items[I]).IsType then
      Exit;
  { Generic types: carried in the TYPE block with IsGeneric set. }
  for I := 0 to Types.Count - 1 do
  begin
    T := TTypeEntry(Types.Items[I]);
    if T.IsGeneric or (T.Def is TGenericTypeDef)
       or (T.Def is TGenericInterfaceDef) or (T.Def is TGenericProcDef) then
      Exit;
  end;
  Result := False;
end;

end.
