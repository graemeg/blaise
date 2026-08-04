{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uUnitLoader;

{ Resolves unit names to source files, parses them, and returns a
  dependency-ordered list (leaves first).  Cycle detection raises
  ECircularDependency; missing units raise EUnitNotFound.

  Built-in FPC RTL unit names (SysUtils, Classes, etc.) are silently
  skipped — their symbols are already registered by TSymbolTable.RegisterBuiltins.
  User-defined units in the search paths are loaded and parsed normally. }

interface

uses
  SysUtils, Classes, contnrs,
  uLexer, uParser, uAST,
  uUnitInterface, uUnitInterfaceIO, uIfaceObject, uCompilerId;

type
  EUnitNotFound       = class(Exception);
  ECircularDependency = class(Exception);

  TUnitLoader = class
  public
    constructor Create(const ASearchPaths: TStringList;
                       const ADefines: TStringList = nil);
    destructor Destroy; override;
    { Returns an owned TObjectList of TUnit in dependency order (leaves
      first).  The caller is responsible for freeing the list.

      Auto-discovery: while resolving each dep, the loader looks for
      a pre-built '<unitname>.o' alongside any '<unitname>.pas' on
      the search path.  If the .o is found and carries an embedded
      iface (.blaise.iface section), the dep is materialised as a
      TUnitInterface (added to PrebuiltIfaces with path noted in
      PrebuiltObjectPaths) and the source .pas is *not* parsed.
      Otherwise we fall back to the existing parse+analyse path. }
    function LoadAll(const AUnitNames: TStringList): TObjectList;

    { Pre-built ifaces discovered during the most recent LoadAll —
      one TUnitInterface per dep that was satisfied via a .o on the
      search path.  Order matches PrebuiltObjectPaths.  Owned by the
      loader; freed in Destroy. }
    property PrebuiltIfaces:      TObjectList read FPrebuiltIfaces;
    { Filesystem paths to the .o files that backed the pre-built
      ifaces.  Caller links against these alongside the main
      program's object. }
    property PrebuiltObjectPaths: TStringList read FPrebuiltObjectPaths;
    { Object paths for impl-only dependencies that must be linked but were
      not semantically imported (and thus are absent from PrebuiltObjectPaths
      and the source-compiled unit set).  Caller links these too. }
    property LinkOnlyObjects:     TStringList read FLinkOnlyObjects;
    { Names of impl-only dependencies that HAVE an initialization section, in
      dependency order (deepest first).  These units are linked but never
      semantically imported, so nothing else registers them — without this the
      caller emits their object yet never calls <Unit>_init, and the unit's
      globals stay nil.  Objects[I] is non-nil when the unit also has a
      finalization section. }
    property LinkOnlyInitUnits:   TStringList read FLinkOnlyInitUnits;
  private
    FSearchPaths:          TStringList;  { not owned }
    FDefines:              TStringList;  { not owned — conditional symbols for each unit's lexer }
    FLoading:              TStringList;  { units currently on the load stack (any edge) — guards re-entry / infinite recursion }
    FIfaceChain:           TStringList;  { units reached along an unbroken chain of interface-section uses — a back-edge into this set is a true circular dependency.  Implementation-section uses do NOT extend this chain (Pascal allows them to point back), so following one starts a fresh chain. }
    FLoadedNames:          TStringList;  { units already fully loaded }
    FSourceLoadedNames:    TStringList;  { units taken via the SOURCE-recompile
                                           path (stale cache or no cache).  A
                                           cached unit whose dependency is in
                                           this set must itself be recompiled —
                                           staleness propagates up the uses graph. }
    FResult:               TObjectList;  { the in-progress output list (not owned here) }
    FPrebuiltIfaces:       TObjectList;  { owned TUnitInterface }
    FPrebuiltObjectPaths:  TStringList;
    FLinkOnlyObjects:      TStringList;  { .o paths for impl-only deps that
                                           must be linked but NOT semantically
                                           imported (see CollectLinkOnlyObject) }
    FLinkOnlySeen:         TStringList;  { unit names already visited by the
                                           link-only collector — cycle guard }
    FLinkOnlyInitUnits:    TStringList;  { impl-only deps with an initialization
                                           section; Objects[I] non-nil when the
                                           unit also has a finalization one }
    { Sort FPrebuiltIfaces / FPrebuiltObjectPaths so a unit follows every unit
      it uses from EITHER section, so $main calls the inits in an order where
      a unit's dependencies are already initialised.  See the implementation
      for why this is a post-pass and not a change to the load recursion. }
    procedure OrderPrebuiltForInit;
    function IsBuiltin(const AName: string): Boolean;
    function Locate(const AName: string): string;
    { Look for '<AName>.o' on the search paths (lowercase or as-cased).
      Returns the path or '' if none found. }
    function LocateObject(const AName: string): string;
    { Read the embedded iface section out of an object file and
      reconstitute a TUnitInterface.  Returns nil on failure. }
    function LoadIfaceFromObject(const APath: string): TUnitInterface;
    function LoadOne(const APath: string): TUnit;
    { True if any interface-use dependency of AIface was taken via the
      source-recompile path (is in FSourceLoadedNames). }
    function DependsOnSourceLoaded(AIface: TUnitInterface): Boolean;
    procedure LoadTransitive(const AName: string);
    { Collect the .o for an impl-only dependency (and its transitive
      dependencies) for linking, without parsing source or importing its
      iface.  Units already loaded normally are skipped — they are linked
      via FPrebuiltObjectPaths / the source-compiled worker objects. }
    procedure CollectLinkOnlyObject(const AName: string);
    { Decide whether to trust a freshly-loaded .bif.  Hash-compares
      against the source .pas if present on the search path; falls
      back to a CompilerId match when source is unavailable. }
    function ValidateIface(AIface: TUnitInterface;
                           const AName: string): Boolean;
  end;

implementation

function TUnitLoader.IsBuiltin(const AName: string): Boolean;
begin
  Result :=
    SameText(AName, 'System')   or SameText(AName, 'Windows')   or
    SameText(AName, 'Unix')     or SameText(AName, 'BaseUnix')  or
    SameText(AName, 'CThreads') or SameText(AName, 'FGL')       or
    SameText(AName, 'Types');
end;

function TUnitLoader.Locate(const AName: string): string;
var
  I:    Integer;
  Base: string;
  Path: string;
begin
  for I := 0 to FSearchPaths.Count - 1 do
  begin
    Base := IncludeTrailingPathDelimiter(FSearchPaths.Strings[I]);
    { Try lowercase first — Blaise convention for unit file names }
    Path := Base + LowerCase(AName) + '.pas';
    if FileExists(Path) then
    begin
      Exit(Path);
    end;
    { Fallback: exact case as written in the uses clause }
    Path := Base + AName + '.pas';
    if FileExists(Path) then
    begin
      Exit(Path);
    end;
  end;
  Result := '';
end;

function TUnitLoader.LocateObject(const AName: string): string;
var
  I:    Integer;
  Base: string;
  Path: string;
begin
  for I := 0 to FSearchPaths.Count - 1 do
  begin
    Base := IncludeTrailingPathDelimiter(FSearchPaths.Strings[I]);
    Path := Base + LowerCase(AName) + '.o';
    if FileExists(Path) then begin Result := Path; Exit; end;
    Path := Base + AName + '.o';
    if FileExists(Path) then begin Result := Path; Exit; end;
  end;
  Result := '';
end;

function TUnitLoader.ValidateIface(AIface: TUnitInterface;
                                   const AName: string): Boolean;
var
  SrcPath: string;
  Src:     TStringList;
  Cur:     string;
begin
  Result := False;
  if AIface = nil then Exit;
  SrcPath := Locate(AName);
  if SrcPath <> '' then
  begin
    { Source available — hash decides.  An empty SourceHash on the
      iface means it was written before this format extension; treat
      as a forced miss so the source-compile path takes over. }
    if AIface.SourceHash = '' then
    begin
      WriteLn(StdErr,
              'note: ', AName,
              '.o iface has no source hash; recompiling from source');
      Exit;
    end;
    Src := TStringList.Create();
    try
      try
        Src.LoadFromFile(SrcPath);
        { Must mirror the writer exactly (WriteUnitInterfaceToFile): the hash
          covers the source text AND every file it embeds, so editing an
          embedded asset invalidates this entry.  FDefines is passed because
          discovery lexes the source -- without the same -d set, a
          define-gated embed is missed and never invalidates. }
        Cur := SourceHashWithEmbeds(Src.Text, SrcPath, FDefines);
      except
        Cur := '';
      end;
    finally
      Src.Free();
    end;
    if Cur = '' then Exit;
    if not SameText(Cur, AIface.SourceHash) then
    begin
      WriteLn(StdErr,
              'note: ', AName,
              '.o iface stale vs source on path; recompiling from source');
      Exit;
    end;
    { Source unchanged — but the cached .o must also have been emitted by THIS
      compiler binary, not a previous one with different codegen/layout (BUG-007).
      EffectiveCompilerId carries a hash of the running binary, so a compiler-dev
      rebuild that changed codegen but not the source auto-invalidates the cache
      here (fixpoint-stable: stage-2==stage-3 binaries hash equal). }
    Result := SameText(AIface.CompilerId, EffectiveCompilerId());
    if not Result then
      WriteLn(StdErr,
              'note: ', AName,
              '.o iface compiled by a different blaise binary; recompiling from source');
    Exit;
  end;
  { No source available — CompilerId match is the only safe signal. }
  if AIface.CompilerId = '' then
  begin
    WriteLn(StdErr,
            'error: ', AName,
            '.o iface has no compiler id and no source on path; cannot use');
    Exit;
  end;
  Result := SameText(AIface.CompilerId, EffectiveCompilerId());
  if not Result then
    WriteLn(StdErr,
            'error: ', AName,
            '.o iface compiled by ''', AIface.CompilerId,
            ''' (this compiler is ''', EffectiveCompilerId(),
            '''); source unavailable to rebuild');
end;

function TUnitLoader.LoadIfaceFromObject(const APath: string): TUnitInterface;
var
  Bytes: string;
begin
  Result := nil;
  { the object may be ELF or Mach-O depending on the target that produced it —
    sniff rather than assume, so a macOS .o is probed the same way }
  Bytes := LoadEmbeddedBifString(APath, DetectObjectFormat(APath));
  if Bytes = '' then Exit;
  try
    Result := ReadUnitInterface(Bytes);
  except
    { A malformed iface section is non-fatal — fall back to the
      .pas source.  Surface the error so the user knows to
      regenerate the .o. }
    on E: Exception do
    begin
      WriteLn(StdErr, 'warning: unreadable iface in ', APath, ': ',
              Exception(E).Message);
      Result := nil;
    end;
  end;
end;

function TUnitLoader.LoadOne(const APath: string): TUnit;
var
  SL: TStringList;
  L:  TLexer;
  P:  TParser;
begin
  SL := TStringList.Create();
  try
    SL.LoadFromFile(APath);
    L := TLexer.Create(SL.Text, APath);
    { Apply the same -d/--define symbols the main program got, so IFDEF
      directives resolve consistently across the program and all its units.
      TLexer.ApplyDefines owns the OS/CPU-replacement rule (a cross --target's
      symbol must displace the host-seeded one), so the loader, the driver and
      the cache-staleness hash all go through it and cannot drift. }
    L.ApplyDefines(FDefines);
    try
      P := TParser.Create(L);
      try
        Result := P.ParseUnit();
        Result.SourceFile := APath;
      finally
        P.Free();
      end;
    finally
      L.Free();
    end;
  finally
    SL.Free();
  end;
end;

procedure TUnitLoader.CollectLinkOnlyObject(const AName: string);
var
  ObjPath: string;
  Iface:   TUnitInterface;
  I:       Integer;
begin
  if IsBuiltin(AName) then Exit;
  { Already loaded the normal way → its object is already linked. }
  if FLoadedNames.IndexOf(AName) >= 0 then Exit;
  if FLinkOnlySeen.IndexOf(AName) >= 0 then Exit;
  FLinkOnlySeen.Add(AName);

  ObjPath := LocateObject(AName);
  if ObjPath = '' then Exit;  { no cached object — nothing to link }
  Iface := LoadIfaceFromObject(ObjPath);
  if Iface = nil then Exit;   { unreadable iface — the source-load path
                                elsewhere will have handled this unit }
  try
    if not ValidateIface(Iface, AName) then Exit;
    if FLinkOnlyObjects.IndexOf(ObjPath) < 0 then
      FLinkOnlyObjects.Add(ObjPath);
    { Recurse FIRST so this dep's own dependencies are linked — and recorded
      for init — ahead of it.  The recursion is what makes FLinkOnlyInitUnits
      dependency-ordered: a unit is appended only after everything it uses. }
    for I := 0 to Iface.UsedUnits.Count - 1 do
      CollectLinkOnlyObject(Iface.UsedUnits.Strings[I]);
    for I := 0 to Iface.ImplUsedUnits.Count - 1 do
      CollectLinkOnlyObject(Iface.ImplUsedUnits.Strings[I]);
    { An impl-only dep is LINKED but never semantically imported, so no other
      path registers its <Unit>_init.  Record it here or the object ships with
      an initialization section that is never called — the unit's globals stay
      nil and the first use segfaults with no compile- or link-time
      diagnostic.  (This is what broke BlaiseGuard: every rule unit impl-uses
      Guard.Rules, whose initialization creates the GRules list.) }
    if Iface.HasInitialization then
      if FLinkOnlyInitUnits.IndexOf(AName) < 0 then
      begin
        { Objects[] carries the fini flag: non-nil = also has a finalization
          section.  Any non-nil pointer works as the marker; the list itself
          is non-owning (raw untyped slots, see TStringList.Objects). }
        if Iface.HasFinalization then
          FLinkOnlyInitUnits.AddObject(AName, Pointer(Self))
        else
          FLinkOnlyInitUnits.AddObject(AName, nil);
      end;
  finally
    Iface.Free();
  end;
end;

function TUnitLoader.DependsOnSourceLoaded(AIface: TUnitInterface): Boolean;
var
  I: Integer;
begin
  Result := True;
  for I := 0 to AIface.UsedUnits.Count - 1 do
    if FSourceLoadedNames.IndexOf(AIface.UsedUnits.Strings[I]) >= 0 then
      Exit;
  Result := False;
end;

procedure TUnitLoader.LoadTransitive(const AName: string);
var
  Path:       string;
  ObjPath:    string;
  Iface:      TUnitInterface;
  U:          TUnit;
  I:          Integer;
  SavedChain: TStringList;
begin
  if IsBuiltin(AName) then Exit;
  if FLoadedNames.IndexOf(AName) >= 0 then Exit;  { already in result list }

  if FLoading.IndexOf(AName) >= 0 then
  begin
    { Already on the load stack.  This is a true circular dependency only when
      the back-edge closes a chain of interface-section uses (those cannot be
      satisfied — each unit's interface needs the other's first).  A back-edge
      reached through an implementation-section use is legal in Pascal, so it
      is simply skipped: the unit is already being loaded higher up the stack
      and its interface will be available by the time bodies are compiled. }
    if FIfaceChain.IndexOf(AName) >= 0 then
      raise ECircularDependency.Create(Format(
        'Circular unit dependency: ''%s''', [AName]));
    Exit;
  end;

  { Auto-discovery: prefer a pre-built '<name>.o' on the search path
    when it carries an embedded iface section.  The .o + embedded
    .bif are inseparable, so no mismatch risk.  When found, recurse
    into the iface's UsedUnits (which the .bif carries) instead of
    parsing the .pas. }
  ObjPath := LocateObject(AName);
  if ObjPath <> '' then
  begin
    Iface := LoadIfaceFromObject(ObjPath);
    if Iface <> nil then
    begin
      { Validate before trusting.  Two outcomes:
          - source .pas present on path: hash-compare.  Match →
            accept iface.  Mismatch → discard, fall through to
            source-compile path (the iface is stale).
          - source not present: a CompilerId match is the only
            signal the iface is safe; mismatch → discard. }
      if not ValidateIface(Iface, AName) then
      begin
        Iface.Free();
        Iface := nil;
      end;
    end;
    if Iface <> nil then
    begin
      FLoading.Add(AName);
      FIfaceChain.Add(AName);
      try
        { A prebuilt .bif carries only interface-section uses, so these all
          extend the interface chain. }
        for I := 0 to Iface.UsedUnits.Count - 1 do
          LoadTransitive(Iface.UsedUnits.Strings[I]);
        { Staleness propagation: if any interface-use dependency was taken via
          the SOURCE path (its cache was stale, or it has no cache), then THIS
          unit's cached iface may reference types whose definitions are only
          available from that recompiled dependency — and those are imported in
          a later phase than cached ifaces, so resolution would fail with an
          EImportError ("field type X unresolved").  Discard the cached iface
          and recompile this unit from source too, so it lands in the
          source-ordered analysis phase after its dependency.  (Without source
          on the path we cannot recompile, so the cache is the only option —
          keep it when source is not locatable.) }
        if DependsOnSourceLoaded(Iface) and (Locate(AName) <> '') then
        begin
          Iface.Free();
          Iface := nil;   { fall through to the source-compile path below }
        end
        else
        begin
          FPrebuiltIfaces.Add(Iface);
          FPrebuiltObjectPaths.Add(ObjPath);
          FLoadedNames.Add(AName);
          { Impl-only dependencies are not reachable via the interface uses,
            but their objects must still be linked or the program loses their
            code (an incremental rebuild that loads this unit from its cached
            .bif would otherwise drop them).  They are collected for LINK ONLY
            — not semantically imported — because the consuming unit never
            references their symbols, and importing their ifaces early would
            break the dependency-ordered import (impl/interface-use cycles, e.g.
            a backend unit whose interface a peer impl-uses, cannot be resolved
            by the leaf-first iface import). }
          for I := 0 to Iface.ImplUsedUnits.Count - 1 do
            CollectLinkOnlyObject(Iface.ImplUsedUnits.Strings[I]);
        end;
      finally
        FLoading.Delete(FLoading.IndexOf(AName));
        FIfaceChain.Delete(FIfaceChain.IndexOf(AName));
      end;
      if Iface <> nil then
        Exit;   { cached path taken — done.  Otherwise fall through to source. }
    end;
  end;

  Path := Locate(AName);
  if Path = '' then
    raise EUnitNotFound.Create(Format(
      'Unit ''%s'' not found in search paths', [AName]));

  FLoading.Add(AName);
  FIfaceChain.Add(AName);
  U := nil;
  try
    U := LoadOne(Path);
    { Post-order DFS: process dependencies before this unit.  Both interface-
      and implementation-section uses are loaded — the parser splits them into
      separate lists.

      Interface-section uses extend the interface chain, so a loop among them
      is reported as a circular dependency.  Implementation-section uses are
      traversed with a FRESH interface chain: Pascal permits a unit's
      implementation to use a unit whose interface (transitively) uses it
      back, and that is not a real cycle (interfaces compile first, bodies
      after).  A back-edge into a unit still on the load stack is then
      tolerated by the guard at the top of this routine. }
    for I := 0 to U.UsedUnits.Count - 1 do
      LoadTransitive(U.UsedUnits.Strings[I]);
    SavedChain  := FIfaceChain;
    FIfaceChain := TStringList.Create();
    FIfaceChain.CaseSensitive := False;
    try
      for I := 0 to U.ImplUsedUnits.Count - 1 do
        LoadTransitive(U.ImplUsedUnits.Strings[I]);
    finally
      FIfaceChain.Free();
      FIfaceChain := SavedChain;
    end;
    { Append this unit after all its dependencies }
    FResult.Add(U);
    FLoadedNames.Add(AName);
    { Record that this unit was recompiled from source, so any cached unit
      that depends on it (interface-use) propagates the staleness and also
      recompiles — see the staleness-propagation guard in the cached path. }
    if FSourceLoadedNames.IndexOf(AName) < 0 then
      FSourceLoadedNames.Add(AName);
    U := nil;  { ownership transferred to FResult }
  finally
    U.Free();  { no-op if U = nil (success path) or on error }
    FLoading.Delete(FLoading.IndexOf(AName));
    FIfaceChain.Delete(FIfaceChain.IndexOf(AName));
  end;
end;

constructor TUnitLoader.Create(const ASearchPaths: TStringList;
                               const ADefines: TStringList = nil);
begin
  inherited Create();
  FSearchPaths := ASearchPaths;
  FDefines     := ADefines;
  FLoading     := TStringList.Create();
  FLoading.CaseSensitive := False;
  FIfaceChain  := TStringList.Create();
  FIfaceChain.CaseSensitive := False;
  FLoadedNames := TStringList.Create();
  FLoadedNames.CaseSensitive := False;
  FSourceLoadedNames := TStringList.Create();
  FSourceLoadedNames.CaseSensitive := False;
  FPrebuiltIfaces      := TObjectList.Create(True);
  FPrebuiltObjectPaths := TStringList.Create();
  FPrebuiltObjectPaths.CaseSensitive := False;
  FLinkOnlyObjects     := TStringList.Create();
  FLinkOnlyObjects.CaseSensitive := False;
  FLinkOnlySeen        := TStringList.Create();
  FLinkOnlyInitUnits   := TStringList.Create();
  FLinkOnlySeen.CaseSensitive := False;
end;

destructor TUnitLoader.Destroy;
begin
  FLinkOnlySeen.Free();
  FLinkOnlyInitUnits.Free();
  FLinkOnlyObjects.Free();
  FPrebuiltObjectPaths.Free();
  FPrebuiltIfaces.Free();
  FSourceLoadedNames.Free();
  FLoadedNames.Free();
  FIfaceChain.Free();
  FLoading.Free();
  inherited Destroy();
end;

function TUnitLoader.LoadAll(const AUnitNames: TStringList): TObjectList;
var
  I: Integer;
begin
  Result  := TObjectList.Create(True);  { owns TUnit items }
  FResult := Result;
  try
    for I := 0 to AUnitNames.Count - 1 do
      LoadTransitive(AUnitNames.Strings[I]);
  except
    FResult := nil;
    Result.Free();
    raise;
  end;
  FResult := nil;
  Self.OrderPrebuiltForInit();
end;

{ Reorder FPrebuiltIfaces (and its parallel FPrebuiltObjectPaths) so that a
  unit always follows every unit it USES, counting implementation-section uses
  as well as interface ones.

  Why this is a separate pass rather than a change to LoadTransitive's
  recursion: the load order doubles as the SEMANTIC IMPORT order, and that
  order deliberately follows interface uses only — an impl-use may point back
  into the chain (Pascal allows it), so recursing through impl uses during
  loading would turn a legal impl/interface cycle into an unresolvable import
  (see CollectLinkOnlyObject's note).  Initialization order is a different
  constraint: a unit's `initialization` may touch anything it uses from EITHER
  section, so it must run last.  Sorting afterwards satisfies both.

  The bug this fixes: every BlaiseGuard rule unit has an empty interface uses
  clause and pulls Guard.Rules in its implementation section.  Ordered by
  interface uses alone, Guard.Rules sorted AFTER the rule units, so
  Guard.Rules_init — which creates the GRules list — ran after thirteen
  RegisterRule calls had already tried to Add to a nil list.  The result was a
  segfault at startup with no diagnostic at compile or link time.

  A genuine cycle (mutually impl-using units) cannot be ordered; those units
  are emitted in their existing relative order rather than dropped, which
  reproduces today's behaviour for a case that has no correct answer. }
procedure TUnitLoader.OrderPrebuiltForInit;
var
  Sorted:      TObjectList;
  SortedPaths: TStringList;
  Placed:      TStringList;
  Progress:    Boolean;
  I, J:        Integer;
  Iface:       TUnitInterface;
  Ready:       Boolean;
  DepName:     string;

  { True when ADep is one of the units still awaiting placement — i.e. a
    dependency that must be emitted before the unit naming it.  Units outside
    FPrebuiltIfaces (builtins, source-compiled deps) never block. }
  function StillPending(const ADep: string): Boolean;
  var
    K: Integer;
  begin
    Result := False;
    for K := 0 to FPrebuiltIfaces.Count - 1 do
      if SameText(TUnitInterface(FPrebuiltIfaces.Items[K]).Name, ADep) and
         (Placed.IndexOf(LowerCase(ADep)) < 0) then
        Exit(True);
  end;

begin
  if FPrebuiltIfaces.Count < 2 then Exit;

  { Create(False) is nominal only — this TObjectList is ARC-based and addrefs
    on Add regardless (FOwnsObjects is not consulted).  That is what we want:
    Sorted holding a reference is exactly what makes the in-place permutation
    below safe, and its Free() balances it. }
  Sorted      := TObjectList.Create(False);
  SortedPaths := TStringList.Create();
  Placed      := TStringList.Create();
  try
    repeat
      Progress := False;
      for I := 0 to FPrebuiltIfaces.Count - 1 do
      begin
        Iface := TUnitInterface(FPrebuiltIfaces.Items[I]);
        if Placed.IndexOf(LowerCase(Iface.Name)) >= 0 then Continue;

        { Ready when no dependency of EITHER section is still pending. }
        Ready := True;
        for J := 0 to Iface.UsedUnits.Count - 1 do
        begin
          DepName := Iface.UsedUnits.Strings[J];
          if not SameText(DepName, Iface.Name) then
            if StillPending(DepName) then
            begin
              Ready := False;
              break;
            end;
        end;
        if Ready then
          for J := 0 to Iface.ImplUsedUnits.Count - 1 do
          begin
            DepName := Iface.ImplUsedUnits.Strings[J];
            if not SameText(DepName, Iface.Name) then
              if StillPending(DepName) then
              begin
                Ready := False;
                break;
              end;
          end;

        if Ready then
        begin
          Sorted.Add(Iface);
          SortedPaths.Add(FPrebuiltObjectPaths.Strings[I]);
          Placed.Add(LowerCase(Iface.Name));
          Progress := True;
        end;
      end;
    until (not Progress) or (Sorted.Count = FPrebuiltIfaces.Count);

    { Cycle (or self-reference): append whatever is left in its original
      relative order.  No ordering is correct for a true cycle, so preserve
      today's behaviour rather than dropping units from the link. }
    if Sorted.Count < FPrebuiltIfaces.Count then
      for I := 0 to FPrebuiltIfaces.Count - 1 do
      begin
        Iface := TUnitInterface(FPrebuiltIfaces.Items[I]);
        if Placed.IndexOf(LowerCase(Iface.Name)) < 0 then
        begin
          Sorted.Add(Iface);
          SortedPaths.Add(FPrebuiltObjectPaths.Strings[I]);
          Placed.Add(LowerCase(Iface.Name));
        end;
      end;

    { Rewrite both lists in the new order.  This is an in-place PERMUTATION,
      not empty-and-refill: TObjectList is ARC-based (contnrs.pas), so
      Extract() removes WITHOUT releasing while Add() addrefs — extracting
      then re-Adding would net +1 refcount per iface and leak every one of
      them.  Put() (the Items setter) addrefs the new entry before releasing
      the old, and `Sorted` holds a reference to every item throughout, so
      each slot can be overwritten safely in any order. }
    for I := 0 to Sorted.Count - 1 do
      FPrebuiltIfaces.Items[I] := TUnitInterface(Sorted.Items[I]);
    FPrebuiltObjectPaths.Clear();
    for I := 0 to SortedPaths.Count - 1 do
      FPrebuiltObjectPaths.Add(SortedPaths.Strings[I]);
  finally
    Sorted.Free();
    SortedPaths.Free();
    Placed.Free();
  end;
end;

end.
