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

{ True if ASym is one of the OS conditional-compilation symbols (the target's
  OS define, injected by the driver, replaces the lexer's host-seeded ones). }
function DefineIsOS(const ASym: string): Boolean;
begin
  Result := SameText(ASym, 'LINUX')   or SameText(ASym, 'FREEBSD') or
            SameText(ASym, 'WINDOWS') or SameText(ASym, 'DARWIN')  or
            SameText(ASym, 'UNIX');
end;

function DefineIsCPU(const ASym: string): Boolean;
begin
  Result := SameText(ASym, 'CPUX86_64') or SameText(ASym, 'CPUAMD64') or
            SameText(ASym, 'CPUARM64')  or SameText(ASym, 'CPUAARCH64');
end;

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
  DI: Integer;
  HasOS: Boolean;
  HasCPU: Boolean;
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
    { Recurse so this dep's own dependencies are linked too. }
    for I := 0 to Iface.UsedUnits.Count - 1 do
      CollectLinkOnlyObject(Iface.UsedUnits.Strings[I]);
    for I := 0 to Iface.ImplUsedUnits.Count - 1 do
      CollectLinkOnlyObject(Iface.ImplUsedUnits.Strings[I]);
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
  FLinkOnlySeen.CaseSensitive := False;
end;

destructor TUnitLoader.Destroy;
begin
  FLinkOnlySeen.Free();
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
end;

end.
