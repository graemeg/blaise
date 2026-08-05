{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ uUnitInterfaceIO — text-based serializer / deserializer for
  TUnitInterface.

  Phase 6c-E starter.  The on-disk story for separate compilation
  needs a stable, parser-free way to materialise a TUnitInterface
  from a byte sequence.  This unit owns that mapping.

  Format (v1):
    Magic + version on a single line, then length-prefixed string
    records.  Lengths are decimal ASCII followed by ':' and the
    raw bytes (no escaping needed since lengths drive consumption).

    BLAISE-IFACE 1\n
    <unit-name lpstr>
    CONST <count>\n
      <name lpstr><typeref lpstr><int64><strval lpstr><flags byte>
    END\n

  Where:
    <lpstr>     = "<decimal-len>:" followed by <len> raw bytes
    <int64>     = lpstr containing the decimal digits
    <flags byte>= '0' / '1' / '2' / '3'
                  bit 0 = IsString, bit 1 = IsFloat

  TypeRef is rendered as "UnitName.TypeName" — '$builtin.Integer',
  '<thisunit>.TFoo', or '.<empty>' for untyped consts.

  Scope of this commit: unit name + const records only.  Vars,
  types, routines, and class/generic bodies land in follow-up
  commits.  The plumbing — magic header, length-prefixed strings,
  cursor-based reader — is the load-bearing part; extending it to
  more record types is mechanical.

  Why text and not binary: easier to diff and inspect during
  development, no endianness concerns, no bit-twiddling.  Once the
  layout stabilises we can re-encode as a compact binary form
  without changing the surface API. }

unit uUnitInterfaceIO;

interface

uses
  Classes, SysUtils, streams, strutils, uAST, uUnitInterface, uStrCompat,
  uLexer, uCompilerId;

const
  IFACE_MAGIC   = 'BLAISE-IFACE';
  IFACE_VERSION = 16; { v16: TMethodDecl.IsStatic added to EncodeMethodDecl/
                          ReadMethodDecl (one extra byte after IsOverload).
                          A `static` method on a GENERIC template travels as a
                          method DECL, not a method SIG, so the sig path's
                          IsStatic (v4) did not cover it: TSet<string>.From(...)
                          resolved inside the declaring unit but was rejected
                          cross-unit as "not a static method".  The method-decl
                          layout grew, so v15 readers must reject these .bif
                          and recompile. }
                      { v15: META block gains HasFinalization after
                          HasInitialization — the per-unit ARC teardown
                          (<Unit>_fini) call flag for cached deps.
                        v14: ROUT entries gain an IsVarArgs bool after
                          ExternalName (C-variadic externals).
                        v13: record payload gains a method list (record
                          methods incl. statics — TUuid.RandomUuid — used to
                          vanish on cached import, BUG-043 follow-on). }
                      { v12 (this cycle): 'anonm' payload carries the '->'
                        lambda facts (IsArrow + optional expression body).
                        v11: 'generic-proc' TYPE-block kind —
                        generic procedural-type templates
                        (TGetter<T> = reference to function(): T).
                        v10: 'reference to' anonymous-method
                          types round-trip.  The PROC payload grew an
                          IsReference bool after IsMethodPtr, so a
                          `type T = reference to procedure(...)` survives
                          export -> import.  v9 readers must reject and
                          recompile (docs/anonymous-methods-design.adoc
                          Phase 0).
                        v9: free-routine external-name linkage now
                          round-trips.  Each ROUT entry grew two trailing fields
                          (IsExternal bool + ExternalName lpstr) after
                          ResolvedQbeName, so a routine declared `external name
                          'socket'` links to the C symbol from a cached .bif (not
                          just from source).  v8 readers must reject and recompile.
                        v8: named integer subranges now round-trip.
                          A `type TIdx = lo..hi;` alias carries IsSubrange + the
                          lo..hi bounds so `array[TIdx] of T` folds to
                          `array[lo..hi] of T` across separate compilation.  The
                          'alias' TYPE entry grew three trailing fields
                          (IsSubrange bool + SubrangeLow + SubrangeHigh, each an
                          lpstr) after TypeName, so v7 readers must reject these
                          .bif and recompile.
                        v7: external-library link dependencies now
                          round-trip.  TUnitInterface.LinkLibs is serialised in
                          the META block (one EncodeStringList after
                          ImplUsedUnits, before HasInitialization) so a unit's
                          `external 'lib' name '...'` declarations propagate the
                          libraries to link.  The META layout grew, so v6 readers
                          must reject these .bif and recompile.
                        v6: the `overload` directive now round-trips.
                          TRoutineSig.IsOverload added to EncodeMethodSig/
                          ReadMethodSig (one extra byte after IsStatic) and
                          TMethodDecl.IsOverload added to EncodeMethodDecl/
                          ReadMethodDecl (after IsOverride; this is the
                          interface- and generic-template-method path).  Without
                          it a cross-unit overload set split across an imported
                          class and its ancestor is truncated by the importer's
                          hiding walk.  Both method layouts grew, so v5 readers
                          must reject these .bif and recompile.
                        v5: member Visibility (private/protected/
                          strict) now serialised — field, method, and property
                          payloads each carry one extra byte for the visibility
                          ordinal, so v4 readers must reject these .bif and
                          recompile.
                        v4: TRoutineSig.IsStatic added to
                          EncodeMethodSig/ReadMethodSig so a cross-unit
                          TypeName.StaticMethod() call resolves through the
                          cached .bif (VTableSlot alone cannot distinguish a
                          static method from a final non-virtual instance
                          method — both are -1).  The method-sig layout grew,
                          so v3 readers must reject these .bif and recompile.
                        v3: `static` (class-level) member facts now
                          serialised — TFieldDecl.IsClassVar + ClassVarEmitName in
                          EncodeFieldList/ReadFieldList, TPropertyDecl.IsStatic in
                          EncodePropertyList/ReadPropertyList, and record/class
                          static-const declarations (ConstDecls) in the record/class
                          payloads.  The layout grew, so v2 readers must reject these
                          .bif and recompile.
                        v1: shipped through release v0.11.x (last public commit
                            d56bdbf).
                        v2 (release v0.12.0): a batch of META/record additions
                          made this cycle, all gated by this single bump since
                          v1 never reached a reader that lacked them:
                            - META block carries ImplUsedUnits + HasInitialization
                            - EncodeBlock carries local var declarations so generic
                              template method bodies round-trip with their locals
                              (e.g. 'var Ptr: ^T')
                            - Exit(value) carries its return value
                            - parameter default values are serialised
                            - free-routine ResolvedQbeName, generic-class template
                              properties, and TRoutineSig vtable facts
                              (VTableSlot/IsVirtual/IsOverride) round-trip.
                          Old (v1) .bif are rejected and recompiled from source. }

type
  EIfaceFormatError = class(Exception);

{ Render AIface into a string.  Caller owns the buffer. }
function WriteUnitInterface(AIface: TUnitInterface): string;

{ Parse AText into a freshly-allocated TUnitInterface.  Caller owns
  the returned interface.  Raises EIfaceFormatError on a malformed
  input or version mismatch. }
function ReadUnitInterface(const AText: string): TUnitInterface;

{ File wrappers.  Caller owns the returned interface. }
procedure WriteUnitInterfaceToFile(AIface: TUnitInterface; const APath: string);
function  ReadUnitInterfaceFromFile(const APath: string): TUnitInterface;

{ FNV-1a 64-bit content hash, lowercase hex.  Cheap, no crypto deps,
  change-detection grade — sufficient for iface-vs-source freshness
  checks but NOT suitable for adversarial integrity. }
function ContentHashFnv1a64(const AContent: string): string;

{ The staleness hash for a unit: its source text PLUS the content of every
  file the source pulls in with an EMBED/EMBEDSTR directive.

  Hashing the .pas alone is not sufficient once a unit can embed assets — an
  icon could change with no effect on the source text, the cached .o would be
  judged fresh, and the rebuilt binary would silently carry the previous
  bytes.  That is precisely the failure mode the embed feature exists to
  remove, so the cache key has to cover the assets too.

  ASourcePath anchors relative embed paths (they resolve against the source
  file's directory, not the CWD).  An embedded file that cannot be read is
  folded in as a marker rather than ignored, so a deleted asset invalidates
  the entry and the following source compile reports it properly.

  ADefines MUST be the same -d/--define set the real compile uses (nil when
  there is none).  Discovery works by lexing, so a define-blind lex takes
  different IFDEF branches than the compile did and silently misses a
  define-gated or cross-target embed -- the cached .o would then never
  invalidate when that asset changed, which is exactly the stale-asset
  failure this hash exists to prevent.

  Both the writer (stamping the .bif) and the validator (checking it) call
  this, so the two sides stay symmetric by construction. }
function SourceHashWithEmbeds(const ASourceText, ASourcePath: string;
                              ADefines: TStringList): string;

{ The -d/--define set in force for this compilation.

  WriteUnitInterfaceToFile stamps a unit's source hash, and that hash must be
  computed with the same defines the validator will use, or the two disagree
  about which IFDEF branches (and therefore which EMBED directives) are live.
  The writer is called from several places that have no define set in scope,
  so the driver publishes it here once instead of threading a parameter
  through every one.  Not owned; the caller keeps ownership. }
procedure SetActiveDefines(ADefines: TStringList);

{ The compiler-identity string stamped into every .bif and checked when a
  cached .o is validated.  It is COMPILER_ID (the human-readable base) PLUS a
  content hash of the RUNNING compiler binary (ParamStr(0)).  The binary-hash
  suffix makes a .bif auto-invalidate whenever the compiler binary changes —
  which is exactly what BUG-007 needs: a compiler-dev rebuild that alters
  codegen/layout but not the hand-bumped COMPILER_ID no longer trusts a cached
  .o emitted by the previous binary.  Fixpoint-stable: stage-2 and stage-3 are
  byte-identical binaries, so their hash (and thus this id) is equal, so
  warm-cache reuse still works.  Computed once and cached. }
function EffectiveCompilerId: string;

implementation

{ Forward — EncodeExpr is defined far below (with the statement/expression
  serialiser) but the method-signature writers need it to emit parameter
  default values. }
function EncodeExpr(AE: TASTExpr): string; forward;

{ ----- Writer ----------------------------------------------------- }

{ Length-prefixed string: "<len>:bytes".  Lets the reader consume
  exactly <len> UTF-8 bytes without worrying about embedded ':',
  newlines, or quotes. }
function EncodeLpstr(const S: string): string;
begin
  Result := IntToStr(Length(S)) + ':' + S;
end;

function EncodeInt64(V: Int64): string;
begin
  Result := EncodeLpstr(IntToStr(V));
end;

function EncodeFlags(AIsString, AIsFloat: Boolean): string;
var
  B: Integer;
begin
  B := 0;
  if AIsString then B := B or 1;
  if AIsFloat  then B := B or 2;
  Result := IntToStr(B);
end;

{ Pass the ref as two strings to dodge the documented record-with-
  strings-as-const-param codegen bug (memory:
  project_record_const_param_crash.md). }
function EncodeQualRefParts(const AUnitName, ATypeName: string): string;
begin
  Result := EncodeLpstr(AUnitName + '.' + ATypeName);
end;

function WriteConsts(AIface: TUnitInterface): string;
var
  I:  Integer;
  C:  TConstEntry;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('CONST ' + IntToStr(AIface.Consts.Count));
    for I := 0 to AIface.Consts.Count - 1 do
    begin
      C := TConstEntry(AIface.Consts.Items[I]);
      SB.AppendLine(
        EncodeLpstr(C.Decl.Name) +
        EncodeQualRefParts(C.TypeRef.UnitName, C.TypeRef.TypeName) +
        EncodeInt64(C.Decl.IntVal) +
        EncodeLpstr(C.Decl.StrVal) +
        EncodeFlags(C.Decl.IsString, C.Decl.IsFloat));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function WriteVars(AIface: TUnitInterface): string;
var
  I:  Integer;
  V:  TVarEntry;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('VAR ' + IntToStr(AIface.Vars.Count));
    for I := 0 to AIface.Vars.Count - 1 do
    begin
      V := TVarEntry(AIface.Vars.Items[I]);
      SB.AppendLine(
        EncodeLpstr(V.Name) +
        EncodeQualRefParts(V.TypeRef.UnitName, V.TypeRef.TypeName) +
        EncodeBool(V.IsThreadVar));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

{ Enum members: encode name=ordinal pairs.  Members.Objects[i]
  holds the explicit ordinal (TEnumTypeDef.AddMember stashes it
  there as a pointer-cast int), so a naive name-only encoding
  rounds back to ordinal 0 for everything.  Renders as
  '<name>=<ord>,<name>=<ord>,…' inside the outer lpstr. }
function EncodeEnumMembers(AEnum: TEnumTypeDef): string;
var
  I:    Integer;
  Acc:  string;
begin
  Acc := '';
  for I := 0 to AEnum.Members.Count - 1 do
  begin
    if I > 0 then Acc := Acc + ',';
    Acc := Acc + AEnum.Members.Strings[I] + '=' + IntToStr(AEnum.OrdinalAt(I));
  end;
  Result := EncodeLpstr(Acc);
end;

{ Tag a TTypeEntry by what its Def is.  Procedural, generic, and
  generic-interface kinds are still skipped on write — they need
  richer payloads (param resolution / template parameter lists) and
  belong in follow-up commits along with inline + generic bodies. }
function TypeEntryKind(AEntry: TTypeEntry): string;
begin
  if      AEntry.Def is TEnumTypeDef         then Result := 'enum'
  else if AEntry.Def is TSetTypeDef          then Result := 'set'
  else if AEntry.Def is TTypeAliasDef        then Result := 'alias'
  else if AEntry.Def is TRecordTypeDef       then Result := 'record'
  else if AEntry.Def is TClassTypeDef        then Result := 'class'
  else if AEntry.Def is TInterfaceTypeDef    then Result := 'interface'
  else if AEntry.Def is TProceduralTypeDef   then Result := 'proc'
  else if AEntry.Def is TGenericTypeDef      then Result := 'generic-class'
  else if AEntry.Def is TGenericInterfaceDef then Result := 'generic-interface'
  else if AEntry.Def is TGenericProcDef      then Result := 'generic-proc'
  else                                            Result := '';
end;

{ ----- TYPE-block payload helpers --------------------------------

  Every value emitted into the TYPE block is an lpstr.  Numeric
  counts and boolean flags are stringified into lpstrs too, which
  costs a few extra bytes but keeps the reader's primitive set
  trivially small (only ReadLpstrAt).  Sequences (attributes,
  implements, fields, methods) are emitted as a count lpstr
  followed by `count` records. }

function EncodeCount(N: Integer): string;
begin
  Result := EncodeLpstr(IntToStr(N));
end;

function EncodeBool(B: Boolean): string;
begin
  if B then Result := EncodeLpstr('1')
       else Result := EncodeLpstr('0');
end;

function EncodeStringList(ASL: TStringList): string;
var
  I: Integer;
begin
  Result := EncodeCount(ASL.Count);
  for I := 0 to ASL.Count - 1 do
    Result := Result + EncodeLpstr(ASL.Strings[I]);
end;

function EncodeFieldList(AFields: TObjectList): string;
var
  I, J: Integer;
  F:    TFieldDecl;
  TotalNames: Integer;
begin
  { TFieldDecl carries Names: TStringList (multi-name fields like
    'X, Y: Integer').  Flatten to one record per name for symmetry
    with how TSymbolTable.AddField is called. }
  TotalNames := 0;
  for I := 0 to AFields.Count - 1 do
    Inc(TotalNames, TFieldDecl(AFields.Items[I]).Names.Count);

  Result := EncodeCount(TotalNames);
  for I := 0 to AFields.Count - 1 do
  begin
    F := TFieldDecl(AFields.Items[I]);
    for J := 0 to F.Names.Count - 1 do
      Result := Result +
                EncodeLpstr(F.Names.Strings[J]) +
                EncodeLpstr(F.TypeName) +
                EncodeBool(F.IsWeak) +
                { `static var` (class variable) facts: IsClassVar marks the field
                  as a shared global rather than an instance slot; ClassVarEmitName
                  is the defining unit's mangled global label (set by uSemantic).
                  An importer cannot re-derive that label — its own unit prefix
                  differs — so the label is carried verbatim.  Both default to
                  False/'' for ordinary instance fields. }
                EncodeBool(F.IsClassVar) +
                EncodeLpstr(F.ClassVarEmitName) +
                { member visibility ordinal (private/protected/strict) }
                EncodeLpstr(IntToStr(Ord(F.Visibility)));
  end;
end;

{ Record/class-level `static const` declarations.  These are scalar
  constants folded by the semantic pass; we serialise the same five-
  field scalar shape the unit-level CONST block uses (Name, TypeName,
  IntVal, StrVal, IsString/IsFloat flags).  Non-scalar const forms
  (array consts, unfolded expression tokens) are not carried here —
  static const members are scalar in the current language surface. }
function EncodeConstDeclList(AConsts: TObjectList): string;
var
  I: Integer;
  C: TConstDecl;
begin
  Result := EncodeCount(AConsts.Count);
  for I := 0 to AConsts.Count - 1 do
  begin
    C := TConstDecl(AConsts.Items[I]);
    Result := Result +
              EncodeLpstr(C.Name) +
              EncodeLpstr(C.TypeName) +
              EncodeInt64(C.IntVal) +
              EncodeLpstr(C.StrVal) +
              EncodeFlags(C.IsString, C.IsFloat);
  end;
end;

{ Per-method routine sig including class-method extras
  (VTableSlot, ResolvedQbeName, IsVirtual, IsOverride).  Used by
  class + interface payloads. }
function EncodeMethodSig(AR: TRoutineSig): string;
var
  J: Integer;
  P: TMethodParam;
begin
  Result :=
    EncodeLpstr(AR.Name) +
    EncodeBool (AR.IsFunction) +
    EncodeQualRefParts(AR.ReturnType.UnitName, AR.ReturnType.TypeName) +
    EncodeBool (AR.IsVirtual) +
    EncodeBool (AR.IsOverride) +
    EncodeLpstr(AR.ResolvedQbeName) +
    EncodeLpstr(IntToStr(AR.VTableSlot)) +
    { static-method flag — distinct from VTableSlot (both static and final
      non-virtual instance methods carry slot -1). }
    EncodeBool (AR.IsStatic) +
    { `overload` directive — must round-trip so a split overload set is not
      truncated by the importer's hiding walk. }
    EncodeBool (AR.IsOverload) +
    { member visibility ordinal }
    EncodeLpstr(IntToStr(Ord(AR.Visibility))) +
    { generic-method type params (Phase 10) — nil means not generic }
    EncodeBool (AR.TypeParams <> nil);
  if AR.TypeParams <> nil then
  begin
    Result := Result + EncodeStringList(AR.TypeParams);
    Result := Result + EncodeBool(AR.TypeParamConstraints <> nil);
    if AR.TypeParamConstraints <> nil then
      Result := Result + EncodeStringList(AR.TypeParamConstraints);
  end;
  Result := Result +
    EncodeCount(AR.Params.Count);
  for J := 0 to AR.Params.Count - 1 do
  begin
    P := TMethodParam(AR.Params.Items[J]);
    Result := Result +
              EncodeLpstr(P.ParamName) +
              EncodeLpstr(P.TypeName) +
              EncodeParamFlags(P) +
              EncodeExpr(P.DefaultValue);
  end;
end;

function EncodeMethodList(AMethods: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AMethods.Count);
  for I := 0 to AMethods.Count - 1 do
    Result := Result + EncodeMethodSig(TRoutineSig(AMethods.Items[I]));
end;

function WriteRecordPayload(AEntry: TTypeEntry): string;
var
  Def: TRecordTypeDef;
begin
  Def := TRecordTypeDef(AEntry.Def);
  Result := EncodeBool(Def.IsPacked) +
            EncodeFieldList(Def.Fields) +
            { record methods (instance + static), as TRoutineSig — v13. }
            EncodeMethodList(AEntry.Methods) +
            { record-level `static const` declarations. }
            EncodeConstDeclList(Def.ConstDecls);
end;

function EncodePropertyList(AList: TObjectList): string;
var
  I: Integer;
  P: TPropertyDecl;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
  begin
    P := TPropertyDecl(AList.Items[I]);
    Result := Result +
              EncodeLpstr(P.Name) +
              EncodeLpstr(P.TypeName) +
              EncodeLpstr(P.ReadName) +
              EncodeLpstr(P.WriteName) +
              EncodeLpstr(P.IndexParamName) +
              EncodeLpstr(P.IndexTypeName) +
              EncodeBool(P.IsDefault) +
              { `static property` — accessors take no implicit Self.  An importer
                needs this to dispatch reads/writes without a receiver. }
              EncodeBool(P.IsStatic) +
              { member visibility ordinal }
              EncodeLpstr(IntToStr(Ord(P.Visibility)));
  end;
end;

function WriteClassPayload(AEntry: TTypeEntry): string;
var
  Def: TClassTypeDef;
begin
  Def := TClassTypeDef(AEntry.Def);
  Result :=
    EncodeQualRefParts(AEntry.ParentClass.UnitName, AEntry.ParentClass.TypeName) +
    EncodeLpstr(IntToStr(AEntry.InstanceSize)) +
    EncodeStringList(AEntry.Attributes) +
    EncodeStringList(AEntry.Implements) +
    EncodeFieldList(Def.Fields) +
    EncodeMethodList(AEntry.Methods) +
    EncodePropertyList(Def.Properties) +
    { class-level `static const` declarations. }
    EncodeConstDeclList(Def.ConstDecls);
end;

{ Encode a TMethodDecl (AST) using the same per-method payload shape
  as EncodeMethodSig, but pulling fields off the AST node.  Interface
  methods live in Def.Methods (TInterfaceTypeDef carries them
  natively), not in AEntry.Methods.  This keeps the writer and the
  importer (uSemanticImport.RegisterInterface, which walks
  Def.Methods) symmetric. }
function EncodeMethodDecl(AM: TMethodDecl): string;
var
  J: Integer;
  P: TMethodParam;
begin
  Result :=
    EncodeLpstr(AM.Name) +
    EncodeBool (AM.ReturnTypeName <> '') +
    EncodeLpstr(AM.ReturnTypeName) +  { stored raw, not a qualref —
                                         interfaces don't carry
                                         resolved cross-unit refs }
    EncodeBool (AM.IsVirtual) +
    EncodeBool (AM.IsOverride) +
    EncodeBool (AM.IsOverload) +      { `overload` directive — generic-template
                                         and interface methods share this path
                                         and may be overloaded }
    EncodeBool (AM.IsStatic) +        { `static` — a static method on a GENERIC
                                         template reaches an importing unit only
                                         through this path (the method-SIG path
                                         carries IsStatic separately, but a
                                         generic's methods travel as decls).
                                         Without it TSet<string>.From(...) was
                                         rejected cross-unit as "not a static
                                         method" while the same code compiled
                                         inside the declaring unit. }
    EncodeCount(AM.Params.Count);
  for J := 0 to AM.Params.Count - 1 do
  begin
    P := TMethodParam(AM.Params.Items[J]);
    Result := Result +
              EncodeLpstr(P.ParamName) +
              EncodeLpstr(P.TypeName) +
              EncodeParamFlags(P) +
              EncodeExpr(P.DefaultValue);
  end;
end;

function EncodeMethodDeclList(AList: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
    Result := Result + EncodeMethodDecl(TMethodDecl(AList.Items[I]));
end;

{ Encode <count> followed by <count> (name, constraint) pairs.  Used
  by both generic-class and generic-interface payloads. }
function EncodeTypeParamList(ANames, AConstraints: TStringList): string;
var
  I: Integer;
  Constraint: string;
begin
  Result := EncodeCount(ANames.Count);
  for I := 0 to ANames.Count - 1 do
  begin
    if (AConstraints <> nil) and (I < AConstraints.Count) then
      Constraint := AConstraints.Strings[I]
    else
      Constraint := '';
    Result := Result + EncodeLpstr(ANames.Strings[I]) + EncodeLpstr(Constraint);
  end;
end;

function WriteGenericClassPayload(AEntry: TTypeEntry): string;
var
  Def:      TGenericTypeDef;
  ClassDef: TClassTypeDef;
  J:        Integer;
  M:        TMethodDecl;
begin
  Def := TGenericTypeDef(AEntry.Def);
  ClassDef := Def.ClassDef;
  Result := EncodeTypeParamList(Def.ParamNames, Def.ParamConstraints);
  if ClassDef <> nil then
  begin
    { Same payload shape as a regular class — uSemanticExport ran
      PopulateClassEntry on the inner ClassDef, so the AEntry-level
      ParentClass / Implements / Attributes / Methods are already
      populated.  InstanceSize stays 0 for the template (no
      concrete layout until instantiation). }
    Result := Result +
              EncodeQualRefParts(AEntry.ParentClass.UnitName,
                                 AEntry.ParentClass.TypeName) +
              EncodeLpstr(IntToStr(AEntry.InstanceSize)) +
              EncodeStringList(AEntry.Attributes) +
              EncodeStringList(AEntry.Implements) +
              EncodeFieldList(ClassDef.Fields) +
              EncodeMethodList(AEntry.Methods);
    { Method bodies, parallel to the method list.  Consumers need
      these to instantiate the template against a concrete type
      argument (the body gets cloned and re-analysed with T bound
      to the concrete type). }
    for J := 0 to ClassDef.Methods.Count - 1 do
    begin
      M := TMethodDecl(ClassDef.Methods.Items[J]);
      Result := Result + EncodeBlock(M.Body);
    end;
    { Property declarations — needed so a cached template instantiates with
      its properties (e.g. TList<T>.Count, TDictionary<K,V>.Count).  Without
      these the instance has no properties and 'D.Count' fails to resolve. }
    Result := Result + EncodePropertyList(ClassDef.Properties);
  end
  else
    { Defensive: encode "has-body" flag = false so the reader can
      detect a templates-without-bodies case without throwing. }
    Result := Result +
              EncodeQualRefParts('', '') +
              EncodeLpstr('0') +
              EncodeCount(0) + EncodeCount(0) +
              EncodeCount(0) + EncodeCount(0) +
              EncodeCount(0);
end;

function WriteGenericInterfacePayload(AEntry: TTypeEntry): string;
var
  Def:     TGenericInterfaceDef;
  IntfDef: TInterfaceTypeDef;
begin
  Def := TGenericInterfaceDef(AEntry.Def);
  IntfDef := Def.IntfDef;
  Result := EncodeTypeParamList(Def.ParamNames, Def.ParamConstraints);
  if IntfDef <> nil then
    Result := Result +
              EncodeLpstr(IntfDef.ParentName) +
              EncodeMethodDeclList(IntfDef.Methods) +
              EncodePropertyList(IntfDef.Properties)
  else
    Result := Result + EncodeLpstr('') + EncodeCount(0) + EncodeCount(0);
end;

function WriteGenericProcPayload(AEntry: TTypeEntry): string;
var
  Def: TGenericProcDef;
  J:   Integer;
  P:   TMethodParam;
begin
  Def := TGenericProcDef(AEntry.Def);
  Result := EncodeTypeParamList(Def.ParamNames, Def.ParamConstraints) +
            EncodeBool (Def.ProcDef.IsFunction) +
            EncodeBool (Def.ProcDef.IsMethodPtr) +
            EncodeBool (Def.ProcDef.IsReference) +
            EncodeLpstr(Def.ProcDef.ReturnTypeName) +
            EncodeCount(Def.ProcDef.Params.Count);
  for J := 0 to Def.ProcDef.Params.Count - 1 do
  begin
    P := TMethodParam(Def.ProcDef.Params.Items[J]);
    Result := Result +
              EncodeLpstr(P.ParamName) +
              EncodeLpstr(P.TypeName) +
              EncodeParamFlags(P);
  end;
end;

function WriteProcPayload(AEntry: TTypeEntry): string;
var
  Def: TProceduralTypeDef;
  J:   Integer;
  P:   TMethodParam;
begin
  Def := TProceduralTypeDef(AEntry.Def);
  Result :=
    EncodeBool (Def.IsFunction) +
    EncodeBool (Def.IsMethodPtr) +
    EncodeBool (Def.IsReference) +
    EncodeLpstr(Def.ReturnTypeName) +
    EncodeCount(Def.Params.Count);
  for J := 0 to Def.Params.Count - 1 do
  begin
    P := TMethodParam(Def.Params.Items[J]);
    Result := Result +
              EncodeLpstr(P.ParamName) +
              EncodeLpstr(P.TypeName) +
              EncodeParamFlags(P);
  end;
end;

function WriteInterfacePayload(AEntry: TTypeEntry): string;
var
  Def: TInterfaceTypeDef;
begin
  Def := TInterfaceTypeDef(AEntry.Def);
  Result :=
    EncodeLpstr(Def.ParentName) +
    EncodeMethodDeclList(Def.Methods) +
    EncodePropertyList(Def.Properties);
end;

function WriteTypes(AIface: TUnitInterface): string;
var
  I:      Integer;
  E:      TTypeEntry;
  SB:     TStringBuilder;
  Kind:   string;
  Eligible: TObjectList;
begin
  Eligible := TObjectList.Create(False);
  SB := TStringBuilder.Create();
  try
    for I := 0 to AIface.Types.Count - 1 do
    begin
      E := TTypeEntry(AIface.Types.Items[I]);
      if TypeEntryKind(E) <> '' then Eligible.Add(E);
    end;

    SB.AppendLine('TYPE ' + IntToStr(Eligible.Count));
    for I := 0 to Eligible.Count - 1 do
    begin
      E := TTypeEntry(Eligible.Items[I]);
      Kind := TypeEntryKind(E);
      if Kind = 'enum' then
        SB.AppendLine(EncodeLpstr('enum') +
               EncodeLpstr(E.Name) +
               EncodeEnumMembers(TEnumTypeDef(E.Def)))
      else if Kind = 'set' then
        SB.AppendLine(EncodeLpstr('set') +
               EncodeLpstr(E.Name) +
               EncodeLpstr(TSetTypeDef(E.Def).BaseTypeName))
      else if Kind = 'alias' then
        SB.AppendLine(EncodeLpstr('alias') +
               EncodeLpstr(E.Name) +
               EncodeLpstr(TTypeAliasDef(E.Def).TypeName) +
               EncodeBool(TTypeAliasDef(E.Def).IsSubrange) +
               EncodeLpstr(IntToStr(TTypeAliasDef(E.Def).SubrangeLow)) +
               EncodeLpstr(IntToStr(TTypeAliasDef(E.Def).SubrangeHigh)))
      else if Kind = 'record' then
        SB.AppendLine(EncodeLpstr('record') +
               EncodeLpstr(E.Name) +
               WriteRecordPayload(E))
      else if Kind = 'class' then
        SB.AppendLine(EncodeLpstr('class') +
               EncodeLpstr(E.Name) +
               WriteClassPayload(E))
      else if Kind = 'interface' then
        SB.AppendLine(EncodeLpstr('interface') +
               EncodeLpstr(E.Name) +
               WriteInterfacePayload(E))
      else if Kind = 'proc' then
        SB.AppendLine(EncodeLpstr('proc') +
               EncodeLpstr(E.Name) +
               WriteProcPayload(E))
      else if Kind = 'generic-class' then
        SB.AppendLine(EncodeLpstr('generic-class') +
               EncodeLpstr(E.Name) +
               WriteGenericClassPayload(E))
      else if Kind = 'generic-proc' then
        SB.AppendLine(EncodeLpstr('generic-proc') +
               EncodeLpstr(E.Name) +
               WriteGenericProcPayload(E))
      else { generic-interface }
        SB.AppendLine(EncodeLpstr('generic-interface') +
               EncodeLpstr(E.Name) +
               WriteGenericInterfacePayload(E));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
    Eligible.Free();
  end;
end;

{ Param flags pack: bit 0 = IsVar, bit 1 = IsConst, bit 2 = IsOpenArray,
  bit 3 = IsOut.  Render as a single decimal lpstr for symmetry with the
  rest of the format. }
function EncodeParamFlags(AParam: TMethodParam): string;
var
  B: Integer;
begin
  B := 0;
  if AParam.IsVarParam   then B := B or 1;
  if AParam.IsConstParam then B := B or 2;
  if AParam.IsOpenArray  then B := B or 4;
  if AParam.IsOutParam   then B := B or 8;
  { Bit 16: this param has a default value.  The default expression itself
    is not serialised; the flag is enough for MinArity / overload resolution
    to accept calls that omit the trailing defaulted arguments. }
  if (AParam.DefaultValue <> nil) or AParam.HasDefault then B := B or 16;
  Result := EncodeLpstr(IntToStr(B));
end;

function WriteRoutines(AIface: TUnitInterface): string;
var
  I, J:   Integer;
  R:      TRoutineSig;
  P:      TMethodParam;
  SB:     TStringBuilder;
  Line:   string;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('ROUT ' + IntToStr(AIface.Routines.Count));
    for I := 0 to AIface.Routines.Count - 1 do
    begin
      R := TRoutineSig(AIface.Routines.Items[I]);
      Line :=
        EncodeLpstr(R.Name) +
        EncodeLpstr(IntToStr(Ord(R.IsFunction))) +
        EncodeQualRefParts(R.ReturnType.UnitName, R.ReturnType.TypeName) +
        EncodeLpstr(IntToStr(R.Params.Count));
      for J := 0 to R.Params.Count - 1 do
      begin
        P    := TMethodParam(R.Params.Items[J]);
        Line := Line +
                EncodeLpstr(P.ParamName) +
                EncodeLpstr(P.TypeName) +
                EncodeParamFlags(P) +
                EncodeExpr(P.DefaultValue);
      end;
      Line := Line + EncodeLpstr(R.CallingConv);
      { ResolvedQbeName — the mangled link symbol.  Required for overloaded
        free routines (e.g. GCHashOf): each overload has a distinct mangled
        name ('..._GCHashOf_D_S' etc.).  Without it the importer falls back
        to the unmangled 'Unit_Name' for every overload, so a call site emits
        a reference to a symbol that does not exist in the cached .o. }
      Line := Line + EncodeLpstr(R.ResolvedQbeName);
      { external-name linkage: a free routine declared `external name 'socket'`
        emits NO Blaise wrapper symbol — the call site must link directly to the
        C name.  ResolvedQbeName carries the mangled 'Unit_Name' (which does not
        exist for an external), so IsExternal + ExternalName must round-trip or a
        caller compiled against the cached .bif emits an undefined 'Unit_Name'
        reference.  (Before v9 these were dropped; Net.Sockets.Socket linked from
        source but not from cache.) }
      Line := Line + EncodeBool(R.IsExternal) + EncodeLpstr(R.ExternalName);
      { varargs (v14): a C-variadic external accepts extra call arguments;
        without the flag a cached import re-imposes the fixed arity. }
      Line := Line + EncodeBool(R.IsVarArgs);
      SB.AppendLine(Line);
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function WriteMeta(AIface: TUnitInterface): string;
var
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('META');
    SB.AppendLine(EncodeLpstr(AIface.SourceFile) +
           EncodeLpstr(AIface.SourceHash) +
           EncodeLpstr(AIface.CompilerId) +
           EncodeInt64(AIface.SourceModTime) +
           EncodeStringList(AIface.UsedUnits) +
           EncodeStringList(AIface.ImplUsedUnits) +
           EncodeStringList(AIface.LinkLibs) +
           EncodeBool(AIface.HasInitialization) +
           EncodeBool(AIface.HasFinalization));
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

{ ----- AST body serialiser ---------------------------------------

  Encodes TASTExpr / TASTStmt / TBlock trees inline within the
  surrounding lpstr stream.  Each node is a sequence of lpstrs:
    <kind lpstr>(<field>…)*
  where kind is a short string tag and the field set depends on
  the kind.  nil children are encoded as the kind 'nil'.

  Scope: every node TASTSerializer.CloneExpr / CloneStmt accepts.
  Anything new added to uAST will compile clean here but trip the
  format-error fallback at read time — a structural change in the
  AST needs a matching version bump in the wire format. }

function EncodeStmt(AStmt: TASTStmt): string; forward;
function EncodeBlock(AB: TBlock): string; forward;

function EncodeExprList(AList: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
    Result := Result + EncodeExpr(TASTExpr(AList.Items[I]));
end;

function EncodeStmtList(AList: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
    Result := Result + EncodeStmt(TASTStmt(AList.Items[I]));
end;

function EncodeExpr(AE: TASTExpr): string;
begin
  if AE = nil then begin Result := EncodeLpstr('nil'); Exit; end;

  if AE is TIntLiteral then
    Result := EncodeLpstr('int') +
              EncodeLpstr(IntToStr(TIntLiteral(AE).Value))
  else if AE is TFloatLiteral then
    Result := EncodeLpstr('float') +
              EncodeLpstr(TFloatLiteral(AE).Value)
  else if AE is TStringLiteral then
    Result := EncodeLpstr('str') +
              EncodeLpstr(TStringLiteral(AE).Value)
  else if AE is TNilLiteral then
    Result := EncodeLpstr('nillit')
  else if AE is TIdentExpr then
    Result := EncodeLpstr('id') +
              EncodeLpstr(TIdentExpr(AE).Name) +
              EncodeLpstr(TIdentExpr(AE).QualifierUnit)
  else if AE is TBinaryExpr then
    Result := EncodeLpstr('bin') +
              EncodeLpstr(IntToStr(Ord(TBinaryExpr(AE).Op))) +
              EncodeExpr(TBinaryExpr(AE).Left) +
              EncodeExpr(TBinaryExpr(AE).Right)
  else if AE is TNotExpr then
    Result := EncodeLpstr('not') +
              EncodeExpr(TNotExpr(AE).Expr)
  else if AE is TFuncCallExpr then
    Result := EncodeLpstr('call') +
              EncodeLpstr(TFuncCallExpr(AE).Name) +
              EncodeExprList(TFuncCallExpr(AE).Args)
  else if AE is TMethodCallExpr then
    Result := EncodeLpstr('mcall') +
              EncodeLpstr(TMethodCallExpr(AE).ObjectName) +
              EncodeLpstr(TMethodCallExpr(AE).Name) +
              EncodeLpstr(TMethodCallExpr(AE).QualifierUnit) +
              EncodeExpr(TMethodCallExpr(AE).ObjExpr) +
              EncodeExprList(TMethodCallExpr(AE).Args)
  else if AE is TIndirectFuncCallExpr then
    Result := EncodeLpstr('icall') +
              EncodeExpr(TIndirectFuncCallExpr(AE).CalleeExpr) +
              EncodeExprList(TIndirectFuncCallExpr(AE).Args)
  else if AE is TFieldAccessExpr then
    Result := EncodeLpstr('field') +
              EncodeLpstr(TFieldAccessExpr(AE).RecordName) +
              EncodeLpstr(TFieldAccessExpr(AE).FieldName) +
              EncodeLpstr(TFieldAccessExpr(AE).QualifierUnit) +
              EncodeExpr(TFieldAccessExpr(AE).Base) +
              EncodeExpr(TFieldAccessExpr(AE).PropIndexExpr)
  else if AE is TDerefExpr then
    Result := EncodeLpstr('deref') +
              EncodeExpr(TDerefExpr(AE).Expr)
  else if AE is TAddrOfExpr then
    Result := EncodeLpstr('addr') +
              EncodeExpr(TAddrOfExpr(AE).Expr)
  else if AE is TStringSubscriptExpr then
    Result := EncodeLpstr('ssub') +
              EncodeExpr(TStringSubscriptExpr(AE).StrExpr) +
              EncodeExpr(TStringSubscriptExpr(AE).IndexExpr)
  else if AE is TArrayLiteralExpr then
    Result := EncodeLpstr('alit') +
              EncodeExprList(TArrayLiteralExpr(AE).Elements)
  else if AE is TSetRangeExpr then
    Result := EncodeLpstr('srng') +
              EncodeExpr(TSetRangeExpr(AE).LowExpr) +
              EncodeExpr(TSetRangeExpr(AE).HighExpr)
  else if AE is TIsExpr then
    Result := EncodeLpstr('isop') +
              EncodeExpr(TIsExpr(AE).Obj) +
              EncodeLpstr(TIsExpr(AE).TypeName)
  else if AE is TAsExpr then
    Result := EncodeLpstr('asop') +
              EncodeExpr(TAsExpr(AE).Obj) +
              EncodeLpstr(TAsExpr(AE).TypeName)
  else if AE is TSupportsExpr then
    Result := EncodeLpstr('supp') +
              EncodeExpr(TSupportsExpr(AE).Obj) +
              EncodeLpstr(TSupportsExpr(AE).IntfTypeName) +
              EncodeLpstr(TSupportsExpr(AE).OutVarName)
  else if AE is TInheritedCallExpr then
    Result := EncodeLpstr('inhc') +
              EncodeLpstr(TInheritedCallExpr(AE).Name) +
              EncodeExprList(TInheritedCallExpr(AE).Args)
  else if AE is TAnonMethodExpr then
  begin
    { Anonymous-method literal inside a generic-body template: the literal's
      declaration (signature) plus its body block travel as parsed AST; the
      [Weak] capture-name list rides along.  Semantic outputs (LiftedName,
      LiftedDecl, EnvType) are re-derived at the importer's monomorphisation
      site and are NOT serialised. }
    Result := EncodeLpstr('anonm') +
              EncodeMethodDecl(TAnonMethodExpr(AE).Decl) +
              EncodeBlock(TAnonMethodExpr(AE).Decl.Body) +
              EncodeBool(TAnonMethodExpr(AE).WeakCaptures <> nil);
    if TAnonMethodExpr(AE).WeakCaptures <> nil then
      Result := Result + EncodeStringList(TAnonMethodExpr(AE).WeakCaptures);
    { Phase 9a: an un-desugared '->' lambda in a template body — its
      expression body travels as parsed AST and is desugared when the
      importer's instantiation supplies the target type. }
    Result := Result + EncodeBool(TAnonMethodExpr(AE).IsArrow) +
              EncodeBool(TAnonMethodExpr(AE).ArrowExpr <> nil);
    if TAnonMethodExpr(AE).ArrowExpr <> nil then
      Result := Result + EncodeExpr(TAnonMethodExpr(AE).ArrowExpr);
  end
  else
    raise EIfaceFormatError.Create(
      'EncodeExpr: unhandled expression node ' + AE.ClassName);
end;

function EncodeExceptHandler(AH: TExceptHandlerClause): string;
begin
  Result := EncodeLpstr(AH.VarName) +
            EncodeLpstr(AH.TypeName) +
            EncodeStmt(AH.Body);
end;

function EncodeCaseBranch(AB: TCaseBranch): string;
begin
  Result := EncodeExprList(AB.Values) +
            EncodeStmt(AB.Stmt);
end;

function EncodeStmt(AStmt: TASTStmt): string;
var
  I: Integer;
  TES: TTryExceptStmt;
  CS:  TCaseStmt;
begin
  if AStmt = nil then begin Result := EncodeLpstr('nil'); Exit; end;

  if AStmt is TAssignment then
    Result := EncodeLpstr('asn') +
              EncodeLpstr(TAssignment(AStmt).Name) +
              EncodeExpr(TAssignment(AStmt).Expr)
  else if AStmt is TCompoundStmt then
    Result := EncodeLpstr('comp') +
              EncodeStmtList(TCompoundStmt(AStmt).Stmts)
  else if AStmt is TIfStmt then
    Result := EncodeLpstr('if') +
              EncodeExpr(TIfStmt(AStmt).Condition) +
              EncodeStmt(TIfStmt(AStmt).ThenStmt) +
              EncodeStmt(TIfStmt(AStmt).ElseStmt)
  else if AStmt is TWhileStmt then
    Result := EncodeLpstr('while') +
              EncodeExpr(TWhileStmt(AStmt).Condition) +
              EncodeStmt(TWhileStmt(AStmt).Body)
  else if AStmt is TRepeatStmt then
    Result := EncodeLpstr('rep') +
              EncodeStmt(TRepeatStmt(AStmt).Body) +
              EncodeExpr(TRepeatStmt(AStmt).Condition)
  else if AStmt is TForStmt then
    Result := EncodeLpstr('for') +
              EncodeLpstr(TForStmt(AStmt).VarName) +
              EncodeExpr (TForStmt(AStmt).StartExpr) +
              EncodeExpr (TForStmt(AStmt).EndExpr) +
              EncodeBool (TForStmt(AStmt).IsDownTo) +
              EncodeStmt (TForStmt(AStmt).Body)
  else if AStmt is TForInStmt then
    Result := EncodeLpstr('forin') +
              EncodeLpstr(TForInStmt(AStmt).VarName) +
              EncodeExpr (TForInStmt(AStmt).CollExpr) +
              EncodeStmt (TForInStmt(AStmt).Body)
  else if AStmt is TTryFinallyStmt then
    Result := EncodeLpstr('tryfin') +
              EncodeStmt(TTryFinallyStmt(AStmt).TryBody) +
              EncodeStmt(TTryFinallyStmt(AStmt).FinallyBody)
  else if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    Result := EncodeLpstr('tryex') +
              EncodeStmt (TES.TryBody) +
              EncodeCount(TES.Handlers.Count);
    for I := 0 to TES.Handlers.Count - 1 do
      Result := Result + EncodeExceptHandler(
        TExceptHandlerClause(TES.Handlers.Items[I]));
    Result := Result + EncodeStmt(TES.ElseBody) +
                       EncodeStmt(TES.ExceptBody);
  end
  else if AStmt is TRaiseStmt then
    Result := EncodeLpstr('raise') +
              EncodeExpr(TRaiseStmt(AStmt).Expr)
  else if AStmt is TExitStmt then
    { Carry the optional return value — 'Exit(expr)'.  Without it a cached
      generic-template body's 'Exit(-1)' round-trips as a bare 'Exit',
      leaving Result uninitialised (e.g. TDictionary.FindKey returns 0 not
      -1, so every key appears found at slot 0). }
    Result := EncodeLpstr('exit') +
              EncodeExpr(TExitStmt(AStmt).Value)
  else if AStmt is TBreakStmt then
    Result := EncodeLpstr('brk')
  else if AStmt is TContinueStmt then
    Result := EncodeLpstr('cont')
  else if AStmt is TCaseStmt then
  begin
    CS := TCaseStmt(AStmt);
    Result := EncodeLpstr('case') +
              EncodeExpr (CS.Selector) +
              EncodeCount(CS.Branches.Count);
    for I := 0 to CS.Branches.Count - 1 do
      Result := Result + EncodeCaseBranch(TCaseBranch(CS.Branches.Items[I]));
    Result := Result + EncodeStmt(CS.ElseStmt);
  end
  else if AStmt is TFieldAssignment then
    Result := EncodeLpstr('fasn') +
              EncodeLpstr(TFieldAssignment(AStmt).RecordName) +
              EncodeLpstr(TFieldAssignment(AStmt).FieldName) +
              EncodeExpr (TFieldAssignment(AStmt).Expr) +
              EncodeExpr (TFieldAssignment(AStmt).ObjExpr) +
              EncodeExpr (TFieldAssignment(AStmt).PropIndexExpr)
  else if AStmt is TStaticSubscriptAssign then
    Result := EncodeLpstr('ssasn') +
              EncodeLpstr(TStaticSubscriptAssign(AStmt).ArrayName) +
              EncodeExpr (TStaticSubscriptAssign(AStmt).IndexExpr) +
              EncodeExpr (TStaticSubscriptAssign(AStmt).ValueExpr) +
              EncodeExpr (TStaticSubscriptAssign(AStmt).BaseExpr)
  else if AStmt is TPointerWriteStmt then
    Result := EncodeLpstr('pw') +
              EncodeExpr(TPointerWriteStmt(AStmt).PtrExpr) +
              EncodeExpr(TPointerWriteStmt(AStmt).ValExpr)
  else if AStmt is TProcCall then
    Result := EncodeLpstr('pcall') +
              EncodeLpstr(TProcCall(AStmt).Name) +
              EncodeExprList(TProcCall(AStmt).Args)
  else if AStmt is TMethodCallStmt then
    Result := EncodeLpstr('mcs') +
              EncodeLpstr(TMethodCallStmt(AStmt).ObjectName) +
              EncodeLpstr(TMethodCallStmt(AStmt).Name) +
              EncodeExpr (TMethodCallStmt(AStmt).ObjExpr) +
              EncodeExprList(TMethodCallStmt(AStmt).Args)
  else if AStmt is TInheritedCallStmt then
    Result := EncodeLpstr('inh') +
              EncodeLpstr(TInheritedCallStmt(AStmt).Name) +
              EncodeExprList(TInheritedCallStmt(AStmt).Args)
  else if AStmt is TAsmStmt then
    Result := EncodeLpstr('asm') +
              EncodeLpstr(TAsmStmt(AStmt).Code)
  else if AStmt is TVarDeclStmt then
    { Block-scoped var declaration (Phase 4): name, type, optional init.
      Semantic outputs (InitAssign, env facts) are re-derived on import. }
    Result := EncodeLpstr('bvar') +
              EncodeLpstr(TVarDeclStmt(AStmt).Decl.Names.Strings[0]) +
              EncodeLpstr(TVarDeclStmt(AStmt).Decl.TypeName) +
              EncodeExpr(TVarDeclStmt(AStmt).InitExpr)
  else
    raise EIfaceFormatError.Create(
      'EncodeStmt: unhandled statement node ' + AStmt.ClassName);
end;

{ Block payload: flag, then a flattened list of statements.  Local
  decls (type/const/var/proc) inside the block are NOT serialised
  yet — bodies of generic free routines typically don't declare
  nested types, and the importer doesn't currently re-emit nested
  proc decls.  Add as needed; nil ABlock encodes as a single
  'nil' lpstr. }
{ Encode a block's local var declarations (names + type name).  Only
  the facts a downstream instantiation needs to declare the local into
  scope are emitted — initialisers and attributes are not required for
  generic template bodies (e.g. 'var Ptr: ^T') and are omitted.  Each
  TVarDecl is emitted flattened: one record per name. }
function EncodeBlockVarDecls(AB: TBlock): string;
var
  I, J:  Integer;
  VD:    TVarDecl;
  Total: Integer;
begin
  Total := 0;
  for I := 0 to AB.Decls.Count - 1 do
    Total := Total + TVarDecl(AB.Decls.Items[I]).Names.Count;
  Result := EncodeCount(Total);
  for I := 0 to AB.Decls.Count - 1 do
  begin
    VD := TVarDecl(AB.Decls.Items[I]);
    for J := 0 to VD.Names.Count - 1 do
      Result := Result + EncodeLpstr(VD.Names.Strings[J]) +
                         EncodeLpstr(VD.TypeName);
  end;
end;

function EncodeBlock(AB: TBlock): string;
begin
  if AB = nil then
  begin Result := EncodeLpstr('nil'); Exit; end;
  Result := EncodeLpstr('block') + EncodeStmtList(AB.Stmts) +
            EncodeBlockVarDecls(AB);
end;

{ Emit only generic free routines.  Generic class/interface
  templates are already in the TYPE block under 'generic-class' /
  'generic-interface' kinds — including those here would
  double-register.  Body AST is NOT serialised yet (no statement /
  expression writer); the wire-side MethodDecl comes back without
  a Body, which downstream instantiation will need.  Until the AST
  body serialiser lands, disk-loaded generic routines are
  signature-only. }
function WriteGenericRoutines(AIface: TUnitInterface): string;
var
  I:   Integer;
  G:   TGenericBody;
  SB:  TStringBuilder;
  Eligible: TObjectList;
begin
  Eligible := TObjectList.Create(False);
  SB := TStringBuilder.Create();
  try
    for I := 0 to AIface.GenericBodies.Count - 1 do
    begin
      G := TGenericBody(AIface.GenericBodies.Items[I]);
      if not G.IsType then Eligible.Add(G);
    end;
    SB.AppendLine('GENROUT ' + IntToStr(Eligible.Count));
    for I := 0 to Eligible.Count - 1 do
    begin
      G := TGenericBody(Eligible.Items[I]);
      SB.AppendLine(
        EncodeLpstr(G.Name) +
        EncodeTypeParamList(G.TypeParams, G.Constraints) +
        EncodeMethodDecl(G.MethodDecl) +
        EncodeBlock(G.MethodDecl.Body));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
    Eligible.Free();
  end;
end;

function WriteInlineBodies(AIface: TUnitInterface): string;
var
  I:  Integer;
  B:  TInlineBody;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('INLINE ' + IntToStr(AIface.InlineBodies.Count));
    for I := 0 to AIface.InlineBodies.Count - 1 do
    begin
      B := TInlineBody(AIface.InlineBodies.Items[I]);
      SB.AppendLine(EncodeLpstr(B.RoutineName) + EncodeBlock(B.Block));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function WriteUnitInterface(AIface: TUnitInterface): string;
begin
  Result :=
    IFACE_MAGIC + ' ' + IntToStr(IFACE_VERSION) + #10 +
    EncodeLpstr(AIface.Name) + #10 +
    WriteMeta           (AIface) +
    WriteTypes          (AIface) +
    WriteConsts         (AIface) +
    WriteVars           (AIface) +
    WriteRoutines       (AIface) +
    WriteGenericRoutines(AIface) +
    WriteInlineBodies   (AIface);
end;

{ ----- Reader ----------------------------------------------------- }

{ Cursor state passed by var-ref into the per-record readers — keeps
  the API surface scalar-friendly so we avoid the const-record-param
  string-field crash documented in memory. }

{ Char-classification on integer ordinals — Blaise lacks a Char
  type and S[i] returns a 1-byte string, so route through Ord() to
  get scalar Integer comparisons. }
function IsWhitespaceOrd(C: Integer): Boolean;
begin
  Result := (C = 32) or (C = 9) or (C = 10) or (C = 13);
end;

function IsUpperOrd(C: Integer): Boolean;
begin
  Result := (C >= Ord('A')) and (C <= Ord('Z'));
end;

function IsDigitOrd(C: Integer): Boolean;
begin
  Result := (C >= Ord('0')) and (C <= Ord('9'));
end;

{ Indexing convention throughout this unit: Blaise strings are
  0-indexed.  S[0] is the first byte; valid positions are 0 ..
  Length(S)-1.  Copy(S, start, len) treats start as 0-based.  Pos
  returns 0-based offset or -1 for not found.  APos cursor is
  0-based. }

procedure SkipWhitespace(const AText: string; var APos: Integer);
begin
  while (APos < Length(AText)) and IsWhitespaceOrd(Ord(AText[APos])) do
    Inc(APos);
end;

function ReadLpstrAt(const AText: string; var APos: Integer): string;
var
  ColonPos: Integer;
  Len:      Integer;
  LenStr:   string;
begin
  SkipWhitespace(AText, APos);
  ColonPos := APos;
  while (ColonPos < Length(AText)) and (AText[ColonPos] <> ':') do
    Inc(ColonPos);
  if ColonPos >= Length(AText) then
    raise EIfaceFormatError.Create('lpstr: missing '':'' separator');
  LenStr := Copy(AText, APos, ColonPos - APos);
  Len    := StrToInt(LenStr);
  if ColonPos + 1 + Len > Length(AText) then
    raise EIfaceFormatError.Create(Format(
      'lpstr: %d bytes requested, only %d available', [Len, Length(AText) - ColonPos - 1]));
  Result := Copy(AText, ColonPos + 1, Len);
  APos   := ColonPos + 1 + Len;
end;

function ReadInt64At(const AText: string; var APos: Integer): Int64;
begin
  Result := StrToInt64(ReadLpstrAt(AText, APos));
end;

function ReadFlagsAt(const AText: string; var APos: Integer;
                     out AIsString, AIsFloat: Boolean): Integer;
var
  B: Integer;
begin
  SkipWhitespace(AText, APos);
  if APos >= Length(AText) then
    raise EIfaceFormatError.Create('flags: end-of-input');
  B := Ord(AText[APos]) - Ord('0');
  Inc(APos);
  AIsString := (B and 1) <> 0;
  AIsFloat  := (B and 2) <> 0;
  Result := B;
end;

{ Split 'Unit.Type' into two strings.  Avoids passing TQualTypeRef
  records — same record-with-strings codegen bug that bit
  uSemanticImport.ResolveRef. }
procedure DecodeQualRef(const ASrc: string; var AUnit, AType: string);
var
  I, LastDot, PfxLen: Integer;
  Pfx: string;
begin
  { Blaise Pos and Copy are 0-based.  Split at the LAST '.', not the first:
    the unit qualifier may itself be dotted (e.g. 'blaise.testing'), while a
    NAMED type name never contains a dot.  Splitting at the first dot mangled a
    qualified type from a dotted unit — 'blaise.testing.TTestCase' decoded to
    unit='blaise', type='testing.TTestCase', so the bare type name was lost
    and a cached parent class could not be relinked (warm --unit-cache
    inherited-method resolution failure).

    EXCEPTION — inline/anonymous types (an array display name like
    'array[0..2] of string', a pointer, etc.) are stored under the synthetic
    '$builtin' unit and DO contain dots (the '..' range).  The last-dot split
    would take '2] of string' as the type name.  So when the ref starts with
    the '$builtin.' prefix, the unit is exactly '$builtin' and the rest —
    dots and all — is the type name (BUG-20260720-unit-iface-static-array-bif-
    roundtrip). }
  Pfx := QUALREF_BUILTIN + '.';
  PfxLen := Length(Pfx);
  if (Length(ASrc) >= PfxLen) and (Copy(ASrc, 0, PfxLen) = Pfx) then
  begin
    AUnit := QUALREF_BUILTIN;
    AType := Copy(ASrc, PfxLen, Length(ASrc) - PfxLen);
    Exit;
  end;
  LastDot := -1;
  for I := 0 to Length(ASrc) - 1 do
    if StrAt(ASrc, I) = Ord('.') then
      LastDot := I;
  if LastDot < 0 then
  begin
    AUnit := '';
    AType := ASrc;
  end
  else
  begin
    AUnit := Copy(ASrc, 0, LastDot);
    AType := Copy(ASrc, LastDot + 1, Length(ASrc) - LastDot - 1);
  end;
end;

{ Read an unterminated keyword (letters only) at the current cursor;
  consume it and advance past trailing whitespace.  Used for record
  tags ('CONST', 'END', etc.). }
function ReadTag(const AText: string; var APos: Integer): string;
var
  Start: Integer;
begin
  SkipWhitespace(AText, APos);
  Start := APos;
  while (APos < Length(AText)) and IsUpperOrd(Ord(AText[APos])) do
    Inc(APos);
  Result := Copy(AText, Start, APos - Start);
end;

function ReadDecimalAt(const AText: string; var APos: Integer): Integer;
var
  Start: Integer;
begin
  SkipWhitespace(AText, APos);
  Start := APos;
  while (APos < Length(AText)) and IsDigitOrd(Ord(AText[APos])) do
    Inc(APos);
  if APos = Start then
    raise EIfaceFormatError.Create('expected decimal digits');
  Result := StrToInt(Copy(AText, Start, APos - Start));
end;

procedure ReadHeader(const AText: string; var APos: Integer);
var
  MagicPos: Integer;
  Ver:      Integer;
begin
  SkipWhitespace(AText, APos);
  { Blaise Pos: 0-based result, -1 = not found.  Match at the
    cursor's current position means MagicPos = APos. }
  MagicPos := Pos(IFACE_MAGIC, AText);
  if MagicPos < 0 then
    raise EIfaceFormatError.Create('missing magic header');
  if MagicPos <> APos then
    raise EIfaceFormatError.Create(Format(
      'magic ''%s'' not at expected position %d (found at %d)',
      [IFACE_MAGIC, APos, MagicPos]));
  Inc(APos, Length(IFACE_MAGIC));
  SkipWhitespace(AText, APos);
  Ver := ReadDecimalAt(AText, APos);
  if Ver <> IFACE_VERSION then
    raise EIfaceFormatError.Create(Format(
      'unsupported version %d (this build understands %d)',
      [Ver, IFACE_VERSION]));
end;

procedure ReadConsts(const AText: string; var APos: Integer;
                     AIface: TUnitInterface);
var
  Count:    Integer;
  I:        Integer;
  Entry:    TConstEntry;
  Name:     string;
  RefStr:   string;
  IntVal:   Int64;
  StrVal:   string;
  IsString: Boolean;
  IsFloat:  Boolean;
  RefUnit:  string;
  RefType:  string;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Name     := ReadLpstrAt(AText, APos);
    RefStr   := ReadLpstrAt(AText, APos);
    IntVal   := ReadInt64At(AText, APos);
    StrVal   := ReadLpstrAt(AText, APos);
    ReadFlagsAt(AText, APos, IsString, IsFloat);
    DecodeQualRef(RefStr, RefUnit, RefType);

    Entry := TConstEntry.Create();
    Entry.Decl := TConstDecl.Create();
    Entry.Decl.Name     := Name;
    Entry.Decl.IntVal   := IntVal;
    Entry.Decl.StrVal   := StrVal;
    Entry.Decl.IsString := IsString;
    Entry.Decl.IsFloat  := IsFloat;
    Entry.TypeRef       := MakeQualRef(RefUnit, RefType);
    AIface.AddConst(Entry);
  end;
  { Trailing 'END' marker — keeps the format extensible: future
    record types follow the same tag/payload/END pattern. }
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('CONST block: missing END marker');
end;

procedure ReadVars(const AText: string; var APos: Integer;
                   AIface: TUnitInterface);
var
  Count:   Integer;
  I:       Integer;
  Entry:   TVarEntry;
  RefStr:  string;
  RefUnit: string;
  RefType: string;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Entry := TVarEntry.Create();
    Entry.Name := ReadLpstrAt(AText, APos);
    RefStr     := ReadLpstrAt(AText, APos);
    DecodeQualRef(RefStr, RefUnit, RefType);
    Entry.TypeRef    := MakeQualRef(RefUnit, RefType);
    Entry.IsThreadVar := DecodeBool(AText, APos);
    AIface.AddVar(Entry);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('VAR block: missing END marker');
end;

{ Split a comma-joined member list back into a TStringList.  Empty
  input ⇒ empty list. }
procedure SplitMembers(const ASrc: string; ATarget: TStringList);
var
  Cur: string;
  P:   Integer;
begin
  Cur := ASrc;
  P   := Pos(',', Cur);
  while P >= 0 do
  begin
    ATarget.Add(Copy(Cur, 0, P));
    Cur := Copy(Cur, P + 1, Length(Cur) - P - 1);
    P   := Pos(',', Cur);
  end;
  if Length(Cur) > 0 then ATarget.Add(Cur);
end;

{ Parse 'name=ord,name=ord,…' into an EnumTypeDef using AddMember so
  the ordinal stash lands in Members.Objects[i] (where OrdinalAt
  reads it back from). }
procedure LoadEnumMembers(const ASrc: string; AEnum: TEnumTypeDef);
var
  Pairs: TStringList;
  I:     Integer;
  Pair:  string;
  Eq:    Integer;
  NameP: string;
  OrdP:  Integer;
begin
  Pairs := TStringList.Create();
  try
    SplitMembers(ASrc, Pairs);
    for I := 0 to Pairs.Count - 1 do
    begin
      Pair := Pairs.Strings[I];
      Eq   := Pos('=', Pair);
      if Eq < 0 then
      begin
        { Tolerate bare names from an older/hand-written .bif —
          assume sequential ordinals. }
        AEnum.AddMember(Pair, I);
      end
      else
      begin
        NameP := Copy(Pair, 0, Eq);
        OrdP  := StrToInt(Copy(Pair, Eq + 1, Length(Pair) - Eq - 1));
        AEnum.AddMember(NameP, OrdP);
      end;
    end;
  finally
    Pairs.Free();
  end;
end;

function ReadExpr(const AText: string; var APos: Integer): TASTExpr; forward;
function ReadStmt(const AText: string; var APos: Integer): TASTStmt; forward;
function ReadBlock(const AText: string; var APos: Integer): TBlock; forward;
function ReadMethodDecl(const AText: string; var APos: Integer): TMethodDecl; forward;

procedure ReadExprList(const AText: string; var APos: Integer;
                       ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := StrToInt(ReadLpstrAt(AText, APos));
  for I := 1 to C do ATarget.Add(ReadExpr(AText, APos));
end;

procedure ReadStmtList(const AText: string; var APos: Integer;
                       ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := StrToInt(ReadLpstrAt(AText, APos));
  for I := 1 to C do ATarget.Add(ReadStmt(AText, APos));
end;

function ReadExceptHandler(const AText: string; var APos: Integer):
  TExceptHandlerClause;
var
  Body: TASTStmt;
begin
  Result := TExceptHandlerClause.Create();
  Result.VarName  := ReadLpstrAt(AText, APos);
  Result.TypeName := ReadLpstrAt(AText, APos);
  Body := ReadStmt(AText, APos);
  if Body is TCompoundStmt then
    Result.Body := TCompoundStmt(Body)
  else
  begin
    { Body always encoded via EncodeStmt of a TCompoundStmt — should
      never see anything else.  Defensive: wrap. }
    Result.Body := TCompoundStmt.Create();
    if Body <> nil then Result.Body.Stmts.Add(Body);
  end;
end;

function ReadCaseBranch(const AText: string; var APos: Integer): TCaseBranch;
begin
  Result := TCaseBranch.Create();
  ReadExprList(AText, APos, Result.Values);
  Result.Stmt := ReadStmt(AText, APos);
end;

function ReadExpr(const AText: string; var APos: Integer): TASTExpr;
var
  Kind: string;
  IL:   TIntLiteral;
  FL:   TFloatLiteral;
  SL:   TStringLiteral;
  IE:   TIdentExpr;
  BE:   TBinaryExpr;
  NE:   TNotExpr;
  FCE:  TFuncCallExpr;
  ICE:  TIndirectFuncCallExpr;
  MCE:  TMethodCallExpr;
  FA:   TFieldAccessExpr;
  DE:   TDerefExpr;
  AoE:  TAddrOfExpr;
  SS:   TStringSubscriptExpr;
  AL:   TArrayLiteralExpr;
  SRE:  TSetRangeExpr;
  IsE:  TIsExpr;
  AsE:  TAsExpr;
  SuE:  TSupportsExpr;
  InhE: TInheritedCallExpr;
  AME:  TAnonMethodExpr;
begin
  Kind := ReadLpstrAt(AText, APos);
  if Kind = 'nil' then begin Result := nil; Exit; end;

  if Kind = 'int' then
  begin
    IL := TIntLiteral.Create();
    IL.Value := StrToInt64(ReadLpstrAt(AText, APos));
    Result := IL;
  end
  else if Kind = 'float' then
  begin
    FL := TFloatLiteral.Create();
    FL.Value := ReadLpstrAt(AText, APos);
    Result := FL;
  end
  else if Kind = 'str' then
  begin
    SL := TStringLiteral.Create();
    SL.Value := ReadLpstrAt(AText, APos);
    Result := SL;
  end
  else if Kind = 'nillit' then
    Result := TNilLiteral.Create()
  else if Kind = 'id' then
  begin
    IE := TIdentExpr.Create();
    IE.Name := ReadLpstrAt(AText, APos);
    IE.QualifierUnit := ReadLpstrAt(AText, APos);
    Result := IE;
  end
  else if Kind = 'bin' then
  begin
    BE := TBinaryExpr.Create();
    BE.Op    := TBinaryOp(StrToInt(ReadLpstrAt(AText, APos)));
    BE.Left  := ReadExpr(AText, APos);
    BE.Right := ReadExpr(AText, APos);
    Result := BE;
  end
  else if Kind = 'not' then
  begin
    NE := TNotExpr.Create();
    NE.Expr := ReadExpr(AText, APos);
    Result := NE;
  end
  else if Kind = 'call' then
  begin
    FCE := TFuncCallExpr.Create();
    FCE.Name := ReadLpstrAt(AText, APos);
    ReadExprList(AText, APos, FCE.Args);
    Result := FCE;
  end
  else if Kind = 'mcall' then
  begin
    MCE := TMethodCallExpr.Create();
    MCE.ObjectName    := ReadLpstrAt(AText, APos);
    MCE.Name          := ReadLpstrAt(AText, APos);
    MCE.QualifierUnit := ReadLpstrAt(AText, APos);
    MCE.ObjExpr       := ReadExpr(AText, APos);
    ReadExprList(AText, APos, MCE.Args);
    Result := MCE;
  end
  else if Kind = 'icall' then
  begin
    ICE := TIndirectFuncCallExpr.Create();
    ICE.CalleeExpr := ReadExpr(AText, APos);
    ReadExprList(AText, APos, ICE.Args);
    Result := ICE;
  end
  else if Kind = 'field' then
  begin
    FA := TFieldAccessExpr.Create();
    FA.RecordName    := ReadLpstrAt(AText, APos);
    FA.FieldName     := ReadLpstrAt(AText, APos);
    FA.QualifierUnit := ReadLpstrAt(AText, APos);
    FA.Base          := ReadExpr(AText, APos);
    FA.PropIndexExpr := ReadExpr(AText, APos);
    Result := FA;
  end
  else if Kind = 'deref' then
  begin
    DE := TDerefExpr.Create();
    DE.Expr := ReadExpr(AText, APos);
    Result := DE;
  end
  else if Kind = 'addr' then
  begin
    AoE := TAddrOfExpr.Create();
    AoE.Expr := ReadExpr(AText, APos);
    Result := AoE;
  end
  else if Kind = 'ssub' then
  begin
    SS := TStringSubscriptExpr.Create();
    SS.StrExpr   := ReadExpr(AText, APos);
    SS.IndexExpr := ReadExpr(AText, APos);
    Result := SS;
  end
  else if Kind = 'alit' then
  begin
    AL := TArrayLiteralExpr.Create();
    ReadExprList(AText, APos, AL.Elements);
    Result := AL;
  end
  else if Kind = 'srng' then
  begin
    SRE := TSetRangeExpr.Create();
    SRE.LowExpr  := ReadExpr(AText, APos);
    SRE.HighExpr := ReadExpr(AText, APos);
    Result := SRE;
  end
  else if Kind = 'isop' then
  begin
    IsE := TIsExpr.Create();
    IsE.Obj      := ReadExpr(AText, APos);
    IsE.TypeName := ReadLpstrAt(AText, APos);
    Result := IsE;
  end
  else if Kind = 'asop' then
  begin
    AsE := TAsExpr.Create();
    AsE.Obj      := ReadExpr(AText, APos);
    AsE.TypeName := ReadLpstrAt(AText, APos);
    Result := AsE;
  end
  else if Kind = 'supp' then
  begin
    SuE := TSupportsExpr.Create();
    SuE.Obj          := ReadExpr(AText, APos);
    SuE.IntfTypeName := ReadLpstrAt(AText, APos);
    SuE.OutVarName   := ReadLpstrAt(AText, APos);
    Result := SuE;
  end
  else if Kind = 'inhc' then
  begin
    InhE := TInheritedCallExpr.Create();
    InhE.Name := ReadLpstrAt(AText, APos);
    ReadExprList(AText, APos, InhE.Args);
    Result := InhE;
  end
  else if Kind = 'anonm' then
  begin
    { Anonymous-method literal (generic-body template).  Mirrors the
      encoder: signature decl, body block, optional [Weak] name list.
      LiftedName/LiftedDecl/EnvType are semantic outputs, re-derived at
      the importer's monomorphisation site. }
    AME := TAnonMethodExpr.Create();
    AME.Decl := ReadMethodDecl(AText, APos);
    AME.Decl.Body := ReadBlock(AText, APos);
    AME.Decl.OwnBody := True;
    if DecodeBool(AText, APos) then
    begin
      AME.WeakCaptures := TStringList.Create();
      ReadStringListBlock(AText, APos, AME.WeakCaptures);
    end;
    AME.IsArrow := DecodeBool(AText, APos);
    if DecodeBool(AText, APos) then
      AME.ArrowExpr := ReadExpr(AText, APos);
    Result := AME;
  end
  else
    raise EIfaceFormatError.Create(
      'ReadExpr: unknown expression kind ''' + Kind + '''');
end;

function ReadStmt(const AText: string; var APos: Integer): TASTStmt;
var
  Kind: string;
  ASn:  TAssignment;
  CSn:  TCompoundStmt;
  IFn:  TIfStmt;
  WSn:  TWhileStmt;
  RSn:  TRepeatStmt;
  FSn:  TForStmt;
  FISn: TForInStmt;
  TFSn: TTryFinallyStmt;
  TESn: TTryExceptStmt;
  RaSn: TRaiseStmt;
  ESn:  TExitStmt;
  CSSn: TCaseStmt;
  FASn: TFieldAssignment;
  SSAn: TStaticSubscriptAssign;
  PWSn: TPointerWriteStmt;
  PCn:  TProcCall;
  VDSn: TVarDeclStmt;
  MCSn: TMethodCallStmt;
  ICSn: TInheritedCallStmt;
  ASMn: TAsmStmt;
  C, I: Integer;
  Body: TASTStmt;
begin
  Kind := ReadLpstrAt(AText, APos);
  if Kind = 'nil' then begin Result := nil; Exit; end;

  if Kind = 'asn' then
  begin
    ASn := TAssignment.Create();
    ASn.Name := ReadLpstrAt(AText, APos);
    ASn.Expr := ReadExpr(AText, APos);
    Result := ASn;
  end
  else if Kind = 'comp' then
  begin
    CSn := TCompoundStmt.Create();
    ReadStmtList(AText, APos, CSn.Stmts);
    Result := CSn;
  end
  else if Kind = 'if' then
  begin
    IFn := TIfStmt.Create();
    IFn.Condition := ReadExpr(AText, APos);
    IFn.ThenStmt  := ReadStmt(AText, APos);
    IFn.ElseStmt  := ReadStmt(AText, APos);
    Result := IFn;
  end
  else if Kind = 'while' then
  begin
    WSn := TWhileStmt.Create();
    WSn.Condition := ReadExpr(AText, APos);
    WSn.Body      := ReadStmt(AText, APos);
    Result := WSn;
  end
  else if Kind = 'rep' then
  begin
    RSn := TRepeatStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then
      RSn.Body := TCompoundStmt(Body)
    else
    begin
      RSn.Body := TCompoundStmt.Create();
      if Body <> nil then RSn.Body.Stmts.Add(Body);
    end;
    RSn.Condition := ReadExpr(AText, APos);
    Result := RSn;
  end
  else if Kind = 'for' then
  begin
    FSn := TForStmt.Create();
    FSn.VarName   := ReadLpstrAt(AText, APos);
    FSn.StartExpr := ReadExpr(AText, APos);
    FSn.EndExpr   := ReadExpr(AText, APos);
    FSn.IsDownTo  := DecodeBool(AText, APos);
    FSn.Body      := ReadStmt(AText, APos);
    Result := FSn;
  end
  else if Kind = 'forin' then
  begin
    FISn := TForInStmt.Create();
    FISn.VarName  := ReadLpstrAt(AText, APos);
    FISn.CollExpr := ReadExpr(AText, APos);
    FISn.Body     := ReadStmt(AText, APos);
    Result := FISn;
  end
  else if Kind = 'tryfin' then
  begin
    TFSn := TTryFinallyStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TFSn.TryBody := TCompoundStmt(Body)
                              else TFSn.TryBody := TCompoundStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TFSn.FinallyBody := TCompoundStmt(Body)
                              else TFSn.FinallyBody := TCompoundStmt.Create();
    Result := TFSn;
  end
  else if Kind = 'tryex' then
  begin
    TESn := TTryExceptStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TESn.TryBody := TCompoundStmt(Body)
                              else TESn.TryBody := TCompoundStmt.Create();
    C := StrToInt(ReadLpstrAt(AText, APos));
    for I := 1 to C do
      TESn.Handlers.Add(ReadExceptHandler(AText, APos));
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TESn.ElseBody := TCompoundStmt(Body)
                              else TESn.ElseBody := nil;
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TESn.ExceptBody := TCompoundStmt(Body)
                              else TESn.ExceptBody := nil;
    Result := TESn;
  end
  else if Kind = 'raise' then
  begin
    RaSn := TRaiseStmt.Create();
    RaSn.Expr := ReadExpr(AText, APos);
    Result := RaSn;
  end
  else if Kind = 'exit' then
  begin
    ESn := TExitStmt.Create();
    ESn.Value := ReadExpr(AText, APos);   { nil for bare 'Exit' }
    Result := ESn;
  end
  else if Kind = 'brk'  then Result := TBreakStmt.Create()
  else if Kind = 'cont' then Result := TContinueStmt.Create()
  else if Kind = 'case' then
  begin
    CSSn := TCaseStmt.Create();
    CSSn.Selector := ReadExpr(AText, APos);
    C := StrToInt(ReadLpstrAt(AText, APos));
    for I := 1 to C do
      CSSn.Branches.Add(ReadCaseBranch(AText, APos));
    CSSn.ElseStmt := ReadStmt(AText, APos);
    Result := CSSn;
  end
  else if Kind = 'fasn' then
  begin
    FASn := TFieldAssignment.Create();
    FASn.RecordName    := ReadLpstrAt(AText, APos);
    FASn.FieldName     := ReadLpstrAt(AText, APos);
    FASn.Expr          := ReadExpr(AText, APos);
    FASn.ObjExpr       := ReadExpr(AText, APos);
    FASn.PropIndexExpr := ReadExpr(AText, APos);
    Result := FASn;
  end
  else if Kind = 'ssasn' then
  begin
    SSAn := TStaticSubscriptAssign.Create();
    SSAn.ArrayName := ReadLpstrAt(AText, APos);
    SSAn.IndexExpr := ReadExpr(AText, APos);
    SSAn.ValueExpr := ReadExpr(AText, APos);
    SSAn.BaseExpr  := ReadExpr(AText, APos);
    Result := SSAn;
  end
  else if Kind = 'pw' then
  begin
    PWSn := TPointerWriteStmt.Create();
    PWSn.PtrExpr := ReadExpr(AText, APos);
    PWSn.ValExpr := ReadExpr(AText, APos);
    Result := PWSn;
  end
  else if Kind = 'pcall' then
  begin
    PCn := TProcCall.Create();
    PCn.Name := ReadLpstrAt(AText, APos);
    ReadExprList(AText, APos, PCn.Args);
    Result := PCn;
  end
  else if Kind = 'mcs' then
  begin
    MCSn := TMethodCallStmt.Create();
    MCSn.ObjectName := ReadLpstrAt(AText, APos);
    MCSn.Name       := ReadLpstrAt(AText, APos);
    MCSn.ObjExpr    := ReadExpr(AText, APos);
    ReadExprList(AText, APos, MCSn.Args);
    Result := MCSn;
  end
  else if Kind = 'inh' then
  begin
    ICSn := TInheritedCallStmt.Create();
    ICSn.Name := ReadLpstrAt(AText, APos);
    ReadExprList(AText, APos, ICSn.Args);
    Result := ICSn;
  end
  else if Kind = 'asm' then
  begin
    ASMn := TAsmStmt.Create();
    ASMn.Code := ReadLpstrAt(AText, APos);
    Result := ASMn;
  end
  else if Kind = 'bvar' then
  begin
    VDSn := TVarDeclStmt.Create();
    VDSn.Decl := TVarDecl.Create();
    VDSn.Decl.IsBlockScoped := True;
    VDSn.Decl.Names.Add(ReadLpstrAt(AText, APos));
    VDSn.Decl.TypeName := ReadLpstrAt(AText, APos);
    VDSn.InitExpr := ReadExpr(AText, APos);
    Result := VDSn;
  end
  else
    raise EIfaceFormatError.Create(
      'ReadStmt: unknown statement kind ''' + Kind + '''');
end;

function ReadBlock(const AText: string; var APos: Integer): TBlock;
var
  Kind:    string;
  C, I:    Integer;
  VarName: string;
  VarType: string;
  VD:      TVarDecl;
begin
  Kind := ReadLpstrAt(AText, APos);
  if Kind = 'nil' then begin Result := nil; Exit; end;
  if Kind <> 'block' then
    raise EIfaceFormatError.Create('ReadBlock: expected ''block'' got ''' + Kind + '''');
  Result := TBlock.Create();
  ReadStmtList(AText, APos, Result.Stmts);
  { Local var declarations (v3+): one flattened record per name. }
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    VarName := ReadLpstrAt(AText, APos);
    VarType := ReadLpstrAt(AText, APos);
    VD := TVarDecl.Create();
    VD.Names.Add(VarName);
    VD.TypeName := VarType;
    Result.Decls.Add(VD);
  end;
end;

function DecodeCount(const AText: string; var APos: Integer): Integer;
begin
  Result := StrToInt(ReadLpstrAt(AText, APos));
end;

function DecodeBool(const AText: string; var APos: Integer): Boolean;
begin
  Result := ReadLpstrAt(AText, APos) = '1';
end;

procedure ReadStringListBlock(const AText: string; var APos: Integer;
                              ATarget: TStringList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do ATarget.Add(ReadLpstrAt(AText, APos));
end;

{ Read a flattened field list into a TRecordTypeDef's Fields list.
  Each field is emitted with a single Name (the writer flattened
  multi-name decls); the reader rebuilds one TFieldDecl per name. }
procedure ReadFieldList(const AText: string; var APos: Integer;
                        ATarget: TObjectList);
var
  C, I:        Integer;
  FldName:     string;
  FldType:     string;
  IsWeak:      Boolean;
  IsClassVar:  Boolean;
  ClassVarEmit: string;
  Vis:         Integer;
  F:           TFieldDecl;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    FldName := ReadLpstrAt(AText, APos);
    FldType := ReadLpstrAt(AText, APos);
    IsWeak  := DecodeBool(AText, APos);
    { Order must mirror EncodeFieldList: IsClassVar then ClassVarEmitName
      then the visibility ordinal. }
    IsClassVar   := DecodeBool(AText, APos);
    ClassVarEmit := ReadLpstrAt(AText, APos);
    Vis          := StrToInt(ReadLpstrAt(AText, APos));
    F := TFieldDecl.Create();
    F.Names.Add(FldName);
    F.TypeName := FldType;
    F.IsWeak   := IsWeak;
    F.IsClassVar      := IsClassVar;
    F.ClassVarEmitName := ClassVarEmit;
    F.Visibility := TMemberVisibility(Vis);
    ATarget.Add(F);
  end;
end;

{ Inverse of EncodeConstDeclList — rebuild record/class `static const`
  decls.  Mirrors the writer's five-field scalar shape exactly. }
procedure ReadConstDeclList(const AText: string; var APos: Integer;
                            ATarget: TObjectList);
var
  C, I:     Integer;
  CD:       TConstDecl;
  IsString: Boolean;
  IsFloat:  Boolean;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    CD := TConstDecl.Create();
    CD.Name     := ReadLpstrAt(AText, APos);
    CD.TypeName := ReadLpstrAt(AText, APos);
    CD.IntVal   := ReadInt64At(AText, APos);
    CD.StrVal   := ReadLpstrAt(AText, APos);
    ReadFlagsAt(AText, APos, IsString, IsFloat);
    CD.IsString := IsString;
    CD.IsFloat  := IsFloat;
    ATarget.Add(CD);
  end;
end;

{ Inverse of EncodeMethodSig — builds a TRoutineSig from the
  per-method payload. }
function ReadMethodSig(const AText: string; var APos: Integer): TRoutineSig;
var
  RefStr:   string;
  RefUnit:  string;
  RefType:  string;
  Pc, J:    Integer;
  Param:    TMethodParam;
  FlagsStr: string;
begin
  Result := TRoutineSig.Create();
  Result.Name        := ReadLpstrAt(AText, APos);
  Result.IsFunction  := DecodeBool(AText, APos);
  RefStr             := ReadLpstrAt(AText, APos);
  DecodeQualRef(RefStr, RefUnit, RefType);
  Result.ReturnType  := MakeQualRef(RefUnit, RefType);
  Result.IsVirtual   := DecodeBool(AText, APos);
  Result.IsOverride  := DecodeBool(AText, APos);
  Result.ResolvedQbeName := ReadLpstrAt(AText, APos);
  Result.VTableSlot  := StrToInt(ReadLpstrAt(AText, APos));
  { Order must mirror EncodeMethodSig: IsStatic follows VTableSlot, then
    IsOverload, then the visibility ordinal. }
  Result.IsStatic    := DecodeBool(AText, APos);
  Result.IsOverload  := DecodeBool(AText, APos);
  Result.Visibility  := TMemberVisibility(StrToInt(ReadLpstrAt(AText, APos)));
  { Generic-method type params (Phase 10). }
  if DecodeBool(AText, APos) then
  begin
    Result.TypeParams := TStringList.Create();
    ReadStringListBlock(AText, APos, Result.TypeParams);
    if DecodeBool(AText, APos) then
    begin
      Result.TypeParamConstraints := TStringList.Create();
      ReadStringListBlock(AText, APos, Result.TypeParamConstraints);
    end;
  end;
  Pc := DecodeCount(AText, APos);
  for J := 1 to Pc do
  begin
    Param := TMethodParam.Create();
    Param.ParamName := ReadLpstrAt(AText, APos);
    Param.TypeName  := ReadLpstrAt(AText, APos);
    FlagsStr := ReadLpstrAt(AText, APos);
    DecodeParamFlags(StrToInt(FlagsStr), Param);
    Param.DefaultValue := ReadExpr(AText, APos);
    Result.Params.Add(Param);
  end;
end;

procedure ReadMethodList(const AText: string; var APos: Integer;
                         ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do ATarget.Add(ReadMethodSig(AText, APos));
end;

procedure ReadRecordPayload(const AText: string; var APos: Integer;
                            AEntry: TTypeEntry);
var
  Def: TRecordTypeDef;
begin
  Def := TRecordTypeDef.Create();
  Def.IsPacked := DecodeBool(AText, APos);
  ReadFieldList(AText, APos, Def.Fields);
  ReadMethodList(AText, APos, AEntry.Methods);   { v13 }
  ReadConstDeclList(AText, APos, Def.ConstDecls);
  AEntry.Def := Def;
end;

procedure ReadClassPayload(const AText: string; var APos: Integer;
                           AEntry: TTypeEntry);
var
  Def:     TClassTypeDef;
  RefStr:  string;
  RefUnit: string;
  RefType: string;
begin
  Def := TClassTypeDef.Create();
  RefStr := ReadLpstrAt(AText, APos);
  DecodeQualRef(RefStr, RefUnit, RefType);
  AEntry.ParentClass  := MakeQualRef(RefUnit, RefType);
  Def.ParentName      := RefType;
  AEntry.InstanceSize := StrToInt64(ReadLpstrAt(AText, APos));
  ReadStringListBlock(AText, APos, AEntry.Attributes);
  ReadStringListBlock(AText, APos, AEntry.Implements);
  ReadFieldList(AText, APos, Def.Fields);
  ReadMethodList(AText, APos, AEntry.Methods);
  ReadPropertyList(AText, APos, Def.Properties);
  ReadConstDeclList(AText, APos, Def.ConstDecls);
  AEntry.IsClass := True;
  AEntry.Def     := Def;
end;

function ReadMethodDecl(const AText: string; var APos: Integer): TMethodDecl;
var
  HasReturn: Boolean;
  Pc, J:     Integer;
  Param:     TMethodParam;
  FlagsStr:  string;
begin
  Result := TMethodDecl.Create();
  Result.Name           := ReadLpstrAt(AText, APos);
  HasReturn             := DecodeBool(AText, APos);
  Result.ReturnTypeName := ReadLpstrAt(AText, APos);
  if not HasReturn then Result.ReturnTypeName := '';
  Result.IsVirtual      := DecodeBool(AText, APos);
  Result.IsOverride     := DecodeBool(AText, APos);
  Result.IsOverload     := DecodeBool(AText, APos);
  { Order must mirror EncodeMethodDecl: IsStatic follows IsOverload. }
  Result.IsStatic       := DecodeBool(AText, APos);
  Pc := DecodeCount(AText, APos);
  for J := 1 to Pc do
  begin
    Param := TMethodParam.Create();
    Param.ParamName := ReadLpstrAt(AText, APos);
    Param.TypeName  := ReadLpstrAt(AText, APos);
    FlagsStr := ReadLpstrAt(AText, APos);
    DecodeParamFlags(StrToInt(FlagsStr), Param);
    Param.DefaultValue := ReadExpr(AText, APos);
    Result.Params.Add(Param);
  end;
end;

procedure ReadMethodDeclList(const AText: string; var APos: Integer;
                             ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do ATarget.Add(ReadMethodDecl(AText, APos));
end;

procedure ReadPropertyList(const AText: string; var APos: Integer;
                           ATarget: TObjectList);
var
  C, I: Integer;
  P:    TPropertyDecl;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    P := TPropertyDecl.Create();
    P.Name           := ReadLpstrAt(AText, APos);
    P.TypeName       := ReadLpstrAt(AText, APos);
    P.ReadName       := ReadLpstrAt(AText, APos);
    P.WriteName      := ReadLpstrAt(AText, APos);
    P.IndexParamName := ReadLpstrAt(AText, APos);
    P.IndexTypeName  := ReadLpstrAt(AText, APos);
    P.IsDefault      := DecodeBool(AText, APos);
    { Order must mirror EncodePropertyList: IsStatic follows IsDefault, then
      the visibility ordinal. }
    P.IsStatic       := DecodeBool(AText, APos);
    P.Visibility     := TMemberVisibility(StrToInt(ReadLpstrAt(AText, APos)));
    ATarget.Add(P);
  end;
end;

procedure ReadInlineBodies(const AText: string; var APos: Integer;
                           AIface: TUnitInterface);
var
  Count, I: Integer;
  B:        TInlineBody;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    B := TInlineBody.Create();
    B.RoutineName := ReadLpstrAt(AText, APos);
    B.Block       := ReadBlock(AText, APos);
    AIface.AddInlineBody(B);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('INLINE block: missing END marker');
end;

procedure ReadGenericRoutines(const AText: string; var APos: Integer;
                              AIface: TUnitInterface);
var
  Count, I, J: Integer;
  G:           TGenericBody;
  Name:        string;
  MD:          TMethodDecl;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Name := ReadLpstrAt(AText, APos);
    G := TGenericBody.Create();
    G.Name   := Name;
    G.IsType := False;
    ReadTypeParamList(AText, APos, G.TypeParams, G.Constraints);
    MD := ReadMethodDecl(AText, APos);
    { ReadMethodDecl doesn't reconstitute TypeParams (the
      method-decl payload omits them — they're encoded once at the
      GenericBody level).  Copy them across so a downstream
      instantiation sees a complete TMethodDecl template. }
    MD.TypeParams := TStringList.Create();
    for J := 0 to G.TypeParams.Count - 1 do
      MD.TypeParams.Add(G.TypeParams.Strings[J]);
    MD.Body := ReadBlock(AText, APos);
    if MD.Body <> nil then MD.OwnBody := True;
    G.MethodDecl := MD;
    AIface.AddGenericBody(G);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('GENROUT block: missing END marker');
end;

procedure ReadMeta(const AText: string; var APos: Integer;
                   AIface: TUnitInterface);
var
  C, I: Integer;
begin
  AIface.SourceFile    := ReadLpstrAt(AText, APos);
  AIface.SourceHash    := ReadLpstrAt(AText, APos);
  AIface.CompilerId    := ReadLpstrAt(AText, APos);
  AIface.SourceModTime := ReadInt64At(AText, APos);
  C := DecodeCount(AText, APos);
  for I := 1 to C do
    AIface.UsedUnits.Add(ReadLpstrAt(AText, APos));
  C := DecodeCount(AText, APos);
  for I := 1 to C do
    AIface.ImplUsedUnits.Add(ReadLpstrAt(AText, APos));
  C := DecodeCount(AText, APos);
  for I := 1 to C do
    AIface.LinkLibs.Add(ReadLpstrAt(AText, APos));
  AIface.HasInitialization := ReadLpstrAt(AText, APos) = '1';
  AIface.HasFinalization := ReadLpstrAt(AText, APos) = '1';
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('META block: missing END marker');
end;

procedure ReadTypeParamList(const AText: string; var APos: Integer;
                            ANames, AConstraints: TStringList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    ANames.Add(ReadLpstrAt(AText, APos));
    AConstraints.Add(ReadLpstrAt(AText, APos));
  end;
end;

{ AUnitName is the interface being imported.  It is stamped onto each
  rebuilt method decl because the visibility check treats an EMPTY declaring
  unit as "same unit" (uSemantic.MemberVisibleTo) — so without it a private
  method on an imported generic is visible everywhere. }
procedure ReadGenericClassPayload(const AText: string; var APos: Integer;
                                  AEntry: TTypeEntry;
                                  const AUnitName: string);
var
  Def:      TGenericTypeDef;
  ClassDef: TClassTypeDef;
  RefStr:   string;
  RefUnit:  string;
  RefType:  string;
  J, K:     Integer;
  Sig:      TRoutineSig;
  MD:       TMethodDecl;
  SrcPar:   TMethodParam;
  NewPar:   TMethodParam;
begin
  Def := TGenericTypeDef.Create();
  ReadTypeParamList(AText, APos, Def.ParamNames, Def.ParamConstraints);

  { Inner ClassDef: the ctor already created an empty one — free
    it and rebuild from the wire. }
  Def.ClassDef.Free();
  ClassDef := TClassTypeDef.Create();
  Def.ClassDef := ClassDef;

  RefStr := ReadLpstrAt(AText, APos);
  DecodeQualRef(RefStr, RefUnit, RefType);
  AEntry.ParentClass  := MakeQualRef(RefUnit, RefType);
  ClassDef.ParentName := RefType;
  AEntry.InstanceSize := StrToInt64(ReadLpstrAt(AText, APos));
  ReadStringListBlock(AText, APos, AEntry.Attributes);
  ReadStringListBlock(AText, APos, AEntry.Implements);
  ReadFieldList(AText, APos, ClassDef.Fields);
  ReadMethodList(AText, APos, AEntry.Methods);

  { Method bodies — parallel to AEntry.Methods, attached to
    ClassDef.Methods as full TMethodDecl objects so InstantiateGeneric
    can clone + substitute when the consumer references this template. }
  for J := 0 to AEntry.Methods.Count - 1 do
  begin
    Sig := TRoutineSig(AEntry.Methods.Items[J]);
    MD := TMethodDecl.Create();
    MD.Name           := Sig.Name;
    MD.OwnerTypeName  := AEntry.Name;
    MD.IsVirtual      := Sig.IsVirtual;
    MD.IsOverride     := Sig.IsOverride;
    { IsStatic must be carried across too: the sig has recorded it since v4,
      but this rebuild dropped it, so a `static` method on an imported GENERIC
      became non-static in the consumer and TSet<string>.From(...) was
      rejected as "not a static method".  Inside the declaring unit the same
      code worked, because there the template AST is used directly. }
    MD.IsStatic       := Sig.IsStatic;
    MD.IsOverload     := Sig.IsOverload;
    { Visibility likewise — the sig has carried it since v5, but dropping it
      here left the rebuilt decl at its zero value (mvPublic), so a `private`
      method on an imported GENERIC was callable from any unit while the same
      method on a non-generic class was correctly rejected. }
    MD.Visibility     := Sig.Visibility;
    { OwningUnit must travel with Visibility: MemberVisibleTo treats an empty
      declaring unit as same-unit (so program-scope types and pre-visibility
      imports are not locked out), which would silently defeat the check. }
    MD.OwningUnit     := AUnitName;
    MD.ReturnTypeName := Sig.ReturnType.TypeName;
    if Sig.TypeParams <> nil then
    begin
      MD.TypeParams := TStringList.Create();
      MD.TypeParams.AddStrings(Sig.TypeParams);
      if Sig.TypeParamConstraints <> nil then
      begin
        MD.TypeParamConstraints := TStringList.Create();
        MD.TypeParamConstraints.AddStrings(Sig.TypeParamConstraints);
      end;
    end;
    for K := 0 to Sig.Params.Count - 1 do
    begin
      SrcPar := TMethodParam(Sig.Params.Items[K]);
      NewPar := TMethodParam.Create();
      NewPar.ParamName    := SrcPar.ParamName;
      NewPar.TypeName     := SrcPar.TypeName;
      NewPar.IsVarParam   := SrcPar.IsVarParam;
      NewPar.IsConstParam := SrcPar.IsConstParam;
      { IsOutParam and the default-value facts were dropped here as well.
        Losing IsOutParam turns an `out` param into a plain `var` for an
        imported generic, and losing HasDefault makes the consumer demand
        arguments the declaring unit treats as optional.  Same failure family
        as the const/out/default loss in the monomorphisation paths. }
      NewPar.IsOutParam   := SrcPar.IsOutParam;
      NewPar.IsOpenArray  := SrcPar.IsOpenArray;
      NewPar.HasDefault   := SrcPar.HasDefault;
      NewPar.DefaultValue := CloneExpr(SrcPar.DefaultValue);
      MD.Params.Add(NewPar);
    end;
    MD.Body := ReadBlock(AText, APos);
    MD.OwnBody := MD.Body <> nil;
    ClassDef.Methods.Add(MD);
  end;

  { Property declarations (parallel to WriteGenericClassPayload). }
  ReadPropertyList(AText, APos, ClassDef.Properties);

  AEntry.IsGeneric := True;
  AEntry.Def       := Def;
end;

procedure ReadGenericInterfacePayload(const AText: string; var APos: Integer;
                                      AEntry: TTypeEntry);
var
  Def:     TGenericInterfaceDef;
  IntfDef: TInterfaceTypeDef;
begin
  Def := TGenericInterfaceDef.Create();
  ReadTypeParamList(AText, APos, Def.ParamNames, Def.ParamConstraints);
  Def.IntfDef.Free();
  IntfDef := TInterfaceTypeDef.Create();
  Def.IntfDef := IntfDef;
  IntfDef.ParentName := ReadLpstrAt(AText, APos);
  ReadMethodDeclList(AText, APos, IntfDef.Methods);
  ReadPropertyList(AText, APos, IntfDef.Properties);
  AEntry.IsGeneric := True;
  AEntry.Def       := Def;
end;

procedure ReadGenericProcPayload(const AText: string; var APos: Integer;
                                 AEntry: TTypeEntry);
var
  Def:      TGenericProcDef;
  Pc, J:    Integer;
  Param:    TMethodParam;
  FlagsStr: string;
begin
  Def := TGenericProcDef.Create();
  ReadTypeParamList(AText, APos, Def.ParamNames, Def.ParamConstraints);
  Def.ProcDef := TProceduralTypeDef.Create();
  Def.ProcDef.IsFunction     := DecodeBool(AText, APos);
  Def.ProcDef.IsMethodPtr    := DecodeBool(AText, APos);
  Def.ProcDef.IsReference    := DecodeBool(AText, APos);
  Def.ProcDef.ReturnTypeName := ReadLpstrAt(AText, APos);
  Pc := DecodeCount(AText, APos);
  for J := 1 to Pc do
  begin
    Param := TMethodParam.Create();
    Param.ParamName := ReadLpstrAt(AText, APos);
    Param.TypeName  := ReadLpstrAt(AText, APos);
    FlagsStr := ReadLpstrAt(AText, APos);
    DecodeParamFlags(StrToInt(FlagsStr), Param);
    Def.ProcDef.Params.Add(Param);
  end;
  AEntry.Def := Def;
end;

procedure ReadProcPayload(const AText: string; var APos: Integer;
                          AEntry: TTypeEntry);
var
  Def:      TProceduralTypeDef;
  Pc, J:    Integer;
  Param:    TMethodParam;
  FlagsStr: string;
begin
  Def := TProceduralTypeDef.Create();
  Def.IsFunction     := DecodeBool(AText, APos);
  Def.IsMethodPtr    := DecodeBool(AText, APos);
  Def.IsReference    := DecodeBool(AText, APos);
  Def.ReturnTypeName := ReadLpstrAt(AText, APos);
  Pc := DecodeCount(AText, APos);
  for J := 1 to Pc do
  begin
    Param := TMethodParam.Create();
    Param.ParamName := ReadLpstrAt(AText, APos);
    Param.TypeName  := ReadLpstrAt(AText, APos);
    FlagsStr := ReadLpstrAt(AText, APos);
    DecodeParamFlags(StrToInt(FlagsStr), Param);
    Def.Params.Add(Param);
  end;
  AEntry.Def := Def;
end;

procedure ReadInterfacePayload(const AText: string; var APos: Integer;
                               AEntry: TTypeEntry);
var
  Def: TInterfaceTypeDef;
begin
  Def := TInterfaceTypeDef.Create();
  Def.ParentName := ReadLpstrAt(AText, APos);
  ReadMethodDeclList(AText, APos, Def.Methods);
  ReadPropertyList(AText, APos, Def.Properties);
  AEntry.Def := Def;
end;

procedure ReadTypes(const AText: string; var APos: Integer;
                    AIface: TUnitInterface);
var
  Count:    Integer;
  I:        Integer;
  Kind:     string;
  Name:     string;
  Payload:  string;
  Entry:    TTypeEntry;
  EnumDef:  TEnumTypeDef;
  SetDef:   TSetTypeDef;
  AliasDef: TTypeAliasDef;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Kind  := ReadLpstrAt(AText, APos);
    Name  := ReadLpstrAt(AText, APos);
    Entry := TTypeEntry.Create();
    Entry.Name := Name;

    if Kind = 'enum' then
    begin
      Payload := ReadLpstrAt(AText, APos);
      EnumDef := TEnumTypeDef.Create();
      LoadEnumMembers(Payload, EnumDef);
      Entry.Def := EnumDef;
    end
    else if Kind = 'set' then
    begin
      Payload := ReadLpstrAt(AText, APos);
      SetDef := TSetTypeDef.Create();
      SetDef.BaseTypeName := Payload;
      Entry.Def := SetDef;
    end
    else if Kind = 'alias' then
    begin
      Payload := ReadLpstrAt(AText, APos);
      AliasDef := TTypeAliasDef.Create();
      AliasDef.TypeName := Payload;
      AliasDef.IsSubrange := ReadLpstrAt(AText, APos) = '1';
      AliasDef.SubrangeLow := ReadInt64At(AText, APos);
      AliasDef.SubrangeHigh := ReadInt64At(AText, APos);
      Entry.Def := AliasDef;
    end
    else if Kind = 'record' then
      ReadRecordPayload(AText, APos, Entry)
    else if Kind = 'class' then
      ReadClassPayload(AText, APos, Entry)
    else if Kind = 'interface' then
      ReadInterfacePayload(AText, APos, Entry)
    else if Kind = 'proc' then
      ReadProcPayload(AText, APos, Entry)
    else if Kind = 'generic-class' then
      ReadGenericClassPayload(AText, APos, Entry, AIface.Name)
    else if Kind = 'generic-interface' then
      ReadGenericInterfacePayload(AText, APos, Entry)
    else if Kind = 'generic-proc' then
      ReadGenericProcPayload(AText, APos, Entry)
    else
    begin
      Entry.Free();
      raise EIfaceFormatError.Create('TYPE block: unknown kind ''' + Kind + '''');
    end;
    AIface.AddType(Entry);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('TYPE block: missing END marker');
end;

{ Inverse of EncodeParamFlags. }
procedure DecodeParamFlags(AFlags: Integer; AParam: TMethodParam);
begin
  AParam.IsVarParam   := (AFlags and 1) <> 0;
  AParam.IsConstParam := (AFlags and 2) <> 0;
  AParam.IsOpenArray  := (AFlags and 4) <> 0;
  AParam.IsOutParam   := (AFlags and 8) <> 0;
  AParam.HasDefault   := (AFlags and 16) <> 0;
end;

procedure ReadRoutines(const AText: string; var APos: Integer;
                       AIface: TUnitInterface);
var
  Count:    Integer;
  I, J:     Integer;
  PCount:   Integer;
  R:        TRoutineSig;
  RefStr:   string;
  RefUnit:  string;
  RefType:  string;
  IsFnStr:  string;
  Param:    TMethodParam;
  FlagsStr: string;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    R := TRoutineSig.Create();
    R.Name        := ReadLpstrAt(AText, APos);
    IsFnStr       := ReadLpstrAt(AText, APos);
    R.IsFunction  := IsFnStr <> '0';
    RefStr        := ReadLpstrAt(AText, APos);
    DecodeQualRef(RefStr, RefUnit, RefType);
    R.ReturnType  := MakeQualRef(RefUnit, RefType);
    PCount := StrToInt(ReadLpstrAt(AText, APos));
    for J := 1 to PCount do
    begin
      Param := TMethodParam.Create();
      Param.ParamName := ReadLpstrAt(AText, APos);
      Param.TypeName  := ReadLpstrAt(AText, APos);
      FlagsStr := ReadLpstrAt(AText, APos);
      DecodeParamFlags(StrToInt(FlagsStr), Param);
      Param.DefaultValue := ReadExpr(AText, APos);
      R.Params.Add(Param);
    end;
    R.CallingConv := ReadLpstrAt(AText, APos);
    R.ResolvedQbeName := ReadLpstrAt(AText, APos);
    R.IsExternal := DecodeBool(AText, APos);
    R.ExternalName := ReadLpstrAt(AText, APos);
    R.IsVarArgs := DecodeBool(AText, APos);
    AIface.AddRoutine(R);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('ROUT block: missing END marker');
end;

function ReadUnitInterface(const AText: string): TUnitInterface;
var
  Cur:    Integer;
  UName:  string;
  Tag:    string;
begin
  Cur := 0;  { 0-based cursor }
  ReadHeader(AText, Cur);
  UName := ReadLpstrAt(AText, Cur);
  Result := TUnitInterface.Create(UName);
  try
    while Cur < Length(AText) do
    begin
      SkipWhitespace(AText, Cur);
      if Cur >= Length(AText) then Break;
      Tag := ReadTag(AText, Cur);
      if      Tag = 'CONST'   then ReadConsts         (AText, Cur, Result)
      else if Tag = 'VAR'     then ReadVars           (AText, Cur, Result)
      else if Tag = 'TYPE'    then ReadTypes          (AText, Cur, Result)
      else if Tag = 'ROUT'    then ReadRoutines       (AText, Cur, Result)
      else if Tag = 'META'    then ReadMeta           (AText, Cur, Result)
      else if Tag = 'GENROUT' then ReadGenericRoutines(AText, Cur, Result)
      else if Tag = 'INLINE'  then ReadInlineBodies   (AText, Cur, Result)
      else if Tag = ''        then Break
      else
        raise EIfaceFormatError.Create(Format(
          'unknown record tag ''%s'' at position %d', [Tag, Cur]));
    end;
  except
    Result.Free();
    raise;
  end;
end;

{ FNV-1a 64-bit content hash.  Cheap, no crypto deps, change-
  detection grade.  Returned as a lowercase hex string for stable
  text-format encoding.

  Constants assembled from 32-bit halves because Blaise's literal
  parser caps numeric literals at Int64 range; FNV_OFFSET is
  >9.2e18 and doesn't fit. }
function ContentHashFnv1a64(const AContent: string): string;
var
  I:    Integer;
  B:    Byte;
  H:    UInt64;
  Lo:   Integer;
  FnvOffset: UInt64;
  FnvPrime:  UInt64;
begin
  FnvOffset := (UInt64($cbf29ce4) shl 32) or UInt64($84222325);
  FnvPrime  := (UInt64($00000100) shl 32) or UInt64($000001b3);
  H := FnvOffset;
  for B in AContent do
  begin
    H := H xor UInt64(B);
    H := H * FnvPrime;
  end;
  Result := '';
  for I := 15 downto 0 do
  begin
    Lo := Integer((H shr (I * 4)) and $f);
    if Lo < 10 then Result := Result + Chr(Ord('0') + Lo)
              else Result := Result + Chr(Ord('a') + Lo - 10);
  end;
end;

function SourceHashWithEmbeds(const ASourceText, ASourcePath: string;
                              ADefines: TStringList): string;
var
  Lx:      TLexer;
  Tok:     TToken;
  Acc:     string;
  I:       Integer;
  Path:    string;
  FIn:     TFileInputStream;
  Blob:    string;
  N:       Integer;
  Got:     Integer;
  I2:      Integer;
begin
  Acc := ASourceText;
  { Discover the embedded files by lexing.  The lexer records each file it
    reads, and resolves relative paths against ASourcePath exactly as the
    real compile will, so the set found here matches the set compiled in.
    A lex failure (bad syntax, missing embed target) leaves the source hash
    alone — the subsequent real compile reports the error with diagnostics. }
  Lx := TLexer.Create(ASourceText, ASourcePath);
  Lx.ApplyDefines(ADefines);   { same branches the real compile takes }
  try
    { blaise-guard: ignore BL-2005 - deliberate; see the except note below }
    try
      repeat
        Tok := Lx.Next();
      until Tok.Kind = tkEOF;
    except
      { Ignore — a lex failure must NOT abort hash discovery; the subsequent
        real compile reports it with proper diagnostics (note above). }
    end;
    for I := 0 to Lx.EmbeddedFiles.Count - 1 do
    begin
      Path := Lx.EmbeddedFiles.Strings[I];
      { Include the path itself, so swapping which file is embedded changes
        the hash even when two assets happen to have identical content. }
      Acc := Acc + Chr(0) + Path + Chr(0);
      Blob := '';
      try
        FIn := TFileInputStream.Create(Path);
        try
          N := Integer(FIn.Size());
          SetLength(Blob, N);
          { Read until N: a single read(2) may legally return fewer bytes,
            which would leave the tail as zeros and hash a file that never
            existed on disk. }
          Got := 0;
          while Got < N do
          begin
            I2 := FIn.Read(PChar(Blob) + Got, N - Got);
            if I2 <= 0 then Break;
            Got := Got + I2;
          end;
          if Got < N then
            SetLength(Blob, Got);
        finally
          FIn.Free();
        end;
      except
        { Unreadable now (deleted since the cached build): fold in a marker
          so the entry invalidates rather than silently matching. }
        Blob := '<unreadable>';
      end;
      Acc := Acc + Blob;
    end;
  finally
    Lx.Free();
  end;
  Result := ContentHashFnv1a64(Acc);
end;

var
  GEffectiveCompilerId: string = '';   { memoised — see EffectiveCompilerId }
  GActiveDefines: TStringList;         { not owned — see SetActiveDefines }

procedure SetActiveDefines(ADefines: TStringList);
begin
  GActiveDefines := ADefines;
end;

function EffectiveCompilerId: string;
var
  FIn:  TFileInputStream;
  Bytes: string;
  Hash: string;
begin
  if GEffectiveCompilerId <> '' then
    Exit(GEffectiveCompilerId);
  { Content-hash the running compiler binary.  Read RAW BYTES via
    TFileInputStream — TStringList.LoadFromFile drops content at the first
    NUL byte of an ELF binary, so two DIFFERENT compiler builds hashed equal
    (only the identical ELF-header prefix survived) and the BUG-007
    invalidation silently never fired.  A read failure (unknown path,
    permissions) degrades to the bare COMPILER_ID — no worse than the old
    behaviour, never a hard error. }
  Hash := '';
  try
    FIn := TFileInputStream.Create(ParamStr(0));
    try
      SetLength(Bytes, Integer(FIn.Size()));
      if Length(Bytes) > 0 then
        FIn.Read(PChar(Bytes), Length(Bytes));
      Hash := ContentHashFnv1a64(Bytes);
    finally
      FIn.Free();
    end;
  except
    Hash := '';
  end;
  if Hash <> '' then
    GEffectiveCompilerId := COMPILER_ID + '+bin' + Hash
  else
    GEffectiveCompilerId := COMPILER_ID;
  Result := GEffectiveCompilerId;
end;

procedure WriteUnitInterfaceToFile(AIface: TUnitInterface; const APath: string);
var
  Bytes: string;
  Src:   string;
  FIn:   TFileInputStream;
  FOut:  TFileOutputStream;
begin
  { Populate source-content hash from disk if SourceFile is set and
    readable.  Empty hash on absent/unreadable source — at load time
    that disables the source-match path and forces compiler-id-match
    fallback. }
  if (AIface.SourceFile <> '') and FileExists(AIface.SourceFile) then
  begin
    try
      FIn := TFileInputStream.Create(AIface.SourceFile);
      try
        SetLength(Src, Integer(FIn.Size()));
        if Length(Src) > 0 then
          FIn.Read(PChar(Src), Length(Src));
      finally
        FIn.Free();
      end;
      { Hash covers the source AND anything it embeds, so an asset edit
        invalidates the cached .o just as a source edit does.  The active
        defines must match the validator's, or the two disagree on which
        IFDEF branches (and so which embeds) are live. }
      AIface.SourceHash := SourceHashWithEmbeds(Src, AIface.SourceFile,
                                                GActiveDefines);
    except
      { Swallow IO failure — best-effort population. }
      AIface.SourceHash := '';
    end;
  end;

  Bytes := WriteUnitInterface(AIface);
  FOut := TFileOutputStream.Create(APath);
  try
    if Length(Bytes) > 0 then
      FOut.Write(PChar(Bytes), Length(Bytes));
  finally
    FOut.Close();
    FOut.Free();
  end;
end;

function ReadUnitInterfaceFromFile(const APath: string): TUnitInterface;
var
  Bytes: string;
  FIn:   TFileInputStream;
begin
  FIn := TFileInputStream.Create(APath);
  try
    SetLength(Bytes, Integer(FIn.Size()));
    if Length(Bytes) > 0 then
      FIn.Read(PChar(Bytes), Length(Bytes));
  finally
    FIn.Free();
  end;
  Result := ReadUnitInterface(Bytes);
end;

end.
