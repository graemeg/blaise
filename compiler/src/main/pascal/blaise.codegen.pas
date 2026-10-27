{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen;

{ Backend-neutral code-generator contract.

  The native backend (blaise.codegen.native.TCodeGenNative) implements
  ICodeGen, so the driver in Blaise.pas runs one codegen sequence against the
  interface rather than branching per backend.

  ICodeGen covers only what the driver invokes polymorphically.  Backend-
  specific configuration (e.g. the native backend's SetTarget) stays on the
  concrete class and is applied before the object is assigned to an ICodeGen
  variable.

  Lifetime: ICodeGen is ARC-managed.  Assign a freshly-created concrete
  codegen to an ICodeGen variable and let it go out of scope — no manual
  Free.  (Mixing an explicit Free with ARC would double-free.) }

interface

uses
  SysUtils, Classes, uAST, uSymbolTable, uDebugFacts, blaise.codegen.target,
  uStrCompat;

type
  TRecReturnClass = (
    rcSret,
    rcInt1,
    rcInt2,
    rcSSE1,
    rcSSE2,
    rcIntSSE,
    rcSSEInt,
    rcWin64Agg
  );

  { How a scope-exit ARC teardown walk must dispose of one variable, keyed on
    its type alone.  See ArcScopeExitReleaseKind. }
  TArcReleaseKind = (
    arkNone,        { no ARC content — emit nothing }
    arkString,      { _StringRelease on the slot value }
    arkClass,       { _ClassRelease on the slot value (or _WeakClear on the
                      slot ADDRESS when the decl is [Weak]) }
    arkIntf,        { _ClassRelease on the _obj half (or _WeakClear on its
                      address when [Weak]); the itab half is static rodata }
    arkDynArray,    { _DynArrayRelease on the slot value }
    arkRefEnv,      { 'reference to' fat value: _ClassRelease the env pointer
                      in the Data half at offset +8 }
    arkAggregate    { record or static array with managed content — walk it
                      via the shared EmitManagedReleaseAt/EmitRecordFieldReleases
                      helpers rather than a direct release call }
  );

  ICodeGen = interface
    { Single-file program compilation: reset output and emit all IR. }
    procedure Generate(AProg: TProgram);

    { Single-unit compilation in isolation. }
    procedure GenerateUnit(AUnit: TUnit);

    { Provide the global symbol table before AppendUnit/AppendProgram so
      class typeinfo, vtable, and field-cleanup data can be emitted. }
    procedure SetSymbolTable(ASymTable: TSymbolTable);

    { Enable backend debug/leak-tracking behaviour. }
    procedure SetDebugMode(AEnabled: Boolean);

    { Enable OPDF-debug code shaping.  When on, the backend emits class vtables
      as exported (global) symbols so the separately-assembled .opdf section can
      reference them across object files (the OPDF class record stores each
      class's VMTAddress for runtime dynamic-type resolution).  Off by default,
      so normal builds are byte-for-byte unchanged. }
    procedure SetOpdfMode(AEnabled: Boolean);

    { Codegen-collected debug facts for the OPDF emitter (exact frame
      offsets, per-statement line labels, function extents).  Only the
      native backend produces them; a codegen that returns nil leaves the
      OPDF emitter to its approximate AST walk. }
    function  GetDebugFacts: TDbgFacts;

    { Multi-unit compilation: append unit IR to existing output without
      resetting the output buffer or string-literal table. }
    procedure AppendUnit(AUnit: TUnit);

    { Append program IR after one or more AppendUnit calls. }
    procedure AppendProgram(AProg: TProgram);

    { Incremental / separate-compilation: when a dependency unit's BODY is
      compiled elsewhere (its own .o) and therefore NOT emitted here via
      AppendUnit, the program startup must still call that unit's
      <Unit>_init() if it has an initialization section.  This registers the
      unit name into the init-call list (in dependency order) WITHOUT emitting
      any body, so AppendProgram's $main emits `call $<Unit>_init()` and the
      call resolves against the symbol exported by the per-unit object.
      AHasInit selects whether the unit actually has an init section; units
      without one are skipped (no spurious call). }
    procedure NoteDepInitUnit(const AUnitName: string; AHasInit: Boolean);

    { The teardown twin of NoteDepInitUnit: when a dependency unit's body is
      compiled elsewhere, the program epilogue must still call that unit's
      <Unit>_fini() (user finalization section + ARC release of the unit's
      managed globals) at main_exit.  Registration order matches the init
      list; the emitter calls the fini list in REVERSE (last initialised,
      first finalised).  AHasFini mirrors the shared UnitNeedsFini predicate
      (TUnitInterface.HasFinalization for cached deps); units without a fini
      are skipped so no dangling call is emitted. }
    procedure NoteDepFiniUnit(const AUnitName: string; AHasFini: Boolean);

    { Retrieve the complete generated output (target assembly text). }
    function GetOutput: string;

    { Link libraries the emitted code depends on.  The driver unions these
      into its -l<name> list so a lib is linked only when actually used.  The
      native backend emits float math inline and returns an empty list. }
    function GetRequiredLibs: TStringList;
  end;

{ ----------------------------------------------------------------------
  Shared System V / Win64 record-return ABI classifier.

  Every x86-64 lowering site must agree, byte for byte, on how a record-typed
  return value is passed (sret vs register, and which register class).  The
  decision is a pure walk over the record's field layout plus the target OS —
  no backend state — so it lives here as free functions rather than as
  drift-prone per-site copies.  Only RecretClassify consults the target (the Win64
  aggregate rule); the leaf predicates are target-independent type walks. }

{ True when ARec (and every nested record) contains no managed content
  (string / class / interface / dynamic array, or a static array of such
  elements) — a precondition for any register return. }
function RecretManagedClean(ARec: TRecordTypeDesc): Boolean;
{ True when every leaf field is an integer-class scalar (or a nested record
  thereof). }
function RecretAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
{ True when every leaf field is a float (Double/Single) or a nested record
  thereof. }
function RecretAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
{ True when every leaf field is an integer- or float-class scalar. }
function RecretAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
{ True when the eightbyte starting at AStartByte holds any float leaf — i.e.
  the eightbyte is SSE-classified under the SysV mixed-class rules. }
function RecretEightbyteIsSSE(ARec: TRecordTypeDesc; AStartByte: Integer): Boolean;
{ Classify ARec's return-passing for ATarget's OS. }
{ Type of the outer variable AName captured by nested routine ADecl: walks
  the EnclosingDecl chain's local var decls and parameters.  nil when the
  name is not found (e.g. a method's captured 'Self').  Both backends use
  this to give interface-typed captures (16-byte fat pointers) their own
  hidden-capture ABI (BUG-038). }
function NestedCapturedVarType(ADecl: TMethodDecl;
  const AName: string): TTypeDesc;

{ True when AType is an interface (nil-safe) — the fat-pointer capture ABI
  test both backends share. }
function IsIntfType(AType: TTypeDesc): Boolean;

function RecretClassify(ARec: TRecordTypeDesc;
  const ATarget: TTargetDesc): TRecReturnClass;

{ ----------------------------------------------------------------------
  Shared ARC ownership-transfer predicate.

  True when AExpr, used as an r-value, leaves an ARC-managed value at
  refcount +1 that the consuming site must NOT AddRef again (it consumes the
  transferred reference).  Covers function/method calls and method-backed
  property reads returning a class, string, or dynamic array.  The decision is
  a pure walk over the AST node + its resolved type — no backend state — so it
  is single-sourced here and both backends call it (formerly the byte-identical
  twins ExprOwnsRef / NativeExprOwnsRef). }
function ArcExprOwnsRef(AExpr: TASTExpr): Boolean;

{ True when AExpr is an INDEXED-property read L[I] / Obj.Items[I] that the
  semantic pass folded into its StrExpr: a TStringSubscriptExpr whose StrExpr
  is a property-read TFieldAccessExpr carrying the index in PropIndexExpr, and
  whose own IndexExpr is nil.  Every backend arm that delegates such a
  subscript to its StrExpr must test this, not just PropRead <> nil: a
  subscript OF a non-indexed property's value, (Obj.Prop)[I], also has a
  property-read StrExpr but keeps its index, and delegating it dropped the
  index (the whole string / array pointer came back as the element). }
function IsFoldedPropSubscript(AExpr: TASTExpr): Boolean;

{ True for a constructor call's result, TFoo.Create(..): a fresh instance at
  refcount 0 that nothing owns (ArcExprOwnsRef is False for it -- a store
  takes the first reference).  Used directly as a method RECEIVER,
  TFoo.Create().Run(), nothing ever took that reference, so the instance
  leaked; a receiver site pins it (0 -> 1) and releases it after the call. }

{ True when AExpr's value is produced by a CALL -- a function or method call,
  a method-backed property read (Obj.Prop, or a bare Prop inside a method),
  or an indexed-property read -- rather than read from storage.  An aggregate
  (static array / record) value of that shape lives in a per-site result
  buffer: a consumer that needs its address (a subscript base) takes the
  buffer's, since the expression has no storage of its own. }
{ Obj.Handler(..) or, inside a method, Handler(..): a call through a
  procedural-typed field, as a value }
function IsProcFieldCallExpr(AExpr: TASTExpr): Boolean;
function IsAggCallValue(AExpr: TASTExpr): Boolean;

{ True when evaluating AExpr may run a CALL anywhere along its access path --
  the expression itself, a base it is read through (F(3).A, O.R.A where R has
  a getter, MkObj().Arr), or an index (Arr[G()]).  False only for a pure
  storage path: identifiers, fields, subscripts with call-free indexes, P^,
  and literals.  A consumer that re-derives an address on every use (a for-in
  over an l-value) must evaluate such an expression ONCE instead, or it runs
  the call again each time.  An unfamiliar node kind counts as a call:
  evaluating once is always correct. }
{ True for an open-array literal argument the backends build as an element
  block in the caller's frame.  A literal whose elements need a managed or
  wide copy (records, interfaces, closures) is typed by the semantic pass as
  a dynamic array instead, and passes as any dynamic array does. }
function IsOALitBlock(AExpr: TASTExpr): Boolean;
function AccessPathHasCall(AExpr: TASTExpr): Boolean;

{ The setter call a property-write statement was lowered to by the semantic
  pass (TAssignment / TFieldAssignment / TStaticSubscriptAssign.SetterCall),
  or nil.  Every backend emits that call in place of the statement. }
{ The statement the semantic pass lowered a call statement to -- a call
  through a getter-backed procedural property (TMethodCallStmt /
  TProcCall.LoweredCall) -- or nil.  Codegen emits it in place of the
  original node. }
function LoweredCallStmt(AStmt: TASTStmt): TASTStmt;
function LoweredSetterCall(AStmt: TASTStmt): TMethodCallStmt;

{ True when AExpr is an ARRAY-ELEMENT l-value — a subscript whose base is a
  static, dynamic, or open array — i.e. a slot with a stable address that a
  consuming site (notably the Free lowering) can write through.  All three
  backends use this so `A[I].Free()` releases AND nils the element slot,
  exactly like the identifier/field receiver forms: a stale pointer left in
  the slot double-frees when the scope-exit ARC walk (or a later element
  store) releases it again (BUG-016). }
function ArcIsArrayElemSlot(AExpr: TASTExpr): Boolean;

{ True for a 'reference to' closure type — a 16-byte [Code; Env] fat value
  whose Env half at +8 strongly references an ARC environment record.  A
  plain procedural type is a bare code pointer, and an 'of object' method
  pointer's Data half is a BORROWED receiver; neither is managed content, so
  only IsReference answers True here.  This is the single discriminator every
  ARC walk must use — IsMethodPtrType (the 16-byte-ABI predicate) covers both
  shapes and is NOT a substitute
  (BUG-20260922-record-closure-field-not-managed). }
function ArcTypeIsRefClosure(AType: TTypeDesc): Boolean;

{ True when AType transitively contains any ARC-managed leaf: a managed
  scalar (string / class / interface / dynamic array), a static array of
  managed elements (at any nesting depth), or a record with such content.
  The native backends gate the scope-exit release of
  static-array LOCALS on this (BUG-016 stage 2) so unmanaged arrays emit no
  dead walk code.  RecretManagedClean (the register-return ABI predicate)
  delegates its static-array-field arm to this walk, so the two agree that
  a static array of managed elements is managed content. }
function ArcTypeHasManagedContent(AType: TTypeDesc): Boolean;

{ Classify how a scope-exit ARC teardown walk must dispose of a variable of
  AType.  This is the SHARED dispatch key for every such walk in the compiler:
  on x86-64 both the procedure-epilogue decl walk and EmitGlobalReleases (the
  program-exit global walk), and the per-unit teardown walks of both ISAs.

  Those walks were three independently hand-maintained if/else-if chains over
  the same TTypeKind values, and they drifted: the x86-64 global walk lacked
  the tyStaticArray arm the procedure walk had, so a program-level
  `array[0..N] of TFoo` leaked every element while the identical array inside
  a procedure was released correctly.  Routing all three through one
  classifier makes such a gap a MISSING CASE ARM in every driver at once
  rather than a silent omission in one.

  The result depends on the TYPE only.  Two orthogonal facts stay with the
  caller because they are properties of the DECLARATION, not the type:

    * [Weak] — modifies how arkClass/arkIntf are emitted (_WeakClear against
      the slot address instead of a strong release of the slot value).
    * storage/addressing — frame offset vs <name>(%rip) vs a GOT load, and
      whether the slot is skipped entirely (env fields, thread-vars).

  arkAggregate deliberately merges tyRecord and tyStaticArray: both are walked
  through the shared EmitManagedReleaseAt family, which already dispatches
  record fields and array elements and recurses between them.  Adding a new
  managed AGGREGATE shape is therefore a change inside that helper which every
  driver inherits; only a new managed SCALAR needs a new TArcReleaseKind and,
  with it, a compiler-visible gap in each driver's case statement. }
function ArcScopeExitReleaseKind(AType: TTypeDesc): TArcReleaseKind;

{ True when ABlock (a unit's interface or implementation block) declares at
  least one module-level variable that needs an ARC release at program exit:
  not a thread-var (per-thread lifetime, matching the data-section split),
  not [Unretained] (non-owning), and of a kind the scope-exit classifier
  covers.  [Weak] declarations count — the weak slot must be _WeakClear'd. }
function UnitBlockHasManagedGlobals(ABlock: TBlock): Boolean;

{ True when AUnit must export a <Unit>_fini procedure: it has a user
  `finalization` section and/or managed module-level globals to release.
  This is THE shared predicate for per-unit ARC teardown — the unit's own
  translation unit emits the fini exactly when it is True, and the driver
  registers a fini CALL for a dependency unit under the same predicate
  (NoteDepFiniUnit / TUnitInterface.HasFinalization), so the call list and
  the emitted symbols can never drift apart.  Units with nothing to do get
  NO fini and no call — binaries do not grow. }
function UnitNeedsFini(AUnit: TUnit): Boolean;

{ True if evaluating AExpr MIGHT defer a class-field-on-owned-transient base
  release (a retained class/interface field read whose base is an owned
  transient — MakeObj().ClassField).  The three backends use this to decide
  whether a condition/branch site needs the flush-and-materialise path
  (BUG-049): when it returns False the fast fused compare-branch is safe (no
  deferred base to leak).  Conservative — a false positive only costs the
  fused-branch optimisation; a false negative would leak, so the walk covers
  every subexpression that EmitExpr descends into. }
function ExprMayDeferTransientBase(AExpr: TASTExpr): Boolean;

{ String transients come in TWO refcount shapes, and disposing them
  differs:

    rc = 1 (owned)    — user function/method/getter results: the callee's
                        `Result := x` AddRef'd.  ArcExprOwnsRef is True.
                        Dispose with ONE _StringRelease (1 -> 0 frees).
    rc = 0 (unowned)  — RTL-built strings: built-in call results (IntToStr,
                        Trim, Copy, ...) and _StringConcat results all come
                        from StrAlloc with RefCount = 0 ("caller must
                        AddRef").  A bare _StringRelease drives the count to
                        -1 = IMMORTAL and the block leaks silently (the leak
                        tracker never saw it either — it registers on the
                        0 -> 1 AddRef).  Dispose with _StringAddRef THEN
                        _StringRelease (0 -> 1 -> 0 frees).

  ArcExprIsUnownedStrTransient identifies the rc = 0 shapes. }
function ArcExprIsUnownedStrTransient(AExpr: TASTExpr): Boolean;
{ True for an = / <> comparison with an OWNED class operand (MakeObj() <> nil):
  the backends park the operands, compare, then release the owned one --
  comparing in place leaked the +1 the call returned. }
function ArcIsOwnedClassCompare(AExpr: TASTExpr): Boolean;

{ Ownership predicate for a STRING argument to a BUILT-IN (FileAge, Trim,
  Length, StrToInt, ...) or a string-operator operand: True when the
  argument is a transient of either refcount shape that the emitting site
  must dispose after the call.  Consult ArcExprIsUnownedStrTransient to
  pick the disposal sequence (release vs addref+release).  Without the
  disposal the temp leaks (e.g. the luhmann directory watcher leaked one
  string per note per poll via FileAge(AbsPathOf(Id))). }
function ArcBuiltinStrArgOwnsRef(AExpr: TASTExpr): Boolean;

{ Mangle a Blaise symbol name into an assembler-legal identifier, shared by
  both ISA backends (formerly QBEMangle / NativeMangle).  Replaces the generic/
  overload metacharacters '<' ',' ' ' -> '_', drops '>', and maps the type-code
  sigils '$' '@' '^' to '_D_' '_V_' '_P_'.  A clean name (no metacharacter) is
  returned unchanged via a fast pre-scan that avoids per-character concat. }
function CodegenMangle(const AName: string): string;

{ The interface name a typeinfo REFERENCE must be emitted under: the resolved
  descriptor's own name when the semantic pass supplied one, else the source
  spelling.

  These differ exactly when the source names the interface through a type
  ALIAS (`IIntBox = IBox<Integer>`).  An alias IS the aliased type, so it has
  no typeinfo of its own — only the instance's token is defined, and only that
  token appears in the implementing class's impllist.  Emitting a reference
  under the alias spelling left typeinfo_IIntBox undefined, which before the
  link guard bound it to a garbage address and made Supports() answer False
  for an interface the class genuinely implements
  (BUG-20260919-intf-alias-typeinfo).

  Nil-safe on purpose: ResolvedIntfType is filled in by uSemantic, and a
  codegen-only or partially-analysed path may not have it. }
function IntfRefName(AResolved: TTypeDesc; const ASourceName: string): string;

implementation

function ArcTypeIsRefClosure(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind = tyProcedural)
            and TProceduralTypeDesc(AType).IsReference;
end;

function RecretManagedClean(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    { A 'reference to' closure field co-owns its Env: register-returning or
      memcpy-copying the record would share the env with no retain
      (BUG-20260922-record-closure-field-not-managed). }
    if ArcTypeIsRefClosure(F.TypeDesc) then Exit;
    case F.TypeDesc.Kind of
      tyString, tyClass, tyInterface, tyDynArray:
        Exit;
      tyRecord:
        if not RecretManagedClean(TRecordTypeDesc(F.TypeDesc)) then Exit;
      tyStaticArray:
        { A static array of managed elements (at any nesting depth) is
          managed content: register-returning or memcpy-copying it would
          share the element refs without retain/release
          (BUG-20260721-recretclean-static-array-of-managed). }
        if ArcTypeHasManagedContent(F.TypeDesc) then Exit;
    else
      { every other kind is unmanaged: it does not block a register return }
    end;
  end;
  Result := True;
end;

function RecretAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    case F.TypeDesc.Kind of
      tyInteger, tyInt64, tyUInt32, tyUInt64,
      tySmallInt, tyInt8, tyWord, tyByte, tyBoolean,
      tyEnum, tyPointer, tyProcedural, tyMetaClass:
        ;
      tyRecord:
        if not RecretAllIntegerLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function RecretAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    case F.TypeDesc.Kind of
      tyDouble, tySingle: ;
      tyRecord:
        if not RecretAllFloatLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function RecretAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    case F.TypeDesc.Kind of
      tyInteger, tyInt64, tyUInt32, tyUInt64,
      tySmallInt, tyInt8, tyWord, tyByte, tyBoolean,
      tyEnum, tyPointer, tyProcedural, tyMetaClass,
      tyDouble, tySingle: ;
      tyRecord:
        if not RecretAllIntOrFloatLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

{ True when a scalar leaf of AType (laid out from byte ABase) overlaps the
  eightbyte at AStart and is a float (AFloat) or a non-float (not AFloat).
  Walks nested records and static arrays. }
function RecretEightbyteHasLeaf(AType: TTypeDesc; ABase, AStart: Integer;
  AFloat: Boolean): Boolean;
var
  I, ESz: Integer;
  F: TFieldInfo;
  AT: TStaticArrayTypeDesc;
begin
  Result := False;
  if AType = nil then Exit;
  if AType.Kind = tyRecord then
  begin
    for I := 0 to TRecordTypeDesc(AType).Fields.Count - 1 do
    begin
      F := TFieldInfo(TRecordTypeDesc(AType).Fields.Items[I]);
      if RecretEightbyteHasLeaf(F.TypeDesc, ABase + F.Offset, AStart, AFloat) then
        Exit(True);
    end;
    Exit;
  end;
  if AType.Kind = tyStaticArray then
  begin
    AT := TStaticArrayTypeDesc(AType);
    ESz := AT.ElementType.RawSize();
    for I := 0 to AT.HighBound - AT.LowBound do
      if RecretEightbyteHasLeaf(AT.ElementType, ABase + I * ESz, AStart, AFloat) then
        Exit(True);
    Exit;
  end;
  if (ABase + AType.RawSize() <= AStart) or (ABase >= AStart + 8) then
    Exit;
  Result := (AType.Kind in [tyDouble, tySingle]) = AFloat;
end;

{ System V eightbyte class: SSE when every scalar in the eightbyte at
  AStartByte is a float; one integer leaf makes it INTEGER. }
function RecretEightbyteIsSSE(ARec: TRecordTypeDesc; AStartByte: Integer): Boolean;
begin
  Result := (ARec <> nil) and
    RecretEightbyteHasLeaf(ARec, 0, AStartByte, True) and
    not RecretEightbyteHasLeaf(ARec, 0, AStartByte, False);
end;

function RecretClassify(ARec: TRecordTypeDesc;
  const ATarget: TTargetDesc): TRecReturnClass;
var
  Sz:               Integer;
  Eb0SSE, Eb1SSE:   Boolean;
begin
  Result := rcSret;
  if (ARec = nil) or (ARec.Kind <> tyRecord) then Exit;
  if ARec.Fields.Count = 0 then Exit;
  if not RecretManagedClean(ARec) then Exit;
  Sz := ARec.TotalSize();

  if ATarget.OS = osWindows then
  begin
    if RecretAllIntOrFloatLeaves(ARec) then
      Result := rcWin64Agg;
    Exit;
  end;

  if RecretAllIntegerLeaves(ARec) then
  begin
    case Sz of
      1, 2, 4, 8:                       Result := rcInt1;
      9, 10, 11, 12, 13, 14, 15, 16:    Result := rcInt2;
    end;
    Exit;
  end;

  if RecretAllFloatLeaves(ARec) then
  begin
    case Sz of
      4, 8:                            Result := rcSSE1;
      9, 10, 11, 12, 13, 14, 15, 16:   Result := rcSSE2;
    end;
    Exit;
  end;

  if not RecretAllIntOrFloatLeaves(ARec) then Exit;
  { a mixed int/float record: an eightbyte holding any integer is INTEGER
    class, one holding only floats SSE (System V) }
  case Sz of
    8:
      if RecretEightbyteIsSSE(ARec, 0) then Result := rcSSE1
      else Result := rcInt1;
    9, 10, 11, 12, 13, 14, 15, 16:
      begin
        Eb0SSE := RecretEightbyteIsSSE(ARec, 0);
        Eb1SSE := RecretEightbyteIsSSE(ARec, 8);
        if      (not Eb0SSE) and Eb1SSE then Result := rcIntSSE
        else if Eb0SSE and (not Eb1SSE) then Result := rcSSEInt
        else if Eb0SSE then Result := rcSSE2
        else Result := rcInt2;
      end;
  end;
end;

function ArcTypeHasManagedContent(AType: TTypeDesc): Boolean;
begin
  { The rule itself lives on TTypeDesc so the semantic pass shares it. }
  Result := (AType <> nil) and AType.HasManagedContent();
end;

function ArcScopeExitReleaseKind(AType: TTypeDesc): TArcReleaseKind;
begin
  Result := arkNone;
  if AType = nil then Exit;
  { Scalars first — each is a single direct release call in every driver.
    IsString() is Kind = tyString; both spellings appear in the drivers this
    replaces and they are equivalent. }
  if AType.IsString() then Exit(arkString);
  if AType.Kind = tyClass then Exit(arkClass);
  if AType.Kind = tyInterface then Exit(arkIntf);
  if AType.Kind = tyDynArray then Exit(arkDynArray);
  { 'reference to' procedurals carry a strong env reference in the Data half.
    A plain (non-reference) procedural type is a bare code pointer with no
    ARC content, so it stays arkNone. }
  if AType.Kind = tyProcedural then
  begin
    if TProceduralTypeDesc(AType).IsReference then Exit(arkRefEnv);
    Exit(arkNone);
  end;
  { Aggregates: only worth walking when something managed is actually in
    there.  This guard is what keeps an unmanaged record or an
    array[0..N] of Integer from emitting a dead walk. }
  if AType.Kind in [tyRecord, tyStaticArray] then
  begin
    if ArcTypeHasManagedContent(AType) then Exit(arkAggregate);
    Exit(arkNone);
  end;
end;

function UnitBlockHasManagedGlobals(ABlock: TBlock): Boolean;
var
  I:  Integer;
  VD: TVarDecl;
begin
  Result := False;
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    VD := TVarDecl(ABlock.Decls.Items[I]);
    if VD.IsThreadVar then Continue;
    if VD.IsUnretained then Continue;
    if ArcScopeExitReleaseKind(VD.ResolvedType) <> arkNone then
      Exit(True);
  end;
end;

function UnitNeedsFini(AUnit: TUnit): Boolean;
begin
  Result := ((AUnit.FinalStmts <> nil) and (AUnit.FinalStmts.Count > 0))
    or UnitBlockHasManagedGlobals(AUnit.IntfBlock)
    or UnitBlockHasManagedGlobals(AUnit.ImplBlock);
end;

function ArcIsArrayElemSlot(AExpr: TASTExpr): Boolean;
begin
  Result := (AExpr is TStringSubscriptExpr) and
    (TStringSubscriptExpr(AExpr).StrExpr <> nil) and
    (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
    (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind in
      [tyStaticArray, tyDynArray, tyOpenArray]);
end;

function ArcExprOwnsRef(AExpr: TASTExpr): Boolean;
var
  FA: TFieldAccessExpr;
  IE: TIdentExpr;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr.ResolvedType = nil then Exit;
  { Ownership transfer applies to every ARC-managed return value, not just
    classes: a function/method returning a String or dynamic array leaves
    its Result at refcount +1 (the callee AddRef'd on `Result := x` and did
    not release Result at scope exit).  The caller's assignment site must
    therefore NOT AddRef again — it consumes that transferred reference.
    Without covering tyString/tyDynArray here the assignment branches emit a
    spurious _StringAddRef/_DynArrayAddRef on the call result, which is never
    balanced and leaks one buffer per call. }
  if not (AExpr.ResolvedType.Kind in [tyClass, tyDynArray])
     and not AExpr.ResolvedType.IsString() then Exit;
  { a dynamic-array literal ([1, 2] given a dyn-array type) is a fresh array }
  if AExpr is TArrayLiteralExpr then
    Exit(True);
  if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr(AExpr);
    if IE.IsImplicitSelfMethod then
      Exit(True);
  end;
  { A constructor call (TFoo.Create) hands back an OWNED reference: the
    instance is retained right after allocation, so it is never at
    refcount 0 while its constructor runs (a retain/release pair inside the
    constructor -- a closure capturing Self, a worker thread started from
    it -- took it 0 -> 1 -> 0 and freed it under the constructor), and the
    consumer takes that reference over like a function result's. }
  if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    if FA.IsConstructorCall then begin Result := True; Exit end;
    if FA.IsMethodCall then begin Result := True; Exit end;
    { a STATIC property read through its getter (TFoo.SP, H.SP, SP) is the
      static getter call, which returns +1 like any function result: not
      counting it, a consumer retained it again (X := TFoo.SP) or never
      released it (TFoo.SP.N), leaking the object }
    if FA.IsStaticPropGet then begin Result := True; Exit end;
    { Method-backed property read (read GetX): the getter returns +1.
      Field-backed reads (read FX) emit a plain load and do NOT own. }
    if (FA.PropRead <> nil) and (FA.PropRead.ReadMethod <> '') then
      Exit(True);
  end;
  { TMethodCallExpr: every method call owns its class result, a constructor
    call included (allocated at +1, like _ClassCreate through a metaclass) }
  if AExpr is TMethodCallExpr then
    Exit(True);
  { A class CAST of an owned value -- MakeObj() as TFoo, TFoo(MakeObj()) --
    is the same pointer, so it carries the operand's +1: a consuming site
    that saw only the cast retained it again (a store) or never released it
    (a receiver, an argument), leaking the object on both backends. }
  if (AExpr is TAsExpr) and (AExpr.ResolvedType.Kind = tyClass) then
    Exit(ArcExprOwnsRef(TAsExpr(AExpr).Obj));
  if (AExpr is TFuncCallExpr) and (AExpr.ResolvedType.Kind = tyClass) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (not TFuncCallExpr(AExpr).IsProcFieldCall) and
     (TFuncCallExpr(AExpr).Args <> nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     SameText(TFuncCallExpr(AExpr).Name, AExpr.ResolvedType.Name) then
    Exit(ArcExprOwnsRef(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])));
  if AExpr is TFuncCallExpr then
  begin
    { ClassCreate(Cls, ...) is _ClassCreate (+1) whether or not a declared
      constructor runs afterwards -- ResolvedDecl is nil for the implicit one }
    { an implicit-Self procedural-FIELD call (C(2) inside a method, C a
      closure / function-pointer field) returns +1 exactly like the
      procedural-variable form -- not counting it leaked one string per
      call on both backends }
    if (TFuncCallExpr(AExpr).ResolvedDecl <> nil) or
       SameText(TFuncCallExpr(AExpr).Name, 'ClassCreate') or
       TFuncCallExpr(AExpr).IsIndirectCall or
       TFuncCallExpr(AExpr).IsProcFieldCall then
      Result := True;
    Exit;
  end;
  { FuncPtrExpr(args) -- a call through the procedure pointer an expression
    yields (GetFn()(X), Fns[I](X)) -- returns +1 exactly like the
    procedural-variable form above.  Missing here, the assignment retained
    the result again and leaked one reference per call. }
  if AExpr is TIndirectFuncCallExpr then
    Exit(True);
  { Indexed property subscript: L[I] desugars to Subscript(FieldAccess(Items))
    where Items has a ReadMethod.  The subscript emitter delegates to the
    getter — the result inherits the +1. }
  if IsFoldedPropSubscript(AExpr) and
     (TFieldAccessExpr(TStringSubscriptExpr(AExpr).StrExpr).PropRead.ReadMethod <> '') then
    Result := True;
end;

function LoweredCallStmt(AStmt: TASTStmt): TASTStmt;
begin
  Result := nil;
  if AStmt is TMethodCallStmt then
    Result := TMethodCallStmt(AStmt).LoweredCall
  else if AStmt is TProcCall then
    Result := TProcCall(AStmt).LoweredCall;
end;

function LoweredSetterCall(AStmt: TASTStmt): TMethodCallStmt;
var
  S: TASTStmt;
begin
  S := nil;
  if AStmt is TAssignment then
    S := TAssignment(AStmt).SetterCall
  else if AStmt is TFieldAssignment then
    S := TFieldAssignment(AStmt).SetterCall
  else if AStmt is TStaticSubscriptAssign then
    S := TStaticSubscriptAssign(AStmt).SetterCall;
  Result := nil;
  if S is TMethodCallStmt then
    Result := TMethodCallStmt(S);
end;

function IsProcFieldCallExpr(AExpr: TASTExpr): Boolean;
begin
  Result := ((AExpr is TFuncCallExpr) and TFuncCallExpr(AExpr).IsProcFieldCall) or
            ((AExpr is TMethodCallExpr) and
             TMethodCallExpr(AExpr).IsProcFieldCall);
end;

function IsAggCallValue(AExpr: TASTExpr): Boolean;
var
  FA: TFieldAccessExpr;
begin
  Result := False;
  if AExpr = nil then Exit;
  if (AExpr is TFuncCallExpr) or (AExpr is TMethodCallExpr) or
     (AExpr is TIndirectFuncCallExpr) or IsFoldedPropSubscript(AExpr) then
    Exit(True);
  if AExpr is TIdentExpr then
    Exit(TIdentExpr(AExpr).IsImplicitSelfMethod);
  if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    Result := FA.IsMethodCall or
              ((FA.PropRead <> nil) and (FA.PropRead.ReadMethod <> ''));
  end;
end;

function IsOALitBlock(AExpr: TASTExpr): Boolean;
begin
  Result := (AExpr is TArrayLiteralExpr) and
    not ((AExpr.ResolvedType <> nil) and
         (AExpr.ResolvedType.Kind = tyDynArray));
end;

function AccessPathHasCall(AExpr: TASTExpr): Boolean;
var
  FA: TFieldAccessExpr;
begin
  if AExpr = nil then
    Exit(False);
  if IsAggCallValue(AExpr) or (AExpr is TInheritedCallExpr) then
    Exit(True);
  if (AExpr is TIntLiteral) or (AExpr is TFloatLiteral) or
     (AExpr is TStringLiteral) or (AExpr is TNilLiteral) then
    Exit(False);
  if AExpr is TIdentExpr then
    Exit(False);
  if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    Exit(AccessPathHasCall(FA.Base) or AccessPathHasCall(FA.PropIndexExpr));
  end;
  if AExpr is TStringSubscriptExpr then
    Exit(AccessPathHasCall(TStringSubscriptExpr(AExpr).StrExpr) or
         AccessPathHasCall(TStringSubscriptExpr(AExpr).IndexExpr));
  if AExpr is TDerefExpr then
    Exit(AccessPathHasCall(TDerefExpr(AExpr).Expr));
  if AExpr is TBinaryExpr then
    Exit((TBinaryExpr(AExpr).LoweredCall <> nil) or
         AccessPathHasCall(TBinaryExpr(AExpr).Left) or
         AccessPathHasCall(TBinaryExpr(AExpr).Right));
  if AExpr is TNotExpr then
    Exit(AccessPathHasCall(TNotExpr(AExpr).Expr));
  if AExpr is TNegExpr then
    Exit((TNegExpr(AExpr).LoweredCall <> nil) or
         AccessPathHasCall(TNegExpr(AExpr).Expr));
  Result := True;
end;

function IsFoldedPropSubscript(AExpr: TASTExpr): Boolean;
begin
  Result := (AExpr is TStringSubscriptExpr) and
            (TStringSubscriptExpr(AExpr).IndexExpr = nil) and
            (TStringSubscriptExpr(AExpr).StrExpr is TFieldAccessExpr) and
            (TFieldAccessExpr(TStringSubscriptExpr(AExpr).StrExpr).PropRead <> nil);
end;

function ExprMayDeferTransientBase(AExpr: TASTExpr): Boolean;
var
  FA: TFieldAccessExpr;
  I: Integer;
begin
  Result := False;
  if AExpr = nil then Exit;
  { the deferring shape: a retained class/interface field read whose base is an
    owned transient (MakeObj().ClassField).  Interface fields defer on x86-64
    too, so include tyInterface. }
  if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    if (FA.Base <> nil) and FA.IsClassAccess and (FA.FieldInfo <> nil) and
       (FA.FieldInfo.TypeDesc <> nil) and
       (FA.FieldInfo.TypeDesc.Kind in [tyClass, tyInterface]) and
       (not FA.IsConstant) and ArcExprOwnsRef(FA.Base) then
      Exit(True);
    if ExprMayDeferTransientBase(FA.Base) then Exit(True);
    Exit;
  end;
  { recurse through every subexpression EmitExpr descends into }
  if AExpr is TBinaryExpr then
    Result := ExprMayDeferTransientBase(TBinaryExpr(AExpr).Left) or
              ExprMayDeferTransientBase(TBinaryExpr(AExpr).Right)
  else if AExpr is TNotExpr then
    Result := ExprMayDeferTransientBase(TNotExpr(AExpr).Expr)
  else if AExpr is TNegExpr then
    Result := ExprMayDeferTransientBase(TNegExpr(AExpr).Expr)
  else if AExpr is TIsExpr then
    Result := ExprMayDeferTransientBase(TIsExpr(AExpr).Obj)
  else if AExpr is TAsExpr then
    Result := ExprMayDeferTransientBase(TAsExpr(AExpr).Obj)
  else if AExpr is TMethodCallExpr then
  begin
    Result := ExprMayDeferTransientBase(TMethodCallExpr(AExpr).ObjExpr);
    if not Result and (TMethodCallExpr(AExpr).Args <> nil) then
      for I := 0 to TMethodCallExpr(AExpr).Args.Count - 1 do
        if ExprMayDeferTransientBase(
             TASTExpr(TMethodCallExpr(AExpr).Args.Items[I])) then
          Exit(True);
  end
  else if AExpr is TFuncCallExpr then
  begin
    if TFuncCallExpr(AExpr).Args <> nil then
      for I := 0 to TFuncCallExpr(AExpr).Args.Count - 1 do
        if ExprMayDeferTransientBase(
             TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])) then
          Exit(True);
  end;
end;

function ArcExprIsUnownedStrTransient(AExpr: TASTExpr): Boolean;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr.ResolvedType = nil then Exit;
  if not AExpr.ResolvedType.IsString() then Exit;
  { String concatenation: _StringConcat returns an rc = 0 StrAlloc buffer. }
  if AExpr is TBinaryExpr then
    Exit(True);
  { Built-in call (no resolved decl, not an indirect call through a proc
    variable): the RTL helpers return rc = 0 StrAlloc buffers.  The
    'string(x)' conversion is one of them only when x is a PChar:
    string(pchar) always allocates (_StringFromPChar), so an unstored
    result must be disposed or it leaks one buffer per evaluation -- a
    file-system call in a loop grew the arena without bound on arm64.
    string(string) can be a pointer-preserving no-op, and disposing that
    would free the source, so every other cast-shaped call stays borrowed. }
  { (an implicit-Self procedural-field call has no resolved decl either, but
    it is a real call returning +1 -- ArcExprOwnsRef -- not a built-in) }
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (not TFuncCallExpr(AExpr).IsProcFieldCall) then
  begin
    if not SameText(TFuncCallExpr(AExpr).Name, 'string') then
      Exit(True);
    if (TFuncCallExpr(AExpr).Args.Count = 1) and
       (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind = tyPChar) then
      Exit(True);
  end;
end;

function ArcIsOwnedClassCompare(AExpr: TASTExpr): Boolean;
var
  BE: TBinaryExpr;
begin
  Result := False;
  if not (AExpr is TBinaryExpr) then Exit;
  BE := TBinaryExpr(AExpr);
  if not (BE.Op in [boEQ, boNE]) then Exit;
  Result :=
    ((BE.Left.ResolvedType <> nil) and (BE.Left.ResolvedType.Kind = tyClass) and
     ArcExprOwnsRef(BE.Left)) or
    ((BE.Right.ResolvedType <> nil) and (BE.Right.ResolvedType.Kind = tyClass) and
     ArcExprOwnsRef(BE.Right));
end;

function ArcBuiltinStrArgOwnsRef(AExpr: TASTExpr): Boolean;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr.ResolvedType = nil then Exit;
  if not AExpr.ResolvedType.IsString() then Exit;
  Result := ArcExprOwnsRef(AExpr) or ArcExprIsUnownedStrTransient(AExpr);
end;

function CodegenMangle(const AName: string): string;
var
  I, C, Depth: Integer;
  Clean: Boolean;
begin
  { Fast path: the overwhelming majority of names contain none of the mangled
    characters — return the input unchanged instead of rebuilding it with one
    concat (and its ARC churn) per character. }
  Clean := True;
  for I := 0 to Length(AName) - 1 do
  begin
    C := StrAt(AName, I);
    if (C = 60) or (C = 62) or (C = 44) or (C = 36) or (C = 64) or
       (C = 94) or (C = 32) or (C = 91) then
    begin
      Clean := False;
      break;
    end;
  end;
  if Clean then
    Exit(AName);
  Result := '';
  Depth := 0;
  for I := 0 to Length(AName) - 1 do
  begin
    C := StrAt(AName, I);
    { the bounds of a static-array type argument (TBox<array[-1..3] of
      Integer> -> TBox_array_m1_3_of_Integer): '[' opens them, '..' becomes
      one '_', a minus sign 'm', ']' closes them.  Outside brackets a '.'
      is left alone, so no existing symbol changes (GH #228: the x86-64
      internal assembler rejected the bracketed names) }
    if (C = 91) then
    begin
      Result := Result + '_';
      Inc(Depth);
      Continue;
    end;
    if (Depth > 0) and (C = 93) then
    begin
      Dec(Depth);
      Continue;
    end;
    if (Depth > 0) and (C = 46) then
    begin
      if (I = 0) or (StrAt(AName, I - 1) <> 46) then
        Result := Result + '_';
      Continue;
    end;
    if (Depth > 0) and (C = 45) then
    begin
      Result := Result + 'm';
      Continue;
    end;
    case C of
      60:  Result := Result + '_';    { '<' }
      62:  ;                          { '>' — skip }
      44:  Result := Result + '_';    { ',' }
      32:  Result := Result + '_';    { ' ' — e.g. 'class of T' }
      36:  Result := Result + '_D_';  { '$' — overload delimiter }
      64:  Result := Result + '_V_';  { '@' — var-param prefix }
      94:  Result := Result + '_P_';  { '^' — pointer prefix }
    else
      Result := Result + Chr(C);
    end;
  end;
end;

function IntfRefName(AResolved: TTypeDesc; const ASourceName: string): string;
begin
  if (AResolved <> nil) and (AResolved.Name <> '') then
    Result := AResolved.Name
  else
    Result := ASourceName;
end;

function IsIntfType(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind = tyInterface);
end;

function NestedCapturedVarType(ADecl: TMethodDecl;
  const AName: string): TTypeDesc;
var
  Encl: TMethodDecl;
  I, J: Integer;
  VD:   TVarDecl;
begin
  Result := nil;
  if ADecl = nil then Exit;
  Encl := ADecl.EnclosingDecl;
  while Encl <> nil do
  begin
    if Encl.Body <> nil then
      for I := 0 to Encl.Body.Decls.Count - 1 do
      begin
        VD := TVarDecl(Encl.Body.Decls.Items[I]);
        for J := 0 to VD.Names.Count - 1 do
          if SameText(VD.Names.Strings[J], AName) then
          begin
            Result := VD.ResolvedType;
            Exit;
          end;
      end;
    for I := 0 to Encl.Params.Count - 1 do
      if SameText(TMethodParam(Encl.Params.Items[I]).ParamName, AName) then
      begin
        Result := TMethodParam(Encl.Params.Items[I]).ResolvedType;
        Exit;
      end;
    Encl := Encl.EnclosingDecl;
  end;
end;

end.