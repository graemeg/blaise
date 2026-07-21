{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.backend;

{ Abstract per-architecture machine-code lowering base for the native code
  generator.

  Lives in its own unit (separate from blaise.codegen.native) so the concrete
  per-CPU backends — blaise.codegen.native.x86_64 etc. — can subclass it
  without a circular dependency back to the driver unit that constructs them.

  A concrete subclass implements instruction selection, register allocation,
  ABI lowering, and assembly printing for one target CPU.  Shared, non-abstract
  helpers (the naive stack-slot allocator, cross-target emit utilities) will be
  added here as the backend grows.

  ARC lowering note: the *decision* logic for ARC is target-independent —
  `NativeExprOwnsRef` (a free function over the AST) decides whether a value
  owns +1, and the field-kind walk (EmitRecordFieldReleases /
  EmitRecordFieldRetains / EmitManagedReleaseAt / EmitStaticArrayReleaseElems
  below) decides *which* fields/elements need a release or retain.  Those
  walks live HERE as Template Methods: the walk order, field-kind dispatch,
  weak/unretained filtering and record/static-array recursion are shared,
  while the leaf steps (which scratch register holds a derived base across a
  call, which mnemonic loads a slot, which runtime helper is called) are the
  abstract Arc*/Emit*SlotAt primitives each per-CPU backend implements.  A
  new CPU backend (arm64) implements only the primitives and inherits the
  walk — the field-kind dispatch is never duplicated per subclass. }

interface

uses
  SysUtils, contnrs, uAST, uSymbolTable, blaise.codegen, strutils,
  blaise.codegen.target, uDebugFacts;

type
  ENativeCodeGenError = class(Exception);

  TNativeBackend = class
  protected
    FTarget:    TTargetDesc;
    FSymTable:  TSymbolTable;     { not owned }
    FDebugMode: Boolean;
    { Separate-compilation (incremental unit) mode: suppress the once-per-program
      TObject/TCustomAttribute system defs, which the program object provides —
      emitting them in each unit object would collide at link time. }
    FSeparateCompile: Boolean;
    FFinalized: Boolean;
    { Assembly text is built append-only and read once at the end, so a
      TStringBuilder (single growable buffer, no per-line heap string and no
      O(N^2) final concat) is the right structure — the same approach the QBE
      backend's TIRBuffer uses. }
    FAsm:      TStringBuilder;

    { Append one line of assembly (a newline is added).  Virtual so a target
      backend can observe the emitted stream (the x86-64 backend tracks the
      stack depth here to keep call sites 16-byte aligned). }
    procedure Emit(const ALine: string); virtual;
    { Append a blank separator line. }
    procedure EmitBlank;

    { Roll-back support for two-pass function emission (stage-1 register
      promotion): mark the buffer, emit a function, inspect the emitted
      region, and optionally truncate back to the mark and re-emit. }
    function  AsmMark: Integer;
    procedure AsmRollback(AMark: Integer);
    function  AsmContainsFrom(AMark: Integer; const ANeedle: string): Boolean;
    function  AsmCountFrom(AMark: Integer; const ANeedle: string): Integer;

    function IsRecordManagedClean(ARec: TRecordTypeDesc): Boolean;
    function IsRecordAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
    function IsRecordAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
    function IsRecordAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
    function EightbyteIsSSE(ARec: TRecordTypeDesc; AStartByte: Integer): Boolean;
    function ClassifyRecordReturn(ARec: TRecordTypeDesc): TRecReturnClass;

    { ---- ARC field-kind walk (Template Method) ----

      The walks below are shared by every CPU backend; register operands are
      opaque strings the leaf primitives interpret (AT&T '%rbx' today, an
      AArch64 'x19' tomorrow).  ABaseReg must be callee-saved — the walk
      emits runtime calls between uses. }

    { Release every ARC-managed field of ART whose storage starts at the
      address in ABaseReg.  Strings, classes, dyn-arrays and interface
      obj-slots are released and their slots zeroed; weak fields cleared;
      unretained fields skipped; nested record fields recursed into at their
      offset; static-array-of-managed fields walked element-by-element
      (BUG-017) — kept symmetric with EmitRecordFieldRetains / record copy,
      which retain the same elements. }
    procedure EmitRecordFieldReleases(ART: TRecordTypeDesc;
                                      const ABaseReg: string;
                                      AZero: Boolean = True);
    { Release one ARC-managed value of type AType whose storage is at the
      address in ABaseReg.  Scalars (string/class/intf/dynarray) release
      directly; records recurse via EmitRecordFieldReleases; static arrays
      recurse element-by-element via EmitStaticArrayReleaseElems.  When AZero
      is set the scalar managed slot is zeroed after release. }
    procedure EmitManagedReleaseAt(AType: TTypeDesc; const ABaseReg: string;
                                   AZero: Boolean);
    { Release every managed element of a static array whose inline storage
      starts at the address in ABaseReg. }
    procedure EmitStaticArrayReleaseElems(AType: TStaticArrayTypeDesc;
                                          const ABaseReg: string;
                                          AZero: Boolean);
    { Retain every ARC-managed field of ART (the copy-side twin of
      EmitRecordFieldReleases): weak and unretained fields are skipped,
      nested records and static-array-of-managed fields recursed. }
    procedure EmitRecordFieldRetains(ART: TRecordTypeDesc;
                                     const ABaseReg: string);
    { Retain one ARC-managed value of type AType whose storage is at the
      address in ABaseReg — the retain-side mirror of EmitManagedReleaseAt:
      scalars retain directly, records recurse via EmitRecordFieldRetains,
      static arrays via EmitStaticArrayAddRefElems (BUG-017). }
    procedure EmitManagedAddRefAt(AType: TTypeDesc; const ABaseReg: string);
    { Retain every managed element of a static array whose inline storage
      starts at the address in ABaseReg — the retain-side mirror of
      EmitStaticArrayReleaseElems. }
    procedure EmitStaticArrayAddRefElems(AType: TStaticArrayTypeDesc;
                                         const ABaseReg: string);

    { ---- ARC walk primitives (abstract per-CPU leaves) ---- }

    { The callee-saved scratch register a nested-record recursion walks with
      (x86-64: '%r14'). }
    function  ArcNestedBaseReg: string; virtual; abstract;
    { Save the nested-base scratch register and derive ABaseReg+AOffset into
      it (the recursion base must survive the recursive walk's calls). }
    procedure ArcPushNestedBase(AOffset: Integer;
                                const ABaseReg: string); virtual; abstract;
    { Restore the nested-base scratch register. }
    procedure ArcPopNestedBase; virtual; abstract;
    { Clear a weak reference slot at ABaseReg+AOffset (call _WeakClear with
      the SLOT ADDRESS). }
    procedure EmitWeakClearAt(AOffset: Integer;
                              const ABaseReg: string); virtual; abstract;
    { Load the managed pointer at ABaseReg+AOffset, call the release helper
      AType selects (_StringRelease/_DynArrayRelease/_ClassRelease), and
      zero the slot when AZero is set. }
    procedure EmitReleaseSlotAt(AType: TTypeDesc; AOffset: Integer;
                                const ABaseReg: string;
                                AZero: Boolean); virtual; abstract;
    { Load the managed pointer at ABaseReg+AOffset and call the retain helper
      AType selects (_StringAddRef/_DynArrayAddRef/_ClassAddRef). }
    procedure EmitRetainSlotAt(AType: TTypeDesc; AOffset: Integer;
                               const ABaseReg: string); virtual; abstract;
    { Begin a static-array element walk: save two callee-saved scratch
      registers and anchor the array base (x86-64: %r15 base, %r14 element). }
    procedure ArcEnterArrayWalk(const ABaseReg: string); virtual; abstract;
    { Derive the element address at AByteOffset from the anchored array base
      into the element scratch register. }
    procedure ArcArrayElemAddr(AByteOffset: Integer); virtual; abstract;
    { The element scratch register ArcArrayElemAddr targets. }
    function  ArcArrayElemReg: string; virtual; abstract;
    { End the static-array element walk (restore the scratch registers). }
    procedure ArcLeaveArrayWalk; virtual; abstract;

    { ---- target-specific program lowering (abstract) ---- }

    { Emit the program entry function ($main): label, frame setup, the
      _SetArgs runtime call, then lower the program body, then return 0. }
    procedure EmitProgram(AProg: TProgram); virtual; abstract;
    { Emit a dependency unit's bodies + data (no $main) into the shared buffer
      for the whole-program multi-unit model. }
    procedure EmitUnit(AUnit: TUnit); virtual; abstract;
    { Emit accumulated data (.data/.bss/.rodata) after all units have been
      processed.  Called once from GenerateUnit or GetOutput — never from
      EmitUnit itself, because in unit-mode the driver appends dep units
      first and the data section must materialise only once at the end. }
    procedure FinalizeEmit; virtual;
  public
    constructor Create(const ATarget: TTargetDesc); virtual;
    destructor Destroy; override;

    { Multi-unit (whole-program) codegen: AppendUnit per dependency, then
      AppendProgram — neither clears the buffer, so units + program accumulate
      into one assembly text retrieved via GetOutput. }
    procedure AppendUnit(AUnit: TUnit);
    procedure AppendProgram(AProg: TProgram);
    { Separate-compilation init-call registration: record a dep unit whose body
      is compiled elsewhere so $main still calls its <Unit>_init.  Concrete
      backends that maintain an init-call list override this; the default is a
      no-op. }
    procedure NoteDepInitUnit(const AUnitName: string;
      AHasInit: Boolean); virtual;
    { Teardown twin of NoteDepInitUnit: register a dep unit whose
      <Unit>_fini (user finalization + managed-global release) is compiled
      elsewhere so $main calls it at main_exit, in reverse init order.
      Concrete backends that maintain a fini-call list override this; the
      default is a no-op (the arm64 backend does not emit per-unit fini
      yet). }
    procedure NoteDepFiniUnit(const AUnitName: string;
      AHasFini: Boolean); virtual;
    function  GetOutput: string;

    procedure SetSymbolTable(ASymTable: TSymbolTable);
    procedure SetSeparateCompile(AEnabled: Boolean);
    { OPDF debug-facts sink — concrete backends that support exact debug
      info override this; the default ignores the facts object. }
    procedure SetDebugFacts(AFacts: TDbgFacts); virtual;
    procedure SetDebugMode(AEnabled: Boolean);

    { Lower a whole program to assembly text and return it. }
    function GenerateProgram(AProg: TProgram): string;
    { Lower a single unit (in isolation) to assembly text and return it. }
    function GenerateUnit(AUnit: TUnit): string;

    property Target: TTargetDesc read FTarget;
  end;

  TNativeBackendClass = class of TNativeBackend;

implementation

procedure TNativeBackend.SetDebugFacts(AFacts: TDbgFacts);
begin
  { Default: backend does not collect debug facts. }
end;

procedure TNativeBackend.FinalizeEmit;
begin
end;

constructor TNativeBackend.Create(const ATarget: TTargetDesc);
begin
  inherited Create();
  FTarget   := ATarget;
  FSymTable := nil;
  FAsm      := TStringBuilder.Create();
end;

destructor TNativeBackend.Destroy;
begin
  FAsm.Free();
  inherited Destroy();
end;

procedure TNativeBackend.SetSymbolTable(ASymTable: TSymbolTable);
begin
  FSymTable := ASymTable;
end;

procedure TNativeBackend.SetSeparateCompile(AEnabled: Boolean);
begin
  FSeparateCompile := AEnabled;
end;

procedure TNativeBackend.SetDebugMode(AEnabled: Boolean);
begin
  FDebugMode := AEnabled;
end;

procedure TNativeBackend.Emit(const ALine: string);
begin
  FAsm.AppendLine(ALine);
end;

procedure TNativeBackend.EmitBlank;
begin
  FAsm.AppendLine();
end;

function TNativeBackend.AsmMark: Integer;
begin
  Result := FAsm.Length;
end;

procedure TNativeBackend.AsmRollback(AMark: Integer);
begin
  FAsm.Truncate(AMark);
end;

function TNativeBackend.AsmContainsFrom(AMark: Integer;
  const ANeedle: string): Boolean;
begin
  Result := FAsm.ContainsFrom(AMark, ANeedle);
end;

function TNativeBackend.AsmCountFrom(AMark: Integer;
  const ANeedle: string): Integer;
begin
  Result := FAsm.CountFrom(AMark, ANeedle);
end;

{ The record-return ABI classifier and its leaf predicates now live as shared
  free functions in blaise.codegen (byte-identical to the QBE backend's former
  twin).  These methods delegate so existing Self.X call sites are unchanged. }
function TNativeBackend.IsRecordManagedClean(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretManagedClean(ARec);
end;

function TNativeBackend.IsRecordAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretAllIntegerLeaves(ARec);
end;

function TNativeBackend.IsRecordAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretAllFloatLeaves(ARec);
end;

function TNativeBackend.IsRecordAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretAllIntOrFloatLeaves(ARec);
end;

function TNativeBackend.EightbyteIsSSE(ARec: TRecordTypeDesc;
  AStartByte: Integer): Boolean;
begin
  Result := RecretEightbyteIsSSE(ARec, AStartByte);
end;

function TNativeBackend.ClassifyRecordReturn(ARec: TRecordTypeDesc): TRecReturnClass;
begin
  Result := RecretClassify(ARec, FTarget);
end;

{ ---- ARC field-kind walk (Template Method bodies) ----

  The walk order and field-kind decisions here must stay byte-identical in
  effect to the historical x86-64 walk: any change to which fields are
  touched, or in which order, changes emitted release/retain sequences on
  every backend at once. }

function ArcFieldIsManagedScalar(AType: TTypeDesc): Boolean;
begin
  Result := AType.IsString() or (AType.Kind = tyClass)
    or (AType.Kind = tyDynArray) or (AType.Kind = tyInterface);
end;

procedure TNativeBackend.EmitRecordFieldReleases(ART: TRecordTypeDesc;
  const ABaseReg: string; AZero: Boolean);
var
  I: Integer;
  F: TFieldInfo;
begin
  if ART = nil then Exit;
  for I := 0 to ART.Fields.Count - 1 do
  begin
    F := TFieldInfo(ART.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    { Nested record field: recurse into its managed sub-fields.  ABaseReg
      must stay pointed at the parent record (each iteration derives field
      addresses from it), so the recursion walks with its own callee-saved
      scratch register. }
    if F.TypeDesc.Kind = tyRecord then
    begin
      Self.ArcPushNestedBase(F.Offset, ABaseReg);
      Self.EmitRecordFieldReleases(TRecordTypeDesc(F.TypeDesc),
        Self.ArcNestedBaseReg(), AZero);
      Self.ArcPopNestedBase();
      Continue;
    end;
    { Static-array-of-managed field (BUG-017): release each element via the
      array walk.  Kept symmetric with EmitRecordFieldRetains and the copy
      paths, which retain the elements — release-only or retain-only here
      over/under-releases on every record copy / by-value param pass. }
    if F.TypeDesc.Kind = tyStaticArray then
    begin
      if ArcTypeHasManagedContent(F.TypeDesc) then
      begin
        Self.ArcPushNestedBase(F.Offset, ABaseReg);
        Self.EmitStaticArrayReleaseElems(TStaticArrayTypeDesc(F.TypeDesc),
          Self.ArcNestedBaseReg(), AZero);
        Self.ArcPopNestedBase();
      end;
      Continue;
    end;
    if not ArcFieldIsManagedScalar(F.TypeDesc) then
      Continue;
    if F.IsUnretained and (F.TypeDesc.Kind = tyClass) then
      Continue;
    if F.IsWeak then
    begin
      Self.EmitWeakClearAt(F.Offset, ABaseReg);
      Continue;
    end;
    { AZero: normally the released slot is zeroed (dtor, teardown, sret pre-
      release — a live nil is required).  On a record COPY path the dest is
      immediately memcpy-overwritten, so zeroing is redundant AND breaks a
      self-copy (R := R): with src==dest the zero clobbers the shared field
      before memcpy reads it, losing the value and orphaning the +1 retain.
      Copy sites pass AZero=False (BUG-20260720-managed-record-self-assign). }
    Self.EmitReleaseSlotAt(F.TypeDesc, F.Offset, ABaseReg, AZero);
  end;
end;

procedure TNativeBackend.EmitManagedReleaseAt(AType: TTypeDesc;
  const ABaseReg: string; AZero: Boolean);
begin
  if AType = nil then Exit;
  if AType.Kind = tyRecord then
  begin
    { thread AZero: a static-array-OF-record element reached on a record-copy
      path must not zero its managed fields either (BUG-20260720-managed-record-
      self-assign — the array-of-record field shape). }
    Self.EmitRecordFieldReleases(TRecordTypeDesc(AType), ABaseReg, AZero);
    Exit;
  end;
  if AType.Kind = tyStaticArray then
  begin
    Self.EmitStaticArrayReleaseElems(TStaticArrayTypeDesc(AType), ABaseReg,
      AZero);
    Exit;
  end;
  if not ArcFieldIsManagedScalar(AType) then
    Exit;
  Self.EmitReleaseSlotAt(AType, 0, ABaseReg, AZero);
end;

procedure TNativeBackend.EmitStaticArrayReleaseElems(
  AType: TStaticArrayTypeDesc; const ABaseReg: string; AZero: Boolean);
var
  I, ElemSize: Integer;
begin
  if (AType = nil) or (AType.ElementType = nil) then Exit;
  ElemSize := AType.ElementType.RawSize();
  Self.ArcEnterArrayWalk(ABaseReg);
  for I := 0 to AType.HighBound - AType.LowBound do
  begin
    Self.ArcArrayElemAddr(I * ElemSize);
    Self.EmitManagedReleaseAt(AType.ElementType, Self.ArcArrayElemReg(),
      AZero);
  end;
  Self.ArcLeaveArrayWalk();
end;

procedure TNativeBackend.EmitRecordFieldRetains(ART: TRecordTypeDesc;
  const ABaseReg: string);
var
  I: Integer;
  F: TFieldInfo;
begin
  if ART = nil then Exit;
  for I := 0 to ART.Fields.Count - 1 do
  begin
    F := TFieldInfo(ART.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    if F.TypeDesc.Kind = tyRecord then
    begin
      Self.ArcPushNestedBase(F.Offset, ABaseReg);
      Self.EmitRecordFieldRetains(TRecordTypeDesc(F.TypeDesc),
        Self.ArcNestedBaseReg());
      Self.ArcPopNestedBase();
      Continue;
    end;
    { Static-array-of-managed field (BUG-017): retain each element — the
      retain-side mirror of the release arm in EmitRecordFieldReleases. }
    if F.TypeDesc.Kind = tyStaticArray then
    begin
      if ArcTypeHasManagedContent(F.TypeDesc) then
      begin
        Self.ArcPushNestedBase(F.Offset, ABaseReg);
        Self.EmitStaticArrayAddRefElems(TStaticArrayTypeDesc(F.TypeDesc),
          Self.ArcNestedBaseReg());
        Self.ArcPopNestedBase();
      end;
      Continue;
    end;
    if not ArcFieldIsManagedScalar(F.TypeDesc) then
      Continue;
    if F.IsUnretained and (F.TypeDesc.Kind = tyClass) then
      Continue;
    if F.IsWeak then Continue;
    Self.EmitRetainSlotAt(F.TypeDesc, F.Offset, ABaseReg);
  end;
end;

procedure TNativeBackend.EmitManagedAddRefAt(AType: TTypeDesc;
  const ABaseReg: string);
begin
  if AType = nil then Exit;
  if AType.Kind = tyRecord then
  begin
    Self.EmitRecordFieldRetains(TRecordTypeDesc(AType), ABaseReg);
    Exit;
  end;
  if AType.Kind = tyStaticArray then
  begin
    Self.EmitStaticArrayAddRefElems(TStaticArrayTypeDesc(AType), ABaseReg);
    Exit;
  end;
  if not ArcFieldIsManagedScalar(AType) then
    Exit;
  Self.EmitRetainSlotAt(AType, 0, ABaseReg);
end;

procedure TNativeBackend.EmitStaticArrayAddRefElems(
  AType: TStaticArrayTypeDesc; const ABaseReg: string);
var
  I, ElemSize: Integer;
begin
  if (AType = nil) or (AType.ElementType = nil) then Exit;
  ElemSize := AType.ElementType.RawSize();
  Self.ArcEnterArrayWalk(ABaseReg);
  for I := 0 to AType.HighBound - AType.LowBound do
  begin
    Self.ArcArrayElemAddr(I * ElemSize);
    Self.EmitManagedAddRefAt(AType.ElementType, Self.ArcArrayElemReg());
  end;
  Self.ArcLeaveArrayWalk();
end;

function TNativeBackend.GenerateProgram(AProg: TProgram): string;
begin
  FAsm.Clear();
  Self.EmitProgram(AProg);
  Result := FAsm.ToString();
end;

function TNativeBackend.GenerateUnit(AUnit: TUnit): string;
begin
  FAsm.Clear();
  FSeparateCompile := True;
  Self.EmitUnit(AUnit);
  Self.FinalizeEmit();
  Result := FAsm.ToString();
end;

procedure TNativeBackend.AppendUnit(AUnit: TUnit);
begin
  { No clear — units and the program accumulate into one buffer. }
  Self.EmitUnit(AUnit);
end;

procedure TNativeBackend.AppendProgram(AProg: TProgram);
begin
  { No clear — emit the program after the already-appended units. }
  Self.EmitProgram(AProg);
end;

procedure TNativeBackend.NoteDepInitUnit(const AUnitName: string;
  AHasInit: Boolean);
begin
  { Default: no init-call list to maintain.  The x86_64 backend overrides. }
end;

procedure TNativeBackend.NoteDepFiniUnit(const AUnitName: string;
  AHasFini: Boolean);
begin
  { Default: no fini-call list to maintain.  The x86_64 backend overrides. }
end;

function TNativeBackend.GetOutput: string;
begin
  if FSeparateCompile and (not FFinalized) then
    Self.FinalizeEmit();
  Result := FAsm.ToString();
end;

end.
