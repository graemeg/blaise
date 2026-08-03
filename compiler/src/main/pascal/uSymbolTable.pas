{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uSymbolTable;

interface

uses
  Classes, SysUtils, contnrs, Generics.Collections;

type
  { Member visibility — class/record field, method, and property access scope.
    Default (a member declared before any visibility keyword) is mvPublic, to
    match Blaise's previous behaviour where visibility was parsed but never
    enforced (everything was effectively public).
      mvPublic / mvPublished — visible everywhere the type is.
      mvPrivate              — visible only within the declaring UNIT
                               (classic Pascal unit-scoped privacy).
      mvProtected            — as mvPrivate plus descendant types' methods,
                               regardless of unit.
      mvStrictPrivate        — visible only from the declaring TYPE's methods.
      mvStrictProtected      — declaring type plus its descendants' methods.
    Declared here (not in uAST) so the symbol-table descriptors can carry it;
    uAST uses uSymbolTable, so the type flows up to the AST member decls. }
  TMemberVisibility = (
    mvPublic,
    mvPrivate,
    mvProtected,
    mvPublished,
    mvStrictPrivate,
    mvStrictProtected
  );

  { ------------------------------------------------------------------ }
  {  Type descriptors                                                   }
  { ------------------------------------------------------------------ }

  TTypeKind = (
    tyInteger,    { Int32  — QBE 'w' }
    tyInt64,      { Int64  — QBE 'l' }
    tyUInt32,     { UInt32 — QBE 'w' unsigned }
    tyUInt64,     { UInt64 / QWord — QBE 'l' unsigned }
    tySmallInt,   { SmallInt / Int16 — QBE 'h' (signed half-word) }
    tyWord,       { Word / UInt16 — QBE 'h' (unsigned half-word) }
    tyByte,       { Byte   — QBE 'b' }
    tyBoolean,    { Boolean — stored as byte, 0/1 only }
    tyString,     { ARC-managed UTF-8 string }
    tyRecord,     { Stack-allocated aggregate (Phase 2) }
    tyClass,      { Heap-allocated, single-inheritance (Phase 2) }
    tyInterface,  { Zero-GUID interface reference (Phase 3) }
    tyVoid,       { No value — used as procedure return type }
    tyNil,        { Pseudo-type for the nil literal; compatible with tyClass }
    tyPointer,    { Typed or untyped pointer — QBE 'l'; see TPointerTypeDesc }
    tyEnum,       { Enumeration type — stored as QBE 'w' (Integer); see TEnumTypeDesc }
    tyOpenArray,   { Open-array parameter — two-register ABI: data ptr + high index }
    tyStaticArray, { Fixed-size array: stack-allocated, compile-time bounds }
    tyDynArray,    { Dynamic array: heap-allocated, ref-counted, runtime length }
    tyPChar, { Opaque C pointer for interop: PChar(str) / string(pchar) }
    tySet,   { Bit-set over an enum base type — QBE 'w' (≤32 members) or 'l' (≤64) }
    tyProcedural, { Bare procedural pointer — QBE 'l'; see TProceduralTypeDesc.
                   Not 'of object' (method ptr), not 'reference to' (closure). }
    tyDouble,    { 64-bit IEEE 754 float — QBE 'd' }
    tySingle,    { 32-bit IEEE 754 float — QBE 's' }
    tyMetaClass  { 'class of TFoo' — typeinfo pointer, see TMetaClassTypeDesc }
  );

  TTypeDesc = class
  public
    Kind: TTypeKind;
    Name: string;
    { Name of the unit that declared this named type (empty for builtins and
      program-scope types).  Set by TSymbolTable.Define when the type symbol is
      registered.  Codegen mangles the type's storage symbols (typeinfo,
      vtable, _FieldCleanup, itab) with this owner so two used units exporting a
      same-named type emit distinct, non-colliding symbols. }
    OwningUnit: string;
    { True when this descriptor was created for a NAMED integer subrange
      (type TIdx = lo..hi;).  Layout/Kind/RawSize remain those of the narrowest
      fitting standard integer type — the value behaves as an ordinary unchecked
      int — but the lo..hi bounds are retained as compile-time metadata so the
      array-index resolver can fold array[TIdx] -> array[lo..hi].  No other path
      (codegen, IsNumeric/IsOrdinal, assignment compatibility) consults these. }
    IsSubrange: Boolean;
    SubrangeLow: Int64;
    SubrangeHigh: Int64;
    function IsNumeric: Boolean;
    function IsFloat: Boolean;
    function IsString: Boolean;
    function IsOrdinal: Boolean;
    { True when this type may index an array subscript: any integer-family
      type, an enum, or Boolean (a 2-element ordinal).  Floats are numeric
      but not valid indices; historically IsNumeric was used here and let
      them slip through — index checks should prefer this predicate. }
    function IsArrayIndex: Boolean;
    function IsRecord: Boolean;
    { True byte size of a value: 1 for Byte/Boolean, 4 for Integer/Single, 8
      for pointer/string/Int64/Double, sum-of-fields for records (with natural
      alignment padding).  Currently identical to RawSize. }
    function ByteSize: Integer;
    { Natural alignment requirement: 1 for Byte/Boolean, 4 for Integer, 8 for
      pointer/string/Int64.  Used to pad field offsets inside records and to
      pick QBE alloc4/alloc8 for stack slots. }
    function AllocAlign: Integer;
    { Same as ByteSize.  Retained for call sites that semantically want
      "storage footprint of a single value" — e.g. static-array element
      stride. }
    function RawSize: Integer;
  end;

  { Typed or untyped pointer descriptor.
    BaseType = nil means untyped 'Pointer'; non-nil means '^BaseType'. }
  TPointerTypeDesc = class(TTypeDesc)
  public
    [Unretained] BaseType: TTypeDesc;  { not owned; nil = untyped Pointer }
  end;

  { Metaclass descriptor — 'class of TFoo'.  The runtime value of any
    metaclass-typed expression is the typeinfo pointer of a class
    descended from BaseClass.  Stored as QBE 'l' (8 bytes). }
  TMetaClassTypeDesc = class(TTypeDesc)
  public
    [Unretained] BaseClass: TTypeDesc;  { not owned; the class type after 'class of' }
  end;

  { Open-array parameter descriptor.
    Carries the element type; the two-register ABI (data ptr + high index)
    is handled entirely in the parser, semantic pass, and codegen. }
  TOpenArrayTypeDesc = class(TTypeDesc)
  public
    [Unretained] ElementType: TTypeDesc;  { not owned }
  end;

  { Dynamic array descriptor: heap-allocated, reference-counted, runtime length.
    Layout: [refcount:4][length:4][element 0][element 1]...
    The variable slot holds a pointer to element 0 (nil = empty/unassigned).
    Element access: data_ptr + I × ElementType.RawSize.
    Length is stored at data_ptr − 4; RefCount at data_ptr − 8. }
  TDynArrayTypeDesc = class(TTypeDesc)
  public
    [Unretained] ElementType: TTypeDesc;  { not owned }
  end;

  { Static array descriptor: fixed-size, stack-allocated, compile-time bounds.
    Element access: base_ptr + (I − LowBound) × ElementType.ByteSize. }
  TStaticArrayTypeDesc = class(TTypeDesc)
  public
    [Unretained] ElementType: TTypeDesc;  { not owned }
    LowBound:    Integer;
    HighBound:   Integer;
  end;

  { Enum type descriptor.  Members are ordered; ordinal values are 0..N-1.
    Stored as QBE 'w' (same as Integer).  Members are NOT registered as bare
    global skConstants; a bare member name resolves through the semantic
    analyser's type-keyed reverse index (see ResolveEnumMember). }
  TEnumTypeDesc = class(TTypeDesc)
  public
    { Owned — ordered member names.  Each member's explicit (or auto-continued)
      ordinal is stored alongside the name in Members.Objects[] as a
      PtrInt-boxed integer, mirroring the AST-level TEnumTypeDef.  This lets
      High/Low fold from the real max/min ordinal rather than assuming a
      contiguous 0-based enum (BUG-20260720-enum-explicit-ordinal-highlow). }
    Members: TStringList;
    constructor Create(const AName: string);
    destructor  Destroy; override;
    { Append a member with its ordinal.  Use this in preference to
      Members.Add (which would box ordinal 0) so explicit ordinals survive. }
    procedure   AddMember(const AMember: string; AOrdinal: Integer);
    { Ordinal stored for the member at position AIndex. }
    function    OrdinalAt(AIndex: Integer): Integer;
    { Ordinal of a member by name, or -1 if not a member.  Returns the stored
      ordinal (which may differ from the positional index for an
      explicit-ordinal enum), NOT the index. }
    function    OrdinalOf(const AMember: string): Integer;
    { Max / min stored ordinal — what High(TE) / Low(TE) must fold to.  Both
      return 0 for an empty enum (never occurs — every enum has >= 1 member). }
    function    MaxOrdinal: Integer;
    function    MinOrdinal: Integer;
  end;

  { Set type descriptor.  BaseType is the element type (enum or ordinal such
    as Byte/Word).  BitCount is the number of bits required.  Each member
    ordinal N maps to bit N of the bitmap.  Representation depends on BitCount:
      BitCount <= 32  -> QBE 'w' (32-bit register), bit (1 shl N)
      BitCount <= 64  -> QBE 'l' (64-bit register), bit (1 shl N)
      BitCount  > 64  -> JUMBO: an inline byte-array bitmap of RawByteSize
                          bytes, treated as an aggregate (like a record): bit N
                          lives at byte (N shr 3), mask (1 shl (N and 7)).
                          Operated on via the _Set* RTL helpers, never a single
                          register.  Max 256 members -> 32 bytes. }
  TSetTypeDesc = class(TTypeDesc)
  public
    [Unretained] BaseType: TTypeDesc;  { not owned — enum or ordinal type }
    BitCount: Integer;
    { True when this set is too wide for a single 64-bit register and must use
      the inline byte-array (aggregate) representation + _Set* RTL helpers. }
    function IsJumbo: Boolean;
    { Number of bitmap bytes for the jumbo representation = ceil(BitCount/8).
      Only meaningful when IsJumbo; <= 32 for the 256-member ceiling. }
    function RawByteSize: Integer;
  end;

  { One parameter of a procedural type signature. }
  TProcParamInfo = class
  public
    Name:         string;
    [Unretained] TypeDesc:     TTypeDesc;  { not owned }
    IsVarParam:   Boolean;
    IsConstParam: Boolean;
  end;

  { Procedural (function or procedure) type descriptor.

    Bare procedural pointer: 8-byte slot, holds a function code pointer.
    Used for callback values such as `type T = function: Integer`.

    Method pointer (IsMethodPtr=True): 16-byte slot, holds (Code, Data).
    Layout: Code at offset 0, Data at offset 8.  The variable's QBE name
    refers to the address of the 16-byte block, mirroring how records
    are represented.  A method-pointer call loads both halves and emits
    `call code(l data, args...)`.  Set when the type was declared with
    the 'of object' suffix. }
  TProceduralTypeDesc = class(TTypeDesc)
  public
    Params:      TObjectList;  { owned TProcParamInfo }
    [Unretained] ReturnType:  TTypeDesc;    { not owned; nil = procedure (no return) }
    IsMethodPtr: Boolean;      { True for 'procedure of object' types }
    IsReference: Boolean;      { True for 'reference to' anonymous-method
                                 types — a 16-byte (Code, Env) fat value
                                 whose Data half is an ARC-managed
                                 environment record (nil when capture-free).
                                 Mutually exclusive with IsMethodPtr. }
    constructor Create(const AName: string);
    destructor  Destroy; override;
    { Two procedural types are compatible iff their return types match
      (both nil or both same TTypeDesc), their method-pointer flags
      match, and their parameter lists match pairwise on type and on
      parameter mode (var/const/value).  Parameter names do not
      participate. }
    function    IsCompatibleWith(AOther: TProceduralTypeDesc): Boolean;
    function    SignatureMatches(AOther: TProceduralTypeDesc): Boolean;
  end;

  { Field entry inside a record type descriptor. }
  TFieldInfo = class
  public
    Name:     string;
    [Unretained] TypeDesc: TTypeDesc;  { not owned }
    Offset:   Integer;    { byte offset from record base }
    IsWeak:   Boolean;    { set when the class field was declared [Weak];
                            field cleanup emits _WeakClear for weak fields
                            and field assignment bypasses addref/release. }
    IsUnretained: Boolean; { set when the class field was declared [Unretained];
                             a non-owning reference to an object owned elsewhere.
                             Unlike [Weak] there is NO weak-registry registration
                             and NO auto-nil: field assignment stores the pointer
                             with neither addref nor release, and field cleanup
                             does nothing.  Use only when the referent is
                             guaranteed to outlive this field. }
    Visibility: TMemberVisibility; { access scope; default mvPublic }
    DeclaringUnit: string; { name of the unit that declares the owning type — the
                             privacy boundary for mvPrivate/mvProtected }
    DeclaringType: string; { name of the class/record that DECLARED this field; for
                             an inherited field this is the ancestor, not the
                             subclass that copied it — protected/strict checks walk
                             the descendant chain up to this type }
  end;

  { One entry in a class vtable — tracks slot index and implementing method. }
  TVTableEntry = class
  public
    Slot:       Integer;  { index in vtable }
    MethName:   string;   { unqualified method name }
    ImplName:   string;   { fully-qualified QBE label, e.g. $TDog_Speak }
    IsAbstract: Boolean;  { True = slot has no implementation; codegen emits abort stub }
  end;

  { Property descriptor — one per declared property on a class. }
  TPropertyInfo = class
  public
    Name:           string;
    [Unretained] TypeDesc:       TTypeDesc;   { not owned — resolved by semantic analysis }
    ReadField:      string;      { '' if method-backed read }
    ReadMethod:     string;      { '' if field-backed read }
    WriteField:     string;      { '' if method-backed write or read-only }
    WriteMethod:    string;      { '' if field-backed write or read-only }
    IndexParamName: string;  { '' = non-indexed property }
    [Unretained] IndexTypeDesc: TTypeDesc;  { not owned; non-nil when IndexParamName <> '' }
    IsDefault:      Boolean; { declared with the `default` directive (Obj[I] sugar) }
    IsStatic:       Boolean; { declared `static property` — accessors are static (no Self) }
    Visibility:     TMemberVisibility; { access scope; default mvPublic }
    DeclaringUnit:  string;  { unit that declares the owning type — privacy boundary }
    DeclaringType:  string;  { class/record that DECLARED this property (ancestor for inherited) }
  end;

  { Type descriptor for zero-GUID interface types (Phase 3). }
  TInterfaceTypeDesc = class(TTypeDesc)
  private
    FMethods:     TStringList;  { method names, case-insensitive }
    FReturnTypes: TStringList;  { parallel: return type name, '' = procedure }
    FParamIsVar:  TStringList;  { parallel: comma-separated '1'/'0' per param; '1' = var param }
    FProperties:  TObjectList;  { owned TPropertyInfo — accessors are interface methods }
    [Unretained] FParent:      TInterfaceTypeDesc;  { not owned; nil if no parent }
  public
    constructor Create(const AName: string);
    destructor Destroy; override;
    procedure AddMethod(const AName: string; const AReturnTypeName: string;
                        const AParamIsVar: string = '');
    function  HasMethod(const AName: string): Boolean;
    function  MethodCount: Integer;
    function  MethodName(AIndex: Integer): string;
    function  MethodReturnTypeName(AIndex: Integer): string;
    function  MethodIndex(const AName: string): Integer;
    function  MethodParamIsVar(AMethodIndex: Integer; AParamIndex: Integer): Boolean;
    function  MethodParamVarFlagsStr(AMethodIndex: Integer): string;
    procedure AddProperty(AInfo: TPropertyInfo);
    { Walks the parent chain — a child interface sees inherited properties. }
    function  FindProperty(const AName: string): TPropertyInfo;
    property  Parent: TInterfaceTypeDesc read FParent write FParent;
  end;

  { Extended type descriptor for record types. }
  TRecordTypeDesc = class(TTypeDesc)
  private
    FFields:          TObjectList;  { owned TFieldInfo }
    FKeys:            TStringList;  { sorted, case-insensitive; Objects[] = TFieldInfo (not owned) }
    [Unretained] FParent:          TRecordTypeDesc;   { not owned; nil for root classes }
    FVTable:          TObjectList;  { owned TVTableEntry; nil if no virtual methods }
    FImplements:      TObjectList;  { not owned — TInterfaceTypeDesc references }
    FProperties:      TObjectList;  { owned TPropertyInfo }
    FHasDestroyMethod:      Boolean; { True when the class declares a 'Destroy' method }
    FDestroyResolvedQbeName: string; { Mangled symbol of the no-arg Destroy when this
                                       class declares its own destructor; empty otherwise.
                                       Codegen reads this for ARC field cleanup so the
                                       call target matches the emitted method symbol when
                                       Destroy is overloaded (e.g. 'TFoo_Destroy$'). }
    FMethodSyms:            TDictionary<string, string>; { method name -> emitted symbol.
                                       Generalises FDestroyResolvedQbeName to EVERY
                                       method, because a NON-VIRTUAL method has no
                                       vtable slot and therefore no other place on the
                                       descriptor that records the symbol its body was
                                       emitted under.  Codegen needs exactly that when
                                       naming an itab entry for an interface method a
                                       class inherits from an ancestor -- especially a
                                       cross-unit ancestor, whose AST it cannot see.
                                       Carries the full mangled form (unit prefix,
                                       declaring-class casing, overload '$sig' suffix),
                                       so no call site has to reconstruct it. }
    FHasAbstractMethods:    Boolean; { True when any vtable slot is abstract (no impl) }
    FClassAttributes:       TStringList; { resolved attribute type names e.g. 'ThreadedAttribute' }
    FIsPacked:              Boolean; { True for `packed record` — skip per-field
                                       alignment and tail padding (records only) }
  public
    property IsPacked: Boolean read FIsPacked write FIsPacked;
    constructor Create(const AName: string; AKind: TTypeKind);
    destructor Destroy; override;
    procedure AddField(const AName: string; AType: TTypeDesc);
    function  FindField(const AName: string): TFieldInfo;
    function  PackedSize: Integer;
    function  TotalSize: Integer;
    function  MaxAlign: Integer;
    function  FieldAlign(AType: TTypeDesc): Integer;

    { Vtable management }
    function  HasVTable: Boolean;
    function  VTableCount: Integer;
    function  VTableEntryAt(ASlot: Integer): TVTableEntry;
    { Record / look up the symbol a method's body is emitted under.  Empty
      result means this class does not declare AName (walk to Parent). }
    procedure AddMethodSym(const AName, AQbeName: string);
    function  FindMethodSym(const AName: string): string;
    function  FindVTableSlot(const AMethodName: string): Integer;
    function  AddVTableSlot(const AMethodName, AImplName: string): Integer;
    procedure OverrideVTableSlot(ASlot: Integer; const AImplName: string);
    { Place a method at an explicit slot index, growing the table with
      placeholder entries if necessary.  Used by the cached-unit importer,
      which knows each method's authoritative slot from the .bif rather than
      relying on registration order. }
    procedure SetVTableSlotAt(ASlot: Integer;
                              const AMethodName, AImplName: string);
    procedure CopyVTableFrom(AParent: TRecordTypeDesc);

    { Interface implements tracking }
    procedure AddImplements(AIntf: TInterfaceTypeDesc);
    function  ImplementsCount: Integer;
    function  ImplementsIntfAt(AIndex: Integer): TInterfaceTypeDesc;

    { Property tracking }
    procedure AddProperty(AProp: TPropertyInfo);
    function  FindProperty(const AName: string): TPropertyInfo;
    function  FindIndexedProperty: TPropertyInfo;
    function  FindDefaultProperty: TPropertyInfo;

    { Custom attribute tracking }
    procedure AddClassAttribute(const AName: string);
    function  ClassAttributeCount: Integer;
    function  ClassAttributeAt(AIndex: Integer): string;

    property  Fields:      TObjectList read FFields;
    property  Properties: TObjectList read FProperties;
    property  Parent: TRecordTypeDesc read FParent write FParent;
    property  HasDestroyMethod: Boolean
              read FHasDestroyMethod write FHasDestroyMethod;
    property  DestroyResolvedQbeName: string
              read FDestroyResolvedQbeName write FDestroyResolvedQbeName;
    property  HasAbstractMethods: Boolean
              read FHasAbstractMethods write FHasAbstractMethods;
  end;

  { ------------------------------------------------------------------ }
  {  Symbols                                                            }
  { ------------------------------------------------------------------ }

  TSymbolKind = (
    skVariable,
    skType,
    skProcedure,
    skFunction,
    skParameter,
    skVarParameter,
    skConstant,    { built-in or user-declared constant; ConstValue holds the integer value }
    skModule       { reserved module name — the program/unit's own name or a
                     directly used unit's name (issue #84).  Exists only so
                     TScope.Define rejects same-scope redeclarations; Lookup
                     treats a hit as unresolvable, so the name is reserved
                     but is not a value.  TypeDesc is nil. }
  );

  TParamDesc = class
  public
    Name:     string;
    [Unretained] TypeDesc: TTypeDesc;  { not owned }
    IsConst:  Boolean;
    IsVar:    Boolean;
  end;

  TSymbol = class
  public
    Name:       string;
    Kind:       TSymbolKind;
    [Unretained] TypeDesc:   TTypeDesc;    { not owned; nil for procedures }
    Params:     TObjectList;  { owned TParamDesc; populated for procedures/functions }
    ConstValue:  Int64;       { valid when Kind = skConstant; integer/bool/enum value }
    ConstString: string;      { valid when Kind = skConstant and type is tyString }
    ConstArray:  TStringList; { owned; non-nil for array-typed const; raw element values }
    ConstArrayQbe: string;    { canonical QBE data-label for an array const; mangled
                                to avoid collisions across scopes and with the RTL }
    ConstSetBytes: TStringList; { owned; non-nil for a JUMBO (>64-member) set
                                  const; one decimal byte value per bitmap byte
                                  (RawByteSize entries).  Small sets keep using
                                  ConstValue (the Int64 mask) instead. }
    ConstSetQbe: string;      { canonical, mangled QBE data-label for a jumbo set
                                const's byte blob (mirrors ConstArrayQbe) }
    IsWeak:     Boolean;      { true for variables declared [Weak]; codegen
                                keys off this to emit _WeakAssign instead
                                of the strong addref/release pattern. }
    IsGlobal:   Boolean;      { true for program-level variables; codegen uses
                                QBE data-section storage instead of stack alloc }
    IsClassVar: Boolean;      { true for a STATIC (class-level) variable.  Stored
                                as a single shared global (IsGlobal is also True),
                                under the mangled GlobalEmitName, not as a
                                per-instance field. }
    GlobalEmitName: string;   { when non-empty, the mangled data-label this symbol
                                emits/loads/stores under (e.g. 'TFoo_FInstance').
                                Lets a bare lookup key ('FInstance') and a
                                qualified one ('TFoo.FInstance') resolve to ONE
                                storage slot.  Mirrors ConstArrayQbe for consts.
                                Empty = emit under Name. }
    IsThreadVar: Boolean;     { true for threadvar declarations; codegen emits
                                TLS storage instead of plain global data }
    [Unretained] BlockSite: TObject; { TVarDeclStmt — non-owning; set for a
                                BLOCK-SCOPED var (Phase 4 of the anonymous-
                                methods design): identifies the declaration
                                site whose per-execution environment the
                                variable belongs to when captured.  nil for
                                ordinary symbols. }
    IsOverload:   Boolean;    { true when declared with the 'overload' directive;
                                same-named overload symbols form a NextOverload chain }
    [Unretained] NextOverload: TSymbol;    { not owned — link to next overload in the chain;
                                nil = last (or only) overload }
    [Unretained] Decl:         TObject;    { not owned — TMethodDecl backing this proc/func symbol;
                                nil for non-callable symbols }
    OwningUnit:   string;     { name of the unit that exported this symbol; empty
                                for builtins, program-local symbols, and locals.
                                Populated by uSemanticImport when registering an
                                imported iface, and by AnalyseUnitForExport for
                                symbols owned by the unit being analysed.  Read
                                by per-unit visibility and by unit-prefix
                                mangling on cross-unit references. }
    IsImplPrivate: Boolean;   { true for a symbol declared in the IMPLEMENTATION
                                section of its owning unit.  Such a symbol is
                                visible only inside that unit — never to a used
                                unit (it is not in the unit's interface) — so
                                Lookup suppresses it whenever the viewing unit is
                                not the owner.  Prevents an impl-section class/
                                type from leaking into an unrelated unit through
                                the flat global scope. }
    Visibility: TMemberVisibility; { for a STATIC (class-level) variable: the
                                declared member visibility (private/protected/
                                strict/public).  Default mvPublic.  Read by the
                                qualified-access visibility checks. }
    OwnerTypeName: string;    { for a STATIC (class-level) variable: the class/
                                record that declared it.  Empty for non-members.
                                Lets strict/protected checks resolve the owning
                                type the same way TFieldInfo.DeclaringType does. }
    constructor Create(const AName: string; AKind: TSymbolKind; AType: TTypeDesc);
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Scope                                                              }
  { ------------------------------------------------------------------ }

  TScope = class
  private
    [Weak] FParent: TScope;  { non-owning back-pointer; parent outlives child }
    FSymbols: TObjectList;  { owns all TSymbol in this scope }
    FKeys:    TStringList;  { sorted, case-insensitive; Objects[] = TSymbol (not owned) }
  public
    constructor Create(AParent: TScope);
    destructor Destroy; override;
    property Parent: TScope read FParent;
    { Returns False if name already defined in this scope; caller must free ASymbol. }
    function Define(ASymbol: TSymbol): Boolean;
    function LookupLocal(const AName: string): TSymbol;
    function Lookup(const AName: string): TSymbol;
    { Iteration over symbols defined directly in this scope (no
      parent walk).  Used by the analyser to harvest unit-imported
      symbols into per-unit caches without threading semantic
      references through every Register* helper. }
    function SymbolCount: Integer;
    function SymbolAt(AIdx: Integer): TSymbol;
    { Detach a directly-defined symbol from this scope WITHOUT freeing
      it (FSymbols owns, so Extract not Remove).  Returns the detached
      symbol, or nil if not present.  Caller takes responsibility for
      the object's lifetime — used so a duplicate import can hand the
      flat-scope slot to a later unit while a per-unit cache keeps the
      original alive. }
    function ExtractLocal(const AName: string): TSymbol;
  end;

  { ------------------------------------------------------------------ }
  {  Symbol table                                                       }
  { ------------------------------------------------------------------ }

  { Abstract chain-lookup provider.  TSemanticAnalyser inherits from
    this and overrides LookupViaUsesChain so TSymbolTable can call
    back without depending on uSemantic.  Returns nil when the chain
    has no visible binding for AName. }
  TUsesChainProvider = class
  public
    function LookupViaUsesChain(const AName: string): TSymbol; virtual;
  end;

  TSymbolTable = class
  private
    FScopeStack: TObjectList;   { owned TScope, index 0 = global }
    FAllTypes:   TObjectList;   { owned TTypeDesc }
    FGenerics:   TStringList;   { base name → template object (in FGenericTemplates) }
    { Owns a strong reference to every registered generic template.  The
      template AST nodes are originally owned by their unit's TypeDecls list,
      but FGenerics must outlive any single instantiation; retaining them here
      keeps FGenerics' pointers valid for the symbol table's whole lifetime.
      Without this an early instantiation could see the slot reused (the node
      freed, its memory becoming an unrelated object), so a later lookup of
      the same generic returns a wrong-class object and silently mis-wires the
      instance (no parent, no vtable). }
    FGenericTemplates: TObjectList;
    FGenericRoutines: TStringList; { non-owning: routine name → TMethodDecl
                                     (generic free-routine templates, populated
                                     by AnalyseStandaloneDecl and by
                                     uSemanticImport when registering a unit
                                     interface's generic free routines) }
    { Declaring unit of each FGenerics / FGenericRoutines entry (lockstep
      indices).  Generic-instance symbols are mangled BARE (the BUG-004
      COMDAT model), so one template base name may only ever come from ONE
      unit program-wide — a same-named template in a second unit would
      produce byte-identical instance symbols that the linker silently
      folds.  Register* returns the earlier unit on a cross-unit conflict
      so the caller can diagnose. }
    FGenericDeclUnits: TStringList;
    FGenericRoutineDeclUnits: TStringList;
    FImportedDecls:   TObjectList; { owned TMethodDecl — synthesised by
                                     uSemanticImport when materialising
                                     routines / methods that came in via a
                                     .bif (no source TUnit holds them). }

    { Builtin-type caches: borrowed views into FAllTypes (the owning pool).
      [Unretained] keeps the pool's single reference authoritative; the
      owned +1 a NewType call returns is released by the Unretained-store
      lowering at the assignment site. }
    [Unretained] FTypeInteger:  TTypeDesc;
    [Unretained] FTypeInt64:    TTypeDesc;
    [Unretained] FTypeUInt32:   TTypeDesc;
    [Unretained] FTypeUInt64:   TTypeDesc;
    [Unretained] FTypeSmallInt: TTypeDesc;
    [Unretained] FTypeWord:     TTypeDesc;
    [Unretained] FTypeByte:     TTypeDesc;
    [Unretained] FTypeBoolean: TTypeDesc;
    [Unretained] FTypeString:  TTypeDesc;
    [Unretained] FTypeVoid:    TTypeDesc;
    [Unretained] FTypeNil:     TTypeDesc;
    [Unretained] FTypeDouble:  TTypeDesc;
    [Unretained] FTypeSingle:  TTypeDesc;
    [Unretained] FTypePointer: TPointerTypeDesc;  { untyped Pointer }
    [Unretained] FTypePChar:   TTypeDesc;         { opaque C pointer }

    { Optional hook into uses-chain lookup.  Set by TSemanticAnalyser
      so Lookup() can consult per-unit visibility after exhausting the
      pushed scopes but BEFORE falling back to the global scope.
      Task #44 step 7.

      [Unretained]: the provider is the TSemanticAnalyser that OWNS this
      symbol table (TSemanticAnalyser.FTable).  A strong reference here
      would form an analyser<->table cycle that refcount ARC cannot
      collect, so Semantic.Free() would never run the analyser destructor
      and the whole AST + symbol-table graph (~325 objects) would leak.
      The analyser always outlives the table — its destructor is what
      frees the table — so a non-owning reference is safe. }
    [Unretained] FUsesChainProvider: TUsesChainProvider;

    { Recursion guard.  TSemanticAnalyser.LookupViaUsesChain (which
      sits behind FUsesChainLookup) calls FTable.Lookup itself to
      retrieve the canonical TSymbol — without this flag we'd loop. }
    FBypassUsesChain: Boolean;

    FInCodegen: Boolean;             { True while a backend is emitting code.
                                       Disables the Layer-6 impl-private
                                       suppression in Lookup: that guard exists
                                       only to stop an implementation-section
                                       symbol of unit A leaking into a different
                                       unit B DURING ANALYSIS.  At codegen time a
                                       backend legitimately resolves a unit's own
                                       impl-section classes (to emit their
                                       typeinfo/vtable/_FieldCleanup and the
                                       references to them), but FDefineOwningUnit
                                       can have drifted to a dependency unit
                                       mid-emit, which made the suppression wrongly
                                       fire and silently drop the class's typeinfo
                                       — a dangling symbol the linker binds to
                                       garbage.  Set by the QBE and native
                                       backends around Generate/GenerateUnit. }

    FDefineOwningUnit: string;       { auto-applied to Sym.OwningUnit on Define
                                       when the symbol has no explicit value;
                                       set by AnalyseUnit/AnalyseUnitForExport
                                       so semantic-side Define sites don't
                                       each need to thread the unit name. }

    FDefineImplPrivate: Boolean;     { when True, Define()/DefineGlobal() mark the
                                       symbol IsImplPrivate.  Set by the analyser
                                       around impl-section type/const registration
                                       so those symbols stay unit-private. }

    function GetCurrentScope: TScope;
    function GetScopeDepth: Integer;
    function NewType(AKind: TTypeKind; const AName: string): TTypeDesc;
    procedure RegisterBuiltins;
  public
    constructor Create;
    destructor Destroy; override;

    { Scope management }
    function  PushScope: TScope;
    procedure PopScope;
    property  CurrentScope: TScope read GetCurrentScope;
    property  ScopeDepth: Integer read GetScopeDepth;
    function  GlobalScope: TScope;

    { Symbol management — owns ASymbol on success; caller must free on False }
    function Define(ASymbol: TSymbol): Boolean;
    { Define in global (outermost) scope regardless of current push depth. }
    function DefineGlobal(ASymbol: TSymbol): Boolean;
    { Detach a symbol from the current scope without freeing it (see
      TScope.ExtractLocal).  Returns the detached symbol or nil. }
    function ExtractLocal(const AName: string): TSymbol;
    function Lookup(const AName: string): TSymbol;

    { Auto-OwningUnit context.  When set, Define()/DefineGlobal() will
      populate Sym.OwningUnit from this string if the symbol has no
      explicit value.  Empty string clears the context. }
    property DefineOwningUnit: string read FDefineOwningUnit
                                       write FDefineOwningUnit;

    { Impl-private context.  When True, Define()/DefineGlobal() mark the symbol
      IsImplPrivate so it stays visible only to its owning unit.  Set by the
      analyser around implementation-section type/const registration. }
    property DefineImplPrivate: Boolean read FDefineImplPrivate
                                         write FDefineImplPrivate;

    { Hook into the analyser's uses-chain lookup.  When non-nil,
      Lookup() consults the chain after pushed scopes and before the
      global scope.  Wired by TSemanticAnalyser.  Task #44 step 7. }
    property UsesChainProvider: TUsesChainProvider read FUsesChainProvider
                                                    write FUsesChainProvider;

    { Recursion guard for the chain hook.  TSemanticAnalyser's chain
      walker calls Lookup itself to retrieve the canonical TSymbol;
      flipping this flag for the duration of that call bypasses the
      hook to break recursion. }
    property BypassUsesChain: Boolean read FBypassUsesChain
                                       write FBypassUsesChain;

    { Set by a backend for the duration of code emission; see FInCodegen. }
    property InCodegen: Boolean read FInCodegen write FInCodegen;

    { Type lookup — case-insensitive, returns nil if not found }
    function FindType(const AName: string): TTypeDesc;

    { Creates a new TRecordTypeDesc, registers it in FAllTypes, and returns it.
      Caller must then add fields and register it as a skType symbol. }
    function NewRecordType(const AName: string): TRecordTypeDesc;

    { Creates a new class type descriptor (tyClass, heap-allocated). }
    function NewClassType(const AName: string): TRecordTypeDesc;

    { Creates a new interface type descriptor (tyInterface). }
    function NewInterfaceType(const AName: string): TInterfaceTypeDesc;

    { Creates a typed pointer descriptor '^BaseType'. Registered in FAllTypes. }
    function NewPointerType(const AName: string; ABase: TTypeDesc): TPointerTypeDesc;
    function NewMetaClassType(const AName: string; ABase: TTypeDesc): TMetaClassTypeDesc;
    function NewEnumType(const AName: string): TEnumTypeDesc;
    function NewSetType(const AName: string; ABase: TEnumTypeDesc): TSetTypeDesc;
    function NewOrdinalSetType(const AName: string; ABase: TTypeDesc;
      ABitCount: Integer): TSetTypeDesc;
    function NewProceduralType(const AName: string): TProceduralTypeDesc;

    { Creates an open-array type descriptor for element type AElementType.
      Registered in FAllTypes so the table owns the lifetime. }
    function NewOpenArrayType(AElementType: TTypeDesc): TOpenArrayTypeDesc;

    { Creates a static array type descriptor. Registered in FAllTypes. }
    function NewStaticArrayType(AElementType: TTypeDesc;
      ALow, AHigh: Integer): TStaticArrayTypeDesc;

    { Creates a dynamic array type descriptor. Registered in FAllTypes. }
    function NewDynArrayType(AElementType: TTypeDesc): TDynArrayTypeDesc;

    { Generic template registry — stores TGenericTypeDef as TObject to avoid
      circular unit dependency with uAST. Callers cast the result.
      ADeclUnit is the unit DECLARING the template ('<program>' for a
      program-level declaration).  Returns '' on success, or the name of the
      unit that already registered the same base name — a cross-unit
      collision the caller must report (see FGenericDeclUnits above). }
    function  RegisterGeneric(const AName: string; ATempl: TObject;
                              const ADeclUnit: string): string;
    function  FindGeneric(const AName: string): TObject;
    function  RegisterGenericRoutine(const AName: string; ATempl: TObject;
                                     const ADeclUnit: string): string;
    function  FindGenericRoutine(const AName: string): TObject;
    { Take ownership of a synthesised TMethodDecl produced during
      .bif import.  Lifetime tracks the symbol table; callers do
      not free.  Returns the same pointer for caller convenience. }
    function  OwnImportedDecl(ADecl: TObject): TObject;

    { Convenience type accessors }
    property TypeInteger:  TTypeDesc read FTypeInteger;
    property TypeInt64:    TTypeDesc read FTypeInt64;
    property TypeUInt32:   TTypeDesc read FTypeUInt32;
    property TypeUInt64:   TTypeDesc read FTypeUInt64;
    property TypeSmallInt: TTypeDesc read FTypeSmallInt;
    property TypeWord:     TTypeDesc read FTypeWord;
    property TypeByte:    TTypeDesc read FTypeByte;
    property TypeBoolean: TTypeDesc read FTypeBoolean;
    property TypeString:  TTypeDesc read FTypeString;
    property TypeVoid:    TTypeDesc    read FTypeVoid;
    property TypeNil:     TTypeDesc    read FTypeNil;
    property TypePointer: TPointerTypeDesc read FTypePointer;
    property TypePChar:   TTypeDesc        read FTypePChar;
    property TypeDouble:  TTypeDesc        read FTypeDouble;
    property TypeSingle:  TTypeDesc        read FTypeSingle;
  end;

{ Foundational units whose exports stay as literal global symbols (no
  unit prefix) so codegen-emitted hardcoded references like
  @_BlaiseGetMem, @TObject_Destroy, @_StartUp, @_StringRelease keep
  resolving.  The empty unit name is also unmangled — that's
  program-level code or builtins. }
function IsUnmangledUnit(const AUnitName: string): Boolean;

{ Returns 'UnitName_' (dots collapse to underscores) for mangled
  units, '' for unmangled ones.  The same prefix is applied at both
  the symbol-defining site (codegen of the exporting unit) and the
  symbol-using site (call/reference in another unit), so they always
  agree on the QBE global name. }
function MangleUnitPrefix(const AUnitName: string): string;

{ Shared diagnostic text for a cross-unit generic-template collision, so the
  source-analysis path (uSemantic) and the cached-.bif import path
  (uSemanticImport) report identically.  AKind is 'Generic type' or
  'Generic routine'. }
function GenericCollisionMsg(const AKind, AName, APrevUnit, ANewUnit: string): string;

const
  { Sentinel owning-unit value meaning "this global's emit name is ALREADY a
    fully-mangled symbol — codegen must add no further unit prefix".  Used for
    static class/record vars, whose label (Unit_Class_Field) is class-qualified
    and complete; the module-var prefixing must not double-apply.  The leading
    control byte can never collide with a real unit name. }
  PreMangledGlobalOwner = #1'premangled';

implementation

uses
  blaise.codegen.target;

{ ------------------------------------------------------------------ }
{ TUsesChainProvider                                                  }
{ ------------------------------------------------------------------ }

function TUsesChainProvider.LookupViaUsesChain(const AName: string): TSymbol;
begin
  { Base impl never matches; descendants override.  Provided so a
    standalone TSymbolTable (no analyser attached) still behaves
    sensibly if a provider isn't wired. }
  Result := nil;
end;

{ ------------------------------------------------------------------ }
{ TTypeDesc                                                           }
{ ------------------------------------------------------------------ }

function TTypeDesc.IsNumeric: Boolean;
begin
  Result := Kind in [tyInteger, tyInt64, tyUInt32, tyUInt64, tySmallInt, tyWord, tyByte, tyEnum, tyDouble, tySingle];
end;

function TTypeDesc.IsFloat: Boolean;
begin
  Result := Kind in [tyDouble, tySingle];
end;

function TTypeDesc.IsString: Boolean;
begin
  Result := Kind = tyString;
end;

function TTypeDesc.IsArrayIndex: Boolean;
begin
  Result := Kind in [tyInteger, tyInt64, tyUInt32, tyUInt64, tySmallInt,
                     tyWord, tyByte, tyBoolean, tyEnum];
end;

function TTypeDesc.IsOrdinal: Boolean;
begin
  Result := Kind in [tyInteger, tyInt64, tyUInt32, tyUInt64, tySmallInt, tyWord, tyByte, tyBoolean, tyEnum];
end;

function TTypeDesc.IsRecord: Boolean;
begin
  Result := Kind = tyRecord;
end;

function TSetTypeDesc.IsJumbo: Boolean;
begin
  Result := BitCount > 64;
end;

function TSetTypeDesc.RawByteSize: Integer;
begin
  Result := (BitCount + 7) div 8;
end;

function TTypeDesc.RawSize: Integer;
begin
  case Kind of
    tyByte, tyBoolean: Result := 1;
    tySmallInt, tyWord: Result := 2;
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyInt64, tyUInt64, tyString, tyClass, tyPointer, tyNil, tyDouble: Result := 8;
    tySingle: Result := 4;
    tyRecord: Result := TRecordTypeDesc(Self).TotalSize();
    tySet:
      if TSetTypeDesc(Self).BitCount <= 32 then Result := 4
      else if TSetTypeDesc(Self).BitCount <= 64 then Result := 8
      else Result := (TSetTypeDesc(Self).RawByteSize() + 7) and (not 7);
    tyStaticArray:
      Result := (TStaticArrayTypeDesc(Self).HighBound -
                 TStaticArrayTypeDesc(Self).LowBound + 1) *
                 TStaticArrayTypeDesc(Self).ElementType.RawSize();
    tyProcedural:
      if TProceduralTypeDesc(Self).IsMethodPtr or
         TProceduralTypeDesc(Self).IsReference then Result := 16
      else Result := 8;
    tyInterface: Result := 16;  { fat pointer: obj@+0, itab@+8 }
  else
    Result := 8;
  end;
end;

function TTypeDesc.ByteSize: Integer;
begin
  case Kind of
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyInt64, tyUInt64:   Result := 8;
    tySmallInt, tyWord:  Result := 2;
    tyByte, tyBoolean:   Result := 1;  { true byte; stack slots are alloc4-padded by codegen }
    tyString:            Result := 8;  { pointer size on 64-bit }
    tyRecord:            Result := TRecordTypeDesc(Self).TotalSize();
    tyNil:               Result := 8;
    tyDouble:            Result := 8;
    tySingle:            Result := 4;
    tySet:
      if TSetTypeDesc(Self).BitCount <= 32 then Result := 4
      else if TSetTypeDesc(Self).BitCount <= 64 then Result := 8
      else Result := (TSetTypeDesc(Self).RawByteSize() + 7) and (not 7);
    tyStaticArray:
      Result := (TStaticArrayTypeDesc(Self).HighBound -
                 TStaticArrayTypeDesc(Self).LowBound + 1) *
                 TStaticArrayTypeDesc(Self).ElementType.RawSize();
    tyProcedural:
      if TProceduralTypeDesc(Self).IsMethodPtr or
         TProceduralTypeDesc(Self).IsReference then Result := 16
      else Result := 8;
    tyInterface: Result := 16;  { fat pointer: obj@+0, itab@+8 }
  else
    Result := 8;
  end;
end;

function TTypeDesc.AllocAlign: Integer;
begin
  case Kind of
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyByte, tyBoolean:   Result := 1;  { natural alignment }
    tySmallInt, tyWord:  Result := 2;
    tySingle:            Result := 4;
    tyInt64, tyUInt64, tyString:   Result := 8;
    tyRecord:            Result := TRecordTypeDesc(Self).MaxAlign();
    { Sets: 4-byte alignment for the 32-bit register form, else 8 (the 64-bit
      register form and the jumbo byte-array, which we keep 8-aligned). }
    tySet: if TSetTypeDesc(Self).BitCount <= 32 then Result := 4 else Result := 8;
    tyStaticArray: Result := TStaticArrayTypeDesc(Self).ElementType.AllocAlign();
  else
    Result := 8;
  end;
end;

{ ------------------------------------------------------------------ }
{ TRecordTypeDesc                                                     }
{ ------------------------------------------------------------------ }

constructor TRecordTypeDesc.Create(const AName: string; AKind: TTypeKind);
begin
  inherited Create();
  Kind        := AKind;
  Name        := AName;
  FFields     := TObjectList.Create(True);
  FKeys       := TStringList.Create();
  FKeys.Sorted        := True;
  FKeys.CaseSensitive := False;
  FKeys.Duplicates    := dupIgnore;
  FVTable     := nil;  { allocated on first use }
  FImplements := TObjectList.Create(False);  { not owned }
  FProperties := TObjectList.Create(True);   { owned TPropertyInfo }
  FClassAttributes := TStringList.Create();
  FMethodSyms := TDictionary<string, string>.Create();
end;

destructor TRecordTypeDesc.Destroy;
begin
  FMethodSyms.Free();
  FClassAttributes.Free();
  FProperties.Free();
  FImplements.Free();
  FKeys.Free();
  FFields.Free();
  FVTable.Free();
  inherited Destroy();
end;

{ Returns the alignment required for AType when laid out inside this record.
  Normally that is AType.AllocAlign.  For a `packed record` the alignment
  drops to 1 — except for ARC-managed fields (string / class / interface /
  dynamic array), which must remain at their natural alignment because the
  runtime helpers (`_StringRelease`, `_ClassRelease`, etc.) perform 64-bit
  loads through the field pointer. }
function TRecordTypeDesc.FieldAlign(AType: TTypeDesc): Integer;
begin
  Result := AType.AllocAlign();
  if not FIsPacked then Exit;
  case AType.Kind of
    tyString, tyClass, tyInterface, tyDynArray: { keep natural alignment } ;
  else
    Result := 1;
  end;
end;

{ Cumulative byte position immediately after the last field (or after the
  vptr if no fields have been added yet).  Excludes the record's tail
  padding — that is only applied in TotalSize. }
function TRecordTypeDesc.PackedSize: Integer;
var
  I, A: Integer;
  FT:   TTypeDesc;
begin
  if HasVTable() then
    Result := 8
  else
    Result := 0;
  for I := 0 to FFields.Count - 1 do
  begin
    FT := TFieldInfo(FFields.Items[I]).TypeDesc;
    A  := FieldAlign(FT);
    if (A > 1) and (Result mod A <> 0) then
      Inc(Result, A - Result mod A);
    Inc(Result, FT.ByteSize());
  end;
end;

procedure TRecordTypeDesc.AddField(const AName: string; AType: TTypeDesc);
var
  Info:   TFieldInfo;
  Offset: Integer;
  A:      Integer;
begin
  Offset := PackedSize();
  A      := FieldAlign(AType);
  if (A > 1) and (Offset mod A <> 0) then
    Offset := Offset + (A - Offset mod A);
  Info          := TFieldInfo.Create();
  Info.Name     := AName;
  Info.TypeDesc := AType;
  Info.Offset   := Offset;
  FFields.Add(Info);
  FKeys.AddObject(AName, Info);
end;

function TRecordTypeDesc.FindField(const AName: string): TFieldInfo;
var
  Idx: Integer;
begin
  if FKeys.Find(AName, Idx) then
    Result := TFieldInfo(FKeys.Objects[Idx])
  else
    Result := nil;
end;

function TRecordTypeDesc.TotalSize: Integer;
var
  Algn: Integer;
begin
  Result := PackedSize();
  { Tail-pad records up to their own alignment so that arrays of records
    and back-to-back fields stay naturally aligned.  Class instances are
    heap-allocated singletons (never directly in arrays — only references
    to them are), so we leave their size unpadded to match FPC/Delphi
    InstanceSize semantics.  `packed record` similarly suppresses tail
    padding. }
  if Kind = tyClass then Exit;
  if FIsPacked then Exit;
  Algn := MaxAlign();
  if (Algn > 1) and (Result mod Algn <> 0) then
    Inc(Result, Algn - Result mod Algn);
end;

function TRecordTypeDesc.MaxAlign: Integer;
var
  I, A: Integer;
  FT:   TTypeDesc;
begin
  Result := 1;
  if HasVTable() then
    Result := 8;  { vptr requires 8-byte alignment }
  for I := 0 to FFields.Count - 1 do
  begin
    FT := TFieldInfo(FFields.Items[I]).TypeDesc;
    if FIsPacked then
      A := FieldAlign(FT)        { ARC fields keep natural align; PODs become 1 }
    else
      A := FT.AllocAlign();
    if A > Result then
      Result := A;
  end;
end;

function TRecordTypeDesc.HasVTable: Boolean;
begin
  Result := (FVTable <> nil) and (FVTable.Count > 0);
end;

function TRecordTypeDesc.VTableCount: Integer;
begin
  if FVTable = nil then
    Result := 0
  else
    Result := FVTable.Count;
end;

function TRecordTypeDesc.VTableEntryAt(ASlot: Integer): TVTableEntry;
begin
  if (FVTable = nil) or (ASlot < 0) or (ASlot >= FVTable.Count) then
    Result := nil
  else
    Result := TVTableEntry(FVTable.Items[ASlot]);
end;

function TRecordTypeDesc.FindVTableSlot(const AMethodName: string): Integer;
var
  I: Integer;
  E: TVTableEntry;
begin
  Result := -1;
  if FVTable = nil then Exit;
  for I := 0 to FVTable.Count - 1 do
  begin
    E := TVTableEntry(FVTable.Items[I]);
    if SameText(E.MethName, AMethodName) then
    begin
      Exit(I);
    end;
  end;
end;

function TRecordTypeDesc.AddVTableSlot(const AMethodName, AImplName: string): Integer;
var
  E: TVTableEntry;
begin
  if FVTable = nil then
    FVTable := TObjectList.Create(True);
  E            := TVTableEntry.Create();
  E.Slot       := FVTable.Count;
  E.MethName := AMethodName;
  E.ImplName   := AImplName;
  FVTable.Add(E);
  Result := E.Slot;
end;

procedure TRecordTypeDesc.OverrideVTableSlot(ASlot: Integer; const AImplName: string);
begin
  if (FVTable <> nil) and (ASlot >= 0) and (ASlot < FVTable.Count) then
    TVTableEntry(FVTable.Items[ASlot]).ImplName := AImplName;
end;

procedure TRecordTypeDesc.AddImplements(AIntf: TInterfaceTypeDesc);
begin
  FImplements.Add(AIntf);
end;

function TRecordTypeDesc.ImplementsCount: Integer;
begin
  Result := FImplements.Count;
end;

function TRecordTypeDesc.ImplementsIntfAt(AIndex: Integer): TInterfaceTypeDesc;
begin
  Result := TInterfaceTypeDesc(FImplements.Items[AIndex]);
end;

procedure TRecordTypeDesc.SetVTableSlotAt(ASlot: Integer;
  const AMethodName, AImplName: string);
var
  E: TVTableEntry;
begin
  if ASlot < 0 then Exit;
  if FVTable = nil then
    FVTable := TObjectList.Create(True);
  { Grow with placeholder slots so ASlot is a valid index.  Placeholders
    carry an empty MethName so FindVTableSlot never matches them. }
  while FVTable.Count <= ASlot do
  begin
    E      := TVTableEntry.Create();
    E.Slot := FVTable.Count;
    E.MethName := '';
    E.ImplName := '';
    FVTable.Add(E);
  end;
  E := TVTableEntry(FVTable.Items[ASlot]);
  E.MethName := AMethodName;
  E.ImplName := AImplName;
end;

procedure TRecordTypeDesc.AddMethodSym(const AName, AQbeName: string);
begin
  if (AName = '') or (AQbeName = '') then Exit;
  { SetItem, not Add: the semantic pass may revisit a method, and the later
    value is the resolved one.  Keys are LOWER-CASED on the way in and out --
    Pascal identifiers are case-insensitive, but TDictionary hashes the exact
    bytes, so an interface declaring `Id` must still find a class that spells
    it `ID`. }
  FMethodSyms.SetItem(LowerCase(AName), AQbeName);
end;

{ Empty means "not declared here" -- the caller walks to Parent.  Deliberately
  NOT recursive: the caller needs to know WHICH class in the chain declared the
  method, and a recursive lookup would hide that. }
function TRecordTypeDesc.FindMethodSym(const AName: string): string;
begin
  if not FMethodSyms.TryGetValue(LowerCase(AName), Result) then
    Result := '';
end;

procedure TRecordTypeDesc.CopyVTableFrom(AParent: TRecordTypeDesc);
var
  I: Integer;
  Src, Dst: TVTableEntry;
begin
  if (AParent = nil) or (AParent.VTableCount() = 0) then Exit;
  if FVTable = nil then
    FVTable := TObjectList.Create(True);
  for I := 0 to AParent.VTableCount() - 1 do
  begin
    Src      := AParent.VTableEntryAt(I);
    Dst      := TVTableEntry.Create();
    Dst.Slot       := Src.Slot;
    Dst.MethName   := Src.MethName;
    Dst.ImplName   := Src.ImplName;
    Dst.IsAbstract := Src.IsAbstract;
    FVTable.Add(Dst);
  end;
end;

{ ------------------------------------------------------------------ }
{ TInterfaceTypeDesc                                                  }
{ ------------------------------------------------------------------ }

procedure TRecordTypeDesc.AddProperty(AProp: TPropertyInfo);
begin
  FProperties.Add(AProp);
end;

function TRecordTypeDesc.FindProperty(const AName: string): TPropertyInfo;
var
  I:    Integer;
  Walk: TRecordTypeDesc;
begin
  Walk := Self;
  while Walk <> nil do
  begin
    for I := 0 to Walk.FProperties.Count - 1 do
      if SameText(TPropertyInfo(Walk.FProperties.Items[I]).Name, AName) then
      begin
        Exit(TPropertyInfo(Walk.FProperties.Items[I]));
      end;
    Walk := Walk.Parent;
  end;
  Result := nil;
end;

function TRecordTypeDesc.FindIndexedProperty: TPropertyInfo;
var
  I:    Integer;
  P:    TPropertyInfo;
  Walk: TRecordTypeDesc;
begin
  Walk := Self;
  while Walk <> nil do
  begin
    for I := 0 to Walk.FProperties.Count - 1 do
    begin
      P := TPropertyInfo(Walk.FProperties.Items[I]);
      if (P.IndexParamName <> '') and (P.ReadMethod <> '') then
      begin
        Exit(P);
      end;
    end;
    Walk := Walk.Parent;
  end;
  Result := nil;
end;

function TRecordTypeDesc.FindDefaultProperty: TPropertyInfo;
{ Returns the property marked `default` (Obj[I] sugar), walking the inheritance
  chain; nil if the class has no default property. }
var
  I:    Integer;
  P:    TPropertyInfo;
  Walk: TRecordTypeDesc;
begin
  Walk := Self;
  while Walk <> nil do
  begin
    for I := 0 to Walk.FProperties.Count - 1 do
    begin
      P := TPropertyInfo(Walk.FProperties.Items[I]);
      if P.IsDefault then Exit(P);
    end;
    Walk := Walk.Parent;
  end;
  Result := nil;
end;

procedure TRecordTypeDesc.AddClassAttribute(const AName: string);
begin
  FClassAttributes.Add(AName);
end;

function TRecordTypeDesc.ClassAttributeCount: Integer;
begin
  Result := FClassAttributes.Count;
end;

function TRecordTypeDesc.ClassAttributeAt(AIndex: Integer): string;
begin
  Result := FClassAttributes.Strings[AIndex];
end;

constructor TInterfaceTypeDesc.Create(const AName: string);
begin
  inherited Create();
  Kind         := tyInterface;
  Name         := AName;
  FMethods     := TStringList.Create();
  FMethods.CaseSensitive := False;
  FReturnTypes := TStringList.Create();
  FParamIsVar  := TStringList.Create();
  FProperties  := TObjectList.Create(True);
  FParent      := nil;
end;

destructor TInterfaceTypeDesc.Destroy;
begin
  FProperties.Free();
  FParamIsVar.Free();
  FReturnTypes.Free();
  FMethods.Free();
  inherited Destroy();
end;

procedure TInterfaceTypeDesc.AddProperty(AInfo: TPropertyInfo);
begin
  FProperties.Add(AInfo);
end;

function TInterfaceTypeDesc.FindProperty(const AName: string): TPropertyInfo;
var
  I: Integer;
begin
  for I := 0 to FProperties.Count - 1 do
  begin
    Result := TPropertyInfo(FProperties.Items[I]);
    if SameText(Result.Name, AName) then
      Exit;
  end;
  if FParent <> nil then
    Exit(FParent.FindProperty(AName));
  Result := nil;
end;

procedure TInterfaceTypeDesc.AddMethod(const AName: string;
  const AReturnTypeName: string; const AParamIsVar: string);
begin
  FMethods.Add(AName);
  FReturnTypes.Add(AReturnTypeName);
  FParamIsVar.Add(AParamIsVar);
end;

function TInterfaceTypeDesc.HasMethod(const AName: string): Boolean;
begin
  Result := FMethods.IndexOf(AName) >= 0;
end;

function TInterfaceTypeDesc.MethodCount: Integer;
begin
  Result := FMethods.Count;
end;

function TInterfaceTypeDesc.MethodName(AIndex: Integer): string;
begin
  Result := FMethods.Strings[AIndex];
end;

function TInterfaceTypeDesc.MethodReturnTypeName(AIndex: Integer): string;
begin
  Result := FReturnTypes.Strings[AIndex];
end;

function TInterfaceTypeDesc.MethodIndex(const AName: string): Integer;
begin
  Result := FMethods.IndexOf(AName);
end;

function TInterfaceTypeDesc.MethodParamIsVar(AMethodIndex: Integer;
  AParamIndex: Integer): Boolean;
var
  Flags:  string;
  Idx:    Integer;
  CurPar: Integer;
begin
  Result := False;
  if (AMethodIndex < 0) or (AMethodIndex >= FParamIsVar.Count) then Exit;
  Flags := FParamIsVar.Strings[AMethodIndex];
  if Flags = '' then Exit;
  { Walk through comma-separated '0'/'1' flags to find AParamIndex.
    Blaise strings are 0-based — starting at index 1 skipped the first
    parameter's flag entirely (var/out at position 0 was never seen). }
  CurPar := 0;
  Idx    := 0;
  while Idx < Length(Flags) do
  begin
    if Flags[Idx] = ',' then
      CurPar := CurPar + 1
    else if CurPar = AParamIndex then
    begin
      Exit(Flags[Idx] = '1');
    end;
    Idx := Idx + 1;
  end;
end;

function TInterfaceTypeDesc.MethodParamVarFlagsStr(AMethodIndex: Integer): string;
begin
  if (AMethodIndex >= 0) and (AMethodIndex < FParamIsVar.Count) then
    Result := FParamIsVar.Strings[AMethodIndex]
  else
    Result := '';
end;

{ ------------------------------------------------------------------ }
{ TSymbol                                                             }
{ ------------------------------------------------------------------ }

constructor TSymbol.Create(const AName: string; AKind: TSymbolKind; AType: TTypeDesc);
begin
  inherited Create();
  Name     := AName;
  Kind     := AKind;
  TypeDesc := AType;
  Params   := TObjectList.Create(True);
  IsWeak   := False;
end;

destructor TSymbol.Destroy;
begin
  { Params and ConstArray are owned class fields — released by ARC field
    cleanup. }
  inherited Destroy();
end;

{ ------------------------------------------------------------------ }
{ TScope                                                              }
{ ------------------------------------------------------------------ }

constructor TScope.Create(AParent: TScope);
begin
  inherited Create();
  FParent  := AParent;
  FSymbols := TObjectList.Create(True);
  FKeys    := TStringList.Create();
  FKeys.Sorted        := True;
  FKeys.CaseSensitive := False;
  FKeys.Duplicates    := dupIgnore;  { we check manually before inserting }
end;

destructor TScope.Destroy;
begin
  { FKeys and FSymbols are owned class fields — ARC field cleanup releases
    them automatically.  Swift-style: destructors handle side-effects only,
    not the release of owned storage. }
  inherited Destroy();
end;

function TScope.Define(ASymbol: TSymbol): Boolean;
var
  Idx: Integer;
  Existing, Tail: TSymbol;
begin
  if FKeys.Find(ASymbol.Name, Idx) then
  begin
    Existing := TSymbol(FKeys.Objects[Idx]);
    { Overload chaining: both old and new must be overload-marked
      procedures or functions.  Mixing overload + non-overload is a
      duplicate-identifier error. }
    if ASymbol.IsOverload and Existing.IsOverload and
       (ASymbol.Kind in [skProcedure, skFunction]) and
       (Existing.Kind in [skProcedure, skFunction]) then
    begin
      Tail := Existing;
      while Tail.NextOverload <> nil do
        Tail := Tail.NextOverload;
      Tail.NextOverload := ASymbol;
      FSymbols.Add(ASymbol);  { take ownership; lookup walks the chain via Existing }
      Exit(True);
    end;
    Exit(False);
  end;
  FSymbols.Add(ASymbol);
  { Store the TSymbol pointer directly in the string list's Objects slot. }
  FKeys.AddObject(ASymbol.Name, ASymbol);
  Result := True;
end;

function TScope.ExtractLocal(const AName: string): TSymbol;
var
  Idx: Integer;
begin
  Result := nil;
  if not FKeys.Find(AName, Idx) then Exit;
  Result := TSymbol(FKeys.Objects[Idx]);
  FKeys.Delete(Idx);              { free the name }
  FSymbols.Extract(Result);       { detach without freeing }
end;

function TScope.LookupLocal(const AName: string): TSymbol;
var
  Idx: Integer;
begin
  if FKeys.Find(AName, Idx) then
    Result := TSymbol(FKeys.Objects[Idx])
  else
    Result := nil;
end;

function TScope.Lookup(const AName: string): TSymbol;
var
  S: TScope;
begin
  S := Self;
  while S <> nil do
  begin
    Result := S.LookupLocal(AName);
    if Result <> nil then
      Exit;
    S := S.FParent;
  end;
  Result := nil;
end;

function TScope.SymbolCount: Integer;
begin
  Result := FSymbols.Count;
end;

function TScope.SymbolAt(AIdx: Integer): TSymbol;
begin
  Result := TSymbol(FSymbols.Items[AIdx]);
end;

{ ------------------------------------------------------------------ }
{ TEnumTypeDesc                                                       }
{ ------------------------------------------------------------------ }

constructor TEnumTypeDesc.Create(const AName: string);
begin
  inherited Create();
  Kind    := tyEnum;
  Name    := AName;
  Members := TStringList.Create();
end;

destructor TEnumTypeDesc.Destroy;
begin
  Members.Free();
  inherited Destroy();
end;

procedure TEnumTypeDesc.AddMember(const AMember: string; AOrdinal: Integer);
begin
  Members.AddObject(AMember, TObject(Pointer(PtrUInt(AOrdinal))));
end;

function TEnumTypeDesc.OrdinalAt(AIndex: Integer): Integer;
begin
  Result := Integer(PtrUInt(Pointer(Members.Objects[AIndex])));
end;

function TEnumTypeDesc.OrdinalOf(const AMember: string): Integer;
var
  I: Integer;
begin
  for I := 0 to Members.Count - 1 do
    if SameText(Members.Strings[I], AMember) then
    begin
      Exit(Self.OrdinalAt(I));
    end;
  Result := -1;
end;

function TEnumTypeDesc.MaxOrdinal: Integer;
var
  I, V: Integer;
begin
  if Members.Count = 0 then
    Exit(0);
  Result := Self.OrdinalAt(0);
  for I := 1 to Members.Count - 1 do
  begin
    V := Self.OrdinalAt(I);
    if V > Result then
      Result := V;
  end;
end;

function TEnumTypeDesc.MinOrdinal: Integer;
var
  I, V: Integer;
begin
  if Members.Count = 0 then
    Exit(0);
  Result := Self.OrdinalAt(0);
  for I := 1 to Members.Count - 1 do
  begin
    V := Self.OrdinalAt(I);
    if V < Result then
      Result := V;
  end;
end;

constructor TProceduralTypeDesc.Create(const AName: string);
begin
  inherited Create();
  Kind       := tyProcedural;
  Name       := AName;
  Params     := TObjectList.Create(True);
  ReturnType := nil;
end;

destructor TProceduralTypeDesc.Destroy;
begin
  Params.Free();
  inherited Destroy();
end;

function TProceduralTypeDesc.IsCompatibleWith(AOther: TProceduralTypeDesc): Boolean;
var
  I: Integer;
  PA, PB: TProcParamInfo;
begin
  Result := False;
  if AOther = nil then Exit;
  if IsMethodPtr <> AOther.IsMethodPtr then Exit;
  if IsReference <> AOther.IsReference then Exit;
  if (ReturnType = nil) <> (AOther.ReturnType = nil) then Exit;
  if (ReturnType <> nil) and (ReturnType <> AOther.ReturnType) then Exit;
  if Params.Count <> AOther.Params.Count then Exit;
  for I := 0 to Params.Count - 1 do
  begin
    PA := TProcParamInfo(Params.Items[I]);
    PB := TProcParamInfo(AOther.Params.Items[I]);
    if PA.TypeDesc <> PB.TypeDesc then
    begin
      { Allow structural pointer equivalence: PSuite and ^TSuite are the same
        type conceptually — both are TPointerTypeDesc with the same BaseType. }
      if (PA.TypeDesc = nil) or (PB.TypeDesc = nil) then Exit;
      if (PA.TypeDesc.Kind <> tyPointer) or (PB.TypeDesc.Kind <> tyPointer) then Exit;
      if TPointerTypeDesc(PA.TypeDesc).BaseType <>
         TPointerTypeDesc(PB.TypeDesc).BaseType then Exit;
    end;
    if PA.IsVarParam <> PB.IsVarParam then Exit;
    if PA.IsConstParam <> PB.IsConstParam then Exit;
  end;
  Result := True;
end;

function TProceduralTypeDesc.SignatureMatches(AOther: TProceduralTypeDesc): Boolean;
{ Flag-agnostic signature comparison: params and return type must match,
  but IsMethodPtr/IsReference may differ.  Used by the method-pointer →
  'reference to' coercion (docs/anonymous-methods-design.adoc, Conversions):
  a method pointer becomes a closure whose Env is the strong-retained
  receiver, so only the CALLABLE shape has to agree. }
var
  I: Integer;
  PA, PB: TProcParamInfo;
begin
  Result := False;
  if AOther = nil then Exit;
  if (ReturnType = nil) <> (AOther.ReturnType = nil) then Exit;
  if (ReturnType <> nil) and (ReturnType <> AOther.ReturnType) then Exit;
  if Params.Count <> AOther.Params.Count then Exit;
  for I := 0 to Params.Count - 1 do
  begin
    PA := TProcParamInfo(Params.Items[I]);
    PB := TProcParamInfo(AOther.Params.Items[I]);
    if PA.TypeDesc <> PB.TypeDesc then
    begin
      if (PA.TypeDesc = nil) or (PB.TypeDesc = nil) then Exit;
      if (PA.TypeDesc.Kind <> tyPointer) or (PB.TypeDesc.Kind <> tyPointer) then Exit;
      if TPointerTypeDesc(PA.TypeDesc).BaseType <>
         TPointerTypeDesc(PB.TypeDesc).BaseType then Exit;
    end;
    if PA.IsVarParam <> PB.IsVarParam then Exit;
    if PA.IsConstParam <> PB.IsConstParam then Exit;
  end;
  Result := True;
end;

{ ------------------------------------------------------------------ }
{ TSymbolTable                                                        }
{ ------------------------------------------------------------------ }

constructor TSymbolTable.Create;
begin
  inherited Create();
  FScopeStack := TObjectList.Create(True);
  FAllTypes   := TObjectList.Create(True);
  FGenerics   := TStringList.Create();
  FGenerics.CaseSensitive := True;
  { Owns (retains) registered generic templates so FGenerics' references stay
    valid even after the originating AST is torn down. }
  FGenericTemplates := TObjectList.Create(True);
  FGenericDeclUnits := TStringList.Create();
  FGenericRoutines := TStringList.Create();
  FGenericRoutines.CaseSensitive := False;
  FGenericRoutineDeclUnits := TStringList.Create();
  FImportedDecls   := TObjectList.Create(True);
  { Global scope — parent = nil }
  FScopeStack.Add(TScope.Create(nil));
  RegisterBuiltins();
end;

destructor TSymbolTable.Destroy;
begin
  FImportedDecls.Free();
  FGenericRoutines.Free();
  { FGenerics, FGenericTemplates, FScopeStack, FAllTypes are owned class fields — released by
    ARC field cleanup. }
  inherited Destroy();
end;

function TSymbolTable.NewType(AKind: TTypeKind; const AName: string): TTypeDesc;
begin
  Result      := TTypeDesc.Create();
  Result.Kind := AKind;
  Result.Name := AName;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewRecordType(const AName: string): TRecordTypeDesc;
begin
  Result := TRecordTypeDesc.Create(AName, tyRecord);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewClassType(const AName: string): TRecordTypeDesc;
begin
  Result := TRecordTypeDesc.Create(AName, tyClass);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewInterfaceType(const AName: string): TInterfaceTypeDesc;
begin
  Result := TInterfaceTypeDesc.Create(AName);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewPointerType(const AName: string; ABase: TTypeDesc): TPointerTypeDesc;
begin
  Result          := TPointerTypeDesc.Create();
  Result.Kind     := tyPointer;
  Result.Name     := AName;
  Result.BaseType := ABase;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewMetaClassType(const AName: string; ABase: TTypeDesc): TMetaClassTypeDesc;
begin
  Result           := TMetaClassTypeDesc.Create();
  Result.Kind      := tyMetaClass;
  Result.Name      := AName;
  Result.BaseClass := ABase;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewEnumType(const AName: string): TEnumTypeDesc;
begin
  Result := TEnumTypeDesc.Create(AName);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewSetType(const AName: string; ABase: TEnumTypeDesc): TSetTypeDesc;
begin
  Result          := TSetTypeDesc.Create();
  Result.Kind     := tySet;
  Result.Name     := AName;
  Result.BaseType := ABase;
  Result.BitCount := ABase.Members.Count;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewOrdinalSetType(const AName: string; ABase: TTypeDesc;
  ABitCount: Integer): TSetTypeDesc;
begin
  Result          := TSetTypeDesc.Create();
  Result.Kind     := tySet;
  Result.Name     := AName;
  Result.BaseType := ABase;
  Result.BitCount := ABitCount;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewProceduralType(const AName: string): TProceduralTypeDesc;
begin
  Result := TProceduralTypeDesc.Create(AName);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewOpenArrayType(AElementType: TTypeDesc): TOpenArrayTypeDesc;
begin
  Result             := TOpenArrayTypeDesc.Create();
  Result.Kind        := tyOpenArray;
  Result.Name        := 'array of ' + AElementType.Name;
  Result.ElementType := AElementType;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewStaticArrayType(AElementType: TTypeDesc;
  ALow, AHigh: Integer): TStaticArrayTypeDesc;
begin
  Result             := TStaticArrayTypeDesc.Create();
  Result.Kind        := tyStaticArray;
  Result.Name        := Format('array[%d..%d] of %s', [ALow, AHigh, AElementType.Name]);
  Result.ElementType := AElementType;
  Result.LowBound    := ALow;
  Result.HighBound   := AHigh;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewDynArrayType(AElementType: TTypeDesc): TDynArrayTypeDesc;
begin
  Result             := TDynArrayTypeDesc.Create();
  Result.Kind        := tyDynArray;
  Result.Name        := 'array of ' + AElementType.Name;
  Result.ElementType := AElementType;
  FAllTypes.Add(Result);
end;

function TSymbolTable.RegisterGeneric(const AName: string; ATempl: TObject;
                                      const ADeclUnit: string): string;
var
  Idx: Integer;
begin
  Result := '';
  Idx := FGenerics.IndexOf(AName);
  if (Idx >= 0) and (not SameText(FGenericDeclUnits.Strings[Idx], ADeclUnit)) then
  begin
    { Cross-unit collision: the first registration stays authoritative and
      the caller reports the conflict (compilation aborts). }
    Result := FGenericDeclUnits.Strings[Idx];
    Exit;
  end;
  FGenerics.AddObject(AName, ATempl);
  FGenericDeclUnits.Add(ADeclUnit);
  FGenericTemplates.Add(ATempl);
end;

function TSymbolTable.FindGeneric(const AName: string): TObject;
var
  Idx: Integer;
begin
  Idx := FGenerics.IndexOf(AName);
  if Idx >= 0 then
    Result := TObject(FGenerics.Objects[Idx])
  else
    Result := nil;
end;

function TSymbolTable.RegisterGenericRoutine(const AName: string; ATempl: TObject;
                                             const ADeclUnit: string): string;
var
  Idx: Integer;
begin
  Result := '';
  Idx := FGenericRoutines.IndexOf(AName);
  if (Idx >= 0) and (not SameText(FGenericRoutineDeclUnits.Strings[Idx], ADeclUnit)) then
  begin
    Result := FGenericRoutineDeclUnits.Strings[Idx];
    Exit;
  end;
  FGenericRoutines.AddObject(AName, ATempl);
  FGenericRoutineDeclUnits.Add(ADeclUnit);
end;

function GenericCollisionMsg(const AKind, AName, APrevUnit, ANewUnit: string): string;
begin
  Result := Format(
    '%s ''%s'' is declared in both ''%s'' and ''%s'': generic instances ' +
    'share one program-wide symbol per instantiation, so same-named ' +
    'generics from different units would silently alias at link time; ' +
    'rename one of them', [AKind, AName, APrevUnit, ANewUnit]);
end;

function TSymbolTable.FindGenericRoutine(const AName: string): TObject;
var
  Idx: Integer;
begin
  Idx := FGenericRoutines.IndexOf(AName);
  if Idx >= 0 then
    Result := FGenericRoutines.Objects[Idx]
  else
    Result := nil;
end;

function TSymbolTable.OwnImportedDecl(ADecl: TObject): TObject;
begin
  FImportedDecls.Add(ADecl);
  Result := ADecl;
end;

procedure TSymbolTable.RegisterBuiltins;
var
  Sym:              TSymbol;
  TObjectDesc:      TRecordTypeDesc;
  FCustomAttrDesc:  TRecordTypeDesc;
  TMethodDesc:      TRecordTypeDesc;
  VarRecDesc:       TRecordTypeDesc;
begin
  { Primitive types }
  FTypeInteger  := NewType(tyInteger,  'Integer');
  FTypeInt64    := NewType(tyInt64,    'Int64');
  FTypeUInt32   := NewType(tyUInt32,   'UInt32');
  FTypeUInt64   := NewType(tyUInt64,   'UInt64');
  FTypeSmallInt := NewType(tySmallInt, 'SmallInt');
  FTypeWord     := NewType(tyWord,     'Word');
  FTypeByte     := NewType(tyByte,     'Byte');
  FTypeBoolean := NewType(tyBoolean, 'Boolean');
  FTypeString  := NewType(tyString,  'string');
  FTypeVoid    := NewType(tyVoid,    'void');
  FTypeNil     := NewType(tyNil,     'nil');
  FTypePointer := NewPointerType('Pointer', nil);  { untyped pointer }
  FTypePChar   := NewType(tyPChar, 'PChar');
  FTypeDouble  := NewType(tyDouble, 'Double');
  FTypeSingle  := NewType(tySingle, 'Single');

  { Register type names as skType symbols in global scope }
  Define(TSymbol.Create('Integer', skType, FTypeInteger));
  Define(TSymbol.Create('Int64',   skType, FTypeInt64));
  Define(TSymbol.Create('UInt32',  skType, FTypeUInt32));
  Define(TSymbol.Create('Cardinal', skType, FTypeUInt32));  { FPC/Delphi alias }
  Define(TSymbol.Create('UInt64',  skType, FTypeUInt64));
  Define(TSymbol.Create('QWord',   skType, FTypeUInt64));   { FPC alias }
  Define(TSymbol.Create('PtrUInt', skType, FTypeUInt64));   { pointer-sized unsigned on 64-bit }
  Define(TSymbol.Create('SmallInt', skType, FTypeSmallInt));
  Define(TSymbol.Create('Int16',    skType, FTypeSmallInt));  { Delphi alias }
  Define(TSymbol.Create('Word',     skType, FTypeWord));
  Define(TSymbol.Create('UInt16',   skType, FTypeWord));      { Delphi alias }
  Define(TSymbol.Create('Byte',    skType, FTypeByte));
  Define(TSymbol.Create('Boolean', skType, FTypeBoolean));
  Define(TSymbol.Create('string',  skType, FTypeString));
  Define(TSymbol.Create('Pointer', skType, FTypePointer));
  Define(TSymbol.Create('PChar',   skType, FTypePChar));
  Define(TSymbol.Create('TClass',  skType, FTypePointer));  { class metareference; placeholder until tyMetaClass lands }
  Define(TSymbol.Create('Double',  skType, FTypeDouble));
  Define(TSymbol.Create('Single',  skType, FTypeSingle));

  { TObject — root of the class hierarchy; no fields, no parent }
  TObjectDesc := NewClassType('TObject');
  TObjectDesc.AddVTableSlot('Destroy',  '$TObject_Destroy');
  TObjectDesc.AddVTableSlot('ToString', '$TObject_ToString');
  Define(TSymbol.Create('TObject', skType, TObjectDesc));

  { TCustomAttribute — base class for user-defined custom attributes.
    Inherits from TObject; no additional fields or methods. }
  FCustomAttrDesc := NewClassType('TCustomAttribute');
  FCustomAttrDesc.CopyVTableFrom(TObjectDesc);
  FCustomAttrDesc.Parent := TObjectDesc;
  Define(TSymbol.Create('TCustomAttribute', skType, FCustomAttrDesc));

  { TMethod — record carrying a (Code, Data) pair, byte-for-byte
    identical to a 'procedure of object' value's representation.  The
    cast 'TMyMethod(m)' (m: TMethod, TMyMethod a method-pointer type)
    is a no-op at the QBE level: both share the 16-byte (Code at +0,
    Data at +8) layout. }
  TMethodDesc := NewRecordType('TMethod');
  TMethodDesc.AddField('Code', FTypePointer);
  TMethodDesc.AddField('Data', FTypePointer);
  Define(TSymbol.Create('TMethod', skType, TMethodDesc));

  { TVarRec — one element of an 'array of const' argument list.  A 16-byte
    tagged value: VType (a vt* discriminant) at +0, and a single pointer-sized
    VValue slot at +8 holding the boxed value (or a pointer to it).  The
    compiler builds these at the call site from a bracket literal; the callee
    reads each element by switching on VType and reinterpret-casting VValue:
      vtInteger / vtBoolean / vtEnum  → Integer(v.VValue)
      vtInt64                         → Int64(v.VValue)
      vtPointer / vtObject            → Pointer/TObject(v.VValue)
      vtAnsiString                    → string(v.VValue)
      vtExtended                      → PDouble(v.VValue)^   (heap-boxed double)
    Layout matches FPC's TVarRec (VType at +0, value slot at +8). }
  VarRecDesc := NewRecordType('TVarRec');
  VarRecDesc.AddField('VType',  FTypeByte);
  VarRecDesc.AddField('VValue', FTypePointer);
  Define(TSymbol.Create('TVarRec', skType, VarRecDesc));

  { vt* discriminant constants for TVarRec.VType.  Values follow FPC where a
    direct equivalent exists, so ported case statements line up. }
  Sym := TSymbol.Create('vtInteger', skConstant, FTypeInteger);
  Sym.ConstValue := 0;  Define(Sym);
  Sym := TSymbol.Create('vtBoolean', skConstant, FTypeInteger);
  Sym.ConstValue := 1;  Define(Sym);
  Sym := TSymbol.Create('vtExtended', skConstant, FTypeInteger);  { Double (heap-boxed) }
  Sym.ConstValue := 3;  Define(Sym);
  Sym := TSymbol.Create('vtPointer', skConstant, FTypeInteger);
  Sym.ConstValue := 5;  Define(Sym);
  Sym := TSymbol.Create('vtObject', skConstant, FTypeInteger);
  Sym.ConstValue := 7;  Define(Sym);
  Sym := TSymbol.Create('vtInt64', skConstant, FTypeInteger);
  Sym.ConstValue := 16;  Define(Sym);
  Sym := TSymbol.Create('vtAnsiString', skConstant, FTypeInteger);  { the UTF-8 string }
  Sym.ConstValue := 20;  Define(Sym);
  Sym := TSymbol.Create('vtEnum', skConstant, FTypeInteger);  { Blaise enum ordinal }
  Sym.ConstValue := 24;  Define(Sym);

  { IInterface — root of the interface hierarchy; no methods }
  Define(TSymbol.Create('IInterface', skType, NewInterfaceType('IInterface')));

  { Boolean constants }
  Sym := TSymbol.Create('True',  skConstant, FTypeBoolean);
  Sym.ConstValue := 1;
  Define(Sym);
  Sym := TSymbol.Create('False', skConstant, FTypeBoolean);
  Sym.ConstValue := 0;
  Define(Sym);

  { Integer range constants — MaxInt is the 32-bit maximum; all Copy(S,N,MaxInt)
    uses mean "rest of string" which works for strings shorter than 2 GB. }
  Sym := TSymbol.Create('MaxInt', skConstant, FTypeInteger);
  Sym.ConstValue := 2147483647;
  Define(Sym);

  { Platform constants — values derived from the compilation target (GTarget).
    Defined in system.pas; pre-seeded here so they resolve even before
    system.pas is loaded as a unit. }
  Sym := TSymbol.Create('LineEnding', skConstant, FTypeString);
  Sym.ConstString := TargetLineEnding(GTarget);
  Define(Sym);
  Sym := TSymbol.Create('DirectorySeparator', skConstant, FTypeString);
  Sym.ConstString := TargetDirectorySeparator(GTarget);
  Define(Sym);
  Sym := TSymbol.Create('PathSeparator', skConstant, FTypeString);
  Sym.ConstString := TargetPathSeparator(GTarget);
  Define(Sym);

  { Built-in I/O procedures }
  Sym := TSymbol.Create('Write',   skProcedure, nil);
  Define(Sym);
  Sym := TSymbol.Create('WriteLn', skProcedure, nil);
  Define(Sym);
  Sym := TSymbol.Create('StdErr', skConstant, FTypeInteger);
  Sym.ConstValue := 2;
  Define(Sym);

  { Built-in set procedures }
  Sym := TSymbol.Create('Include', skProcedure, nil);
  Define(Sym);
  Sym := TSymbol.Create('Exclude', skProcedure, nil);
  Define(Sym);

  { Built-in memory management }
  Sym := TSymbol.Create('GetMem',     skFunction,  FTypePointer);
  Define(Sym);
  Sym := TSymbol.Create('ReallocMem', skFunction,  FTypePointer);
  Define(Sym);
  Sym := TSymbol.Create('FreeMem',    skProcedure, nil);
  Define(Sym);

  { Built-in string operations }
  Sym := TSymbol.Create('Format',    skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('Length',    skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Pos',       skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('PosEx',     skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Copy',      skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('UpperCase', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('LowerCase', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('Trim',      skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('SameText',  skFunction, FTypeBoolean);
  Define(Sym);
  Sym := TSymbol.Create('IntToStr',  skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('Int64ToStr',  skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('UInt64ToStr', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('DoubleToStr', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('SingleToStr', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('StrToDouble', skFunction, FTypeDouble);
  Define(Sym);
  Sym := TSymbol.Create('StrToInt',  skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('StrToInt64', skFunction, FTypeInt64);
  Define(Sym);
  Sym := TSymbol.Create('CompareStr',  skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('CompareText', skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('OrdAt',       skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Ord',         skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Chr',         skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('UpCase',      skFunction, FTypeString);
  Define(Sym);
  { Abs — absolute value; return type matches argument type (resolved in semantic) }
  Sym := TSymbol.Create('Abs', skFunction, FTypeInteger); Define(Sym);
  { MethodAddress(Obj, Name) — published-method lookup via typeinfo chain }
  Sym := TSymbol.Create('MethodAddress', skFunction, FTypePointer); Define(Sym);
  { ClassCreate(Cls, ...args) — runtime construction from a metaclass value.
    Calls _ClassCreate to allocate + install vtable, then invokes the
    constructor on Cls.BaseClass with the supplied args.  Result type is
    the BaseClass; resolved by AnalyseFuncCallExpr in uSemantic. }
  Sym := TSymbol.Create('ClassCreate', skFunction, FTypePointer); Define(Sym);
  { Inc/Dec — in-place increment/decrement (var param, 1 or 2 args) }
  Sym := TSymbol.Create('Inc', skProcedure, nil); Define(Sym);
  Sym := TSymbol.Create('Dec', skProcedure, nil); Define(Sym);
  { Delete(var S: string; Idx, Count: Integer) — string mutator }
  Sym := TSymbol.Create('Delete', skProcedure, nil); Define(Sym);
  { SetLength(var S: string; N: Integer) — string truncate/grow }
  Sym := TSymbol.Create('SetLength', skProcedure, nil); Define(Sym);
  { Assigned(P): Boolean — True if P <> nil; accepts pointer/class/proc types }
  Sym := TSymbol.Create('Assigned', skFunction, FTypeBoolean); Define(Sym);
  { Memory utilities }
  Sym := TSymbol.Create('ZeroMem', skProcedure, nil); Define(Sym);
  { CLI arguments }
  Sym := TSymbol.Create('ParamCount', skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('ParamStr',   skFunction,  FTypeString);  Define(Sym);
  { File I/O }
  Sym := TSymbol.Create('ReadFile',   skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('WriteFile',  skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('AppendFile', skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('FileExists',             skFunction,  FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('FileAge',               skFunction,  FTypeInt64);   Define(Sym);
  Sym := TSymbol.Create('DeleteFile',             skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('CurrentExceptionMessage', skFunction,  FTypeString);  Define(Sym);
  { Environment and process }
  Sym := TSymbol.Create('GetEnvVar',  skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('GetEnvironmentVariable', skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('Exec',       skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('Halt',       skProcedure, nil);          Define(Sym);
  { OS utility functions }
  Sym := TSymbol.Create('GetProcessID',      skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('GetTempDir',        skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('DirectoryExists',   skFunction,  FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('ForceDirectories',  skFunction,  FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('GetCurrentDir',     skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('GetTempFileName',   skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('Sleep',             skProcedure, nil);          Define(Sym);
  { File path manipulation }
  Sym := TSymbol.Create('ChangeFileExt',                skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFileName',              skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFilePath',              skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFileExt',               skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('IncludeTrailingPathDelimiter', skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFileDir',               skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExcludeTrailingPathDelimiter', skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('RemoveDir',                    skProcedure, nil);        Define(Sym);
  Sym := TSymbol.Create('RenameFile',                   skFunction, FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('SetCurrentDir',                skFunction, FTypeBoolean); Define(Sym);
  { Process management (used by Process.pas RTL) }
  Sym := TSymbol.Create('ProcessCreate',     skFunction,  FTypePointer); Define(Sym);
  Sym := TSymbol.Create('ProcessSetExe',     skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('ProcessAddArg',     skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('ProcessExecute',    skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('ProcessRunning',    skFunction,  FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('ProcessReadOutput', skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('ProcessWaitOnExit', skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('ProcessExitCode',   skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('ProcessFree',       skProcedure, nil);          Define(Sym);
  { Math builtins — Sqrt/Ceil/Floor/Round/Trunc/Ln/Log2/Log10/Power,
    Sin/Cos/Tan/ArcTan/ArcTan2, IsNaN/IsInfinite.
    Return types marked here are overridden in uSemantic.AnalyseFuncCallExpr
    (e.g. Ceil/Floor/Round/Trunc return Integer; Sin/Cos/Tan return the arg
    type; IsNaN/IsInfinite return Boolean). }
  Sym := TSymbol.Create('Sqrt',       skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Ceil',       skFunction, FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('Floor',      skFunction, FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('Round',      skFunction, FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('Trunc',      skFunction, FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('Ln',         skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Log2',       skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Log10',      skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Power',      skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Sin',        skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Cos',        skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Tan',        skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('ArcTan',     skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('ArcTan2',    skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('ArcSin',     skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('ArcCos',     skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Sinh',       skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Cosh',       skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('Tanh',       skFunction, FTypeDouble);  Define(Sym);
  Sym := TSymbol.Create('IsNaN',      skFunction, FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('IsInfinite', skFunction, FTypeBoolean); Define(Sym);
end;

function TSymbolTable.DefineGlobal(ASymbol: TSymbol): Boolean;
begin
  if (ASymbol.OwningUnit = '') and (FDefineOwningUnit <> '') then
    ASymbol.OwningUnit := FDefineOwningUnit;
  if FDefineImplPrivate then
    ASymbol.IsImplPrivate := True;
  Result := TScope(FScopeStack.Items[0]).Define(ASymbol);
end;

function TSymbolTable.GlobalScope: TScope;
begin
  Result := TScope(FScopeStack.Items[0]);
end;

function TSymbolTable.GetCurrentScope: TScope;
begin
  Result := TScope(FScopeStack.Items[FScopeStack.Count - 1]);
end;

function TSymbolTable.GetScopeDepth: Integer;
begin
  Result := FScopeStack.Count;
end;

function TSymbolTable.PushScope: TScope;
begin
  Result := TScope.Create(CurrentScope);
  FScopeStack.Add(Result);
end;

procedure TSymbolTable.PopScope;
begin
  if FScopeStack.Count > 1 then
    FScopeStack.Delete(FScopeStack.Count - 1);
end;

function TSymbolTable.Define(ASymbol: TSymbol): Boolean;
begin
  { Only auto-tag global-scope symbols.  Locals (parameters, var
    blocks inside method bodies, etc.) live in pushed scopes and
    must remain OwningUnit='' — uses-chain visibility doesn't apply
    to them. }
  if (ASymbol.OwningUnit = '') and (FDefineOwningUnit <> '')
     and (FScopeStack.Count = 1) then
    ASymbol.OwningUnit := FDefineOwningUnit;
  if FDefineImplPrivate and (FScopeStack.Count = 1) then
    ASymbol.IsImplPrivate := True;
  { Propagate the owning unit onto the type descriptor so codegen can mangle a
    type's storage symbols by the declaring unit even after a same-named type
    from another used unit wins the flat slot (cross-unit type last-wins). }
  if (ASymbol.Kind = skType) and (ASymbol.TypeDesc <> nil)
     and (ASymbol.TypeDesc.OwningUnit = '') and (ASymbol.OwningUnit <> '') then
    ASymbol.TypeDesc.OwningUnit := ASymbol.OwningUnit;
  Result := CurrentScope.Define(ASymbol);
end;

function TSymbolTable.ExtractLocal(const AName: string): TSymbol;
begin
  Result := CurrentScope.ExtractLocal(AName);
end;

function TSymbolTable.Lookup(const AName: string): TSymbol;
var
  I: Integer;
  Sym: TSymbol;
begin
  { Resolution layers, highest to lowest priority:

      1. Pushed scopes (locals, params, nested-routine outer locals)
      2. Class context — class members, walked via the parent chain.
         Currently handled at caller sites (FCurrentClass.FindField
         fallback) because TFieldInfo isn't a TSymbol; promotion into
         this function lands with the step-9 refactor.
      3. Current compilation unit's own symbols
      4. Uses chain, right-to-left (last in `uses` wins)
      5. System — implicitly prepended to the chain at index 0, so
         it falls out of layer 4 naturally
      6. True global — language builtins from RegisterBuiltins, and
         (today) any flat-merged unit symbols not caught by layer 3
         or 4.  The flat residue goes away in step 9. }

  { Layer 1. }
  for I := FScopeStack.Count - 1 downto 1 do
  begin
    Result := TScope(FScopeStack.Items[I]).LookupLocal(AName);
    if Result <> nil then
    begin
      { A module-name marker reserves the identifier but is not a
        value — the name resolves to nothing, and it shadows any
        same-named symbol in lower layers (issue #84). }
      if Result.Kind = skModule then
        Result := nil;
      Exit;
    end;
  end;

  { Layer 3 — probe the global scope but only return a hit when the
    symbol is owned by the unit currently being analysed.  This makes
    `MyUnit.X` declared in the interface section beat an X from a
    used unit, the same way it would have if we'd stored current-unit
    symbols in a dedicated pool.  Builtins (OwningUnit = '') and
    symbols owned by other units fall through to later layers. }
  Sym := TScope(FScopeStack.Items[0]).LookupLocal(AName);
  { Module-name marker at global scope: same rule as layer 1 — the
    name is reserved, resolves to nothing, and blocks lower layers. }
  if (Sym <> nil) and (Sym.Kind = skModule) then
  begin
    Result := nil;
    Exit;
  end;
  if (Sym <> nil) and (FDefineOwningUnit <> '')
     and SameText(Sym.OwningUnit, FDefineOwningUnit) then
  begin
    Result := Sym;
    Exit;
  end;

  { Layer 4 + 5 — the chain walker prepends System so we don't probe
    it separately.  Bypassed when the chain walker itself is calling
    us back to retrieve a canonical TSymbol. }
  if (FUsesChainProvider <> nil) and not FBypassUsesChain then
  begin
    Result := FUsesChainProvider.LookupViaUsesChain(AName);
    if Result <> nil then Exit;
  end;

  { Layer 6 — whatever the global walk produced earlier (builtins, or
    flat-merged residue not yet caught above).

    Suppress one specific leak: an IMPLEMENTATION-section symbol of unit A is
    private to A and must never resolve while a DIFFERENT unit B is being
    analysed.  Without this, a class declared in A's implementation section
    leaks into an unrelated B through the flat global scope (the root blocker
    for "classes in unit implementation section").  Interface symbols are left
    untouched here so existing transitive-visibility behaviour is unchanged.

    The check only runs while a unit/program is being analysed
    (FDefineOwningUnit <> '') and the chain walker is not mid-callback; outside
    analysis (some codegen-side lookups clear FDefineOwningUnit) the residue is
    returned unchanged so unit-prefix mangling still resolves owned symbols.

    It is also disabled during code emission (FInCodegen): the leak it guards is
    purely an analysis-time concern, whereas a backend legitimately resolves a
    unit's own implementation-section classes to emit their typeinfo/vtable/
    _FieldCleanup.  FDefineOwningUnit can have drifted to a dependency unit
    mid-emit, which would otherwise make this suppression wrongly fire and drop
    the class's typeinfo, leaving a dangling symbol the linker binds to garbage. }
  if (Sym <> nil) and Sym.IsImplPrivate and (FDefineOwningUnit <> '')
     and not FBypassUsesChain and not FInCodegen
     and not SameText(Sym.OwningUnit, FDefineOwningUnit) then
  begin
    Result := nil;
    Exit;
  end;
  Result := Sym;
end;

{ For a plain dotted identifier path 'A.B.C' (every component an identifier,
  single-dot separators) return the final component 'C'.  In a qualified type
  reference 'UnitName.TypeName' the type is always that final identifier and
  the leading components name the (possibly dotted) unit.  Returns '' when
  AName is not such a path — e.g. the bracket/space/caret/angle-bracket forms
  used to encode array, pointer, set and generic-instance types — leaving
  those untouched for the on-demand resolver. }
function UnitQualifierTail(const AName: string): string;
var
  I, LastDot: Integer;
  B: Integer;
begin
  Result  := '';
  LastDot := -1;
  for I := 0 to Length(AName) - 1 do
  begin
    B := AName[I];
    if B = Ord('.') then
      LastDot := I
    else if not (((B >= Ord('A')) and (B <= Ord('Z'))) or
                 ((B >= Ord('a')) and (B <= Ord('z'))) or
                 ((B >= Ord('0')) and (B <= Ord('9'))) or
                 (B = Ord('_'))) then
      Exit;  { contains a non-identifier byte — not a qualified name }
  end;
  if (LastDot >= 0) and (LastDot < Length(AName) - 1) then
    Result := Copy(AName, LastDot + 1, MaxInt);
end;

function TSymbolTable.FindType(const AName: string): TTypeDesc;
var
  Sym:  TSymbol;
  Tail: string;
begin
  Sym := Lookup(AName);  { honour uses-chain visibility }
  if (Sym <> nil) and (Sym.Kind = skType) then
    Exit(Sym.TypeDesc);
  { Qualified type name 'UnitName.TypeName' — resolve by the final dotted
    component through the same uses chain (the qualifier names a used unit). }
  Tail := UnitQualifierTail(AName);
  if Tail <> '' then
  begin
    Sym := Lookup(Tail);
    if (Sym <> nil) and (Sym.Kind = skType) then
      Exit(Sym.TypeDesc);
  end;
  Result := nil;
end;

function IsUnmangledUnit(const AUnitName: string): Boolean;
begin
  { RTL units export their runtime symbols (_SetArgs, _BlaiseGetMem, _start, …)
    UNMANGLED — the compiler emits bare calls to them — so their unit prefix is
    empty.  The RTL units are: System, the rtl.* platform units, and the
    runtime.* units (dotted-flat names after the RTL-unification move; the
    legacy blaise_* names are still accepted for any not-yet-renamed source). }
  Result := True;
  if AUnitName = '' then Exit;
  if SameText(AUnitName, 'System') then Exit;
  if (Length(AUnitName) >= 4)
     and SameText(Copy(AUnitName, 0, 4), 'rtl.') then Exit;
  if (Length(AUnitName) >= 8)
     and SameText(Copy(AUnitName, 0, 8), 'runtime.') then Exit;
  if (Length(AUnitName) >= 7)
     and SameText(Copy(AUnitName, 0, 7), 'blaise_') then Exit;
  Result := False;
end;

function MangleUnitPrefix(const AUnitName: string): string;
var
  I:  Integer;
  Ch: string;
begin
  if IsUnmangledUnit(AUnitName) then
  begin
    Result := '';
    Exit;
  end;
  Result := '';
  for I := 0 to Length(AUnitName) - 1 do
  begin
    Ch := Copy(AUnitName, I, 1);
    if Ch = '.' then Result := Result + '_'
    else             Result := Result + Ch;
  end;
  Result := Result + '_';
end;

end.
