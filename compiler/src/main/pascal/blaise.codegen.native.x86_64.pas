{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.x86_64;

{ x86_64 (System V AMD64 ABI) backend for the native code generator.

  Emits AT&T-syntax assembly text (fed to `as`/`cc`, like QBE's .s output).

  Expression evaluation strategy (naive, correctness-first): every integer
  expression is evaluated into %eax.  Binary operators evaluate the left
  operand into %eax, push it, evaluate the right operand into %eax, pop the
  left into %ecx, then combine.  This needs no register allocator and is
  correct for arbitrary nesting; the push/pop pairs are always balanced within
  one expression, so %rsp is back to its frame-aligned position at every call
  site (SysV requires 16-byte alignment at calls).

  Milestone M2: integer literals, + - * div mod, and Write/WriteLn of integers
  (mapped to the _SysWriteInt / _SysWriteNewline runtime calls). }

interface

uses
  SysUtils, Classes, contnrs, Generics.Collections, uAST, uSymbolTable, uStrCompat,
  blaise.codegen, blaise.codegen.arcshapes, uDebugFacts, strutils,
  blaise.codegen.native.backend, blaise.codegen.target;

const
  { Per-argument hoist kinds recorded by EmitArgHoist, parallel to the
    depth list.  Kinds >= akRecCall reload a single saved 8-byte value in
    the arg loop; akOALit reloads the saved data pointer and pushes the
    high index as a second slot. }
  akNone = 0;        { not hoisted — evaluated in the normal arg loop }
  akOALit = 1;       { open-array literal: element block + saved data ptr }
  akRecCall = 2;     { record-returning call arg: sret buffer + saved ptr }
  akStrPin = 3;      { const-string pin: saved value, AddRef'd; released after }
  akStrConsume = 4;  { const-string consume: saved +1 value; released after }
  akIntfConsume = 5; { interface-returning-call arg: owned (+1) fat pointer
                       saved (itab then obj, obj on top); obj released after }

  { Number of reserved statement-scoped deferred-release frame slots (BUG-003
    native half).  A single statement rarely defers more than one owned-transient
    chain base; 8 is a generous bound.  Overflow falls back to the AddRef-pin
    (safe leak), so this cap never causes incorrect code. }
  PENDREL_SLOTS = 8;

type
  { Per-call bookkeeping for hoisted call arguments — see EmitArgHoist.
    Frames nest: a call emitted while evaluating another call's arguments
    pushes its own frame. }
  TOALCallFrame = class
  public
    Depths: TList<Integer>;   { per-arg saved-slot depth; -1 = not hoisted }
    Kinds: TList<Integer>;    { per-arg hoist kind (akXxx), parallel to Depths }
    Total: Integer;           { bytes of blocks, buffers + saved slots on the stack }
    Pushed: Integer;          { bytes pushed since the hoist pre-pass }
    { The call's argument list — read by the EndCallArgs epilogue for
      record-temp field releases.  Owned by the AST, not by the frame. }
    [Unretained] Args: TObjectList;
    constructor Create;
    destructor Destroy; override;
  end;

  TX86_64Backend = class(TNativeBackend)
  protected
    FLabelCount: Integer;       { monotonic source of unique local labels }
    { Tracked stack depth of the emitted instruction stream, in bytes below
      the 16-byte-aligned post-prologue %rsp (0 right after
      `movq %rsp, %rbp`; a function label resets it to 8 = the return
      address of a not-yet-framed function).  Maintained by the Emit
      override, which parses pushq/popq/subq/addq-on-%rsp lines as they are
      emitted.  System V requires %rsp ≡ 0 (mod 16) at every call
      instruction; argument staging pushes values, so a call evaluated
      while an odd number of 8-byte slots is pinned (F(a, G(...)) — a is
      pushed while G's whole subtree runs) would execute at %rsp ≡ 8
      (mod 16).  Emit wraps any callq at a misaligned tracked depth in a
      subq $8/addq $8 pad pair.  Calls that pass genuine SysV stack
      arguments must NOT be wrapped (the pad would shift the arguments);
      the >6-slot overflow paths instead size their overflow region via
      AlignFreshBytes so the call site is aligned by construction and the
      wrap pad never fires for them. }
    FSPDepth: Integer;
    { One-line peephole window: a just-emitted `pushq %reg` is held back here
      so an immediately following `popq %reg2` fuses into a single
      `movq %reg, %reg2` (or into nothing when the registers match).  Any
      other line flushes the pending push first.  FSPDepth is updated when
      the push is PENDED (so AlignFreshBytes and the callq wrap pad see the
      true depth) and rolled back on fusion. }
    FPendingPush: string;
    { --- Stage-1 register promotion (two-pass) -----------------------
      Hot, safe scalar locals/params live in callee-saved %r14/%r15 for
      the whole function instead of frame slots.  Pass 1 emits the
      function unpromoted; if that text contains NO %r14/%r15 (all the
      emitter's scratch windows would collide) and candidates exist, the
      region is rolled back and re-emitted with FPromoActive set:
      VarOperand answers the register, and PromoRewrite maps each
      width-suffixed memory-form instruction onto the matching
      sub-register form.  Promotion is disabled under --debug-opdf
      (OPDF has no register location expression; pdr reads frame slots). }
    FPromoActive: Boolean;
    { Promotion register pool: vars are assigned to the first AVAILABLE
      registers (available = absent from the pass-1 text) in this order.
      %r13 is deliberately NOT in the pool — it is the cross-call pin. }
    FPromoVars: array[0..3] of string;   { var per pool slot ('' unused) }
    FPromoAvail: array[0..3] of Boolean; { pass-1 scan verdict per slot }
    FPromoFunc: string;    { symbol being emitted (promotion diagnostics) }
    { Bisection aid: BLAISE_PROMO_LIMIT=N promotes only the first N eligible
      functions (-1 = unlimited).  BLAISE_PROMO_LOG=1 prints each promoted
      symbol to stderr.  Used to pin a promotion miscompile to one function
      during self-hosting bring-up; costs one env read per backend. }
    FPromoCount: Integer;
    FPromoLimit: Integer;
    FPromoLog: Boolean;
    FPromoOnly: string;    { BLAISE_PROMO_ONLY=Sym — promote only that symbol }
    { True when the current function contains try statements: its except
      paths hold the in-flight exception in %r15 (callee-saved) WITHOUT a
      window save, so the function saves/restores the incumbent %r15 in
      its prologue/epilogue.  Without this, any function whose exception
      path executes clobbers the caller's %r15 — latent before register
      promotion (nothing lived in %r15 across calls), fatal after. }
    FTryR15Save: Boolean;
    { Cross-call pin: when the pass-1 scan also proved %r13 unused, the
      generic binary-operator bracket saves its LHS in %r13 across a
      complex RHS (typically a call) instead of pushq/popq — killing the
      stack round-trip AND the odd-depth call-site alignment pad.  Only
      the OUTERMOST bracket pins (FPinDepth); nested brackets fall back
      to push/pop.  %r13 is callee-saved and untouched by the except
      machinery; the incumbent is saved beside the promo saves. }
    FPromoPinOk: Boolean;
    FPinDepth: Integer;
    { --- Phase-1 inlining (native port of the QBE inliner) -----------
      Small leaf functions (TMethodDecl.IsInlineCandidate, computed by
      uSemantic) expand at the call site: arguments stage into a shared
      caller-frame scratch area (_inl_area, reserved by a BuildFrame
      pre-scan and validated independently at emission — a site the
      pre-scan missed simply stays a normal call), the body emits with
      the callee's params/Result name-mapped onto area slots, and Exit
      jumps to a per-site end label.  Depth 1: calls inside an inlined
      body emit as normal calls.  Disabled under --debug-opdf. }
    FInlineActive: Boolean;
    FInlineDepth: Integer;      { nesting level (cap 2, matching QBE) }
    FInlineNextIdx: Integer;    { next free scratch-slot index (nested sites) }
    FInlineMap: TDictionary<string, Integer>;     { callee name → rbp offset }
    FInlineTypes: TDictionary<string, TTypeDesc>; { callee name → type }
    FInlineEndLbl: string;
    FInlineSlotCount: Integer;  { _inl_s slots reserved this function }
    FInlineCount: Integer;      { sites inlined so far (bisection aid) }
    FInlineLimit: Integer;      { BLAISE_INLINE_LIMIT (-1 = unlimited) }
    FInlineLog: Boolean;        { BLAISE_INLINE_LOG }
    { OPDF debug facts (nil unless --debug-opdf): the backend records each
      function's symbol, end label, real frame-slot offsets and per-statement
      line labels here; the OPDF emitter consumes them for exact debug info.
      Owned by TCodeGenNative. }
    [Unretained] FDbgFacts: TDbgFacts;
    [Unretained] FDbgCur: TDbgFunc;   { facts entry for the function being emitted }
    FDbgSeq: Integer;                 { .Ldbg_N label counter }
    { Enclosing function while a nested proc is being emitted — lets
      DbgMarkParams resolve captured-var types from the outer var/param
      declarations.  nil for top-level functions. }
    [Unretained] FDbgOuterDecl: TMethodDecl;
    { Source file of the unit currently being emitted; stamped onto each
      TDbgFunc so per-unit line records carry the right file.  Empty while
      emitting the main program (the emitter falls back to its own file). }
    FDbgSrcFile: string;
    { Global slots to define in the .data section: program-level variables plus
      hidden for-loop end-value slots.  Insertion-ordered so EmitDataSection
      emits them in declaration order; ContainsKey gives O(1) dedup.  The value
      is the slot's static type so loads, stores, and the .data directive all
      pick the right width and signedness. }
    FDataGlobals: TOrderedDictionary<string, TTypeDesc>;
    { Canonical global emit name → its owning unit (captured at AddGlobal time).
      EmitDataSection and IsImportedGlobal consult this instead of re-looking-up
      the (now-mangled) canonical key in the symbol table, which would miss. }
    FGlobalOwners: TDictionary<string, string>;
    { Bare names known to be MODULE-LEVEL variables (unit interface/implementation
      section or program-level).  GlobalSymName consults this to decide whether an
      unexported (Sym=nil at codegen) name may take the FCurrentUnitName context
      prefix — keeping class-var ClassVarEmitName and internal labels verbatim. }
    FModuleVarNames: TStringList;
    FGlobalInits: TDictionary<string, TConstDecl>;  { global name → initialiser (var G: T = value) }
    FThreadVarGlobals: TDictionary<string, Boolean>;
    FWeakGlobals:      TDictionary<string, Boolean>;
    { Class-name string blobs already emitted to avoid duplicate label errors.
      Keyed by mangled name. }
    FClassNameEmitted: TDictionary<string, Boolean>;
    { String literal pool: unique string values in encounter order.  Each gets
      a __sN label in .rodata (12-byte ARC header + data + NUL).  The data
      pointer (str_ptr convention) is header+12. }
    FStrLits: TStringList;

    { Current function's stack frame: maps a local name (param, var, or Result)
      to its negative %rbp-relative byte offset.  nil while emitting program
      $main (whose top-level vars are globals, not frame slots).  Built once per
      function then looked up by name on every ident read and assignment — a
      key->value map, so TDictionary is the right container for the access
      pattern. }
    FFrame:     TDictionary<string, Integer>;
    { Parallel to FFrame: the static type of each frame slot, so loads and
      stores pick the right width and signedness. }
    FFrameTypes: TDictionary<string, TTypeDesc>;
    FFrameSize:  Integer;       { bytes to reserve for locals (16-aligned) }

    { Statement-scoped deferred class-release list (BUG-003 native half).
      Reading a managed class field off an OWNED transient base yields a value
      that aliases INTO the base's object graph; the base's release frees it.
      To avoid both the use-after-free (release inline) and the leak (pin the
      field forever), the base pointer is SPILLED to one of a small fixed set of
      reserved frame slots (_pendrel_0..N, dual .bss in $main like _jset_scratch)
      and its release DEFERRED to the end of the enclosing leaf statement, AFTER
      the field value has been stored.  FPendingRelCount is how many slots are
      live right now; a leaf statement captures it, emits, then releases the new
      ones (FlushNativePendingReleases).  If a single statement would exceed
      PENDREL_SLOTS the field-read falls back to the old AddRef-pin (safe leak),
      so overflow degrades rather than breaks. }
    FPendingRelCount: Integer;
    FProgHasPendRel:  Boolean;  { $main used a pending-release slot -> emit .bss }

    { Loop label stacks for break/continue: the top entry is the innermost
      loop's end-label (break) or condition-label (continue).
      Parallel FBreakExcDepths / FContinueExcDepths record FExcDepth at the
      point where the loop was entered so EmitExcUnwind knows how many frames
      to pop on a non-local exit. }
    FBreakLabels:       TStack<string>;
    FContinueLabels:    TStack<string>;
    FBreakExcDepths:    TStack<Integer>;
    FContinueExcDepths: TStack<Integer>;
    { Exit label: when non-empty, Exit jumps here (function epilogue).  Empty
      in program $main where Exit maps to a bare return. }
    FExitLabel: string;
    { True when the current function returns a record via the sret convention:
      the hidden first param (%rdi) is the caller's result buffer; Result maps
      to the pointer stored in the Result frame slot; field writes dereference
      through it; the epilogue emits a plain ret. }
    FSretFunc: Boolean;
    { ABI classification for the current record-returning function.  Set in
      BuildFrame; rcSret when FSretFunc is True; rcInt1/rcSSE1/etc. when the
      record qualifies for register return (FSretFunc is False in that case). }
    FRecRetClass: TRecReturnClass;

    { Captured outer-scope variables: when emitting a nested function, this
      holds the names of variables captured from the enclosing scope.  Each
      captured var is passed as an implicit leading pointer param and
      reads/writes are transparently redirected through that pointer.
      Nil when not inside a nested function. }
    FCapturedVars: TStringList;
    { Phase-2 anonymous-method capture: names promoted into the current
      function's heap environment record.  Each gets a '_cap_<Name>' pointer
      slot filled by EmitEnvPrologue (env base + field offset), so every
      IsCaptured access path redirects through it unchanged. }
    FEnvVarNames: TStringList;
    { Phase-4 block-scoped envs: names captured from block-scoped 'var'
      declarations in the CURRENT function (redirected via _cap_ slots
      refilled at the declaring statement, per block execution). }
    FBlockEnvVarNames: TStringList;
    { Locals of the current function that may not be borrowed as const-string
      arguments: address-taken (explicit @ or var/out arg) plus anything
      captured by a nested procedure.  Rebuilt per function in
      EmitFunctionDef; consulted by ConstStrShape.  Mirrors the QBE
      backend's FConstArgUnsafe. }
    FConstArgUnsafe: TStringList;

    { Exception-frame accounting (per-function, reset in ClearFrame):
      FExcDepth    — number of exc frames currently live (pushed − popped).
      FExcFrameNext — index of the next pre-allocated frame slot to consume.
      FFinallyStack — parallel to FExcDepth: the finally body for each live
                      try/finally frame, or nil for a try/except frame.
                      Used by EmitExcUnwind to run finally bodies on Exit/Break/Continue.
                      Uses TList<TCompoundStmt> so nil entries are safe (no ARC release). }
    FExcDepth:     Integer;
    FExcFrameNext: Integer;
    { Frame layout cursor: bytes below %rbp consumed so far.  Kept after
      BuildFrame so EnsureExcFrameSlot can lazily grow the frame when the
      body consumes more exception-frame slots than the source-level
      pre-count saw (finally bodies are emitted more than once). }
    FFrameBottom: Integer;
    FFinallyStack: TList<TCompoundStmt>;
    FForEndNext: Integer;
    { Stack of open-array-literal call frames; top = innermost call currently
      having its arguments pushed.  Owned (frames freed by EndCallArgs). }
    FOALFrames: TList<TOALCallFrame>;
    { Number of exc frame global slots to emit for the program main body.
      Zero when no try stmts appear in the top-level program statements. }
    FProgExcFrameCount: Integer;
    { True when the program-main body uses jumbo sets: two scratch bitmap
      buffers (_jset_scratch_0/1) are emitted as .bss globals (main has no
      frame, so set-op result/literal buffers live in static storage). }
    FProgHasJumboSet: Boolean;
    { Whole-program multi-unit guard: the system-class (TObject /
      TCustomAttribute) class-name strings, typeinfo, vtables and field-cleanup
      stubs are emitted by the FIRST class section that runs (the first unit
      that declares a class, or the program if none does).  Set True after the
      first emission so subsequent units/program do not redefine those symbols. }
    FSystemDefsEmitted: Boolean;
    { Names of dependency units that declared an initialization section, in
      AppendUnit order.  $main calls <Unit>_init for each, in order, after
      _SetArgs — mirrors the QBE backend's EmitMainHeader loop. }
    FUnitInitNames: TStringList;
    { Names of dependency units that export a <Unit>_fini (user finalization
      section and/or managed globals to release), in AppendUnit /
      NoteDepFiniUnit order.  $main calls <Unit>_fini for each in REVERSE
      order at main_exit, BEFORE the program's own EmitGlobalReleases —
      mirrors FUnitInitNames. }
    FUnitFiniNames: TStringList;
    { Owner-prefixed global names already released by some unit's fini walk.
      In the whole-program model unit globals also land in FDataGlobals, so
      EmitGlobalReleases must skip these or the slot would be released twice
      (fini + main epilogue). }
    FFiniReleased: TStringList;
    { Names of dependency units imported from cached .bif/.o in incremental /
      separate-compilation mode (SkipDepCodegen).  A global whose owning unit
      is in this set is DEFINED by that unit's own object — this program/unit
      object must only REFERENCE it (no .globl/label definition), otherwise the
      linker reports a multiple definition.  Recorded by NoteDepInitUnit for
      every imported unit regardless of whether it has an initialization
      section.  Stores raw (unmangled) unit names, matching TSymbol.OwningUnit. }
    FImportedUnits: TStringList;
    FCurrentUnitName: string;
    FProgramName: string;     { set by EmitProgram — program-scope classes keep
                                bare symbol names (no unit prefix), matching
                                uSemantic.CurrentUnitPrefix }

    { Allocate a fresh local assembly label (".L<prefix><N>"). }
    function NewLabel(const APrefix: string): string;
    { True when a catchable EDivByZero can be raised (SysUtils, which declares
      EDivByZero + _RaiseDivByZero, is in scope).  Gates the div/mod zero
      guard; without it a zero divisor traps in hardware as before. }
    function DivGuardAvailable(): Boolean;
    { True when a StrToInt/StrToInt64 call should route to the validating
      SysUtils wrapper (raises EConvertError on invalid input) rather than
      the lenient runtime _StrToInt.  True iff SysUtils is in scope and the
      unit being emitted is NOT SysUtils itself (the wrapper calls StrToInt
      and would otherwise recurse forever). }
    function StrToIntChecked(): Boolean;
    { Register a global integer slot of the given type (idempotent; the first
      registration's type wins).  The width and signedness drive both the
      .data directive and every load/store of the slot. }
    procedure AddGlobal(const AName: string; AType: TTypeDesc);
    procedure RegisterClassVars(AFields: TObjectList);
    procedure MarkThreadVar(const AName: string);
    procedure MarkWeakGlobal(const AName: string);
    function IsThreadVarGlobal(const AName: string): Boolean;
    function IsWeakGlobal(const AName: string): Boolean;
    { True when the global's owning unit was imported from a cached .bif/.o
      (SkipDepCodegen): the cached object DEFINES the global, so this object
      must reference it only — emitting a definition here would clash at link. }
    function IsImportedGlobal(const AName: string): Boolean;
    { True when this global is defined in an unmangled unit (rtl.*/runtime.*/
      System), so its symbol is BARE and re-defined by every object that inlines
      the unit (--no-incremental).  Such definitions must get WEAK link binding
      so archive-member duplicates collapse instead of colliding (GH #174).
      Distinct from IsWeakGlobal, which flags a [Weak] ARC reference. }
    function GlobalLinkWeak(const AName: string): Boolean;
    { The binding directive ('.weak ' or '.globl ') for a global's DEFINITION,
      chosen by GlobalLinkWeak.  Used at every module-var definition site so a
      bare unmangled-unit global gets weak binding (GH #174). }
    function GlobalBindDir(const AName: string): string;
    { The owner-correct emit symbol for a MODULE global (a unit-level var or
      threadvar).  Mirrors the QBE backend's GlobalVarUnitPrefix + VarRef: a
      plain module var owned by unit ua emits as 'ua_GVal'; a program var or an
      RTL/runtime var stays bare.  Names that are NOT module vars in the symbol
      table (class-var ClassVarEmitName, which is already fully mangled, and
      internal labels such as _exc_frame_/_jset_scratch_) are returned verbatim
      so they are never double-prefixed.  This is the native counterpart to the
      QBE ResolvedOwnerUnit honouring — every module global is REGISTERED and
      REFERENCED under this canonical name, so definition and reference always
      agree, and same-named vars across units no longer collide. }
    function GlobalSymName(const AName: string): string;
    { Module-var owner→prefix, matching QBE.MangleGlobalOwner (program-name and
      RTL units → bare).  NOT ClassOwnerPrefix (which prefixes runtime.* classes). }
    function GlobalOwnerPrefix(const AOwner: string): string;
    { The static type of a frame-local slot, or nil if AName is not a local. }
    function LocalType(const AName: string): TTypeDesc;
    { The static type of a program global, or nil if AName is not registered. }
    function GlobalType(const AName: string): TTypeDesc;
    { Emit the accumulated .data section (one slot per registered global). }
    procedure EmitDataSection;
    { Release every ARC-managed program global at program exit (string, class,
      interface obj-slot, dyn-array, and record globals' managed fields), so a
      global object's _FieldCleanup runs at program end.  Mirrors the QBE
      backend's @main_exit release pass.  Called from EmitProgram after the
      exit label. }
    procedure EmitGlobalReleases;
    { Release ONE ARC-managed global slot (owner-prefixed name AName of type
      ATy) via the shared ArcScopeExitReleaseKind dispatch.  The single walk
      body behind BOTH program-exit teardown (EmitGlobalReleases) and the
      per-unit <Unit>_fini walk (EmitUnit), so they cannot drift apart. }
    procedure EmitGlobalReleaseOne(const AName: string; ATy: TTypeDesc);
    { The <Unit>_fini release walk over one unit block's module-level var
      decls: releases every managed, non-threadvar, non-[Unretained] global
      via EmitGlobalReleaseOne and records the owner-prefixed name in
      FFiniReleased so the whole-program EmitGlobalReleases does not release
      the same slot a second time. }
    procedure EmitUnitGlobalReleases(ABlock: TBlock);
    { Emit all class-related data: class-name strings, published-method tables,
      typeinfo blocks, vtables, itab/impllist blocks.  Mirrors QBE backend's
      EmitTypeInfoDefs + EmitVTableDefs.  Called from EmitProgram (program type
      decls) and EmitUnit (unit interface-block type decls). }
    procedure EmitClassSection(ATypeDecls: TObjectList;
                               AGenericInstances: TObjectList;
                               ASymTable: TSymbolTable);
    function ConstElemAsmDir(const AElemType: string): string;
    procedure EmitArrayConstData(ABlock: TBlock; const APrefix: string);
    { Escape a Pascal string for use inside an AS .ascii directive. }
    function AsmEscapeString(const AStr: string): string;
    { Emit a leaq __sN+12(%rip), %rax for the string literal AValue,
      registering a new .rodata blob if not yet seen. }
    procedure EmitStrLitAddr(const AValue: string);
    { Emit an initialised global's data slot from its folded const value
      (var G: T = value).  Called from EmitDataSection inside the .data pass. }
    procedure EmitGlobalInitData(const AName: string; AType: TTypeDesc;
                                 CD: TConstDecl);
    { Emit string literal blobs in .rodata. Called from EmitDataSection. }
    procedure EmitStrLitSection;
    { Emit an immortal class-name string blob in the data section and return
      the label+12 expression that points to the character data.  ASymName
      names the data symbol; AText is the runtime-visible string content. }
    function EmitClassNameString(const ASymName, AText: string): string;
    { Emit the 'attrs_<C>' (class) and 'methattrs_<C>' (method) attribute
      tables for one class decl and return the typeinfo slot expressions
      ('0' when a table is empty).  Class table entries are (attr typeinfo,
      factory thunk) pairs; method table entries are (method name ptr, attr
      typeinfo, factory thunk) triples for published methods.  Mirrors the
      QBE backend's EmitAttrTables. }
    procedure EmitAttrTables(ACD: TClassTypeDef; const ACSym: string;
      out AAttrsStr, AMethAttrsStr: string);
    { Emit the body of one $_FieldCleanup_<T> function.  Calls the
      destructor (if any), releases ARC-managed fields, then returns. }
    procedure EmitVarDeclStmt(AStmt: TVarDeclStmt);
    procedure EmitEnvPrologue(ADecl: TMethodDecl);
    procedure EmitEnvCleanupDefs(ABlock: TBlock);
    { Phase 6: closure envs inside generic-instance method bodies (the
      instances' cloned methods live on the Generic*Instances lists, not in
      any TBlock). }
    procedure EmitEnvCleanupDefsForInstances(AInstances: TObjectList;
                                             ARecordInstances: TObjectList);
    procedure EmitEnvCleanupDefsForMethod(AMD: TMethodDecl);
    { Materialise an anonymous-method literal's 16-byte (Code, Env) fat value
      into its hidden '__anonv_*' frame slot (uSemantic reserves one per
      literal) and leave the slot's ADDRESS in %rax.  Used when the literal is
      consumed in VALUE position (argument passing).  The slot owns one env
      reference, balanced by the reference-local scope-exit release; the old
      value is released first so loop re-evaluation cannot leak. }
    procedure EmitAnonValueToSlot(AME: TAnonMethodExpr);
    procedure EmitFieldCleanupFn(const AMangledName: string;
                                 ART: TRecordTypeDesc;
                                 AWeak: Boolean);
    { ARC field-kind walks (EmitRecordFieldReleases / EmitRecordFieldRetains /
      EmitManagedReleaseAt / EmitStaticArrayReleaseElems) live in
      TNativeBackend as Template Methods; this backend supplies only the
      x86-64 leaf primitives below.  ABaseReg operands are AT&T register
      names ('%rbx' etc.) and must be callee-saved. }
    function  ArcNestedBaseReg: string; override;
    procedure ArcPushNestedBase(AOffset: Integer;
                                const ABaseReg: string); override;
    procedure ArcPopNestedBase; override;
    procedure EmitWeakClearAt(AOffset: Integer;
                              const ABaseReg: string); override;
    procedure EmitReleaseSlotAt(AType: TTypeDesc; AOffset: Integer;
                                const ABaseReg: string;
                                AZero: Boolean); override;
    procedure EmitRetainSlotAt(AType: TTypeDesc; AOffset: Integer;
                               const ABaseReg: string); override;
    procedure ArcEnterArrayWalk(const ABaseReg: string); override;
    procedure ArcArrayElemAddr(AByteOffset: Integer); override;
    function  ArcArrayElemReg: string; override;
    procedure ArcLeaveArrayWalk; override;
    { Emit all class/record method definitions for the given type decls plus
      the supplied generic-instance lists. }
    procedure EmitClassMethods(ATypeDecls: TObjectList;
                               AGenericInstances: TObjectList;
                               AGenericRecordInstances: TObjectList;
                               AGenericMethodInstances: TObjectList);

    { Resolve a class/interface name to its assembly symbol form, adding the
      unit prefix when the type is defined in a non-system unit.  Mirrors the
      QBE backend's ClassSymName logic. }
    function ClassSymName(const AClassName: string): string;
    { Allowlist + dot-collapse owner→prefix core, shared by ClassSymName (name
      based) and ClassSymNameForDecl (emitting-unit based). }
    function ClassOwnerPrefix(const AOwner: string): string;
    { Owner-correct class-symbol suffix for a type DEFINITION, keyed on the unit
      currently being emitted (cross-unit last-wins safe). }
    function ClassSymNameForDecl(ATypeDecl: TTypeDecl): string;
    { Emit a property accessor (getter/setter) call.  The receiver instance
      must already be in %rdi.  When AVSlot >= 0 the accessor is virtual and
      the call dispatches through the vtable so an overridden accessor is
      reached; otherwise it is a static call to <ClassSymName>_<method>.  The
      slot is computed by the semantic pass (PropAccessorVSlot).  Mirrors
      EmitPropAccessorCall in the QBE backend. }
    procedure EmitPropAccessorCallNative(const AOwnerType, AMethod: string;
      AVSlot: Integer);
    function IntfTypeInfoName(const AIntfName: string): string;
    { True when AName is a captured outer-scope variable in the current
      nested function (accessed via an implicit pointer param). }
    function IsCaptured(const AName: string): Boolean;
    { Load a variable's base (address or stored value) into ADstReg, handling
      local / global / nested-captured variables uniformly. }
    procedure EmitVarBaseToReg(const AName: string; AWantAddress: Boolean;
                               const ADstReg: string);
    { True when AName is a slot in the current function frame. }
    function IsLocal(const AName: string): Boolean;
    { The AT&T operand addressing AName: "-N(%rbp)" for a frame local,
      "name(%rip)" for a global. }
    function VarOperand(const AName: string): string;
    procedure EmitLeaqGlobal(const AName: string; const ADstReg: string);
    { Load the ADDRESS of a named variable into ADstReg, whether it is a stack
      local (leaq off %rbp) or a global (PC-relative, or TLS via EmitLeaqGlobal
      for a threadvar).  The local-or-global address-of-base selector that
      recurs across the field-access and method-receiver ladders. }
    procedure EmitVarAddr(const AName: string; const ADstReg: string);
    { Operands for the two halves of an interface fat pointer.  Locals occupy
      a contiguous 16-byte slot (obj at the slot base, itab 8 bytes above);
      globals are two separate .data labels, AName + '_obj'/'_itab'. }
    function IntfObjOperand(const AName: string; AIsGlobal: Boolean): string;
    function IntfItabOperand(const AName: string; AIsGlobal: Boolean): string;
    { Push the (itab, obj) pair of a named interface ident source — itab
      first so obj ends on top; leaves obj in %rax for the ARC retain that
      follows.  Handles the sret interface Result, whose slot holds a
      POINTER to the caller's 16-byte buffer rather than the fat pointer
      itself (IntfObjOperand alone would push that pointer as the obj). }
    procedure PushIntfIdentPair(AIdent: TIdentExpr);
    { Lower one interface method call (TFieldAccessExpr.IsInterfaceCall or a
      TMethodCallExpr/Stmt whose ResolvedClassType is tyInterface): load obj +
      itab, index the itab by method slot, call the loaded pointer with obj as
      Self and AArgs after it.  Result (if any) left in %rax/%xmm0.

      The receiver is normally a named interface local/global (AObjName, split
      _obj/_itab slots).  When AObjExpr is a non-nil interface-typed
      TFieldAccessExpr (the receiver is an interface stored in a record/class
      field, e.g. H.G.Greet()), obj/itab are loaded from that field's contiguous
      fat pointer instead and AObjName is ignored. }
    procedure EmitInterfaceCall(const AObjName: string; AIsGlobal: Boolean;
                                AIsVarParam: Boolean;
                                AIntf: TInterfaceTypeDesc;
                                const AMethName: string; AArgs: TObjectList;
                                AObjExpr: TASTExpr = nil;
                                ADiscardIntfRet: Boolean = False);
    procedure EmitInterfaceFieldCall(AFld: TFieldInfo; AIntf: TInterfaceTypeDesc;
                                const AMethName: string; AArgs: TObjectList;
                                ADiscardIntfRet: Boolean = False);
    { Emit typeinfo / itab / impllist blocks for interfaces and the classes
      that implement them.  Mirrors the QBE backend's EmitInterfaceDefs. }
    procedure EmitInterfaceDefs(ATypeDecls: TObjectList;
                                AGenericInstances: TObjectList;
                                AGenericIntfInstances: TObjectList;
                                ASymTable: TSymbolTable);
    { Lower an assignment whose LHS is interface-typed.  Handles the four RHS
      forms: as-cast (T as IFoo via _GetItab), direct class->interface (static
      itab), interface->interface copy, and := nil.  Strong references only;
      weak interface refs are deferred. }
    procedure EmitInterfaceAssign(AAsgn: TAssignment);
    { Store an interface expression into a record/class field's contiguous
      16-byte fat pointer (obj at ABaseReg+AOffset, itab at +8).  ABaseReg is an
      AT&T register operand (e.g. '%rcx') holding the record/object base address;
      it is copied into a callee-saved register internally so it survives the
      ARC calls.  AIntfType is the destination's declared interface type, needed
      to name the static itab when the source is a class.  Handles a class source
      (obj + static $itab_<Class>_<Interface>) and an interface source (copy
      obj+itab), retaining the new obj and releasing the old. }
    procedure EmitInterfaceToFieldSlotsAt(AExpr: TASTExpr;
      const ABaseReg: string; AOffset: Integer; AIntfType: TTypeDesc);
    { Compute the address of an interface-typed FIELD's contiguous fat pointer
      (obj at the address, itab at +8) into ADstReg (an AT&T register operand
      such as '%r15').  Handles the receiver shapes a TFieldAccessExpr can take:
      implicit-Self field, class-access (H.G), var-param/record receiver, and
      a nested receiver expression (FA.Base).  ADstReg must be free to clobber;
      callers that need it across calls pick a callee-saved register. }
    procedure EmitInterfaceFieldAddr(AFA: TFieldAccessExpr; const ADstReg: string);
    { Leave the address of an interface element of a static array in ADstReg. }
    procedure EmitIntfStaticElemAddr(ASub: TStringSubscriptExpr;
                                     const ADstReg: string);
    { As EmitIntfStaticElemAddr but for a DYNAMIC or OPEN array: the base is the
      heap data pointer (EmitExprToEax of the array), scaled by index * 16 with
      NO LowBound.  Leaves the element fat-pointer address in ADstReg. }
    procedure EmitIntfDynElemAddr(ASub: TStringSubscriptExpr;
                                  const ADstReg: string);
    { True when AMethName resolves to an abstract slot on ARec (the itab entry
      must then point at _AbstractMethodError). }
    function IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                   const AMethName: string): Boolean;
    { True when the class or any ancestor implements an interface. }
    function ClassOrAncestorImplements(AClassRT: TRecordTypeDesc): Boolean;
    { Native label for a class's implementation of an interface method,
      resolved via the vtable (inherited + overridden both work). }
    function ItabMethodRefNative(AClassRT: TRecordTypeDesc;
      ATD: TTypeDecl; const AMethName: string;
      ATypeDecls: TObjectList): string;
    { Load an integer-family value from AOperand into %rax, extended to 64
      bits per AType (sign/zero-extend by width and signedness). }
    procedure EmitLoadVar(const AOperand: string; AType: TTypeDesc);
    { EmitLoadVar generalised to any destination register pair (64-bit name +
      32-bit sub-view), so a trivial RHS operand can load straight into %rcx
      without disturbing the LHS value in %rax. }
    procedure EmitLoadVarToReg(const AOperand: string; AType: TTypeDesc;
      const AReg64, AReg32: string);
    { Materialise an integer immediate into a register using the shortest
      correct form: movl for [0, 2^31), movq (sign-extended imm32) for
      negative int32-range values, movabsq only for true 64-bit values. }
    procedure EmitImmToReg(AValue: Int64; const AReg64, AReg32: string);
    { True when AExpr is a compile-time integer value (int literal, integer
      const ident, char-coerced single-char literal, nil); returns it. }
    function  TryGetImmValue(AExpr: TASTExpr; out AValue: Int64): Boolean;
    { Trivial-RHS operand emission: when AExpr is an immediate or a plain
      scalar local/global/param load with no side effects and no use of
      %rax, load it directly into %rcx and return True.  Returning False
      means the caller must fall back to the push/pop evaluation bracket. }
    function  TryEmitOperandToRcx(AExpr: TASTExpr): Boolean;
    { Store the integer-family value currently in %rax into AOperand, using
      the right-width register sub-view for AType. }
    procedure EmitStoreVar(const AOperand: string; AType: TTypeDesc);
    { Reserve an 8-byte-aligned frame slot for AName:AType, advancing AOffset. }
    procedure AddSlot(const AName: string; AType: TTypeDesc;
                      var AOffset: Integer);
    { Build FFrame for a function: assign offsets to params, Result, locals. }
    procedure BuildFrame(ADecl: TMethodDecl);
    { Tear down the current frame. }
    procedure ClearFrame;

    procedure EmitProgram(AProg: TProgram); override;
    procedure EmitUnit(AUnit: TUnit); override;
    procedure NoteDepInitUnit(const AUnitName: string;
      AHasInit: Boolean); override;
    procedure NoteDepFiniUnit(const AUnitName: string;
      AHasFini: Boolean); override;
    procedure FinalizeEmit; override;
    { Emit a standalone procedure/function definition.  AExported controls
      whether the symbol gets .globl visibility (True by default).  In
      monolithic compilation, implementation-section helpers pass False so
      their labels stay local and do not collide with the RTL archive. }
    procedure EmitFunctionDef(ADecl: TMethodDecl; AExported: Boolean);
    { Spill incoming arg register AIdx into a param slot at AType's width. }
    procedure EmitSpillArg(AIdx: Integer; const AOperand: string;
                           AType: TTypeDesc);
    { Lower one statement. }
    procedure EmitStmt(AStmt: TASTStmt);
    { The real statement emitter; EmitStmt wraps it to flush statement-scoped
      deferred class releases (BUG-003 native half) at leaf boundaries. }
    procedure EmitStmtBody(AStmt: TASTStmt);
    { Lower every statement in AList (a TObjectList of TASTStmt) in order — the
      compound-body inline idiom used for try/finally/except bodies, loop
      bodies, the program block, and unit init sections.  Nil AList is a no-op. }
    procedure EmitStmtList(AList: TObjectList);
    { Given a static-array element index already in %rax, scale it to a byte
      offset: subtract the (non-zero) low bound, then multiply by the element
      size.  The read-path subscript sites all spell this the same way. }
    procedure EmitStaticElemScale(ASAT: TStaticArrayTypeDesc);
    { After an sret interface call whose argument hoist left AHoistTotal bytes
      of hoist region BELOW the 16-byte return buffer at (%rsp): reclaim the
      hoist region and leave the fat pointer (obj, itab) re-pushed at (%rsp) so
      the caller's `fat pointer at (%rsp)` contract holds.  No-op when
      AHoistTotal is 0 (nothing was hoisted, buffer already at the top). }
    procedure EmitSretBufferSlideDown(AHoistTotal: Integer);
    { Lower a Write/WriteLn call (ANewline = WriteLn). }
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    { Lower a for loop. }
    procedure EmitForStmt(AFor: TForStmt);
    { Lower a for-in loop.  Dispatches to one of five strategies depending on
      the boolean flags set by the semantic analyser: static array, dynamic
      array, string byte-iteration, set bit-scan, or class enumerator. }
    procedure EmitForInStmt(AStmt: TForInStmt);
    { Lower a case statement.  Linear comparison chain, not a jump table. }
    procedure EmitCaseStmt(AStmt: TCaseStmt);
    { Emit the element-to-loop-variable assignment for index-based for-in
      paths.  Handles ARC (string/class AddRef/Release) and width-correct
      stores.  AElemInRax is True when the element value is already in %rax. }
    procedure EmitForInAssignElem(AStmt: TForInStmt);
    { Copy an aggregate array element (record / inline array / jumbo set) into
      the for-in loop variable by value.  %rax holds the element address on
      entry.  Records go through retain/release + memcpy so managed fields are
      ref-counted (issue #169); a scalar load would truncate to 8 bytes. }
    procedure EmitForInAggAssignElem(AStmt: TForInStmt;
      AElemType: TTypeDesc; AElemSize: Integer);
    { Count all try/finally and try/except statements nested inside AStmt
      (recursively) to pre-allocate exc frame slots in BuildFrame. }
    function CountTryStmts(AStmt: TASTStmt): Integer;
    function CountForStmts(AStmt: TASTStmt): Integer;
    { Unwind exception frames from FExcDepth down to ATargetDepth+1.
      For try/finally frames, emits the finally body inline.
      For try/except frames, only calls _PopExcFrame. }
    procedure EmitExcUnwind(ATargetDepth: Integer);
    { Emit the shared try-frame entry sequence: take the next pre-allocated
      512-byte exc-frame slot, _PushExcFrame, bump FExcDepth, push AFinallyBody
      onto FFinallyStack (nil for a try/except frame — keeps the stack index-
      aligned with FExcDepth), then _blaise_setjmp; branch to ALblExc on the
      longjmp return (eax<>0) or fall through to ALblTry.  Shared verbatim by
      both EmitTryFinallyStmt and EmitTryExceptStmt. }
    procedure EmitTryFramePrologue(AFinallyBody: TCompoundStmt;
      const ALblExc, ALblTry: string);
    { Emit the shared frame-pop bookkeeping triplet: _PopExcFrame, Dec(FExcDepth),
      drop the FFinallyStack top.  The Dec and the Delete must always travel with
      the pop, so they are emitted together here. }
    { Lazily allocate a 512-byte exception-frame slot the body needs beyond
      BuildFrame's pre-count.  Safe because the prologue's frame-reserve subq
      is emitted after the body (see EmitFunctionDef). }
    procedure EnsureExcFrameSlot(AIndex: Integer; const AName: string);
    procedure EmitPopExcFrame;
    { Lower try/finally. }
    procedure EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
    { Lower try/except. }
    procedure EmitTryExceptStmt(AStmt: TTryExceptStmt);
    { Lower raise / bare raise. }
    procedure EmitRaiseStmt(AStmt: TRaiseStmt);
    { Allocate stack storage for an inline array literal [a,b,...], fill each
      element, and leave the base pointer in %rax.  Returns the number of bytes
      allocated on the stack (caller must addq that amount after the call). }
    function EmitOpenArrayLiteral(ALit: TArrayLiteralExpr): Integer;
    function EmitConstArrayLiteral(ALit: TArrayLiteralExpr): Integer;
    { Emit a direct call to a user procedure/function; result (if any) in %eax.
      ADecl is the callee's declaration (needed for var/out param handling);
      nil for type-cast calls. }
    procedure EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                       AArgs: TObjectList);
    { Emit a call to a record-returning function using the sret convention:
      ASretAddr is the AT&T operand for the destination buffer (already allocated
      by the caller), passed as the hidden first integer argument in %rdi.
      When ASretIsIndirect is True the operand holds a *pointer* to the buffer
      (sret forwarding from an outer sret function) and must be loaded with movq
      instead of leaq. }
    procedure EmitSretCall(const AFuncSym: string; ADecl: TMethodDecl;
                           AArgs: TObjectList; const ASretAddr: string;
                           ASretIsIndirect: Boolean);
    { Integer-register slot count of an sret call's explicit args (interface = 2). }
    function  SretUserSlots(ADecl: TMethodDecl; AArgs: TObjectList): Integer;
    { True when AExpr is a record-returning function or method call. }
    function  IsNativeRecordCall(AExpr: TASTExpr): Boolean;
    { True when AExpr is a record-method call whose receiver is exactly the
      variable AName/AIsGlobal — i.e. M := M.Method(...) would have the sret
      destination alias Self.  Such an assignment must route the result through
      a fresh temporary first. }
    function  RecordCallReceiverIsVar(AExpr: TASTExpr;
                                      const AName: string;
                                      AIsGlobal: Boolean): Boolean;
    { True when a call's sret destination variable AName/AIsGlobal is also read
      by the call itself — as the receiver of a record method
      (M := M.Method(...)) or as any bare-identifier ARGUMENT
      (X := F(X), X := F(N, X), X := Obj.M(X)).  EmitSretCall zeroes the
      destination BEFORE evaluating the argument list, so an aliased argument
      reaches the callee already cleared; such an assignment must route the
      result through a fresh stack temporary and memcpy it in afterwards.

      Matching is by NAME + SCOPE only — deliberately conservative, no alias
      analysis.  Biasing towards True is always correct (the temp path is
      merely slower), so an ambiguous case such as a local shadowing a global
      of the same name reports True. }
    function  CallAliasesDestVar(AExpr: TASTExpr;
                                 const AName: string;
                                 AIsGlobal: Boolean): Boolean;
    { Sret a record-returning call (function or method) into ADest. }
    procedure EmitRecordCallSretAt(AExpr: TASTExpr; const ADest: string;
      AIndirect: Boolean = False);
    { Sret call for a TFuncCallExpr: routes an implicit-Self method through the
      vtable-aware method-sret emitter, a free function through EmitSretCall. }
    procedure EmitFuncCallSret(AFC: TFuncCallExpr; const ADest: string;
      AIndirect: Boolean);
    procedure EmitMethodSretCall(ACall: TMethodCallExpr; const ASretAddr: string;
                                 ASretIsIndirect: Boolean;
                                 AForceStatic: Boolean = False);
    { Sret an inherited record return into ADest: an implicit-Self call
      dispatched statically to the parent's symbol.  Reuses EmitMethodSretCall
      via a transient implicit-Self method node so the sret pointer is threaded
      the same way as any other record-returning call. }
    procedure EmitInheritedRecordSret(MD: TMethodDecl; AArgs: TObjectList;
                                      const AName, ADest: string;
                                      ADestIsIndirect: Boolean);
    { Free a record-call-receiver buffer materialised by EmitMethodSretCall. }
    procedure EmitMethodSretRecvCleanup(ABytes: Integer);
    { Emit the base ADDRESS of a NAMED LOCAL record into AReg (e.g.
      '%rcx', '%rax').  Normally a stack value record, so leaq the slot.
      The one exception is the sret-function Result: its frame slot holds
      the caller's buffer POINTER, not the record, so it must be loaded
      with movq.  Every field-access receiver ladder routes its
      "IsLocal(RecordName)" leaf through here so the sret-Result
      indirection is decided in ONE place (the implicit-Result analogue of
      the implicit-Self field-access symmetry rule). }
    procedure EmitLocalRecordBase(const AName, AReg: string);
    { Compute the address of a record/class field into %rcx.  Handles
      local/global records, class fields, var-param records, chained
      access (Base <> nil), and implicit-Self fields. }
    procedure EmitFieldAddrToRcx(AFA: TFieldAccessExpr);
    { Emit the function epilogue for a reg-return record: load the local
      Result buffer into the SysV return registers (rax/rdx/xmm0/xmm1)
      according to AClass, then the caller will ret.  Only called when
      AClass <> rcSret.  VarOperand('Result') is the buffer address. }
    procedure EmitRecordReturnEpilogue(ARec: TRecordTypeDesc;
                                       AClass: TRecReturnClass);
    { Caller-side: call a record-returning function whose return class is
      AClass (non-sret).  The function is called, the return register(s)
      are stored into ADestAddr.  Args must already be set up in the SysV
      integer registers (%rdi onwards for free functions, %rsi onwards for
      methods with Self in %rdi).  Only handles the return-capture part. }
    procedure EmitRecordRegReturnCapture(const ADestAddr: string;
                                         ARec: TRecordTypeDesc;
                                         AClass: TRecReturnClass;
                                         AIsIndirect: Boolean);
    { Emit a call to a function that returns an interface via sret.  The 16-byte
      buffer (obj+itab) is left on the stack; caller is responsible for loading
      the slots and cleaning up (addq $16, %rsp). }
    procedure EmitIntfSretCall(ACall: TFuncCallExpr);
    { Interface-method call (itab dispatch) RETURNING an interface: the callee
      writes the fat pointer through a hidden sret first arg (%rdi), with the
      receiver obj as the second arg (%rsi).  Same caller contract as
      EmitIntfSretCall: the 16-byte buffer is left at (%rsp); the caller loads
      the slots and pops it (addq $16, %rsp). }
    procedure EmitIntfSretMethodCall(ACall: TMethodCallExpr);
    { Interface-method call (itab dispatch) RETURNING a RECORD: dispatch through
      the itab and write the record result into the caller-supplied ADest,
      honouring the full record-return ABI (hidden sret pointer for a
      memory-class record; register capture for a register-class one).  Mirrors
      the QBE EmitIntfSretDispatch helper.  ADestIsIndirect: ADest holds a
      pointer to the destination buffer (var/out / Result), not the buffer. }
    procedure EmitIntfRecordSretDispatch(ACall: TMethodCallExpr;
                                         const ADest: string;
                                         ADestIsIndirect: Boolean);
    { Class-receiver method call RETURNING an interface (Obj.Make() where Obj
      is class-typed): sret hidden first arg (%rdi), receiver in %rsi, static
      or vtable dispatch from the receiver's class.  Same caller contract as
      EmitIntfSretCall: the 16-byte buffer is left at (%rsp); the caller loads
      the slots and pops it (addq $16, %rsp). }
    procedure EmitClassIntfSretMethodCall(ACall: TMethodCallExpr);
    { Indirect call: load a bare function pointer from APtrOperand (an AT&T
      memory operand, e.g. "-8(%rbp)"), set up args as for EmitCall, then
      dispatch via callq *%r10.  AProcType supplies the param list for
      var-param detection; result (if any) is left in %rax. }
    procedure EmitCallIndirect(const APtrOperand: string;
                               AProcType: TProceduralTypeDesc;
                               AArgs: TObjectList);
    { Call a procedural-typed CLASS FIELD through a receiver
      (Self.FFn(args)).  The function pointer lives at [instance + Offset],
      which is not a %rbp/%rip-relative operand, so this cannot reuse
      EmitCallIndirect/EmitMethodPtrCall.  Mirrors the interface-dispatch
      shape instead: push args, then load the (call-free) receiver and the
      field's code pointer.  AResultType nil = statement call (no result
      narrowing).  Receiver shapes: a named var/global via AObjectName, a
      var/out param (AIsVarParam), or a call-free AObjExpr (an identifier or
      field access). }
    procedure EmitProcFieldCall(AObjExpr: TASTExpr; const AObjectName: string;
                                AIsVarParam: Boolean; AFieldInfo: TFieldInfo;
                                AProcType: TProceduralTypeDesc;
                                AArgs: TObjectList; AResultType: TTypeDesc);
    { Evaluate an integer expression; result left in %rax (64-bit-extended). }
    procedure EmitExprToEax(AExpr: TASTExpr);
    procedure EmitByteRhsToEax(AExpr: TASTExpr);
    { Evaluate a float expression (tyDouble or tySingle); result left in %xmm0.
      Binary ops: left → push onto int stack via subq/movsd, right → %xmm0,
      pop left → %xmm1, then addsd/subsd/mulsd/divsd. }
    procedure EmitExprToXmm0(AExpr: TASTExpr);
    function EmitFloatBuiltin(FC: TFuncCallExpr): Boolean;
    { Load a float (Double or Single) from AOperand into %xmm0. }
    procedure EmitLoadFloat(const AOperand: string; AType: TTypeDesc);
    { Store %xmm0 into AOperand at the float type's width. }
    procedure EmitStoreFloat(const AOperand: string; AType: TTypeDesc);
    procedure EmitXmm0WidthAdjust(ASrcType: TTypeDesc; AWantSingle: Boolean);
    { The integer-family type to use when loading the value of AExpr: the
      recorded slot type for a known local/global (authoritative), otherwise
      the node's ResolvedType. }
    function IntExprType(AExpr: TASTExpr): TTypeDesc;
    { Re-truncate and re-extend the value in %rax to AType's width and
      signedness — used after a call (whose ABI return is 32-bit) and to
      implement an explicit narrowing/widening type cast. }
    procedure EmitNarrowToType(AType: TTypeDesc);
    { Inc(x)/Dec(x) with support for simple variables, implicit-Self fields,
      var params, and field-access expressions. }
    procedure EmitLValueSlotAddr(AExpr: TASTExpr);
    { --- OPDF debug-fact hooks (no-ops when facts collection is off) --- }
    procedure SetDebugFacts(AFacts: TDbgFacts); override;
    procedure DbgBeginFunc(const ASymbol: string);
    procedure DbgRecordSlot(const AName: string; AType: TTypeDesc; AOffset: Integer);
    procedure DbgMarkParams(ADecl: TMethodDecl);
    function OuterVarType(const AName: string): TTypeDesc;
    procedure DbgStmtLabel(AStmt: TASTStmt);
    procedure DbgEndFunc;
    procedure EmitIncDec(ACall: TProcCall);
    procedure EmitIncDecAddrOp(IsInc, IsWide, HasStep: Boolean;
      AElemType: TTypeDesc);
    { BUG-003 native half: statement-scoped deferred class-release.
      DeferNativeClassRelease spills the pointer currently in %rax to the next
      free _pendrel slot and returns True; returns False (caller keeps its own
      handling) when all PENDREL_SLOTS are in use.  FlushNativePendingReleases
      releases every deferred base whose slot index is >= AMark and resets the
      count, called by EmitStmt at leaf-statement boundaries AFTER the store. }
    function  DeferNativeClassRelease: Boolean;
    procedure FlushNativePendingReleases(AMark: Integer);
    { Evaluate a boolean condition and branch: if true jump ATrueLabel, else
      fall through to AFalseLabel (a jmp is emitted to it). }
    procedure EmitCondBranch(AExpr: TASTExpr;
                             const ATrueLabel, AFalseLabel: string);
    { Like EmitCondBranch, but flushes any class-field-on-transient bases the
      condition deferred, so the borrowed field value is consumed and its
      transient released within this evaluation (BUG-049).  Materialises the
      condition to a 0/1 in %rax (rather than fusing compare+branch) so the
      flush can sit between the eval and the branch; used at loop conditions
      (per iteration) and the if condition. }
    procedure EmitCondBranchFlushed(AExpr: TASTExpr;
                             const ATrueLabel, AFalseLabel: string);
    { Emit a TMethodCallExpr (class method call, with explicit receiver).
      Loads Self into %rdi and evaluates scalar args; result in %rax/%xmm0. }
    procedure EmitMethodCallExpr(ACall: TMethodCallExpr);
    { Implicit-Self regular (non-sret) method call whose register slots
      (Self + args) exceed 6: evaluate args into a stack slot block (slot 0 =
      Self), load the first six into registers and spill the rest, then dispatch
      (vtable-aware) with Self in %rdi.  Mirrors EmitMethodCallExpr's >6-slot
      branch; the implicit-Self expression path (EmitExprToEax) lacked it. }
    procedure EmitImplicitSelfCallOverflow(MD: TMethodDecl;
      AArgs: TObjectList; const ASym: string);
    { Emit a TMethodCallStmt (class method call in statement position). }
    procedure EmitMethodCallStmt(ACall: TMethodCallStmt);
    { Emit a TInheritedCallStmt (`inherited Method[(args)]`).  Direct static
      dispatch to the parent method (no vtable); Self is the current method's
      Self; a value-returning parent stores its result into the Result slot. }
    procedure EmitInheritedCall(ACall: TInheritedCallStmt);
    { Shared static-dispatch sequence (Self + args + direct callq); result in
      %rax/%xmm0 on return.  Used by both inherited forms (stmt + expr). }
    procedure EmitInheritedCallSeq(MD: TMethodDecl; AArgs: TObjectList;
      const AName: string);
    { Evaluate one method-call argument and push it onto the stack.  Scalar and
      var/out params push one value; interface params push two (itab first, then
      obj — reversed so the pop loop restores them in the correct register order). }
    procedure EmitMethodArgPush(APar: TMethodParam; AArg: TASTExpr);
    procedure EmitVarArgAddrToRax(AArg: TASTExpr);
    { %rax holds the address of an array FIELD (static: inline storage;
      dyn/open: the data-pointer slot).  Apply AFAE.PropIndexExpr — loading
      the data pointer for a dyn/open array and adding (idx - LowBound) *
      ElemSize — leaving the ELEMENT address in %rax.  The index expression
      may clobber %rax, so the base is parked on the stack across it.  Shared
      by the var/out l-value path (BUG-20260723-vararg-field-array-elem-subscript-drop). }
    procedure EmitFieldArrayElemAddrToRax(AFAE: TFieldAccessExpr);
    { Pre-pass for call arguments (phase A of the call protocol).  Hoists
      three argument kinds into a stack region BELOW the argument slots,
      recording one (depth, kind) pair per argument (-1/akNone when not
      hoisted):

        akOALit      — open-array literals: EmitOpenArrayLiteral moves %rsp,
                       so the element block is emitted here and its data
                       pointer saved behind it.
        akRecCall    — record-returning call arguments: the callee's sret
                       buffer is materialised here (EmitExprToEax leaves it
                       at %rsp) and the buffer pointer saved.  Without the
                       hoist the buffer lands between pushed argument slots
                       and the popq sequence reads buffer words.
        akStrPin /
        akStrConsume — const-string arguments needing caller protection
                       (see blaise.codegen.arcshapes.TConstArgMode): the
                       value is evaluated and saved; pin mode AddRefs it.
                       Param const-ness comes from AParams (TMethodParam) or
                       AProcParams (TProcParamInfo); when AKnownSig is False
                       (interface dispatch) every string-typed argument is
                       protected by shape, with AVarFlags ('1'/'0' comma
                       list) marking var positions to skip.

      Returns the region bytes.  The call site reloads hoisted values in its
      arg loop and finishes with EmitHoistEpilogue AFTER the call. }
    { Emit override: tracks FSPDepth across the emitted stream and wraps any
      callq at a misaligned tracked depth in a subq $8/addq $8 pad pair (see
      the FSPDepth field comment for the full rationale). }
    procedure Emit(const ALine: string); override;
    { The pre-promotion Emit body: peephole + stack-depth tracking +
      call-site alignment.  Emit itself first applies PromoRewrite. }
    procedure EmitTracked(const ALine: string);
    { Emit the held-back pushq (peephole window) without re-tracking its
      stack-depth contribution (applied when it was pended). }
    procedure FlushPendingPush;
    { True for types safe to register-promote: unmanaged scalars only.
      Managed types stay in slots (ARC release walks read them). }
    function  PromoEligibleType(ATy: TTypeDesc): Boolean;
    { Pick up to two promotion candidates for ADecl (params first, then
      Result, then locals in declaration order) into FPromoVars.
      False when the function is ineligible (debug build, try stmts,
      nostackframe) or no candidate exists. }
    function  SelectPromotions(ADecl: TMethodDecl; AMark: Integer): Boolean;
    { SelectPromotions helper: append AName to the candidate lists when it
      is promotable, with its pass-1 slot-traffic count.  A plain method
      (not a nested proc): the release bootstrap binary miscompiles
      method calls on captured class locals — the very bug fixed in this
      source — so the compiler's own source must not use that shape until
      a fixed bootstrap binary exists (teach-then-use). }
    procedure ConsiderPromo(const AName: string; ATy: TTypeDesc;
      AMark: Integer; ACandNames: TStringList; ACandCounts: TList<Integer>);
    { Rewrite one instruction line for register-resident operands:
      width-suffixed memory forms map onto the matching %r14/%r15
      sub-register.  Raises on any form that would need an address. }
    function  PromoRewrite(const ALine: string): string;
    { The per-function emission tail (symbol, frame, prologue, body,
      epilogue) — extracted from EmitFunctionDef so the two-pass driver
      can run it twice. }
    procedure EmitFunctionCore(ADecl: TMethodDecl; AExported: Boolean);
    { Prologue init for a promoted param that arrived on the STACK (7th+
      integer arg): load the caller-pushed slot into the register.  No-op
      for locals, Result, and register-passed params. }
    procedure PromoInitStackParam(const AName, AReg: string);
    { Inline a qualifying direct call.  ADecl/AArgs are the callee and the
      call-site arguments; AWantResult loads the Result slot into %rax or
      %xmm0 (per return type) at the end.  False = emit a normal call. }
    function  TryEmitInlineCall(ADecl: TObject; AArgs: TObjectList;
      AWantResult: Boolean): Boolean;
    { Parse the immediate of a `subq $N, %rsp` / `addq $N, %rsp` line and
      apply it to FSPDepth (ASign = +1 for subq, -1 for addq).  Lines whose
      destination is not %rsp are ignored. }
    procedure TrackRspAdjust(const ALine: string; ASign: Integer);
    { Bytes for a fresh SysV stack-argument region holding ASlots 8-byte
      slots, padded (+8) when needed so that a call emitted after
      `subq $Result, %rsp` (with no further %rsp movement) sees a
      16-byte-aligned %rsp.  Used by every >6-slot overflow path: copying
      the overflow slots into such a region makes the call site aligned by
      construction, so the Emit wrap pad (which would shift genuine stack
      arguments) never fires for those calls. }
    function AlignFreshBytes(ASlots: Integer): Integer;
    function EmitArgHoist(AParams: TObjectList; AProcParams: TObjectList;
                          AKnownSig: Boolean; const AVarFlags: string;
                          AArgs: TObjectList;
                          ADepths: TList<Integer>; AKinds: TList<Integer>): Integer;
    { Phase C — post-call epilogue: releases pinned/consumed const-string
      values and the managed fields of hoisted record temporaries, preserving
      the call's return registers (%rax/%rdx/%xmm0/%xmm1), then reclaims
      ATotal + ABase bytes when AReclaim is True.  ABase = extra bytes (e.g.
      overflow-arg cleanup) between %rsp and the hoist region at this point. }
    procedure EmitHoistEpilogue(AArgs: TObjectList; ADepths: TList<Integer>;
                                AKinds: TList<Integer>; ATotal, ABase: Integer;
                                AReclaim: Boolean);
    { Shape classification for a const-string argument — mirror of the QBE
      backend's ConstArgMode.  APinPlainLocals forces plain locals to pin
      (var/out string sibling param, or unknown parameter types). }
    function  ConstStrShape(AArg: TASTExpr; APinPlainLocals: Boolean): TConstArgMode;
    { Built-in call with ONE string argument (FileAge, Trim, StrToInt, ...):
      evaluate AArg, call ARtl with it in %rdi, and release the argument temp
      after the call when it is an owned (+1) transient (function/method/
      getter/built-in result — see ArcBuiltinStrArgOwnsRef), preserving the
      call's result (%rax, or %xmm0 when AResultXmm).  Without the release,
      one string leaks per call. }
    procedure EmitBuiltinStrCall1(AArg: TASTExpr; const ARtl: string;
                                  AResultXmm: Boolean = False);
    { Built-in call with TWO arguments in %rdi/%rsi where either may be an
      owned string transient (Pos, SameText, RenameFile, string '='/compare
      operators, ...).  AStr0/AStr1 pass nil for a non-string operand slot
      (its value still travels through the same stack slot untouched). }
    procedure EmitBuiltinStrCall2(AArg0, AArg1: TASTExpr; const ARtl: string);
    { Dispose a string transient parked in stack slot ASlot (an operand like
      '(%rsp)' or '8(%rsp)').  rc=1 owned temps (user-call results) take one
      _StringRelease; rc=0 unowned temps (built-in/concat results — see
      ArcExprIsUnownedStrTransient) take _StringAddRef + _StringRelease,
      because a bare release would drive the count to -1 = IMMORTAL and the
      buffer would silently leak.  Clobbers %rdi only. }
    procedure EmitStrDisposeFromSlot(AArg: TASTExpr; const ASlot: string);
    { True when AArg is a record-returning function/method call (its
      evaluation materialises an sret buffer on the stack). }
    function  IsRecCallArg(AArg: TASTExpr): Boolean;
    { Stack bytes the sret buffer of a hoisted record-call argument occupies. }
    function  RecArgBufBytes(AArg: TASTExpr): Integer;
    function  ParamsHaveVarString(AParams: TObjectList): Boolean;
    function  ProcParamsHaveVarString(AProcParams: TObjectList): Boolean;
    { Reads the AIndex'th flag of a MethodParamVarFlagsStr-style '1'/'0'
      comma list; False when out of range or empty. }
    function  VarFlagAt(const AFlags: string; AIndex: Integer): Boolean;
    { Total of the innermost open call frame — used by sret call paths to
      address a dest pointer saved just below the hoist region. }
    function  TopFrameTotal: Integer;
    { Phase B — push the slot(s) for one argument.  Hoisted arguments reload
      their saved value from the phase-A region: the saved slot sits
      (ATotal - ADepth + APushed) bytes above the current %rsp, where
      APushed counts every byte pushed since EmitArgHoist returned. }
    procedure EmitArgPush(APar: TMethodParam; AArg: TASTExpr;
                          ATotal, ADepth, AKind: Integer; var APushed: Integer);
    { Frame-stack wrappers around EmitArgHoist/EmitArgPush for the standard
      push-loop call sites.  BeginCallArgs runs the hoist pre-pass and pushes
      a frame; PushCallArg pushes one argument's slot(s) (AIndex = position in
      the original argument list); EndCallArgs emits the post-call epilogue
      (string releases, record-temp field releases, region reclaim — place it
      where the post-call stack cleanup belongs) and pops the frame. }
    procedure BeginCallArgs(AParams: TObjectList; AArgs: TObjectList);
    procedure PushCallArg(APar: TMethodParam; AArg: TASTExpr; AIndex: Integer);
    procedure EndCallArgs;
    { Return the total number of integer register slots consumed by AParams.
      Most params = 1 slot; interface params = 2 slots (obj + itab); open-array
      params = 2 slots (ptr + high).  Used by pop loops so they count slots, not
      logical argument positions. }
    { Load a class method call's receiver instance pointer into %rax. }
    procedure EmitMethodReceiverToRax(ACall: TMethodCallExpr);
    function CountArgSlots(AParams: TObjectList): Integer;
    { Bounds-checked System V integer-arg-register accessor (raises if > 5). }
    function SysVArg64(AIndex: Integer): string;
    { Consume ASlots pushed arg slots into SysV registers from index ABase,
      spilling any overflow to the stack.  Returns overflow bytes to clean up
      after the call.  Used by the interface/class sret call emitters. }
    function EmitSretRegArgs(ASlots, ABase: Integer): Integer;
    { Float-aware sibling of EmitSretRegArgs for itab dispatch: ASlotClasses
      holds one entry per pushed slot in push order (0 = integer/pointer
      eightbyte, 1 = float eightbyte stored as its 8-byte xmm bit pattern).
      Integer slots consume the SysV integer registers from ABase and spill
      any overflow; float slots consume %xmm0.. and never spill.  Delegates
      to EmitSretRegArgs when no float slot is present, so float-free call
      sites emit unchanged code.  Returns overflow bytes to clean up after
      the call. }
    function EmitIntfRegArgs(ASlotClasses: TList<Integer>;
                             ABase: Integer): Integer;
    { Pop already-pushed method-call arg slots (slot 0 pushed first, on top is
      the last slot) into the System V argument registers, routing float-family
      params to %xmm0.. and everything else to the integer registers starting
      at AIntBase (1 when only Self/%rdi is reserved).  Mirrors EmitCall's SysV
      classification so a Double/Single method or constructor argument lands in
      its xmm register instead of being mis-passed in an integer register. }
    procedure EmitPopMethodArgsToRegs(AParams, AArgs: TObjectList;
      AIntBase: Integer);
    { Append one SysV slot-class entry per logical argument to AList (1 = float
      eightbyte → xmm, 0 = integer/pointer eightbyte → integer register).  Open
      arrays and by-value interfaces occupy two integer slots; a by-value
      Double/Single occupies one xmm slot; everything else is one integer slot.
      The receiver/Self slot is NOT added here — callers prepend it as needed.
      Shared by EmitPopMethodArgsToRegs and EmitMethodOverflowLoad so the
      classification stays single-sourced. }
    procedure BuildArgSlotClasses(AParams, AArgs: TObjectList;
      AList: TList<Integer>);
    { Emit the call for a method whose receiver (Self) is already in %rdi:
      a vtable dispatch when AMD is virtual (VTableSlot >= 0) so the call
      respects polymorphism, otherwise a static callq to AStaticSym.  Used by
      the implicit-Self call paths, which must dispatch identically to an
      explicit Self.Method() call. }
    procedure EmitSelfDispatch(AMD: TMethodDecl; const AStaticSym: string);
    { As EmitSelfDispatch but with Self in an explicit register (e.g. %rsi when
      %rdi holds an sret buffer pointer). }
    procedure EmitSelfDispatchVia(AMD: TMethodDecl;
      const AStaticSym, ASelfReg: string);
    { Float-aware register load + overflow relocation for the >6-slot
      method-family layout.  The caller has stored every arg into a flat region
      whose slot I lives at offset (I+1)*8 (slot 0 is the receiver/Self) and has
      placed Self at 0(%rsp).  This loads slot 0 into %rdi and each arg slot into
      its System V register (integers from %rsi.., floats into xmm0..),
      relocates the integer-overflow slots to the top of AAllocSz and raises
      %rsp to the overflow base, returning the overflow byte count for the
      caller to reclaim after the call.  Float args never overflow (8 xmm regs).
      The store loop must already have written float slots as their 8-byte bit
      pattern (movsd %xmm0). }
    function EmitMethodOverflowLoad(AParams, AArgs: TObjectList;
      AAllocSz: Integer): Integer;
    { Store every logical argument into its 8-byte slot in the >6-slot call
      frame already allocated at (%rsp): slot I goes to (I+1)*8(%rsp) (slot 0 is
      reserved for Self).  Dispatches per arg kind — a hoisted akRecCall buffer
      is reloaded from its hoist depth, a var/out param stores its address, a
      by-value float stores the width-adjusted xmm bit pattern, and a plain
      scalar stores %rax.  AHoistDepths/AHoistKinds are the (depth, kind) vectors
      EmitArgHoist produced; AAllocSz/AHoistTotal frame the akRecCall reload
      offset.  Shared verbatim by every >6-slot method/implicit-Self/metaclass
      call path. }
    procedure EmitArgsToSlots(AArgs, AParams: TObjectList;
      AAllocSz, AHoistTotal: Integer;
      AHoistDepths, AHoistKinds: TList<Integer>);
    { True when the parameter at AIndex is a by-value float-family param (the
      caller must store its slot as an xmm bit pattern, not via %rax). }
    function OverflowArgIsFloat(AParams: TObjectList; AIndex: Integer): Boolean;
    { Emit a method-pointer (of-object) call: load Code from offset 0 and Data
      from offset 8 of the TMethod block at APtrOperand; call Code with Data as
      Self (%rdi) and the remaining args shifted. }
    procedure EmitMethodPtrCall(const APtrOperand: string;
                                AProcType: TProceduralTypeDesc;
                                AArgs: TObjectList);
    { Emit a Format(Fmt, arg1, ...) built-in call via _StringFormatN.
      Builds a temporary args array on the stack: each slot is 16 bytes
      (type tag at [0], value at [8]), matching the QBE backend's layout. }
    procedure EmitFormatCall(AArgs: TObjectList);
  public
    constructor Create(const ATarget: TTargetDesc); override;
    destructor Destroy; override;
  end;

implementation

const
  { SysV AMD64 integer argument registers (32-bit views), in order. }
  SysVArgRegs: array[0..5] of string =
    ('%edi', '%esi', '%edx', '%ecx', '%r8d', '%r9d');
  { Same registers, 64-bit views — used for Int64/UInt64 arguments. }
  SysVArgRegs64: array[0..5] of string =
    ('%rdi', '%rsi', '%rdx', '%rcx', '%r8', '%r9');
  { 8-bit and 16-bit views, for spilling a narrow incoming argument into its
    same-width param slot. }
  SysVArgRegs8: array[0..5] of string =
    ('%dil', '%sil', '%dl', '%cl', '%r8b', '%r9b');
  SysVArgRegs16: array[0..5] of string =
    ('%di', '%si', '%dx', '%cx', '%r8w', '%r9w');

var
  { Process-wide singleton method-pointer return record + its shared Pointer
    leaf type; built lazily by MethodPtrReturnRec and reused by every codegen
    instance.  A `function ... of object` value is a 16-byte [Code; Data]
    aggregate that is ABI-identical to `record Code, Data: Pointer end` — two
    integer eightbytes classify as rcInt2 (rax:rdx) on SysV.  Never mutated
    after creation; intentionally not freed (a single process-lifetime
    constant), mirroring the QBE backend's GMethodPtrRec.  The native names are
    distinct (GNative*) so the two backend units do not collide on the emitted
    global symbol when both are linked into the self-hosting compiler. }
  GNativeMethodPtrRec:  TRecordTypeDesc;
  GNativeMethodPtrLeaf: TTypeDesc;

{ True for an 'of object' method-pointer type or a 'reference to' closure
  type — both are 16-byte [Code; Data] aggregates returned by the same ABI
  as a two-pointer record. }
function IsMethodPtrType(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind = tyProcedural)
            and (TProceduralTypeDesc(AType).IsMethodPtr or
                 TProceduralTypeDesc(AType).IsReference);
end;

{ Lazily-built canonical 16-byte [Code; Data] record for method pointers.
  Returning a canonical record descriptor lets the whole record-return path
  (classify, prologue/epilogue, call-site capture) handle method-pointer
  returns uniformly.  Built once and cached in a unit-level singleton. }
function MethodPtrReturnRec(): TRecordTypeDesc;
begin
  if GNativeMethodPtrRec = nil then
  begin
    GNativeMethodPtrLeaf      := TTypeDesc.Create();
    GNativeMethodPtrLeaf.Kind := tyPointer;
    GNativeMethodPtrLeaf.Name := 'Pointer';
    GNativeMethodPtrRec := TRecordTypeDesc.Create('_BlaiseMethodPtr', tyRecord);
    GNativeMethodPtrRec.AddField('Code', GNativeMethodPtrLeaf);
    GNativeMethodPtrRec.AddField('Data', GNativeMethodPtrLeaf);
  end;
  Result := GNativeMethodPtrRec;
end;

{ The record descriptor governing AType's by-aggregate return ABI: AType itself
  for a real record, the canonical method-pointer record for an 'of object'
  procedural type, else nil.  Mirrors TCodeGenQBE.AggRetRec. }
function AggRetRec(AType: TTypeDesc): TRecordTypeDesc;
begin
  if AType = nil then
    Result := nil
  else if AType.Kind = tyRecord then
    Result := TRecordTypeDesc(AType)
  else if IsMethodPtrType(AType) then
    Result := MethodPtrReturnRec()
  else
    Result := nil;
end;

constructor TOALCallFrame.Create;
begin
  inherited Create();
  Depths := TList<Integer>.Create();
  Kinds := TList<Integer>.Create();
  Total := 0;
  Pushed := 0;
  Args := nil;
end;

destructor TOALCallFrame.Destroy;
begin
  Depths.Free();
  Kinds.Free();
  inherited Destroy();
end;

{ ------------------------------------------------------------------ }
{ Integer-family width / signedness helpers                            }
{ ------------------------------------------------------------------ }

{ Byte width (1/2/4/8) of an integer-family type. Defaults to 4. }
function IntByteSize(AType: TTypeDesc): Integer;
begin
  { nil / unmapped kinds default to pointer width, mirroring the QBE
    backend's 'l' default (QbeTypeOf / PromotedQType).  A nil TypeDesc
    is typically an unresolved forward class reference — loading such a
    field with 4-byte width truncates the pointer. }
  if AType = nil then
  begin
    Exit(8);
  end;
  case AType.Kind of
    tyByte, tyBoolean:                          Result := 1;
    tySmallInt, tyWord:                         Result := 2;
    tyInteger, tyUInt32, tyEnum:                Result := 4;
    tyInt64, tyUInt64,
    tyProcedural, tyPointer, tyPChar, tyClass,
    tyString, tyMetaClass, tyDynArray,
    tyInterface:                                Result := 8;
    tyDouble:                                   Result := 8;
    tySingle:                                   Result := 4;
    tySet:
      if TSetTypeDesc(AType).IsJumbo() then
        Result := TSetTypeDesc(AType).RawSize()   { inline byte-array bitmap }
      else if TSetTypeDesc(AType).BitCount > 32 then
        Result := 8
      else
        Result := 4;
  else
    Result := 8;
  end;
end;

{ True for floating-point types supported in %xmm registers. }
function IsFloatFamily(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind in [tyDouble, tySingle]);
end;

{ True for a JUMBO (>64-member) set: an inline byte-array bitmap aggregate
  (like a record / static array), operated on via the _Set* RTL helpers and
  passed/returned by pointer.  Sets of 64 members or fewer stay register-sized. }
function IsJumboSet(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind = tySet) and
            TSetTypeDesc(AType).IsJumbo();
end;

{ Bitmap byte count of a jumbo set (= ceil(BitCount/8), <= 32). }
function JumboSetNBytes(AType: TTypeDesc): Integer;
begin
  Result := TSetTypeDesc(AType).RawByteSize();
end;

{ Byte size of an sret return buffer: a record's full layout size, or a jumbo
  set's 8-byte-rounded bitmap slot.  Both are returned through the hidden
  first-argument pointer, so both need a caller-allocated buffer of this size. }
function SretRetSize(AType: TTypeDesc): Integer;
begin
  if IsJumboSet(AType) then
    Result := TSetTypeDesc(AType).RawSize()
  else
    Result := TRecordTypeDesc(AType).TotalSize();
end;

{ SysV AMD64 XMM argument registers, in order. }
const
  SysVXmmArgRegs: array[0..7] of string =
    ('%xmm0', '%xmm1', '%xmm2', '%xmm3', '%xmm4', '%xmm5', '%xmm6', '%xmm7');

{ True for unsigned integer-family types. Byte/Word/UInt32/UInt64 are
  unsigned; Boolean and Enum hold non-negative ordinals and so are read
  zero-extended. SmallInt/Integer/Int64 are signed. A small set is a
  bitmask and must load/widen zero-extended — a movslq of a 4-byte set
  with bit 31 set would smear bits 32..63 when it flows into a 64-bit
  set destination (BUG-20260721-qbe-set-into-dynarray-elem review). }
function IsUnsignedInt(AType: TTypeDesc): Boolean;
begin
  if AType = nil then
  begin
    Exit(False);
  end;
  Result := AType.Kind in [tyByte, tyBoolean, tyWord, tyUInt32, tyUInt64,
    tyEnum, tySet];
end;


{ The assembly symbol for a procedure/function.  An `external name '...'`
  binding names a foreign (C/asm) symbol that must be used verbatim — never
  mangled or unit-prefixed (matching the QBE backend's ExternalName handling).
  Otherwise the semantic pass sets ResolvedQbeName for overloaded/mangled names;
  failing that use the source name. }
function FuncSymbolFromDecl(ADecl: TMethodDecl): string;
begin
  if (ADecl <> nil) and ADecl.IsExternal and (ADecl.ExternalName <> '') then
    Result := ADecl.ExternalName
  else if (ADecl <> nil) and (ADecl.ResolvedQbeName <> '') then
    Result := NativeMangle(ADecl.ResolvedQbeName)
  else if ADecl <> nil then
    Result := NativeMangle(ADecl.Name)
  else
    Result := '';
end;

{ One kind code per declared parameter of AMD — third field of every
  published-method table entry, read by the test runner's [TestCase]
  typed dispatch.  Mirrors the QBE backend's MethodParamSig:
    'i' 32-bit-or-smaller ordinal, 'I' Int64/UInt64, 'b' Boolean,
    's' string, 'd' Double/Single (recorded, not dispatchable),
    'x' anything else or var/out/open-array.  '' = parameterless. }
function MethodParamSig(AMD: TMethodDecl): string;
var
  I:   Integer;
  Par: TMethodParam;
begin
  Result := '';
  for I := 0 to AMD.Params.Count - 1 do
  begin
    Par := TMethodParam(AMD.Params.Items[I]);
    if Par.IsVarParam or Par.IsOutParam or Par.IsOpenArray or
       (Par.ResolvedType = nil) then
      Result := Result + 'x'
    else
      case Par.ResolvedType.Kind of
        tyInteger, tyUInt32, tySmallInt, tyWord, tyByte, tyEnum:
          Result := Result + 'i';
        tyInt64, tyUInt64:
          Result := Result + 'I';
        tyBoolean:
          Result := Result + 'b';
        tyString:
          Result := Result + 's';
        tyDouble, tySingle:
          Result := Result + 'd';
      else
        Result := Result + 'x';
      end;
  end;
end;

function FuncSymbolOf(ACall: TFuncCallExpr): string;
begin
  Result := FuncSymbolFromDecl(TMethodDecl(ACall.ResolvedDecl));
  if Result = '' then
    Result := NativeMangle(ACall.Name);
end;

constructor TX86_64Backend.Create(const ATarget: TTargetDesc);
begin
  inherited Create(ATarget);
  FLabelCount          := 0;
  FDataGlobals         := TOrderedDictionary<string, TTypeDesc>.Create();
  FGlobalOwners        := TDictionary<string, string>.Create();
  FModuleVarNames      := TStringList.Create();
  FModuleVarNames.CaseSensitive := True;
  FModuleVarNames.Sorted := True;
  FModuleVarNames.Duplicates := dupIgnore;
  FGlobalInits         := TDictionary<string, TConstDecl>.Create();
  FThreadVarGlobals    := TDictionary<string, Boolean>.Create();
  FWeakGlobals         := TDictionary<string, Boolean>.Create();
  FClassNameEmitted    := TDictionary<string, Boolean>.Create();
  FStrLits             := TStringList.Create();
  FBreakLabels        := TStack<string>.Create();
  FContinueLabels     := TStack<string>.Create();
  FBreakExcDepths     := TStack<Integer>.Create();
  FContinueExcDepths  := TStack<Integer>.Create();
  FFinallyStack       := TList<TCompoundStmt>.Create();
  FOALFrames          := TList<TOALCallFrame>.Create();
  FFrame          := nil;
  FFrameTypes     := nil;
  FFrameSize      := 0;
  FExitLabel      := '';
  FPromoCount     := 0;
  FPromoLimit     := -1;
  if GetEnvironmentVariable('BLAISE_PROMO_LIMIT') <> '' then
    FPromoLimit := StrToIntDef(GetEnvironmentVariable('BLAISE_PROMO_LIMIT'), -1);
  FPromoLog := GetEnvironmentVariable('BLAISE_PROMO_LOG') <> '';
  FPromoOnly := GetEnvironmentVariable('BLAISE_PROMO_ONLY');
  FInlineMap := TDictionary<string, Integer>.Create();
  FInlineTypes := TDictionary<string, TTypeDesc>.Create();
  FInlineLimit := -1;
  if GetEnvironmentVariable('BLAISE_INLINE_LIMIT') <> '' then
    FInlineLimit := StrToIntDef(GetEnvironmentVariable('BLAISE_INLINE_LIMIT'), -1);
  FInlineLog := GetEnvironmentVariable('BLAISE_INLINE_LOG') <> '';
  FSretFunc       := False;
  FRecRetClass    := rcSret;
  FExcDepth           := 0;
  FExcFrameNext       := 0;
  FForEndNext         := 0;
  FProgExcFrameCount  := 0;
  FSystemDefsEmitted  := False;
  FUnitInitNames      := TStringList.Create();
  FUnitFiniNames      := TStringList.Create();
  FFiniReleased       := TStringList.Create();
  FFiniReleased.CaseSensitive := True;
  FFiniReleased.Sorted := True;
  FFiniReleased.Duplicates := dupIgnore;
  FImportedUnits      := TStringList.Create();
  FImportedUnits.CaseSensitive := False;
  FImportedUnits.Sorted := True;
  FImportedUnits.Duplicates := dupIgnore;
  FConstArgUnsafe     := TStringList.Create();
  FConstArgUnsafe.CaseSensitive := True;
  FConstArgUnsafe.Sorted := True;
  FConstArgUnsafe.Duplicates := dupIgnore;
end;

destructor TX86_64Backend.Destroy;
begin
  Self.ClearFrame();
  FConstArgUnsafe.Free();
  FImportedUnits.Free();
  FFiniReleased.Free();
  FUnitFiniNames.Free();
  FUnitInitNames.Free();
  FOALFrames.Free();
  FFinallyStack.Free();
  FContinueExcDepths.Free();
  FBreakExcDepths.Free();
  FContinueLabels.Free();
  FBreakLabels.Free();
  FClassNameEmitted.Free();
  FStrLits.Free();
  FWeakGlobals.Free();
  FThreadVarGlobals.Free();
  FGlobalInits.Free();
  FModuleVarNames.Free();
  FGlobalOwners.Free();
  FDataGlobals.Free();
  inherited Destroy();
end;

function TX86_64Backend.NewLabel(const APrefix: string): string;
begin
  Result := '.L' + APrefix + IntToStr(FLabelCount);
  Inc(FLabelCount);
end;

function TX86_64Backend.DivGuardAvailable(): Boolean;
begin
  Result := (FSymTable <> nil) and (FSymTable.Lookup('EDivByZero') <> nil);
end;

function TX86_64Backend.StrToIntChecked(): Boolean;
begin
  Result := (FSymTable <> nil)
        and (FSymTable.Lookup('EConvertError') <> nil)
        and (not SameText(FCurrentUnitName, 'SysUtils'));
end;

procedure TX86_64Backend.AddGlobal(const AName: string; AType: TTypeDesc);
var
  Key:   string;
  Sym:   TSymbol;
  Owner: string;
begin
  { Register under the canonical owner-prefixed emit name so that same-named
    module vars from different units occupy DISTINCT slots (ua_GVal vs ub_GVal)
    instead of silently sharing one — and so that references (which apply the
    same GlobalSymName) resolve to the matching definition.  Class-var and
    internal names pass through unchanged. }
  Key := Self.GlobalSymName(AName);
  { Remember the owning unit so EmitDataSection / IsImportedGlobal can consult it
    without re-looking-up the mangled canonical key (which is not a symbol). }
  Owner := '';
  if FSymTable <> nil then
  begin
    Sym := FSymTable.Lookup(AName);
    if (Sym <> nil) and (Sym.Kind = skVariable) then
      Owner := Sym.OwningUnit;
  end;
  if not FGlobalOwners.ContainsKey(Key) then
    FGlobalOwners.Add(Key, Owner);
  if not FDataGlobals.ContainsKey(Key) then
    FDataGlobals.Add(Key, AType);
end;

{ Register a shared data global for every STATIC (class-level) variable in a
  class/record field list, under the mangled ClassVarEmitName stamped by the
  semantic pass.  EmitDataSection then emits a correctly-sized zero slot.  This
  covers read-only static vars that no assignment site auto-registers. }
procedure TX86_64Backend.RegisterClassVars(AFields: TObjectList);
var
  I: Integer;
  FDecl: TFieldDecl;
begin
  if AFields = nil then Exit;
  for I := 0 to AFields.Count - 1 do
  begin
    FDecl := TFieldDecl(AFields.Items[I]);
    if not FDecl.IsClassVar then Continue;
    if FDecl.ClassVarEmitName = '' then Continue;
    if FDecl.ResolvedType = nil then Continue;
    Self.AddGlobal(FDecl.ClassVarEmitName, FDecl.ResolvedType);
  end;
end;

procedure TX86_64Backend.MarkThreadVar(const AName: string);
var
  Key: string;
begin
  { Keyed on the canonical owner-prefixed name, matching AddGlobal — the .tbss
    definition and every %fs:...@tpoff reference use the same GlobalSymName. }
  Key := Self.GlobalSymName(AName);
  if not FThreadVarGlobals.ContainsKey(Key) then
    FThreadVarGlobals.Add(Key, True);
end;

procedure TX86_64Backend.MarkWeakGlobal(const AName: string);
var
  Key: string;
begin
  Key := Self.GlobalSymName(AName);
  if not FWeakGlobals.ContainsKey(Key) then
    FWeakGlobals.Add(Key, True);
end;

function TX86_64Backend.IsThreadVarGlobal(const AName: string): Boolean;
var
  Dummy: Boolean;
begin
  { Accepts either a bare AST name or an already-canonical key; GlobalSymName is
    idempotent on the canonical form (the mangled key is not a module-var
    symbol, so it returns verbatim). }
  Result := FThreadVarGlobals.TryGetValue(Self.GlobalSymName(AName), Dummy);
end;

function TX86_64Backend.IsWeakGlobal(const AName: string): Boolean;
var
  Dummy: Boolean;
begin
  Result := FWeakGlobals.TryGetValue(Self.GlobalSymName(AName), Dummy);
end;

function TX86_64Backend.GlobalType(const AName: string): TTypeDesc;
begin
  { Keyed on the canonical name; GlobalSymName is idempotent so a bare or an
    already-canonical name both resolve to the same slot. }
  if not FDataGlobals.TryGetValue(Self.GlobalSymName(AName), Result) then
    Result := nil;
end;

function TX86_64Backend.IsImportedGlobal(const AName: string): Boolean;
var
  Sym:   TSymbol;
  Owner: string;
begin
  { A global whose owning unit was imported from a cached .bif/.o (incremental /
    separate compilation) is DEFINED by that unit's own object.  This object must
    only reference it (no .globl/label here), or the linker reports a multiple
    definition.  References (leaq Name(%rip)) resolve against the cached object's
    exported symbol. }
  Result := False;
  if FImportedUnits.Count = 0 then Exit;
  { EmitDataSection passes a canonical (owner-prefixed) key — the owning unit is
    recorded in FGlobalOwners, so consult that first (a symbol re-lookup of the
    mangled key would miss). }
  if FGlobalOwners.TryGetValue(AName, Owner) then
  begin
    if Owner = '' then Exit;
    Result := FImportedUnits.IndexOf(Owner) >= 0;
    Exit;
  end;
  if FGlobalOwners.TryGetValue(Self.GlobalSymName(AName), Owner) then
  begin
    if Owner = '' then Exit;
    Result := FImportedUnits.IndexOf(Owner) >= 0;
    Exit;
  end;
  if FSymTable = nil then Exit;
  Sym := FSymTable.Lookup(AName);
  if Sym = nil then Exit;
  if Sym.OwningUnit = '' then Exit;
  Result := FImportedUnits.IndexOf(Sym.OwningUnit) >= 0;
end;

function TX86_64Backend.GlobalLinkWeak(const AName: string): Boolean;
var
  Sym:   TSymbol;
  Owner: string;
begin
  { Owner resolution mirrors IsImportedGlobal: EmitDataSection passes the
    canonical (owner-prefixed) key, whose owning unit is recorded in
    FGlobalOwners; fall back to a symbol re-lookup for a bare name.  A global
    owned by an unmangled unit carries a bare symbol every inlining object
    re-defines — weak binding lets the copies collapse (GH #174). }
  Result := False;
  Owner := '';
  if not FGlobalOwners.TryGetValue(AName, Owner) then
    FGlobalOwners.TryGetValue(Self.GlobalSymName(AName), Owner);
  if (Owner = '') and (FSymTable <> nil) then
  begin
    Sym := FSymTable.Lookup(AName);
    if (Sym <> nil) and (Sym.Kind = skVariable) then
      Owner := Sym.OwningUnit;
  end;
  if Owner = '' then Exit;
  { The program itself is not unmangled here — its own globals stay strong. }
  Result := IsUnmangledUnit(Owner);
end;

function TX86_64Backend.GlobalBindDir(const AName: string): string;
begin
  if Self.GlobalLinkWeak(AName) then
    Result := '.weak '
  else
    Result := '.globl ';
end;

function TX86_64Backend.GlobalOwnerPrefix(const AOwner: string): string;
begin
  { The module-var owner→prefix, mirroring QBE.MangleGlobalOwner EXACTLY: the
    program name and every unmangled RTL unit (System, rtl.*, runtime.*,
    blaise_*) map to '' (bare); any other unit maps to its dotted-to-underscore
    prefix.  Deliberately NOT ClassOwnerPrefix — that one prefixes runtime.*
    class symbols, which is right for CLASS mangling but wrong for module vars,
    where runtime.* globals must stay bare like the RTL routines they sit
    beside. }
  Result := '';
  if AOwner = '' then Exit;
  if (FProgramName <> '') and SameText(AOwner, FProgramName) then Exit;
  Result := MangleUnitPrefix(AOwner);
end;

function TX86_64Backend.GlobalSymName(const AName: string): string;
var
  Sym: TSymbol;
begin
  Result := AName;
  { Owner resolution mirrors QBE.GlobalVarUnitPrefix + VarRef:
    (1) an EXPORTED symbol (interface-section module var) is in the symbol table
        with a non-empty OwningUnit — a cross-unit reference must prefix by THAT
        owner regardless of the emitting unit.
    (2) an implementation-section PRIVATE module var is NOT reachable via
        FSymTable.Lookup at codegen time (Sym=nil) and is only ever referenced
        from within its own unit, so the emitting unit (FCurrentUnitName) IS the
        owner — but only names KNOWN to be module vars (registered in
        FModuleVarNames) may take this context prefix, so class-var
        ClassVarEmitName and internal labels (.L*, _exc_frame_, __sN) are left
        verbatim. }
  if FSymTable <> nil then
  begin
    Sym := FSymTable.Lookup(AName);
    if (Sym <> nil) and (Sym.Kind = skVariable) and (Sym.OwningUnit <> '') then
    begin
      Result := Self.GlobalOwnerPrefix(Sym.OwningUnit) + AName;
      Exit;
    end;
  end;
  if (FModuleVarNames <> nil) and (FModuleVarNames.IndexOf(AName) >= 0) then
    Result := Self.GlobalOwnerPrefix(FCurrentUnitName) + AName;
end;

procedure TX86_64Backend.EmitDataSection;
var
  I, Sz:    Integer;
  Name:     string;
  Directive: string;
  IsTls:    Boolean;
  HasData, HasTbss: Boolean;
  InitCD:   TConstDecl;
begin
  if (FDataGlobals.Count = 0) and (FProgExcFrameCount = 0) and
     (not FProgHasJumboSet) and (not FProgHasPendRel) then
  begin
    Self.EmitStrLitSection();
    Exit;
  end;
  HasData := False;
  HasTbss := False;
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    if Self.IsImportedGlobal(FDataGlobals.Keys[I]) then
      Continue;
    if Self.IsThreadVarGlobal(FDataGlobals.Keys[I]) then
      HasTbss := True
    else
      HasData := True;
  end;
  if FProgExcFrameCount > 0 then HasData := True;
  if FProgHasJumboSet then HasData := True;
  { Two passes: first .data globals, then .tbss threadvars. }
  if HasData then
    Self.Emit('.data');
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    Name  := FDataGlobals.Keys[I];
    if Self.IsImportedGlobal(Name) then Continue;
    IsTls := Self.IsThreadVarGlobal(Name);
    if IsTls then Continue;
    { Initialised global (var G: T = value): emit the folded value.  threadvars
      are excluded (they live in .tbss / always zero). }
    if FGlobalInits.TryGetValue(Name, InitCD) then
    begin
      Self.EmitGlobalInitData(Name, Self.GlobalType(Name), InitCD);
      Continue;
    end;
    { Method pointers (of-object) and 'reference to' closures: 16-byte
      Code+Data fat values, zero-initialised.  (A reference global emitted
      as a single .quad silently OVERLAPPED the next data symbol — its Env
      half aliased the neighbour's first word.) }
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyProcedural) and
       (TProceduralTypeDesc(Self.GlobalType(Name)).IsMethodPtr or
        TProceduralTypeDesc(Self.GlobalType(Name)).IsReference) then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 0, 2) <> '.L' then
        Self.Emit(Self.GlobalBindDir(Name) + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.quad 0');
      Self.Emit(#9'.quad 0');
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyInterface) then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 0, 2) <> '.L' then
      begin
        Self.Emit(Self.GlobalBindDir(Name) + Name + '_obj');
        Self.Emit(Self.GlobalBindDir(Name) + Name + '_itab');
      end;
      Self.Emit(Name + '_obj:');
      Self.Emit(#9'.quad 0');
      Self.Emit(Name + '_itab:');
      Self.Emit(#9'.quad 0');
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (IsJumboSet(Self.GlobalType(Name)) or
          (Self.GlobalType(Name).Kind in [tyRecord, tyStaticArray])) then
    begin
      Sz := Self.GlobalType(Name).RawSize();
      Self.Emit('.balign 8');
      if Copy(Name, 0, 2) <> '.L' then
        Self.Emit(Self.GlobalBindDir(Name) + Name);
      Self.Emit(Name + ':');
      Self.Emit(Format(#9'.skip %d', [Sz]));
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyDouble) then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 0, 2) <> '.L' then
        Self.Emit(Self.GlobalBindDir(Name) + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.double 0.0');
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tySingle) then
    begin
      Self.Emit('.balign 4');
      if Copy(Name, 0, 2) <> '.L' then
        Self.Emit(Self.GlobalBindDir(Name) + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.float 0.0');
      Continue;
    end;
    Sz := IntByteSize(Self.GlobalType(Name));
    case Sz of
      1: begin Directive := #9'.byte 0'; Self.Emit('.balign 1'); end;
      2: begin Directive := #9'.word 0'; Self.Emit('.balign 2'); end;
      8: begin Directive := #9'.quad 0'; Self.Emit('.balign 8'); end;
    else
      begin Directive := #9'.long 0'; Self.Emit('.balign 4'); end;
    end;
    if Copy(Name, 0, 2) <> '.L' then
      Self.Emit(Self.GlobalBindDir(Name) + Name);
    Self.Emit(Name + ':');
    Self.Emit(Directive);
  end;
  { Exception frame slots for the program-main body. }
  for I := 0 to FProgExcFrameCount - 1 do
  begin
    Self.Emit('.balign 16');
    Self.Emit('_exc_frame_' + IntToStr(I) + ':');
    Self.Emit(#9'.skip 512');
  end;
  { Jumbo-set scratch buffers for the program-main body (32 bytes each, the
    256-member maximum). }
  if FProgHasJumboSet then
  begin
    Self.Emit('.balign 8');
    Self.Emit('_jset_scratch_0:');
    Self.Emit(#9'.skip 32');
    Self.Emit('.balign 8');
    Self.Emit('_jset_scratch_1:');
    Self.Emit(#9'.skip 32');
  end;
  { Deferred-release slots for the program-main body (BUG-003 native half):
    $main has no %rbp frame, so its pending-release slots are .bss globals,
    exactly like _jset_scratch above.  Single-threaded one-shot, so sharing is
    fine. }
  if FProgHasPendRel then
  begin
    for I := 0 to PENDREL_SLOTS - 1 do
    begin
      Self.Emit('.balign 8');
      Self.Emit(Format('_pendrel_%d:', [I]));
      Self.Emit(#9'.skip 8');
    end;
  end;
  { Threadvar globals: emit in .tbss (zero-initialised thread-local storage). }
  if HasTbss then
  begin
    Self.Emit('.section .tbss,"awT",@nobits');
    for I := 0 to FDataGlobals.Count - 1 do
    begin
      Name := FDataGlobals.Keys[I];
      if Self.IsImportedGlobal(Name) then Continue;
      if not Self.IsThreadVarGlobal(Name) then Continue;
      if (Self.GlobalType(Name) <> nil) and
         (IsJumboSet(Self.GlobalType(Name)) or
          (Self.GlobalType(Name).Kind in [tyRecord, tyStaticArray])) then
        Sz := Self.GlobalType(Name).RawSize()
      else if (Self.GlobalType(Name) <> nil) and
              (Self.GlobalType(Name).Kind = tyDouble) then
        Sz := 8
      else
      begin
        Sz := IntByteSize(Self.GlobalType(Name));
        if Sz < 4 then Sz := 4;
      end;
      if Sz >= 8 then
        Self.Emit('.balign 8')
      else
        Self.Emit(Format('.balign %d', [Sz]));
      Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(Format(#9'.skip %d', [Sz]));
    end;
  end;
  Self.EmitStrLitSection();
end;

procedure TX86_64Backend.EmitGlobalInitData(const AName: string;
  AType: TTypeDesc; CD: TConstDecl);
var
  J:        Integer;
  ElemKind: TTypeKind;
  ElemDir:  string;
  Idx:      Integer;
  SAT:      TStaticArrayTypeDesc;
begin
  { Static array initialiser: inline element list. }
  if (AType.Kind = tyStaticArray) and CD.IsArrayConst then
  begin
    SAT := TStaticArrayTypeDesc(AType);
    { Multi-dimensional const arrays are nested static-array types; the element
      directive is governed by the INNERMOST scalar element, and the flat
      row-major ArrayElements already match the contiguous layout. }
    while SAT.ElementType.Kind = tyStaticArray do
      SAT := TStaticArrayTypeDesc(SAT.ElementType);
    ElemKind := SAT.ElementType.Kind;
    Self.Emit('.balign 8');
    if Copy(AName, 0, 2) <> '.L' then
      Self.Emit(Self.GlobalBindDir(AName) + AName);
    Self.Emit(AName + ':');
    if ElemKind = tyString then
    begin
      for J := 0 to CD.ArrayElements.Count - 1 do
        if FStrLits.IndexOf(CD.ArrayElements[J]) < 0 then
          FStrLits.Add(CD.ArrayElements[J]);
      for J := 0 to CD.ArrayElements.Count - 1 do
      begin
        Idx := FStrLits.IndexOf(CD.ArrayElements[J]);
        Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
      end;
      Exit;
    end;
    case ElemKind of
      tyByte, tyBoolean:           ElemDir := #9'.byte ';
      tySmallInt, tyWord:          ElemDir := #9'.word ';
      tyInt64, tyUInt64, tyPointer, tyPChar: ElemDir := #9'.quad ';
      tyDouble:                    ElemDir := #9'.double ';
      tySingle:                    ElemDir := #9'.float ';
    else
      ElemDir := #9'.long ';
    end;
    for J := 0 to CD.ArrayElements.Count - 1 do
      Self.Emit(ElemDir + CD.ArrayElements[J]);
    Exit;
  end;

  { String scalar: point at an immortal static string header (__sN + 12). }
  if AType.IsString() then
  begin
    if FStrLits.IndexOf(CD.StrVal) < 0 then
      FStrLits.Add(CD.StrVal);
    Idx := FStrLits.IndexOf(CD.StrVal);
    Self.Emit('.balign 8');
    if Copy(AName, 0, 2) <> '.L' then
      Self.Emit(Self.GlobalBindDir(AName) + AName);
    Self.Emit(AName + ':');
    Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
    Exit;
  end;

  { Scalar numeric / boolean / enum / real. }
  case AType.Kind of
    tyDouble:
      begin
        Self.Emit('.balign 8');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit(Self.GlobalBindDir(AName) + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.double %s', [CD.StrVal]));
      end;
    tySingle:
      begin
        Self.Emit('.balign 4');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit(Self.GlobalBindDir(AName) + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.float %s', [CD.StrVal]));
      end;
    tyByte, tyBoolean:
      begin
        Self.Emit('.balign 1');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit(Self.GlobalBindDir(AName) + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.byte %d', [CD.IntVal]));
      end;
    tySmallInt, tyWord:
      begin
        Self.Emit('.balign 2');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit(Self.GlobalBindDir(AName) + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.word %d', [CD.IntVal]));
      end;
    tyInt64, tyUInt64, tyPointer, tyPChar:
      begin
        Self.Emit('.balign 8');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit(Self.GlobalBindDir(AName) + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.quad %d', [CD.IntVal]));
      end;
  else
    { Integer / UInt32 / enum — 32-bit. }
    Self.Emit('.balign 4');
    if Copy(AName, 0, 2) <> '.L' then Self.Emit('.globl ' + AName);
    Self.Emit(AName + ':');
    Self.Emit(Format(#9'.long %d', [CD.IntVal]));
  end;
end;

{ ------------------------------------------------------------------ }
{ String literal helpers (M7c)                                         }
{ ------------------------------------------------------------------ }

{ Escape a string for use in an AT&T .ascii directive.
  GNU as accepts the same escapes as C string literals. }
{ Escape a string for a gas .ascii directive.

  Non-printable bytes are emitted as THREE-DIGIT OCTAL, not '\xNN'.  gas's
  hex escape is greedy -- it consumes every hex digit that follows, so a NUL
  before the letter 'b' becomes '\x00b', which gas reads as the single byte
  0x0B.  That silently corrupts the data AND desynchronises it from the
  length already written into the ARC header.  Octal escapes in gas are
  capped at three digits, so zero-padding makes each one self-terminating
  regardless of the next character. }
function TX86_64Backend.AsmEscapeString(const AStr: string): string;
var
  I, C: Integer;
begin
  Result := '';
  for I := 0 to Length(AStr) - 1 do
  begin
    C := StrAt(AStr, I);
    case C of
      34:  Result := Result + '\"';
      92:  Result := Result + '\\';
    else
      if (C < 32) or (C > 126) then
        { Three octal digits, zero-padded: '\000'..'\377'. }
        Result := Result + '\'
                  + Chr(48 + ((C shr 6) and 7))
                  + Chr(48 + ((C shr 3) and 7))
                  + Chr(48 + (C and 7))
      else
        Result := Result + Chr(C);
    end;
  end;
end;

procedure TX86_64Backend.EmitGlobalReleases;
{ Program-exit teardown of ARC-managed GLOBALS owned by the PROGRAM itself.
  Addressing is <Name>(%rip); the sibling procedure-epilogue walk in
  EmitProcDecl does the same job for frame-resident locals via VarOperand.
  Both dispatch on the shared ArcScopeExitReleaseKind classifier (see
  EmitGlobalReleaseOne) so they cannot drift apart on which type kinds they
  cover.  UNIT-owned globals are NOT released here: each unit's own
  <Unit>_fini (emitted in the unit's translation unit, where impl-section
  privates are reachable) releases them, and $main calls the finis in
  reverse init order just before this walk.  Hence the two skips below —
  imported globals (incremental mode: the owning unit's object holds both
  the slot and its fini) and FFiniReleased entries (whole-program mode:
  unit globals share this FDataGlobals map with program globals). }
var
  I:     Integer;
  Name:  string;
  Ty:    TTypeDesc;
begin
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    Name := FDataGlobals.Keys[I];
    Ty   := Self.GlobalType(Name);
    if Ty = nil then Continue;
    { Thread-var globals live in TLS and are not released here (matches the
      data-section split; their lifetime is per-thread, not program-global). }
    if Self.IsThreadVarGlobal(Name) then Continue;
    { Unit-owned: released by the owning unit's <Unit>_fini, called above. }
    if Self.IsImportedGlobal(Name) then Continue;
    if FFiniReleased.IndexOf(Name) >= 0 then Continue;
    Self.EmitGlobalReleaseOne(Name, Ty);
  end;
end;

procedure TX86_64Backend.EmitUnitGlobalReleases(ABlock: TBlock);
var
  I, J: Integer;
  VD:   TVarDecl;
  Name: string;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    VD := TVarDecl(ABlock.Decls.Items[I]);
    if VD.ResolvedType = nil then Continue;
    if VD.IsThreadVar then Continue;
    if VD.IsUnretained then Continue;
    if ArcScopeExitReleaseKind(VD.ResolvedType) = arkNone then Continue;
    for J := 0 to VD.Names.Count - 1 do
    begin
      Name := Self.GlobalSymName(VD.Names.Strings[J]);
      Self.EmitGlobalReleaseOne(Name, VD.ResolvedType);
      FFiniReleased.Add(Name);
    end;
  end;
end;

procedure TX86_64Backend.EmitGlobalReleaseOne(const AName: string; ATy: TTypeDesc);
begin
    case ArcScopeExitReleaseKind(ATy) of
      arkString:
        begin
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [AName]));
          Self.Emit(#9'callq _StringRelease');
        end;
      arkClass:
        begin
          if Self.IsWeakGlobal(AName) then
          begin
            Self.Emit(Format(#9'leaq %s(%%rip), %%rdi', [AName]));
            Self.Emit(#9'callq _WeakClear');
          end
          else
          begin
            Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [AName]));
            Self.Emit(#9'callq _ClassRelease');
          end;
        end;
      arkDynArray:
        begin
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [AName]));
          Self.Emit(#9'callq _DynArrayRelease');
        end;
      arkIntf:
        begin
          if Self.IsWeakGlobal(AName) then
          begin
            Self.Emit(Format(#9'leaq %s_obj(%%rip), %%rdi', [AName]));
            Self.Emit(#9'callq _WeakClear');
          end
          else
          begin
            Self.Emit(Format(#9'movq %s_obj(%%rip), %%rdi', [AName]));
            Self.Emit(#9'callq _ClassRelease');
          end;
        end;
      arkRefEnv:
        begin
          { 'reference to' global: the fat value is a code pointer at +0 and
            an env pointer at +8.  That Data half strong-references an ARC
            env record (nil for
            capture-free closures — _ClassRelease is nil-safe).  Balance the
            reference the slot holds.

            The procedure-epilogue walk has had this arm all along; this one
            did not, so a program-level `reference to procedure` holding a
            capturing closure leaked its env at exit while the identical
            local inside a procedure was released correctly.  Exactly the
            (A)/(B) drift the shared classifier exists to prevent — with the
            case statements aligned, the gap is now visible as a missing arm
            rather than an invisible fall-off-the-end. }
          Self.Emit(Format(#9'movq %s+8(%%rip), %%rdi', [AName]));
          Self.Emit(#9'callq _ClassRelease');
        end;
      arkAggregate:
        begin
          { Aggregate global with managed content: walk it at program exit.
            EmitManagedReleaseAt dispatches record fields (recursing into
            static-array fields) and static-array elements (recursing into
            record elements) — the same shared helper the arm64 backend's
            main epilogue uses, so both architectures release program-level
            aggregates through one code path.

            Before this, the kind chain covered string/class/dyn-array/
            interface/record only: a PROGRAM-level `array[0..N] of TFoo`
            is registered as a GLOBAL (EmitProgram accepts tyStaticArray),
            so it fell off the end of the chain and every element leaked.
            The identical array inside a procedure was fine — that goes
            through the separate procedure-frame walk, which grew its
            tyStaticArray arm in the BUG-016 stage-2 work.  QBE never had
            the gap: it has one cleanup routine for both cases.

            The arkAggregate classification already excludes an unmanaged
            aggregate, so nothing is emitted for one (the record arm used
            to emit a bare pushq/leaq/popq trio for a record with no
            managed fields).

            Safe against manual element lifetimes: A[I].Free() nils the
            element slot, so this walk is a no-op on already-freed
            elements. }
          Self.Emit(#9'pushq %rbx');
          Self.Emit(Format(#9'leaq %s(%%rip), %%rbx', [AName]));
          Self.EmitManagedReleaseAt(ATy, '%rbx', False);
          Self.Emit(#9'popq %rbx');
        end;
    end;
end;

{ Evaluate a string literal: register it in the pool if new, then emit
  leaq __sN+12(%rip), %rax so %rax holds the Blaise data pointer. }
{ Assembler data directive for one non-string array-const element of the named
  element type.  Honours the element's real width (Boolean/Byte -> .byte,
  Int64/pointer -> .quad, ...) so the emitted stride matches the subscript-read
  stride.  Defaults to .long (4-byte Integer) when the type is unknown. }
function TX86_64Backend.ConstElemAsmDir(const AElemType: string): string;
var
  TD: TTypeDesc;
  Sz: Integer;
begin
  { Map built-in scalar names directly so the result is correct even when
    FSymTable is unset (some callers build a codegen without a table); user
    types fall back to the table, defaulting to .long (4-byte). }
  if SameText(AElemType, 'Boolean') or SameText(AElemType, 'Byte') or
     SameText(AElemType, 'ShortInt') or SameText(AElemType, 'AnsiChar') then
    Exit(#9'.byte');
  if SameText(AElemType, 'SmallInt') or SameText(AElemType, 'Word') then
    Exit(#9'.word');
  { Float elements need a FLOAT directive: '.quad 0.25' silently
    mis-assembles (gas reads the mantissa text as an integer expression),
    so every element of a const Double array loaded as garbage. }
  if SameText(AElemType, 'Double') then
    Exit(#9'.double');
  if SameText(AElemType, 'Single') then
    Exit(#9'.float');
  if SameText(AElemType, 'Int64') or SameText(AElemType, 'UInt64') or
     SameText(AElemType, 'Pointer') then
    Exit(#9'.quad');
  if SameText(AElemType, 'Integer') or SameText(AElemType, 'UInt32') or
     SameText(AElemType, 'LongInt') or SameText(AElemType, 'Cardinal') then
    Exit(#9'.long');
  Sz := 4;
  if FSymTable <> nil then
  begin
    TD := FSymTable.FindType(AElemType);
    if TD <> nil then
    begin
      { A named alias of a float type must keep the float directive too. }
      if TD.Kind = tyDouble then Exit(#9'.double');
      if TD.Kind = tySingle then Exit(#9'.float');
      Sz := TD.RawSize();
    end;
  end;
  case Sz of
    1: Result := #9'.byte';
    2: Result := #9'.word';
    8: Result := #9'.quad';
  else
    Result := #9'.long';
  end;
end;

procedure TX86_64Backend.EmitArrayConstData(ABlock: TBlock;
  const APrefix: string);
var
  I, J, K, M: Integer;
  CD:   TConstDecl;
  TD:   TTypeDecl;
  Decl: TMethodDecl;
  Lbl:  string;
  Idx:  Integer;
  IsStr: Boolean;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    { Jumbo set constant: emit the bitmap as a byte blob under the mangled
      label (shares the const-data pass with array consts). }
    if (CD.ConstSetBytes <> nil) and (CD.ConstSetBytes.Count > 0) then
    begin
      if APrefix <> '' then
        Lbl := APrefix + '_' + CD.Name
      else if CD.ResolvedSetQbeName <> '' then
        Lbl := NativeMangle(CD.ResolvedSetQbeName)
      else
        Lbl := CD.Name;
      Self.Emit('.data');
      Self.Emit('.balign 8');
      { A unit's INTERFACE-section const (or a class/record const, APrefix <>
        '') is referenced from other separately-compiled .o files under
        incremental compilation and must be exported; an implementation- or
        program-level const is never referenced across a .o boundary and
        stays local, avoiding a cross-compile label collision (see
        NewArrayConstLabel). }
      if (Copy(Lbl, 0, 2) <> '.L') and ((APrefix <> '') or CD.IsExportedConst) then
        Self.Emit('.globl ' + Lbl);
      Self.Emit(Lbl + ':');
      for J := 0 to CD.ConstSetBytes.Count - 1 do
        Self.Emit(Format(#9'.byte %s', [CD.ConstSetBytes[J]]));
      Continue;
    end;
    if not CD.IsArrayConst then Continue;
    if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
    if APrefix <> '' then
      Lbl := APrefix + '_' + CD.Name
    else if CD.ResolvedQbeName <> '' then
      Lbl := NativeMangle(CD.ResolvedQbeName)
    else
      Lbl := CD.Name;
    IsStr := SameText(CD.ArrayElemType, 'string');
    if IsStr then
    begin
      for J := 0 to CD.ArrayElements.Count - 1 do
        if FStrLits.IndexOf(CD.ArrayElements[J]) < 0 then
          FStrLits.Add(CD.ArrayElements[J]);
      Self.Emit('.data');
      Self.Emit('.balign 8');
      if (Copy(Lbl, 0, 2) <> '.L') and ((APrefix <> '') or CD.IsExportedConst) then
        Self.Emit('.globl ' + Lbl);
      Self.Emit(Lbl + ':');
      for J := 0 to CD.ArrayElements.Count - 1 do
      begin
        Idx := FStrLits.IndexOf(CD.ArrayElements[J]);
        Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
      end;
    end
    else
    begin
      Self.Emit('.data');
      Self.Emit('.balign 8');
      if (Copy(Lbl, 0, 2) <> '.L') and ((APrefix <> '') or CD.IsExportedConst) then
        Self.Emit('.globl ' + Lbl);
      Self.Emit(Lbl + ':');
      for J := 0 to CD.ArrayElements.Count - 1 do
        Self.Emit(Format('%s %s',
          [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[J]]));
    end;
  end;
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if Decl.Body = nil then Continue;
    for J := 0 to Decl.Body.ConstDecls.Count - 1 do
    begin
      CD := TConstDecl(Decl.Body.ConstDecls.Items[J]);
      if not CD.IsArrayConst then Continue;
      if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
      if CD.ResolvedQbeName <> '' then
        Lbl := NativeMangle(CD.ResolvedQbeName)
      else
        Lbl := CD.Name;
      IsStr := SameText(CD.ArrayElemType, 'string');
      if IsStr then
      begin
        for K := 0 to CD.ArrayElements.Count - 1 do
          if FStrLits.IndexOf(CD.ArrayElements[K]) < 0 then
            FStrLits.Add(CD.ArrayElements[K]);
        Self.Emit('.data');
        Self.Emit('.balign 8');
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
        begin
          Idx := FStrLits.IndexOf(CD.ArrayElements[K]);
          Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
        end;
      end
      else
      begin
        Self.Emit('.data');
        Self.Emit('.balign 8');
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
          Self.Emit(Format('%s %s',
            [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[K]]));
      end;
    end;
  end;
  { Static (class-level) variables: register one shared global per IsClassVar
    field so EmitDataSection emits a zero-initialised slot under the mangled
    label (ClassVarEmitName).  Done for BOTH class and record types, and
    independently of any assignment (a read-only static var has no assignment to
    auto-register it via AddGlobal at the write site). }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
      RegisterClassVars(TClassTypeDef(TD.Def).Fields)
    else if TD.Def is TRecordTypeDef then
      RegisterClassVars(TRecordTypeDef(TD.Def).Fields);
  end;
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    for J := 0 to TClassTypeDef(TD.Def).ConstDecls.Count - 1 do
    begin
      CD := TConstDecl(TClassTypeDef(TD.Def).ConstDecls.Items[J]);
      if not CD.IsArrayConst then Continue;
      if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
      Lbl := TD.Name + '_' + CD.Name;
      IsStr := SameText(CD.ArrayElemType, 'string');
      if IsStr then
      begin
        for K := 0 to CD.ArrayElements.Count - 1 do
          if FStrLits.IndexOf(CD.ArrayElements[K]) < 0 then
            FStrLits.Add(CD.ArrayElements[K]);
        Self.Emit('.data');
        Self.Emit('.balign 8');
        Self.Emit('.globl ' + Lbl);
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
        begin
          Idx := FStrLits.IndexOf(CD.ArrayElements[K]);
          Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
        end;
      end
      else
      begin
        Self.Emit('.data');
        Self.Emit('.balign 8');
        Self.Emit('.globl ' + Lbl);
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
          Self.Emit(Format('%s %s',
            [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[K]]));
      end;
    end;
    for J := 0 to TClassTypeDef(TD.Def).Methods.Count - 1 do
    begin
      Decl := TMethodDecl(TClassTypeDef(TD.Def).Methods.Items[J]);
      if Decl.Body = nil then Continue;
      for K := 0 to Decl.Body.ConstDecls.Count - 1 do
      begin
        CD := TConstDecl(Decl.Body.ConstDecls.Items[K]);
        if not CD.IsArrayConst then Continue;
        if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
        if CD.ResolvedQbeName <> '' then
          Lbl := NativeMangle(CD.ResolvedQbeName)
        else
          Lbl := CD.Name;
        IsStr := SameText(CD.ArrayElemType, 'string');
        if IsStr then
        begin
          for M := 0 to CD.ArrayElements.Count - 1 do
            if FStrLits.IndexOf(CD.ArrayElements[M]) < 0 then
              FStrLits.Add(CD.ArrayElements[M]);
          Self.Emit('.data');
          Self.Emit('.balign 8');
          Self.Emit(Lbl + ':');
          for M := 0 to CD.ArrayElements.Count - 1 do
          begin
            Idx := FStrLits.IndexOf(CD.ArrayElements[M]);
            Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
          end;
        end
        else
        begin
          Self.Emit('.data');
          Self.Emit('.balign 8');
          Self.Emit(Lbl + ':');
          for M := 0 to CD.ArrayElements.Count - 1 do
            Self.Emit(Format('%s %s',
              [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[M]]));
        end;
      end;
    end;
  end;
end;

procedure TX86_64Backend.EmitStrLitAddr(const AValue: string);
var
  Idx: Integer;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  Self.Emit(Format(#9'leaq __s%d + 12(%%rip), %%rax', [Idx]));
end;

{ Emit all accumulated string literal blobs to .rodata.
  Each blob: 4-byte refcnt=-1 (immortal), 4-byte length, 4-byte capacity,
  then the ASCII bytes, then a NUL terminator.
  The Blaise string data pointer convention: str_ptr = &header + 12. }
procedure TX86_64Backend.EmitStrLitSection;
var
  I:   Integer;
  Len: Integer;
begin
  if FStrLits.Count = 0 then Exit;
  Self.Emit('.section .rodata');
  for I := 0 to FStrLits.Count - 1 do
  begin
    Len := Length(FStrLits.Strings[I]);
    Self.Emit('.balign 4');
    Self.Emit(Format('__s%d:', [I]));
    Self.Emit(Format(#9'.long -1', []));       { refcnt = immortal }
    Self.Emit(Format(#9'.long %d', [Len]));    { length }
    Self.Emit(Format(#9'.long %d', [Len]));    { capacity }
    if Len > 0 then
      Self.Emit(Format(#9'.ascii "%s"', [Self.AsmEscapeString(FStrLits.Strings[I])]));
    Self.Emit(#9'.byte 0');                    { NUL terminator }
  end;
end;

{ ------------------------------------------------------------------ }
{ Class data section helpers                                           }
{ ------------------------------------------------------------------ }

{ Mangle a name for use as an assembly label: replace characters that are
  invalid in label names with underscores, matching QBE backend's QBEMangle. }
function NativeMangle(const AName: string): string;
begin
  { Delegates to the shared backend-neutral mangler in blaise.codegen
    (formerly a per-character twin of the QBE backend's QBEMangle). }
  Result := CodegenMangle(AName);
end;

function TX86_64Backend.ClassOwnerPrefix(const AOwner: string): string;
var
  I: Integer;
  Ch: string;
begin
  Result := '';
  { Program-scope classes keep bare names — see the QBE backend's
    ClassUnitPrefix and uSemantic.CurrentUnitPrefix. }
  if (AOwner <> '') and
     not ((FProgramName <> '') and SameText(AOwner, FProgramName)) and
     not SameText(AOwner, 'System') and
     not ((Length(AOwner) >= 4) and SameText(Copy(AOwner, 0, 4), 'rtl.')) and
     not ((Length(AOwner) >= 7) and SameText(Copy(AOwner, 0, 7), 'blaise_')) then
  begin
    for I := 0 to Length(AOwner) - 1 do
    begin
      Ch := Copy(AOwner, I, 1);
      if Ch = '.' then Result := Result + '_'
      else              Result := Result + Ch;
    end;
    Result := Result + '_';
  end;
end;

function TX86_64Backend.ClassSymName(const AClassName: string): string;
var
  Sym: TSymbol;
begin
  Result := '';
  { Generic instances are ALWAYS bare — never unit-prefixed.  The same
    instance is materialised by every compilation process that touches it,
    so its symbols must be unit-independent (per-unit codegen emits them
    WEAK and the linker dedups; BUGS.md BUG-004).  The Sym.OwningUnit of an
    import-triggered instance points at the RE-EXPORTING unit, which never
    emitted a copy — mirrors the QBE backend's ClassUnitPrefix. }
  if (Pos('<', AClassName) < 0) and (FSymTable <> nil) then
  begin
    Sym := FSymTable.Lookup(AClassName);
    if Sym <> nil then
      Result := ClassOwnerPrefix(Sym.OwningUnit);
  end;
  Result := Result + NativeMangle(AClassName);
end;

function TX86_64Backend.ClassSymNameForDecl(ATypeDecl: TTypeDecl): string;
begin
  { A type's definition is emitted under its own unit's codegen pass, so key the
    symbol on the unit currently being emitted (FCurrentUnitName) rather than a
    flat-table name re-lookup — which would mis-mangle a cross-unit last-wins
    loser as the winner.  Mirrors the QBE backend's ClassSymNameForDecl. }
  Result := ClassOwnerPrefix(FCurrentUnitName) + NativeMangle(ATypeDecl.Name);
end;

procedure TX86_64Backend.EmitPropAccessorCallNative(
  const AOwnerType, AMethod: string; AVSlot: Integer);
begin
  if AVSlot >= 0 then
  begin
    { Virtual dispatch: receiver in %rdi.  Load vptr, then the function
      pointer from vtable[(Slot+1)*8] (slot 0 reserved for typeinfo). }
    Self.Emit(#9'movq (%rdi), %rax');
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(AVSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + Self.ClassSymName(AOwnerType) + '_'
      + NativeMangle(AMethod));
end;

function TX86_64Backend.IntfTypeInfoName(const AIntfName: string): string;
begin
  if Pos('<', AIntfName) >= 0 then
    Result := NativeMangle(AIntfName)
  else
    Result := Self.ClassSymName(AIntfName);
end;

function FindMethodInClassDef(AClassDef: TClassTypeDef;
  const AName: string): TMethodDecl;
var
  I: Integer;
  M: TMethodDecl;
begin
  Result := nil;
  for I := 0 to AClassDef.Methods.Count - 1 do
  begin
    M := TMethodDecl(AClassDef.Methods.Items[I]);
    if SameText(M.Name, AName) then
      Exit(M);
  end;
end;

{ Compute the mangled emit name for a class method: ResolvedQbeName if set,
  else TypeName_MethodName, both passed through NativeMangle. }
function MethodEmitNameNative(ADecl: TMethodDecl; const ATypeName, AMethodName: string): string;
begin
  if (ADecl <> nil) and (ADecl.ResolvedQbeName <> '') then
    Result := NativeMangle(ADecl.ResolvedQbeName)
  else if ADecl <> nil then
    Result := NativeMangle(ATypeName + '_' + ADecl.Name)
  else
    Result := NativeMangle(ATypeName + '_' + AMethodName);
end;

function NativeExprOwnsRef(AExpr: TASTExpr): Boolean;
begin
  { Delegates to the shared backend-neutral predicate in blaise.codegen
    (formerly a byte-identical twin of the QBE backend's ExprOwnsRef). }
  Result := ArcExprOwnsRef(AExpr);
end;

{ Emit an immortal class-name string blob and return the label+12 reference
  (the pointer to the character data, past the 12-byte ARC/length header).
  ASymName names the data symbol (may be unit-prefixed to avoid link
  collisions); AText is the string content — the bare class/method name
  that ClassName/TestClassName must observe at runtime. }
function TX86_64Backend.EmitClassNameString(const ASymName, AText: string): string;
var
  Mangled: string;
  Len:     Integer;
begin
  Mangled := NativeMangle(ASymName);
  Result  := '__cn_' + Mangled + ' + 12';
  { Idempotent: skip if already emitted (MethodAddress and class section may
    both request the same name string). }
  if FClassNameEmitted.ContainsKey(Mangled) then
    Exit;
  FClassNameEmitted.Add(Mangled, True);
  Len := Length(AText);
  Self.Emit('.balign 4');
  Self.Emit('__cn_' + Mangled + ':');
  Self.Emit(#9'.long -1');
  Self.Emit(Format(#9'.long %d', [Len]));
  Self.Emit(Format(#9'.long %d', [Len]));
  Self.Emit(Format(#9'.ascii "%s"', [AText]));
  Self.Emit(#9'.byte 0');
end;

procedure TX86_64Backend.EmitAttrTables(ACD: TClassTypeDef; const ACSym: string;
  out AAttrsStr, AMethAttrsStr: string);
var
  J, K:  Integer;
  Count: Integer;
  AU:    TAttributeUse;
  MD:    TMethodDecl;
begin
  AAttrsStr     := '0';
  AMethAttrsStr := '0';

  Count := 0;
  for J := 0 to ACD.AttrUses.Count - 1 do
    if TAttributeUse(ACD.AttrUses.Items[J]).ThunkDecl <> nil then
      Inc(Count);
  if Count > 0 then
  begin
    Self.Emit('.balign 8');
    Self.Emit('attrs_' + ACSym + ':');
    Self.Emit(Format(#9'.quad %d', [Count]));
    for J := 0 to ACD.AttrUses.Count - 1 do
    begin
      AU := TAttributeUse(ACD.AttrUses.Items[J]);
      if AU.ThunkDecl = nil then Continue;
      Self.Emit(#9'.quad typeinfo_' + Self.ClassSymName(AU.ResolvedClassName));
      Self.Emit(#9'.quad ' + FuncSymbolFromDecl(TMethodDecl(AU.ThunkDecl)));
    end;
    AAttrsStr := 'attrs_' + ACSym;
  end;

  Count := 0;
  for J := 0 to ACD.Methods.Count - 1 do
  begin
    MD := TMethodDecl(ACD.Methods.Items[J]);
    if not MD.IsPublished then Continue;
    for K := 0 to MD.AttrUses.Count - 1 do
      if TAttributeUse(MD.AttrUses.Items[K]).ThunkDecl <> nil then
        Inc(Count);
  end;
  if Count > 0 then
  begin
    { Method-name blobs first (EmitClassNameString is idempotent, so names
      already emitted for the published-method table are not duplicated) —
      the table's .quad sequence below must not be interleaved with them. }
    for J := 0 to ACD.Methods.Count - 1 do
    begin
      MD := TMethodDecl(ACD.Methods.Items[J]);
      if MD.IsPublished and (MD.AttrUses.Count > 0) then
        Self.EmitClassNameString(MD.Name, MD.Name);
    end;
    Self.Emit('.balign 8');
    Self.Emit('methattrs_' + ACSym + ':');
    Self.Emit(Format(#9'.quad %d', [Count]));
    for J := 0 to ACD.Methods.Count - 1 do
    begin
      MD := TMethodDecl(ACD.Methods.Items[J]);
      if not MD.IsPublished then Continue;
      for K := 0 to MD.AttrUses.Count - 1 do
      begin
        AU := TAttributeUse(MD.AttrUses.Items[K]);
        if AU.ThunkDecl = nil then Continue;
        Self.Emit(Format(#9'.quad __cn_%s + 12', [NativeMangle(MD.Name)]));
        Self.Emit(#9'.quad typeinfo_' + Self.ClassSymName(AU.ResolvedClassName));
        Self.Emit(#9'.quad ' + FuncSymbolFromDecl(TMethodDecl(AU.ThunkDecl)));
      end;
    end;
    AMethAttrsStr := 'methattrs_' + ACSym;
  end;
end;

procedure TX86_64Backend.EmitVarDeclStmt(AStmt: TVarDeclStmt);
{ Block-scoped 'var' declaration statement (Phase 4) — native mirror of the
  QBE emitter: (1) env-alloc site drops the previous execution's env and
  allocates a fresh one, refilling the group's '_cap_' pointer slots;
  (2) a non-captured name re-zeroes its frame slot (releasing a managed old
  value); (3) the optional initialiser runs as a redirect-aware assignment. }
var
  Env:  TRecordTypeDesc;
  F:    TFieldInfo;
  Name: string;
  I:    Integer;
begin
  if AStmt.IsEnvAllocSite then
  begin
    Env := TRecordTypeDesc(AStmt.EnvType);
    Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(AStmt.EnvSlotName)]));
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(Format(#9'movq $%d, %%rdi', [Env.TotalSize()]));
    Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi',
      [NativeMangle(Env.Name)]));
    Self.Emit(#9'callq _ClassAlloc');
    Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(AStmt.EnvSlotName)]));
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(AStmt.EnvSlotName)]));
    for I := 0 to Env.Fields.Count - 1 do
    begin
      F := TFieldInfo(Env.Fields.Items[I]);
      Self.Emit(Format(#9'leaq %d(%%rax), %%rcx', [F.Offset]));
      Self.Emit(Format(#9'movq %%rcx, %s', [Self.VarOperand('_cap_' + F.Name)]));
    end;
  end;
  Name := AStmt.Decl.Names.Strings[0];
  if not Self.IsCaptured(Name) then
  begin
    if AStmt.Decl.ResolvedType.IsString() then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(Name)]));
      Self.Emit(#9'callq _StringRelease');
      Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(Name)]));
    end
    else if AStmt.Decl.ResolvedType.Kind = tyClass then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(Name)]));
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(Name)]));
    end
    else if AStmt.Decl.ResolvedType.Kind = tyDynArray then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(Name)]));
      Self.Emit(#9'callq _DynArrayRelease');
      Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(Name)]));
    end
    else if AStmt.Decl.ResolvedType.Kind in [tyInteger, tyUInt32, tyBoolean,
             tyByte, tyEnum, tySmallInt, tyWord] then
      Self.Emit(Format(#9'movl $0, %s', [Self.VarOperand(Name)]))
    else
      Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(Name)]));
  end;
  if AStmt.InitAssign <> nil then
    Self.EmitStmt(AStmt.InitAssign);
end;

procedure TX86_64Backend.EmitEnvPrologue(ADecl: TMethodDecl);
{ Phase-2 anonymous-method capture (docs/anonymous-methods-design.adoc):
  mirror of the QBE EmitEnvPrologue.  Enclosing frame: heap-allocate the env
  via _ClassAlloc (zeroed — captured locals start at zero-init for free),
  take the frame's own strong reference, then snapshot captured VALUE
  parameters from their spilled slots into the env fields (managed values
  take an extra retain — the env owns its copy independently of the param
  slot, which the param-exit pass releases separately).  Thunk: the env
  arrives through the hidden '__env' first parameter and is BORROWED.
  Either way, each promoted name's '_cap_<Name>' slot receives the field's
  heap address so every IsCaptured access path redirects unchanged. }
var
  Env:  TRecordTypeDesc;
  I, J: Integer;
  F:    TFieldInfo;
  Name: string;
  P:    TMethodParam;
begin
  Env := TRecordTypeDesc(ADecl.EnvType);
  if ADecl.IsAnonThunk then
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('__env')]))
  else
  begin
    Self.Emit(Format(#9'movq $%d, %%rdi', [Env.TotalSize()]));
    Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi',
      [NativeMangle(Env.Name)]));
    Self.Emit(#9'callq _ClassAlloc');
    Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand('__envp')]));
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('__envp')]));
  end;
  for I := 0 to ADecl.EnvCaptured.Count - 1 do
  begin
    Name := ADecl.EnvCaptured.Strings[I];
    F := Env.FindField(Name);
    Self.Emit(Format(#9'leaq %d(%%rax), %%rcx', [F.Offset]));
    Self.Emit(Format(#9'movq %%rcx, %s', [Self.VarOperand('_cap_' + Name)]));
  end;
  if ADecl.IsAnonThunk then
  begin
    { Thunk from a method body (Phase 3): materialise the real Self slot
      from the env field (Self is never reassigned — snapshot ≡ by-ref). }
    if ADecl.EnvCaptured.IndexOf('Self') >= 0 then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_Self')]));
      Self.Emit(#9'movq (%rcx), %rcx');
      Self.Emit(Format(#9'movq %%rcx, %s', [Self.VarOperand('Self')]));
    end;
    Exit;
  end;
  { Enclosing METHOD frame (Phase 3): snapshot Self into its env field with
    the env's own retain (the env cleanup releases it).  A [Weak Self]
    capture (Phase 5) routes through _WeakAssign instead: registered in the
    weak table, auto-nil'd when the receiver dies, no refcount taken. }
  if ADecl.EnvCaptured.IndexOf('Self') >= 0 then
  begin
    if (Env.FindField('Self') <> nil) and Env.FindField('Self').IsWeak then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('_cap_Self')]));
      Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand('Self')]));
      Self.Emit(#9'callq _WeakAssign');
    end
    else
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_Self')]));
      Self.Emit(#9'movq %rax, (%rcx)');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
    end;
  end;
  for J := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[J]);
    if ADecl.EnvCaptured.IndexOf(P.ParamName) < 0 then Continue;
    F := Env.FindField(P.ParamName);
    if F.TypeDesc.Kind = tyRecord then
    begin
      { Param slot holds a pointer to the local _data copy (repointed in the
        phase-2 param pass above); deep-copy into the env field with a
        per-managed-field retain (env owns its copy). }
      Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.VarOperand('_cap_' + P.ParamName)]));
      Self.Emit(Format(#9'movq $%d, %%rdx', [F.TypeDesc.RawSize()]));
      Self.Emit(#9'callq memcpy');
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'movq %s, %%rbx',
        [Self.VarOperand('_cap_' + P.ParamName)]));
      Self.EmitRecordFieldRetains(TRecordTypeDesc(F.TypeDesc), '%rbx');
      Self.Emit(#9'popq %rbx');
    end
    else if IsFloatFamily(F.TypeDesc) then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand('_cap_' + P.ParamName)]));
      if F.TypeDesc.Kind = tySingle then
      begin
        Self.Emit(Format(#9'movss %s, %%xmm0', [Self.VarOperand(P.ParamName)]));
        Self.Emit(#9'movss %xmm0, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movsd %s, %%xmm0', [Self.VarOperand(P.ParamName)]));
        Self.Emit(#9'movsd %xmm0, (%rcx)');
      end;
    end
    else if F.TypeDesc.Kind in [tyInteger, tyUInt32, tyBoolean, tyByte,
                                tyEnum, tySmallInt, tyWord] then
    begin
      Self.Emit(Format(#9'movl %s, %%eax', [Self.VarOperand(P.ParamName)]));
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand('_cap_' + P.ParamName)]));
      Self.Emit(#9'movl %eax, (%rcx)');
    end
    else
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(P.ParamName)]));
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand('_cap_' + P.ParamName)]));
      Self.Emit(#9'movq %rax, (%rcx)');
      if F.TypeDesc.IsString() then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
      end
      else if F.TypeDesc.Kind = tyClass then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
      end
      else if F.TypeDesc.Kind = tyDynArray then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _DynArrayAddRef');
      end;
    end;
  end;
end;

procedure TX86_64Backend.EmitEnvCleanupDefs(ABlock: TBlock);
{ Emit _FieldCleanup_<env> for every routine (at any nesting depth) whose
  frame allocates an anonymous-method environment record.  Thunks share the
  enclosing frame's EnvType — skipped to avoid duplicate definitions. }
var
  I, J, K: Integer;
  MD:   TMethodDecl;
  TD:   TTypeDecl;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    MD := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if (MD.EnvType <> nil) and (not MD.IsAnonThunk) then
      Self.EmitFieldCleanupFn(NativeMangle(TRecordTypeDesc(MD.EnvType).Name),
        TRecordTypeDesc(MD.EnvType), False);
    if MD.BlockEnvTypes <> nil then
      for J := 0 to MD.BlockEnvTypes.Count - 1 do
        Self.EmitFieldCleanupFn(
          NativeMangle(TRecordTypeDesc(MD.BlockEnvTypes.Items[J]).Name),
          TRecordTypeDesc(MD.BlockEnvTypes.Items[J]), False);
    if MD.Body <> nil then
      Self.EmitEnvCleanupDefs(MD.Body);
  end;
  { Enclosing frames that are METHOD bodies (Phase 3). }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    for J := 0 to TClassTypeDef(TD.Def).Methods.Count - 1 do
    begin
      MD := TMethodDecl(TClassTypeDef(TD.Def).Methods.Items[J]);
      if (MD.EnvType <> nil) and (not MD.IsAnonThunk) then
        Self.EmitFieldCleanupFn(NativeMangle(TRecordTypeDesc(MD.EnvType).Name),
          TRecordTypeDesc(MD.EnvType), False);
      if MD.BlockEnvTypes <> nil then
        for K := 0 to MD.BlockEnvTypes.Count - 1 do
          Self.EmitFieldCleanupFn(
            NativeMangle(TRecordTypeDesc(MD.BlockEnvTypes.Items[K]).Name),
            TRecordTypeDesc(MD.BlockEnvTypes.Items[K]), False);
      if MD.Body <> nil then
        Self.EmitEnvCleanupDefs(MD.Body);
    end;
  end;
end;

procedure TX86_64Backend.EmitAnonValueToSlot(AME: TAnonMethodExpr);
var
  MD: TMethodDecl;
begin
  MD := TMethodDecl(AME.LiftedDecl);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: anonymous method not lifted — semantic pass required');
  if AME.ValueSlotName = '' then
    raise ENativeCodeGenError.Create(
      'native backend: anonymous method has no value slot at line ' +
      IntToStr(AME.Line));
  Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand(AME.ValueSlotName)]));
  Self.Emit(#9'movq 8(%rcx), %rdi');
  Self.Emit(#9'pushq %rcx');
  Self.Emit(#9'callq _ClassRelease');
  Self.Emit(#9'popq %rcx');
  Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [FuncSymbolFromDecl(MD)]));
  Self.Emit(#9'movq %rax, (%rcx)');
  if MD.EnvCaptured <> nil then
  begin
    if MD.EnvSlotName <> '' then
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(MD.EnvSlotName)]))
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('__envp')]));
    Self.Emit(#9'movq %rax, 8(%rcx)');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'pushq %rcx');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(#9'popq %rcx');
  end
  else
    Self.Emit(#9'movq $0, 8(%rcx)');
  Self.Emit(#9'movq %rcx, %rax');
end;

procedure TX86_64Backend.EmitEnvCleanupDefsForMethod(AMD: TMethodDecl);
var
  L: Integer;
begin
  if (AMD.EnvType <> nil) and (not AMD.IsAnonThunk) then
    Self.EmitFieldCleanupFn(NativeMangle(TRecordTypeDesc(AMD.EnvType).Name),
      TRecordTypeDesc(AMD.EnvType), True);
  if AMD.BlockEnvTypes <> nil then
    for L := 0 to AMD.BlockEnvTypes.Count - 1 do
      Self.EmitFieldCleanupFn(
        NativeMangle(TRecordTypeDesc(AMD.BlockEnvTypes.Items[L]).Name),
        TRecordTypeDesc(AMD.BlockEnvTypes.Items[L]), True);
  if AMD.Body <> nil then
    Self.EmitEnvCleanupDefs(AMD.Body);
end;

procedure TX86_64Backend.EmitEnvCleanupDefsForInstances(AInstances: TObjectList;
                                                        ARecordInstances: TObjectList);
var
  I, J: Integer;
begin
  if AInstances <> nil then
    for I := 0 to AInstances.Count - 1 do
      for J := 0 to TGenericInstance(AInstances.Items[I]).ClassDef.Methods.Count - 1 do
        Self.EmitEnvCleanupDefsForMethod(TMethodDecl(
          TGenericInstance(AInstances.Items[I]).ClassDef.Methods.Items[J]));
  if ARecordInstances <> nil then
    for I := 0 to ARecordInstances.Count - 1 do
      for J := 0 to TGenericRecordInstance(ARecordInstances.Items[I]).RecordDef.Methods.Count - 1 do
        Self.EmitEnvCleanupDefsForMethod(TMethodDecl(
          TGenericRecordInstance(ARecordInstances.Items[I]).RecordDef.Methods.Items[J]));
end;

procedure TX86_64Backend.EmitFieldCleanupFn(const AMangledName: string;
                                            ART: TRecordTypeDesc;
                                            AWeak: Boolean);
var
  Walk: TRecordTypeDesc;
  DestroyName: string;
begin
  Self.Emit('.text');
  { AWeak: generic-instance cleanup fns are bare-named and may be carried
    by several objects in one link (BUG-004). }
  if AWeak then
    Self.Emit('.weak _FieldCleanup_' + AMangledName)
  else
    Self.Emit('.globl _FieldCleanup_' + AMangledName);
  Self.Emit('_FieldCleanup_' + AMangledName + ':');
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  Self.Emit(#9'pushq %rbx');
  Self.Emit(#9'movq %rdi, %rbx');
  if ART <> nil then
  begin
    Walk := ART;
    while Walk <> nil do
    begin
      if Walk.HasDestroyMethod then
      begin
        if Walk.DestroyResolvedQbeName <> '' then
          DestroyName := NativeMangle(Walk.DestroyResolvedQbeName)
        else
          DestroyName := NativeMangle(Walk.Name) + '_Destroy';
        Self.Emit(#9'movq %rbx, %rdi');
        Self.Emit(#9'callq ' + DestroyName);
        Break;
      end;
      Walk := Walk.Parent;
    end;
    { %rbx holds the object base and is callee-saved, so it survives the release
      calls. }
    Self.EmitRecordFieldReleases(ART, '%rbx');
  end;
  Self.Emit(#9'popq %rbx');
  Self.Emit(#9'movq %rbp, %rsp');
  Self.Emit(#9'popq %rbp');
  Self.Emit(#9'ret');
  Self.Emit('.type _FieldCleanup_' + AMangledName + ', @function');
end;

{ ---- ARC walk primitives (x86-64 leaves of the TNativeBackend walks) ---- }

function TX86_64Backend.ArcNestedBaseReg: string;
begin
  Result := '%r14';
end;

procedure TX86_64Backend.ArcPushNestedBase(AOffset: Integer;
  const ABaseReg: string);
begin
  { Derive the nested record base into %r14 (callee-saved) so the recursive
    releases/retains survive their own calls without disturbing ABaseReg. }
  Self.Emit(#9'pushq %r14');
  if AOffset > 0 then
    Self.Emit(Format(#9'leaq %d(%s), %%r14', [AOffset, ABaseReg]))
  else
    Self.Emit(Format(#9'movq %s, %%r14', [ABaseReg]));
end;

procedure TX86_64Backend.ArcPopNestedBase;
begin
  Self.Emit(#9'popq %r14');
end;

procedure TX86_64Backend.EmitWeakClearAt(AOffset: Integer;
  const ABaseReg: string);
begin
  if AOffset > 0 then
    Self.Emit(Format(#9'leaq %d(%s), %%rdi', [AOffset, ABaseReg]))
  else
    Self.Emit(Format(#9'movq %s, %%rdi', [ABaseReg]));
  Self.Emit(#9'callq _WeakClear');
end;

procedure TX86_64Backend.EmitReleaseSlotAt(AType: TTypeDesc; AOffset: Integer;
  const ABaseReg: string; AZero: Boolean);
begin
  { Load the slot's obj/data pointer (interface: the obj slot at +0). }
  if AOffset > 0 then
    Self.Emit(Format(#9'movq %d(%s), %%rdi', [AOffset, ABaseReg]))
  else
    Self.Emit(Format(#9'movq (%s), %%rdi', [ABaseReg]));
  if AType.IsString() then
    Self.Emit(#9'callq _StringRelease')
  else if AType.Kind = tyDynArray then
    Self.Emit(#9'callq _DynArrayRelease')
  else
    { tyClass and tyInterface both release the obj slot via _ClassRelease; an
      interface's itab slot at +8 is static rodata and needs no release. }
    Self.Emit(#9'callq _ClassRelease');
  if AZero then
  begin
    if AOffset > 0 then
      Self.Emit(Format(#9'movq $0, %d(%s)', [AOffset, ABaseReg]))
    else
      Self.Emit(Format(#9'movq $0, (%s)', [ABaseReg]));
  end;
end;

procedure TX86_64Backend.EmitRetainSlotAt(AType: TTypeDesc; AOffset: Integer;
  const ABaseReg: string);
begin
  if AOffset > 0 then
    Self.Emit(Format(#9'movq %d(%s), %%rdi', [AOffset, ABaseReg]))
  else
    Self.Emit(Format(#9'movq (%s), %%rdi', [ABaseReg]));
  if AType.IsString() then
    Self.Emit(#9'callq _StringAddRef')
  else if AType.Kind = tyDynArray then
    Self.Emit(#9'callq _DynArrayAddRef')
  else
    Self.Emit(#9'callq _ClassAddRef');
end;

procedure TX86_64Backend.ArcEnterArrayWalk(const ABaseReg: string);
begin
  { Hold the array base in callee-saved %r15 and recompute each element address
    into %r14.  Both are saved/restored as a PAIR (even push count) so the
    stack stays 16-byte aligned at the per-element release callq.  Keeping the
    base in %r15 (not advancing %r14 in place) keeps the addressing correct
    under nested static arrays, whose recursive call reuses %r14. }
  Self.Emit(#9'pushq %r15');
  Self.Emit(#9'pushq %r14');
  Self.Emit(Format(#9'movq %s, %%r15', [ABaseReg]));
end;

procedure TX86_64Backend.ArcArrayElemAddr(AByteOffset: Integer);
begin
  if AByteOffset > 0 then
    Self.Emit(Format(#9'leaq %d(%%r15), %%r14', [AByteOffset]))
  else
    Self.Emit(#9'movq %r15, %r14');
end;

function TX86_64Backend.ArcArrayElemReg: string;
begin
  Result := '%r14';
end;

procedure TX86_64Backend.ArcLeaveArrayWalk;
begin
  Self.Emit(#9'popq %r14');
  Self.Emit(#9'popq %r15');
end;

procedure TX86_64Backend.EmitClassSection(ATypeDecls: TObjectList;
                                          AGenericInstances: TObjectList;
                                          ASymTable: TSymbolTable);
var
  I, J, S:   Integer;
  TD:        TTypeDecl;
  TDesc:     TTypeDesc;
  RT:        TRecordTypeDesc;
  CD:        TClassTypeDef;
  MD:        TMethodDecl;
  E:         TVTableEntry;
  GI:        TGenericInstance;
  MName:     string;
  CSym:      string;
  ParentStr: string;
  ImplStr:   string;
  MethStr:      string;
  AttrsStr:     string;
  MethAttrsStr: string;
  PubCount:     Integer;
  Line:         string;
  EmitSys:      Boolean;
  BareClass:    Boolean;
begin
  { Classes in an unmangled unit (rtl.*/runtime.*/System) carry BARE symbols
    that every object referencing the class re-defines.  Under --no-incremental
    two archive members both strong-define e.g. typeinfo_TRtlPlatform and the
    link fails with a multiple-definition error (GH #174).  Emit their
    typeinfo/vtable/_FieldCleanup WEAK so duplicate definitions collapse — the
    same treatment generic instances already get.  A prefixed (normal) unit's
    class is referenced externally by other units, so it stays strong.
    EmitClassSection also runs for program-scope classes (FCurrentUnitName is
    the program, never rtl.*), which correctly stay strong. }
  BareClass := IsUnmangledUnit(FCurrentUnitName);
  { Fixed RTL class-name strings and stubs for TObject and TCustomAttribute.
    Emitted exactly once across the whole program (the first class section that
    runs); guarded so multiple units + the program do not redefine the symbols.
    In separate-compilation (incremental unit) mode they are NOT emitted at all —
    the program object provides the single definition, so emitting them in each
    unit object would collide at link time. }
  EmitSys := (not FSystemDefsEmitted) and (not FSeparateCompile);
  Self.Emit('.data');
  if EmitSys then
  begin
    Self.EmitClassNameString('TObject', 'TObject');
    Self.EmitClassNameString('TCustomAttribute', 'TCustomAttribute');
  end;

  { User class data: name strings, method tables, typeinfo, vtables. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    { Re-assert the viewing context before EVERY FindType.  Resolving a prior
      class in this loop (its parent/field/method types via ClassSymName ->
      Lookup -> the uses-chain walk) can leave FSymTable.DefineOwningUnit
      pointing at a dependency unit.  If it has drifted, FindType for one of THIS
      unit's own implementation-section (IsImplPrivate) classes is suppressed by
      Lookup's cross-unit-leak guard and returns nil — so the class is skipped
      and its typeinfo / vtable / _FieldCleanup are NEVER emitted, leaving a
      dangling reference the linker binds to garbage (an out-of-range metaclass
      crash, e.g. via RegisterTest).  Pin DOU to the unit being emitted so an
      owned impl-private class always resolves. }
    if (ASymTable <> nil) and (FCurrentUnitName <> '') then
      ASymTable.DefineOwningUnit := FCurrentUnitName;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    CD := TClassTypeDef(TD.Def);
    CSym := Self.ClassSymNameForDecl(TD);

    { Class-name string blob — the symbol uses the unit-prefixed name so
      __cn_ matches the typeinfo class-name reference, but the content is
      the bare class name (what ClassName must return at runtime). }
    Self.EmitClassNameString(CSym, TD.Name);

    { Published-method table: count, then (nameref, codeptr, sigref)
      triples.  The sig is an immortal string of per-param kind codes
      (0 = parameterless — see MethodParamSig). }
    PubCount := 0;
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).IsPublished then
        Inc(PubCount);
    if PubCount > 0 then
    begin
      { Emit name + param-sig strings for published methods.  The blobs
        must precede the table so its .quad sequence is uninterrupted. }
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if MD.IsPublished then
        begin
          Self.EmitClassNameString(MD.Name, MD.Name);
          if MethodParamSig(MD) <> '' then
            Self.EmitClassNameString('__sig_' + TD.Name + '_' + MD.Name,
              MethodParamSig(MD));
        end;
      end;
      Self.Emit('.balign 8');
      { Bare (unmangled-unit) methods table is re-defined by every referencing
        object — mark it WEAK too (GH #174). }
      if BareClass then
        Self.Emit('.weak methods_' + CSym)
      else
        Self.Emit('.globl methods_' + CSym);
      Self.Emit('methods_' + CSym + ':');
      Self.Emit(Format(#9'.quad %d', [PubCount]));
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if not MD.IsPublished then Continue;
        Self.Emit(Format(#9'.quad __cn_%s + 12', [NativeMangle(MD.Name)]));
        Self.Emit(Format(#9'.quad %s', [MethodEmitNameNative(MD, TD.Name, MD.Name)]));
        if MethodParamSig(MD) <> '' then
          Self.Emit(Format(#9'.quad __cn_%s + 12',
            [NativeMangle('__sig_' + TD.Name + '_' + MD.Name)]))
        else
          Self.Emit(#9'.quad 0');
      end;
      MethStr := 'methods_' + CSym;
    end
    else
      MethStr := '0';
  end;

  { Generic class instances — emit class-name string blobs. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    Self.EmitClassNameString(Self.ClassSymName(GI.TypeName), GI.TypeName);
  end;

  { Typeinfo blocks — must come after all class-name strings are emitted.
    System-class typeinfo is emitted once (EmitSys). }
  if EmitSys then
  begin
    Self.Emit('.balign 8');
    { Global so separately-compiled unit objects (incremental mode) can
      reference the single program-provided system typeinfo. }
    Self.Emit('.globl typeinfo_TObject');
    Self.Emit('typeinfo_TObject:');
    Self.Emit(#9'.quad 0');          { parent = nil }
    Self.Emit(#9'.quad 0');          { impllist = nil }
    Self.Emit(#9'.quad __cn_TObject + 12');
    Self.Emit(#9'.quad 0');          { methods = nil }
    Self.Emit(#9'.quad 8');          { size = 8 (vptr only) }
    Self.Emit(#9'.quad _FieldCleanup_TObject');
    Self.Emit(#9'.quad vtable_TObject');
    Self.Emit(#9'.quad 0');          { attrs = nil }
    Self.Emit(#9'.quad 0');          { method attrs = nil }

    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_TCustomAttribute');
    Self.Emit('typeinfo_TCustomAttribute:');
    Self.Emit(#9'.quad typeinfo_TObject');
    Self.Emit(#9'.quad 0');
    Self.Emit(#9'.quad __cn_TCustomAttribute + 12');
    Self.Emit(#9'.quad 0');
    Self.Emit(#9'.quad 8');
    Self.Emit(#9'.quad _FieldCleanup_TCustomAttribute');
    Self.Emit(#9'.quad vtable_TCustomAttribute');
    Self.Emit(#9'.quad 0');
    Self.Emit(#9'.quad 0');
  end;

  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    CSym := Self.ClassSymNameForDecl(TD);

    if RT.Parent <> nil then
      ParentStr := 'typeinfo_' + Self.ClassSymName(RT.Parent.Name)
    else
      ParentStr := '0';
    { Point at the impllist when this class OR any ancestor implements an
      interface — a descendant inherits its parent's interfaces and gets its
      own impllist (issue #130 bug3). }
    if Self.ClassOrAncestorImplements(RT) then
      ImplStr := 'impllist_' + CSym
    else
      ImplStr := '0';

    { Rebuild MethStr for typeinfo (already computed above but not stored). }
    CD := TClassTypeDef(TD.Def);
    PubCount := 0;
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).IsPublished then
        Inc(PubCount);
    if PubCount > 0 then
      MethStr := 'methods_' + CSym
    else
      MethStr := '0';

    { Attribute RTTI tables at typeinfo slots 7 and 8.  Emitted before the
      typeinfo so the symbols are defined when the slots reference them;
      nil when the class carries no attributes.  Mirrors the QBE backend. }
    Self.EmitAttrTables(CD, CSym, AttrsStr, MethAttrsStr);

    Self.Emit('.balign 8');
    if BareClass then
      Self.Emit('.weak typeinfo_' + CSym)
    else
      Self.Emit('.globl typeinfo_' + CSym);
    Self.Emit('typeinfo_' + CSym + ':');
    Self.Emit(#9'.quad ' + ParentStr);
    Self.Emit(#9'.quad ' + ImplStr);
    Self.Emit(Format(#9'.quad __cn_%s + 12', [NativeMangle(CSym)]));
    Self.Emit(#9'.quad ' + MethStr);
    Self.Emit(Format(#9'.quad %d', [RT.TotalSize()]));
    Self.Emit(#9'.quad _FieldCleanup_' + CSym);
    Self.Emit(#9'.quad vtable_' + CSym);
    Self.Emit(#9'.quad ' + AttrsStr);      { attrs }
    Self.Emit(#9'.quad ' + MethAttrsStr);  { method attrs }
  end;

  { Typeinfo blocks for generic class instances.  All generic-instance
    symbols are emitted WEAK: any number of objects in a link may carry the
    identical bare-named copy and the linker keeps one (BUG-004). }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    MName := Self.ClassSymName(GI.TypeName);
    if RT.Parent <> nil then
      ParentStr := 'typeinfo_' + Self.ClassSymName(RT.Parent.Name)
    else
      ParentStr := '0';
    if RT.ImplementsCount() > 0 then
      ImplStr := 'impllist_' + MName
    else
      ImplStr := '0';
    Self.Emit('.balign 8');
    Self.Emit('.weak typeinfo_' + MName);
    Self.Emit('typeinfo_' + MName + ':');
    Self.Emit(#9'.quad ' + ParentStr);
    Self.Emit(#9'.quad ' + ImplStr);
    Self.Emit(Format(#9'.quad __cn_%s + 12', [MName]));
    Self.Emit(#9'.quad 0');
    Self.Emit(Format(#9'.quad %d', [RT.TotalSize()]));
    Self.Emit(#9'.quad _FieldCleanup_' + MName);
    Self.Emit(#9'.quad vtable_' + MName);
    Self.Emit(#9'.quad 0');
    Self.Emit(#9'.quad 0');
  end;

  { Field cleanup functions for the fixed RTL classes (once). }
  if EmitSys then
  begin
    Self.EmitFieldCleanupFn('TObject', nil, False);
    Self.EmitFieldCleanupFn('TCustomAttribute', nil, False);
  end;
  { Field cleanup for user classes. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    Self.EmitFieldCleanupFn(Self.ClassSymNameForDecl(TD), RT, BareClass);
  end;
  { Field cleanup for generic class instances. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    Self.EmitFieldCleanupFn(Self.ClassSymName(GI.TypeName), RT, True);
  end;

  { Vtables — must be in .data (pointers to other data symbols). }
  Self.Emit('.data');
  if EmitSys then
  begin
    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_TObject');
    Self.Emit('vtable_TObject:');
    Self.Emit(#9'.quad typeinfo_TObject');
    Self.Emit(#9'.quad TObject_Destroy');
    Self.Emit(#9'.quad TObject_ToString');

    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_TCustomAttribute');
    Self.Emit('vtable_TCustomAttribute:');
    Self.Emit(#9'.quad typeinfo_TCustomAttribute');
    Self.Emit(#9'.quad TObject_Destroy');
    Self.Emit(#9'.quad TObject_ToString');
  end;

  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if not RT.HasVTable() then Continue;
    CSym := Self.ClassSymNameForDecl(TD);

    Self.Emit('.balign 8');
    if BareClass then
      Self.Emit('.weak vtable_' + CSym)
    else
      Self.Emit('.globl vtable_' + CSym);
    Self.Emit('vtable_' + CSym + ':');
    Self.Emit(#9'.quad typeinfo_' + CSym);
    for S := 0 to RT.VTableCount() - 1 do
    begin
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        Line := #9'.quad _AbstractMethodError'
      else
      begin
        { E.ImplName may have a '$' prefix (QBE convention) — strip it for native.
          Use StrAt for 0-based string indexing. }
        if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = 36) then
          Line := #9'.quad ' + NativeMangle(StrCopyTail(E.ImplName, 1))
        else
          Line := #9'.quad ' + NativeMangle(E.ImplName);
      end;
      Self.Emit(Line);
    end;
  end;

  { Vtables for generic class instances (WEAK — see typeinfo loop). }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    if not RT.HasVTable() then Continue;
    MName := Self.ClassSymName(GI.TypeName);
    Self.Emit('.balign 8');
    Self.Emit('.weak vtable_' + MName);
    Self.Emit('vtable_' + MName + ':');
    Self.Emit(#9'.quad typeinfo_' + MName);
    for S := 0 to RT.VTableCount() - 1 do
    begin
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        Line := #9'.quad _AbstractMethodError'
      else
      begin
        if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = 36) then
          Line := #9'.quad ' + NativeMangle(StrCopyTail(E.ImplName, 1))
        else
          Line := #9'.quad ' + NativeMangle(E.ImplName);
      end;
      Self.Emit(Line);
    end;
  end;

  if EmitSys then
    FSystemDefsEmitted := True;
end;

{ Lower an interface method call.  The receiver is an interface fat pointer
  (obj + itab) named AObjName; AIntf supplies the method's slot index.  The
  itab is a flat array of method-code pointers (no leading typeinfo slot, in
  contrast to a vtable), so the slot offset is MethodIndex * PtrSize.

  Calling sequence mirrors EmitMethodCallExpr: evaluate args left-to-right onto
  the stack, load the obj (Self) and the resolved code pointer into caller-saved
  scratch (%r10/%r11) that survive the pop loop, pop args into %rsi.. (shifted
  by one for Self in %rdi), set %rdi := obj, then `callq *%r11`. }
procedure TX86_64Backend.EmitInterfaceCall(const AObjName: string;
                                           AIsGlobal: Boolean;
                                           AIsVarParam: Boolean;
                                           AIntf: TInterfaceTypeDesc;
                                           const AMethName: string;
                                           AArgs: TObjectList);
var
  I, SlotOff, Ps, ArgN: Integer;
  Arg: TASTExpr;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
  RecvOnStack: Boolean;
  DiscSz: Integer;
  CleanBytes: Integer;
  SlotClasses: TList<Integer>;
begin
  { x86_64: pointers are 8 bytes (this backend's invariant, like the rest of the
    file).  i386/arm64 backends will be separate TNativeBackend subclasses. }
  Ps := 8;
  ArgN := 0;
  if AArgs <> nil then ArgN := AArgs.Count;
  RecvOnStack := False;
  if (AObjExpr <> nil) and (AObjExpr is TFuncCallExpr) then
  begin
    { Function-call receiver (GetDriver().Info()): evaluate it FIRST via the
      sret convention — it is a call and would clobber pushed args.  The
      owned (+1) fat pair stays at (%rsp) until after the dispatch, then the
      obj is released. }
    Self.EmitIntfSretCall(TFuncCallExpr(AObjExpr));
    RecvOnStack := True;
  end
  else if (AObjExpr <> nil) and (AObjExpr is TMethodCallExpr) and
          (TMethodCallExpr(AObjExpr).ResolvedClassType <> nil) then
  begin
    { Method-call receiver (B.Get().Value(), L.Get(0).Value()): same shape as
      the TFuncCallExpr case above and it must take the same sret path.  A
      call result has no NAME, so without this arm the receiver fell through
      to the named-slot branch below with an empty AObjName and emitted
      `movq _obj(%rip)` / `movq _itab(%rip)` — symbols that are never
      defined.  The linker bound them to arbitrary addresses, so the program
      compiled clean and segfaulted at run time.  Reached most often through
      a generic container monomorphised at an interface element type.

      Which sret helper applies depends on the RECEIVER of the inner call,
      not on its return type: a class receiver (B.Get, where B: TBox<IFoo>)
      is a direct call, while an interface receiver dispatches through the
      itab.  Same discrimination as the assignment paths below. }
    if TMethodCallExpr(AObjExpr).ResolvedClassType.Kind = tyInterface then
      Self.EmitIntfSretMethodCall(TMethodCallExpr(AObjExpr))
    else
      Self.EmitClassIntfSretMethodCall(TMethodCallExpr(AObjExpr));
    RecvOnStack := True;
  end;
  DiscSz := 0;
  if ADiscardIntfRet then
  begin
    { Throwaway sret buffer for a DISCARDED interface return: without it the
      callee would write its 16-byte fat-pointer return through %rdi. }
    Self.Emit(#9'subq $16, %rsp');
    Self.Emit(#9'movq $0, (%rsp)');
    Self.Emit(#9'movq $0, 8(%rsp)');
    DiscSz := 16;
  end;
  { Hoist record-call args and (shape-classified) string args — the
    implementing method's const-ness is invisible at an interface call site,
    so every string-typed value argument is protected by shape.  The var
    flags recorded on the interface type mark by-reference positions. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := AIntf.MethodParamVarFlagsStr(AIntf.MethodIndex(AMethName));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, AArgs, HD, HK);
  Pushed := 0;
  { Evaluate args left-to-right and push them.  Interface args push two values
    (obj then itab); all other args push one.  Pass nil as the TMethodParam so
    EmitMethodArgPush falls through to scalar for non-interface args. }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      { Hoisted record-call or string argument — reload the saved value. }
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      { var/out position: pass the slot ADDRESS — same rule as direct
        calls; covers managed types (string, dynarray) the callee rebinds. }
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in interface dispatch');
    end
    else if (Arg.ResolvedType <> nil) and IsFloatFamily(Arg.ResolvedType) then
    begin
      { Float scalar argument: materialise to %xmm0 and push its 8-byte bit
        pattern as one slot; EmitIntfRegArgs routes it into an xmm register
        instead of an integer one. }
      Self.EmitExprToXmm0(Arg);
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, 0(%rsp)');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    { Track bytes pushed so far — hoisted-value reloads are %rsp-relative.
      var positions always occupy one slot, even for interface-typed args. }
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Load obj (Self) into %r10 and the itab into %rax, then index the itab.
    For a field receiver the fat pointer is contiguous (obj at the field
    address, itab at +8); EmitInterfaceFieldAddr leaves that address in %r10.
    The receiver shapes that need EmitExprToEax (FA.Base) are not yet reachable
    here — args are already on the stack, so only the call-free shapes (class
    access, local/global record, var-param) are safe; reject the rest loudly. }
  if RecvOnStack then
  begin
    { Receiver fat pair sits above the discard buffer + hoist region + args. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%r10', [Pushed + HTotal + DiscSz]));
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [Pushed + HTotal + DiscSz + 8]));
  end
  else if (AObjExpr <> nil) and (AObjExpr is TFieldAccessExpr) then
  begin
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');   { itab }
    Self.Emit(#9'movq (%r10), %r10');    { obj }
  end
  else if (AObjExpr <> nil) and (AObjExpr is TIdentExpr) and
          TIdentExpr(AObjExpr).IsImplicitSelf and
          (TIdentExpr(AObjExpr).ImplicitFieldInfo <> nil) then
  begin
    { Interface-typed field of Self as receiver (bare `FField.M()` inside a
      method): the fat pointer sits at Self + field offset (obj at +0,
      itab at +8).  Guards against the named-global fallback emitting bogus
      bare _obj/_itab labels. }
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    if TFieldInfo(TIdentExpr(AObjExpr).ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r10',
        [TFieldInfo(TIdentExpr(AObjExpr).ImplicitFieldInfo).Offset]));
    Self.Emit(#9'movq 8(%r10), %rax');   { itab }
    Self.Emit(#9'movq (%r10), %r10');    { obj }
  end
  else if (AObjExpr <> nil) and (AObjExpr is TStringSubscriptExpr) and
          (TStringSubscriptExpr(AObjExpr).StrExpr.ResolvedType <> nil) and
          (TStringSubscriptExpr(AObjExpr).StrExpr.ResolvedType.Kind = tyStaticArray) then
  begin
    { Static-array interface element receiver (Arr[I].M()): the element is a
      contiguous fat pointer (obj at the element address, itab at +8).  The
      static-array guard keeps a class default-property subscript out — it is
      subscript-shaped but has no array base, and would crash the compiler
      inside EmitIntfStaticElemAddr. }
    Self.EmitIntfStaticElemAddr(TStringSubscriptExpr(AObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');   { itab }
    Self.Emit(#9'movq (%r10), %r10');    { obj }
  end
  else if (AObjExpr <> nil) and (AObjExpr is TStringSubscriptExpr) and
          (TStringSubscriptExpr(AObjExpr).StrExpr.ResolvedType <> nil) and
          (TStringSubscriptExpr(AObjExpr).StrExpr.ResolvedType.Kind in
             [tyDynArray, tyOpenArray]) then
  begin
    { Dynamic / open-array interface element receiver (Arr[I].M()): the fat
      pointer lives at data_ptr + index*16 (BUG-20260720-qbe-dynarray-intf-
      elem-read, native side). }
    Self.EmitIntfDynElemAddr(TStringSubscriptExpr(AObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');   { itab }
    Self.Emit(#9'movq (%r10), %r10');    { obj }
  end
  else if AIsVarParam then
  begin
    { var/out interface param receiver: the slot holds the address of the
      caller's contiguous fat pointer — obj at +0, itab at +8. }
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(AObjName)]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if Self.IsCaptured(AObjName) then
  begin
    { Captured interface local (BUG-038): the capture slot holds the ADDRESS
      of the enclosing routine's contiguous fat pointer — obj at +0, itab at
      +8 (the same shape as a var/out interface param). }
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('_cap_' + AObjName)]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%r10', [Self.IntfObjOperand(AObjName, AIsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax', [Self.IntfItabOperand(AObjName, AIsGlobal)]));
  end;
  SlotOff := AIntf.MethodIndex(AMethName) * Ps;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Classify the pushed slots for the register-load phase, mirroring the
    push loop above: hoist-reloaded and var slots are integer; interface
    args are two integer slots (obj + itab); float args are xmm slots. }
  SlotClasses := TList<Integer>.Create();
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if HK.Get(I) >= akRecCall then
      SlotClasses.Add(0)
    else if Self.VarFlagAt(VFlags, I) then
      SlotClasses.Add(0)
    else if (Arg.ResolvedType <> nil) and
            (Arg.ResolvedType.Kind = tyInterface) then
    begin
      SlotClasses.Add(0);
      SlotClasses.Add(0);
    end
    else if (Arg.ResolvedType <> nil) and IsFloatFamily(Arg.ResolvedType) then
      SlotClasses.Add(1)
    else
      SlotClasses.Add(0);
  end;
  if ADiscardIntfRet then
  begin
    { sret convention: %rdi = buffer, %rsi = Self, visible args from %rdx.
      EmitIntfRegArgs spills integer slots beyond the registers to the stack
      (Self + sret already occupy two); it returns the extra bytes between
      %rsp and the hoist region at call time, so the buffer leaq shifts by
      them. }
    CleanBytes := Self.EmitIntfRegArgs(SlotClasses, 2);
    Self.Emit(Format(#9'leaq %d(%%rsp), %%rdi', [HTotal + CleanBytes]));
    Self.Emit(#9'movq %r10, %rsi');
  end
  else
  begin
    CleanBytes := Self.EmitIntfRegArgs(SlotClasses, 1);
    Self.Emit(#9'movq %r10, %rdi');
  end;
  SlotClasses.Free();
  Self.Emit(#9'callq *%r11');
  if CleanBytes > 0 then
    { Reclaim the spill region + still-pushed slots so the epilogue below
      sees the register-only stack layout.  addq preserves the return
      registers (%rax/%rdx/%xmm0). }
    Self.Emit(Format(#9'addq $%d, %%rsp', [CleanBytes]));
  Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  if ADiscardIntfRet then
  begin
    { Discarded owned return: release the obj half; statement position, so
      no live result registers to preserve. }
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'addq $16, %rsp');
  end;
  if RecvOnStack then
  begin
    { Release the owned receiver pair; preserve the dispatch result regs
      (this path also serves expression position). }
    Self.Emit(#9'subq $24, %rsp');
    Self.Emit(#9'movq %rax, 0(%rsp)');
    Self.Emit(#9'movq %rdx, 8(%rsp)');
    Self.Emit(#9'movsd %xmm0, 16(%rsp)');
    Self.Emit(#9'movq 24(%rsp), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq 0(%rsp), %rax');
    Self.Emit(#9'movq 8(%rsp), %rdx');
    Self.Emit(#9'movsd 16(%rsp), %xmm0');
    Self.Emit(#9'addq $40, %rsp');
  end;
  HD.Free();
  HK.Free();
end;

procedure TX86_64Backend.EmitInterfaceFieldCall(AFld: TFieldInfo;
  AIntf: TInterfaceTypeDesc; const AMethName: string; AArgs: TObjectList);
{ Dispatch an interface method call through a class field.  The fat pointer
  lives at Self + AFld.Offset (obj) and Self + AFld.Offset + 8 (itab). }
var
  I, SlotOff, ArgN: Integer;
  Arg: TASTExpr;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
  CleanBytes: Integer;
  SlotClasses: TList<Integer>;
begin
  ArgN := 0;
  if AArgs <> nil then ArgN := AArgs.Count;
  if ADiscardIntfRet then
  begin
    { Throwaway sret buffer for a DISCARDED interface return: without it the
      callee would write its 16-byte fat-pointer return through %rdi. }
    Self.Emit(#9'subq $16, %rsp');
    Self.Emit(#9'movq $0, (%rsp)');
    Self.Emit(#9'movq $0, 8(%rsp)');
  end;
  { Same unknown-signature hoist as EmitInterfaceCall. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := AIntf.MethodParamVarFlagsStr(AIntf.MethodIndex(AMethName));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, AArgs, HD, HK);
  Pushed := 0;
  { Push args left-to-right; interface args push obj then itab (2 slots). }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      { Hoisted record-call or string argument — reload the saved value. }
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      { var/out position: pass the slot ADDRESS — same rule as direct
        calls; covers managed types (string, dynarray) the callee rebinds. }
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in field dispatch');
    end
    else if (Arg.ResolvedType <> nil) and IsFloatFamily(Arg.ResolvedType) then
    begin
      { Float scalar argument: push its 8-byte xmm bit pattern as one slot;
        EmitIntfRegArgs routes it into an xmm register. }
      Self.EmitExprToXmm0(Arg);
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, 0(%rsp)');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    { Track bytes pushed so far — hoisted-value reloads are %rsp-relative.
      var positions always occupy one slot, even for interface-typed args. }
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Load Self and compute field base; use %r11 for base pointer. }
  Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('Self')]));
  if AFld.Offset > 0 then
    Self.Emit(Format(#9'addq $%d, %%r11', [AFld.Offset]));
  { Load obj into %r10, itab into %rax. }
  Self.Emit(#9'movq (%r11), %r10');
  Self.Emit(#9'movq 8(%r11), %rax');
  SlotOff := AIntf.MethodIndex(AMethName) * 8;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Classify the pushed slots for the register-load phase, mirroring the
    push loop above (see EmitInterfaceCall). }
  SlotClasses := TList<Integer>.Create();
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if HK.Get(I) >= akRecCall then
      SlotClasses.Add(0)
    else if Self.VarFlagAt(VFlags, I) then
      SlotClasses.Add(0)
    else if (Arg.ResolvedType <> nil) and
            (Arg.ResolvedType.Kind = tyInterface) then
    begin
      SlotClasses.Add(0);
      SlotClasses.Add(0);
    end
    else if (Arg.ResolvedType <> nil) and IsFloatFamily(Arg.ResolvedType) then
      SlotClasses.Add(1)
    else
      SlotClasses.Add(0);
  end;
  if ADiscardIntfRet then
  begin
    { sret convention: %rdi = buffer, %rsi = Self, visible args from %rdx.
      EmitIntfRegArgs spills integer slots beyond the registers; its return
      value shifts the buffer leaq (see EmitInterfaceCall). }
    CleanBytes := Self.EmitIntfRegArgs(SlotClasses, 2);
    Self.Emit(Format(#9'leaq %d(%%rsp), %%rdi', [HTotal + CleanBytes]));
    Self.Emit(#9'movq %r10, %rsi');
  end
  else
  begin
    CleanBytes := Self.EmitIntfRegArgs(SlotClasses, 1);
    Self.Emit(#9'movq %r10, %rdi');
  end;
  SlotClasses.Free();
  Self.Emit(#9'callq *%r11');
  if CleanBytes > 0 then
    { Reclaim spill region + still-pushed slots (addq preserves the return
      registers) so the epilogue sees the register-only layout. }
    Self.Emit(Format(#9'addq $%d, %%rsp', [CleanBytes]));
  Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  if ADiscardIntfRet then
  begin
    { Discarded owned return: release the obj half (statement position). }
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'addq $16, %rsp');
  end;
  HD.Free();
  HK.Free();
end;

{ An interface method maps to one of ARec's vtable slots.  When that slot is
  abstract, the itab entry must point at _AbstractMethodError (the concrete
  symbol does not exist on an abstract base). }
function TX86_64Backend.IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                              const AMethName: string): Boolean;
var
  Slot: Integer;
begin
  Slot := ARec.FindVTableSlot(AMethName);
  if Slot < 0 then
    Result := False
  else
    Result := ARec.VTableEntryAt(Slot).IsAbstract;
end;

{ True when AClassRT or any of its ancestors implements at least one interface.
  A descendant inherits its parent's interface implementations (issue #130
  bug3), so the whole class parent chain must be scanned. }
function TX86_64Backend.ClassOrAncestorImplements(AClassRT: TRecordTypeDesc): Boolean;
var
  Walk: TRecordTypeDesc;
begin
  Walk := AClassRT;
  while Walk <> nil do
  begin
    if Walk.ImplementsCount() > 0 then Exit(True);
    Walk := Walk.Parent;
  end;
  Result := False;
end;

{ Native label for AClassRT's implementation of interface method AMethName.
  Prefers the vtable slot's resolved ImplName (so an inherited method points at
  the ancestor's body and an override at the descendant's — issue #130 bug3);
  the ImplName may carry a leading '$' (QBE convention) which is stripped, then
  NativeMangle is applied.  Falls back to the declaring-class method name. }
function TX86_64Backend.ItabMethodRefNative(AClassRT: TRecordTypeDesc;
  ATD: TTypeDecl; const AMethName: string;
  ATypeDecls: TObjectList): string;
var
  Slot:    Integer;
  E:       TVTableEntry;
  CurTD:   TTypeDecl;
  CD:      TClassTypeDef;
  MD:      TMethodDecl;
  I:       Integer;
  CurName: string;
  AncRT:   TRecordTypeDesc;
  Sym:     string;
begin
  if AClassRT <> nil then
  begin
    Slot := AClassRT.FindVTableSlot(AMethName);
    if Slot >= 0 then
    begin
      E := AClassRT.VTableEntryAt(Slot);
      if (E <> nil) and (E.ImplName <> '') then
      begin
        if StrAt(E.ImplName, 0) = 36 then   { 36 = '$' }
          Exit(NativeMangle(StrCopyTail(E.ImplName, 1)))
        else
          Exit(NativeMangle(E.ImplName));
      end;
    end;
  end;
  { No vtable slot — a non-virtual interface method.  Walk the AST class chain
    (self, then ParentName ancestors) to the nearest class that DECLARES the
    method and name $<declaringclass>_<method>; naming $<thisclass>_<method> for
    an inherited method links to a symbol that does not exist (issue #130 bug3). }
  CurTD := ATD;
  while CurTD <> nil do
  begin
    if not (CurTD.Def is TClassTypeDef) then break;
    CD := TClassTypeDef(CurTD.Def);
    MD := FindMethodInClassDef(CD, AMethName);
    if MD <> nil then
      Exit(MethodEmitNameNative(MD, CurTD.Name, AMethName));
    CurName := CD.ParentName;
    CurTD   := nil;
    if (CurName <> '') and (ATypeDecls <> nil) then
      for I := 0 to ATypeDecls.Count - 1 do
        if SameText(TTypeDecl(ATypeDecls.Items[I]).Name, CurName) then
        begin
          CurTD := TTypeDecl(ATypeDecls.Items[I]);
          break;
        end;
  end;
  { The AST walk above only sees THIS unit's declarations, so it runs out when
    the declaring ancestor lives in another unit.  Climb the descriptor chain
    instead -- Parent is populated across units, and AddMethodSym records every
    method's emitted symbol (including non-virtual ones, which have no vtable
    slot).  The first hit is the NEAREST declarer, which is exactly Pascal's
    resolution order. }
  AncRT := AClassRT;
  while AncRT <> nil do
  begin
    Sym := AncRT.FindMethodSym(AMethName);
    if Sym <> '' then
      Exit(NativeMangle(Sym));
    AncRT := AncRT.Parent;
  end;
  { Nothing in the chain declares it.  Naming <thisclass>_<method> here is what
    turned this into a load-time "undefined symbol" instead of a compile error,
    so fail loudly (matching the arm64 backend's posture). }
  raise ENativeCodeGenError.Create(
    'native backend: no implementation found for interface method ''' +
    AMethName + ''' on class ''' + ATD.Name + '''');
end;

{ Emit typeinfo / itab / impllist blocks for interfaces and implementing
  classes.  Mirrors the QBE backend's EmitInterfaceDefs:

    typeinfo_IFoo:        .quad 0            (address IS the identity token)
    itab_TFoo_IFoo:       .quad TFoo_DoIt, .quad TFoo_GetVal   (decl order)
    impllist_TFoo:        .quad typeinfo_IFoo, .quad itab_TFoo_IFoo, .quad 0

  impllist is a NULL-terminated array of (typeinfo, itab) pairs, walked by the
  _GetItab runtime helper for `as`-casts. }
procedure TX86_64Backend.EmitInterfaceDefs(ATypeDecls: TObjectList;
                                           AGenericInstances: TObjectList;
                                           AGenericIntfInstances: TObjectList;
                                           ASymTable: TSymbolTable);
var
  I, J, K:    Integer;
  TD:         TTypeDecl;
  TDesc:      TTypeDesc;
  IntfDesc:   TInterfaceTypeDesc;
  ClassRT:    TRecordTypeDesc;
  GI:         TGenericInstance;
  GII:        TGenericInterfaceInstance;
  CSym:       string;
  MName:      string;
  MethName:   string;
  MethRef:    string;
  MDecl:      TMethodDecl;
  EmitIntfs:  TObjectList;
  IntfWalk:   TInterfaceTypeDesc;
  ClassWalk:  TRecordTypeDesc;
  BareClass:  Boolean;
begin
  { A class in an unmangled unit (rtl.*/runtime.*/System) has BARE itab/impllist
    symbols that every inlining object re-defines — emit them WEAK so archive
    members collapse instead of colliding (GH #174), matching EmitClassSection's
    treatment of typeinfo/vtable/methods.  Program-scope classes stay strong
    (FCurrentUnitName is the program, never rtl.*). }
  BareClass := IsUnmangledUnit(FCurrentUnitName);
  { Typeinfo blocks for every plain interface. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TInterfaceTypeDef) then Continue;
    CSym := Self.ClassSymNameForDecl(TD);
    Self.Emit('.balign 8');
    { A bare (unmangled-unit) interface's own typeinfo is re-defined by every
      inlining object too — mark it WEAK (GH #174). }
    if BareClass then
      Self.Emit('.weak typeinfo_' + CSym)
    else
      Self.Emit('.globl typeinfo_' + CSym);
    Self.Emit('typeinfo_' + CSym + ':');
    Self.Emit(#9'.quad 0');
  end;

  { Typeinfo blocks for generic interface instances (WEAK — bare-named,
    any object may carry the copy; BUG-004). }
  for I := 0 to AGenericIntfInstances.Count - 1 do
  begin
    GII := TGenericInterfaceInstance(AGenericIntfInstances.Items[I]);
    Self.Emit('.balign 8');
    Self.Emit('.weak typeinfo_' + GII.InstName);
    Self.Emit('typeinfo_' + GII.InstName + ':');
    Self.Emit(#9'.quad 0');
  end;

  { Itab and impllist blocks for each implementing class. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    ClassRT := TRecordTypeDesc(TDesc);
    { Skip only when neither this class NOR any ancestor implements an interface
      — a descendant inherits its parent's interfaces (issue #130 bug3). }
    if not Self.ClassOrAncestorImplements(ClassRT) then Continue;
    CSym := Self.ClassSymNameForDecl(TD);

    { Collect each implemented interface PLUS every ancestor on its parent
      chain so a class instance can narrow directly to a base interface (an
      ancestor's methods are a prefix of the descendant's itab — same impl
      pointers).  Also walk the CLASS parent chain to pick up interfaces an
      ancestor implements (issue #130 bug3).  Dedup keeps one itab per
      (class, interface). }
    EmitIntfs := TObjectList.Create(False);
    try
      ClassWalk := ClassRT;
      while ClassWalk <> nil do
      begin
        for J := 0 to ClassWalk.ImplementsCount() - 1 do
        begin
          IntfWalk := ClassWalk.ImplementsIntfAt(J);
          while IntfWalk <> nil do
          begin
            if EmitIntfs.IndexOf(IntfWalk) < 0 then EmitIntfs.Add(IntfWalk);
            IntfWalk := IntfWalk.Parent;
          end;
        end;
        ClassWalk := ClassWalk.Parent;
      end;

      { One itab per interface — a flat array of method-code ptrs in interface
        declaration order. }
      for J := 0 to EmitIntfs.Count - 1 do
      begin
        IntfDesc := TInterfaceTypeDesc(EmitIntfs.Items[J]);
        Self.Emit('.balign 8');
        if BareClass then
          Self.Emit('.weak itab_' + CSym + '_' + Self.IntfTypeInfoName(IntfDesc.Name))
        else
          Self.Emit('.globl itab_' + CSym + '_' + Self.IntfTypeInfoName(IntfDesc.Name));
        Self.Emit('itab_' + CSym + '_' + Self.IntfTypeInfoName(IntfDesc.Name) + ':');
        for K := 0 to IntfDesc.MethodCount() - 1 do
        begin
          MethName := IntfDesc.MethodName(K);
          if Self.IsAbstractClassMethod(ClassRT, MethName) then
            MethRef := '_AbstractMethodError'
          else
            { Resolve via the vtable so an inherited (non-overridden) method
              points at the ancestor's body and an override at the descendant's
              (issue #130 bug3). }
            MethRef := Self.ItabMethodRefNative(ClassRT, TD, MethName, ATypeDecls);
          Self.Emit(#9'.quad ' + MethRef);
        end;
      end;

      { One impllist per class: NULL-terminated (typeinfo, itab) pairs.
        Includes ancestor interfaces so _GetItab(obj, typeinfo_IBase) resolves. }
      Self.Emit('.balign 8');
      if BareClass then
        Self.Emit('.weak impllist_' + CSym)
      else
        Self.Emit('.globl impllist_' + CSym);
      Self.Emit('impllist_' + CSym + ':');
      for J := 0 to EmitIntfs.Count - 1 do
      begin
        IntfDesc := TInterfaceTypeDesc(EmitIntfs.Items[J]);
        Self.Emit(#9'.quad typeinfo_' + Self.IntfTypeInfoName(IntfDesc.Name));
        Self.Emit(#9'.quad itab_' + CSym + '_' + Self.IntfTypeInfoName(IntfDesc.Name));
      end;
      Self.Emit(#9'.quad 0');
    finally
      EmitIntfs.Free();
    end;
  end;

  { Itab and impllist for generic class instances that implement interfaces. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    ClassRT := TRecordTypeDesc(GI.TypeDesc);
    if ClassRT.ImplementsCount() = 0 then Continue;
    MName := Self.ClassSymName(GI.TypeName);

    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      CSym := Self.IntfTypeInfoName(IntfDesc.Name);
      Self.Emit('.balign 8');
      Self.Emit('.weak itab_' + MName + '_' + CSym);
      Self.Emit('itab_' + MName + '_' + CSym + ':');
      for K := 0 to IntfDesc.MethodCount() - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if Self.IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '_AbstractMethodError'
        else
        begin
          MDecl := FindMethodInClassDef(GI.ClassDef, MethName);
          if (MDecl <> nil) and (MDecl.ResolvedQbeName <> '') then
            MethRef := NativeMangle(MDecl.ResolvedQbeName)
          else
            MethRef := MName + '_' + MethName;
        end;
        Self.Emit(#9'.quad ' + MethRef);
      end;
    end;

    Self.Emit('.balign 8');
    Self.Emit('.weak impllist_' + MName);
    Self.Emit('impllist_' + MName + ':');
    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      Self.Emit(#9'.quad typeinfo_' + Self.IntfTypeInfoName(IntfDesc.Name));
      Self.Emit(#9'.quad itab_' + MName + '_' + Self.IntfTypeInfoName(IntfDesc.Name));
    end;
    Self.Emit(#9'.quad 0');
  end;
end;

procedure TX86_64Backend.EmitInterfaceAssign(AAsgn: TAssignment);
{ Strong-reference interface assignment.  The LHS fat pointer is (obj, itab).
  In every form the obj slot co-owns the backing class instance: the new obj is
  retained and the prior obj released before the store.  The itab slot points at
  static rodata and is not refcounted. }
var
  Intf:    TInterfaceTypeDesc;
  ClassRT: TRecordTypeDesc;
  AE:      TAsExpr;
  ItabSym: string;
  ObjOp:   string;
  ItabOp:  string;
  LFail:   string;
  LEnd:    string;
  ISFld:   TFieldInfo;
begin
  Intf := TInterfaceTypeDesc(AAsgn.ResolvedLhsType);
  { Implicit Self.Field assignment: the fat pointer lives inside the object at
    Self + FieldOffset (obj) and Self + FieldOffset + 8 (itab).
    Handle entirely here rather than falling through to the ObjOp/ItabOp paths
    below (which use fixed operand strings that could be clobbered by calls). }
  if AAsgn.ImplicitSelfField <> nil then
  begin
    ISFld := TFieldInfo(AAsgn.ImplicitSelfField);
    { Compute Self + FieldOffset into %r15 (callee-saved: survives callq). }
    Self.Emit(#9'pushq %r15');
    Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Self')]));
    if ISFld.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r15', [ISFld.Offset]));
    { Now (%r15) = obj slot, 8(%r15) = itab slot. }
    if AAsgn.Expr.ResolvedType.Kind = tyClass then
    begin
      ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
      ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
      Self.EmitExprToEax(AAsgn.Expr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if AAsgn.Expr is TNilLiteral then
    begin
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq $0, (%r15)');
      Self.Emit(#9'movq $0, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and (AAsgn.Expr is TIdentExpr) then
    begin
      Self.PushIntfIdentPair(TIdentExpr(AAsgn.Expr));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and (AAsgn.Expr is TFieldAccessExpr) then
    begin
      Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AAsgn.Expr), '%rax');
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq %rcx, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if (AAsgn.Expr is TFuncCallExpr) and
            (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyInterface) then
    begin
      Self.EmitIntfSretCall(TFuncCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyInterface) then
    begin
      { Interface-method call (itab dispatch) returning an interface — the
        callee hands back an OWNED +1 fat pointer in the sret buffer. }
      Self.EmitIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyClass) then
    begin
      { Class-receiver method call returning an interface — sret protocol;
        the callee hands back an OWNED +1 fat pointer. }
      Self.EmitClassIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface-field assignment RHS');
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { sret interface Result: the Result slot holds a pointer to the caller's
    16-byte buffer.  Dereference it into %r15 so that (%r15)=obj, 8(%r15)=itab. }
  if (FSretFunc and SameText(AAsgn.Name, 'Result')) or AAsgn.IsVarParam then
  begin
    { Both shapes hold a POINTER to the caller's 16-byte fat-pointer block:
      the sret Result slot, or a var/out interface param slot. }
    Self.Emit(#9'pushq %r15');
    if AAsgn.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand(AAsgn.Name)]))
    else
      Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Result')]));
    ObjOp  := '(%r15)';
    ItabOp := '8(%r15)';
    if AAsgn.Expr.ResolvedType.Kind = tyClass then
    begin
      ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
      ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
      Self.EmitExprToEax(AAsgn.Expr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if AAsgn.Expr is TNilLiteral then
    begin
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq $0, (%r15)');
      Self.Emit(#9'movq $0, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and (AAsgn.Expr is TIdentExpr) then
    begin
      Self.PushIntfIdentPair(TIdentExpr(AAsgn.Expr));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
            (AAsgn.Expr is TDerefExpr) then
    begin
      { Result := Src^ where Src: ^IFoo — exactly the body of TList<T>.Get
        monomorphised at T = an interface, which is what made TList<IFoo>
        uninstantiable.  The pointee is a contiguous fat pointer; load both
        words from it before storing into the sret destination.  %r14 is
        callee-saved so the source address survives the ARC calls, and %r15
        (the sret destination) must not be disturbed. }
      Self.Emit(#9'pushq %r14');
      Self.EmitExprToEax(TDerefExpr(AAsgn.Expr).Expr);
      Self.Emit(#9'movq %rax, %r14');
      Self.Emit(#9'movq 8(%r14), %rax');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq (%r14), %rax');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'popq %r14');
    end
    else if (AAsgn.Expr is TFuncCallExpr) and
            (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyInterface) then
    begin
      Self.EmitIntfSretCall(TFuncCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyInterface) then
    begin
      { Interface-method call (itab dispatch) returning an interface — the
        callee hands back an OWNED +1 fat pointer in the sret buffer. }
      Self.EmitIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyClass) then
    begin
      { Class-receiver method call returning an interface — sret protocol;
        the callee hands back an OWNED +1 fat pointer. }
      Self.EmitClassIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TStringSubscriptExpr) and
            (TStringSubscriptExpr(AAsgn.Expr).StrExpr is TFieldAccessExpr) and
            (TFieldAccessExpr(TStringSubscriptExpr(AAsgn.Expr).StrExpr).PropRead <> nil) then
    begin
    { Interface element read through an INDEXED PROPERTY: List[I] where the
      default property's getter returns an interface.  There is no element
      address to take -- the getter hands back the fat pair BY VALUE through
      the sret convention -- so this is the class-receiver-call shape.
      EmitRecordCallSretAt already unwraps the subscript to its PropRead
      FieldAccess and synthesises the getter call, so it does the marshalling;
      it just was never reached from the interface paths. }
      Self.Emit(#9'subq $16, %rsp');
      Self.EmitRecordCallSretAt(AAsgn.Expr, '(%rsp)', False);
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported sret interface Result assignment RHS');
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { Register a global LHS so EmitDataSection emits its _obj/_itab labels. }
  if not Self.IsLocal(AAsgn.Name) then
  begin
    Self.AddGlobal(AAsgn.Name, AAsgn.ResolvedLhsType);
    if AAsgn.IsThreadVar then Self.MarkThreadVar(AAsgn.Name);
    if AAsgn.IsWeakLhs then Self.MarkWeakGlobal(AAsgn.Name);
  end;
  ObjOp  := Self.IntfObjOperand(AAsgn.Name, AAsgn.IsGlobal);
  ItabOp := Self.IntfItabOperand(AAsgn.Name, AAsgn.IsGlobal);

  { F := nil — release old obj, zero both slots. }
  if AAsgn.Expr is TNilLiteral then
  begin
    if AAsgn.IsWeakLhs then
      Self.Emit(Format(#9'leaq %s, %%rdi', [ObjOp]))
    else
      Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));
    if AAsgn.IsWeakLhs then
      Self.Emit(#9'callq _WeakClear')
    else
      Self.Emit(#9'callq _ClassRelease');
    Self.Emit(Format(#9'movq $0, %s', [ObjOp]));
    Self.Emit(Format(#9'movq $0, %s', [ItabOp]));
    Exit;
  end;

  { F := T as IFoo — runtime itab lookup via _GetItab(obj, typeinfo_IFoo).
    A nil result means the cast failed; raise EInvalidCast. }
  if (AAsgn.Expr is TAsExpr) and
     (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) then
  begin
    AE := TAsExpr(AAsgn.Expr);
    Self.EmitExprToEax(AE.Obj);          { obj -> %rax }
    Self.Emit(#9'pushq %rax');            { keep obj on the stack across calls }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi', [Self.IntfTypeInfoName(AE.TypeName)]));
    Self.Emit(#9'callq _GetItab');         { itab -> %rax }
    Self.Emit(#9'pushq %rax');            { keep itab; stack now (itab, obj) }
    LFail := Self.NewLabel('as_fail');
    LEnd  := Self.NewLabel('as_end');
    Self.Emit(#9'testq %rax, %rax');
    Self.Emit(#9'jz ' + LFail);
    { Cast OK: addref new obj, release old, store obj + itab. }
    Self.Emit(#9'movq 8(%rsp), %rdi');     { obj }
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %rax');              { obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'jmp ' + LEnd);
    Self.Emit(LFail + ':');
    Self.Emit(#9'addq $16, %rsp');         { discard pushed obj+itab }
    Self.Emit(#9'callq _Raise_InvalidCast');
    Self.Emit(LEnd + ':');
    Exit;
  end;

  { F := T where T is a class implementing the interface — static itab. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyClass) then
  begin
    ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
    ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
    Self.EmitExprToEax(AAsgn.Expr);       { new obj -> %rax }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Exit;
  end;

  { F := G where both sides are interface-typed — copy obj+itab. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TIdentExpr) then
  begin
    if AAsgn.IsWeakLhs then
    begin
      Self.Emit(Format(#9'movq %s, %%rsi',
        [Self.IntfObjOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
      Self.Emit(Format(#9'leaq %s, %%rdi', [ObjOp]));
      Self.Emit(#9'callq _WeakAssign');
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.IntfItabOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
      Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    end
    else
    begin
      { Load src obj+itab; addref new obj; release old obj; store both. }
      Self.PushIntfIdentPair(TIdentExpr(AAsgn.Expr));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');              { new obj }
      Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
      Self.Emit(#9'popq %rax');              { itab }
      Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    end;
    Exit;
  end;

  { F := H.G where the RHS is an interface stored in a record/class field.  The
    fat pointer is contiguous in the field's memory (obj at the field address,
    itab at +8) — load both, addref the new obj, release the old, store both. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TFieldAccessExpr) then
  begin
    { Compute the source field's base address into %r15 (callee-saved). }
    Self.Emit(#9'pushq %r15');
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AAsgn.Expr), '%r15');
    Self.Emit(#9'movq 8(%r15), %rax');     { src itab }
    Self.Emit(#9'pushq %rax');             { itab }
    Self.Emit(#9'movq (%r15), %rax');      { src obj }
    Self.Emit(#9'pushq %rax');             { obj; stack now (obj, itab) }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { F := P^ where the RHS is an interface read through a typed pointer.  The
    pointee is a contiguous fat pointer (obj at the pointer value, itab at +8)
    — the same shape as the field-access case above, with the pointer VALUE
    standing in for the field address.  Without this arm the read hit the
    fail-loud else: the native backend addresses interfaces by NAMED SLOT
    (X_obj / X_itab), so no address-based read path existed at all. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TDerefExpr) then
  begin
    Self.Emit(#9'pushq %r15');
    Self.EmitExprToEax(TDerefExpr(AAsgn.Expr).Expr);
    Self.Emit(#9'movq %rax, %r15');
    Self.Emit(#9'movq 8(%r15), %rax');     { src itab }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq (%r15), %rax');      { src obj }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { F := Arr[I] where the RHS is an interface element of a static array.  The
    element is a contiguous fat pointer (obj at the element address, itab at +8)
    — compute the element address into %r15 and copy obj+itab with ARC, mirroring
    the field-access case above. }
  { The StrExpr guard is load-bearing: a class default-property subscript
    (L[0], which desugars to the Items getter) is ALSO a TStringSubscriptExpr,
    but it has no static-array base and no evaluated index.  Without the check
    it fell in here and EmitIntfStaticElemAddr cast the class type to
    TStaticArrayTypeDesc and dereferenced a nil index expression — segfaulting
    the COMPILER rather than reporting anything. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AAsgn.Expr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AAsgn.Expr).StrExpr.ResolvedType.Kind = tyStaticArray) then
  begin
    Self.Emit(#9'pushq %r15');
    Self.EmitIntfStaticElemAddr(TStringSubscriptExpr(AAsgn.Expr), '%r15');
    Self.Emit(#9'movq 8(%r15), %rax');     { src itab }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq (%r15), %rax');      { src obj }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %r15');
    Exit;
  end;
  { Same, for a dynamic / open-array interface element source: fat pointer at
    data_ptr + index*16 (BUG-20260720-qbe-dynarray-intf-elem-read). }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AAsgn.Expr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AAsgn.Expr).StrExpr.ResolvedType.Kind in
        [tyDynArray, tyOpenArray]) then
  begin
    Self.Emit(#9'pushq %r15');
    Self.EmitIntfDynElemAddr(TStringSubscriptExpr(AAsgn.Expr), '%r15');
    Self.Emit(#9'movq 8(%r15), %rax');     { src itab }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq (%r15), %rax');      { src obj }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { F := FuncReturningInterface() — sret convention: allocate a 16-byte buffer
    on the stack, pass its address as the hidden first arg (%rdi), call the
    function (which writes obj+itab into the buffer), then move the result to
    the LHS with ARC. }
  if (AAsgn.Expr is TFuncCallExpr) and
     (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil) and
     (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
     (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyInterface) then
  begin
    Self.EmitIntfSretCall(TFuncCallExpr(AAsgn.Expr));
    { Sret buffer at (%rsp): obj at 0(%rsp), itab at 8(%rsp). }
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));  { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'movq 8(%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'addq $16, %rsp');
    Exit;
  end;

  { F := SomeIntf.Method(args) where Method (itab dispatch) returns an
    interface — same sret protocol; the callee hands back an OWNED +1 fat
    pointer, so release the old obj and store without an extra AddRef. }
  if (AAsgn.Expr is TMethodCallExpr) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyInterface) then
  begin
    Self.EmitIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));  { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'movq 8(%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'addq $16, %rsp');
    Exit;
  end;

  { F := Obj.Method() where Obj is class-typed and Method returns an
    interface — sret protocol with the receiver in %rsi; the callee hands
    back an OWNED +1 fat pointer, so release the old obj and store without
    an extra AddRef. }
  if (AAsgn.Expr is TMethodCallExpr) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyClass) then
  begin
    Self.EmitClassIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));  { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'movq 8(%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'addq $16, %rsp');
    Exit;
  end;

  if (AAsgn.Expr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AAsgn.Expr).StrExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(TStringSubscriptExpr(AAsgn.Expr).StrExpr).PropRead <> nil) then
  begin
  { Interface element read through an INDEXED PROPERTY: List[I] where the
    default property's getter returns an interface.  There is no element
    address to take -- the getter hands back the fat pair BY VALUE through
    the sret convention -- so this is the class-receiver-call shape.
    EmitRecordCallSretAt already unwraps the subscript to its PropRead
    FieldAccess and synthesises the getter call, so it does the marshalling;
    it just was never reached from the interface paths. }
    Self.Emit(#9'subq $16, %rsp');
    Self.EmitRecordCallSretAt(AAsgn.Expr, '(%rsp)', False);
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));  { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'movq 8(%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'addq $16, %rsp');
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported interface-field assignment RHS');
end;

procedure TX86_64Backend.EmitInterfaceToFieldSlotsAt(AExpr: TASTExpr;
  const ABaseReg: string; AOffset: Integer; AIntfType: TTypeDesc);
{ Store an interface RHS into a contiguous fat-pointer field.  The destination
  base address is taken from ABaseReg into the callee-saved %r15 so it survives
  the ARC calls; obj slot is (%r15), itab slot is 8(%r15). }
var
  Intf:    TInterfaceTypeDesc;
  ClassRT: TRecordTypeDesc;
  ItabSym: string;
begin
  if (AIntfType = nil) or (AIntfType.Kind <> tyInterface) then
    raise ENativeCodeGenError.Create(
      'native backend: interface-field store needs a destination interface type');
  Intf := TInterfaceTypeDesc(AIntfType);

  { Capture the destination base address in a callee-saved register. }
  Self.Emit(#9'pushq %r15');
  Self.Emit(Format(#9'movq %s, %%r15', [ABaseReg]));
  if AOffset > 0 then
    Self.Emit(Format(#9'addq $%d, %%r15', [AOffset]));
  { Now (%r15) = obj slot, 8(%r15) = itab slot. }

  if AExpr is TNilLiteral then
  begin
    Self.Emit(#9'movq (%r15), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq $0, (%r15)');
    Self.Emit(#9'movq $0, 8(%r15)');
  end
  else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
  begin
    ClassRT := TRecordTypeDesc(AExpr.ResolvedType);
    ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
    Self.EmitExprToEax(AExpr);
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(#9'movq (%r15), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');
    Self.Emit(#9'movq %rax, (%r15)');
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
    Self.Emit(#9'movq %rax, 8(%r15)');
  end
  else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyInterface) then
  begin
    { Interface source: copy obj+itab from the source's fat pointer.  A named
      interface local/global uses split _obj/_itab slots; an interface stored in
      a record/class field uses a contiguous fat pointer (obj / obj+8). }
    if AExpr is TIdentExpr then
    begin
      if TIdentExpr(AExpr).IsImplicitSelf and
         (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
        if TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rax',
            [TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset]));
        Self.Emit(#9'movq 8(%rax), %rcx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'pushq %rcx');
      end
      else
        Self.PushIntfIdentPair(TIdentExpr(AExpr));
    end
    else if AExpr is TFieldAccessExpr then
    begin
      Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AExpr), '%rax');
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
    end
    else if AExpr is TDerefExpr then
    begin
      { Interface read through a typed pointer (P^): the pointer VALUE is the
        address of the contiguous fat pointer. }
      Self.EmitExprToEax(TDerefExpr(AExpr).Expr);
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { itab }
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { obj on top }
    end
    else if (AExpr is TStringSubscriptExpr) and
            (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
            (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyStaticArray) then
    begin
      { Static-array interface element source (Arr[I]): contiguous fat pointer.
        The static-array guard keeps a class default-property subscript (L[0])
        out — it is subscript-shaped but has no array base and no evaluated
        index, and would crash EmitIntfStaticElemAddr.  It falls through to the
        fail-loud else below instead. }
      Self.EmitIntfStaticElemAddr(TStringSubscriptExpr(AExpr), '%rax');
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { itab }
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { obj on top }
    end
    else if (AExpr is TStringSubscriptExpr) and
            (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
            (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind in
               [tyDynArray, tyOpenArray]) then
    begin
      { Dynamic / open-array interface element source: fat pointer at
        data_ptr + index*16 (BUG-20260720-qbe-dynarray-intf-elem-read). }
      Self.EmitIntfDynElemAddr(TStringSubscriptExpr(AExpr), '%rax');
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { itab }
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { obj on top }
    end
    else if (AExpr is TFuncCallExpr) and
            (TFuncCallExpr(AExpr).ResolvedDecl <> nil) then
    begin
      Self.EmitIntfSretCall(TFuncCallExpr(AExpr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
      Self.Emit(#9'popq %r15');
      Exit;
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface source for interface-field store');
    Self.Emit(#9'movq (%rsp), %rdi');        { new obj }
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(#9'movq (%r15), %rdi');        { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');                { new obj }
    Self.Emit(#9'movq %rax, (%r15)');
    Self.Emit(#9'popq %rax');                { itab }
    Self.Emit(#9'movq %rax, 8(%r15)');
  end
  else
    raise ENativeCodeGenError.Create(
      'native backend: unsupported interface-field store RHS');

  Self.Emit(#9'popq %r15');
end;

procedure TX86_64Backend.EmitInterfaceFieldAddr(AFA: TFieldAccessExpr;
  const ADstReg: string);
{ Leave the address of AFA's interface field (the contiguous obj/itab fat
  pointer) in ADstReg.  Mirrors the receiver-base resolution used by the
  field-read path, but stops at the address rather than loading a value. }
begin
  if AFA.Base <> nil then
  begin
    { Nested receiver expression (e.g. Outer.Inner.G): evaluate it to the base
      address. }
    Self.EmitExprToEax(AFA.Base);
    Self.Emit(Format(#9'movq %%rax, %s', [ADstReg]));
  end
  else if AFA.IsImplicitSelf then
  begin
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand('Self'), ADstReg]));
    if (AFA.ImplicitBaseInfo <> nil) and (AFA.ImplicitBaseInfo.Offset > 0) then
      Self.Emit(Format(#9'addq $%d, %s', [AFA.ImplicitBaseInfo.Offset, ADstReg]));
    if AFA.IsClassAccess then
      Self.Emit(Format(#9'movq (%s), %s', [ADstReg, ADstReg]));
  end
  else if AFA.IsClassAccess then
  begin
    if Self.IsLocal(AFA.RecordName) then
      Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand(AFA.RecordName), ADstReg]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %s',
        [Self.GlobalSymName(AFA.RecordName), ADstReg]));
    if AFA.IsVarParam then
      { var-param class: slot -> caller var -> instance }
      Self.Emit(Format(#9'movq (%s), %s', [ADstReg, ADstReg]));
  end
  else if AFA.IsVarParam then
  begin
    if Self.IsLocal(AFA.RecordName) then
      Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand(AFA.RecordName), ADstReg]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %s',
        [Self.GlobalSymName(AFA.RecordName), ADstReg]));
  end
  else
    Self.EmitVarAddr(AFA.RecordName, ADstReg);
  { Add the field offset to reach the fat pointer's obj slot. }
  if AFA.FieldInfo.Offset > 0 then
    Self.Emit(Format(#9'addq $%d, %s', [AFA.FieldInfo.Offset, ADstReg]));
  { ARRAY-FIELD ELEMENT (H.FArr[0], IsArrayAccess): ADstReg holds the array
    FIELD address — index into it so the fat pair is the ELEMENT's.  Without
    this every consumer read the field slot as the pair base
    (BUG-20260721-fieldaccess-intf-array-elem-read). }
  if AFA.IsArrayAccess then
  begin
    if AFA.FieldInfo.TypeDesc.Kind in [tyDynArray, tyOpenArray] then
      { heap data pointer lives in the field slot }
      Self.Emit(Format(#9'movq (%s), %s', [ADstReg, ADstReg]));
    Self.Emit(Format(#9'pushq %s', [ADstReg]));
    Self.EmitExprToEax(AFA.PropIndexExpr);
    if AFA.FieldInfo.TypeDesc.Kind = tyStaticArray then
      Self.EmitStaticElemScale(TStaticArrayTypeDesc(AFA.FieldInfo.TypeDesc))
    else
      Self.Emit(#9'imulq $16, %rax');
    { Pop the base through %rcx, not ADstReg: several callers pass %rax as
      ADstReg, and popping the base into %rax would destroy the scaled index
      just computed there ("addq %rax, %rax" then doubled the base). }
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    if ADstReg <> '%rax' then
      Self.Emit(Format(#9'movq %%rax, %s', [ADstReg]));
  end;
end;

procedure TX86_64Backend.EmitIntfStaticElemAddr(ASub: TStringSubscriptExpr;
  const ADstReg: string);
{ Leave the address of an interface element of a static array (the contiguous
  obj/itab fat pointer) in ADstReg.  Computes base + (idx - LowBound) * 16.
  The element-address arithmetic clobbers %rax/%rcx, so ADstReg should be a
  callee-saved register (e.g. %r15) when it must survive subsequent ARC calls. }
var
  SAT: TStaticArrayTypeDesc;
begin
  SAT := TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType);
  Self.EmitExprToEax(ASub.IndexExpr);          { index -> %rax }
  Self.EmitStaticElemScale(SAT);
  { Base address of the array's inline storage into %rcx. }
  if (ASub.StrExpr is TIdentExpr) and
     TIdentExpr(ASub.StrExpr).IsImplicitSelf and
     (TIdentExpr(ASub.StrExpr).ImplicitFieldInfo <> nil) then
  begin
    { Static-array field of Self: inline storage at Self + field offset. }
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
    if TFieldInfo(TIdentExpr(ASub.StrExpr).ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rcx',
        [TFieldInfo(TIdentExpr(ASub.StrExpr).ImplicitFieldInfo).Offset]));
  end
  else if ASub.StrExpr is TIdentExpr then
  begin
    if Self.IsLocal(TIdentExpr(ASub.StrExpr).Name) then
      Self.Emit(Format(#9'leaq %s, %%rcx',
        [Self.VarOperand(TIdentExpr(ASub.StrExpr).Name)]))
    else
      Self.EmitLeaqGlobal(TIdentExpr(ASub.StrExpr).Name, '%rcx');
  end
  else
    raise ENativeCodeGenError.Create(
      'native backend: unsupported interface static-array base expression');
  Self.Emit(Format(#9'addq %%rax, %%rcx', []));
  Self.Emit(Format(#9'movq %%rcx, %s', [ADstReg]));
end;

procedure TX86_64Backend.EmitIntfDynElemAddr(ASub: TStringSubscriptExpr;
  const ADstReg: string);
{ Element fat-pointer address of an interface element of a DYNAMIC / OPEN array:
  data_ptr + index * 16 (an interface fat pointer is 16 bytes; no LowBound). }
begin
  Self.EmitExprToEax(ASub.StrExpr);            { data pointer -> %rax }
  Self.Emit(#9'pushq %rax');
  Self.EmitExprToEax(ASub.IndexExpr);          { index -> %rax }
  Self.Emit(#9'imulq $16, %rax');
  Self.Emit(#9'popq %rcx');                    { data pointer }
  Self.Emit(#9'addq %rcx, %rax');
  Self.Emit(Format(#9'movq %%rax, %s', [ADstReg]));
end;

procedure TX86_64Backend.EmitClassMethods(ATypeDecls: TObjectList;
                                          AGenericInstances: TObjectList;
                                          AGenericRecordInstances: TObjectList;
                                          AGenericMethodInstances: TObjectList);
var
  I, J: Integer;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  RD:   TRecordTypeDef;
  GI:   TGenericInstance;
  GRI:  TGenericRecordInstance;
  GMI:  TGenericMethodInstance;
  Decl: TMethodDecl;
  SavedUnit: string;
begin
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
    begin
      CD := TClassTypeDef(TD.Def);
      for J := 0 to CD.Methods.Count - 1 do
      begin
        Decl := TMethodDecl(CD.Methods.Items[J]);
        if Decl.Body = nil then Continue;
        { Generic-method templates emit per instantiation, not as a template. }
        if Decl.TypeParams <> nil then Continue;
        Self.EmitFunctionDef(Decl, True);
      end;
    end
    else if TD.Def is TRecordTypeDef then
    begin
      RD := TRecordTypeDef(TD.Def);
      for J := 0 to RD.Methods.Count - 1 do
      begin
        Decl := TMethodDecl(RD.Methods.Items[J]);
        if Decl.Body = nil then Continue;
        if Decl.TypeParams <> nil then Continue;
        Self.EmitFunctionDef(Decl, True);
      end;
    end;
  end;

  { Generic instance method bodies are template clones: their Line fields
    refer to the unit that DECLARES the template, so allocation-site
    tracking must report that unit, not the instantiating one. }
  SavedUnit := FCurrentUnitName;
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    if GI.DefUnitName <> '' then
      FCurrentUnitName := GI.DefUnitName
    else
      FCurrentUnitName := SavedUnit;
    for J := 0 to GI.ClassDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      Self.EmitFunctionDef(Decl, True);
    end;
  end;
  FCurrentUnitName := SavedUnit;

  for I := 0 to AGenericRecordInstances.Count - 1 do
  begin
    GRI := TGenericRecordInstance(AGenericRecordInstances.Items[I]);
    for J := 0 to GRI.RecordDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GRI.RecordDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      Self.EmitFunctionDef(Decl, True);
    end;
  end;

  { Generic METHOD instances (method-level <T>): each monomorphised body.  Its
    ResolvedQbeName encodes <Owner>_<Method><args> and OwnerTypeName is set, so
    EmitFunctionDef emits it with the implicit Self like any method. }
  for I := 0 to AGenericMethodInstances.Count - 1 do
  begin
    GMI := TGenericMethodInstance(AGenericMethodInstances.Items[I]);
    if GMI.MethodDecl.Body <> nil then
      Self.EmitFunctionDef(GMI.MethodDecl, True);
  end;
end;

{ ------------------------------------------------------------------ }
{ Frame model                                                          }
{ ------------------------------------------------------------------ }

function TX86_64Backend.IsCaptured(const AName: string): Boolean;
begin
  { An inline candidate captures nothing; without this, a callee ident
    sharing a name with one of the CALLER's captured vars would be
    misrouted through the caller's _cap_ pointer. }
  if FInlineActive then Exit(False);
  Result := ((FCapturedVars <> nil) and (FCapturedVars.IndexOf(AName) >= 0)) or
            ((FEnvVarNames <> nil) and (FEnvVarNames.IndexOf(AName) >= 0)) or
            ((FBlockEnvVarNames <> nil) and (FBlockEnvVarNames.IndexOf(AName) >= 0));
end;

procedure TX86_64Backend.EmitVarBaseToReg(const AName: string;
  AWantAddress: Boolean; const ADstReg: string);
{ Load the base of the variable AName into ADstReg, handling locals, globals
  and variables CAPTURED from an enclosing proc uniformly.

  AWantAddress = True  -> ADstReg receives the ADDRESS of the variable's own
                          storage (what `leaq` / EmitVarAddr would give for a
                          local; the record base for a plain-record variable).
  AWantAddress = False -> ADstReg receives the VALUE stored in the variable
                          (one dereference; e.g. the pointer held by a
                          var-param or class slot).

  A captured variable is reached through its hidden `_cap_<Name>` pointer slot,
  which holds the ADDRESS of the enclosing variable's storage — exactly the
  AWantAddress=True result.  For AWantAddress=False one further load yields the
  stored value, mirroring the local case. }
begin
  if Self.IsCaptured(AName) then
  begin
    Self.Emit(Format(#9'movq %s, %s',
      [Self.VarOperand('_cap_' + AName), ADstReg]));
    if not AWantAddress then
      Self.Emit(Format(#9'movq (%s), %s', [ADstReg, ADstReg]));
  end
  { sret Result: its slot holds the caller's record buffer POINTER, so the
    "address of the record" is the stored value, not a leaq of the slot.
    (A captured name is never Result, so this follows the capture branch.) }
  else if FSretFunc and SameText(AName, 'Result') then
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand('Result'), ADstReg]))
  else if AWantAddress then
    Self.EmitVarAddr(AName, ADstReg)
  else if Self.IsLocal(AName) then
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand(AName), ADstReg]))
  else
    { Global value load: VarOperand applies the owner prefix (and the %fs:@tpoff
      form for a threadvar). }
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand(AName), ADstReg]));
end;

function TX86_64Backend.IsLocal(const AName: string): Boolean;
var
  Off: Integer;
begin
  if FInlineActive then
  begin
    if FInlineMap.TryGetValue(AName, Off) then Exit(True);
    if (Length(AName) = 0) or (StrAt(AName, 0) <> 95) then
      Exit(False);                    { inlined-body ident: global }
  end;
  Result := (FFrame <> nil) and FFrame.ContainsKey(AName);
end;


function TX86_64Backend.VarOperand(const AName: string): string;
var
  Off: Integer;
begin
  { Inlined-body names resolve through the inline map; anything else
    referenced from an inlined body is a GLOBAL — never the caller's
    frame (a caller local sharing the callee's global's name must not
    hijack it).  Internal '_'-prefixed helper slots (_pendrel, _jset,
    _promo_save, _inl_area) still live in the caller frame. }
  if FInlineActive then
  begin
    if FInlineMap.TryGetValue(AName, Off) then
      { Map value is a scratch-slot INDEX: resolve the _inl_s name so a
        PROMOTED slot answers its register. }
      Exit(Self.VarOperand('_inl_s' + IntToStr(Off)));
    if (Length(AName) = 0) or (StrAt(AName, 0) <> 95) then    { '_' }
    begin
      if Self.IsThreadVarGlobal(AName) then
        Exit('%fs:' + Self.GlobalSymName(AName) + '@tpoff');
      Exit(Self.GlobalSymName(AName) + '(%rip)');
    end;
  end;
  { Register-promoted var: the register IS the storage.  PromoRewrite in
    Emit maps width-suffixed instruction forms onto the sub-registers. }
  if FPromoActive then
    for Off := 0 to 3 do
      if (FPromoVars[Off] <> '') and (AName = FPromoVars[Off]) then
        Exit(PROMO_REGS[Off]);
  if (FFrame <> nil) and FFrame.TryGetValue(AName, Off) then
  begin
    if Off > 0 then
      Result := Format('%d(%%rbp)', [Off])
    else
      Result := Format('-%d(%%rbp)', [-Off])
  end
  else if Self.IsThreadVarGlobal(AName) then
    { Threadvars are unit-prefixed too (a same-named threadvar in two units would
      otherwise collide); the .tbss definition and this %fs:...@tpoff reference
      both apply GlobalSymName so they agree. }
    Result := '%fs:' + Self.GlobalSymName(AName) + '@tpoff'
  else
    { Module global: reference the owner-prefixed symbol so it binds to the
      matching definition (mirrors QBE's VarRef honouring ResolvedOwnerUnit). }
    Result := Self.GlobalSymName(AName) + '(%rip)';
end;

procedure TX86_64Backend.EmitLeaqGlobal(const AName: string; const ADstReg: string);
begin
  if Self.IsThreadVarGlobal(AName) then
  begin
    Self.Emit(Format(#9'movq %%fs:0, %s', [ADstReg]));
    Self.Emit(Format(#9'leaq %s@tpoff(%s), %s',
      [Self.GlobalSymName(AName), ADstReg, ADstReg]));
  end
  else
    Self.Emit(Format(#9'leaq %s(%%rip), %s',
      [Self.GlobalSymName(AName), ADstReg]));
end;

procedure TX86_64Backend.EmitVarAddr(const AName: string; const ADstReg: string);
begin
  if Self.IsLocal(AName) then
    Self.Emit(Format(#9'leaq %s, %s', [Self.VarOperand(AName), ADstReg]))
  else
    Self.EmitLeaqGlobal(AName, ADstReg);
end;

function TX86_64Backend.LocalType(const AName: string): TTypeDesc;
begin
  if FInlineActive then
  begin
    if FInlineTypes.TryGetValue(AName, Result) then Exit;
    if (Length(AName) = 0) or (StrAt(AName, 0) <> 95) then
      Exit(nil);                      { inlined-body ident: global }
  end;
  if (FFrameTypes = nil) or (not FFrameTypes.TryGetValue(AName, Result)) then
    Result := nil;
end;

{ The obj half of an interface fat pointer.  Locals: the 16-byte slot base
  (VarOperand returns the low address = obj).  Globals: a dedicated label
  AName + '_obj', registered for emission in EmitDataSection. }
function TX86_64Backend.IntfObjOperand(const AName: string; AIsGlobal: Boolean): string;
begin
  if (not AIsGlobal) and Self.IsLocal(AName) then
    Result := Self.VarOperand(AName)
  else
    { Owner-prefixed label matching EmitDataSection's <Name>_obj definition. }
    Result := Self.GlobalSymName(AName) + '_obj(%rip)';
end;

{ The itab half of an interface fat pointer.  Locals: 8 bytes above the obj
  slot (the slot base address is the obj operand, so add 8 to its rbp offset).
  Globals: a dedicated label AName + '_itab'. }
function TX86_64Backend.IntfItabOperand(const AName: string; AIsGlobal: Boolean): string;
var
  Off: Integer;
begin
  if (not AIsGlobal) and Self.IsLocal(AName) then
  begin
    FFrame.TryGetValue(AName, Off);
    { Off is negative (slot base = obj). itab is 8 bytes higher in memory. }
    Result := Format('%d(%%rbp)', [Off + 8]);
  end
  else
    Result := Self.GlobalSymName(AName) + '_itab(%rip)';
end;

procedure TX86_64Backend.PushIntfIdentPair(AIdent: TIdentExpr);
begin
  if FSretFunc and SameText(AIdent.Name, 'Result') then
  begin
    { sret interface Result: the slot holds the caller-buffer address —
      dereference for obj (+0) and itab (+8). }
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Result')]));
    Self.Emit(#9'movq 8(%rax), %rcx');
    Self.Emit(#9'pushq %rcx');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'pushq %rax');
  end
  else if Self.IsCaptured(AIdent.Name) then
  begin
    { Captured interface local (BUG-038): the capture slot holds the address
      of the enclosing routine's contiguous fat pointer. }
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.VarOperand('_cap_' + AIdent.Name)]));
    Self.Emit(#9'movq 8(%rax), %rcx');
    Self.Emit(#9'pushq %rcx');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'pushq %rax');
  end
  else if AIdent.IsImplicitSelf and (AIdent.ImplicitFieldInfo <> nil) then
  begin
    { Interface-typed FIELD of Self referenced by bare name inside a method:
      the contiguous fat pointer lives at Self + field offset (obj at +0,
      itab at +8).  Without this branch the fallthrough would build bogus
      <Name>_obj / <Name>_itab global labels from the field name. }
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    if TFieldInfo(AIdent.ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rax',
        [TFieldInfo(AIdent.ImplicitFieldInfo).Offset]));
    Self.Emit(#9'movq 8(%rax), %rcx');
    Self.Emit(#9'pushq %rcx');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'pushq %rax');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(AIdent.Name, AIdent.IsGlobal)]));
    Self.Emit(#9'pushq %rax');
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfObjOperand(AIdent.Name, AIdent.IsGlobal)]));
    Self.Emit(#9'pushq %rax');
  end;
end;

{ Load an integer-family value from memory into %rax, extended to the full
  64-bit register according to AType's width and signedness.  Narrower-than-
  32-bit loads use a sign/zero-extending move; 32-bit signed widens with
  movslq, 32-bit unsigned with a plain movl (which zero-extends the upper 32
  bits on x86-64); 64-bit is a straight movq. }
procedure TX86_64Backend.EmitLoadVar(const AOperand: string; AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzbq %s, %%rax', [AOperand]))
       else
         Self.Emit(Format(#9'movsbq %s, %%rax', [AOperand]));
    2: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzwq %s, %%rax', [AOperand]))
       else
         Self.Emit(Format(#9'movswq %s, %%rax', [AOperand]));
    8: Self.Emit(Format(#9'movq %s, %%rax', [AOperand]));
  else
    { 4-byte: a movl into %eax zero-extends into %rax.  For a signed Integer
      sign-extend instead so the upper 32 bits carry the sign. }
    if IsUnsignedInt(AType) then
      Self.Emit(Format(#9'movl %s, %%eax', [AOperand]))
    else
      Self.Emit(Format(#9'movslq %s, %%rax', [AOperand]));
  end;
end;

procedure TX86_64Backend.EmitLoadVarToReg(const AOperand: string;
  AType: TTypeDesc; const AReg64, AReg32: string);
begin
  case IntByteSize(AType) of
    1: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzbq %s, %s', [AOperand, AReg64]))
       else
         Self.Emit(Format(#9'movsbq %s, %s', [AOperand, AReg64]));
    2: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzwq %s, %s', [AOperand, AReg64]))
       else
         Self.Emit(Format(#9'movswq %s, %s', [AOperand, AReg64]));
    8: Self.Emit(Format(#9'movq %s, %s', [AOperand, AReg64]));
  else
    if IsUnsignedInt(AType) then
      Self.Emit(Format(#9'movl %s, %s', [AOperand, AReg32]))
    else
      Self.Emit(Format(#9'movslq %s, %s', [AOperand, AReg64]));
  end;
end;

procedure TX86_64Backend.EmitImmToReg(AValue: Int64; const AReg64, AReg32: string);
begin
  if (AValue >= 0) and (AValue <= 2147483647) then
    { movl zero-extends into the full 64-bit register. }
    Self.Emit(Format(#9'movl $%s, %s', [IntToStr(AValue), AReg32]))
  else if (AValue < 0) and (AValue >= -2147483648) then
    { movq sign-extends its imm32 — correct for negative int32-range values.
      Positive values above 2^31-1 MUST NOT take this form: they do not fit
      the sign-extended imm32 (e.g. $FFFFFFFF would materialise as -1). }
    Self.Emit(Format(#9'movq $%s, %s', [IntToStr(AValue), AReg64]))
  else
    Self.Emit(Format(#9'movabsq $%s, %s', [IntToStr(AValue), AReg64]));
end;

function TX86_64Backend.TryGetImmValue(AExpr: TASTExpr; out AValue: Int64): Boolean;
begin
  AValue := 0;
  Result := True;
  if AExpr is TIntLiteral then
    AValue := TIntLiteral(AExpr).Value
  else if AExpr is TNilLiteral then
    AValue := 0
  else if (AExpr is TStringLiteral) and TStringLiteral(AExpr).IsCharCoerce then
    AValue := TStringLiteral(AExpr).CharOrdValue
  else if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsConstant and
          ((TIdentExpr(AExpr).ResolvedType = nil) or
           not TIdentExpr(AExpr).ResolvedType.IsString()) then
    AValue := TIdentExpr(AExpr).ConstValue
  else
    Result := False;
end;

function TX86_64Backend.TryEmitOperandToRcx(AExpr: TASTExpr): Boolean;
var
  E:   TIdentExpr;
  Ty:  TTypeDesc;
  Imm: Int64;
begin
  Result := True;
  if Self.TryGetImmValue(AExpr, Imm) then
  begin
    Self.EmitImmToReg(Imm, '%rcx', '%ecx');
    Exit;
  end;
  if not (AExpr is TIdentExpr) then
    Exit(False);
  E := TIdentExpr(AExpr);
  { Only plain scalar loads qualify — every special ident form (metaclass,
    implicit Self, captured outer local, aggregate/interface/method-ptr
    value, sret Result) keeps the general push/pop path. }
  if E.IsMetaclassRef or E.IsImplicitSelfMethod or E.IsImplicitSelf or
     E.IsConstant or Self.IsCaptured(E.Name) then
    Exit(False);
  if FSretFunc and SameText(E.Name, 'Result') then
    Exit(False);
  Ty := Self.IntExprType(E);
  if not (IsIntFamily(Ty) or
          ((Ty <> nil) and (Ty.Kind in [tyPointer, tyPChar]))) then
    Exit(False);
  if E.ParamMode <> pmNone then
  begin
    { var/out/by-ref param: slot holds the address; deref into %rcx. }
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(E.Name)]));
    Self.EmitLoadVarToReg('(%rcx)', Ty, '%rcx', '%ecx');
    Exit;
  end;
  Self.EmitLoadVarToReg(Self.VarOperand(E.Name), Ty, '%rcx', '%ecx');
end;

{ Store the value in %rax to memory at the slot's natural width, using the
  matching register sub-view (%al / %ax / %eax / %rax). }
procedure TX86_64Backend.EmitStoreVar(const AOperand: string; AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: Self.Emit(Format(#9'movb %%al, %s', [AOperand]));
    2: Self.Emit(Format(#9'movw %%ax, %s', [AOperand]));
    8: Self.Emit(Format(#9'movq %%rax, %s', [AOperand]));
  else
    Self.Emit(Format(#9'movl %%eax, %s', [AOperand]));
  end;
end;

{ Reserve a slot for AName of type AType in the current frame, advancing
  AOffset by the slot size (8 bytes for scalars/pointers; TotalSize rounded
  up to the next 8-byte boundary for records).  Stores the offset as a
  negative integer so VarOperand emits -N(%rbp). }
procedure TX86_64Backend.AddSlot(const AName: string; AType: TTypeDesc;
                                 var AOffset: Integer);
var
  Sz: Integer;
begin
  if ((AType <> nil) and (AType.Kind in [tyRecord, tyStaticArray])) or
     IsJumboSet(AType) then
    Sz := (AType.RawSize() + 7) and (-8)   { full inline aggregate slot }
  else if (AType <> nil) and (AType.Kind = tyInterface) then
    Sz := 16   { fat pointer: obj slot (+0) then itab slot (+8) }
  else if (AType <> nil) and (AType.Kind = tyProcedural) and
          (TProceduralTypeDesc(AType).IsMethodPtr or
           TProceduralTypeDesc(AType).IsReference) then
    Sz := 16   { method ptr / closure: code slot (+0) and data/env slot (+8) }
  else
    Sz := 8;
  Inc(AOffset, Sz);
  FFrame.Add(AName, -AOffset);
  FFrameTypes.Add(AName, AType);
  Self.DbgRecordSlot(AName, AType, -AOffset);
end;

procedure TX86_64Backend.BuildFrame(ADecl: TMethodDecl);
var
  I, J, K, Offset, StackOff, TryCount, IntIdx2, XmmIdx2: Integer;
  P:    TMethodParam;
  VD:   TVarDecl;
  HasJumbo: Boolean;
begin
  Self.ClearFrame();
  FFrame      := TDictionary<string, Integer>.Create();
  FFrameTypes := TDictionary<string, TTypeDesc>.Create();
  Offset   := 0;
  StackOff := 16;  { first stack arg: +16(%rbp) — above saved %rbp and ret addr }

  { Determine sret-ness UP FRONT.  The hidden sret buffer pointer consumes an
    integer register (%rdi), which shifts where the visible params land — so the
    param-register accounting below must know this before assigning slots.  This
    classification was historically done only when allocating the Result slot
    (further down), i.e. AFTER the param loop, leaving FSretFunc stale from the
    previous function and mis-placing a stack-passed param of an sret method as
    the last register param. }
  FSretFunc := False;
  FRecRetClass := rcSret;
  if ADecl.ResolvedReturnType <> nil then
  begin
    if (ADecl.ResolvedReturnType.Kind = tyInterface) or
       IsJumboSet(ADecl.ResolvedReturnType) or
       (ADecl.ResolvedReturnType.Kind = tyStaticArray) then
      FSretFunc := True
    else if ADecl.ResolvedReturnType.Kind = tyRecord then
    begin
      FRecRetClass := ClassifyRecordReturn(
        TRecordTypeDesc(ADecl.ResolvedReturnType));
      FSretFunc := FRecRetClass = rcSret;
    end
    else if IsMethodPtrType(ADecl.ResolvedReturnType) then
    begin
      { A method pointer is a 16-byte [Code; Data] aggregate — two integer
        eightbytes -> rcInt2 (rax:rdx) on SysV.  Route it through the same
        record-return machinery as a real two-pointer record. }
      FRecRetClass := ClassifyRecordReturn(MethodPtrReturnRec());
      FSretFunc := FRecRetClass = rcSret;
    end;
  end;

  { Captured outer-scope variables are prepended as implicit leading pointer
    params before Self and normal params.  Each captured var gets a pointer-size
    slot named '_cap_<VarName>' in the frame. }
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
  begin
    for I := 0 to ADecl.CapturedVars.Count - 1 do
      Self.AddSlot('_cap_' + ADecl.CapturedVars.Strings[I], nil, Offset);
    { A nested routine that captured the enclosing METHOD's Self (BUG-008)
      also gets a REAL 'Self' slot, filled in the prologue by loading through
      _cap_Self, so every hardcoded implicit-Self path works exactly as
      inside the method (mirrors the anon-thunk Self slot below). }
    if (ADecl.OwnerTypeName = '') and
       (ADecl.CapturedVars.IndexOf('Self') >= 0) then
      Self.AddSlot('Self', nil, Offset);
  end;

  { Phase-2 anonymous-method capture: the env base slot plus one
    '_cap_<Name>' pointer slot per promoted name.  These are NOT hidden
    params (no IntIdx2 accounting) — EmitEnvPrologue fills them from the
    env record.  The promoted locals keep their ordinary (now dead) slots:
    zero-init writes them harmlessly and the scope-exit ARC pass releases
    their permanently-nil values as a no-op, while all real accesses
    redirect through IsCaptured. }
  if ADecl.EnvCaptured <> nil then
  begin
    Self.AddSlot('__envp', nil, Offset);
    for I := 0 to ADecl.EnvCaptured.Count - 1 do
      Self.AddSlot('_cap_' + ADecl.EnvCaptured.Strings[I], nil, Offset);
    { Thunk lifted from a method body (Phase 3): a REAL 'Self' slot, filled
      from the env field by EmitEnvPrologue, so every hardcoded
      implicit-Self path works exactly as inside the method. }
    if ADecl.IsAnonThunk and (ADecl.EnvCaptured.IndexOf('Self') >= 0) then
      Self.AddSlot('Self', nil, Offset);
  end;

  { Phase-4 block-scoped envs: one tracking slot per block env, plus the
    per-name '_cap_' pointer slots refilled at each block execution. }
  if ADecl.BlockEnvTypes <> nil then
    for I := 0 to ADecl.BlockEnvTypes.Count - 1 do
      Self.AddSlot('__envp_b' + IntToStr(I), nil, Offset);
  if ADecl.BlockEnvCaptured <> nil then
    for I := 0 to ADecl.BlockEnvCaptured.Count - 1 do
      Self.AddSlot('_cap_' + ADecl.BlockEnvCaptured.Strings[I], nil, Offset);

  { For class methods, Self is the implicit first integer param (%rdi).
    Allocate a pointer-size slot for it; normal params start at IntIdx=1.
    A `static` method takes NO implicit Self (like a class function/Java
    static), so no Self slot is reserved and the first user param occupies
    %rdi directly. }
  if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
    Self.AddSlot('Self', nil, Offset);  { nil = pointer size (8 bytes) }

  { Params: first 6 integer register slots are register-passed (spilled to
    negative slots in prologue); slots 7+ are on the stack at positive %rbp
    offsets.  Open-array params consume TWO register slots each: data ptr and
    high index.  Track IntIdx2 separately from the logical param index I. }
  begin
    IntIdx2 := 0;
    XmmIdx2 := 0;
    { Captured vars, the sret buffer pointer, and Self EACH consume one integer
      register slot, and they stack: an sret-returning class/interface method
      uses %rdi for the buffer AND %rsi for Self, so the count must include
      BOTH (not one or the other).  This mirrors the prologue spill loop, which
      sets IntIdx := 1 for sret then Inc's again for Self; the two must agree or
      a stack-passed param is mistaken for the last register param. }
    if (ADecl.CapturedVars <> nil) then
      Inc(IntIdx2, ADecl.CapturedVars.Count);
    if FSretFunc then
      Inc(IntIdx2);  { sret buffer pointer in %rdi }
    if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
      Inc(IntIdx2);  { Self in the next integer register (static methods have none) }
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      P := TMethodParam(ADecl.Params.Items[I]);
      if P.IsOpenArray then
      begin
        { Two register slots: data pointer and high index. }
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, nil, Offset)   { nil = pointer-size (8 bytes) }
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, nil);
          Self.DbgRecordSlot(P.ParamName, nil, StackOff);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName + '_high', nil, Offset)
        else
        begin
          FFrame.Add(P.ParamName + '_high', StackOff);
          FFrameTypes.Add(P.ParamName + '_high', nil);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
      end
      else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) then
      begin
        { Interface param: fat pointer = two consecutive integer register slots.
          Allocate a single 16-byte slot (obj at base, itab at base+8) so that
          IntfObjOperand/IntfItabOperand can address both halves.  Two IntIdx
          increments mirror the register-passing convention. }
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Self.DbgRecordSlot(P.ParamName, P.ResolvedType, StackOff);
          Inc(StackOff, 16);
        end;
        Inc(IntIdx2);
        { Second slot (itab): if register-passed, no separate frame entry needed
          (AddSlot already reserved 16 bytes at ParamName); if stack-passed the
          itab word sits at StackOff+8 which IntfItabOperand computes from Off+8. }
        Inc(IntIdx2);
      end
      else if (P.ResolvedType <> nil) and
              ((P.ResolvedType.Kind in [tyRecord, tyStaticArray]) or
               IsJumboSet(P.ResolvedType)) and
              not P.IsVarParam then
      begin
        if IntIdx2 < 6 then
        begin
          Self.AddSlot(P.ParamName, nil, Offset);
          Self.AddSlot(P.ParamName + '_data', P.ResolvedType, Offset);
        end
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, nil);
          Self.DbgRecordSlot(P.ParamName, nil, StackOff);
          Inc(StackOff, 8);
          Self.AddSlot(P.ParamName + '_data', P.ResolvedType, Offset);
        end;
        Inc(IntIdx2);
      end
      else if IsFloatFamily(P.ResolvedType) and not P.IsVarParam then
      begin
        { Float param: consumes an SSE (xmm) arg register, NOT an integer one,
          and must not advance IntIdx2 (a following integer param would
          otherwise be mis-placed onto the stack — the caller passes it in an
          integer register).  Mirrors the prologue spill loop's float branch. }
        if XmmIdx2 < 8 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Self.DbgRecordSlot(P.ParamName, P.ResolvedType, StackOff);
          Inc(StackOff, 8);
        end;
        Inc(XmmIdx2);
      end
      else
      begin
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          { Stack-passed param: lives at +StackOff(%rbp), pushed by caller. }
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Self.DbgRecordSlot(P.ParamName, P.ResolvedType, StackOff);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
      end;
    end;
  end;
  { Result slot for a function (not a procedure).
    For a record-returning (sret) function the Result IS the caller's buffer —
    we store the incoming sret pointer (%rdi) in an 8-byte slot and dereference
    through it on every field write.  We record the slot as tyPointer so
    VarOperand returns the slot address (not the record address).
    For small POD records that qualify for register return, Result is a local
    buffer and the epilogue loads it into rax/rdx/xmm0/xmm1. }
  { FSretFunc / FRecRetClass were classified up front (see top of BuildFrame).
    Here we only allocate the Result slot: an sret return stores the incoming
    hidden buffer pointer (record/interface/jumbo-set/static-array), so the slot
    is pointer-sized; a register-returned record / scalar gets a typed slot. }
  if ADecl.ResolvedReturnType <> nil then
  begin
    if FSretFunc then
      Self.AddSlot('Result', nil, Offset)
    else
      Self.AddSlot('Result', ADecl.ResolvedReturnType, Offset);
  end;
  { Local var declarations. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(ADecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
        Self.AddSlot(VD.Names.Strings[J], VD.ResolvedType, Offset);
    end;
  { Pre-allocate 512-byte exception frame slots — one per try/finally or
    try/except in the function body (recursively).  Pre-allocation ensures
    frames live at static %rbp-relative addresses rather than being carved
    from %rsp inside a loop, which would grow the stack by 512 bytes per
    iteration and corrupt parent frame prev-pointers.
    Each slot name is '_exc_frame_N'; VarOperand returns the low-address
    operand (-N(%rbp)), which is what _PushExcFrame expects as the frame base. }
  if ADecl.Body <> nil then
  begin
    TryCount := 0;
    for K := 0 to ADecl.Body.Stmts.Count - 1 do
      TryCount := TryCount + Self.CountTryStmts(TASTStmt(ADecl.Body.Stmts.Items[K]));
    for K := 0 to TryCount - 1 do
    begin
      { Each frame is 512 bytes, 16-byte aligned.  We bump Offset by 512 and
        store the negative offset as the slot base (the lowest address of the
        block, matching alloc16 semantics). }
      Inc(Offset, 512);
      { Align to 16 bytes after the bump. }
      Offset := (Offset + 15) and (-16);
      FFrame.Add('_exc_frame_' + IntToStr(K), -Offset);
      FFrameTypes.Add('_exc_frame_' + IntToStr(K), nil);
    end;
  end;
  if ADecl.Body <> nil then
  begin
    TryCount := 0;
    for K := 0 to ADecl.Body.Stmts.Count - 1 do
      TryCount := TryCount + Self.CountForStmts(TASTStmt(ADecl.Body.Stmts.Items[K]));
    for K := 0 to TryCount - 1 do
      Self.AddSlot('_for_end_' + IntToStr(K), nil, Offset);
  end;
  { Except paths park the in-flight exception in %r15 across handler
    bodies; the function must preserve the caller's %r15 (see FTryR15Save). }
  FTryR15Save := FFrame.ContainsKey('_exc_frame_0');
  if FTryR15Save then
    Self.AddSlot('_try_r15_save', nil, Offset);
  { Jumbo-set scratch slots: a jumbo set literal, union, intersection, or
    difference produces a new bitmap that must live somewhere addressable.
    Such a value can appear deep inside any expression (e.g. 'X in [members]'
    over a >64-member enum, which is common in the compiler's own token tests),
    so rather than walk the whole body we reserve the two 32-byte scratch slots
    in every function frame.  The cost is 64 bytes per frame; correctness and
    self-host stability outweigh it.  HasJumbo is retained for future
    refinement to a body-walk-gated reservation. }
  HasJumbo := True;
  if HasJumbo then
  begin
    Inc(Offset, 32);
    Offset := (Offset + 7) and (-8);
    FFrame.Add('_jset_scratch_0', -Offset);
    FFrameTypes.Add('_jset_scratch_0', nil);
    Inc(Offset, 32);
    Offset := (Offset + 7) and (-8);
    FFrame.Add('_jset_scratch_1', -Offset);
    FFrameTypes.Add('_jset_scratch_1', nil);
  end;
  { Statement-scoped deferred-release slots (BUG-003 native half): one 8-byte
    slot per PENDREL_SLOTS, holding a spilled owned-transient base pointer until
    its enclosing leaf statement flushes the release.  Always reserved (cheap:
    64 bytes) so any function's field-reads can defer without a pre-scan. }
  for I := 0 to PENDREL_SLOTS - 1 do
  begin
    Inc(Offset, 8);
    Offset := (Offset + 7) and (-8);
    FFrame.Add(Format('_pendrel_%d', [I]), -Offset);
    FFrameTypes.Add(Format('_pendrel_%d', [I]), nil);
  end;
  { Register promotion: slots to save/restore the callee-saved incumbents
    of %r14/%r15 across this function (pass 2 only). }
  if FPromoActive then
  begin
    for K := 0 to 3 do
      if FPromoVars[K] <> '' then
        Self.AddSlot('_promo_save_' + IntToStr(K), nil, Offset);
    if FPromoPinOk then
      Self.AddSlot('_promo_save_pin', nil, Offset);
  end;
  { Inline scratch slots: the largest qualifying call site's need, found
    by an optimistic pre-scan (emission re-validates per site).  Each
    8-byte slot is an individually NAMED frame slot (_inl_s0..) so the
    register-promotion ranking can see and promote the hot ones — this
    is what extends register residency INTO inlined bodies. }
  FInlineSlotCount := 0;
  if (FDbgFacts = nil) and (ADecl.Body <> nil) and not ADecl.NoStackFrame then
  begin
    IntIdx2 := 0;
    for K := 0 to ADecl.Body.Stmts.Count - 1 do
      if InlineNeedStmtD(TASTStmt(ADecl.Body.Stmts.Items[K]), 0) > IntIdx2 then
        IntIdx2 := InlineNeedStmtD(TASTStmt(ADecl.Body.Stmts.Items[K]), 0);
    FInlineSlotCount := IntIdx2 div 8;
    for K := 0 to FInlineSlotCount - 1 do
      Self.AddSlot('_inl_s' + IntToStr(K), nil, Offset);
  end;
  { Round the reserved size up to a 16-byte multiple (SysV alignment).
    -16 is the bitmask not(15) in two's complement (Blaise `not` is Boolean). }
  FFrameBottom := Offset;
  FFrameSize := (Offset + 15) and (-16);
end;

procedure TX86_64Backend.ClearFrame;
begin
  { Inline scratch state is per-frame: a stale non-zero slot count from
    the previous function would let a frameless context (EmitProgram's
    main, unit init sections) "inline" into slots it never reserved. }
  FInlineSlotCount := 0;
  if FFrame <> nil then
  begin
    FFrame.Free();
    FFrame := nil;
  end;
  if FFrameTypes <> nil then
  begin
    FFrameTypes.Free();
    FFrameTypes := nil;
  end;
  FFrameSize    := 0;
  FFrameBottom  := 0;
  FSretFunc     := False;
  FRecRetClass  := rcSret;
  FExcDepth     := 0;
  FExcFrameNext := 0;
  FForEndNext   := 0;
  FFinallyStack.Free();
  FFinallyStack := TList<TCompoundStmt>.Create();
end;

{ ------------------------------------------------------------------ }
{ Expression lowering                                                  }
{ ------------------------------------------------------------------ }

function TX86_64Backend.IntExprType(AExpr: TASTExpr): TTypeDesc;
var
  T: TTypeDesc;
begin
  if AExpr is TIdentExpr then
  begin
    { Prefer the slot's recorded type (local then global) over the node's
      ResolvedType: the slot type is what the memory actually holds. }
    T := Self.LocalType(TIdentExpr(AExpr).Name);
    if T = nil then
      T := Self.GlobalType(TIdentExpr(AExpr).Name);
    if T <> nil then
    begin
      Exit(T);
    end;
  end;
  Result := AExpr.ResolvedType;
end;

{ Re-narrow the value in %rax to AType, then re-extend so the register again
  holds a value consistent with that type.  Narrowing masks/truncates to the
  low N bits; widening sign- or zero-extends.  A no-op for a value already
  consistent with a 4- or 8-byte type, but harmless to apply. }
procedure TX86_64Backend.EmitNarrowToType(AType: TTypeDesc);
begin
  if AType = nil then Exit;
  { Pointer-shaped values are full 64-bit addresses — "narrowing" one (e.g.
    after a class cast TFoo(X), which routes through the type-cast call
    path) truncates the pointer to its low 32 bits. }
  if AType.Kind in [tyClass, tyMetaClass, tyInterface, tyString, tyPChar,
                    tyPointer, tyDynArray, tyOpenArray, tyRecord,
                    tyStaticArray, tyProcedural] then
    Exit;
  case IntByteSize(AType) of
    1: if IsUnsignedInt(AType) then
         Self.Emit(#9'movzbq %al, %rax')
       else
         Self.Emit(#9'movsbq %al, %rax');
    2: if IsUnsignedInt(AType) then
         Self.Emit(#9'movzwq %ax, %rax')
       else
         Self.Emit(#9'movswq %ax, %rax');
    8: ;  { already a full 64-bit value }
  else
    { 4-byte: re-establish the upper 32 bits per signedness. }
    if IsUnsignedInt(AType) then
      Self.Emit(#9'movl %eax, %eax')    { zero-extends into %rax }
    else
      Self.Emit(#9'movslq %eax, %rax');
  end;
end;

{ Inc(x)/Dec(x) — general-purpose handler.
  Emits load-from-address / add-or-sub / store-to-address, supporting:
  - simple local/global TIdentExpr
  - implicit-Self field TIdentExpr (bare FField inside a method)
  - var-param TIdentExpr (dereference the pointer)
  - TFieldAccessExpr (Rec.Field, Obj.Field)
  - TDerefExpr (P^) }
{ Compute the ADDRESS of an L-value slot into %rdx.  Supports plain
  identifiers (locals, globals, var-params, implicit-Self fields) and
  field-access targets: R.F (inline record), C.F (class variable — slot
  holds the object pointer), implicit-Self record/class bases, var-param
  record bases, and chained Base.F (Base evaluated to an address). }
{ Evaluate the RHS of a byte-sized store into %eax.

  Chr(N) must NOT lower via the normal _Chr call — that returns a heap
  string POINTER, and the byte store would truncate to the pointer's low
  byte (the "P[I] := Chr(N)" garbage bug).  Emit the argument N directly.
  Single-char string literals get the same fold to their ordinal.
  Mirrors the QBE backend's EmitByteRhs. }
procedure TX86_64Backend.EmitByteRhsToEax(AExpr: TASTExpr);
begin
  if (AExpr is TFuncCallExpr) and
     SameText(TFuncCallExpr(AExpr).Name, 'Chr') and
     (TFuncCallExpr(AExpr).Args.Count = 1) then
  begin
    Self.EmitExprToEax(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    Exit;
  end;
  if (AExpr is TStringLiteral) and
     (Length(TStringLiteral(AExpr).Value) = 1) then
  begin
    { Use StrAt (OrdAt) rather than Ord(Value[0]): the bare subscript-then-Ord
      idiom miscompiles under the self-hosted native stage (it produced a
      pointer-sized garbage immediate, surfacing as a CI-only failure of the
      S[i] := 'c' test), whereas StrAt is the stage-stable byte-read helper
      used everywhere else in this backend. }
    Self.Emit(Format(#9'movl $%d, %%eax',
      [StrAt(TStringLiteral(AExpr).Value, 0)]));
    Exit;
  end;
  Self.EmitExprToEax(AExpr);
end;

procedure TX86_64Backend.EmitLValueSlotAddr(AExpr: TASTExpr);
var
  IE:  TIdentExpr;
  FAE: TFieldAccessExpr;
  FI:  TFieldInfo;
  SlotAddrWrap: TAddrOfExpr;
begin
  if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr(AExpr);
    if IE.IsImplicitSelf and (IE.ImplicitFieldInfo <> nil) then
    begin
      FI := TFieldInfo(IE.ImplicitFieldInfo);
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
      if FI.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FI.Offset]));
    end
    else if IE.ParamMode <> pmNone then
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand(IE.Name)]))
    else
      Self.EmitVarAddr(IE.Name, '%rdx');
    Exit;
  end;
  if AExpr is TFieldAccessExpr then
  begin
    FAE := TFieldAccessExpr(AExpr);
    { Static (class-level) var used as an l-value (e.g. the receiver of
      TFoo.StaticVar.Free()): its storage IS the mangled global slot — load its
      address, not a field of an instance.  Has no FieldInfo, so this must
      precede the FieldInfo requirement below. }
    if FAE.IsClassVarRead then
    begin
      Self.Emit(Format(#9'leaq %s(%%rip), %%rdx',
        [NativeMangle(FAE.ClassVarEmitName)]));
      Exit;
    end;
    if FAE.FieldInfo = nil then
      raise ENativeCodeGenError.Create(
        'native backend: L-value field access has no resolved field info');
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      Self.Emit(#9'movq %rax, %rdx');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rdx), %rdx');
    end
    else if FAE.IsClassAccess or FAE.IsVarParam then
    begin
      { Class variable / var-param: the slot holds a POINTER — load it. }
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rdx');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rdx), %rdx');
    end
    else
      { Plain value record: take the address of its storage.  For an ordinary
        local the slot IS the record; for the sret Result the slot holds the
        buffer POINTER; for a nested-captured record the _cap_ slot holds the
        record's address — EmitVarBaseToReg(AWantAddress=True) handles all
        three.  Without this, SetLength(Result.DynField, N) and other l-value
        field slots in an sret function added the field offset to the address
        of the pointer slot instead of to the pointed-to record. }
      Self.EmitVarBaseToReg(FAE.RecordName, True, '%rdx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdx', [FAE.FieldInfo.Offset]));
    { An array-FIELD ELEMENT slot (SetLength(H.FNest[0], N) where FNest is an
      array field): %rdx now holds the address of the FIELD; apply the
      subscript so the slot address points at the indexed element, mirroring
      the QBE EmitLValueAddr IsArrayAccess tail.  Without this the subscript
      was dropped and SetLength wrote through the wrong slot -> SIGSEGV
      (BUG-20260723-native-setlength-field-array-elem). }
    if FAE.IsArrayAccess then
    begin
      Self.Emit(#9'movq %rdx, %rax');
      Self.EmitFieldArrayElemAddrToRax(FAE);
      Self.Emit(#9'movq %rax, %rdx');
    end;
    Exit;
  end;
  { Array element a[i] as an l-value slot (e.g. SetLength(m[i], n) for a 2-D
    dynamic array): its address is what @a[i] computes — evaluate that into
    %rax via a transient TAddrOfExpr, then move to %rdx. }
  if AExpr is TStringSubscriptExpr then
  begin
    SlotAddrWrap := TAddrOfExpr.Create();
    try
      SlotAddrWrap.Expr := AExpr;
      Self.EmitExprToEax(SlotAddrWrap);
    finally
      SlotAddrWrap.Expr := nil;   { AExpr owned by the caller }
      SlotAddrWrap.Free();
    end;
    Self.Emit(#9'movq %rax, %rdx');
    Exit;
  end;
  raise ENativeCodeGenError.Create(
    'native backend: unsupported L-value form');
end;

procedure TX86_64Backend.SetDebugFacts(AFacts: TDbgFacts);
begin
  FDbgFacts := AFacts;
end;

procedure TX86_64Backend.DbgBeginFunc(const ASymbol: string);
begin
  if FDbgFacts = nil then Exit;
  FDbgCur := FDbgFacts.BeginFunc(ASymbol);
  FDbgCur.SourceFile := FDbgSrcFile;
end;

procedure TX86_64Backend.DbgRecordSlot(const AName: string; AType: TTypeDesc;
  AOffset: Integer);
begin
  if FDbgCur = nil then Exit;
  { Skip internal bookkeeping slots (exception frames, open-array highs).
    '_data' record-param shadows and '_cap_' capture pointers are kept —
    DbgMarkParams presents the shadow AS the parameter and a capture slot
    AS the outer variable (indirect location). }
  if AName = '' then Exit;
  if (AName[0] = '_') and (Copy(AName, 0, 5) <> '_cap_') then Exit;
  if (Length(AName) > 5) and (Copy(AName, Length(AName) - 5, 5) = '_high') then Exit;
  FDbgCur.AddVar(AName, AType, AOffset);
end;

procedure TX86_64Backend.DbgMarkParams(ADecl: TMethodDecl);
var
  I: Integer;
  P: TMethodParam;
  V: TDbgVar;
  DV: TDbgVar;
  Sym: TSymbol;
  MDEncl: TMethodDecl;
begin
  if (FDbgCur = nil) or (ADecl = nil) then Exit;
  V := FDbgCur.FindVar('Self');
  if V <> nil then
  begin
    V.IsParam := True;
    { Type Self as the owning class so the debugger can drill its fields
      (the slot holds the instance pointer; pdr derefs class types). }
    if (V.TypeDesc = nil) and (ADecl.OwnerTypeName <> '') and
       (FSymTable <> nil) then
    begin
      Sym := FSymTable.Lookup(ADecl.OwnerTypeName);
      if (Sym <> nil) and (Sym.TypeDesc <> nil) then
        V.TypeDesc := Sym.TypeDesc;
    end;
  end;
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    V := FDbgCur.FindVar(P.ParamName);
    if V = nil then Continue;
    V.IsParam := True;
    V.IsVarParam := P.IsVarParam;
    V.IsConstParam := P.IsConstParam;
    { Value record/static-array params: the named slot holds an ABI pointer;
      the callee's inline copy lives in the '_data' shadow slot.  Present
      the shadow AS the parameter — its fields are inline at known offsets,
      which is what field drilldown needs. }
    DV := FDbgCur.FindVar(P.ParamName + '_data');
    if DV <> nil then
    begin
      FDbgCur.Vars.Delete(FDbgCur.Vars.IndexOf(V));   { drop the raw pointer slot }
      DV.Name := P.ParamName;
      DV.IsParam := True;
      DV.IsVarParam := P.IsVarParam;
      DV.IsConstParam := P.IsConstParam;
    end
    else if P.IsOpenArray then
    begin
      { Open-array parameter: the named slot holds the data pointer; the
        element count is High+1, where High lives in the companion
        '<name>_high' slot.  Record the companion offset so the OPDF
        emitter can locate the length — the debugger has no heap header
        to read it from. }
      V.IsOpenArray := True;
      if not FFrame.TryGetValue(P.ParamName + '_high', V.HighRbpOffset) then
        V.HighRbpOffset := 0;
      if (V.TypeDesc = nil) and (P.ResolvedType <> nil) then
        V.TypeDesc := P.ResolvedType;
    end
    else if P.IsVarParam then
    begin
      { var/out parameter: the slot holds the ADDRESS of the caller's
        variable — indirect location, typed as the VALUE. }
      V.Indirect := True;
      if (V.TypeDesc = nil) and (P.ResolvedType <> nil) then
        V.TypeDesc := P.ResolvedType;
    end
    else if (V.TypeDesc = nil) and (P.ResolvedType <> nil) then
      V.TypeDesc := P.ResolvedType;
  end;
  { Captured outer locals: each '_cap_<Name>' slot holds a pointer to the
    outer variable.  Present it as the variable itself via the indirect
    location, typed from the enclosing function's var/param declarations
    (FDbgOuterDecl — set while nested procs are emitted). }
  if ADecl.CapturedVars <> nil then
    for I := 0 to ADecl.CapturedVars.Count - 1 do
    begin
      if ADecl.CapturedVars.Strings[I] = 'Self' then
      begin
        { Captured METHOD Self (BUG-008): the routine has a REAL 'Self' slot,
          filled in the prologue by loading through _cap_Self.  Present that
          direct slot as Self, typed as the enclosing method's class, and
          drop the raw capture pointer. }
        V := FDbgCur.FindVar('_cap_Self');
        if V <> nil then
          FDbgCur.Vars.Delete(FDbgCur.Vars.IndexOf(V));
        V := FDbgCur.FindVar('Self');
        if (V <> nil) and (V.TypeDesc = nil) and (FSymTable <> nil) then
        begin
          MDEncl := FDbgOuterDecl;
          while (MDEncl <> nil) and (MDEncl.OwnerTypeName = '') do
            MDEncl := TMethodDecl(MDEncl.EnclosingDecl);
          if MDEncl <> nil then
          begin
            Sym := FSymTable.Lookup(MDEncl.OwnerTypeName);
            if (Sym <> nil) and (Sym.TypeDesc <> nil) then
              V.TypeDesc := Sym.TypeDesc;
          end;
        end;
        Continue;
      end;
      V := FDbgCur.FindVar('_cap_' + ADecl.CapturedVars.Strings[I]);
      if V = nil then Continue;
      V.Name := ADecl.CapturedVars.Strings[I];
      V.Indirect := True;
      if V.TypeDesc = nil then
        V.TypeDesc := Self.OuterVarType(ADecl.CapturedVars.Strings[I]);
    end;
  { Env-promoted captures (anonymous methods, Phase 2): each '_cap_<Name>'
    slot holds the heap env field's ADDRESS — present it as the variable
    itself via the indirect location, typed from the env record field.  In
    the enclosing routine the promoted local's ordinary slot is DEAD (all
    accesses redirect through the env) — drop it so the debugger shows the
    live env-backed value, not the stale frame slot. }
  if ADecl.EnvCaptured <> nil then
    for I := 0 to ADecl.EnvCaptured.Count - 1 do
    begin
      V := FDbgCur.FindVar(ADecl.EnvCaptured.Strings[I]);
      if V <> nil then
        FDbgCur.Vars.Delete(FDbgCur.Vars.IndexOf(V));
      V := FDbgCur.FindVar('_cap_' + ADecl.EnvCaptured.Strings[I]);
      if V = nil then Continue;
      V.Name := ADecl.EnvCaptured.Strings[I];
      V.Indirect := True;
      if (V.TypeDesc = nil) and (ADecl.EnvType <> nil) then
        V.TypeDesc := TRecordTypeDesc(ADecl.EnvType).FindField(
          ADecl.EnvCaptured.Strings[I]).TypeDesc;
    end;
end;

{ Resolve the type of a captured outer variable by name from the enclosing
  function's local var declarations and parameters.  Returns nil when no
  enclosing decl is recorded or the name is not found. }
function TX86_64Backend.OuterVarType(const AName: string): TTypeDesc;
var
  I, J: Integer;
  VD: TVarDecl;
  P: TMethodParam;
begin
  Result := nil;
  if FDbgOuterDecl = nil then Exit;
  if FDbgOuterDecl.Body <> nil then
    for I := 0 to FDbgOuterDecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(FDbgOuterDecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
        if SameText(VD.Names.Strings[J], AName) then
          Exit(VD.ResolvedType);
    end;
  for I := 0 to FDbgOuterDecl.Params.Count - 1 do
  begin
    P := TMethodParam(FDbgOuterDecl.Params.Items[I]);
    if SameText(P.ParamName, AName) then
      Exit(P.ResolvedType);
  end;
end;

procedure TX86_64Backend.DbgStmtLabel(AStmt: TASTStmt);
var
  L: TDbgLine;
begin
  if (FDbgCur = nil) or (AStmt = nil) then Exit;
  if AStmt.Line <= 0 then Exit;
  { Structural containers re-dispatch to their children; labelling them would
    duplicate the first child's line. }
  if AStmt is TCompoundStmt then Exit;
  L := TDbgLine.Create();
  L.LabelName := Format('.Ldbg_%d', [FDbgSeq]);
  L.Line := AStmt.Line;
  L.Col := AStmt.Col;
  Inc(FDbgSeq);
  FDbgCur.Lines.Add(L);
  Self.Emit(L.LabelName + ':');
end;

procedure TX86_64Backend.DbgEndFunc;
var
  EndLbl: string;
begin
  if FDbgCur = nil then Exit;
  EndLbl := Format('.Ldbg_end_%d', [FDbgSeq]);
  Inc(FDbgSeq);
  Self.Emit(EndLbl + ':');
  FDbgCur.EndLabel := EndLbl;
  FDbgCur := nil;
end;

function TX86_64Backend.IsNativeRecordCall(AExpr: TASTExpr): Boolean;
begin
  Result := False;
  { Interface (itab) dispatch has no ResolvedMethod — classify by the call's
    resolved return type instead, so a record-returning itab call routes
    through the sret/record-return path (EmitIntfRecordSretDispatch) like a
    direct record method call.  Mirrors the QBE IsRecordCall interface case. }
  if (AExpr is TMethodCallExpr) and
     (TMethodCallExpr(AExpr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AExpr).ResolvedClassType.Kind = tyInterface) then
  begin
    Result := (TMethodCallExpr(AExpr).ResolvedType <> nil) and
              (TMethodCallExpr(AExpr).ResolvedType.Kind = tyRecord);
    Exit;
  end;
  if (AExpr is TMethodCallExpr) and
     (TMethodCallExpr(AExpr).ResolvedMethod <> nil) and
     (TMethodDecl(TMethodCallExpr(AExpr).ResolvedMethod).ResolvedReturnType <> nil) and
     (TMethodDecl(TMethodCallExpr(AExpr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) then
    Exit(True);
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl <> nil) and
     (TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl).ResolvedReturnType <> nil) and
     (TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl).ResolvedReturnType.Kind = tyRecord) then
    Exit(True);
  if (AExpr is TInheritedCallExpr) and
     (TInheritedCallExpr(AExpr).ResolvedMethod <> nil) and
     (TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod).ResolvedReturnType <> nil) and
     (TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) then
    Exit(True);
  { Method-backed property read whose getter returns a record — a getter call,
    routed through EmitRecordCallSretAt (which synthesises the method call).
    An INDEXED property (PropIndexExpr <> nil) is handled too: the index is
    threaded into the synthesised call as the getter's argument (BUG-20260719-
    native-indexed-prop-record), mirroring the QBE EmitRecordCallSret path. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).PropRead <> nil) and
     (TFieldAccessExpr(AExpr).PropReadDecl <> nil) and
     (TFieldAccessExpr(AExpr).PropRead.TypeDesc <> nil) and
     (TFieldAccessExpr(AExpr).PropRead.TypeDesc.Kind = tyRecord) then
    Exit(True);
  { A DEFAULT-array-property subscript (Obj[I]) that returns a record is lowered
    as a TStringSubscriptExpr wrapping that same record-returning PropRead
    FieldAccess.  Treat it as a record call by unwrapping to the inner StrExpr,
    so both the record-into-var assignment (V := Obj[I]) and a field-read off it
    (Obj[I].F) route through the sret path (BUG-002 A-indexed via default
    subscript). }
  if (AExpr is TStringSubscriptExpr) then
    Exit(Self.IsNativeRecordCall(TStringSubscriptExpr(AExpr).StrExpr));
end;

function TX86_64Backend.RecordCallReceiverIsVar(AExpr: TASTExpr;
  const AName: string; AIsGlobal: Boolean): Boolean;
var
  MCall: TMethodCallExpr;
  MDecl: TMethodDecl;
begin
  Result := False;
  if not (AExpr is TMethodCallExpr) then Exit;
  MCall := TMethodCallExpr(AExpr);
  if MCall.ResolvedMethod = nil then Exit;
  MDecl := TMethodDecl(MCall.ResolvedMethod);
  if not MDecl.IsRecordMethod then Exit;
  { Only a bare variable receiver (M.Method) can alias the destination var. }
  if MCall.ObjExpr <> nil then Exit;
  Result := (MCall.ObjectName = AName) and (MCall.IsGlobal = AIsGlobal);
end;

function TX86_64Backend.CallAliasesDestVar(AExpr: TASTExpr;
  const AName: string; AIsGlobal: Boolean): Boolean;
var
  Args: TObjectList;
  I:    Integer;
  Arg:  TASTExpr;
begin
  Result := False;
  { receiver alias — M := M.Method(...) }
  if Self.RecordCallReceiverIsVar(AExpr, AName, AIsGlobal) then Exit(True);
  { argument alias — X := F(X) / X := F(N, X) / X := Obj.M(X).  Only a bare
    identifier is matched: a subscript, field access or expression is not a
    whole-variable alias of the destination var. }
  Args := nil;
  if AExpr is TFuncCallExpr then
    Args := TFuncCallExpr(AExpr).Args
  else if AExpr is TMethodCallExpr then
    Args := TMethodCallExpr(AExpr).Args;
  if Args = nil then Exit;
  for I := 0 to Args.Count - 1 do
  begin
    Arg := TASTExpr(Args.Items[I]);
    if not (Arg is TIdentExpr) then Continue;
    if TIdentExpr(Arg).Name <> AName then Continue;
    if TIdentExpr(Arg).IsGlobal <> AIsGlobal then Continue;
    Exit(True);
  end;
end;

{ Emit an sret (record/jumbo-set/static-array-returning) call for a
  TFuncCallExpr.  An implicit-Self method is routed through EmitMethodSretCall
  (which passes Self and vtable-dispatches a virtual method); a free function
  goes through EmitSretCall.  Without this an implicit-Self virtual method
  returning a record would be static-dispatched (wrong override, abstract-base
  link error) and miss its Self receiver. }
procedure TX86_64Backend.EmitFuncCallSret(AFC: TFuncCallExpr;
  const ADest: string; AIndirect: Boolean);
var
  Synth: TMethodCallExpr;
begin
  if AFC.IsImplicitSelfMethod then
  begin
    Synth := TMethodCallExpr.Create();
    try
      Synth.Name           := AFC.Name;
      Synth.Args           := AFC.Args;    { borrowed — detached before Free }
      Synth.ResolvedMethod := AFC.ResolvedDecl;
      Synth.ResolvedType   := AFC.ResolvedType;
      Self.EmitMethodSretCall(Synth, ADest, AIndirect);
    finally
      Synth.Args := nil;   { do not free the borrowed arg list }
      Synth.Free();
    end;
  end
  else
    Self.EmitSretCall(FuncSymbolOf(AFC), TMethodDecl(AFC.ResolvedDecl),
      AFC.Args, ADest, AIndirect);
end;

procedure TX86_64Backend.EmitRecordCallSretAt(AExpr: TASTExpr; const ADest: string;
  AIndirect: Boolean);
var
  FAE:      TFieldAccessExpr;
  Synth:    TMethodCallExpr;
  SynthArgs: TObjectList;
begin
  { Unwrap a default-array-property subscript (Obj[I]) to its inner
    record-returning PropRead FieldAccess so it shares the sret path with the
    named form (BUG-002 A-indexed via default subscript). }
  if AExpr is TStringSubscriptExpr then
    AExpr := TStringSubscriptExpr(AExpr).StrExpr;
  { Record-returning property read (O.Prop): a getter call, so synthesise the
    method call from the resolved getter decl and route it through
    EmitMethodSretCall exactly as a record-returning method call.  An INDEXED
    property (PropIndexExpr <> nil) threads its index into the synthesised call
    as the getter's single argument (BUG-20260719-native-indexed-prop-record) —
    EmitMethodSretCall then marshals it correctly for both the register-return
    and sret-return record classes, exactly as for a direct O.Get(index) call. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).PropRead <> nil) and
     (TFieldAccessExpr(AExpr).PropReadDecl <> nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    Synth := TMethodCallExpr.Create();
    SynthArgs := nil;
    try
      Synth.Name           := FAE.PropRead.ReadMethod;
      Synth.ResolvedMethod := FAE.PropReadDecl;
      Synth.ResolvedType   := FAE.ResolvedType;
      Synth.ObjExpr        := FAE.Base;          { borrowed — detached before Free }
      if FAE.Base = nil then
      begin
        Synth.ObjectName := FAE.RecordName;
        Synth.IsGlobal   := FAE.IsGlobal;
      end;
      if FAE.PropIndexExpr <> nil then
      begin
        { non-owning list carrying the borrowed index expr — detached below }
        SynthArgs := TObjectList.Create(False);
        SynthArgs.Add(FAE.PropIndexExpr);
        Synth.Args := SynthArgs;
      end;
      Self.EmitMethodSretCall(Synth, ADest, AIndirect);
    finally
      Synth.ObjExpr := nil;   { do not free the borrowed base expression }
      Synth.Args    := nil;   { do not free the borrowed index expr }
      Synth.Free();
      SynthArgs.Free();       { frees the wrapper list only (OwnsObjects=False) }
    end;
    Exit;
  end;
  if (AExpr is TMethodCallExpr) and
     (TMethodCallExpr(AExpr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AExpr).ResolvedClassType.Kind = tyInterface) then
    { Interface (itab) record-returning dispatch — EmitMethodSretCall raises on
      a nil ResolvedMethod, so route through the itab record-return helper. }
    Self.EmitIntfRecordSretDispatch(TMethodCallExpr(AExpr), ADest, AIndirect)
  else if AExpr is TMethodCallExpr then
    Self.EmitMethodSretCall(TMethodCallExpr(AExpr), ADest, AIndirect)
  else if AExpr is TInheritedCallExpr then
    Self.EmitInheritedRecordSret(
      TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod),
      TInheritedCallExpr(AExpr).Args,
      TInheritedCallExpr(AExpr).Name, ADest, AIndirect)
  else
    Self.EmitFuncCallSret(TFuncCallExpr(AExpr), ADest, AIndirect);
end;

function TX86_64Backend.DeferNativeClassRelease: Boolean;
begin
  { Spill the owned-transient base pointer currently in %rax into the next free
    _pendrel slot and record it as pending.  Returns False (no slot free) so the
    caller falls back to its own inline handling — never emits incorrect code. }
  if FPendingRelCount >= PENDREL_SLOTS then
  begin
    Result := False;
    Exit;
  end;
  Self.Emit(Format(#9'movq %%rax, %s',
    [Self.VarOperand(Format('_pendrel_%d', [FPendingRelCount]))]));
  if not Self.IsLocal(Format('_pendrel_%d', [FPendingRelCount])) then
    FProgHasPendRel := True;   { $main body uses a .bss pendrel slot }
  FPendingRelCount := FPendingRelCount + 1;
  Result := True;
end;

procedure TX86_64Backend.FlushNativePendingReleases(AMark: Integer);
begin
  { Release every deferred base at slot index >= AMark (LIFO), then shrink the
    count back to the mark.  Called at leaf-statement boundaries AFTER the store,
    so the field value the base's graph owned has already been consumed. %rax /
    %rdi are free at a statement boundary, so no save/restore is needed. }
  while FPendingRelCount > AMark do
  begin
    FPendingRelCount := FPendingRelCount - 1;
    Self.Emit(Format(#9'movq %s, %%rdi',
      [Self.VarOperand(Format('_pendrel_%d', [FPendingRelCount]))]));
    Self.Emit(#9'callq _ClassRelease');
  end;
end;

procedure TX86_64Backend.EmitIncDec(ACall: TProcCall);
var
  Arg0: TASTExpr;
  IE: TIdentExpr;
  FAE: TFieldAccessExpr;
  IsInc, IsWide, HasStep, NarrowIdent: Boolean;
  FI: TFieldInfo;
begin
  IsInc := SameText(ACall.Name, 'Inc');
  Arg0 := TASTExpr(ACall.Args.Items[0]);
  HasStep := ACall.Args.Count >= 2;
  IsWide := (Arg0.ResolvedType <> nil) and
            (Arg0.ResolvedType.Kind in [tyInt64, tyUInt64, tyClass, tyPointer]);

  if Arg0 is TIdentExpr then
  begin
    IE := TIdentExpr(Arg0);
    if HasStep then
    begin
      Self.EmitExprToEax(TASTExpr(ACall.Args.Items[1]));
      if IsWide then Self.Emit(#9'movq %rax, %rcx')
      else           Self.Emit(#9'movl %eax, %ecx');
    end;
    if IE.IsImplicitSelf and (IE.ImplicitFieldInfo <> nil) then
    begin
      FI := TFieldInfo(IE.ImplicitFieldInfo);
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
      if FI.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FI.Offset]));
      Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep, Arg0.ResolvedType);
    end
    else if IE.ParamMode <> pmNone then
    begin
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand(IE.Name)]));
      Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep, Arg0.ResolvedType);
    end
    else if Self.IsCaptured(IE.Name) then
    begin
      { Captured outer local: the _cap_ slot holds the var's ADDRESS — load it
        into %rdx and do the in-place add/sub through it. }
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('_cap_' + IE.Name)]));
      Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep, Arg0.ResolvedType);
    end
    else
    begin
      { A narrow (Byte/Word/SmallInt) GLOBAL is emitted PACKED (.balign 1/2),
        so a 32-bit load/store carries across byte boundaries and over-writes
        the neighbouring global (BUG-20260723-incdec-narrow-global-rmw).  Load
        and store at the variable's natural width via the same helpers
        EmitIncDecAddrOp uses; the 32-bit arithmetic is unchanged.  Narrow
        LOCALS are safe (8-byte frame slots), but this arm serves both, so key
        off the element width, not local-vs-global. }
      NarrowIdent := (Arg0.ResolvedType <> nil) and
                     (IntByteSize(Arg0.ResolvedType) < 4);
      if NarrowIdent then
        Self.EmitLoadVarToReg(Self.VarOperand(IE.Name), Arg0.ResolvedType,
          '%rax', '%eax')
      else if IsWide then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(IE.Name)]))
      else
        Self.Emit(Format(#9'movl %s, %%eax', [Self.VarOperand(IE.Name)]));
      if HasStep then
      begin
        if IsWide then
        begin
          if IsInc then Self.Emit(#9'addq %rcx, %rax')
          else          Self.Emit(#9'subq %rcx, %rax');
        end
        else
        begin
          if IsInc then Self.Emit(#9'addl %ecx, %eax')
          else          Self.Emit(#9'subl %ecx, %eax');
        end;
      end
      else
      begin
        if IsWide then
        begin
          if IsInc then Self.Emit(#9'addq $1, %rax')
          else          Self.Emit(#9'subq $1, %rax');
        end
        else
        begin
          if IsInc then Self.Emit(#9'addl $1, %eax')
          else          Self.Emit(#9'subl $1, %eax');
        end;
      end;
      if NarrowIdent then
        Self.EmitStoreVar(Self.VarOperand(IE.Name), Arg0.ResolvedType)
      else if IsWide then
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(IE.Name)]))
      else
        Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(IE.Name)]));

    end;
  end
  else if Arg0 is TFieldAccessExpr then
  begin
    FAE := TFieldAccessExpr(Arg0);
    { Compute the l-value SLOT address into %rdx via the shared path.  The
      hand-rolled version this replaced was missing IsClassAccess handling
      (an explicit class-instance receiver landed on the receiver's pointer
      slot instead of the instance) and the IsArrayAccess subscript tail
      (Inc(R.RI[1]) dropped the subscript) — both silently wrong on the
      native backend (BUG-20260723-native-incdec-field-receiver).
      EmitLValueSlotAddr covers static vars, class receivers, var-params,
      implicit Self, plain records, and field-array elements. }
    Self.EmitLValueSlotAddr(FAE);
    Self.Emit(#9'pushq %rdx');
    if HasStep then
    begin
      Self.EmitExprToEax(TASTExpr(ACall.Args.Items[1]));
      if IsWide then Self.Emit(#9'movq %rax, %rcx')
      else           Self.Emit(#9'movl %eax, %ecx');
    end;
    Self.Emit(#9'popq %rdx');
    Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep, Arg0.ResolvedType);
  end
  else if Arg0 is TDerefExpr then
  begin
    Self.EmitExprToEax(TDerefExpr(Arg0).Expr);
    Self.Emit(#9'pushq %rax');
    if HasStep then
    begin
      Self.EmitExprToEax(TASTExpr(ACall.Args.Items[1]));
      if IsWide then Self.Emit(#9'movq %rax, %rcx')
      else           Self.Emit(#9'movl %eax, %ecx');
    end;
    Self.Emit(#9'popq %rdx');
    Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep, Arg0.ResolvedType);
  end
  else if Arg0 is TStringSubscriptExpr then
  begin
    { Inc/Dec on a plain array-variable ELEMENT (A[i]): EmitLValueSlotAddr's
      TStringSubscriptExpr arm computes the element address into %rdx via a
      transient TAddrOfExpr.  Without this branch the subscript fell through
      to the raise while QBE (which routes Inc/Dec through EmitLValueAddr)
      accepted it (BUG-20260723-native-incdec-plain-array-elem). }
    Self.EmitLValueSlotAddr(Arg0);
    Self.Emit(#9'pushq %rdx');
    if HasStep then
    begin
      Self.EmitExprToEax(TASTExpr(ACall.Args.Items[1]));
      if IsWide then Self.Emit(#9'movq %rax, %rcx')
      else           Self.Emit(#9'movl %eax, %ecx');
    end;
    Self.Emit(#9'popq %rdx');
    Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep, Arg0.ResolvedType);
  end
  else
    raise ENativeCodeGenError.Create(
      'native backend: Inc/Dec on unsupported expression form');
end;

procedure TX86_64Backend.EmitIncDecAddrOp(IsInc, IsWide, HasStep: Boolean;
  AElemType: TTypeDesc);
var
  Narrow: Boolean;
begin
  { Load / store at the ELEMENT's natural width, not a fixed 32 bits.  A Byte
    or Word element loaded+stored as a 32-bit word carried out of the element
    into its neighbour (Inc of a 255-valued Byte incremented the next byte) and
    over-read up to 3 bytes past the element (BUG-20260723-incdec-narrow-elem-rmw).
    EmitLoadVarToReg zero/sign-extends the narrow value into %eax so the 32-bit
    add/sub is correct; EmitStoreVar writes back only the element's bytes, so
    Byte/Word wraparound stays modular and neighbours are untouched.  The
    arithmetic width is unchanged (32-bit for narrow, matching the step the
    caller placed in %ecx); only the memory access narrows. }
  Narrow := (AElemType <> nil) and (IntByteSize(AElemType) < 4);
  if Narrow then
    Self.EmitLoadVarToReg('(%rdx)', AElemType, '%rax', '%eax')
  else if IsWide then
    Self.Emit(#9'movq (%rdx), %rax')
  else
    Self.Emit(#9'movl (%rdx), %eax');
  if HasStep then
  begin
    if IsWide then
    begin
      if IsInc then Self.Emit(#9'addq %rcx, %rax')
      else          Self.Emit(#9'subq %rcx, %rax');
    end
    else
    begin
      if IsInc then Self.Emit(#9'addl %ecx, %eax')
      else          Self.Emit(#9'subl %ecx, %eax');
    end;
  end
  else
  begin
    if IsWide then
    begin
      if IsInc then Self.Emit(#9'addq $1, %rax')
      else          Self.Emit(#9'subq $1, %rax');
    end
    else
    begin
      if IsInc then Self.Emit(#9'addl $1, %eax')
      else          Self.Emit(#9'subl $1, %eax');
    end;
  end;
  if Narrow then
    Self.EmitStoreVar('(%rdx)', AElemType)
  else if IsWide then
    Self.Emit(#9'movq %rax, (%rdx)')
  else
    Self.Emit(#9'movl %eax, (%rdx)');
end;

{ Load a float value from memory into %xmm0. }
procedure TX86_64Backend.EmitLoadFloat(const AOperand: string; AType: TTypeDesc);
begin
  if (AType <> nil) and (AType.Kind = tySingle) then
    Self.Emit(Format(#9'movss %s, %%xmm0', [AOperand]))
  else
    Self.Emit(Format(#9'movsd %s, %%xmm0', [AOperand]));
end;

{ Store %xmm0 into memory. }
{ Adjust the float width of the value in %xmm0.  EmitExprToXmm0 leaves a
  SINGLE for tySingle-typed expressions and a DOUBLE for everything else
  (Double expressions, integer expressions through the int fallback, and
  integer literals).  Callers that need a specific width convert here. }
procedure TX86_64Backend.EmitXmm0WidthAdjust(ASrcType: TTypeDesc;
  AWantSingle: Boolean);
var
  SrcIsSingle: Boolean;
begin
  SrcIsSingle := (ASrcType <> nil) and (ASrcType.Kind = tySingle);
  if AWantSingle and not SrcIsSingle then
    Self.Emit(#9'cvtsd2ss %xmm0, %xmm0')
  else if SrcIsSingle and not AWantSingle then
    Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
end;

procedure TX86_64Backend.EmitStoreFloat(const AOperand: string; AType: TTypeDesc);
begin
  if (AType <> nil) and (AType.Kind = tySingle) then
    Self.Emit(Format(#9'movss %%xmm0, %s', [AOperand]))
  else
    Self.Emit(Format(#9'movsd %%xmm0, %s', [AOperand]));
end;

{ Evaluate a floating-point expression, leaving the result in %xmm0.
  Binary operators: push %xmm0 onto the stack via subq/movsd, evaluate the
  right operand into %xmm0, then pop the left into %xmm1 and combine.
  This mirrors the integer strategy (push %rax) without requiring movaps/movups
  shuffles. }
procedure TX86_64Backend.EmitExprToXmm0(AExpr: TASTExpr);
var
  FL:  TFloatLiteral;
  BE:  TBinaryExpr;
  FC:  TFuncCallExpr;
  MD:  TMethodDecl;
  Ty:  TTypeDesc;
  IsS: Boolean;
  I:   Integer;
  CleanBytes: Integer;
begin
  if AExpr is TFloatLiteral then
  begin
    FL  := TFloatLiteral(AExpr);
    Ty  := AExpr.ResolvedType;
    IsS := (Ty <> nil) and (Ty.Kind = tySingle);
    { Use a .rodata constant for the immediate float — x86 has no mov-imm
      for xmm registers.  Emit a file-local label that holds the 8-byte
      (Double) or 4-byte (Single) encoding of the literal. }
    if IsS then
    begin
      Self.Emit(Format(#9'movss .LF%s(%%rip), %%xmm0',
        [IntToStr(FLabelCount)]));
      { Defer the .rodata entry to the data section by registering a synthetic
        global with a special FP-literal tag.  We emit it directly since our
        data section is collected: just write it now in a .section .rodata block. }
      Self.Emit('.section .rodata');
      Self.Emit('.balign 4');
      Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
      Self.Emit(Format(#9'.float %s', [FL.Value]));
      Self.Emit('.text');
      Inc(FLabelCount);
    end
    else
    begin
      Self.Emit(Format(#9'movsd .LF%s(%%rip), %%xmm0',
        [IntToStr(FLabelCount)]));
      Self.Emit('.section .rodata');
      Self.Emit('.balign 8');
      Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
      Self.Emit(Format(#9'.double %s', [FL.Value]));
      Self.Emit('.text');
      Inc(FLabelCount);
    end;
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    Self.Emit(Format(#9'movsd .LF%s(%%rip), %%xmm0', [IntToStr(FLabelCount)]));
    Self.Emit('.section .rodata');
    Self.Emit('.balign 8');
    Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
    Self.Emit(Format(#9'.double %d.0', [TIntLiteral(AExpr).Value]));
    Self.Emit('.text');
    Inc(FLabelCount);
    Exit;
  end;

  { Integer-typed expression in a float context (e.g. Tanh(i), Power(2, n)):
    evaluate to %rax (sign-extended) and convert to double. }
  if (AExpr.ResolvedType <> nil) and IsIntFamily(AExpr.ResolvedType) then
  begin
    Self.EmitExprToEax(AExpr);
    Self.Emit(#9'cvtsi2sdq %rax, %xmm0');
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    { Implicit-Self float field read (FFloat inside a method): load from the
      Self instance at the field offset, NOT from a global symbol named after
      the field.  Without this the field reference falls through to the plain
      VarOperand path below and emits `movsd FFloat(%rip)` — an undefined
      symbol in per-unit (.o) codegen.  (The store path already handles this;
      only the read was missing it.) }
    if TIdentExpr(AExpr).IsImplicitSelf and
       (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx',
          [TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset]));
      Self.EmitLoadFloat('(%rcx)', AExpr.ResolvedType);
      Exit;
    end;
    { Float-typed named constant (const X = 6.28; ...): inline its literal
      value.  The const has no storage — its ConstString holds the source
      text — so loading from a symbol named after it (VarOperand) would
      reference an undefined label.  Emit the value via .rodata exactly as
      a TFloatLiteral does. }
    if TIdentExpr(AExpr).IsConstant and IsFloatFamily(AExpr.ResolvedType) then
    begin
      IsS := (AExpr.ResolvedType <> nil) and
             (AExpr.ResolvedType.Kind = tySingle);
      if IsS then
      begin
        Self.Emit(Format(#9'movss .LF%s(%%rip), %%xmm0', [IntToStr(FLabelCount)]));
        Self.Emit('.section .rodata');
        Self.Emit('.balign 4');
        Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
        Self.Emit(Format(#9'.float %s', [TIdentExpr(AExpr).ConstString]));
      end
      else
      begin
        Self.Emit(Format(#9'movsd .LF%s(%%rip), %%xmm0', [IntToStr(FLabelCount)]));
        Self.Emit('.section .rodata');
        Self.Emit('.balign 8');
        Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
        Self.Emit(Format(#9'.double %s', [TIdentExpr(AExpr).ConstString]));
      end;
      Self.Emit('.text');
      Inc(FLabelCount);
      Exit;
    end;
    Ty := AExpr.ResolvedType;
    if (Ty = nil) and Self.IsLocal(TIdentExpr(AExpr).Name) then
      Ty := Self.LocalType(TIdentExpr(AExpr).Name);
    if (Ty = nil) then
      Ty := Self.GlobalType(TIdentExpr(AExpr).Name);
    if Self.IsCaptured(TIdentExpr(AExpr).Name) then
    begin
      { CAPTURED first: a captured var-param is BOTH captured and ParamMode<>
        pmNone; the var-param arm below would wrongly use VarOperand(Name) =
        Name(%rip).  The _cap_ slot holds the enclosing var's address; a
        captured VAR/OUT param's enclosing slot in turn holds the caller's
        address, so deref once more before loading the float value
        (BUG-20260720-capture-varparam — the float arms mirror the integer ones). }
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand('_cap_' + TIdentExpr(AExpr).Name)]));
      if TIdentExpr(AExpr).ParamMode <> pmNone then
        Self.Emit(#9'movq (%rcx), %rcx');
      Self.EmitLoadFloat('(%rcx)', Ty);
    end
    else if TIdentExpr(AExpr).ParamMode <> pmNone then
    begin
      { var/out float param: the slot holds the value's address. }
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand(TIdentExpr(AExpr).Name)]));
      Self.EmitLoadFloat('(%rcx)', Ty);
    end
    else
      Self.EmitLoadFloat(Self.VarOperand(TIdentExpr(AExpr).Name), Ty);
    Exit;
  end;

  if AExpr is TFieldAccessExpr then
  begin
    Self.EmitFieldAddrToRcx(TFieldAccessExpr(AExpr));
    Ty := TFieldAccessExpr(AExpr).FieldInfo.TypeDesc;
    Self.EmitLoadFloat('(%rcx)', Ty);
    Exit;
  end;

  { Pointer dereference yielding a float: P^ where P: ^Double/^Single.
    Evaluate the pointer into %rcx and load the float from (%rcx). }
  if AExpr is TDerefExpr then
  begin
    Self.EmitExprToEax(TDerefExpr(AExpr).Expr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.EmitLoadFloat('(%rcx)', AExpr.ResolvedType);
    Exit;
  end;

  { Operator overloading: uSemantic normally REBINDS the owning slot to the
    synthesised call (AnalyseExprSlot), so a lowered operator reaches codegen
    as a plain TMethodCallExpr and every record/sret/ARC node-class test
    matches.  This guard is the belt-and-braces path for any slot not yet
    converted to the slot form — delegate to the general emitter rather than
    re-implementing the call here. }
  if (AExpr is TBinaryExpr) and (TBinaryExpr(AExpr).LoweredCall <> nil) then
  begin
    Self.EmitExprToXmm0(TBinaryExpr(AExpr).LoweredCall);
    Exit;
  end;
  if AExpr is TBinaryExpr then
  begin
    BE  := TBinaryExpr(AExpr);
    IsS := (BE.ResolvedType <> nil) and (BE.ResolvedType.Kind = tySingle);
    { left → %xmm0, push to stack via subq/movsd; right → %xmm0;
      pop left into %xmm1 via movsd/addq.  Operands whose own width differs
      from the operation width (mixed Single/Double, integer operands and
      integer literals — which EmitExprToXmm0 produces as Double) are
      converted as they arrive. }
    Self.EmitExprToXmm0(BE.Left);
    Self.EmitXmm0WidthAdjust(BE.Left.ResolvedType, IsS);
    Self.Emit(#9'subq $8, %rsp');
    if IsS then
      Self.Emit(#9'movss %xmm0, (%rsp)')
    else
      Self.Emit(#9'movsd %xmm0, (%rsp)');
    Self.EmitExprToXmm0(BE.Right);
    Self.EmitXmm0WidthAdjust(BE.Right.ResolvedType, IsS);
    if IsS then
    begin
      Self.Emit(#9'movss (%rsp), %xmm1');
      Self.Emit(#9'addq $8, %rsp');
      case BE.Op of
        boAdd:   Self.Emit(#9'addss %xmm0, %xmm1');
        boSub:   Self.Emit(#9'subss %xmm0, %xmm1');  { left - right }
        boMul:   Self.Emit(#9'mulss %xmm0, %xmm1');
        boSlash: Self.Emit(#9'divss %xmm0, %xmm1');
        boEQ, boNE, boLT, boGT, boLE, boGE:
          begin
            Self.Emit(#9'ucomiss %xmm0, %xmm1');  { %xmm1 - %xmm0 }
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');   { below (CF set) }
              boGT: Self.Emit(#9'seta %al');   { above }
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end;
            Self.Emit(#9'movzbl %al, %eax');
            Self.Emit(#9'movq %rax, %xmm0');  { comparison result as int in %rax then convert? }
            { Actually we need int result for condition tests — put result in %rax,
              then caller decides if it needs to be in %xmm0.  But EmitExprToXmm0
              is for float expressions; comparisons of floats return int (Boolean).
              Fall through: return the 0/1 in %rax.  The caller (EmitCondBranch)
              actually calls EmitExprToEax and tests %rax.  So we shouldn't reach
              here for comparisons — they go through EmitCondBranch → EmitExprToEax
              which will handle float comparisons. }
          end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float binary operator');
      end;
      { Result is in %xmm1, copy to %xmm0 if not a comparison. }
      if BE.Op in [boAdd, boSub, boMul, boSlash] then
        Self.Emit(#9'movaps %xmm1, %xmm0');
    end
    else
    begin
      Self.Emit(#9'movsd (%rsp), %xmm1');
      Self.Emit(#9'addq $8, %rsp');
      case BE.Op of
        boAdd:   Self.Emit(#9'addsd %xmm0, %xmm1');
        boSub:   Self.Emit(#9'subsd %xmm0, %xmm1');  { left - right }
        boMul:   Self.Emit(#9'mulsd %xmm0, %xmm1');
        boSlash: Self.Emit(#9'divsd %xmm0, %xmm1');
        boEQ, boNE, boLT, boGT, boLE, boGE:
          begin
            Self.Emit(#9'ucomisd %xmm0, %xmm1');
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');
              boGT: Self.Emit(#9'seta %al');
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end;
            Self.Emit(#9'movzbl %al, %eax');
            { Float comparisons result in integer 0/1 — return via %rax, not %xmm0. }
            Exit;
          end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float binary operator');
      end;
      Self.Emit(#9'movapd %xmm1, %xmm0');
    end;
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    if Self.EmitFloatBuiltin(FC) then
      Exit;
    { Float-returning INDIRECT call (procvar / method-ptr / closure): the
      callee leaves the result in %xmm0 — dispatch like the EmitExprToEax
      arm and use it directly.  Must run BEFORE the type-cast arm below:
      an indirect call also has ResolvedDecl=nil, and a one-arg call was
      mistaken for a cast, returning its ARGUMENT
      (BUG-20260722-native-procvar-float-args). }
    if FC.IsIndirectCall then
    begin
      if (FC.ResolvedProcType <> nil) and
         (TProceduralTypeDesc(FC.ResolvedProcType).IsMethodPtr or
          TProceduralTypeDesc(FC.ResolvedProcType).IsReference) then
        Self.EmitMethodPtrCall(
          Self.VarOperand(FC.Name),
          TProceduralTypeDesc(FC.ResolvedProcType),
          FC.Args)
      else
        Self.EmitCallIndirect(
          Self.VarOperand(FC.Name),
          TProceduralTypeDesc(FC.ResolvedProcType),
          FC.Args);
      Exit;
    end;
    if FC.IsProcFieldCall then
    begin
      Self.EmitProcFieldCall(nil, 'Self', False, FC.ProcFieldInfo,
        TProceduralTypeDesc(FC.ResolvedProcType), FC.Args, FC.ResolvedType);
      Exit;
    end;
    { Type cast Double(X) / Single(X): ResolvedDecl is nil.  Emit a real
      numeric conversion, never a bit copy. }
    if (FC.ResolvedDecl = nil) and (FC.Args.Count = 1) then
    begin
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         TASTExpr(FC.Args.Items[0]).ResolvedType.IsFloat() then
      begin
        Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
        if (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) and
           (FC.ResolvedType.Kind = tyDouble) then
          Self.Emit(#9'cvtss2sd %xmm0, %xmm0')
        else if (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyDouble) and
                (FC.ResolvedType.Kind = tySingle) then
          Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
      begin
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
        if FC.ResolvedType.Kind = tySingle then
          Self.Emit(#9'cvtsi2ssq %rax, %xmm0')
        else
          Self.Emit(#9'cvtsi2sdq %rax, %xmm0');
      end;
      Exit;
    end;
    if FC.IsImplicitSelfMethod and (FC.ResolvedDecl <> nil) then
    begin
      MD := TMethodDecl(FC.ResolvedDecl);
      Self.BeginCallArgs(MD.Params, FC.Args);
      for I := 0 to FC.Args.Count - 1 do
        Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
          TASTExpr(FC.Args.Items[I]), I);
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
      { Self + args can exceed the six integer registers: EmitSretRegArgs
        spills the overflow and returns the bytes to reclaim post-call. }
      CleanBytes := Self.EmitSretRegArgs(Self.CountArgSlots(MD.Params), 1);
      Self.Emit(#9'movq %r10, %rdi');
      Self.Emit(#9'callq ' + FuncSymbolOf(FC));
      if CleanBytes > 0 then
        Self.Emit(Format(#9'addq $%d, %%rsp', [CleanBytes]));
      Self.EndCallArgs();
      Exit;
    end;
    { User function call whose return type is float. }
    if Self.TryEmitInlineCall(FC.ResolvedDecl, FC.Args, True) then
      Exit;
    Self.EmitCall(FuncSymbolOf(FC), TMethodDecl(FC.ResolvedDecl), FC.Args);
    { Return value is in %xmm0 per SysV ABI. }
    Exit;
  end;

  { Qualified method call returning a float, e.g. d := Obj.GetF().  The method
    emitter performs vtable/static dispatch and the SysV ABI leaves the float
    result in %xmm0, so no further work is needed here. }
  if AExpr is TMethodCallExpr then
  begin
    Self.EmitMethodCallExpr(TMethodCallExpr(AExpr));
    Exit;
  end;

  { Float array element read A[I] (dynamic or static array of Double/Single).
    The element ADDRESS computation matches the integer EmitExprToEax subscript
    paths; only the final load differs — movsd/movss into %xmm0 rather than a
    GPR load.  Without this case a float element read falls through to the
    error below. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyDynArray) and
     IsFloatFamily(TDynArrayTypeDesc(
       TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType) then
  begin
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TDynArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType)
        .ElementType.RawSize()]));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.EmitLoadFloat('(%rax)',
      TDynArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType)
        .ElementType);
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyStaticArray) and
     IsFloatFamily(TStaticArrayTypeDesc(
       TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType) then
  begin
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).IndexExpr);
    Self.EmitStaticElemScale(
      TStaticArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.EmitLoadFloat('(%rax)',
      TStaticArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType)
        .ElementType);
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported float expression form ' + AExpr.ClassName);
end;

function TX86_64Backend.EmitFloatBuiltin(FC: TFuncCallExpr): Boolean;
var
  IsS: Boolean;
begin
  Result := True;
  { StrToDouble(S): the RTL helper takes a string pointer in %rdi and returns
    the Double in %xmm0.  It MUST be handled here in the float emitter — if it
    falls through to the integer EmitExprToEax path, the result (already in
    %xmm0) is discarded and the leftover %rax is cvtsi2sd'd into garbage. }
  if SameText(FC.Name, 'StrToDouble') and (FC.Args.Count = 1) then
  begin
    Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StrToDouble', True);
    Exit;
  end;
  if SameText(FC.Name, 'Abs') and (FC.Args.Count = 1) and
     (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
     TASTExpr(FC.Args.Items[0]).ResolvedType.IsFloat() then
  begin
    { float Abs: clear the sign bit via the runtime.math helper.  Without
      this arm the float emitter fell through and the argument came back
      UNCHANGED (Abs(-2.5) = -2.5) -- the integer Abs arm never applies
      in a float context. }
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseFabs');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseFabs');
    Exit;
  end;
  if SameText(FC.Name, 'Sqrt') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'sqrtss %xmm0, %xmm0')
    else
      Self.Emit(#9'sqrtsd %xmm0, %xmm0');
    Exit;
  end;
  if SameText(FC.Name, 'Sin') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseSin');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseSin');
    Exit;
  end;
  if SameText(FC.Name, 'Cos') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseCos');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseCos');
    Exit;
  end;
  if SameText(FC.Name, 'Tan') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseTan');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseTan');
    Exit;
  end;
  if SameText(FC.Name, 'ArcTan') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseArcTan');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseArcTan');
    Exit;
  end;
  if SameText(FC.Name, 'ArcTan2') and (FC.Args.Count = 2) then
  begin
    { each argument is widened to double by ITS OWN type (the old code
      keyed both on the first argument, mishandling mixed Single/Double
      pairs); the runtime.math function is double-only }
    IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if IsS then
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
    Self.Emit(#9'subq $8, %rsp');
    Self.Emit(#9'movsd %xmm0, (%rsp)');
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
    if (TASTExpr(FC.Args.Items[1]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[1]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
    Self.Emit(#9'movaps %xmm0, %xmm1');
    Self.Emit(#9'movsd (%rsp), %xmm0');
    Self.Emit(#9'addq $8, %rsp');
    Self.Emit(#9'callq _BlaiseArcTan2');
    if IsS then
      { result type follows the first argument }
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    Exit;
  end;
  if SameText(FC.Name, 'ArcSin') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseArcSin');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseArcSin');
    Exit;
  end;
  if SameText(FC.Name, 'ArcCos') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseArcCos');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseArcCos');
    Exit;
  end;
  if SameText(FC.Name, 'Ln') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseLn');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseLn');
    Exit;
  end;
  if SameText(FC.Name, 'Log2') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseLog2');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseLog2');
    Exit;
  end;
  if SameText(FC.Name, 'Log10') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseLog10');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseLog10');
    Exit;
  end;
  if SameText(FC.Name, 'Power') and (FC.Args.Count = 2) then
  begin
    { each argument is widened to double by ITS OWN type (the old code
      keyed both on the first argument, mishandling mixed Single/Double
      pairs); the runtime.math function is double-only }
    IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if IsS then
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
    Self.Emit(#9'subq $8, %rsp');
    Self.Emit(#9'movsd %xmm0, (%rsp)');
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
    if (TASTExpr(FC.Args.Items[1]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[1]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
    Self.Emit(#9'movaps %xmm0, %xmm1');
    Self.Emit(#9'movsd (%rsp), %xmm0');
    Self.Emit(#9'addq $8, %rsp');
    Self.Emit(#9'callq _BlaisePow');
    Exit;
  end;
  if SameText(FC.Name, 'Sinh') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseSinh');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseSinh');
    Exit;
  end;
  if SameText(FC.Name, 'Cosh') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseCosh');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseCosh');
    Exit;
  end;
  if SameText(FC.Name, 'Tanh') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'callq _BlaiseTanh');
      Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
    end
    else
      Self.Emit(#9'callq _BlaiseTanh');
    Exit;
  end;
  Result := False;
end;

{ Evaluate an integer-family expression, leaving a 64-bit-extended value in
  %rax.  Every value flows in the full register held sign- or zero-extended to
  its static type, so mixed-width arithmetic (e.g. Integer promoted into an
  Int64 expression) is correct without per-node width tracking; the final
  store re-narrows to the destination slot's width.  Arithmetic and
  comparisons use 64-bit ops uniformly. }
procedure TX86_64Backend.EmitExprToEax(AExpr: TASTExpr);
var
  BE:  TBinaryExpr;
  FC:  TFuncCallExpr;
  FAE: TFieldAccessExpr;
  SAE: TStringSubscriptExpr;
  MD:  TMethodDecl;
  IMD: TMethodDecl;
  Unsigned: Boolean;
  AOE: TAddrOfExpr;
  IE:  TIdentExpr;
  SetMask: Int64;
  SetI: Integer;
  I:   Integer;
  SetElem: TASTExpr;
  CastArg: TASTExpr;
  ScEndLbl: string;
  IsS: Boolean;
  DivOkLbl: string;
  HasImm: Boolean;
  ImmV: Int64;
  SuppOut: string;
  LSuppNo: string;
  LSuppEnd: string;
  SCAT: TStaticArrayTypeDesc;
begin
  if AExpr is TNilLiteral then
  begin
    Self.Emit(#9'xorq %rax, %rax');
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    { Shortest correct materialisation: movl (zero-extends), movq (sign-
      extended imm32) or movabsq for true 64-bit values. }
    Self.EmitImmToReg(TIntLiteral(AExpr).Value, '%rax', '%eax');
    Exit;
  end;

  if AExpr is TStringLiteral then
  begin
    if TStringLiteral(AExpr).IsCharCoerce then
      { Char context (e.g. S[I] = ','): the semantic pass marked this
        single-char literal for ordinal coercion — emitting the data
        pointer here would compare an address against a byte. }
      Self.Emit(Format(#9'movl $%d, %%eax',
        [TStringLiteral(AExpr).CharOrdValue]))
    else
      Self.EmitStrLitAddr(TStringLiteral(AExpr).Value);
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    if TIdentExpr(AExpr).IsMetaclassRef then
    begin
      { Bare class type identifier used as a value — the metaclass value IS
        the typeinfo address (same pointer vtable[0] holds at runtime),
        mirroring the QBE backend's `copy $typeinfo_<T>`. }
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rax',
        [Self.ClassSymName(TIdentExpr(AExpr).Name)]));
      Exit;
    end;
    if TIdentExpr(AExpr).IsImplicitSelfMethod and
       (TIdentExpr(AExpr).ImplicitMethodDecl <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
      IMD := TMethodDecl(TIdentExpr(AExpr).ImplicitMethodDecl);
      Self.Emit(Format(#9'callq %s',
        [MethodEmitNameNative(IMD, IMD.OwnerTypeName, IMD.Name)]));
      Exit;
    end;
    if TIdentExpr(AExpr).IsImplicitSelf and
       (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx',
          [TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset]));
      if (TIdentExpr(AExpr).ResolvedType <> nil) and
         (IsJumboSet(TIdentExpr(AExpr).ResolvedType) or
          IsMethodPtrType(TIdentExpr(AExpr).ResolvedType) or
          (TIdentExpr(AExpr).ResolvedType.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(#9'movq %rcx, %rax')
      else if (TIdentExpr(AExpr).ResolvedType <> nil) and
              (TIdentExpr(AExpr).ResolvedType.Kind = tyClass) then
        Self.Emit(#9'movq (%rcx), %rax')
      else
        Self.EmitLoadVar('(%rcx)', Self.IntExprType(AExpr));
      Exit;
    end;
    if (TIdentExpr(AExpr).ResolvedType <> nil) and
       (IsJumboSet(TIdentExpr(AExpr).ResolvedType) or
          IsMethodPtrType(TIdentExpr(AExpr).ResolvedType) or
          (TIdentExpr(AExpr).ResolvedType.Kind in [tyRecord, tyStaticArray])) then
    begin
      { Method-ptr / closure idents yield their block ADDRESS too — value
        params receive the address and callees copy 16 bytes (Phase 2b). }
      if FSretFunc and (TIdentExpr(AExpr).Name = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Result')]))
      else if Self.IsCaptured(TIdentExpr(AExpr).Name) then
        { Captured outer record/static-array: the _cap_ slot holds the address
          of the enclosing variable's storage.  For a captured plain local that
          IS the aggregate address (AWantAddress=True); for a captured var/out
          param the enclosing slot holds the caller's pointer, so one extra
          dereference (AWantAddress=False) yields the aggregate address. }
        Self.EmitVarBaseToReg(TIdentExpr(AExpr).Name,
          TIdentExpr(AExpr).ParamMode = pmNone, '%rax')
      else if Self.IsLocal(TIdentExpr(AExpr).Name) and
              (TIdentExpr(AExpr).ParamMode <> pmNone) then
        { Any param mode: the slot holds the record/array ADDRESS (value
          record/static-array params are ABI by-ref; var/out params hold
          the caller variable's address, which IS the aggregate). }
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(TIdentExpr(AExpr).Name)]))
      else if Self.IsLocal(TIdentExpr(AExpr).Name) then
        Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand(TIdentExpr(AExpr).Name)]))
      else if TIdentExpr(AExpr).ConstArraySymbol <> '' then
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [NativeMangle(TIdentExpr(AExpr).ConstArraySymbol)]))
      else
        Self.EmitLeaqGlobal(TIdentExpr(AExpr).Name, '%rax');
      Exit;
    end;
    if TIdentExpr(AExpr).IsConstant then
    begin
      if (TIdentExpr(AExpr).ResolvedType <> nil) and
         TIdentExpr(AExpr).ResolvedType.IsString() then
        Self.EmitStrLitAddr(TIdentExpr(AExpr).ConstString)
      else
        Self.EmitImmToReg(TIdentExpr(AExpr).ConstValue, '%rax', '%eax');
    end
    else if Self.IsCaptured(TIdentExpr(AExpr).Name) then
    begin
      { CAPTURED first: a captured var-param is BOTH captured and ParamMode<>
        pmNone; the param arm below would wrongly load VarOperand(Name) =
        Name(%rip).  The capture slot holds the enclosing var's address; a
        captured VAR/OUT param's enclosing slot in turn holds the caller's
        address, so deref once more before loading the value
        (BUG-20260720-capture-varparam). }
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand('_cap_' + TIdentExpr(AExpr).Name)]));
      if TIdentExpr(AExpr).ParamMode <> pmNone then
        Self.Emit(#9'movq (%rcx), %rcx');
      Self.EmitLoadVar('(%rcx)', Self.IntExprType(AExpr));
    end
    else if TIdentExpr(AExpr).ParamMode <> pmNone then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand(TIdentExpr(AExpr).Name)]));
      Self.EmitLoadVar('(%rcx)', Self.IntExprType(AExpr));
    end
    else if (TIdentExpr(AExpr).ResolvedType <> nil) and
            (TIdentExpr(AExpr).ResolvedType.Kind = tyInterface) then
    begin
      { Interface ident used as a single value (nil/identity compare): load
        the obj half of the fat pointer.  An sret Result slot holds a POINTER
        to the caller's 16-byte buffer — dereference it; locals keep obj at
        the slot base and globals use the _obj data label (a bare global
        symbol load would reference a label that does not exist). }
      if FSretFunc and SameText(TIdentExpr(AExpr).Name, 'Result') then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]));
        Self.Emit(#9'movq (%rcx), %rax');
      end
      else
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.IntfObjOperand(TIdentExpr(AExpr).Name,
              TIdentExpr(AExpr).IsGlobal)]));
    end
    else
      Self.EmitLoadVar(Self.VarOperand(TIdentExpr(AExpr).Name),
        Self.IntExprType(AExpr));
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    { MethodAddress(Instance, 'MethodName') — runtime method table lookup.
      The method name string blob (__cn_Name) must exist in the data section;
      the class section emits it for published methods.  Just reference it here
      via a forward label without re-emitting the blob. }
    if SameText(FC.Name, 'MethodAddress') and (FC.Args.Count = 2) then
    begin
      { Arg0: class instance → class pointer in %rdi }
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'pushq %rdi');
      { Arg1: string data pointer for method name.  Literals reference the
        __cn_ blob directly; variable/call expressions evaluate to a managed
        string whose value is already the data pointer. }
      if TASTExpr(FC.Args.Items[1]) is TStringLiteral then
        Self.Emit(Format(#9'leaq __cn_%s + 12(%%rip), %%rsi',
          [NativeMangle(TStringLiteral(TASTExpr(FC.Args.Items[1])).Value)]))
      else
      begin
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
        Self.Emit(#9'movq %rax, %rsi');
      end;
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _MethodAddress');
      { Result = method code pointer in %rax. }
      Exit;
    end;
    { HasClassAttribute(AClass, AAttrClass): Boolean — query attribute RTTI.
      Both args are metaclass expressions that lower to typeinfo pointers.
      Pass them in %rdi/%rsi and call the runtime helper (result in %al).
      Without this the native backend never emitted the call — the result
      was the low byte of the first metaclass's typeinfo address, a layout-
      dependent false positive. }
    if FC.IsBuiltinHasClassAttr and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));   { ti_class -> %rax }
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));   { ti_attr  -> %rax }
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _HasClassAttribute');
      { Result Boolean in %al; normalise to a clean 0/1 in %rax. }
      Self.Emit(#9'movzbq %al, %rax');
      Exit;
    end;
    { Attribute-RTTI builtins (GetClassAttribute, HasMethodAttribute,
      GetMethodAttribute, MethodAttributeCount, GetMethodAttributeAt) —
      args in %rdi/%rsi/%rdx, call the same-named runtime helper prefixed
      '_'.  Get* return the attribute instance pointer in %rax;
      HasMethodAttribute returns Boolean in %al (normalised);
      MethodAttributeCount returns Integer in %eax (sign-extended). }
    if FC.AttrRTTIBuiltin <> '' then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      if FC.Args.Count = 3 then
      begin
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
        Self.Emit(#9'movq %rax, %rdx');
        Self.Emit(#9'popq %rsi');
      end
      else
        Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _' + FC.AttrRTTIBuiltin);
      if SameText(FC.AttrRTTIBuiltin, 'HasMethodAttribute') then
        Self.Emit(#9'movzbq %al, %rax')
      else if SameText(FC.AttrRTTIBuiltin, 'MethodAttributeCount') then
        Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    { SizeOf(expr) → integer literal = byte size of the resolved type. }
    if SameText(FC.Name, 'SizeOf') and (FC.Args.Count = 1) then
    begin
      Self.Emit(Format(#9'movq $%d, %%rax',
        [TASTExpr(FC.Args.Items[0]).ResolvedType.ByteSize()]));
      Exit;
    end;
    { Length/High/Low built-ins for arrays and strings. }
    if SameText(FC.Name, 'High') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      { High(subrange) is the subrange's own HIGH bound, not the base type's
        max — the descriptor's Kind is the narrowest fitting int but SubrangeHigh
        carries the real bound (GH #160). }
      if TASTExpr(FC.Args.Items[0]).ResolvedType.IsSubrange then
      begin
        Self.EmitImmToReg(TASTExpr(FC.Args.Items[0]).ResolvedType.SubrangeHigh,
          '%rax', '%eax');
        Exit;
      end;
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound]));
        tyOpenArray:
        begin
          { Load the _high slot for this open-array param. }
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(FC.Args.Items[0]).Name + '_high')]));
        end;
        tyDynArray:
        begin
          { High(A) = Length(A) - 1; delegate to RTL. }
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');
        end;
        tyString:
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _StringLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');
        end;
      else
        { Integer/enum types: type-level High (max).  EmitImmToReg picks the
          correct encoding — movl for values that zero-extend, movq for
          sign-extended imm32, movabsq for true 64-bit values.  A raw
          'movq $4294967295' would sign-extend the imm32 to -1, so UInt32
          MUST go through the helper too (GH #176). }
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyByte:     Self.EmitImmToReg(255, '%rax', '%eax');
          tyBoolean:  Self.EmitImmToReg(1, '%rax', '%eax');
          tySmallInt: Self.EmitImmToReg(32767, '%rax', '%eax');
          tyWord:     Self.EmitImmToReg(65535, '%rax', '%eax');
          tyInteger:  Self.EmitImmToReg(2147483647, '%rax', '%eax');
          tyUInt32:   Self.EmitImmToReg(4294967295, '%rax', '%eax');
          tyInt64:    Self.EmitImmToReg(9223372036854775807, '%rax', '%eax');
          { High(UInt64) = 18446744073709551615, i.e. all-ones — the -1
            Int64 bit pattern; movabsq $-1 materialises it exactly. }
          tyUInt64:   Self.Emit(#9'movabsq $-1, %rax');
          { High(enum) is the MAX stored ordinal, not member-count-1 — an
            explicit-ordinal enum is not contiguous 0-based
            (BUG-20260720-enum-explicit-ordinal-highlow). }
          tyEnum:     Self.EmitImmToReg(
            TEnumTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).MaxOrdinal(),
            '%rax', '%eax');
        else
          Self.Emit(#9'movq $0, %rax');
        end;
      end;
      Exit;
    end;

    if SameText(FC.Name, 'Low') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      { Low(subrange) is the subrange's own LOW bound (may be negative), not the
        base type's minimum (GH #160). }
      if TASTExpr(FC.Args.Items[0]).ResolvedType.IsSubrange then
      begin
        Self.EmitImmToReg(TASTExpr(FC.Args.Items[0]).ResolvedType.SubrangeLow,
          '%rax', '%eax');
        Exit;
      end;
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
          Self.EmitImmToReg(
            TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound,
            '%rax', '%eax');
        { Low(enum) is the MIN stored ordinal (may be negative), not 0
          (BUG-20260720-enum-explicit-ordinal-highlow). }
        tyEnum:
          Self.EmitImmToReg(
            TEnumTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).MinOrdinal(),
            '%rax', '%eax');
        tySmallInt: Self.Emit(#9'movq $-32768, %rax');
        tyInteger:  Self.Emit(#9'movq $-2147483648, %rax');
        { Low(Int64) = -9223372036854775808, the Int64 minimum — a true
          64-bit value that needs movabsq (GH #176).  Spelled as the literal
          (not Low(Int64)) so the fold is stable across self-hosting stages —
          the stage-1 binary predates this fix and would fold Low(Int64) to 0. }
        tyInt64:    Self.Emit(#9'movabsq $-9223372036854775808, %rax');
      else
        Self.Emit(#9'movq $0, %rax');  { 0 for all array/byte/bool/word/unsigned/open/dyn }
      end;
      Exit;
    end;

    if SameText(FC.Name, 'Length') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
        begin
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound + 1]));
        end;
        tyOpenArray:
        begin
          { Length = High + 1: load _high slot and add 1. }
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(FC.Args.Items[0]).Name + '_high')]));
          Self.Emit(#9'incq %rax');
        end;
        tyDynArray:
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
        end;
      else
        { String: delegate to RTL. }
        Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StringLength');
        Self.Emit(#9'movslq %eax, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'Pos') and (FC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(FC.Args.Items[0]),
        TASTExpr(FC.Args.Items[1]), '_StringPos');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Copy') and (FC.Args.Count = 3) then
    begin
      if ArcBuiltinStrArgOwnsRef(TASTExpr(FC.Args.Items[0])) then
      begin
        { Owned (+1) source transient — Copy(GetStr(), ..): park it in a
          16-byte slot pair and release it after the call (result preserved). }
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
        Self.Emit(#9'subq $16, %rsp');
        Self.Emit(#9'movq %rax, (%rsp)');
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
        Self.Emit(#9'movl %eax, %edx');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movl %eax, %esi');
        Self.Emit(#9'popq %rdi');
        Self.Emit(#9'callq _StringCopy');
        Self.Emit(#9'movq %rax, 8(%rsp)');
        Self.EmitStrDisposeFromSlot(TASTExpr(FC.Args.Items[0]), '(%rsp)');
        Self.Emit(#9'movq 8(%rsp), %rax');
        Self.Emit(#9'addq $16, %rsp');
        Exit;
      end;
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringCopy');
      Exit;
    end;
    if SameText(FC.Name, 'UpperCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StringUpperCase');
      Exit;
    end;
    if SameText(FC.Name, 'LowerCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StringLowerCase');
      Exit;
    end;
    if SameText(FC.Name, 'Trim') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StringTrim');
      Exit;
    end;
    { GetMem(N) → _BlaiseGetMem(N) → pointer.  Size arg is Integer (32-bit). }
    if SameText(FC.Name, 'GetMem') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _BlaiseGetMem');
      Exit;
    end;
    { ReallocMem(P, N) → _BlaiseReallocMem(P, N) → pointer. }
    if SameText(FC.Name, 'ReallocMem') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _BlaiseReallocMem');
      Exit;
    end;
    if SameText(FC.Name, 'SameText') and (FC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(FC.Args.Items[0]),
        TASTExpr(FC.Args.Items[1]), '_StringSameText');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Chr') and (FC.Args.Count = 1) then
    begin
      { Chr(N) returns a one-character heap String (tyString) — the data pointer
        of a freshly-allocated string.  Lower to _Chr(N), matching the QBE
        backend; the result (in %rax) is a String pointer, so it flows through
        the String ARC assignment/concat paths unchanged.  (Emitting the integer
        N here, as the missing case used to, fed a raw 66 into _StringAddRef and
        crashed.) }
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _Chr');
      Exit;
    end;
    if SameText(FC.Name, 'IntToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyInt64) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _Int64ToStr');
      end
      else if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
              (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyUInt64) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _UInt64ToStr');
      end
      else if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
              (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyUInt32) then
      begin
        { A Cardinal does not fit _IntToStr's signed Integer parameter —
          route to _Int64ToStr so a value >= 2^31 keeps its magnitude.
          %rax already holds the zero-extended value (32-bit loads/ops
          clear the upper 32 bits on x86-64). }
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _Int64ToStr');
      end
      else
      begin
        Self.Emit(#9'movl %eax, %edi');
        Self.Emit(#9'callq _IntToStr');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'StrToInt') and (FC.Args.Count = 1) then
    begin
      if Self.StrToIntChecked() then
        Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]),
          'SysUtils__StrToIntChecked')
      else
        Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StrToInt');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'StrToInt64') and (FC.Args.Count = 1) then
    begin
      if Self.StrToIntChecked() then
        Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]),
          'SysUtils__StrToInt64Checked')
      else
        Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StrToInt64');
      Exit;
    end;
    if SameText(FC.Name, 'PChar') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      { PChar(str) is identity — the Blaise string data pointer IS the char data. }
      Exit;
    end;
    if SameText(FC.Name, 'string') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringFromPChar');
      Exit;
    end;
    { Format(Fmt, Arg1, ...) — built-in that builds an args array and calls
      _StringFormatN; handled specially because it takes a variadic args list. }
    if SameText(FC.Name, 'Format') and (FC.Args.Count >= 1) then
    begin
      Self.EmitFormatCall(FC.Args);
      Exit;
    end;
    if SameText(FC.Name, 'Ord') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyString) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(#9'callq _OrdAt');
      end;
      Exit;
    end;
    if (SameText(FC.Name, 'Succ') or SameText(FC.Name, 'Pred')) and
       (FC.Args.Count = 1) then
    begin
      { Next/previous ordinal value: +1 / -1.  Result keeps the arg's type. }
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if SameText(FC.Name, 'Succ') then
        Self.Emit(#9'addl $1, %eax')
      else
        Self.Emit(#9'subl $1, %eax');
      Exit;
    end;
    if SameText(FC.Name, 'Assigned') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'testq %rax, %rax');
      Self.Emit(#9'setne %al');
      Self.Emit(#9'movzbl %al, %eax');
      Exit;
    end;
    if SameText(FC.Name, 'Int64ToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _Int64ToStr');
      Exit;
    end;
    if SameText(FC.Name, 'UInt64ToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _UInt64ToStr');
      Exit;
    end;
    if SameText(FC.Name, 'Abs') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind in [tyInt64, tyUInt64]) then
      begin
        Self.Emit(#9'cqto');
        Self.Emit(#9'xorq %rdx, %rax');
        Self.Emit(#9'subq %rdx, %rax');
      end
      else
      begin
        Self.Emit(#9'cltd');
        Self.Emit(#9'xorl %edx, %eax');
        Self.Emit(#9'subl %edx, %eax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'DoubleToStr') and (FC.Args.Count = 1) then
    begin
      { The argument expression may resolve to Single (e.g. a bare Single
        variable, or Sqrt(X)/Abs(X) where X: Single -- every float-unary
        builtin narrows its result back to the argument's own width).
        EmitExprToXmm0 then leaves a genuine 32-bit Single bit pattern in
        %xmm0; _DoubleToStr(V: Double) reads it via a movsd ABI, so it
        must be widened here. }
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      Self.EmitXmm0WidthAdjust(TASTExpr(FC.Args.Items[0]).ResolvedType, False);
      Self.Emit(#9'callq _DoubleToStr');
      Exit;
    end;
    if SameText(FC.Name, 'SingleToStr') and (FC.Args.Count = 1) then
    begin
      { Mirror of the DoubleToStr arm above: the argument expression may
        resolve to Double (e.g. Abs(D) where D: Double, or any other
        Double-typed sub-expression implicitly narrowed) -- narrow to
        Single here so _SingleToStr (movss ABI) always sees a genuine
        32-bit value, not a Double bit pattern. }
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      Self.EmitXmm0WidthAdjust(TASTExpr(FC.Args.Items[0]).ResolvedType, True);
      Self.Emit(#9'callq _SingleToStr');
      Exit;
    end;
    if SameText(FC.Name, 'StrToDouble') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_StrToDouble', True);
      Exit;
    end;
    if SameText(FC.Name, 'Round') and (FC.Args.Count = 1) then
    begin
      { Round half-away-from-zero, matching Delphi/FPC Round() and the QBE
        backend.  cvtsd2si/cvtss2si alone would honour the FPU rounding mode
        (round-half-to-even / banker's), which disagrees with QBE — so route
        through C99 round()/roundf() first, then truncate the integral result. }
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseRoundD');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end
      else
      begin
        Self.Emit(#9'callq _BlaiseRoundD');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'Trunc') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'cvttss2si %xmm0, %rax')
      else
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Abs') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       TASTExpr(FC.Args.Items[0]).ResolvedType.IsFloat() then
    begin
      { float Abs in the rax-value context -- see the float-emitter arm }
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseFabs');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseFabs');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Sqrt') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'sqrtss %xmm0, %xmm0')
      else
        Self.Emit(#9'sqrtsd %xmm0, %xmm0');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'CompareStr') and (FC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(FC.Args.Items[0]),
        TASTExpr(FC.Args.Items[1]), '_StringCompare');
      Exit;
    end;
    if SameText(FC.Name, 'CompareText') and (FC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(FC.Args.Items[0]),
        TASTExpr(FC.Args.Items[1]), '_StringCompareText');
      Exit;
    end;
    if SameText(FC.Name, 'PosEx') and (FC.Args.Count = 3) then
    begin
      if ArcBuiltinStrArgOwnsRef(TASTExpr(FC.Args.Items[0])) or
         ArcBuiltinStrArgOwnsRef(TASTExpr(FC.Args.Items[1])) then
      begin
        { Owned (+1) string transient(s) — slots: 0=sub, 8=s, 16=result. }
        Self.Emit(#9'subq $32, %rsp');
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
        Self.Emit(#9'movq %rax, (%rsp)');
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
        Self.Emit(#9'movq %rax, 8(%rsp)');
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
        Self.Emit(#9'movl %eax, %edx');
        Self.Emit(#9'movq (%rsp), %rdi');
        Self.Emit(#9'movq 8(%rsp), %rsi');
        Self.Emit(#9'callq _StringPosEx');
        Self.Emit(#9'movq %rax, 16(%rsp)');
        if ArcBuiltinStrArgOwnsRef(TASTExpr(FC.Args.Items[0])) then
          Self.EmitStrDisposeFromSlot(TASTExpr(FC.Args.Items[0]), '(%rsp)');
        if ArcBuiltinStrArgOwnsRef(TASTExpr(FC.Args.Items[1])) then
          Self.EmitStrDisposeFromSlot(TASTExpr(FC.Args.Items[1]), '8(%rsp)');
        Self.Emit(#9'movq 16(%rsp), %rax');
        Self.Emit(#9'addq $32, %rsp');
        Exit;
      end;
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringPosEx');
      Exit;
    end;
    if SameText(FC.Name, 'UpCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         TASTExpr(FC.Args.Items[0]).ResolvedType.IsString() then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(#9'callq _OrdAt');
      end;
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _UpCase');
      Exit;
    end;
    if SameText(FC.Name, 'ClassCreate') and (FC.Args.Count >= 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassCreate');
      { The constructor is a plain procedure (no Result) — it does NOT
        return Self in %rax.  Keep the _ClassCreate result in callee-saved
        %rbx across the ctor call, mirroring the direct constructor path. }
      if (FC.ResolvedDecl <> nil) and (FC.Args.Count > 1) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        for SetI := 1 to FC.Args.Count - 1 do
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[SetI]));
          Self.Emit(#9'pushq %rax');
        end;
        for SetI := FC.Args.Count - 1 downto 1 do
          Self.Emit(Format(#9'popq %s', [SysVArg64(SetI)]));
        Self.Emit(#9'movq %rbx, %rdi');
        if TMethodDecl(FC.ResolvedDecl).VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax',
            [(TMethodDecl(FC.ResolvedDecl).VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(Format(#9'callq %s',
            [MethodEmitNameNative(TMethodDecl(FC.ResolvedDecl),
              TMethodDecl(FC.ResolvedDecl).OwnerTypeName, 'Create')]));
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end
      else if FC.ResolvedDecl <> nil then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.Emit(#9'movq %rax, %rdi');
        if TMethodDecl(FC.ResolvedDecl).VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax',
            [(TMethodDecl(FC.ResolvedDecl).VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(Format(#9'callq %s',
            [MethodEmitNameNative(TMethodDecl(FC.ResolvedDecl),
              TMethodDecl(FC.ResolvedDecl).OwnerTypeName, 'Create')]));
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'OrdAt') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _OrdAt');
      Exit;
    end;
    if SameText(FC.Name, 'FileExists') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_FileExists');
      Exit;
    end;
    if SameText(FC.Name, 'DirectoryExists') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_DirectoryExists');
      Exit;
    end;
    if SameText(FC.Name, 'ReadFile') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_ReadFile');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFilePath') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_ExtractFilePath');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFileName') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_ExtractFileName');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFileDir') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_ExtractFileDir');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFileExt') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_ExtractFileExt');
      Exit;
    end;
    if SameText(FC.Name, 'ChangeFileExt') and (FC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(FC.Args.Items[0]),
        TASTExpr(FC.Args.Items[1]), '_ChangeFileExt');
      Exit;
    end;
    if SameText(FC.Name, 'ForceDirectories') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_ForceDirectories');
      Exit;
    end;
    if SameText(FC.Name, 'ExcludeTrailingPathDelimiter') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]),
        '_ExcludeTrailingPathDelimiter');
      Exit;
    end;
    if SameText(FC.Name, 'IncludeTrailingPathDelimiter') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]),
        '_IncludeTrailingPathDelimiter');
      Exit;
    end;
    if SameText(FC.Name, 'RenameFile') and (FC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(FC.Args.Items[0]),
        TASTExpr(FC.Args.Items[1]), '_RenameFile');
      Exit;
    end;
    if SameText(FC.Name, 'SetCurrentDir') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_SetCurrentDir');
      Exit;
    end;
    if SameText(FC.Name, 'GetCurrentDir') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _GetCurrentDir');
      Exit;
    end;
    if SameText(FC.Name, 'ParamStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _ParamStr');
      Exit;
    end;
    if SameText(FC.Name, 'ParamCount') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _ParamCount');
      Exit;
    end;
    if (SameText(FC.Name, 'GetEnvVar') or SameText(FC.Name, 'GetEnvironmentVariable'))
       and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_GetEnvVar');
      Exit;
    end;
    if SameText(FC.Name, 'GetProcessID') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _GetProcessID');
      Exit;
    end;
    if SameText(FC.Name, 'GetTempDir') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _GetTempDir');
      Exit;
    end;
    if SameText(FC.Name, 'GetTempFileName') and (FC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(FC.Args.Items[0]),
        TASTExpr(FC.Args.Items[1]), '_GetTempFileName');
      Exit;
    end;
    if SameText(FC.Name, 'Exec') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_Exec');
      Exit;
    end;
    if SameText(FC.Name, 'CurrentExceptionMessage') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _CurrentExceptionMessage');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessCreate') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _ProcessCreate');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessRunning') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessRunning');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessReadOutput') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessReadOutput');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessExitCode') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessExitCode');
      Exit;
    end;
    if SameText(FC.Name, 'FileAge') and (FC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(FC.Args.Items[0]), '_FileAge');
      Exit;
    end;
    if SameText(FC.Name, 'Floor') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseFloorD');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end
      else
      begin
        Self.Emit(#9'callq _BlaiseFloorD');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'Ceil') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseCeilD');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end
      else
      begin
        Self.Emit(#9'callq _BlaiseCeilD');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'IsNaN') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq __isnanf')
      else
        Self.Emit(#9'callq __isnan');
      Exit;
    end;
    if SameText(FC.Name, 'IsInfinite') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq __isinff')
      else
        Self.Emit(#9'callq __isinf');
      Exit;
    end;
    if SameText(FC.Name, 'Sin') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseSin');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseSin');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Cos') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseCos');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseCos');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Tan') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseTan');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseTan');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcTan') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseArcTan');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseArcTan');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcTan2') and (FC.Args.Count = 2) then
    begin
      { each argument is widened to double by ITS OWN type (the old code
        keyed both on the first argument, mishandling mixed Single/Double
        pairs); the runtime.math function is double-only }
      IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
             (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if IsS then
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
      if (TASTExpr(FC.Args.Items[1]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[1]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'movaps %xmm0, %xmm1');
      Self.Emit(#9'movsd (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'callq _BlaiseArcTan2');
      if IsS then
        { result type follows the first argument }
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcSin') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseArcSin');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseArcSin');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcCos') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseArcCos');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseArcCos');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Ln') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseLn');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseLn');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Log2') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseLog2');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseLog2');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Log10') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseLog10');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseLog10');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Power') and (FC.Args.Count = 2) then
    begin
      { each argument is widened to double by ITS OWN type (the old code
        keyed both on the first argument, mishandling mixed Single/Double
        pairs); the runtime.math function is double-only }
      IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
             (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if IsS then
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
      if (TASTExpr(FC.Args.Items[1]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[1]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
      Self.Emit(#9'movaps %xmm0, %xmm1');
      Self.Emit(#9'movsd (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'callq _BlaisePow');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Sinh') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseSinh');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseSinh');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Cosh') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseCosh');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseCosh');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Tanh') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
        Self.Emit(#9'callq _BlaiseTanh');
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
        Self.Emit(#9'callq _BlaiseTanh');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    { Unqualified call to a procedural-typed field of the current class
      (implicit Self.Field) used as an expression. }
    if FC.IsProcFieldCall then
    begin
      Self.EmitProcFieldCall(nil, 'Self', False, FC.ProcFieldInfo,
        TProceduralTypeDesc(FC.ResolvedProcType), FC.Args, FC.ResolvedType);
      Exit;
    end;
    if FC.IsIndirectCall then
    begin
      { Bare function-pointer call: load the pointer from the variable slot
        and dispatch via callq *%r10.  Method pointers (of object) and
        'reference to' closures carry a 16-byte block — Data (Self / env)
        must be loaded from +8 and the user args shifted right, exactly as
        in the statement path. }
      if (FC.ResolvedProcType <> nil) and
         (TProceduralTypeDesc(FC.ResolvedProcType).IsMethodPtr or
          TProceduralTypeDesc(FC.ResolvedProcType).IsReference) then
        Self.EmitMethodPtrCall(
          Self.VarOperand(FC.Name),
          TProceduralTypeDesc(FC.ResolvedProcType),
          FC.Args)
      else
        Self.EmitCallIndirect(
          Self.VarOperand(FC.Name),   { local slot or global RIP-relative }
          TProceduralTypeDesc(FC.ResolvedProcType),
          FC.Args);
      { Normalise the return value width. }
      if FC.ResolvedType <> nil then
        Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    { Type cast TypeName(Expr): ResolvedDecl is nil.  Evaluate the operand,
      then truncate/extend to the target integer-family type.  Mirrors the QBE
      backend's cast lowering. }
    if FC.ResolvedDecl = nil then
    begin
      CastArg := TASTExpr(FC.Args.Items[0]);
      if (CastArg.ResolvedType <> nil) and
         (CastArg.ResolvedType.Kind = tyInterface) and
         (CastArg is TIdentExpr) then
      begin
        { Interface ident operand — five slot layouts, mirroring
          PushIntfIdentPair (BUG-20260722-native-downcast-intf-nonslot-shapes):
          sret Result (slot holds the caller-buffer ADDRESS), captured local
          (the _cap_ slot holds the fat pair's address), implicit-Self FIELD
          (contiguous fat pair at Self+offset — the plain-ident load would
          reference a nonexistent <name>_obj global), var/out param (the slot
          holds the ADDRESS of the caller's fat pair), and the plain
          local/global split _obj/_itab slots. }
        if FSretFunc and SameText(TIdentExpr(CastArg).Name, 'Result') then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Result')]));
          Self.Emit(#9'movq (%rax), %rax');
        end
        else if Self.IsCaptured(TIdentExpr(CastArg).Name) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand('_cap_' + TIdentExpr(CastArg).Name)]));
          Self.Emit(#9'movq (%rax), %rax');
        end
        else if TIdentExpr(CastArg).IsImplicitSelf and
           (TIdentExpr(CastArg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          Self.Emit(Format(#9'movq %d(%%rax), %%rax',
            [TFieldInfo(TIdentExpr(CastArg).ImplicitFieldInfo).Offset]));
        end
        else if TIdentExpr(CastArg).ParamMode = pmVar then
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(CastArg).Name)]));
          Self.Emit(#9'movq (%rax), %rax');
        end
        else
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(CastArg).Name,
                                 TIdentExpr(CastArg).IsGlobal)]));
      end
      else if (CastArg.ResolvedType <> nil) and
              (CastArg.ResolvedType.Kind = tyInterface) and
              (CastArg is TFuncCallExpr) and
              (TFuncCallExpr(CastArg).ResolvedDecl <> nil) then
      begin
        { Interface-returning CALL operand: EmitIntfSretCall leaves the
          16-byte fat pair at (%rsp).  The callee transferred a +1 obj
          reference; defer its release to the statement boundary so the
          cast result stays alive for the consuming expression (falls back
          to a leak, never a use-after-free, if all pendrel slots are
          taken). }
        Self.EmitIntfSretCall(TFuncCallExpr(CastArg));
        Self.Emit(#9'movq (%rsp), %rax');
        Self.Emit(#9'addq $16, %rsp');
        Self.DeferNativeClassRelease();
      end
      else if (CastArg.ResolvedType <> nil) and
              (CastArg.ResolvedType.Kind = tyInterface) and
              (CastArg is TMethodCallExpr) and
              (TMethodCallExpr(CastArg).ResolvedClassType <> nil) then
      begin
        { Interface-returning METHOD-call operand (TG(Obj.GetI())): same sret
          contract and same deferred obj release as the plain-call arm above.
          Which sret helper applies depends on the RECEIVER: an interface
          receiver dispatches through the itab, a class receiver is a direct
          or vtable call. }
        if TMethodCallExpr(CastArg).ResolvedClassType.Kind = tyInterface then
          Self.EmitIntfSretMethodCall(TMethodCallExpr(CastArg))
        else
          Self.EmitClassIntfSretMethodCall(TMethodCallExpr(CastArg));
        Self.Emit(#9'movq (%rsp), %rax');
        Self.Emit(#9'addq $16, %rsp');
        Self.DeferNativeClassRelease();
      end
      else if (CastArg.ResolvedType <> nil) and
              (CastArg.ResolvedType.Kind = tyInterface) and
              (CastArg is TFieldAccessExpr) then
      begin
        { Interface FIELD operand (TG(H.FIntf)) or array-field ELEMENT
          (TG(H.FArr[0]), IsArrayAccess): resolve the fat pair's address and
          load the obj half.  The generic EmitExprToEax below returns the
          element ADDRESS for an IsArrayAccess interface element
          (BUG-20260721-fieldaccess-intf-array-elem-read), which the cast
          would then treat as the obj pointer. }
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(CastArg), '%rax');
        Self.Emit(#9'movq (%rax), %rax');
      end
      else
        Self.EmitExprToEax(CastArg);
      Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    { A jumbo-set return uses the same hidden-sret convention as a record
      (BuildFrame sets FSretFunc for it).  Without this the call site emitted a
      plain call and read %eax as if the bitmap were a scalar, so an operand
      like `MakeSet() + [x]` dereferenced a truncated garbage address. }
    if (FC.ResolvedType <> nil) and
       ((FC.ResolvedType.Kind = tyRecord) or IsJumboSet(FC.ResolvedType)) and
       (TMethodDecl(FC.ResolvedDecl).ResolvedReturnType <> nil) and
       ((TMethodDecl(FC.ResolvedDecl).ResolvedReturnType.Kind = tyRecord) or
        IsJumboSet(TMethodDecl(FC.ResolvedDecl).ResolvedReturnType)) then
    begin
      MD := TMethodDecl(FC.ResolvedDecl);
      Self.Emit(Format(#9'subq $%d, %%rsp',
        [(SretRetSize(MD.ResolvedReturnType) + 15) and (-16)]));
      if FC.IsImplicitSelfMethod then
      begin
        Self.Emit(#9'leaq (%rsp), %r10');
        Self.Emit(#9'movq %r10, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(Format(#9'movq $%d, %%rdx',
          [SretRetSize(MD.ResolvedReturnType)]));
        Self.Emit(#9'callq memset');
        Self.Emit(#9'leaq (%rsp), %r10');
        Self.BeginCallArgs(MD.Params, FC.Args);
        for I := 0 to FC.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(FC.Args.Items[I]), I);
        Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('Self')]));
        Self.EmitPopMethodArgsToRegs(MD.Params, FC.Args, 2);
        Self.Emit(#9'movq %r11, %rsi');
        Self.Emit(#9'movq %r10, %rdi');
        { Virtual record-sret implicit-Self call dispatches via the vtable
          (Self in %rsi, sret buffer in %rdi). }
        Self.EmitSelfDispatchVia(MD, FuncSymbolOf(FC), '%rsi');
        Self.EndCallArgs();
      end
      else
        Self.EmitSretCall(FuncSymbolOf(FC), MD, FC.Args, '(%rsp)', False);
      Self.Emit(#9'leaq (%rsp), %rax');
      Exit;
    end;
    if FC.IsImplicitSelfMethod then
    begin
      MD := TMethodDecl(FC.ResolvedDecl);
      { Register slots = Self (%rdi) + the arg slots.  When they fit in the six
        integer registers, use the push/pop-into-registers fast path; otherwise
        spill the overflow to the stack per the SysV ABI. }
      if Self.CountArgSlots(MD.Params) + 1 <= 6 then
      begin
        Self.BeginCallArgs(MD.Params, FC.Args);
        for I := 0 to FC.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(FC.Args.Items[I]), I);
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
        Self.EmitPopMethodArgsToRegs(MD.Params, FC.Args, 1);
        Self.Emit(#9'movq %r10, %rdi');
        { Implicit-Self call to a virtual method must dispatch through the vtable
          (Self may be a more-derived instance), exactly as Self.Method() does;
          a static callq would bind to the declaring class and break
          polymorphism (and link-fail for an abstract base). }
        Self.EmitSelfDispatch(MD, FuncSymbolOf(FC));
        Self.EndCallArgs();
      end
      else
        Self.EmitImplicitSelfCallOverflow(MD, FC.Args, FuncSymbolOf(FC));
      if FC.ResolvedType <> nil then
        Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    if Self.TryEmitInlineCall(FC.ResolvedDecl, FC.Args, True) then
    begin
      if FC.ResolvedType <> nil then
        Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    Self.EmitCall(FuncSymbolOf(FC), TMethodDecl(FC.ResolvedDecl), FC.Args);
    { Normalise the (32-bit-ABI) return value to the callee's return width so
      it is correctly extended in %rax before entering further arithmetic. }
    if FC.ResolvedType <> nil then
      Self.EmitNarrowToType(FC.ResolvedType);
    Exit;
  end;

  { Operator overloading: uSemantic normally REBINDS the owning slot to the
    synthesised call (AnalyseExprSlot), so a lowered operator reaches codegen
    as a plain TMethodCallExpr and every record/sret/ARC node-class test
    matches.  This guard is the belt-and-braces path for any slot not yet
    converted to the slot form — delegate to the general emitter rather than
    re-implementing the call here. }
  if (AExpr is TBinaryExpr) and (TBinaryExpr(AExpr).LoweredCall <> nil) then
  begin
    Self.EmitExprToEax(TBinaryExpr(AExpr).LoweredCall);
    Exit;
  end;
  if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr(AExpr);
    { Float comparison evaluated for its boolean value (0/1 in %rax).
      EmitCondBranch handles float comparisons that are themselves the
      branch condition, but when a float comparison is a sub-expression —
      nested in `and`/`or`, assigned to a Boolean, or passed as an
      argument — it reaches EmitExprToEax and must materialise the
      result.  The integer comparison path below cannot, because its
      operand emission (EmitExprToEax) has no TFloatLiteral handler. }
    if (BE.Op in [boEQ, boNE, boLT, boGT, boLE, boGE]) and
       (IsFloatFamily(BE.Left.ResolvedType) or
        IsFloatFamily(BE.Right.ResolvedType)) then
    begin
      IsS := (BE.Left.ResolvedType <> nil) and (BE.Left.ResolvedType.Kind = tySingle) and
             (BE.Right.ResolvedType <> nil) and (BE.Right.ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(BE.Left);
      Self.EmitXmm0WidthAdjust(BE.Left.ResolvedType, IsS);
      Self.Emit(#9'subq $8, %rsp');
      if IsS then Self.Emit(#9'movss %xmm0, (%rsp)')
      else        Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(BE.Right);
      Self.EmitXmm0WidthAdjust(BE.Right.ResolvedType, IsS);
      if IsS then
      begin
        Self.Emit(#9'movss (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomiss %xmm0, %xmm1');
      end
      else
      begin
        Self.Emit(#9'movsd (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomisd %xmm0, %xmm1');
      end;
      case BE.Op of
        boEQ: Self.Emit(#9'sete %al');
        boNE: Self.Emit(#9'setne %al');
        boLT: Self.Emit(#9'setb %al');   { below (CF set) }
        boGT: Self.Emit(#9'seta %al');   { above }
        boLE: Self.Emit(#9'setbe %al');
        boGE: Self.Emit(#9'setae %al');
      end;
      Self.Emit(#9'movzbl %al, %eax');
      Exit;
    end;
    { String concatenation (boAdd on tyString): call _StringConcat(left, right).
      Transient operands must be disposed after the concat or every nested
      concat / call operand leaks its buffer: an rc=1 user-call result takes
      one release, an rc=0 built-in/concat result takes addref+release (see
      EmitStrDisposeFromSlot).  Borrowed operands (locals, fields, literals)
      take nothing — the fast path below keeps them at the plain sequence. }
    if (BE.Op = boAdd) and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyString) then
    begin
      if ArcBuiltinStrArgOwnsRef(BE.Left) or ArcBuiltinStrArgOwnsRef(BE.Right) then
      begin
        { Slots: 0 = left, 8 = right, 16 = result, 24 = pad. }
        Self.Emit(#9'subq $32, %rsp');
        Self.EmitExprToEax(BE.Left);
        Self.Emit(#9'movq %rax, (%rsp)');
        Self.EmitExprToEax(BE.Right);
        Self.Emit(#9'movq %rax, 8(%rsp)');
        Self.Emit(#9'movq (%rsp), %rdi');
        Self.Emit(#9'movq 8(%rsp), %rsi');
        Self.Emit(#9'callq _StringConcat');
        Self.Emit(#9'movq %rax, 16(%rsp)');
        if ArcBuiltinStrArgOwnsRef(BE.Left) then
          Self.EmitStrDisposeFromSlot(BE.Left, '(%rsp)');
        if ArcBuiltinStrArgOwnsRef(BE.Right) then
          Self.EmitStrDisposeFromSlot(BE.Right, '8(%rsp)');
        Self.Emit(#9'movq 16(%rsp), %rax');
        Self.Emit(#9'addq $32, %rsp');
        Exit;
      end;
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringConcat');
      Exit;
    end;
    { String equality/inequality: content comparison via _StringEquals. }
    if (BE.Op in [boEQ, boNE]) and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyString) then
    begin
      Self.EmitBuiltinStrCall2(BE.Left, BE.Right, '_StringEquals');
      if BE.Op = boNE then
        Self.Emit(#9'xorl $1, %eax');
      Exit;
    end;
    { String relational order via _StringCompare (strcmp-like: <0 / 0 / >0).
      Compare the result against 0 with the matching signed condition.  Without
      this, string < > <= >= fell through to the integer comparison path, which
      compared the string POINTERS (wrong answer). }
    if (BE.Op in [boLT, boGT, boLE, boGE]) and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyString) then
    begin
      Self.EmitBuiltinStrCall2(BE.Left, BE.Right, '_StringCompare');
      Self.Emit(#9'cmpl $0, %eax');
      case BE.Op of
        boLT: Self.Emit(#9'setl %al');
        boGT: Self.Emit(#9'setg %al');
        boLE: Self.Emit(#9'setle %al');
        boGE: Self.Emit(#9'setge %al');
      end;
      Self.Emit(#9'movzbl %al, %eax');
      Exit;
    end;
    { Set membership: elem in SetVar — (set >> ord(elem)) & 1 }
    if (BE.Op = boIn) and
       (BE.Right.ResolvedType <> nil) and
       (BE.Right.ResolvedType.Kind = tySet) then
    begin
      if IsJumboSet(BE.Right.ResolvedType) then
      begin
        { Jumbo: evaluate ordinal, save it, get the set's bitmap address, then
          _SetIn(rdi=set, esi=ord). }
        Self.EmitExprToEax(BE.Left);
        Self.Emit(#9'pushq %rax');           { ordinal }
        Self.EmitExprToEax(BE.Right);        { set bitmap addr -> %rax }
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'popq %rsi');
        Self.Emit(#9'callq _SetIn');
        Exit;
      end;
      { Evaluate the ordinal and SAVE IT ON THE STACK, not in %ecx: the RHS set
        expression may itself be an array-element field access whose address
        computation clobbers %rcx (index scaling), which would destroy the
        ordinal before the shift.  Push/pop keeps it live across the RHS eval —
        the same discipline the jumbo path above already uses. }
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');            { ordinal saved }
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'popq %rcx');             { ordinal -> %rcx (and %cl) }
      if TSetTypeDesc(BE.Right.ResolvedType).BitCount > 32 then
      begin
        Self.Emit(#9'shrq %cl, %rax');
        Self.Emit(#9'andq $1, %rax');
      end
      else
      begin
        Self.Emit(#9'shrl %cl, %eax');
        Self.Emit(#9'andl $1, %eax');
      end;
      { Range guard: force 0 when the ordinal is >= the set width.  The set may
        be sized to a literal's max ordinal (X in [low members]) while the
        tested element's ordinal is larger; x86 shift counts wrap mod 32/64, so
        the raw shift result for an out-of-range ordinal is meaningless and
        must be masked out.  %edx = (ord < BitCount) ? 1 : 0. }
      Self.Emit(Format(#9'cmpl $%d, %%ecx',
        [TSetTypeDesc(BE.Right.ResolvedType).BitCount]));
      Self.Emit(#9'setl %dl');
      Self.Emit(#9'movzbl %dl, %edx');
      Self.Emit(#9'andl %edx, %eax');
      Exit;
    end;
    { Set arithmetic: union (+), difference (-), intersection (*), equality. }
    if (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tySet) and
       (BE.Op in [boAdd, boSub, boMul, boEQ, boNE, boLE, boGE]) then
    begin
      if IsJumboSet(BE.Left.ResolvedType) then
      begin
        { Equality compares two bitmap addresses via _SetEqual. }
        if BE.Op in [boEQ, boNE] then
        begin
          Self.EmitExprToEax(BE.Left);
          Self.Emit(#9'pushq %rax');
          Self.EmitExprToEax(BE.Right);
          Self.Emit(#9'movq %rax, %rsi');
          Self.Emit(#9'popq %rdi');
          Self.Emit(Format(#9'movl $%d, %%edx',
            [JumboSetNBytes(BE.Left.ResolvedType)]));
          Self.Emit(#9'callq _SetEqual');
          if BE.Op = boNE then
            Self.Emit(#9'xorl $1, %eax');
          Exit;
        end;
        { Subset (<=) / superset (>=): _SetSubset(A, B) tests A subset of B.
          For >= the operands are swapped (B subset of A). }
        if BE.Op in [boLE, boGE] then
        begin
          Self.EmitExprToEax(BE.Left);
          Self.Emit(#9'pushq %rax');
          Self.EmitExprToEax(BE.Right);
          if BE.Op = boLE then
          begin
            Self.Emit(#9'movq %rax, %rsi');   { B }
            Self.Emit(#9'popq %rdi');         { A }
          end
          else
          begin
            Self.Emit(#9'movq %rax, %rdi');   { B -> A-arg }
            Self.Emit(#9'popq %rsi');         { A -> B-arg }
          end;
          Self.Emit(Format(#9'movl $%d, %%edx',
            [JumboSetNBytes(BE.Left.ResolvedType)]));
          Self.Emit(#9'callq _SetSubset');
          Exit;
        end;
        { Union/intersection/difference: write the result into a frame scratch
          slot and return its address.  The _Set helper takes rdi=dest,
          rsi=A, rdx=B, ecx=nbytes. %r12/%r13 are callee-saved across the two
          operand evaluations and the helper call. }
        Self.EmitExprToEax(BE.Left);
        Self.Emit(#9'pushq %r12');
        Self.Emit(#9'pushq %r13');
        Self.Emit(#9'movq %rax, %r12');         { A addr }
        Self.EmitExprToEax(BE.Right);
        Self.Emit(#9'movq %rax, %r13');         { B addr }
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand('_jset_scratch_0')]));
        Self.Emit(#9'movq %r12, %rsi');
        Self.Emit(#9'movq %r13, %rdx');
        Self.Emit(Format(#9'movl $%d, %%ecx', [JumboSetNBytes(BE.Left.ResolvedType)]));
        case BE.Op of
          boAdd: Self.Emit(#9'callq _SetUnion');
          boMul: Self.Emit(#9'callq _SetInter');
          boSub: Self.Emit(#9'callq _SetDiff');
        end;
        Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand('_jset_scratch_0')]));
        Self.Emit(#9'popq %r13');
        Self.Emit(#9'popq %r12');
        Exit;
      end;
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'popq %rax');
      case BE.Op of
        boAdd: Self.Emit(#9'orq %rcx, %rax');
        boSub:
        begin
          Self.Emit(#9'notq %rcx');
          Self.Emit(#9'andq %rcx, %rax');
        end;
        boMul: Self.Emit(#9'andq %rcx, %rax');
        boEQ, boNE:
        begin
          Self.Emit(#9'cmpq %rcx, %rax');
          if BE.Op = boEQ then
            Self.Emit(#9'sete %al')
          else
            Self.Emit(#9'setne %al');
          Self.Emit(#9'movzbl %al, %eax');
        end;
        boLE, boGE:
        begin
          { subset s<=t: (s and not t)=0 ; superset s>=t: (t and not s)=0.
            %rax=s (left), %rcx=t (right).  For <= mask = s and not t; for >=
            mask = t and not s.  Then test the mask is zero. }
          if BE.Op = boLE then
          begin
            Self.Emit(#9'notq %rcx');        { ~t }
            Self.Emit(#9'andq %rcx, %rax');  { s and ~t }
          end
          else
          begin
            Self.Emit(#9'notq %rax');        { ~s }
            Self.Emit(#9'andq %rcx, %rax');  { t and ~s }
          end;
          Self.Emit(#9'testq %rax, %rax');
          Self.Emit(#9'sete %al');
          Self.Emit(#9'movzbl %al, %eax');
        end;
      end;
      Exit;
    end;
    { Short-circuit boolean and/or: evaluate LHS; skip RHS when the result
      is already determined.  For `and`, LHS=0 means result=0 (skip).
      For `or`, LHS<>0 means result=1 (skip).  When we don't skip, RHS
      is evaluated and its 0/1 value becomes the final result in %eax. }
    if ((BE.Op = boAnd) or (BE.Op = boOr)) and
       ((BE.ResolvedType = nil) or not BE.ResolvedType.IsNumeric()) then
    begin
      ScEndLbl := Self.NewLabel('sc_end');
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'testl %eax, %eax');
      if BE.Op = boAnd then
        Self.Emit(#9'jz ' + ScEndLbl)
      else
        Self.Emit(#9'jnz ' + ScEndLbl);
      Self.EmitExprToEax(BE.Right);
      Self.Emit(ScEndLbl + ':');
      Exit;
    end;
    { left -> %rax.  A compile-time RHS folds into the instruction's
      immediate field; a trivial RHS (plain scalar local/param/global)
      loads straight into %rcx.  Only a complex RHS — one whose evaluation
      may clobber %rax — needs the push/pop save bracket. }
    Self.EmitExprToEax(BE.Left);
    { An interface element of an ARRAY FIELD (H.FArr[0], IsArrayAccess)
      evaluates to its element ADDRESS, like records
      (BUG-20260721-fieldaccess-intf-array-elem-read).  A comparison operand
      needs the obj half — load it. }
    if (BE.Left is TFieldAccessExpr) and
       TFieldAccessExpr(BE.Left).IsArrayAccess and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyInterface) then
      Self.Emit(#9'movq (%rax), %rax');
    HasImm := Self.TryGetImmValue(BE.Right, ImmV) and
              (ImmV >= -2147483648) and (ImmV <= 2147483647) and
              (BE.Op in [boAdd, boSub, boMul, boAnd, boOr, boXor,
                         boShl, boShr, boSar,
                         boEQ, boNE, boLT, boGT, boLE, boGE]);
    if (not HasImm) and (not Self.TryEmitOperandToRcx(BE.Right)) then
    begin
      if FPromoActive and FPromoPinOk and (FPinDepth = 0) then
      begin
        { Pin the LHS in callee-saved %r13 across the complex RHS
          (typically a call): no stack round-trip, and the call site
          stays 16-byte aligned (no wrap pad).  Only the outermost
          bracket pins; nested brackets keep push/pop. }
        FPinDepth := FPinDepth + 1;
        Self.Emit(#9'movq %rax, %r13');
        Self.EmitExprToEax(BE.Right);
        if (BE.Right is TFieldAccessExpr) and
           TFieldAccessExpr(BE.Right).IsArrayAccess and
           (BE.Right.ResolvedType <> nil) and
           (BE.Right.ResolvedType.Kind = tyInterface) then
          Self.Emit(#9'movq (%rax), %rax'); { element addr -> obj half }
        Self.Emit(#9'movq %rax, %rcx');   { right in %rcx }
        Self.Emit(#9'movq %r13, %rax');   { left in %rax }
        FPinDepth := FPinDepth - 1;
      end
      else
      begin
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(BE.Right);
        if (BE.Right is TFieldAccessExpr) and
           TFieldAccessExpr(BE.Right).IsArrayAccess and
           (BE.Right.ResolvedType <> nil) and
           (BE.Right.ResolvedType.Kind = tyInterface) then
          Self.Emit(#9'movq (%rax), %rax'); { element addr -> obj half }
        Self.Emit(#9'movq %rax, %rcx');   { right in %rcx }
        Self.Emit(#9'popq %rax');          { left in %rax }
      end;
    end;
    case BE.Op of
      boAdd:
        if HasImm then
          Self.Emit(#9'addq $' + IntToStr(ImmV) + ', %rax')
        else
          Self.Emit(#9'addq %rcx, %rax');
      boSub:
        if HasImm then
          Self.Emit(#9'subq $' + IntToStr(ImmV) + ', %rax')
        else
          Self.Emit(#9'subq %rcx, %rax');
      boMul:
        if HasImm then
          Self.Emit(#9'imulq $' + IntToStr(ImmV) + ', %rax, %rax')
        else
          Self.Emit(#9'imulq %rcx, %rax');
      boDiv, boMod:
        begin
          { Divisor-zero guard: when SysUtils is in scope, a zero divisor
            raises a catchable EDivByZero instead of trapping (SIGFPE).
            The divisor is in %rcx; SysUtils__RaiseDivByZero longjmps and
            never returns. }
          if Self.DivGuardAvailable() then
          begin
            DivOkLbl := Self.NewLabel('divok');
            Self.Emit(#9'testq %rcx, %rcx');
            Self.Emit(#9'jne ' + DivOkLbl);
            Self.Emit(#9'callq SysUtils__RaiseDivByZero');
            Self.Emit(DivOkLbl + ':');
          end;
          { 64-bit divide.  Choose signed vs unsigned by the EXPRESSION's
            result type, matching the QBE backend (which keys udiv/urem off
            BinExpr.ResolvedType).  Requiring both operands to be unsigned
            was wrong: in `U div 16` with U: UInt64 the literal types as a
            signed integer, so the conjunction failed and idivq read a
            high-bit-set U as negative (GH #196).  The semantic pass already
            resolves such an expression to UInt64.  Fall back to the operand
            types only when the result type is unavailable.  cqto sign-extends
            %rax into %rdx:%rax; for unsigned we zero %rdx instead. }
          if BE.ResolvedType <> nil then
            Unsigned := IsUnsignedInt(BE.ResolvedType)
          else
            Unsigned := IsUnsignedInt(BE.Left.ResolvedType) and
                        IsUnsignedInt(BE.Right.ResolvedType);
          if Unsigned then
          begin
            Self.Emit(#9'xorl %edx, %edx');
            Self.Emit(#9'divq %rcx');
          end
          else
          begin
            Self.Emit(#9'cqto');
            Self.Emit(#9'idivq %rcx');
          end;
          if BE.Op = boMod then
            Self.Emit(#9'movq %rdx, %rax');  { remainder in %rdx }
        end;
      { Signed integer comparisons -> boolean 0/1 in %rax.  AT&T `cmpq B, A`
        computes A - B; setcc yields 0/1, then movzbl clears the rest. }
      boAnd:
        if HasImm then
          Self.Emit(#9'andq $' + IntToStr(ImmV) + ', %rax')
        else
          Self.Emit(#9'andq %rcx, %rax');
      boOr:
        if HasImm then
          Self.Emit(#9'orq $' + IntToStr(ImmV) + ', %rax')
        else
          Self.Emit(#9'orq %rcx, %rax');
      boXor:
        if HasImm then
          Self.Emit(#9'xorq $' + IntToStr(ImmV) + ', %rax')
        else
          Self.Emit(#9'xorq %rcx, %rax');
      boShl:
        if HasImm then
          Self.Emit(#9'shlq $' + IntToStr(ImmV and 63) + ', %rax')
        else
          Self.Emit(#9'shlq %cl, %rax');
      boShr:
        if HasImm then
          Self.Emit(#9'shrq $' + IntToStr(ImmV and 63) + ', %rax')
        else
          Self.Emit(#9'shrq %cl, %rax');
      boSar:
        if HasImm then
          Self.Emit(#9'sarq $' + IntToStr(ImmV and 63) + ', %rax')
        else
          Self.Emit(#9'sarq %cl, %rax');
      boEQ, boNE, boLT, boGT, boLE, boGE:
        begin
          if (BE.Left.ResolvedType <> nil) and
             (BE.Left.ResolvedType.Kind in [tyInt64, tyUInt64, tyClass,
                tyPointer, tyInterface, tyString, tyDynArray, tyProcedural]) then
          begin
            if HasImm then
              Self.Emit(#9'cmpq $' + IntToStr(ImmV) + ', %rax')
            else
              Self.Emit(#9'cmpq %rcx, %rax');
          end
          else
          begin
            if HasImm then
              Self.Emit(#9'cmpl $' + IntToStr(ImmV) + ', %eax')
            else
              Self.Emit(#9'cmpl %ecx, %eax');
          end;
          Unsigned := IsUnsignedInt(BE.Left.ResolvedType) or
                      IsUnsignedInt(BE.Right.ResolvedType) or
                      ((BE.Left.ResolvedType <> nil) and
                       (BE.Left.ResolvedType.Kind in [tyPointer, tyClass,
                          tyInterface, tyString, tyDynArray, tyProcedural]));
          if Unsigned then
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');
              boGT: Self.Emit(#9'seta %al');
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end
          else
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setl %al');
              boGT: Self.Emit(#9'setg %al');
              boLE: Self.Emit(#9'setle %al');
              boGE: Self.Emit(#9'setge %al');
            end;
          Self.Emit(#9'movzbl %al, %eax');  { 0/1 in %rax (movzbl zero-extends) }
        end;
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported binary operator in integer expression');
    end;
    Exit;
  end;

  { Open-array element read: A[I] where A is an open-array parameter.
    The data pointer lives in the _var_A slot (not _var_A_high). }
  { Indexed/default property read: Obj.Items[I] or Obj[I] (default property) —
    semantic has folded the index into StrExpr (a TFieldAccessExpr with PropRead
    + PropIndexExpr), leaving AExpr.IndexExpr nil.  Delegate to the StrExpr. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(TStringSubscriptExpr(AExpr).StrExpr).PropRead <> nil) then
  begin
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).StrExpr);
    Exit;
  end;

  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr is TIdentExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyOpenArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.VarOperand(TIdentExpr(SAE.StrExpr).Name)]));
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    { Record and jumbo-set elements evaluate to their address — loading
      8 bytes here would read the first field / first bitmap bytes instead
      (BUG-20260721-jumbo-set-in-array-elem). }
    if (TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.Kind <> tyRecord) and
       not IsJumboSet(TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType) then
      Self.EmitLoadVar('(%rax)',
        TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { Dynamic-array element read: A[I] where A is a dynamic array variable.
    Data pointer is stored directly in the variable slot. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyDynArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    { Record and jumbo-set elements evaluate to their address — loading
      8 bytes here would read the first field / first bitmap bytes instead
      (BUG-20260721-jumbo-set-in-array-elem). }
    if (TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.Kind <> tyRecord) and
       not IsJumboSet(TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType) then
      Self.EmitLoadVar('(%rax)',
        TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { Static array element read: A[I] where A: array[L..H] of T.
    Uses TStringSubscriptExpr (the parser's postfix-bracket node). }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyStaticArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.EmitStaticElemScale(TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    { Record, nested static-array, and jumbo-set elements evaluate to their
      address — records are by-value via pointer; a nested array is inline
      storage that a further subscript A[I][J] indexes into; a jumbo set is
      an inline bitmap.  Loading 8 bytes here would read the first
      field/element/bitmap bytes instead of yielding the aggregate address
      (BUG-20260721-jumbo-set-in-array-elem). }
    if not ((TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.Kind in
             [tyRecord, tyStaticArray]) or
            IsJumboSet(TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType)) then
      Self.EmitLoadVar('(%rax)',
        TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { PChar element read: P[I] where P: PChar.  The pointer lives directly in
    the variable slot; load one (zero-extended) byte at base + I. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyPChar) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movzbl (%rax), %eax');
    Exit;
  end;

  { String subscript S[I]: calls _OrdAt(str_ptr, index) -> byte value as Integer. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyString) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(#9'movl %eax, %esi');
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'callq _OrdAt');
    Self.Emit(#9'movslq %eax, %rax');
    Exit;
  end;

  { Zero-arg interface method call: G.GetVal where G: IFoo.  Dispatched through
    the itab; result (if any) in %rax. }
  { Class const accessed via the type name (TThing.MaxCount): semantic marks
    the field-access node IsConstant with the value inlined — no storage to
    load, mirror the IDENT-const path. }
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsConstant then
  begin
    FAE := TFieldAccessExpr(AExpr);
    { Class-level const ARRAY element access (T.Days[I]): semantic folds the
      subscript into the field-access node, setting ConstArraySymbol (the global
      data label), ConstArrayType (the static-array type) and PropIndexExpr (the
      index).  Compute base + (idx - LowBound)*ElemSize and load — mirrors the
      QBE EmitSupportsExpr/IsConstant ConstArraySymbol path.  Without this the
      access fell through to the scalar-string branch and read an empty literal. }
    if (FAE.ConstArraySymbol <> '') and (FAE.PropIndexExpr <> nil) and
       (FAE.ConstArrayType <> nil) then
    begin
      SCAT := TStaticArrayTypeDesc(FAE.ConstArrayType);
      Self.EmitExprToEax(FAE.PropIndexExpr);          { index -> %rax }
      Self.EmitStaticElemScale(SCAT);
      Self.Emit(Format(#9'leaq %s(%%rip), %%rcx',
        [NativeMangle(FAE.ConstArraySymbol)]));
      Self.Emit(#9'addq %rcx, %rax');
      if (SCAT.ElementType <> nil) and IsFloatFamily(SCAT.ElementType) then
        Self.EmitLoadFloat('(%rax)', SCAT.ElementType)
      else if (SCAT.ElementType <> nil) and SCAT.ElementType.IsString() then
        Self.Emit(#9'movq (%rax), %rax')
      else
      begin
        Self.Emit(#9'movq (%rax), %rax');
        Self.EmitNarrowToType(SCAT.ElementType);
      end;
      Exit;
    end;
    { Bare class-const array reference (no subscript): the data label address. }
    if FAE.ConstArraySymbol <> '' then
    begin
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
        [NativeMangle(FAE.ConstArraySymbol)]));
      Exit;
    end;
    if (FAE.ResolvedType <> nil) and FAE.ResolvedType.IsString() then
      Self.EmitStrLitAddr(FAE.ConstString)
    else
      Self.Emit(Format(#9'movabsq $%s, %%rax', [IntToStr(FAE.ConstValue)]));
    Exit;
  end;

  { Static var read: TypeName.StaticVar — a plain global load of the mangled
    label resolved by the semantic pass (no Self, no instance). }
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsClassVarRead then
  begin
    FAE := TFieldAccessExpr(AExpr);
    Self.Emit(Format(#9'movq %s(%%rip), %%rax',
      [NativeMangle(FAE.ClassVarEmitName)]));
    if (FAE.ResolvedType <> nil) and IsIntFamily(FAE.ResolvedType) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    Exit;
  end;

  { Static property read: TypeName.StaticProp — call the static getter (no Self
    argument); result in %rax. }
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsStaticPropGet then
  begin
    FAE := TFieldAccessExpr(AExpr);
    MD  := TMethodDecl(FAE.ResolvedMethod);
    Self.Emit(#9'callq ' +
      MethodEmitNameNative(MD,
        TRecordTypeDesc(FAE.ResolvedClassType).Name, MD.Name));
    if (FAE.ResolvedType <> nil) and IsIntFamily(FAE.ResolvedType) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    Exit;
  end;

  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsInterfaceCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    Self.EmitInterfaceCall(FAE.RecordName, FAE.IsGlobal, FAE.IsVarParam,
      TInterfaceTypeDesc(FAE.ResolvedClassType), FAE.FieldName, nil);
    if (FAE.ResolvedType <> nil) and
       not (FAE.ResolvedType.Kind in [tyInt64, tyUInt64, tyPointer, tyClass,
                                      tyString, tyPChar, tyInterface]) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    Exit;
  end;

  { Built-in: Obj.ClassName — instance → vtable[0] → typeinfo[0] → name at +16 }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsClassNameAccess then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'movq 16(%rax), %rax');
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { Built-in: Obj.ClassType — instance → vtable[0] → typeinfo[0] }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsClassTypeAccess then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'movq (%rax), %rax');
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { Method-backed property read: Obj.Prop or Obj.Prop[I].
    Load the receiver (Self pointer) into %rdi, optional index into %rsi,
    then call the getter method.  Covers chained (Base <> nil), implicit-Self,
    and plain variable receivers. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).PropRead <> nil) and
     (TFieldAccessExpr(AExpr).PropRead.ReadMethod <> '') then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rdi', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rdi), %rdi');
    end
    else
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rdi');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rdi), %rdi');
    end;
    if FAE.FieldInfo <> nil then
    begin
      if FAE.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdi', [FAE.FieldInfo.Offset]));
      Self.Emit(#9'movq (%rdi), %rdi');
    end;
    if FAE.PropIndexExpr <> nil then
    begin
      Self.Emit(#9'pushq %rdi');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'movq %rax, %rsi');
    end;
    Self.EmitPropAccessorCallNative(FAE.PropOwnerType, FAE.PropRead.ReadMethod,
      FAE.PropAccessorVSlot);
    if (FAE.ResolvedType <> nil) and
       not IsIntFamily(FAE.ResolvedType) and
       not IsFloatFamily(FAE.ResolvedType) and
       (FAE.ResolvedType.Kind <> tyString) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { String field subscript read: R.Field[I] (0-based char access).
    Same receiver ladder as the array path, then load the string data
    pointer from the field slot and read byte I. }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsCharAccess and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      Self.Emit(#9'movq %rax, %rcx');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else if FAE.IsClassAccess or FAE.IsVarParam then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
    Self.Emit(#9'movq (%rcx), %rcx');      { string data pointer }
    Self.Emit(#9'pushq %rcx');
    Self.EmitExprToEax(FAE.PropIndexExpr);
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movzbq (%rax), %rax');
    Exit;
  end;

  { Array field subscript read: R.Arr[I] where Arr is an array-typed field.
    Compute the record base address, add FieldInfo.Offset to reach the array
    field, then index into the array (static, dynamic, or open). }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsArrayAccess and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      { Chained receiver (c.N.Arr[I]): the base expression evaluates to the
        record/object address. }
      Self.EmitExprToEax(FAE.Base);
      Self.Emit(#9'movq %rax, %rcx');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else if FAE.IsClassAccess or FAE.IsVarParam then
    begin
      { Class variable / var-param: the slot holds a POINTER to the object
        or record — load it. }
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
    if FAE.FieldInfo.TypeDesc.Kind = tyDynArray then
    begin
      Self.Emit(#9'movq (%rcx), %rcx');
      { The index expression may itself use %rcx (a record-field or chained
        read), so the data pointer must survive on the stack — same
        protection the static-array branch below has always had. }
      Self.Emit(#9'pushq %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'addq %rcx, %rax');
      { Record and interface elements evaluate to their element ADDRESS
        (an interface element is a contiguous 16-byte fat pointer; an
        8-byte load handed consumers the obj as the pair base
        (BUG-20260721-fieldaccess-intf-array-elem-read)).  A jumbo-set
        element is an inline bitmap — its address is the value; an 8-byte
        load handed _SetIn a truncated garbage pointer → SIGSEGV
        (BUG-20260722-jumbo-field-array-elem). }
      if (TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind in
            [tyRecord, tyInterface, tyStaticArray]) or
         IsJumboSet(TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType) then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else if FAE.FieldInfo.TypeDesc.Kind = tyStaticArray then
    begin
      Self.Emit(#9'pushq %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.EmitStaticElemScale(TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc));
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'addq %rcx, %rax');
      if (TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind in
            [tyRecord, tyInterface, tyStaticArray]) or
         IsJumboSet(TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType) then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else if FAE.FieldInfo.TypeDesc.Kind = tyOpenArray then
    begin
      Self.Emit(#9'movq (%rcx), %rcx');
      { Same %rcx-survival rule as the dynamic-array branch above. }
      Self.Emit(#9'pushq %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'addq %rcx, %rax');
      if (TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind in
            [tyRecord, tyInterface, tyStaticArray]) or
         IsJumboSet(TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType) then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else
      raise ENativeCodeGenError.Create(Format(
        'IsArrayAccess on non-array field ''%s'' (kind %d) at line %d',
        [FAE.FieldName, Ord(FAE.FieldInfo.TypeDesc.Kind), FAE.Line]));
    Exit;
  end;

  { Chained field access: Base.Field where Base is another expression.
    Recursively emit the base (returns address for records), then add offset. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     not TFieldAccessExpr(AExpr).IsMethodCall and
     not TFieldAccessExpr(AExpr).IsConstructorCall and
     (TFieldAccessExpr(AExpr).Base <> nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    { When the base is a record-returning call, EmitExprToEax materialises an
      sret buffer with `subq $N,%rsp` and never frees it — fine for a
      standalone expression (the frame epilogue reclaims it), but inside an
      argument push/pop sequence that stray allocation shifts %rsp and
      corrupts the other already-pushed arguments (e.g. a const-string arg
      reloaded by %rsp offset).  Allocate the buffer here, read the scalar
      field out of it, then FREE it so this expression nets zero stack change.
      Only safe for scalar fields — a record/static-array field returns an
      address INTO the buffer, so its lifetime must outlive this read and the
      buffer cannot be freed here. }
    if Self.IsNativeRecordCall(FAE.Base) and
       not (IsJumboSet(FAE.FieldInfo.TypeDesc) or
            (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
    begin
      Self.Emit(Format(#9'subq $%d, %%rsp', [Self.RecArgBufBytes(FAE.Base)]));
      Self.EmitRecordCallSretAt(FAE.Base, '(%rsp)');
      Self.Emit(#9'movq %rsp, %rcx');
      if FAE.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rcx', [FAE.FieldInfo.Offset]));
      Self.EmitLoadVar('(%rcx)', FAE.FieldInfo.TypeDesc);
      Self.Emit(Format(#9'addq $%d, %%rsp', [Self.RecArgBufBytes(FAE.Base)]));
      Exit;
    end;
    Self.EmitExprToEax(FAE.Base);
    if NativeExprOwnsRef(FAE.Base) then
      Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rcx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'leaq %d(%%rcx), %%rcx', [FAE.FieldInfo.Offset]));
    if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
      Self.Emit(#9'movq %rcx, %rax')
    else
      Self.EmitLoadVar('(%rcx)', FAE.FieldInfo.TypeDesc);
    if NativeExprOwnsRef(FAE.Base) then
    begin
      { The loaded field value (%rax) is borrowed from the owned transient base
        (on the stack).  If the field is itself a managed class/interface ref it
        aliases INTO the base's object graph — releasing the base inline runs its
        _FieldCleanup, freeing the very object the loaded pointer designates, so
        the value dangles for the rest of the chain (MakeIt().A.B.Method():
        freeing the MakeIt() transient frees A, whose cleanup frees B, before B's
        method runs).  DEFER the base release to the end of the enclosing leaf
        statement (BUG-003 native half): spill the base to a _pendrel slot so it
        stays alive through the field value's use, then FlushNativePendingReleases
        releases it after the store.  For a SCALAR field there is no aliasing, so
        release the base inline as before. }
      if FAE.FieldInfo.TypeDesc.Kind in [tyClass, tyInterface] then
      begin
        { Field value in %rax, base on the stack.  Stash the field value, pop the
          base into %rax, and try to defer its release. }
        Self.Emit(#9'movq %rax, %rcx');    { %rcx = field value (survives defer) }
        Self.Emit(#9'popq %rax');          { %rax = owned transient base }
        if Self.DeferNativeClassRelease() then
          { base spilled to a _pendrel slot; released at statement end }
          Self.Emit(#9'movq %rcx, %rax')   { restore the field value }
        else
        begin
          { All _pendrel slots in use — fall back to the AddRef-pin (safe leak):
            pin the field value so the inline base release does not free it. }
          Self.Emit(#9'pushq %rax');       { save base again }
          Self.Emit(#9'movq %rcx, %rdi');  { AddRef the field value }
          Self.Emit(#9'callq _ClassAddRef');
          Self.Emit(#9'popq %rdi');        { base -> %rdi }
          Self.Emit(#9'callq _ClassRelease');
          Self.Emit(#9'movq %rcx, %rax');  { restore the field value }
        end;
      end
      else
      begin
        { Scalar field: no aliasing.  Release the base inline. }
        Self.Emit(#9'popq %rdi');
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
      end;
    end;
    Exit;
  end;

  { Record/class field read: Rec.Field or Class.Field.
    Handles local/global record bases and class (pointer-deref) bases. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     not TFieldAccessExpr(AExpr).IsMethodCall and
     not TFieldAccessExpr(AExpr).IsConstructorCall and
     (TFieldAccessExpr(AExpr).Base = nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rcx), %rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]))
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end
    else if FAE.IsClassAccess then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rcx), %rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]))
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end
    else if FAE.IsVarParam then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]))
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end
    else if (not Self.IsCaptured(FAE.RecordName)) and
            (not (FSretFunc and SameText(FAE.RecordName, 'Result'))) and
            (not Self.IsLocal(FAE.RecordName)) and
            (FAE.FieldInfo.Offset = 0) and
            (not (IsJumboSet(FAE.FieldInfo.TypeDesc) or
                  (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray]))) and
            (not Self.IsThreadVarGlobal(FAE.RecordName)) then
      { Non-threadvar offset-0 fast path: read the field directly off the
        PC-relative global.  Only applies to a genuine global (not local, not
        captured, not sret Result, not threadvar). }
      Self.EmitLoadVar(Self.GlobalSymName(FAE.RecordName) + '(%rip)', FAE.FieldInfo.TypeDesc)
    else
    begin
      { Compute the record base into %rcx, handling local / global / sret-Result
        / nested-captured uniformly, then read or address the field.  Aggregate
        fields (record/static array/jumbo set) yield an ADDRESS in %rax; scalar
        fields are loaded by value. }
      Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
      begin
        if FAE.FieldInfo.Offset = 0 then
          Self.Emit(#9'movq %rcx, %rax')
        else
          Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]));
      end
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end;
    Exit;
  end;

  { Zero-arg method call on a variable: B.GetVal or H.GetValue.
    For class variables Self is the loaded pointer; for record variables Self
    is the address of the record storage. }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsMethodCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.ResolvedMethod = nil then
      raise ENativeCodeGenError.Create(
        'native backend: zero-arg method call has no ResolvedMethod');
    MD := TMethodDecl(FAE.ResolvedMethod);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
    end
    else if MD.IsRecordMethod and FAE.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FAE.RecordName)]))
    else if MD.IsRecordMethod then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, True, '%rdi');
    end
    else if FAE.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FAE.RecordName)]));
      Self.Emit(#9'movq (%rdi), %rdi');
    end
    else
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rdi');
    end;
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + MethodEmitNameNative(
        MD, MD.OwnerTypeName, FAE.FieldName));
    if (MD.ResolvedReturnType <> nil) and
       not IsIntFamily(MD.ResolvedReturnType) and
       not IsFloatFamily(MD.ResolvedReturnType) and
       (MD.ResolvedReturnType.Kind <> tyString) then
      Self.EmitNarrowToType(MD.ResolvedReturnType);
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { ── TAddrOfExpr: @Expr ── }
  if AExpr is TAddrOfExpr then
  begin
    AOE := TAddrOfExpr(AExpr);

    { @TFoo.StaticVar — a static (class-level) var's storage IS the mangled
      global slot; take its address directly rather than as a field of an
      instance. }
    if (AOE.Expr is TFieldAccessExpr) and
       TFieldAccessExpr(AOE.Expr).IsClassVarRead then
    begin
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
        [NativeMangle(TFieldAccessExpr(AOE.Expr).ClassVarEmitName)]));
      Exit;
    end;

    { @Array[I] — address of array element.  The inner expression is
      TStringSubscriptExpr (the parser's postfix-bracket node).  Compute
      base + index * elemSize without the final load. }
    if AOE.Expr is TStringSubscriptExpr then
    begin
      SAE := TStringSubscriptExpr(AOE.Expr);
      if (SAE.StrExpr.ResolvedType <> nil) and
         (SAE.StrExpr.ResolvedType.Kind = tyStaticArray) then
      begin
        Self.EmitExprToEax(SAE.StrExpr);
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(SAE.IndexExpr);
        Self.EmitStaticElemScale(TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
        Exit;
      end;
      if (SAE.StrExpr.ResolvedType <> nil) and
         (SAE.StrExpr.ResolvedType.Kind = tyOpenArray) then
      begin
        if (SAE.StrExpr is TIdentExpr) then
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(SAE.StrExpr).Name)]))
        else
          Self.EmitExprToEax(SAE.StrExpr);
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(SAE.IndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
        Exit;
      end;
      if (SAE.StrExpr.ResolvedType <> nil) and
         (SAE.StrExpr.ResolvedType.Kind = tyDynArray) then
      begin
        Self.EmitExprToEax(SAE.StrExpr);
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(SAE.IndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
        Exit;
      end;
    end;

    { @FuncName — load the function's code address into %rax. }
    if (AOE.Expr is TIdentExpr) and
       (TIdentExpr(AOE.Expr).ResolvedType <> nil) and
       (TIdentExpr(AOE.Expr).ResolvedType.Kind = tyProcedural) then
    begin
      if AOE.ResolvedFreeRoutine <> nil then
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [NativeMangle(TMethodDecl(AOE.ResolvedFreeRoutine).ResolvedQbeName)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [Self.GlobalSymName(TIdentExpr(AOE.Expr).Name)]));
      Exit;
    end;

    { @VarParam — the variable's slot holds a pointer to the caller's data;
      load that pointer value (not the slot address). }
    if (AOE.Expr is TIdentExpr) and (TIdentExpr(AOE.Expr).ParamMode <> pmNone) then
    begin
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AOE.Expr).Name)]));
      Exit;
    end;

    { @ImplicitSelfField — field of Self accessed by bare name inside a method. }
    if (AOE.Expr is TIdentExpr) and
       TIdentExpr(AOE.Expr).IsImplicitSelf and
       (TIdentExpr(AOE.Expr).ImplicitFieldInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AOE.Expr).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rax',
          [TFieldInfo(TIdentExpr(AOE.Expr).ImplicitFieldInfo).Offset]));
      Exit;
    end;

    { @Variable — take the address of a local or global variable.
      Routed through EmitVarAddr so a threadvar global yields the
      PER-THREAD address (movq %fs:0 + leaq @tpoff) instead of a
      static leaq Name(%rip) — the bare rip-relative form made every
      thread's @TV identical, silently breaking any code that keys
      identity off a threadvar address (runtime.mem's MyTid). }
    { @IntfVar — an interface variable's storage is a 16-byte fat pointer, but
      the native backend addresses it by NAMED SLOT: a local occupies its frame
      slot (obj) plus the 8 bytes above it (itab), and a global emits adjacent
      <Name>_obj / <Name>_itab labels.  There is no symbol under the bare name,
      so EmitVarAddr below would emit `leaq Slot(%rip)` against an UNDEFINED
      symbol — the linker bound it to a garbage address and `Fill(@Slot)`
      segfaulted.  Take the address of the obj slot, which is the base of the
      contiguous fat pointer. }
    if (AOE.Expr is TIdentExpr) and
       (AOE.Expr.ResolvedType <> nil) and
       (AOE.Expr.ResolvedType.Kind = tyInterface) then
    begin
      IE := TIdentExpr(AOE.Expr);
      if (not IE.IsGlobal) and Self.IsLocal(IE.Name) then
        Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand(IE.Name)]))
      else
      begin
        Self.AddGlobal(IE.Name, IE.ResolvedType);
        Self.Emit(Format(#9'leaq %s_obj(%%rip), %%rax',
          [Self.GlobalSymName(IE.Name)]));
      end;
      Exit;
    end;

    if AOE.Expr is TIdentExpr then
    begin
      Self.EmitVarAddr(TIdentExpr(AOE.Expr).Name, '%rax');
      Exit;
    end;

    { @Rec.Arr[I] — address of array-field element.  The field access has
      IsArrayAccess set by semantic and PropIndexExpr holds the subscript. }
    if (AOE.Expr is TFieldAccessExpr) and
       TFieldAccessExpr(AOE.Expr).IsArrayAccess then
    begin
      FAE := TFieldAccessExpr(AOE.Expr);
      if FAE.Base <> nil then
      begin
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FAE.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
        if FAE.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
        if FAE.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]))
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
      end;
      if FAE.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
      if FAE.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        Self.Emit(#9'movq (%rcx), %rcx');
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.PropIndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
      end
      else if FAE.FieldInfo.TypeDesc.Kind = tyStaticArray then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.PropIndexExpr);
        Self.EmitStaticElemScale(TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
      end
      else
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.PropIndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
      end;
      Exit;
    end;

    { @Obj.MethodName — method-pointer construction is handled at statement
      level (TAssignment) to write directly into the 16-byte destination slot. }
    if (AOE.Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(AOE.Expr).ResolvedType <> nil) and
       (TFieldAccessExpr(AOE.Expr).ResolvedType.Kind = tyProcedural) and
       TProceduralTypeDesc(TFieldAccessExpr(AOE.Expr).ResolvedType).IsMethodPtr then
      raise ENativeCodeGenError.Create(
        'native backend: @Obj.Method must be used in assignment context');

    { @Rec.Field — address of a record/class field (non-array). }
    if AOE.Expr is TFieldAccessExpr then
    begin
      FAE := TFieldAccessExpr(AOE.Expr);
      if FAE.Base <> nil then
      begin
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FAE.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
        if FAE.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
        if FAE.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]))
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
      end;
      if (FAE.FieldInfo <> nil) and (FAE.FieldInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
      Self.Emit(#9'movq %rcx, %rax');
      Exit;
    end;

    raise ENativeCodeGenError.Create(
      'native backend: unsupported TAddrOfExpr form (' +
      AOE.Expr.ClassName + ')');
  end;

  { P^ — pointer dereference read.  Load the pointer into %rcx, then load
    the pointed-to value into %rax through (%rcx). }
  { Set literal [EnumA, EnumC, ...] — compute bitmask at compile time. }
  if (AExpr is TArrayLiteralExpr) and
     (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tySet) then
  begin
    { Jumbo set literal: build the bitmap in the scratch_1 slot — memset 0,
      then _SetInclude per element (elements may be non-constant).  Return the
      buffer address.  scratch_1 (not scratch_0) so a surrounding set-op
      assignment, which uses scratch_0, is not clobbered. }
    if IsJumboSet(AExpr.ResolvedType) then
    begin
      Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand('_jset_scratch_1')]));
      Self.Emit(#9'xorl %esi, %esi');
      Self.Emit(Format(#9'movl $%d, %%edx', [TSetTypeDesc(AExpr.ResolvedType).RawSize()]));
      Self.Emit(#9'callq memset');
      for SetI := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
      begin
        SetElem := TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[SetI]);
        Self.EmitExprToEax(SetElem);
        Self.Emit(#9'movl %eax, %esi');     { ordinal }
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand('_jset_scratch_1')]));
        Self.Emit(#9'callq _SetInclude');
      end;
      Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand('_jset_scratch_1')]));
      Exit;
    end;
    SetMask := 0;
    for SetI := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
    begin
      SetElem := TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[SetI]);
      if SetElem is TIntLiteral then
        SetMask := SetMask or (Int64(1) shl TIntLiteral(SetElem).Value)
      else if (SetElem is TIdentExpr) and TIdentExpr(SetElem).IsConstant then
        SetMask := SetMask or (Int64(1) shl TIdentExpr(SetElem).ConstValue);
    end;
    if TSetTypeDesc(AExpr.ResolvedType).BitCount > 32 then
      Self.Emit(Format(#9'movabsq $%s, %%rax', [IntToStr(SetMask)]))
    else
      Self.Emit(Format(#9'movl $%s, %%eax', [IntToStr(SetMask)]));
    Exit;
  end;

  if AExpr is TDerefExpr then
  begin
    Self.EmitExprToEax(TDerefExpr(AExpr).Expr);
    if (AExpr.ResolvedType <> nil) and
       (IsJumboSet(AExpr.ResolvedType) or
       (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray])) then
    begin
      { Pointer-to-record/array: the pointer value IS the record address.
        Callers (field access, assignment) work with addresses for records. }
    end
    else
    begin
      Self.Emit(#9'movq %rax, %rcx');
      Self.EmitLoadVar('(%rcx)', AExpr.ResolvedType);
    end;
    Exit;
  end;

  { not Expr — logical or bitwise NOT. }
  if AExpr is TNotExpr then
  begin
    Self.EmitExprToEax(TNotExpr(AExpr).Expr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyBoolean) then
      Self.Emit(#9'xorl $1, %eax')
    else if (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind in [tyInt64, tyUInt64]) then
      Self.Emit(#9'notq %rax')
    else
      Self.Emit(#9'notl %eax');
    Exit;
  end;

  { TypeName.Create — allocate a new class instance.
    Returns the instance pointer in %rax.  Does NOT do ARC (caller's job). }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsConstructorCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if (FAE.ResolvedType = nil) or not (FAE.ResolvedType is TRecordTypeDesc) then
      raise ENativeCodeGenError.Create('native backend: constructor call has no class type');
    { _ClassAlloc(size, fieldcleanup_fn): returns zeroed instance ptr (after header). }
    Self.Emit(Format(#9'movq $%d, %%rdi',
      [TRecordTypeDesc(FAE.ResolvedType).TotalSize()]));
    Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi',
      [Self.ClassSymName(FAE.ResolvedType.Name)]));
    Self.Emit(#9'callq _ClassAlloc');
    { Store vtable pointer at offset 0 if the class has virtual methods. }
    if TRecordTypeDesc(FAE.ResolvedType).HasVTable() then
    begin
      Self.Emit(Format(#9'leaq vtable_%s(%%rip), %%rcx',
        [Self.ClassSymName(FAE.ResolvedType.Name)]));
      Self.Emit(#9'movq %rcx, (%rax)');
    end;
    if FDebugMode then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'movq %rax, %rbx');
      Self.Emit(#9'movq %rbx, %rdi');
      Self.Emit(Format(#9'movq typeinfo_%s+16(%%rip), %%rsi',
        [Self.ClassSymName(FAE.ResolvedType.Name)]));
      SetI := FStrLits.IndexOf(FCurrentUnitName);
      if SetI < 0 then SetI := FStrLits.Add(FCurrentUnitName);
      Self.Emit(Format(#9'leaq __s%d+12(%%rip), %%rdx', [SetI]));
      Self.Emit(Format(#9'movq $%d, %%rcx', [FAE.Line]));
      Self.Emit(#9'callq _LeakTrackerRegister');
      Self.Emit(#9'movq %rbx, %rax');
      Self.Emit(#9'popq %rbx');
    end;
    { Call user-defined zero-arg Create body if present. }
    if FAE.ResolvedMethod <> nil then
    begin
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq ' + MethodEmitNameNative(
        TMethodDecl(FAE.ResolvedMethod), FAE.ResolvedType.Name, FAE.FieldName));
      Self.Emit(#9'popq %rax');
    end;
    { %rax = new instance pointer. }
    Exit;
  end;

  { Class method call: C.Method() or C.Method(args) returning a scalar. }
  if AExpr is TMethodCallExpr then
  begin
    Self.EmitMethodCallExpr(TMethodCallExpr(AExpr));
    Exit;
  end;

  { Indirect function call expression: FuncPtrExpr(args) returning a value.
    Evaluate the callee expression, save the function pointer on the stack
    (arg evaluation may invoke callq which clobbers caller-saved regs), push
    args, pop them into registers, load the saved func ptr into %r10, and
    dispatch via callq *%r10. }
  if AExpr is TIndirectFuncCallExpr then
  begin
    { Method-pointer callee ('of object'): the callee yields a 16-byte
      [Code; Data] block, not a bare function pointer.  Materialise the callee
      value into a stack buffer (it may itself be a method-ptr-returning call,
      e.g. Obj.GetFn()(args)) and dispatch through EmitMethodPtrCall, which
      loads Code into %r10 and Data (Self) into %rdi. }
    if (TIndirectFuncCallExpr(AExpr).ResolvedProcType <> nil) and
       (TProceduralTypeDesc(
          TIndirectFuncCallExpr(AExpr).ResolvedProcType).IsMethodPtr or
        TProceduralTypeDesc(
          TIndirectFuncCallExpr(AExpr).ResolvedProcType).IsReference) then
    begin
      { Materialise the callee's 16-byte [Code; Data] block into a stack buffer
        and carry its address in callee-saved %rbx — EmitMethodPtrCall reads its
        operand AFTER pushing args (which moves %rsp), so a %rsp-relative operand
        would drift; %rbx survives the arg push/pop. }
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'subq $16, %rsp');
      Self.EmitRecordCallSretAt(TIndirectFuncCallExpr(AExpr).CalleeExpr, '(%rsp)');
      Self.Emit(#9'movq %rsp, %rbx');
      Self.EmitMethodPtrCall('(%rbx)',
        TProceduralTypeDesc(TIndirectFuncCallExpr(AExpr).ResolvedProcType),
        TIndirectFuncCallExpr(AExpr).Args);
      Self.Emit(#9'addq $16, %rsp');
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    Self.EmitExprToEax(TIndirectFuncCallExpr(AExpr).CalleeExpr);
    Self.Emit(#9'pushq %rax');
    for SetI := 0 to TIndirectFuncCallExpr(AExpr).Args.Count - 1 do
    begin
      Self.EmitExprToEax(TASTExpr(TIndirectFuncCallExpr(AExpr).Args.Items[SetI]));
      Self.Emit(#9'pushq %rax');
    end;
    for SetI := TIndirectFuncCallExpr(AExpr).Args.Count - 1 downto 0 do
      Self.Emit(Format(#9'popq %s', [SysVArg64(SetI)]));
    Self.Emit(#9'popq %r10');
    Self.Emit(#9'callq *%r10');
    Exit;
  end;

  { `inherited Method(args)` in expression position — static dispatch to the
    parent slot; result lands in %rax / %xmm0 (the EmitExprToEax contract). }
  if AExpr is TInheritedCallExpr then
  begin
    Self.EmitInheritedCallSeq(
      TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod),
      TInheritedCallExpr(AExpr).Args,
      TInheritedCallExpr(AExpr).Name);
    Exit;
  end;

  { X is TFoo — class type test via _IsInstance / _ImplementsInterface.
    Result: 0/1 in %eax. }
  if AExpr is TIsExpr then
  begin
    Self.EmitExprToEax(TIsExpr(AExpr).Obj);
    Self.Emit(#9'movq %rax, %rdi');
    if (TIsExpr(AExpr).ResolvedTargetType <> nil) and
       (TIsExpr(AExpr).ResolvedTargetType.Kind = tyInterface) then
    begin
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.ClassSymName(TIsExpr(AExpr).TypeName)]));
      Self.Emit(#9'callq _ImplementsInterface');
    end
    else
    begin
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.ClassSymName(TIsExpr(AExpr).TypeName)]));
      Self.Emit(#9'callq _IsInstance');
    end;
    Exit;
  end;

  { X as TFoo — checked downcast.  Calls _IsInstance; raises EInvalidCast on
    failure; result = original object pointer (class-to-class). }
  if AExpr is TAsExpr then
  begin
    ScEndLbl := Self.NewLabel('as_ok');
    Self.EmitExprToEax(TAsExpr(AExpr).Obj);
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
      [Self.ClassSymName(TAsExpr(AExpr).TypeName)]));
    Self.Emit(#9'callq _IsInstance');
    Self.Emit(#9'testl %eax, %eax');
    Self.Emit(#9'jnz ' + ScEndLbl);
    Self.Emit(#9'callq _Raise_InvalidCast');
    Self.Emit(ScEndLbl + ':');
    Self.Emit(#9'popq %rax');
    Exit;
  end;

  { Supports(Obj, IFoo[, OutVar]) — interface query via _ImplementsInterface.
    Result: 0/1 in %eax.  The 3-arg form additionally populates OutVar's fat
    pointer (obj+itab) on success, with ARC retain/release, mirroring the QBE
    EmitSupportsExpr path. }
  if AExpr is TSupportsExpr then
  begin
    SuppOut := TSupportsExpr(AExpr).OutVarName;
    Self.EmitExprToEax(TSupportsExpr(AExpr).Obj);
    if SuppOut = '' then
    begin
      { 2-arg form: boolean result only. }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.IntfTypeInfoName(TSupportsExpr(AExpr).IntfTypeName)]));
      Self.Emit(#9'callq _ImplementsInterface');
      Exit;
    end;
    { 3-arg form.  Keep obj on the stack across the helper calls. }
    Self.Emit(#9'pushq %rax');               { (obj) }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
      [Self.IntfTypeInfoName(TSupportsExpr(AExpr).IntfTypeName)]));
    Self.Emit(#9'callq _ImplementsInterface');
    LSuppNo  := Self.NewLabel('supports_no');
    LSuppEnd := Self.NewLabel('supports_end');
    Self.Emit(#9'testl %eax, %eax');
    Self.Emit(#9'jz ' + LSuppNo);
    { Success: register the out-var (if global) so its _obj/_itab labels are
      emitted, then store the new fat pointer with ARC. }
    if not Self.IsLocal(SuppOut) then
      Self.AddGlobal(SuppOut, TSupportsExpr(AExpr).ResolvedIntfType);
    Self.Emit(#9'movq (%rsp), %rdi');        { obj }
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
      [Self.IntfTypeInfoName(TSupportsExpr(AExpr).IntfTypeName)]));
    Self.Emit(#9'callq _GetItab');           { itab -> %rax }
    Self.Emit(#9'pushq %rax');               { (itab, obj) }
    { ARC: retain new obj, release the out-var's old obj slot. }
    Self.Emit(#9'movq 8(%rsp), %rdi');       { obj }
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi',
      [Self.IntfObjOperand(SuppOut, TSupportsExpr(AExpr).OutVarIsGlobal)]));
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');                { itab }
    Self.Emit(Format(#9'movq %%rax, %s',
      [Self.IntfItabOperand(SuppOut, TSupportsExpr(AExpr).OutVarIsGlobal)]));
    Self.Emit(#9'popq %rax');                { obj }
    Self.Emit(Format(#9'movq %%rax, %s',
      [Self.IntfObjOperand(SuppOut, TSupportsExpr(AExpr).OutVarIsGlobal)]));
    Self.Emit(#9'movl $1, %eax');
    Self.Emit(#9'jmp ' + LSuppEnd);
    Self.Emit(LSuppNo + ':');
    Self.Emit(#9'addq $8, %rsp');            { discard saved obj }
    Self.Emit(#9'movl $0, %eax');
    Self.Emit(LSuppEnd + ':');
    Exit;
  end;

  if AExpr is TAnonMethodExpr then
  begin
    { Literal consumed in VALUE position: materialise into its hidden slot
      and yield the slot ADDRESS (aggregate-style, like records). }
    Self.EmitAnonValueToSlot(TAnonMethodExpr(AExpr));
    Exit;
  end;
  raise ENativeCodeGenError.Create(
    Format('native backend: unsupported expression form %s at line %d col %d in %s',
      [AExpr.ClassName, AExpr.Line, AExpr.Col, FCurrentUnitName]));
end;

{ Emit a class method call: load Self into %rdi, then scalar args starting at
  %rsi/%rdx/etc.  The method symbol is OwnerTypeName_MethodName. }
procedure TX86_64Backend.EmitMethodCallExpr(ACall: TMethodCallExpr);
var
  I:          Integer;
  SetI:       Integer;
  MD:         TMethodDecl;
  Sym:        string;
  Arg:        TASTExpr;
  RT:         TRecordTypeDesc;
  UserSlots:     Integer;
  TotalSlots:    Integer;
  AllocSz:       Integer;
  SlotOff:       Integer;
  CleanUp:       Integer;
  OverflowSlots: Integer;
  Dest:          Integer;
  HD:            TList<Integer>;
  HK:            TList<Integer>;
  HTotal:        Integer;
  RecvBufBytes:  Integer;
begin
  { Interface method dispatch: receiver is an interface fat pointer; route
    through the itab rather than a static method symbol. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    { When the receiver is an expression (an interface stored in a field, e.g.
      H.G.Greet(), or a bare `FField.M()` inside a method where semantic
      synthesises ObjExpr = an implicit-Self field ident), ACall.ObjectName is
      empty — pass ACall.ObjExpr so obj/itab are loaded from the field's fat
      pointer rather than bogus _obj/_itab operands. }
    Self.EmitInterfaceCall(ACall.ObjectName, ACall.IsGlobal, ACall.IsVarParam,
      TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args,
      ACall.ObjExpr);
    Exit;
  end;

  { Constructor call with args: TypeName.Create(args).
    Allocate the instance, save it in %r10, push args, pop into registers,
    call the constructor body, then return the instance in %rax. }
  if ACall.IsConstructorCall then
  begin
    RT := TRecordTypeDesc(ACall.ResolvedClassType);
    if ACall.IsMetaclassDispatch then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'callq _ClassCreate');
    end
    else
    begin
      Self.Emit(Format(#9'movq $%d, %%rdi', [RT.TotalSize()]));
      Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi', [Self.ClassSymName(RT.Name)]));
      Self.Emit(#9'callq _ClassAlloc');
      if RT.HasVTable() then
      begin
        Self.Emit(Format(#9'leaq vtable_%s(%%rip), %%rcx', [Self.ClassSymName(RT.Name)]));
        Self.Emit(#9'movq %rcx, (%rax)');
      end;
    end;
    if FDebugMode then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'movq %rax, %rbx');
      Self.Emit(#9'movq %rbx, %rdi');
      Self.Emit(Format(#9'movq typeinfo_%s+16(%%rip), %%rsi',
        [Self.ClassSymName(RT.Name)]));
      SetI := FStrLits.IndexOf(FCurrentUnitName);
      if SetI < 0 then SetI := FStrLits.Add(FCurrentUnitName);
      Self.Emit(Format(#9'leaq __s%d+12(%%rip), %%rdx', [SetI]));
      Self.Emit(Format(#9'movq $%d, %%rcx', [ACall.Line]));
      Self.Emit(#9'callq _LeakTrackerRegister');
      Self.Emit(#9'movq %rbx, %rax');
      Self.Emit(#9'popq %rbx');
    end;
    MD := TMethodDecl(ACall.ResolvedMethod);
    if MD <> nil then
    begin
      UserSlots  := Self.CountArgSlots(MD.Params);
      TotalSlots := UserSlots + 1;
      Sym := MethodEmitNameNative(MD, RT.Name, ACall.Name);

      if TotalSlots <= 6 then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.BeginCallArgs(MD.Params, ACall.Args);
        for I := 0 to ACall.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(ACall.Args.Items[I]), I);
        Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
        Self.Emit(#9'movq %rbx, %rdi');
        if ACall.IsMetaclassDispatch and (MD.VTableSlot >= 0) then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EndCallArgs();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end
      else
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        HD := TList<Integer>.Create();
        HK := TList<Integer>.Create();
        HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
        OverflowSlots := TotalSlots - 6;
        AllocSz := ((TotalSlots * 8 + 15) and (-16));
        Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
        Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);
        Self.Emit(Format(#9'movq %%rbx, 0(%%rsp)', []));
        CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
        if ACall.IsMetaclassDispatch and (MD.VTableSlot >= 0) then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
        HD.Free();
        HK.Free();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end;
    end;
    Exit;
  end;

  { Built-in TObject.InheritsFrom(C): _InheritsFrom(self_typeinfo, arg_typeinfo)
    → Boolean in %eax.  A class-instance receiver carries its typeinfo at
    vtable[0] = *( *obj ); the argument is a class-of value that EmitExprToEax
    lowers to a typeinfo pointer (mirrors the QBE path). }
  if ACall.IsBuiltinInheritsFrom then
  begin
    Self.EmitMethodReceiverToRax(ACall);     { instance ptr -> %rax }
    if (ACall.ResolvedClassType <> nil) and
       (ACall.ResolvedClassType.Kind = tyClass) then
    begin
      Self.Emit(#9'movq (%rax), %rax');       { vtable }
      Self.Emit(#9'movq (%rax), %rax');       { typeinfo = vtable[0] }
    end;
    Self.Emit(#9'pushq %rax');                { save self typeinfo }
    Self.EmitExprToEax(TASTExpr(ACall.Args.Items[0]));  { arg typeinfo -> %rax }
    Self.Emit(#9'movq %rax, %rsi');
    Self.Emit(#9'popq %rdi');                 { self typeinfo }
    Self.Emit(#9'callq _InheritsFrom');
    Exit;
  end;

  { Built-in TObject.ToString: virtual dispatch through vtable slot 2 (offset 16:
    [0]=typeinfo, [8]=Destroy, [16]=ToString).  Returns a string in %rax. }
  if ACall.IsBuiltinToString then
  begin
    Self.EmitMethodReceiverToRax(ACall);     { instance ptr -> %rax }
    Self.Emit(#9'movq %rax, %rdi');           { Self }
    Self.Emit(#9'movq (%rdi), %rax');         { vtable }
    Self.Emit(#9'movq 16(%rax), %rax');       { vtable[2] = ToString }
    Self.Emit(#9'callq *%rax');
    Exit;
  end;

  { Procedural-typed field call used as an expression: Result := Self.FFn(S).
    Dispatch through the (Code, Data) pair stored in the field; the result is
    left in %rax. }
  if ACall.IsProcFieldCall then
  begin
    Self.EmitProcFieldCall(ACall.ObjExpr, ACall.ObjectName, ACall.IsVarParam,
      ACall.ProcFieldInfo, TProceduralTypeDesc(ACall.ResolvedProcType),
      ACall.Args, ACall.ResolvedType);
    Exit;
  end;

  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: TMethodCallExpr has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Static method call (TypeName.StaticMethod(args)): NO implicit Self — the
    callee shifts every parameter down one register (first user arg in %rdi).
    A value-returning static method is exactly a plain function call to the
    method's mangled symbol, so route it through EmitCall, which marshals args
    into %rdi.. with no receiver.  Record-returning static factories use the
    sret ABI and are handled in EmitMethodSretCall. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    Self.EmitCall(Sym, MD, ACall.Args);
    Exit;
  end;

  UserSlots  := Self.CountArgSlots(MD.Params);
  TotalSlots := UserSlots + 1;

  if TotalSlots <= 6 then
  begin
    { Record-returning-call receiver (e.g. A.Plus(B).Val()): the receiver is a
      transient record value with no home, but a record method needs Self as an
      ADDRESS.  Materialise the call result into a stack buffer FIRST (before any
      args are pushed) and carry its address in callee-saved %rbx, which survives
      the arg push/pop sequence.  %rbx is saved/restored around the whole call. }
    RecvBufBytes := 0;
    if (ACall.ObjExpr <> nil) and MD.IsRecordMethod and
       Self.IsNativeRecordCall(ACall.ObjExpr) then
    begin
      RecvBufBytes := Self.RecArgBufBytes(ACall.ObjExpr);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [RecvBufBytes]));
      Self.EmitRecordCallSretAt(ACall.ObjExpr, '(%rsp)');
      Self.Emit(#9'movq %rsp, %rbx');     { receiver address -> callee-saved }
    end;

    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;

    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%r10');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%r10), %r10');
      end
      else
      begin
        if Self.IsCaptured(ACall.ObjectName) then
        begin
          { Captured outer class local: _cap_ holds the OUTER slot's
            address — dereference it for the object pointer.  Falling
            through to the global path bound a nonexistent global symbol
            (nested-proc receiver bug, 2026-07-12). }
          Self.Emit(Format(#9'movq %s, %%r10',
            [Self.VarOperand('_cap_' + ACall.ObjectName)]));
          Self.Emit(#9'movq (%r10), %r10');
        end
        else if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%r10',
            [Self.GlobalSymName(ACall.ObjectName)]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %r10')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %r10');
    end
    else
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));

    Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
    Self.Emit(#9'movq %r10, %rdi');
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
    if RecvBufBytes > 0 then
    begin
      { Free the receiver buffer and restore %rbx (does not touch the return
        registers %rax/%rdx/%xmm0/%xmm1). }
      Self.Emit(Format(#9'addq $%d, %%rsp', [RecvBufBytes]));
      Self.Emit(#9'popq %rbx');
    end;
  end
  else
  begin
    { Record-returning-call receiver on the >6-slot path: materialise the result
      into a stack buffer and carry its address in callee-saved %rbx (immune to
      the hoist/alloc %rsp movement below).  See the <=6 path for the rationale. }
    RecvBufBytes := 0;
    if (ACall.ObjExpr <> nil) and MD.IsRecordMethod and
       Self.IsNativeRecordCall(ACall.ObjExpr) then
    begin
      RecvBufBytes := Self.RecArgBufBytes(ACall.ObjExpr);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [RecvBufBytes]));
      Self.EmitRecordCallSretAt(ACall.ObjExpr, '(%rsp)');
      Self.Emit(#9'movq %rsp, %rbx');
    end;
    OverflowSlots := TotalSlots - 6;
    AllocSz := ((TotalSlots * 8 + 15) and (-16));
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));

    Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);

    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rax');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rax), %rax');
      end
      else
      begin
        if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rax',
            [Self.GlobalSymName(ACall.ObjectName)]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rax')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 0(%%rsp)', []));

    CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
    if RecvBufBytes > 0 then
    begin
      Self.Emit(Format(#9'addq $%d, %%rsp', [RecvBufBytes]));
      Self.Emit(#9'popq %rbx');
    end;
  end;
end;

procedure TX86_64Backend.EmitImplicitSelfCallOverflow(MD: TMethodDecl;
  AArgs: TObjectList; const ASym: string);
var
  I, AllocSz, CleanUp, Dest: Integer;
  Arg: TASTExpr;
  HD, HK: TList<Integer>;
  HTotal: Integer;
begin
  { Slot block: slot 0 = Self, slots 1.. = one per logical arg (matching
    EmitMethodOverflowLoad's reader).  16-aligned. }
  AllocSz := (((Self.CountArgSlots(MD.Params) + 1) * 8 + 15) and (-16));
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', AArgs, HD, HK);
  Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
  Self.EmitArgsToSlots(AArgs, MD.Params, AllocSz, HTotal, HD, HK);
  { Self into slot 0. }
  Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
  Self.Emit(#9'movq %rax, 0(%rsp)');
  { Load slot 0 -> %rdi (Self) and the arg slots into %rsi.. / %xmm0.., spilling
    the >6th integer slot to the stack; returns bytes to reclaim after the call. }
  CleanUp := Self.EmitMethodOverflowLoad(MD.Params, AArgs, AllocSz);
  { Self is now in %rdi — dispatch (vtable-aware) exactly like Self.Method(). }
  Self.EmitSelfDispatch(MD, ASym);
  Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  HD.Free();
  HK.Free();
end;

{ Leave the ADDRESS of a var/out argument in %rax.  Shared by every
  call-emission path that passes a var param — loading the variable's
  VALUE here (the old EmitSretCall behaviour) hands the callee a garbage
  pointer. }
procedure TX86_64Backend.EmitFieldArrayElemAddrToRax(AFAE: TFieldAccessExpr);
var
  ElemT: TTypeDesc;
begin
  { For a dyn/open array field the %rax slot holds the data POINTER — load it.
    A static array's inline storage starts at %rax directly. }
  if AFAE.FieldInfo.TypeDesc.Kind = tyDynArray then
    ElemT := TDynArrayTypeDesc(AFAE.FieldInfo.TypeDesc).ElementType
  else if AFAE.FieldInfo.TypeDesc.Kind = tyOpenArray then
    ElemT := TOpenArrayTypeDesc(AFAE.FieldInfo.TypeDesc).ElementType
  else
    ElemT := TStaticArrayTypeDesc(AFAE.FieldInfo.TypeDesc).ElementType;
  if AFAE.FieldInfo.TypeDesc.Kind in [tyDynArray, tyOpenArray] then
    Self.Emit(#9'movq (%rax), %rax');        { data pointer }
  Self.Emit(#9'pushq %rax');                 { park base across index eval }
  Self.EmitExprToEax(AFAE.PropIndexExpr);
  if (AFAE.FieldInfo.TypeDesc.Kind = tyStaticArray) and
     (TStaticArrayTypeDesc(AFAE.FieldInfo.TypeDesc).LowBound <> 0) then
    Self.Emit(Format(#9'subq $%d, %%rax',
      [TStaticArrayTypeDesc(AFAE.FieldInfo.TypeDesc).LowBound]));
  Self.Emit(Format(#9'imulq $%d, %%rax', [ElemT.RawSize()]));
  Self.Emit(#9'popq %rcx');                  { base }
  Self.Emit(#9'addq %rcx, %rax');            { element address }
end;

procedure TX86_64Backend.EmitVarArgAddrToRax(AArg: TASTExpr);
var
  FAE: TFieldAccessExpr;
  SubAddrWrap: TAddrOfExpr;
begin
  if (AArg is TIdentExpr) and (TIdentExpr(AArg).ParamMode <> pmNone) then
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.VarOperand(TIdentExpr(AArg).Name)]))
  else if (AArg is TIdentExpr) and TIdentExpr(AArg).IsImplicitSelf
          and (TIdentExpr(AArg).ImplicitFieldInfo <> nil) then
  begin
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    if TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rax',
        [TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset]));
  end
  else if (AArg is TIdentExpr) and Self.IsLocal(TIdentExpr(AArg).Name) then
    Self.Emit(Format(#9'leaq %s, %%rax',
      [Self.VarOperand(TIdentExpr(AArg).Name)]))
  else if (AArg is TIdentExpr) and (TIdentExpr(AArg).ConstArraySymbol <> '') then
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
      [NativeMangle(TIdentExpr(AArg).ConstArraySymbol)]))
  else if (AArg is TIdentExpr) and (AArg.ResolvedType <> nil) and
          (AArg.ResolvedType.Kind = tyInterface) then
    { Global interface: there is no bare Name symbol — the 16-byte fat
      pointer block starts at the Name_obj label. }
    Self.Emit(Format(#9'leaq %s_obj(%%rip), %%rax',
      [Self.GlobalSymName(TIdentExpr(AArg).Name)]))
  else if AArg is TIdentExpr then
    Self.EmitLeaqGlobal(TIdentExpr(AArg).Name, '%rax')
  else if AArg is TFieldAccessExpr then
  begin
    { Record/class field as var argument (including fields of the sret
      Result record).  Compute the field's address. }
    FAE := TFieldAccessExpr(AArg);
    { A static (class-level) var passed by reference: its storage IS the
      mangled global slot — take its address, not a field of an instance.
      Has no FieldInfo, so this must precede the guard below. }
    if FAE.IsClassVarRead then
    begin
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
        [NativeMangle(FAE.ClassVarEmitName)]));
      Exit;
    end;
    if FAE.FieldInfo = nil then
      raise ENativeCodeGenError.Create(
        'native backend: var/out field argument has no resolved field info');
    if FAE.Base <> nil then
      Self.EmitExprToEax(FAE.Base)
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rax', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rax), %rax');
    end
    else if (FSretFunc and SameText(FAE.RecordName, 'Result'))
            or FAE.IsClassAccess or FAE.IsVarParam then
    begin
      { The slot holds a POINTER (sret Result, class instance, var-param
        record) — load it. }
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rax), %rax');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, True, '%rax');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rax', [FAE.FieldInfo.Offset]));
    { An array-FIELD ELEMENT l-value (R.Arr[I] as a var/out actual): the
      code above reaches the array FIELD; apply the subscript so the address
      is the ELEMENT's.  Without this the subscript was silently dropped and
      the l-value was the field base (element 0) — or, for a dyn-array field,
      the data-POINTER slot (BUG-20260723-vararg-field-array-elem-subscript-drop).
      %rax = array field address; leave the element address in %rax. }
    if FAE.IsArrayAccess then
      Self.EmitFieldArrayElemAddrToRax(FAE);
  end
  else if AArg is TStringSubscriptExpr then
  begin
    { Array element a[i] as a var/out actual.  Its address is what @a[i]
      computes, so evaluate a transient TAddrOfExpr (leaves the element
      address in %rax). }
    SubAddrWrap := TAddrOfExpr.Create();
    try
      SubAddrWrap.Expr := AArg;
      Self.EmitExprToEax(SubAddrWrap);
    finally
      SubAddrWrap.Expr := nil;   { AArg owned by the caller }
      SubAddrWrap.Free();
    end;
  end
  else if AArg is TDerefExpr then
    { Pointer dereference P^ as a var/out actual: the address of P^ is
      simply the pointer's value — evaluate P itself. }
    Self.EmitExprToEax(TDerefExpr(AArg).Expr)
  else
    raise ENativeCodeGenError.Create(
      'native backend: var/out argument must be a variable or field');
end;

procedure TX86_64Backend.EmitMethodArgPush(APar: TMethodParam; AArg: TASTExpr);
var
  ClassRT: TRecordTypeDesc;
  IntfDesc: TInterfaceTypeDesc;
  ItabSym: string;
begin
  if (APar <> nil) and APar.IsVarParam then
  begin
    Self.EmitVarArgAddrToRax(AArg);
    Self.Emit(#9'pushq %rax');
  end
  else if (APar <> nil) and (APar.ResolvedType <> nil) and
          (APar.ResolvedType.Kind = tyInterface) then
  begin
    { Interface param: push obj first (lower register slot), then itab (higher
      register slot).  The pop loop runs high-to-low, so itab (pushed last) is
      popped first into the higher register, obj (pushed first) into the lower. }
    IntfDesc := TInterfaceTypeDesc(APar.ResolvedType);
    if AArg.ResolvedType.Kind = tyClass then
    begin
      { Class expression → interface: emit obj, look up static itab. }
      ClassRT := TRecordTypeDesc(AArg.ResolvedType);
      ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(IntfDesc.Name);
      Self.EmitExprToEax(AArg);          { obj -> %rax }
      Self.Emit(#9'pushq %rax');         { push obj }
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'pushq %rax');         { push itab }
    end
    else if AArg is TAsExpr then
    begin
      { T as IFoo: runtime itab lookup. }
      Self.EmitExprToEax(TAsExpr(AArg).Obj);
      Self.Emit(#9'pushq %rax');         { save obj for push below }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.IntfTypeInfoName(TAsExpr(AArg).TypeName)]));
      Self.Emit(#9'callq _GetItab');
      Self.Emit(#9'pushq %rax');         { itab on top; obj below }
      { Stack top: itab, below: obj — but we need obj first (lower slot).
        Swap: pop itab into %rcx, leave obj on stack, push itab back. }
      Self.Emit(#9'popq %rcx');          { rcx = itab }
      { %rax is still obj (was saved before callq). Re-load from stack: }
      Self.Emit(#9'movq (%rsp), %rax'); { rax = obj (already on stack) }
      { Stack already has obj; push itab on top. }
      Self.Emit(#9'pushq %rcx');         { itab on top, obj below ✓ }
    end
    else if (AArg is TIdentExpr) and
            TIdentExpr(AArg).IsImplicitSelf and
            (TIdentExpr(AArg).ImplicitFieldInfo <> nil) then
    begin
      { Implicit Self.field of interface type: load from object layout. }
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rax',
          [TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset]));
      Self.Emit(#9'movq (%rax), %rcx');  { obj }
      Self.Emit(#9'movq 8(%rax), %rdx'); { itab }
      Self.Emit(#9'pushq %rcx');         { push obj }
      Self.Emit(#9'pushq %rdx');         { push itab }
    end
    else if AArg is TFieldAccessExpr then
    begin
      Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AArg), '%rax');
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'movq 8(%rax), %rdx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'pushq %rdx');
    end
    else if (AArg is TIdentExpr) and Self.IsCaptured(TIdentExpr(AArg).Name) then
    begin
      { Captured interface local (BUG-038): dereference the capture pointer
        for both halves. }
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand('_cap_' + TIdentExpr(AArg).Name)]));
      Self.Emit(#9'movq (%rax), %rcx');   { obj }
      Self.Emit(#9'movq 8(%rax), %rdx');  { itab }
      Self.Emit(#9'pushq %rcx');          { push obj }
      Self.Emit(#9'pushq %rdx');          { push itab }
    end
    else if AArg is TIdentExpr then
    begin
      { Interface variable: load both halves. }
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.IntfObjOperand(TIdentExpr(AArg).Name, TIdentExpr(AArg).IsGlobal)]));
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.IntfItabOperand(TIdentExpr(AArg).Name, TIdentExpr(AArg).IsGlobal)]));
      Self.Emit(#9'pushq %rax');         { push obj }
      Self.Emit(#9'pushq %rcx');         { push itab }
    end
    else if ((AArg is TFuncCallExpr) or (AArg is TMethodCallExpr)) and
            (AArg.ResolvedType <> nil) and
            (AArg.ResolvedType.Kind = tyInterface) then
    begin
      { Interface-returning call result passed positionally, e.g.
        Show(MakeFoo(42)).  EmitIntfSretCall leaves the owned (+1) fat pointer
        at (%rsp): obj at 0, itab at 8.  Load both halves and push in the
        arg-slot order (obj first, itab on top), then drop the sret buffer.
        The pushed obj keeps the +1 ref; the callee borrows it for the call. }
      if AArg is TFuncCallExpr then
        Self.EmitIntfSretCall(TFuncCallExpr(AArg))
      else
        Self.EmitIntfSretMethodCall(TMethodCallExpr(AArg));
      Self.Emit(#9'movq (%rsp), %rax');   { obj }
      Self.Emit(#9'movq 8(%rsp), %rcx');  { itab }
      Self.Emit(#9'addq $16, %rsp');      { drop the sret buffer }
      Self.Emit(#9'pushq %rax');          { push obj }
      Self.Emit(#9'pushq %rcx');          { push itab }
    end
    else if (AArg is TStringSubscriptExpr) and
            (TStringSubscriptExpr(AArg).StrExpr.ResolvedType <> nil) and
            (TStringSubscriptExpr(AArg).StrExpr.ResolvedType.Kind in
               [tyStaticArray, tyDynArray, tyOpenArray]) then
    begin
      { Interface array element passed as an argument (Use(Arr[I])): fat pointer
        at the element address (BUG-20260720-qbe-dynarray-intf-elem-read). }
      if TStringSubscriptExpr(AArg).StrExpr.ResolvedType.Kind = tyStaticArray then
        Self.EmitIntfStaticElemAddr(TStringSubscriptExpr(AArg), '%rax')
      else
        Self.EmitIntfDynElemAddr(TStringSubscriptExpr(AArg), '%rax');
      Self.Emit(#9'movq (%rax), %rcx');   { obj }
      Self.Emit(#9'movq 8(%rax), %rdx');  { itab }
      Self.Emit(#9'pushq %rcx');          { push obj }
      Self.Emit(#9'pushq %rdx');          { push itab }
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface argument expression');
  end
  else if (APar <> nil) and APar.IsOpenArray then
  begin
    if AArg is TArrayLiteralExpr then
      { An open-array literal emitted here would subq its element block in the
        middle of the slot-push sequence and break the caller's popq order.
        Call sites must hoist literals via HoistOALitArgs and push them with
        EmitArgPush. }
      raise ENativeCodeGenError.Create(
        'native backend: open-array literal argument reached EmitMethodArgPush'
        + ' — call site must hoist it via HoistOALitArgs')
    else if (AArg is TIdentExpr) and
            (TIdentExpr(AArg).ResolvedType <> nil) and
            (TIdentExpr(AArg).ResolvedType.Kind = tyStaticArray) then
    begin
      if Self.IsLocal(TIdentExpr(AArg).Name) then
        Self.Emit(Format(#9'leaq %s, %%rax',
          [Self.VarOperand(TIdentExpr(AArg).Name)]))
      else if TIdentExpr(AArg).ConstArraySymbol <> '' then
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [NativeMangle(TIdentExpr(AArg).ConstArraySymbol)]))
      else
        Self.EmitLeaqGlobal(TIdentExpr(AArg).Name, '%rax');
      Self.Emit(#9'pushq %rax');
      Self.Emit(Format(#9'pushq $%d',
        [TStaticArrayTypeDesc(TIdentExpr(AArg).ResolvedType).HighBound -
         TStaticArrayTypeDesc(TIdentExpr(AArg).ResolvedType).LowBound]));
    end
    else if (AArg.ResolvedType <> nil) and
            (AArg.ResolvedType.Kind = tyDynArray) then
    begin
      { Dynamic array coerced to open-array: push data ptr + (length - 1). }
      Self.EmitExprToEax(AArg);          { data ptr -> %rax }
      Self.Emit(#9'pushq %rax');         { push ptr }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _DynArrayLength');
      Self.Emit(#9'movslq %eax, %rax');
      Self.Emit(#9'decq %rax');          { high = length - 1 }
      Self.Emit(#9'pushq %rax');         { push high }
    end
    else
    begin
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AArg).Name)]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AArg).Name + '_high')]));
      Self.Emit(#9'pushq %rax');
    end;
  end
  else if (APar <> nil) and IsFloatFamily(APar.ResolvedType) then
  begin
    { Float scalar argument: materialise to %xmm0 (handles literals via the
      .LF constant path, variables, expressions), adjust to the param's width,
      and push its 8-byte bit pattern onto the stack as one slot.  The pop loop
      (EmitPopMethodArgsToRegs) routes this slot into an xmm argument register
      per the SysV ABI instead of an integer register. }
    Self.EmitExprToXmm0(AArg);
    Self.EmitXmm0WidthAdjust(AArg.ResolvedType,
      APar.ResolvedType.Kind = tySingle);
    Self.Emit(#9'subq $8, %rsp');
    Self.Emit(#9'movsd %xmm0, 0(%rsp)');
  end
  else if (APar <> nil) and IsMethodPtrType(APar.ResolvedType) then
  begin
    { Method-pointer / closure argument: pass the ADDRESS of the 16-byte fat
      value (one slot); the callee copies it into its own slot (Phase 2b in
      EmitFunctionDef).  Literals materialise into their hidden value slot. }
    if AArg is TAnonMethodExpr then
      Self.EmitAnonValueToSlot(TAnonMethodExpr(AArg))
    else if (AArg is TIdentExpr) and (not TIdentExpr(AArg).IsImplicitSelf) and
            (not Self.IsCaptured(TIdentExpr(AArg).Name)) then
      Self.Emit(Format(#9'leaq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AArg).Name)]))
    else
      { Field access / captured / call-returning forms: EmitExprToEax yields
        the block address for aggregate-style reads. }
      Self.EmitExprToEax(AArg);
    Self.Emit(#9'pushq %rax');
  end
  else
  begin
    Self.EmitExprToEax(AArg);
    Self.Emit(#9'pushq %rax');
  end;
end;

{ Count total integer register slots consumed by a parameter list.
  Most params = 1 slot; interface params = 2 (obj + itab); open-array = 2.
  Used by pop loops so they iterate over slots, not logical arg positions. }
function TX86_64Backend.SysVArg64(AIndex: Integer): string;
{ Bounds-checked accessor for the 6 System V integer argument registers.  An
  index > 5 means a call-emission slot loop tried to use more than the 6
  available integer registers (args + sret/Self offset overflowed) — a latent
  codegen bug that previously read past SysVArgRegs64[0..5] and returned an
  adjacent data-section value (garbage pointer -> _StringConcat crash).  Raise
  loudly so the offending call path is named instead of silently miscompiling. }
begin
  if (AIndex < 0) or (AIndex > 5) then
    raise ENativeCodeGenError.Create(Format(
      'native backend: System V integer arg register index %d out of range ' +
      '[0..5] — a call has more register-passed slots than the ABI allows ' +
      '(sret/Self offset + args); this path must spill to the stack', [AIndex]));
  Result := SysVArgRegs64[AIndex];
end;

{ Load the receiver object pointer of a class method call into %rax.  Covers an
  expression receiver, a named local/global instance, and implicit Self.  Used by
  the TObject builtins (InheritsFrom, ToString) which only need the instance
  pointer, not the record/var-param address handling of the full call path. }
procedure TX86_64Backend.EmitMethodReceiverToRax(ACall: TMethodCallExpr);
begin
  if ACall.ObjExpr <> nil then
    Self.EmitExprToEax(ACall.ObjExpr)
  else if ACall.ObjectName <> '' then
  begin
    if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%rax), %rax');
    end
    else if Self.IsLocal(ACall.ObjectName) then
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %%rax', [Self.GlobalSymName(ACall.ObjectName)]));
  end
  else
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
end;

function TX86_64Backend.CountArgSlots(AParams: TObjectList): Integer;
var
  I: Integer;
  P: TMethodParam;
begin
  Result := 0;
  if AParams = nil then Exit;
  for I := 0 to AParams.Count - 1 do
  begin
    P := TMethodParam(AParams.Items[I]);
    if P.IsOpenArray then
      Inc(Result, 2)
    else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) then
      Inc(Result, 2)
    else
      Inc(Result);
  end;
end;

{ Consume ASlots argument slots already pushed onto the stack (slot 0 pushed
  first, so slot 0 is at the highest address and slot ASlots-1 is on top) into
  the System V integer argument registers starting at register index ABase
  (ABase = 1 when only %rdi is pre-reserved for the sret buffer, ABase = 2 when
  %rdi=sret buffer and %rsi=receiver/Self are both pre-reserved).

  The first (6 - ABase) slots map to the remaining integer registers; any
  further slots overflow onto the stack per the System V ABI.

  Stack geometry (offsets from %rsp on entry, all in bytes):
    slot i lives at (ASlots-1-i)*8.  So the RegSlots register-mapped slots
    (i = 0..RegSlots-1) occupy the HIGH offsets and the overflow slots
    (i = RegSlots..ASlots-1) occupy the LOW offsets — but in reverse order
    (slot ASlots-1 at offset 0).  System V wants the lowest-indexed overflow
    slot at the lowest address at call time.

  Strategy: load the register slots with `movq` (not pop).  Then relocate the
  overflow slots into the HIGH part of the region (just below the sret buffer)
  in ascending index order, and raise %rsp past the vacated register-slot
  space so the overflow ends up at 0(%rsp).., slot RegSlots first.  The
  relocation runs highest-target-first so a target never overwrites an
  as-yet-unmoved source.

  Returns the number of stack bytes occupied by overflow arguments at call time;
  the caller must `addq` this back after the call (before any sret-buffer slide).
  For ASlots <= (6 - ABase) the result is 0 and the stack is fully consumed. }
function TX86_64Backend.EmitSretRegArgs(ASlots, ABase: Integer): Integer;
var
  RegSlots, OverflowSlots, K, SrcOff, DstOff: Integer;
begin
  RegSlots := 6 - ABase;
  if RegSlots < 0 then RegSlots := 0;
  if ASlots <= RegSlots then
  begin
    { Fast path: everything fits in registers — pop top-down as before. }
    for K := ASlots - 1 downto 0 do
      Self.Emit(#9'popq ' + Self.SysVArg64(K + ABase));
    Result := 0;
    Exit;
  end;
  OverflowSlots := ASlots - RegSlots;
  { Load the register-mapped slots (slots 0 .. RegSlots-1). }
  for K := 0 to RegSlots - 1 do
    Self.Emit(Format(#9'movq %d(%%rsp), %s',
      [(ASlots - 1 - K) * 8, Self.SysVArg64(K + ABase)]));
  { Copy the overflow slots into a FRESH region below the pushed slots, in
    ascending arg order, so the call sees them at 0(%rsp).. (System V
    order).  Every destination is strictly below every source, so the copy
    can never clobber an unread slot, and AlignFreshBytes sizes the region
    so the call site is 16-byte aligned even when pinned pushes above the
    slot block have left the frame at an odd slot count.  Result = bytes
    between %rsp and the region above the pushed slots at call time — the
    caller both re-derives its sret buffer pointer from it and reclaims it
    after the call. }
  DstOff := Self.AlignFreshBytes(OverflowSlots);
  Self.Emit(Format(#9'subq $%d, %%rsp', [DstOff]));
  for K := 0 to OverflowSlots - 1 do
  begin
    SrcOff := DstOff + (ASlots - 1 - (RegSlots + K)) * 8;
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [SrcOff]));
    Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [K * 8]));
  end;
  Result := DstOff + ASlots * 8;
end;

function TX86_64Backend.EmitIntfRegArgs(ASlotClasses: TList<Integer>;
  ABase: Integer): Integer;
var
  I, K, Slots, IntCount, RegInts, IntIdx, XmmIdx: Integer;
  SrcOff, DstOff: Integer;
  Dest: TStringList;
  OvSlots: TList<Integer>;   { forward slot indices of overflow int slots }
begin
  Slots := ASlotClasses.Count;
  IntCount := 0;
  for I := 0 to Slots - 1 do
    if ASlotClasses.Get(I) = 0 then
      Inc(IntCount);
  if IntCount = Slots then
  begin
    { No float slot: keep the classic path so float-free itab calls emit
      byte-identical code. }
    Result := Self.EmitSretRegArgs(Slots, ABase);
    Exit;
  end;
  RegInts := 6 - ABase;
  if RegInts < 0 then RegInts := 0;
  { A 9th+ float slot must overflow to the stack
    (BUG-20260721-x86-method-call-overflow-float), so the all-register fast
    path also requires every float to fit xmm0..7. }
  if (IntCount <= RegInts) and (Slots - IntCount <= 8) then
  begin
    { Everything register-mapped: assign registers in forward slot order
      (integer and xmm sequences advance independently, per SysV), then
      consume the stack top-down — the current slot is always at 0(%rsp). }
    Dest := TStringList.Create();
    try
      IntIdx := ABase;
      XmmIdx := 0;
      for I := 0 to Slots - 1 do
      begin
        if ASlotClasses.Get(I) = 1 then
        begin
          Dest.Add(SysVXmmArgRegs[XmmIdx]);
          Inc(XmmIdx);
        end
        else
        begin
          Dest.Add(Self.SysVArg64(IntIdx));
          Inc(IntIdx);
        end;
      end;
      for I := Slots - 1 downto 0 do
      begin
        if ASlotClasses.Get(I) = 1 then
        begin
          Self.Emit(Format(#9'movsd 0(%%rsp), %s', [Dest.Strings[I]]));
          Self.Emit(#9'addq $8, %rsp');
        end
        else
          Self.Emit(#9'popq ' + Dest.Strings[I]);
      end;
    finally
      Dest.Free();
    end;
    Result := 0;
    Exit;
  end;
  { Register overflow with floats present: leave the pushed slots in place,
    load every register-mapped slot from its %rsp offset, then relocate the
    overflow slots (7th+ integer AND 9th+ float, in ascending arg order —
    System V stack-arg order at 0(%rsp)..) into a fresh region below the
    pushed block.  Same scheme as EmitSretRegArgs; the type-agnostic 8-byte
    relocation is harmless for Single (low 4 bytes)
    (BUG-20260721-x86-method-call-overflow-float). }
  OvSlots := TList<Integer>.Create();
  try
    IntIdx := ABase;
    XmmIdx := 0;
    for I := 0 to Slots - 1 do
    begin
      SrcOff := (Slots - 1 - I) * 8;
      if ASlotClasses.Get(I) = 1 then
      begin
        if XmmIdx <= 7 then
        begin
          Self.Emit(Format(#9'movsd %d(%%rsp), %s',
            [SrcOff, SysVXmmArgRegs[XmmIdx]]));
          Inc(XmmIdx);
        end
        else
          OvSlots.Add(I);
      end
      else if IntIdx <= 5 then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %s',
          [SrcOff, Self.SysVArg64(IntIdx)]));
        Inc(IntIdx);
      end
      else
        OvSlots.Add(I);
    end;
    DstOff := Self.AlignFreshBytes(OvSlots.Count);
    Self.Emit(Format(#9'subq $%d, %%rsp', [DstOff]));
    for K := 0 to OvSlots.Count - 1 do
    begin
      SrcOff := DstOff + (Slots - 1 - OvSlots.Get(K)) * 8;
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [SrcOff]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [K * 8]));
    end;
    Result := DstOff + Slots * 8;
  finally
    OvSlots.Free();
  end;
end;

procedure TX86_64Backend.EmitSelfDispatch(AMD: TMethodDecl;
  const AStaticSym: string);
begin
  Self.EmitSelfDispatchVia(AMD, AStaticSym, '%rdi');
end;

procedure TX86_64Backend.EmitSelfDispatchVia(AMD: TMethodDecl;
  const AStaticSym, ASelfReg: string);
begin
  if (AMD <> nil) and (AMD.VTableSlot >= 0) then
  begin
    Self.Emit(Format(#9'movq (%s), %%rax', [ASelfReg]));
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(AMD.VTableSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + AStaticSym);
end;

procedure TX86_64Backend.BuildArgSlotClasses(AParams, AArgs: TObjectList;
  AList: TList<Integer>);
var
  I, NParams: Integer;
  P: TMethodParam;
  PT: TTypeDesc;
begin
  { Determine the param backing each logical arg.  AParams may be nil (no
    declared params): then every arg is a plain integer slot. }
  NParams := 0;
  if AParams <> nil then NParams := AParams.Count;

  for I := 0 to AArgs.Count - 1 do
  begin
    P := nil;
    if I < NParams then P := TMethodParam(AParams.Items[I]);
    PT := nil;
    if P <> nil then PT := P.ResolvedType;
    if (PT = nil) and (TASTExpr(AArgs.Items[I]).ResolvedType <> nil) then
      PT := TASTExpr(AArgs.Items[I]).ResolvedType;
    if (P <> nil) and P.IsOpenArray then
    begin
      AList.Add(0);  AList.Add(0);   { ptr + high }
    end
    else if (PT <> nil) and (PT.Kind = tyInterface) and
            ((P = nil) or not P.IsVarParam) then
    begin
      AList.Add(0);  AList.Add(0);   { obj + itab }
    end
    else if IsFloatFamily(PT) and ((P = nil) or
            (not P.IsVarParam and not P.IsOpenArray)) then
      AList.Add(1)                   { float scalar -> xmm }
    else
      AList.Add(0);                  { integer/ptr scalar }
  end;
end;

procedure TX86_64Backend.EmitPopMethodArgsToRegs(AParams, AArgs: TObjectList;
  AIntBase: Integer);
var
  I, IntIdx, XmmIdx: Integer;
  IsFloatSlot: TList<Integer>;  { 1 = float (xmm) slot, 0 = integer slot,
                                  in stack-slot order (slot 0 pushed first) }
  Dest: TStringList;            { target register per slot, parallel to above }
  Slots: Integer;
begin
  IsFloatSlot := TList<Integer>.Create();
  Dest := TStringList.Create();
  try
    { Forward pass: one entry per stack slot, in push order (slot 0 first). }
    Self.BuildArgSlotClasses(AParams, AArgs, IsFloatSlot);

    { Assign a register to each slot in forward order: integers consume the
      SysV integer registers from AIntBase, floats consume xmm0.. — the two
      sequences advance independently, per SysV. }
    IntIdx := AIntBase;
    XmmIdx := 0;
    for I := 0 to IsFloatSlot.Count - 1 do
    begin
      if IsFloatSlot.Get(I) = 1 then
      begin
        Dest.Add(SysVXmmArgRegs[XmmIdx]);
        Inc(XmmIdx);
      end
      else
      begin
        Dest.Add(Self.SysVArg64(IntIdx));
        Inc(IntIdx);
      end;
    end;

    { Reverse pass: the top of the stack is the LAST slot.  Pop from the last
      slot down to slot 0, moving each into its precomputed register.  Every
      slot is 8 bytes and consumed in turn, so the current slot is always at
      0(%rsp) — a float reads it then raises %rsp by 8, an integer pops it. }
    Slots := IsFloatSlot.Count;
    for I := Slots - 1 downto 0 do
    begin
      if IsFloatSlot.Get(I) = 1 then
      begin
        Self.Emit(Format(#9'movsd 0(%%rsp), %s', [Dest.Strings[I]]));
        Self.Emit(#9'addq $8, %rsp');
      end
      else
        Self.Emit(#9'popq ' + Dest.Strings[I]);
    end;
  finally
    Dest.Free();
    IsFloatSlot.Free();
  end;
end;

function TX86_64Backend.OverflowArgIsFloat(AParams: TObjectList;
  AIndex: Integer): Boolean;
var
  P: TMethodParam;
begin
  Result := False;
  if (AParams = nil) or (AIndex >= AParams.Count) then Exit;
  P := TMethodParam(AParams.Items[AIndex]);
  Result := IsFloatFamily(P.ResolvedType) and not P.IsVarParam and
            not P.IsOpenArray;
end;

procedure TX86_64Backend.EmitArgsToSlots(AArgs, AParams: TObjectList;
  AAllocSz, AHoistTotal: Integer;
  AHoistDepths, AHoistKinds: TList<Integer>);
var
  I, Dest, Slot: Integer;
  Arg: TASTExpr;
  Par: TMethodParam;
begin
  { Slot is the FLAT slot cursor (slot 0 = the receiver/Self), advancing by
    the true slot width of each argument.  Using the LOGICAL index for the
    destination collapsed an open array's two slots (data ptr + high) into
    one, shifting every later slot: the callee then read a garbage high and
    wrote its out params through code addresses.  The reader
    (EmitMethodOverflowLoad / BuildArgSlotClasses) always walked flat slots;
    the writer must match it. }
  Slot := 1;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    Par := TMethodParam(AParams.Items[I]);
    Dest := Slot * 8;
    if Par.IsOpenArray then
    begin
      { two flat slots: data pointer, then high (mirrors EmitMethodArgPush) }
      if AHoistKinds.Get(I) = akOALit then
      begin
        { hoisted literal: saved data pointer; high from the element count }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AAllocSz + AHoistTotal - AHoistDepths.Get(I)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
        Self.Emit(Format(#9'movq $%d, %%rax',
          [TArrayLiteralExpr(Arg).Elements.Count - 1]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest + 8]));
      end
      else if (Arg is TIdentExpr) and
              (TIdentExpr(Arg).ResolvedType <> nil) and
              (TIdentExpr(Arg).ResolvedType.Kind = tyStaticArray) then
      begin
        if Self.IsLocal(TIdentExpr(Arg).Name) then
          Self.Emit(Format(#9'leaq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]))
        else if TIdentExpr(Arg).ConstArraySymbol <> '' then
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [NativeMangle(TIdentExpr(Arg).ConstArraySymbol)]))
        else
          Self.EmitLeaqGlobal(TIdentExpr(Arg).Name, '%rax');
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
        Self.Emit(Format(#9'movq $%d, %%rax',
          [TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).HighBound -
           TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).LowBound]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest + 8]));
      end
      else if (Arg.ResolvedType <> nil) and
              (Arg.ResolvedType.Kind = tyDynArray) then
      begin
        { dynamic array coerced to open array: data ptr + (length - 1).
          The ptr slot is stored before the _DynArrayLength call clobbers
          %rax; the call itself only touches memory below %rsp, never the
          positive-offset slot region. }
        Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _DynArrayLength');
        Self.Emit(#9'movslq %eax, %rax');
        Self.Emit(#9'decq %rax');
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest + 8]));
      end
      else
      begin
        { open-array param forwarded onwards: slot holds ptr, sibling
          <name>_high slot holds high }
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.VarOperand(TIdentExpr(Arg).Name)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.VarOperand(TIdentExpr(Arg).Name + '_high')]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest + 8]));
      end;
      Slot := Slot + 2;
      Continue;
    end;
    if (Par.ResolvedType <> nil) and
       (Par.ResolvedType.Kind = tyInterface) then
      { two-slot (obj + itab) interface args are not wired into the >6-slot
        store path yet; fail loudly rather than shift every later slot }
      raise ENativeCodeGenError.Create(
        'native backend: interface argument in a >6-slot call is not ' +
        'supported yet');
    if AHoistKinds.Get(I) >= akRecCall then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [AAllocSz + AHoistTotal - AHoistDepths.Get(I)]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
    end
    else if Par.IsVarParam then
    begin
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
    end
    else if Self.OverflowArgIsFloat(AParams, I) then
    begin
      Self.EmitExprToXmm0(Arg);
      Self.EmitXmm0WidthAdjust(Arg.ResolvedType,
        Par.ResolvedType.Kind = tySingle);
      Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [Dest]));
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
    end;
    Slot := Slot + 1;
  end;
end;

function TX86_64Backend.EmitMethodOverflowLoad(AParams, AArgs: TObjectList;
  AAllocSz: Integer): Integer;
var
  I, IntIdx, XmmIdx, SlotOff: Integer;
  IsFloatSlot: TList<Integer>;   { per flat slot (slot 0 = Self): 1 = xmm }
  OverflowOffs: TList<Integer>;  { source offsets of overflow slots (7th+
                                   integer and 9th+ float, in arg order) }
  RK, RSrc, OverflowBytes: Integer;
begin
  IsFloatSlot := TList<Integer>.Create();
  OverflowOffs := TList<Integer>.Create();
  try
    { Slot 0 = Self/receiver — always integer.  The per-arg slots follow. }
    IsFloatSlot.Add(0);
    Self.BuildArgSlotClasses(AParams, AArgs, IsFloatSlot);

    { Load register-bound slots; record integer-overflow slot offsets.  Self is
      integer register 0 (%rdi); arg integers continue from index 1. }
    IntIdx := 0;
    XmmIdx := 0;
    SlotOff := 0;
    for I := 0 to IsFloatSlot.Count - 1 do
    begin
      if IsFloatSlot.Get(I) = 1 then
      begin
        { A 9th+ float overflows to the stack like an integer slot — it was
          silently DROPPED before (the callee then read garbage)
          (BUG-20260721-x86-method-call-overflow-float).  The type-agnostic
          8-byte relocation below is harmless for Single (low 4 bytes). }
        if XmmIdx < 8 then
          Self.Emit(Format(#9'movsd %d(%%rsp), %s',
            [SlotOff, SysVXmmArgRegs[XmmIdx]]))
        else
          OverflowOffs.Add(SlotOff);
        Inc(XmmIdx);
      end
      else
      begin
        if IntIdx < 6 then
          Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]))
        else
          OverflowOffs.Add(SlotOff);
        Inc(IntIdx);
      end;
      Inc(SlotOff, 8);
    end;

    if OverflowOffs.Count = 0 then
    begin
      Self.Emit(Format(#9'addq $%d, %%rsp', [AAllocSz]));
      Result := 0;
      Exit;
    end;

    { Copy the overflow slots into a FRESH region below the slot block, with
      the lowest-indexed overflow arg first (System V order).  Every
      destination is strictly below every source, so the copy can never
      clobber an unread slot, and AlignFreshBytes sizes the region so the
      call sees a 16-byte-aligned %rsp even when pinned pushes above the
      slot block have left the frame at an odd slot count.  The slot block
      plus the fresh region is reclaimed after the call (Result). }
    OverflowBytes := Self.AlignFreshBytes(OverflowOffs.Count);
    Self.Emit(Format(#9'subq $%d, %%rsp', [OverflowBytes]));
    for RK := 0 to OverflowOffs.Count - 1 do
    begin
      RSrc := OverflowBytes + OverflowOffs.Get(RK);
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [RSrc]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [RK * 8]));
    end;
    Result := OverflowBytes + AAllocSz;
  finally
    OverflowOffs.Free();
    IsFloatSlot.Free();
  end;
end;

{ Emit a TMethodCallStmt (class method call in statement position).
  Same as EmitMethodCallExpr but for statement nodes. }
procedure TX86_64Backend.EmitMethodCallStmt(ACall: TMethodCallStmt);
var
  I:        Integer;
  MD:       TMethodDecl;
  Sym:      string;
  Arg:      TASTExpr;
  UserSlots, TotalSlots, AllocSz, SlotOff, CleanUp: Integer;
  OverflowSlots, Dest: Integer;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  RT:       TRecordTypeDesc;
  IsSretDiscard: Boolean;
  SretBufSize:   Integer;
  SretRT:        TRecordTypeDesc;
  SretShim:      TMethodCallExpr;
begin
  { Metaclass-var constructor dispatch in statement position: C.Create(args)
    where C is a 'class of' variable and the result is discarded.  Only the
    expression-position path (EmitExpr) allocated the instance and dispatched
    the ctor through the vtable; without this branch the generic dispatch
    below loads the metaclass typeinfo pointer as the object and calls a
    garbage vtable slot — crashing at runtime.  (A non-metaclass ctor as a
    statement, TFoo.Create();, is rejected by the semantic pass as 'not a
    variable', so only the metaclass shape reaches here.)  The instance comes
    back from _ClassCreate at refcount 1; the result is discarded, so we
    release it once afterwards to free rather than leak it. }
  if ACall.IsConstructorCall and ACall.IsMetaclassDispatch then
  begin
    RT := TRecordTypeDesc(ACall.ResolvedClassType);
    MD := TMethodDecl(ACall.ResolvedMethod);
    Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]));
    Self.Emit(#9'callq _ClassCreate');
    if MD <> nil then
    begin
      UserSlots  := Self.CountArgSlots(MD.Params);
      TotalSlots := UserSlots + 1;
      Sym := MethodEmitNameNative(MD, RT.Name, ACall.Name);
      if TotalSlots <= 6 then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.BeginCallArgs(MD.Params, ACall.Args);
        for I := 0 to ACall.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(ACall.Args.Items[I]), I);
        Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
        Self.Emit(#9'movq %rbx, %rdi');
        if MD.VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EndCallArgs();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end
      else
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        HD := TList<Integer>.Create();
        HK := TList<Integer>.Create();
        HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
        OverflowSlots := TotalSlots - 6;
        AllocSz := ((TotalSlots * 8 + 15) and (-16));
        Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
        Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);
        Self.Emit(Format(#9'movq %%rbx, 0(%%rsp)', []));
        CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
        if MD.VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
        HD.Free();
        HK.Free();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end;
    end;
    { Discarded result: free the rc=1 instance. }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Exit;
  end;

  { Discarded interface (itab) method call returning a RECORD: the callee
    follows the record-return ABI (sret pointer for a memory-class record,
    register return for a register-class one).  The plain EmitInterfaceCall
    path below treats the return as a scalar / fat pointer and hands the callee
    no sret buffer, so an sret record is written over caller memory.  Allocate
    a zeroed throwaway buffer, dispatch into it, then release its managed
    fields.  Mirrors the QBE EmitMethodCall record-discard branch. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) and
     (ACall.ResolvedReturnTypeDesc <> nil) and
     (ACall.ResolvedReturnTypeDesc.Kind = tyRecord) then
  begin
    SretRT := TRecordTypeDesc(ACall.ResolvedReturnTypeDesc);
    SretBufSize := (SretRT.TotalSize() + 15) and (-16);
    Self.Emit(#9'pushq %rbx');
    Self.Emit(Format(#9'subq $%d, %%rsp', [SretBufSize]));
    Self.Emit(#9'movq %rsp, %rbx');
    { Zero the buffer so EmitRecordFieldReleases sees nil managed fields if the
      callee leaves any unset. }
    Self.Emit(#9'movq %rbx, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx', [SretRT.TotalSize()]));
    Self.Emit(#9'callq memset');
    { EmitIntfRecordSretDispatch takes the expression form; build a transient
      TMethodCallExpr view of this statement node (the relevant fields are the
      same).  Args are borrowed and detached before Free. }
    SretShim := TMethodCallExpr.Create();
    try
      SretShim.ObjectName       := ACall.ObjectName;
      SretShim.Name             := ACall.Name;
      SretShim.Args             := ACall.Args;
      SretShim.ObjExpr          := ACall.ObjExpr;
      SretShim.ResolvedClassType := ACall.ResolvedClassType;
      SretShim.ResolvedType     := ACall.ResolvedReturnTypeDesc;
      SretShim.IsGlobal         := ACall.IsGlobal;
      SretShim.IsVarParam       := ACall.IsVarParam;
      Self.EmitIntfRecordSretDispatch(SretShim, '(%rbx)', False);
    finally
      SretShim.Args    := nil;   { borrowed — do not free }
      SretShim.ObjExpr := nil;   { borrowed — do not free }
      SretShim.Free();
    end;
    { The dispatch may clobber %rbx during arg evaluation; %rsp is balanced and
      still points at the buffer, so re-derive the buffer address. }
    Self.Emit(#9'movq %rsp, %rbx');
    Self.EmitRecordFieldReleases(SretRT, '%rbx');
    Self.Emit(Format(#9'addq $%d, %%rsp', [SretBufSize]));
    Self.Emit(#9'popq %rbx');
    Exit;
  end;

  { Interface method dispatch (statement position): route through the itab.
    Pass ObjExpr so receivers that are interface-typed fields (H.S.Note())
    load obj/itab from the field's fat pointer instead of bogus _obj/_itab
    operands built from an empty ObjectName. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    if ACall.IsImplicitSelf and (ACall.ImplicitBaseInfo <> nil) then
      Self.EmitInterfaceFieldCall(ACall.ImplicitBaseInfo,
        TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args,
        (ACall.ResolvedReturnTypeDesc <> nil) and
        (ACall.ResolvedReturnTypeDesc.Kind = tyInterface))
    else
      Self.EmitInterfaceCall(ACall.ObjectName, ACall.IsGlobal, ACall.IsVarParam,
        TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args,
        ACall.ObjExpr,
        (ACall.ResolvedReturnTypeDesc <> nil) and
        (ACall.ResolvedReturnTypeDesc.Kind = tyInterface));
    Exit;
  end;

  if (ACall.ResolvedMethod = nil) and SameText(ACall.Name, 'Free') then
  begin
    if ACall.IsImplicitSelf then
    begin
      Self.Emit(#9'movq ' + Self.VarOperand('Self') + ', %rax');
      if ACall.ImplicitBaseInfo.Offset > 0 then
        Self.Emit(Format(#9'leaq %d(%%rax), %%rax', [ACall.ImplicitBaseInfo.Offset]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq (%rax), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq $0, (%rax)');
    end
    else if ACall.ObjExpr <> nil then
    begin
      if (ACall.ObjExpr is TFieldAccessExpr) or (ACall.ObjExpr is TIdentExpr) or
         ArcIsArrayElemSlot(ACall.ObjExpr) then
      begin
        { L-value receiver (Def.ClassDef.Free(), A[I].Free()): release AND nil
          the slot.  A stale pointer left here aliases the next allocation of
          the same size class, and the following ARC field store or scope-exit
          walk double-releases it — the QBE lowering nils the slot, so must
          we. }
        Self.EmitLValueSlotAddr(ACall.ObjExpr);
        Self.Emit(#9'pushq %rdx');
        Self.Emit(#9'movq (%rdx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'movq $0, (%rdx)');
      end
      else
      begin
        Self.EmitExprToEax(ACall.ObjExpr);
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassRelease');
      end;
    end
    else if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq (%rax), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq $0, (%rax)');
    end
    else if Self.IsCaptured(ACall.ObjectName) then
    begin
      { Captured class local: release the object through the capture
        pointer and nil the OUTER slot (mirrors the var-param shape). }
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand('_cap_' + ACall.ObjectName)]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq (%rax), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq $0, (%rax)');
    end
    else
    begin
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [Self.GlobalSymName(ACall.ObjectName)]));
      Self.Emit(#9'callq _ClassRelease');
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq $0, %s(%%rip)', [Self.GlobalSymName(ACall.ObjectName)]));
    end;
    Exit;
  end;

  { Procedural-typed field call as a statement: Self.FFn(args).  Dispatch
    through the (Code, Data) pair stored in the field; no result is wanted. }
  if ACall.IsProcFieldCall then
  begin
    Self.EmitProcFieldCall(ACall.ObjExpr, ACall.ObjectName, ACall.IsVarParam,
      ACall.ProcFieldInfo, TProceduralTypeDesc(ACall.ResolvedProcType),
      ACall.Args, nil);
    Exit;
  end;

  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: TMethodCallStmt has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Static method call in statement position (TypeName.StaticMethod(args), result
    discarded): NO implicit Self.  A void/scalar-returning static method is a
    plain function call (EmitCall marshals args into %rdi.., result ignored).  A
    record-returning static factory whose result is discarded needs a throwaway
    sret buffer, dispatched via EmitSretCall, with its managed fields released. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    if (ACall.ResolvedReturnTypeDesc <> nil) and
       (ACall.ResolvedReturnTypeDesc.Kind = tyRecord) then
    begin
      SretRT      := TRecordTypeDesc(ACall.ResolvedReturnTypeDesc);
      SretBufSize := (SretRT.TotalSize() + 15) and (-16);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [SretBufSize]));
      Self.Emit(#9'movq %rsp, %rbx');
      Self.EmitSretCall(Sym, MD, ACall.Args, '(%rbx)', False);
      { EmitSretCall may have clobbered %rbx during arg evaluation; %rsp still
        points at the buffer, so re-derive its address before releasing. }
      Self.Emit(#9'movq %rsp, %rbx');
      if not Self.IsRecordManagedClean(SretRT) then
        Self.EmitRecordFieldReleases(SretRT, '%rbx');
      Self.Emit(Format(#9'addq $%d, %%rsp', [SretBufSize]));
      Self.Emit(#9'popq %rbx');
    end
    else
      Self.EmitCall(Sym, MD, ACall.Args);
    Exit;
  end;

  IsSretDiscard := (ACall.ResolvedReturnTypeDesc <> nil) and
    (ACall.ResolvedReturnTypeDesc.Kind = tyRecord) and
    (ClassifyRecordReturn(TRecordTypeDesc(ACall.ResolvedReturnTypeDesc)) = rcSret);
  SretBufSize := 0;
  SretRT      := nil;
  if IsSretDiscard then
  begin
    SretRT      := TRecordTypeDesc(ACall.ResolvedReturnTypeDesc);
    SretBufSize := (SretRT.TotalSize() + 15) and (-16);
  end;

  UserSlots  := Self.CountArgSlots(MD.Params);
  TotalSlots := UserSlots + 1;

  if TotalSlots <= 6 then
  begin
    { ≤6 total slots: push/pop strategy (Self in %rdi, args in %rsi..%r9).
      When IsSretDiscard is set, %rdi holds the throwaway buffer and Self
      shifts to %rsi, so user args start at %rdx (IntBase = 2). }
    if IsSretDiscard then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [SretBufSize]));
      Self.Emit(#9'movq %rsp, %rbx');
      Self.Emit(#9'movq %rbx, %rdi');
      Self.Emit(#9'xorl %esi, %esi');
      Self.Emit(Format(#9'movq $%d, %%rdx', [SretRT.TotalSize()]));
      Self.Emit(#9'callq memset');
    end;

    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;

    if ACall.IsImplicitSelf and (ACall.ImplicitBaseInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
      if ACall.ImplicitBaseInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%r10', [ACall.ImplicitBaseInfo.Offset]));
      if ACall.ImplicitBaseInfo.TypeDesc.Kind <> tyRecord then
        Self.Emit(#9'movq (%r10), %r10');
    end
    else if MD.IsRecordMethod and ACall.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
    else if MD.IsRecordMethod then
    begin
      if FSretFunc and SameText(ACall.ObjectName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Result')]))
      else
        Self.EmitVarAddr(ACall.ObjectName, '%r10');
    end
    else if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%r10), %r10');
    end
    else if ACall.ObjectName <> '' then
    begin
      if Self.IsCaptured(ACall.ObjectName) then
      begin
        Self.Emit(Format(#9'movq %s, %%r10',
          [Self.VarOperand('_cap_' + ACall.ObjectName)]));
        Self.Emit(#9'movq (%r10), %r10');
      end
      else if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%r10', [Self.GlobalSymName(ACall.ObjectName)]));
    end
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %r10');
    end
    else
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));

    if IsSretDiscard then
    begin
      Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 2);
      Self.Emit(#9'movq %r10, %rsi');
      Self.Emit(#9'movq %rbx, %rdi');
    end
    else
    begin
      Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
      Self.Emit(#9'movq %r10, %rdi');
    end;
  end
  else
  begin
    OverflowSlots := TotalSlots - 6;
    AllocSz := ((TotalSlots * 8 + 15) and (-16));
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));

    Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);

    if ACall.IsImplicitSelf and (ACall.ImplicitBaseInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if ACall.ImplicitBaseInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rax', [ACall.ImplicitBaseInfo.Offset]));
      if ACall.ImplicitBaseInfo.TypeDesc.Kind <> tyRecord then
        Self.Emit(#9'movq (%rax), %rax');
    end
    else if MD.IsRecordMethod and ACall.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
    else if MD.IsRecordMethod then
    begin
      if FSretFunc and SameText(ACall.ObjectName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Result')]))
      else
        Self.EmitVarAddr(ACall.ObjectName, '%rax');
    end
    else if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%rax), %rax');
    end
    else if ACall.ObjectName <> '' then
    begin
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [Self.GlobalSymName(ACall.ObjectName)]));
    end
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 0(%%rsp)', []));

    CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
  end;

  if MD.VTableSlot >= 0 then
  begin
    if IsSretDiscard then
      Self.Emit(#9'movq (%rsi), %rax')
    else
      Self.Emit(#9'movq (%rdi), %rax');
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + Sym);

  if TotalSlots > 6 then
  begin
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
  end
  else
    Self.EndCallArgs();

  if IsSretDiscard then
  begin
    if not Self.IsRecordManagedClean(SretRT) then
      Self.EmitRecordFieldReleases(SretRT, '%rbx');
    Self.Emit(Format(#9'addq $%d, %%rsp', [SretBufSize]));
    Self.Emit(#9'popq %rbx');
  end;
end;

{ Shared static-dispatch call sequence for both inherited forms.  Marshals
  Self + args and emits the direct callq to the parent method; on return the
  result (if any) is in %rax / %xmm0 per the SysV ABI.  AMD/AArgs/AName come
  from either TInheritedCallStmt or TInheritedCallExpr. }
procedure TX86_64Backend.EmitInheritedCallSeq(MD: TMethodDecl;
  AArgs: TObjectList; const AName: string);
var
  I:   Integer;
  Sym: string;
  Par: TMethodParam;
  UserSlots, TotalSlots, OverflowSlots, AllocSz, CleanUp, Dest, HTotal: Integer;
  Arg: TASTExpr;
  HD, HK: TList<Integer>;
begin
  Sym        := MethodEmitNameNative(MD, MD.OwnerTypeName, AName);
  UserSlots  := CountArgSlots(MD.Params);
  TotalSlots := UserSlots + 1;   { + Self }

  if TotalSlots <= 6 then
  begin
    { All of Self + args fit in the 6 integer arg registers: push then pop. }
    Self.BeginCallArgs(MD.Params, AArgs);
    for I := 0 to AArgs.Count - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Self.PushCallArg(Par, TASTExpr(AArgs.Items[I]), I);
    end;
    { Self is the current method's Self slot. }
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    Self.EmitPopMethodArgsToRegs(MD.Params, AArgs, 1);
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
  end
  else
  begin
    { More than 6 register slots (Self + args): the surplus must spill to the
      stack.  Build the 6 register slots + overflow region in one frame, place
      Self in slot 0, evaluate each arg into its slot, load regs 0..5, drop the
      6-register prefix so the overflow sits at the callee's [rsp+0..], then
      static-dispatch to the parent.  Mirrors EmitMethodCallStmt's >6 path
      (the inherited call is always a direct callq, never vtable). }
    OverflowSlots := TotalSlots - 6;
    AllocSz := ((TotalSlots * 8 + 15) and (-16));
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', AArgs, HD, HK);
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    Self.EmitArgsToSlots(AArgs, MD.Params, AllocSz, HTotal, HD, HK);
    { Self into slot 0 (the implicit first integer arg). }
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 0(%%rsp)', []));
    CleanUp := Self.EmitMethodOverflowLoad(MD.Params, AArgs, AllocSz);
    Self.Emit(#9'callq ' + Sym);
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
  end;
end;

procedure TX86_64Backend.EmitInheritedCall(ACall: TInheritedCallStmt);
var
  MD: TMethodDecl;
begin
  { `inherited` on TObject (no parent body) is a no-op. }
  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then Exit;

  { A record-returning parent uses the sret ABI, not a %rax value: route it
    through the sret path writing straight into the current Result slot (the
    statement form sets Result).  For an sret function that slot holds the
    buffer ADDRESS (indirect); for a register-returned record it is the buffer
    itself.  Without this the scalar store below would treat %rax as the record
    and corrupt the heap. }
  if (MD.ResolvedReturnType <> nil) and
     (MD.ResolvedReturnType.Kind = tyRecord) then
  begin
    Self.EmitInheritedRecordSret(MD, ACall.Args, ACall.Name,
      Self.VarOperand('Result'), Self.FSretFunc);
    Exit;
  end;

  Self.EmitInheritedCallSeq(MD, ACall.Args, ACall.Name);

  { A value-returning parent stores its result into the current Result slot,
    so `Result := ...` is unnecessary for `inherited F;` to set Result. }
  if (MD.ResolvedReturnType <> nil) and (MD.ResolvedReturnType.Kind <> tyVoid) then
  begin
    if IsFloatFamily(MD.ResolvedReturnType) then
      Self.EmitStoreFloat(Self.VarOperand('Result'), MD.ResolvedReturnType)
    else
      Self.EmitStoreVar(Self.VarOperand('Result'), MD.ResolvedReturnType);
  end;
end;

procedure TX86_64Backend.EmitCondBranch(AExpr: TASTExpr;
                                        const ATrueLabel, AFalseLabel: string);
var
  BE: TBinaryExpr;
  IsS: Boolean;
  HasImm: Boolean;
  ImmV: Int64;
  Unsigned: Boolean;
begin
  { Operator overloading (see EmitExprToEax): a lowered operator is not a
    comparison shape either fused path can handle — materialise it through
    the general expression emitter and test the 0/1. }
  if (AExpr is TBinaryExpr) and (TBinaryExpr(AExpr).LoweredCall <> nil) then
  begin
    Self.EmitExprToEax(AExpr);
    Self.Emit(#9'testq %rax, %rax');
    Self.Emit(#9'jne ' + ATrueLabel);
    Self.Emit(#9'jmp ' + AFalseLabel);
    Exit;
  end;
  { Float comparison: ucomisd/ucomiss sets CF/ZF directly; use conditional
    jumps that map CF/ZF to the comparison operator.  The result is a direct
    branch without materialising a 0/1 in %rax. }
  if (AExpr is TBinaryExpr) then
  begin
    BE  := TBinaryExpr(AExpr);
    if IsFloatFamily(BE.Left.ResolvedType) or IsFloatFamily(BE.Right.ResolvedType) then
    begin
      IsS := (BE.Left.ResolvedType <> nil) and (BE.Left.ResolvedType.Kind = tySingle) and
             (BE.Right.ResolvedType <> nil) and (BE.Right.ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(BE.Left);
      Self.EmitXmm0WidthAdjust(BE.Left.ResolvedType, IsS);
      Self.Emit(#9'subq $8, %rsp');
      if IsS then Self.Emit(#9'movss %xmm0, (%rsp)')
      else        Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(BE.Right);
      Self.EmitXmm0WidthAdjust(BE.Right.ResolvedType, IsS);
      if IsS then
      begin
        Self.Emit(#9'movss (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomiss %xmm0, %xmm1');
      end
      else
      begin
        Self.Emit(#9'movsd (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomisd %xmm0, %xmm1');
      end;
      { ucomisd %xmm0, %xmm1 computes xmm1 - xmm0 conceptually for flags.
        CF=1 means xmm1 < xmm0.  ZF=1 means equal. }
      case BE.Op of
        boEQ: begin Self.Emit(#9'je '  + ATrueLabel); end;
        boNE: begin Self.Emit(#9'jne ' + ATrueLabel); end;
        boLT: begin Self.Emit(#9'jb '  + ATrueLabel); end;  { below: CF }
        boGT: begin Self.Emit(#9'ja '  + ATrueLabel); end;  { above: ~CF & ~ZF }
        boLE: begin Self.Emit(#9'jbe ' + ATrueLabel); end;
        boGE: begin Self.Emit(#9'jae ' + ATrueLabel); end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float comparison operator');
      end;
      Self.Emit(#9'jmp ' + AFalseLabel);
      Exit;
    end;
  end;

  { Integer/pointer comparison as the branch condition: emit cmp + jcc
    directly instead of materialising a 0/1 via setcc/movzbl and then
    re-testing it.  Strings (content comparison via RTL call) and sets
    (subset semantics for <=/>=) keep the materialised path below. }
  if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr(AExpr);
    if (BE.Op in [boEQ, boNE, boLT, boGT, boLE, boGE]) and
       ((BE.Left.ResolvedType = nil) or
        not (BE.Left.ResolvedType.Kind in [tyString, tySet])) and
       ((BE.Right.ResolvedType = nil) or
        not (BE.Right.ResolvedType.Kind in [tyString, tySet])) then
    begin
      Self.EmitExprToEax(BE.Left);
      { An interface element of an ARRAY FIELD evaluates to its element
        ADDRESS — a comparison operand needs the obj half, or `= nil`
        compares the never-nil address (same deref as EmitExprToEax's
        materialised compare; BUG-20260721-fieldaccess-intf-array-elem-read). }
      if (BE.Left is TFieldAccessExpr) and
         TFieldAccessExpr(BE.Left).IsArrayAccess and
         (BE.Left.ResolvedType <> nil) and
         (BE.Left.ResolvedType.Kind = tyInterface) then
        Self.Emit(#9'movq (%rax), %rax');
      HasImm := Self.TryGetImmValue(BE.Right, ImmV) and
                (ImmV >= -2147483648) and (ImmV <= 2147483647);
      if (not HasImm) and (not Self.TryEmitOperandToRcx(BE.Right)) then
      begin
        if FPromoActive and FPromoPinOk and (FPinDepth = 0) then
        begin
          FPinDepth := FPinDepth + 1;
          Self.Emit(#9'movq %rax, %r13');
          Self.EmitExprToEax(BE.Right);
          if (BE.Right is TFieldAccessExpr) and
             TFieldAccessExpr(BE.Right).IsArrayAccess and
             (BE.Right.ResolvedType <> nil) and
             (BE.Right.ResolvedType.Kind = tyInterface) then
            Self.Emit(#9'movq (%rax), %rax'); { element addr -> obj half }
          Self.Emit(#9'movq %rax, %rcx');
          Self.Emit(#9'movq %r13, %rax');
          FPinDepth := FPinDepth - 1;
        end
        else
        begin
          Self.Emit(#9'pushq %rax');
          Self.EmitExprToEax(BE.Right);
          if (BE.Right is TFieldAccessExpr) and
             TFieldAccessExpr(BE.Right).IsArrayAccess and
             (BE.Right.ResolvedType <> nil) and
             (BE.Right.ResolvedType.Kind = tyInterface) then
            Self.Emit(#9'movq (%rax), %rax'); { element addr -> obj half }
          Self.Emit(#9'movq %rax, %rcx');
          Self.Emit(#9'popq %rax');
        end;
      end;
      { Width + signedness selection mirrors the materialising comparison
        path in EmitExprToEax — the two must stay in lockstep. }
      if (BE.Left.ResolvedType <> nil) and
         (BE.Left.ResolvedType.Kind in [tyInt64, tyUInt64, tyClass,
            tyPointer, tyInterface, tyString, tyDynArray, tyProcedural]) then
      begin
        if HasImm then
          Self.Emit(#9'cmpq $' + IntToStr(ImmV) + ', %rax')
        else
          Self.Emit(#9'cmpq %rcx, %rax');
      end
      else
      begin
        if HasImm then
          Self.Emit(#9'cmpl $' + IntToStr(ImmV) + ', %eax')
        else
          Self.Emit(#9'cmpl %ecx, %eax');
      end;
      Unsigned := IsUnsignedInt(BE.Left.ResolvedType) or
                  IsUnsignedInt(BE.Right.ResolvedType) or
                  ((BE.Left.ResolvedType <> nil) and
                   (BE.Left.ResolvedType.Kind in [tyPointer, tyClass,
                      tyInterface, tyString, tyDynArray, tyProcedural]));
      if Unsigned then
        case BE.Op of
          boEQ: Self.Emit(#9'je '  + ATrueLabel);
          boNE: Self.Emit(#9'jne ' + ATrueLabel);
          boLT: Self.Emit(#9'jb '  + ATrueLabel);
          boGT: Self.Emit(#9'ja '  + ATrueLabel);
          boLE: Self.Emit(#9'jbe ' + ATrueLabel);
          boGE: Self.Emit(#9'jae ' + ATrueLabel);
        end
      else
        case BE.Op of
          boEQ: Self.Emit(#9'je '  + ATrueLabel);
          boNE: Self.Emit(#9'jne ' + ATrueLabel);
          boLT: Self.Emit(#9'jl '  + ATrueLabel);
          boGT: Self.Emit(#9'jg '  + ATrueLabel);
          boLE: Self.Emit(#9'jle ' + ATrueLabel);
          boGE: Self.Emit(#9'jge ' + ATrueLabel);
        end;
      Self.Emit(#9'jmp ' + AFalseLabel);
      Exit;
    end;
  end;

  { Integer condition: evaluate to a 0/1 (or any nonzero=true) value in %eax. }
  Self.EmitExprToEax(AExpr);
  Self.Emit(#9'testq %rax, %rax');
  Self.Emit(#9'jne ' + ATrueLabel);
  Self.Emit(#9'jmp ' + AFalseLabel);
end;

procedure TX86_64Backend.EmitCondBranchFlushed(AExpr: TASTExpr;
                             const ATrueLabel, AFalseLabel: string);
var
  Mark: Integer;
begin
  { Common case: the condition cannot defer a transient base, so use the fast
    fused compare-branch (preserves the cmp+jcc optimisation). }
  if not ExprMayDeferTransientBase(AExpr) then
  begin
    Self.EmitCondBranch(AExpr, ATrueLabel, AFalseLabel);
    Exit;
  end;
  { The condition reads a class field off an owned transient — materialise it
    to a 0/1 so the deferred base can be flushed between the eval and the
    branch.  Preserve the boolean across the flush (which clobbers %rax/%rdi). }
  Mark := FPendingRelCount;
  Self.EmitExprToEax(AExpr);
  Self.Emit(#9'pushq %rax');
  Self.FlushNativePendingReleases(Mark);
  Self.Emit(#9'popq %rax');
  Self.Emit(#9'testq %rax, %rax');
  Self.Emit(#9'jne ' + ATrueLabel);
  Self.Emit(#9'jmp ' + AFalseLabel);
end;

{ ------------------------------------------------------------------ }
{ Statement lowering                                                   }
{ ------------------------------------------------------------------ }

procedure TX86_64Backend.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  I:        Integer;
  StartIdx: Integer;
  FdLit:    string;
  ArgExpr:  TASTExpr;
  K:        TTypeKind;
begin
  if ACall.Args.Count = 0 then
  begin
    if ANewline then
    begin
      Self.Emit(#9'movl $1, %edi');
      Self.Emit(#9'callq _SysWriteNewline');
    end;
    Exit;
  end;

  StartIdx := 0;
  FdLit    := '$1';
  ArgExpr  := TASTExpr(ACall.Args.Items[0]);
  if (ArgExpr is TIdentExpr) and SameText(TIdentExpr(ArgExpr).Name, 'StdErr') then
  begin
    StartIdx := 1;
    FdLit    := '$2';
  end;

  if StartIdx >= ACall.Args.Count then
  begin
    if ANewline then
    begin
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteNewline');
    end;
    Exit;
  end;

  for I := StartIdx to ACall.Args.Count - 1 do
  begin
    ArgExpr := TASTExpr(ACall.Args.Items[I]);
    if ArgExpr.ResolvedType <> nil then
      K := ArgExpr.ResolvedType.Kind
    else
      K := tyInteger;
    if K in [tyString, tyPChar] then
    begin
      Self.EmitExprToEax(ArgExpr);
      { A string argument that OWNS its reference (a call/concat result that
        returned a fresh +1 string) is borrowed by _SysWriteStr and nothing
        else holds it — release the transient after the write, or it leaks
        once per Write/WriteLn.  Stash the pointer across the call, then
        release.  Plain variables / literals / PChars are borrowed and are
        not released. }
      if (K = tyString) and ArcBuiltinStrArgOwnsRef(ArgExpr) then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteStr');
        { rc=0 transients (concat / built-in results) need the extra AddRef
          so the release actually frees — see EmitStrDisposeFromSlot. }
        if ArcExprIsUnownedStrTransient(ArgExpr) then
        begin
          Self.Emit(#9'movq (%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
        end;
        Self.Emit(#9'popq %rdi');
        Self.Emit(#9'callq _StringRelease');
      end
      else
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteStr');
      end;
    end
    else if K = tyDouble then
    begin
      Self.EmitExprToXmm0(ArgExpr);
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteDouble');
    end
    else if K = tySingle then
    begin
      Self.EmitExprToXmm0(ArgExpr);
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteSingle');
    end
    else if K = tyBoolean then
    begin
      Self.EmitExprToEax(ArgExpr);
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteBool');
    end
    else
    begin
      Self.EmitExprToEax(ArgExpr);
      if K = tyUInt64 then
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteUInt64');
      end
      else if K = tyInt64 then
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteInt64');
      end
      else if K in [tyUInt32, tyWord] then
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteUInt64');
      end
      else
      begin
        Self.Emit(#9'movl %eax, %esi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteInt');
      end;
    end;
  end;
  if ANewline then
  begin
    Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
    Self.Emit(#9'callq _SysWriteNewline');
  end;
end;

procedure TX86_64Backend.EmitForStmt(AFor: TForStmt);
var
  VarOp, EndSlot:              string;
  LCond, LBody, LNext, LEnd:  string;
  VarType:                     TTypeDesc;
  FForBoundMark:               Integer;
begin
  if Self.IsLocal(AFor.VarName) then
    VarType := Self.LocalType(AFor.VarName)
  else
  begin
    VarType := AFor.StartExpr.ResolvedType;
    Self.AddGlobal(AFor.VarName, VarType);
  end;
  VarOp   := Self.VarOperand(AFor.VarName);
  if (FFrame <> nil) and FFrame.ContainsKey('_for_end_' + IntToStr(FForEndNext)) then
  begin
    EndSlot := Self.VarOperand('_for_end_' + IntToStr(FForEndNext));
    Inc(FForEndNext);
  end
  else
  begin
    EndSlot := Self.NewLabel('forend');
    Self.AddGlobal(EndSlot, VarType);
    EndSlot := EndSlot + '(%rip)';
  end;
  LCond := Self.NewLabel('fcond');
  LBody := Self.NewLabel('fbody');
  LNext := Self.NewLabel('fnext');
  LEnd  := Self.NewLabel('fend');

  { A captured loop counter (nested-proc or anonymous-method env) lives
    behind its '_cap_' pointer slot — route every counter access through it
    so closures and the loop agree on ONE storage location. }
  FForBoundMark := FPendingRelCount;
  if Self.IsCaptured(AFor.VarName) then
  begin
    Self.EmitExprToEax(AFor.StartExpr);
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + AFor.VarName)]));
    Self.EmitStoreVar('(%rcx)', VarType);
  end
  else
  begin
    Self.EmitExprToEax(AFor.StartExpr);
    Self.EmitStoreVar(VarOp, VarType);
  end;
  Self.EmitExprToEax(AFor.EndExpr);
  Self.EmitStoreVar(EndSlot, VarType);
  { start/end bounds may read a field off a transient; both are now stored to
    slots (%rax free), and the per-iteration test only RELOADS the slots, so a
    single flush of their deferred bases suffices (BUG-049). }
  Self.FlushNativePendingReleases(FForBoundMark);

  { ROTATED loop: the condition sits at the BOTTOM — each iteration runs
    increment + compare + one taken branch back to the body, instead of a
    body-end jmp plus the top-of-loop compare-and-two-branches. }
  Self.Emit(#9'jmp ' + LCond);

  Self.Emit(LBody + ':');
  FBreakLabels.Push(LEnd);
  FBreakExcDepths.Push(FExcDepth);
  FContinueLabels.Push(LNext);
  FContinueExcDepths.Push(FExcDepth);
  Self.EmitStmt(AFor.Body);
  FContinueExcDepths.Pop();
  FContinueLabels.Pop();
  FBreakExcDepths.Pop();
  FBreakLabels.Pop();

  Self.Emit(LNext + ':');
  if Self.IsCaptured(AFor.VarName) then
  begin
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + AFor.VarName)]));
    Self.EmitLoadVar('(%rcx)', VarType);
  end
  else
    Self.EmitLoadVar(VarOp, VarType);
  if AFor.IsDownTo then
    Self.Emit(#9'subq $1, %rax')
  else
    Self.Emit(#9'addq $1, %rax');
  if Self.IsCaptured(AFor.VarName) then
  begin
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + AFor.VarName)]));
    Self.EmitStoreVar('(%rcx)', VarType);
  end
  else
    Self.EmitStoreVar(VarOp, VarType);
  Self.Emit(LCond + ':');
  if Self.IsCaptured(AFor.VarName) then
  begin
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + AFor.VarName)]));
    Self.EmitLoadVar('(%rcx)', VarType);
  end
  else
    Self.EmitLoadVar(VarOp, VarType);
  { The end value is a plain slot/global load with no side effects and no
    %rax use — straight into %rcx, no push/pop bracket. }
  Self.EmitLoadVarToReg(EndSlot, VarType, '%rcx', '%ecx');
  Self.Emit(#9'cmpq %rcx, %rax');
  if AFor.IsDownTo then
    Self.Emit(#9'jge ' + LBody)
  else
    Self.Emit(#9'jle ' + LBody);
  Self.Emit(LEnd + ':');
end;

{ ------------------------------------------------------------------ }
{ For-in and Case statements                                           }
{ ------------------------------------------------------------------ }

{ Assign the element value (already in %rax) to the for-in loop variable,
  with ARC handling for strings and classes. }
procedure TX86_64Backend.EmitForInAssignElem(AStmt: TForInStmt);
var
  VarOp: string;
  Cap:   Boolean;
begin
  { A captured for-in variable (nested-proc or anonymous-method env) lives
    behind its '_cap_' pointer slot.  %r11 (caller-saved, non-arg) carries
    the storage address and is RELOADED after every runtime call below. }
  Cap := (not AStmt.VarIsGlobal) and Self.IsCaptured(AStmt.VarName);
  if AStmt.VarIsGlobal then
    VarOp := Self.GlobalSymName(AStmt.VarName) + '(%rip)'
  else if Cap then
    VarOp := '(%r11)'
  else
    VarOp := Self.VarOperand(AStmt.VarName);
  if AStmt.ResolvedVarType.IsString() then
  begin
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _StringAddRef');
    if Cap then
      Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('_cap_' + AStmt.VarName)]));
    Self.Emit(Format(#9'movq %s, %%rdi', [VarOp]));
    Self.Emit(#9'callq _StringRelease');
    Self.Emit(#9'popq %rax');
    if Cap then
      Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('_cap_' + AStmt.VarName)]));
    Self.Emit(Format(#9'movq %%rax, %s', [VarOp]));
  end
  else if AStmt.ResolvedVarType.Kind = tyClass then
  begin
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    if Cap then
      Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('_cap_' + AStmt.VarName)]));
    Self.Emit(Format(#9'movq %s, %%rdi', [VarOp]));
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');
    if Cap then
      Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('_cap_' + AStmt.VarName)]));
    Self.Emit(Format(#9'movq %%rax, %s', [VarOp]));
  end
  else
  begin
    if Cap then
      Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('_cap_' + AStmt.VarName)]));
    Self.EmitStoreVar(VarOp, AStmt.ResolvedVarType);
  end;
end;

procedure TX86_64Backend.EmitForInAggAssignElem(AStmt: TForInStmt;
  AElemType: TTypeDesc; AElemSize: Integer);
{ %rax = address of the current array element.  Copy the whole aggregate into
  the loop variable, mirroring the record-var assignment path: retain the
  source's managed fields, release the destination's old ones, then memcpy the
  raw bytes.  A scalar load/store would truncate the element to its first 8
  bytes and skip the managed-field ARC, leaving the tail stale (issue #169). }
begin
  Self.Emit(#9'pushq %r15');
  Self.Emit(#9'pushq %rbx');
  Self.Emit(#9'movq %rax, %rbx');            { src = element address }
  Self.EmitVarAddr(AStmt.VarName, '%r15');   { dst = loop-var address }
  if AElemType.Kind = tyRecord then
  begin
    Self.EmitRecordFieldRetains(TRecordTypeDesc(AElemType), '%rbx');
    Self.EmitRecordFieldReleases(TRecordTypeDesc(AElemType), '%r15', False);
  end;
  Self.Emit(#9'movq %r15, %rdi');
  Self.Emit(#9'movq %rbx, %rsi');
  Self.Emit(Format(#9'movq $%d, %%rdx', [AElemSize]));
  Self.Emit(#9'callq memcpy');
  Self.Emit(#9'popq %rbx');
  Self.Emit(#9'popq %r15');
end;

procedure TX86_64Backend.EmitForInStmt(AStmt: TForInStmt);
var
  LCond, LBody, LNext, LEnd: string;
  IdxOp:     string;
  SAT:       TStaticArrayTypeDesc;
  DAT:       TDynArrayTypeDesc;
  ElemSize:  Integer;
  GetEDecl, MNDecl, CurDecl: TMethodDecl;
  EnumOp, Sym: string;
  SlotOff:   Integer;
  CurRT:     TRecordTypeDesc;
  SynthCur:  TMethodCallExpr;
begin
  if AStmt.IsArrayIter then
  begin
    { ---- Static array iteration ----
      idx runs ArrayLow..ArrayHigh (inclusive).  Element address =
      base + (idx - ArrayLow) * ElemSize. }
    SAT      := TStaticArrayTypeDesc(AStmt.CollExpr.ResolvedType);
    ElemSize := SAT.ElementType.RawSize();
    IdxOp    := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    { Initialise index to ArrayLow }
    Self.Emit(Format(#9'movl $%d, %%eax', [AStmt.ArrayLow]));
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(Format(#9'cmpl $%d, %%eax', [AStmt.ArrayHigh]));
    Self.Emit(#9'jle ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Compute element address: base + (idx - ArrayLow) * ElemSize }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.Emit(Format(#9'movslq %s, %%rax', [IdxOp]));
    if AStmt.ArrayLow <> 0 then
      Self.Emit(Format(#9'subq $%d, %%rax', [AStmt.ArrayLow]));
    Self.Emit(Format(#9'imulq $%d, %%rax, %%rax', [ElemSize]));
    Self.Emit(#9'addq %rcx, %rax');
    if (SAT.ElementType.Kind = tyRecord) or (SAT.ElementType.RawSize() > 8) then
      { %rax = element address; copy the aggregate by value. }
      Self.EmitForInAggAssignElem(AStmt, SAT.ElementType, ElemSize)
    else
    begin
      { Load element from (%rax) }
      case ElemSize of
        1: if IsUnsignedInt(SAT.ElementType) then
             Self.Emit(#9'movzbq (%rax), %rax')
           else
             Self.Emit(#9'movsbq (%rax), %rax');
        2: if IsUnsignedInt(SAT.ElementType) then
             Self.Emit(#9'movzwq (%rax), %rax')
           else
             Self.Emit(#9'movswq (%rax), %rax');
        4: Self.Emit(#9'movslq (%rax), %rax');
      else
        Self.Emit(#9'movq (%rax), %rax');
      end;
      Self.EmitForInAssignElem(AStmt);
    end;

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsDynArrayIter then
  begin
    { ---- Dynamic array iteration ----
      idx runs 0.._DynArrayLength(ptr)-1.  Element address =
      data_ptr + idx * ElemSize. }
    DAT      := TDynArrayTypeDesc(AStmt.CollExpr.ResolvedType);
    ElemSize := DAT.ElementType.RawSize();
    IdxOp    := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    { Get length via _DynArrayLength }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _DynArrayLength');
    Self.Emit(#9'movl %eax, %ecx');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'cmpl %ecx, %eax');
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Element address: data_ptr + idx * ElemSize }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.Emit(Format(#9'movslq %s, %%rax', [IdxOp]));
    Self.Emit(Format(#9'imulq $%d, %%rax, %%rax', [ElemSize]));
    Self.Emit(#9'addq %rcx, %rax');
    if (DAT.ElementType.Kind = tyRecord) or (DAT.ElementType.RawSize() > 8) then
      { %rax = element address; copy the aggregate by value. }
      Self.EmitForInAggAssignElem(AStmt, DAT.ElementType, ElemSize)
    else
    begin
      case ElemSize of
        1: if IsUnsignedInt(DAT.ElementType) then
             Self.Emit(#9'movzbq (%rax), %rax')
           else
             Self.Emit(#9'movsbq (%rax), %rax');
        2: if IsUnsignedInt(DAT.ElementType) then
             Self.Emit(#9'movzwq (%rax), %rax')
           else
             Self.Emit(#9'movswq (%rax), %rax');
        4: Self.Emit(#9'movslq (%rax), %rax');
      else
        Self.Emit(#9'movq (%rax), %rax');
      end;
      Self.EmitForInAssignElem(AStmt);
    end;

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsCodePointIter then
  begin
    { ---- String codepoint-iteration ----
      Calls _Utf8DecodeAt(strptr, byteIdx) which returns packed Int64:
        low 32 bits = codepoint, high 32 bits = byte advance (1-4).
      Advance is stored in a synthetic __adv_N slot to survive the body. }
    IdxOp := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movl -8(%rax), %ecx');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'cmpl %ecx, %eax');
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'movl %s, %%esi', [IdxOp]));
    Self.Emit(#9'callq _Utf8DecodeAt');
    Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(AStmt.VarName)]));
    Self.Emit(#9'shrq $32, %rax');
    Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(AStmt.AdvVarName)]));

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(Format(#9'addl %s, %%eax', [Self.VarOperand(AStmt.AdvVarName)]));
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsStringIter then
  begin
    { ---- String byte-iteration ----
      String data pointer layout: [data...]
      Length at data_ptr - 8 (4-byte integer).
      idx runs 0..length-1.  Element = byte at data_ptr + idx. }
    IdxOp := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    { Load string length from data_ptr - 8 }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movl -8(%rax), %ecx');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'cmpl %ecx, %eax');
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Load byte at data_ptr + idx }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.Emit(Format(#9'movslq %s, %%rax', [IdxOp]));
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movzbq (%rax), %rax');
    Self.EmitForInAssignElem(AStmt);

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsSetIter then
  begin
    { ---- Set iteration ----
      Evaluate set expression once into mask slot.  Iterate bit positions
      0..SetBitCount-1.  For each set bit, assign the ordinal to the loop
      variable and run the body. }
    IdxOp := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    { Evaluate set expression once }
    Self.EmitExprToEax(AStmt.CollExpr);
    if AStmt.SetBitCount > 32 then
    begin
      Self.Emit(Format(#9'movq %%rax, %s',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
    end
    else
    begin
      Self.Emit(Format(#9'movl %%eax, %s',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
    end;
    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(Format(#9'cmpl $%d, %%eax', [AStmt.SetBitCount]));
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    { Test bit: jumbo via _SetIn(set_addr, idx); else (mask >> idx) & 1 }
    if AStmt.SetIsJumbo then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.VarOperand(AStmt.SetMaskVarName)]));   { set bitmap addr }
      Self.Emit(Format(#9'movl %s, %%esi', [IdxOp]));
      Self.Emit(#9'callq _SetIn');
      Self.Emit(#9'testl %eax, %eax');
    end
    else if AStmt.SetBitCount > 32 then
    begin
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
      Self.Emit(Format(#9'movl %s, %%ecx', [IdxOp]));
      Self.Emit(#9'shrq %cl, %rax');
      Self.Emit(#9'andq $1, %rax');
      Self.Emit(#9'testq %rax, %rax');
    end
    else
    begin
      Self.Emit(Format(#9'movl %s, %%eax',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
      Self.Emit(Format(#9'movl %s, %%ecx', [IdxOp]));
      Self.Emit(#9'shrl %cl, %eax');
      Self.Emit(#9'andl $1, %eax');
      Self.Emit(#9'testl %eax, %eax');
    end;
    Self.Emit(#9'jne ' + LBody + '_yes');
    Self.Emit(#9'jmp ' + LNext);
    Self.Emit(LBody + '_yes:');

    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Assign ordinal (idx) to loop variable }
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.EmitForInAssignElem(AStmt);

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  { ---- Class enumerator protocol ----
    GetEnumerator → enumerator object (ARC'd).
    while MoveNext do LoopVar := Current. }
  LCond := Self.NewLabel('ficond');
  LBody := Self.NewLabel('fibody');
  LEnd  := Self.NewLabel('fiend');
  GetEDecl := TMethodDecl(AStmt.GetEnumDecl);
  MNDecl   := TMethodDecl(AStmt.MoveNextDecl);
  CurDecl  := TMethodDecl(AStmt.CurrentDecl);
  EnumOp   := Self.VarOperand(AStmt.EnumVarName);

  { Call GetEnumerator on the collection }
  Self.EmitExprToEax(AStmt.CollExpr);
  Self.Emit(#9'movq %rax, %rdi');
  Sym := MethodEmitNameNative(GetEDecl, GetEDecl.OwnerTypeName, GetEDecl.Name);
  if GetEDecl.VTableSlot >= 0 then
  begin
    SlotOff := (GetEDecl.VTableSlot + 1) * 8;
    Self.Emit(#9'movq (%rdi), %rcx');
    Self.Emit(Format(#9'movq %d(%%rcx), %%r10', [SlotOff]));
    Self.Emit(#9'callq *%r10');
  end
  else
    Self.Emit(#9'callq ' + Sym);

  { Move the enumerator into the synthetic slot.  GetEnumerator's
    result is an owned +1 (constructor/call result) — transfer it;
    an extra AddRef here leaks one enumerator per loop because the
    function epilogue releases the slot exactly once. }
  Self.Emit(#9'pushq %rax');
  Self.Emit(Format(#9'movq %s, %%rdi', [EnumOp]));
  Self.Emit(#9'callq _ClassRelease');
  Self.Emit(#9'popq %rax');
  Self.Emit(Format(#9'movq %%rax, %s', [EnumOp]));

  { Condition: call MoveNext }
  Self.Emit(LCond + ':');
  Self.Emit(Format(#9'movq %s, %%rdi', [EnumOp]));
  Sym := MethodEmitNameNative(MNDecl, MNDecl.OwnerTypeName, MNDecl.Name);
  if MNDecl.VTableSlot >= 0 then
  begin
    SlotOff := (MNDecl.VTableSlot + 1) * 8;
    Self.Emit(#9'movq (%rdi), %rcx');
    Self.Emit(Format(#9'movq %d(%%rcx), %%r10', [SlotOff]));
    Self.Emit(#9'callq *%r10');
  end
  else
    Self.Emit(#9'callq ' + Sym);
  Self.Emit(#9'testl %eax, %eax');
  Self.Emit(#9'jne ' + LBody);
  Self.Emit(#9'jmp ' + LEnd);

  { Body: read Current, assign to loop var }
  Self.Emit(LBody + ':');
  FBreakLabels.Push(LEnd);
  FBreakExcDepths.Push(FExcDepth);
  FContinueLabels.Push(LCond);
  FContinueExcDepths.Push(FExcDepth);

  if CurDecl.ResolvedReturnType.Kind = tyRecord then
  begin
    { Record-returning Current: sret the getter straight into the loop-var
      slot after releasing the previous entry, exactly as `V := Enum.Current`
      lowers (the record-method-call assignment path).  A scalar-return call
      would use the wrong ABI and corrupt the managed fields. }
    CurRT := TRecordTypeDesc(CurDecl.ResolvedReturnType);
    SynthCur := TMethodCallExpr.Create();
    try
      SynthCur.Name           := CurDecl.Name;
      SynthCur.ResolvedMethod := CurDecl;
      SynthCur.ResolvedType   := CurDecl.ResolvedReturnType;
      SynthCur.ObjectName     := AStmt.EnumVarName;
      SynthCur.IsGlobal       := False;
      Self.Emit(#9'pushq %rbx');
      Self.EmitVarAddr(AStmt.VarName, '%rbx');
      Self.EmitRecordFieldReleases(CurRT, '%rbx');
      Self.EmitMethodSretCall(SynthCur, '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
    finally
      SynthCur.Free();
    end;
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%rdi', [EnumOp]));
    Sym := MethodEmitNameNative(CurDecl, CurDecl.OwnerTypeName, CurDecl.Name);
    if CurDecl.VTableSlot >= 0 then
    begin
      SlotOff := (CurDecl.VTableSlot + 1) * 8;
      Self.Emit(#9'movq (%rdi), %rcx');
      Self.Emit(Format(#9'movq %d(%%rcx), %%r10', [SlotOff]));
      Self.Emit(#9'callq *%r10');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EmitForInAssignElem(AStmt);
  end;

  Self.EmitStmt(AStmt.Body);
  FContinueExcDepths.Pop();
  FContinueLabels.Pop();
  FBreakExcDepths.Pop();
  FBreakLabels.Pop();

  Self.Emit(#9'jmp ' + LCond);
  Self.Emit(LEnd + ':');
end;

procedure TX86_64Backend.EmitCaseStmt(AStmt: TCaseStmt);
var
  EndLbl, ElseLbl, BranchLbl, NextLbl: string;
  Branch:       TCaseBranch;
  I, J:         Integer;
  BranchLabels: TStringList;
  CaseSelMark:  Integer;
begin
  { Evaluate selector once, keep in %rax, save to %r10 (caller-saved scratch). }
  CaseSelMark := FPendingRelCount;
  Self.EmitExprToEax(AStmt.Selector);
  Self.Emit(#9'movq %rax, %r10');
  { the selector may read a field off a transient; it is now safe in %r10, so
    flush its deferred base (flush clobbers %rax/%rdi, not %r10).  Evaluated
    once (BUG-049). }
  Self.FlushNativePendingReleases(CaseSelMark);

  EndLbl  := Self.NewLabel('csend');
  ElseLbl := Self.NewLabel('cselse');

  BranchLabels := TStringList.Create();
  for I := 0 to AStmt.Branches.Count - 1 do
    BranchLabels.Add(Self.NewLabel('csbr'));

  { Dispatch block: linear chain of comparisons.  For each branch, test all
    its values; on any match, jump to that branch body.  On no match for
    any branch, fall through to the else block. }
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Branch    := TCaseBranch(AStmt.Branches.Items[I]);
    BranchLbl := BranchLabels.Strings[I];
    for J := 0 to Branch.Values.Count - 1 do
    begin
      NextLbl := Self.NewLabel('csnxt');
      if TASTExpr(Branch.Values.Items[J]) is TSetRangeExpr then
      begin
        { Range label lo..hi: match when (sel >= lo) and (sel <= hi).  Signed
          ordinal comparison; selector stays in %r10 across both bound evals. }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TSetRangeExpr(Branch.Values.Items[J]).LowExpr);
        Self.Emit(#9'movl %eax, %ecx');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'cmpl %ecx, %r10d');
        Self.Emit(#9'jl ' + NextLbl);        { sel < lo -> no match }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TSetRangeExpr(Branch.Values.Items[J]).HighExpr);
        Self.Emit(#9'movl %eax, %ecx');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'cmpl %ecx, %r10d');
        Self.Emit(#9'jg ' + NextLbl);        { sel > hi -> no match }
        Self.Emit(#9'jmp ' + BranchLbl);
      end
      else if AStmt.IsStringCase then
      begin
        { String comparison: call _StringEquals(selector, value) }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TASTExpr(Branch.Values.Items[J]));
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'movq %r10, %rdi');
        Self.Emit(#9'pushq %r10');
        Self.Emit(#9'callq _StringEquals');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'testl %eax, %eax');
        Self.Emit(#9'jne ' + BranchLbl);
        Self.Emit(#9'jmp ' + NextLbl);
      end
      else
      begin
        { Integer/enum comparison }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TASTExpr(Branch.Values.Items[J]));
        Self.Emit(#9'movl %eax, %ecx');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'cmpl %ecx, %r10d');
        Self.Emit(#9'je ' + BranchLbl);
        Self.Emit(#9'jmp ' + NextLbl);
      end;
      Self.Emit(NextLbl + ':');
    end;
  end;
  Self.Emit(#9'jmp ' + ElseLbl);

  { Branch bodies }
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Branch    := TCaseBranch(AStmt.Branches.Items[I]);
    BranchLbl := BranchLabels.Strings[I];
    Self.Emit(BranchLbl + ':');
    Self.EmitStmt(Branch.Stmt);
    Self.Emit(#9'jmp ' + EndLbl);
  end;

  { Else block }
  Self.Emit(ElseLbl + ':');
  if AStmt.ElseStmt <> nil then
    Self.EmitStmt(AStmt.ElseStmt);
  Self.Emit(#9'jmp ' + EndLbl);

  Self.Emit(EndLbl + ':');
  BranchLabels.Free();
end;

{ ------------------------------------------------------------------ }
{ Exception handling                                                   }
{ ------------------------------------------------------------------ }

function TX86_64Backend.CountTryStmts(AStmt: TASTStmt): Integer;
var
  I:    Integer;
  TFS:  TTryFinallyStmt;
  TES:  TTryExceptStmt;
  Cmp:  TCompoundStmt;
  IfS:  TIfStmt;
  WhS:  TWhileStmt;
  ForS: TForStmt;
  RepS: TRepeatStmt;
  H:    TExceptHandlerClause;
begin
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    Result := 1;
    for I := 0 to TFS.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TFS.TryBody.Stmts.Items[I]));
    for I := 0 to TFS.FinallyBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TFS.FinallyBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    Result := 1;
    for I := 0 to TES.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TES.TryBody.Stmts.Items[I]));
    for I := 0 to TES.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(TES.Handlers.Items[I]);
      Result := Result + Self.CountTryStmts(H.Body);
    end;
    if TES.ElseBody <> nil then
      for I := 0 to TES.ElseBody.Stmts.Count - 1 do
        Result := Result + Self.CountTryStmts(TASTStmt(TES.ElseBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(Cmp.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    IfS := TIfStmt(AStmt);
    Exit(Self.CountTryStmts(IfS.ThenStmt) + Self.CountTryStmts(IfS.ElseStmt));
  end;
  if AStmt is TWhileStmt then
  begin
    WhS := TWhileStmt(AStmt);
    Exit(Self.CountTryStmts(WhS.Body));
  end;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    Exit(Self.CountTryStmts(ForS.Body));
  end;
  if AStmt is TRepeatStmt then
  begin
    RepS := TRepeatStmt(AStmt);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(RepS.Body.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TForInStmt then
    Exit(Self.CountTryStmts(TForInStmt(AStmt).Body));
  if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      Result := Result + Self.CountTryStmts(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt);
    Result := Result + Self.CountTryStmts(TCaseStmt(AStmt).ElseStmt);
    Exit;
  end;
end;

function TX86_64Backend.CountForStmts(AStmt: TASTStmt): Integer;
var
  I:    Integer;
  TFS:  TTryFinallyStmt;
  TES:  TTryExceptStmt;
  Cmp:  TCompoundStmt;
  IfS:  TIfStmt;
  WhS:  TWhileStmt;
  ForS: TForStmt;
  RepS: TRepeatStmt;
  H:    TExceptHandlerClause;
begin
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    for I := 0 to TFS.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(TFS.TryBody.Stmts.Items[I]));
    for I := 0 to TFS.FinallyBody.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(TFS.FinallyBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    for I := 0 to TES.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(TES.TryBody.Stmts.Items[I]));
    for I := 0 to TES.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(TES.Handlers.Items[I]);
      Result := Result + Self.CountForStmts(H.Body);
    end;
    if TES.ElseBody <> nil then
      for I := 0 to TES.ElseBody.Stmts.Count - 1 do
        Result := Result + Self.CountForStmts(TASTStmt(TES.ElseBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(Cmp.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    IfS := TIfStmt(AStmt);
    Exit(Self.CountForStmts(IfS.ThenStmt) + Self.CountForStmts(IfS.ElseStmt));
  end;
  if AStmt is TWhileStmt then
  begin
    WhS := TWhileStmt(AStmt);
    Exit(Self.CountForStmts(WhS.Body));
  end;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    Exit(1 + Self.CountForStmts(ForS.Body));
  end;
  if AStmt is TRepeatStmt then
  begin
    RepS := TRepeatStmt(AStmt);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(RepS.Body.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TForInStmt then
    Exit(Self.CountForStmts(TForInStmt(AStmt).Body));
  if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      Result := Result + Self.CountForStmts(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt);
    Result := Result + Self.CountForStmts(TCaseStmt(AStmt).ElseStmt);
    Exit;
  end;
end;

{ Unwind exception frames from FExcDepth down to ATargetDepth+1.
  For each frame: pop it; if it is a try/finally frame, also emit the
  finally body inline.  try/except frames have a nil FFinallyStack entry. }
procedure TX86_64Backend.EmitExcUnwind(ATargetDepth: Integer);
var
  I, J:    Integer;
  FinBody: TCompoundStmt;
begin
  for I := FExcDepth downto ATargetDepth + 1 do
  begin
    Self.Emit(#9'callq _PopExcFrame');
    if I - 1 < FFinallyStack.Count then
    begin
      FinBody := FFinallyStack.Get(I - 1);
      if FinBody <> nil then
        Self.EmitStmtList(FinBody.Stmts);
    end;
  end;
end;

procedure TX86_64Backend.EnsureExcFrameSlot(AIndex: Integer; const AName: string);
begin
  { Finally bodies are emitted more than once (normal path, exception path,
    and every non-local-exit unwind site), so a try nested inside a finally
    body consumes more frame slots than the source-level pre-counts provide.
    Grow lazily: for a framed function the prologue's frame-reserve subq is
    emitted after the body (EmitFunctionCore), and for a frameless context
    (program main / unit init) the _exc_frame_N .bss labels are emitted in
    EmitDataSection after all code — both cover late slots. }
  if FFrame = nil then
  begin
    if AIndex >= FProgExcFrameCount then
      FProgExcFrameCount := AIndex + 1;
    Exit;
  end;
  if FFrame.ContainsKey(AName) then Exit;
  Inc(FFrameBottom, 512);
  FFrameBottom := (FFrameBottom + 15) and (-16);
  FFrame.Add(AName, -FFrameBottom);
  FFrameTypes.Add(AName, nil);
  FFrameSize := (FFrameBottom + 15) and (-16);
end;

procedure TX86_64Backend.EmitTryFramePrologue(AFinallyBody: TCompoundStmt;
  const ALblExc, ALblTry: string);
var
  FrameSlot: string;
begin
  { Use the next pre-allocated 512-byte frame slot from BuildFrame, or grow
    the frame if the pre-count ran out (try inside a finally body). }
  FrameSlot := '_exc_frame_' + IntToStr(FExcFrameNext);
  Self.EnsureExcFrameSlot(FExcFrameNext, FrameSlot);
  Inc(FExcFrameNext);

  { _PushExcFrame wants the frame base address in %rdi. }
  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _PushExcFrame');
  Inc(FExcDepth);
  FFinallyStack.Add(AFinallyBody);

  { _blaise_setjmp(frame): returns 0 on normal entry, 1 on exception longjmp. }
  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _blaise_setjmp');
  Self.Emit(#9'testl %eax, %eax');
  Self.Emit(#9'jnz ' + ALblExc);
  Self.Emit(#9'jmp ' + ALblTry);
end;

procedure TX86_64Backend.EmitPopExcFrame;
begin
  Self.Emit(#9'callq _PopExcFrame');
  Dec(FExcDepth);
  FFinallyStack.Delete(FFinallyStack.Count - 1);
end;

procedure TX86_64Backend.EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
var
  LblTry:    string;
  LblFinExc: string;
  LblEnd:    string;
begin
  LblTry    := Self.NewLabel('try_body');
  LblFinExc := Self.NewLabel('fin_exc');
  LblEnd    := Self.NewLabel('fin_end');

  Self.EmitTryFramePrologue(AStmt.FinallyBody, LblFinExc, LblTry);

  { Normal path: run try body, pop frame, run finally, done. }
  Self.Emit(LblTry + ':');
  Self.EmitStmtList(AStmt.TryBody.Stmts);
  Self.EmitPopExcFrame();
  Self.EmitStmtList(AStmt.FinallyBody.Stmts);
  Self.Emit(#9'jmp ' + LblEnd);

  { Exception path: capture exception, pop frame, run finally, re-raise.
    Restore FExcDepth to the try-entry level so the exception-path codegen
    sees the same depth as the normal path (both paths execute at codegen time
    even though only one runs at runtime). }
  Inc(FExcDepth);
  FFinallyStack.Add(AStmt.FinallyBody);
  Self.Emit(LblFinExc + ':');
  Self.Emit(#9'callq _CurrentException');
  Self.Emit(#9'pushq %rax');   { save exception pointer across finally body }
  Self.EmitPopExcFrame();
  Self.EmitStmtList(AStmt.FinallyBody.Stmts);
  Self.Emit(#9'popq %rdi');    { restore saved exception }
  Self.Emit(#9'callq _Reraise');
  Self.Emit(#9'jmp ' + LblEnd);  { unreachable; satisfies assembler block exit }

  Self.Emit(LblEnd + ':');
end;

procedure TX86_64Backend.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblTry:    string;
  LblExcept: string;
  LblEnd:    string;
  LblBody:   string;
  LblNext:   string;
  I:         Integer;
  H:         TExceptHandlerClause;
begin
  LblTry    := Self.NewLabel('try_body');
  LblExcept := Self.NewLabel('except_handler');
  LblEnd    := Self.NewLabel('except_end');

  { Push nil so FFinallyStack stays index-aligned with FExcDepth.
    A non-local exit crossing a try/except frame only pops it — no body to run. }
  Self.EmitTryFramePrologue(nil, LblExcept, LblTry);

  { Normal path: run try body, pop frame on clean exit. }
  Self.Emit(LblTry + ':');
  Self.EmitStmtList(AStmt.TryBody.Stmts);
  Self.EmitPopExcFrame();
  Self.Emit(#9'jmp ' + LblEnd);

  { Exception path: dispatch handlers.
    Restore codegen-time FExcDepth/FFinallyStack to the try-entry level so
    the exception path sees the same bookkeeping state (both paths execute at
    codegen time even though only one runs at runtime). }
  Inc(FExcDepth);
  FFinallyStack.Add(nil);
  Self.Emit(LblExcept + ':');

  if AStmt.Handlers.Count > 0 then
  begin
    { Capture current exception while our frame is still on the stack. }
    Self.Emit(#9'callq _CurrentException');
    Self.Emit(#9'pushq %rax');   { save exception across _PopExcFrame }
    Self.EmitPopExcFrame();
    Self.Emit(#9'popq %r15');    { exception in %r15 (callee-saved — survives handler bodies) }

    for I := 0 to AStmt.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(AStmt.Handlers[I]);
      LblBody := Self.NewLabel('exc_handler_body');
      LblNext := Self.NewLabel('exc_handler_next');

      { _IsInstance(obj, typeinfo): returns non-zero if obj is an instance of the type. }
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'leaq typeinfo_' + Self.ClassSymName(H.TypeName) + '(%rip), %rsi');
      Self.Emit(#9'callq _IsInstance');
      Self.Emit(#9'testl %eax, %eax');
      Self.Emit(#9'jnz ' + LblBody);
      Self.Emit(#9'jmp ' + LblNext);

      Self.Emit(LblBody + ':');
      if H.VarName <> '' then
      begin
        { Retain the exception to balance the scope-exit release (the handler
          var is a class local; EmitFunctionDef will emit a release at epilogue
          only for string vars, but we retain here to match QBE backend ARC).
          Release any PRIOR binding first — the slot is shared by every
          same-named handler in the function.
          The handler var slot is a pre-declared local: assign %r15 into it. }
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        if Self.IsLocal(H.VarName) then
          Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(H.VarName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [Self.GlobalSymName(H.VarName)]));
        Self.Emit(#9'callq _ClassRelease');
        if Self.IsLocal(H.VarName) then
          Self.Emit(Format(#9'movq %%r15, %s', [Self.VarOperand(H.VarName)]))
        else
          Self.Emit(Format(#9'movq %%r15, %s(%%rip)', [Self.GlobalSymName(H.VarName)]));
      end;
      Self.EmitStmtList(H.Body.Stmts);
      { A handler with NO variable owns disposal too: the exception is created
        rc=0 and only borrowed, so with no handler-var slot to release it at
        scope exit it would be orphaned (BUG-20260720-exception-object-leak).
        Balanced AddRef/Release (0->1->0) frees it + deregisters from the tracker
        (%r15 holds the exception, callee-saved across the body). }
      if H.VarName = '' then
      begin
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'callq _ClassRelease');
      end;
      Self.Emit(#9'jmp ' + LblEnd);

      Self.Emit(LblNext + ':');
    end;

    { No handler matched: run else body if any, otherwise re-raise. }
    if AStmt.ElseBody <> nil then
    begin
      Self.EmitStmtList(AStmt.ElseBody.Stmts);
      { The else branch HANDLES without a variable — dispose the exception.
        (The re-raise path below forwards the borrow — must NOT dispose.) }
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'jmp ' + LblEnd);
    end
    else
    begin
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'callq _Reraise');
      Self.Emit(#9'jmp ' + LblEnd);
    end;
  end
  else
  begin
    { Plain catch-all except body.  Capture the borrowed exception into a
      callee-saved reg BEFORE popping the frame, so it can be disposed after the
      body (BUG-20260720-exception-object-leak). }
    Self.Emit(#9'pushq %r15');
    Self.Emit(#9'callq _CurrentException');
    Self.Emit(#9'movq %rax, %r15');
    Self.EmitPopExcFrame();
    Self.EmitStmtList(AStmt.ExceptBody.Stmts);
    Self.Emit(#9'movq %r15, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(#9'movq %r15, %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %r15');
    Self.Emit(#9'jmp ' + LblEnd);
  end;

  Self.Emit(LblEnd + ':');
end;

procedure TX86_64Backend.EmitRaiseStmt(AStmt: TRaiseStmt);
begin
  if AStmt.Expr <> nil then
  begin
    { NOTE (BUG-049): a raise operand that reads a class field off an owned
      transient (raise MakeFactory().ExcField) is NOT flushed here.  The
      exception object aliases the transient's graph and ESCAPES via the
      exception machinery, so releasing the transient would free the in-flight
      exception (UAF) — and AddRef-pinning it to compensate then leaks it after
      the handler (the exception system frees only its own +1).  Getting both
      right needs the exception machinery to adopt the operand's ownership,
      which is out of scope here.  The deferred base simply stays in its
      _pendrel slot (leaked, as before this fix) — never a UAF.  This exotic
      shape is the sole residual of BUG-049; the common contexts (conditions,
      loops, call arguments) are all flushed and leak-free. }
    Self.EmitExprToEax(AStmt.Expr);
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _Raise');
  end
  else
  begin
    { Bare re-raise: retrieve the current exception then re-raise it. }
    Self.Emit(#9'callq _CurrentException');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _Reraise');
  end;
end;

procedure TX86_64Backend.EmitStmtList(AList: TObjectList);
var
  I: Integer;
begin
  if AList = nil then Exit;
  for I := 0 to AList.Count - 1 do
    Self.EmitStmt(TASTStmt(AList.Items[I]));
end;

procedure TX86_64Backend.EmitStaticElemScale(ASAT: TStaticArrayTypeDesc);
begin
  if ASAT.LowBound <> 0 then
    Self.Emit(Format(#9'subq $%d, %%rax', [ASAT.LowBound]));
  Self.Emit(Format(#9'imulq $%d, %%rax', [ASAT.ElementType.RawSize()]));
end;

procedure TX86_64Backend.EmitSretBufferSlideDown(AHoistTotal: Integer);
begin
  if AHoistTotal > 0 then
  begin
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(#9'movq 8(%rsp), %rcx');
    Self.Emit(Format(#9'addq $%d, %%rsp', [16 + AHoistTotal]));
    Self.Emit(#9'pushq %rcx');
    Self.Emit(#9'pushq %rax');
  end;
end;

procedure TX86_64Backend.EmitStmt(AStmt: TASTStmt);
var
  Mark: Integer;
begin
  { Statement-scoped deferred-release boundary (BUG-003/BUG-049).  A class
    field read on an owned transient base spills that base to a _pendrel slot
    (see the field-read emitter) instead of releasing it inline (use-after-
    free) or pinning the field (leak).  Bracketing EVERY statement flushes
    those deferred bases at the statement boundary, AFTER the borrowed field
    value has been consumed — closing the leak in every statement context
    (assignment, call argument, if-body, …), not just leaf assignments.
    Control-flow / compound statements recurse into EmitStmtBody -> EmitStmt
    for their child leaves, each of which flushes its own; a LOOP condition
    additionally flushes per iteration inside its emitter (the single post-
    body flush here would only release the last iteration's deferred base).
    Statements whose emitter ends in a non-returning call (Raise) flush before
    that call in their own emitter, since this post-body flush is dead code
    there. }
  Mark := FPendingRelCount;
  Self.EmitStmtBody(AStmt);
  Self.FlushNativePendingReleases(Mark);
end;

procedure TX86_64Backend.EmitStmtBody(AStmt: TASTStmt);
var
  PC:    TProcCall;
  Comp:  TCompoundStmt;
  IfS:   TIfStmt;
  WhileS: TWhileStmt;
  RepS:  TRepeatStmt;
  Asgn:  TAssignment;
  FA:    TFieldAssignment;
  LNilStore, LSkipAdd, LDone: string;
  CVStore: TAssignment;
  FAE:   TFieldAccessExpr;
  SSA:   TStaticSubscriptAssign;
  MD:    TMethodDecl;
  DAElemType: TTypeDesc;
  I:     Integer;
  LThen, LElse, LEnd:    string;
  LCond, LBody:          string;
  FDynArgName: string;
  FDynElemSz:  Integer;
  SetLValAddr: TAddrOfExpr;
  SetWide:     Boolean;
  ISFld:   TFieldInfo;
  IntfArgs: TObjectList;
  PCUserSlots, PCTotalSlots, PCOverflow, PCCleanUp, PCAllocSz, PCDest: Integer;
  PCHD, PCHK: TList<Integer>;
  PCHTotal: Integer;
  AliasBuf: Integer;
  AliasSz:  Integer;
  DiscBufSz: Integer;
  DiscShim: TFuncCallExpr;
  PropRelStr: Boolean;
begin
  { An empty statement (e.g. the body of `for x := 0 to N do;`) parses to a nil
    statement — the parser's convention for "no statement here".  It is a valid,
    do-nothing body, so emit nothing.  Without this guard the unsupported-
    statement fallback at the tail dereferences AStmt.ClassName and segfaults. }
  if AStmt = nil then
    Exit;
  Self.DbgStmtLabel(AStmt);
  if AStmt is TAsmStmt then
  begin
    { Inline assembler: emit the verbatim block.  The internal/external
      assembler parses it; the front end never did. }
    Self.Emit(TAsmStmt(AStmt).Code);
    Exit;
  end;
  if AStmt is TAssignment then
  begin
    Asgn := TAssignment(AStmt);
    { Implicit-Self field assignment (bare `FName := x` inside a method) must be
      resolved as a field of Self, NOT as a variable named FName — otherwise the
      managed-type branches below would treat it as a global/local and write to
      the wrong slot.  Interface fields are excluded here: EmitInterfaceAssign
      (reached via the tyInterface branch) already handles ImplicitSelfField. }
    if (Asgn.ImplicitSelfField <> nil) and
       (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind <> tyInterface) then
    begin
      ISFld := TFieldInfo(Asgn.ImplicitSelfField);
      { Method-pointer field via implicit Self (bare FFn := @Obj.Method): store
        the [CodePtr, ObjPtr] pair into the field's 16-byte slot.  Checked before
        the ARC/generic stores below, which would route the RHS through
        EmitExprToEax(@Obj.Method) and raise "must be used in assignment
        context".  Destination base is Self + field offset; the rest mirrors the
        simple-variable and explicit-field method-ptr assignment cases. }
      if (ISFld.TypeDesc.Kind = tyProcedural) and
         TProceduralTypeDesc(ISFld.TypeDesc).IsMethodPtr and
         (Asgn.Expr is TAddrOfExpr) and
         (TAddrOfExpr(Asgn.Expr).Expr is TFieldAccessExpr) and
         (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType <> nil) and
         (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType.Kind = tyProcedural) and
         TProceduralTypeDesc(TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType).IsMethodPtr then
      begin
        FAE := TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr);
        MD  := TMethodDecl(FAE.ResolvedMethod);
        { Destination field address = Self + field offset → %rcx }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [ISFld.Offset]));
        { Store the captured object pointer at offset 8 first — a virtual method
          reads its code pointer from THIS instance's vtable. }
        if FAE.Base <> nil then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.EmitExprToEax(FAE.Base);
          Self.Emit(#9'popq %rcx');
          Self.Emit(#9'movq %rax, 8(%rcx)');
        end
        else
        begin
          Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
          Self.Emit(#9'movq %rax, 8(%rcx)');
        end;
        { Store the code pointer at offset 0, vtable-resolved for a
          virtual/override method so @Obj.M captures the dynamic override (slot 0
          is typeinfo, method N at (N+1)*8); static label otherwise. }
        if MD.VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq 8(%rcx), %rax');
          Self.Emit(#9'movq (%rax), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
        end
        else
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [MethodEmitNameNative(MD, MD.OwnerTypeName, FAE.FieldName)]));
        Self.Emit(#9'movq %rax, (%rcx)');
        Exit;
      end;
      { General method-pointer / closure implicit-Self field store
        (bare 'FProc := <ident|literal|nil>' inside a method): 16-byte copy
        with env ARC for 'reference to' fields.  Mirrors the explicit-field
        arm in the TFieldAssignment path. }
      if IsMethodPtrType(ISFld.TypeDesc) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'pushq %r12');
        if Asgn.Expr is TNilLiteral then
          Self.Emit(#9'xorl %r12d, %r12d')
        else
        begin
          if Asgn.Expr is TAnonMethodExpr then
            Self.EmitAnonValueToSlot(TAnonMethodExpr(Asgn.Expr))
          else
            Self.EmitExprToEax(Asgn.Expr);
          Self.Emit(#9'movq %rax, %r12');
        end;
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rbx', [ISFld.Offset]));
        LNilStore := Self.NewLabel('fpnili');
        LSkipAdd := Self.NewLabel('fpskipaddi');
        LDone := Self.NewLabel('fpdonei');
        if TProceduralTypeDesc(ISFld.TypeDesc).IsReference then
        begin
          Self.Emit(#9'testq %r12, %r12');
          Self.Emit(Format(#9'jz %s', [LSkipAdd]));
          Self.Emit(#9'movq 8(%r12), %rdi');
          Self.Emit(#9'callq _ClassAddRef');
          Self.Emit(LSkipAdd + ':');
          Self.Emit(#9'movq 8(%rbx), %rdi');
          Self.Emit(#9'callq _ClassRelease');
        end;
        Self.Emit(#9'testq %r12, %r12');
        Self.Emit(Format(#9'jz %s', [LNilStore]));
        Self.Emit(#9'movq (%r12), %rax');
        Self.Emit(#9'movq %rax, (%rbx)');
        Self.Emit(#9'movq 8(%r12), %rax');
        Self.Emit(#9'movq %rax, 8(%rbx)');
        Self.Emit(Format(#9'jmp %s', [LDone]));
        Self.Emit(LNilStore + ':');
        Self.Emit(#9'movq $0, (%rbx)');
        Self.Emit(#9'movq $0, 8(%rbx)');
        Self.Emit(LDone + ':');
        Self.Emit(#9'popq %r12');
        Self.Emit(#9'popq %rbx');
        Exit;
      end;
      { ARC-managed implicit-Self field: retain the new value (unless the RHS
        already owns +1) and release the old before overwriting.  %r15
        (callee-saved) holds the slot address across the ARC calls. }
      if ISFld.IsUnretained or ISFld.IsWeak then
      begin
        { Non-owning fields keep plain/weak store semantics. }
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [ISFld.Offset]));
        if ISFld.IsWeak then
        begin
          Self.Emit(#9'movq %rax, %rsi');
          Self.Emit(#9'movq %rcx, %rdi');
          Self.Emit(#9'callq _WeakAssign');
        end
        else
          Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Asgn.ResolvedLhsType.IsString()
           or (Asgn.ResolvedLhsType.Kind = tyClass)
           or (Asgn.ResolvedLhsType.Kind = tyDynArray) then
      begin
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(#9'pushq %r15');
        Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%r15', [ISFld.Offset]));
        Self.Emit(#9'pushq %rax');
        { String/dyn-array: elide the retain when the RHS already owns +1 (a
          call result), else the buffer leaks one ref per store.  Class: the
          retain stays unconditional — some method calls return a borrowed class
          reference that NativeExprOwnsRef reports as owning, so eliding it would
          release a reference the field never acquired (a use-after-free).  This
          mirrors the deliberate asymmetry in the QBE backend (96514ee). }
        if not NativeExprOwnsRef(Asgn.Expr) then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          if Asgn.ResolvedLhsType.IsString() then
            Self.Emit(#9'callq _StringAddRef')
          else if Asgn.ResolvedLhsType.Kind = tyDynArray then
            Self.Emit(#9'callq _DynArrayAddRef')
          else
            Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(#9'movq (%r15), %rdi');     { old value }
        if Asgn.ResolvedLhsType.IsString() then
          Self.Emit(#9'callq _StringRelease')
        else if Asgn.ResolvedLhsType.Kind = tyDynArray then
          Self.Emit(#9'callq _DynArrayRelease')
        else
          Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %rax, (%r15)');
        Self.Emit(#9'popq %r15');
      end
      else if (Asgn.ResolvedLhsType.Kind = tyRecord) and
              (Asgn.Expr is TMethodCallExpr) and
              (TMethodCallExpr(Asgn.Expr).ResolvedClassType <> nil) and
              (TMethodCallExpr(Asgn.Expr).ResolvedClassType.Kind = tyInterface) and
              (TMethodCallExpr(Asgn.Expr).ResolvedType <> nil) and
              (TMethodCallExpr(Asgn.Expr).ResolvedType.Kind = tyRecord) then
      begin
        { Interface (itab) record-returning dispatch into an implicit-Self
          field — EmitRecordCallSretAt routes the itab case to the record-
          return helper. }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rbx', [ISFld.Offset]));
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitIntfRecordSretDispatch(TMethodCallExpr(Asgn.Expr), '(%rbx)', False);
        Self.Emit(#9'popq %rbx');
      end
      else if (Asgn.ResolvedLhsType.Kind = tyRecord) and
              (Asgn.Expr is TMethodCallExpr) and
              (TMethodCallExpr(Asgn.Expr).ResolvedMethod <> nil) and
              (TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
              (TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rbx', [ISFld.Offset]));
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr), '(%rbx)', False);
        Self.Emit(#9'popq %rbx');
      end
      else if (Asgn.ResolvedLhsType.Kind = tyRecord) and
              (Asgn.Expr is TFuncCallExpr) and
              (TFuncCallExpr(Asgn.Expr).ResolvedDecl <> nil) and
              (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
              (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyRecord) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rbx', [ISFld.Offset]));
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr), '(%rbx)', False);
        Self.Emit(#9'popq %rbx');
      end
      else if IsJumboSet(Asgn.ResolvedLhsType) then
      begin
        { Jumbo set into an implicit-Self field: plain bitmap memcpy (a set has
          no managed fields, so no retain/release). }
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');         { source bitmap addr }
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rdi', [ISFld.Offset]));
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %rbx');
      end
      else if (Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) then
      begin
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%r15', [ISFld.Offset]));
        Self.EmitRecordFieldRetains(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%r15', False);
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %rbx');
        Self.Emit(#9'popq %r15');
      end
      else
      begin
        { Non-managed implicit-Self field (integer, float, enum, etc.). }
        if IsFloatFamily(Asgn.ResolvedLhsType) then
        begin
          Self.EmitExprToXmm0(Asgn.Expr);
          { Narrow a Double/integer RHS to Single before the movss store
            (see the TFieldAssignment float path). }
          Self.EmitXmm0WidthAdjust(Asgn.Expr.ResolvedType,
            Asgn.ResolvedLhsType.Kind = tySingle);
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
          if ISFld.Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rcx', [ISFld.Offset]));
          Self.EmitStoreFloat('(%rcx)', Asgn.ResolvedLhsType);
        end
        else
        begin
          Self.EmitExprToEax(Asgn.Expr);
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
          if ISFld.Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rcx', [ISFld.Offset]));
          Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
        end;
      end;
      Exit;
    end;
    { 'reference to' closure assignment (Phase 1): three direct RHS shapes.
      An anonymous-method literal stores (Code = thunk, Env = nil); nil
      zeroes both halves; another reference-typed variable is a plain
      16-byte copy.  Capture-free closures carry no environment, so no
      retain/release accompanies these stores yet — environment ARC arrives
      with capture support.  A closure-returning call RHS falls through to
      the IsMethodPtrType sret arms below (that predicate covers reference
      types too). }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyProcedural) and
       TProceduralTypeDesc(Asgn.ResolvedLhsType).IsReference then
    begin
      { ARC (Phase 2): the 'reference to' Data half is a strong reference to
        an ARC env record — release the OLD value's env before overwrite
        (addref-new first where the RHS is a borrow, so self-assignment is
        safe).  A literal RHS takes a fresh retain for the slot it lands in.
        _ClassRelease is nil-safe, so capture-free (Env = nil) values cost a
        no-op call. }
      if Asgn.Expr is TAnonMethodExpr then
      begin
        MD := TMethodDecl(TAnonMethodExpr(Asgn.Expr).LiftedDecl);
        if MD = nil then
          raise ENativeCodeGenError.Create(
            'native backend: anonymous method not lifted — semantic pass required');
        Self.EmitVarAddr(Asgn.Name, '%rcx');
        Self.Emit(#9'movq 8(%rcx), %rdi');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [FuncSymbolFromDecl(MD)]));
        Self.Emit(#9'movq %rax, (%rcx)');
        if MD.EnvCaptured <> nil then
        begin
          { Capturing closure: store its env — the frame env, or the block
            env's current execution (Phase 4) — and take the fat value's
            own strong reference. }
          if MD.EnvSlotName <> '' then
            Self.Emit(Format(#9'movq %s, %%rax',
              [Self.VarOperand(MD.EnvSlotName)]))
          else
            Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('__envp')]));
          Self.Emit(#9'movq %rax, 8(%rcx)');
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _ClassAddRef');
        end
        else
          Self.Emit(#9'movq $0, 8(%rcx)');
        Exit;
      end;
      if Asgn.Expr is TNilLiteral then
      begin
        Self.EmitVarAddr(Asgn.Name, '%rcx');
        Self.Emit(#9'movq 8(%rcx), %rdi');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'movq $0, (%rcx)');
        Self.Emit(#9'movq $0, 8(%rcx)');
        Exit;
      end;
      { Method-pointer coercion, @Obj.M form (Phase 3): build the
        [code, receiver] pair straight into the destination — identical
        layout to a closure whose Env is the receiver — with the closure
        slot taking a STRONG reference to the receiver.  Virtual methods
        resolve through the instance's vtable (dynamic override), matching
        the method-pointer assignment path. }
      if (Asgn.Expr is TAddrOfExpr) and
         (TAddrOfExpr(Asgn.Expr).Expr is TFieldAccessExpr) and
         (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType <> nil) and
         (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType.Kind = tyProcedural) and
         TProceduralTypeDesc(TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType).IsMethodPtr then
      begin
        FAE := TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr);
        MD  := TMethodDecl(FAE.ResolvedMethod);
        { Release the old env before overwrite. }
        Self.EmitVarAddr(Asgn.Name, '%rcx');
        Self.Emit(#9'movq 8(%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        { Receiver -> %rax (evaluated fresh; %rcx recomputed after). }
        if FAE.Base <> nil then
          Self.EmitExprToEax(FAE.Base)
        else
          Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
        Self.EmitVarAddr(Asgn.Name, '%rcx');
        Self.Emit(#9'movq %rax, 8(%rcx)');
        { Code pointer: vtable-resolved for virtual/override methods. }
        if MD.VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rax), %rdx');
          Self.Emit(Format(#9'movq %d(%%rdx), %%rdx', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'movq %rdx, (%rcx)');
        end
        else
        begin
          Self.Emit(Format(#9'leaq %s(%%rip), %%rdx',
            [MethodEmitNameNative(MD, MD.OwnerTypeName, FAE.FieldName)]));
          Self.Emit(#9'movq %rdx, (%rcx)');
        end;
        { The closure slot owns a strong reference to the receiver. }
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Exit;
      end;
      if (Asgn.Expr is TIdentExpr) and
         (Asgn.Expr.ResolvedType <> nil) and
         (Asgn.Expr.ResolvedType.Kind = tyProcedural) and
         (TProceduralTypeDesc(Asgn.Expr.ResolvedType).IsReference or
          TProceduralTypeDesc(Asgn.Expr.ResolvedType).IsMethodPtr) then
      begin
        { Var-to-var copy (reference source, or a method-pointer variable
          coerced into a closure — same 16-byte layout, receiver retained):
          retain the incoming env/receiver, release the old one, then copy
          the 16-byte block. }
        if Self.IsLocal(TIdentExpr(Asgn.Expr).Name) then
          Self.Emit(Format(#9'leaq %s, %%rsi',
            [Self.VarOperand(TIdentExpr(Asgn.Expr).Name)]))
        else
          Self.Emit(Format(#9'leaq %s(%%rip), %%rsi',
            [Self.GlobalSymName(TIdentExpr(Asgn.Expr).Name)]));
        Self.Emit(#9'pushq %rsi');
        Self.Emit(#9'movq 8(%rsi), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.EmitVarAddr(Asgn.Name, '%rcx');
        Self.Emit(#9'movq 8(%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rsi');
        Self.EmitVarAddr(Asgn.Name, '%rdi');
        Self.Emit(#9'movq $16, %rdx');
        Self.Emit(#9'callq memcpy');
        Exit;
      end;
    end;
    { Method-pointer assignment from @Obj.Method: directly store the
      [CodePtr, ObjPtr] pair into the destination's 16-byte slot. }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyProcedural) and
       (TProceduralTypeDesc(Asgn.ResolvedLhsType).IsMethodPtr) and
       (Asgn.Expr is TAddrOfExpr) and
       (TAddrOfExpr(Asgn.Expr).Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType <> nil) and
       (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType.Kind = tyProcedural) and
       TProceduralTypeDesc(TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType).IsMethodPtr then
    begin
      FAE := TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr);
      MD  := TMethodDecl(FAE.ResolvedMethod);
      { Destination address → %rcx }
      if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand(Asgn.Name)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rcx', [Self.GlobalSymName(Asgn.Name)]));
      { Store object pointer at offset 8 first — a virtual method reads its
        code pointer from THIS instance's vtable. }
      if FAE.Base <> nil then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end;
      { Store code pointer at offset 0.  A virtual/override method must be
        resolved through the instance's vtable so @Obj.M captures the dynamic
        type's override — matching a direct Obj.M() call — instead of freezing
        the static address.  Slot 0 of the vtable is typeinfo, so method N is
        at offset (N+1)*8 (mirrors the dispatch in the call path). }
      if MD.VTableSlot >= 0 then
      begin
        Self.Emit(#9'movq 8(%rcx), %rax');     { obj  = data slot }
        Self.Emit(#9'movq (%rax), %rax');      { vptr = obj[0] }
        Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      end
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [MethodEmitNameNative(MD, MD.OwnerTypeName, FAE.FieldName)]));
      Self.Emit(#9'movq %rax, (%rcx)');
      Exit;
    end;
    { Method-pointer (of-object) assignment from a TMethod/TAddProc cast:
      P := TAddProc(M) — both sides are 16-byte Code+Data blocks.
      Emit as memcpy(dest, src, 16). }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyProcedural) and
       (TProceduralTypeDesc(Asgn.ResolvedLhsType).IsMethodPtr) and
       (Asgn.Expr is TFuncCallExpr) and
       (TFuncCallExpr(Asgn.Expr).ResolvedDecl = nil) and
       (TFuncCallExpr(Asgn.Expr).Args.Count = 1) then
    begin
      { Destination address → %rdi }
      Self.EmitVarAddr(Asgn.Name, '%rdi');
      { Source address: the cast argument (a TMethod record or another method ptr). }
      if TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0]) is TIdentExpr then
      begin
        if Self.IsLocal(TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name) then
          Self.Emit(Format(#9'leaq %s, %%rsi',
            [Self.VarOperand(TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'leaq %s(%%rip), %%rsi',
            [Self.GlobalSymName(TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name)]));
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: method-ptr cast source must be a simple variable');
      Self.Emit(#9'movq $16, %rdx');
      Self.Emit(#9'callq memcpy');
      Exit;
    end;
    { Method-ptr-returning call assignment: LHS is an 'of object' method pointer
      and RHS is a function/method call returning one.  A method pointer is a
      16-byte [Code; Data] aggregate returned via the record-return ABI (rcInt2,
      rax:rdx on SysV) — route it through the same sret helpers as a two-pointer
      record so BOTH halves are captured into the 16-byte destination slot. }
    if (Asgn.ResolvedLhsType <> nil) and
       IsMethodPtrType(Asgn.ResolvedLhsType) and
       (Asgn.Expr is TFuncCallExpr) and
       (TFuncCallExpr(Asgn.Expr).ResolvedDecl <> nil) and
       IsMethodPtrType(
         TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType) then
    begin
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.GlobalSymName(Asgn.Name) + '(%rip)', False);
      end;
      Exit;
    end;
    if (Asgn.ResolvedLhsType <> nil) and
       IsMethodPtrType(Asgn.ResolvedLhsType) and
       (Asgn.Expr is TMethodCallExpr) and
       (TMethodCallExpr(Asgn.Expr).ResolvedMethod <> nil) and
       IsMethodPtrType(
         TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType) then
    begin
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.GlobalSymName(Asgn.Name) + '(%rip)', False);
      end;
      Exit;
    end;
    { sret assignment: LHS is a record (or jumbo set) variable; RHS is a
      record/jumbo-set-returning call.  Pass the destination buffer address as
      the hidden first arg (%rdi). }
    if (Asgn.ResolvedLhsType <> nil) and
       ((Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) or
        IsJumboSet(Asgn.ResolvedLhsType)) and
       (Asgn.Expr is TFuncCallExpr) and
       (TFuncCallExpr(Asgn.Expr).ResolvedDecl <> nil) and
       (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
       ((TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType.Kind in
          [tyRecord, tyStaticArray]) or
        IsJumboSet(TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType)) then
    begin
      { The call reads the destination variable as one of its ARGUMENTS
        (R := CompR(R), S := Comp(N, S)).  EmitSretCall memsets the sret
        destination to zero BEFORE evaluating the argument list, so passing the
        destination straight in hands the callee an already-cleared value.
        Route the call through a fresh zeroed stack buffer (address held in
        callee-saved %r14), then move the result into the destination — release
        the old managed fields first (records only), then raw memcpy so the
        constructed +1 field refs transfer.  Mirrors the record-method arm
        below and the QBE backend's fresh-temp path. }
      if Self.CallAliasesDestVar(Asgn.Expr, Asgn.Name, Asgn.IsGlobal) then
      begin
        { RawSize is valid for a record (delegates to TotalSize), a jumbo set
          (bitmap byte count) and a static array alike — TotalSize would fault
          on the non-record kinds this branch also serves. }
        AliasSz := Asgn.ResolvedLhsType.RawSize();
        AliasBuf := (AliasSz + 15) and (-16);
        Self.Emit(#9'pushq %r14');
        Self.Emit(Format(#9'subq $%d, %%rsp', [AliasBuf]));
        Self.Emit(#9'movq %rsp, %r14');
        Self.Emit(#9'movq %r14, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [AliasSz]));
        Self.Emit(#9'callq memset');
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr), '(%r14)', False);
        { %r14 still holds the temp buffer address (callee-saved across the
          call).  Resolve the destination address into %rbx, release its old
          managed fields, then memcpy the constructed result over it. }
        Self.Emit(#9'pushq %rbx');
        if Asgn.IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
        else
          Self.EmitVarAddr(Asgn.Name, '%rbx');
        if Asgn.ResolvedLhsType.Kind = tyRecord then
          Self.EmitRecordFieldReleases(
            TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.Emit(#9'movq %rbx, %rdi');
        Self.Emit(#9'movq %r14, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [AliasSz]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %rbx');
        Self.Emit(Format(#9'addq $%d, %%rsp', [AliasBuf]));
        Self.Emit(#9'popq %r14');
        Exit;
      end;
      { Non-aliasing: the call does not read the destination, so EmitSretCall's
        memset-then-write of the dest is safe for the DATA — but the memset would
        silently orphan the destination's OLD managed fields (leaking one copy of
        every managed leaf per overwrite; BUG-20260720-sret-assign-old-fields-
        leak).  Release the dest's old managed fields FIRST (records only; the
        call at this point cannot alias the dest — the aliasing sub-case Exited
        above).  Result on first entry is zeroed, but a loop reassigning Result
        has old fields too, so it is released alongside the others. }
      if Asgn.ResolvedLhsType.Kind = tyRecord then
      begin
        Self.Emit(#9'pushq %rbx');
        if FSretFunc and SameText(Asgn.Name, 'Result') then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
        else if Asgn.IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
        else if Self.IsLocal(Asgn.Name) then
          Self.EmitVarAddr(Asgn.Name, '%rbx')
        else
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          Self.EmitLeaqGlobal(Asgn.Name, '%rbx');
        end;
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.Emit(#9'popq %rbx');
      end;
      { For a local jumbo set the dest is leaq'd; EmitSretCall's caller passes
        the operand and a 'by-ref' flag.  Mirror the record dispatch below. }
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.GlobalSymName(Asgn.Name) + '(%rip)', False);
      end;
      Exit;
    end;
    { sret assignment: interface (itab) method call returning a record.  The
      itab call has no ResolvedMethod, so it is classified by ResolvedClassType
      = interface + ResolvedType = record.  EmitIntfRecordSretDispatch writes
      the record straight into the destination, honouring the record-return ABI
      (hidden sret pointer for a memory-class record; register capture for a
      register-class one).  Mirrors the QBE EmitIntfSretDispatch path. }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyRecord) and
       (Asgn.Expr is TMethodCallExpr) and
       (TMethodCallExpr(Asgn.Expr).ResolvedClassType <> nil) and
       (TMethodCallExpr(Asgn.Expr).ResolvedClassType.Kind = tyInterface) and
       (TMethodCallExpr(Asgn.Expr).ResolvedType <> nil) and
       (TMethodCallExpr(Asgn.Expr).ResolvedType.Kind = tyRecord) then
    begin
      { Release the destination's prior managed fields before overwriting it,
        then dispatch.  The dispatch writes the constructed record (which owns
        its managed fields +1) over the dest, so ownership transfers cleanly. }
      Self.Emit(#9'pushq %rbx');
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if Asgn.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
      else if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        Self.EmitLeaqGlobal(Asgn.Name, '%rbx');
      end;
      Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
      Self.EmitIntfRecordSretDispatch(TMethodCallExpr(Asgn.Expr), '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { sret assignment: record-returning property read (V := Obj.Prop, indexed or
      not).  A getter call, so route it through EmitRecordCallSretAt (which
      synthesises the method call, threading an index arg for an indexed
      property) exactly as the record-method-call case above.  No aliasing guard
      is needed — the receiver is a class, distinct from the record dest. }
    { The RHS is normally a bare FieldAccess (V := Obj.Prop); a
      DEFAULT-array-property subscript (V := Obj[I]) wraps that same record-
      returning PropRead FieldAccess inside a TStringSubscriptExpr.
      IsNativeRecordCall / EmitRecordCallSretAt both unwrap the subscript, so
      both forms route through the identical sret path
      (BUG-002 A-indexed via default subscript). }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyRecord) and
       Self.IsNativeRecordCall(Asgn.Expr) and
       (((Asgn.Expr is TFieldAccessExpr) and
         (TFieldAccessExpr(Asgn.Expr).PropRead <> nil)) or
        (Asgn.Expr is TStringSubscriptExpr)) then
    begin
      Self.Emit(#9'pushq %rbx');
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if Asgn.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
      else if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        Self.EmitLeaqGlobal(Asgn.Name, '%rbx');
      end;
      Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
      Self.EmitRecordCallSretAt(Asgn.Expr, '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { sret assignment: method call returning a record (or jumbo set).
      %rdi = sret ptr, %rsi = Self, %rdx.. = user args. }
    if (Asgn.ResolvedLhsType <> nil) and
       ((Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) or
        IsJumboSet(Asgn.ResolvedLhsType)) and
       (Asgn.Expr is TMethodCallExpr) and
       (TMethodCallExpr(Asgn.Expr).ResolvedMethod <> nil) and
       (TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
       ((TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType.Kind in
          [tyRecord, tyStaticArray]) or
        IsJumboSet(TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType)) then
    begin
      { Self-assigned record method (M := M.Method(...)): the sret destination
        would alias the receiver, so the callee would clobber Self while still
        reading it.  Route the call through a fresh zeroed stack buffer (address
        held in callee-saved %r14), then move the result into the destination
        (release old fields, raw memcpy — ownership of the constructed managed
        fields transfers). }
      if ((Asgn.ResolvedLhsType.Kind = tyRecord) or
          IsJumboSet(Asgn.ResolvedLhsType)) and
         Self.CallAliasesDestVar(Asgn.Expr, Asgn.Name, Asgn.IsGlobal) then
      begin
        { RawSize is valid for a record (delegates to TotalSize) and for a
          jumbo set (bitmap byte count) alike — TotalSize would fault on a set
          type, which this arm now also serves. }
        AliasSz := Asgn.ResolvedLhsType.RawSize();
        AliasBuf := (AliasSz + 15) and (-16);
        Self.Emit(#9'pushq %r14');
        Self.Emit(Format(#9'subq $%d, %%rsp', [AliasBuf]));
        Self.Emit(#9'movq %rsp, %r14');
        Self.Emit(#9'movq %r14, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [AliasSz]));
        Self.Emit(#9'callq memset');
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr), '(%r14)', False);
        { %r14 still holds the temp buffer address (callee-saved across the call).
          Resolve the destination address into %rbx, release its old managed
          fields, then memcpy the constructed result over it. }
        Self.Emit(#9'pushq %rbx');
        if Asgn.IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
        else
          Self.EmitVarAddr(Asgn.Name, '%rbx');
        if Asgn.ResolvedLhsType.Kind = tyRecord then
          Self.EmitRecordFieldReleases(
            TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.Emit(#9'movq %rbx, %rdi');
        Self.Emit(#9'movq %r14, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [AliasSz]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %rbx');
        Self.Emit(Format(#9'addq $%d, %%rsp', [AliasBuf]));
        Self.Emit(#9'popq %r14');
        Exit;
      end;
      { Non-aliasing: release the dest's OLD managed fields before the sret call
        memsets and overwrites them, else each overwrite orphans one copy of
        every managed leaf (BUG-20260720-sret-assign-old-fields-leak).  The
        aliasing sub-case Exited above, so the call cannot read the dest here. }
      if Asgn.ResolvedLhsType.Kind = tyRecord then
      begin
        Self.Emit(#9'pushq %rbx');
        if FSretFunc and SameText(Asgn.Name, 'Result') then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
        else if Asgn.IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
        else if Self.IsLocal(Asgn.Name) then
          Self.EmitVarAddr(Asgn.Name, '%rbx')
        else
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          Self.EmitLeaqGlobal(Asgn.Name, '%rbx');
        end;
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.Emit(#9'popq %rbx');
      end;
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.GlobalSymName(Asgn.Name) + '(%rip)', False);
      end;
      Exit;
    end;
    { sret assignment: `<rec> := inherited M(...)` — static dispatch to the
      parent, same destination selection as the method/func branches above. }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) and
       (Asgn.Expr is TInheritedCallExpr) and
       (TInheritedCallExpr(Asgn.Expr).ResolvedMethod <> nil) and
       (TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
       (TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType.Kind in
          [tyRecord, tyStaticArray]) then
    begin
      { Release the dest's OLD managed fields before the sret call overwrites
        them (BUG-20260720-sret-assign-old-fields-leak).  Gate on the dest NOT
        aliasing an argument — `R := inherited M(R)` would UAF a source the call
        still reads (this arm has no fresh-temp-buffer aliasing path, unlike the
        method/func arms, so the guard is checked explicitly here). }
      if (Asgn.ResolvedLhsType.Kind = tyRecord) and
         not Self.CallAliasesDestVar(Asgn.Expr, Asgn.Name, Asgn.IsGlobal) then
      begin
        Self.Emit(#9'pushq %rbx');
        if FSretFunc and SameText(Asgn.Name, 'Result') then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
        else if Asgn.IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
        else if Self.IsLocal(Asgn.Name) then
          Self.EmitVarAddr(Asgn.Name, '%rbx')
        else
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          Self.EmitLeaqGlobal(Asgn.Name, '%rbx');
        end;
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.Emit(#9'popq %rbx');
      end;
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Self.GlobalSymName(Asgn.Name) + '(%rip)', False);
      end;
      Exit;
    end;
    if IsFloatFamily(Asgn.ResolvedLhsType) then
    begin
      { Float assignment: value → %xmm0, then store. }
      Self.EmitExprToXmm0(Asgn.Expr);
      { Adjust the value to the LHS width: Double/integer RHS into a Single
        LHS narrows (cvtsd2ss); a Single RHS into a Double LHS widens
        (cvtss2sd). }
      Self.EmitXmm0WidthAdjust(Asgn.Expr.ResolvedType,
        Asgn.ResolvedLhsType.Kind = tySingle);
      { CAPTURED first (see the float read + integer arms): a captured var-param
        float must go through _cap_ with an extra deref, not the var-param arm's
        bogus Name(%rip) (BUG-20260720-capture-varparam). }
      if Self.IsCaptured(Asgn.Name) then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        if Asgn.IsVarParam then
          Self.Emit(#9'movq (%rcx), %rcx');
        Self.EmitStoreFloat('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.EmitStoreFloat('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitStoreFloat(Self.VarOperand(Asgn.Name), Self.LocalType(Asgn.Name))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        Self.EmitStoreFloat(Self.VarOperand(Asgn.Name), Asgn.ResolvedLhsType);
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyString) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'pushq %rax');
      if not NativeExprOwnsRef(Asgn.Expr) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
      end;
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyDynArray) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'pushq %rax');
      if not NativeExprOwnsRef(Asgn.Expr) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _DynArrayAddRef');
      end;
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rax');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyInterface) then
    begin
      Self.EmitInterfaceAssign(Asgn);
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyClass) and
            (Asgn.Expr is TNilLiteral) then
    begin
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq $0, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq $0, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'callq _ClassRelease');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyClass) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'pushq %rax');
      { Elide the retain when the RHS already owns +1 (a call result): a
        function/method returning a class leaves Result at +1 (the callee's
        `Result := x` AddRef'd and the epilogue did not release it), so the
        assignment consumes that transferred reference.  AddRef'ing again leaks
        one ref per call.  This matches the tyString/tyDynArray branches above
        and the QBE backend's ExprOwnsRef elision. }
      if not NativeExprOwnsRef(Asgn.Expr) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
      end;
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (IsJumboSet(Asgn.ResolvedLhsType) or
             (Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray])) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'movq %rax, %rsi');
      if Asgn.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(Asgn.Name)]))
      else if Self.IsCaptured(Asgn.Name) then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('_cap_' + Asgn.Name)]))
      else if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Result')]))
      else if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(Asgn.Name)]))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        Self.EmitLeaqGlobal(Asgn.Name, '%rdi');
      end;
      { Record with managed fields (string / class / interface / dyn-array, or
        nested record thereof): a bare memcpy would make the copy share the
        source's references at the same refcount, so mutating either side later
        drops a shared buffer to 0 and frees it under the other (use-after-free
        / double-free).  Release the destination's prior fields, and — unless the
        source already transferred ownership (+1, e.g. a record-returning
        property getter / call whose Result owns its fields) — retain the
        source's managed fields so the copy owns its own references.  Mirrors the
        string/dyn-array assignment paths' NativeExprOwnsRef guard and the
        record-field-store copy path. }
      if (Asgn.ResolvedLhsType.Kind = tyRecord) and
         not RecretManagedClean(TRecordTypeDesc(Asgn.ResolvedLhsType)) then
      begin
        { %rsi = source addr, %rdi = dest addr — preserve both across the ARC
          calls in callee-saved registers (%rbx = source, %r15 = dest). }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'movq %rsi, %rbx');
        Self.Emit(#9'movq %rdi, %r15');
        if not NativeExprOwnsRef(Asgn.Expr) then
          Self.EmitRecordFieldRetains(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%r15', False);
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %r15');
        Self.Emit(#9'popq %rbx');
      end
      else
      begin
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
      end;
    end
    else
    begin
      Self.EmitExprToEax(Asgn.Expr);
      { CAPTURED first: a captured var-param is BOTH captured and IsVarParam;
        the var-param arm below would wrongly use VarOperand(Name) = Name(%rip)
        (a bogus global) — so a captured name must take the capture path.  The
        capture slot holds the enclosing var's address; for a captured VAR/OUT
        param that enclosing slot in turn holds the caller's address, so deref
        once more to reach the pointee (BUG-20260720-capture-varparam). }
      if Self.IsCaptured(Asgn.Name) then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx',
          [Self.VarOperand('_cap_' + Asgn.Name)]));
        if Asgn.IsVarParam then
          Self.Emit(#9'movq (%rcx), %rcx');
        Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx',
          [Self.VarOperand(Asgn.Name)]));
        Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
      end
      else
      begin
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.EmitStoreVar(Self.VarOperand(Asgn.Name),
          Asgn.ResolvedLhsType);
      end;
    end;
    Exit;
  end;

  if AStmt is TForStmt then
  begin
    Self.EmitForStmt(TForStmt(AStmt));
    Exit;
  end;

  if AStmt is TForInStmt then
  begin
    Self.EmitForInStmt(TForInStmt(AStmt));
    Exit;
  end;

  if AStmt is TCaseStmt then
  begin
    Self.EmitCaseStmt(TCaseStmt(AStmt));
    Exit;
  end;

  if AStmt is TProcCall then
  begin
    PC := TProcCall(AStmt);
    if SameText(PC.Name, 'WriteLn') then
    begin
      Self.EmitWrite(PC, True);
      Exit;
    end;
    if SameText(PC.Name, 'Write') then
    begin
      Self.EmitWrite(PC, False);
      Exit;
    end;
    { FreeMem(P) → _BlaiseFreeMem(P).  Pointer arg in %rdi. }
    if SameText(PC.Name, 'FreeMem') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _BlaiseFreeMem');
      Exit;
    end;
    { Delete(S, Idx, Count): S := _StringDelete(S, Idx, Count) with ARC. }
    if SameText(PC.Name, 'Delete') and (PC.Args.Count = 3) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringDelete');
      { Assign result back: addref new, release old, store.  Mirrors the string
        SetLength store-back: the bare local/global ident arm writes the named
        slot directly; every other receiver (class field, implicit-Self field,
        var-param, field-array element) stores through the slot address from
        EmitLValueSlotAddr.  Before, the store-back was guarded by a bare
        `is TIdentExpr`, so a field receiver dropped the result on the floor —
        no store, and the old field value and the _StringDelete result both
        leaked (BUG-20260723-native-delete-string-field-noop). }
      if (TASTExpr(PC.Args.Items[0]) is TIdentExpr) and
         not TIdentExpr(TASTExpr(PC.Args.Items[0])).IsImplicitSelf and
         (TIdentExpr(TASTExpr(PC.Args.Items[0])).ParamMode = pmNone) then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi',
            [Self.GlobalSymName(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]));
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %%rax, %s',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)',
            [Self.GlobalSymName(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]));
      end
      else
      begin
        { Field / element / implicit-Self / var-param receiver: new string is
          in %rax — retain it, release the old slot value, store through the
          slot address. }
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        Self.EmitLValueSlotAddr(TASTExpr(PC.Args.Items[0]));
        Self.Emit(#9'pushq %rdx');
        Self.Emit(#9'movq (%rdx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %rax, (%rdx)');
      end;
      Exit;
    end;
    { SetLength(A, N) for dynamic arrays: A := _DynArraySetLength(A, N, ElemSize). }
    if SameText(PC.Name, 'SetLength') and (PC.Args.Count = 2) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType.Kind = tyDynArray) then
    begin
      if (TASTExpr(PC.Args.Items[0]) is TIdentExpr) and
         not TIdentExpr(TASTExpr(PC.Args.Items[0])).IsImplicitSelf and
         (TIdentExpr(TASTExpr(PC.Args.Items[0])).ParamMode = pmNone) then
      begin
        FDynArgName := TIdentExpr(TASTExpr(PC.Args.Items[0])).Name;
        FDynElemSz :=
          TDynArrayTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).ElementType.RawSize();
        { Evaluate the new-length expression FIRST.  It may itself emit a call
          (e.g. SetLength(Result, Length(A)) lowers Length(A) to a
          _DynArrayLength call) which clobbers %rdi, so the array pointer must
          be loaded into %rdi only after this expression is fully evaluated. }
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'movl %eax, %esi');
        { Load current data ptr into %rdi (after N is evaluated). }
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [Self.GlobalSymName(FDynArgName)]));
        { Element size into %edx. }
        Self.Emit(Format(#9'movl $%d, %%edx', [FDynElemSz]));
        Self.Emit(#9'callq _DynArraySetLength');
        { Store new data ptr back. }
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)', [Self.GlobalSymName(FDynArgName)]));
      end
      else
      begin
        { Field receiver (R.A / C.A / chained): compute the slot address,
          call through it, store the new data pointer back. }
        FDynElemSz :=
          TDynArrayTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).ElementType.RawSize();
        Self.EmitLValueSlotAddr(TASTExpr(PC.Args.Items[0]));
        Self.Emit(#9'pushq %rdx');
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'pushq %rdx');
        Self.Emit(#9'subq $8, %rsp');   { keep calls 16-byte aligned }
        Self.Emit(#9'movl %eax, %esi');
        Self.Emit(#9'movq (%rdx), %rdi');
        Self.Emit(Format(#9'movl $%d, %%edx', [FDynElemSz]));
        Self.Emit(#9'callq _DynArraySetLength');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'movq %rax, (%rdx)');
      end;
      Exit;
    end;
    { SetLength(S, N): S := _StringSetLength(S, N) with ARC. }
    if SameText(PC.Name, 'SetLength') and (PC.Args.Count = 2) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringSetLength');
      if (TASTExpr(PC.Args.Items[0]) is TIdentExpr) and
         not TIdentExpr(TASTExpr(PC.Args.Items[0])).IsImplicitSelf and
         (TIdentExpr(TASTExpr(PC.Args.Items[0])).ParamMode = pmNone) then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi',
            [Self.GlobalSymName(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]));
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %%rax, %s',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)',
            [Self.GlobalSymName(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]));
      end
      else
      begin
        { Field receiver: new string is in %rax — retain it, release the old
          field value, store through the slot address. }
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        Self.EmitLValueSlotAddr(TASTExpr(PC.Args.Items[0]));
        Self.Emit(#9'pushq %rdx');
        Self.Emit(#9'movq (%rdx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %rax, (%rdx)');
      end;
      Exit;
    end;
    { Inc(x) / Inc(x,n) / Dec(x) / Dec(x,n) — in-place add/sub.
      Supports TIdentExpr (local, global, implicit-Self field, var param)
      and TFieldAccessExpr (record/class field). }
    if (SameText(PC.Name, 'Inc') or SameText(PC.Name, 'Dec')) and
       (PC.Args.Count >= 1) and (PC.Args.Count <= 2) then
    begin
      Self.EmitIncDec(PC);
      Exit;
    end;
    { Include(S, elem): S := S or (1 shl ord(elem)) }
    if SameText(PC.Name, 'Include') and (PC.Args.Count = 2) then
    begin
      { Jumbo set: address of the set, ordinal, then _SetInclude. Handles any
        lvalue shape (var, field, element), not just a bare ident. }
      if IsJumboSet(TASTExpr(PC.Args.Items[0]).ResolvedType) then
      begin
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'pushq %rax');           { ordinal }
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));  { set addr -> %rax }
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'popq %rsi');
        Self.Emit(#9'callq _SetInclude');
        Exit;
      end;
      { Small set (<=64 bits): mask = 1 shl ord(elem), then OR it into the set
        lvalue's memory.  Take the set's ADDRESS via a transient @-wrapper so
        every lvalue shape works — a plain var (local/global/threadvar), a field
        of Self or another object, or an array element — not only a bare
        identifier.  The previous form hard-cast Args[0] to TIdentExpr and, for a
        set-typed FIELD, emitted `orl %eax, <FieldName>(%rip)` against a
        non-existent global, crashing at run time. }
      SetWide := (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
                 (TSetTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).BitCount > 32);
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));   { ordinal -> %eax }
      Self.Emit(#9'movl %eax, %ecx');
      if SetWide then
      begin
        Self.Emit(#9'movq $1, %rax');
        Self.Emit(#9'shlq %cl, %rax');
      end
      else
      begin
        Self.Emit(#9'movl $1, %eax');
        Self.Emit(#9'shll %cl, %eax');
      end;
      Self.Emit(#9'pushq %rax');                        { save mask across addr eval }
      SetLValAddr := TAddrOfExpr.Create();
      try
        SetLValAddr.Expr := TASTExpr(PC.Args.Items[0]);
        Self.EmitExprToEax(SetLValAddr);                { set lvalue addr -> %rax }
      finally
        SetLValAddr.Expr := nil;   { Args[0] is owned by the call node }
        SetLValAddr.Free();
      end;
      Self.Emit(#9'popq %rcx');                         { mask -> %rcx }
      if SetWide then
        Self.Emit(#9'orq %rcx, (%rax)')
      else
        Self.Emit(#9'orl %ecx, (%rax)');
      Exit;
    end;
    { Exclude(S, elem): S := S and (not (1 shl ord(elem))) }
    if SameText(PC.Name, 'Exclude') and (PC.Args.Count = 2) then
    begin
      { Jumbo set: address of the set, ordinal, then _SetExclude. }
      if IsJumboSet(TASTExpr(PC.Args.Items[0]).ResolvedType) then
      begin
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'popq %rsi');
        Self.Emit(#9'callq _SetExclude');
        Exit;
      end;
      { Small set: clear-mask = not (1 shl ord(elem)), AND'd into the set
        lvalue's memory.  Address-based, mirroring Include above, so a set
        FIELD (or element) is handled correctly rather than as a bogus global. }
      SetWide := (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
                 (TSetTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).BitCount > 32);
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));   { ordinal -> %eax }
      Self.Emit(#9'movl %eax, %ecx');
      if SetWide then
      begin
        Self.Emit(#9'movq $1, %rax');
        Self.Emit(#9'shlq %cl, %rax');
        Self.Emit(#9'notq %rax');
      end
      else
      begin
        Self.Emit(#9'movl $1, %eax');
        Self.Emit(#9'shll %cl, %eax');
        Self.Emit(#9'notl %eax');
      end;
      Self.Emit(#9'pushq %rax');                        { save clear-mask }
      SetLValAddr := TAddrOfExpr.Create();
      try
        SetLValAddr.Expr := TASTExpr(PC.Args.Items[0]);
        Self.EmitExprToEax(SetLValAddr);                { set lvalue addr -> %rax }
      finally
        SetLValAddr.Expr := nil;   { Args[0] is owned by the call node }
        SetLValAddr.Free();
      end;
      Self.Emit(#9'popq %rcx');                         { clear-mask -> %rcx }
      if SetWide then
        Self.Emit(#9'andq %rcx, (%rax)')
      else
        Self.Emit(#9'andl %ecx, (%rax)');
      Exit;
    end;
    if SameText(PC.Name, 'Halt') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq exit');
      Exit;
    end;
    if SameText(PC.Name, 'ZeroMem') and (PC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rdx');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'xorl %esi, %esi');
      Self.Emit(#9'callq memset');
      Exit;
    end;
    if SameText(PC.Name, 'Sleep') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _Sleep');
      Exit;
    end;
    if SameText(PC.Name, 'DeleteFile') and (PC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(PC.Args.Items[0]), '_DeleteFile');
      Exit;
    end;
    if SameText(PC.Name, 'RemoveDir') and (PC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(PC.Args.Items[0]), '_RemoveDir');
      Exit;
    end;
    if SameText(PC.Name, 'ForceDirectories') and (PC.Args.Count = 1) then
    begin
      Self.EmitBuiltinStrCall1(TASTExpr(PC.Args.Items[0]), '_ForceDirectories');
      Exit;
    end;
    if SameText(PC.Name, 'WriteFile') and (PC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(PC.Args.Items[0]),
        TASTExpr(PC.Args.Items[1]), '_WriteFile');
      Exit;
    end;
    if SameText(PC.Name, 'AppendFile') and (PC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(PC.Args.Items[0]),
        TASTExpr(PC.Args.Items[1]), '_AppendFile');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessSetExe') and (PC.Args.Count = 2) then
    begin
      { Arg1 (the string) may be an owned (+1) transient — EmitBuiltinStrCall2
        handles both operand slots; the pointer arg0 just travels through. }
      Self.EmitBuiltinStrCall2(TASTExpr(PC.Args.Items[0]),
        TASTExpr(PC.Args.Items[1]), '_ProcessSetExe');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessAddArg') and (PC.Args.Count = 2) then
    begin
      Self.EmitBuiltinStrCall2(TASTExpr(PC.Args.Items[0]),
        TASTExpr(PC.Args.Items[1]), '_ProcessAddArg');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessExecute') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessExecute');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessWaitOnExit') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessWaitOnExit');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessFree') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessFree');
      Exit;
    end;
    { Unqualified call to a procedural-typed field of the current class
      (implicit Self.Field) used as a statement. }
    if PC.IsProcFieldCall then
    begin
      Self.EmitProcFieldCall(nil, 'Self', False, PC.ProcFieldInfo,
        TProceduralTypeDesc(PC.ResolvedProcType), PC.Args, nil);
      Exit;
    end;
    if PC.IsIndirectCall then
    begin
      if (PC.ResolvedProcType <> nil) and
         (TProceduralTypeDesc(PC.ResolvedProcType).IsMethodPtr or
          TProceduralTypeDesc(PC.ResolvedProcType).IsReference) then
        Self.EmitMethodPtrCall(Self.VarOperand(PC.Name),
          TProceduralTypeDesc(PC.ResolvedProcType), PC.Args)
      else
        Self.EmitCallIndirect(
          Self.VarOperand(PC.Name),
          TProceduralTypeDesc(PC.ResolvedProcType),
          PC.Args);
      Exit;
    end;
    if PC.IsImplicitSelfMethod and (PC.ResolvedDecl <> nil) then
    begin
      MD := TMethodDecl(PC.ResolvedDecl);
      { Self occupies %rdi, leaving %rsi..%r9 (5 registers) for arguments.  The
        push/pop-into-registers fast path is only valid when every argument
        slot fits a register — i.e. Self + args <= 6 total.  When the call has
        more slots, the surplus must go on the stack; otherwise the pop loop
        indexes SysVArg64 past %r9 (the OOB that crashed _StringConcat). }
      if Self.CountArgSlots(MD.Params) + 1 <= 6 then
      begin
        Self.BeginCallArgs(MD.Params, PC.Args);
        for I := 0 to PC.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(PC.Args.Items[I]), I);
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
        Self.EmitPopMethodArgsToRegs(MD.Params, PC.Args, 1);
        Self.Emit(#9'movq %r10, %rdi');
        { Virtual implicit-Self call dispatches through the vtable. }
        Self.EmitSelfDispatch(MD, FuncSymbolFromDecl(MD));
        Self.EndCallArgs();
        Exit;
      end;
      { >6 slots: stack-spill path (mirrors EmitMethodCallStmt).  Reserve a
        6-register staging area plus overflow space; slot 0 = Self -> %rdi,
        slots 1..5 -> %rsi..%r9, surplus slots stay on the stack. }
      PCUserSlots := Self.CountArgSlots(MD.Params);
      PCTotalSlots := PCUserSlots + 1;
      PCOverflow := PCTotalSlots - 6;
      PCAllocSz := ((PCTotalSlots * 8 + 15) and (-16));
      PCHD := TList<Integer>.Create();
      PCHK := TList<Integer>.Create();
      PCHTotal := Self.EmitArgHoist(MD.Params, nil, True, '', PC.Args, PCHD, PCHK);
      Self.Emit(Format(#9'subq $%d, %%rsp', [PCAllocSz]));
      Self.EmitArgsToSlots(PC.Args, MD.Params, PCAllocSz, PCHTotal, PCHD, PCHK);
      { Self into slot 0 -> %rdi. }
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      Self.Emit(#9'movq %rax, 0(%rsp)');
      PCCleanUp := Self.EmitMethodOverflowLoad(MD.Params, PC.Args, PCAllocSz);
      Self.EmitSelfDispatch(MD, FuncSymbolFromDecl(MD));
      Self.EmitHoistEpilogue(PC.Args, PCHD, PCHK, PCHTotal, PCCleanUp, True);
      PCHD.Free();
      PCHK.Free();
      Exit;
    end;
    { No intrinsic case above matched and the semantic pass attached no
      declaration: a builtin this backend cannot lower in statement position
      (e.g. a builtin FUNCTION used as a statement).  Raise the same
      diagnostic the QBE backend gives instead of dereferencing the nil
      decl below, which crashed the compiler (BUG-035). }
    if PC.ResolvedDecl = nil then
      raise ENativeCodeGenError.Create(Format(
        'Unknown procedure ''%s'' at line %d', [PC.Name, PC.Line]));
    { User procedure call (result, if any, ignored in statement position). }
    if Self.TryEmitInlineCall(PC.ResolvedDecl, PC.Args, False) then
      Exit;
    MD := TMethodDecl(PC.ResolvedDecl);
    { An sret-shaped return (record / interface / static array / jumbo set)
      discarded in statement position still needs the hidden result buffer:
      the callee writes through %rdi, so a bare `callq F` makes it write its
      result over caller memory.  Allocate a throwaway buffer, route the call
      through the sret machinery, then release the discarded result's managed
      content (BUG-20260722-discarded-sret-call-no-buffer).  Mirrors the itab
      record-discard branch. }
    if (MD.ResolvedReturnType <> nil) and
       ((MD.ResolvedReturnType.Kind in [tyRecord, tyStaticArray]) or
        IsJumboSet(MD.ResolvedReturnType)) then
    begin
      DiscBufSz := (MD.ResolvedReturnType.RawSize() + 15) and (-16);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [DiscBufSz]));
      Self.Emit(#9'movq %rsp, %rbx');
      { EmitSretCall zeroes the buffer itself and also handles the
        register-class record shapes (capture into the buffer). }
      Self.EmitSretCall(FuncSymbolFromDecl(MD), MD, PC.Args, '(%rbx)', False);
      { Arg evaluation may clobber %rbx; %rsp is balanced and still points
        at the buffer, so re-derive its address. }
      Self.Emit(#9'movq %rsp, %rbx');
      if MD.ResolvedReturnType.Kind = tyRecord then
      begin
        if not RecretManagedClean(TRecordTypeDesc(MD.ResolvedReturnType)) then
          Self.EmitRecordFieldReleases(
            TRecordTypeDesc(MD.ResolvedReturnType), '%rbx');
      end
      else if (MD.ResolvedReturnType.Kind = tyStaticArray) and
              ArcTypeHasManagedContent(MD.ResolvedReturnType) then
        Self.EmitStaticArrayReleaseElems(
          TStaticArrayTypeDesc(MD.ResolvedReturnType), '%rbx', False);
      Self.Emit(Format(#9'addq $%d, %%rsp', [DiscBufSz]));
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    if (MD.ResolvedReturnType <> nil) and
       (MD.ResolvedReturnType.Kind = tyInterface) then
    begin
      { EmitIntfSretCall takes the expression form; build a transient
        TFuncCallExpr view of this statement node (args are borrowed and
        detached before Free).  The helper leaves the 16-byte fat pair at
        (%rsp); release the transferred obj reference and pop the buffer. }
      DiscShim := TFuncCallExpr.Create();
      try
        DiscShim.Name := PC.Name;
        DiscShim.Args := PC.Args;
        DiscShim.ResolvedDecl := PC.ResolvedDecl;
        Self.EmitIntfSretCall(DiscShim);
      finally
        DiscShim.Args := nil;          { borrowed — do not free }
        DiscShim.ResolvedDecl := nil;  { borrowed — do not free }
        DiscShim.Free();
      end;
      Self.Emit(#9'movq (%rsp), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'addq $16, %rsp');
      Exit;
    end;
    Self.EmitCall(FuncSymbolFromDecl(TMethodDecl(PC.ResolvedDecl)),
      TMethodDecl(PC.ResolvedDecl), PC.Args);
    { A function called in statement position discards its result.  When the
      result is a managed CLASS the callee transferred a +1 reference (it
      AddRef'd on `Result := x` and did not release Result at scope exit); the
      discard would leak it — the same transient-release rule the assignment/arg
      paths apply, here for the discarded call.  The return is in %rax; release
      it once.  Only tyClass needs this (String/dynarray discards balance via
      the callee's scope-exit convention; non-managed returns own nothing).  A
      bare TProcCall is never a constructor, so every tyClass return is owned. }
    MD := TMethodDecl(PC.ResolvedDecl);
    if (MD.ResolvedReturnType <> nil) and
       (MD.ResolvedReturnType.Kind = tyClass) then
    begin
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassRelease');
    end;
    Exit;
  end;

  if AStmt is TCompoundStmt then
  begin
    Comp := TCompoundStmt(AStmt);
    Self.EmitStmtList(Comp.Stmts);
    Exit;
  end;

  if AStmt is TIfStmt then
  begin
    IfS   := TIfStmt(AStmt);
    LThen := Self.NewLabel('then');
    LEnd  := Self.NewLabel('ifend');
    if IfS.ElseStmt <> nil then
      LElse := Self.NewLabel('else')
    else
      LElse := LEnd;
    Self.EmitCondBranchFlushed(IfS.Condition, LThen, LElse);  { flush cond xient }
    Self.Emit(LThen + ':');
    Self.EmitStmt(IfS.ThenStmt);
    Self.Emit(#9'jmp ' + LEnd);
    if IfS.ElseStmt <> nil then
    begin
      Self.Emit(LElse + ':');
      Self.EmitStmt(IfS.ElseStmt);
      Self.Emit(#9'jmp ' + LEnd);
    end;
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TTryFinallyStmt then
  begin
    Self.EmitTryFinallyStmt(TTryFinallyStmt(AStmt));
    Exit;
  end;

  if AStmt is TTryExceptStmt then
  begin
    Self.EmitTryExceptStmt(TTryExceptStmt(AStmt));
    Exit;
  end;

  if AStmt is TRaiseStmt then
  begin
    Self.EmitRaiseStmt(TRaiseStmt(AStmt));
    Exit;
  end;

  if AStmt is TWhileStmt then
  begin
    WhileS := TWhileStmt(AStmt);
    LCond  := Self.NewLabel('wcond');
    LBody  := Self.NewLabel('wbody');
    LEnd   := Self.NewLabel('wend');
    { ROTATED loop: the condition sits at the BOTTOM, so each iteration
      executes one taken branch (jcc back to the body) instead of a
      body-end jmp plus the condition's forward branches. }
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LCond);
    FContinueExcDepths.Push(FExcDepth);
    Self.EmitStmt(WhileS.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();
    Self.Emit(LCond + ':');
    Self.EmitCondBranchFlushed(WhileS.Condition, LBody, LEnd);  { per-iter flush }
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TRepeatStmt then
  begin
    RepS  := TRepeatStmt(AStmt);
    LBody := Self.NewLabel('rbody');
    LCond := Self.NewLabel('rcond');
    LEnd  := Self.NewLabel('rend');
    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LCond);
    FContinueExcDepths.Push(FExcDepth);
    Self.EmitStmtList(RepS.Body.Stmts);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();
    Self.Emit(LCond + ':');
    Self.EmitCondBranchFlushed(RepS.Condition, LEnd, LBody);  { per-iter flush }
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TBreakStmt then
  begin
    if FBreakLabels.Count = 0 then
      raise ENativeCodeGenError.Create('break outside loop');
    Self.EmitExcUnwind(FBreakExcDepths.Peek());
    Self.Emit(#9'jmp ' + FBreakLabels.Peek());
    Exit;
  end;

  if AStmt is TContinueStmt then
  begin
    if FContinueLabels.Count = 0 then
      raise ENativeCodeGenError.Create('continue outside loop');
    Self.EmitExcUnwind(FContinueExcDepths.Peek());
    Self.Emit(#9'jmp ' + FContinueLabels.Peek());
    Exit;
  end;

  if AStmt is TVarDeclStmt then
  begin
    Self.EmitVarDeclStmt(TVarDeclStmt(AStmt));
    Exit;
  end;
  if AStmt is TExitStmt then
  begin
    if TExitStmt(AStmt).ResultAssign <> nil then
      Self.EmitStmt(TExitStmt(AStmt).ResultAssign);
    { Exit inside an INLINED body returns from the CALLEE only: jump to
      the inline end label.  No exception unwinding (the callee cannot
      contain try) and no caller-epilogue involvement. }
    if FInlineActive then
    begin
      Self.Emit(#9'jmp ' + FInlineEndLbl);
      Exit;
    end;
    Self.EmitExcUnwind(0);
    if FExitLabel <> '' then
      Self.Emit(#9'jmp ' + FExitLabel)
    else
    begin
      Self.Emit(#9'movl $0, %eax');
      Self.Emit(#9'leave');
      Self.Emit(#9'ret');
    end;
    Exit;
  end;

  if AStmt is TMethodCallStmt then
  begin
    { Class method call in statement position (result discarded). }
    Self.EmitMethodCallStmt(TMethodCallStmt(AStmt));
    Exit;
  end;

  if AStmt is TInheritedCallStmt then
  begin
    Self.EmitInheritedCall(TInheritedCallStmt(AStmt));
    Exit;
  end;

  if AStmt is TFieldAssignment then
  begin
    FA := TFieldAssignment(AStmt);
    { Qualified STATIC var write 'TFoo.X := V': lower exactly like a bare global
      store to the shared slot.  Delegate to the TAssignment path via a borrowed
      synthetic node (Expr nilled before Free so the shared expression is not
      released twice) — reuses the scalar / class-ARC / interface store logic. }
    if FA.IsClassVarWrite then
    begin
      CVStore := TAssignment.Create();
      try
        CVStore.Name            := FA.ClassVarEmitName;
        CVStore.IsGlobal        := True;
        CVStore.ResolvedLhsType := FA.ClassVarLhsType;
        CVStore.Expr            := FA.Expr;
        Self.EmitStmt(CVStore);
      finally
        CVStore.Expr := nil;
        CVStore.Free();
      end;
      Exit;
    end;
    { Interface property write: I.Prop := V — FieldName holds the SETTER
      (rewritten by semantic); dispatch through the itab with V as the
      single argument. }
    if FA.IntfWriteDesc <> nil then
    begin
      IntfArgs := TObjectList.Create(False);
      try
        IntfArgs.Add(FA.Expr);
        Self.EmitInterfaceCall(FA.RecordName, FA.IsGlobal, FA.IsVarParam,
          TInterfaceTypeDesc(FA.IntfWriteDesc), FA.FieldName, IntfArgs);
      finally
        IntfArgs.Free();
      end;
      Exit;
    end;
    if FA.PropWriteInfo <> nil then
    begin
      { Owned-transient string value
        (BUG-20260721-propsetter-owned-transient-str-leak): the setter
        borrows the value, so the caller must dispose it.  An rc=0 unowned
        transient (concat / builtin result) is pinned BEFORE the call — a
        by-value setter param's own entry-retain/exit-release cycle would
        otherwise free it during the call, making any post-call disposal a
        double-free (a non-storing setter like TStringList.SetText exposes
        this).  The matching release follows the call; an rc=1 owned
        transient needs only that release.  Parked in callee-saved %rbx. }
      PropRelStr := TPropertyInfo(FA.PropWriteInfo).TypeDesc.IsString() and
                    ArcBuiltinStrArgOwnsRef(FA.Expr);
      if PropRelStr then
        Self.Emit(#9'pushq %rbx');
      Self.EmitExprToEax(FA.Expr);
      if PropRelStr then
      begin
        Self.Emit(#9'movq %rax, %rbx');
        if ArcExprIsUnownedStrTransient(FA.Expr) then
        begin
          Self.Emit(#9'movq %rbx, %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'movq %rbx, %rax');
        end;
      end;
      Self.Emit(#9'pushq %rax');
      if FA.ObjExpr <> nil then
      begin
        { Receiver is an arbitrary expression (default-property write through a
          property/field result): its value is the object pointer. }
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rdi');
      end
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rdi', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rdi), %rdi');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rdi');
        if FA.IsClassAccess and FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rdi), %rdi');
      end;
      if FA.PropIndexExpr <> nil then
      begin
        Self.Emit(#9'pushq %rdi');
        Self.EmitExprToEax(FA.PropIndexExpr);
        Self.Emit(#9'popq %rdi');
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(#9'popq %rdx');
      end
      else
        Self.Emit(#9'popq %rsi');
      Self.EmitPropAccessorCallNative(FA.PropOwnerType,
        FA.PropWriteInfo.WriteMethod, FA.PropAccessorVSlot);
      if PropRelStr then
      begin
        { Release the transient pinned (rc=0) or owned (rc=1) above. }
        Self.Emit(#9'movq %rbx, %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rbx');
      end;
      Exit;
    end;
    if FA.FieldInfo = nil then
      raise ENativeCodeGenError.Create(
        'native backend: field assignment has no resolved field info');
    { Element write into an array-typed field: Receiver.Field[Idx] := V.
      Evaluate the value, the scaled index, then the field slot address;
      for a dynamic array deref the slot to reach the data pointer; store
      by ELEMENT type with the same ARC rules as plain subscript writes. }
    if FA.IsElemWrite then
    begin
      if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
        DAElemType := TDynArrayTypeDesc(FA.FieldInfo.TypeDesc).ElementType
      else
        DAElemType := TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).ElementType;
      { Interface element: a two-slot fat pointer — the generic path below
        stored only 8 bytes (the obj), leaving the element's itab garbage
        (BUG-20260721-fieldaccess-intf-array-elem-read).  VALUE-FIRST: the
        RHS is evaluated into a zeroed 16-byte stack temp via
        EmitInterfaceToFieldSlotsAt (retain-new against a nil old — the
        RHS may reallocate the very dyn-array field being stored into, so
        the element address must be computed AFTER it runs), then the
        element address is derived fresh, the old obj released, and the
        owned pair moved in with a raw 16-byte copy. }
      if DAElemType.Kind = tyInterface then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'subq $16, %rsp');
        Self.Emit(#9'movq $0, (%rsp)');
        Self.Emit(#9'movq $0, 8(%rsp)');
        Self.Emit(#9'movq %rsp, %rbx');    { temp pair address }
        Self.EmitInterfaceToFieldSlotsAt(FA.Expr, '%rbx', 0, DAElemType);
        { Element address → %rcx, fresh (post-RHS), per receiver shape. }
        Self.EmitExprToEax(FA.PropIndexExpr);
        if (FA.FieldInfo.TypeDesc.Kind = tyStaticArray) and
           (TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).LowBound <> 0) then
          Self.Emit(Format(#9'subq $%d, %%rax',
            [TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).LowBound]));
        Self.Emit(#9'imulq $16, %rax');
        Self.Emit(#9'pushq %rax');         { scaled element offset }
        if FA.ObjExpr <> nil then
        begin
          Self.EmitExprToEax(FA.ObjExpr);
          Self.Emit(#9'movq %rax, %rcx');
        end
        else if FSretFunc and (FA.RecordName = 'Result') then
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
        else if FA.IsImplicitSelf then
        begin
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
          if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
            Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
          if FA.IsClassAccess then
            Self.Emit(#9'movq (%rcx), %rcx');
        end
        else if FA.IsClassAccess then
        begin
          Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
          if FA.IsVarParam then
            Self.Emit(#9'movq (%rcx), %rcx');
        end
        else if FA.IsVarParam then
        begin
          Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        end
        else Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
        if FA.FieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.FieldInfo.Offset]));
        if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
          Self.Emit(#9'movq (%rcx), %rcx'); { heap data pointer (fresh) }
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'addq %rax, %rcx');     { element address }
        { Release the element's old obj, then move the owned pair in. }
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'movq %rsp, %rbx');     { re-derive temp (rsp unmoved) }
        Self.Emit(#9'movq (%rbx), %rax');
        Self.Emit(#9'movq %rax, (%rcx)');
        Self.Emit(#9'movq 8(%rbx), %rax');
        Self.Emit(#9'movq %rax, 8(%rcx)');
        Self.Emit(#9'addq $16, %rsp');
        Self.Emit(#9'popq %rbx');
        Exit;
      end;
      if DAElemType.Kind in [tyByte, tyBoolean] then
        Self.EmitByteRhsToEax(FA.Expr)
      else
        Self.EmitExprToEax(FA.Expr);
      Self.Emit(#9'pushq %rax');           { value (or record src addr) }
      Self.EmitExprToEax(FA.PropIndexExpr);
      if (FA.FieldInfo.TypeDesc.Kind = tyStaticArray) and
         (TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).LowBound <> 0) then
        Self.Emit(Format(#9'subq $%d, %%rax',
          [TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).LowBound]));
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      Self.Emit(#9'pushq %rax');           { scaled element offset }
      { Field slot address → %rdx, per receiver shape. }
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rdx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rdx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rdx), %rdx');
      end
      else if FA.IsClassAccess or FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rdx');
        if FA.IsClassAccess and FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rdx), %rdx');
      end
      else
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rdx');
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FA.FieldInfo.Offset]));
      if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
        Self.Emit(#9'movq (%rdx), %rdx');  { data pointer }
      Self.Emit(#9'popq %rax');            { scaled offset }
      Self.Emit(#9'addq %rax, %rdx');
      Self.Emit(#9'movq %rdx, %rcx');      { element address }
      if (DAElemType.Kind = tyRecord) or IsJumboSet(DAElemType) then
      begin
        { Record element: ARC-aware copy (retain src fields, release dest
          fields, memcpy).  Source record address is on the stack. }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'subq $8, %rsp');
        Self.Emit(#9'movq %rcx, %r15');      { dest element addr }
        Self.Emit(#9'movq 24(%rsp), %rbx');  { src record addr }
        { A jumbo set is a plain byte bitmap — no managed fields to ARC. }
        if DAElemType.Kind = tyRecord then
        begin
          Self.EmitRecordFieldRetains(TRecordTypeDesc(DAElemType), '%rbx');
          Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%r15', False);
        end;
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [DAElemType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'popq %r15');
        Self.Emit(#9'popq %rbx');
        Self.Emit(#9'addq $8, %rsp');        { drop saved src addr }
        Exit;
      end;
      { Retain the new element only when the RHS does not already own +1 —
        an owned call result transfers its reference (mirrors the QBE and
        arm64 element stores and scalar field assignment). }
      if DAElemType.Kind = tyString then
      begin
        Self.Emit(#9'pushq %rcx');
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
        end;
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
      end
      else if DAElemType.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
      end;
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar('(%rcx)', DAElemType);
      Exit;
    end;
    { Interface-typed field: store a two-slot fat pointer (obj + itab), not a
      single value.  Compute the destination record/object base into %rcx for
      each receiver shape, then hand off to EmitInterfaceToFieldSlotsAt (which
      evaluates the RHS itself and applies ARC on the obj slot). }
    if FA.FieldInfo.TypeDesc.Kind = tyInterface then
    begin
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
      end
      else Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      Self.EmitInterfaceToFieldSlotsAt(FA.Expr, '%rcx', FA.FieldInfo.Offset,
        FA.FieldInfo.TypeDesc);
      Exit;
    end;
    { Method-pointer (of object) field assignment from @Obj.Method: store the
      [CodePtr, ObjPtr] pair into the field's 16-byte slot.  Mirrors the
      simple-variable case in EmitAssignment; the only difference is that the
      destination is a field, so its containing-object base is computed per
      receiver shape (exactly as the interface-field store above does). }
    if (FA.FieldInfo.TypeDesc.Kind = tyProcedural) and
       TProceduralTypeDesc(FA.FieldInfo.TypeDesc).IsMethodPtr and
       (FA.Expr is TAddrOfExpr) and
       (TAddrOfExpr(FA.Expr).Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr).ResolvedType <> nil) and
       (TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr).ResolvedType.Kind = tyProcedural) and
       TProceduralTypeDesc(TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr).ResolvedType).IsMethodPtr then
    begin
      FAE := TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr);
      MD  := TMethodDecl(FAE.ResolvedMethod);
      { Destination field's containing-object base → %rcx, per receiver shape. }
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
      end
      else Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FA.FieldInfo.Offset]));
      { Store the captured object pointer at offset 8 first — a virtual method
        reads its code pointer from THIS instance's vtable. }
      if FAE.Base <> nil then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end;
      { Store the code pointer at offset 0.  A virtual/override method must be
        resolved through the instance's vtable so @Obj.M captures the dynamic
        type's override — matching a direct Obj.M() call — instead of freezing
        the static address.  Slot 0 of the vtable is typeinfo, so method N is
        at offset (N+1)*8. }
      if MD.VTableSlot >= 0 then
      begin
        Self.Emit(#9'movq 8(%rcx), %rax');     { obj  = data slot }
        Self.Emit(#9'movq (%rax), %rax');      { vptr = obj[0] }
        Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      end
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [MethodEmitNameNative(MD, MD.OwnerTypeName, FAE.FieldName)]));
      Self.Emit(#9'movq %rax, (%rcx)');
      Exit;
    end;
    { Field := MethodCall() where the method returns a record (or method ptr)
      via the aggregate-return ABI.  Compute the field address into %rbx
      (callee-saved), release managed fields of the old record (none for a
      method ptr), then call with %rbx as the destination.  A method-ptr field
      is a 16-byte [Code; Data] slot captured via rcInt2 by EmitMethodSretCall. }
    if ((FA.FieldInfo.TypeDesc.Kind = tyRecord) or
        IsMethodPtrType(FA.FieldInfo.TypeDesc)) and
       (FA.Expr is TMethodCallExpr) and
       (TMethodCallExpr(FA.Expr).ResolvedMethod <> nil) and
       (TMethodDecl(TMethodCallExpr(FA.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
       ((TMethodDecl(TMethodCallExpr(FA.Expr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) or
        IsMethodPtrType(TMethodDecl(TMethodCallExpr(FA.Expr).ResolvedMethod).ResolvedReturnType)) then
    begin
      Self.Emit(#9'pushq %rbx');
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rbx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rbx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rbx');
      end;
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rbx', [FA.FieldInfo.Offset]));
      if FA.FieldInfo.TypeDesc.Kind = tyRecord then
        Self.EmitRecordFieldReleases(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%rbx');
      Self.EmitMethodSretCall(TMethodCallExpr(FA.Expr), '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { Field := FuncCall() where the function returns a record (or method ptr). }
    if ((FA.FieldInfo.TypeDesc.Kind = tyRecord) or
        IsMethodPtrType(FA.FieldInfo.TypeDesc)) and
       (FA.Expr is TFuncCallExpr) and
       (TFuncCallExpr(FA.Expr).ResolvedDecl <> nil) and
       (TMethodDecl(TFuncCallExpr(FA.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
       ((TMethodDecl(TFuncCallExpr(FA.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyRecord) or
        IsMethodPtrType(TMethodDecl(TFuncCallExpr(FA.Expr).ResolvedDecl).ResolvedReturnType)) then
    begin
      Self.Emit(#9'pushq %rbx');
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rbx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rbx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsVarParam then
      begin
        { var-param record base: the slot holds the record's ADDRESS — load it,
          do not leaq the slot itself (that wrote the sret result over the
          caller's stack; the method-call and prop-getter arms already had
          this case). }
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rbx');
      end;
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rbx', [FA.FieldInfo.Offset]));
      if FA.FieldInfo.TypeDesc.Kind = tyRecord then
        Self.EmitRecordFieldReleases(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%rbx');
      Self.EmitFuncCallSret(TFuncCallExpr(FA.Expr), '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { Field := <record-returning property getter> (indexed or not, including
      the default-subscript form): a getter call, routed through
      EmitRecordCallSretAt with the field address as the sret destination —
      the arms above only matched explicit method/function call nodes, so a
      TFieldAccessExpr PropRead RHS fell through and mishandled the sret
      buffer (BUG-20260721-native-recprop-into-recfield). }
    if (FA.FieldInfo.TypeDesc.Kind = tyRecord) and
       ((FA.Expr is TFieldAccessExpr) or (FA.Expr is TStringSubscriptExpr)) and
       Self.IsNativeRecordCall(FA.Expr) then
    begin
      Self.Emit(#9'pushq %rbx');
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rbx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rbx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rbx');
      end;
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rbx', [FA.FieldInfo.Offset]));
      Self.EmitRecordFieldReleases(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%rbx');
      Self.EmitRecordCallSretAt(FA.Expr, '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { General method-pointer / closure field store: Field := <ident|literal>.
      The RHS evaluates to the ADDRESS of a 16-byte (Code, Data) fat value
      (EmitExprToEax yields block addresses for fat-proc idents and
      materialised literals).  For a 'reference to' field the Data half is a
      strong env reference: retain the new env, release the old one, then
      copy both halves.  Mirrors the QBE EmitFieldAssignment arm. }
    if IsMethodPtrType(FA.FieldInfo.TypeDesc) then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'pushq %r12');
      { RHS address -> %r12 (callee-saved; survives the ARC calls).  A nil
        RHS has no source block: %r12 = 0 marks the zero-both-halves path. }
      if FA.Expr is TNilLiteral then
        Self.Emit(#9'xorl %r12d, %r12d')
      else
      begin
        if FA.Expr is TAnonMethodExpr then
          Self.EmitAnonValueToSlot(TAnonMethodExpr(FA.Expr))
        else
          Self.EmitExprToEax(FA.Expr);
        Self.Emit(#9'movq %rax, %r12');
      end;
      { Field address -> %rbx. }
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rbx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rbx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
        if FA.IsVarParam then
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsVarParam then
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx')
      else
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rbx');
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rbx', [FA.FieldInfo.Offset]));
      LNilStore := Self.NewLabel('fpnil');
      LSkipAdd := Self.NewLabel('fpskipadd');
      LDone := Self.NewLabel('fpdone');
      if TProceduralTypeDesc(FA.FieldInfo.TypeDesc).IsReference then
      begin
        Self.Emit(#9'testq %r12, %r12');
        Self.Emit(Format(#9'jz %s', [LSkipAdd]));
        Self.Emit(#9'movq 8(%r12), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(LSkipAdd + ':');
        Self.Emit(#9'movq 8(%rbx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
      end;
      Self.Emit(#9'testq %r12, %r12');
      Self.Emit(Format(#9'jz %s', [LNilStore]));
      Self.Emit(#9'movq (%r12), %rax');
      Self.Emit(#9'movq %rax, (%rbx)');
      Self.Emit(#9'movq 8(%r12), %rax');
      Self.Emit(#9'movq %rax, 8(%rbx)');
      Self.Emit(Format(#9'jmp %s', [LDone]));
      Self.Emit(LNilStore + ':');
      Self.Emit(#9'movq $0, (%rbx)');
      Self.Emit(#9'movq $0, 8(%rbx)');
      Self.Emit(LDone + ':');
      Self.Emit(#9'popq %r12');
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    if IsFloatFamily(FA.FieldInfo.TypeDesc) then
    begin
      Self.EmitExprToXmm0(FA.Expr);
      { An integer RHS (and any Double sub-expression) lands in %xmm0 as a
        DOUBLE; a Single field needs it narrowed (cvtsd2ss) before the movss
        store, else only the low 32 bits of the double are written — garbage.
        Mirrors the QBE swtof/truncd field-store conversion. }
      Self.EmitXmm0WidthAdjust(FA.Expr.ResolvedType,
        FA.FieldInfo.TypeDesc.Kind = tySingle);
      if FA.ObjExpr <> nil then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else if FA.IsClassAccess then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else if FA.IsVarParam then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      end;
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FA.FieldInfo.Offset]));
      Self.EmitStoreFloat('(%rcx)', FA.FieldInfo.TypeDesc);
      Exit;
    end;
    { Record-typed field := record value: full copy with ARC (retain the
      source's managed fields, release the destination's, then memcpy).
      The scalar tail below would store just the source ADDRESS — an
      8-byte pointer write masquerading as a record copy. }
    if (FA.FieldInfo.TypeDesc.Kind = tyRecord) or
       IsJumboSet(FA.FieldInfo.TypeDesc) then
    begin
      Self.EmitExprToEax(FA.Expr);       { source record / bitmap address }
      Self.Emit(#9'pushq %rax');
      { Destination field address -> %rcx per receiver shape. }
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsClassAccess or FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsClassAccess and FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FA.FieldInfo.Offset]));
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'pushq %r15');
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movq %rcx, %r15');      { dest field addr }
      Self.Emit(#9'movq 24(%rsp), %rbx');  { src record addr }
      { A jumbo set is a plain byte bitmap with no managed fields — only a
        record carries per-field ARC. }
      if FA.FieldInfo.TypeDesc.Kind = tyRecord then
      begin
        Self.EmitRecordFieldRetains(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%r15', False);
      end;
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'movq %rbx, %rsi');
      Self.Emit(Format(#9'movq $%d, %%rdx',
        [FA.FieldInfo.TypeDesc.RawSize()]));
      Self.Emit(#9'callq memcpy');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'popq %r15');
      Self.Emit(#9'popq %rbx');
      Self.Emit(#9'addq $8, %rsp');        { drop saved src addr }
      Exit;
    end;
    Self.EmitExprToEax(FA.Expr);
    { Chained field assignment: ObjExpr is the receiver expression (e.g. DT.Date
      or H.R.Obj).  Emit the receiver to get the base address, then store at the
      field offset — with ARC for managed fields (interface fields are handled by
      the unified block above and never reach here). }
    if FA.ObjExpr <> nil then
    begin
      if FA.FieldInfo.TypeDesc.IsString()
         or (FA.FieldInfo.TypeDesc.Kind = tyClass)
         or (FA.FieldInfo.TypeDesc.Kind = tyDynArray) then
      begin
        { Managed field: retain new (string/dyn-array only when the RHS does not
          already own +1; class stays unconditional — see the IsClassAccess
          branch), release old, store.  %r15 (callee-saved, preserved) holds the
          receiver base across the ARC calls; the new value sits on the stack. }
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'pushq %rax');            { new value }
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %r15');       { receiver base }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq (%rsp), %rdi');   { new value }
          if FA.FieldInfo.TypeDesc.IsString() then
            Self.Emit(#9'callq _StringAddRef')
          else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
            Self.Emit(#9'callq _DynArrayAddRef')
          else
            Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(Format(#9'movq %d(%%r15), %%rdi', [FA.FieldInfo.Offset]));
        if FA.FieldInfo.TypeDesc.IsString() then
          Self.Emit(#9'callq _StringRelease')
        else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
          Self.Emit(#9'callq _DynArrayRelease')
        else
          Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');             { new value }
        Self.Emit(#9'movq %r15, %rcx');
        Self.Emit(#9'popq %r15');             { restore caller's %r15 }
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end;
    end
    else if FSretFunc and (FA.RecordName = 'Result') then
    begin
      if FA.FieldInfo.TypeDesc.IsString()
         or (FA.FieldInfo.TypeDesc.Kind = tyClass)
         or (FA.FieldInfo.TypeDesc.Kind = tyDynArray) then
      begin
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'pushq %rax');
        Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Result')]));
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          if FA.FieldInfo.TypeDesc.IsString() then
            Self.Emit(#9'callq _StringAddRef')
          else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
            Self.Emit(#9'callq _DynArrayAddRef')
          else
            Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(Format(#9'movq %d(%%r15), %%rdi', [FA.FieldInfo.Offset]));
        if FA.FieldInfo.TypeDesc.IsString() then
          Self.Emit(#9'callq _StringRelease')
        else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
          Self.Emit(#9'callq _DynArrayRelease')
        else
          Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %r15, %rcx');
        Self.Emit(#9'popq %r15');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]));
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end;
    end
    else if FA.IsClassAccess or FA.IsImplicitSelf then
    begin
      Self.Emit(#9'pushq %rax');
      if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end;
      if FA.FieldInfo.IsUnretained and (FA.FieldInfo.TypeDesc.Kind = tyClass) then
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
        if NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _ClassRelease');
        end;
      end
      else if FA.FieldInfo.IsWeak then
      begin
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(#9'callq _WeakAssign');
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyClass then
      begin
        { ARC: addref(new) unless the RHS already owns +1 (call results
          transfer ownership), release(old), store new. }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _ClassAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.IsString() then
      begin
        { When the RHS already owns +1 (a call result), the field consumes that
          transferred reference and must NOT AddRef again — otherwise the buffer
          leaks one ref per store.  The old field contents are released
          unconditionally. }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        { Dynamic-array field: same ARC shape as String — retain new buffer,
          release the old, store.  Skip the retain when the RHS already owns +1. }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _DynArrayAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end;
    end
    else if FA.IsVarParam then
    begin
      Self.Emit(#9'pushq %rax');
      Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
      if FA.FieldInfo.TypeDesc.IsString() then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'popq %rcx');
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _DynArrayAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end;
    end
    else
    begin
      Self.Emit(#9'pushq %rax');
      Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      if FA.FieldInfo.TypeDesc.IsString() then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'popq %rcx');
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _DynArrayAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end;
    end;
    Exit;
  end;

  if AStmt is TStaticSubscriptAssign then
  begin
    SSA := TStaticSubscriptAssign(AStmt);
    { Default array property write: Obj[I] := V lowered to a setter call.
      Args: receiver %rdi, index %rsi, value %rdx (System V).  Evaluate value
      and index first (they clobber registers), stash on the stack, then load
      the receiver and reload the args. }
    if SSA.PropWriteInfo <> nil then
    begin
      { Owned-transient string value: rc=0 shapes pinned BEFORE the call,
        released after; parked in %rbx — see the TFieldAssignment
        property-write arm
        (BUG-20260721-propsetter-owned-transient-str-leak). }
      PropRelStr := TPropertyInfo(SSA.PropWriteInfo).TypeDesc.IsString() and
                    ArcBuiltinStrArgOwnsRef(SSA.ValueExpr);
      if PropRelStr then
        Self.Emit(#9'pushq %rbx');
      Self.EmitExprToEax(SSA.ValueExpr);       { value }
      if PropRelStr then
      begin
        Self.Emit(#9'movq %rax, %rbx');
        if ArcExprIsUnownedStrTransient(SSA.ValueExpr) then
        begin
          Self.Emit(#9'movq %rbx, %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'movq %rbx, %rax');
        end;
      end;
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(SSA.IndexExpr);       { index }
      Self.Emit(#9'pushq %rax');
      if SSA.IsImplicitSelf then
      begin
        { Self.Field[I] := V — load Self, reach the field slot, deref to the
          field's class object (the setter receiver). }
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rdi', [SSA.ImplicitFieldInfo.Offset]));
        Self.Emit(#9'movq (%rdi), %rdi');
      end
      else
      begin
        Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rdi');
        if SSA.IsVarParam then
          Self.Emit(#9'movq (%rdi), %rdi');      { var-param: slot -> instance }
      end;
      Self.Emit(#9'popq %rsi');                { index }
      Self.Emit(#9'popq %rdx');                { value }
      Self.EmitPropAccessorCallNative(SSA.PropOwnerType,
        TPropertyInfo(SSA.PropWriteInfo).WriteMethod, SSA.PropAccessorVSlot);
      if PropRelStr then
      begin
        { Release the transient pinned (rc=0) or owned (rc=1) above. }
        Self.Emit(#9'movq %rbx, %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rbx');
      end;
      Exit;
    end;
    if (SSA.ResolvedArrayType <> nil) and
       (SSA.ResolvedArrayType.Kind = tyString) then
    begin
      { String subscript write S[I] := ch with copy-on-write.  %rbx holds the
        address of the slot that stores the string's data pointer (a
        local/global slot directly, or the caller's variable address for a
        var/out param).  _StringUnique returns a uniquely-owned writable
        pointer (releasing the old one when it copies); store it back so the
        slot keeps exactly one owned reference, then storeb into it.  Without
        the COW, writing a literal-backed string would hit read-only memory. }
      Self.EmitByteRhsToEax(SSA.ValueExpr);
      Self.Emit(#9'pushq %rax');                  { [rsp] = byte value }
      Self.EmitExprToEax(SSA.IndexExpr);
      Self.Emit(#9'pushq %rax');                  { [rsp] = index }
      { Preserve %rbx and keep %rsp 16-aligned across the call: pushing %rbx
        alone (3rd push) would misalign, so reserve a paired 8-byte pad. }
      Self.Emit(#9'pushq %rbx');                  { preserve %rbx }
      Self.Emit(#9'subq $8, %rsp');               { align to 16 }
      { %rbx := address of the slot holding the data pointer. }
      Self.EmitVarBaseToReg(SSA.ArrayName, True, '%rbx');
      if SSA.IsVarParam then
        { var/out param: slot holds the caller variable's address; that is
          where the string pointer actually lives. }
        Self.Emit(#9'movq (%rbx), %rbx');
      Self.Emit(#9'movq (%rbx), %rdi');           { old data pointer }
      Self.Emit(#9'callq _StringUnique');         { %rax = unique pointer }
      Self.Emit(#9'movq %rax, (%rbx)');           { write back to slot }
      Self.Emit(#9'movq %rax, %rcx');             { %rcx = unique base }
      Self.Emit(#9'addq $8, %rsp');               { drop alignment pad }
      Self.Emit(#9'popq %rbx');                   { restore %rbx }
      Self.Emit(#9'popq %rax');                   { index }
      Self.Emit(#9'addq %rax, %rcx');
      Self.Emit(#9'popq %rax');                   { byte value }
      Self.Emit(#9'movb %al, (%rcx)');
      Exit;
    end;
    if (SSA.ResolvedArrayType <> nil) and
       (SSA.ResolvedArrayType.Kind = tyPChar) then
    begin
      { PChar subscript write: P[I] := byte — storeb at base + I.  PChar is a
        raw pointer with no ARC header (the slot holds it directly). }
      Self.EmitByteRhsToEax(SSA.ValueExpr);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(SSA.IndexExpr);
      Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rcx');
      if SSA.IsVarParam then
        { var/out param: slot -> caller var -> char pointer. }
        Self.Emit(#9'movq (%rcx), %rcx');
      Self.Emit(#9'addq %rax, %rcx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movb %al, (%rcx)');
      Exit;
    end;
    if (SSA.ResolvedArrayType <> nil) and
       (SSA.ResolvedArrayType.Kind in [tyDynArray, tyOpenArray]) then
    begin
      { Open arrays share the dynamic-array element-write path: both address the
        element as data_ptr + I*elemsize.  The one difference is the var-param
        deref below — an open-array param slot already holds the data pointer
        directly, so it must NOT be dereferenced a second time (issue #130
        bug5). }
      if SSA.ResolvedArrayType.Kind = tyOpenArray then
        DAElemType := TOpenArrayTypeDesc(SSA.ResolvedArrayType).ElementType
      else
      DAElemType := TDynArrayTypeDesc(SSA.ResolvedArrayType).ElementType;
      { Chained / multi-dimensional write A[I][J] := V where the inner array
        is itself a dynamic array: BaseExpr (A[I]) evaluates to the inner
        dynarray value — its data pointer.  Stash it on the stack so index
        and value evaluation below can clobber registers freely; the
        base-resolve steps then reload it instead of a named slot. }
      if SSA.BaseExpr <> nil then
      begin
        Self.EmitExprToEax(SSA.BaseExpr);
        Self.Emit(#9'pushq %rax');             { stack: [baseptr] }
      end;
      { Record-returning call as the RHS: sret directly into the element —
        EmitExprToEax cannot evaluate a record call (the callee writes its
        Result through the hidden sret pointer, which would be garbage). }
      if (DAElemType.Kind = tyRecord) and Self.IsNativeRecordCall(SSA.ValueExpr) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.EmitExprToEax(SSA.IndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
        if SSA.BaseExpr <> nil then
          { Base ptr pushed before %rbx: now at 8(%rsp). }
          Self.Emit(#9'movq 8(%rsp), %rcx')
        else if SSA.IsImplicitSelf then
        begin
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
          if SSA.ImplicitFieldInfo.Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
          Self.Emit(#9'movq (%rcx), %rcx');
        end
        else if Self.IsLocal(SSA.ArrayName) then
        begin
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]));
          if SSA.IsVarParam then
            { var/out param: slot -> caller var -> data pointer. }
            Self.Emit(#9'movq (%rcx), %rcx');
        end
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [Self.GlobalSymName(SSA.ArrayName)]));
        Self.Emit(#9'addq %rcx, %rax');
        Self.Emit(#9'movq %rax, %rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%rbx');
        Self.EmitRecordCallSretAt(SSA.ValueExpr, '(%rbx)');
        Self.Emit(#9'popq %rbx');
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'addq $8, %rsp');         { drop stashed base ptr }
        Exit;
      end;
      { Interface element write into a dyn-array (Arr[I] := V): a 16-byte fat
        pointer (obj at +0, itab at +8).  Compute the element address (data_ptr
        + idx*16, no LowBound) into callee-saved %r14 and delegate to
        EmitInterfaceToFieldSlotsAt, which writes obj+itab with ARC — the same
        discipline as the static-array interface arm below
        (BUG-20260720-qbe-dynarray-intf-elem-read / -ownership-divergence). }
      if DAElemType.Kind = tyInterface then
      begin
        Self.Emit(#9'pushq %r14');
        Self.EmitExprToEax(SSA.IndexExpr);
        Self.Emit(#9'imulq $16, %rax');
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'movq 8(%rsp), %r14')     { base ptr pushed before %r14 }
        else if SSA.IsImplicitSelf then
        begin
          Self.Emit(Format(#9'movq %s, %%r14', [Self.VarOperand('Self')]));
          if SSA.ImplicitFieldInfo.Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%r14', [SSA.ImplicitFieldInfo.Offset]));
          Self.Emit(#9'movq (%r14), %r14');
        end
        else if Self.IsLocal(SSA.ArrayName) then
        begin
          Self.Emit(Format(#9'movq %s, %%r14', [Self.VarOperand(SSA.ArrayName)]));
          if SSA.IsVarParam then
            Self.Emit(#9'movq (%r14), %r14');
        end
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%r14',
            [Self.GlobalSymName(SSA.ArrayName)]));
        Self.Emit(#9'addq %rax, %r14');          { %r14 = element address }
        Self.EmitInterfaceToFieldSlotsAt(SSA.ValueExpr, '%r14', 0, DAElemType);
        Self.Emit(#9'popq %r14');
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'addq $8, %rsp');           { drop stashed base ptr }
        Exit;
      end;
      { Float element: evaluate the RHS into %xmm0, coerce to the element's
        width, then spill the bit pattern through %rax onto the stack (x86 has
        no push for xmm regs).  EmitExprToEax cannot evaluate a float
        expression; the integer store path (movq) would store garbage. }
      if IsFloatFamily(DAElemType) then
      begin
        Self.EmitExprToXmm0(SSA.ValueExpr);
        Self.EmitXmm0WidthAdjust(SSA.ValueExpr.ResolvedType,
                                 DAElemType.Kind = tySingle);
        Self.Emit(#9'movq %xmm0, %rax');
      end
      else if DAElemType.Kind in [tyByte, tyBoolean] then
        Self.EmitByteRhsToEax(SSA.ValueExpr)
      else
        Self.EmitExprToEax(SSA.ValueExpr);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(SSA.IndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      if SSA.BaseExpr <> nil then
        { Base ptr pushed before the value: value is on top, so the base
          sits at 8(%rsp). }
        Self.Emit(#9'movq 8(%rsp), %rcx')
      else if SSA.IsImplicitSelf then
      begin
        { ArrayName is a dyn-array field of Self: Self + offset holds the
          data pointer. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
        Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if Self.IsLocal(SSA.ArrayName) then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]));
        { An open-array param slot already holds the data pointer, so it is NOT
          dereferenced again (a var dynamic-array slot holds the caller-var
          address and does need the extra load). }
        if SSA.IsVarParam and (SSA.ResolvedArrayType.Kind <> tyOpenArray) then
          { var/out param: slot -> caller var -> data pointer. }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [Self.GlobalSymName(SSA.ArrayName)]));
      Self.Emit(#9'addq %rcx, %rax');
      Self.Emit(#9'movq %rax, %rcx');
      if IsFloatFamily(DAElemType) then
      begin
        { Float store: reload the spilled value into %xmm0, store at the
          element address with the element's width. }
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %rax, %xmm0');
        Self.EmitStoreFloat('(%rcx)', DAElemType);
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'addq $8, %rsp');         { drop stashed base ptr }
        Exit;
      end;
      if (DAElemType.Kind = tyRecord) or IsJumboSet(DAElemType) then
      begin
        { Record element: ARC-aware copy of the record contents (retain the
          source's managed fields, release the destination's, then memcpy).
          The source record address was pushed above; %rcx holds the element
          address.  Push count stays even so calls remain 16-byte aligned. }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'subq $8, %rsp');
        Self.Emit(#9'movq %rcx, %r15');        { dest element addr }
        Self.Emit(#9'movq 24(%rsp), %rbx');    { src record addr }
        { A jumbo set is a plain byte bitmap — no managed fields to ARC. }
        if DAElemType.Kind = tyRecord then
        begin
          Self.EmitRecordFieldRetains(TRecordTypeDesc(DAElemType), '%rbx');
          Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%r15', False);
        end;
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [DAElemType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'popq %r15');
        Self.Emit(#9'popq %rbx');
        Self.Emit(#9'addq $8, %rsp');          { drop saved src addr }
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'addq $8, %rsp');         { drop stashed base ptr }
        Exit;
      end;
      { Retain the new element only when the RHS does not already own +1 —
        an owned call result transfers its reference (mirrors the QBE and
        arm64 element stores and scalar assignment). }
      if DAElemType.Kind = tyString then
      begin
        Self.Emit(#9'pushq %rcx');
        if not NativeExprOwnsRef(SSA.ValueExpr) then
        begin
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
        end;
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
      end
      else if DAElemType.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        if not NativeExprOwnsRef(SSA.ValueExpr) then
        begin
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
      end;
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar('(%rcx)', DAElemType);
      if SSA.BaseExpr <> nil then
        Self.Emit(#9'addq $8, %rsp');           { drop stashed base ptr }
      Exit;
    end;
    { Static array element write. }
    if (SSA.ResolvedArrayType = nil) or
       (SSA.ResolvedArrayType.Kind <> tyStaticArray) then
      raise ENativeCodeGenError.Create(
        'native backend: static subscript assign on non-static-array');
    DAElemType := TStaticArrayTypeDesc(SSA.ResolvedArrayType).ElementType;
    { Interface element write (Arr[I] := V): the element is a contiguous 16-byte
      fat pointer (obj at +0, itab at +8).  A plain EmitStoreVar would store only
      the 8-byte obj and leave the itab garbage, so a later dispatch/read faults.
      Compute the element address into a callee-saved register (it must survive
      the helper's ARC calls) and delegate to EmitInterfaceToFieldSlotsAt, which
      stores obj+itab with ARC for nil / class-instance / interface sources. }
    if DAElemType.Kind = tyInterface then
    begin
      Self.Emit(#9'pushq %r14');
      { Build a TStringSubscriptExpr-equivalent address: reuse the SSA fields.
        EmitIntfStaticElemAddr expects StrExpr/IndexExpr, but here the array is
        named by SSA — compute the element address inline (base + idx*16). }
      Self.EmitExprToEax(SSA.IndexExpr);
      if TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound <> 0 then
        Self.Emit(Format(#9'subq $%d, %%rax',
          [TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound]));
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      if SSA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%r14', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%r14', [SSA.ImplicitFieldInfo.Offset]));
      end
      else if SSA.IsVarParam then
        { var-param array: the slot holds the array POINTER (AWantAddress=False).
          For a captured var-param the _cap_ slot holds the address of that
          pointer slot, so EmitVarBaseToReg(False) loads it and derefs once. }
        Self.EmitVarBaseToReg(SSA.ArrayName, False, '%r14')
      else if FSretFunc and SameText(SSA.ArrayName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%r14', [Self.VarOperand(SSA.ArrayName)]))
      else
        Self.EmitVarBaseToReg(SSA.ArrayName, True, '%r14');
      Self.Emit(#9'addq %rax, %r14');          { %r14 = element address }
      Self.EmitInterfaceToFieldSlotsAt(SSA.ValueExpr, '%r14', 0, DAElemType);
      Self.Emit(#9'popq %r14');
      Exit;
    end;
    { Record-returning call RHS: sret directly into the element (see the
      dyn-array branch above). }
    if (DAElemType.Kind = tyRecord) and Self.IsNativeRecordCall(SSA.ValueExpr) then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.EmitExprToEax(SSA.IndexExpr);
      if TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound <> 0 then
        Self.Emit(Format(#9'subq $%d, %%rax',
          [TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound]));
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      if SSA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
      end
      else if SSA.IsVarParam then
        Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rcx')
      else if FSretFunc and SameText(SSA.ArrayName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]))
      else
        Self.EmitVarBaseToReg(SSA.ArrayName, True, '%rcx');
      Self.Emit(#9'addq %rcx, %rax');
      Self.Emit(#9'movq %rax, %rbx');
      Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%rbx');
      Self.EmitRecordCallSretAt(SSA.ValueExpr, '(%rbx)');
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { Chained / multi-dimensional write A[I][J] := V: evaluate BaseExpr (the
      inner-array address) first and stash it on the stack so the index
      evaluation below can clobber registers freely; the base-resolve step
      then pops it instead of loading from a named slot. }
    if SSA.BaseExpr <> nil then
    begin
      Self.EmitExprToEax(SSA.BaseExpr);
      Self.Emit(#9'pushq %rax');             { stack: [baseaddr] }
    end;
    { Float element: evaluate into %xmm0, coerce to the element width, then
      spill through %rax (see the dyn-array float branch above). }
    if IsFloatFamily(DAElemType) then
    begin
      Self.EmitExprToXmm0(SSA.ValueExpr);
      Self.EmitXmm0WidthAdjust(SSA.ValueExpr.ResolvedType,
                               DAElemType.Kind = tySingle);
      Self.Emit(#9'movq %xmm0, %rax');
    end
    else if DAElemType.Kind in [tyByte, tyBoolean] then
      Self.EmitByteRhsToEax(SSA.ValueExpr)
    else
      Self.EmitExprToEax(SSA.ValueExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SSA.IndexExpr);
    if TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound <> 0 then
      Self.Emit(Format(#9'subq $%d, %%rax',
        [TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound]));
    Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
    if SSA.BaseExpr <> nil then
    begin
      { Base address was pushed before the value: it now sits at 8(%rsp)
        (the value is on top).  Load it without disturbing the value. }
      Self.Emit(#9'movq 8(%rsp), %rcx');
    end
    else if SSA.IsImplicitSelf then
    begin
      { ArrayName is a static-array field of Self: the inline storage
        starts at Self + field offset. }
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if SSA.ImplicitFieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
    end
    else if SSA.IsVarParam then
      Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rcx')
    else if FSretFunc and SameText(SSA.ArrayName, 'Result') then
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]))
    else
      Self.EmitVarBaseToReg(SSA.ArrayName, True, '%rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movq %rax, %rcx');
    if IsFloatFamily(DAElemType) then
    begin
      { Float store: reload the spilled value into %xmm0 and store with the
        element width. }
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, %xmm0');
      Self.EmitStoreFloat('(%rcx)', DAElemType);
      if SSA.BaseExpr <> nil then
        Self.Emit(#9'addq $8, %rsp');           { drop stashed base address }
      Exit;
    end;
    if (DAElemType.Kind = tyRecord) or IsJumboSet(DAElemType) then
    begin
      { Record element: ARC-aware copy — same scheme as the dyn-array
        record branch above. }
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'pushq %r15');
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movq %rcx, %r15');        { dest element addr }
      Self.Emit(#9'movq 24(%rsp), %rbx');    { src record addr }
      { A jumbo set is a plain byte bitmap — no managed fields to ARC. }
      if DAElemType.Kind = tyRecord then
      begin
        Self.EmitRecordFieldRetains(TRecordTypeDesc(DAElemType), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%r15', False);
      end;
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'movq %rbx, %rsi');
      Self.Emit(Format(#9'movq $%d, %%rdx', [DAElemType.RawSize()]));
      Self.Emit(#9'callq memcpy');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'popq %r15');
      Self.Emit(#9'popq %rbx');
      Self.Emit(#9'addq $8, %rsp');          { drop saved src addr }
      if SSA.BaseExpr <> nil then
        Self.Emit(#9'addq $8, %rsp');         { drop stashed base address }
      Exit;
    end;
    { Retain the new element only when the RHS does not already own +1 —
      an owned call result transfers its reference (mirrors the QBE and
      arm64 element stores and scalar assignment). }
    if DAElemType.Kind = tyString then
    begin
      Self.Emit(#9'pushq %rcx');
      if not NativeExprOwnsRef(SSA.ValueExpr) then
      begin
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _StringAddRef');
      end;
      Self.Emit(#9'movq (%rsp), %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'callq _StringRelease');
      Self.Emit(#9'popq %rcx');
    end
    else if DAElemType.Kind = tyClass then
    begin
      Self.Emit(#9'pushq %rcx');
      if not NativeExprOwnsRef(SSA.ValueExpr) then
      begin
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
      end;
      Self.Emit(#9'movq (%rsp), %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rcx');
    end;
    Self.Emit(#9'popq %rax');
    Self.EmitStoreVar('(%rcx)', DAElemType);
    if SSA.BaseExpr <> nil then
      Self.Emit(#9'addq $8, %rsp');           { drop stashed base address }
    Exit;
  end;

  { P^ := Value — pointer dereference write.  Evaluate value into %rax,
    save it, evaluate pointer into %rcx, then store through (%rcx). }
  if AStmt is TPointerWriteStmt then
  begin
    if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
       TPointerWriteStmt(AStmt).BaseTy.IsString() then
    begin
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'callq _StringRelease');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringAddRef');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'movq %rax, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tyClass) then
    begin
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'callq _ClassRelease');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'movq %rax, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tyInterface) then
    begin
      { P^ := V through a ^IFoo — the slot is a contiguous 16-byte fat pointer
        (obj at +0, itab at +8).  Without this arm the store fell through to
        the scalar path, which wrote only the 8-byte obj with NO retain and
        left the itab stale: TList<IFoo> was silently non-owning and the slot
        dangled once the source variable died.  Compute the destination into
        the callee-saved %r14 (it must survive the helper's ARC calls) and
        delegate to EmitInterfaceToFieldSlotsAt, exactly as the static-array
        interface element write does. }
      Self.Emit(#9'pushq %r14');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %r14');
      Self.EmitInterfaceToFieldSlotsAt(TPointerWriteStmt(AStmt).ValExpr,
        '%r14', 0, TPointerWriteStmt(AStmt).BaseTy);
      Self.Emit(#9'popq %r14');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tyDynArray) then
    begin
      { Dynamic array through a typed pointer: same retain/release discipline
        as the string and class arms, via the dyn-array RTL entry points. }
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'callq _DynArrayRelease');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _DynArrayAddRef');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'movq %rax, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tyDouble) then
    begin
      Self.EmitExprToXmm0(TPointerWriteStmt(AStmt).ValExpr);
      { EmitExprToXmm0 leaves a Single for a tySingle RHS; widen it to the
        Double slot (cvtss2sd) so 'PDouble^ := SomeSingle' stores the value,
        not the low 32 bits of the single bit-pattern. }
      Self.EmitXmm0WidthAdjust(TPointerWriteStmt(AStmt).ValExpr.ResolvedType, False);
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movsd (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tySingle) then
    begin
      Self.EmitExprToXmm0(TPointerWriteStmt(AStmt).ValExpr);
      { EmitExprToXmm0 leaves a Double for a Double/integer RHS; narrow it to
        the Single slot (cvtsd2ss) so 'PSingle^ := SomeInteger' stores the
        value, not the low 32 bits of the double bit-pattern (which are 0 for
        small integers — the BUG-027 wrong-0). }
      Self.EmitXmm0WidthAdjust(TPointerWriteStmt(AStmt).ValExpr.ResolvedType, True);
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movss %xmm0, (%rsp)');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movss (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'movss %xmm0, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            ((TPointerWriteStmt(AStmt).BaseTy.Kind = tyRecord) or
             IsJumboSet(TPointerWriteStmt(AStmt).BaseTy)) then
    begin
      { Whole-RECORD (or whole jumbo-set bitmap) store through a typed pointer:
        ARC-aware copy (retain source fields, release dest fields, memcpy) —
        the scalar fallback below would store the aggregate's ADDRESS instead
        of its bytes (BUG-039).  Same sequence as the array-element record
        write.  A jumbo set carries no managed fields, so it skips the ARC. }
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');           { source record address }
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'pushq %r15');
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movq %rax, %r15');      { dest address }
      Self.Emit(#9'movq 24(%rsp), %rbx');  { source record address }
      if TPointerWriteStmt(AStmt).BaseTy.Kind = tyRecord then
      begin
        Self.EmitRecordFieldRetains(
          TRecordTypeDesc(TPointerWriteStmt(AStmt).BaseTy), '%rbx');
        { copy site: no-zero release so P^ := P^ (src==dest) is exact
          (BUG-20260720-managed-record-self-assign) }
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(TPointerWriteStmt(AStmt).BaseTy), '%r15', False);
      end;
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'movq %rbx, %rsi');
      Self.Emit(Format(#9'movq $%d, %%rdx',
        [TPointerWriteStmt(AStmt).BaseTy.RawSize()]));
      Self.Emit(#9'callq memcpy');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'popq %r15');
      Self.Emit(#9'popq %rbx');
      Self.Emit(#9'addq $8, %rsp');        { drop saved source address }
    end
    else
    begin
      if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
         (TPointerWriteStmt(AStmt).BaseTy.Kind in [tyByte, tyBoolean]) then
        Self.EmitByteRhsToEax(TPointerWriteStmt(AStmt).ValExpr)
      else
        Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar('(%rcx)', TPointerWriteStmt(AStmt).BaseTy);
    end;
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported statement ' + AStmt.ClassName);
end;

{ ------------------------------------------------------------------ }
{ Calls and function definitions                                       }
{ ------------------------------------------------------------------ }

{ Allocate stack storage for an inline open-array literal, fill elements in
  order, and leave a pointer to element 0 in %rax.  Returns the bytes allocated
  on the stack; caller must addq that after the call to reclaim them. }
function TX86_64Backend.EmitOpenArrayLiteral(ALit: TArrayLiteralExpr): Integer;
var
  OAType:   TOpenArrayTypeDesc;
  ElemType: TTypeDesc;
  ElemSize: Integer;
  TotalSz:  Integer;
  I:        Integer;
begin
  { 'array of const' literal: each element is a 16-byte TVarRec (VType at +0,
    VValue at +8). }
  if ALit.IsConstArray then
    Exit(Self.EmitConstArrayLiteral(ALit));

  OAType   := TOpenArrayTypeDesc(ALit.ResolvedType);
  ElemType := OAType.ElementType;
  ElemSize := ElemType.RawSize();
  TotalSz  := ALit.Elements.Count * ElemSize;
  if TotalSz < 1 then TotalSz := 1;
  { Align to 16 bytes for ABI compliance. }
  TotalSz := (TotalSz + 15) and (-16);
  Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSz]));
  Self.Emit(#9'movq %rsp, %rax');  { %rax = base of element storage }
  for I := 0 to ALit.Elements.Count - 1 do
  begin
    Self.EmitExprToEax(TASTExpr(ALit.Elements.Items[I]));
    case ElemSize of
      1: Self.Emit(Format(#9'movb %%al, %d(%%rsp)', [I * ElemSize]));
      2: Self.Emit(Format(#9'movw %%ax, %d(%%rsp)', [I * ElemSize]));
      4: Self.Emit(Format(#9'movl %%eax, %d(%%rsp)', [I * ElemSize]));
    else
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * ElemSize]));
    end;
  end;
  { Re-load %rax with the base ptr (EmitExprToEax may have clobbered it). }
  Self.Emit(#9'movq %rsp, %rax');
  Exit(TotalSz);
end;

function TX86_64Backend.EmitConstArrayLiteral(ALit: TArrayLiteralExpr): Integer;
{ Build an 'array of const' temporary on the stack: one 16-byte TVarRec per
  element (VType byte at +0, pointer-sized VValue at +8).  Borrow semantics —
  strings/objects are stored without an AddRef.  Doubles are heap-boxed (a
  PDouble in the slot) since a double does not fit the integer value slot.
  Returns the bytes subtracted from %rsp (caller restores), with %rax = base. }
var
  Count, TotalSz, I, Tag, Off: Integer;
  Elem: TASTExpr;
  EK:   TTypeKind;
begin
  Count := ALit.Elements.Count;
  if Count < 1 then
  begin
    { Empty [] — no storage; null data pointer, callee sees high = -1. }
    Self.Emit(#9'xorq %rax, %rax');
    Exit(0);
  end;
  TotalSz := Count * 16;
  TotalSz := (TotalSz + 15) and (-16);   { 16-byte ABI alignment }
  Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSz]));
  { %rbx holds the stable block base across element evaluation (callee-saved). }
  Self.Emit(#9'pushq %rbx');
  Self.Emit(#9'leaq 8(%rsp), %rbx');     { base = rsp + 8 (skip saved rbx) }
  for I := 0 to Count - 1 do
  begin
    Elem := TASTExpr(ALit.Elements.Items[I]);
    EK   := Elem.ResolvedType.Kind;
    Off  := I * 16;
    case EK of
      tyDouble, tySingle:
        begin
          Tag := 3;   { vtExtended — heap-box the double }
          Self.EmitExprToXmm0(Elem);
          { A tySingle element leaves a SINGLE in %xmm0; the box always holds
            a Double, so widen (cvtss2sd) before the movsd (BUG-027 class). }
          Self.EmitXmm0WidthAdjust(Elem.ResolvedType, False);
          Self.Emit(#9'subq $8, %rsp');
          Self.Emit(#9'movsd %xmm0, (%rsp)');   { stash the double }
          Self.Emit(#9'movl $8, %edi');
          Self.Emit(#9'callq _BlaiseGetMem');   { ptr in %rax }
          Self.Emit(#9'movsd (%rsp), %xmm0');
          Self.Emit(#9'addq $8, %rsp');
          Self.Emit(#9'movsd %xmm0, (%rax)');   { *box = double }
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyBoolean:
        begin
          Tag := 1;
          Self.EmitExprToEax(Elem);
          Self.Emit(#9'movzbl %al, %eax');
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyInteger, tyUInt32, tyByte, tySmallInt, tyWord:
        begin
          Tag := 0;   { vtInteger }
          Self.EmitExprToEax(Elem);
          Self.Emit(#9'movslq %eax, %rax');     { sign-extend to 64 bits }
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyEnum:
        begin
          Tag := 24;  { vtEnum }
          Self.EmitExprToEax(Elem);
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyInt64, tyUInt64:
        begin
          Tag := 16;  { vtInt64 }
          Self.EmitExprToEax(Elem);
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyString:
        begin
          Tag := 20;  { vtAnsiString — borrow the string data pointer }
          Self.EmitExprToEax(Elem);
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyClass, tyMetaClass:
        begin
          Tag := 7;   { vtObject — borrow the object pointer }
          Self.EmitExprToEax(Elem);
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
    else
      Tag := 5;       { vtPointer }
      Self.EmitExprToEax(Elem);
      Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
    end;
    { Store the tag byte at slot +0. }
    Self.Emit(Format(#9'movb $%d, %d(%%rbx)', [Tag, Off]));
  end;
  Self.Emit(#9'movq %rbx, %rax');   { base pointer to the TVarRec block }
  Self.Emit(#9'popq %rbx');
  Exit(TotalSz);
end;

function TX86_64Backend.ConstStrShape(AArg: TASTExpr;
  APinPlainLocals: Boolean): TConstArgMode;
var
  IE: TIdentExpr;
begin
  Result := camPin;
  if AArg = nil then Exit;
  if AArg is TStringLiteral then
    Exit(camBorrowed);
  if AArg is TIdentExpr then
  begin
    IE := TIdentExpr(AArg);
    if IE.IsImplicitSelfMethod then
      Exit(camConsume);   { bare zero-arg method call — +1 owned return }
    if IE.IsConstant then
      Exit(camBorrowed);  { named string const — immortal literal data }
    if (not IE.IsGlobal) and (IE.ParamMode = pmNone) and
       (IE.ImplicitFieldInfo = nil) and not Self.IsCaptured(IE.Name) and
       (FConstArgUnsafe.IndexOf(IE.Name) < 0) then
    begin
      { Plain local / by-value or const param: the frame's own reference
        outlives the call — unless an alias can defeat that (var/out string
        sibling param in the same signature, or unknown parameter types). }
      if APinPlainLocals then
        Exit(camPin);
      Exit(camBorrowed);
    end;
    Exit(camPin);         { global, var-param read, implicit-Self field,
                            address-taken or nested-captured local }
  end;
  if NativeExprOwnsRef(AArg) then
    Exit(camConsume);     { function/method/getter return — +1 owned temp }
end;

procedure TX86_64Backend.EmitStrDisposeFromSlot(AArg: TASTExpr;
  const ASlot: string);
begin
  if ArcExprIsUnownedStrTransient(AArg) then
  begin
    Self.Emit(Format(#9'movq %s, %%rdi', [ASlot]));
    Self.Emit(#9'callq _StringAddRef');
  end;
  Self.Emit(Format(#9'movq %s, %%rdi', [ASlot]));
  Self.Emit(#9'callq _StringRelease');
end;

procedure TX86_64Backend.EmitBuiltinStrCall1(AArg: TASTExpr; const ARtl: string;
  AResultXmm: Boolean);
begin
  Self.EmitExprToEax(AArg);
  if not ArcBuiltinStrArgOwnsRef(AArg) then
  begin
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq ' + ARtl);
    Exit;
  end;
  { Owned (+1) argument transient: park it (16 bytes keeps %rsp alignment
    unchanged), call, save the result across the release, release, restore. }
  Self.Emit(#9'subq $16, %rsp');
  Self.Emit(#9'movq %rax, (%rsp)');
  Self.Emit(#9'movq %rax, %rdi');
  Self.Emit(#9'callq ' + ARtl);
  if AResultXmm then
    Self.Emit(#9'movsd %xmm0, 8(%rsp)')
  else
    Self.Emit(#9'movq %rax, 8(%rsp)');
  Self.EmitStrDisposeFromSlot(AArg, '(%rsp)');
  if AResultXmm then
    Self.Emit(#9'movsd 8(%rsp), %xmm0')
  else
    Self.Emit(#9'movq 8(%rsp), %rax');
  Self.Emit(#9'addq $16, %rsp');
end;

procedure TX86_64Backend.EmitBuiltinStrCall2(AArg0, AArg1: TASTExpr;
  const ARtl: string);
var
  O0, O1: Boolean;
begin
  O0 := ArcBuiltinStrArgOwnsRef(AArg0);
  O1 := ArcBuiltinStrArgOwnsRef(AArg1);
  { Fast path — neither operand owned: the classic push/eval/pop sequence. }
  if not (O0 or O1) then
  begin
    Self.EmitExprToEax(AArg0);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(AArg1);
    Self.Emit(#9'movq %rax, %rsi');
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'callq ' + ARtl);
    Exit;
  end;
  { Slots: 0 = arg0, 8 = arg1, 16 = result, 24 = pad (32 keeps alignment). }
  Self.Emit(#9'subq $32, %rsp');
  Self.EmitExprToEax(AArg0);
  Self.Emit(#9'movq %rax, (%rsp)');
  Self.EmitExprToEax(AArg1);
  Self.Emit(#9'movq %rax, 8(%rsp)');
  Self.Emit(#9'movq (%rsp), %rdi');
  Self.Emit(#9'movq 8(%rsp), %rsi');
  Self.Emit(#9'callq ' + ARtl);
  Self.Emit(#9'movq %rax, 16(%rsp)');
  if O0 then
    Self.EmitStrDisposeFromSlot(AArg0, '(%rsp)');
  if O1 then
    Self.EmitStrDisposeFromSlot(AArg1, '8(%rsp)');
  Self.Emit(#9'movq 16(%rsp), %rax');
  Self.Emit(#9'addq $32, %rsp');
end;

function TX86_64Backend.IsRecCallArg(AArg: TASTExpr): Boolean;
begin
  Result := False;
  if (AArg = nil) or (AArg.ResolvedType = nil) then Exit;
  if AArg.ResolvedType.Kind <> tyRecord then Exit;
  if (AArg is TFuncCallExpr) and (TFuncCallExpr(AArg).ResolvedDecl <> nil) then
    Exit(True);
  if (AArg is TMethodCallExpr) and
     not TMethodCallExpr(AArg).IsConstructorCall then
    Exit(True);
  { A record-returning property read (Obj.Prop) is a getter call producing a
    fresh sret record — materialise it into a buffer like any record-call arg. }
  if (AArg is TFieldAccessExpr) and
     (TFieldAccessExpr(AArg).PropRead <> nil) and
     (TFieldAccessExpr(AArg).PropReadDecl <> nil) and
     (TFieldAccessExpr(AArg).PropIndexExpr = nil) then
    Exit(True);
end;

function TX86_64Backend.RecArgBufBytes(AArg: TASTExpr): Integer;
begin
  Result := (TRecordTypeDesc(AArg.ResolvedType).TotalSize() + 15) and (-16);
end;

function TX86_64Backend.ParamsHaveVarString(AParams: TObjectList): Boolean;
var
  I: Integer;
  P: TMethodParam;
begin
  Result := False;
  if AParams = nil then Exit;
  for I := 0 to AParams.Count - 1 do
  begin
    P := TMethodParam(AParams.Items[I]);
    if P.IsVarParam and (P.ResolvedType <> nil) and
       P.ResolvedType.IsString() then
      Exit(True);
  end;
end;

function TX86_64Backend.ProcParamsHaveVarString(AProcParams: TObjectList): Boolean;
var
  I: Integer;
  P: TProcParamInfo;
begin
  Result := False;
  if AProcParams = nil then Exit;
  for I := 0 to AProcParams.Count - 1 do
  begin
    P := TProcParamInfo(AProcParams.Items[I]);
    if P.IsVarParam and (P.TypeDesc <> nil) and P.TypeDesc.IsString() then
      Exit(True);
  end;
end;

function TX86_64Backend.VarFlagAt(const AFlags: string; AIndex: Integer): Boolean;
var
  I, Idx: Integer;
begin
  Result := False;
  if AFlags = '' then Exit;
  Idx := 0;
  for I := 0 to Length(AFlags) - 1 do
  begin
    if AFlags[I] = ',' then
      Idx := Idx + 1
    else if Idx = AIndex then
      Exit(AFlags[I] = '1');
  end;
end;

function TX86_64Backend.TopFrameTotal: Integer;
begin
  Result := TOALCallFrame(FOALFrames.Get(FOALFrames.Count - 1)).Total;
end;

{ File-local: does ALine start with APrefix?  Allocation-free (Emit is on the
  hot path — one call per emitted assembly line). }
function LineStartsWith(const ALine, APrefix: string): Boolean;
var
  I, PL: Integer;
begin
  PL := Length(APrefix);
  if Length(ALine) < PL then
  begin
    Result := False;
    Exit;
  end;
  for I := 0 to PL - 1 do
    if StrAt(ALine, I) <> StrAt(APrefix, I) then
    begin
      Result := False;
      Exit;
    end;
  Result := True;
end;

{ '%rax'..'%r15' when the tail of a pushq/popq line (starting at AFrom) is a
  plain 64-bit GPR operand; '' for memory/immediate operands and for
  %rsp/%rbp (frame-critical — never part of the peephole window). }
function PlainRegOperandAt(const ALine: string; AFrom: Integer): string;
var
  I, L, C: Integer;
begin
  Result := '';
  L := Length(ALine);
  if (L <= AFrom) or (StrAt(ALine, AFrom) <> 37) then   { 37 = '%' }
    Exit;
  for I := AFrom + 1 to L - 1 do
  begin
    C := StrAt(ALine, I);
    if not (((C >= 97) and (C <= 122)) or               { 'a'..'z' }
            ((C >= 48) and (C <= 57))) then             { '0'..'9' }
      Exit;
  end;
  Result := StrCopyTail(ALine, AFrom);
  if (Result = '%rsp') or (Result = '%rbp') then
    Result := '';
end;

const
  PROMO_REGS: array[0..3] of string = ('%r14', '%r15', '%rbx', '%r12');

{ Width sub-register of a promotion-pool register: W is 'b'/'w'/'l'/'q'. }
function PromoSubReg(const AReg64, W: string): string;
begin
  Result := AReg64;
  if W = 'q' then Exit;
  if AReg64 = '%rbx' then
  begin
    if W = 'b' then Exit('%bl');
    if W = 'w' then Exit('%bx');
    Exit('%ebx');                                      { l }
  end;
  { %r12/%r14/%r15: numbered registers suffix directly. }
  if W = 'l' then Exit(AReg64 + 'd');
  Result := AReg64 + W;                                { b / w }
end;

{ The pushed register of a #9'pushq %REG' line, or ''. }
function PlainPushedReg(const ALine: string): string;
begin
  Result := '';
  if LineStartsWith(ALine, #9'pushq %') then
    Result := PlainRegOperandAt(ALine, 7);   { after TAB + 'pushq ' }
end;

{ The popped register of a #9'popq %REG' line, or ''. }
function PlainPoppedReg(const ALine: string): string;
begin
  Result := '';
  if LineStartsWith(ALine, #9'popq %') then
    Result := PlainRegOperandAt(ALine, 6);   { after TAB + 'popq ' }
end;

procedure TX86_64Backend.Emit(const ALine: string);
begin
  if FPromoActive then
    Self.EmitTracked(Self.PromoRewrite(ALine))
  else
    Self.EmitTracked(ALine);
end;

procedure TX86_64Backend.EmitTracked(const ALine: string);
var
  L, C, Rem: Integer;
  Reg: string;
begin
  { --- adjacent push/pop peephole ------------------------------------
    A pended `pushq %reg` immediately followed by `popq %reg2` fuses into
    `movq %reg, %reg2` (nothing at all when reg = reg2).  Any other line
    flushes the pending push first, so instruction order is preserved. }
  if FPendingPush <> '' then
  begin
    Reg := PlainPoppedReg(ALine);
    if Reg <> '' then
    begin
      { Fuse: cancel the pended push's depth contribution; the pop is
        never emitted so it contributes nothing either. }
      FSPDepth := FSPDepth - 8;
      if Reg <> PlainPushedReg(FPendingPush) then
        inherited Emit(#9'movq ' + PlainPushedReg(FPendingPush) + ', ' + Reg);
      FPendingPush := '';
      Exit;
    end;
    Self.FlushPendingPush();
  end;
  Reg := PlainPushedReg(ALine);
  if Reg <> '' then
  begin
    { Hold the push back one line; track its depth NOW so AlignFreshBytes
      and the callq wrap pad observe the true stack depth. }
    FPendingPush := ALine;
    FSPDepth := FSPDepth + 8;
    Exit;
  end;

  L := Length(ALine);
  if (L > 1) and (StrAt(ALine, 0) = 9) then          { 9 = TAB: instruction }
  begin
    C := StrAt(ALine, 1);
    if C = 112 then                                  { 'p' }
    begin
      if LineStartsWith(ALine, #9'pushq ') then
        FSPDepth := FSPDepth + 8
      else if LineStartsWith(ALine, #9'popq ') then
        FSPDepth := FSPDepth - 8;
    end
    else if C = 115 then                             { 's' }
    begin
      if LineStartsWith(ALine, #9'subq $') then
        Self.TrackRspAdjust(ALine, 1);
    end
    else if C = 97 then                              { 'a' }
    begin
      if LineStartsWith(ALine, #9'addq $') then
        Self.TrackRspAdjust(ALine, -1);
    end
    else if C = 109 then                             { 'm' }
    begin
      { Prologue baseline: after `movq %rsp, %rbp` the return address (8)
        plus the saved %rbp (8) leave %rsp 16-aligned — depth 0.  The
        epilogue frame restore re-establishes the same point. }
      if ALine = #9'movq %rsp, %rbp' then
        FSPDepth := 0
      else if ALine = #9'movq %rbp, %rsp' then
        FSPDepth := 0;
    end
    else if C = 108 then                             { 'l' }
    begin
      if ALine = #9'leave' then
        FSPDepth := 0;
    end
    else if C = 99 then                              { 'c' }
    begin
      if LineStartsWith(ALine, #9'callq ') then
      begin
        Rem := FSPDepth mod 16;
        if Rem < 0 then
          Rem := Rem + 16;
        if Rem <> 0 then
        begin
          { Misaligned call site (odd pinned-slot count above): pad %rsp to
            a 16-byte boundary for the duration of the call.  Safe for every
            call reached here — its arguments are all in registers.  Calls
            with genuine SysV stack arguments size their overflow region via
            AlignFreshBytes, so their tracked depth is 0 mod 16 and they
            never take this branch (a pad would shift their stack args). }
          inherited Emit(Format(#9'subq $%d, %%rsp', [16 - Rem]));
          inherited Emit(ALine);
          inherited Emit(Format(#9'addq $%d, %%rsp', [16 - Rem]));
          Exit;
        end;
      end;
    end;
  end
  else if (L > 1) and (StrAt(ALine, 0) <> 46) and    { 46 = '.' }
          (StrAt(ALine, L - 1) = 58) then            { 58 = ':' }
    { A non-local label (control-flow labels are all .L-prefixed): a
      function or data entry point.  At function entry only the return
      address sits on the stack — depth 8.  Data labels never precede
      instructions, so the reset is harmless there. }
    FSPDepth := 8;
  inherited Emit(ALine);
end;

procedure TX86_64Backend.FlushPendingPush;
var
  P: string;
begin
  if FPendingPush = '' then
    Exit;
  P := FPendingPush;
  FPendingPush := '';
  { Depth was tracked when the line was pended — emit raw, no re-tracking. }
  inherited Emit(P);
end;

{ ---- Inline-area pre-scan --------------------------------------------
  Walk a function body and return the LARGEST inline scratch need (bytes)
  of any qualifying call site: (param count + 1) * 8.  Purely an
  optimistic reservation — emission re-validates each site against the
  reserved size, so a shape this walker misses degrades to a normal call
  rather than miscompiling. }
const
  INLINE_MAX_DEPTH = 2;   { matches the QBE inliner's MAX_INLINE_DEPTH }

function InlineNeedStmtD(AStmt: TASTStmt; ADepth: Integer): Integer; forward;

function InlineSiteNeed(AD: TObject; AArgCount, ADepth: Integer): Integer;
var
  MD: TMethodDecl;
  I, N: Integer;
begin
  Result := 0;
  if ADepth >= INLINE_MAX_DEPTH then Exit;
  if (AD = nil) or not (AD is TMethodDecl) then Exit;
  MD := TMethodDecl(AD);
  if not MD.IsInlineCandidate then Exit;
  if MD.Body = nil then Exit;
  if AArgCount <> MD.Params.Count then Exit;
  Result := (MD.Params.Count + 1) * 8;
  { A nested qualifying site inside the callee body stacks on top of this
    frame's slots — add the deepest such need. }
  N := 0;
  for I := 0 to MD.Body.Stmts.Count - 1 do
    if InlineNeedStmtD(TASTStmt(MD.Body.Stmts.Items[I]), ADepth + 1) > N then
      N := InlineNeedStmtD(TASTStmt(MD.Body.Stmts.Items[I]), ADepth + 1);
  Result := Result + N;
end;

function InlineNeedExprD(AExpr: TASTExpr; ADepth: Integer): Integer;
var
  I, N: Integer;
begin
  Result := 0;
  if AExpr = nil then Exit;
  if AExpr is TFuncCallExpr then
  begin
    Result := InlineSiteNeed(TFuncCallExpr(AExpr).ResolvedDecl,
      TFuncCallExpr(AExpr).Args.Count, ADepth);
    for I := 0 to TFuncCallExpr(AExpr).Args.Count - 1 do
    begin
      N := InlineNeedExprD(TASTExpr(TFuncCallExpr(AExpr).Args.Items[I]), ADepth);
      if N > Result then Result := N;
    end;
    Exit;
  end;
  if AExpr is TMethodCallExpr then
  begin
    Result := InlineNeedExprD(TMethodCallExpr(AExpr).ObjExpr, ADepth);
    for I := 0 to TMethodCallExpr(AExpr).Args.Count - 1 do
    begin
      N := InlineNeedExprD(TASTExpr(TMethodCallExpr(AExpr).Args.Items[I]), ADepth);
      if N > Result then Result := N;
    end;
    Exit;
  end;
  if (AExpr is TBinaryExpr) and (TBinaryExpr(AExpr).LoweredCall <> nil) then
    { Lowered operator: Left/Right were MOVED into the call's arg list and are
      nil here, so walk the call instead. }
    Result := InlineNeedExprD(TBinaryExpr(AExpr).LoweredCall, ADepth)
  else if AExpr is TBinaryExpr then
  begin
    Result := InlineNeedExprD(TBinaryExpr(AExpr).Left, ADepth);
    N := InlineNeedExprD(TBinaryExpr(AExpr).Right, ADepth);
    if N > Result then Result := N;
  end
  else if AExpr is TNotExpr then
    Result := InlineNeedExprD(TNotExpr(AExpr).Expr, ADepth)
  else if AExpr is TFieldAccessExpr then
  begin
    Result := InlineNeedExprD(TFieldAccessExpr(AExpr).Base, ADepth);
    N := InlineNeedExprD(TFieldAccessExpr(AExpr).PropIndexExpr, ADepth);
    if N > Result then Result := N;
  end
  else if AExpr is TDerefExpr then
    Result := InlineNeedExprD(TDerefExpr(AExpr).Expr, ADepth)
  else if AExpr is TStringSubscriptExpr then
  begin
    Result := InlineNeedExprD(TStringSubscriptExpr(AExpr).StrExpr, ADepth);
    N := InlineNeedExprD(TStringSubscriptExpr(AExpr).IndexExpr, ADepth);
    if N > Result then Result := N;
  end
  else if AExpr is TIsExpr then
    Result := InlineNeedExprD(TIsExpr(AExpr).Obj, ADepth)
  else if AExpr is TAsExpr then
    Result := InlineNeedExprD(TAsExpr(AExpr).Obj, ADepth)
  else if AExpr is TSupportsExpr then
    Result := InlineNeedExprD(TSupportsExpr(AExpr).Obj, ADepth)
  else if AExpr is TAddrOfExpr then
    Result := InlineNeedExprD(TAddrOfExpr(AExpr).Expr, ADepth)
  else if AExpr is TArrayLiteralExpr then
    for I := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
    begin
      N := InlineNeedExprD(TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[I]), ADepth);
      if N > Result then Result := N;
    end;
end;

function InlineNeedStmtD(AStmt: TASTStmt; ADepth: Integer): Integer;
var
  I, J, N: Integer;
begin
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TCompoundStmt then
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
    begin
      N := InlineNeedStmtD(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]), ADepth);
      if N > Result then Result := N;
    end
  else if AStmt is TIfStmt then
  begin
    Result := InlineNeedExprD(TIfStmt(AStmt).Condition, ADepth);
    N := InlineNeedStmtD(TIfStmt(AStmt).ThenStmt, ADepth);
    if N > Result then Result := N;
    N := InlineNeedStmtD(TIfStmt(AStmt).ElseStmt, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TWhileStmt then
  begin
    Result := InlineNeedExprD(TWhileStmt(AStmt).Condition, ADepth);
    N := InlineNeedStmtD(TWhileStmt(AStmt).Body, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TRepeatStmt then
  begin
    Result := InlineNeedExprD(TRepeatStmt(AStmt).Condition, ADepth);
    N := InlineNeedStmtD(TRepeatStmt(AStmt).Body, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TForStmt then
  begin
    Result := InlineNeedExprD(TForStmt(AStmt).StartExpr, ADepth);
    N := InlineNeedExprD(TForStmt(AStmt).EndExpr, ADepth);
    if N > Result then Result := N;
    N := InlineNeedStmtD(TForStmt(AStmt).Body, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TForInStmt then
  begin
    Result := InlineNeedExprD(TForInStmt(AStmt).CollExpr, ADepth);
    N := InlineNeedStmtD(TForInStmt(AStmt).Body, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TAssignment then
    Result := InlineNeedExprD(TAssignment(AStmt).Expr, ADepth)
  else if AStmt is TFieldAssignment then
    Result := InlineNeedExprD(TFieldAssignment(AStmt).Expr, ADepth)
  else if AStmt is TPointerWriteStmt then
  begin
    Result := InlineNeedExprD(TPointerWriteStmt(AStmt).PtrExpr, ADepth);
    N := InlineNeedExprD(TPointerWriteStmt(AStmt).ValExpr, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TStaticSubscriptAssign then
  begin
    Result := InlineNeedExprD(TStaticSubscriptAssign(AStmt).IndexExpr, ADepth);
    N := InlineNeedExprD(TStaticSubscriptAssign(AStmt).ValueExpr, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TProcCall then
  begin
    Result := InlineSiteNeed(TProcCall(AStmt).ResolvedDecl,
      TProcCall(AStmt).Args.Count, ADepth);
    for I := 0 to TProcCall(AStmt).Args.Count - 1 do
    begin
      N := InlineNeedExprD(TASTExpr(TProcCall(AStmt).Args.Items[I]), ADepth);
      if N > Result then Result := N;
    end;
  end
  else if AStmt is TMethodCallStmt then
  begin
    Result := InlineNeedExprD(TMethodCallStmt(AStmt).ObjExpr, ADepth);
    for I := 0 to TMethodCallStmt(AStmt).Args.Count - 1 do
    begin
      N := InlineNeedExprD(TASTExpr(TMethodCallStmt(AStmt).Args.Items[I]), ADepth);
      if N > Result then Result := N;
    end;
  end
  else if AStmt is TTryFinallyStmt then
  begin
    Result := InlineNeedStmtD(TTryFinallyStmt(AStmt).TryBody, ADepth);
    N := InlineNeedStmtD(TTryFinallyStmt(AStmt).FinallyBody, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TTryExceptStmt then
  begin
    Result := InlineNeedStmtD(TTryExceptStmt(AStmt).TryBody, ADepth);
    for I := 0 to TTryExceptStmt(AStmt).Handlers.Count - 1 do
    begin
      N := InlineNeedStmtD(TExceptHandlerClause(TTryExceptStmt(AStmt).Handlers.Items[I]).Body, ADepth);
      if N > Result then Result := N;
    end;
    N := InlineNeedStmtD(TTryExceptStmt(AStmt).ElseBody, ADepth);
    if N > Result then Result := N;
    N := InlineNeedStmtD(TTryExceptStmt(AStmt).ExceptBody, ADepth);
    if N > Result then Result := N;
  end
  else if AStmt is TRaiseStmt then
    Result := InlineNeedExprD(TRaiseStmt(AStmt).Expr, ADepth)
  else if AStmt is TCaseStmt then
  begin
    Result := InlineNeedExprD(TCaseStmt(AStmt).Selector, ADepth);
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
    begin
      for J := 0 to TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Values.Count - 1 do
      begin
        N := InlineNeedExprD(TASTExpr(
          TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Values.Items[J]), ADepth);
        if N > Result then Result := N;
      end;
      N := InlineNeedStmtD(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt, ADepth);
      if N > Result then Result := N;
    end;
    N := InlineNeedStmtD(TCaseStmt(AStmt).ElseStmt, ADepth);
    if N > Result then Result := N;
  end
  else if (AStmt is TExitStmt) and (TExitStmt(AStmt).ResultAssign <> nil) then
    Result := InlineNeedStmtD(TExitStmt(AStmt).ResultAssign, ADepth);
end;

function TX86_64Backend.PromoEligibleType(ATy: TTypeDesc): Boolean;
begin
  { Unmanaged scalars only: ints, enums, booleans, raw pointers.  Managed
    types (string/class/interface/dynarray/closures) must stay in frame
    slots — the ARC release walks and exception cleanup read them there. }
  Result := (ATy <> nil) and
    (IsIntFamily(ATy) or (ATy.Kind in [tyPointer, tyPChar]));
end;

procedure TX86_64Backend.ConsiderPromo(const AName: string; ATy: TTypeDesc;
  AMark: Integer; ACandNames: TStringList; ACandCounts: TList<Integer>);
var
  SlotOp: string;
  N, SlotOff: Integer;
begin
  { _inl_s scratch slots are plain 8-byte scalar slots by construction
    (inline params/Result are primitive-only); they carry no static type
    (widths come from each site's FInlineTypes at emission). }
  if not Self.PromoEligibleType(ATy) then
    if not ((Length(AName) > 6) and (StrCopyFrom(AName, 0, 6) = '_inl_s')) then
      Exit;
  if AName = 'Self' then Exit;                         { hardcoded paths }
  { Address-taken (@ / var-out arg) or captured by a nested proc: the
    slot is the contract. }
  if FConstArgUnsafe.IndexOf(AName) >= 0 then Exit;
  { A var this function itself captures FROM an enclosing frame lives
    in the OUTER frame — never register-resident here. }
  if Self.IsCaptured(AName) then Exit;
  if ACandNames.IndexOf(AName) >= 0 then Exit;
  { Rank by ACTUAL slot traffic: count the slot operand's occurrences
    in the pass-1 text.  A leading space keeps '-24(%rbp)' from
    matching inside '-124(%rbp)'.  Static text count — not loop-depth
    weighted — but it beats declaration order at zero AST-walk cost. }
  if (FFrame = nil) or not FFrame.TryGetValue(AName, SlotOff) then Exit;
  if SlotOff > 0 then
    SlotOp := Format(' %d(%%rbp)', [SlotOff])
  else
    SlotOp := Format(' -%d(%%rbp)', [-SlotOff]);
  N := Self.AsmCountFrom(AMark, SlotOp);
  { Fewer than two accesses: a register residency saves nothing over
    the slot (the prologue save/restore would cost as much). }
  if N < 2 then Exit;
  ACandNames.Add(AName);
  ACandCounts.Add(N);
end;

function TX86_64Backend.SelectPromotions(ADecl: TMethodDecl;
  AMark: Integer): Boolean;
var
  I, J, TryCount: Integer;
  P:  TMethodParam;
  VD: TVarDecl;
  CandNames: TStringList;
  CandCounts: TList<Integer>;
  Best, BestIdx: Integer;
begin
  for I := 0 to 3 do
    FPromoVars[I] := '';
  Result := False;
  { OPDF debug builds keep exact frame-slot locations for pdr. }
  if FDbgFacts <> nil then Exit;
  if ADecl.NoStackFrame or (ADecl.Body = nil) then Exit;
  { setjmp contract: locals modified after setjmp and read after longjmp
    are indeterminate in registers — any try statement disables promotion. }
  TryCount := 0;
  for I := 0 to ADecl.Body.Stmts.Count - 1 do
    TryCount := TryCount + Self.CountTryStmts(TASTStmt(ADecl.Body.Stmts.Items[I]));
  if TryCount > 0 then Exit;
  CandNames := TStringList.Create();
  CandNames.CaseSensitive := True;
  CandCounts := TList<Integer>.Create();
  try
    { Candidate order (the tie-break): params, Result, locals. }
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      P := TMethodParam(ADecl.Params.Items[I]);
      if P.IsVarParam or P.IsOpenArray then Continue;
      Self.ConsiderPromo(P.ParamName, P.ResolvedType, AMark,
        CandNames, CandCounts);
    end;
    if (ADecl.ResolvedReturnType <> nil) and not FSretFunc then
      Self.ConsiderPromo('Result', ADecl.ResolvedReturnType, AMark,
        CandNames, CandCounts);
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(ADecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
        Self.ConsiderPromo(VD.Names.Strings[J], VD.ResolvedType, AMark,
          CandNames, CandCounts);
    end;
    { Inline scratch slots: promoting the hot ones extends register
      residency INTO inlined bodies. }
    for I := 0 to FInlineSlotCount - 1 do
      Self.ConsiderPromo('_inl_s' + IntToStr(I), nil, AMark,
        CandNames, CandCounts);
    { Assign the highest-traffic candidates (stable on ties) to the
      AVAILABLE pool registers, best first. }
    for J := 0 to 3 do
    begin
      if not FPromoAvail[J] then Continue;
      Best := 0;
      BestIdx := -1;
      for I := 0 to CandNames.Count - 1 do
        if CandCounts.Get(I) > Best then
        begin
          Best := CandCounts.Get(I);
          BestIdx := I;
        end;
      if BestIdx < 0 then Break;
      FPromoVars[J] := CandNames.Strings[BestIdx];
      CandCounts.SetItem(BestIdx, 0);
    end;
  finally
    CandCounts.Free();
    CandNames.Free();
  end;
  for I := 0 to 3 do
    if FPromoVars[I] <> '' then
      Result := True;
end;

procedure TX86_64Backend.PromoInitStackParam(const AName, AReg: string);
var
  Off: Integer;
begin
  { Stack-passed params were assigned POSITIVE rbp offsets in BuildFrame;
    locals/Result/register params are negative and need no init here
    (register params spill into the promoted register via the normal
    spill code, locals via zero-init). }
  if (FFrame <> nil) and FFrame.TryGetValue(AName, Off) and (Off > 0) then
    Self.EmitLoadVarToReg(Format('%d(%%rbp)', [Off]),
      Self.LocalType(AName), AReg, AReg);
end;

{ Scratch-slot name for inline expansion (file-level, NOT a nested
  function: the release bootstrap binary miscompiles captured locals in
  nested routines — teach-then-use). }
function InlSlotName(AIdx: Integer): string;
begin
  Result := '_inl_s' + IntToStr(AIdx);
end;

function TX86_64Backend.TryEmitInlineCall(ADecl: TObject; AArgs: TObjectList;
  AWantResult: Boolean): Boolean;
var
  Callee: TMethodDecl;
  Par:    TMethodParam;
  I, Need, MyBase: Integer;
  EndL:   string;
  RetTy:  TTypeDesc;
  HasFloat: Boolean;
  OldMap: TDictionary<string, Integer>;
  OldTypes: TDictionary<string, TTypeDesc>;
  OldEnd: string;
  OldNext: Integer;

begin
  Result := False;
  if FInlineDepth >= INLINE_MAX_DEPTH then Exit;
  if FDbgFacts <> nil then Exit;                 { exact debug info }
  if (ADecl = nil) or not (ADecl is TMethodDecl) then Exit;
  Callee := TMethodDecl(ADecl);
  if not Callee.IsInlineCandidate then Exit;
  if Callee.Body = nil then Exit;
  { Phase 1 is SAME-UNIT only (as per docs/inlining-design.adoc): a
    cross-unit callee's body may reference its own unit's globals or
    threadvars, whose owner-prefixed symbols are not resolvable from
    this emission context (the async.fibers CurrentFiber threadvar bug).
    Program-level callees have OwningUnit = '' and are only callable
    from the program itself. }
  if (Callee.OwningUnit <> '') and
     not SameText(Callee.OwningUnit, FCurrentUnitName) then Exit;
  { Nested procs and closures receive HIDDEN capture/env arguments that
    are not in AArgs, and their bodies reference outer frames — never
    inline them (their captured idents would resolve as globals). }
  if Callee.EnclosingDecl <> nil then Exit;
  if Callee.IsAnonThunk then Exit;
  if (Callee.CapturedVars <> nil) and (Callee.CapturedVars.Count > 0) then Exit;
  if (Callee.EnvCaptured <> nil) and (Callee.EnvCaptured.Count > 0) then Exit;
  if (Callee.BlockEnvCaptured <> nil) and (Callee.BlockEnvCaptured.Count > 0) then Exit;
  if (AArgs = nil) or (AArgs.Count <> Callee.Params.Count) then Exit;
  if (FInlineLimit >= 0) and (FInlineCount >= FInlineLimit) then Exit;
  { This frame's slots start where the ENCLOSING inline frame (if any)
    ends; the whole stack of frames must fit the reserved slots. }
  if FInlineDepth = 0 then
    MyBase := 0
  else
    MyBase := FInlineNextIdx;
  Need := Callee.Params.Count + 1;   { slots }
  if FInlineSlotCount <= 0 then Exit;
  if MyBase + Need > FInlineSlotCount then Exit;
  { Float params/return read/write their slots with movsd/movss forms
    that cannot address a PROMOTED (register-resident) slot — bail to a
    normal call when any needed slot is register-resident this pass. }
  HasFloat := (Callee.ResolvedReturnType <> nil) and
              IsFloatFamily(Callee.ResolvedReturnType);
  for I := 0 to Callee.Params.Count - 1 do
    if IsFloatFamily(TMethodParam(Callee.Params.Items[I]).ResolvedType) then
      HasFloat := True;
  if HasFloat then
    for I := 0 to Need - 1 do
      if StrAt(Self.VarOperand(InlSlotName(MyBase + I)), 0) = 37 then   { '%': register }
        Exit;
  { Mixed int/float coercion at the boundary is the normal call path's
    job — inline only exact-family matches. }
  for I := 0 to Callee.Params.Count - 1 do
  begin
    Par := TMethodParam(Callee.Params.Items[I]);
    if IsFloatFamily(Par.ResolvedType) <>
       IsFloatFamily(TASTExpr(AArgs.Items[I]).ResolvedType) then
      Exit;
  end;

  { Stage arguments via the stack: an argument expression may itself
    contain an inlinable call (which uses the SAME scratch area while
    this site's earlier arguments are being computed), so nothing may
    land in the area until every argument value exists. }
  for I := 0 to Callee.Params.Count - 1 do
  begin
    Par := TMethodParam(Callee.Params.Items[I]);
    if IsFloatFamily(Par.ResolvedType) then
    begin
      Self.EmitExprToXmm0(TASTExpr(AArgs.Items[I]));
      Self.EmitXmm0WidthAdjust(TASTExpr(AArgs.Items[I]).ResolvedType,
        (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tySingle));
      Self.Emit(#9'movq %xmm0, %rax');
    end
    else
      Self.EmitExprToEax(TASTExpr(AArgs.Items[I]));
    Self.Emit(#9'pushq %rax');
  end;
  { All argument values exist — the area is free now.  Pop into the
    param slots (reverse order), width-correct per param type. }
  for I := Callee.Params.Count - 1 downto 0 do
  begin
    Par := TMethodParam(Callee.Params.Items[I]);
    Self.Emit(#9'popq %rax');
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tySingle) then
      Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(InlSlotName(MyBase + I))]))
    else if IsFloatFamily(Par.ResolvedType) then
      Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(InlSlotName(MyBase + I))]))
    else
      Self.EmitStoreVar(Self.VarOperand(InlSlotName(MyBase + I)), Par.ResolvedType);
  end;
  { Zero the Result slot (Blaise zero-init semantics). }
  RetTy := Callee.ResolvedReturnType;
  if RetTy <> nil then
    Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(InlSlotName(MyBase + Callee.Params.Count))]));

  FInlineCount := FInlineCount + 1;
  if FInlineLog then
    WriteLn(StdErr, '[inl] ', Callee.Name, ' (', IntToStr(FInlineCount), ')');
  EndL := Self.NewLabel('inl_end');
  { Stack a fresh name frame (depth 2 restores the enclosing one after). }
  OldMap := FInlineMap;
  OldTypes := FInlineTypes;
  OldEnd := FInlineEndLbl;
  OldNext := FInlineNextIdx;
  FInlineMap := TDictionary<string, Integer>.Create();
  FInlineTypes := TDictionary<string, TTypeDesc>.Create();
  for I := 0 to Callee.Params.Count - 1 do
  begin
    Par := TMethodParam(Callee.Params.Items[I]);
    FInlineMap.Add(Par.ParamName, MyBase + I);
    FInlineTypes.Add(Par.ParamName, Par.ResolvedType);
  end;
  if RetTy <> nil then
  begin
    FInlineMap.Add('Result', MyBase + Callee.Params.Count);
    FInlineTypes.Add('Result', RetTy);
  end;
  FInlineEndLbl := EndL;
  FInlineNextIdx := MyBase + Need;
  FInlineDepth := FInlineDepth + 1;
  FInlineActive := True;
  try
    for I := 0 to Callee.Body.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(Callee.Body.Stmts.Items[I]));
  finally
    FInlineDepth := FInlineDepth - 1;
    FInlineActive := FInlineDepth > 0;
    FInlineMap.Free();
    FInlineTypes.Free();
    FInlineMap := OldMap;
    FInlineTypes := OldTypes;
    FInlineEndLbl := OldEnd;
    FInlineNextIdx := OldNext;
  end;
  Self.Emit(EndL + ':');
  if AWantResult and (RetTy <> nil) then
  begin
    if IsFloatFamily(RetTy) then
      Self.EmitLoadFloat(Self.VarOperand(InlSlotName(MyBase + Callee.Params.Count)), RetTy)
    else
      Self.EmitLoadVar(Self.VarOperand(InlSlotName(MyBase + Callee.Params.Count)), RetTy);
  end;
  Result := True;
end;

function TX86_64Backend.PromoRewrite(const ALine: string): string;
var
  I, L, CommaP: Integer;
  M, Rest, Op1, Op2: string;
  WSrc, WDst: string;

  function SubReg(const AOp, W: string): string;
  var
    R: Integer;
  begin
    Result := AOp;
    for R := 0 to 3 do
      if (FPromoVars[R] <> '') and (AOp = PROMO_REGS[R]) then
        Exit(PromoSubReg(AOp, W));
    { An embedded (non-bare) occurrence — '(%r14)', '-8(%rbx)' — means a
      promoted register leaked into an addressing context. }
    for R := 0 to 3 do
      if (FPromoVars[R] <> '') and (Pos(PROMO_REGS[R], AOp) >= 0) then
        raise ENativeCodeGenError.Create(
          'register promotion: unexpected operand form in ' + FPromoFunc +
          ': ' + ALine);
  end;

begin
  Result := ALine;
  { Only lines touching a register that actually HOLDS a promoted var are
    rewritten: an unassigned pool register (e.g. %rbx while only %r14/
    %r15 carry vars) may legitimately appear in scratch windows and must
    pass through untouched. }
  I := -1;
  for CommaP := 0 to 3 do
    if (FPromoVars[CommaP] <> '') and (Pos(PROMO_REGS[CommaP], ALine) >= 0) then
      I := CommaP;
  if I < 0 then Exit;
  L := Length(ALine);
  if (L < 2) or (StrAt(ALine, 0) <> 9) then Exit;      { instructions only }
  I := 1;
  while (I < L) and (StrAt(ALine, I) <> 32) do
    I := I + 1;
  M := StrCopyFrom(ALine, 1, I - 1);
  if I >= L then Exit;
  Rest := StrCopyTail(ALine, I + 1);
  { Two-width extension movs carry the source width in the mnemonic. }
  WSrc := '';
  WDst := '';
  if (M = 'movsbq') or (M = 'movzbq') then begin WSrc := 'b'; WDst := 'q'; end
  else if (M = 'movswq') or (M = 'movzwq') then begin WSrc := 'w'; WDst := 'q'; end
  else if M = 'movslq' then begin WSrc := 'l'; WDst := 'q'; end
  else if (M = 'movsbl') or (M = 'movzbl') then begin WSrc := 'b'; WDst := 'l'; end
  else if (M = 'movswl') or (M = 'movzwl') then begin WSrc := 'w'; WDst := 'l'; end
  else if (M = 'movsbw') or (M = 'movzbw') then begin WSrc := 'b'; WDst := 'w'; end
  else
  begin
    case StrAt(M, Length(M) - 1) of
      98:  begin WSrc := 'b'; WDst := 'b'; end;        { ...b }
      119: begin WSrc := 'w'; WDst := 'w'; end;        { ...w }
      108: begin WSrc := 'l'; WDst := 'l'; end;        { ...l }
      113: begin WSrc := 'q'; WDst := 'q'; end;        { ...q }
    else
      raise ENativeCodeGenError.Create(
        'register promotion: unhandled mnemonic in ' + FPromoFunc + ': ' + ALine);
    end;
  end;
  CommaP := Pos(', ', Rest);
  if CommaP < 0 then
  begin
    Result := #9 + M + ' ' + SubReg(Rest, WSrc);
    Exit;
  end;
  Op1 := StrCopyFrom(Rest, 0, CommaP);
  Op2 := StrCopyTail(Rest, CommaP + 2);
  { leaq of a register has no meaning — a promoted var's address must
    never be taken (the selection predicate guarantees this). }
  if M = 'leaq' then
    for CommaP := 0 to 3 do
      if Op1 = PROMO_REGS[CommaP] then
        raise ENativeCodeGenError.Create(
          'register promotion: address taken of promoted register in ' +
          FPromoFunc + ': ' + ALine);
  Result := #9 + M + ' ' + SubReg(Op1, WSrc) + ', ' + SubReg(Op2, WDst);
end;

procedure TX86_64Backend.TrackRspAdjust(const ALine: string; ASign: Integer);
var
  I, L, C, V: Integer;
begin
  { ALine is #9'subq $N, <dest>' or #9'addq $N, <dest>' — index 7 is the
    first digit of N.  Only a %rsp destination adjusts the tracked depth
    (e.g. `addq $16, %rax` must not count). }
  L := Length(ALine);
  V := 0;
  I := 7;
  while I < L do
  begin
    C := StrAt(ALine, I);
    if (C >= 48) and (C <= 57) then                  { '0'..'9' }
      V := V * 10 + (C - 48)
    else
      Break;
    I := I + 1;
  end;
  if StrCopyTail(ALine, I) = ', %rsp' then
    FSPDepth := FSPDepth + ASign * V;
end;

function TX86_64Backend.AlignFreshBytes(ASlots: Integer): Integer;
var
  Rem: Integer;
begin
  Result := ASlots * 8;
  Rem := (FSPDepth + Result) mod 16;
  if Rem < 0 then
    Rem := Rem + 16;
  if Rem <> 0 then
    Result := Result + (16 - Rem);
end;

function TX86_64Backend.EmitArgHoist(AParams: TObjectList;
  AProcParams: TObjectList; AKnownSig: Boolean; const AVarFlags: string;
  AArgs: TObjectList;
  ADepths: TList<Integer>; AKinds: TList<Integer>): Integer;
var
  I: Integer;
  Par: TMethodParam;
  PP: TProcParamInfo;
  Arg: TASTExpr;
  IsVarPos: Boolean;
  ConstStr: Boolean;
  ValStr: Boolean;
  PinPlain: Boolean;
  Mode: TConstArgMode;
begin
  Result := 0;
  if AArgs = nil then Exit;
  { One var/out string sibling param pins plain locals; unknown parameter
    types (interface dispatch) pin them too unless the var flags prove the
    signature has no var params at all. }
  if AParams <> nil then
    PinPlain := Self.ParamsHaveVarString(AParams)
  else if AProcParams <> nil then
    PinPlain := Self.ProcParamsHaveVarString(AProcParams)
  else
    PinPlain := Pos('1', AVarFlags) >= 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    Par := nil;
    PP := nil;
    if (AParams <> nil) and (I < AParams.Count) then
      Par := TMethodParam(AParams.Items[I]);
    if (AProcParams <> nil) and (I < AProcParams.Count) then
      PP := TProcParamInfo(AProcParams.Items[I]);
    IsVarPos := ((Par <> nil) and Par.IsVarParam) or
                ((PP <> nil) and PP.IsVarParam) or
                Self.VarFlagAt(AVarFlags, I);

    { Open-array literal: element block + saved data pointer. }
    if (Par <> nil) and Par.IsOpenArray and (Arg is TArrayLiteralExpr) then
    begin
      Result := Result + Self.EmitOpenArrayLiteral(TArrayLiteralExpr(Arg));
      Self.Emit(#9'pushq %rax');
      Result := Result + 8;
      ADepths.Add(Result);
      AKinds.Add(akOALit);
      Continue;
    end;

    { Record-returning call: materialise the sret buffer here and save the
      buffer pointer.  Evaluated mid-loop it would land between pushed
      argument slots and corrupt the popq sequence. }
    if (not IsVarPos) and Self.IsRecCallArg(Arg) then
    begin
      if Arg is TMethodCallExpr then
      begin
        { EmitExprToEax routes a method call through EmitMethodCallExpr, which
          has no sret-buffer path — it would leave %rax pointing at nothing.
          Allocate the buffer and drive the sret call directly, mirroring the
          TFuncCallExpr path in EmitExprToEax. }
        Self.Emit(Format(#9'subq $%d, %%rsp', [Self.RecArgBufBytes(Arg)]));
        Self.EmitMethodSretCall(TMethodCallExpr(Arg), '(%rsp)', False);
        Self.Emit(#9'leaq (%rsp), %rax');
      end
      else if (Arg is TFieldAccessExpr) and
              (TFieldAccessExpr(Arg).PropRead <> nil) then
      begin
        { Record-returning property read: same as the method-call arg — sret the
          getter into a fresh buffer, then carry its pointer in %rax. }
        Self.Emit(Format(#9'subq $%d, %%rsp', [Self.RecArgBufBytes(Arg)]));
        Self.EmitRecordCallSretAt(Arg, '(%rsp)', False);
        Self.Emit(#9'leaq (%rsp), %rax');
      end
      else
        Self.EmitExprToEax(Arg);        { buffer at %rsp, pointer in %rax }
      { The buffer (RecArgBufBytes, 16-aligned) plus the 8-byte saved pointer
        would leave the hoist region 8 bytes off 16-alignment.  Reserve a
        16-byte slot for the pointer (push + 8-byte pad) so the total stays a
        multiple of 16 — otherwise a later call in this argument list (or the
        callee, e.g. a libm routine using `movdqa`) faults on a misaligned %rsp.
        The pad sits ABOVE the saved pointer, so the reload offset (which uses
        Result - depth) is unchanged. }
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'pushq %rax');
      Result := Result + Self.RecArgBufBytes(Arg) + 16;
      ADepths.Add(Result);
      AKinds.Add(akRecCall);
      Continue;
    end;

    { Interface-returning call argument (Show(MakeFoo(42))): the callee hands
      back an OWNED (+1) fat pointer that the borrowing parameter does not
      release.  Hoist it here so EmitHoistEpilogue can release the obj after the
      call (mirrors akStrConsume).  EmitIntfSretCall leaves the fat pointer at
      (%rsp) over a 16-byte buffer: obj@0, itab@8.  Save it as a contiguous
      16-byte pair (itab pushed first, obj on top); depth records the obj. }
    if (not IsVarPos) and
       ((Arg is TFuncCallExpr) or (Arg is TMethodCallExpr)) and
       (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TFuncCallExpr then
        Self.EmitIntfSretCall(TFuncCallExpr(Arg))
      else
        Self.EmitIntfSretMethodCall(TMethodCallExpr(Arg));
      Self.Emit(#9'movq (%rsp), %rax');     { obj }
      Self.Emit(#9'movq 8(%rsp), %rcx');    { itab }
      Self.Emit(#9'addq $16, %rsp');        { drop the sret buffer }
      Self.Emit(#9'pushq %rcx');            { save itab }
      Self.Emit(#9'pushq %rax');            { save obj (on top) }
      Result := Result + 16;
      ADepths.Add(Result);
      AKinds.Add(akIntfConsume);
      Continue;
    end;

    { Const-string argument needing caller protection. }
    ConstStr := False;
    if Par <> nil then
      ConstStr := Par.IsConstParam and (Par.ResolvedType <> nil) and
                  (Par.ResolvedType.Kind = tyString)
    else if PP <> nil then
      ConstStr := PP.IsConstParam and (PP.TypeDesc <> nil) and
                  (PP.TypeDesc.Kind = tyString)
    else if not AKnownSig then
      { Unknown signature: the implementing method's const-ness is invisible,
        so protect every string-typed value argument by shape.  Pin/consume
        are safe for value params too (the callee pair nets to zero on top). }
      ConstStr := (not IsVarPos) and (Arg.ResolvedType <> nil) and
                  (Arg.ResolvedType.Kind = tyString);
    { By-value string param: the callee's entry-retain/exit-release pair nets
      to zero, so the caller still owns any transient it passes and must
      dispose it after the call — the SAME shape treatment as a const param:
        camConsume — owned (+1) user-call result: release after the call;
        camPin     — aliasable value OR an rc=0 transient (concat / built-in
                     result, which ConstStrShape defaults to camPin):
                     AddRef before + release after — for the rc=0 shapes
                     that pair IS the disposal (0 -> 1 -> 0 frees);
        camBorrowed — plain local/literal: nothing.
      Mirrors the QBE backend's EmitOwnedArgReleases + pin handling. }
    ValStr := False;
    if not ConstStr then
    begin
      if Par <> nil then
        ValStr := (not Par.IsConstParam) and (not IsVarPos) and
                  (not Par.IsOpenArray) and (Par.ResolvedType <> nil) and
                  (Par.ResolvedType.Kind = tyString)
      else if PP <> nil then
        ValStr := (not PP.IsConstParam) and (not IsVarPos) and
                  (PP.TypeDesc <> nil) and (PP.TypeDesc.Kind = tyString);
    end;
    if ConstStr or ValStr then
    begin
      Mode := Self.ConstStrShape(Arg, PinPlain);
      if Mode <> camBorrowed then
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
        if Mode = camPin then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _StringAddRef');
        end;
        Result := Result + 8;
        ADepths.Add(Result);
        if Mode = camPin then
          AKinds.Add(akStrPin)
        else
          AKinds.Add(akStrConsume);
        Continue;
      end;
    end;

    ADepths.Add(-1);
    AKinds.Add(akNone);
  end;
end;

procedure TX86_64Backend.EmitHoistEpilogue(AArgs: TObjectList;
  ADepths: TList<Integer>; AKinds: TList<Integer>; ATotal, ABase: Integer;
  AReclaim: Boolean);
var
  I, K, Off: Integer;
  HasWork: Boolean;
begin
  HasWork := False;
  for I := 0 to AKinds.Count - 1 do
    if AKinds.Get(I) >= akRecCall then
      HasWork := True;
  if HasWork then
  begin
    { Preserve the call's return registers across the release calls:
      %rax/%rdx (int and two-reg record returns), %xmm0/%xmm1 (float and
      SSE-class record returns).  %rbx is the record-release scratch. }
    Self.Emit(#9'subq $40, %rsp');
    Self.Emit(#9'movq %rax, 0(%rsp)');
    Self.Emit(#9'movq %rdx, 8(%rsp)');
    Self.Emit(#9'movq %rbx, 16(%rsp)');
    Self.Emit(#9'movsd %xmm0, 24(%rsp)');
    Self.Emit(#9'movsd %xmm1, 32(%rsp)');
    for I := 0 to AKinds.Count - 1 do
    begin
      K := AKinds.Get(I);
      if K < akRecCall then Continue;
      Off := 40 + ABase + ATotal - ADepths.Get(I);
      if (K = akStrPin) or (K = akStrConsume) then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [Off]));
        Self.Emit(#9'callq _StringRelease');
      end
      else if K = akIntfConsume then
      begin
        { Release the owned (+1) obj of a hoisted interface-call argument. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [Off]));
        Self.Emit(#9'callq _ClassRelease');
      end
      else
      begin
        { Hoisted record temp: release its managed fields; the buffer
          itself is stack memory reclaimed below. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rbx', [Off]));
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(TASTExpr(AArgs.Items[I]).ResolvedType), '%rbx');
      end;
    end;
    Self.Emit(#9'movq 0(%rsp), %rax');
    Self.Emit(#9'movq 8(%rsp), %rdx');
    Self.Emit(#9'movq 16(%rsp), %rbx');
    Self.Emit(#9'movsd 24(%rsp), %xmm0');
    Self.Emit(#9'movsd 32(%rsp), %xmm1');
    Self.Emit(#9'addq $40, %rsp');
  end;
  if AReclaim and (ATotal + ABase > 0) then
    Self.Emit(Format(#9'addq $%d, %%rsp', [ATotal + ABase]));
end;

procedure TX86_64Backend.EmitArgPush(APar: TMethodParam; AArg: TASTExpr;
  ATotal, ADepth, AKind: Integer; var APushed: Integer);
begin
  if AKind = akOALit then
  begin
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
      [ATotal - ADepth + APushed]));
    Self.Emit(#9'pushq %rax');
    Self.Emit(Format(#9'pushq $%d',
      [TArrayLiteralExpr(AArg).Elements.Count - 1]));
    APushed := APushed + 16;
    Exit;
  end;
  if AKind = akIntfConsume then
  begin
    { Hoisted interface-returning-call argument: the saved 16-byte fat pointer
      has obj on top (at depth) and itab just below.  Push both as the two
      interface arg slots (obj first, itab on top), matching the layout
      EmitMethodArgPush emits for an interface argument. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
      [ATotal - ADepth + APushed]));         { obj }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rcx',
      [ATotal - ADepth + APushed + 8]));     { itab }
    Self.Emit(#9'pushq %rax');               { push obj }
    Self.Emit(#9'pushq %rcx');               { push itab }
    APushed := APushed + 16;
    Exit;
  end;
  if AKind >= akRecCall then
  begin
    { Hoisted record-call or const-string argument: reload the saved value. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
      [ATotal - ADepth + APushed]));
    Self.Emit(#9'pushq %rax');
    APushed := APushed + 8;
    Exit;
  end;
  Self.EmitMethodArgPush(APar, AArg);
  if (APar <> nil) and (APar.IsOpenArray or
     ((APar.ResolvedType <> nil) and (APar.ResolvedType.Kind = tyInterface))) then
    APushed := APushed + 16
  else
    APushed := APushed + 8;
end;

procedure TX86_64Backend.BeginCallArgs(AParams: TObjectList; AArgs: TObjectList);
var
  F: TOALCallFrame;
begin
  F := TOALCallFrame.Create();
  F.Args := AArgs;
  F.Total := Self.EmitArgHoist(AParams, nil, True, '', AArgs, F.Depths, F.Kinds);
  FOALFrames.Add(F);
end;

procedure TX86_64Backend.PushCallArg(APar: TMethodParam; AArg: TASTExpr;
  AIndex: Integer);
var
  F: TOALCallFrame;
  Depth: Integer;
  Kind: Integer;
  Pushed: Integer;
begin
  F := FOALFrames.Get(FOALFrames.Count - 1);
  if AIndex < F.Depths.Count then
  begin
    Depth := F.Depths.Get(AIndex);
    Kind := F.Kinds.Get(AIndex);
  end
  else
  begin
    Depth := -1;
    Kind := akNone;
  end;
  Pushed := F.Pushed;
  Self.EmitArgPush(APar, AArg, F.Total, Depth, Kind, Pushed);
  F.Pushed := Pushed;
end;

procedure TX86_64Backend.EndCallArgs;
var
  F: TOALCallFrame;
begin
  F := FOALFrames.Get(FOALFrames.Count - 1);
  FOALFrames.Delete(FOALFrames.Count - 1);
  Self.EmitHoistEpilogue(F.Args, F.Depths, F.Kinds, F.Total, 0, True);
  F.Free();
end;

{ Emit a direct call.  SysV AMD64: integer args in rdi/rsi/rdx/rcx/r8/r9;
  float args in xmm0..xmm5 (independent counters).  Stack args (args 7+ in
  total, after registers are exhausted) go right-to-left.  For M6 the common
  cases are:
    - all-integer params: existing push/pop strategy (up to 8 args).
    - all-float params: evaluate left-to-right into %xmm0..%xmmN directly.
    - mixed int+float params (e.g. _SysWriteDouble): evaluate left-to-right;
      integer args push to stack then pop to int regs; float args evaluated
      directly into xmm regs.  All args must fit in registers (≤6 each). }
procedure TX86_64Backend.EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                                  AArgs: TObjectList);
var
  I:              Integer;
  Arg:            TASTExpr;
  IsVar:          Boolean;
  IsOA:           Boolean;
  ParamType:      TTypeDesc;
  HasFloat:       Boolean;
  SlotCount:      Integer;
  IntIdx, XmmIdx: Integer;
  AllocSz, SlotOff: Integer;
  OverflowBytes:  Integer;
  CleanUp:        Integer;
  OALD:           TList<Integer>;
  OALK:           TList<Integer>;
  OALTotal:       Integer;
  OALPushed:      Integer;
  OverflowOffs:   TList<Integer>;  { source offsets of integer-overflow slots,
                                     in ascending arg order, for relocation }
  RK, RSrc: Integer;
begin
  { Detect whether any arg is float-typed.
    Also compute SlotCount: open-array args expand to 2 register slots each. }
  HasFloat  := False;
  SlotCount := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    IsOA := (ADecl <> nil) and (I < ADecl.Params.Count) and
            TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
    IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
             TMethodParam(ADecl.Params.Items[I]).IsVarParam;
    ParamType := nil;
    if (ADecl <> nil) and (I < ADecl.Params.Count) then
      ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
    if ParamType = nil then
      ParamType := Arg.ResolvedType;
    if IsFloatFamily(ParamType) and not IsVar then
      HasFloat := True;
    if IsOA or ((not IsVar) and (ParamType <> nil) and
                (ParamType.Kind = tyInterface)) then
      Inc(SlotCount, 2)
    else
      Inc(SlotCount);
  end;

  { Count implicit captured-var pointer args (prepended before normal args). }
  if (ADecl <> nil) and (ADecl.CapturedVars <> nil) then
    Inc(SlotCount, ADecl.CapturedVars.Count);

  OverflowBytes := 0;

  { Hoist open-array literal blocks, record-call argument buffers and
    pinned const-string values before any slot push / slot store (see
    EmitArgHoist).  EmitHoistEpilogue after the call releases and reclaims. }
  OALD := TList<Integer>.Create();
  OALK := TList<Integer>.Create();
  OverflowOffs := TList<Integer>.Create();
  if ADecl <> nil then
    OALTotal := Self.EmitArgHoist(ADecl.Params, nil, True, '', AArgs, OALD, OALK)
  else
    OALTotal := Self.EmitArgHoist(nil, nil, True, '', AArgs, OALD, OALK);
  OALPushed := 0;

  if (not HasFloat) and (SlotCount <= 6) then
  begin
    { Pure integer call with ≤6 slots: push/pop strategy.
      Open-array arg A pushes: data ptr first, then high index.
      SlotCount counts register slots after expansion. }

    { Push captured-var addresses as implicit leading args. }
    if (ADecl <> nil) and (ADecl.CapturedVars <> nil) and
       (ADecl.CapturedVars.Count > 0) then
      for I := 0 to ADecl.CapturedVars.Count - 1 do
      begin
        if Self.IsCaptured(ADecl.CapturedVars.Strings[I]) then
          Self.Emit(Format(#9'pushq %s',
            [Self.VarOperand('_cap_' + ADecl.CapturedVars.Strings[I])]))
        else if Self.IsLocal(ADecl.CapturedVars.Strings[I]) then
        begin
          Self.Emit(Format(#9'leaq %s, %%rax',
            [Self.VarOperand(ADecl.CapturedVars.Strings[I])]));
          Self.Emit(#9'pushq %rax');
        end
        else
        begin
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [Self.GlobalSymName(ADecl.CapturedVars.Strings[I])]));
          Self.Emit(#9'pushq %rax');
        end;
        OALPushed := OALPushed + 8;
      end;

    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      IsOA  := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
      { Recompute the param type per argument — the counting loop above
        leaves ParamType holding the LAST argument's type. }
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      if (not IsOA) and (OALK.Get(I) = akIntfConsume) then
      begin
        { Hoisted interface-returning-call argument — reload the saved 16-byte
          fat pointer (obj on top at depth, itab just below) and push both as
          the two interface arg slots (obj first, itab on top). }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [OALTotal - OALD.Get(I) + OALPushed]));        { obj }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rcx',
          [OALTotal - OALD.Get(I) + OALPushed + 8]));    { itab }
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'pushq %rcx');
      end
      else if (not IsOA) and (OALK.Get(I) >= akRecCall) then
      begin
        { Hoisted record-call or const-string argument — reload the saved
          value from the pre-pass region. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [OALTotal - OALD.Get(I) + OALPushed]));
        Self.Emit(#9'pushq %rax');
      end
      else if IsOA then
      begin
        if Arg is TArrayLiteralExpr then
        begin
          { Hoisted in the pre-pass — reload the saved data pointer. }
          Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
            [OALTotal - OALD.Get(I) + OALPushed]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'pushq $%d',
            [TArrayLiteralExpr(Arg).Elements.Count - 1]));
        end
        else if (Arg is TIdentExpr) and
                (TIdentExpr(Arg).ResolvedType <> nil) and
                (TIdentExpr(Arg).ResolvedType.Kind = tyStaticArray) then
        begin
          if Self.IsLocal(TIdentExpr(Arg).Name) then
            Self.Emit(Format(#9'leaq %s, %%rax',
              [Self.VarOperand(TIdentExpr(Arg).Name)]))
          else if TIdentExpr(Arg).ConstArraySymbol <> '' then
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [NativeMangle(TIdentExpr(Arg).ConstArraySymbol)]))
          else
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [TIdentExpr(Arg).Name]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'pushq $%d',
            [TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).LowBound]));
        end
        else if (Arg.ResolvedType <> nil) and
                (Arg.ResolvedType.Kind = tyDynArray) then
        begin
          { Dynamic array coerced to open-array: push data ptr +
            (runtime length - 1) as the high index. }
          Self.EmitExprToEax(Arg);          { data ptr -> %rax }
          Self.Emit(#9'pushq %rax');         { push ptr }
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');          { high = length - 1 }
          Self.Emit(#9'pushq %rax');         { push high }
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name + '_high')]));
          Self.Emit(#9'pushq %rax');
        end;
      end
      else if IsVar then
      begin
        Self.EmitVarArgAddrToRax(Arg);
        Self.Emit(#9'pushq %rax');
      end
      else if (ParamType <> nil) and (ParamType.Kind = tyInterface) then
      begin
        if (ADecl <> nil) and (I < ADecl.Params.Count) then
          Self.EmitMethodArgPush(TMethodParam(ADecl.Params.Items[I]), Arg)
        else if Arg is TFieldAccessExpr then
        begin
          Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else if Arg is TIdentExpr then
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end
        else
          raise ENativeCodeGenError.Create(
            'native backend: unsupported interface arg expression in EmitCall');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
      { Track bytes pushed so far — hoisted-literal reloads above are
        %rsp-relative.  Mirrors the slot widths of the branches. }
      if IsOA or ((not IsVar) and (ParamType <> nil) and
                  (ParamType.Kind = tyInterface)) then
        OALPushed := OALPushed + 16
      else
        OALPushed := OALPushed + 8;
    end;

    for I := SlotCount - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I));
  end
  else
  begin
    { >6 integer slots or mixed int/float call.  Pre-allocate strategy:
      1. Allocate SC×8 bytes on the stack (16-byte aligned).
      2. Evaluate each arg left-to-right into slot[I] at I×8(%rsp).
      3. Load the first 6 int args into SysV int regs, first 8 float args
         into xmm regs; overflow int args stay on the stack.
      4. Adjust %rsp so the overflow args sit at the top. }

    AllocSz := ((SlotCount * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));

    { Evaluate captured-var addresses into the first slots. }
    SlotOff := 0;
    if (ADecl <> nil) and (ADecl.CapturedVars <> nil) and
       (ADecl.CapturedVars.Count > 0) then
      for I := 0 to ADecl.CapturedVars.Count - 1 do
      begin
        if Self.IsCaptured(ADecl.CapturedVars.Strings[I]) then
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand('_cap_' + ADecl.CapturedVars.Strings[I])]))
        else if Self.IsLocal(ADecl.CapturedVars.Strings[I]) then
          Self.Emit(Format(#9'leaq %s, %%rax',
            [Self.VarOperand(ADecl.CapturedVars.Strings[I])]))
        else
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [Self.GlobalSymName(ADecl.CapturedVars.Strings[I])]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end;

    { Evaluate each arg left-to-right into its slot. }
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      IsOA  := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;

      if (not IsOA) and (OALK.Get(I) >= akRecCall) then
      begin
        { Hoisted record-call or const-string argument — reload the saved
          value from above the slot block. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + OALTotal - OALD.Get(I)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end
      else if IsOA then
      begin
        if Arg is TArrayLiteralExpr then
        begin
          { Hoisted in the pre-pass — the saved data pointer sits above the
            slot block allocated by the subq just before this loop. }
          Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
            [AllocSz + OALTotal - OALD.Get(I)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq $%d, %d(%%rsp)',
            [TArrayLiteralExpr(Arg).Elements.Count - 1, SlotOff]));
          Inc(SlotOff, 8);
        end
        else if (Arg is TIdentExpr) and
                (TIdentExpr(Arg).ResolvedType <> nil) and
                (TIdentExpr(Arg).ResolvedType.Kind = tyStaticArray) then
        begin
          if Self.IsLocal(TIdentExpr(Arg).Name) then
            Self.Emit(Format(#9'leaq %s, %%rax',
              [Self.VarOperand(TIdentExpr(Arg).Name)]))
          else if TIdentExpr(Arg).ConstArraySymbol <> '' then
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [NativeMangle(TIdentExpr(Arg).ConstArraySymbol)]))
          else
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [TIdentExpr(Arg).Name]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq $%d, %d(%%rsp)',
            [TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).LowBound,
             SlotOff]));
          Inc(SlotOff, 8);
        end
        else if (Arg.ResolvedType <> nil) and
                (Arg.ResolvedType.Kind = tyDynArray) then
        begin
          { Dynamic array coerced to open-array: store data ptr +
            (runtime length - 1) as the high index. }
          Self.EmitExprToEax(Arg);          { data ptr -> %rax }
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');          { high = length - 1 }
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name + '_high')]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end;
      end
      else if IsFloatFamily(ParamType) and not IsVar then
      begin
        Self.EmitExprToXmm0(Arg);
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
        begin
          if (Arg.ResolvedType = nil) or (Arg.ResolvedType.Kind <> tySingle) then
            Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
          Self.Emit(Format(#9'movss %%xmm0, %d(%%rsp)', [SlotOff]));
        end
        else
        begin
          if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tySingle) then
            Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
          Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [SlotOff]));
        end;
        Inc(SlotOff, 8);
      end
      else if IsVar then
      begin
        Self.EmitVarArgAddrToRax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end
      else if (ParamType <> nil) and (ParamType.Kind = tyInterface) then
      begin
        if (ADecl <> nil) and (I < ADecl.Params.Count) then
        begin
          Self.EmitExprToEax(Arg);
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          { Interface itab — for a simple ident, load from itab slot. }
          if Arg is TIdentExpr then
            Self.Emit(Format(#9'movq %s, %%rax',
              [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]))
          else
            Self.Emit(#9'xorq %rax, %rax');
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else if Arg is TFieldAccessExpr then
        begin
          Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(Format(#9'movq %%rcx, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(#9'movq 8(%rax), %rcx');
          Self.Emit(Format(#9'movq %%rcx, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else if Arg is TIdentExpr then
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else
          raise ENativeCodeGenError.Create(
            'native backend: unsupported interface arg expression in EmitCall');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end;
    end;

    { Pass 2: load from slots into registers.  Integer args use separate
      IntIdx (0..5 → registers, ≥6 → leave on stack), float args use
      XmmIdx (0..7 → xmm registers).  We read slots in order and load
      the register-bound ones; overflow int args must end up at (%rsp)
      in forward order after we remove the register-bound region. }

    { First, load the register-bound args.  Captured vars occupy the
      first slots; normal args follow. }
    IntIdx := 0;
    XmmIdx := 0;
    SlotOff := 0;
    if (ADecl <> nil) and (ADecl.CapturedVars <> nil) then
      for I := 0 to ADecl.CapturedVars.Count - 1 do
      begin
        if IntIdx < 6 then
        begin
          Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
          Inc(IntIdx);
        end;
        Inc(SlotOff, 8);
      end;
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      IsOA := (ADecl <> nil) and (I < ADecl.Params.Count) and
              TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;

      if IsFloatFamily(ParamType) and not IsOA and not IsVar then
      begin
        if XmmIdx < 8 then
        begin
          if (ParamType <> nil) and (ParamType.Kind = tySingle) then
            Self.Emit(Format(#9'movss %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]))
          else
            Self.Emit(Format(#9'movsd %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]));
          Inc(XmmIdx);
        end
        else
          { >8 float args: the 9th onward overflow to the outgoing stack area,
            exactly like an integer overflow arg.  Without this the slot was
            silently dropped (never relocated, then reclaimed by the frame
            addq/subq), so the callee read an uninitialised stack slot — garbage
            for BOTH Single and Double overflow floats
            (BUG-20260721-x86-single-overflow-arg; the defect is not
            Single-specific — the caller dropped every overflow float).  The
            callee's BuildFrame advances the SAME shared StackOff for int and
            float overflow params in arg order, so adding SlotOff here in loop
            (= argument) order reproduces the System V stack layout the callee
            expects.  Pass 1 wrote a Single as a raw 4-byte movss into the low
            half of the 8-byte slot; the 8-byte relocation copy carries garbage
            in the high 4 bytes, but the callee reads a Single with movss (low 4
            only), so it is harmless. }
          OverflowOffs.Add(SlotOff);
        Inc(SlotOff, 8);
      end
      else
      begin
        if IsOA then
        begin
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
        end
        else if (ParamType <> nil) and (ParamType.Kind = tyInterface) and
                not IsVar then
        begin
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
        end
        else
        begin
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
        end;
      end;
    end;

    { If nothing overflowed, reclaim the entire pre-allocated area.  Otherwise
      copy the integer-overflow slots into a FRESH region below the slot
      block, in ascending arg order, so the call sees the overflow at
      0(%rsp).. with the lowest-indexed overflow arg first (System V order).
      Every destination is strictly below every source, so the copy can never
      clobber an unread slot, and AlignFreshBytes sizes the region so the
      call site is 16-byte aligned even when pinned pushes above the slot
      block have left the frame at an odd slot count.  Both integer AND float
      overflow slots appear here (a 9th+ float arg overflows to the stack just
      like a 7th+ integer arg), collected in argument order — the callee's
      BuildFrame lays out int and float overflow params against one shared
      StackOff in the same order, so the relocation matches.  The slot block
      plus the fresh region is reclaimed after the call via the hoist
      epilogue's base bytes.

      This replaces a former `addq $48` shortcut that assumed exactly the
      first six contiguous slots were register-bound; with floats
      interspersed fewer integer slots precede the overflow, so that shortcut
      placed the overflow at the wrong address and crashed the callee. }
    if OverflowOffs.Count = 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [AllocSz]))
    else
    begin
      OverflowBytes := Self.AlignFreshBytes(OverflowOffs.Count);
      Self.Emit(Format(#9'subq $%d, %%rsp', [OverflowBytes]));
      for RK := 0 to OverflowOffs.Count - 1 do
      begin
        RSrc := OverflowBytes + OverflowOffs.Get(RK);
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [RSrc]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [RK * 8]));
      end;
      { The hoist epilogue reclaims OverflowBytes as its base — it must now
        cover the fresh region AND the still-allocated slot block. }
      OverflowBytes := OverflowBytes + AllocSz;
    end;
  end;

  Self.Emit(#9'callq ' + AFuncSym);
  Self.EmitHoistEpilogue(AArgs, OALD, OALK, OALTotal, OverflowBytes, True);
  OALD.Free();
  OALK.Free();
  OverflowOffs.Free();
end;

{ Spill the incoming argument register at index AIdx into the param slot
  AOperand, using the register sub-view matching the param's width. }
procedure TX86_64Backend.EmitSpillArg(AIdx: Integer; const AOperand: string;
                                      AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: Self.Emit(Format(#9'movb %s, %s', [SysVArgRegs8[AIdx],  AOperand]));
    2: Self.Emit(Format(#9'movw %s, %s', [SysVArgRegs16[AIdx], AOperand]));
    8: Self.Emit(Format(#9'movq %s, %s', [SysVArg64(AIdx), AOperand]));
  else
    Self.Emit(Format(#9'movl %s, %s', [SysVArgRegs[AIdx], AOperand]));
  end;
end;

{ Emit a call through a bare function pointer held in APtrOperand (an AT&T
  memory operand).  Loads the pointer into %r10 (caller-saved scratch, not
  clobbered by arg evaluation in %rax), sets up args exactly as EmitCall does,
  then dispatches via `callq *%r10`.  AProcType supplies the param signature
  for var/out param detection; nil means all value params. }
procedure TX86_64Backend.EmitCallIndirect(const APtrOperand: string;
                                          AProcType: TProceduralTypeDesc;
                                          AArgs: TObjectList);
var
  I:        Integer;
  Arg:      TASTExpr;
  IsVar:    Boolean;
  AllocSz:  Integer;
  FreshSz:  Integer;
  CleanUp:  Integer;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  PParams:  TObjectList;
  ParamTy:  TTypeDesc;
  IsFloatSlot: TList<Integer>;
  OvSlots:  TList<Integer>;
  IntIdx, XmmIdx: Integer;
begin
  PParams := nil;
  if AProcType <> nil then
    PParams := AProcType.Params;
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  IsFloatSlot := TList<Integer>.Create();
  OvSlots := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(nil, PParams, True, '', AArgs, HD, HK);
  { The function pointer is loaded into %r10 only AFTER all argument
    evaluation: %r10 is caller-saved, so any call emitted while evaluating
    an argument (or the hoist pre-pass above) would clobber it.
    APtrOperand is %rbp- or %rip-relative, never %rsp-relative.

    Uniform slot-block scheme: evaluate every arg into a pre-allocated
    8-byte slot (floats via %xmm0 — the old path routed EVERY arg through
    the integer registers, so a single Double arg read garbage from xmm
    and following ints were shifted; BUG-20260722-native-procvar-float-args),
    then assign registers in arg order with independent int/xmm counters,
    overflow slots (7th+ int, 9th+ float) relocated in ascending arg order
    exactly as EmitMethodOverflowLoad does.  Slot writes are %rsp-relative
    and position-fixed, so a call inside an argument expression cannot
    clobber earlier slots. }
  AllocSz := ((AArgs.Count * 8 + 15) and (-16));
  if AllocSz > 0 then
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    IsVar := (AProcType <> nil) and (I < AProcType.Params.Count) and
             TProcParamInfo(AProcType.Params.Items[I]).IsVarParam;
    if (AProcType <> nil) and (I < AProcType.Params.Count) then
      ParamTy := TProcParamInfo(AProcType.Params.Items[I]).TypeDesc
    else
      ParamTy := Arg.ResolvedType;
    if (not IsVar) and IsFloatFamily(ParamTy) then
      IsFloatSlot.Add(1)
    else
      IsFloatSlot.Add(0);
    if HK.Get(I) >= akRecCall then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [AllocSz + HTotal - HD.Get(I)]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * 8]));
    end
    else if IsVar then
    begin
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * 8]));
    end
    else if IsFloatSlot.Get(I) = 1 then
    begin
      { Float slot: materialise at the PARAM's width (a Single param wants
        the single bit pattern in the low 4 bytes; the 8-byte movsd
        store/reload is harmless). }
      Self.EmitExprToXmm0(Arg);
      Self.EmitXmm0WidthAdjust(Arg.ResolvedType,
        (ParamTy <> nil) and (ParamTy.Kind = tySingle));
      Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [I * 8]));
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * 8]));
    end;
  end;
  { Register assignment in arg order; int and xmm sequences advance
    independently per SysV. }
  IntIdx := 0;
  XmmIdx := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    if IsFloatSlot.Get(I) = 1 then
    begin
      if XmmIdx <= 7 then
      begin
        Self.Emit(Format(#9'movsd %d(%%rsp), %s',
          [I * 8, SysVXmmArgRegs[XmmIdx]]));
        Inc(XmmIdx);
      end
      else
        OvSlots.Add(I);
    end
    else if IntIdx <= 5 then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [I * 8, SysVArg64(IntIdx)]));
      Inc(IntIdx);
    end
    else
      OvSlots.Add(I);
  end;
  CleanUp := AllocSz;
  if OvSlots.Count > 0 then
  begin
    { Relocate overflow slots into a FRESH region below the slot block so
      the call sees them at 0(%rsp).. in ascending arg order on a 16-byte-
      aligned %rsp regardless of pinned pushes above (AlignFreshBytes).
      The type-agnostic 8-byte copy is harmless for Single (low 4 bytes).
      FreshSz MUST be computed exactly once, BEFORE the subq: AlignFreshBytes
      reads FSPDepth, which the subq itself advances — recomputing it after
      the subq can differ by 8 (e.g. one hoisted string pin above), shifting
      every reload offset and the cleanup amount. }
    FreshSz := Self.AlignFreshBytes(OvSlots.Count);
    Self.Emit(Format(#9'subq $%d, %%rsp', [FreshSz]));
    for I := 0 to OvSlots.Count - 1 do
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [FreshSz + OvSlots.Get(I) * 8]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * 8]));
    end;
    CleanUp := CleanUp + FreshSz;
  end;
  Self.Emit(Format(#9'movq %s, %%r10', [APtrOperand]));
  Self.Emit(#9'callq *%r10');
  Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  OvSlots.Free();
  IsFloatSlot.Free();
  HD.Free();
  HK.Free();
end;

{ Call a procedural-typed class field through a receiver — emits:
    <push each arg>
    movq <receiver>, %rax ; addq $Offset, %rax   ; %rax = field slot
    movq 8(%rax), %rdi   (of object only: Data -> first arg)
    movq (%rax), %r10    ; code pointer
    popq <arg regs>      ; callq *%r10 }
procedure TX86_64Backend.EmitProcFieldCall(AObjExpr: TASTExpr;
  const AObjectName: string; AIsVarParam: Boolean; AFieldInfo: TFieldInfo;
  AProcType: TProceduralTypeDesc; AArgs: TObjectList; AResultType: TTypeDesc);
var
  I:       Integer;
  Arg:     TASTExpr;
  IsVar:   Boolean;
  IsMeth:  Boolean;
  Slots:   Integer;
  HD:      TList<Integer>;
  HK:      TList<Integer>;
  HTotal:  Integer;
begin
  { 'reference to' closures carry their env in the Data half exactly like an
    'of object' method pointer carries Self — both must load and pass it. }
  IsMeth := (AProcType <> nil) and
            (AProcType.IsMethodPtr or AProcType.IsReference);
  { A method pointer consumes %rdi for the captured Data (Self), leaving five
    argument registers; a plain function pointer leaves all six.  Anything
    larger would need the stack-overflow argument strategy — fail loudly
    rather than emit a silently wrong call. }
  if IsMeth then Slots := AArgs.Count + 1 else Slots := AArgs.Count;
  if Slots > 6 then
    raise ENativeCodeGenError.Create(
      'native backend: procedural-field call with >6 argument slots is not supported');

  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  try
    HTotal := Self.EmitArgHoist(nil, AProcType.Params, True, '', AArgs, HD, HK);
    { Evaluate args left-to-right and push them.  var/out positions push the
      argument's address; record-call/string args are reloaded from the hoist
      region. }
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (I < AProcType.Params.Count) and
               TProcParamInfo(AProcType.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [HTotal - HD.Get(I) + I * 8]));
        Self.Emit(#9'pushq %rax');
      end
      else if IsVar then
      begin
        Self.EmitVarArgAddrToRax(Arg);
        Self.Emit(#9'pushq %rax');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
    end;

    { Load the receiver instance pointer into %rax.  This must be call-free so
      it cannot clobber the already-pushed arguments. }
    if AObjExpr <> nil then
    begin
      if (AObjExpr is TIdentExpr) or (AObjExpr is TFieldAccessExpr) then
        Self.EmitExprToEax(AObjExpr)
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported receiver expression in procedural-field call');
    end
    else if AIsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(AObjectName)]));
      Self.Emit(#9'movq (%rax), %rax');
    end
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(AObjectName)]));

    { %rax now holds the instance pointer; advance to the field slot (the code
      pointer for a plain function pointer, or the 16-byte (Code, Data) block
      for a method pointer). }
    if AFieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rax', [AFieldInfo.Offset]));

    if IsMeth then
    begin
      Self.Emit(#9'movq 8(%rax), %rdi');   { Data (Self) -> first argument }
      Self.Emit(#9'movq (%rax), %r10');    { Code pointer }
      for I := AArgs.Count - 1 downto 0 do
        Self.Emit(#9'popq ' + SysVArg64(I + 1));
    end
    else
    begin
      Self.Emit(#9'movq (%rax), %r10');    { Code pointer }
      for I := AArgs.Count - 1 downto 0 do
        Self.Emit(#9'popq ' + SysVArg64(I));
    end;
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  finally
    HD.Free();
    HK.Free();
  end;

  { Normalise the (32-bit-ABI) return value to the field signature's return
    width.  Statement calls pass nil and need no result. }
  if AResultType <> nil then
    Self.EmitNarrowToType(AResultType);
end;

procedure TX86_64Backend.EmitLocalRecordBase(const AName, AReg: string);
begin
  if FSretFunc and SameText(AName, 'Result') then
    { sret Result: the slot holds the caller's buffer POINTER. }
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand('Result'), AReg]))
  else
    { Ordinary local value record: the slot IS the record. }
    Self.Emit(Format(#9'leaq %s, %s', [Self.VarOperand(AName), AReg]));
end;

procedure TX86_64Backend.EmitFieldAddrToRcx(AFA: TFieldAccessExpr);
begin
  if AFA.Base <> nil then
  begin
    Self.EmitExprToEax(AFA.Base);
    Self.Emit(#9'movq %rax, %rcx');
  end
  else if AFA.IsImplicitSelf then
  begin
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
    if (AFA.ImplicitBaseInfo <> nil) and (AFA.ImplicitBaseInfo.Offset > 0) then
      Self.Emit(Format(#9'addq $%d, %%rcx', [AFA.ImplicitBaseInfo.Offset]));
    if AFA.IsClassAccess then
      Self.Emit(#9'movq (%rcx), %rcx');
  end
  else if AFA.IsClassAccess then
  begin
    Self.EmitVarBaseToReg(AFA.RecordName, False, '%rcx');
    if AFA.IsVarParam then
      { var-param class: slot -> caller var -> instance }
      Self.Emit(#9'movq (%rcx), %rcx');
  end
  else if AFA.IsVarParam then
  begin
    Self.EmitVarBaseToReg(AFA.RecordName, False, '%rcx');
  end
  else Self.EmitVarBaseToReg(AFA.RecordName, True, '%rcx');
  if AFA.FieldInfo.Offset > 0 then
    Self.Emit(Format(#9'addq $%d, %%rcx', [AFA.FieldInfo.Offset]));
end;

{ Emit a call to a record-returning function using the sret convention.
  ASretAddr is the AT&T operand for the destination buffer already allocated
  by the caller.  Strategy:
    1. leaq ASretAddr → %r10  (save addr before arg eval clobbers %rax/%rdi)
    2. Evaluate each normal arg (push/pop strategy for integer args)
    3. Pop into %rsi/%rdx/... (index 1..N)
    4. movq %r10, %rdi  (hidden first arg = sret ptr)
    5. callq AFuncSym
  All args must be integer-family value params (≤5 since %rdi is taken by sret). }

procedure TX86_64Backend.EmitRecordReturnEpilogue(ARec: TRecordTypeDesc;
  AClass: TRecReturnClass);
var
  ResOp: string;
  Sz: Integer;
begin
  ResOp := Self.VarOperand('Result');
  Sz := ARec.TotalSize();
  case AClass of
    rcInt1:
      begin
        Self.Emit(Format(#9'leaq %s, %%rax', [ResOp]));
        case Sz of
          1: Self.Emit(#9'movzbl (%rax), %eax');
          2: Self.Emit(#9'movzwl (%rax), %eax');
          4: Self.Emit(#9'movl (%rax), %eax');
          8: Self.Emit(#9'movq (%rax), %rax');
        end;
      end;
    rcInt2:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movq (%rcx), %rax');
        Self.Emit(#9'movq 8(%rcx), %rdx');
      end;
    rcSSE1:
      begin
        if Sz = 4 then
          Self.Emit(Format(#9'movss %s, %%xmm0', [ResOp]))
        else
          Self.Emit(Format(#9'movsd %s, %%xmm0', [ResOp]));
      end;
    rcSSE2:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movsd (%rcx), %xmm0');
        Self.Emit(#9'movsd 8(%rcx), %xmm1');
      end;
    rcIntSSE:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movq (%rcx), %rax');
        Self.Emit(#9'movsd 8(%rcx), %xmm0');
      end;
    rcSSEInt:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movsd (%rcx), %xmm0');
        Self.Emit(#9'movq 8(%rcx), %rax');
      end;
  end;
end;

procedure TX86_64Backend.EmitRecordRegReturnCapture(const ADestAddr: string;
  ARec: TRecordTypeDesc; AClass: TRecReturnClass; AIsIndirect: Boolean);
var
  Sz:      Integer;
  LoadOp:  string;
begin
  Sz := ARec.TotalSize();
  if AIsIndirect then
    LoadOp := 'movq'
  else
    LoadOp := 'leaq';
  case AClass of
    rcInt1:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        case Sz of
          1: Self.Emit(#9'movb %al, (%rcx)');
          2: Self.Emit(#9'movw %ax, (%rcx)');
          4: Self.Emit(#9'movl %eax, (%rcx)');
          8: Self.Emit(#9'movq %rax, (%rcx)');
        end;
      end;
    rcInt2:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movq %rax, (%rcx)');
        Self.Emit(#9'movq %rdx, 8(%rcx)');
      end;
    rcSSE1:
      begin
        if AIsIndirect then
        begin
          Self.Emit(Format(#9'movq %s, %%rcx', [ADestAddr]));
          if Sz = 4 then
            Self.Emit(#9'movss %xmm0, (%rcx)')
          else
            Self.Emit(#9'movsd %xmm0, (%rcx)');
        end
        else
        begin
          if Sz = 4 then
            Self.Emit(Format(#9'movss %%xmm0, %s', [ADestAddr]))
          else
            Self.Emit(Format(#9'movsd %%xmm0, %s', [ADestAddr]));
        end;
      end;
    rcSSE2:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movsd %xmm0, (%rcx)');
        Self.Emit(#9'movsd %xmm1, 8(%rcx)');
      end;
    rcIntSSE:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movq %rax, (%rcx)');
        Self.Emit(#9'movsd %xmm0, 8(%rcx)');
      end;
    rcSSEInt:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movsd %xmm0, (%rcx)');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end;
  end;
end;

{ Number of integer-register SLOTS the explicit args of an sret free-function
  call occupy, expanding interface params to two (obj + itab).  Used to pick the
  register vs stack-spill path and to drive the pop loop. }
function TX86_64Backend.SretUserSlots(ADecl: TMethodDecl;
                                      AArgs: TObjectList): Integer;
var
  I: Integer;
  PT: TTypeDesc;
  IsVar: Boolean;
begin
  Result := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
             TMethodParam(ADecl.Params.Items[I]).IsVarParam;
    PT := nil;
    if (ADecl <> nil) and (I < ADecl.Params.Count) then
      PT := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
    if PT = nil then
      PT := TASTExpr(AArgs.Items[I]).ResolvedType;
    if (not IsVar) and (PT <> nil) and (PT.Kind = tyInterface) then
      Inc(Result, 2)
    else
      Inc(Result);
  end;
end;

procedure TX86_64Backend.EmitSretCall(const AFuncSym: string; ADecl: TMethodDecl;
                                      AArgs: TObjectList; const ASretAddr: string;
                                      ASretIsIndirect: Boolean);
var
  I:        Integer;
  Arg:      TASTExpr;
  IsVar:    Boolean;
  AllocSz:  Integer;
  CleanUp:  Integer;
  RC:       TRecReturnClass;
  RetRec:   TRecordTypeDesc;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  HasFloat: Boolean;
  ParamType: TTypeDesc;
  IntIdx, XmmIdx, SlotOff: Integer;
  ArgPushed: Integer;
begin
  { Check if the callee returns a small POD record (or method pointer) via
    registers.  RetRec is the real record or the canonical method-ptr record. }
  RC := rcSret;
  RetRec := nil;
  if ADecl <> nil then RetRec := AggRetRec(ADecl.ResolvedReturnType);
  if RetRec <> nil then
    RC := ClassifyRecordReturn(RetRec);
  if RC <> rcSret then
  begin
    { Reg-return: zero the dest buffer, call without hidden sret param,
      capture return registers into the dest buffer. }
    if ASretIsIndirect then
      Self.Emit(Format(#9'movq %s, %%r10', [ASretAddr]))
    else
      Self.Emit(Format(#9'leaq %s, %%r10', [ASretAddr]));
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx', [RetRec.TotalSize()]));
    Self.Emit(#9'callq memset');
    Self.EmitCall(AFuncSym, ADecl, AArgs);
    Self.EmitRecordRegReturnCapture(ASretAddr, RetRec, RC, ASretIsIndirect);
    Exit;
  end;
  { Save the destination address on the stack, below the hoist region:
    no caller-saved register survives argument evaluation, and a
    %rsp-relative ASretAddr (e.g. '(%rsp)') would drift once the region is
    live.  When ASretIsIndirect the operand holds a pointer to the buffer
    (sret forwarding) — load it with movq. }
  if ASretIsIndirect then
    Self.Emit(Format(#9'movq %s, %%rax', [ASretAddr]))
  else
    Self.Emit(Format(#9'leaq %s, %%rax', [ASretAddr]));
  Self.Emit(#9'pushq %rax');
  { Zero the destination buffer via memset(dest, 0, size), mirroring the QBE
    backend.  The return type is a record or a jumbo set here; RawSize covers
    both (TotalSize for a record, the bitmap byte count for a jumbo set). }
  if (ADecl <> nil) and (ADecl.ResolvedReturnType <> nil) then
  begin
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx',
      [ADecl.ResolvedReturnType.RawSize()]));
    Self.Emit(#9'callq memset');
  end;
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  if ADecl <> nil then
    HTotal := Self.EmitArgHoist(ADecl.Params, nil, True, '', AArgs, HD, HK)
  else
    HTotal := Self.EmitArgHoist(nil, nil, True, '', AArgs, HD, HK);
  { Detect a float-typed by-value argument: the integer push/pop path below
    cannot carry one (it would route the float through %rax and an integer arg
    register).  When present, use the slot-based scheme that places each float
    arg in an %xmm register per the SysV ABI (mirrors EmitCall's float path). }
  HasFloat := False;
  for I := 0 to AArgs.Count - 1 do
  begin
    ParamType := nil;
    if (ADecl <> nil) and (I < ADecl.Params.Count) then
      ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
    if ParamType = nil then
      ParamType := TASTExpr(AArgs.Items[I]).ResolvedType;
    IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
             TMethodParam(ADecl.Params.Items[I]).IsVarParam;
    if IsFloatFamily(ParamType) and not IsVar then
      HasFloat := True;
  end;

  if HasFloat then
  begin
    { Slot-based: sret = slot 0 (%rdi), explicit args = slots 1..Count.  Each
      arg is evaluated into its 8-byte slot (float via movsd/movss, integer via
      movq), then int slots load into %rsi.. and float slots into %xmm0.., each
      stream counted independently.  Args beyond the 5 int / 8 xmm registers
      would need stack spill — record-returning functions with that many float
      args do not occur yet, so guard the integer overflow loudly via SysVArg64. }
    AllocSz := (((AArgs.Count + 1) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    { Reload the saved sret dest (pushed just below the hoist region). }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
      end
      else if IsFloatFamily(ParamType) and not IsVar then
      begin
        Self.EmitExprToXmm0(Arg);
        { Match the value width to the PARAM width before spilling: an
          integer/Double arg into a Single param narrows (cvtsd2ss), a Single
          arg into a Double param widens (cvtss2sd).  Without this the movss/
          movsd below deposits the wrong-width bit-pattern (BUG-027 class). }
        Self.EmitXmm0WidthAdjust(Arg.ResolvedType,
          (ParamType <> nil) and (ParamType.Kind = tySingle));
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %%xmm0, %d(%%rsp)', [(I + 1) * 8]))
        else
          Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [(I + 1) * 8]));
      end
      else
      begin
        if IsVar then
          Self.EmitVarArgAddrToRax(Arg)
        else
          Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
      end;
    end;
    { Load sret ptr into %rdi, then int args into %rsi.. and float args into
      %xmm0.., each stream advancing its own register index. }
    Self.Emit(#9'movq 0(%rsp), %rdi');
    IntIdx := 1;   { %rdi consumed by sret }
    XmmIdx := 0;
    for I := 0 to AArgs.Count - 1 do
    begin
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := TASTExpr(AArgs.Items[I]).ResolvedType;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      SlotOff := (I + 1) * 8;
      if IsFloatFamily(ParamType) and not IsVar then
      begin
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]))
        else
          Self.Emit(Format(#9'movsd %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]));
        Inc(XmmIdx);
      end
      else
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
        Inc(IntIdx);
      end;
    end;
    { %al = number of vector registers used (SysV varargs/AL convention; the
      callee ignores it for a fixed prototype but the ABI requires it set). }
    Self.Emit(Format(#9'movb $%d, %%al', [XmmIdx]));
    { Drop the (Count+1) register-bound slots so any overflow sits at the top;
      with <=5 args there is no overflow, so this reclaims the whole region
      except the alignment padding. }
    Self.Emit(Format(#9'addq $%d, %%rsp', [(AArgs.Count + 1) * 8]));
    Self.Emit(#9'callq ' + AFuncSym);
    CleanUp := AllocSz - (AArgs.Count + 1) * 8;
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  end
  else if Self.SretUserSlots(ADecl, AArgs) <= 5 then
  begin
    { Push each arg's register slot(s) — an interface arg is a fat pointer that
      occupies TWO slots (obj then itab on top), so the push count is the SLOT
      count, not the arg count.  ArgPushed tracks bytes pushed so far so the
      hoisted-value reloads stay correct as %rsp moves. }
    ArgPushed := 0;
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      if (not IsVar) and (HK.Get(I) = akIntfConsume) then
      begin
        { Hoisted interface-returning-call arg: reload the saved 16-byte fat
          pointer (obj, then itab) and push both slots (obj first, itab on top). }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + ArgPushed]));
        Self.Emit(Format(#9'movq %d(%%rsp), %%rcx', [HTotal - HD.Get(I) + ArgPushed + 8]));
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'pushq %rcx');
        ArgPushed := ArgPushed + 16;
      end
      else if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + ArgPushed]));
        Self.Emit(#9'pushq %rax');
        ArgPushed := ArgPushed + 8;
      end
      else if (not IsVar) and (ParamType <> nil) and (ParamType.Kind = tyInterface) then
      begin
        { Direct interface arg (variable / field): push obj then itab. }
        Self.EmitMethodArgPush(TMethodParam(ADecl.Params.Items[I]), Arg);
        ArgPushed := ArgPushed + 16;
      end
      else
      begin
        if IsVar then
          Self.EmitVarArgAddrToRax(Arg)
        else
          Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
        ArgPushed := ArgPushed + 8;
      end;
    end;
    { Pop one register per pushed SLOT into %rsi onwards (%rdi is the sret ptr,
      loaded below).  ArgPushed/8 = total slots; topmost slot -> highest reg. }
    for I := (ArgPushed div 8) - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    { The saved dest sits just below the hoist region. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [HTotal]));
    Self.Emit(#9'callq ' + AFuncSym);
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  end
  else
  begin
    { >5 explicit args + sret: pre-allocate (Count+1) slots (sret = slot 0,
      explicit args = slots 1..Count).  Evaluate, load regs, leave overflow.
      This overflow path assumes one slot per logical arg; an interface arg
      (two slots) is not yet handled here.  Fail loudly rather than silently
      mis-place registers — the <=5-slot path above covers interface args. }
    for I := 0 to AArgs.Count - 1 do
    begin
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := TASTExpr(AArgs.Items[I]).ResolvedType;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      if (not IsVar) and (ParamType <> nil) and (ParamType.Kind = tyInterface) then
        raise ENativeCodeGenError.Create('native backend: interface argument in ' +
          'an sret call with more than 5 register slots is not yet supported');
    end;
    AllocSz := (((AArgs.Count + 1) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]))
      else if IsVar then
        Self.EmitVarArgAddrToRax(Arg)
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
    end;
    { Load sret ptr into %rdi, first 5 explicit args into %rsi..%r9. }
    Self.Emit(#9'movq 0(%rsp), %rdi');
    for I := 0 to 4 do
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [(I + 1) * 8, SysVArg64(I + 1)]));
    { Shift %rsp past the 6 register-bound slots (sret + 5 args). }
    Self.Emit(Format(#9'addq $%d, %%rsp', [6 * 8]));
    Self.Emit(#9'callq ' + AFuncSym);
    CleanUp := AllocSz - 6 * 8;
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  end;
  { Reclaim the saved dest slot. }
  Self.Emit(#9'addq $8, %rsp');
  HD.Free();
  HK.Free();
end;

{ Free a record-call-receiver buffer materialised by EmitMethodSretCall (see
  the RecvBufBytes prologue there).  No-op when ABytes = 0.  Does not touch the
  sret destination (written via its own pointer) nor any return register. }
procedure TX86_64Backend.EmitMethodSretRecvCleanup(ABytes: Integer);
begin
  if ABytes > 0 then
  begin
    { Mirror the prologue's pushes: subq buffer, pushq %rbx, pushq %r14
      (in that order) -> free buffer, popq %rbx, popq %r14. }
    Self.Emit(Format(#9'addq $%d, %%rsp', [ABytes]));
    Self.Emit(#9'popq %rbx');
    Self.Emit(#9'popq %r14');
  end;
end;

{ Emit a method call that returns a record via the sret convention.
  Register layout: %rdi = sret ptr, %rsi = Self, %rdx.. = user args.
  The destination buffer is at ASretAddr (AT&T operand, already allocated). }
procedure TX86_64Backend.EmitMethodSretCall(ACall: TMethodCallExpr;
                                            const ASretAddr: string;
                                            ASretIsIndirect: Boolean;
                                            AForceStatic: Boolean);
var
  I:        Integer;
  MD:       TMethodDecl;
  Sym:      string;
  Arg:      TASTExpr;
  AllocSz:  Integer;
  CleanUp:  Integer;
  RC:       TRecReturnClass;
  RetRec:   TRecordTypeDesc;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  HasFloat: Boolean;
  ParamType: TTypeDesc;
  IntIdx, XmmIdx, SlotOff: Integer;
  RecvBufBytes: Integer;
  LSretAddr: string;
  LSretIndirect: Boolean;
  UserSlots: Integer;
begin
  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: method-sret call has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Record-returning static factory (TypeName.Make(args): TRec): NO implicit
    Self, so it follows the plain record-return ABI exactly — sret buffer in
    %rdi, user args in %rsi.. — which is what EmitSretCall (the free-function
    record-return emitter) already produces.  Delegate to it with the method's
    mangled symbol; the Self-threading code below is for instance methods only. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    Self.EmitSretCall(Sym, MD, ACall.Args, ASretAddr, ASretIsIndirect);
    Exit;
  end;

  { Record-returning-call receiver (e.g. A.Plus(B).Scale(2), where the OUTER
    method Scale itself returns a record via sret): materialise the inner call
    result into a stack buffer up front and carry its address in callee-saved
    %rbx, which survives all the arg-evaluation %rsp movement below.  Every
    ObjExpr-receiver site loads %rbx instead of evaluating the call value as a
    pointer; the buffer + %rbx are freed at each exit (EmitMethodSretCleanup).

    Because this prologue moves %rsp, a caller-supplied %rsp-relative ASretAddr
    (the recursive EmitRecordCallSretAt('(%rsp)') case in a nested chain like
    A.Plus(B).Plus(A)) would drift.  Resolve the destination to an ABSOLUTE
    pointer FIRST, save it in callee-saved %r14, and re-express the rest of the
    routine as an indirect store through %r14. }
  RecvBufBytes := 0;
  LSretAddr := ASretAddr;
  LSretIndirect := ASretIsIndirect;
  if (ACall.ObjExpr <> nil) and MD.IsRecordMethod and
     Self.IsNativeRecordCall(ACall.ObjExpr) then
  begin
    RecvBufBytes := Self.RecArgBufBytes(ACall.ObjExpr);
    { Resolve the destination to an absolute pointer BEFORE pushing anything —
      a %rsp-relative ASretAddr (the recursive EmitRecordCallSretAt('(%rsp)')
      case) must be read while %rsp still has its caller value. }
    if ASretIsIndirect then
      Self.Emit(Format(#9'movq %s, %%rax', [ASretAddr]))
    else
      Self.Emit(Format(#9'leaq %s, %%rax', [ASretAddr]));
    Self.Emit(#9'pushq %r14');
    Self.Emit(#9'movq %rax, %r14');
    { %r14 now HOLDS the destination address.  Express it as a non-indirect
      operand so consumers do `leaq (%r14), %reg` (i.e. %reg := %r14), not a
      double dereference. }
    LSretAddr := '(%r14)';
    LSretIndirect := False;
    Self.Emit(#9'pushq %rbx');
    Self.Emit(Format(#9'subq $%d, %%rsp', [RecvBufBytes]));
    Self.EmitRecordCallSretAt(ACall.ObjExpr, '(%rsp)');
    Self.Emit(#9'movq %rsp, %rbx');
  end;

  { Check for register-return: no hidden sret param, Self goes in %rdi,
    args in %rsi onwards.  RetRec is the real record or the canonical
    method-ptr record (a method pointer is a 16-byte [Code; Data] rcInt2). }
  RC := rcSret;
  RetRec := AggRetRec(MD.ResolvedReturnType);
  if RetRec <> nil then
    RC := ClassifyRecordReturn(RetRec);
  if RC <> rcSret then
  begin
    if LSretIndirect then
      Self.Emit(Format(#9'movq %s, %%r10', [LSretAddr]))
    else
      Self.Emit(Format(#9'leaq %s, %%r10', [LSretAddr]));
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx', [RetRec.TotalSize()]));
    Self.Emit(#9'callq memset');
    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;
    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rdi');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rdi), %rdi');
      end
      else
      begin
        if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [Self.GlobalSymName(ACall.ObjectName)]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rdi')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %rdi');
    end
    else
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
    { Pop one register per SLOT (interface args take two) into %rsi onwards;
      Self occupies %rdi (slot index 0), so user slots start at index 1. }
    for I := Self.CountArgSlots(MD.Params) - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    if (MD.VTableSlot >= 0) and not AForceStatic then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
    Self.EmitRecordRegReturnCapture(LSretAddr, RetRec, RC, LSretIndirect);
    Self.EmitMethodSretRecvCleanup(RecvBufBytes);
    Exit;
  end;

  { Save the destination address below the hoist region — no caller-saved
    register survives argument evaluation, and a %rsp-relative ASretAddr
    would drift once the region is live. }
  if LSretIndirect then
    Self.Emit(Format(#9'movq %s, %%rax', [LSretAddr]))
  else
    Self.Emit(Format(#9'leaq %s, %%rax', [LSretAddr]));
  Self.Emit(#9'pushq %rax');
  if (MD.ResolvedReturnType <> nil) then
  begin
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx',
      [MD.ResolvedReturnType.RawSize()]));
    Self.Emit(#9'callq memset');
  end;

  { Detect a float-typed by-value argument.  The integer push/pop path below
    cannot carry one to an %xmm register, so route the whole call through a
    slot-based scheme: sret = slot 0 (%rdi), Self = slot 1 (%rsi), explicit
    args = slots 2..Count+1, int args load into %rdx.. and float args into
    %xmm0.. per the SysV ABI. }
  HasFloat := False;
  for I := 0 to ACall.Args.Count - 1 do
  begin
    ParamType := nil;
    if I < MD.Params.Count then
      ParamType := TMethodParam(MD.Params.Items[I]).ResolvedType;
    if ParamType = nil then
      ParamType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
    if IsFloatFamily(ParamType) and
       not ((I < MD.Params.Count) and TMethodParam(MD.Params.Items[I]).IsVarParam) then
      HasFloat := True;
  end;

  if HasFloat then
  begin
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    AllocSz := (((ACall.Args.Count + 2) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    { sret into slot 0. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    { Evaluate each explicit arg into slot I+2 (float kept in its slot for the
      xmm load below; int/record-ptr via movq). }
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      ParamType := nil;
      if I < MD.Params.Count then
        ParamType := TMethodParam(MD.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 2) * 8]));
      end
      else if IsFloatFamily(ParamType) and
              not ((I < MD.Params.Count) and
                   TMethodParam(MD.Params.Items[I]).IsVarParam) then
      begin
        Self.EmitExprToXmm0(Arg);
        { Match the value width to the PARAM width before spilling — see the
          same adjust in EmitSretCall (BUG-027 class). }
        Self.EmitXmm0WidthAdjust(Arg.ResolvedType,
          (ParamType <> nil) and (ParamType.Kind = tySingle));
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %%xmm0, %d(%%rsp)', [(I + 2) * 8]))
        else
          Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [(I + 2) * 8]));
      end
      else
      begin
        if (I < MD.Params.Count) and TMethodParam(MD.Params.Items[I]).IsVarParam then
          Self.EmitVarArgAddrToRax(Arg)
        else
          Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 2) * 8]));
      end;
    end;
    { Self pointer into slot 1. }
    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rax');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rax), %rax');
      end
      else if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [Self.GlobalSymName(ACall.ObjectName)]));
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rax')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 8(%%rsp)', []));
    { Load registers: %rdi = sret, %rsi = Self, then int args into %rdx.. and
      float args into %xmm0.. }
    Self.Emit(#9'movq 0(%rsp), %rdi');
    Self.Emit(#9'movq 8(%rsp), %rsi');
    IntIdx := 2;   { %rdi (sret), %rsi (Self) consumed }
    XmmIdx := 0;
    for I := 0 to ACall.Args.Count - 1 do
    begin
      ParamType := nil;
      if I < MD.Params.Count then
        ParamType := TMethodParam(MD.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
      SlotOff := (I + 2) * 8;
      if IsFloatFamily(ParamType) and
         not ((I < MD.Params.Count) and TMethodParam(MD.Params.Items[I]).IsVarParam) then
      begin
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]))
        else
          Self.Emit(Format(#9'movsd %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]));
        Inc(XmmIdx);
      end
      else
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
        Inc(IntIdx);
      end;
    end;
    Self.Emit(Format(#9'movb $%d, %%al', [XmmIdx]));
    Self.Emit(Format(#9'addq $%d, %%rsp', [(ACall.Args.Count + 2) * 8]));
    if (MD.VTableSlot >= 0) and not AForceStatic then
    begin
      Self.Emit(#9'movq (%rsi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      { %al was clobbered by the vtable load; for a fixed prototype the callee
        ignores it, so this is benign. }
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    CleanUp := AllocSz - (ACall.Args.Count + 2) * 8;
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
    Self.Emit(#9'addq $8, %rsp');   { reclaim the saved dest slot }
    Self.EmitMethodSretRecvCleanup(RecvBufBytes);
    Exit;
  end;

  { Register-path guard is on SLOTS, not logical args: an interface argument is
    a fat pointer occupying TWO integer registers, so a 2-arg call can need more
    registers than 2.  sret (%rdi) + Self (%rsi) consume two; the user args must
    fit in the remaining four. }
  UserSlots := Self.CountArgSlots(MD.Params);
  if UserSlots + 2 <= 6 then
  begin
    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;

    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rsi');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rsi), %rsi');
      end
      else
      begin
        if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rsi', [Self.GlobalSymName(ACall.ObjectName)]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rsi')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %rsi');
    end
    else
      Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand('Self')]));

    { Pop one register per SLOT (interface args occupy two), into the integer
      registers after %rdi (sret) and %rsi (Self): %rdx, %rcx, %r8, %r9. }
    Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 2);
    { The saved dest sits just below the call frame's hoist region. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [Self.TopFrameTotal()]));
    if (MD.VTableSlot >= 0) and not AForceStatic then
    begin
      Self.Emit(#9'pushq %rdi');
      Self.Emit(#9'movq (%rsi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
      Self.Emit(#9'popq %rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
  end
  else
  begin
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    AllocSz := (((ACall.Args.Count + 2) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]))
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 2) * 8]));
    end;
    if ACall.ObjectName <> '' then
    begin
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [Self.GlobalSymName(ACall.ObjectName)]));
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rax')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 8(%%rsp)', []));
    Self.Emit(#9'movq 0(%rsp), %rdi');
    for I := 0 to 4 do
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [(I + 1) * 8, SysVArg64(I + 1)]));
    Self.Emit(Format(#9'addq $%d, %%rsp', [6 * 8]));
    Self.Emit(#9'callq ' + Sym);
    CleanUp := AllocSz - 6 * 8;
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
  end;
  { Reclaim the saved dest slot. }
  Self.Emit(#9'addq $8, %rsp');
  Self.EmitMethodSretRecvCleanup(RecvBufBytes);
end;

{ Sret an inherited record return: build a transient implicit-Self method node
  carrying the parent method + the inherited call's args and emit it
  force-static, so EmitMethodSretCall threads the sret pointer / register-return
  capture the same way every other record-returning call does (instead of a
  second copy of the sret sequence).  The Args list is borrowed and detached
  before Free so the caller's node keeps ownership. }
procedure TX86_64Backend.EmitInheritedRecordSret(MD: TMethodDecl;
  AArgs: TObjectList; const AName, ADest: string; ADestIsIndirect: Boolean);
var
  Shim: TMethodCallExpr;
begin
  { An inherited call is an implicit-Self call (ObjectName = '' and ObjExpr =
    nil, so EmitMethodSretCall loads the receiver from the current Self slot)
    dispatched STATICALLY to the parent's method. }
  Shim := TMethodCallExpr.Create();
  Shim.ResolvedMethod := MD;
  Shim.Name := AName;
  Shim.Args := AArgs;
  Self.EmitMethodSretCall(Shim, ADest, ADestIsIndirect, True);
  Shim.Args := nil;
  Shim.Free();
end;

{ Emit a standalone function call that returns an interface via sret.
  Allocates a 16-byte buffer on the stack, passes its address as the first
  hidden arg (%rdi), calls the function, and leaves the buffer on the stack
  (caller loads obj at 0(%rsp) and itab at 8(%rsp), then addq $16, %rsp). }
procedure TX86_64Backend.EmitIntfSretCall(ACall: TFuncCallExpr);
var
  I:      Integer;
  MD:     TMethodDecl;
  FSym:   string;
  Arg:    TASTExpr;
  ArgCnt: Integer;
  Par:    TMethodParam;
  HD:     TList<Integer>;
  HK:     TList<Integer>;
  HTotal: Integer;
  Pushed: Integer;
  OverflowBytes: Integer;
begin
  MD := TMethodDecl(ACall.ResolvedDecl);
  FSym := FuncSymbolOf(ACall);
  ArgCnt := ACall.Args.Count;
  { Hoist region BELOW the sret buffer: the buffer must sit exactly at %rsp
    when the call is made, so the region cannot live between buffer and call.
    After the call the buffer is relocated down over the region so callers
    keep their `fat pointer at (%rsp), addq $16` contract. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
  { Allocate the 16-byte sret buffer on the stack and zero it. }
  Self.Emit(#9'subq $16, %rsp');
  Self.Emit(#9'movq $0, (%rsp)');
  Self.Emit(#9'movq $0, 8(%rsp)');
  if ACall.IsImplicitSelfMethod then
  begin
    { Open-array literal args raise in EmitMethodArgPush — unsupported for
      interface-sret calls. }
    Pushed := 0;
    for I := 0 to ArgCnt - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [16 + HTotal - HD.Get(I) + Pushed]));
        Self.Emit(#9'pushq %rax');
        Pushed := Pushed + 8;
      end
      else
      begin
        Self.EmitMethodArgPush(Par, Arg);
        if Par.IsOpenArray or
           ((Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface)) then
          Pushed := Pushed + 16
        else
          Pushed := Pushed + 8;
      end;
    end;
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    { Consume args (base 2: %rdi = sret buffer, %rsi = Self); spill overflow. }
    OverflowBytes := Self.EmitSretRegArgs(Self.CountArgSlots(MD.Params), 2);
    Self.Emit(#9'movq %r10, %rsi');
    Self.Emit(#9'movq %rsp, %rdi');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
    { Virtual implicit-Self interface-sret call dispatches through the vtable
      (Self is in %rsi here; %rdi holds the sret buffer). }
    Self.EmitSelfDispatchVia(MD, FSym, '%rsi');
  end
  else
  begin
    Pushed := 0;
    for I := 0 to ArgCnt - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [16 + HTotal - HD.Get(I) + Pushed]))
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
      Pushed := Pushed + 8;
    end;
    { Consume args (base 1: %rdi = sret buffer); spill overflow. }
    OverflowBytes := Self.EmitSretRegArgs(ArgCnt, 1);
    Self.Emit(#9'movq %rsp, %rdi');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
    Self.Emit(#9'callq ' + FSym);
  end;
  { Reclaim overflow stack args before touching the sret buffer. }
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
  { Post-call: release hoisted values (the 16-byte buffer sits between %rsp
    and the region), then slide the buffer down over the region so the
    caller's contract holds. }
  Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
  Self.EmitSretBufferSlideDown(HTotal);
  HD.Free();
  HK.Free();
end;

procedure TX86_64Backend.EmitIntfSretMethodCall(ACall: TMethodCallExpr);
var
  I, SlotOff, ArgN: Integer;
  Arg: TASTExpr;
  IntfD: TInterfaceTypeDesc;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
  IE: TIdentExpr;
  OverflowBytes: Integer;
begin
  IntfD := TInterfaceTypeDesc(ACall.ResolvedClassType);
  ArgN := 0;
  if ACall.Args <> nil then ArgN := ACall.Args.Count;
  { Same unknown-signature hoist as EmitInterfaceCall; the region sits BELOW
    the sret buffer (see EmitIntfSretCall for the layout rationale). }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := IntfD.MethodParamVarFlagsStr(IntfD.MethodIndex(ACall.Name));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, ACall.Args, HD, HK);
  { Allocate and zero the 16-byte sret buffer. }
  Self.Emit(#9'subq $16, %rsp');
  Self.Emit(#9'movq $0, (%rsp)');
  Self.Emit(#9'movq $0, 8(%rsp)');
  Pushed := 0;
  { Push args left-to-right; interface args push obj then itab (2 slots). }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      { Hoisted record-call or string argument — reload the saved value
        (+16 for the sret buffer between %rsp and the hoist region). }
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [16 + HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      { var/out position: pass the slot ADDRESS — same rule as direct
        calls; covers managed types (string, dynarray) the callee rebinds. }
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in sret interface dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Resolve the receiver: obj into %r10, itab into %rax. }
  if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TFieldAccessExpr) then
  begin
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(ACall.ObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) and
          TIdentExpr(ACall.ObjExpr).IsImplicitSelf and
          (TIdentExpr(ACall.ObjExpr).ImplicitFieldInfo <> nil) then
  begin
    { Interface field of Self as receiver: fat pointer at Self + offset. }
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    if TFieldInfo(IE.ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r10',
        [TFieldInfo(IE.ImplicitFieldInfo).Offset]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) then
  begin
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(IE.Name, IE.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(IE.Name, IE.IsGlobal)]));
  end
  else if ACall.ObjExpr <> nil then
    raise ENativeCodeGenError.Create(
      'native backend: unsupported receiver expression in sret interface dispatch')
  else if ACall.IsVarParam then
  begin
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(ACall.ObjectName, ACall.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(ACall.ObjectName, ACall.IsGlobal)]));
  end;
  SlotOff := IntfD.MethodIndex(ACall.Name) * 8;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Pop args shifted by 2: %rdi = sret buffer, %rsi = receiver obj.
    var positions take one slot. }
  SlotOff := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if (not Self.VarFlagAt(VFlags, I)) and (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Inc(SlotOff, 2)
    else
      Inc(SlotOff);
  end;
  { Consume args (base 2: %rdi = sret buffer, %rsi = receiver obj); spill
    overflow slots beyond the 4 remaining registers to the stack. }
  OverflowBytes := Self.EmitSretRegArgs(SlotOff, 2);
  Self.Emit(#9'movq %r10, %rsi');
  Self.Emit(#9'movq %rsp, %rdi');
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
  Self.Emit(#9'callq *%r11');
  { Reclaim overflow stack args before touching the sret buffer. }
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
  { Post-call: release hoisted values, then slide the buffer down over the
    hoist region so the caller's `fat pointer at (%rsp)` contract holds. }
  Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
  Self.EmitSretBufferSlideDown(HTotal);
  HD.Free();
  HK.Free();
end;

procedure TX86_64Backend.EmitIntfRecordSretDispatch(ACall: TMethodCallExpr;
  const ADest: string; ADestIsIndirect: Boolean);
var
  I, SlotOff, ArgN, Slots: Integer;
  Arg: TASTExpr;
  IntfD: TInterfaceTypeDesc;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
  IE: TIdentExpr;
  OverflowBytes, ABase: Integer;
  RC: TRecReturnClass;
  RetRec: TRecordTypeDesc;
begin
  IntfD := TInterfaceTypeDesc(ACall.ResolvedClassType);
  RetRec := TRecordTypeDesc(ACall.ResolvedType);
  RC := ClassifyRecordReturn(RetRec);
  ArgN := 0;
  if ACall.Args <> nil then ArgN := ACall.Args.Count;

  { Resolve the destination to an ABSOLUTE pointer FIRST, in callee-saved %r14,
    before any %rsp movement (arg pushes / overflow spill) can drift a
    %rsp-relative ADest. }
  Self.Emit(#9'pushq %r14');
  if ADestIsIndirect then
    Self.Emit(Format(#9'movq %s, %%r14', [ADest]))
  else
    Self.Emit(Format(#9'leaq %s, %%r14', [ADest]));

  { Same unknown-signature hoist as EmitIntfSretMethodCall; the region sits
    BELOW any sret buffer space we reserve. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := IntfD.MethodParamVarFlagsStr(IntfD.MethodIndex(ACall.Name));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, ACall.Args, HD, HK);
  Pushed := 0;
  { Push args left-to-right; interface args push obj then itab (2 slots). }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in sret interface record dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Resolve the receiver: obj into %r10, itab into %rax. }
  if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TFieldAccessExpr) then
  begin
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(ACall.ObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) and
          TIdentExpr(ACall.ObjExpr).IsImplicitSelf and
          (TIdentExpr(ACall.ObjExpr).ImplicitFieldInfo <> nil) then
  begin
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    if TFieldInfo(IE.ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r10',
        [TFieldInfo(IE.ImplicitFieldInfo).Offset]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) then
  begin
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(IE.Name, IE.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(IE.Name, IE.IsGlobal)]));
  end
  else if ACall.ObjExpr <> nil then
    raise ENativeCodeGenError.Create(
      'native backend: unsupported receiver expression in sret interface record dispatch')
  else if ACall.IsVarParam then
  begin
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(ACall.ObjectName, ACall.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(ACall.ObjectName, ACall.IsGlobal)]));
  end;
  SlotOff := IntfD.MethodIndex(ACall.Name) * 8;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));

  { Count the arg SLOTS (var positions one slot; interface args two). }
  Slots := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if (not Self.VarFlagAt(VFlags, I)) and (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Inc(Slots, 2)
    else
      Inc(Slots);
  end;

  if RC = rcSret then
  begin
    { Memory-class record: hidden sret pointer in %rdi, receiver obj in %rsi,
      visible args from %rdx (base index 2).  The dest buffer is %r14. }
    Self.Emit(#9'movq %r14, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx', [RetRec.TotalSize()]));
    Self.Emit(#9'pushq %r10');           { preserve receiver obj across memset }
    Self.Emit(#9'pushq %r11');           { preserve fptr across memset }
    Self.Emit(#9'callq memset');
    Self.Emit(#9'popq %r11');
    Self.Emit(#9'popq %r10');
    ABase := 2;
    OverflowBytes := Self.EmitSretRegArgs(Slots, ABase);
    Self.Emit(#9'movq %r10, %rsi');
    Self.Emit(#9'movq %r14, %rdi');
    Self.Emit(#9'callq *%r11');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 0, True);
  end
  else
  begin
    { Register-class record: NO hidden sret arg.  Receiver obj in %rdi,
      visible args from %rsi (base index 1).  Capture the register return
      into the dest buffer (%r14). }
    ABase := 1;
    OverflowBytes := Self.EmitSretRegArgs(Slots, ABase);
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'callq *%r11');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
    { %r14 still holds the dest pointer (callee-saved across the call). }
    Self.EmitRecordRegReturnCapture('%r14', RetRec, RC, True);
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 0, True);
  end;
  HD.Free();
  HK.Free();
  Self.Emit(#9'popq %r14');
end;

procedure TX86_64Backend.EmitClassIntfSretMethodCall(ACall: TMethodCallExpr);
var
  I: Integer;
  MD: TMethodDecl;
  Sym: string;
  Arg: TASTExpr;
  Par: TMethodParam;
  UserSlots: Integer;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal: Integer;
  Pushed: Integer;
  OverflowBytes: Integer;
begin
  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: class sret interface call has no ResolvedMethod (' +
      ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Static method returning an interface (TypeName.GetIt: IFoo): there is NO
    receiver, so the call follows the plain free-function interface-sret ABI —
    sret buffer in %rdi, user args from %rsi (base 1), and a direct callq to the
    mangled static symbol.  Without this branch the code below would treat the
    bare TypeName (ACall.ObjectName) as a global Self and emit a load of an
    undefined `TypeName` symbol.  Mirrors the non-Self `else` arm of
    EmitIntfSretCall. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    UserSlots := Self.CountArgSlots(MD.Params);
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    Self.Emit(#9'subq $16, %rsp');
    Self.Emit(#9'movq $0, (%rsp)');
    Self.Emit(#9'movq $0, 8(%rsp)');
    Pushed := 0;
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [16 + HTotal - HD.Get(I) + Pushed]));
        Self.Emit(#9'pushq %rax');
        Pushed := Pushed + 8;
      end
      else
      begin
        Self.EmitMethodArgPush(Par, Arg);
        if Par.IsOpenArray or
           ((Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface)) then
          Pushed := Pushed + 16
        else
          Pushed := Pushed + 8;
      end;
    end;
    { Base 1: %rdi = sret buffer, user args from %rsi; no Self register. }
    OverflowBytes := Self.EmitSretRegArgs(UserSlots, 1);
    Self.Emit(#9'movq %rsp, %rdi');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
    Self.Emit(#9'callq ' + Sym);
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
    Self.EmitSretBufferSlideDown(HTotal);
    HD.Free();
    HK.Free();
    Exit;
  end;

  UserSlots := Self.CountArgSlots(MD.Params);
  { %rdi = sret buffer, %rsi = Self leave four integer arg registers; further
    slots spill to the stack via EmitSretRegArgs (ABase = 2). }
  { Hoist region BELOW the sret buffer — same layout rationale as
    EmitIntfSretCall. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
  Self.Emit(#9'subq $16, %rsp');
  Self.Emit(#9'movq $0, (%rsp)');
  Self.Emit(#9'movq $0, 8(%rsp)');
  Pushed := 0;
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MD.Params.Items[I]);
    Arg := TASTExpr(ACall.Args.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [16 + HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
      Pushed := Pushed + 8;
    end
    else
    begin
      Self.EmitMethodArgPush(Par, Arg);
      if Par.IsOpenArray or
         ((Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface)) then
        Pushed := Pushed + 16
      else
        Pushed := Pushed + 8;
    end;
  end;
  { Receiver into %r10 — mirrors EmitMethodCallExpr's resolution for
    class-typed receivers. }
  if ACall.ObjectName <> '' then
  begin
    if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%r10), %r10');
    end
    else if Self.IsCaptured(ACall.ObjectName) then
    begin
      Self.Emit(Format(#9'movq %s, %%r10',
        [Self.VarOperand('_cap_' + ACall.ObjectName)]));
      Self.Emit(#9'movq (%r10), %r10');
    end
    else if Self.IsLocal(ACall.ObjectName) then
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %%r10', [Self.GlobalSymName(ACall.ObjectName)]));
  end
  else if ACall.ObjExpr <> nil then
  begin
    Self.EmitExprToEax(ACall.ObjExpr);
    Self.Emit(#9'movq %rax, %r10');
  end
  else
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
  { Consume args into registers (shifted by 2: %rdi = sret buffer,
    %rsi = receiver); slots beyond the 4 remaining registers spill. }
  OverflowBytes := Self.EmitSretRegArgs(UserSlots, 2);
  Self.Emit(#9'movq %r10, %rsi');
  Self.Emit(#9'movq %rsp, %rdi');
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
  if MD.VTableSlot >= 0 then
  begin
    { Virtual dispatch through the receiver's vtable (slot 0 is the
      typeinfo pointer, hence +1). }
    Self.Emit(#9'movq (%rsi), %rax');
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + Sym);
  { Reclaim any overflow stack args before touching the sret buffer. }
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
  { Post-call: release hoisted values, then slide the buffer down over the
    hoist region so the caller's `fat pointer at (%rsp)` contract holds. }
  Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
  Self.EmitSretBufferSlideDown(HTotal);
  HD.Free();
  HK.Free();
end;

{ Emit a method-pointer (of-object) call through a TMethod block.
  APtrOperand is the AT&T memory operand for the 16-byte Code+Data block.
  Load Code into %r10, Data into %rdi, push/pop other args, then callq *%r10. }
procedure TX86_64Backend.EmitMethodPtrCall(const APtrOperand: string;
                                           AProcType: TProceduralTypeDesc;
                                           AArgs: TObjectList);
var
  I:       Integer;
  Arg:     TASTExpr;
  AllocSz: Integer;
  CleanUp: Integer;
  HD:      TList<Integer>;
  HK:      TList<Integer>;
  HTotal:  Integer;
  PParams: TObjectList;
begin
  PParams := nil;
  if AProcType <> nil then
    PParams := AProcType.Params;
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(nil, PParams, True, '', AArgs, HD, HK);
  { Code/Data are loaded into %r10/%r11 only AFTER all argument evaluation:
    both are caller-saved, so any call emitted while evaluating an argument
    (or the hoist pre-pass above) would clobber them.  APtrOperand is %rbp-
    or %rip-relative, never %rsp-relative. }

  if AArgs.Count <= 5 then
  begin
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [HTotal - HD.Get(I) + I * 8]));
        Self.Emit(#9'pushq %rax');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
    end;
    for I := AArgs.Count - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    Self.Emit(Format(#9'leaq %s, %%r11', [APtrOperand]));
    Self.Emit(#9'movq (%r11), %r10');
    Self.Emit(#9'movq 8(%r11), %rdi');
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  end
  else
  begin
    { >5 explicit args: pre-allocate (Count+1) slots (slot 0 unused, args=1..N). }
    AllocSz := (((AArgs.Count + 1) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]))
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
    end;
    Self.Emit(Format(#9'leaq %s, %%rcx', [APtrOperand]));
    Self.Emit(#9'movq (%rcx), %r10');
    Self.Emit(#9'movq 8(%rcx), %rdi');
    for I := 0 to 4 do
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [(I + 1) * 8, SysVArg64(I + 1)]));
    { Copy the overflow args (slots 6.., offsets 48..) into a FRESH region
      below the slot block so the call sees them at 0(%rsp).. on a 16-byte-
      aligned %rsp regardless of pinned pushes above (see AlignFreshBytes). }
    CleanUp := Self.AlignFreshBytes(AArgs.Count - 5);
    Self.Emit(Format(#9'subq $%d, %%rsp', [CleanUp]));
    for I := 0 to AArgs.Count - 6 do
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [CleanUp + 48 + I * 8]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * 8]));
    end;
    CleanUp := CleanUp + AllocSz;
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  end;
  HD.Free();
  HK.Free();
end;

{ True when AType is an integer-family type the backend can place in a
  general-purpose register (Byte..Int64).  Floats, records, strings, etc. are
  not yet handled and must fail loudly. }
function IsIntFamily(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    (AType.Kind in [tyInteger, tyUInt32, tyInt64, tyUInt64,
                    tySmallInt, tyWord, tyByte, tyBoolean, tyEnum]);
end;

{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  The args array layout (matching the QBE backend and blaise_str.pas):
    slot[I] at arr + I*16:  [0..7] = type tag (0=int, 1=string); [8..15] = value.
  We allocate the array on the stack via subq, fill it, then call the RTL. }
{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  Stack layout at the callq:
    [%rbp - old_frame ... fmt_ptr ... arr[0]...arr[N-1]] → then call
  The args array layout (matching the QBE backend and blaise_str.pas):
    slot[I] at arr + I*16: [0..7]=type tag (0=int, 1=str); [8..15]=value. }
{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  The args array layout (matching the QBE backend):
    slot[I] at arr + I*16: [0..7]=type tag (0=int, 1=str); [8..15]=value.
  Stack discipline: evaluate fmt first and push it (so later push/pop from
  nested expr evaluation cannot overwrite the array we build below it). }
procedure TX86_64Backend.EmitFormatCall(AArgs: TObjectList);
var
  I:         Integer;
  FmtCount:  Integer;
  Arg:       TASTExpr;
  IsIntArg:  Boolean;
  TotalSize: Integer;
  ArrLit:    TArrayLiteralExpr;
  UseArray:  Boolean;
begin
  { Forwarded 'array of const' param (BUG-047): Format(fmt, ArgsParam) where
    ArgsParam is a plain open-array-of-TVarRec reference, not a bracket
    literal.  The runtime holds real 16-byte TVarRecs; _StringFormatVarRecs
    translates them to the 3-tag block.  Count = high + 1 from the companion
    _high slot. }
  if (AArgs.Count = 2) and (TASTExpr(AArgs.Items[1]) is TIdentExpr) and
     (TASTExpr(AArgs.Items[1]).ResolvedType <> nil) and
     (TASTExpr(AArgs.Items[1]).ResolvedType is TOpenArrayTypeDesc) and
     (TOpenArrayTypeDesc(
        TASTExpr(AArgs.Items[1]).ResolvedType).ElementType <> nil) and
     SameText(TOpenArrayTypeDesc(
        TASTExpr(AArgs.Items[1]).ResolvedType).ElementType.Name, 'TVarRec') then
  begin
    { The _high companion must be a slot of the CURRENT frame.  A captured
      array-of-const param (referenced from a nested routine) does not forward
      its _high companion, and VarOperand would silently fall back to a
      module-global operand — a wrong count read.  Keep it honest. }
    if not Self.IsLocal(TIdentExpr(AArgs.Items[1]).Name + '_high') then
      raise ENativeCodeGenError.Create(
        'native backend: Format over a captured array-of-const parameter ' +
        'not supported at line ' + IntToStr(TASTExpr(AArgs.Items[1]).Line));
    Self.EmitExprToEax(TASTExpr(AArgs.Items[0]));   { %rdi = fmt }
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(TASTExpr(AArgs.Items[1]));   { %rsi = data ptr }
    Self.Emit(#9'movq %rax, %rsi');
    Self.Emit(Format(#9'movq %s, %%rdx',
      [Self.VarOperand(TIdentExpr(AArgs.Items[1]).Name + '_high')]));
    Self.Emit(#9'incl %edx');                        { count = high + 1 }
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'callq _StringFormatVarRecs');
    Exit;
  end;
  UseArray := (AArgs.Count = 2) and (AArgs.Items[1] is TArrayLiteralExpr);
  if UseArray then
  begin
    ArrLit := TArrayLiteralExpr(AArgs.Items[1]);
    FmtCount := ArrLit.Elements.Count;
  end
  else
  begin
    ArrLit := nil;
    FmtCount := AArgs.Count - 1;
  end;
  Self.EmitExprToEax(TASTExpr(AArgs.Items[0]));
  Self.Emit(#9'pushq %rax');
  if FmtCount > 0 then
  begin
    TotalSize := ((FmtCount * 16) + 15) and (-16);
    Self.Emit(#9'pushq %rbx');
    Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSize]));
    Self.Emit(#9'movq %rsp, %rbx');
    for I := 0 to FmtCount - 1 do
    begin
      if UseArray then
        Arg := TASTExpr(ArrLit.Elements.Items[I])
      else
        Arg := TASTExpr(AArgs.Items[I + 1]);
      if (Arg.ResolvedType <> nil) and
         (Arg.ResolvedType.Kind in [tyDouble, tySingle]) then
      begin
        { Float arg: tag 2, value = raw IEEE-754 binary64 bits.  Evaluate to
          %xmm0, widen a Single to Double, then bit-copy the 64-bit pattern
          via movq into the value slot (matching the QBE backend's 'cast'). }
        Self.Emit(Format(#9'movq $2, %d(%%rbx)', [I * 16]));
        Self.EmitExprToXmm0(Arg);
        Self.EmitXmm0WidthAdjust(Arg.ResolvedType, False);
        Self.Emit(#9'movq %xmm0, %rax');
        Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [I * 16 + 8]));
        Continue;
      end;
      IsIntArg := (Arg.ResolvedType = nil) or
        (Arg.ResolvedType.Kind in [tyInteger, tyBoolean, tyByte, tyUInt32,
                                    tyInt64, tyUInt64, tySmallInt, tyWord, tyEnum]);
      if IsIntArg then
        Self.Emit(Format(#9'movq $0, %d(%%rbx)', [I * 16]))
      else
        Self.Emit(Format(#9'movq $1, %d(%%rbx)', [I * 16]));
      Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [I * 16 + 8]));
    end;
    Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [TotalSize + 8]));
    Self.Emit(#9'movq %rbx, %rsi');
    Self.Emit(Format(#9'movl $%d, %%edx', [FmtCount]));
    Self.Emit(#9'callq _StringFormatN');
    Self.Emit(Format(#9'addq $%d, %%rsp', [TotalSize]));
    Self.Emit(#9'popq %rbx');
    Self.Emit(#9'addq $8, %rsp');
  end
  else
  begin
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(#9'xorl %edx, %edx');
    Self.Emit(#9'callq _StringFormatN');
  end;
end;

{ Emit a standalone procedure/function definition.  Frame layout mirrors the
  reference (FPC -O- and the QBE backend): params, Result and locals each get
  an 8-byte-aligned %rbp-relative slot sized by their type; the prologue
  spills the incoming argument registers into the param slots at their width;
  the body runs through the slots; a function returns its Result slot
  (64-bit-extended) in %rax/%eax.  M5 supports integer-family value
  parameters and integer-family/void return. }
procedure TX86_64Backend.EmitFunctionDef(ADecl: TMethodDecl; AExported: Boolean);
var
  I, J:        Integer;
  P:           TMethodParam;
  Mark:        Integer;
  NestedDecl:  TMethodDecl;
  SavedOuterDecl: TMethodDecl;
  AddrTaken:   TStringList;
begin
  { Generic templates (routine- or method-level type params) are never
    emitted — call sites emit monomorphised instances. }
  if ADecl.TypeParams <> nil then Exit;
  { Emit any nested procedures declared inside this function's body before
    emitting this function itself.  Each nested proc gets a mangled name
    OuterName_InnerName to avoid global symbol collisions.  FDbgOuterDecl
    carries the enclosing decl so DbgMarkParams can type captured vars;
    saved/restored to keep doubly-nested emission consistent. }
  if ADecl.Body <> nil then
  begin
    SavedOuterDecl := FDbgOuterDecl;
    for I := 0 to ADecl.Body.ProcDecls.Count - 1 do
    begin
      NestedDecl := TMethodDecl(ADecl.Body.ProcDecls.Items[I]);
      if NestedDecl.Body = nil then Continue;
      { Prefix with the outer routine's RESOLVED symbol, not its bare name
        (BUG-20260720-method-nested-proc-mangle): a method's ResolvedQbeName
        carries the class ('TFoo_DoIt'), so its Inner is 'TFoo_DoIt_Inner' —
        distinct from another class's DoIt.Inner — and a multi-level chain
        composes to 'L1_L2_L3'.  Un-mangled name-space; platform prefix added
        downstream. }
      if ADecl.ResolvedQbeName <> '' then
        NestedDecl.ResolvedQbeName := ADecl.ResolvedQbeName + '_' + NestedDecl.Name
      else
        NestedDecl.ResolvedQbeName := ADecl.Name + '_' + NestedDecl.Name;
      FDbgOuterDecl := ADecl;
      Self.EmitFunctionDef(NestedDecl, False);
    end;
    FDbgOuterDecl := SavedOuterDecl;
  end;

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray then Continue;  { open array: (ptr, high) pair — always ok }
    if P.IsVarParam then Continue;  { var/out: always a pointer — ok }
    if not IsIntFamily(P.ResolvedType) and not IsFloatFamily(P.ResolvedType) and
       ((P.ResolvedType = nil) or
        not (P.ResolvedType.Kind in [tyString, tyPChar, tyPointer,
                                     tyClass, tyMetaClass, tyInterface,
                                     tyOpenArray, tyDynArray,
                                     tyRecord, tyStaticArray,
                                     tyProcedural, tySet])) then
      raise ENativeCodeGenError.Create(
        'native backend: unsupported parameter type (param ' + P.ParamName + ')');
  end;
  if (ADecl.ResolvedReturnType <> nil) and
     not IsIntFamily(ADecl.ResolvedReturnType) and
     not IsFloatFamily(ADecl.ResolvedReturnType) and
     not (ADecl.ResolvedReturnType.Kind in [tyRecord, tyStaticArray, tyString,
                                          tyPChar, tyPointer, tyClass, tyMetaClass,
                                          tyDynArray, tyInterface, tyProcedural,
                                          tySet]) then
    raise ENativeCodeGenError.Create(
      'native backend: unsupported return type (function ' + ADecl.Name + ')');

  { Set FCapturedVars for the duration of this function's emission so that
    variable-access paths redirect through the capture pointers. }
  FCapturedVars := ADecl.CapturedVars;
  FEnvVarNames  := ADecl.EnvCaptured;
  FBlockEnvVarNames := ADecl.BlockEnvCaptured;

  { Rebuild the borrowed-argument blocklist for this function: address-taken
    locals (explicit @, var/out args) plus anything captured by a nested
    procedure.  Consulted by ConstStrShape. }
  FConstArgUnsafe.Clear();
  if ADecl.Body <> nil then
  begin
    AddrTaken := CollectAddressTaken(ADecl.Body);
    for I := 0 to AddrTaken.Count - 1 do
      FConstArgUnsafe.Add(AddrTaken.Strings[I]);
    AddrTaken.Free();
    for I := 0 to ADecl.Body.ProcDecls.Count - 1 do
      if TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars <> nil then
        for J := 0 to TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars.Count - 1 do
          FConstArgUnsafe.Add(
            TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars.Strings[J]);
  end;

  Mark := Self.AsmMark();
  FPromoActive := False;
  for I := 0 to 3 do
  begin
    FPromoVars[I] := '';
    FPromoAvail[I] := False;
  end;
  Self.EmitFunctionCore(ADecl, AExported);
  { Two-pass register promotion: each pool register whose absence from
    the unpromoted text proves no scratch-window collision is available;
    candidates are assigned best-traffic-first across available slots. }
  for I := 0 to 3 do
    FPromoAvail[I] := not Self.AsmContainsFrom(Mark, PROMO_REGS[I]);
  if Self.SelectPromotions(ADecl, Mark) and
     ((FPromoLimit < 0) or (FPromoCount < FPromoLimit)) and
     ((FPromoOnly = '') or (FPromoOnly = FuncSymbolFromDecl(ADecl))) then
  begin
    FPromoCount := FPromoCount + 1;
    { %r13 free too?  Then the binary-op bracket may pin its LHS there
      across calls instead of pushq/popq. }
    FPromoPinOk := not Self.AsmContainsFrom(Mark, '%r13');
    FPinDepth := 0;
    if FPromoLog then
      WriteLn(StdErr, '[promo] ', FuncSymbolFromDecl(ADecl), ' [',
        FPromoVars[0], '/', FPromoVars[1], '/', FPromoVars[2], '/',
        FPromoVars[3], ']');
    Self.AsmRollback(Mark);
    FPromoActive := True;
    FPromoFunc := FuncSymbolFromDecl(ADecl);
    Self.EmitFunctionCore(ADecl, AExported);
    FPromoActive := False;
    FPromoPinOk := False;
    FPromoFunc := '';
  end;
  for I := 0 to 3 do
    FPromoVars[I] := '';
  FCapturedVars := nil;
  Self.ClearFrame();
end;

procedure TX86_64Backend.EmitFunctionCore(ADecl: TMethodDecl; AExported: Boolean);
var
  I, J:    Integer;
  P:       TMethodParam;
  Sym:     string;
  IntIdx:  Integer;
  XmmIdx:  Integer;
  SlotOff: Integer;
  SavedAsm: TStringBuilder;
  BodyBuf:  TStringBuilder;
  VD:       TVarDecl;
  AKind:    TArcReleaseKind;
begin
  Sym := FuncSymbolFromDecl(ADecl);
  Self.DbgBeginFunc(Sym);
  Self.BuildFrame(ADecl);
  Self.DbgMarkParams(ADecl);

  Self.Emit('.text');
  if AExported then
  begin
    { Generic-instance bodies (instance methods, monomorphised generic
      functions/methods) are emitted WEAK: any number of objects in a link
      may carry the identical copy and the linker keeps one (BUG-004).
      The internal assembler gives .globl precedence over .weak, so emit
      .weak INSTEAD OF .globl — gas treats a lone .weak the same way.

      Functions owned by an unmangled RTL unit (System, rtl.*, runtime.*,
      blaise_*) are ALSO emitted weak.  In the RTL archive each unit is a
      separate member, but a whole-program-per-unit build (--no-incremental
      without --skip-dep-codegen, as the RTL Makefile uses) inlines a
      dependency unit's bodies into every importing object.  Two archive
      members then define the same bare RTL symbol (e.g. _AtomicAddInt32 in
      both runtime.atomic.o and runtime.mem.o), and pulling both at link
      time is a multiple-definition error.  Weak binding lets the copies
      collapse — exactly the treatment RTL GLOBALS already get (GH #174,
      GlobalLinkWeak).  This fixes GH #180. }
    { _start is the ELF entry point: the internal linker resolves the entry
      symbol by name and requires a STRONG definition, so it must never be
      weakened even though runtime.start is an unmangled RTL unit. }
    if (StrPos('<', ADecl.OwnerTypeName) >= 0) or
       (StrPos('<', ADecl.Name) >= 0) or
       ((ADecl.OwningUnit <> '') and IsUnmangledUnit(ADecl.OwningUnit)
        and (Sym <> '_start')) then
      Self.Emit('.weak ' + Sym)
    else
      Self.Emit('.globl ' + Sym);
  end;
  Self.Emit(Sym + ':');
  { nostackframe: the body is an inline-asm block that owns the entire frame
    (prologue, args-from-registers, ret).  Emit no compiler prologue/epilogue,
    no param spill, no ARC — just the verbatim block.  This is the null-object
    frame strategy (see docs/inline-asm-design.adoc). }
  if ADecl.NoStackFrame then
  begin
    if (ADecl.Body <> nil) then
      Self.EmitStmtList(ADecl.Body.Stmts);
    Self.DbgEndFunc();
    Self.Emit('.type ' + Sym + ', @function');
    FExitLabel    := '';
    FCapturedVars := nil;
    FEnvVarNames  := nil;
    FBlockEnvVarNames := nil;
    Exit;
  end;
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  { The rest of the function is emitted into a side buffer so the frame-
    reserve subq below can be written with the FINAL frame size — the body
    may lazily grow the frame via EnsureExcFrameSlot (a try nested inside a
    finally body needs more exception-frame slots than BuildFrame's source-
    level pre-count provides). }
  SavedAsm := FAsm;
  BodyBuf := TStringBuilder.Create();
  FAsm := BodyBuf;
  try
  { Register promotion: save the callee-saved incumbents into their frame
    slots, then explicitly load any STACK-passed promoted param (it has no
    spill instruction — its home was the caller-pushed slot).  Register-
    passed promoted params land in the promoted register via the normal
    spill code below (VarOperand answers the register). }
  if FPromoActive then
  begin
    for I := 0 to 3 do
      if FPromoVars[I] <> '' then
        Self.Emit(Format(#9'movq %s, %s',
          [PROMO_REGS[I], Self.VarOperand('_promo_save_' + IntToStr(I))]));
    for I := 0 to 3 do
      if FPromoVars[I] <> '' then
        Self.PromoInitStackParam(FPromoVars[I], PROMO_REGS[I]);
    if FPromoPinOk then
      Self.Emit(Format(#9'movq %%r13, %s', [Self.VarOperand('_promo_save_pin')]));
  end;
  if FTryR15Save then
    Self.Emit(Format(#9'movq %%r15, %s', [Self.VarOperand('_try_r15_save')]));
  { Spill incoming argument registers into param slots.  SysV AMD64 passes
    integer args in %rdi/%rsi/... and float args in %xmm0/%xmm1/... independently.
    Track separate counters: IntIdx for integer params, XmmIdx for float params.
    For sret functions the hidden first integer arg (%rdi) is the destination
    buffer pointer; spill it into the Result slot first, then continue with
    the normal params starting at IntIdx=1. }
  IntIdx := 0;
  XmmIdx := 0;
  { Spill captured-var pointer params into their _cap_ slots. }
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
  begin
    for I := 0 to ADecl.CapturedVars.Count - 1 do
    begin
      Self.Emit(Format(#9'movq %s, %s',
        [SysVArg64(IntIdx),
         Self.VarOperand('_cap_' + ADecl.CapturedVars.Strings[I])]));
      Inc(IntIdx);
    end;
    { Captured METHOD Self (BUG-008): _cap_Self holds the address of the
      enclosing method's Self slot — load the receiver through it into this
      frame's real 'Self' slot so hardcoded implicit-Self paths work. }
    if (ADecl.OwnerTypeName = '') and
       (ADecl.CapturedVars.IndexOf('Self') >= 0) then
    begin
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand('_cap_Self')]));
      Self.Emit(#9'movq (%rax), %rax');
      Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand('Self')]));
    end;
  end;
  if FSretFunc then
  begin
    { Save the sret buffer pointer from %rdi into the Result slot. }
    Self.Emit(Format(#9'movq %%rdi, %s', [Self.VarOperand('Result')]));
    IntIdx := 1;
  end;
  if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
  begin
    { Class method: spill Self from the first int arg register into its slot.
      A `static` method has NO implicit Self — its first user parameter is the
      first integer arg (%rdi), so no Self spill and IntIdx stays put. }
    Self.Emit(Format(#9'movq %s, %s',
      [SysVArg64(IntIdx), Self.VarOperand('Self')]));
    Inc(IntIdx);
  end;
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray then
    begin
      { Open array: two consecutive integer registers — data ptr then high index. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName + '_high')]));
        Inc(IntIdx);
      end;
    end
    else if IsFloatFamily(P.ResolvedType) and not P.IsVarParam then
    begin
      { SSE arg registers xmm0..7; a float beyond the 8th arrives on the stack
        (its frame slot is already the +StackOff location, so no spill). }
      if XmmIdx < 8 then
      begin
        if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %s, %s',
            [SysVXmmArgRegs[XmmIdx], Self.VarOperand(P.ParamName)]))
        else
          Self.Emit(Format(#9'movsd %s, %s',
            [SysVXmmArgRegs[XmmIdx], Self.VarOperand(P.ParamName)]));
        Inc(XmmIdx);
      end;
    end
    else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) and
            not P.IsVarParam then
    begin
      { Interface param: spill obj register into the 16-byte slot base,
        itab register into base+8.  IntfItabOperand computes Off+8 from the
        frame entry, which lands correctly because AddSlot reserved 16 bytes.
        A var/out interface param arrives as ONE pointer (the caller's fat
        pointer address) and is spilled by the IsVarParam branch below. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.IntfItabOperand(P.ParamName, False)]));
        Inc(IntIdx);
      end;
    end
    else if P.IsVarParam then
    begin
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
    end
    else if (P.ResolvedType <> nil) and
            ((P.ResolvedType.Kind in [tyRecord, tyStaticArray]) or
             IsJumboSet(P.ResolvedType)) then
    begin
      { Phase 1: spill only the incoming pointer.  The local copy is made
        AFTER every register is spilled — memcpy clobbers the caller-saved
        argument registers, so copying here would corrupt any parameter
        that follows this one. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
    end
    else
    begin
      if IntIdx < 6 then
      begin
        Self.EmitSpillArg(IntIdx, Self.VarOperand(P.ParamName), P.ResolvedType);
        Inc(IntIdx);
      end;
    end;
  end;
  { Phase 2: copy record / static-array value params into their local _data
    blocks (Pascal value semantics) now that all registers are spilled, then
    repoint the param slot at the copy. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray or P.IsVarParam then Continue;
    if (P.ResolvedType = nil) or
       not ((P.ResolvedType.Kind in [tyRecord, tyStaticArray]) or
            IsJumboSet(P.ResolvedType)) then Continue;
    Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(P.ParamName)]));
    Self.Emit(Format(#9'leaq %s, %%rdi',
      [Self.VarOperand(P.ParamName + '_data')]));
    Self.Emit(Format(#9'movq $%d, %%rdx', [P.ResolvedType.RawSize()]));
    Self.Emit(#9'callq memcpy');
    Self.Emit(Format(#9'leaq %s, %%rax',
      [Self.VarOperand(P.ParamName + '_data')]));
    Self.Emit(Format(#9'movq %%rax, %s',
      [Self.VarOperand(P.ParamName)]));
  end;
  { Phase 2b: method-pointer / closure value params arrive as a POINTER to the
    caller's 16-byte (Code, Data) fat value (one register slot); replace the
    pointer with a 16-byte copy IN the slot so call-through, re-assignment and
    onward passing all see a real fat value.  Before this the caller passed
    only the CODE half and a capturing closure argument read a garbage env. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray or P.IsVarParam then Continue;
    if not IsMethodPtrType(P.ResolvedType) then Continue;
    Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(P.ParamName)]));
    Self.Emit(Format(#9'leaq %s, %%rdx', [Self.VarOperand(P.ParamName)]));
    Self.Emit(#9'movq (%rsi), %rax');
    Self.Emit(#9'movq 8(%rsi), %rcx');
    Self.Emit(#9'movq %rax, (%rdx)');
    Self.Emit(#9'movq %rcx, 8(%rdx)');
  end;
  { Initialise Result to 0 (defined default), like the QBE backend.
    For sret functions Result IS the caller's buffer (already zeroed by caller). }
  if (ADecl.ResolvedReturnType <> nil) and not FSretFunc then
  begin
    if IsFloatFamily(ADecl.ResolvedReturnType) then
    begin
      { Zero %xmm0 by xorpd/xorps. }
      if ADecl.ResolvedReturnType.Kind = tySingle then
        Self.Emit(#9'xorps %xmm0, %xmm0')
      else
        Self.Emit(#9'xorpd %xmm0, %xmm0');
      Self.EmitStoreFloat(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
    end
    else if IsMethodPtrType(ADecl.ResolvedReturnType) then
    begin
      { Method-ptr Result is a 16-byte [Code; Data] slot — zero BOTH halves so
        the Data (Self) half is defined even if the body never assigns it. }
      Self.Emit(#9'xorl %eax, %eax');
      Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand('Result')]));
      Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand('Result')]));
      Self.Emit(#9'movq %rax, 8(%rcx)');
    end
    else
    begin
      Self.Emit(#9'xorl %eax, %eax');
      Self.EmitStoreVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
    end;
  end;
  { Zero-initialise ALL local variable slots — Blaise guarantees zero
    initialisation of every variable as a language semantic.  The case
    branches mirror EmitVarAllocs in the QBE backend so both backends
    behave identically.  The else clause deliberately raises an error so
    that any new TTypeKind added in the future is caught here immediately. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType = nil then Continue;
      case TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind of

        tyInteger, tyUInt32, tySmallInt, tyWord, tyBoolean, tyByte, tyEnum:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            Self.Emit(Format(#9'movl $0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyInt64, tyUInt64,
        tyString,
        tyClass,
        tyPointer, tyPChar, tyMetaClass,
        tyDynArray:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            Self.Emit(Format(#9'movq $0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyInterface:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(Format(#9'movq $0, %s',
              [Self.IntfObjOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
            Self.Emit(Format(#9'movq $0, %s',
              [Self.IntfItabOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
          end;

        tyDouble:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(#9'xorpd %xmm0, %xmm0');
            Self.Emit(Format(#9'movsd %%xmm0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          end;

        tySingle:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(#9'xorps %xmm0, %xmm0');
            Self.Emit(Format(#9'movss %%xmm0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          end;

        tySet:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            if IsJumboSet(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType) then
            begin
              { Jumbo set: zero the whole inline bitmap via memset. }
              Self.Emit(Format(#9'leaq %s, %%rdi',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
              Self.Emit(#9'xorl %esi, %esi');
              Self.Emit(Format(#9'movl $%d, %%edx',
                [TSetTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).RawSize()]));
              Self.Emit(#9'callq memset');
            end
            else if TSetTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).BitCount <= 32 then
              Self.Emit(Format(#9'movl $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]))
            else
              Self.Emit(Format(#9'movq $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyProcedural:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            if TProceduralTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).IsMethodPtr or
               TProceduralTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).IsReference then
            begin
              { Method pointer / closure: two consecutive 8-byte slots
                (Code + Data/Env).
                VarOperand gives Code at the base; Data is 8 bytes above it. }
              Self.Emit(Format(#9'movq $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
              FFrame.TryGetValue(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], SlotOff);
              Self.Emit(Format(#9'movq $0, %d(%%rbp)', [SlotOff + 8]));
            end
            else
              Self.Emit(Format(#9'movq $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyRecord:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(Format(#9'leaq %s, %%rdi',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
            Self.Emit(#9'xorl %esi, %esi');
            Self.Emit(Format(#9'movq $%d, %%rdx',
              [TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.RawSize()]));
            Self.Emit(#9'callq memset');
          end;

        tyStaticArray:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(Format(#9'leaq %s, %%rdi',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
            Self.Emit(#9'xorl %esi, %esi');
            Self.Emit(Format(#9'movq $%d, %%rdx',
              [TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.RawSize()]));
            Self.Emit(#9'callq memset');
          end;

        { Open-array locals are never declared — they are caller-owned
          pointer+high pairs passed as parameters only. }
        tyOpenArray: ;

        { tyVoid and tyNil cannot appear as the type of a declared variable;
          any hit here indicates a semantic-pass bug. }
      else
        raise ENativeCodeGenError.Create(Format(
          'native zero-init: unhandled type kind %d for local ''%s''',
          [Ord(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind),
           TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[0]]));
      end;
    end;
  { ARC: retain string/class/interface value params on entry — balances the
    release pass at the epilogue.  Skip var, out, open-array and const
    params.  Const params (including const strings) are protected
    CALLER-side by shape — see EmitArgHoist and the QBE backend's
    ConstArgMode; both backends share this convention, which also keeps
    calls into the QBE-compiled RTL consistent. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsVarParam or P.IsOpenArray or P.IsConstParam then Continue;
    if P.ResolvedType = nil then Continue;
    if P.ResolvedType.Kind = tyString then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _StringAddRef');
    end
    else if P.ResolvedType.Kind = tyClass then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _ClassAddRef');
    end
    else if P.ResolvedType.Kind = tyInterface then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.IntfObjOperand(P.ParamName, False)]));
      Self.Emit(#9'callq _ClassAddRef');
    end
    else if P.ResolvedType.Kind = tyDynArray then
    begin
      { A dyn-array is a ref-counted buffer pointer: the callee's by-value
        copy is co-owning and must be counted, or the caller dropping its
        reference mid-call frees the buffer under the callee
        (BUG-20260721-byval-dynarray-param-no-arc). }
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _DynArrayAddRef');
    end
    else if P.ResolvedType.Kind = tyRecord then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(P.ParamName)]));
      Self.EmitRecordFieldRetains(TRecordTypeDesc(P.ResolvedType), '%rbx');
      Self.Emit(#9'popq %rbx');
    end;
  end;
  { Body.  FExitLabel directs Exit statements to the epilogue. }
  { Phase-2 anonymous-method capture: allocate/receive the env record and
    fill the '_cap_' pointer slots before any user statement runs. }
  if ADecl.EnvCaptured <> nil then
    Self.EmitEnvPrologue(ADecl);
  { Phase-4 block envs: zero the tracking slots (the declaring statement
    allocates into them per execution). }
  if ADecl.BlockEnvTypes <> nil then
    for I := 0 to ADecl.BlockEnvTypes.Count - 1 do
      Self.Emit(Format(#9'movq $0, %s',
        [Self.VarOperand('__envp_b' + IntToStr(I))]));
  FExitLabel := Self.NewLabel('exit');
  if ADecl.Body <> nil then
    Self.EmitStmtList(ADecl.Body.Stmts);
  { Epilogue: Exit lands here.  The Result is loaded into %rax/%xmm0 only AFTER
    the ARC release passes below — those call _ClassRelease/_StringRelease, which
    clobber %rax (and may touch the XMM regs), so loading Result first would
    return garbage from a value-returning function that also releases ARC
    params/locals.  For sret functions the caller's buffer already holds the
    result, so no load is needed. }
  Self.Emit(FExitLabel + ':');
  { Anonymous-method env: the enclosing frame drops its strong reference on
    exit; the env lives on iff an escaped closure still references it.  A
    thunk BORROWS its env from the closure fat value — no release. }
  if (ADecl.EnvCaptured <> nil) and (not ADecl.IsAnonThunk) then
  begin
    Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('__envp')]));
    Self.Emit(#9'callq _ClassRelease');
  end;
  if ADecl.BlockEnvTypes <> nil then
    for I := 0 to ADecl.BlockEnvTypes.Count - 1 do
    begin
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.VarOperand('__envp_b' + IntToStr(I))]));
      Self.Emit(#9'callq _ClassRelease');
    end;
  { Release ARC-managed locals (not params, not Result).
    Result is returned to the caller who owns it.

    Addressing is VarOperand (frame offsets); the sibling EmitGlobalReleases
    walk does the same job for program-level globals via <Name>(%rip).  Both
    dispatch on the shared ArcScopeExitReleaseKind classifier so they cannot
    drift apart on which type kinds they cover. }
  if ADecl.Body <> nil then
  begin
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(ADecl.Body.Decls.Items[I]);
      if VD.ResolvedType = nil then Continue;
      AKind := ArcScopeExitReleaseKind(VD.ResolvedType);
      case AKind of
        { String locals: release the string. }
        arkString:
          for J := 0 to VD.Names.Count - 1 do
          begin
            Self.Emit(Format(#9'movq %s, %%rdi',
              [Self.VarOperand(VD.Names.Strings[J])]));
            Self.Emit(#9'callq _StringRelease');
          end;
        { Class locals: release the object reference. }
        arkClass:
          for J := 0 to VD.Names.Count - 1 do
          begin
            if VD.IsWeak then
            begin
              Self.Emit(Format(#9'leaq %s, %%rdi',
                [Self.VarOperand(VD.Names.Strings[J])]));
              Self.Emit(#9'callq _WeakClear');
            end
            else
            begin
              Self.Emit(Format(#9'movq %s, %%rdi',
                [Self.VarOperand(VD.Names.Strings[J])]));
              Self.Emit(#9'callq _ClassRelease');
            end;
          end;
        { Interface locals: release the obj half of the fat pointer; the itab
          is static rodata and is not refcounted. }
        arkIntf:
          for J := 0 to VD.Names.Count - 1 do
          begin
            if VD.IsWeak then
            begin
              Self.Emit(Format(#9'leaq %s, %%rdi',
                [Self.IntfObjOperand(VD.Names.Strings[J], False)]));
              Self.Emit(#9'callq _WeakClear');
            end
            else
            begin
              Self.Emit(Format(#9'movq %s, %%rdi',
                [Self.IntfObjOperand(VD.Names.Strings[J], False)]));
              Self.Emit(#9'callq _ClassRelease');
            end;
          end;
        { Dyn-array locals: release the data buffer; balances the
          first-assignment retain (a dyn-array var assignment retains the new
          buffer). }
        arkDynArray:
          for J := 0 to VD.Names.Count - 1 do
          begin
            Self.Emit(Format(#9'movq %s, %%rdi',
              [Self.VarOperand(VD.Names.Strings[J])]));
            Self.Emit(#9'callq _DynArrayRelease');
          end;
        { 'reference to' locals: the Data half strong-references an ARC env
          record (nil for capture-free closures — release is a nil-safe
          no-op). }
        arkRefEnv:
          for J := 0 to VD.Names.Count - 1 do
          begin
            Self.Emit(Format(#9'leaq %s, %%rcx',
              [Self.VarOperand(VD.Names.Strings[J])]));
            Self.Emit(#9'movq 8(%rcx), %rdi');
            Self.Emit(#9'callq _ClassRelease');
          end;
        { Record locals with managed fields: release each ARC-managed field at
          scope exit.  The record block lives in the frame; its address goes
          into %rbx (callee-saved) so it survives the per-field release calls.

          Static-array-of-managed locals (class, string, interface, dyn-array,
          or record with managed content): release each element at scope exit
          (BUG-016 stage 2 — previously interface elements only).  The inline
          storage base goes into %rbx (callee-saved).

          Safe against manual element lifetimes (e.g. the ELF writer's
          `RelaBuf: array[0..MaxSecOrder] of TByteBuf`, MaxSecOrder = 6):
          A[I].Free() nils the element slot, making this walk a no-op on
          manually-freed elements, and the element store's retain is
          conditional on RHS ownership (stage 1), so each live slot holds
          exactly one reference for this walk to balance. }
        arkAggregate:
          for J := 0 to VD.Names.Count - 1 do
          begin
            Self.Emit(#9'pushq %rbx');
            Self.Emit(Format(#9'leaq %s, %%rbx',
              [Self.VarOperand(VD.Names.Strings[J])]));
            if VD.ResolvedType.Kind = tyRecord then
              Self.EmitRecordFieldReleases(
                TRecordTypeDesc(VD.ResolvedType), '%rbx')
            else
              Self.EmitStaticArrayReleaseElems(
                TStaticArrayTypeDesc(VD.ResolvedType), '%rbx', False);
            Self.Emit(#9'popq %rbx');
          end;
      end;
    end;
  end;
  { ARC: release string/class/interface value params on exit — matches the
    entry retain pass.  Skip var, out, open-array and const params (const
    params are caller-protected; see the entry pass comment). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsVarParam or P.IsOpenArray or P.IsConstParam then Continue;
    if P.ResolvedType = nil then Continue;
    if P.ResolvedType.Kind = tyString then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _StringRelease');
    end
    else if P.ResolvedType.Kind = tyClass then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _ClassRelease');
    end
    else if P.ResolvedType.Kind = tyInterface then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.IntfObjOperand(P.ParamName, False)]));
      Self.Emit(#9'callq _ClassRelease');
    end
    else if P.ResolvedType.Kind = tyDynArray then
    begin
      { Balances the entry retain
        (BUG-20260721-byval-dynarray-param-no-arc). }
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _DynArrayRelease');
    end
    else if P.ResolvedType.Kind = tyRecord then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(P.ParamName)]));
      Self.EmitRecordFieldReleases(TRecordTypeDesc(P.ResolvedType), '%rbx');
      Self.Emit(#9'popq %rbx');
    end;
  end;
  { Now that every ARC release call is done (none can clobber the result), load
    Result into %rax (int) or %xmm0 (float).  sret functions return via the
    caller's buffer and need no load.  Reg-return records load into
    rax/rdx/xmm0/xmm1 per the SysV classification. }
  if (ADecl.ResolvedReturnType <> nil) and not FSretFunc then
  begin
    if (ADecl.ResolvedReturnType.Kind = tyRecord) and (FRecRetClass <> rcSret) then
      Self.EmitRecordReturnEpilogue(
        TRecordTypeDesc(ADecl.ResolvedReturnType), FRecRetClass)
    else if IsMethodPtrType(ADecl.ResolvedReturnType) and (FRecRetClass <> rcSret) then
      { Method-ptr return: load both halves of the 16-byte Result slot into the
        return registers (rax:rdx for rcInt2) via the canonical record. }
      Self.EmitRecordReturnEpilogue(MethodPtrReturnRec(), FRecRetClass)
    else if IsFloatFamily(ADecl.ResolvedReturnType) then
      Self.EmitLoadFloat(Self.VarOperand('Result'), ADecl.ResolvedReturnType)
    else
      Self.EmitLoadVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
  end;
  { Restore the promoted registers' incumbents (saved in the prologue)
    before the frame teardown. }
  if FPromoActive then
  begin
    for I := 0 to 3 do
      if FPromoVars[I] <> '' then
        Self.Emit(Format(#9'movq %s, %s',
          [Self.VarOperand('_promo_save_' + IntToStr(I)), PROMO_REGS[I]]));
    if FPromoPinOk then
      Self.Emit(Format(#9'movq %s, %%r13', [Self.VarOperand('_promo_save_pin')]));
  end;
  if FTryR15Save then
    Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('_try_r15_save')]));
  Self.Emit(#9'movq %rbp, %rsp');
    Self.Emit(#9'popq %rbp');
    Self.Emit(#9'ret');
  finally
    FAsm := SavedAsm;
  end;
  if FFrameSize > 0 then
    Self.Emit(Format(#9'subq $%d, %%rsp', [FFrameSize]));
  FAsm.Append(BodyBuf.ToString());
  BodyBuf.Free();
  Self.DbgEndFunc();
  Self.Emit('.type ' + Sym + ', @function');

  FExitLabel := '';
end;

{ Emit the program entry function.

  The Blaise runtime expects an exported `main(argc, argv)` returning int.  It
  must call $_SetArgs(argc, argv) before any program code, then run the body,
  then return 0.  This mirrors the QBE backend's $main shape (see the QBE IR
  for an empty program).

  The body statements are lowered between the _SetArgs call and the return-0
  epilogue.  After `pushq %rbp` the stack is 16-byte aligned, and expression
  evaluation balances its push/pop pairs, so %rsp stays aligned at every call
  site. }
procedure TX86_64Backend.EmitProgram(AProg: TProgram);
var
  I, J:  Integer;
  VD:    TVarDecl;
  Decl:  TMethodDecl;
begin
  if FSymTable <> nil then FSymTable.InCodegen := True;
  FCurrentUnitName := AProg.Name;
  FDbgSrcFile := '';
  FProgramName := AProg.Name;
  { Register declared program-level variables as global slots. }
  for I := 0 to AProg.Block.Decls.Count - 1 do
  begin
    VD := TVarDecl(AProg.Block.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) or IsFloatFamily(VD.ResolvedType) or
       ((VD.ResolvedType <> nil) and
        (VD.ResolvedType.Kind in [tyRecord, tyStaticArray, tyClass,
                                  tyProcedural, tyPointer, tyString, tyPChar,
                                  tyDynArray, tySet])) then
      for J := 0 to VD.Names.Count - 1 do
      begin
        { Record as a module var FIRST so AddGlobal's GlobalSymName applies the
          owning-unit prefix (this loop runs with FCurrentUnitName = the owner). }
        FModuleVarNames.Add(VD.Names.Strings[J]);
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
        if VD.IsThreadVar then
          Self.MarkThreadVar(VD.Names.Strings[J]);
        if VD.IsWeak then
          Self.MarkWeakGlobal(VD.Names.Strings[J]);
        if VD.InitConst <> nil then
          FGlobalInits.Add(Self.GlobalSymName(VD.Names.Strings[J]), VD.InitConst);
      end;
  end;

  { Class method bodies before standalone procedures. }
  Self.EmitClassMethods(AProg.Block.TypeDecls, AProg.GenericInstances,
                        AProg.GenericRecordInstances, AProg.GenericMethodInstances);

  { Array-typed constants — emit data sections so const arrays are defined
    as assembly labels before being referenced in code.  Covers block-level
    consts and local consts inside procedure bodies. }
  Self.EmitArrayConstData(AProg.Block, '');

  { Standalone procedures/functions, then $main. }
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls.Items[I]);
    if Decl.OwnerTypeName <> '' then Continue;     { class methods: above }
    if Decl.TypeParams <> nil then Continue;       { generic templates: skip }
    if Decl.Body = nil then Continue;              { forward decls }
    if Decl.IsExternal then Continue;              { external: later }
    Self.EmitFunctionDef(Decl, True);
  end;

  { Concrete generic function instances. }
  for I := 0 to AProg.GenericFuncInstances.Count - 1 do
    Self.EmitFunctionDef(
      TGenericFuncInstance(AProg.GenericFuncInstances.Items[I]).MethodDecl, True);

  { Pre-count try stmts in the program body so VarOperand resolves
    _exc_frame_N as globals (FFrame is nil in main, so the global path is
    taken).  The actual .bss labels are emitted in EmitDataSection. }
  FProgExcFrameCount := 0;
  for I := 0 to AProg.Block.Stmts.Count - 1 do
    FProgExcFrameCount := FProgExcFrameCount +
      Self.CountTryStmts(TASTStmt(AProg.Block.Stmts.Items[I]));
  { Jumbo-set scratch in main: main has no stack frame, so set literal / set-op
    result buffers live in static .bss.  A jumbo set value can appear in any
    expression in the program body (e.g. 'X in [members]' over a >64 enum), so
    always reserve the two scratch buffers. }
  FProgHasJumboSet := True;
  { Reset per-function state before emitting the program body. }
  FExcDepth     := 0;
  FExcFrameNext := 0;
  FForEndNext   := 0;
  FFinallyStack.Free();
  FFinallyStack := TList<TCompoundStmt>.Create();
  { Program-level vars are globals (always pinned as const args), so the
    blocklist only needs to be free of stale entries from the last function. }
  FConstArgUnsafe.Clear();

  Self.Emit('.text');
  Self.Emit('.globl main');
  Self.DbgBeginFunc('main');
  Self.Emit('main:');
  { Prologue: establish a frame.  argc is in %edi, argv in %rsi per SysV. }
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  { _SetArgs(argc, argv): args already in %edi/%rsi — pass through.  Must
    precede _BlaiseInit, which clobbers the SysV arg registers. }
  Self.Emit(#9'callq _SetArgs');
  { RTL one-time setup the per-unit init dispatch below misses for archive
    units (e.g. blaise_weak's WeakMutex — see _BlaiseInit). }
  Self.Emit(#9'callq _BlaiseInit');
  { Assign GPlatformLayout for the compile-time --target by calling the host
    layout unit's init BY NAME (rtl.platform.layout.<os>_init).  The layout unit
    is linked by the driver (BuildRTLUnitList) but not imported by posix, so it
    is not in the per-unit init dispatch below; calling it here — first, before
    any other unit init — makes the target's layout win deterministically even
    if a unit (e.g. a test) imported a non-host layout whose init also runs. }
  Self.Emit(#9'callq ' + PlatformLayoutInitSym(FTarget));
  { Call initialization sections of imported units in order. }
  for I := 0 to FUnitInitNames.Count - 1 do
    Self.Emit(#9'callq ' + FUnitInitNames.Strings[I] + '_init');
  if FDebugMode then
    Self.Emit(#9'callq _LeakTrackerEnable');
  { Program body. }
  FExitLabel := Self.NewLabel('main_exit');
  Self.EmitStmtList(AProg.Block.Stmts);
  { Epilogue: Exit lands here; release ARC-managed globals, then return 0.
    Mirrors the QBE backend, which releases each managed global at @main_exit so
    a global object's _FieldCleanup (and hence its destructor) runs at program
    end. }
  Self.Emit(FExitLabel + ':');
  FExitLabel := '';
  { Per-unit teardown first, in REVERSE init order (last initialised, first
    finalised): each <Unit>_fini runs that unit's user finalization section
    and releases its managed globals — including implementation-section
    privates this translation unit cannot even name.  Then the program's own
    globals are released (a program global may hold a back-reference into a
    unit global's object graph, so the program-owned references go last). }
  for I := FUnitFiniNames.Count - 1 downto 0 do
    Self.Emit(#9'callq ' + FUnitFiniNames.Strings[I] + '_fini');
  Self.EmitGlobalReleases();
  Self.Emit(#9'movl $0, %eax');
  Self.Emit(#9'leave');
  Self.Emit(#9'ret');
  Self.DbgEndFunc();
  Self.Emit('.type main, @function');
  { Mark the stack non-executable (matches QBE output). }
  Self.Emit('.section .note.GNU-stack,"",@progbits');

  { Data section: all registered global integer/float/record slots. }
  Self.EmitDataSection();
  { Class data section: typeinfo, vtables, field-cleanup functions. }
  Self.EmitClassSection(AProg.Block.TypeDecls, AProg.GenericInstances,
                        AProg.SymbolTable);
  { Anonymous-method environment cleanup functions (Phase 2). }
  Self.EmitEnvCleanupDefs(AProg.Block);
  Self.EmitEnvCleanupDefsForInstances(AProg.GenericInstances,
                                      AProg.GenericRecordInstances);
  { Interface data: typeinfo tokens, itabs, impllists.  Emitted after the class
    section so the class-name strings and method symbols it references exist. }
  Self.Emit('.data');
  Self.EmitInterfaceDefs(AProg.Block.TypeDecls, AProg.GenericInstances,
                         AProg.GenericIntfInstances, AProg.SymbolTable);
end;

{ ------------------------------------------------------------------ }
{ Whole-program multi-unit: emit one dependency unit                   }
{ ------------------------------------------------------------------ }

procedure TX86_64Backend.EmitUnit(AUnit: TUnit);
var
  I, J:      Integer;
  ImplDecl:  TMethodDecl;
  VD:        TVarDecl;
  UnitSym:   TSymbolTable;
  IntfNames: TStringList;
  EmptyGen:  TObjectList;   { empty generic-instance list for the ImplBlock
                             second-pass calls (generics are per-unit and were
                             emitted once with the IntfBlock pass — never
                             duplicate them). }
  SavedDOU:  string;        { prior FSymTable.DefineOwningUnit, restored at end }
begin
  FCurrentUnitName := AUnit.Name;
  FDbgSrcFile := AUnit.SourceFile;
  { Establish THIS unit as the symbol-table viewing context so that resolving
    the unit's own implementation-section (IsImplPrivate) types — for
    ClassSymName mangling and EmitClassSection's FindType — is not suppressed
    by the cross-unit-leak guard in TSymbolTable.Lookup.  Restored at end. }
  SavedDOU := '';
  if FSymTable <> nil then
  begin
    SavedDOU := FSymTable.DefineOwningUnit;
    FSymTable.DefineOwningUnit := AUnit.Name;
  end;
  { Register the unit's global variables (interface + implementation sections)
    as data slots, mirroring EmitProgram's program-global registration. }
  for I := 0 to AUnit.IntfBlock.Decls.Count - 1 do
  begin
    VD := TVarDecl(AUnit.IntfBlock.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) or IsFloatFamily(VD.ResolvedType) or
       ((VD.ResolvedType <> nil) and
        (VD.ResolvedType.Kind in [tyRecord, tyStaticArray, tyClass,
                                  tyProcedural, tyPointer, tyString, tyPChar,
                                  tyDynArray, tyInterface, tySet])) then
      for J := 0 to VD.Names.Count - 1 do
      begin
        { Record as a module var FIRST so AddGlobal's GlobalSymName applies the
          owning-unit prefix (this loop runs with FCurrentUnitName = the owner). }
        FModuleVarNames.Add(VD.Names.Strings[J]);
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
        if VD.IsThreadVar then
          Self.MarkThreadVar(VD.Names.Strings[J]);
        { Mirror EmitProgram's weak registration so the <Unit>_fini walk
          clears a [Weak] slot instead of strong-releasing it. }
        if VD.IsWeak then
          Self.MarkWeakGlobal(VD.Names.Strings[J]);
        if VD.InitConst <> nil then
          FGlobalInits.Add(Self.GlobalSymName(VD.Names.Strings[J]), VD.InitConst);
      end;
  end;
  for I := 0 to AUnit.ImplBlock.Decls.Count - 1 do
  begin
    VD := TVarDecl(AUnit.ImplBlock.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) or IsFloatFamily(VD.ResolvedType) or
       ((VD.ResolvedType <> nil) and
        (VD.ResolvedType.Kind in [tyRecord, tyStaticArray, tyClass,
                                  tyProcedural, tyPointer, tyString, tyPChar,
                                  tyDynArray, tyInterface, tySet])) then
      for J := 0 to VD.Names.Count - 1 do
      begin
        { Record as a module var FIRST so AddGlobal's GlobalSymName applies the
          owning-unit prefix (this loop runs with FCurrentUnitName = the owner). }
        FModuleVarNames.Add(VD.Names.Strings[J]);
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
        if VD.IsThreadVar then
          Self.MarkThreadVar(VD.Names.Strings[J]);
        { Mirror EmitProgram's weak registration so the <Unit>_fini walk
          clears a [Weak] slot instead of strong-releasing it. }
        if VD.IsWeak then
          Self.MarkWeakGlobal(VD.Names.Strings[J]);
        if VD.InitConst <> nil then
          FGlobalInits.Add(Self.GlobalSymName(VD.Names.Strings[J]), VD.InitConst);
      end;
  end;

  EmptyGen := TObjectList.Create(False);   { not owned — borrowed slots only }

  { Class / record method bodies declared in the interface block, plus any
    generic class/record instances declared in this unit.  After
    LinkClassMethodImpls the definition's TMethodDecl nodes hold the bodies. }
  Self.EmitClassMethods(AUnit.IntfBlock.TypeDecls, AUnit.GenericInstances,
                        AUnit.GenericRecordInstances, AUnit.GenericMethodInstances);
  { Classes/records declared in the IMPLEMENTATION section: their method bodies
    are emitted too (generics already covered by the IntfBlock pass above, so
    pass empty generic lists to avoid re-emitting them). }
  Self.EmitClassMethods(AUnit.ImplBlock.TypeDecls, EmptyGen, EmptyGen, EmptyGen);

  { Array-typed constants from both interface and implementation blocks. }
  Self.EmitArrayConstData(AUnit.IntfBlock, '');
  Self.EmitArrayConstData(AUnit.ImplBlock, '');

  { Standalone procedures/functions from the implementation block.  Skip class
    method stubs (OwnerTypeName <> '': their bodies were transferred to the
    class definition and emitted above), generic templates, forward decls, and
    externals.  In monolithic mode, only interface-exported functions need
    .globl — implementation-only helpers stay local to avoid collisions with
    the same symbols in the RTL archive. }
  IntfNames := TStringList.Create();
  try
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]).Name);
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if ImplDecl.OwnerTypeName <> '' then Continue;
      if ImplDecl.TypeParams <> nil then Continue;
      if ImplDecl.Body = nil then Continue;
      if ImplDecl.IsExternal then Continue;
      Self.EmitFunctionDef(ImplDecl, IntfNames.IndexOf(ImplDecl.Name) >= 0);
    end;
  finally
    IntfNames.Free();
  end;

  { Concrete generic function instances declared in this unit. }
  for I := 0 to AUnit.GenericFuncInstances.Count - 1 do
    Self.EmitFunctionDef(
      TGenericFuncInstance(AUnit.GenericFuncInstances.Items[I]).MethodDecl, True);

  { Initialization section: emit as a function <Unit>_init that the program's
    $main calls before the program body.  (Finalization is not yet wired into
    the native main footer; emitted but only init is invoked.) }
  if (AUnit.InitStmts <> nil) and (AUnit.InitStmts.Count > 0) then
  begin
    { Re-assert THIS unit as the viewing context.  Earlier emit passes in this
      procedure (method-body type resolution that walks the uses chain) can
      leave DefineOwningUnit pointing at a dependency unit; if the init block
      references one of THIS unit's own implementation-section (IsImplPrivate)
      classes — e.g. a metaclass value passed to a registrar — TSymbolTable.Lookup
      would otherwise suppress it as a cross-unit leak and ClassSymName would fall
      back to a bare, unqualified, undefined typeinfo symbol (silent link-time
      garbage).  See the impl-section-class visibility guard in
      TSymbolTable.Lookup. }
    if FSymTable <> nil then
      FSymTable.DefineOwningUnit := AUnit.Name;
    FUnitInitNames.Add(NativeMangle(AUnit.Name));
    { A unit's initialization block is emitted frame-less, exactly like the
      program-main body, so a jumbo-set literal or set-op inside it resolves
      _jset_scratch_0/1 through the global path.  Reserve the .bss buffers in
      THIS object too — without them the init code referenced scratch symbols
      that only the program object defined, and the link failed with an
      undefined reference to `_jset_scratch_1'. }
    FProgHasJumboSet := True;
    Self.ClearFrame();
    FExitLabel := '';
    FExcDepth     := 0;
    FExcFrameNext := 0;
    FForEndNext   := 0;
    FFinallyStack.Free();
  FFinallyStack := TList<TCompoundStmt>.Create();
    Self.Emit('.text');
    Self.Emit('.globl ' + NativeMangle(AUnit.Name) + '_init');
    Self.Emit(NativeMangle(AUnit.Name) + '_init:');
    Self.Emit(#9'pushq %rbp');
    Self.Emit(#9'movq %rsp, %rbp');
    Self.EmitStmtList(AUnit.InitStmts);
    Self.Emit(#9'movl $0, %eax');
    Self.Emit(#9'leave');
    Self.Emit(#9'ret');
    Self.Emit('.type ' + NativeMangle(AUnit.Name) + '_init, @function');
  end;

  { Per-unit teardown: emit <Unit>_fini when the shared UnitNeedsFini
    predicate holds (user finalization section and/or managed module
    globals).  The program's $main calls every registered fini at main_exit
    in REVERSE init order, BEFORE its own EmitGlobalReleases.  The fini
    lives in the unit's OWN translation unit so implementation-section
    private globals — unreachable from the program object — are released
    too.  Order inside the fini: user finalization code FIRST (it may still
    read the globals), then the ARC release walk. }
  if UnitNeedsFini(AUnit) then
  begin
    { Re-assert the viewing context (see the init-block note above):
      GlobalSymName and any finalization-body symbol resolution must see
      THIS unit's own impl-section symbols. }
    if FSymTable <> nil then
      FSymTable.DefineOwningUnit := AUnit.Name;
    FUnitFiniNames.Add(NativeMangle(AUnit.Name));
    FProgHasJumboSet := True;
    Self.ClearFrame();
    FExitLabel := '';
    FExcDepth := 0;
    FExcFrameNext := 0;
    FForEndNext := 0;
    FFinallyStack.Free();
    FFinallyStack := TList<TCompoundStmt>.Create();
    Self.Emit('.text');
    { An RTL (unmangled) unit's <Unit>_fini must be WEAK: the RTL Makefile
      builds each RTL object whole-program-per-unit, so a dependency RTL
      unit (e.g. rtl.platform, imported by both rtl.platform.posix and
      rtl.platform.layout.linux) has its fini inlined into every importing
      object.  A strong .globl then multiply-defines <Unit>_fini across
      archive members and an end-user link fails (GH #191) — exactly the
      RTL-function weak treatment of GH #180, which this site missed. }
    if IsUnmangledUnit(AUnit.Name) then
      Self.Emit('.weak ' + NativeMangle(AUnit.Name) + '_fini')
    else
      Self.Emit('.globl ' + NativeMangle(AUnit.Name) + '_fini');
    Self.Emit(NativeMangle(AUnit.Name) + '_fini:');
    Self.Emit(#9'pushq %rbp');
    Self.Emit(#9'movq %rsp, %rbp');
    if (AUnit.FinalStmts <> nil) and (AUnit.FinalStmts.Count > 0) then
      Self.EmitStmtList(AUnit.FinalStmts);
    Self.EmitUnitGlobalReleases(AUnit.IntfBlock);
    Self.EmitUnitGlobalReleases(AUnit.ImplBlock);
    Self.Emit(#9'movl $0, %eax');
    Self.Emit(#9'leave');
    Self.Emit(#9'ret');
    Self.Emit('.type ' + NativeMangle(AUnit.Name) + '_fini, @function');
  end;

  { Class data section: typeinfo, vtables, field-cleanup functions for the
    unit's classes.  System defs (TObject/TCustomAttribute) emitted once. }
  { In the whole-program multi-unit model the unit is analysed as part of the
    program, so AUnit.SymbolTable is nil and its resolved types live in the
    program's (global) symbol table — supplied via SetSymbolTable before
    AppendUnit.  Prefer the unit's own table when it was analysed standalone. }
  if AUnit.SymbolTable <> nil then
    UnitSym := AUnit.SymbolTable
  else
    UnitSym := FSymTable;
  { Disable the analysis-time impl-private suppression in Lookup for the table
    EmitClassSection consults — at codegen the backend must resolve THIS unit's
    own implementation-section classes (see TSymbolTable.FInCodegen). }
  if UnitSym <> nil then UnitSym.InCodegen := True;
  { Re-assert the viewing context (see the init-block note above): the class
    section emits unit-qualified typeinfo/vtable/_FieldCleanup names via
    ClassSymName, which must resolve THIS unit's own impl-section classes. }
  if FSymTable <> nil then
    FSymTable.DefineOwningUnit := AUnit.Name;
  Self.EmitClassSection(AUnit.IntfBlock.TypeDecls, AUnit.GenericInstances,
                        UnitSym);
  { Impl-section classes' typeinfo / vtable / _FieldCleanup (generics already
    emitted above — empty list here). }
  Self.EmitClassSection(AUnit.ImplBlock.TypeDecls, EmptyGen, UnitSym);
  { Anonymous-method environment cleanup functions (Phase 2). }
  Self.EmitEnvCleanupDefs(AUnit.ImplBlock);
  { Interface-section classes carry their method bodies after
    LinkClassMethodImpls — emit their closures' env cleanups too. }
  Self.EmitEnvCleanupDefs(AUnit.IntfBlock);
  Self.EmitEnvCleanupDefsForInstances(AUnit.GenericInstances,
                                      AUnit.GenericRecordInstances);
  { Interface data: typeinfo tokens, itabs, impllists. }
  Self.Emit('.data');
  Self.EmitInterfaceDefs(AUnit.IntfBlock.TypeDecls, AUnit.GenericInstances,
                         AUnit.GenericIntfInstances, UnitSym);
  Self.EmitInterfaceDefs(AUnit.ImplBlock.TypeDecls, EmptyGen, EmptyGen, UnitSym);

  EmptyGen.Free();
  if FSymTable <> nil then
    FSymTable.DefineOwningUnit := SavedDOU;
end;

procedure TX86_64Backend.NoteDepInitUnit(const AUnitName: string;
  AHasInit: Boolean);
begin
  { Separate-compilation: the dep's body (and its <Unit>_init) is in its own
    object; record the mangled name so EmitProgram's $main calls it.  Mangling
    matches EmitUnit's FUnitInitNames.Add(NativeMangle(AUnit.Name)). }
  if AHasInit then
    FUnitInitNames.Add(NativeMangle(AUnitName));
  { Record the imported unit (raw name, matching TSymbol.OwningUnit) so
    EmitDataSection emits globals owned by it as references, not definitions —
    the cached object owns the definition. }
  FImportedUnits.Add(AUnitName);
end;

procedure TX86_64Backend.NoteDepFiniUnit(const AUnitName: string;
  AHasFini: Boolean);
begin
  { Separate-compilation: the dep's <Unit>_fini is in its own object; record
    the mangled name so EmitProgram's $main calls it at main_exit (in reverse
    registration order).  Mangling matches EmitUnit's
    FUnitFiniNames.Add(NativeMangle(AUnit.Name)). }
  if AHasFini then
    FUnitFiniNames.Add(NativeMangle(AUnitName));
end;

procedure TX86_64Backend.FinalizeEmit;
begin
  if FFinalized then Exit;
  FFinalized := True;
  Self.EmitDataSection();
end;

end.
