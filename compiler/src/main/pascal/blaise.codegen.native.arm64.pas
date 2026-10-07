{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.arm64;

{ AArch64 (Apple Silicon macOS) native backend — the second Template-Method
  leaf of TNativeBackend (macos-arm64 Phase 2,
  docs/macos-arm64-backend-design.adoc).

  Emits AArch64 GNU-syntax assembly text into the inherited FAsm buffer;
  blaise.assembler.arm64 encodes that text into a Mach-O MH_OBJECT.  All
  target-independent walks (the ARC field-kind walk, ClassifyRecordReturn)
  come from the base class; this leaf supplies only registers and mnemonics.

  DELIBERATELY INCREMENTAL: this backend currently lowers a well-defined
  subset (program entry, integer arithmetic/comparisons, integer and string
  locals/globals, WriteLn/Write, if/while).  Every unsupported construct
  raises ENativeCodeGenError with an 'arm64:' prefix naming the node — an
  honest hole, never silent wrong code.  The subset grows commit by commit
  against the Phase 2 checklist.

  Conventions in this leaf (AAPCS64 + Apple):
    x0-x7 / d0-d7   argument + result registers
    x8               sret pointer (indirect record result)
    x9-x15           scratch
    x16/x17          IP0/IP1 (linker veneers) — not used by codegen
    x18              RESERVED by Apple — never touched
    x19-x28          callee-saved (x19 = ARC base anchor, x20/x21 = the
                     ARC walk scratch pair — the %rbx/%r14/%r15 analogues)
    x29/x30          frame pointer / link register — the fp chain is ALWAYS
                     maintained (Darwin unwind requirement)
    sp               16-byte aligned at every call

  Frame model: `stp x29, x30, [sp, #-16]!` + `mov x29, sp` +
  `sub sp, sp, #FrameSize`.  Locals live at NEGATIVE x29 offsets and are
  addressed with ldur/stur (unscaled ±256) or a materialised address for
  larger frames.  Expression evaluation uses full-width stack brackets
  (`str x0, [sp, #-16]!` / `ldr x9, [sp], #16`) so sp stays 16-aligned. }

interface

uses
  SysUtils, Classes, contnrs, Generics.Collections, uAST, uSymbolTable,
  uStrCompat, blaise.codegen, blaise.codegen.native.backend, strutils,
  blaise.codegen.target;

const
  VIRT_NONE = -1;   { EmitCall: no virtual dispatch — direct bl }
  VIRT_INDIRECT = -2;  { EmitCall: call through the code word of the fat /
                         plain procedural value whose ADDRESS is parked in
                         the FIndirectSlot frame slot }
  { EmitCall: no caller-provided x8 sret buffer for this call. }
  SRET_NO_BUF = -1;
  { Statement-scoped deferred class-release frame slots (BUG-048 arm64 half —
    mirrors x86-64's PENDREL_SLOTS).  A retained class field read on an owned
    transient base defers the base release to the end of the enclosing leaf
    statement instead of AddRef-pinning the borrowed field value (which
    leaked one ref).  Overflow past this count falls back to the AddRef-pin
    (safe leak).  Unlike x86-64, arm64's _main has a real frame, so these are
    ordinary AddLocal slots in every frame — no .bss dual path. }
  PENDREL_SLOTS = 8;
  { Widest jumbo-set bitmap: a set is capped at 256 members = 32 bytes.  One
    frame slot of this size serves every jumbo-set operator in the frame. }
  JUMBO_SCRATCH_BYTES = 32;

  { Fixed x29-relative pool for parking owned-string-transient call args across
    a call (see ReservePendRelSlots).  A single call rarely passes more than a
    few owned string transients; overflow is a NotYet, not silent corruption. }
  STRTRANS_SLOTS = 8;

type
  TArm64Backend = class(TNativeBackend)
  private
    FFrame:       TDictionary<string, Integer>;  { local -> POSITIVE byte
                                                   distance below x29 }
    FFrameSize:   Integer;
    FGlobalNames: TStringList;                   { program-level int globals }
    FStrLits:     TStringList;
    FLabelN:      Integer;
    FProgramName: string;
    FIsFunction:  Boolean;       { current routine returns a value }
    FResultFloat: Boolean;       { ...and that value is a Double (d0) }
    FResultSingle: Boolean;      { ...or a Single (returned in s0) }
    FExitLabel:   string;        { current routine's epilogue label }
    FBreakLbls:   TStringList;   { innermost-last loop end labels }
    FContLbls:    TStringList;   { innermost-last loop continue labels }
    FForN:        Integer;       { hidden for-loop end-slot counter }
    FFloatLits:   TStringList;   { .rodata double-literal texts }
    FStrLocals:   TStringList;   { string locals of the current routine —
                                   released at the shared exit label }
    FCurrentUnitName: string;    { '' = program context; else the unit being emitted }
    FModuleVarNames: TStringList; { unit-level var names (both sections) — these
                                    take the owning-unit symbol prefix }
    FUnitInits:   TStringList;   { emitted <unit>_init symbols, called by _main }
    FUnitFinals:  TStringList;   { emitted <unit>_final symbols — called at
                                    program exit in REVERSE dependency order }
    FGlobalInits: TDictionary<string, string>;  { prefixed symbol -> .data
                                    directive for initialised globals }
    FGlobalStrInits: TStringList; { symbols of string-initialised globals }
    FGlobalStrVals:  TStringList; { parallel: the literal values }
    FClassDecls:  TObjectList;   { not owned — program-level class TTypeDecls }
    FRecordDecls: TObjectList;   { not owned — program-level record TTypeDecls
                                   that declare methods.  Records need no
                                   typeinfo or vtable, so unlike FClassDecls
                                   this list exists ONLY to emit method bodies:
                                   a record method is an ordinary function whose
                                   Self is the ADDRESS of the record. }
    FUnitEmittedClasses: TObjectList; { not owned — unit class TTypeDecls whose
                                   method bodies were ALREADY emitted by EmitUnit
                                   (in unit context).  EmitProgram's FClassDecls
                                   walk skips these to avoid a double-emit (a
                                   second copy would run in program context and
                                   mis-resolve impl-section unit globals + hit a
                                   duplicate label). }
    FGenericDecls: TObjectList;  { owned — synthetic TTypeDecl wrappers around
                                   TGenericInstance clones so instances flow
                                   through the ordinary class machinery }
    FObjLocals:   TStringList;   { class-typed locals — released at scope exit }
    FWeakLocals:  TStringList;   { [Weak] class/interface locals — the obj slot is
                                   deregistered (_WeakClear) at scope exit }
    FObjGlobals:  TStringList;   { class-typed globals — released at program exit }
    FTlvGlobals:  TStringList;   { threadvar globals — Mach-O TLV descriptors }
    FTlvSize:     TDictionary<string, Integer>;  { per-thread storage bytes }
    FGlobalWeak:  TStringList;   { globals bound weak: RTL-unit-owned copies
                                   collapse across per-unit objects (GH #174) }
    FIntfDecls:   TObjectList;   { not owned — program-level interface TTypeDecls }
    FGenericIntfInstances: TObjectList; { not owned — TGenericInterfaceInstance
                                   for each monomorphised interface instance
                                   (IComparer<Integer> etc); their typeinfo is
                                   emitted WEAK so the itab/impllist reference
                                   resolves and cross-unit copies dedup }
    FIntfLocals:  TStringList;   { interface locals (base name) — obj released at exit }
    FIntfGlobals: TStringList;   { interface globals (prefixed base name) }
    FExcDepth:    Integer;       { active exception frames at emission point }
    FExcSlotN:    Integer;       { next _excf_N frame slot ordinal }
    FFinallyBodies: TObjectList; { not owned — TCompoundStmt per frame (nil =
                                   except frame); mirrors the runtime stack }
    FLoopExcDepth: TStringList;  { FExcDepth at each enclosing loop's entry —
                                   break/continue unwind to it }
    FDynLocals:   TStringList;   { dyn-array locals — released at scope exit }
    FDynGlobals:  TStringList;   { dyn-array globals — released at exit }
    FStrGlobals:  TStringList;   { string program globals — released at
                                   the program exit }
    FRecLocals:   TStringList;   { record locals; Objects = TRecordTypeDesc }
    { BY-VALUE record parameters of the routine being emitted.  The semantic
      pass marks EVERY record param IsVarParam=True ("records pass by reference
      at the ABI level"), so codegen needs its own record of which of those are
      really by-value in THIS backend's frame.  A >16B (shape 0) param is by
      pointer and gets a '__pptr_' slot; a shape 1/2/HFA param arrives in
      registers and is spilled INLINE with no '__pptr_' — inferring by-value
      from '__pptr_' presence therefore misclassified every small record param
      as var/out and dereferenced its value (macOS arm64 on-device crash,
      2026-07-23).  Membership here is the explicit answer. }
    FByValRecParams: TStringList;
    FRecGlobals:  TStringList;   { record program globals; Objects = desc }
    FRefLocals:   TStringList;   { 'reference to' closure locals — the Env half
                                   (+8) is _ClassRelease'd at scope exit (arkRefEnv) }
    FRefGlobals:  TStringList;   { 'reference to' closure program globals }
    FGlobalSize:  TDictionary<string, Integer>;  { bss size per global }
    FFloatNames:  TStringList;   { program-level float globals (parallel
                                   subset of FGlobalNames' world) }
    FPendingRelCount: Integer;   { live statement-scoped deferred class
                                   releases (BUG-048/BUG-049) — also the next
                                   free _pendrel_N slot index }
    FIndirectSlot: string;       { VIRT_INDIRECT: frame slot holding the
                                   address of the procedural value to call }
    FJArgN: Integer;             { counter for '__jarg_<n>' jumbo-set
                                   argument snapshots }
    FFretN: Integer;             { counter for '__fret_<n>' closure-result
                                   scratch slots (one per call site) }
    FCurEnvCaptured: TStringList; { borrowed: the current routine's
                                   EnvCaptured -- names living in a PACKED env
                                   field rather than an 8-byte frame slot }
    FEnvCaps: TStringList;       { owned: CapturedVars + EnvCaptured merged for
                                   a routine with a closure env (FCapturedVars
                                   points here while it is emitted) }
    FCapturedVars: TStringList;  { names captured from an enclosing routine
                                   while emitting a nested routine (leg 17).
                                   Each captured var V has a hidden leading
                                   pointer param spilled to a '_cap_V' frame
                                   slot holding &V; reads/writes/address-of of
                                   V redirect through that slot.  Nil outside a
                                   capturing nested routine.  Mirrors the x86-64
                                   backend's FCapturedVars. }

    function  NewLabel(const APrefix: string): string;
    { True when AName is captured from an enclosing routine in the current
      nested routine (accessed via its hidden '_cap_<Name>' pointer slot). }
    function  IsCaptured(const AName: string): Boolean;
    { True when RecordName is a BY-VALUE record param (its inline copy lives in
      the ParamName slot, so its address is EmitSlotAddr, NOT EmitLoadSlot).
      The semantic pass flags EVERY record param IsVarParam=True (records pass
      by reference at the ABI level), so codegen keeps its own explicit record
      of which ones are really by-value — FByValRecParams, filled by the frame
      setup.  A >16B (shape 0) param arrives by pointer and the prologue
      memcpies it into the inline slot; a shape 1/2/HFA param is spilled inline
      straight from its argument registers.  Either way the slot ends up
      holding the value, which is what distinguishes it from a true var/out
      param whose slot holds the caller's address. }
    function  IsByValueRecordParam(const AName: string): Boolean;
    { Load into AReg the ADDRESS of a plain (Base=nil) record lvalue named
      AName, given its resolved IsVarParam flag.  A TRUE var/out record param's
      slot holds the caller's address (one deref → EmitLoadSlot); a by-value
      record param and a local/global record hold the value inline (address is
      EmitSlotAddr).  Centralises the '__pptr_' discriminator so every
      field-store/read arm agrees. }
    procedure EmitRecordBaseAddr(const AReg, AName: string; AIsVarParam: Boolean);
    { True when a string ARG expression is a BORROWED aliasable source — a
      param read (const or by-value), a global, an implicit-Self field, or a
      captured local — that must be PINNED (_StringAddRef before / _StringRelease
      after) when handed to a by-value or const string param.  The callee's
      by-value param does entry-retain/exit-release, so if the borrowed source's
      liveness across the call is not guaranteed by a stable owning slot, the
      callee's exit-release can drop it one too many and free it mid-flight.
      Mirrors the x86-64 ConstStrShape / QBE ConstArgMode camPin classification.
      A plain owned local also pins when the callee signature carries a var/out
      string param (the F(L, L) alias hazard), via APinPlain. }
    function  IsPinnedBorrowedStrArg(AArg: TASTExpr; APinPlain: Boolean): Boolean;
    { True when AParams has any var/out string param (the F(const A; var B)
      alias hazard that forces a plain-local source to pin). }
    function  ParamsHaveVarString(AParams: TObjectList): Boolean;
    procedure NotYet(const AWhat: string; ANode: TASTNode);

    { ---- frame + operands ---- }
    procedure AddIntfLocal(const AName: string);
    procedure AddLocal(const AName: string; ASize: Integer);
    function  IsLocal(const AName: string): Boolean;
    { Deferred class-release (BUG-048): reserve the PENDREL_SLOTS frame slots,
      record a base pointer (in x0) for release at statement end, and flush
      the pending releases back down to a saved mark. }
    procedure ReservePendRelSlots;
    function  DeferNativeClassRelease: Boolean;
    procedure FlushNativePendingReleases(AMark: Integer);
    { Load a captured var's field-access base / method receiver through its
      hidden '_cap_' slot (leg 19).  Returns True when AName was captured. }
    function  EmitCapturedBase(const AReg, AName: string;
      AWantValue, AIsVarParam: Boolean): Boolean;
    { Load/store x-register <-> local slot / global (int-family only). }
    procedure EmitLoadSlot(const AReg, AName: string);
    procedure EmitStoreSlot(const AReg, AName: string);
    { Store AValReg through the ADDRESS in AAddrReg using the exact width of
      AType — for storage that is only as wide as its declared type (a var/out
      param's target, a field, an array element), where a full 64-bit store
      would clobber the bytes that follow. }
    procedure EmitStoreByWidth(const AValReg, AAddrReg: string;
      AType: TTypeDesc);
    { Re-widen a NARROW variable's slot after a callee wrote only the declared
      width into it through a var/out parameter.  See the call site in EmitCall. }
    procedure EmitNormaliseNarrowSlot(const AName: string; AType: TTypeDesc);
    { Address of a variable's storage (record base / slot address). }
    procedure EmitSlotAddr(const AReg, AName: string);
    procedure EmitRecIdentAddr(const AReg: string; AE: TIdentExpr);
    procedure EmitRecFieldAddrToX0(AFA: TFieldAccessExpr);
    procedure EmitRecAddrToX0(AExpr: TASTExpr);
    procedure EmitRecCallToRret(AExpr: TASTExpr);
    procedure EmitPropRecvToX0(AStmt: TFieldAssignment);
    procedure EmitIndexedPropWrite(AProp: TPropertyInfo; const AOwner: string;
      AVSlot: Integer; AIndex, AValue: TASTExpr; AStmt: TASTStmt);
    procedure EmitSubscriptPropRecvToX0(AStmt: TStaticSubscriptAssign);
    { Materialise an anonymous-method literal into its hidden 16-byte value slot
      (Code at +0, Env at +8) and leave the slot ADDRESS in x0 — the fat value
      is used by reference (leg 38).  For a capture-free literal Env is nil. }
    procedure EmitAnonValueToSlot(AME: TAnonMethodExpr);
    procedure EmitAnonValueInto(AME: TAnonMethodExpr; const ASlot: string);
    procedure EmitFatPtrAssign(AAsgn: TAssignment);
    procedure EmitParenlessCtor(AFA: TFieldAccessExpr);
    procedure EmitSetIncludeExclude(ACall: TProcCall; AInclude: Boolean);
    procedure EmitFatFieldStoreStacked(AFld: TFieldInfo; AValueExpr: TASTExpr);
    function  EmitClosureResultCall(ACallDecl: TMethodDecl; const AName: string;
      AArgs: TObjectList): string;
    procedure EmitEnvPrologue(ADecl: TMethodDecl);
    function  IsEnvCaptured(const AName: string): Boolean;
    procedure EmitCapturedLoad(AIdent: TIdentExpr);
    procedure EmitEnvCleanupFn(AEnv: TRecordTypeDesc);
    { Invoke a closure/method-pointer fat value whose ADDRESS is in AAddrReg:
      load Code, pass Env as the hidden first arg (x0), the visible args in
      x1.., blr.  Result in x0/d0 per the callee's return type. }
    { NotYet when a procedural signature has an open-array param: the
      indirect-call loops pass one register per arg, so a dynamic array would
      silently lose its high (BUG-20260923-addr-of-openarray-proc). }
    procedure GuardNoOpenArrayParam(AProcType: TProceduralTypeDesc;
      ANode: TASTNode);
    procedure EmitFatPtrCall(const AAddrReg: string; AProcType: TProceduralTypeDesc;
      AArgs: TObjectList; AIsFat: Boolean = True);
    procedure EmitProcFieldAddr(const AObjectName: string; AObjExpr: TASTExpr;
      AIsVarParam, AImplicitSelf: Boolean; AReceiver: TTypeDesc;
      AField: TFieldInfo; ANode: TASTNode);
    procedure EmitDiscardedProcResult(APT: TProceduralTypeDesc);
    procedure EmitProcFieldCall(const AObjectName: string; AObjExpr: TASTExpr;
      AIsVarParam, AImplicitSelf: Boolean; AReceiver: TTypeDesc;
      AField: TFieldInfo; AArgs: TObjectList; ANode: TASTNode);
    { Release an owned-transient STRING value in x0 by shape, mirroring
      EmitCall's post-call disposal: a concat/rc=0 unowned transient
      (ArcExprIsUnownedStrTransient) needs AddRef+Release (0->1->0 frees once);
      an rc=1 owned transient needs a bare Release.  Used after a property
      setter borrows the value (leg 36); the rc=0 pin half moved BEFORE the
      call (BUG-20260722-arm64-propsetter-pin-after-call). }
    procedure EmitOwnedStrTransientRelease(AValueExpr: TASTExpr);
    procedure EmitOwnedStrTransientPin(AValueExpr: TASTExpr);
    procedure EmitFieldAssign(AStmt: TFieldAssignment);
    { Rec.Field[Index] := value where Field is an array-typed field (leg 12).
      Computes the element address (field data pointer + index*elemsize) and
      stores the value with the ARC discipline of the element type — the same
      element-store logic as EmitStaticElemAssign, sourcing the array from a
      record field slot instead of a plain variable. }
    procedure EmitFieldElemAssign(AStmt: TFieldAssignment);
    { Compute the address of Rec.Field[Index] into x0 — called AFTER the value
      expression is materialised so a value that reallocates the field's
      dyn-array cannot leave a stale data pointer. }
    procedure EmitFieldElemAddrToX0(AStmt: TFieldAssignment; AElem: TTypeDesc;
      AIsDyn: Boolean; ALow: Integer);

    { ---- expression lowering (result in x0) ---- }
    procedure EmitExprToX0(AExpr: TASTExpr);
    procedure EmitAddSubImm(const AOp, ADst, ASrc: string; AImm: Integer);
    procedure EmitPushX0;
    procedure EmitPopTo(const AReg: string);
    procedure EmitIntLiteral(const AReg: string; AValue: Int64);
    { Float expression lowering (result in d0). }
    procedure EmitExprToD0(AExpr: TASTExpr);
    { Float-context operand: floats via EmitExprToD0, integers via
      EmitExprToX0 + scvtf widening. }
    procedure EmitExprToD0OrConvert(AExpr: TASTExpr);
    function  IsFloatExpr(AExpr: TASTExpr): Boolean;
    { Ownership of a string value in x0: ArcExprOwnsRef plus concat — this
      backend consumes concat's +1 directly instead of the deferred
      transient-release machinery the mature backends use (a concat result
      here is always consumed exactly once by its statement). }
    procedure EmitStrDisposeX0(AExpr: TASTExpr);
    procedure EmitFloatLitSection;
    procedure EmitStrLitAddr(AValue: string);
    { Emit the RHS of a BYTE store (strb) into x0 as a raw ordinal.

      Chr(N) must NOT be lowered through the normal _Chr call here: Chr returns
      a heap string POINTER, and a following strb would store the low byte of
      that pointer instead of N — the classic "P[I] := Chr(N)" garbage bug that
      QBE and x86-64 both short-circuit.  The same trap applies to a
      single-character string literal, whose normal lowering yields the
      literal's data ADDRESS.  Both fold to the ordinal directly; anything else
      evaluates normally. }
    procedure EmitStrLen(const AReg: string);
    procedure EmitByteRhsToX0(AValueExpr: TASTExpr);
    { Advance the base pointer in AReg from Self across an implicit-Self
      intermediate field (Self.FIntermediate.Member).  If FIntermediate is an
      embedded RECORD, its bytes live inside the instance, so add its offset.
      If it is a CLASS reference (a pointer), LOAD the pointer at that offset
      and continue from the pointee.  Passing the record's kind unconditionally
      as "add" miscompiled every Self.<classfield>.<member> access — the class
      field was treated as embedded and its offset added instead of derefed
      (macOS arm64, 2026-07-23). }
    procedure EmitImplicitBaseStep(const AReg: string; ABaseInfo: TFieldInfo);
    function  AsmEscape(const AValue: string): string;
    { Box one 'array of const' element as a 16-byte TVarRec (VType byte at +0,
      VValue at +8) at [sp, #AOffset].  AOffset is sp-relative and stable
      across the element evaluation (no net sp change).  Mirrors x86-64
      EmitConstArrayLiteral's per-element boxing. }
    procedure EmitConstArrayElemToVarRec(AElem: TASTExpr; AOffset: Integer);
    { Evaluate a condition/selector/operand expression to x0 and flush any
      class-field-on-transient bases it deferred, so the borrowed field value
      is consumed and its transient released within this evaluation — the
      result (in x0) is preserved across the flush.  Used at loop conditions
      (per iteration), if/case/raise operands (BUG-049). }
    procedure EmitCondToX0Flushed(AExpr: TASTExpr);

    { ---- statements ---- }
    procedure EmitStmt(AStmt: TASTStmt);
    procedure EmitStmtBody(AStmt: TASTStmt);
    procedure EmitStmtList(AStmts: TObjectList);
    procedure EmitAssignment(AAsgn: TAssignment);
    procedure EmitProcCallStmt(ACall: TProcCall);
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    procedure EmitIf(AStmt: TIfStmt);
    procedure EmitWhile(AStmt: TWhileStmt);
    function  NewExcFrameSlot: string;
    procedure EmitExcPrologue(const AFrameSlot, AExcLbl, ATryLbl: string);
    procedure EmitExcUnwindTo(ATargetDepth: Integer);
    procedure EmitTryFinally(AStmt: TTryFinallyStmt);
    procedure EmitTryExcept(AStmt: TTryExceptStmt);
    procedure EmitStaticElemAssign(AStmt: TStaticSubscriptAssign);
    procedure EmitRaise(AStmt: TRaiseStmt);
    procedure EmitRepeat(AStmt: TRepeatStmt);
    procedure EmitCase(AStmt: TCaseStmt);
    procedure EmitExprToX0Aux(AExpr: TASTExpr);
    procedure EmitFor(AStmt: TForStmt);
    procedure EmitForIn(AStmt: TForInStmt);
    procedure EmitForInAssignX0(AStmt: TForInStmt; AOwned: Boolean);
    { assign the record / interface value whose ADDRESS is in x0 to a for-in
      loop variable; AOwned = the value's references transfer (no retain) }
    procedure EmitForInAssignAddr(AStmt: TForInStmt; AOwned: Boolean);
    procedure EmitPointerWrite(AStmt: TPointerWriteStmt);
    procedure EmitNarrowX0(AType: TTypeDesc);
    procedure EmitBuiltinStrCall1(AArg: TASTExpr; const ASym: string);
    procedure EmitFormatCall(AArgs: TObjectList);
    procedure EmitRecCallDispatch(AExpr: TASTExpr; const ADest: string;
      ASretSpOff: Integer = SRET_NO_BUF);
    procedure EmitBuiltinStrCall2(AArg0, AArg1: TASTExpr;
      const ASym: string);
    procedure EmitExit(AStmt: TExitStmt);
    procedure EmitFunctionDef(ADecl: TMethodDecl;
      AWeakBind: Boolean = False);
    function  StackArgSize(AArg: TASTExpr): Integer;
    function  StackParamSize(APar: TMethodParam): Integer;
    function  AlignTo(AValue, AAlign: Integer): Integer;
    function  ComputeStackArgArea(ADecl: TMethodDecl; AArgs: TObjectList;
      ASelfPushed: Boolean): Integer;
    function  ComputeStackArgAreaEx(ADecl: TMethodDecl; AArgs: TObjectList;
      ASelfPushed: Boolean; out ALitBase: Integer;
      out ATransBase: Integer; out ARecBase: Integer): Integer;
    function  IsRecordCallArg(AArg: TASTExpr): Boolean;
    procedure DecodeMemArg(const AEntry: string; out AOff, ASize: Integer);
    procedure EmitCall(ADecl: TMethodDecl; const AName: string;
      AArgs: TObjectList; const ASretDest: string = '';
      ASelfPushed: Boolean = False; AVirtSlot: Integer = VIRT_NONE;
      { >=0: the callee's x8 indirect-result buffer lives at sp+this,
        measured at OUR entry (before our own outgoing-area sub sp).  Used
        for a >16B record-returning call whose destination is a caller
        scratch buffer with no slot name, so ASretDest cannot name it. }
      ASretSpOff: Integer = SRET_NO_BUF);
    { Pre-pass: register every local/param/hidden slot a routine body needs
      so the frame size is final before the prologue's sub sp. }
    function  MaxManagedRecRet(AStmt: TASTStmt): Integer;
    procedure RegisterFrameSlots(ADecl: TMethodDecl; ABody: TBlock);
    procedure RegisterForSlots(AStmt: TASTStmt);
    { THE DARWIN UNDERSCORE RULE — the single seam that applies the Mach-O C
      symbol-prefix convention.  On Darwin EVERY name gets exactly one leading
      '_', with no exceptions and no attempt to classify the name first.

      That uniformity is not a simplification we chose; it is what the platform
      and QBE already do, and it is verifiable:

        Pascal Helper          -> _Helper
        Pascal _StringAddRef   -> __StringAddRef
        external 'getpid'      -> _getpid          (libSystem's real symbol)
        external '__cxa_atexit'-> ___cxa_atexit    (libSystem's real symbol)

      QBE, whose Apple target has always done this, emits exactly these names,
      so a QBE-compiled program and a natively-built RTL object agree and link.
      An earlier version of this rule skipped a name that already began with
      '_', which kept the RTL's own _StringAddRef spelled _StringAddRef; that
      disagreed with QBE's __StringAddRef and made the two object worlds
      unlinkable on macOS.  It was also non-injective (a routine 'X' beside a
      routine '_X' collapsed onto one symbol).  Both problems are artefacts of
      the skip, not of the convention.

      Because the rule needs no C-versus-Pascal discrimination, it applies to
      ADecl.ExternalName too, and TMachOLinker.BindNameOf is consequently the
      identity — names reach the linker already correctly spelled.

      Gated on the TARGET OS, not the host: linux-arm64 and freebsd-arm64 are
      real targets whose ELF output must stay byte-identical. }
    function  DarwinSym(const AName: string): string;
    { The '.section' directive for each logical section, spelled for the
      TARGET's container.  ELF names them .rodata/.data/.bss; Mach-O names them
      (segment,section) pairs, and Darwin's assembler REJECTS the ELF spelling
      outright — 'error: unknown directive'.  Our own internal assembler accepts
      either, which is exactly why this stayed hidden: every path that mattered
      went through the internal assembler, so the emitted text was only wrong for
      the EXTERNAL one.  It cost 135 e2e tests, which link native output with cc,
      and it is why fixpoint-native-internal.sh cannot run on macOS.
      Three accessors rather than one string-keyed helper so a call site cannot
      typo a section name into a silent fallthrough. }
    function  SecRodata: string;
    function  SecData: string;
    function  SecBss: string;
    { Binding directives for a DEFINITION, spelled for the target.  A weak
      definition is '.weak' alone on ELF, but Mach-O needs '.globl' AND
      '.weak_definition' for the same symbol — '.weak' is not a directive the
      Darwin assembler knows at all.  Routed through here so no site has to
      remember that, and so the ELF output stays byte-identical. }
    procedure EmitWeakDef(const ASym: string);
    procedure EmitGloblDef(const ASym: string);
    { Emit a call to a fixed, hand-named symbol — an RTL routine (_StringAddRef)
      or a libc function (memcpy).  Routing every such site through here keeps
      the ~240 hard-coded call targets in this unit target-independent: the
      platform prefix is applied once, here, instead of being baked into each
      literal. }
    procedure EmitCallSym(const AName: string);
    { The metadata symbol families.  Each is the SINGLE source of truth for its
      spelling so a definition and every reference cannot drift — the lesson
      TypeinfoSymFor already records, applied to the other three. ABase is a
      ClassSym result (already unit-prefixed and mangled). }
    function  TypeinfoSym(const ABase: string): string;
    function  VtableSym(const ABase: string): string;
    function  ImpllistSym(const ABase: string): string;
    function  FieldCleanupSym(const ABase: string): string;
    function  RoutineSym(ADecl: TMethodDecl; const AName: string): string;
    function  GlobalSym(const AName: string): string;
    function  ItabBaseName(const AName: string): string;
    function  IsSymTableVar(const AName: string): Boolean;
    procedure RegisterGlobalInit(const ASym: string; AVD: TVarDecl);
    { AAPCS64 record-return shape for ARec: 0 = sret via x8, 1 = x0,
      2 = x0:x1 memory image, 3/4 = HFA of N Doubles in d0..d(N-1)
      (encoded as 100+N).  Derived from the shared classifier; the
      register choice is this leaf's per-CPU step. }
    function  TypeinfoSymFor(const ATypeName: string): string;
    procedure EmitArrayConstData(ABlock: TBlock);
    procedure EmitAttrTables(ACD: TClassTypeDef; const ACSym: string;
      out AAttrsRef, AMethAttrsRef: string);
    { methods_<C>: the PUBLISHED-method table referenced by typeinfo[3] —
      count then (name, code, param-sig-or-0) triples, the layout
      runtime.arc's _MethodAddress walks. }
    procedure EmitMethodsTable(ACD: TClassTypeDef; const ACSym: string;
      out AMethodsRef: string);
    procedure EmitSmallSetLiteral(AExpr: TArrayLiteralExpr);
    procedure EmitJumboSetOp(ABE: TBinaryExpr);
    procedure EmitJumboSetLiteral(AExpr: TArrayLiteralExpr);
    function  JumboSetLiteralBytes(AExpr: TASTExpr): Integer;
    function  IsJumboSetType(AType: TTypeDesc): Boolean;
    procedure EmitStaticElemAddr(ASub: TStringSubscriptExpr);
    { x0 := address of the inline storage of a STATIC-array-valued
      expression (a variable, a field, an element of an outer array, P^) }
    procedure EmitArrayStorageAddr(AExpr: TASTExpr);
    procedure EmitDynElemAddr(ASub: TStringSubscriptExpr);
    { x0 := address of an ELEMENT of an array-typed FIELD (leg 20):
      @Obj.Arr[I] / @Self.Arr[I] / @Rec.Arr[I].  The field access carries
      IsArrayAccess with the index in PropIndexExpr.  A static-array field is
      inline at base+offset (no deref); dyn/open-array fields deref the data
      pointer first. }
    procedure EmitFieldElemAddr(AFAE: TFieldAccessExpr);
    procedure EmitElemLoad(AElem: TTypeDesc);
    function  AggHasManaged(AType: TTypeDesc): Boolean;
    function  RecReturnShape(ARec: TRecordTypeDesc): Integer;

    procedure EmitStrLitSection;
    procedure EmitGlobalsSection;
  protected
    procedure EmitProgram(AProg: TProgram); override;
    procedure EmitUnit(AUnit: TUnit); override;
    procedure EmitUnitInit(AUnit: TUnit);
    procedure EmitUnitSection(AUnit: TUnit; AStmts: TObjectList;
      const ASym: string; ARegistry: TStringList);
    function  ClassPrefixOwner(const AOwner: string): string;
    function  PropAccessorSym(const AOwnerType, AMethod: string): string;
    function  ClassSym(ATD: TTypeDecl): string;
    function  ClassDescOf(ATD: TTypeDecl): TRecordTypeDesc;
    procedure EmitClassCleanupFns;
    procedure EmitClassMetaSections;
    procedure EmitTlvAddr(const ASym: string);
    procedure EmitTlvSections;
    procedure EmitMethodCallCommon(AMethod: TMethodDecl; const AName: string;
      AArgs: TObjectList);
    procedure EmitMethodCallOnExpr(AMethod: TMethodDecl; const AName: string;
      AArgs: TObjectList; AObjExpr: TASTExpr);
    procedure EmitMethodCallStmt(AStmt: TMethodCallStmt);
    procedure EmitMethodCallExpr(AExpr: TMethodCallExpr);
    procedure EmitClassCreate(AExpr: TFuncCallExpr);
    { A failed `as`: SysUtils' _RaiseInvalidCast (a catchable EInvalidCast)
      when SysUtils is in scope, else the RTL's fatal _Raise_InvalidCast. }
    procedure EmitRaiseInvalidCast;
    procedure EmitNonOwningFieldStore(AFld: TFieldInfo; const ABase: string);
    { ABaseInfo describes the CONTAINING field for a nested Self path
      (Self.FIntermediate.SubField) — AFld then describes only SubField, whose
      Offset is relative to the intermediate.  If the intermediate is an
      embedded RECORD its offset is added to the base; if it is a CLASS
      reference the base pointer is LOADED (dereferenced) from that offset.
      Omitting the step stored every sub-field at Self + SubField.Offset
      (record case: SetSource's FToken.* landed on the vtable/FSource); adding
      it unconditionally miscompiled a class intermediate (both 2026-07-23).
      nil = no intermediate (a direct Self.Field). }
    procedure EmitInstanceFieldStore(AFld: TFieldInfo;
      AValueExpr: TASTExpr; const AInstSlot: string; AInstVarParam: Boolean;
      ABaseInfo: TFieldInfo = nil);
    { Load the instance-pointer base for a field store into AReg — captured
      (via '_cap_') or a plain slot ('Self' / a class var).  leg 19. }
    procedure EmitInstBase(const AReg, AInstSlot: string;
      AInstVarParam: Boolean; ABaseInfo: TFieldInfo = nil);
    procedure EmitImplicitSelfStore(AAsgn: TAssignment);
    procedure EmitInterfaceAssign(AAsgn: TAssignment);
    procedure EmitPropReadCall(AFld: TFieldAccessExpr; const ASret: string = '');
    { the record-typed property read inside AExpr (Obj.Prop, Obj.Items[I] or
      the default-property form Obj[I]), or nil }
    function  RecordPropRead(AExpr: TASTExpr): TFieldAccessExpr;
    { x0 := address of a per-site scratch holding a record property's value }
    procedure EmitRecPropToTemp(AFld: TFieldAccessExpr);
    procedure EmitInterfaceAsCast(AAsgn: TAssignment);
    { Load an interface-typed value into x0 (obj) / x1 (itab); True when the
      obj half is an OWNED +1 (a call result), False when it is borrowed. }
    function  EmitIntfPairToX0X1(AExpr: TASTExpr; AIntfType: TTypeDesc): Boolean;
    { Store an interface value into the 16-byte (obj, itab) pair at
      [base + AOff], the base on TOP of the stack (consumed). }
    procedure EmitIntfStoreStacked(AOff: Integer; AValueExpr: TASTExpr;
      AIntfType: TTypeDesc);
    { x0/x1 := the (obj, itab) pair of an interface method-call RECEIVER }
    function  EmitIntfRecvPair(const AObjName: string; AObjExpr: TASTExpr;
      AVarParam: Boolean; AImplicitBase: TFieldInfo; ANode: TASTNode): Boolean;
    function  IntfItabSym(const AClassName, AIntfName: string): string;
    procedure EmitTypeinfoAddr(const AReg, ATypeName: string);
    procedure EmitVarArgAddrToX0(Arg: TASTExpr);
    function  IsIntfArg(ADecl: TMethodDecl; AIndex: Integer;
      AArg: TASTExpr): Boolean;
    procedure EmitIntfDispatch(const AVarName: string; AIntf: TInterfaceTypeDesc;
      AIdx: Integer;
      AArgs: TObjectList; AObjExpr: TASTExpr = nil; AVarParam: Boolean = False;
      AImplicitBase: TFieldInfo = nil; const ASret: string = '');
    procedure EmitIntfMetaSections;
    function  FindClassMethodImpl(ATD: TTypeDecl;
      const AName: string): TMethodDecl;
    { True if AMethName maps to an ABSTRACT vtable slot on AClassRT (an
      interface method with no implementation) — the itab slot then points at
      _AbstractMethodError.  Mirrors x86-64 IsAbstractClassMethod. }
    function  IsAbstractClassMethod(AClassRT: TRecordTypeDesc;
      const AMethName: string): Boolean;
    { Symbol the itab entry for AMethName on AClassRT/ATD should point at:
      the method's vtable-slot ImplName (correct across units + for inherited /
      generic-instance methods), falling back to the AST class chain for a
      non-virtual interface method.  Mirrors x86-64 ItabMethodRefNative. }
    function  ItabMethodRefArm64(AClassRT: TRecordTypeDesc; ATD: TTypeDecl;
      const AMethName: string): string;
    function  ClassImplementsAny(ATD: TTypeDecl): Boolean;
    procedure EmitInstanceFieldStoreStacked(AFld: TFieldInfo;
      AValueExpr: TASTExpr);
    procedure RegisterUnitVars(ABlock: TBlock);
    procedure FinalizeEmit; override;

    { ---- ARC walk primitives (TNativeBackend contract) ----
      x21 anchors an array walk (x86 %r15), x20 is the derived-base /
      element scratch (x86 %r14); both callee-saved, saved as a 16-byte
      pair so sp alignment holds across the per-element runtime calls. }
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
  public
    constructor Create(const ATarget: TTargetDesc); override;
    destructor Destroy; override;
    { Separate compilation: a dependency unit's body — and its <Unit>_init /
      <Unit>_final — live in the dep's OWN object, so EmitUnit never runs for
      it here and never fills FUnitInits/FUnitFinals.  These record the names
      anyway so _main still calls them.  Without the overrides arm64 inherited
      TNativeBackend's no-op and an incrementally built program called NO unit
      initialization at all: every initialization-populated global stayed empty
      (e.g. GDrivers, leaving 'no driver registered for backend kind') — the
      macOS arm64 on-device failure of 2026-07-23.  The whole-program path was
      unaffected, which is why --emit-asm looked correct. }
    procedure NoteDepInitUnit(const AUnitName: string;
      AHasInit: Boolean); override;
    procedure NoteDepFiniUnit(const AUnitName: string;
      AHasFini: Boolean); override;
  end;

implementation

{ Integer-family predicate (local twin of the x86-64 unit's free function;
  candidate for a shared home in blaise.codegen once the leaf grows). }
function IsIntFam(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    (AType.Kind in [tyInteger, tyInt64, tyUInt64, tyUInt32, tyByte,
                    tySmallInt, tyWord, tyBoolean, tyEnum]);
end;

{ True for unsigned integer-family types (local twin of the x86-64 unit's
  IsUnsignedInt).  Byte/Word/UInt32/UInt64 are unsigned; Boolean and Enum
  hold non-negative ordinals; a small set is a bitmask.  Used to pick
  udiv over sdiv — see the boDiv/boMod arm. }
function IsUnsignedIntA64(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    (AType.Kind in [tyByte, tyBoolean, tyWord, tyUInt32, tyUInt64,
                    tyEnum, tySet]);
end;

{ True when AType is a 32-bit-or-narrower integer/ordinal (NOT Int64/UInt64,
  pointer, string, class or float).  Such a value occupies only the low 32 bits
  of its 64-bit register, and the upper 32 bits are NON-CANONICAL: an Integer
  LITERAL with bit 31 set is materialised sign-extended, but a value COMPUTED
  via shifts/or (e.g. RdU32's byte assembly) is left zero-extended.  A 64-bit
  compare of two such differently-extended values is wrong (the Mach-O reader's
  MH_MAGIC_64 check rejected a valid object on-device, macOS arm64 2026-07-24).
  Comparing these operands with 32-bit `w` registers ignores the non-canonical
  upper halves, exactly as the x86-64 backend's 32-bit `cmpl` does. }
function IsNarrow32Ord(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    (AType.Kind in [tyInteger, tyUInt32, tyByte, tySmallInt, tyWord,
                    tyBoolean, tyEnum]);
end;

{ A method-pointer ('of object') or closure ('reference to') procedural type —
  a 16-byte FAT value: Code at +0, Data/Env at +8.  Mirrors the x86-64 unit's
  IsMethodPtrType.  A plain proc pointer (neither flag) is a single code
  pointer and is NOT matched here. }
function IsMethodPtrType(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind = tyProcedural) and
    (TProceduralTypeDesc(AType).IsMethodPtr or
     TProceduralTypeDesc(AType).IsReference);
end;

{ True for a result returned through the caller's x8 buffer (an sret
  aggregate): a record (by RecReturnShape), an interface fat pointer, or a
  closure / method-pointer fat value.  The "not yet lowered" guards on call
  positions that pass no x8 buffer test THIS, so a closure-returning call
  there is rejected instead of letting the callee write through a garbage x8. }
function IsAggregateReturn(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    ((AType.Kind in [tyRecord, tyInterface]) or IsMethodPtrType(AType));
end;

{ A set held inline as a bitmask (<= 64 members).  A jumbo set is a byte
  bitmap reached by ADDRESS, so it is not a loadable scalar. }
function IsSmallSetType(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType is TSetTypeDesc) and
            not TSetTypeDesc(AType).IsJumbo();
end;

{ A one-word reference value with no ARC: a metaclass, or a PLAIN procedural
  pointer (a single code address).  The 16-byte closure / method-pointer
  kinds are excluded -- an 8-byte load of those would drop the Env half. }
function IsPlainWordRef(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    ((AType.Kind = tyMetaClass) or
     ((AType.Kind = tyProcedural) and not IsMethodPtrType(AType)));
end;

constructor TArm64Backend.Create(const ATarget: TTargetDesc);
begin
  inherited Create(ATarget);
  FFrame       := TDictionary<string, Integer>.Create();
  FGlobalNames := TStringList.Create();
  FStrLits     := TStringList.Create();
  FBreakLbls   := TStringList.Create();
  FContLbls    := TStringList.Create();
  FFloatLits   := TStringList.Create();
  FFloatNames  := TStringList.Create();
  FStrLocals   := TStringList.Create();
  FStrGlobals  := TStringList.Create();
  FModuleVarNames := TStringList.Create();
  FUnitInits   := TStringList.Create();
  FUnitFinals  := TStringList.Create();
  FGlobalInits := TDictionary<string, string>.Create();
  FGlobalStrInits := TStringList.Create();
  FGlobalStrVals  := TStringList.Create();
  FClassDecls  := TObjectList.Create(False);
  FRecordDecls := TObjectList.Create(False);
  FGenericDecls := TObjectList.Create(True);
  FUnitEmittedClasses := TObjectList.Create(False);
  FObjLocals   := TStringList.Create();
  FWeakLocals  := TStringList.Create();
  FObjGlobals  := TStringList.Create();
  FTlvGlobals  := TStringList.Create();
  FTlvSize     := TDictionary<string, Integer>.Create();
  FGlobalWeak  := TStringList.Create();
  FIntfDecls   := TObjectList.Create(False);
  FGenericIntfInstances := TObjectList.Create(False);
  FIntfLocals  := TStringList.Create();
  FIntfGlobals := TStringList.Create();
  FFinallyBodies := TObjectList.Create(False);
  FLoopExcDepth := TStringList.Create();
  FDynLocals := TStringList.Create();
  FDynGlobals := TStringList.Create();
  FRecLocals   := TStringList.Create();
  FByValRecParams := TStringList.Create();
  FRecGlobals  := TStringList.Create();
  FRefLocals   := TStringList.Create();
  FRefGlobals  := TStringList.Create();
  FGlobalSize  := TDictionary<string, Integer>.Create();
  FFrameSize   := 0;
  FLabelN      := 0;
  FForN        := 0;
  FCapturedVars := nil;   { borrowed ref to ADecl.CapturedVars; not owned }
  FEnvCaps := TStringList.Create();
end;

destructor TArm64Backend.Destroy;
begin
  FEnvCaps.Free();
  FGlobalSize.Free();
  FRecGlobals.Free();
  FRecLocals.Free();
  FByValRecParams.Free();
  FRefLocals.Free();
  FRefGlobals.Free();
  FStrGlobals.Free();
  FModuleVarNames.Free();
  FUnitInits.Free();
  FUnitFinals.Free();
  FGlobalInits.Free();
  FGlobalStrInits.Free();
  FGlobalStrVals.Free();
  FRecordDecls.Free();
  FClassDecls.Free();
  FUnitEmittedClasses.Free();
  FGenericDecls.Free();
  FObjLocals.Free();
  FWeakLocals.Free();
  FObjGlobals.Free();
  FTlvGlobals.Free();
  FTlvSize.Free();
  FGlobalWeak.Free();
  FIntfDecls.Free();
  FGenericIntfInstances.Free();
  FIntfLocals.Free();
  FIntfGlobals.Free();
  FFinallyBodies.Free();
  FLoopExcDepth.Free();
  FDynLocals.Free();
  FDynGlobals.Free();
  FStrLocals.Free();
  FFloatNames.Free();
  FFloatLits.Free();
  FContLbls.Free();
  FBreakLbls.Free();
  FStrLits.Free();
  FGlobalNames.Free();
  FFrame.Free();
  inherited Destroy();
end;

function TArm64Backend.NewLabel(const APrefix: string): string;
begin
  Result := 'L' + APrefix + IntToStr(FLabelN);
  FLabelN := FLabelN + 1;
end;

function TArm64Backend.IsCaptured(const AName: string): Boolean;
begin
  Result := (FCapturedVars <> nil) and (FCapturedVars.IndexOf(AName) >= 0);
end;

{ True when AName is captured into a closure env record.  Unlike a
  nested-routine capture -- whose '_cap_' points at an 8-byte frame slot --
  an env field is packed at its declared width, so a store into it must be
  width-exact (an 8-byte store into a 4-byte Integer field overwrote the
  next field). }
function TArm64Backend.IsEnvCaptured(const AName: string): Boolean;
begin
  Result := (FCurEnvCaptured <> nil) and
            (FCurEnvCaptured.IndexOf(AName) >= 0);
end;

procedure TArm64Backend.EmitCapturedLoad(AIdent: TIdentExpr);
var
  T: TTypeDesc;
begin
  { '_cap_<Name>' holds &<Name>; a captured var-param's storage holds the
    caller's address, so it takes one more deref to reach the value.  The
    value itself is loaded at its DECLARED width: an env field is packed, so
    a 64-bit load of a 4-byte Integer dragged the neighbouring field into
    the upper half (A + K returned 10*2^32 + 115).  For an 8-byte frame slot
    the width-exact load reads the same canonical low bytes. }
  EmitLoadSlot('x0', '_cap_' + AIdent.Name);
  if AIdent.ParamMode = pmVar then
    Self.Emit(#9'ldr x0, [x0]');
  T := AIdent.ResolvedType;
  if (T <> nil) and (T.RawSize() < 8) and (T.RawSize() <> 3) and
     (IsIntFam(T) or (T.Kind in [tyBoolean, tyEnum, tySingle])) then
    EmitElemLoad(T)
  else
    Self.Emit(#9'ldr x0, [x0]');
end;

procedure TArm64Backend.NotYet(const AWhat: string; ANode: TASTNode);
var
  Pos: string;
begin
  Pos := '';
  if ANode <> nil then
    Pos := Format(' at line %d col %d', [ANode.Line, ANode.Col]);
  raise ENativeCodeGenError.Create(
    'arm64: not yet lowered: ' + AWhat + Pos
    + ' (the AArch64 backend subset grows incrementally — Phase 2)');
end;

{ ---- frame + operands --------------------------------------------------- }

procedure TArm64Backend.AddIntfLocal(const AName: string);
begin
  { an interface variable's (obj, itab) halves are ONE 16-byte block, obj at
    the lower address, so the pair has an address of its own: a var/out
    interface parameter receives it, and the callee reads/writes both halves
    at [addr] / [addr + 8].  The '_itab' name aliases the upper eightbyte. }
  AddLocal(AName, 16);
  FFrame.Add(AName + '_itab', FFrameSize - 8);
end;

procedure TArm64Backend.AddLocal(const AName: string; ASize: Integer);
var
  Sz: Integer;
begin
  Sz := ASize;
  if Sz < 8 then Sz := 8;
  { keep every slot 8-aligned; the frame total is 16-aligned at prologue }
  Sz := (Sz + 7) and (not 7);
  FFrameSize := FFrameSize + Sz;
  FFrame.Add(AName, FFrameSize);   { distance below x29 }
end;

function TArm64Backend.IsLocal(const AName: string): Boolean;
var
  Off: Integer;
begin
  Result := FFrame.TryGetValue(AName, Off);
end;

function TArm64Backend.IsByValueRecordParam(const AName: string): Boolean;
begin
  { A by-value record param's ParamName slot holds the record INLINE, so its
    address is EmitSlotAddr; a true var/out param's slot holds the caller's
    address (EmitLoadSlot).  Every shape ends up inline: a shape-0 param
    arrives by pointer (parked in '__pptr_') and the prologue's pass-2 memcpy
    copies the bytes INTO the ParamName slot, while a shape 1/2/HFA param is
    spilled inline straight from its registers.

    This used to test IsLocal('__pptr_' + AName), but that slot only ever
    exists for shape 0 — so every small (<=16B) record param was misread as a
    true var/out and its VALUE was dereferenced as a pointer (the macOS arm64
    TargetName(const ATarget: TTargetDesc) crash, 2026-07-23).  The frame setup
    now records by-value record params explicitly. }
  Result := FByValRecParams.IndexOf(AName) >= 0;
end;

function TArm64Backend.ParamsHaveVarString(AParams: TObjectList): Boolean;
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

function TArm64Backend.IsPinnedBorrowedStrArg(AArg: TASTExpr;
  APinPlain: Boolean): Boolean;
var
  IE: TIdentExpr;
begin
  { Mirrors x86-64 ConstStrShape / QBE ConstArgMode camPin classification.
    A string literal or named string constant is immortal (camBorrowed, no
    pin).  A bare zero-arg implicit-Self method call is an owned +1 return —
    disposed by the owned-transient path (ArcExprOwnsRef), not here. }
  Result := False;
  if AArg = nil then Exit;
  if AArg is TStringLiteral then Exit;
  if not (AArg is TIdentExpr) then Exit;
  IE := TIdentExpr(AArg);
  if IE.IsImplicitSelfMethod then Exit;   { owned return — not a borrow }
  if IE.IsConstant then Exit;             { immortal literal data }
  if (not IE.IsGlobal) and (IE.ParamMode = pmNone) and
     (IE.ImplicitFieldInfo = nil) and not Self.IsCaptured(IE.Name) then
    { Plain non-captured local: the frame's own reference outlives the call,
      UNLESS a var/out string sibling param can free it mid-call (F(L, L)). }
    Exit(APinPlain);
  { global, const/by-value/var param read, implicit-Self field, captured
    local — aliasable; the frame does not guarantee liveness across the call. }
  Result := True;
end;

procedure TArm64Backend.EmitRecordBaseAddr(const AReg, AName: string;
  AIsVarParam: Boolean);
begin
  if AIsVarParam and not Self.IsByValueRecordParam(AName) then
    EmitLoadSlot(AReg, AName)          { true var/out: slot holds caller addr }
  else
    EmitSlotAddr(AReg, AName);         { inline value: local/global/by-value }
end;

procedure TArm64Backend.ReservePendRelSlots;
var
  I: Integer;
begin
  { one 8-byte frame slot per PENDREL_SLOTS, reserved in every frame.  Called
    from RegisterFrameSlots and the _main/init/final frame setup so the
    deferred-release slots exist wherever a leaf statement might defer. }
  for I := 0 to PENDREL_SLOTS - 1 do
    AddLocal(Format('_pendrel_%d', [I]), 8);
  FPendingRelCount := 0;
  { Owned-string-transient CALL-ARG park slots (x29-relative, STABLE across the
    call's own arg pushes/pops and the post-call result spills).  A call parks
    each owned-string-transient arg here pre-call and reloads it post-call for
    its single dispose.  Previously these were kept in sp-relative outgoing-area
    slots, whose offset the arg pushes AND the result/d0 spills perturbed — the
    reload read a NEIGHBOURING (borrowed) string and freed it, poisoning the
    allocator (BUG-20260724-arm64-transient-arg-reload-off / classes-emit UAF).
    A fixed x29-relative pool sidesteps all sp arithmetic. }
  for I := 0 to STRTRANS_SLOTS - 1 do
    AddLocal(Format('__strtrans_%d', [I]), 8);
  { Jumbo-set operator destination.  ONE fixed frame slot, reserved in every
    frame and reused, so a set operation inside a loop costs nothing — see
    EmitJumboSetOp for why a per-evaluation sp-lowering leaks the stack there.
    JUMBO_SCRATCH_BYTES covers the widest jumbo set (a set's bitmap is capped
    at 32 bytes = 256 members), so one slot fits every instantiation. }
  AddLocal('_jset_scratch', JUMBO_SCRATCH_BYTES);
end;

function TArm64Backend.DeferNativeClassRelease: Boolean;
begin
  { record the owned-transient base pointer (in x0) into the next free
    _pendrel slot; the caller keeps the borrowed field value.  Returns False
    when all slots are in use — the caller then falls back to the AddRef-pin. }
  if FPendingRelCount >= PENDREL_SLOTS then
  begin
    Result := False;
    Exit;
  end;
  EmitStoreSlot('x0', Format('_pendrel_%d', [FPendingRelCount]));
  FPendingRelCount := FPendingRelCount + 1;
  Result := True;
end;

procedure TArm64Backend.FlushNativePendingReleases(AMark: Integer);
begin
  { LIFO-release every base deferred since the mark, resetting the count.
    Emitted at the leaf-statement boundary where x0 is free. }
  while FPendingRelCount > AMark do
  begin
    FPendingRelCount := FPendingRelCount - 1;
    EmitLoadSlot('x0', Format('_pendrel_%d', [FPendingRelCount]));
    EmitCallSym('_ClassRelease');
  end;
end;

procedure TArm64Backend.EmitTlvAddr(const ASym: string);
begin
  { Mach-O TLV access: get the descriptor's address, load its thunk (dyld
    resolved it to _tlv_get_addr at bind time) and call it with x0 =
    &descriptor; the thunk returns the per-thread address in x0.  Clobbers
    caller-saved registers, like any call.

    ADDRESS-OF, not load-through-a-slot: adrp + ADD with PLAIN @PAGE/@PAGEOFF.
    The descriptor is always defined in THIS image (we emit every TLV we use), so
    its address can be formed directly and no indirection slot is needed.

    Two earlier rounds each got half of this right, and the pairing is the whole
    point — the ADD and the PLAIN relocation must change together:

      * adrp+ADD with @TLVPPAGEOFF: ld rejects it outright, because
        ARM64_RELOC_TLVP_LOAD_PAGEOFF12 is defined to sit on a LOAD ("relocation
        on non-LDR instruction").  That is BUG-20260726-arm64-tlv-nonldr-reloc.
      * adrp+LDR with @TLVPPAGEOFF (Apple's canonical form): correct ONLY if the
        linker either materialises a __thread_ptrs slot or RELAXES the load into
        an add.  Ours relaxes; Apple's ld did NEITHER for our objects — it
        resolved the TLVP reloc directly, leaving `ldr x0,[x0,#off]` reading the
        descriptor's FIRST WORD instead of its address.  One dereference too
        many, so `blr x9` jumped through the thunk pointer's contents.  Verified
        by disassembling both binaries: the internal link shows
        `add x0, x0, #0x9d8`, the cc link `ldr x0, [x0, #0x278]`.  That is why
        cc-linked binaries — native AND qbe — segfaulted before reaching main.

    Plain @PAGE/@PAGEOFF needs no relaxation and no slot, so BOTH linkers agree.
    Confirmed on hardware: assembling this sequence with clang, linking with cc
    and running it returns cleanly.  See ARM64_TLS_SEGFAULT_FEEDBACK.md for the
    original evidence chain. }
  Self.Emit(Format(#9'adrp x0, _tv_%s@PAGE', [ASym]));
  Self.Emit(Format(#9'add x0, x0, _tv_%s@PAGEOFF', [ASym]));
  Self.Emit(#9'ldr x9, [x0]');
  Self.Emit(#9'blr x9');
end;

function TArm64Backend.EmitCapturedBase(const AReg, AName: string;
  AWantValue, AIsVarParam: Boolean): Boolean;
{ leg 19: when AName is a variable CAPTURED from an enclosing routine and used
  as a field-access base / method-call receiver, load it through its hidden
  '_cap_<Name>' pointer slot instead of the (non-existent) bare frame slot.
  The '_cap_' slot holds &<Name>.
    AWantValue=True  -> AReg receives the VALUE stored in <Name> (one deref) —
                        e.g. a class instance pointer held by a class-typed
                        capture.  A captured var-param needs a further deref
                        (its storage holds the caller's address).
    AWantValue=False -> AReg receives the ADDRESS of <Name>'s storage (the
                        '_cap_' value itself) — e.g. a captured RECORD base;
                        a captured var-param derefs once to the caller's addr.
  Returns True when it handled the load (AName was captured), False otherwise
  so the caller runs its normal bare path.  Mirrors x86-64 EmitVarBaseToReg. }
begin
  Result := False;
  if not IsCaptured(AName) then Exit;
  EmitLoadSlot(AReg, '_cap_' + AName);
  if AWantValue then
  begin
    Self.Emit(Format(#9'ldr %s, [%s]', [AReg, AReg]));
    if AIsVarParam then
      Self.Emit(Format(#9'ldr %s, [%s]', [AReg, AReg]));
  end
  else if AIsVarParam then
    Self.Emit(Format(#9'ldr %s, [%s]', [AReg, AReg]));
  Result := True;
end;

procedure TArm64Backend.EmitLoadSlot(const AReg, AName: string);
var
  Off: Integer;
  Sym: string;
begin
  if FFrame.TryGetValue(AName, Off) then
  begin
    if Off <= 256 then
      Self.Emit(Format(#9'ldur %s, [x29, #-%d]', [AReg, Off]))
    else
    begin
      EmitAddSubImm('sub', 'x9', 'x29', Off);
      Self.Emit(Format(#9'ldr %s, [x9]', [AReg]));
    end;
    Exit;
  end;
  Sym := GlobalSym(AName);
  if FTlvGlobals.IndexOf(Sym) >= 0 then
  begin
    EmitTlvAddr(Sym);
    Self.Emit(Format(#9'ldr %s, [x0]', [AReg]));
    Exit;
  end;
  if (FGlobalNames.IndexOf(Sym) >= 0) or
     IsSymTableVar(AName) then
  begin
    { registered here, or a cross-unit variable defined in a dependency's
      object — the assembler emits a reloc for the undefined symbol }
    Self.Emit(Format(#9'adrp x9, _g_%s@PAGE', [Sym]));
    Self.Emit(Format(#9'ldr %s, [x9, _g_%s@PAGEOFF]', [AReg, Sym]));
    Exit;
  end;
  NotYet('load of variable ''' + AName + '''', nil);
end;

procedure TArm64Backend.EmitStoreByWidth(const AValReg, AAddrReg: string;
  AType: TTypeDesc);
var
  W: Integer;
begin
  { A frame SLOT is always 8 bytes, so a store into one can be full width.
    Storage that is only as wide as its declared type cannot: writing 8 bytes
    into a 4-byte Integer overwrites the 4 bytes after it.  AType = nil means
    the caller could not resolve a width — keep the full-width store rather
    than guess narrow, which would leave the upper bytes stale. }
  if AType = nil then
  begin
    Self.Emit(Format(#9'str %s, [%s]', [AValReg, AAddrReg]));
    Exit;
  end;
  W := AType.RawSize();
  case W of
    1: Self.Emit(Format(#9'strb w%s, [%s]',
         [Copy(AValReg, 1, Length(AValReg) - 1), AAddrReg]));
    2: Self.Emit(Format(#9'strh w%s, [%s]',
         [Copy(AValReg, 1, Length(AValReg) - 1), AAddrReg]));
    4: Self.Emit(Format(#9'str w%s, [%s]',
         [Copy(AValReg, 1, Length(AValReg) - 1), AAddrReg]));
  else
    Self.Emit(Format(#9'str %s, [%s]', [AValReg, AAddrReg]));
  end;
end;

{ True when AExpr is a var/out argument whose storage is a plain 8-byte
  variable SLOT holding a sub-64-bit integer — the only shape that needs
  re-widening after the callee's narrow store.  The three excluded forms are the
  ones EmitRecIdentAddr routes away from EmitSlotAddr: a var-param forward (the
  slot holds the caller's ADDRESS), a captured variable (reached via '_cap_'),
  and an implicit-Self field (no slot exists for it).  The captured case is
  screened in EmitNormaliseNarrowSlot, which can reach IsCaptured. }
function IsRewidenableVarSlot(AExpr: TASTExpr): Boolean;
begin
  Result := False;
  if not (AExpr is TIdentExpr) then Exit;
  if AExpr.ResolvedType = nil then Exit;
  if not IsIntFam(AExpr.ResolvedType) then Exit;
  if AExpr.ResolvedType.RawSize() >= 8 then Exit;
  if TIdentExpr(AExpr).ParamMode = pmVar then Exit;
  if TIdentExpr(AExpr).IsImplicitSelf and
     (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then Exit;
  Result := True;
end;

procedure TArm64Backend.EmitNormaliseNarrowSlot(const AName: string;
  AType: TTypeDesc);
var
  W: Integer;
  Sh: Integer;
begin
  { A frame slot (and a scalar global — both are 8 bytes, .balign 8/.zero 8) is
    READ 64-bit wide by EmitLoadSlot, but a callee writing through a var/out
    parameter stores only the declared width, as the ABI requires: the target may
    be a 4-byte record field, and writing 8 bytes there corrupts the next field
    (BUG-20260726-arm64-varparam-store-width).  When the target IS a full slot,
    that leaves the slot's upper bytes stale, so the next 64-bit read of the
    variable yields a value that is right in 32 bits and wrong in 64 —
    comparisons still worked while WriteLn/Format/Int64() printed a zero-extended
    number (BUG-20260726-arm64-varparam-slot-not-rewidened).
    So after such a call the slot is re-widened here, from the width and
    signedness the variable actually has. }
  if AType = nil then Exit;
  W := AType.RawSize();
  if W >= 8 then Exit;
  { a captured variable has no bare frame slot — it is reached through '_cap_',
    and EmitSlotAddr would mistake the name for a global }
  if IsCaptured(AName) then Exit;
  EmitSlotAddr('x9', AName);
  if W = 4 then
  begin
    if IsUnsignedIntA64(AType) then
      Self.Emit(#9'ldr w0, [x9]')      { zero-extends into x0 }
    else
      Self.Emit(#9'ldrsw x0, [x9]');
    Self.Emit(#9'str x0, [x9]');
    Exit;
  end;
  { 1- and 2-byte: only the zero-extending loads exist (there is no ldrsb/ldrsh
    in the internal assembler), so a signed narrow type is sign-extended with the
    shift pair — lsl to put its sign bit at bit 63, asr to smear it back. }
  if W = 2 then
  begin
    Self.Emit(#9'ldrh w0, [x9]');
    Sh := 48;
  end
  else
  begin
    Self.Emit(#9'ldrb w0, [x9]');
    Sh := 56;
  end;
  if not IsUnsignedIntA64(AType) then
  begin
    Self.Emit(Format(#9'lsl x0, x0, #%d', [Sh]));
    Self.Emit(Format(#9'asr x0, x0, #%d', [Sh]));
  end;
  Self.Emit(#9'str x0, [x9]');
end;

procedure TArm64Backend.EmitStoreSlot(const AReg, AName: string);
var
  Off: Integer;
  Sym: string;
begin
  if FFrame.TryGetValue(AName, Off) then
  begin
    if Off <= 256 then
      Self.Emit(Format(#9'stur %s, [x29, #-%d]', [AReg, Off]))
    else
    begin
      EmitAddSubImm('sub', 'x9', 'x29', Off);
      Self.Emit(Format(#9'str %s, [x9]', [AReg]));
    end;
    Exit;
  end;
  Sym := GlobalSym(AName);
  if FTlvGlobals.IndexOf(Sym) >= 0 then
  begin
    { park the value across the thunk call }
    Self.Emit(Format(#9'str %s, [sp, #-16]!', [AReg]));
    EmitTlvAddr(Sym);
    Self.Emit(#9'mov x9, x0');
    Self.Emit(#9'ldr x0, [sp], #16');
    Self.Emit(#9'str x0, [x9]');
    Exit;
  end;
  if (FGlobalNames.IndexOf(Sym) >= 0) or
     IsSymTableVar(AName) then
  begin
    Self.Emit(Format(#9'adrp x9, _g_%s@PAGE', [Sym]));
    Self.Emit(Format(#9'str %s, [x9, _g_%s@PAGEOFF]', [AReg, Sym]));
    Exit;
  end;
  NotYet('store to variable ''' + AName + '''', nil);
end;

procedure TArm64Backend.EmitSlotAddr(const AReg, AName: string);
var
  Off: Integer;
  Sym: string;
begin
  if FFrame.TryGetValue(AName, Off) then
  begin
    EmitAddSubImm('sub', AReg, 'x29', Off);
    Exit;
  end;
  Sym := GlobalSym(AName);
  if FTlvGlobals.IndexOf(Sym) >= 0 then
  begin
    EmitTlvAddr(Sym);
    if AReg <> 'x0' then
      Self.Emit(Format(#9'mov %s, x0', [AReg]));
    Exit;
  end;
  if (FGlobalNames.IndexOf(Sym) >= 0) or
     IsSymTableVar(AName) then
  begin
    Self.Emit(Format(#9'adrp %s, _g_%s@PAGE', [AReg, Sym]));
    Self.Emit(Format(#9'add %s, %s, _g_%s@PAGEOFF', [AReg, AReg, Sym]));
    Exit;
  end;
  NotYet('address of variable ''' + AName + '''', nil);
end;

procedure TArm64Backend.EmitRecIdentAddr(const AReg: string; AE: TIdentExpr);
begin
  { address of a record-valued identifier: a captured outer var's '_cap_'
    slot IS its address (leg 17); an implicit-Self FIELD lives at Self +
    field offset (no frame slot exists for it); a var param's slot holds the
    caller's address; everything else is a frame slot }
  if IsCaptured(AE.Name) then
  begin
    EmitLoadSlot(AReg, '_cap_' + AE.Name);
    if AE.ParamMode = pmVar then
      Self.Emit(Format(#9'ldr %s, [%s]', [AReg, AReg]));
    Exit;
  end;
  if AE.IsImplicitSelf and (AE.ImplicitFieldInfo <> nil) then
  begin
    EmitLoadSlot(AReg, 'Self');
    if TFieldInfo(AE.ImplicitFieldInfo).Offset <> 0 then
      EmitAddSubImm('add', AReg, AReg,
        TFieldInfo(AE.ImplicitFieldInfo).Offset);
    Exit;
  end;
  if AE.ParamMode = pmVar then
  begin
    EmitLoadSlot(AReg, AE.Name);
    Exit;
  end;
  EmitSlotAddr(AReg, AE.Name);
end;

procedure TArm64Backend.EmitRecFieldAddrToX0(AFA: TFieldAccessExpr);
begin
  { x0 := ADDRESS of the record VALUE named by a field access — the
    base for a chained read like FTok.Token.TextStart, where Token is a
    record-typed field and the outer access needs its address }
  if AFA.FieldInfo = nil then
    NotYet('address of an unresolved field', AFA);
  { record-typed ELEMENT of an array field (Obj.ArrField[I] as an rvalue, e.g.
    Sec.Relocs[J]): the field itself is an array, not the record — its element
    address needs the subscript scaled in AND, for a dynarray field, the data
    pointer DEREFERENCED.  EmitFieldElemAddr does exactly that.  Falling through
    to the plain-field path below yields &field-slot (missing both the deref and
    the index), which reads the dynarray header/neighbouring fields as the
    record — the arm64-only store/read asymmetry behind the Mach-O writer's
    corrupt-reloc crash (macOS arm64, 2026-07-24). }
  if AFA.IsArrayAccess then
  begin
    EmitFieldElemAddr(AFA);
    Exit;
  end;
  if AFA.Base <> nil then
  begin
    if AFA.IsClassAccess then
    begin
      { chained CLASS base: the base expression yields the instance pointer }
      if ArcExprOwnsRef(AFA.Base) then
        NotYet('record address on an owned transient base', AFA);
      Self.EmitExprToX0(AFA.Base);
    end
    else if (AFA.Base.ResolvedType <> nil) and
            (AFA.Base.ResolvedType.Kind = tyRecord) then
      { chained RECORD-field base (leg 24): the base is itself a record-typed
        field/ident/element — recurse to its ADDRESS (no deref), then add this
        field's offset.  Handles Rec.RecField.Field / A.B.C. }
      EmitRecAddrToX0(AFA.Base)
    else
      NotYet('record address through this base form', AFA);
  end
  else if AFA.IsImplicitSelf then
    EmitLoadSlot('x0', 'Self')
  else if AFA.IsClassAccess then
    EmitLoadSlot('x0', AFA.RecordName)
  else
    { TRUE var/out record: slot holds the CALLER's record ADDRESS — deref it
      (leg 27), then add the field offset.  A BY-VALUE record param also has
      IsVarParam=True (records pass by reference in the ABI) but its inline copy
      lives in the ParamName slot — the '__pptr_' discriminator in
      EmitRecordBaseAddr keeps the two apart (was a double-deref). }
    EmitRecordBaseAddr('x0', AFA.RecordName, AFA.IsVarParam);
  { Step across the intermediate field for a nested Self.FIntermediate.SubField
    path — add for an embedded record, deref for a class reference (kept in
    step with the load and store paths via EmitImplicitBaseStep). }
  if AFA.IsImplicitSelf then
    EmitImplicitBaseStep('x0', AFA.ImplicitBaseInfo);
  if AFA.FieldInfo.Offset <> 0 then
    EmitAddSubImm('add', 'x0', 'x0', AFA.FieldInfo.Offset);
end;

procedure TArm64Backend.EmitInstBase(const AReg, AInstSlot: string;
  AInstVarParam: Boolean);
begin
  { the instance pointer for a field store lives in AInstSlot ('Self' or a
    class var).  When that var is CAPTURED from an enclosing routine (leg 19),
    it has no bare frame slot — go through '_cap_' and deref to the pointer.
    A captured VAR-PARAM class base needs a further deref (its storage holds
    the caller's address), so AInstVarParam is threaded into the capture path.
    The non-captured fallthrough keeps its original behaviour (the bare slot
    already holds the instance pointer for the forms that reach here). }
  if not EmitCapturedBase(AReg, AInstSlot, True, AInstVarParam) then
    EmitLoadSlot(AReg, AInstSlot);
  { Nested Self.FIntermediate.SubField: fold the intermediate into the base —
    add its offset for an embedded record, deref for a class reference. }
  EmitImplicitBaseStep(AReg, ABaseInfo);
end;

{ Store the value on TOP of the stack (left there) into the non-owning
  class field AFld of the instance at ABase: a plain store for
  [Unretained], _WeakAssign(slot, value) for [Weak].  No refcount moves. }
procedure TArm64Backend.EmitNonOwningFieldStore(AFld: TFieldInfo;
  const ABase: string);
begin
  if AFld.IsWeak then
  begin
    if AFld.Offset <> 0 then
      EmitAddSubImm('add', 'x0', ABase, AFld.Offset)
    else
      Self.Emit(Format(#9'mov x0, %s', [ABase]));
    Self.Emit(#9'ldr x1, [sp]');
    EmitCallSym('_WeakAssign');
  end
  else
  begin
    Self.Emit(#9'ldr x0, [sp]');
    Self.Emit(Format(#9'str x0, [%s, #%d]', [ABase, AFld.Offset]));
  end;
end;

procedure TArm64Backend.EmitInstanceFieldStore(AFld: TFieldInfo;
  AValueExpr: TASTExpr; const AInstSlot: string; AInstVarParam: Boolean;
  ABaseInfo: TFieldInfo);
var
  I, Shape: Integer;
  Off: Integer;
begin
  { The base register already includes the intermediate (EmitInstBase applied
    EmitImplicitBaseStep), so only the sub-field's own offset remains. }
  Off := AFld.Offset;
  { store AValueExpr into AFld of the instance whose POINTER lives in the
    frame slot AInstSlot ('Self' or a class-typed variable).  Managed
    fields run the retain/release discipline; the instance pointer is
    re-loaded after any release call (it clobbers scratch regs). }
  if (AFld.TypeDesc.Kind = tyClass) and (AFld.IsUnretained or AFld.IsWeak) then
  begin
    { a NON-OWNING field takes no reference and drops none: a plain store
      ([Unretained]) or the weak-table registration ([Weak]).  An owned +1
      value (a call result) has no other owner, so it is released once the
      store is done (x86-64 / QBE parity). }
    Self.EmitExprToX0(AValueExpr);
    EmitPushX0();                       { [value] }
    EmitInstBase('x9', AInstSlot, AInstVarParam, ABaseInfo);
    EmitNonOwningFieldStore(AFld, 'x9');
    EmitPopTo('x0');
    if ArcExprOwnsRef(AValueExpr) then
      EmitCallSym('_ClassRelease');
    Exit;
  end;
  if AFld.TypeDesc.IsString() or (AFld.TypeDesc.Kind = tyClass) then
  begin
    Self.EmitExprToX0(AValueExpr);
    if (AFld.TypeDesc.IsString() and not ArcExprOwnsRef(AValueExpr)) or
       ((AFld.TypeDesc.Kind = tyClass) and
        not ArcExprOwnsRef(AValueExpr)) then
    begin
      EmitPushX0();
      if AFld.TypeDesc.IsString() then
        EmitCallSym('_StringAddRef')
      else
        EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();
    EmitInstBase('x9', AInstSlot, AInstVarParam, ABaseInfo);
    Self.Emit(Format(#9'ldr x0, [x9, #%d]', [Off]));
    if AFld.TypeDesc.IsString() then
      EmitCallSym('_StringRelease')
    else
      EmitCallSym('_ClassRelease');
    EmitInstBase('x9', AInstSlot, AInstVarParam, ABaseInfo);
    EmitPopTo('x0');
    Self.Emit(Format(#9'str x0, [x9, #%d]', [Off]));
    Exit;
  end;
  if AFld.TypeDesc.Kind = tyRecord then
  begin
    if ((AValueExpr is TFuncCallExpr) and
        (TFuncCallExpr(AValueExpr).ResolvedDecl <> nil)) or
       ((AValueExpr is TMethodCallExpr) and
        (TMethodCallExpr(AValueExpr).ResolvedMethod <> nil) and
        not TMethodCallExpr(AValueExpr).IsConstructorCall) then
    begin
      { record-returning call into a field: land the fresh value in the
        __rret scratch, release the field's OLD refs, then memcpy in —
        the callee's +1 field refs TRANSFER (no source retain) }
      Shape := RecReturnShape(TRecordTypeDesc(AFld.TypeDesc));
      if Shape = 0 then
        EmitRecCallDispatch(AValueExpr, '__rret')
      else
      begin
        EmitRecCallDispatch(AValueExpr, '');
        EmitSlotAddr('x9', '__rret');
        case Shape of
          1: Self.Emit(#9'str x0, [x9]');
          2:
          begin
            Self.Emit(#9'str x0, [x9]');
            Self.Emit(#9'str x1, [x9, #8]');
          end;
        else
          for I := 0 to (Shape - 100) - 1 do
            Self.Emit(Format(#9'str d%d, [x9, #%d]', [I, I * 8]));
        end;
      end;
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      EmitInstBase('x22', AInstSlot, AInstVarParam, ABaseInfo);
      if Off <> 0 then
        EmitAddSubImm('add', 'x22', 'x22', Off);
      if not RecretManagedClean(TRecordTypeDesc(AFld.TypeDesc)) then
        Self.EmitRecordFieldReleases(TRecordTypeDesc(AFld.TypeDesc), 'x22');
      Self.Emit(#9'mov x0, x22');
      EmitSlotAddr('x1', '__rret');
      EmitIntLiteral('x2', AFld.TypeDesc.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Exit;
    end;
    { record-typed field store: memcpy from the source record's address;
      managed fields retain-source then release-dest (record-assign rule) }
    if not RecretManagedClean(TRecordTypeDesc(AFld.TypeDesc)) then
    begin
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      EmitRecAddrToX0(AValueExpr);
      Self.Emit(#9'mov x19, x0');
      EmitInstBase('x22', AInstSlot, AInstVarParam, ABaseInfo);
      if Off <> 0 then
        EmitAddSubImm('add', 'x22', 'x22', Off);
      Self.EmitRecordFieldRetains(TRecordTypeDesc(AFld.TypeDesc), 'x19');
      { copy site: no-zero release keeps a self-copy exact
        (BUG-20260720-managed-record-self-assign) }
      Self.EmitRecordFieldReleases(TRecordTypeDesc(AFld.TypeDesc), 'x22', False);
      Self.Emit(#9'mov x0, x22');
      Self.Emit(#9'mov x1, x19');
      EmitIntLiteral('x2', AFld.TypeDesc.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Exit;
    end;
    EmitRecAddrToX0(AValueExpr);
    EmitPushX0();
    EmitInstBase('x0', AInstSlot, AInstVarParam, ABaseInfo);
    if Off <> 0 then
      EmitAddSubImm('add', 'x0', 'x0', Off);
    EmitPopTo('x1');
    EmitIntLiteral('x2', AFld.TypeDesc.RawSize());
    EmitCallSym('memcpy');
    Exit;
  end;
  if AFld.TypeDesc.Kind = tySingle then
  begin
    Self.EmitExprToD0OrConvert(AValueExpr);
    Self.Emit(#9'fcvt s0, d0');
    EmitInstBase('x9', AInstSlot, AInstVarParam, ABaseInfo);
    Self.Emit(Format(#9'str s0, [x9, #%d]', [Off]));
    Exit;
  end;
  if AFld.TypeDesc.Kind = tyDouble then
  begin
    Self.EmitExprToD0OrConvert(AValueExpr);
    Self.Emit(#9'fmov x0, d0');
  end
  else if IsIntFam(AFld.TypeDesc) or
          (AFld.TypeDesc.Kind in [tyPointer, tyPChar]) then
    Self.EmitExprToX0(AValueExpr)
  else
  begin
    { every other field kind (closure / method pointer, plain procedural,
      dyn array, metaclass, small set, non-managed record) is handled by the
      stacked store: put the instance base on the stack and delegate }
    EmitInstBase('x0', AInstSlot, AInstVarParam, ABaseInfo);
    EmitPushX0();
    EmitInstanceFieldStoreStacked(AFld, AValueExpr);
    Exit;
  end;
  EmitPushX0();
  EmitInstBase('x9', AInstSlot, AInstVarParam, ABaseInfo);
  EmitPopTo('x0');
  { width-keyed store: a 4-byte field at a 4-aligned offset would fault
    the scaled 8-byte form, and an 8-byte store would trash the neighbour }
  case AFld.TypeDesc.RawSize() of
    1: Self.Emit(Format(#9'strb w0, [x9, #%d]', [Off]));
    2: Self.Emit(Format(#9'strh w0, [x9, #%d]', [Off]));
    4: Self.Emit(Format(#9'str w0, [x9, #%d]', [Off]));
  else
    Self.Emit(Format(#9'str x0, [x9, #%d]', [Off]));
  end;
end;

procedure TArm64Backend.EmitInstanceFieldStoreStacked(AFld: TFieldInfo;
  AValueExpr: TASTExpr);
var
  NB: Integer;
begin
  { like EmitInstanceFieldStore, but the instance pointer is on TOP of the
    stack (pushed by the caller); consumed on exit.  Needed for chained
    bases (A.B.C := v), which have no frame slot to re-derive from. }
  if IsMethodPtrType(AFld.TypeDesc) then
  begin
    EmitFatFieldStoreStacked(AFld, AValueExpr);
    Exit;
  end;
  if AFld.TypeDesc.Kind = tyInterface then
  begin
    EmitIntfStoreStacked(AFld.Offset, AValueExpr, AFld.TypeDesc);
    Exit;
  end;
  if ((AFld.TypeDesc.Kind = tyRecord) or (AFld.TypeDesc.Kind = tyStaticArray)) and
     not AggHasManaged(AFld.TypeDesc) then
  begin
    { a non-managed aggregate field: copy its bytes from the value's address }
    EmitRecAddrToX0(AValueExpr);
    Self.Emit(#9'mov x1, x0');
    Self.Emit(#9'ldr x0, [sp], #16');   { pop the base }
    if AFld.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0', AFld.Offset);
    EmitIntLiteral('x2', AFld.TypeDesc.RawSize());
    EmitCallSym('memcpy');
    Exit;
  end;
  if (AFld.TypeDesc.Kind = tyClass) and (AFld.IsUnretained or AFld.IsWeak) then
  begin
    { non-owning field -- see EmitInstanceFieldStore }
    Self.EmitExprToX0(AValueExpr);
    EmitPushX0();                       { [base][value] }
    Self.Emit(#9'ldr x9, [sp, #16]');
    EmitNonOwningFieldStore(AFld, 'x9');
    EmitPopTo('x0');
    if ArcExprOwnsRef(AValueExpr) then
      EmitCallSym('_ClassRelease');
    Self.Emit(#9'add sp, sp, #16');     { drop the base }
    Exit;
  end;
  if AFld.TypeDesc.IsString() or (AFld.TypeDesc.Kind = tyClass) or
     (AFld.TypeDesc.Kind = tyDynArray) then
  begin
    Self.EmitExprToX0(AValueExpr);
    if not ArcExprOwnsRef(AValueExpr) then
    begin
      EmitPushX0();
      if AFld.TypeDesc.IsString() then
        EmitCallSym('_StringAddRef')
      else if AFld.TypeDesc.Kind = tyDynArray then
        EmitCallSym('_DynArrayAddRef')
      else
        EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();                       { [base][value] }
    Self.Emit(#9'ldr x9, [sp, #16]');
    Self.Emit(Format(#9'ldr x0, [x9, #%d]', [AFld.Offset]));
    if AFld.TypeDesc.IsString() then
      EmitCallSym('_StringRelease')
    else if AFld.TypeDesc.Kind = tyDynArray then
      EmitCallSym('_DynArrayRelease')
    else
      EmitCallSym('_ClassRelease');
    Self.Emit(#9'ldr x9, [sp, #16]');
    EmitPopTo('x0');
    Self.Emit(Format(#9'str x0, [x9, #%d]', [AFld.Offset]));
    Self.Emit(#9'add sp, sp, #16');     { drop the base }
    Exit;
  end;
  if AFld.TypeDesc.Kind = tySingle then
  begin
    Self.EmitExprToD0OrConvert(AValueExpr);
    Self.Emit(#9'fcvt s0, d0');
    Self.Emit(#9'ldr x9, [sp], #16');   { pop the base }
    Self.Emit(Format(#9'str s0, [x9, #%d]', [AFld.Offset]));
    Exit;
  end;
  if (AFld.TypeDesc is TSetTypeDesc) and
     TSetTypeDesc(AFld.TypeDesc).IsJumbo() then
  begin
    { a JUMBO set field is an inline bitmap and its value evaluates to an
      ADDRESS: copy the bitmap in.  A literal value materialises its bitmap
      below sp (EmitJumboSetLiteral's contract), so the parked base sits
      that many bytes further up, and the caller restores sp afterwards. }
    NB := JumboSetLiteralBytes(AValueExpr);
    Self.EmitExprToX0(AValueExpr);                 { source bitmap address }
    Self.Emit(#9'mov x1, x0');
    Self.Emit(Format(#9'ldr x0, [sp, #%d]', [NB]));
    if AFld.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0', AFld.Offset);
    EmitIntLiteral('x2', AFld.TypeDesc.RawSize());
    EmitCallSym('memcpy');
    EmitAddSubImm('add', 'sp', 'sp', NB + 16);    { literal buffer + base }
    Exit;
  end;
  if AFld.TypeDesc.Kind = tyDouble then
  begin
    Self.EmitExprToD0OrConvert(AValueExpr);
    Self.Emit(#9'fmov x0, d0');
  end
  else if IsIntFam(AFld.TypeDesc) or
          (AFld.TypeDesc.Kind in [tyPointer, tyPChar, tyMetaClass,
                                  tyProcedural]) or
          IsSmallSetType(AFld.TypeDesc) then
    { (a plain procedural field is one code word; the fat closure /
      method-pointer kind was routed above) }
    Self.EmitExprToX0(AValueExpr)
  else
    NotYet('store to a field of this type', AValueExpr);
  Self.Emit(#9'ldr x9, [sp], #16');     { pop the base }
  case AFld.TypeDesc.RawSize() of
    1: Self.Emit(Format(#9'strb w0, [x9, #%d]', [AFld.Offset]));
    2: Self.Emit(Format(#9'strh w0, [x9, #%d]', [AFld.Offset]));
    4: Self.Emit(Format(#9'str w0, [x9, #%d]', [AFld.Offset]));
  else
    Self.Emit(Format(#9'str x0, [x9, #%d]', [AFld.Offset]));
  end;
end;

procedure TArm64Backend.EmitImplicitSelfStore(AAsgn: TAssignment);
begin
  EmitInstanceFieldStore(TFieldInfo(AAsgn.ImplicitSelfField), AAsgn.Expr,
    'Self', False);
end;

procedure TArm64Backend.EmitRecAddrToX0(AExpr: TASTExpr);
begin
  { x0 := address of a record VALUE — every lvalue-ish record shape the
    copy paths accept: plain/var-param/implicit-Self idents, subscripted
    elements, and record-typed field accesses }
  if RecordPropRead(AExpr) <> nil then
  begin
    { a record-typed property (L[I] on a TList<TRec>): its getter's value }
    EmitRecPropToTemp(RecordPropRead(AExpr));
    Exit;
  end;
  if AExpr is TIdentExpr then
  begin
    EmitRecIdentAddr('x0', TIdentExpr(AExpr));
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) then
  begin
    case TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind of
      tyStaticArray:
        EmitStaticElemAddr(TStringSubscriptExpr(AExpr));
      tyDynArray, tyOpenArray:
        EmitDynElemAddr(TStringSubscriptExpr(AExpr));
    else
      NotYet('record address of this subscript base', AExpr);
    end;
    Exit;
  end;
  if AExpr is TFieldAccessExpr then
  begin
    EmitRecFieldAddrToX0(TFieldAccessExpr(AExpr));
    Exit;
  end;
  { P^ -- the record a pointer designates: its address is the pointer value
    (P^.Rec.Field, the fiber runtime's F^.Ctx.SP) }
  if AExpr is TDerefExpr then
  begin
    Self.EmitExprToX0(TDerefExpr(AExpr).Expr);
    Exit;
  end;
  NotYet('record address of this expression', AExpr);
end;

procedure TArm64Backend.EmitRecCallToRret(AExpr: TASTExpr);
var
  Shape, K: Integer;
  Tmp: string;
begin
  { materialise a record-returning call into a scratch and leave the
    scratch's ADDRESS in x0.  Shape 0 (>16B) sret's straight into it; the
    register-returned shapes store x0/x0:x1/d0.. into it.
    The scratch is a PER-SITE frame slot sized to this record (the frame grows
    lazily -- the body is buffered).  It used to be the shared __rret, which is
    only 16 bytes unless a managed-record assignment in the same body widened
    it: a larger unmanaged result (a 24-byte record's method receiver or field
    read) overran it into the neighbouring slot.  Per site also means two such
    calls in one expression keep separate results. }
  Tmp := '__rtmp_' + IntToStr(FJArgN);
  FJArgN := FJArgN + 1;
  if not FFrame.ContainsKey(Tmp) then
    AddLocal(Tmp, AExpr.ResolvedType.RawSize());
  Shape := RecReturnShape(TRecordTypeDesc(AExpr.ResolvedType));
  if Shape = 0 then
    EmitRecCallDispatch(AExpr, Tmp)
  else
  begin
    EmitRecCallDispatch(AExpr, '');
    EmitSlotAddr('x9', Tmp);
    case Shape of
      1: Self.Emit(#9'str x0, [x9]');
      2:
      begin
        Self.Emit(#9'str x0, [x9]');
        Self.Emit(#9'str x1, [x9, #8]');
      end;
    else
      for K := 0 to (Shape - 100) - 1 do
        Self.Emit(Format(#9'str d%d, [x9, #%d]', [K, K * 8]));
    end;
  end;
  EmitSlotAddr('x0', Tmp);
end;

procedure TArm64Backend.EmitPropRecvToX0(AStmt: TFieldAssignment);
begin
  { property-write receiver: a plain slot, a var param's pointee, or a
    FIELD of Self (FDefines.CaseSensitive := ...).  Step across the
    intermediate the same way every other implicit-Self path does — deref a
    class reference, add an embedded record's offset. }
  if AStmt.IsImplicitSelf and (AStmt.ImplicitBaseInfo <> nil) then
  begin
    EmitLoadSlot('x0', 'Self');
    EmitImplicitBaseStep('x0', AStmt.ImplicitBaseInfo);
    Exit;
  end;
  { a CHAINED receiver -- o.Inner.V := X: the instance is the value of the
    receiver expression (EmitFieldAssign rejects an owned-transient one,
    which would need a post-call release) }
  if AStmt.ObjExpr <> nil then
  begin
    Self.EmitExprToX0(AStmt.ObjExpr);
    Exit;
  end;
  EmitLoadSlot('x0', AStmt.RecordName);
  if AStmt.IsVarParam then
    Self.Emit(#9'ldr x0, [x0]');
end;

procedure TArm64Backend.EmitAnonValueToSlot(AME: TAnonMethodExpr);
begin
  if AME.ValueSlotName = '' then
    NotYet('anonymous method has no value slot', AME);
  EmitAnonValueInto(AME, AME.ValueSlotName);
end;

procedure TArm64Backend.EmitAnonValueInto(AME: TAnonMethodExpr;
  const ASlot: string);
var
  MD: TMethodDecl;
  Sym: string;
begin
  MD := TMethodDecl(AME.LiftedDecl);
  if MD = nil then
    NotYet('anonymous method not lifted (semantic pass required)', AME);
  { x9 := &slot; release the old Env half (nil-safe), then write Code and Env. }
  EmitSlotAddr('x9', ASlot);
  Self.Emit(#9'ldr x0, [x9, #8]');            { old Env }
  Self.Emit(#9'str x9, [sp, #-16]!');         { park &slot across the call }
  EmitCallSym('_ClassRelease');
  Self.Emit(#9'ldr x9, [sp], #16');
  Sym := RoutineSym(MD, '');
  Self.Emit(Format(#9'adrp x0, %s@PAGE', [Sym]));
  Self.Emit(Format(#9'add x0, x0, %s@PAGEOFF', [Sym]));
  Self.Emit(#9'str x0, [x9]');                { Code at +0 }
  if MD.EnvCaptured <> nil then
  begin
    { capturing closure: Env is the enclosing frame's env pointer (block env if
      the thunk names one), and the slot takes its own strong ref. }
    if MD.EnvSlotName <> '' then
      EmitLoadSlot('x0', MD.EnvSlotName)
    else
      EmitLoadSlot('x0', '__envp');
    Self.Emit(#9'str x0, [x9, #8]');          { Env at +8 }
    Self.Emit(#9'str x9, [sp, #-16]!');
    EmitCallSym('_ClassAddRef');
    Self.Emit(#9'ldr x9, [sp], #16');
  end
  else
    Self.Emit(#9'str xzr, [x9, #8]');         { capture-free: Env = nil }
  Self.Emit(#9'mov x0, x9');                  { yield the slot ADDRESS }
end;

procedure TArm64Backend.EmitFatPtrAssign(AAsgn: TAssignment);
var
  IsRef: Boolean;
  Src: TIdentExpr;
  Tmp: string;
  FAE: TFieldAccessExpr;
  MD: TMethodDecl;
  FldAddr: TAddrOfExpr;
begin
  { Closure ('reference to') / method-pointer ('of object') target: a 16-byte
    fat value, Code at +0 and Env/Data at +8.  The generic scalar path stored
    only an 8-byte word -- for a closure literal, the ADDRESS of its temp --
    so the call through the variable branched into data.  Mirrors the x86-64
    reference-to assignment arms.  A 'reference to' value co-owns its Env, so
    the old Env is released and a copied one retained; an 'of object' value
    holds its receiver unretained, as on x86-64. }
  if AAsgn.ImplicitSelfField <> nil then
  begin
    { FHandler := value inside a method: a 16-byte FIELD of Self -- the
      field-store machinery (EmitFatFieldStoreStacked) runs the same Env
      retain/release discipline against the instance }
    EmitImplicitSelfStore(AAsgn);
    Exit;
  end;
  if IsCaptured(AAsgn.Name) or AAsgn.IsVarParam then
    NotYet('closure / method-pointer assignment to this target', AAsgn);
  IsRef := (AAsgn.ResolvedLhsType.Kind = tyProcedural) and
           TProceduralTypeDesc(AAsgn.ResolvedLhsType).IsReference;
  if AAsgn.Expr is TAnonMethodExpr then
  begin
    { materialise the literal straight into the target (old Env released,
      captured Env retained -- EmitAnonValueInto) }
    EmitAnonValueInto(TAnonMethodExpr(AAsgn.Expr), AAsgn.Name);
    Exit;
  end;
  if AAsgn.Expr is TNilLiteral then
  begin
    EmitSlotAddr('x9', AAsgn.Name);
    if IsRef then
    begin
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');
      EmitSlotAddr('x9', AAsgn.Name);
    end;
    Self.Emit(#9'stp xzr, xzr, [x9]');
    Exit;
  end;
  if (AAsgn.Expr is TFieldAccessExpr) and
     IsMethodPtrType(AAsgn.Expr.ResolvedType) and
     (TFieldAccessExpr(AAsgn.Expr).FieldInfo <> nil) and
     not TFieldAccessExpr(AAsgn.Expr).IsMethodCall and
     (TFieldAccessExpr(AAsgn.Expr).PropRead = nil) then
  begin
    { F := Obj.FieldF / Obj.Rec.FieldF: address the 16-byte field through
      a transient @-wrapper, then copy it like a variable (Env retained
      before the old one is released) }
    FldAddr := TAddrOfExpr.Create();
    try
      FldAddr.Line := AAsgn.Line;
      FldAddr.Col := AAsgn.Col;
      FldAddr.Expr := AAsgn.Expr;
      Self.EmitExprToX0(FldAddr);
    finally
      FldAddr.Expr := nil;   { owned by the assignment }
      FldAddr.Free();
    end;
    EmitPushX0();                                { [&src] }
    if IsRef then
    begin
      Self.Emit(#9'ldr x0, [x0, #8]');
      EmitCallSym('_ClassAddRef');
      EmitSlotAddr('x9', AAsgn.Name);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');
    end;
    EmitPopTo('x1');
    Self.Emit(#9'ldp x9, x10, [x1]');
    EmitSlotAddr('x1', AAsgn.Name);
    Self.Emit(#9'stp x9, x10, [x1]');
    Exit;
  end;
  if (AAsgn.Expr is TIdentExpr) and IsMethodPtrType(AAsgn.Expr.ResolvedType) and
     not IsCaptured(TIdentExpr(AAsgn.Expr).Name) and
     (TIdentExpr(AAsgn.Expr).ParamMode = pmNone) and
     not TIdentExpr(AAsgn.Expr).IsImplicitSelf then
  begin
    { variable-to-variable copy: retain the incoming Env BEFORE releasing the
      old one, so F := F is safe; then copy both words }
    Src := TIdentExpr(AAsgn.Expr);
    if IsRef then
    begin
      EmitSlotAddr('x9', Src.Name);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassAddRef');
      EmitSlotAddr('x9', AAsgn.Name);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');
    end;
    EmitSlotAddr('x1', Src.Name);
    Self.Emit(#9'ldp x9, x10, [x1]');
    EmitSlotAddr('x1', AAsgn.Name);
    Self.Emit(#9'stp x9, x10, [x1]');
    Exit;
  end;
  if (AAsgn.Expr is TAddrOfExpr) and
     (TAddrOfExpr(AAsgn.Expr).Expr is TFieldAccessExpr) and
     (TFieldAccessExpr(TAddrOfExpr(AAsgn.Expr).Expr).ResolvedMethod is TMethodDecl) then
  begin
    { F := @Obj.Method: build the (Code, receiver) pair straight into the
      target -- the same layout as a closure whose Env is the receiver.  A
      virtual method resolves through the receiver's vtable, so @Obj.M
      captures the dynamic override exactly as a direct Obj.M() call would.
      A 'reference to' target takes a strong reference to the receiver and
      releases the old Env; an 'of object' target holds it unretained, as
      on x86-64. }
    FAE := TFieldAccessExpr(TAddrOfExpr(AAsgn.Expr).Expr);
    MD := TMethodDecl(FAE.ResolvedMethod);
    if MD.IsRecordMethod or MD.IsStatic or FAE.IsImplicitSelf then
      NotYet('method pointer to this method form', AAsgn);
    if IsRef then
    begin
      EmitSlotAddr('x9', AAsgn.Name);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');
    end;
    if FAE.Base <> nil then
    begin
      if ArcExprOwnsRef(FAE.Base) then
        NotYet('method pointer on an owned transient receiver', AAsgn);
      Self.EmitExprToX0(FAE.Base);
    end
    else if not EmitCapturedBase('x0', FAE.RecordName, True, False) then
      EmitLoadSlot('x0', FAE.RecordName);
    EmitPushX0();                              { [receiver] }
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'ldr x9, [x0]');             { vtable }
      Self.Emit(Format(#9'ldr x1, [x9, #%d]', [(MD.VTableSlot + 1) * 8]));
    end
    else
    begin
      Self.Emit(Format(#9'adrp x1, %s@PAGE', [RoutineSym(MD, '')]));
      Self.Emit(Format(#9'add x1, x1, %s@PAGEOFF', [RoutineSym(MD, '')]));
    end;
    EmitSlotAddr('x9', AAsgn.Name);
    EmitPopTo('x0');                           { receiver }
    Self.Emit(#9'stp x1, x0, [x9]');           { Code at +0, receiver at +8 }
    if IsRef then
      EmitCallSym('_ClassAddRef');
    Exit;
  end;
  if (AAsgn.Expr is TFuncCallExpr) and
     (TFuncCallExpr(AAsgn.Expr).ResolvedDecl is TMethodDecl) and
     not TFuncCallExpr(AAsgn.Expr).IsIndirectCall and
     not TFuncCallExpr(AAsgn.Expr).IsImplicitSelfMethod and
     (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).OwnerTypeName = '') and
     IsMethodPtrType(TMethodDecl(
       TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType) then
  begin
    { F := MakeClosure(...): the callee fills a fresh scratch through x8 and
      hands over its Env reference, so the old Env is released and the pair
      moved in WITHOUT a retain }
    Tmp := EmitClosureResultCall(
      TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl),
      TFuncCallExpr(AAsgn.Expr).Name, TFuncCallExpr(AAsgn.Expr).Args);
    if IsRef then
    begin
      EmitSlotAddr('x9', AAsgn.Name);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');
    end;
    EmitSlotAddr('x1', Tmp);
    Self.Emit(#9'ldp x9, x10, [x1]');
    EmitSlotAddr('x1', AAsgn.Name);
    Self.Emit(#9'stp x9, x10, [x1]');
    Exit;
  end;
  if (AAsgn.Expr is TMethodCallExpr) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedMethod is TMethodDecl) and
     not TMethodCallExpr(AAsgn.Expr).IsConstructorCall and
     not TMethodCallExpr(AAsgn.Expr).IsStaticCall and
     not TMethodCallExpr(AAsgn.Expr).IsProcFieldCall and
     not TMethodCallExpr(AAsgn.Expr).IsMetaclassDispatch and
     not TMethodDecl(TMethodCallExpr(AAsgn.Expr).ResolvedMethod).IsRecordMethod and
     IsMethodPtrType(TMethodDecl(
       TMethodCallExpr(AAsgn.Expr).ResolvedMethod).ResolvedReturnType) then
  begin
    { F := Obj.MakeClosure(...): as for a plain factory call, the callee
      fills a fresh scratch through x8 and hands over its Env reference; the
      receiver is pushed for EmitCall to pop into x0 (virtual dispatch keys
      on the method's VTableSlot) }
    MD := TMethodDecl(TMethodCallExpr(AAsgn.Expr).ResolvedMethod);
    if TMethodCallExpr(AAsgn.Expr).ObjExpr <> nil then
    begin
      if ArcExprOwnsRef(TMethodCallExpr(AAsgn.Expr).ObjExpr) then
        NotYet('closure-returning call on an owned transient receiver', AAsgn);
      Self.EmitExprToX0(TMethodCallExpr(AAsgn.Expr).ObjExpr);
    end
    else if not EmitCapturedBase('x0', TMethodCallExpr(AAsgn.Expr).ObjectName,
              True, TMethodCallExpr(AAsgn.Expr).IsVarParam) then
    begin
      EmitLoadSlot('x0', TMethodCallExpr(AAsgn.Expr).ObjectName);
      if TMethodCallExpr(AAsgn.Expr).IsVarParam then
        Self.Emit(#9'ldr x0, [x0]');
    end;
    EmitPushX0();
    Tmp := '__fret_' + IntToStr(FFretN);
    FFretN := FFretN + 1;
    if not FFrame.ContainsKey(Tmp) then
      AddLocal(Tmp, 16);
    EmitCall(MD, TMethodCallExpr(AAsgn.Expr).Name,
      TMethodCallExpr(AAsgn.Expr).Args, Tmp, True, MD.VTableSlot);
    if IsRef then
    begin
      EmitSlotAddr('x9', AAsgn.Name);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');
    end;
    EmitSlotAddr('x1', Tmp);
    Self.Emit(#9'ldp x9, x10, [x1]');
    EmitSlotAddr('x1', AAsgn.Name);
    Self.Emit(#9'stp x9, x10, [x1]');
    Exit;
  end;
  NotYet('closure / method-pointer assignment from this expression', AAsgn);
end;

function TArm64Backend.EmitClosureResultCall(ACallDecl: TMethodDecl;
  const AName: string; AArgs: TObjectList): string;
begin
  { Call a closure-returning plain routine with x8 pointing at a fresh
    16-byte frame scratch (the frame grows lazily -- the body is buffered,
    as for NewExcFrameSlot) and return the scratch's slot name.  The scratch
    then holds the callee's +1 on the Env. }
  Result := '__fret_' + IntToStr(FFretN);
  FFretN := FFretN + 1;
  if not FFrame.ContainsKey(Result) then
    AddLocal(Result, 16);
  EmitCall(ACallDecl, AName, AArgs, Result);
end;

procedure TArm64Backend.EmitEnvPrologue(ADecl: TMethodDecl);
var
  Env: TRecordTypeDesc;
  I: Integer;
  F: TFieldInfo;
  Name: string;
  P: TMethodParam;
begin
  { Anonymous-method capture: the enclosing frame heap-allocates the env
    (_ClassAlloc zeroes it, so promoted locals start zero-initialised) and
    takes its own strong reference; a thunk receives the env through its
    hidden '__env' first parameter and BORROWS it.  Either way each
    '_cap_<Name>' slot gets the address of its env field, so every
    IsCaptured access path redirects unchanged.  Mirrors x86-64
    EmitEnvPrologue. }
  Env := TRecordTypeDesc(ADecl.EnvType);
  if Env = nil then
    NotYet('closure env without an env record', ADecl);
  if ADecl.IsAnonThunk then
    EmitLoadSlot('x0', '__env')
  else
  begin
    EmitIntLiteral('x0', Env.TotalSize());
    Self.Emit(Format(#9'adrp x1, %s@PAGE',
      [FieldCleanupSym(CodegenMangle(Env.Name))]));
    Self.Emit(Format(#9'add x1, x1, %s@PAGEOFF',
      [FieldCleanupSym(CodegenMangle(Env.Name))]));
    EmitCallSym('_ClassAlloc');
    EmitStoreSlot('x0', '__envp');
    EmitCallSym('_ClassAddRef');
    EmitLoadSlot('x0', '__envp');
  end;
  for I := 0 to ADecl.EnvCaptured.Count - 1 do
  begin
    Name := ADecl.EnvCaptured.Strings[I];
    F := Env.FindField(Name);
    if F = nil then
      NotYet('captured name without an env field', ADecl);
    EmitAddSubImm('add', 'x1', 'x0', F.Offset);
    EmitStoreSlot('x1', '_cap_' + Name);
  end;
  if ADecl.IsAnonThunk then
  begin
    { thunk from a method body: materialise the real Self slot from the env
      field (Self is never reassigned -- snapshot = by-ref) }
    if ADecl.EnvCaptured.IndexOf('Self') >= 0 then
    begin
      EmitLoadSlot('x9', '_cap_Self');
      Self.Emit(#9'ldr x0, [x9]');
      EmitStoreSlot('x0', 'Self');
    end;
    Exit;
  end;
  { enclosing METHOD frame: snapshot Self into its env field, with the env's
    own retain (the env cleanup releases it) }
  if ADecl.EnvCaptured.IndexOf('Self') >= 0 then
  begin
    if Env.FindField('Self').IsWeak then
      NotYet('[Weak Self] closure capture', ADecl);
    EmitLoadSlot('x0', 'Self');
    EmitLoadSlot('x9', '_cap_Self');
    Self.Emit(#9'str x0, [x9]');
    EmitCallSym('_ClassAddRef');
  end;
  { captured VALUE parameters: copy the spilled param into its env field;
    a managed value takes the env's own reference }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if ADecl.EnvCaptured.IndexOf(P.ParamName) < 0 then Continue;
    F := Env.FindField(P.ParamName);
    if P.IsVarParam or P.IsOpenArray or
       (F.TypeDesc.Kind in [tyRecord, tyStaticArray, tyInterface, tySingle,
                            tyProcedural]) then
      NotYet('closure capture of a parameter of this type', ADecl);
    EmitLoadSlot('x0', P.ParamName);
    EmitLoadSlot('x9', '_cap_' + P.ParamName);
    EmitStoreByWidth('x0', 'x9', F.TypeDesc);
    case F.TypeDesc.Kind of
      tyString:   EmitCallSym('_StringAddRef');
      tyClass:    if not F.IsWeak then EmitCallSym('_ClassAddRef');
      tyDynArray: EmitCallSym('_DynArrayAddRef');
    end;
  end;
end;

procedure TArm64Backend.EmitEnvCleanupFn(AEnv: TRecordTypeDesc);
var
  Sym: string;
begin
  { The env record's field-cleanup routine, handed to _ClassAlloc: releases
    the managed captured values when the last closure (or the frame) drops
    the env.  Same shape as a class's _FieldCleanup.  Weak, because the
    record name is only unit-unique. }
  Sym := FieldCleanupSym(CodegenMangle(AEnv.Name));
  Self.Emit('');
  Self.Emit('.text');
  Self.Emit('.balign 4');
  EmitWeakDef(Sym);
  Self.Emit(Sym + ':');
  Self.Emit(#9'stp x29, x30, [sp, #-16]!');
  Self.Emit(#9'mov x29, sp');
  Self.Emit(#9'str x19, [sp, #-16]!');
  Self.Emit(#9'mov x19, x0');
  Self.EmitRecordFieldReleases(AEnv, 'x19');
  Self.Emit(#9'ldr x19, [sp], #16');
  Self.Emit(#9'mov sp, x29');
  Self.Emit(#9'ldp x29, x30, [sp], #16');
  Self.Emit(#9'ret');
end;

procedure TArm64Backend.EmitParenlessCtor(AFA: TFieldAccessExpr);
var
  MC: TMethodCallExpr;
begin
  if AFA.Base <> nil then
    NotYet('parameterless constructor on this receiver form', AFA);
  MC := TMethodCallExpr.Create();
  try
    MC.Line := AFA.Line;
    MC.Col := AFA.Col;
    MC.ObjectName := AFA.RecordName;
    MC.Name := AFA.FieldName;
    MC.ResolvedType := AFA.ResolvedType;
    MC.ResolvedClassType := AFA.ResolvedType;
    MC.ResolvedMethod := AFA.ResolvedMethod;
    MC.IsConstructorCall := True;
    EmitMethodCallExpr(MC);
  finally
    MC.Free();
  end;
end;

procedure TArm64Backend.EmitSetIncludeExclude(ACall: TProcCall;
  AInclude: Boolean);
var
  SetT: TSetTypeDesc;
  LVal: TAddrOfExpr;
  W: Integer;
begin
  { Include(S, E) / Exclude(S, E), mirroring x86-64: the set lvalue is
    addressed through a transient @-wrapper, so a plain variable, a field and
    an element all work.  A jumbo set (> 64 members) goes to _SetInclude /
    _SetExclude with its address and the ordinal; a small set ORs in (or
    BICs out) 1 shl ord(E) at the set's own storage width. }
  SetT := TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType);
  Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));       { ordinal }
  if not SetT.IsJumbo() then
  begin
    Self.Emit(#9'mov x1, x0');
    Self.Emit(#9'movz x0, #1');
    Self.Emit(#9'lsl x0, x0, x1');                         { mask }
  end;
  EmitPushX0();
  LVal := TAddrOfExpr.Create();
  try
    LVal.Line := ACall.Line;
    LVal.Col := ACall.Col;
    LVal.Expr := TASTExpr(ACall.Args.Items[0]);
    Self.EmitExprToX0(LVal);                                { &S }
  finally
    LVal.Expr := nil;   { Args[0] is owned by the call node }
    LVal.Free();
  end;
  EmitPopTo('x1');
  if SetT.IsJumbo() then
  begin
    if AInclude then
      EmitCallSym('_SetInclude')
    else
      EmitCallSym('_SetExclude');
    Exit;
  end;
  W := SetT.RawSize();
  case W of
    1: Self.Emit(#9'ldrb w2, [x0]');
    2: Self.Emit(#9'ldrh w2, [x0]');
    4: Self.Emit(#9'ldr w2, [x0]');
  else
    Self.Emit(#9'ldr x2, [x0]');
  end;
  if AInclude then
    Self.Emit(#9'orr x2, x2, x1')
  else
  begin
    Self.Emit(#9'mvn x1, x1');                             { no bic encoding }
    Self.Emit(#9'and x2, x2, x1');
  end;
  case W of
    1: Self.Emit(#9'strb w2, [x0]');
    2: Self.Emit(#9'strh w2, [x0]');
    4: Self.Emit(#9'str w2, [x0]');
  else
    Self.Emit(#9'str x2, [x0]');
  end;
end;

procedure TArm64Backend.EmitFatFieldStoreStacked(AFld: TFieldInfo;
  AValueExpr: TASTExpr);
var
  IsRef: Boolean;
  FAE: TFieldAccessExpr;
  MD: TMethodDecl;
  SrcAddr: TAddrOfExpr;
begin
  { A closure / method-pointer FIELD (16 bytes: Code, Env) at AFld.Offset of
    the instance whose address is on TOP of the stack (consumed).  The value
    is materialised at an address first -- a literal into its hidden slot,
    a variable at its own slot -- then both words are copied.  For
    'reference to' the incoming Env is retained before the old one is
    released (so F := F is safe); 'of object' receivers stay unretained. }
  IsRef := (AFld.TypeDesc.Kind = tyProcedural) and
           TProceduralTypeDesc(AFld.TypeDesc).IsReference;
  if AValueExpr is TNilLiteral then
  begin
    if IsRef then
    begin
      Self.Emit(#9'ldr x9, [sp]');
      EmitAddSubImm('add', 'x9', 'x9', AFld.Offset);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');
    end;
    Self.Emit(#9'ldr x9, [sp], #16');
    EmitAddSubImm('add', 'x9', 'x9', AFld.Offset);
    Self.Emit(#9'stp xzr, xzr, [x9]');
    Exit;
  end;
  if (AValueExpr is TAddrOfExpr) and
     (TAddrOfExpr(AValueExpr).Expr is TFieldAccessExpr) and
     (TFieldAccessExpr(TAddrOfExpr(AValueExpr).Expr).ResolvedMethod is TMethodDecl) then
  begin
    { Field := @Obj.Method: (Code, receiver) built straight into the field;
      a virtual method's code comes from the receiver's own vtable }
    FAE := TFieldAccessExpr(TAddrOfExpr(AValueExpr).Expr);
    MD := TMethodDecl(FAE.ResolvedMethod);
    if MD.IsRecordMethod or MD.IsStatic or FAE.IsImplicitSelf or
       ((FAE.Base <> nil) and ArcExprOwnsRef(FAE.Base)) then
      NotYet('method pointer to this method form', AValueExpr);
    if IsRef then
    begin
      Self.Emit(#9'ldr x9, [sp]');
      EmitAddSubImm('add', 'x9', 'x9', AFld.Offset);
      Self.Emit(#9'ldr x0, [x9, #8]');
      EmitCallSym('_ClassRelease');              { the old Env }
    end;
    if FAE.Base <> nil then
      Self.EmitExprToX0(FAE.Base)
    else if not EmitCapturedBase('x0', FAE.RecordName, True, False) then
      EmitLoadSlot('x0', FAE.RecordName);
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'ldr x9, [x0]');
      Self.Emit(Format(#9'ldr x1, [x9, #%d]', [(MD.VTableSlot + 1) * 8]));
    end
    else
    begin
      Self.Emit(Format(#9'adrp x1, %s@PAGE', [RoutineSym(MD, '')]));
      Self.Emit(Format(#9'add x1, x1, %s@PAGEOFF', [RoutineSym(MD, '')]));
    end;
    Self.Emit(#9'ldr x9, [sp], #16');            { pop the base }
    EmitAddSubImm('add', 'x9', 'x9', AFld.Offset);
    Self.Emit(#9'stp x1, x0, [x9]');             { Code, receiver }
    if IsRef then
      EmitCallSym('_ClassAddRef');               { x0 = receiver }
    Exit;
  end;
  if AValueExpr is TAnonMethodExpr then
    EmitAnonValueToSlot(TAnonMethodExpr(AValueExpr))
  else if (AValueExpr is TIdentExpr) and IsMethodPtrType(AValueExpr.ResolvedType) and
          not IsCaptured(TIdentExpr(AValueExpr).Name) and
          (TIdentExpr(AValueExpr).ParamMode = pmNone) and
          not TIdentExpr(AValueExpr).IsImplicitSelf then
    EmitSlotAddr('x0', TIdentExpr(AValueExpr).Name)
  else if (AValueExpr is TFieldAccessExpr) and
          (TFieldAccessExpr(AValueExpr).FieldInfo <> nil) and
          not TFieldAccessExpr(AValueExpr).IsMethodCall and
          (TFieldAccessExpr(AValueExpr).PropRead = nil) then
  begin
    { another closure FIELD as the source: address it via a transient @ }
    SrcAddr := TAddrOfExpr.Create();
    try
      SrcAddr.Line := AValueExpr.Line;
      SrcAddr.Col := AValueExpr.Col;
      SrcAddr.Expr := AValueExpr;
      Self.EmitExprToX0(SrcAddr);
    finally
      SrcAddr.Expr := nil;   { owned by the caller's node }
      SrcAddr.Free();
    end;
  end
  else
    NotYet('closure / method-pointer field store from this expression',
      AValueExpr);
  EmitPushX0();                                  { [base][&value] }
  if IsRef then
  begin
    Self.Emit(#9'ldr x0, [sp]');
    Self.Emit(#9'ldr x0, [x0, #8]');
    EmitCallSym('_ClassAddRef');                 { the field's own Env ref }
    Self.Emit(#9'ldr x9, [sp, #16]');
    EmitAddSubImm('add', 'x9', 'x9', AFld.Offset);
    Self.Emit(#9'ldr x0, [x9, #8]');
    EmitCallSym('_ClassRelease');                { the old Env }
  end;
  Self.Emit(#9'ldr x1, [sp]');
  Self.Emit(#9'ldp x10, x11, [x1]');
  Self.Emit(#9'ldr x9, [sp, #16]');
  EmitAddSubImm('add', 'x9', 'x9', AFld.Offset);
  Self.Emit(#9'stp x10, x11, [x9]');
  Self.Emit(#9'add sp, sp, #32');                { drop &value and base }
end;

procedure TArm64Backend.EmitProcFieldAddr(const AObjectName: string;
  AObjExpr: TASTExpr; AIsVarParam, AImplicitSelf: Boolean;
  AReceiver: TTypeDesc; AField: TFieldInfo; ANode: TASTNode);
var
  IsRec: Boolean;
begin
  { x0 := the address of a procedural-typed FIELD.  The receiver base follows
    the class-vs-record rule (BUG-20260722-closure-record-field-direct-call):
    a class reference's VALUE is the instance, a record's ADDRESS is its
    storage.  Every arm here is call-free except the chained-expression one,
    which runs before any argument is evaluated. }
  if AField = nil then
    NotYet('procedural-field call without field info', ANode);
  IsRec := (AReceiver <> nil) and (AReceiver.Kind = tyRecord);
  if AImplicitSelf then
    EmitLoadSlot('x0', 'Self')        { a record method's Self is an address too }
  else if AObjExpr <> nil then
  begin
    if (AObjExpr.ResolvedType <> nil) and (AObjExpr.ResolvedType.Kind = tyRecord) then
      EmitRecAddrToX0(AObjExpr)
    else
    begin
      if ArcExprOwnsRef(AObjExpr) then
        NotYet('procedural-field call on an owned transient receiver', ANode);
      Self.EmitExprToX0(AObjExpr);
    end;
  end
  else if IsRec then
  begin
    if IsCaptured(AObjectName) then
    begin
      EmitLoadSlot('x0', '_cap_' + AObjectName);
      if AIsVarParam then
        Self.Emit(#9'ldr x0, [x0]');
    end
    else if AIsVarParam then
      EmitLoadSlot('x0', AObjectName)  { slot holds the caller's record address }
    else
      EmitSlotAddr('x0', AObjectName);
  end
  else if not EmitCapturedBase('x0', AObjectName, True, AIsVarParam) then
  begin
    EmitLoadSlot('x0', AObjectName);
    if AIsVarParam then
      Self.Emit(#9'ldr x0, [x0]');
  end;
  if AField.Offset <> 0 then
    EmitAddSubImm('add', 'x0', 'x0', AField.Offset);
end;

procedure TArm64Backend.EmitProcFieldCall(const AObjectName: string;
  AObjExpr: TASTExpr; AIsVarParam, AImplicitSelf: Boolean;
  AReceiver: TTypeDesc; AField: TFieldInfo; AArgs: TObjectList;
  ANode: TASTNode);
var
  PT: TProceduralTypeDesc;
begin
  { Obj.Handler(args) / Handler(args) where Handler is a procedural-typed
    FIELD: address the field, then dispatch through it -- a closure / method
    pointer as a fat value (Env or Self in x0), a plain procedure pointer as
    one code word. }
  if (AField = nil) or not (AField.TypeDesc is TProceduralTypeDesc) then
    NotYet('procedural-field call on this field', ANode);
  PT := TProceduralTypeDesc(AField.TypeDesc);
  EmitProcFieldAddr(AObjectName, AObjExpr, AIsVarParam, AImplicitSelf,
    AReceiver, AField, ANode);
  EmitFatPtrCall('x0', PT, AArgs, IsMethodPtrType(PT));
end;

procedure TArm64Backend.EmitDiscardedProcResult(APT: TProceduralTypeDesc);
begin
  { a DISCARDED owned result of a call through a procedural value is released,
    as for a direct call (results come back rc=1) }
  if (APT = nil) or (APT.ReturnType = nil) then Exit;
  if APT.ReturnType.IsString() then
    EmitCallSym('_StringRelease')
  else if APT.ReturnType.Kind = tyClass then
    EmitCallSym('_ClassRelease')
  else if APT.ReturnType.Kind = tyDynArray then
    EmitCallSym('_DynArrayRelease');
end;

procedure TArm64Backend.GuardNoOpenArrayParam(AProcType: TProceduralTypeDesc;
  ANode: TASTNode);
var
  I: Integer;
begin
  if AProcType = nil then Exit;
  for I := 0 to AProcType.Params.Count - 1 do
    if (TProcParamInfo(AProcType.Params.Items[I]).TypeDesc <> nil) and
       (TProcParamInfo(AProcType.Params.Items[I]).TypeDesc.Kind = tyOpenArray) then
      NotYet('open-array parameter in a call through a procedural type', ANode);
end;

procedure TArm64Backend.EmitFatPtrCall(const AAddrReg: string;
  AProcType: TProceduralTypeDesc; AArgs: TObjectList; AIsFat: Boolean);
var
  I: Integer;
  Decl: TMethodDecl;
  Par: TMethodParam;
  Info: TProcParamInfo;
  Slot: string;
begin
  { AAddrReg holds the address of a procedural value: a 16-byte fat value
    (Code at +0, Env/Self at +8) when AIsFat, else one plain code word.

    The call itself is an ordinary EmitCall against a TMethodDecl synthesised
    from the procedural type's signature, so every argument class EmitCall
    lowers -- doubles, records by shape, interfaces, closures, jumbo sets,
    var/out, owned transients released after the call -- works through a
    closure exactly as through a direct call, and the two cannot drift.  The
    Env rides as the hidden first argument the way a method's Self does
    (pushed, ASelfPushed), and VIRT_INDIRECT makes EmitCall branch through the
    code word instead of a symbol.  The value's address is parked in a
    per-site frame slot, because the arguments may themselves call. }
  GuardNoOpenArrayParam(AProcType, nil);
  Slot := '__icall_' + IntToStr(FJArgN);
  FJArgN := FJArgN + 1;
  if not FFrame.ContainsKey(Slot) then
    AddLocal(Slot, 8);
  Self.Emit(Format(#9'mov x10, %s', [AAddrReg]));
  EmitStoreSlot('x10', Slot);
  Decl := TMethodDecl.Create();
  try
    for I := 0 to AProcType.Params.Count - 1 do
    begin
      Info := TProcParamInfo(AProcType.Params.Items[I]);
      Par := TMethodParam.Create();
      Par.ParamName := Info.Name;
      Par.ResolvedType := Info.TypeDesc;
      Par.IsVarParam := Info.IsVarParam;
      Par.IsConstParam := Info.IsConstParam;
      Decl.Params.Add(Par);
    end;
    Decl.ResolvedReturnType := AProcType.ReturnType;
    if AIsFat then
    begin
      EmitLoadSlot('x10', Slot);
      Self.Emit(#9'ldr x0, [x10, #8]');       { Env / Self -> hidden first arg }
      EmitPushX0();
    end;
    FIndirectSlot := Slot;
    EmitCall(Decl, '', AArgs, '', AIsFat, VIRT_INDIRECT);
  finally
    Decl.Free();
  end;
end;

procedure TArm64Backend.EmitOwnedStrTransientRelease(AValueExpr: TASTExpr);
begin
  { The transient pointer is in x0.  An rc=0 unowned transient must have
    been PINNED (_StringAddRef) BEFORE the consuming call: a by-value
    callee param's own entry-retain/exit-release cycle frees an unpinned
    rc=0 transient during the call, so pinning here (after the call) was a
    double-free with a non-storing callee
    (BUG-20260722-arm64-propsetter-pin-after-call).  This helper now emits
    only the release half; call sites emit the pre-call pin. }
  EmitCallSym('_StringRelease');
end;

{ Pin an rc=0 unowned string transient (value in x0) BEFORE the call that
  consumes it: 0 -> 1, so the callee's borrow cycle cannot free it and the
  post-call release balances (1 -> 0 frees, or higher when the callee
  stored it).  x0 is preserved.  rc=1 owned transients need no pin. }
procedure TArm64Backend.EmitOwnedStrTransientPin(AValueExpr: TASTExpr);
begin
  if ArcExprIsUnownedStrTransient(AValueExpr) then
  begin
    EmitPushX0();
    EmitCallSym('_StringAddRef');
    EmitPopTo('x0');
  end;
end;

procedure TArm64Backend.EmitIndexedPropWrite(AProp: TPropertyInfo;
  const AOwner: string; AVSlot: Integer; AIndex, AValue: TASTExpr;
  AStmt: TASTStmt);
var
  RelStr: Boolean;
  Shape: Integer;
begin
  { setter(self, index, value) for an indexed property write, shared by the
    field form (Obj.Items[I] := V) and the DEFAULT-property form
    (Obj[I] := V, a TStaticSubscriptAssign carrying PropWriteInfo) }
  if AProp.IsStatic then
    NotYet('static indexed property write', AStmt);
  if AProp.TypeDesc.IsFloat() then
    NotYet('float indexed property write', AStmt);
  { The index rides in one integer register — an int OR a string (a
    pointer) fits identically (leg 18).  A string KEY is passed BORROWED:
    the by-value setter param retains its own copy only if it stores the
    key, so the caller adds no ref — matching the x86-64 (:15211) and QBE
    (:7310) reference backends, which have no index-type guard and no key
    AddRef.  Other non-integer index kinds (float/record/managed-non-string)
    stay an honest hole. }
  if not (IsIntFam(AIndex.ResolvedType) or
          (AIndex is TIntLiteral) or
          ((AIndex.ResolvedType <> nil) and
           (AIndex.ResolvedType.Kind = tyString))) then
    NotYet('indexed property with a non-integer index', AStmt);
  if AProp.TypeDesc.Kind = tyRecord then
  begin
    { a record VALUE travels by its AAPCS64 shape: a large one by address,
      a one- or two-eightbyte one in integer registers (the setter's prologue
      copies it in by the same rule).  The value is read from the source's
      own storage, so it must be addressable; an HFA rides in float
      registers and stays an honest hole. }
    Shape := RecReturnShape(TRecordTypeDesc(AProp.TypeDesc));
    if (Shape < 0) or (Shape > 2) then
      NotYet('indexed property of this record shape', AStmt);
    Self.EmitExprToX0(AIndex);
    EmitPushX0();                          { index arg }
    EmitRecAddrToX0(AValue);
    EmitPushX0();                          { value address }
    if AStmt is TFieldAssignment then
      EmitPropRecvToX0(TFieldAssignment(AStmt))
    else
      EmitSubscriptPropRecvToX0(TStaticSubscriptAssign(AStmt));
    EmitPopTo('x9');                       { value address }
    EmitPopTo('x1');                       { index }
    case Shape of
      0: Self.Emit(#9'mov x2, x9');
      1: Self.Emit(#9'ldr x2, [x9]');
    else
      Self.Emit(#9'ldp x2, x3, [x9]');
    end;
    if AVSlot >= 0 then
    begin
      Self.Emit(#9'ldr x9, [x0]');
      Self.Emit(Format(#9'ldr x9, [x9, #%d]', [(AVSlot + 1) * 8]));
      Self.Emit(#9'blr x9');
    end
    else
      Self.Emit(Format(#9'bl %s', [PropAccessorSym(AOwner, AProp.WriteMethod)]));
    Exit;
  end;
  { An OWNED managed STRING value (a concat / call-result transient) is
    passed BORROWED to the setter (which retains its own copy), so the
    caller must dispose the transient AFTER the call — the same +1 handover
    EmitCall applies to an owned-transient string argument.  A class-typed
    owned transient here is still an honest hole (untested; no self-host
    need).  RelStr flags the string-transient case; the parked value in a
    dedicated top-of-stack slot survives the setter bl/blr (only x0-x18 are
    clobbered) and is released by shape below. }
  RelStr := AProp.TypeDesc.IsString() and
            ArcBuiltinStrArgOwnsRef(AValue);
  if (AProp.TypeDesc.Kind = tyClass) and
     ArcExprOwnsRef(AValue) then
    NotYet('owned transient as indexed-property value', AStmt);
  { The borrowed case emits byte-identical code to before (index pushed,
    then value; pop x2=value, x1=index).  For an owned string transient the
    value pointer is captured in x19 (callee-saved, survives the setter
    bl/blr) so the SAME buffer that was passed can be released afterwards —
    the setter borrows the value, so the caller disposes the transient. }
  if RelStr then
    Self.Emit(#9'str x19, [sp, #-16]!');  { preserve x19 }
  Self.EmitExprToX0(AIndex);
  EmitPushX0();                          { index arg }
  Self.EmitExprToX0(AValue);
  if RelStr then
  begin
    Self.Emit(#9'mov x19, x0');          { capture the value transient }
    { rc=0 transients pin BEFORE the call — the setter's by-value param
      cycle would free an unpinned one mid-call
      (BUG-20260722-arm64-propsetter-pin-after-call). }
    Self.EmitOwnedStrTransientPin(AValue);
  end;
  EmitPushX0();                          { value arg }
  if AStmt is TFieldAssignment then
    EmitPropRecvToX0(TFieldAssignment(AStmt))
  else
    EmitSubscriptPropRecvToX0(TStaticSubscriptAssign(AStmt));
  EmitPopTo('x2');                       { value }
  EmitPopTo('x1');                       { index }
  if AVSlot >= 0 then
  begin
    Self.Emit(#9'ldr x9, [x0]');
    Self.Emit(Format(#9'ldr x9, [x9, #%d]',
      [(AVSlot + 1) * 8]));
    Self.Emit(#9'blr x9');
  end
  else
    Self.Emit(Format(#9'bl %s',
      [PropAccessorSym(AOwner,
        AProp.WriteMethod)]));
  if RelStr then
  begin
    Self.Emit(#9'mov x0, x19');          { the value transient }
    EmitOwnedStrTransientRelease(AValue);
    Self.Emit(#9'ldr x19, [sp], #16');   { restore x19 }
  end;
end;

procedure TArm64Backend.EmitSubscriptPropRecvToX0(AStmt: TStaticSubscriptAssign);
begin
  { default-property receiver Obj[I] := V: a class variable holds the
    instance; a record variable's ADDRESS is its Self.  A Self field or a var
    parameter adds the usual indirection. }
  if AStmt.IsImplicitSelf then
  begin
    if AStmt.ImplicitFieldInfo = nil then
      NotYet('default-property write on this receiver form', AStmt);
    EmitLoadSlot('x0', 'Self');
    if AStmt.ImplicitFieldInfo.TypeDesc.Kind = tyRecord then
    begin
      if AStmt.ImplicitFieldInfo.Offset <> 0 then
        EmitAddSubImm('add', 'x0', 'x0', AStmt.ImplicitFieldInfo.Offset);
    end
    else
      Self.Emit(Format(#9'ldr x0, [x0, #%d]',
        [AStmt.ImplicitFieldInfo.Offset]));
    Exit;
  end;
  if IsCaptured(AStmt.ArrayName) then
    NotYet('default-property write on a captured receiver', AStmt);
  if (AStmt.ResolvedArrayType <> nil) and
     (AStmt.ResolvedArrayType.Kind = tyRecord) then
  begin
    if AStmt.IsVarParam then
      EmitLoadSlot('x0', AStmt.ArrayName)
    else
      EmitRecordBaseAddr('x0', AStmt.ArrayName, False);
    Exit;
  end;
  EmitLoadSlot('x0', AStmt.ArrayName);
  if AStmt.IsVarParam then
    Self.Emit(#9'ldr x0, [x0]');
end;

procedure TArm64Backend.EmitFieldAssign(AStmt: TFieldAssignment);
var
  RelStr: Boolean;
begin
  RelStr := False;
  if AStmt.PropWriteInfo <> nil then
  begin
    { method-backed property write: setter(self, value) — or
      setter(self, index, value) for the indexed form }
    if ((AStmt.ObjExpr <> nil) and ArcExprOwnsRef(AStmt.ObjExpr)) or
       (AStmt.IsImplicitSelf and (AStmt.ImplicitBaseInfo = nil)) then
      NotYet('property write on this receiver form', AStmt);
    if AStmt.PropIndexExpr <> nil then
    begin
      if AStmt.IsElemWrite then
        NotYet('array-field element write via subscript', AStmt);
      EmitIndexedPropWrite(TPropertyInfo(AStmt.PropWriteInfo),
        AStmt.PropOwnerType, AStmt.PropAccessorVSlot, AStmt.PropIndexExpr,
        AStmt.Expr, AStmt);
      Exit;
    end;
    if TPropertyInfo(AStmt.PropWriteInfo).IsStatic then
    begin
      { static setter: the value is the FIRST argument (no Self) }
      if TPropertyInfo(AStmt.PropWriteInfo).TypeDesc.IsFloat() then
        Self.EmitExprToD0OrConvert(AStmt.Expr)
      else
        Self.EmitExprToX0(AStmt.Expr);
      Self.Emit(Format(#9'bl %s',
        [PropAccessorSym(AStmt.PropOwnerType,
          TPropertyInfo(AStmt.PropWriteInfo).WriteMethod)]));
      Exit;
    end;
    if TPropertyInfo(AStmt.PropWriteInfo).TypeDesc.IsFloat() then
    begin
      Self.EmitExprToD0OrConvert(AStmt.Expr);
      { a chained receiver is a full expression evaluation (it may call a
        getter), which can clobber d0 -- park the value across it }
      if AStmt.ObjExpr <> nil then
        Self.Emit(#9'str d0, [sp, #-16]!');
      EmitPropRecvToX0(AStmt);
      if AStmt.ObjExpr <> nil then
        Self.Emit(#9'ldr d0, [sp], #16');
    end
    else
    begin
      { An owned-transient STRING value is disposed after the setter borrows it
        (leg 36); a class-typed owned transient stays an honest hole. }
      RelStr := TPropertyInfo(AStmt.PropWriteInfo).TypeDesc.IsString() and
                ArcBuiltinStrArgOwnsRef(AStmt.Expr);
      if (TPropertyInfo(AStmt.PropWriteInfo).TypeDesc.Kind = tyClass) and
         ArcExprOwnsRef(AStmt.Expr) then
        NotYet('owned transient as property value', AStmt);
      Self.EmitExprToX0(AStmt.Expr);
      if RelStr then
      begin
        Self.Emit(#9'str x0, [sp, #-16]!');  { park the transient — released after call }
        { rc=0 transients pin BEFORE the call
          (BUG-20260722-arm64-propsetter-pin-after-call). }
        Self.EmitOwnedStrTransientPin(AStmt.Expr);
      end;
      EmitPushX0();
      EmitPropRecvToX0(AStmt);
      EmitPopTo('x1');
    end;
    if AStmt.PropAccessorVSlot >= 0 then
    begin
      Self.Emit(#9'ldr x9, [x0]');
      Self.Emit(Format(#9'ldr x9, [x9, #%d]',
        [(AStmt.PropAccessorVSlot + 1) * 8]));
      Self.Emit(#9'blr x9');
    end
    else
      Self.Emit(Format(#9'bl %s',
        [PropAccessorSym(AStmt.PropOwnerType,
          TPropertyInfo(AStmt.PropWriteInfo).WriteMethod)]));
    if RelStr then
    begin
      Self.Emit(#9'ldr x0, [sp], #16');      { the parked transient }
      EmitOwnedStrTransientRelease(AStmt.Expr);
    end;
    Exit;
  end;
  if (AStmt.ObjExpr <> nil) and not AStmt.IsElemWrite then
  begin
    { chained base: A.B.C := v — the base expression yields the instance.
      An OWNED transient base (a call result, +1) is kept in a second slot
      and released after the field store, so the object survives the write
      but its temporary +1 does not leak.  An element write (A.B.Arr[i] := v)
      is routed to EmitFieldElemAssign instead — the field-store machinery
      here would drop the index and write the value over the array slot. }
    if AStmt.FieldInfo = nil then
      NotYet('unresolved field assignment', AStmt);
    if (AStmt.ObjExpr.ResolvedType <> nil) and
       (AStmt.ObjExpr.ResolvedType.Kind = tyRecord) then
    begin
      { a RECORD base -- P^.Rec.Field := v, A.Rec.Field := v: the store goes
        through the record's ADDRESS (EmitRecAddrToX0), not its value; a
        record cannot be loaded into one register at all }
      EmitRecAddrToX0(AStmt.ObjExpr);
      EmitPushX0();
      EmitInstanceFieldStoreStacked(AStmt.FieldInfo, AStmt.Expr);
      Exit;
    end;
    Self.EmitExprToX0(AStmt.ObjExpr);
    if ArcExprOwnsRef(AStmt.ObjExpr) then
    begin
      EmitPushX0();                 { [obj] — the +1 copy, released below }
      EmitPushX0();                 { [obj][obj] — consumed by the store }
      EmitInstanceFieldStoreStacked(AStmt.FieldInfo, AStmt.Expr);
      EmitPopTo('x0');              { the retained copy }
      EmitCallSym('_ClassRelease');
      Exit;
    end;
    EmitPushX0();
    EmitInstanceFieldStoreStacked(AStmt.FieldInfo, AStmt.Expr);
    Exit;
  end;
  if AStmt.IsElemWrite then
  begin
    EmitFieldElemAssign(AStmt);
    Exit;
  end;
  if AStmt.PropIndexExpr <> nil then
    NotYet('this field-assignment form', AStmt);
  if AStmt.FieldInfo = nil then
    NotYet('unresolved field assignment', AStmt);
  if AStmt.IsImplicitSelf then
  begin
    { A nested path (Self.FIntermediate.SubField := V) resolves FieldInfo to
      SubField, whose Offset is relative to the intermediate — pass
      ImplicitBaseInfo so EmitInstBase folds it into the base (add for an
      embedded record, deref for a class reference). }
    EmitInstanceFieldStore(AStmt.FieldInfo, AStmt.Expr, 'Self', False,
      AStmt.ImplicitBaseInfo);
    Exit;
  end;
  if AStmt.IsClassAccess then
  begin
    { Obj.Field := value — the instance pointer lives in Obj's slot (a captured
      var-param class base needs the extra deref, threaded via IsVarParam) }
    EmitInstanceFieldStore(AStmt.FieldInfo, AStmt.Expr, AStmt.RecordName,
      AStmt.IsVarParam);
    Exit;
  end;
  if AStmt.FieldInfo.TypeDesc.Kind = tyRecord then
  begin
    { Rec.Field := <record> — memcpy from the source's address (a record
      lvalue) or from __rret (a record-returning call). }
    if (not IsRecordCallArg(AStmt.Expr)) and
       (not RecretManagedClean(TRecordTypeDesc(AStmt.FieldInfo.TypeDesc))) then
    begin
      { managed record LVALUE source (leg 25): retain the source's managed
        fields, release the dest FIELD's old ones, then memcpy — the same
        discipline as EmitInstanceFieldStore's managed tyRecord arm, but the
        dest is a record-field address (RecordName slot + field offset).
        Source and dest live in callee-saved x19/x22 across the ARC walks and
        the memcpy.  Retain-before-release keeps a self-assign exact. }
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      EmitRecAddrToX0(AStmt.Expr);
      Self.Emit(#9'mov x19, x0');                   { x19 = source addr }
      EmitRecordBaseAddr('x22', AStmt.RecordName, AStmt.IsVarParam);
      if AStmt.FieldInfo.Offset <> 0 then
        EmitAddSubImm('add', 'x22', 'x22', AStmt.FieldInfo.Offset);  { dest field }
      Self.EmitRecordFieldRetains(
        TRecordTypeDesc(AStmt.FieldInfo.TypeDesc), 'x19');
      { copy site: no-zero release (BUG-20260720-managed-record-self-assign) }
      Self.EmitRecordFieldReleases(
        TRecordTypeDesc(AStmt.FieldInfo.TypeDesc), 'x22', False);
      Self.Emit(#9'mov x0, x22');
      Self.Emit(#9'mov x1, x19');
      EmitIntLiteral('x2', AStmt.FieldInfo.TypeDesc.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Exit;
    end;
    if IsRecordCallArg(AStmt.Expr) then
      EmitRecCallToRret(AStmt.Expr)   { x0 = __rret address; +1 refs transfer }
    else
      EmitRecAddrToX0(AStmt.Expr);    { x0 = source record address (clean) }
    EmitPushX0();                     { [srcaddr] }
    { the destination field's OLD managed refs must be released before a
      call-source transfers its +1 refs in (dest may hold stale values) }
    if IsRecordCallArg(AStmt.Expr) and
       not RecretManagedClean(TRecordTypeDesc(AStmt.FieldInfo.TypeDesc)) then
    begin
      EmitRecordBaseAddr('x0', AStmt.RecordName, AStmt.IsVarParam);
      if AStmt.FieldInfo.Offset <> 0 then
        EmitAddSubImm('add', 'x0', 'x0', AStmt.FieldInfo.Offset);
      Self.EmitRecordFieldReleases(
        TRecordTypeDesc(AStmt.FieldInfo.TypeDesc), 'x0');
    end;
    EmitRecordBaseAddr('x0', AStmt.RecordName, AStmt.IsVarParam);
    if AStmt.FieldInfo.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0', AStmt.FieldInfo.Offset);
    EmitPopTo('x1');                  { source address }
    EmitIntLiteral('x2', AStmt.FieldInfo.TypeDesc.RawSize());
    EmitCallSym('memcpy');
    Exit;
  end;
  { tyPointer/tyPChar are unmanaged 8-byte words, so the plain store path
    below handles them exactly like an Int64 (RawSize picks `str x0`).
    tyProcedural is deliberately NOT here: a method-pointer/closure is a
    16-byte fat value and would need a two-word store. }
  if not (IsIntFam(AStmt.FieldInfo.TypeDesc) or
          (AStmt.FieldInfo.TypeDesc.Kind in [tyDouble, tySingle,
                                             tyClass, tyPointer,
                                             tyPChar]) or
          AStmt.FieldInfo.TypeDesc.IsString()) then
  begin
    { the remaining kinds -- a closure / method pointer (a two-word store),
      a plain procedural pointer, a dyn array, a metaclass, a small set -- go
      through the stacked instance-field store with the record's ADDRESS as
      the base, which applies each kind's width and ARC discipline }
    EmitRecordBaseAddr('x0', AStmt.RecordName, AStmt.IsVarParam);
    EmitPushX0();
    EmitInstanceFieldStoreStacked(AStmt.FieldInfo, AStmt.Expr);
    Exit;
  end;
  if AStmt.FieldInfo.TypeDesc.Kind = tySingle then
  begin
    Self.EmitExprToD0OrConvert(AStmt.Expr);
    Self.Emit(#9'fcvt s0, d0');
    EmitRecordBaseAddr('x9', AStmt.RecordName, AStmt.IsVarParam);
    Self.Emit(Format(#9'str s0, [x9, #%d]', [AStmt.FieldInfo.Offset]));
    Exit;
  end;
  if AStmt.FieldInfo.TypeDesc.IsString() or
     (AStmt.FieldInfo.TypeDesc.Kind = tyClass) then
  begin
    { managed field store: retain the value unless the expression owns a
      +1 already, release the field's old value, then store.  The slot
      address is re-derived after the release call (it clobbers x9). }
    Self.EmitExprToX0(AStmt.Expr);
    if (AStmt.FieldInfo.TypeDesc.IsString() and
        not ArcExprOwnsRef(AStmt.Expr)) or
       ((AStmt.FieldInfo.TypeDesc.Kind = tyClass) and
        not ArcExprOwnsRef(AStmt.Expr)) then
    begin
      EmitPushX0();
      if AStmt.FieldInfo.TypeDesc.IsString() then
        EmitCallSym('_StringAddRef')
      else
        EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();
    EmitRecordBaseAddr('x9', AStmt.RecordName, AStmt.IsVarParam);
    Self.Emit(Format(#9'ldr x0, [x9, #%d]', [AStmt.FieldInfo.Offset]));
    if AStmt.FieldInfo.TypeDesc.IsString() then
      EmitCallSym('_StringRelease')
    else
      EmitCallSym('_ClassRelease');
    EmitRecordBaseAddr('x9', AStmt.RecordName, AStmt.IsVarParam);
    EmitPopTo('x0');
    Self.Emit(Format(#9'str x0, [x9, #%d]', [AStmt.FieldInfo.Offset]));
    Exit;
  end;
  if AStmt.FieldInfo.TypeDesc.Kind = tyDouble then
  begin
    Self.EmitExprToD0OrConvert(AStmt.Expr);
    Self.Emit(#9'fmov x0, d0');
  end
  else
    Self.EmitExprToX0(AStmt.Expr);
  EmitPushX0();
  EmitRecordBaseAddr('x9', AStmt.RecordName, AStmt.IsVarParam);
  EmitPopTo('x0');
  case AStmt.FieldInfo.TypeDesc.RawSize() of
    1: Self.Emit(Format(#9'strb w0, [x9, #%d]', [AStmt.FieldInfo.Offset]));
    2: Self.Emit(Format(#9'strh w0, [x9, #%d]', [AStmt.FieldInfo.Offset]));
    4: Self.Emit(Format(#9'str w0, [x9, #%d]', [AStmt.FieldInfo.Offset]));
  else
    Self.Emit(Format(#9'str x0, [x9, #%d]', [AStmt.FieldInfo.Offset]));
  end;
end;

procedure TArm64Backend.EmitFieldElemAssign(AStmt: TFieldAssignment);
var
  Elem: TTypeDesc;
  IsDyn: Boolean;
  Low: Integer;
  NB: Integer;
begin
  { Rec.Field[Index] := value.  Handled leaf base shapes: a plain
    local/global record, a by-value record param, and (leg 28) a TRUE var/out
    record param — EmitFieldElemAddrToX0 computes the base address through
    EmitRecordBaseAddr, so the var/out slot is derefed to the caller's record
    while a by-value/local/global slot is addressed inline.  Element container:
    dyn-array (field slot holds the data pointer — deref) or static array (the
    field storage IS the array).
    Still NotYet:
      * ObjExpr <> nil        — a chained object base (A.B.Arr[i]) needs the
        base expression evaluated, not a slot+offset.
      * IsImplicitSelf        — needs Self + ImplicitBaseInfo.Offset, which the
        plain slot+offset path does not account for.
      * IsVarParam and IsClassAccess — a var-param CLASS receiver's element
        write needs an extra deref (the slot holds &instance) that the
        IsClassAccess address arm below does not add; keep it honest until a
        var-param class base is wired end-to-end. }
  if AStmt.IsImplicitSelf and (AStmt.ObjExpr <> nil) then
    NotYet('array-field element write on this base form', AStmt);
  if AStmt.FieldInfo = nil then
    NotYet('unresolved field element write', AStmt);
  if AStmt.FieldInfo.TypeDesc.Kind = tyDynArray then
    Elem := TDynArrayTypeDesc(AStmt.FieldInfo.TypeDesc).ElementType
  else if AStmt.FieldInfo.TypeDesc.Kind = tyStaticArray then
    Elem := TStaticArrayTypeDesc(AStmt.FieldInfo.TypeDesc).ElementType
  else
    NotYet('field element write on this field type', AStmt);
  IsDyn := AStmt.FieldInfo.TypeDesc.Kind = tyDynArray;
  Low := 0;
  if not IsDyn then
    Low := TStaticArrayTypeDesc(AStmt.FieldInfo.TypeDesc).LowBound;

  { Evaluate the VALUE FIRST (and complete its AddRef), THEN compute the
    element address — a value expression that reassigns/grows the SAME
    dyn-array field (R.Arr[i] := F() where F does SetLength(R.Arr,...)) would
    otherwise leave a stale/freed data pointer.  Matches the x86-64 order. }
  if Elem.IsString() or (Elem.Kind = tyClass) then
  begin
    Self.EmitExprToX0(AStmt.Expr);
    if not ArcExprOwnsRef(AStmt.Expr) then
    begin
      EmitPushX0();
      if Elem.IsString() then
        EmitCallSym('_StringAddRef')
      else
        EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();                              { [val] }
    EmitFieldElemAddrToX0(AStmt, Elem, IsDyn, Low);  { x0 = &element (fresh) }
    EmitPushX0();                              { [val][elemaddr] }
    Self.Emit(#9'ldr x0, [x0]');               { old element value }
    if Elem.IsString() then
      EmitCallSym('_StringRelease')
    else
      EmitCallSym('_ClassRelease');
    Self.Emit(#9'ldr x9, [sp]');               { elem address }
    Self.Emit(#9'ldr x0, [sp, #16]');          { new value }
    Self.Emit(#9'str x0, [x9]');
    Self.Emit(#9'add sp, sp, #32');            { drop [val][elemaddr] }
    Exit;
  end;
  if Elem.Kind in [tyDouble, tySingle] then
  begin
    Self.EmitExprToD0OrConvert(AStmt.Expr);
    Self.Emit(#9'str d0, [sp, #-16]!');        { park the value }
    EmitFieldElemAddrToX0(AStmt, Elem, IsDyn, Low);
    Self.Emit(#9'ldr d0, [sp], #16');          { restore value }
    if Elem.Kind = tySingle then
    begin
      Self.Emit(#9'fcvt s0, d0');
      Self.Emit(#9'str s0, [x0]');
    end
    else
      Self.Emit(#9'str d0, [x0]');
    Exit;
  end;
  if Elem.Kind = tyRecord then
  begin
    { record element store: memcpy from the source record's address, with the
      retain-source-then-release-dest discipline for MANAGED records (a plain
      memcpy for clean ones).  Mirrors the local-array record-element store
      (EmitStaticElemAssign) and the field-store leg.  A record-returning CALL
      source has no lvalue — materialise it into __rret (its +1 field refs
      transfer, so release the dest's old refs, no source retain).  Element
      address is computed AFTER the source per the value-first rule above. }
    if IsRecordCallArg(AStmt.Expr) then
    begin
      { Materialise the CALL into __rret FIRST (a stable frame slot), THEN
        compute the element address fresh — a call that reallocates the SAME
        dyn-array field (Box.Recs[i] := F() where F does SetLength(Box.Recs,…))
        must not leave a stale element pointer into the freed old block.
        Mirrors the x86-64 field path's value-first ordering. }
      EmitRecCallToRret(AStmt.Expr);   { x0 = the result's scratch; +1 transfers }
      EmitPushX0();                                    { [result] }
      EmitFieldElemAddrToX0(AStmt, Elem, IsDyn, Low);  { x0 = &element (fresh) }
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      Self.Emit(#9'mov x22, x0');                      { x22 = element addr }
      Self.Emit(#9'ldr x19, [sp, #16]');               { x19 = the result }
      if not RecretManagedClean(TRecordTypeDesc(Elem)) then
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Elem), 'x22');
      Self.Emit(#9'mov x0, x22');
      Self.Emit(#9'mov x1, x19');
      EmitIntLiteral('x2', Elem.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Self.Emit(#9'add sp, sp, #16');                  { drop [result] }
      Exit;
    end;
    EmitRecAddrToX0(AStmt.Expr);       { x0 = source record address }
    EmitPushX0();                                      { park [srcaddr] }
    EmitFieldElemAddrToX0(AStmt, Elem, IsDyn, Low);    { x0 = &element (fresh) }
    Self.Emit(#9'stp x19, x22, [sp, #-16]!');
    Self.Emit(#9'mov x22, x0');                        { x22 = dest element }
    Self.Emit(#9'ldr x19, [sp, #16]');                 { x19 = source addr }
    if not RecretManagedClean(TRecordTypeDesc(Elem)) then
    begin
      Self.EmitRecordFieldRetains(TRecordTypeDesc(Elem), 'x19');
      { copy site: no-zero release (BUG-20260720-managed-record-self-assign) }
      Self.EmitRecordFieldReleases(TRecordTypeDesc(Elem), 'x22', False);
    end;
    Self.Emit(#9'mov x0, x22');
    Self.Emit(#9'mov x1, x19');
    EmitIntLiteral('x2', Elem.RawSize());
    EmitCallSym('memcpy');
    Self.Emit(#9'ldp x19, x22, [sp], #16');
    Self.Emit(#9'add sp, sp, #16');                    { drop srcaddr }
    Exit;
  end;
  if Elem.Kind = tyInterface then
  begin
    { an interface element: value first (retained unless owned), then the
      fresh element address, then release the old obj and store both halves }
    if not EmitIntfPairToX0X1(AStmt.Expr, Elem) then
    begin
      Self.Emit(#9'stp x0, x1, [sp, #-16]!');
      EmitCallSym('_ClassAddRef');
      Self.Emit(#9'ldp x0, x1, [sp], #16');
    end;
    Self.Emit(#9'stp x0, x1, [sp, #-16]!');          { [pair] }
    EmitFieldElemAddrToX0(AStmt, Elem, IsDyn, Low);
    EmitPushX0();                                     { [pair][elemaddr] }
    Self.Emit(#9'ldr x0, [x0]');                      { old obj }
    EmitCallSym('_ClassRelease');
    EmitPopTo('x9');
    Self.Emit(#9'ldp x0, x1, [sp], #16');
    Self.Emit(#9'stp x0, x1, [x9]');
    Exit;
  end;
  if IsJumboSetType(Elem) then
  begin
    { a jumbo-set element: the value is a bitmap ADDRESS (a literal's lives
      below sp until we give it back); copy it into the fresh element }
    NB := JumboSetLiteralBytes(AStmt.Expr);
    Self.EmitExprToX0(AStmt.Expr);
    EmitPushX0();                                     { [lit][src] }
    EmitFieldElemAddrToX0(AStmt, Elem, IsDyn, Low);
    EmitPopTo('x1');
    EmitIntLiteral('x2', Elem.RawSize());
    EmitCallSym('memcpy');
    if NB > 0 then
      EmitAddSubImm('add', 'sp', 'sp', NB);
    Exit;
  end;
  if not IsIntFam(Elem) and (Elem.Kind <> tyPointer) and
     (Elem.Kind <> tyPChar) and not IsSmallSetType(Elem) then
    NotYet('field array element of this type', AStmt);
  { integer-family element: value first, then address, then store by width }
  Self.EmitExprToX0(AStmt.Expr);
  EmitPushX0();                                { [val] }
  EmitFieldElemAddrToX0(AStmt, Elem, IsDyn, Low);
  Self.Emit(#9'mov x9, x0');                   { x9 = elem address }
  EmitPopTo('x0');                             { value }
  case Elem.RawSize() of
    1: Self.Emit(#9'strb w0, [x9]');
    2: Self.Emit(#9'strh w0, [x9]');
    4: Self.Emit(#9'str w0, [x9]');
  else
    Self.Emit(#9'str x0, [x9]');
  end;
end;

procedure TArm64Backend.EmitFieldElemAddrToX0(AStmt: TFieldAssignment;
  AElem: TTypeDesc; AIsDyn: Boolean; ALow: Integer);
begin
  { x0 := address of Rec.Field[Index].  Evaluated AFTER the value expression
    (its caller parks the value), so a value that reallocates the dyn-array
    field cannot leave a stale data pointer.  Index → scaled offset, parked;
    field data pointer (deref for dyn-array) + scaled index. }
  Self.EmitExprToX0(AStmt.PropIndexExpr);
  if ALow > 0 then
    EmitAddSubImm('sub', 'x0', 'x0', ALow)
  else if ALow < 0 then
    EmitAddSubImm('add', 'x0', 'x0', -ALow);   { subtracting a negative low }
  EmitPushX0();                                { [index] }
  if AStmt.ObjExpr <> nil then
  begin
    { a chained base (A.B.Arr[I], P^.Arr[I], R.Items[J].Arr[I]): a class-typed
      base yields the instance pointer, a record-typed one its address }
    if (AStmt.ObjExpr.ResolvedType <> nil) and
       (AStmt.ObjExpr.ResolvedType.Kind = tyClass) then
    begin
      if ArcExprOwnsRef(AStmt.ObjExpr) then
        NotYet('array-field element write on an owned transient base', AStmt);
      Self.EmitExprToX0(AStmt.ObjExpr);
    end
    else
      EmitRecAddrToX0(AStmt.ObjExpr);
  end
  else if AStmt.IsImplicitSelf then
  begin
    { a field of Self's intermediate (FInner.Arr[I] inside a method): step
      from Self across it -- deref a class field, advance past a record }
    EmitLoadSlot('x0', 'Self');
    EmitImplicitBaseStep('x0', AStmt.ImplicitBaseInfo);
  end
  else if AStmt.IsClassAccess then
  begin
    EmitLoadSlot('x0', AStmt.RecordName);      { class inst: slot holds pointer }
    if AStmt.IsVarParam then
      Self.Emit(#9'ldr x0, [x0]');             { var param: slot holds &inst }
  end
  else
    { record base: a TRUE var/out param derefs the slot to the caller's record;
      a by-value/local/global record addresses the slot inline (leg 28). }
    EmitRecordBaseAddr('x0', AStmt.RecordName, AStmt.IsVarParam);
  if AStmt.FieldInfo.Offset <> 0 then
    EmitAddSubImm('add', 'x0', 'x0', AStmt.FieldInfo.Offset);
  if AIsDyn then
    Self.Emit(#9'ldr x0, [x0]');               { dyn-array: slot holds data ptr }
  EmitPopTo('x1');                             { index }
  EmitIntLiteral('x2', AElem.RawSize());
  Self.Emit(#9'mul x1, x1, x2');
  Self.Emit(#9'add x0, x0, x1');               { x0 = element address }
end;

{ ---- expressions --------------------------------------------------------- }

procedure TArm64Backend.EmitAddSubImm(const AOp, ADst, ASrc: string;
  AImm: Integer);
begin
  { add/sub immediates encode 12 bits; larger deltas (big frames — a
    4 KiB local buffer) materialise through x16 (IP0, the linker
    scratch — never live across our sequences) }
  if AImm <= 4095 then
    Self.Emit(Format(#9'%s %s, %s, #%d', [AOp, ADst, ASrc, AImm]))
  else
  begin
    EmitIntLiteral('x16', AImm);
    Self.Emit(Format(#9'%s %s, %s, x16', [AOp, ADst, ASrc]));
  end;
end;

procedure TArm64Backend.EmitPushX0;
begin
  { full 16-byte slot so sp stays aligned for any call inside the bracket }
  Self.Emit(#9'str x0, [sp, #-16]!');
end;

procedure TArm64Backend.EmitPopTo(const AReg: string);
begin
  Self.Emit(Format(#9'ldr %s, [sp], #16', [AReg]));
end;

procedure TArm64Backend.EmitIntLiteral(const AReg: string; AValue: Int64);
var
  U: Int64;
  Shift: Integer;
  Chunk: Integer;
  First: Boolean;
begin
  if (AValue >= 0) and (AValue <= $FFFF) then
  begin
    Self.Emit(Format(#9'movz %s, #%d', [AReg, AValue]));
    Exit;
  end;
  if (AValue < 0) and (AValue >= -65536) then
  begin
    Self.Emit(Format(#9'movn %s, #%d', [AReg, (not AValue) and $FFFF]));
    Exit;
  end;
  { general 64-bit: movz + movk chain over the non-zero 16-bit chunks }
  U := AValue;
  First := True;
  for Shift := 0 to 3 do
  begin
    Chunk := Integer((U shr (Shift * 16)) and $FFFF);
    if (Chunk = 0) and (not First or (Shift < 3)) and not (First and (Shift = 3)) then
      Continue;
    if First then
    begin
      Self.Emit(Format(#9'movz %s, #%d, lsl #%d', [AReg, Chunk, Shift * 16]));
      First := False;
    end
    else
      Self.Emit(Format(#9'movk %s, #%d, lsl #%d', [AReg, Chunk, Shift * 16]));
  end;
  if First then
    Self.Emit(Format(#9'movz %s, #0', [AReg]));
end;

{ Escape a string for a .ascii directive.  Mirrors the x86-64 backend's
  AsmEscapeString: every non-printable byte becomes a THREE-DIGIT OCTAL
  escape.

  A bare '\0' is not usable -- it is ambiguous with the digits that may
  follow ('\0' then "0b" is not the same as '\000' then "b"), and a raw
  high byte passed through unescaped is not portable in a quoted .ascii
  operand.  Zero-padded octal is self-terminating at three digits, so each
  byte round-trips regardless of what follows it. }
function TArm64Backend.AsmEscape(const AValue: string): string;
var
  I, C: Integer;
begin
  Result := '';
  for I := 0 to Length(AValue) - 1 do
  begin
    C := StrAt(AValue, I);
    if C = Ord('\') then Result := Result + '\\'
    else if C = Ord('"') then Result := Result + '\"'
    else if (C < 32) or (C > 126) then
      Result := Result + '\'
                + Chr(48 + ((C shr 6) and 7))
                + Chr(48 + ((C shr 3) and 7))
                + Chr(48 + (C and 7))
    else Result := Result + Chr(C);
  end;
end;

procedure TArm64Backend.EmitImplicitBaseStep(const AReg: string;
  ABaseInfo: TFieldInfo);
begin
  if ABaseInfo = nil then Exit;
  if (ABaseInfo.TypeDesc <> nil) and (ABaseInfo.TypeDesc.Kind = tyClass) then
    { class reference: the field holds a POINTER — load it and continue from
      the pointee (ldr even at offset 0, so the base becomes the instance). }
    Self.Emit(Format(#9'ldr %s, [%s, #%d]', [AReg, AReg, ABaseInfo.Offset]))
  else if ABaseInfo.Offset <> 0 then
    { embedded record: its bytes are inline, so just advance the base. }
    EmitAddSubImm('add', AReg, AReg, ABaseInfo.Offset);
end;

procedure TArm64Backend.EmitStrLen(const AReg: string);
var
  NilL: string;
begin
  { AReg holds a string DATA pointer; replace it with the string's length.
    In Blaise a nil pointer IS the empty string, so the header read at
    [ptr-8] must be nil-guarded (a bare read of [nil-8] faults) — mirrors
    _StringLength / StrLen, which return 0 for nil. }
  NilL := NewLabel('slen0');
  Self.Emit(Format(#9'cbz %s, %s', [AReg, NilL]));
  Self.Emit(Format(#9'ldur w0, [%s, #-8]', [AReg]));
  if AReg <> 'x0' then
    Self.Emit(Format(#9'mov %s, x0', [AReg]));
  Self.Emit(Format(#9'b %s_done', [NilL]));
  Self.Emit(NilL + ':');
  Self.Emit(Format(#9'movz %s, #0', [AReg]));
  Self.Emit(NilL + '_done:');
end;

procedure TArm64Backend.EmitByteRhsToX0(AValueExpr: TASTExpr);
var
  FC: TFuncCallExpr;
begin
  { single-char literal -> its ordinal (not the literal's data address) }
  if AValueExpr is TStringLiteral then
  begin
    if Length(TStringLiteral(AValueExpr).Value) = 0 then
      Self.Emit(#9'movz x0, #0')
    else
      EmitIntLiteral('x0', OrdAt(TStringLiteral(AValueExpr).Value, 0));
    Exit;
  end;
  { Chr(N) -> N directly, WITHOUT the _Chr allocation: a strb of a _Chr result
    would store the low byte of the returned heap pointer. }
  if (AValueExpr is TFuncCallExpr) then
  begin
    FC := TFuncCallExpr(AValueExpr);
    if (FC.ResolvedDecl = nil) and (FC.Args.Count = 1) and
       SameText(FC.Name, 'Chr') then
    begin
      Self.EmitExprToX0(TASTExpr(FC.Args.Items[0]));
      Exit;
    end;
  end;
  Self.EmitExprToX0(AValueExpr);
end;

procedure TArm64Backend.EmitStrLitAddr(AValue: string);
var
  Idx: Integer;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  { pointer = blob + 12 (past the refcnt/len/cap header — same immutable
    string layout the x86-64 backend emits) }
  Self.Emit(Format(#9'adrp x0, __s%d@PAGE', [Idx]));
  Self.Emit(Format(#9'add x0, x0, __s%d@PAGEOFF', [Idx]));
  Self.Emit(#9'add x0, x0, #12');
end;

procedure TArm64Backend.EmitConstArrayElemToVarRec(AElem: TASTExpr;
  AOffset: Integer);
var
  EK: TTypeKind;
  Tag: Integer;
begin
  EK := AElem.ResolvedType.Kind;
  if EK in [tyDouble, tySingle] then
  begin
    { vtExtended(3): heap-box the double.  The block address is sp-relative,
      so build the box FIRST (which parks d0 across the _BlaiseGetMem call and
      restores sp) and only then compute [sp,#AOffset]. }
    Self.EmitExprToD0OrConvert(AElem);      { widens tySingle -> double in d0 }
    Self.Emit(#9'str d0, [sp, #-16]!');     { park the double across the call }
    EmitIntLiteral('x0', 8);
    EmitCallSym('_BlaiseGetMem');        { x0 = box ptr }
    Self.Emit(#9'ldr d0, [sp], #16');       { restore double (sp back to base) }
    Self.Emit(#9'str d0, [x0]');            { *box = double }
    { x0 = box ptr; store as VValue, tag 3 as VType }
    EmitAddSubImm('add', 'x9', 'sp', AOffset);
    Self.Emit(#9'str x0, [x9, #8]');
    Self.Emit(#9'mov w0, #3');
    Self.Emit(#9'strb w0, [x9]');
    Exit;
  end;
  { integer/string/object families: evaluate to x0, then box. }
  case EK of
    tyBoolean:
      begin Tag := 1; Self.EmitExprToX0(AElem);
        Self.Emit(#9'and x0, x0, #0xff'); end;   { zero-extend the byte }
    tyInteger, tyUInt32, tyByte, tySmallInt, tyWord:
      begin Tag := 0; Self.EmitExprToX0(AElem);
        Self.Emit(#9'sxtw x0, w0'); end;          { sign-extend to 64 bits }
    tyEnum:
      begin Tag := 24; Self.EmitExprToX0(AElem);
        Self.Emit(#9'sxtw x0, w0'); end;
    tyInt64, tyUInt64:
      begin Tag := 16; Self.EmitExprToX0(AElem); end;
    tyString:
      begin Tag := 20; Self.EmitExprToX0(AElem); end;  { borrow the data ptr }
    tyClass, tyMetaClass:
      begin Tag := 7; Self.EmitExprToX0(AElem); end;    { borrow the obj ptr }
  else
    Tag := 5; Self.EmitExprToX0(AElem);                 { vtPointer }
  end;
  EmitAddSubImm('add', 'x9', 'sp', AOffset);
  Self.Emit(#9'str x0, [x9, #8]');                 { VValue at +8 }
  Self.Emit(Format(#9'mov w0, #%d', [Tag]));
  Self.Emit(#9'strb w0, [x9]');                    { VType byte at +0 }
end;

procedure TArm64Backend.EmitCondToX0Flushed(AExpr: TASTExpr);
var
  Mark: Integer;
begin
  Mark := FPendingRelCount;
  Self.EmitExprToX0(AExpr);
  if FPendingRelCount > Mark then
  begin
    { the condition deferred a transient base — preserve the boolean result
      across the flush (FlushNativePendingReleases clobbers x0) }
    EmitPushX0();
    FlushNativePendingReleases(Mark);
    EmitPopTo('x0');
  end;
end;

procedure TArm64Backend.EmitExprToX0(AExpr: TASTExpr);
var
  BE: TBinaryExpr;
  JTmp: string;
  DivGuardOk: string;
  DivUnsigned: Boolean;
  CmpUnsigned: Boolean;
  CondName: string;
  Lit: string;
  Idx, I: Integer;
  EmptyArgs: TObjectList;
begin
  { ClassCreate carries the resolved CONSTRUCTOR in ResolvedDecl, so it must
    be claimed before any arm that lowers a resolved call as a plain call }
  if (AExpr is TFuncCallExpr) and
     SameText(TFuncCallExpr(AExpr).Name, 'ClassCreate') and
     (TFuncCallExpr(AExpr).Args.Count >= 1) then
  begin
    EmitClassCreate(TFuncCallExpr(AExpr));
    Exit;
  end;
  if IsJumboSetType(AExpr.ResolvedType) and
     (((AExpr is TFuncCallExpr) and
       (TFuncCallExpr(AExpr).ResolvedDecl <> nil)) or
      ((AExpr is TMethodCallExpr) and
       (TMethodCallExpr(AExpr).ResolvedMethod <> nil) and
       not TMethodCallExpr(AExpr).IsConstructorCall and
       not TMethodCallExpr(AExpr).IsProcFieldCall)) then
  begin
    { a jumbo-set-returning call: the callee fills a per-site frame scratch
      through x8, and -- like every jumbo set value -- the call evaluates to
      that bitmap's ADDRESS.  Per site, so two such calls in one expression
      (F(A) + F(B)) cannot overwrite each other's result. }
    if (AExpr is TFuncCallExpr) and
       TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl).IsExternal then
      NotYet('external jumbo-set-returning call', AExpr);
    JTmp := '__jret_' + IntToStr(FJArgN);
    FJArgN := FJArgN + 1;
    if not FFrame.ContainsKey(JTmp) then
      AddLocal(JTmp, AExpr.ResolvedType.RawSize());
    EmitRecCallDispatch(AExpr, JTmp);
    EmitSlotAddr('x0', JTmp);
    Exit;
  end;
  if AExpr is TIntLiteral then
  begin
    EmitIntLiteral('x0', TIntLiteral(AExpr).Value);
    Exit;
  end;
  if AExpr is TAnonMethodExpr then
  begin
    { closure literal: materialise the fat value into its hidden slot; x0 holds
      the slot ADDRESS (the value is used by reference — leg 38). }
    EmitAnonValueToSlot(TAnonMethodExpr(AExpr));
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and TFuncCallExpr(AExpr).IsProcFieldCall then
  begin
    { Handler(args) as an expression inside a method, Handler a procedural-
      typed field of Self (BUG-20260922) }
    EmitProcFieldCall('', nil, False, True, nil,
      TFuncCallExpr(AExpr).ProcFieldInfo, TFuncCallExpr(AExpr).Args, AExpr);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsConstructorCall then
  begin
    { `TFoo.Create` WITHOUT parentheses: the parser yields a field access
      flagged IsConstructorCall rather than a method call.  It means exactly
      TFoo.Create(), so lower it through the same constructor path
      (allocate at rc 0, install the vtable, run a declared Create body). }
    EmitParenlessCtor(TFieldAccessExpr(AExpr));
    Exit;
  end;
  if AExpr is TStringLiteral then
  begin
    if TStringLiteral(AExpr).IsCharCoerce then
      { char/ordinal context (e.g. BufP[I] = '/'): the semantic pass marked
        this single-char literal for ordinal coercion.  Emitting the data
        pointer here would compare a byte against the string's ADDRESS — always
        false — which broke the RTL's ForceDirectories slash-scan on arm64
        (macOS arm64, 2026-07-24).  Mirror the x86-64 backend's fold. }
      EmitIntLiteral('x0', TStringLiteral(AExpr).CharOrdValue)
    else
      EmitStrLitAddr(TStringLiteral(AExpr).Value);
    Exit;
  end;
  if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsMetaclassRef then
  begin
    { bare class name as a value: the typeinfo address IS the metaclass }
    EmitTypeinfoAddr('x0', TIdentExpr(AExpr).Name);
    Exit;
  end;
  if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsImplicitSelf and
     (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then
  begin
    { bare field name inside a method: compute the field ADDRESS (Self + offset)
      then load width-keyed via EmitElemLoad.  A raw `ldr x0, [x0, #Offset]`
      (8-byte scaled) was both a WIDTH bug (it read 8 bytes of a 1/2/4-byte
      field) and an ENCODING bug (a field at a large or non-8-aligned byte
      offset — e.g. a Boolean/Integer at offset 309 in a class with packed small
      fields — is not a valid scaled immediate).  EmitAddSubImm materialises any
      offset (>4095 via x16); EmitElemLoad loads the correct width. }
    EmitLoadSlot('x0', 'Self');
    if TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset);
    EmitElemLoad(TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).TypeDesc);
    Exit;
  end;
  if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsConstant then
  begin
    { named constant / enum member — folded by the semantic pass }
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyString) then
    begin
      Idx := FStrLits.IndexOf(TIdentExpr(AExpr).ConstString);
      if Idx < 0 then
        Idx := FStrLits.Add(TIdentExpr(AExpr).ConstString);
      Self.Emit(Format(#9'adrp x0, __s%d@PAGE', [Idx]));
      Self.Emit(Format(#9'add x0, x0, __s%d@PAGEOFF', [Idx]));
      Self.Emit(#9'add x0, x0, #12');
      Exit;
    end;
    EmitIntLiteral('x0', TIdentExpr(AExpr).ConstValue);
    Exit;
  end;
  if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsImplicitSelfMethod and
     (TIdentExpr(AExpr).ImplicitMethodDecl <> nil) then
  begin
    { bare zero-arg method call on Self written without parens }
    if (AExpr.ResolvedType <> nil) and
       IsAggregateReturn(AExpr.ResolvedType) then
      NotYet('aggregate-returning bare method call', AExpr);
    EmitLoadSlot('x0', 'Self');
    EmptyArgs := TObjectList.Create(False);
    try
      EmitMethodCallCommon(
        TMethodDecl(TIdentExpr(AExpr).ImplicitMethodDecl),
        TIdentExpr(AExpr).Name, EmptyArgs);
    finally
      EmptyArgs.Free();
    end;
    Exit;
  end;
  if AExpr is TIdentExpr then
  begin
    if (AExpr.ResolvedType is TSetTypeDesc) and
       TSetTypeDesc(AExpr.ResolvedType).IsJumbo() then
    begin
      { A JUMBO set is an inline byte bitmap: as an operand it evaluates to
        its ADDRESS (what _SetIn / _SetInclude / the jumbo operators take).
        Loading the slot handed the bitmap's first 8 bytes over as if they
        were a pointer, so `E in J` on a jumbo VARIABLE read garbage. }
      if IsCaptured(TIdentExpr(AExpr).Name) then
      begin
        EmitLoadSlot('x0', '_cap_' + TIdentExpr(AExpr).Name);
        if TIdentExpr(AExpr).ParamMode = pmVar then
          Self.Emit(#9'ldr x0, [x0]');
      end
      else if TIdentExpr(AExpr).ParamMode = pmVar then
        EmitLoadSlot('x0', TIdentExpr(AExpr).Name)   { slot holds &set }
      else
        EmitSlotAddr('x0', TIdentExpr(AExpr).Name);
      Exit;
    end;
    if IsCaptured(TIdentExpr(AExpr).Name) then
    begin
      { captured outer var (leg 17): '_cap_<Name>' holds &<Name>, so deref
        once for the value.  A captured var-param's outer storage itself
        holds the caller's address, so a var-param capture needs a second
        deref — matching the direct-var path below. }
      EmitCapturedLoad(TIdentExpr(AExpr));
      Exit;
    end;
    EmitLoadSlot('x0', TIdentExpr(AExpr).Name);
    if TIdentExpr(AExpr).ParamMode = pmVar then
      Self.Emit(#9'ldr x0, [x0]');   { var param: slot holds the address }
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]) is TIdentExpr) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind =
       tyOpenArray) and
     (SameText(TFuncCallExpr(AExpr).Name, 'High') or
      SameText(TFuncCallExpr(AExpr).Name, 'Low') or
      SameText(TFuncCallExpr(AExpr).Name, 'Length')) then
  begin
    { open-array bounds live in the (ptr, high) slot pair: High reads
      the companion slot, Length is High + 1, Low is always 0 }
    if SameText(TFuncCallExpr(AExpr).Name, 'Low') then
      Self.Emit(#9'movz x0, #0')
    else
    begin
      EmitLoadSlot('x0',
        TIdentExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])).Name
        + '_high');
      if SameText(TFuncCallExpr(AExpr).Name, 'Length') then
        Self.Emit(#9'add x0, x0, #1');
    end;
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind =
       tyStaticArray) and
     (SameText(TFuncCallExpr(AExpr).Name, 'High') or
      SameText(TFuncCallExpr(AExpr).Name, 'Low')) then
  begin
    { static-array bounds are compile-time constants }
    if SameText(TFuncCallExpr(AExpr).Name, 'High') then
      EmitIntLiteral('x0', TStaticArrayTypeDesc(
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType).HighBound)
    else
      EmitIntLiteral('x0', TStaticArrayTypeDesc(
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType).LowBound);
    Exit;
  end;
  { Length(static array) = HighBound - LowBound + 1 (compile-time). }
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind =
       tyStaticArray) and
     SameText(TFuncCallExpr(AExpr).Name, 'Length') then
  begin
    EmitIntLiteral('x0',
      TStaticArrayTypeDesc(
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType).HighBound -
      TStaticArrayTypeDesc(
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType).LowBound + 1);
    Exit;
  end;
  { Type-level High/Low of an ENUM or scalar-integer argument — a compile-time
    constant.  High(enum) is the MAX stored ordinal and Low(enum) the MIN (which
    may be negative) — NOT member-count-1 / 0, since an explicit-ordinal enum
    (TE=(A=5,B=10)) is not contiguous 0-based
    (BUG-20260720-enum-explicit-ordinal-highlow).  Mirrors x86-64.
    EmitIntLiteral materialises every immediate via movz/movk (no sign-extension
    trap), so the large scalar bounds are exact. }
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind in
       [tyEnum, tyByte, tyBoolean, tySmallInt, tyWord, tyInteger,
        tyUInt32, tyInt64, tyUInt64]) and
     (SameText(TFuncCallExpr(AExpr).Name, 'High') or
      SameText(TFuncCallExpr(AExpr).Name, 'Low')) then
  begin
    { High/Low(subrange) is the subrange's own bound (Low may be negative), not
      the base type's — the descriptor's Kind is the narrowest fitting int but
      SubrangeLow/High carry the real bounds (GH #160). }
    if TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.IsSubrange then
    begin
      if SameText(TFuncCallExpr(AExpr).Name, 'High') then
        EmitIntLiteral('x0',
          TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.SubrangeHigh)
      else
        EmitIntLiteral('x0',
          TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.SubrangeLow);
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'High') then
      case TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind of
        tyEnum:     EmitIntLiteral('x0', TEnumTypeDesc(
          TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType)
            .MaxOrdinal());
        tyByte:     EmitIntLiteral('x0', 255);
        tyBoolean:  EmitIntLiteral('x0', 1);
        tySmallInt: EmitIntLiteral('x0', 32767);
        tyWord:     EmitIntLiteral('x0', 65535);
        tyInteger:  EmitIntLiteral('x0', 2147483647);
        tyUInt32:   EmitIntLiteral('x0', 4294967295);
        tyInt64:    EmitIntLiteral('x0', 9223372036854775807);
        tyUInt64:   EmitIntLiteral('x0', -1);   { all-ones bit pattern }
      end
    else
      { Low: enum = MIN stored ordinal (may be negative); byte/bool/word/unsigned
        = 0; signed ints reach their min }
      case TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind of
        tyEnum:     EmitIntLiteral('x0', TEnumTypeDesc(
          TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType)
            .MinOrdinal());
        tySmallInt: EmitIntLiteral('x0', -32768);
        tyInteger:  EmitIntLiteral('x0', -2147483648);
        tyInt64:    EmitIntLiteral('x0', Int64($8000000000000000));
      else
        EmitIntLiteral('x0', 0);
      end;
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind =
       tyDynArray) and
     SameText(TFuncCallExpr(AExpr).Name, 'High') then
  begin
    { High(D) = Length(D) - 1 }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitCallSym('_DynArrayLength');
    Self.Emit(#9'sub x0, x0, #1');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     SameText(TFuncCallExpr(AExpr).Name, 'Length') and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind =
       tyDynArray) then
  begin
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitCallSym('_DynArrayLength');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.IsString()
     and SameText(TFuncCallExpr(AExpr).Name, 'Length') then
  begin
    { Length(S): 4-byte length 8 bytes below the data pointer.  In Blaise a
      nil pointer IS the empty string, so the read must be nil-guarded — a bare
      `ldur w0,[x0,#-8]` on a nil string reads [nil-8] and faults (this crashed
      the .bif writer's EncodeLpstr on an empty routine field, macOS arm64,
      2026-07-24).  _StringLength / StrLen already returns 0 for nil; EmitStrLen
      mirrors that with an inline cbz guard.  A transient argument is disposed
      by shape with the length parked. }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    if ArcBuiltinStrArgOwnsRef(
         TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])) then
    begin
      EmitPushX0();
      EmitStrLen('x0');
      EmitPushX0();
      Self.Emit(#9'ldr x0, [sp, #16]');
      EmitStrDisposeX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitPopTo('x0');
      Self.Emit(#9'add sp, sp, #16');
      Exit;
    end;
    EmitStrLen('x0');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 1) then
  begin
    { one-string-arg RTL builtins (the sysutils file/string surface) —
      each disposes a transient argument by shape (handover doc rule) }
    if SameText(TFuncCallExpr(AExpr).Name, 'FileExists') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_FileExists');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'DirectoryExists') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_DirectoryExists');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ReadFile') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ReadFile');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'FileAge') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_FileAge');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ForceDirectories') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ForceDirectories');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Trim') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_StringTrim');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'LowerCase') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_StringLowerCase');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'UpperCase') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_StringUpperCase');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ExtractFilePath') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ExtractFilePath');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ExtractFileName') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ExtractFileName');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ExtractFileDir') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ExtractFileDir');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ExtractFileExt') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ExtractFileExt');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ListDir') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ListDir');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'GetEnvVar') or
       SameText(TFuncCallExpr(AExpr).Name, 'GetEnvironmentVariable') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_GetEnvVar');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'SetCurrentDir') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_SetCurrentDir');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'StrToInt') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_StrToInt');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'StrToInt64') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_StrToInt64');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Exec') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_Exec');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name,
         'IncludeTrailingPathDelimiter') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_IncludeTrailingPathDelimiter');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name,
         'ExcludeTrailingPathDelimiter') then
    begin
      EmitBuiltinStrCall1(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        '_ExcludeTrailingPathDelimiter');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ParamStr') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_ParamStr');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'UpCase') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      { _UpCase takes an INTEGER char code.  A STRING argument (UpCase(Chr(C)),
        UpCase(S[i]), etc.) must first be reduced to its first char's code via
        _OrdAt(S, 0) — passing the string POINTER straight through makes _UpCase
        run _Chr on the pointer, yielding a char whose code is the pointer's low
        byte (garbage).  This broke DirectiveName/DirectiveArg (UpCase(Chr(C))),
        which silently disabled ALL $IFDEF/$ELSE conditional compilation on the
        arm64 build (macOS arm64, 2026-07-24).  Mirror the x86-64 backend. }
      if (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
         TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.IsString()
      then
      begin
        Self.Emit(#9'mov x1, #0');
        EmitCallSym('_OrdAt');
      end;
      EmitCallSym('_UpCase');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Assigned') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      Self.Emit(#9'cmp x0, #0');
      Self.Emit(#9'cset x0, ne');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Pred') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      Self.Emit(#9'sub x0, x0, #1');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Succ') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      Self.Emit(#9'add x0, x0, #1');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'GetMem') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_BlaiseGetMem');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'DoubleToStr') and
       (TFuncCallExpr(AExpr).Args.Count = 1) then
    begin
      { float -> shortest round-trip decimal string.  EmitExprToD0OrConvert
        leaves any numeric argument (Single, Double or integer) as a Double
        in d0, which is _DoubleToStr's ABI.  Mirrors x86-64. }
      Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_DoubleToStr');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'SingleToStr') and
       (TFuncCallExpr(AExpr).Args.Count = 1) then
    begin
      { _SingleToStr takes a genuine 32-bit Single in s0: narrow the Double
        the argument evaluates to (cf. GH #200 -- reading the wrong width
        printed garbage digits) }
      Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      Self.Emit(#9'fcvt s0, d0');
      EmitCallSym('_SingleToStr');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Abs') and
       (TFuncCallExpr(AExpr).Args.Count = 1) and
       not IsFloatExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])) then
    begin
      { integer Abs: negate when negative.  An Integer is held sign-extended
        in x0, so the 64-bit test and negate are exact for every width. }
      Lit := NewLabel('absok');
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      Self.Emit(#9'cmp x0, #0');
      Self.Emit(Format(#9'b.ge %s', [Lit]));
      Self.Emit(#9'mvn x0, x0');
      Self.Emit(#9'add x0, x0, #1');
      Self.Emit(Lit + ':');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'IntToStr') then
    begin
      { integer argument — no transient to dispose.  A UInt64 needs the
        unsigned formatter: _Int64ToStr would print a value with the high
        bit set as negative.  Every narrower type arrives in x0 already
        sign- or zero-extended to its 64-bit value. }
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      if (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind = tyUInt64) then
        EmitCallSym('_UInt64ToStr')
      else
        EmitCallSym('_Int64ToStr');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Int64ToStr') then
    begin
      { Int64 -> decimal string; same lowering as IntToStr, which already
        routes through _Int64ToStr.  Integer argument, no transient to
        dispose.  Mirrors x86-64's Int64ToStr case. }
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_Int64ToStr');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'UInt64ToStr') then
    begin
      { unsigned 64-bit -> decimal string.  Mirrors x86-64's UInt64ToStr case. }
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_UInt64ToStr');
      Exit;
    end;
    { float -> integer.  Mirrors x86-64 exactly: round/floor/ceil go through
      the pure-Pascal runtime.math helper first (_BlaiseRoundD is the musl
      round() port -- half-AWAY-from-zero, which the FPU rounding mode would
      get wrong) and the integral result is then truncated, so the semantics
      match the x86-64 and QBE backends with no libm/libSystem dependency.
      AArch64's one-instruction fcvtas/fcvtms/fcvtps would also work, but the
      internal assembler implements only fcvtzs of that family today.
      EmitExprToD0OrConvert promotes a Single operand to double, and AAPCS
      passes/returns the double in d0, so no shuffling is needed. }
    if SameText(TFuncCallExpr(AExpr).Name, 'Trunc') then
    begin
      Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      Self.Emit(#9'fcvtzs x0, d0');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Round') then
    begin
      Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_BlaiseRoundD');
      Self.Emit(#9'fcvtzs x0, d0');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Floor') then
    begin
      Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_BlaiseFloorD');
      Self.Emit(#9'fcvtzs x0, d0');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Ceil') then
    begin
      Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_BlaiseCeilD');
      Self.Emit(#9'fcvtzs x0, d0');
      Exit;
    end;
    { process-control family (expression context): each takes the process
      handle (a pointer) and returns an int/pointer — pointer arg, no
      transient to dispose }
    if SameText(TFuncCallExpr(AExpr).Name, 'ProcessRunning') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_ProcessRunning');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ProcessReadOutput') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_ProcessReadOutput');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ProcessExitCode') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym('_ProcessExitCode');
      Exit;
    end;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 2) and
     SameText(TFuncCallExpr(AExpr).Name, 'MethodAddress') then
  begin
    { MethodAddress(Instance, 'Name') — published-method lookup through
      typeinfo[3] (see EmitMethodsTable).  x0 = instance, x1 = the name's
      string DATA pointer: a literal is addressed straight at its blob, any
      other expression already evaluates to a data pointer.  Mirrors
      x86-64's MethodAddress case.  Two args, so this sits OUTSIDE the
      one-arg builtin block above. }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitPushX0();
    if TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]) is TStringLiteral then
      EmitStrLitAddr(
        TStringLiteral(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1])).Value)
    else
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
    Self.Emit(#9'mov x1, x0');
    EmitPopTo('x0');
    EmitCallSym('_MethodAddress');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 0) then
  begin
    if SameText(TFuncCallExpr(AExpr).Name, 'ParamCount') then
    begin
      EmitCallSym('_ParamCount');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'GetCurrentDir') then
    begin
      EmitCallSym('_GetCurrentDir');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'GetTempDir') then
    begin
      EmitCallSym('_GetTempDir');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'CurrentExceptionMessage') then
    begin
      EmitCallSym('_CurrentExceptionMessage');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'GetProcessID') then
    begin
      EmitCallSym('_GetProcessID');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ProcessCreate') then
    begin
      { allocate a process handle — returns a pointer in x0 }
      EmitCallSym('_ProcessCreate');
      Exit;
    end;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count > 2) and
     SameText(TFuncCallExpr(AExpr).Name, 'Format') then
  begin
    { Format(F, A, B, ...) -- the bare variadic form with several values }
    Self.EmitFormatCall(TFuncCallExpr(AExpr).Args);
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 2) then
  begin
    if SameText(TFuncCallExpr(AExpr).Name, 'Format') then
    begin
      Self.EmitFormatCall(TFuncCallExpr(AExpr).Args);
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'Pos') then
    begin
      EmitBuiltinStrCall2(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]), '_StringPos');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'SameText') then
    begin
      EmitBuiltinStrCall2(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]), '_StringSameText');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'CompareStr') then
    begin
      EmitBuiltinStrCall2(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]), '_StringCompare');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'CompareText') then
    begin
      EmitBuiltinStrCall2(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]), '_StringCompareText');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'OrdAt') then
    begin
      { OrdAt(S, I): byte value at 0-based index — (str, int) args }
      if ArcExprOwnsRef(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])) then
        NotYet('owned transient argument to OrdAt', AExpr);
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitPushX0();
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
      Self.Emit(#9'mov x1, x0');
      EmitPopTo('x0');
      EmitCallSym('_OrdAt');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ChangeFileExt') then
    begin
      EmitBuiltinStrCall2(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]), '_ChangeFileExt');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'RenameFile') then
    begin
      EmitBuiltinStrCall2(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]), '_RenameFile');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'GetTempFileName') then
    begin
      EmitBuiltinStrCall2(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]),
        TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]), '_GetTempFileName');
      Exit;
    end;
    if SameText(TFuncCallExpr(AExpr).Name, 'ReallocMem') then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitPushX0();
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
      Self.Emit(#9'mov x1, x0');
      EmitPopTo('x0');
      EmitCallSym('_BlaiseReallocMem');
      Exit;
    end;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 3) and
     (SameText(TFuncCallExpr(AExpr).Name, 'Copy') or
      SameText(TFuncCallExpr(AExpr).Name, 'PosEx')) then
  begin
    { Copy(S, I, N) / PosEx(Sub, S, From): three args, first two may be
      string transients — full parking bracket like the 2-arg helper }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitPushX0();
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
    EmitPushX0();
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[2]));
    Self.Emit(#9'mov x2, x0');
    Self.Emit(#9'ldr x1, [sp]');
    Self.Emit(#9'ldr x0, [sp, #16]');
    if SameText(TFuncCallExpr(AExpr).Name, 'Copy') then
      EmitCallSym('_StringCopy')
    else
      EmitCallSym('_StringPosEx');
    EmitPushX0();
    if ArcBuiltinStrArgOwnsRef(
         TASTExpr(TFuncCallExpr(AExpr).Args.Items[1])) then
    begin
      Self.Emit(#9'ldr x0, [sp, #16]');
      EmitStrDisposeX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
    end;
    if ArcBuiltinStrArgOwnsRef(
         TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])) then
    begin
      Self.Emit(#9'ldr x0, [sp, #32]');
      EmitStrDisposeX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    end;
    EmitPopTo('x0');
    Self.Emit(#9'add sp, sp, #32');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     SameText(TFuncCallExpr(AExpr).Name, 'string') and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.Kind = tyPChar) then
  begin
    { string(pchar): copy the NUL-terminated bytes into a new string (an
      rc = 0 buffer, like the other RTL string helpers; ArcExprOwnsRef
      treats the cast as borrowed, so a store retains it).  Treating it as
      a reinterpret handed the RTL a raw PChar with no string header. }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitCallSym('_StringFromPChar');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (SameText(TFuncCallExpr(AExpr).Name, 'PChar') or
      SameText(TFuncCallExpr(AExpr).Name, 'Pointer')) then
  begin
    { PChar(x)/Pointer(x): bit-level reinterpret — a Blaise string data
      pointer is already NUL-terminated, so it IS the PChar value }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     SameText(TFuncCallExpr(AExpr).Name, 'SizeOf') and
     (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) then
  begin
    { SizeOf(x): compile-time constant — the resolved type's byte size }
    EmitIntLiteral('x0',
      TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.ByteSize());
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     SameText(TFuncCallExpr(AExpr).Name, 'Ord') then
  begin
    { Ord(x): a char literal folds to its byte; any other ordinal is already
      its own value (Char IS its byte in this backend). }
    if TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]) is TStringLiteral then
    begin
      if Length(TStringLiteral(
           TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])).Value) = 0 then
        Self.Emit(#9'movz x0, #0')
      else
        EmitIntLiteral('x0', OrdAt(TStringLiteral(
          TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])).Value, 0));
      Exit;
    end;
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     SameText(TFuncCallExpr(AExpr).Name, 'Chr') then
  begin
    { Chr(N) is the INVERSE of Ord: the semantic pass types it tyString, so it
      must return a freshly-allocated one-character heap string — lower it to
      the _Chr RTL helper, matching x86-64 and QBE.  It was previously folded
      into the Ord identity case above, which returned the raw ordinal: a
      `S := S + Chr(C)` then handed StringConcat a small integer as its string
      operand and faulted dereferencing it (macOS arm64, 2026-07-23; x86-64
      carried the identical bug once and its fix comment records the same
      symptom).  Byte-store contexts (S[I] := Chr(N)) must NOT allocate — they
      go through EmitByteRhsToX0 below, which keeps the raw-ordinal form. }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitCallSym('_Chr');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     TFuncCallExpr(AExpr).IsBuiltinHasClassAttr and
     (TFuncCallExpr(AExpr).Args.Count = 2) then
  begin
    { HasClassAttribute(AClass, AAttrClass): both args lower to typeinfo
      pointers; the walk lives in the RTL helper }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitPushX0();
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
    Self.Emit(#9'mov x1, x0');
    EmitPopTo('x0');
    EmitCallSym('_HasClassAttribute');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).AttrRTTIBuiltin <> '') and
     (TFuncCallExpr(AExpr).Args.Count >= 2) then
  begin
    { GetClassAttribute / HasMethodAttribute / GetMethodAttribute /
      MethodAttributeCount / GetMethodAttributeAt — args in x0..x2, the
      same-named RTL helper does the table walk.  The helpers are Blaise
      functions, so results come back as clean 64-bit values. }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitPushX0();
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
    EmitPushX0();
    if TFuncCallExpr(AExpr).Args.Count = 3 then
    begin
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[2]));
      Self.Emit(#9'mov x2, x0');
    end;
    EmitPopTo('x1');
    EmitPopTo('x0');
    EmitCallSym('_' + TFuncCallExpr(AExpr).AttrRTTIBuiltin);
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (AExpr.ResolvedType <> nil) and
     { the name denotes a TYPE: either the table resolves it, or -- for a
       type declared inside a unit, which the program-level table cannot
       see (PStackNode in the fiber runtime) -- the call's result type IS
       that named type.  A builtin's result type never carries the builtin's
       own name, so an unlowered builtin still reaches the honest NotYet. }
     (((FSymTable <> nil) and
       (FSymTable.FindType(TFuncCallExpr(AExpr).Name) <> nil)) or
      SameText(AExpr.ResolvedType.Name, TFuncCallExpr(AExpr).Name)) and
     (IsIntFam(AExpr.ResolvedType) or
      (AExpr.ResolvedType.Kind in [tyPointer, tyPChar, tyClass,
                                   tyString, tyProcedural])) then
  begin
    { TypeName(x): a value cast, NOT a builtin — the name resolves to a
      TYPE.  Evaluate the operand and normalise to the target width
      (pointer-like, class and string targets pass through — string(pchar)
      is pointer-preserving, treated as borrowed like the other backends). }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    EmitNarrowX0(AExpr.ResolvedType);
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and TFuncCallExpr(AExpr).IsIndirectCall and
     IsMethodPtrType(TTypeDesc(TFuncCallExpr(AExpr).ResolvedProcType)) then
  begin
    { call through a closure / method-pointer variable (a 16-byte fat value):
      route to EmitFatPtrCall with the ADDRESS of the fat value.  Non-float,
      non-aggregate return only in this slice. }
    if IsFloatExpr(AExpr) then
      NotYet('float-returning closure call in integer context', AExpr);
    if (AExpr.ResolvedType <> nil) and
       IsAggregateReturn(AExpr.ResolvedType) then
      NotYet('aggregate-returning closure call', AExpr);
    EmitSlotAddr('x9', TFuncCallExpr(AExpr).Name);
    EmitFatPtrCall('x9',
      TProceduralTypeDesc(TFuncCallExpr(AExpr).ResolvedProcType),
      TFuncCallExpr(AExpr).Args);
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and TFuncCallExpr(AExpr).IsIndirectCall and
     (TFuncCallExpr(AExpr).Args.Count <= 8) then
  begin
    { call through a procedural-typed variable, expression position:
      int-class args in x0.., fptr from the variable's slot, blr }
    GuardNoOpenArrayParam(
      TProceduralTypeDesc(TFuncCallExpr(AExpr).ResolvedProcType), AExpr);
    for I := 0 to TFuncCallExpr(AExpr).Args.Count - 1 do
    begin
      if not (IsIntFam(TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])
                .ResolvedType) or
              (TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])
                 is TIntLiteral) or
              (TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])
                 is TNilLiteral) or
              ((TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])
                  .ResolvedType <> nil) and
               (TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])
                  .ResolvedType.Kind in [tyPChar, tyPointer,
                                         tyClass, tyString,
                                         tyMetaClass]))) then
        NotYet('indirect-call argument of this type',
          TASTExpr(TFuncCallExpr(AExpr).Args.Items[I]));
      { a string arg passes as a BORROWED pointer; an owned transient
        would need a park slot — keep the hole honest }
      if ArcExprOwnsRef(TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])) then
        NotYet('owned transient argument in an indirect call',
          TASTExpr(TFuncCallExpr(AExpr).Args.Items[I]));
      Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[I]));
      EmitPushX0();
    end;
    for I := TFuncCallExpr(AExpr).Args.Count - 1 downto 0 do
      EmitPopTo('x' + IntToStr(I));
    EmitLoadSlot('x9', TFuncCallExpr(AExpr).Name);
    Self.Emit(#9'blr x9');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     TFuncCallExpr(AExpr).IsImplicitSelfMethod and
     (TFuncCallExpr(AExpr).ResolvedDecl <> nil) then
  begin
    { bare method call on Self in expression position }
    if IsFloatExpr(AExpr) then
      NotYet('float-returning implicit-Self call in integer context', AExpr);
    if (AExpr.ResolvedType <> nil) and
       IsAggregateReturn(AExpr.ResolvedType) then
      NotYet('aggregate-returning implicit-Self call', AExpr);
    EmitLoadSlot('x0', 'Self');
    EmitMethodCallCommon(
      TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl),
      TFuncCallExpr(AExpr).Name, TFuncCallExpr(AExpr).Args);
    Exit;
  end;
  if AExpr is TFuncCallExpr then
  begin
    if TFuncCallExpr(AExpr).IsIndirectCall or
       TFuncCallExpr(AExpr).IsImplicitSelfMethod or
       (TFuncCallExpr(AExpr).ResolvedDecl = nil) then
      NotYet('this call form (''' + TFuncCallExpr(AExpr).Name + ''')', AExpr);
    if IsFloatExpr(AExpr) then
      NotYet('float-returning call in integer context', AExpr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyRecord) then
      NotYet('record-returning call outside direct assignment', AExpr);
    if IsMethodPtrType(AExpr.ResolvedType) then
      NotYet('closure-returning call outside direct assignment', AExpr);
    EmitCall(TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl),
      TFuncCallExpr(AExpr).Name, TFuncCallExpr(AExpr).Args);
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
    Self.EmitExprToX0(TBinaryExpr(AExpr).LoweredCall);
    Exit;
  end;
  if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr(AExpr);
    { X in SmallSet: ((set shr ord) and 1) and (ord < BitCount) — the
      range guard forces 0 for ordinals past the set width (a shift past
      the register width is undefined) }
    if (BE.Op = boIn) and (BE.Right.ResolvedType <> nil) and
       (BE.Right.ResolvedType.Kind = tySet) and
       TSetTypeDesc(BE.Right.ResolvedType).IsJumbo() then
    begin
      { jumbo membership: _SetIn(bitmap, ord) → 0/1.  A jumbo LITERAL RHS
        materialises a stack bitmap (EmitJumboSetLiteral lowers sp); a
        non-literal RHS (a set variable) evaluates to its bitmap address
        directly.  The ordinal is parked across the RHS eval. }
      Self.EmitExprToX0(BE.Left);         { ordinal }
      EmitPushX0();                       { [ord] — survives the RHS eval }
      if (BE.Right is TArrayLiteralExpr) then
      begin
        EmitJumboSetLiteral(TArrayLiteralExpr(BE.Right));  { x0 = bitmap, sp lowered }
        Self.Emit(Format(#9'ldr x1, [sp, #%d]',
          [JumboSetLiteralBytes(BE.Right)]));              { the parked ord }
        EmitCallSym('_SetIn');
        EmitAddSubImm('add', 'sp', 'sp', JumboSetLiteralBytes(BE.Right));
        Self.Emit(#9'add sp, sp, #16');   { drop the parked ord }
      end
      else
      begin
        Self.EmitExprToX0(BE.Right);      { bitmap address }
        EmitPopTo('x1');                  { the parked ord }
        EmitCallSym('_SetIn');
      end;
      Exit;
    end;
    if (BE.Op = boIn) and (BE.Right.ResolvedType <> nil) and
       (BE.Right.ResolvedType.Kind = tySet) then
    begin
      Self.EmitExprToX0(BE.Right);
      EmitPushX0();
      Self.EmitExprToX0(BE.Left);
      Self.Emit(#9'mov x1, x0');
      EmitPopTo('x0');
      Self.Emit(#9'lsr x0, x0, x1');
      Self.Emit(#9'movz x2, #1');
      Self.Emit(#9'and x0, x0, x2');
      EmitIntLiteral('x2',
        TSetTypeDesc(BE.Right.ResolvedType).BitCount);
      Self.Emit(#9'cmp x1, x2');
      Self.Emit(#9'cset x2, lt');
      Self.Emit(#9'and x0, x0, x2');
      Exit;
    end;
    { small-set arithmetic: union/intersection/difference are plain bit
      ops on the mask; equality compares the masks }
    if (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tySet) then
    begin
      if TSetTypeDesc(BE.Left.ResolvedType).IsJumbo() then
      begin
        EmitJumboSetOp(BE);
        Exit;
      end;
      Self.EmitExprToX0(BE.Left);
      EmitPushX0();
      Self.EmitExprToX0(BE.Right);
      Self.Emit(#9'mov x1, x0');
      EmitPopTo('x0');
      case BE.Op of
        boAdd: Self.Emit(#9'orr x0, x0, x1');
        boMul: Self.Emit(#9'and x0, x0, x1');
        boSub:
        begin
          { A - B = A and (not B): complement via eor with all-ones }
          Self.Emit(#9'movn x2, #0');
          Self.Emit(#9'eor x1, x1, x2');
          Self.Emit(#9'and x0, x0, x1');
        end;
        boEQ:
        begin
          Self.Emit(#9'cmp x0, x1');
          Self.Emit(#9'cset x0, eq');
        end;
        boNE:
        begin
          Self.Emit(#9'cmp x0, x1');
          Self.Emit(#9'cset x0, ne');
        end;
      else
        NotYet('this set operation', AExpr);
      end;
      Exit;
    end;
    { string concatenation: _StringConcat returns an owned +1 string }
    if (BE.Op = boAdd) and (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToX0(BE.Left);
      EmitPushX0();
      Self.EmitExprToX0(BE.Right);
      EmitPushX0();
      Self.Emit(#9'ldur x1, [sp]');        { right }
      Self.Emit(#9'ldur x0, [sp, #16]');   { left  }
      EmitCallSym('_StringConcat');
      { dispose operand transients by shape — nested concats produce rc=0
        intermediates that would otherwise leak permanently }
      if ArcBuiltinStrArgOwnsRef(BE.Left) or
         ArcBuiltinStrArgOwnsRef(BE.Right) then
      begin
        EmitPushX0();                      { park the result }
        if ArcBuiltinStrArgOwnsRef(BE.Right) then
        begin
          Self.Emit(#9'ldur x0, [sp, #16]');
          EmitStrDisposeX0(BE.Right);
        end;
        if ArcBuiltinStrArgOwnsRef(BE.Left) then
        begin
          Self.Emit(#9'ldur x0, [sp, #32]');
          EmitStrDisposeX0(BE.Left);
        end;
        EmitPopTo('x0');
      end;
      Self.Emit(#9'add sp, sp, #32');      { drop the operand brackets }
      Exit;
    end;
    { string comparisons: content comparison via the RTL helpers — an int
      cmp on the pointers would be silently wrong.  Owned operands (concat/
      call transients) are released after the compare (this backend has no
      deferred transient-release list). }
    if (BE.Op in [boEQ, boNE, boLT, boGT, boLE, boGE]) and
       (BE.Left.ResolvedType <> nil) and
       BE.Left.ResolvedType.IsString() then
    begin
      Self.EmitExprToX0(BE.Left);
      EmitPushX0();
      Self.EmitExprToX0(BE.Right);
      EmitPushX0();
      Self.Emit(#9'ldur x0, [sp, #16]');   { left  (peek) }
      Self.Emit(#9'ldur x1, [sp]');        { right (peek) }
      if BE.Op in [boEQ, boNE] then
        EmitCallSym('_StringEquals')
      else
        EmitCallSym('_StringCompare');
      EmitPushX0();                        { result bracket }
      if ArcBuiltinStrArgOwnsRef(BE.Right) then
      begin
        Self.Emit(#9'ldur x0, [sp, #16]');
        EmitStrDisposeX0(BE.Right);
      end;
      if ArcBuiltinStrArgOwnsRef(BE.Left) then
      begin
        Self.Emit(#9'ldur x0, [sp, #32]');
        EmitStrDisposeX0(BE.Left);
      end;
      EmitPopTo('x0');
      Self.Emit(#9'add sp, sp, #32');      { drop the operand brackets }
      case BE.Op of
        boEQ: ;                            { 0/1 already }
        boNE:
        begin
          Self.Emit(#9'cmp x0, #0');
          Self.Emit(#9'cset x0, eq');
        end;
      else
        begin
          { _StringCompare is strcmp-like: signed compare against 0 }
          Self.Emit(#9'sxtw x0, w0');
          Self.Emit(#9'cmp x0, #0');
          case BE.Op of
            boLT: Self.Emit(#9'cset x0, lt');
            boGT: Self.Emit(#9'cset x0, gt');
            boLE: Self.Emit(#9'cset x0, le');
          else
            Self.Emit(#9'cset x0, ge');
          end;
        end;
      end;
      Exit;
    end;
    { any other operator on strings stays a named hole }
    if ((BE.Left.ResolvedType <> nil) and BE.Left.ResolvedType.IsString())
       or ((BE.Right.ResolvedType <> nil) and
           BE.Right.ResolvedType.IsString()) then
      NotYet('string operator', AExpr);
    { float COMPARISON in integer/boolean context: fcmp + cset }
    if (BE.Op in [boEQ, boNE, boLT, boGT, boLE, boGE]) and
       (IsFloatExpr(BE.Left) or IsFloatExpr(BE.Right)) then
    begin
      Self.EmitExprToD0OrConvert(BE.Left);
      Self.Emit(#9'str d0, [sp, #-16]!');
      Self.EmitExprToD0OrConvert(BE.Right);
      Self.Emit(#9'fmov d1, d0');
      Self.Emit(#9'ldr d0, [sp], #16');
      Self.Emit(#9'fcmp d0, d1');
      case BE.Op of
        boEQ: CondName := 'eq';
        boNE: CondName := 'ne';
        boLT: CondName := 'mi';   { ordered less: N set }
        boGT: CondName := 'gt';
        boLE: CondName := 'ls';   { ordered less-or-equal }
      else
        CondName := 'ge';
      end;
      Self.Emit(Format(#9'cset x0, %s', [CondName]));
      Exit;
    end;
    { short-circuit boolean and/or: evaluate the LHS; skip the RHS when
      the result is already decided (and: LHS=0 -> 0; or: LHS<>0 -> 1).
      Eager evaluation here is SILENT WRONG CODE, not a missed
      optimisation — the RTL's nil-guard idiom
      (P <> nil) and (P^.Field ...) dereferenced nil on the M1
      (ARM64_TLS_SEGFAULT_FEEDBACK.md part 2).  Numeric operands keep
      the bitwise arm below, mirroring the x86-64 backend. }
    if ((BE.Op = boAnd) or (BE.Op = boOr)) and
       ((BE.ResolvedType = nil) or not BE.ResolvedType.IsNumeric()) then
    begin
      Lit := NewLabel('scend');
      Self.EmitExprToX0(BE.Left);
      if BE.Op = boAnd then
        Self.Emit(Format(#9'cbz x0, %s', [Lit]))
      else
        Self.Emit(Format(#9'cbnz x0, %s', [Lit]));
      Self.EmitExprToX0(BE.Right);
      Self.Emit(Lit + ':');
      Exit;
    end;
    Self.EmitExprToX0(BE.Left);
    EmitPushX0();
    Self.EmitExprToX0(BE.Right);
    Self.Emit(#9'mov x1, x0');
    EmitPopTo('x0');
    case BE.Op of
      boAdd: Self.Emit(#9'add x0, x0, x1');
      boSub: Self.Emit(#9'sub x0, x0, x1');
      boMul: Self.Emit(#9'mul x0, x0, x1');
      boDiv, boMod:
      begin
        { AArch64 sdiv does NOT trap on a zero divisor (it yields 0), so the
          guard is ALWAYS emitted — the x86-64 backend can lean on the CPU
          trap, this leaf cannot (design doc, Phase 2 risks). }
        DivGuardOk := NewLabel('divok');
        Self.Emit(Format(#9'cbnz x1, %s', [DivGuardOk]));
        if (FSymTable <> nil) and (FSymTable.Lookup('EDivByZero') <> nil) then
          { SysUtils in scope: a catchable EDivByZero (x86-64 / QBE parity);
            _RaiseDivByZero never returns }
          EmitCallSym('SysUtils__RaiseDivByZero')
        else
          Self.Emit(#9'brk #1');              { deliberate trap: div by zero }
        Self.Emit(DivGuardOk + ':');
        { Signed vs unsigned follows the EXPRESSION's result type, matching
          the QBE backend (which keys udiv/urem off BinExpr.ResolvedType).
          This leaf previously always emitted sdiv, so any UInt64 division
          with bit 63 set read its operand as negative (GH #196).  Fall back
          to the operand types only when the result type is unavailable. }
        if BE.ResolvedType <> nil then
          DivUnsigned := IsUnsignedIntA64(BE.ResolvedType)
        else
          DivUnsigned := IsUnsignedIntA64(BE.Left.ResolvedType) and
                         IsUnsignedIntA64(BE.Right.ResolvedType);
        if BE.Op = boDiv then
        begin
          if DivUnsigned then
            Self.Emit(#9'udiv x0, x0, x1')
          else
            Self.Emit(#9'sdiv x0, x0, x1');
        end
        else
        begin
          if DivUnsigned then
            Self.Emit(#9'udiv x9, x0, x1')
          else
            Self.Emit(#9'sdiv x9, x0, x1');
          Self.Emit(#9'msub x0, x9, x1, x0'); { x0 - (x0 div x1)*x1 }
        end;
      end;
      boAnd: Self.Emit(#9'and x0, x0, x1');
      boOr:  Self.Emit(#9'orr x0, x0, x1');
      boXor: Self.Emit(#9'eor x0, x0, x1');
      boShl: Self.Emit(#9'lsl x0, x0, x1');
      boShr: Self.Emit(#9'lsr x0, x0, x1');
      boSar: Self.Emit(#9'asr x0, x0, x1');
      boEQ, boNE, boLT, boGT, boLE, boGE:
      begin
        { Unsigned when EITHER operand is an unsigned integer, or the left
          is pointer-like -- the x86-64 rule (setb/seta), so both backends
          agree.  Always-signed conditions made MaxUInt64 > 1 false. }
        CmpUnsigned := IsUnsignedIntA64(BE.Left.ResolvedType) or
                       IsUnsignedIntA64(BE.Right.ResolvedType) or
                       ((BE.Left.ResolvedType <> nil) and
                        (BE.Left.ResolvedType.Kind in [tyPointer, tyClass,
                           tyInterface, tyString, tyDynArray, tyProcedural]));
        case BE.Op of
          boEQ: CondName := 'eq';
          boNE: CondName := 'ne';
          boLT: if CmpUnsigned then CondName := 'lo' else CondName := 'lt';
          boGT: if CmpUnsigned then CondName := 'hi' else CondName := 'gt';
          boLE: if CmpUnsigned then CondName := 'ls' else CondName := 'le';
        else
          if CmpUnsigned then CondName := 'hs' else CondName := 'ge';
        end;
        { Compare 32-bit-ordinal operands as `w` — their upper 32 bits are
          non-canonical (a bit-31-set literal is sign-extended, a computed value
          zero-extended), so a 64-bit cmp of two such values can be wrong.
          Int64/UInt64/pointer operands stay 64-bit (`x`). }
        if IsNarrow32Ord(BE.Left.ResolvedType) and
           IsNarrow32Ord(BE.Right.ResolvedType) then
          Self.Emit(#9'cmp w0, w1')
        else
          Self.Emit(#9'cmp x0, x1');
        Self.Emit(Format(#9'cset x0, %s', [CondName]));
      end;
    else
      NotYet('binary operator ' + IntToStr(Ord(BE.Op)), AExpr);
    end;
    Exit;
  end;
  if AExpr is TInheritedCallExpr then
  begin
    if TInheritedCallExpr(AExpr).ResolvedMethod = nil then
      NotYet('unresolved inherited call', AExpr);
    if IsFloatExpr(AExpr) then
      NotYet('float-returning inherited call in integer context', AExpr);
    EmitLoadSlot('x0', 'Self');
    EmitPushX0();
    EmitCall(TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod),
      TInheritedCallExpr(AExpr).Name, TInheritedCallExpr(AExpr).Args,
      '', True, VIRT_NONE);
    Exit;
  end;
  { Default/indexed property read Obj[I] (e.g. L[0] on a TStringList): the
    semantic pass folds the index into StrExpr — a TFieldAccessExpr with PropRead
    and PropIndexExpr set — and leaves the SUBSCRIPT'S own IndexExpr nil.  This
    must be caught BEFORE the string-subscript case below, which would take the
    nil IndexExpr as a byte index and EmitExprToX0(nil) → compiler segfault
    (macOS arm64, 2026-07-24).  Delegate to the StrExpr, mirroring x86-64. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(TStringSubscriptExpr(AExpr).StrExpr).PropRead <> nil) then
  begin
    Self.EmitExprToX0(TStringSubscriptExpr(AExpr).StrExpr);
    Exit;
  end;
  { Subscript of a STRING-typed FIELD — Rec.Field[N] / Obj.Field[N] /
    Self.FField[N].  The semantic pass does NOT build a TStringSubscriptExpr for
    this: it folds the index into the field access itself (IsCharAccess with the
    index in PropIndexExpr, uSemantic ~14106).  arm64 had NO arm for that flag
    anywhere — `grep IsCharAccess` found nothing in this unit — so every such
    read fell through to a plain whole-field read and silently produced the
    field's DATA POINTER instead of the byte, dropping the subscript entirely
    (BUG-20260726-arm64-field-characcess-dropped).  That is why
    Ord(M.Data[0]) returned 4332157884: a heap address, not 'A'.
    QBE has handled it since BUG-20260723 (qbe.pas ~15043).

    Blaise strings are 0-based and the value IS the data pointer, so this is the
    same byte load the plain S[I] arm below does — only the base is reached
    through the field. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc is TSetTypeDesc) and
     TSetTypeDesc(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc).IsJumbo() and
     (TFieldAccessExpr(AExpr).PropRead = nil) and
     (TFieldAccessExpr(AExpr).PropIndexExpr = nil) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { a JUMBO set field evaluates to its bitmap ADDRESS -- the value shape a
      jumbo set variable has, so membership, copies and the _Set* helpers
      need no special case.  EmitRecFieldAddrToX0 resolves every base form
      (record, class, Self, chained). }
    EmitRecFieldAddrToX0(TFieldAccessExpr(AExpr));
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsCharAccess then
  begin
    if TFieldAccessExpr(AExpr).PropIndexExpr = nil then
      NotYet('string-field subscript without an index', AExpr);
    Self.EmitExprToX0(TFieldAccessExpr(AExpr).PropIndexExpr);
    EmitPushX0();
    EmitRecFieldAddrToX0(TFieldAccessExpr(AExpr));
    Self.Emit(#9'ldr x0, [x0]');
    EmitPopTo('x1');
    Self.Emit(#9'add x0, x0, x1');
    Self.Emit(#9'ldrb w0, [x0]');
    Exit;
  end;
  { Reading an ELEMENT of an array-typed FIELD as a scalar — Obj.Arr[I] /
    Rec.Arr[I] / Self.Arr[I].  Like IsCharAccess above, the semantic pass folds
    the subscript into the field access (IsArrayAccess + PropIndexExpr) and the
    read path had no arm for it, so it produced the ARRAY'S DATA POINTER and
    dropped the index: S.BB[1] returned 4336386304 instead of 11, for every
    element width (BUG-20260726-arm64-field-arrayaccess-read-dropped).  The
    implicit-Self form already worked through another route, which is why the
    compiler's own `Bytes[I]` uses went unnoticed while the Mach-O writer's
    Sec.Bytes[...] fold read garbage.

    Both halves already existed and were only reachable from the ADDRESS path:
    EmitFieldElemAddr scales the subscript (and derefs a dyn-array's data
    pointer), EmitElemLoad narrows the load to the element width.  RECORD and
    static-array elements are excluded — those evaluate to their ADDRESS by
    design (leg 32) and keep their existing paths. }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsArrayAccess and
     (TFieldAccessExpr(AExpr).ResolvedType <> nil) then
  begin
    EmitFieldElemAddr(TFieldAccessExpr(AExpr));
    { a record, static-array or jumbo-set element evaluates to its ADDRESS
      (leg 32; a jumbo set's value IS its bitmap address) }
    if not ((TFieldAccessExpr(AExpr).ResolvedType.Kind in
               [tyRecord, tyStaticArray]) or
            IsJumboSetType(TFieldAccessExpr(AExpr).ResolvedType)) then
      EmitElemLoad(TFieldAccessExpr(AExpr).ResolvedType);
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     ((TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyPChar) or
      TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.IsString()) then
  begin
    { S[I] / P[I]: byte at data-pointer+index (Blaise strings are
      0-based and the value IS the data pointer) }
    Self.EmitExprToX0(TStringSubscriptExpr(AExpr).IndexExpr);
    EmitPushX0();
    Self.EmitExprToX0(TStringSubscriptExpr(AExpr).StrExpr);
    EmitPopTo('x1');
    Self.Emit(#9'add x0, x0, x1');
    Self.Emit(#9'ldrb w0, [x0]');
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind =
       tyStaticArray) then
  begin
    EmitStaticElemAddr(TStringSubscriptExpr(AExpr));
    { A record / nested static-array element evaluates to its ADDRESS (already
      in x0) — it is used by reference downstream (whole-record copy, field
      read/write, by-hidden-pointer arg).  Value-loading it would read the first
      field/element instead (BUG: leg 32; mirrors x86-64 :9167). }
    if not (TStaticArrayTypeDesc(
              TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType.Kind
              in [tyRecord, tyStaticArray]) then
      EmitElemLoad(TStaticArrayTypeDesc(
        TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType);
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind =
       tyDynArray) then
  begin
    EmitDynElemAddr(TStringSubscriptExpr(AExpr));
    { Record element: leave the element address in x0 (used by reference). }
    if TDynArrayTypeDesc(
         TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType.Kind
         <> tyRecord then
      EmitElemLoad(TDynArrayTypeDesc(
        TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType);
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind =
       tyOpenArray) then
  begin
    { A[I] on an open-array param: element read through the borrowed
      data pointer — a string/class element stays a BORROW (no ARC) }
    EmitDynElemAddr(TStringSubscriptExpr(AExpr));
    { Record element: leave the element address in x0 (used by reference). }
    if TOpenArrayTypeDesc(
         TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType.Kind
         <> tyRecord then
      EmitElemLoad(TOpenArrayTypeDesc(
        TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType);
    Exit;
  end;
  if AExpr is TMethodCallExpr then
  begin
    if IsFloatExpr(AExpr) then
      NotYet('float-returning method call in integer context', AExpr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyRecord) then
      NotYet('record-returning method call', AExpr);
    if IsMethodPtrType(AExpr.ResolvedType) then
      NotYet('closure-returning method call', AExpr);
    EmitMethodCallExpr(TMethodCallExpr(AExpr));
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).IsClassNameAccess or
      TFieldAccessExpr(AExpr).IsClassTypeAccess) then
  begin
    { Obj.ClassName / Obj.ClassType — instance[0] = vtable, vtable[0] =
      typeinfo; ClassName reads the name string ptr at typeinfo+16,
      ClassType returns the typeinfo pointer itself.  An owned transient
      base is released after the read. }
    if TFieldAccessExpr(AExpr).Base <> nil then
    begin
      if ArcExprOwnsRef(TFieldAccessExpr(AExpr).Base) then
        NotYet('ClassName/ClassType on an owned transient base', AExpr);
      Self.EmitExprToX0(TFieldAccessExpr(AExpr).Base);
    end
    else if TFieldAccessExpr(AExpr).IsImplicitSelf then
      EmitLoadSlot('x0', 'Self')
    else
      EmitLoadSlot('x0', TFieldAccessExpr(AExpr).RecordName);
    Self.Emit(#9'ldr x0, [x0]');    { vtable }
    Self.Emit(#9'ldr x0, [x0]');    { typeinfo }
    if TFieldAccessExpr(AExpr).IsClassNameAccess then
      Self.Emit(#9'ldr x0, [x0, #16]');   { name string ptr }
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).PropRead <> nil) then
  begin
    EmitPropReadCall(TFieldAccessExpr(AExpr));
    Exit;
  end;
  if AExpr is TNilLiteral then
  begin
    Self.Emit(#9'movz x0, #0');
    Exit;
  end;
  if AExpr is TIsExpr then
  begin
    { X is TFoo: _IsInstance(obj, typeinfo) walks the parent chain;
      interface targets query the impllist via _ImplementsInterface }
    Self.EmitExprToX0(TIsExpr(AExpr).Obj);
    EmitTypeinfoAddr('x1', TIsExpr(AExpr).TypeName);
    if (TIsExpr(AExpr).ResolvedTargetType <> nil) and
       (TIsExpr(AExpr).ResolvedTargetType.Kind = tyInterface) then
      EmitCallSym('_ImplementsInterface')
    else
      EmitCallSym('_IsInstance');
    Exit;
  end;
  if (AExpr is TAsExpr) and (AExpr.ResolvedType <> nil) and
     (AExpr.ResolvedType.Kind = tyClass) then
  begin
    { X as TFoo (class-to-class): checked downcast — raise on mismatch,
      result is the original pointer }
    CondName := NewLabel('asok');
    Self.EmitExprToX0(TAsExpr(AExpr).Obj);
    EmitPushX0();
    EmitTypeinfoAddr('x1', TAsExpr(AExpr).TypeName);
    EmitCallSym('_IsInstance');
    Self.Emit(Format(#9'cbnz x0, %s', [CondName]));
    EmitRaiseInvalidCast();
    Self.Emit(CondName + ':');
    EmitPopTo('x0');
    Exit;
  end;
  if AExpr is TNotExpr then
  begin
    Self.EmitExprToX0(TNotExpr(AExpr).Expr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyBoolean) then
    begin
      Self.Emit(#9'cmp x0, #0');
      Self.Emit(#9'cset x0, eq');
    end
    else
    begin
      { bitwise NOT: eor with all-ones (no mvn/orn in the assembler) }
      Self.Emit(#9'movn x1, #0');
      Self.Emit(#9'eor x0, x0, x1');
    end;
    Exit;
  end;
  if AExpr is TDerefExpr then
  begin
    { P^: the pointer value is the address; aggregates stay as addresses
      (field access / assignment work with record addresses), scalars
      load through with the pointee's width }
    Self.EmitExprToX0(TDerefExpr(AExpr).Expr);
    if not ((AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray])) then
      EmitElemLoad(AExpr.ResolvedType);
    Exit;
  end;
  if AExpr is TAddrOfExpr then
  begin
    if TAddrOfExpr(AExpr).ResolvedFreeRoutine <> nil then
    begin
      { @Routine: the code address of a standalone routine }
      Self.Emit(Format(#9'adrp x0, %s@PAGE',
        [RoutineSym(TMethodDecl(TAddrOfExpr(AExpr).ResolvedFreeRoutine),
          '')]));
      Self.Emit(Format(#9'add x0, x0, %s@PAGEOFF',
        [RoutineSym(TMethodDecl(TAddrOfExpr(AExpr).ResolvedFreeRoutine),
          '')]));
      Exit;
    end;
    if (TAddrOfExpr(AExpr).Expr is TIdentExpr) and
       (TIdentExpr(TAddrOfExpr(AExpr).Expr).ParamMode <> pmVar) then
    begin
      { @IntfVar: an interface variable is a 16-byte (obj, itab) pair.  A
        frame local / parameter is ONE contiguous block (AddIntfLocal) and a
        Self field sits inline, so the pair's address is the obj slot's
        address (EmitRecIdentAddr: slot, Self field or capture).  A GLOBAL is
        still two separate symbols with no single address -- refuse it rather
        than hand out an address whose +8 is not the itab. }
      if (TAddrOfExpr(AExpr).Expr.ResolvedType <> nil) and
         (TAddrOfExpr(AExpr).Expr.ResolvedType.Kind = tyInterface) then
      begin
        if not IsLocal(TIdentExpr(TAddrOfExpr(AExpr).Expr).Name) and
           not TIdentExpr(TAddrOfExpr(AExpr).Expr).IsImplicitSelf and
           not IsCaptured(TIdentExpr(TAddrOfExpr(AExpr).Expr).Name) then
          NotYet('address-of a global interface variable', AExpr);
        EmitRecIdentAddr('x0', TIdentExpr(TAddrOfExpr(AExpr).Expr));
        Exit;
      end;
      { a bare FIELD of Self inside a method: Self + the field's offset (there
        is no slot of that name) }
      if TIdentExpr(TAddrOfExpr(AExpr).Expr).IsImplicitSelf and
         (TIdentExpr(TAddrOfExpr(AExpr).Expr).ImplicitFieldInfo <> nil) then
      begin
        EmitLoadSlot('x0', 'Self');
        EmitAddSubImm('add', 'x0', 'x0',
          TFieldInfo(TIdentExpr(TAddrOfExpr(AExpr).Expr).ImplicitFieldInfo).Offset);
        Exit;
      end;
      { a captured variable: '_cap_<Name>' already holds its address }
      if IsCaptured(TIdentExpr(TAddrOfExpr(AExpr).Expr).Name) then
      begin
        EmitLoadSlot('x0', '_cap_' + TIdentExpr(TAddrOfExpr(AExpr).Expr).Name);
        Exit;
      end;
      EmitSlotAddr('x0', TIdentExpr(TAddrOfExpr(AExpr).Expr).Name);
      Exit;
    end;
    if (TAddrOfExpr(AExpr).Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).FieldInfo <> nil) and
       TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).IsArrayAccess then
    begin
      { @Obj.Arr[I] / @Self.Arr[I] / @Rec.Arr[I] — address of an array-field
        ELEMENT (the field access carries IsArrayAccess + PropIndexExpr) }
      EmitFieldElemAddr(TFieldAccessExpr(TAddrOfExpr(AExpr).Expr));
      Exit;
    end;
    if (TAddrOfExpr(AExpr).Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).FieldInfo <> nil) then
    begin
      { @Rec.Field / @P^.Field: the field's address }
      if TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base is TDerefExpr then
        Self.EmitExprToX0(TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base)
      else if (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base = nil) and
              (not TFieldAccessExpr(TAddrOfExpr(AExpr).Expr)
                     .IsClassAccess) and
              (not TFieldAccessExpr(TAddrOfExpr(AExpr).Expr)
                     .IsImplicitSelf) then
        EmitSlotAddr('x0',
          TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).RecordName)
      else if (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base = nil) and
              TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).IsClassAccess and
              (not TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).IsImplicitSelf) then
      begin
        { @Obj.Field: the instance pointer the class variable holds }
        if not EmitCapturedBase('x0',
                 TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).RecordName,
                 True, False) then
          EmitLoadSlot('x0', TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).RecordName);
      end
      else if (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base <> nil) and
              (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base.ResolvedType <> nil) and
              (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base.ResolvedType.Kind
                 = tyClass) and
              not ArcExprOwnsRef(TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base) then
        { @A.B.Field with B a class: B's value is the instance pointer }
        Self.EmitExprToX0(TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base)
      else if (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base <> nil) and
              (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base.ResolvedType <> nil) and
              (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base.ResolvedType.Kind
                 = tyRecord) then
        { @A.Rec.Field: the record base's own address }
        EmitRecAddrToX0(TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base)
      else if (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).Base = nil) and
              TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).IsImplicitSelf and
              (TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).ImplicitBaseInfo <> nil) then
      begin
        { @FRec.Field / @FObj.Field inside a method: step from Self to the
          base the same way every other implicit-Self access does }
        EmitLoadSlot('x0', 'Self');
        EmitImplicitBaseStep('x0',
          TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).ImplicitBaseInfo);
      end
      else
        NotYet('address-of on this field form', AExpr);
      if TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).FieldInfo.Offset <> 0 then
        Self.Emit(Format(#9'add x0, x0, #%d',
          [TFieldAccessExpr(TAddrOfExpr(AExpr).Expr).FieldInfo.Offset]));
      Exit;
    end;
    if (TAddrOfExpr(AExpr).Expr is TStringSubscriptExpr) and
       (TStringSubscriptExpr(TAddrOfExpr(AExpr).Expr).StrExpr.ResolvedType
          <> nil) then
    begin
      { @Arr[I] — the element address the subscript emitters compute }
      case TStringSubscriptExpr(TAddrOfExpr(AExpr).Expr).StrExpr
             .ResolvedType.Kind of
        tyStaticArray:
        begin
          EmitStaticElemAddr(
            TStringSubscriptExpr(TAddrOfExpr(AExpr).Expr));
          Exit;
        end;
        tyDynArray, tyOpenArray:
        begin
          EmitDynElemAddr(TStringSubscriptExpr(TAddrOfExpr(AExpr).Expr));
          Exit;
        end;
        tyPChar:
        begin
          Self.EmitExprToX0(
            TStringSubscriptExpr(TAddrOfExpr(AExpr).Expr).IndexExpr);
          EmitPushX0();
          Self.EmitExprToX0(
            TStringSubscriptExpr(TAddrOfExpr(AExpr).Expr).StrExpr);
          EmitPopTo('x1');
          Self.Emit(#9'add x0, x0, x1');
          Exit;
        end;
      end;
    end;
    { @V where V is a var / out parameter: its slot already holds the
      caller's variable address (net.sockets FillSockAddr(var AAddr) passes
      @AAddr on); a captured var parameter's storage holds that address }
    if (TAddrOfExpr(AExpr).Expr is TIdentExpr) and
       (TIdentExpr(TAddrOfExpr(AExpr).Expr).ParamMode = pmVar) then
    begin
      if IsCaptured(TIdentExpr(TAddrOfExpr(AExpr).Expr).Name) then
      begin
        EmitLoadSlot('x0', '_cap_' + TIdentExpr(TAddrOfExpr(AExpr).Expr).Name);
        Self.Emit(#9'ldr x0, [x0]');
      end
      else
        EmitLoadSlot('x0', TIdentExpr(TAddrOfExpr(AExpr).Expr).Name);
      Exit;
    end;
    { @P^ is just the pointer value P }
    if TAddrOfExpr(AExpr).Expr is TDerefExpr then
    begin
      Self.EmitExprToX0(TDerefExpr(TAddrOfExpr(AExpr).Expr).Expr);
      Exit;
    end;
    NotYet('address-of on this expression', AExpr);
  end;
  if AExpr is TSupportsExpr then
  begin
    { Supports(Obj, IFoo): non-nil itab in the impllist chain.  The
      3-arg form populates the out-var's fat pointer on success and
      leaves it UNTOUCHED on failure (QBE parity). }
    if ArcExprOwnsRef(TSupportsExpr(AExpr).Obj) then
      NotYet('Supports on an owned transient', AExpr);
    if TSupportsExpr(AExpr).OutVarName = '' then
    begin
      Self.EmitExprToX0(TSupportsExpr(AExpr).Obj);
      EmitTypeinfoAddr('x1', IntfRefName(TSupportsExpr(AExpr).ResolvedIntfType, TSupportsExpr(AExpr).IntfTypeName));
      EmitCallSym('_GetItab');
      Self.Emit(#9'cmp x0, #0');
      Self.Emit(#9'cset x0, ne');
      Exit;
    end;
    Self.EmitExprToX0(TSupportsExpr(AExpr).Obj);
    EmitPushX0();                                    { [obj] }
    EmitTypeinfoAddr('x1', IntfRefName(TSupportsExpr(AExpr).ResolvedIntfType, TSupportsExpr(AExpr).IntfTypeName));
    EmitCallSym('_GetItab');
    EmitPushX0();                                    { [obj][itab] }
    CondName := NewLabel('supno');
    Lit := NewLabel('supend');
    Self.Emit(Format(#9'cbz x0, %s', [CondName]));
    EmitPopTo('x0');
    EmitStoreSlot('x0', TSupportsExpr(AExpr).OutVarName + '_itab');
    Self.Emit(#9'ldr x0, [sp]');
    EmitCallSym('_ClassAddRef');
    EmitLoadSlot('x0', TSupportsExpr(AExpr).OutVarName);
    EmitCallSym('_ClassRelease');
    EmitPopTo('x0');
    EmitStoreSlot('x0', TSupportsExpr(AExpr).OutVarName);
    Self.Emit(#9'movz x0, #1');
    Self.Emit(Format(#9'b %s', [Lit]));
    Self.Emit(CondName + ':');
    Self.Emit(#9'add sp, sp, #32');
    Self.Emit(#9'movz x0, #0');
    Self.Emit(Lit + ':');
    Exit;
  end;
  if (AExpr is TArrayLiteralExpr) and (AExpr.ResolvedType <> nil) and
     (AExpr.ResolvedType.Kind = tySet) then
  begin
    if TSetTypeDesc(AExpr.ResolvedType).IsJumbo() then
    begin
      { A jumbo literal materialises a stack bitmap and yields its ADDRESS in
        x0 — the same value shape a jumbo set variable evaluates to, so the
        consumer needs no special case.

        NOTE the sp contract: EmitJumboSetLiteral LOWERS sp by
        JumboSetLiteralBytes, and the buffer stays live until the frame is
        torn down (sp is restored from x29 at function exit).  That is fine
        for a literal, which is materialised once where it appears.  It is NOT
        fine for an OPERATOR, which can sit inside a loop — see
        EmitJumboSetOp, which uses a fixed frame slot for exactly that reason. }
      EmitJumboSetLiteral(TArrayLiteralExpr(AExpr));
      Exit;
    end;
    EmitSmallSetLiteral(TArrayLiteralExpr(AExpr));
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsConstant then
  begin
    { TypeName.ConstName — folded by the semantic pass }
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyString) then
    begin
      Idx := FStrLits.IndexOf(TFieldAccessExpr(AExpr).ConstString);
      if Idx < 0 then
        Idx := FStrLits.Add(TFieldAccessExpr(AExpr).ConstString);
      Self.Emit(Format(#9'adrp x0, __s%d@PAGE', [Idx]));
      Self.Emit(Format(#9'add x0, x0, __s%d@PAGEOFF', [Idx]));
      Self.Emit(#9'add x0, x0, #12');
      Exit;
    end;
    EmitIntLiteral('x0', TFieldAccessExpr(AExpr).ConstValue);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base <> nil) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     TFieldAccessExpr(AExpr).IsClassAccess and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { chained field read A.B.C: the base expression yields the instance
      pointer.  An OWNED transient base (a call result, +1) is kept across
      the field load and released after — the loaded scalar field value
      survives the release. }
    if not (IsSmallSetType(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsPlainWordRef(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsIntFam(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind in
              [tyDouble, tySingle, tyClass, tyPointer, tyPChar,
               tyDynArray]) or
            TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.IsString()) then
      NotYet('read of a field of this type', AExpr);
    if ArcExprOwnsRef(TFieldAccessExpr(AExpr).Base) then
    begin
      { The base is an owned +1 transient; releasing it runs its
        _FieldCleanup, which releases the base's own fields.  Discipline by
        field kind (mirrors x86-64 field-read-on-owned-transient, 9134+):

        - A retained CLASS field aliases INTO the base's object graph — the
          base cleanup would free the very object we loaded.  DEFER the base
          release to the end of the enclosing leaf statement (BUG-048 fix):
          the borrowed field value stays live until the statement's store /
          use has run, and the deferred release then balances the transient's
          +1 with NO leak (the read result is borrowed — ArcExprOwnsRef is
          False for a plain field read — so pinning it would leak).  If all
          _pendrel slots are in use we fall back to x86-64's leak-safe
          AddRef-pin (safe, one-ref leak; only when >8 transient-field reads
          nest in one statement).  The string arm below is leak-free.

        - A STRING field, an [Unretained] class field, and scalar fields all
          flow through the inline-release template below: x86-64 releases the
          base inline for these (a string data pointer / a back-reference /
          a value are not freed out from under the read in the common case —
          string fields are typically immortal literals). }
      if (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind = tyClass) and
         not TFieldAccessExpr(AExpr).FieldInfo.IsUnretained then
      begin
        Self.EmitExprToX0(TFieldAccessExpr(AExpr).Base);
        EmitPushX0();                  { [base] }
        if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
          Self.Emit(Format(#9'add x0, x0, #%d',
            [TFieldAccessExpr(AExpr).FieldInfo.Offset]));
        EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
        EmitPushX0();                  { [base][fieldval] — both parked on the
                                         stack across the defer/release so no
                                         volatile register has to survive a
                                         slot spill (clobbers x9) or a call. }
        Self.Emit(#9'ldr x0, [sp, #16]'); { x0 = owned transient base }
        { DEFER the base release to the enclosing statement boundary (or, for
          a loop/if condition, the per-iteration flush in the control-flow
          emitter).  EVERY statement is now flush-bracketed (BUG-049), so a
          deferred base is always released — no context leaks.  Only when all
          _pendrel slots are busy (>8 transient-field reads nested in one
          expression) do we fall back to the leak-safe AddRef-pin. }
        if DeferNativeClassRelease() then { spill base -> _pendrel slot }
        begin
          EmitPopTo('x0');                { fieldval }
          Self.Emit(#9'add sp, sp, #16'); { drop base }
        end
        else
        begin
          Self.Emit(#9'ldr x0, [sp]');     { fieldval }
          EmitCallSym('_ClassAddRef');  { pin it across the base release }
          Self.Emit(#9'ldr x0, [sp, #16]'); { base }
          EmitCallSym('_ClassRelease'); { release base — field pinned }
          EmitPopTo('x0');                 { fieldval }
          Self.Emit(#9'add sp, sp, #16');  { drop base }
        end;
        Exit;
      end;
      Self.EmitExprToX0(TFieldAccessExpr(AExpr).Base);
      EmitPushX0();                    { [base] — released after the load }
      if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
        Self.Emit(Format(#9'add x0, x0, #%d',
          [TFieldAccessExpr(AExpr).FieldInfo.Offset]));
      EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
      EmitPushX0();                    { [base][fieldval] }
      Self.Emit(#9'ldr x0, [sp, #16]');
      EmitCallSym('_ClassRelease');
      EmitPopTo('x0');                 { fieldval }
      Self.Emit(#9'add sp, sp, #16');  { drop base }
      Exit;
    end;
    Self.EmitExprToX0(TFieldAccessExpr(AExpr).Base);
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      Self.Emit(Format(#9'add x0, x0, #%d',
        [TFieldAccessExpr(AExpr).FieldInfo.Offset]));
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base = nil) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (TFieldAccessExpr(AExpr).IsClassAccess or
      TFieldAccessExpr(AExpr).IsImplicitSelf) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { instance field read: the base is a POINTER — Obj's slot value, or
      Self for a bare field name inside a method }
    if not (IsSmallSetType(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsPlainWordRef(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsIntFam(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind in
              [tyDouble, tySingle, tyClass, tyPointer, tyPChar,
               tyDynArray]) or
            TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.IsString()) then
      NotYet('read of a field of this type', AExpr);
    if TFieldAccessExpr(AExpr).IsImplicitSelf then
      EmitLoadSlot('x0', 'Self')
    else if not EmitCapturedBase('x0', TFieldAccessExpr(AExpr).RecordName,
                 True, TFieldAccessExpr(AExpr).IsVarParam) then
      EmitLoadSlot('x0', TFieldAccessExpr(AExpr).RecordName);
    { Step across the intermediate field (Self.FIntermediate.Member): add its
      offset for an embedded record, or deref it for a class reference.  A
      record intermediate was the tokeniser's FToken.SubField (2026-07-23);
      a class intermediate is Self.FScopeStack.Count and needs the load. }
    EmitImplicitBaseStep('x0', TFieldAccessExpr(AExpr).ImplicitBaseInfo);
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldAccessExpr(AExpr).FieldInfo.Offset);
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base is TDerefExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (not TFieldAccessExpr(AExpr).IsClassAccess) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { P^.Field: the deref of a record pointer IS the record address —
      load the field at its offset, width by field kind }
    Self.EmitExprToX0(TFieldAccessExpr(AExpr).Base);
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      Self.Emit(Format(#9'add x0, x0, #%d',
        [TFieldAccessExpr(AExpr).FieldInfo.Offset]));
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base = nil) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (not TFieldAccessExpr(AExpr).IsImplicitSelf) and
     (not TFieldAccessExpr(AExpr).IsClassAccess) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { plain Rec.Field read of a local/global/var-param record }
    if not (IsSmallSetType(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsPlainWordRef(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsIntFam(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind in
              [tyDouble, tySingle, tyClass, tyPointer, tyPChar,
               tyDynArray]) or
            TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.IsString()) then
      NotYet('read of a field of this type', AExpr);
    { captured record base (leg 19): a captured VALUE record's '_cap_' holds
      its address directly (no deref); a captured VAR-PARAM record's '_cap_'
      holds &(the var-param slot), and that slot holds the caller's record
      address — so one deref yields the base.  Both cases: want the record
      ADDRESS, driven by IsVarParam. }
    if IsCaptured(TFieldAccessExpr(AExpr).RecordName) then
      EmitCapturedBase('x9', TFieldAccessExpr(AExpr).RecordName,
        TFieldAccessExpr(AExpr).IsVarParam, False)
    else
      { TRUE var/out record → one deref; by-value record param / local / global
        → EmitSlotAddr.  A by-value record param is IsVarParam=True too (records
        pass by reference), so the '__pptr_' discriminator in EmitRecordBaseAddr
        keeps them apart (was a double-deref that mis-read the first word). }
      EmitRecordBaseAddr('x9', TFieldAccessExpr(AExpr).RecordName,
        TFieldAccessExpr(AExpr).IsVarParam);
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      Self.Emit(Format(#9'add x9, x9, #%d',
        [TFieldAccessExpr(AExpr).FieldInfo.Offset]));
    Self.Emit(#9'mov x0, x9');
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base.ResolvedType <> nil) and
     (TFieldAccessExpr(AExpr).Base.ResolvedType.Kind = tyRecord) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { field of a RECORD-VALUED field access (FTok.Token.TextStart):
      compute the inner record's address, then load at the outer offset }
    if not (IsSmallSetType(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsPlainWordRef(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsIntFam(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind in
              [tyDouble, tySingle, tyClass, tyPointer, tyPChar,
               tyDynArray]) or
            TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.IsString()) then
      NotYet('read of a field of this type', AExpr);
    EmitRecFieldAddrToX0(TFieldAccessExpr(TFieldAccessExpr(AExpr).Base));
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldAccessExpr(AExpr).FieldInfo.Offset);
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base <> nil) and
     IsRecordCallArg(TFieldAccessExpr(AExpr).Base) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { field of a record-RETURNING CALL (HostTarget().OS): materialise the
      record into the __rret scratch, then load the field at its offset }
    if not (IsSmallSetType(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsPlainWordRef(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsIntFam(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind in
              [tyDouble, tySingle, tyClass, tyPointer, tyPChar,
               tyDynArray]) or
            TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.IsString()) then
      NotYet('read of a field of this type', AExpr);
    EmitRecCallToRret(TFieldAccessExpr(AExpr).Base);   { x0 = __rret addr }
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldAccessExpr(AExpr).FieldInfo.Offset);
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base is TStringSubscriptExpr) and
     (TFieldAccessExpr(AExpr).Base.ResolvedType <> nil) and
     (TFieldAccessExpr(AExpr).Base.ResolvedType.Kind = tyRecord) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { field of a subscripted RECORD element: A[I].Kind — the subscript
      emitters yield the element address, the field loads at its offset }
    if not (IsSmallSetType(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsPlainWordRef(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsIntFam(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind in
              [tyDouble, tySingle, tyClass, tyPointer, tyPChar,
               tyDynArray]) or
            TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.IsString()) then
      NotYet('read of a field of this type', AExpr);
    if RecordPropRead(TFieldAccessExpr(AExpr).Base) <> nil then
      { L[I].Field on a default record property: the getter's value }
      EmitRecPropToTemp(RecordPropRead(TFieldAccessExpr(AExpr).Base))
    else
    case TStringSubscriptExpr(TFieldAccessExpr(AExpr).Base)
           .StrExpr.ResolvedType.Kind of
      tyStaticArray:
        EmitStaticElemAddr(
          TStringSubscriptExpr(TFieldAccessExpr(AExpr).Base));
      tyDynArray, tyOpenArray:
        EmitDynElemAddr(
          TStringSubscriptExpr(TFieldAccessExpr(AExpr).Base));
    else
      NotYet('field read on this subscript base', AExpr);
    end;
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldAccessExpr(AExpr).FieldInfo.Offset);
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc <> nil) and
     (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind = tyRecord) and
     (not TFieldAccessExpr(AExpr).IsClassAccess) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { a RECORD-typed field access yields the ADDRESS of the sub-record (leg 24)
      — Rec.RecField / A.B where B is a record field.  This is what a further
      access (A.B.C) or a whole-record copy needs; the value of a record IS its
      address.  EmitRecFieldAddrToX0 recurses through a record intermediate
      base and adds the field offset. }
    EmitRecFieldAddrToX0(TFieldAccessExpr(AExpr));
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).Base <> nil) and
     (TFieldAccessExpr(AExpr).Base.ResolvedType <> nil) and
     (TFieldAccessExpr(AExpr).Base.ResolvedType.Kind = tyRecord) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (TFieldAccessExpr(AExpr).PropRead = nil) and
     (not TFieldAccessExpr(AExpr).IsMethodCall) and
     (not TFieldAccessExpr(AExpr).IsClassAccess) and
     (not TFieldAccessExpr(AExpr).IsConstant) then
  begin
    { a field of any other record-valued base expression -- a record
      identifier carried as a Base node (the receiver of GS.Box.Bump(),
      GS a record global), P^, a var param: EmitRecAddrToX0 yields the
      record's address, the field loads at its offset }
    if not (IsSmallSetType(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsPlainWordRef(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            IsIntFam(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc) or
            (TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.Kind in
              [tyDouble, tySingle, tyClass, tyPointer, tyPChar,
               tyDynArray, tyInterface, tyMetaClass]) or
            TFieldAccessExpr(AExpr).FieldInfo.TypeDesc.IsString()) then
      NotYet('read of a field of this type', AExpr);
    EmitRecAddrToX0(TFieldAccessExpr(AExpr).Base);
    if TFieldAccessExpr(AExpr).FieldInfo.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldAccessExpr(AExpr).FieldInfo.Offset);
    EmitElemLoad(TFieldAccessExpr(AExpr).FieldInfo.TypeDesc);
    Exit;
  end;
  NotYet('expression ' + AExpr.ClassName, AExpr);
end;

procedure TArm64Backend.EmitStrDisposeX0(AExpr: TASTExpr);
begin
  { dispose the string transient whose value is in x0, by refcount shape
    (docs/arc-string-transient-handover.adoc):
      rc = 1 (ArcExprOwnsRef, user routine results)  -> one Release
      rc = 0 (concat/built-in results)               -> AddRef THEN Release
    A bare release on an rc = 0 buffer drives it to -1 = IMMORTAL — a
    permanent leak the --debug tracker cannot see. }
  if ArcExprOwnsRef(AExpr) then
    EmitCallSym('_StringRelease')
  else if ArcExprIsUnownedStrTransient(AExpr) then
  begin
    EmitPushX0();
    EmitCallSym('_StringAddRef');
    EmitPopTo('x0');
    EmitCallSym('_StringRelease');
  end;
end;

function TArm64Backend.IsFloatExpr(AExpr: TASTExpr): Boolean;
begin
  Result := ((AExpr.ResolvedType <> nil) and AExpr.ResolvedType.IsFloat())
    or (AExpr is TFloatLiteral);
end;

procedure TArm64Backend.EmitExprToD0(AExpr: TASTExpr);
var
  BE: TBinaryExpr;
  Idx: Integer;
  Lit: string;
  CondName: string;
  RtlMathSym: string;
begin
  if AExpr is TFloatLiteral then
  begin
    { .rodata double constant addressed via an adrp/PAGEOFF pair — the
      AArch64 analogue of the x86-64 .LF label + movsd(%rip) }
    Lit := TFloatLiteral(AExpr).Value;
    Idx := FFloatLits.IndexOf(Lit);
    if Idx < 0 then
      Idx := FFloatLits.Add(Lit);
    Self.Emit(Format(#9'adrp x9, __d%d@PAGE', [Idx]));
    Self.Emit(Format(#9'ldr d0, [x9, __d%d@PAGEOFF]', [Idx]));
    Exit;
  end;
  if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsConstant and
     (AExpr.ResolvedType <> nil) and AExpr.ResolvedType.IsFloat() then
  begin
    { Float-typed named constant (const X = 6.28; ...): inline its literal
      value.  The const has no storage — ConstString holds the source
      text — so loading from a symbol named after it would reference an
      undefined label.  Same .rodata pool as a TFloatLiteral (mirrors the
      x86-64 arm of this rule). }
    Lit := TIdentExpr(AExpr).ConstString;
    Idx := FFloatLits.IndexOf(Lit);
    if Idx < 0 then
      Idx := FFloatLits.Add(Lit);
    Self.Emit(Format(#9'adrp x9, __d%d@PAGE', [Idx]));
    Self.Emit(Format(#9'ldr d0, [x9, __d%d@PAGEOFF]', [Idx]));
    if AExpr.ResolvedType.Kind = tySingle then
    begin
      { the pool slot holds a double image of the literal; round to the
        declared Single precision so the value matches a Single load }
      Self.Emit(#9'fcvt s0, d0');
      Self.Emit(#9'fcvt d0, s0');
    end;
    Exit;
  end;
  if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsImplicitSelf and
     (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) and IsFloatExpr(AExpr) then
  begin
    { bare float field inside a method — the X0 path loads the bit
      pattern through Self (symmetry rule: every TIdentExpr branch needs
      its implicit-Self twin) }
    Self.EmitExprToX0(AExpr);
    Self.Emit(#9'fmov d0, x0');
    Exit;
  end;
  if (AExpr is TIdentExpr) and IsFloatExpr(AExpr) then
  begin
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tySingle) then
    begin
      { Single lives as a 4-byte value: load through s0 and widen }
      if TIdentExpr(AExpr).ParamMode = pmVar then
        NotYet('var Single parameter', AExpr);
      EmitSlotAddr('x9', TIdentExpr(AExpr).Name);
      Self.Emit(#9'ldr s0, [x9]');
      Self.Emit(#9'fcvt d0, s0');
      Exit;
    end;
    { reuse the slot machinery: load the 8-byte pattern into x0, move to d0 }
    EmitLoadSlot('x0', TIdentExpr(AExpr).Name);
    if TIdentExpr(AExpr).ParamMode = pmVar then
      Self.Emit(#9'ldr x0, [x0]');   { var param: slot holds the address }
    Self.Emit(#9'fmov d0, x0');
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and IsFloatExpr(AExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind =
       tyStaticArray) then
  begin
    { float array element: the integer path loads the bit pattern }
    Self.EmitExprToX0(AExpr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'str w0, [sp, #-16]!');
      Self.Emit(#9'ldr s0, [sp]');
      Self.Emit(#9'add sp, sp, #16');
      Self.Emit(#9'fcvt d0, s0');
    end
    else
      Self.Emit(#9'fmov d0, x0');
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).PropRead <> nil) and IsFloatExpr(AExpr) then
  begin
    { float property read: the getter leaves the value in d0 (or s0 for
      Single — widen) }
    EmitPropReadCall(TFieldAccessExpr(AExpr));
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tySingle) then
      Self.Emit(#9'fcvt d0, s0');
    Exit;
  end;
  if (AExpr is TFieldAccessExpr) and IsFloatExpr(AExpr) then
  begin
    { float field: load the bit pattern via the integer path.  A Single
      field arrives as 4 bytes in w0 — bounce it through the stack into
      s0 and widen (no fmov s,w encoding in the assembler yet). }
    Self.EmitExprToX0(AExpr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'str w0, [sp, #-16]!');
      Self.Emit(#9'ldr s0, [sp]');
      Self.Emit(#9'add sp, sp, #16');
      Self.Emit(#9'fcvt d0, s0');
    end
    else
      Self.Emit(#9'fmov d0, x0');
    Exit;
  end;
  if AExpr is TMethodCallExpr then
  begin
    { float-returning method call: the integer emitter's method paths end
      at the call, and the value is already in d0 }
    if TMethodCallExpr(AExpr).IsConstructorCall then
      NotYet('constructor in float context', AExpr);
    EmitMethodCallExpr(TMethodCallExpr(AExpr));
    Exit;
  end;
  { Numeric type-cast Double(X) / Single(X) in a float context (leg 30): the
    name resolves to a TYPE, so the node is a TFuncCallExpr with ResolvedDecl
    = nil and one argument — it is a real conversion, NEVER a call/bit copy.
    Mirrors x86-64 (:6912) and QBE (:12964).  The D0 contract is "d0 holds a
    double", so: a float operand is materialised into d0 (already widened by
    EmitExprToD0OrConvert), then when the cast TARGET is Single the value is
    round-tripped through single precision (fcvt s0,d0 / fcvt d0,s0) so the
    32-bit rounding actually happens — Double(Single(x)) must lose precision. }
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 1) and
     (AExpr.ResolvedType <> nil) and
     { the name denotes a TYPE: either the table resolves it, or -- for a
       type declared inside a unit, which the program-level table cannot
       see (PStackNode in the fiber runtime) -- the call's result type IS
       that named type.  A builtin's result type never carries the builtin's
       own name, so an unlowered builtin still reaches the honest NotYet. }
     (((FSymTable <> nil) and
       (FSymTable.FindType(TFuncCallExpr(AExpr).Name) <> nil)) or
      SameText(AExpr.ResolvedType.Name, TFuncCallExpr(AExpr).Name)) and AExpr.ResolvedType.IsFloat() then
  begin
    Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    if AExpr.ResolvedType.Kind = tySingle then
    begin
      Self.Emit(#9'fcvt s0, d0');   { round to single precision }
      Self.Emit(#9'fcvt d0, s0');   { re-widen — the D0 contract is a double }
    end;
    Exit;
  end;
  { Float-math builtins lower to the pure-Pascal runtime.math RTL, the
    same functions the x86-64 and QBE backends call -- no libm/libSystem
    math anywhere.  All are double-only; the D0 contract is "d0 holds a
    double", so no Single narrowing happens here (the caller narrows when
    the expression type is Single).  EmitExprToD0OrConvert widens any
    Single/integer argument, and AAPCS64 passes/returns doubles in d0. }
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 1) then
  begin
    RtlMathSym := '';
    if SameText(TFuncCallExpr(AExpr).Name, 'Sqrt') then
      RtlMathSym := '_BlaiseSqrtD'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Sin') then
      RtlMathSym := '_BlaiseSin'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Cos') then
      RtlMathSym := '_BlaiseCos'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Tan') then
      RtlMathSym := '_BlaiseTan'
    else if SameText(TFuncCallExpr(AExpr).Name, 'ArcSin') then
      RtlMathSym := '_BlaiseArcSin'
    else if SameText(TFuncCallExpr(AExpr).Name, 'ArcCos') then
      RtlMathSym := '_BlaiseArcCos'
    else if SameText(TFuncCallExpr(AExpr).Name, 'ArcTan') then
      RtlMathSym := '_BlaiseArcTan'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Ln') then
      RtlMathSym := '_BlaiseLn'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Log2') then
      RtlMathSym := '_BlaiseLog2'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Log10') then
      RtlMathSym := '_BlaiseLog10'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Sinh') then
      RtlMathSym := '_BlaiseSinh'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Cosh') then
      RtlMathSym := '_BlaiseCosh'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Tanh') then
      RtlMathSym := '_BlaiseTanh'
    else if SameText(TFuncCallExpr(AExpr).Name, 'Abs') and
            (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType <> nil) and
            TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]).ResolvedType.IsFloat() then
      RtlMathSym := '_BlaiseFabs';
    if RtlMathSym <> '' then
    begin
      Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
      EmitCallSym(RtlMathSym);
      Exit;
    end;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AExpr).IsIndirectCall) and
     (TFuncCallExpr(AExpr).Args.Count = 2) and
     (SameText(TFuncCallExpr(AExpr).Name, 'Power') or
      SameText(TFuncCallExpr(AExpr).Name, 'ArcTan2')) then
  begin
    { two-argument RTL math call: first arg in d0, second in d1, each
      widened to double by its own type via EmitExprToD0OrConvert }
    Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    Self.Emit(#9'str d0, [sp, #-16]!');
    Self.EmitExprToD0OrConvert(TASTExpr(TFuncCallExpr(AExpr).Args.Items[1]));
    Self.Emit(#9'fmov d1, d0');
    Self.Emit(#9'ldr d0, [sp], #16');
    if SameText(TFuncCallExpr(AExpr).Name, 'Power') then
      EmitCallSym('_BlaisePow')
    else
      EmitCallSym('_BlaiseArcTan2');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     SameText(TFuncCallExpr(AExpr).Name, 'StrToDouble') and
     (TFuncCallExpr(AExpr).ResolvedDecl = nil) and
     (TFuncCallExpr(AExpr).Args.Count = 1) then
  begin
    { _StrToDouble(S): Double in d0.  An OWNED string argument (a concat or
      call result) is released after the call, with the result parked. }
    Self.EmitExprToX0(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    if ArcExprOwnsRef(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0])) then
    begin
      EmitPushX0();                           { [str] }
      EmitCallSym('_StrToDouble');
      Self.Emit(#9'str d0, [sp, #-16]!');     { [str][d0] }
      Self.Emit(#9'ldr x0, [sp, #16]');
      EmitCallSym('_StringRelease');
      Self.Emit(#9'ldr d0, [sp], #16');
      Self.Emit(#9'add sp, sp, #16');
    end
    else
      EmitCallSym('_StrToDouble');
    Exit;
  end;
  if AExpr is TFuncCallExpr then
  begin
    if TFuncCallExpr(AExpr).IsIndirectCall or
       TFuncCallExpr(AExpr).IsImplicitSelfMethod or
       (TFuncCallExpr(AExpr).ResolvedDecl = nil) then
      NotYet('this call form in float context', AExpr);
    EmitCall(TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl),
      TFuncCallExpr(AExpr).Name, TFuncCallExpr(AExpr).Args);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tySingle) then
      Self.Emit(#9'fcvt d0, s0');   { Single returns in s0 — widen }
    { a Double-returning call leaves its result in d0 already }
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
    Self.EmitExprToD0(TBinaryExpr(AExpr).LoweredCall);
    Exit;
  end;
  if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr(AExpr);
    { int operands convert on the way in (scvtf) — mixed int/float exprs }
    Self.EmitExprToD0OrConvert(BE.Left);
    Self.Emit(#9'str d0, [sp, #-16]!');
    Self.EmitExprToD0OrConvert(BE.Right);
    Self.Emit(#9'fmov d1, d0');
    Self.Emit(#9'ldr d0, [sp], #16');
    case BE.Op of
      boAdd:   Self.Emit(#9'fadd d0, d0, d1');
      boSub:   Self.Emit(#9'fsub d0, d0, d1');
      boMul:   Self.Emit(#9'fmul d0, d0, d1');
      boSlash: Self.Emit(#9'fdiv d0, d0, d1');
    else
      NotYet('float binary operator', AExpr);
    end;
    Exit;
  end;
  if AExpr is TDerefExpr then
  begin
    { P^ where the pointee is Double/Single: load through the pointer }
    Self.EmitExprToX0(TDerefExpr(AExpr).Expr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tySingle) then
    begin
      Self.Emit(#9'ldr s0, [x0]');
      Self.Emit(#9'fcvt d0, s0');
    end
    else
      Self.Emit(#9'ldr d0, [x0]');
    Exit;
  end;
  NotYet('float expression ' + AExpr.ClassName, AExpr);
end;

procedure TArm64Backend.EmitExprToD0OrConvert(AExpr: TASTExpr);
begin
  if IsFloatExpr(AExpr) then
    EmitExprToD0(AExpr)
  else
  begin
    Self.EmitExprToX0(AExpr);
    Self.Emit(#9'scvtf d0, x0');
  end;
end;

{ ---- statements ---------------------------------------------------------- }

procedure TArm64Backend.EmitStmtList(AStmts: TObjectList);
var
  I: Integer;
begin
  for I := 0 to AStmts.Count - 1 do
    Self.EmitStmt(TASTStmt(AStmts.Items[I]));
end;

procedure TArm64Backend.EmitStmt(AStmt: TASTStmt);
var
  Mark: Integer;
begin
  { Statement-scoped deferred-release boundary (BUG-048/BUG-049).  A class
    field read on an owned transient base spills that base to a _pendrel slot
    (see the field-read emitter) instead of releasing it inline (UAF) or
    pinning it (leak).  Bracketing EVERY statement flushes those deferred
    bases at the statement boundary, AFTER the borrowed field value has been
    consumed — so the leak is closed in every statement context (assignment,
    call argument, if-body, …), not just the four leaf-assignment kinds.
    Control-flow / compound statements recurse into EmitStmtBody -> EmitStmt
    for their own child leaves, each of which flushes its own; a LOOP
    condition additionally flushes per iteration inside its emitter (the
    single post-body flush here would only release the last iteration's
    deferred base). }
  Mark := FPendingRelCount;
  Self.EmitStmtBody(AStmt);
  Self.FlushNativePendingReleases(Mark);
end;

procedure TArm64Backend.EmitStmtBody(AStmt: TASTStmt);
begin
  { empty statement (bare ';' bodies — `while X do ;`, `if C then ;`):
    nothing to emit.  Without this guard the fallthrough NotYet derefs
    nil for the class name and the COMPILER segfaults. }
  if AStmt = nil then Exit;
  if AStmt is TCompoundStmt then
  begin
    EmitStmtList(TCompoundStmt(AStmt).Stmts);
    Exit;
  end;
  if AStmt is TAsmStmt then
  begin
    { verbatim inline-asm block — the text is already arm64 (asm routines
      in the RTL are guarded by the target OS define) }
    Self.Emit(TAsmStmt(AStmt).Code);
    Exit;
  end;
  if AStmt is TAssignment then
  begin
    EmitAssignment(TAssignment(AStmt));
    Exit;
  end;
  if AStmt is TFieldAssignment then
  begin
    EmitFieldAssign(TFieldAssignment(AStmt));
    Exit;
  end;
  if AStmt is TProcCall then
  begin
    EmitProcCallStmt(TProcCall(AStmt));
    Exit;
  end;
  if AStmt is TMethodCallStmt then
  begin
    EmitMethodCallStmt(TMethodCallStmt(AStmt));
    Exit;
  end;
  if AStmt is TInheritedCallStmt then
  begin
    { static dispatch to the parent implementation with the current Self.
      `inherited` resolving to NO parent body (TObject's default) is a
      no-op, matching the x86-64 backend. }
    if TInheritedCallStmt(AStmt).ResolvedMethod = nil then
      Exit;
    EmitLoadSlot('x0', 'Self');
    EmitPushX0();
    EmitCall(TMethodDecl(TInheritedCallStmt(AStmt).ResolvedMethod),
      TInheritedCallStmt(AStmt).Name, TInheritedCallStmt(AStmt).Args,
      '', True, VIRT_NONE);
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    EmitIf(TIfStmt(AStmt));
    Exit;
  end;
  if AStmt is TWhileStmt then
  begin
    EmitWhile(TWhileStmt(AStmt));
    Exit;
  end;
  if AStmt is TRepeatStmt then
  begin
    EmitRepeat(TRepeatStmt(AStmt));
    Exit;
  end;
  if AStmt is TCaseStmt then
  begin
    EmitCase(TCaseStmt(AStmt));
    Exit;
  end;
  if AStmt is TTryFinallyStmt then
  begin
    EmitTryFinally(TTryFinallyStmt(AStmt));
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    EmitTryExcept(TTryExceptStmt(AStmt));
    Exit;
  end;
  if AStmt is TRaiseStmt then
  begin
    EmitRaise(TRaiseStmt(AStmt));
    Exit;
  end;
  if AStmt is TStaticSubscriptAssign then
  begin
    EmitStaticElemAssign(TStaticSubscriptAssign(AStmt));
    Exit;
  end;
  if AStmt is TForStmt then
  begin
    EmitFor(TForStmt(AStmt));
    Exit;
  end;
  if AStmt is TForInStmt then
  begin
    EmitForIn(TForInStmt(AStmt));
    Exit;
  end;
  if AStmt is TPointerWriteStmt then
  begin
    EmitPointerWrite(TPointerWriteStmt(AStmt));
    Exit;
  end;
  if AStmt is TExitStmt then
  begin
    EmitExit(TExitStmt(AStmt));
    Exit;
  end;
  if AStmt is TBreakStmt then
  begin
    if FBreakLbls.Count = 0 then
      NotYet('break outside a loop', AStmt);
    if FLoopExcDepth.Count > 0 then
      EmitExcUnwindTo(StrToInt(
        FLoopExcDepth.Strings[FLoopExcDepth.Count - 1]));
    Self.Emit(Format(#9'b %s', [FBreakLbls.Strings[FBreakLbls.Count - 1]]));
    Exit;
  end;
  if AStmt is TContinueStmt then
  begin
    if FContLbls.Count = 0 then
      NotYet('continue outside a loop', AStmt);
    if FLoopExcDepth.Count > 0 then
      EmitExcUnwindTo(StrToInt(
        FLoopExcDepth.Strings[FLoopExcDepth.Count - 1]));
    Self.Emit(Format(#9'b %s', [FContLbls.Strings[FContLbls.Count - 1]]));
    Exit;
  end;
  NotYet('statement ' + AStmt.ClassName, AStmt);
end;

procedure TArm64Backend.EmitPropReadCall(AFld: TFieldAccessExpr;
  const ASret: string);
begin
  { method-backed property read: a getter call on the receiver.  The value
    lands wherever the getter's return convention puts it (x0 for scalars,
    d0 for floats) — callers pick the register that matches the context.
    An indexed read calls getter(self, index). }
  if (AFld.PropRead.IndexParamName <> '') and (AFld.PropIndexExpr = nil) then
    NotYet('indexed property read without an index', AFld);
  if AFld.PropRead.IsStatic then
  begin
    { static property: the getter is a class-level routine — no receiver }
    Self.Emit(Format(#9'bl %s',
      [PropAccessorSym(AFld.PropOwnerType, AFld.PropRead.ReadMethod)]));
    Exit;
  end;
  if AFld.PropIndexExpr <> nil then
  begin
    { a string index is a single pointer-sized register value, passed borrowed
      like any string arg (leg 18) — same relaxation as the write path, mirrors
      x86-64 (:9256) / QBE which have no index-type guard. }
    if not (IsIntFam(AFld.PropIndexExpr.ResolvedType) or
            (AFld.PropIndexExpr is TIntLiteral) or
            ((AFld.PropIndexExpr.ResolvedType <> nil) and
             (AFld.PropIndexExpr.ResolvedType.Kind = tyString))) then
      NotYet('indexed property with a non-integer index', AFld);
    Self.EmitExprToX0(AFld.PropIndexExpr);
    EmitPushX0();
  end;
  { ---- receiver, in two stages ------------------------------------------
    STAGE 1 loads the object that HOLDS the receiver into x0; the three
    receiver forms differ only in how that object is reached.
    STAGE 2 steps from that object to the receiver itself, ONCE, for every
    form.

    Keeping stage 2 out of the branches is deliberate.  Each branch used to
    carry its own copy of the step, and each independently forgot it:
      2026-07-23  implicit Self  FUsedUnits.Strings[I] ran TStringList.Get on
                                the TParser
      2026-07-24  RecordName     Days via CD.ArrayElements[J]
      2026-07-25  chained base   Prog.Block.Decls[0] ran TObjectList.Get on the
                                TBlock — 46 crashing suites
                                (BUG-20260725-arm64-chained-indexed-prop-base)
    QBE has had none of the three because it applies the step once for all
    receiver forms (blaise.codegen.qbe.pas ~7075).  With the step hoisted here, a
    receiver form added later inherits it instead of becoming the fourth. }
  if AFld.Base <> nil then
  begin
    { chained receiver (A.B.Prop): the base expression yields the
      instance pointer }
    Self.EmitExprToX0(AFld.Base);
    { An OWNED transient base (Factory().Prop) carries a +1 nobody else will
      drop.  Hand that reference to a _pendrel slot: the release then happens
      at the enclosing statement's flush (every statement is flush-bracketed,
      BUG-049), which keeps the instance — and therefore any value the getter
      borrows from it — alive for the rest of the statement.  x0 is untouched
      by the frame store, so it stays the receiver.  This mirrors x86-64,
      which spills such a base to a _pendrel slot for field reads. }
    if ArcExprOwnsRef(AFld.Base) then
      if not DeferNativeClassRelease() then
        NotYet('property read on an owned transient base with all _pendrel '
          + 'slots busy', AFld);
  end
  else if AFld.IsImplicitSelf then
    EmitLoadSlot('x0', 'Self')
  else
  begin
    EmitLoadSlot('x0', AFld.RecordName);
    { a TRUE var/out record slot holds the caller's ADDRESS — deref to the
      record before stepping into its field. }
    if AFld.IsVarParam then
      Self.Emit(#9'ldr x0, [x0]');
  end;
  { STAGE 2 — the getter's receiver is the intermediate FIELD that holds it
    (the list in R.Field[I] / A.B.Field[I] / Self.FField[I]), not the object
    stage 1 produced.  EmitImplicitBaseStep is the one correct step: it
    dereferences a class-typed field and merely advances past an EMBEDDED
    record one, where the open-coded `add offset` + unconditional `ldr` the
    other two branches used would have wrongly dereferenced record bytes.
    A bare default-property read on the object itself (L[I]) carries no field
    info and needs no step. }
  if AFld.IsImplicitSelf and (AFld.Base = nil) then
    EmitImplicitBaseStep('x0', AFld.ImplicitBaseInfo)
  else
    EmitImplicitBaseStep('x0', AFld.FieldInfo);
  if AFld.PropIndexExpr <> nil then
    EmitPopTo('x1');
  { a large record getter writes its Result through x8 }
  if ASret <> '' then
    EmitSlotAddr('x8', ASret);
  if AFld.PropAccessorVSlot >= 0 then
  begin
    Self.Emit(#9'ldr x9, [x0]');
    Self.Emit(Format(#9'ldr x9, [x9, #%d]',
      [(AFld.PropAccessorVSlot + 1) * 8]));
    Self.Emit(#9'blr x9');
  end
  else
    Self.Emit(Format(#9'bl %s',
      [PropAccessorSym(AFld.PropOwnerType, AFld.PropRead.ReadMethod)]));
end;

function TArm64Backend.RecordPropRead(AExpr: TASTExpr): TFieldAccessExpr;
var
  E: TASTExpr;
begin
  Result := nil;
  E := AExpr;
  if (E is TStringSubscriptExpr) and
     (TStringSubscriptExpr(E).IndexExpr = nil) then
    { the default-property form Obj[I]: a subscript wrapping the property
      read, whose PropIndexExpr carries the index }
    E := TStringSubscriptExpr(E).StrExpr;
  if (E is TFieldAccessExpr) and
     (TFieldAccessExpr(E).PropRead <> nil) and
     (E.ResolvedType <> nil) and
     (E.ResolvedType.Kind = tyRecord) then
    Result := TFieldAccessExpr(E);
end;

procedure TArm64Backend.EmitRecPropToTemp(AFld: TFieldAccessExpr);
var
  Shape, K: Integer;
  Tmp: string;
begin
  { a record-typed property getter's value, materialised like a record
    call (EmitRecCallToRret): a per-site scratch, filled through x8 for the
    large shape or from x0/x1/d0.. for the register shapes }
  Tmp := '__rtmp_' + IntToStr(FJArgN);
  FJArgN := FJArgN + 1;
  if not FFrame.ContainsKey(Tmp) then
    AddLocal(Tmp, AFld.ResolvedType.RawSize());
  Shape := RecReturnShape(TRecordTypeDesc(AFld.ResolvedType));
  if Shape = 0 then
    EmitPropReadCall(AFld, Tmp)
  else
  begin
    EmitPropReadCall(AFld);
    EmitSlotAddr('x9', Tmp);
    case Shape of
      1: Self.Emit(#9'str x0, [x9]');
      2:
      begin
        Self.Emit(#9'str x0, [x9]');
        Self.Emit(#9'str x1, [x9, #8]');
      end;
    else
      for K := 0 to (Shape - 100) - 1 do
        Self.Emit(Format(#9'str d%d, [x9, #%d]', [K, K * 8]));
    end;
  end;
  EmitSlotAddr('x0', Tmp);
end;

procedure TArm64Backend.EmitInterfaceAssign(AAsgn: TAssignment);
var
  ItabSym: string;
begin
  { fat-pointer stores: the obj half co-owns the backing instance (retain
    on store unless the source owns a +1, release the old); the itab half
    is static rodata — never refcounted. }
  if AAsgn.IsWeakLhs then
  begin
    { weak interface: the obj half goes through the weak table; the itab
      half is plain data }
    if AAsgn.IsVarParam or (AAsgn.ImplicitSelfField <> nil) then
      NotYet('[Weak] interface assignment to this target', AAsgn);
    if ArcExprOwnsRef(AAsgn.Expr) then
      NotYet('owned transient into a [Weak] interface', AAsgn);
    if (AAsgn.Expr.ResolvedType <> nil) and
       (AAsgn.Expr.ResolvedType.Kind = tyClass) then
    begin
      Self.EmitExprToX0(AAsgn.Expr);
      Self.Emit(#9'mov x1, x0');
      EmitSlotAddr('x0', AAsgn.Name);
      EmitCallSym('_WeakAssign');
      ItabSym := IntfItabSym(TRecordTypeDesc(AAsgn.Expr.ResolvedType).Name,
        AAsgn.ResolvedLhsType.Name);
      Self.Emit(Format(#9'adrp x0, %s@PAGE', [ItabSym]));
      Self.Emit(Format(#9'add x0, x0, %s@PAGEOFF', [ItabSym]));
      EmitStoreSlot('x0', AAsgn.Name + '_itab');
      Exit;
    end;
    NotYet('[Weak] interface assignment from this expression', AAsgn);
  end;
  if (AAsgn.Expr is TAsExpr) and (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) then
  begin
    { I := Obj as IFoo — runtime itab lookup through the impllist chain;
      a nil result is an invalid cast }
    if AAsgn.IsVarParam or (AAsgn.ImplicitSelfField <> nil) then
      NotYet('as-cast into this interface target', AAsgn);
    EmitInterfaceAsCast(AAsgn);
    Exit;
  end;
  if AAsgn.ImplicitSelfField <> nil then
  begin
    { FIntf := value inside a method: the pair is a field of Self }
    EmitInstBase('x0', 'Self', False);
    EmitPushX0();
    EmitIntfStoreStacked(TFieldInfo(AAsgn.ImplicitSelfField).Offset,
      AAsgn.Expr, AAsgn.ResolvedLhsType);
    Exit;
  end;
  if AAsgn.IsVarParam then
  begin
    { var/out interface parameter: the slot holds the address of the
      caller's (obj, itab) pair }
    EmitLoadSlot('x0', AAsgn.Name);
    EmitPushX0();
    EmitIntfStoreStacked(0, AAsgn.Expr, AAsgn.ResolvedLhsType);
    Exit;
  end;
  { a named variable: its two halves are separate slots (frame or global) }
  if not EmitIntfPairToX0X1(AAsgn.Expr, AAsgn.ResolvedLhsType) then
  begin
    Self.Emit(#9'stp x0, x1, [sp, #-16]!');
    EmitCallSym('_ClassAddRef');
    Self.Emit(#9'ldp x0, x1, [sp], #16');
  end;
  Self.Emit(#9'stp x0, x1, [sp, #-16]!');
  EmitLoadSlot('x0', AAsgn.Name);
  EmitCallSym('_ClassRelease');
  Self.Emit(#9'ldp x0, x1, [sp], #16');
  { obj first: a threadvar store parks only its own value register and
    returns through x0 }
  EmitStoreSlot('x0', AAsgn.Name);
  EmitStoreSlot('x1', AAsgn.Name + '_itab');
end;

procedure TArm64Backend.EmitInterfaceAsCast(AAsgn: TAssignment);
var
  AE: TAsExpr;
  OkL: string;
begin
  AE := TAsExpr(AAsgn.Expr);
  if ArcExprOwnsRef(AE.Obj) then
    NotYet('as-cast of an owned transient', AAsgn);
  Self.EmitExprToX0(AE.Obj);
  EmitPushX0();                     { the obj value }
  { load the typeinfo address through EmitTypeinfoAddr so the symbol matches the
    prefixed definition/impllist (LINK-1: a bare name here dangled). }
  EmitTypeinfoAddr('x1', AE.TypeName);
  EmitCallSym('_GetItab');       { x0 = itab or nil }
  OkL := NewLabel('asok');
  Self.Emit(Format(#9'cbnz x0, %s', [OkL]));
  EmitRaiseInvalidCast();
  Self.Emit(OkL + ':');
  EmitStoreSlot('x0', AAsgn.Name + '_itab');
  { obj half with the usual ARC: retain new (borrowed source), release old }
  Self.Emit(#9'ldr x0, [sp]');      { peek the obj }
  EmitCallSym('_ClassAddRef');
  EmitLoadSlot('x0', AAsgn.Name);
  EmitCallSym('_ClassRelease');
  EmitPopTo('x0');
  EmitStoreSlot('x0', AAsgn.Name);
end;

function TArm64Backend.EmitIntfPairToX0X1(AExpr: TASTExpr;
  AIntfType: TTypeDesc): Boolean;
var
  FA: TFieldAccessExpr;
  IE: TIdentExpr;
  ME: TMethodCallExpr;
  ItabSym: string;
begin
  { One source lowering for every interface consumer (assignment, field
    store, argument, receiver): x0 = obj, x1 = itab.  Result tells the
    caller whether the obj half is already an owned +1 (call results) or a
    borrow it must retain before storing. }
  Result := False;
  if AExpr is TNilLiteral then
  begin
    Self.Emit(#9'mov x0, xzr');
    Self.Emit(#9'mov x1, xzr');
    Result := True;                   { nothing to retain }
    Exit;
  end;
  if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
  begin
    { narrowing a class value: the itab is known statically }
    ItabSym := IntfItabSym(TRecordTypeDesc(AExpr.ResolvedType).Name,
      AIntfType.Name);
    Self.EmitExprToX0(AExpr);
    Result := ArcExprOwnsRef(AExpr);
    Self.Emit(Format(#9'adrp x1, %s@PAGE', [ItabSym]));
    Self.Emit(Format(#9'add x1, x1, %s@PAGEOFF', [ItabSym]));
    Exit;
  end;
  if (AExpr.ResolvedType = nil) or (AExpr.ResolvedType.Kind <> tyInterface) then
    NotYet('interface value from this expression', AExpr);
  if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr(AExpr);
    if IsCaptured(IE.Name) then
      NotYet('read of a captured interface variable', AExpr);
    if (IE.IsImplicitSelf and (IE.ImplicitFieldInfo <> nil)) or
       (IE.ParamMode = pmVar) then
    begin
      { the pair lives in memory: a field of Self, or the caller's pair
        behind a var parameter }
      EmitRecIdentAddr('x9', IE);
      Self.Emit(#9'ldp x0, x1, [x9]');
      Exit;
    end;
    { itab first: a threadvar's TLV thunk returns through x0 }
    EmitLoadSlot('x1', IE.Name + '_itab');
    EmitLoadSlot('x0', IE.Name);
    Exit;
  end;
  if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    if FA.IsArrayAccess and (FA.FieldInfo <> nil) then
    begin
      { an interface ELEMENT of an array field (Obj.Items[I], A.B.Arr[I]) }
      EmitFieldElemAddr(FA);
      Self.Emit(#9'ldp x0, x1, [x0]');
      Exit;
    end;
    if (FA.FieldInfo = nil) or (FA.PropRead <> nil) or FA.IsMethodCall or
       FA.IsInterfaceCall or (FA.PropIndexExpr <> nil) or
       FA.IsClassVarRead or FA.IsStaticPropGet then
      NotYet('interface value from this field form', AExpr);
    { an interface FIELD: both halves sit side by side in the instance }
    EmitRecFieldAddrToX0(FA);
    Self.Emit(#9'ldp x0, x1, [x0]');
    Exit;
  end;
  if AExpr is TDerefExpr then
  begin
    { P^ with P: ^IFoo (TListEnumerator<T>.GetCurrent's Result := Ptr^): the
      pointer designates an (obj, itab) pair -- a borrow }
    Self.EmitExprToX0(TDerefExpr(AExpr).Expr);
    Self.Emit(#9'ldp x0, x1, [x0]');
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) then
  begin
    { an interface ELEMENT: both halves sit side by side in the array }
    case TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind of
      tyStaticArray: EmitStaticElemAddr(TStringSubscriptExpr(AExpr));
      tyDynArray, tyOpenArray: EmitDynElemAddr(TStringSubscriptExpr(AExpr));
    else
      NotYet('interface value from this subscript', AExpr);
    end;
    Self.Emit(#9'ldp x0, x1, [x0]');
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl <> nil) then
  begin
    { interface-returning call: the callee fills the 16-byte __iret
      scratch through x8; the returned obj is OWNED (+1) }
    if TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl).IsExternal then
      NotYet('external interface-returning call', AExpr);
    EmitCall(TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl),
      TFuncCallExpr(AExpr).Name, TFuncCallExpr(AExpr).Args, '__iret');
    EmitSlotAddr('x9', '__iret');
    Self.Emit(#9'ldp x0, x1, [x9]');
    Result := True;
    Exit;
  end;
  if AExpr is TMethodCallExpr then
  begin
    ME := TMethodCallExpr(AExpr);
    if (ME.ResolvedClassType <> nil) and
       (ME.ResolvedClassType.Kind = tyInterface) then
      { itab dispatch returning an interface: the same x8 sret contract }
      EmitIntfDispatch(ME.ObjectName,
        TInterfaceTypeDesc(ME.ResolvedClassType),
        TInterfaceTypeDesc(ME.ResolvedClassType).MethodIndex(ME.Name),
        ME.Args, ME.ObjExpr, ME.IsVarParam, nil, '__iret')
    else if (ME.ResolvedMethod <> nil) and not ME.IsConstructorCall and
            not ME.IsProcFieldCall then
      { class-receiver method returning an interface: EmitRecCallDispatch
        handles the receiver forms and virtual dispatch }
      EmitRecCallDispatch(AExpr, '__iret')
    else
      NotYet('interface value from this method-call form', AExpr);
    EmitSlotAddr('x9', '__iret');
    Self.Emit(#9'ldp x0, x1, [x9]');
    Result := True;
    Exit;
  end;
  NotYet('interface value from this expression', AExpr);
end;

procedure TArm64Backend.EmitIntfStoreStacked(AOff: Integer;
  AValueExpr: TASTExpr; AIntfType: TTypeDesc);
begin
  { [base] is on top of the stack.  Retain the new obj unless the source
    already owns it, release the old obj, then store both halves; the base
    is re-read after the release call (it clobbers scratch registers). }
  if not EmitIntfPairToX0X1(AValueExpr, AIntfType) then
  begin
    Self.Emit(#9'stp x0, x1, [sp, #-16]!');
    EmitCallSym('_ClassAddRef');
    Self.Emit(#9'ldp x0, x1, [sp], #16');
  end;
  Self.Emit(#9'stp x0, x1, [sp, #-16]!');      { [base][obj,itab] }
  Self.Emit(#9'ldr x9, [sp, #16]');
  Self.Emit(Format(#9'ldr x0, [x9, #%d]', [AOff]));
  EmitCallSym('_ClassRelease');
  Self.Emit(#9'ldr x9, [sp, #16]');
  Self.Emit(#9'ldp x0, x1, [sp], #16');
  Self.Emit(Format(#9'str x0, [x9, #%d]', [AOff]));
  Self.Emit(Format(#9'str x1, [x9, #%d]', [AOff + 8]));
  Self.Emit(#9'add sp, sp, #16');               { drop the base }
end;

function TArm64Backend.EmitIntfRecvPair(const AObjName: string;
  AObjExpr: TASTExpr; AVarParam: Boolean; AImplicitBase: TFieldInfo;
  ANode: TASTNode): Boolean;
begin
  { x0/x1 := the receiver pair.  Result = the obj half is an OWNED +1 (a
    call result: MakeIntf().M()), which the caller releases after the call;
    every other receiver is a borrow for the call's duration. }
  Result := False;
  if AObjExpr <> nil then
  begin
    Result := EmitIntfPairToX0X1(AObjExpr, AObjExpr.ResolvedType);
    Exit;
  end;
  if AImplicitBase <> nil then
  begin
    { FIntf.Method() inside a method: the pair is a field of Self }
    EmitInstBase('x9', 'Self', False);
    if AImplicitBase.Offset <> 0 then
      EmitAddSubImm('add', 'x9', 'x9', AImplicitBase.Offset);
    Self.Emit(#9'ldp x0, x1, [x9]');
    Exit;
  end;
  if AVarParam then
  begin
    EmitLoadSlot('x9', AObjName);
    Self.Emit(#9'ldp x0, x1, [x9]');
    Exit;
  end;
  EmitLoadSlot('x1', AObjName + '_itab');   { itab first: see above }
  EmitLoadSlot('x0', AObjName);
end;

procedure TArm64Backend.EmitAssignment(AAsgn: TAssignment);
var
  I, Shape: Integer;
  RD: TMethodDecl;
begin
  { Run := TRunMethod(M) — a RECORD cast to a method-pointer type.  Both sides
    are 16-byte fat values (Code at +0, Data/Env at +8), but the generic value
    cast lowers to a single x0 word, so only Code was stored and Data was left
    as whatever the slot already held.  EmitFatPtrCall then read Data from that
    stale half and called the method with a junk Self — the shape
    blaise.testing's RunTest uses to dispatch every published test, so every
    test crashed on its first field access.  Copy BOTH words. }
  if (AAsgn.ResolvedLhsType <> nil) and
     IsMethodPtrType(AAsgn.ResolvedLhsType) and
     (AAsgn.Expr is TFuncCallExpr) and
     (TFuncCallExpr(AAsgn.Expr).ResolvedDecl = nil) and
     (not TFuncCallExpr(AAsgn.Expr).IsIndirectCall) and
     (TFuncCallExpr(AAsgn.Expr).Args.Count = 1) and
     (TASTExpr(TFuncCallExpr(AAsgn.Expr).Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(TFuncCallExpr(AAsgn.Expr).Args.Items[0]).ResolvedType.Kind
        = tyRecord) then
  begin
    if IsCaptured(AAsgn.Name) or AAsgn.IsVarParam then
      NotYet('method-pointer cast into a captured or var-param target', AAsgn);
    { x0 = &source record; x9 = &destination fat slot (local or global) }
    EmitRecAddrToX0(TASTExpr(TFuncCallExpr(AAsgn.Expr).Args.Items[0]));
    Self.Emit(#9'ldr x1, [x0]');          { Code }
    Self.Emit(#9'ldr x2, [x0, #8]');      { Data / Env }
    EmitSlotAddr('x9', AAsgn.Name);
    Self.Emit(#9'str x1, [x9]');
    Self.Emit(#9'str x2, [x9, #8]');
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and
     IsMethodPtrType(AAsgn.ResolvedLhsType) then
  begin
    EmitFatPtrAssign(AAsgn);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType is TSetTypeDesc) and
     TSetTypeDesc(AAsgn.ResolvedLhsType).IsJumbo() then
  begin
    { S := <jumbo set>: a jumbo set is an inline byte bitmap and its value
      evaluates to an ADDRESS, so the assignment COPIES the bitmap into the
      target.  The generic scalar path stored that address into the target's
      first 8 bytes instead -- a pointer to the RHS's temporary bitmap, which
      dangled once its frame or loop iteration moved on. }
    Self.EmitExprToX0(AAsgn.Expr);                  { source bitmap address }
    Self.Emit(#9'mov x1, x0');
    if AAsgn.ImplicitSelfField <> nil then
    begin
      EmitLoadSlot('x0', 'Self');
      EmitAddSubImm('add', 'x0', 'x0', TFieldInfo(AAsgn.ImplicitSelfField).Offset);
    end
    else if IsCaptured(AAsgn.Name) then
    begin
      EmitLoadSlot('x0', '_cap_' + AAsgn.Name);
      if AAsgn.IsVarParam then
        Self.Emit(#9'ldr x0, [x0]');
    end
    else if AAsgn.IsVarParam then
      EmitLoadSlot('x0', AAsgn.Name)                { slot holds &set }
    else
      EmitSlotAddr('x0', AAsgn.Name);
    EmitIntLiteral('x2', AAsgn.ResolvedLhsType.RawSize());
    { an operator result lands in its own frame slot, so source and target
      never partially overlap (S := S is an exact self-copy) }
    EmitCallSym('memcpy');
    Exit;
  end;
  { Captured managed writes (leg 17).  '_cap_<Name>' holds &<Name>, so the ARC
    store runs retain-new / release-old THROUGH that address — the same
    discipline as a var-param managed target, but the address is the capture
    pointer (one indirection to the outer storage).  String and class are
    wired here; interface/dyn-array/record captured writes stay an honest hole
    (their ARC-through-indirection arms are not yet split out). }
  if IsCaptured(AAsgn.Name) and (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind = tyString) then
  begin
    Self.EmitExprToX0(AAsgn.Expr);
    if not ArcExprOwnsRef(AAsgn.Expr) then
    begin
      EmitPushX0();
      EmitCallSym('_StringAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();                       { [newval] }
    EmitLoadSlot('x9', '_cap_' + AAsgn.Name);
    if AAsgn.IsVarParam then
      Self.Emit(#9'ldr x9, [x9]');      { captured var-param: extra deref }
    Self.Emit(#9'ldr x0, [x9]');        { old string }
    EmitCallSym('_StringRelease');
    EmitLoadSlot('x9', '_cap_' + AAsgn.Name);
    if AAsgn.IsVarParam then
      Self.Emit(#9'ldr x9, [x9]');
    EmitPopTo('x0');                    { newval }
    Self.Emit(#9'str x0, [x9]');
    Exit;
  end;
  if IsCaptured(AAsgn.Name) and (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind = tyClass) and not AAsgn.IsWeakLhs then
  begin
    Self.EmitExprToX0(AAsgn.Expr);
    if not ArcExprOwnsRef(AAsgn.Expr) then
    begin
      EmitPushX0();
      EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();
    EmitLoadSlot('x9', '_cap_' + AAsgn.Name);
    if AAsgn.IsVarParam then
      Self.Emit(#9'ldr x9, [x9]');
    Self.Emit(#9'ldr x0, [x9]');
    EmitCallSym('_ClassRelease');
    EmitLoadSlot('x9', '_cap_' + AAsgn.Name);
    if AAsgn.IsVarParam then
      Self.Emit(#9'ldr x9, [x9]');
    EmitPopTo('x0');
    Self.Emit(#9'str x0, [x9]');
    Exit;
  end;
  if IsCaptured(AAsgn.Name) and (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind in [tyInterface, tyDynArray, tyRecord]) then
    NotYet('assignment to a captured managed variable of this type', AAsgn);
  if (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind in [tyString, tyClass]) and
     (AAsgn.ImplicitSelfField <> nil) and not AAsgn.IsWeakLhs then
  begin
    { bare managed field := value inside a method — the instance-field
      store machinery runs the retain/release discipline against the
      field slot, not a frame slot }
    EmitImplicitSelfStore(AAsgn);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind = tyString) then
  begin
    { ARC discipline (mirrors x86-64): retain the incoming value unless the
      expression already OWNS a +1 reference (concat/call results), release
      the slot's previous string, then store.  A var-param target holds the
      caller's ADDRESS — the old-value load and the store deref it (the
      address is re-loaded after the release call clobbers x9). }
    Self.EmitExprToX0(AAsgn.Expr);
    if not ArcExprOwnsRef(AAsgn.Expr) then
    begin
      EmitPushX0();
      EmitCallSym('_StringAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();
    if AAsgn.IsVarParam then
    begin
      EmitLoadSlot('x9', AAsgn.Name);
      Self.Emit(#9'ldr x0, [x9]');
      EmitCallSym('_StringRelease');
      EmitLoadSlot('x9', AAsgn.Name);
      EmitPopTo('x0');
      Self.Emit(#9'str x0, [x9]');
      Exit;
    end;
    EmitLoadSlot('x0', AAsgn.Name);
    EmitCallSym('_StringRelease');
    EmitPopTo('x0');
    EmitStoreSlot('x0', AAsgn.Name);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind = tyInterface) then
  begin
    EmitInterfaceAssign(AAsgn);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind = tyDynArray) then
  begin
    { data-pointer ARC, mirroring the string discipline }
    if AAsgn.IsWeakLhs or AAsgn.IsVarParam or
       (AAsgn.ImplicitSelfField <> nil) then
      NotYet('dyn-array assignment to this target', AAsgn);
    Self.EmitExprToX0(AAsgn.Expr);
    if not ArcExprOwnsRef(AAsgn.Expr) then
    begin
      EmitPushX0();
      EmitCallSym('_DynArrayAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();
    EmitLoadSlot('x0', AAsgn.Name);
    EmitCallSym('_DynArrayRelease');
    EmitPopTo('x0');
    EmitStoreSlot('x0', AAsgn.Name);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind = tyClass) then
  begin
    if AAsgn.ImplicitSelfField <> nil then
      NotYet('implicit-Self class-field assignment via TAssignment', AAsgn);
    if AAsgn.IsWeakLhs then
    begin
      { weak slot: registered in the weak table, no refcount held.  An
        owned +1 RHS would leak into a non-owning slot — keep it honest }
      if ArcExprOwnsRef(AAsgn.Expr) then
        NotYet('owned transient into a [Weak] variable', AAsgn);
      Self.EmitExprToX0(AAsgn.Expr);
      Self.Emit(#9'mov x1, x0');
      EmitSlotAddr('x0', AAsgn.Name);
      EmitCallSym('_WeakAssign');
      Exit;
    end;
    { same ARC discipline as strings, through _Class* }
    Self.EmitExprToX0(AAsgn.Expr);
    if not ArcExprOwnsRef(AAsgn.Expr) then
    begin
      EmitPushX0();
      EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();                       { [newval] — survives the release }
    if AAsgn.IsVarParam then
    begin
      { var-param class: the slot holds the caller's ADDRESS.  Release the
        old value THROUGH the address, then store the new value there. }
      EmitLoadSlot('x9', AAsgn.Name);   { caller var address }
      Self.Emit(#9'ldr x0, [x9]');      { old value }
      EmitCallSym('_ClassRelease');
      EmitLoadSlot('x9', AAsgn.Name);   { re-load addr (release clobbers x9) }
      EmitPopTo('x0');                  { newval }
      Self.Emit(#9'str x0, [x9]');
      Exit;
    end;
    EmitLoadSlot('x0', AAsgn.Name);
    EmitCallSym('_ClassRelease');
    EmitPopTo('x0');
    EmitStoreSlot('x0', AAsgn.Name);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and (AAsgn.ImplicitSelfField <> nil) then
  begin
    { bare field := value inside a method — route through the field-store
      machinery with Self as the instance }
    EmitImplicitSelfStore(AAsgn);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and
     (AAsgn.ResolvedLhsType.Kind = tyRecord) then
  begin
    { A var-param record LHS: the slot holds the caller's ADDRESS, so the
      whole-record COPY path below dereferences the slot (EmitLoadSlot) for the
      dest instead of taking the slot's own address (leg 23).  The
      record-returning-CALL-into-var-param sub-case (which writes through an
      sret/x8 destination) is not yet wired for the deref'd dest — keep it an
      honest hole (self-host only needs the copy form, R := Arr[i]). }
    if AAsgn.IsVarParam and
       (((AAsgn.Expr is TFuncCallExpr) and
         (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil)) or
        ((AAsgn.Expr is TMethodCallExpr) and
         (TMethodCallExpr(AAsgn.Expr).ResolvedMethod <> nil) and
         not TMethodCallExpr(AAsgn.Expr).IsConstructorCall)) then
    begin
      { V := F() with V a var/out record (TList<T>.TryGet's AValue :=
        Get(I)): the call lands in its own scratch first -- the destination
        may alias an argument -- then the destination's old managed fields are
        released and the bytes move in, the call's +1 field refs transferring
        (no retain).  Callee-saved x19/x22 hold the two addresses across the
        release walk. }
      if (AAsgn.Expr is TFuncCallExpr) and
         TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).IsExternal then
        NotYet('external record-returning call', AAsgn);
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      EmitRecCallToRret(AAsgn.Expr);
      Self.Emit(#9'mov x19, x0');
      EmitLoadSlot('x22', AAsgn.Name);              { the caller's record }
      if not RecretManagedClean(TRecordTypeDesc(AAsgn.ResolvedLhsType)) then
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(AAsgn.ResolvedLhsType), 'x22', False);
      Self.Emit(#9'mov x0, x22');
      Self.Emit(#9'mov x1, x19');
      EmitIntLiteral('x2', AAsgn.ResolvedLhsType.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Exit;
    end;
    { record-returning call: classify the callee's return shape }
    if ((AAsgn.Expr is TFuncCallExpr) and
        (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil)) or
       ((AAsgn.Expr is TMethodCallExpr) and
        (TMethodCallExpr(AAsgn.Expr).ResolvedMethod <> nil) and
        not TMethodCallExpr(AAsgn.Expr).IsConstructorCall) then
    begin
      if AAsgn.Expr is TFuncCallExpr then
        RD := TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl)
      else
        RD := TMethodDecl(TMethodCallExpr(AAsgn.Expr).ResolvedMethod);
      if RD.IsExternal then
        { a C-side small-struct return needs full AAPCS64 marshalling
          validation on real hardware first — keep the hole honest }
        NotYet('external record-returning call', AAsgn);
      Shape := RecReturnShape(TRecordTypeDesc(AAsgn.ResolvedLhsType));
      if not RecretManagedClean(TRecordTypeDesc(AAsgn.ResolvedLhsType)) then
      begin
        { managed LHS: the callee's fresh value lands in the __rret
          scratch first — the LHS may alias an argument, so its old field
          refs are released only AFTER the call — then moves in with the
          +1 field refs transferring (no retain). }
        if Shape = 0 then
          EmitRecCallDispatch(AAsgn.Expr, '__rret')
        else
        begin
          EmitRecCallDispatch(AAsgn.Expr, '');
          EmitSlotAddr('x9', '__rret');
          case Shape of
            1: Self.Emit(#9'str x0, [x9]');
            2:
            begin
              Self.Emit(#9'str x0, [x9]');
              Self.Emit(#9'str x1, [x9, #8]');
            end;
          else
            for I := 0 to (Shape - 100) - 1 do
              Self.Emit(Format(#9'str d%d, [x9, #%d]', [I, I * 8]));
          end;
        end;
        Self.Emit(#9'str x19, [sp, #-16]!');
        EmitSlotAddr('x19', AAsgn.Name);
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(AAsgn.ResolvedLhsType), 'x19');
        Self.Emit(#9'ldr x19, [sp], #16');
        EmitSlotAddr('x0', AAsgn.Name);
        EmitSlotAddr('x1', '__rret');
        EmitIntLiteral('x2', AAsgn.ResolvedLhsType.RawSize());
        EmitCallSym('memcpy');
        Exit;
      end;
      if Shape = 0 then
      begin
        EmitRecCallDispatch(AAsgn.Expr, AAsgn.Name);
        Exit;
      end;
      EmitRecCallDispatch(AAsgn.Expr, '');
      EmitSlotAddr('x9', AAsgn.Name);
      case Shape of
        1: Self.Emit(#9'str x0, [x9]');
        2:
        begin
          Self.Emit(#9'str x0, [x9]');
          Self.Emit(#9'str x1, [x9, #8]');
        end;
      else
        for I := 0 to (Shape - 100) - 1 do
          Self.Emit(Format(#9'str d%d, [x9, #%d]', [I, I * 8]));
      end;
      Exit;
    end;
    { whole-record copy.  With managed fields the ARC discipline mirrors
      x86-64's record-var assignment: retain the SOURCE's managed fields
      first, release the destination's old ones, then memcpy the raw
      bytes — retain-before-release keeps self-assignment (R := R) exact.
      The walk calls clobber the scratch regs, so the two base addresses
      live in callee-saved x19/x22 for the duration. }
    if not RecretManagedClean(TRecordTypeDesc(AAsgn.ResolvedLhsType)) then
    begin
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      EmitRecAddrToX0(AAsgn.Expr);
      Self.Emit(#9'mov x19, x0');
      { dest = the record's address: a TRUE var-param slot holds the caller's
        ADDRESS (deref it); a local/global/by-value-param slot IS the record
        (its address). }
      EmitRecordBaseAddr('x22', AAsgn.Name, AAsgn.IsVarParam);
      Self.EmitRecordFieldRetains(
        TRecordTypeDesc(AAsgn.ResolvedLhsType), 'x19');
      { copy site: no-zero release keeps R := R exact
        (BUG-20260720-managed-record-self-assign) }
      Self.EmitRecordFieldReleases(
        TRecordTypeDesc(AAsgn.ResolvedLhsType), 'x22', False);
      Self.Emit(#9'mov x0, x22');
      Self.Emit(#9'mov x1, x19');
      EmitIntLiteral('x2', AAsgn.ResolvedLhsType.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Exit;
    end;
    EmitRecordBaseAddr('x0', AAsgn.Name, AAsgn.IsVarParam);
    EmitPushX0();
    EmitRecAddrToX0(AAsgn.Expr);
    Self.Emit(#9'mov x1, x0');
    EmitPopTo('x0');
    EmitIntLiteral('x2', AAsgn.ResolvedLhsType.RawSize());
    EmitCallSym('memcpy');
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and AAsgn.ResolvedLhsType.IsFloat() then
  begin
    if AAsgn.ResolvedLhsType.Kind = tySingle then
    begin
      if AAsgn.IsVarParam then
        NotYet('var Single parameter', AAsgn);
      Self.EmitExprToD0OrConvert(AAsgn.Expr);
      Self.Emit(#9'fcvt s0, d0');
      EmitSlotAddr('x9', AAsgn.Name);
      Self.Emit(#9'str s0, [x9]');
      Exit;
    end;
    Self.EmitExprToD0OrConvert(AAsgn.Expr);
    Self.Emit(#9'fmov x0, d0');
    if IsCaptured(AAsgn.Name) then
    begin
      EmitLoadSlot('x9', '_cap_' + AAsgn.Name);
      if AAsgn.IsVarParam then
        Self.Emit(#9'ldr x9, [x9]');
      Self.Emit(#9'str x0, [x9]');
    end
    else if AAsgn.IsVarParam then
    begin
      EmitLoadSlot('x9', AAsgn.Name);
      Self.Emit(#9'str x0, [x9]');
    end
    else
      EmitStoreSlot('x0', AAsgn.Name);
    Exit;
  end;
  if (AAsgn.ResolvedLhsType <> nil) and
     not IsIntFam(AAsgn.ResolvedLhsType) and
     not (AAsgn.ResolvedLhsType.Kind in [tyBoolean, tyMetaClass,
                                         tyPointer, tyPChar, tySet,
                                         tyProcedural]) then
    NotYet('assignment to non-integer variable', AAsgn);
  Self.EmitExprToX0(AAsgn.Expr);
  { Wrap the value to the target's own width and signedness before it lands.
    A frame slot / scalar global is 8 bytes and read back 64-bit wide, so an
    unnarrowed `B := B + 200` (B: Byte = 100) stored 300 and every later
    read saw 300, not 44 -- silently.  A width-exact store (var param, env
    field) truncates in memory anyway; narrowing first is harmless there. }
  EmitNarrowX0(AAsgn.ResolvedLhsType);
  if IsCaptured(AAsgn.Name) then
  begin
    { captured scalar (leg 17): '_cap_' holds &<Name> — store through it.
      A captured var-param needs a further deref to the caller's storage. }
    EmitPushX0();
    EmitLoadSlot('x9', '_cap_' + AAsgn.Name);
    if AAsgn.IsVarParam then
      Self.Emit(#9'ldr x9, [x9]');
    EmitPopTo('x0');
    if AAsgn.IsVarParam or IsEnvCaptured(AAsgn.Name) then
      { through to the CALLER's storage, or into a packed env field —
        store its exact width }
      EmitStoreByWidth('x0', 'x9', AAsgn.ResolvedLhsType)
    else
      { '_cap_' points at our own 8-byte frame slot, which is read back
        64-bit wide, so the full-width store is the correct one here. }
      Self.Emit(#9'str x0, [x9]');
  end
  else if AAsgn.IsVarParam then
  begin
    EmitLoadSlot('x9', AAsgn.Name);
    { A var/out param's slot holds the CALLER's ADDRESS, and the caller's
      storage is exactly as wide as the declared type — NOT the 8-byte frame
      slot a local gets.  The unconditional `str x0` here wrote 8 bytes for a
      4-byte Integer and silently clobbered the next 4 bytes of whatever the
      caller had bound: for `LookupReg(RegName, Result.Base, ...)` in the x86
      assembler that zeroed the ADJACENT Result.Index field, turning its -1
      ("no index register") sentinel into 0 (= rax).  Every bare memory operand
      then assembled as a SIB form indexed by rax — `movq %rcx, (%rax)` came out
      48 89 0C 00 = [rax+rax] instead of 48 89 08
      (BUG-20260726-arm64-varparam-store-width). }
    EmitStoreByWidth('x0', 'x9', AAsgn.ResolvedLhsType);
  end
  else
    EmitStoreSlot('x0', AAsgn.Name);
end;

procedure TArm64Backend.EmitProcCallStmt(ACall: TProcCall);
var
  I: Integer;
  Arg: TASTExpr;
  Tmp: string;
  IncLVal: TAddrOfExpr;
begin
  if ACall.IsProcFieldCall then
  begin
    { Handler(args); inside a method, Handler a procedural-typed field of
      Self (BUG-20260922) }
    EmitProcFieldCall('', nil, False, True, nil, ACall.ProcFieldInfo,
      ACall.Args, ACall);
    if ACall.ProcFieldInfo.TypeDesc is TProceduralTypeDesc then
      EmitDiscardedProcResult(TProceduralTypeDesc(ACall.ProcFieldInfo.TypeDesc));
    Exit;
  end;
  if SameText(ACall.Name, 'WriteLn') then
  begin
    EmitWrite(ACall, True);
    Exit;
  end;
  if SameText(ACall.Name, 'Write') then
  begin
    EmitWrite(ACall, False);
    Exit;
  end;
  if SameText(ACall.Name, 'SetLength') and (ACall.Args.Count = 2) and
     (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
     TASTExpr(ACall.Args.Items[0]).ResolvedType.IsString() and
     (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) and
     (not TIdentExpr(TASTExpr(ACall.Args.Items[0])).IsImplicitSelf) and
     (TIdentExpr(TASTExpr(ACall.Args.Items[0])).ParamMode in
       [pmNone, pmVar]) then
  begin
    { SetLength(S, N): S := _StringSetLength(S, N).  The result comes back
      rc=0 (StrAlloc allocates a fresh unowned buffer), so it must be AddRef'd
      before it lands in the slot — otherwise the local's scope-exit release
      drives 0 -> -1 = immortal/leak.  The old value is released.  Mirrors
      x86-64 (:14907) and QBE (:11368); works through the slot ADDRESS so a
      var/out param (slot = caller var-address, one extra deref) is handled by
      the same path (leg 34). }
    { Save x19 BEFORE pushing N.  It used to be saved after, so the save sat
      on top of N and `EmitPopTo('x1')` below popped the SAVED X19 as the
      length — a pointer-sized garbage length.  _StringSetLength then asked
      StrAlloc for an absurd size, the allocator's mmap failed, and SetLength
      returned nil: the macOS arm64 crash writing byte 0 of a nil buffer in
      TStringBuilder.ToString (2026-07-23).  It looked like an allocator fault
      but the allocator was simply handed a preposterous request. }
    Self.Emit(#9'str x19, [sp, #-16]!');
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
    EmitPushX0();                                { [N] }
    { x19 (callee-saved) = the address that holds the string pointer — survives
      the three RTL calls below. }
    EmitSlotAddr('x19', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
    if TIdentExpr(TASTExpr(ACall.Args.Items[0])).ParamMode <> pmNone then
      { var/out param: the slot holds the caller variable's address. }
      Self.Emit(#9'ldr x19, [x19]');
    Self.Emit(#9'ldr x0, [x19]');                { old string pointer }
    EmitPopTo('x1');                             { N }
    EmitCallSym('_StringSetLength');          { x0 = new (rc=0) }
    EmitPushX0();                                { [new] }
    EmitCallSym('_StringAddRef');             { new +1 (x0 already = new) }
    Self.Emit(#9'ldr x0, [x19]');                { old string pointer }
    EmitCallSym('_StringRelease');            { old -1 }
    EmitPopTo('x0');                             { new }
    Self.Emit(#9'str x0, [x19]');                { store new through the address }
    Self.Emit(#9'ldr x19, [sp], #16');           { restore x19 }
    Exit;
  end;
  if SameText(ACall.Name, 'SetLength') and (ACall.Args.Count = 2) and
     (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
     (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind = tyDynArray) then
  begin
    { arr := _DynArraySetLength(arr, n, elemsize) }
    if TASTExpr(ACall.Args.Items[0]) is TFieldAccessExpr then
    begin
      { dyn-array FIELD of an explicit record/class (Rec.Field / Result.Cands):
        work through the field's address, exactly like the implicit-Self arm
        but sourcing the address from EmitRecFieldAddrToX0 (which applies the
        field offset).  _DynArraySetLength frees the old block and returns a
        fresh rc=1 block, so the new pointer is just stored back — no ARC.

        EmitRecFieldAddrToX0 resolves every lvalue shape here: a var-param
        record field (its var-param arm derefs the slot -- leg 27), an
        implicit-Self intermediate (SetLength(FRec.Arr, N): it steps across
        ImplicitBaseInfo), and a subscripted array field
        (SetLength(R.Matrix[I], N): IsArrayAccess routes to EmitFieldElemAddr,
        so the ELEMENT slot is resized, not the outer array). }
      if (TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])).PropIndexExpr <> nil)
         and not TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])).IsArrayAccess then
        NotYet('SetLength on this field-lvalue form', ACall);
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
      EmitPushX0();                                       { [N] }
      EmitRecFieldAddrToX0(TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])));
      EmitPushX0();                                       { [N][addr] }
      Self.Emit(#9'ldr x0, [x0]');                        { old array }
      Self.Emit(#9'ldr x1, [sp, #16]');                   { N }
      EmitIntLiteral('x2', TDynArrayTypeDesc(
        TASTExpr(ACall.Args.Items[0]).ResolvedType).ElementType.RawSize());
      EmitCallSym('_DynArraySetLength');
      Self.Emit(#9'ldr x9, [sp]');                        { addr }
      Self.Emit(#9'str x0, [x9]');
      Self.Emit(#9'add sp, sp, #32');
      Exit;
    end;
    { plain ident lvalue }
    if not (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) then
      NotYet('SetLength on this lvalue form', ACall);
    if (TIdentExpr(TASTExpr(ACall.Args.Items[0])).ParamMode = pmVar) or
       IsCaptured(TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name) then
    begin
      { A var parameter's slot holds the caller variable's ADDRESS, and a
        captured variable's '_cap_' slot holds its storage address (its own
        promoted slot is dead) -- resize through that address. }
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
      EmitPushX0();                                       { [N] }
      if IsCaptured(TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name) then
      begin
        EmitLoadSlot('x0', '_cap_' + TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
        if TIdentExpr(TASTExpr(ACall.Args.Items[0])).ParamMode = pmVar then
          Self.Emit(#9'ldr x0, [x0]');
      end
      else
        EmitLoadSlot('x0', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
      EmitPushX0();                                       { [N][addr] }
      Self.Emit(#9'ldr x0, [x0]');                        { old array }
      Self.Emit(#9'ldr x1, [sp, #16]');                   { N }
      EmitIntLiteral('x2', TDynArrayTypeDesc(
        TASTExpr(ACall.Args.Items[0]).ResolvedType).ElementType.RawSize());
      EmitCallSym('_DynArraySetLength');
      Self.Emit(#9'ldr x9, [sp]');                        { addr }
      Self.Emit(#9'str x0, [x9]');
      Self.Emit(#9'add sp, sp, #32');
      Exit;
    end;
    if TIdentExpr(TASTExpr(ACall.Args.Items[0])).IsImplicitSelf and
       (TIdentExpr(TASTExpr(ACall.Args.Items[0])).ImplicitFieldInfo
          <> nil) then
    begin
      { dyn-array FIELD of Self: work through the field's address }
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
      EmitPushX0();                                       { [N] }
      EmitLoadSlot('x0', 'Self');
      if TFieldInfo(TIdentExpr(TASTExpr(ACall.Args.Items[0]))
           .ImplicitFieldInfo).Offset <> 0 then
        EmitAddSubImm('add', 'x0', 'x0',
          TFieldInfo(TIdentExpr(TASTExpr(ACall.Args.Items[0]))
            .ImplicitFieldInfo).Offset);
      EmitPushX0();                                       { [N][addr] }
      Self.Emit(#9'ldr x0, [x0]');                        { old array }
      Self.Emit(#9'ldr x1, [sp, #16]');                   { N }
      EmitIntLiteral('x2', TDynArrayTypeDesc(
        TASTExpr(ACall.Args.Items[0]).ResolvedType).ElementType.RawSize());
      EmitCallSym('_DynArraySetLength');
      Self.Emit(#9'ldr x9, [sp]');                        { addr }
      Self.Emit(#9'str x0, [x9]');
      Self.Emit(#9'add sp, sp, #32');
      Exit;
    end;
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
    EmitPushX0();
    EmitLoadSlot('x0', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
    EmitPopTo('x1');
    EmitIntLiteral('x2', TDynArrayTypeDesc(
      TASTExpr(ACall.Args.Items[0]).ResolvedType).ElementType.RawSize());
    EmitCallSym('_DynArraySetLength');
    EmitStoreSlot('x0',
      TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
    Exit;
  end;
  if SameText(ACall.Name, 'FreeMem') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 1) then
  begin
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]));
    EmitCallSym('_BlaiseFreeMem');
    Exit;
  end;
  if SameText(ACall.Name, 'Halt') and (ACall.ResolvedDecl = nil) then
  begin
    if ACall.Args.Count = 1 then
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]))
    else
      Self.Emit(#9'movz x0, #0');
    EmitCallSym('exit');
    Exit;
  end;
  if SameText(ACall.Name, 'Sleep') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 1) then
  begin
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]));
    EmitCallSym('_Sleep');
    Exit;
  end;
  if SameText(ACall.Name, 'ZeroMem') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 2) then
  begin
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]));
    EmitPushX0();
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
    Self.Emit(#9'mov x2, x0');
    Self.Emit(#9'movz x1, #0');
    EmitPopTo('x0');
    EmitCallSym('memset');
    Exit;
  end;
  if SameText(ACall.Name, 'RemoveDir') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 1) then
  begin
    EmitBuiltinStrCall1(TASTExpr(ACall.Args.Items[0]), '_RemoveDir');
    Exit;
  end;
  if SameText(ACall.Name, 'ForceDirectories') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 1) then
  begin
    { statement-context ForceDirectories (return value discarded) — the
      expression path is already handled in EmitExprToX0.  Mirrors x86-64. }
    EmitBuiltinStrCall1(TASTExpr(ACall.Args.Items[0]), '_ForceDirectories');
    Exit;
  end;
  if SameText(ACall.Name, 'AppendFile') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 2) then
  begin
    EmitBuiltinStrCall2(TASTExpr(ACall.Args.Items[0]),
      TASTExpr(ACall.Args.Items[1]), '_AppendFile');
    Exit;
  end;
  if SameText(ACall.Name, 'Delete') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 3) and
     (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) then
  begin
    { Delete(S, I, N): _StringDelete returns the new string — retain it,
      release the ident's old value, store back (x86 parity) }
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]));
    EmitPushX0();
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
    EmitPushX0();
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[2]));
    Self.Emit(#9'mov x2, x0');
    EmitPopTo('x1');
    EmitPopTo('x0');
    EmitCallSym('_StringDelete');
    EmitPushX0();
    EmitCallSym('_StringAddRef');
    EmitLoadSlot('x0', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
    EmitCallSym('_StringRelease');
    EmitPopTo('x0');
    EmitStoreSlot('x0', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
    Exit;
  end;
  if SameText(ACall.Name, 'DeleteFile') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 1) then
  begin
    EmitBuiltinStrCall1(TASTExpr(ACall.Args.Items[0]), '_DeleteFile');
    Exit;
  end;
  if SameText(ACall.Name, 'WriteFile') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 2) then
  begin
    EmitBuiltinStrCall2(TASTExpr(ACall.Args.Items[0]),
      TASTExpr(ACall.Args.Items[1]), '_WriteFile');
    Exit;
  end;
  { process-control family (statement context): SetExe/AddArg take (handle,
    string) — the string arg may be an owned transient, so route both slots
    through EmitBuiltinStrCall2; Execute/WaitOnExit/Free take the handle
    pointer only }
  if SameText(ACall.Name, 'ProcessSetExe') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 2) then
  begin
    EmitBuiltinStrCall2(TASTExpr(ACall.Args.Items[0]),
      TASTExpr(ACall.Args.Items[1]), '_ProcessSetExe');
    Exit;
  end;
  if SameText(ACall.Name, 'ProcessAddArg') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 2) then
  begin
    EmitBuiltinStrCall2(TASTExpr(ACall.Args.Items[0]),
      TASTExpr(ACall.Args.Items[1]), '_ProcessAddArg');
    Exit;
  end;
  if SameText(ACall.Name, 'ProcessExecute') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 1) then
  begin
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]));
    EmitCallSym('_ProcessExecute');
    Exit;
  end;
  if SameText(ACall.Name, 'ProcessWaitOnExit') and
     (ACall.ResolvedDecl = nil) and (ACall.Args.Count = 1) then
  begin
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]));
    EmitCallSym('_ProcessWaitOnExit');
    Exit;
  end;
  if SameText(ACall.Name, 'ProcessFree') and (ACall.ResolvedDecl = nil) and
     (ACall.Args.Count = 1) then
  begin
    Self.EmitExprToX0(TASTExpr(ACall.Args.Items[0]));
    EmitCallSym('_ProcessFree');
    Exit;
  end;
  if (SameText(ACall.Name, 'Include') or SameText(ACall.Name, 'Exclude')) and
     (ACall.ResolvedDecl = nil) and (ACall.Args.Count = 2) and
     (TASTExpr(ACall.Args.Items[0]).ResolvedType is TSetTypeDesc) then
  begin
    EmitSetIncludeExclude(ACall, SameText(ACall.Name, 'Include'));
    Exit;
  end;
  if (SameText(ACall.Name, 'Inc') or SameText(ACall.Name, 'Dec')) and
     (ACall.ResolvedDecl = nil) and
     ((ACall.Args.Count = 1) or (ACall.Args.Count = 2)) and
     (TASTExpr(ACall.Args.Items[0]) is TFieldAccessExpr) and
     (TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])).Base is TDerefExpr) and
     (TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])).FieldInfo <> nil) then
  begin
    { Inc/Dec(P^.Field[, N]): field address, then width-keyed
      load-adjust-store }
    if ACall.Args.Count = 2 then
    begin
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
      EmitPushX0();
    end;
    Self.EmitExprToX0(
      TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])).Base);
    if TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])).FieldInfo.Offset
       <> 0 then
      Self.Emit(Format(#9'add x0, x0, #%d',
        [TFieldAccessExpr(TASTExpr(ACall.Args.Items[0]))
           .FieldInfo.Offset]));
    Self.Emit(#9'mov x9, x0');
    if ACall.Args.Count = 2 then
      EmitPopTo('x2')
    else
      Self.Emit(#9'movz x2, #1');
    EmitElemLoad(
      TFieldAccessExpr(TASTExpr(ACall.Args.Items[0])).FieldInfo.TypeDesc);
    if SameText(ACall.Name, 'Inc') then
      Self.Emit(#9'add x0, x0, x2')
    else
      Self.Emit(#9'sub x0, x0, x2');
    case TFieldAccessExpr(TASTExpr(ACall.Args.Items[0]))
           .FieldInfo.TypeDesc.RawSize() of
      1: Self.Emit(#9'strb w0, [x9]');
      2: Self.Emit(#9'strh w0, [x9]');
      4: Self.Emit(#9'str w0, [x9]');
    else
      Self.Emit(#9'str x0, [x9]');
    end;
    Exit;
  end;
  if (SameText(ACall.Name, 'Inc') or SameText(ACall.Name, 'Dec')) and
     (ACall.ResolvedDecl = nil) and
     ((ACall.Args.Count = 1) or (ACall.Args.Count = 2)) and
     (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) and
     TIdentExpr(TASTExpr(ACall.Args.Items[0])).IsImplicitSelf and
     (TIdentExpr(TASTExpr(ACall.Args.Items[0])).ImplicitFieldInfo <> nil) then
  begin
    { Inc/Dec(FField[, N]) on an implicit-Self field: field address is
      Self + offset; width-keyed load-adjust-store there }
    if ACall.Args.Count = 2 then
    begin
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
      EmitPushX0();
    end;
    EmitLoadSlot('x0', 'Self');
    if TFieldInfo(TIdentExpr(TASTExpr(ACall.Args.Items[0]))
         .ImplicitFieldInfo).Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldInfo(TIdentExpr(TASTExpr(ACall.Args.Items[0]))
          .ImplicitFieldInfo).Offset);
    Self.Emit(#9'mov x9, x0');
    if ACall.Args.Count = 2 then
      EmitPopTo('x2')
    else
      Self.Emit(#9'movz x2, #1');
    EmitElemLoad(TFieldInfo(TIdentExpr(TASTExpr(ACall.Args.Items[0]))
      .ImplicitFieldInfo).TypeDesc);
    if SameText(ACall.Name, 'Inc') then
      Self.Emit(#9'add x0, x0, x2')
    else
      Self.Emit(#9'sub x0, x0, x2');
    case TFieldInfo(TIdentExpr(TASTExpr(ACall.Args.Items[0]))
           .ImplicitFieldInfo).TypeDesc.RawSize() of
      1: Self.Emit(#9'strb w0, [x9]');
      2: Self.Emit(#9'strh w0, [x9]');
      4: Self.Emit(#9'str w0, [x9]');
    else
      Self.Emit(#9'str x0, [x9]');
    end;
    Exit;
  end;
  if (SameText(ACall.Name, 'Inc') or SameText(ACall.Name, 'Dec')) and
     (ACall.ResolvedDecl = nil) and
     ((ACall.Args.Count = 1) or (ACall.Args.Count = 2)) and
     (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) then
  begin
    { Inc/Dec(X[, N]) on a plain ident lvalue: load, adjust, store.
      A var-param slot holds the caller's ADDRESS — deref both ways. }
    if ACall.Args.Count = 2 then
    begin
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]));
      Self.Emit(#9'mov x2, x0');
    end
    else
      Self.Emit(#9'movz x2, #1');
    if IsCaptured(TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name) then
    begin
      { captured variable: the promoted local's own slot is dead -- adjust
        the storage '_cap_' points at (env field or outer frame slot) }
      Self.Emit(#9'str x2, [sp, #-16]!');
      EmitCapturedLoad(TIdentExpr(TASTExpr(ACall.Args.Items[0])));
      Self.Emit(#9'ldr x2, [sp], #16');
      if SameText(ACall.Name, 'Inc') then
        Self.Emit(#9'add x0, x0, x2')
      else
        Self.Emit(#9'sub x0, x0, x2');
      EmitLoadSlot('x9', '_cap_' + TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
      if TIdentExpr(TASTExpr(ACall.Args.Items[0])).ParamMode = pmVar then
        Self.Emit(#9'ldr x9, [x9]');
      if IsEnvCaptured(TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name) or
         (TIdentExpr(TASTExpr(ACall.Args.Items[0])).ParamMode = pmVar) then
        EmitStoreByWidth('x0', 'x9', TASTExpr(ACall.Args.Items[0]).ResolvedType)
      else
      begin
        { an outer 8-byte frame slot is read 64-bit wide: wrap, store full }
        EmitNarrowX0(TASTExpr(ACall.Args.Items[0]).ResolvedType);
        Self.Emit(#9'str x0, [x9]');
      end;
      Exit;
    end;
    if TIdentExpr(TASTExpr(ACall.Args.Items[0])).ParamMode = pmVar then
    begin
      { The var target may be a 1/2/4-byte field or slot: load and store at
        the DECLARED width (an 8-byte str clobbered the bytes after a Byte or
        Integer target), exactly as the field arms above do. }
      EmitLoadSlot('x9', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
      Self.Emit(#9'mov x0, x9');
      EmitElemLoad(TASTExpr(ACall.Args.Items[0]).ResolvedType);
      if SameText(ACall.Name, 'Inc') then
        Self.Emit(#9'add x0, x0, x2')
      else
        Self.Emit(#9'sub x0, x0, x2');
      case TASTExpr(ACall.Args.Items[0]).ResolvedType.RawSize() of
        1: Self.Emit(#9'strb w0, [x9]');
        2: Self.Emit(#9'strh w0, [x9]');
        4: Self.Emit(#9'str w0, [x9]');
      else
        Self.Emit(#9'str x0, [x9]');
      end;
      Exit;
    end;
    EmitLoadSlot('x0', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
    if SameText(ACall.Name, 'Inc') then
      Self.Emit(#9'add x0, x0, x2')
    else
      Self.Emit(#9'sub x0, x0, x2');
    { The slot is 8 bytes and read 64-bit wide, so the result must be wrapped
      to the variable's own width and signedness: Dec on a Byte holding 0
      left -1 in the slot instead of 255. }
    EmitNarrowX0(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    EmitStoreSlot('x0', TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name);
    Exit;
  end;
  { The semantic pass's IsImplicitSelfMethod is authoritative: an empty
    OwnerTypeName must never route an implicit-Self call to the plain-routine
    arm, which passes no Self. }
  if (ACall.ResolvedDecl <> nil) and (ACall.ResolvedDecl is TMethodDecl) and
     (TMethodDecl(ACall.ResolvedDecl).OwnerTypeName = '') and
     not ACall.IsImplicitSelfMethod then
  begin
    if IsMethodPtrType(TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType) then
    begin
      { a DISCARDED closure result still needs its x8 buffer, and the Env
        reference the callee handed over must be dropped }
      Tmp := EmitClosureResultCall(TMethodDecl(ACall.ResolvedDecl),
        ACall.Name, ACall.Args);
      if TProceduralTypeDesc(
           TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType).IsReference then
      begin
        EmitSlotAddr('x9', Tmp);
        Self.Emit(#9'ldr x0, [x9, #8]');
        EmitCallSym('_ClassRelease');
      end;
      Exit;
    end;
    EmitCall(TMethodDecl(ACall.ResolvedDecl), ACall.Name, ACall.Args);
    { a DISCARDED owned result must be disposed (user routine results are
      rc=1 — one release) }
    if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType <> nil then
    begin
      if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType.IsString() then
        EmitCallSym('_StringRelease')
      else if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType.Kind =
              tyClass then
        EmitCallSym('_ClassRelease')
      else if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType.Kind =
              tyDynArray then
        EmitCallSym('_DynArrayRelease');
    end;
    Exit;
  end;
  if ACall.IsImplicitSelfMethod and (ACall.ResolvedDecl <> nil) then
  begin
    { bare method call on Self as a statement: Advance(); }
    if (TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType <> nil) and
       IsAggregateReturn(TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType) then
      NotYet('discarded aggregate-returning implicit-Self call', ACall);
    EmitLoadSlot('x0', 'Self');
    EmitMethodCallCommon(TMethodDecl(ACall.ResolvedDecl), ACall.Name,
      ACall.Args);
    { a discarded owned return must still be released }
    if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType <> nil then
    begin
      if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType.Kind =
           tyString then
        EmitCallSym('_StringRelease')
      else if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType.Kind =
              tyClass then
        EmitCallSym('_ClassRelease')
      else if TMethodDecl(ACall.ResolvedDecl).ResolvedReturnType.Kind =
              tyDynArray then
        EmitCallSym('_DynArrayRelease');
    end;
    Exit;
  end;
  if ACall.IsIndirectCall and
     IsMethodPtrType(TTypeDesc(ACall.ResolvedProcType)) then
  begin
    { statement-position call through a closure / method-pointer variable (a
      16-byte fat value): route to EmitFatPtrCall with the fat value's ADDRESS.
      The result (if any) is discarded — EmitFatPtrCall leaves it in x0/d0
      harmlessly.  Mirrors the expression-position fat-callee arm. }
    EmitSlotAddr('x9', ACall.Name);
    EmitFatPtrCall('x9',
      TProceduralTypeDesc(ACall.ResolvedProcType), ACall.Args);
    Exit;
  end;
  if ACall.IsIndirectCall and (ACall.Args.Count <= 8) then
  begin
    { call through a plain proc-pointer variable: int-class args in
      x0..x(n-1), function pointer from the variable's slot, blr }
    GuardNoOpenArrayParam(TProceduralTypeDesc(ACall.ResolvedProcType), ACall);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      if not (IsIntFam(Arg.ResolvedType) or (Arg is TIntLiteral) or
              (Arg is TNilLiteral) or
              ((Arg.ResolvedType <> nil) and
               (Arg.ResolvedType.Kind in [tyPChar, tyPointer,
                                          tyClass, tyString, tyDynArray,
                                          tyMetaClass]))) then
        NotYet('indirect-call argument of this type', Arg);
      { an owned transient would need a park slot (like EmitFatPtrCall) — keep
        the hole honest rather than leak it }
      if ArcExprOwnsRef(Arg) then
        NotYet('owned transient argument in an indirect call', Arg);
      Self.EmitExprToX0(Arg);
      EmitPushX0();
    end;
    for I := ACall.Args.Count - 1 downto 0 do
      EmitPopTo('x' + IntToStr(I));
    EmitLoadSlot('x9', ACall.Name);
    Self.Emit(#9'blr x9');
    Exit;
  end;
  if (SameText(ACall.Name, 'Inc') or SameText(ACall.Name, 'Dec')) and
     (ACall.ResolvedDecl = nil) and
     ((ACall.Args.Count = 1) or (ACall.Args.Count = 2)) and
     (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
     (IsIntFam(TASTExpr(ACall.Args.Items[0]).ResolvedType) or
      (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind = tyPChar)) then
  begin
    { Inc/Dec on any other lvalue -- a record field, an array element, a
      pointer dereference: address it through a transient @-wrapper (as
      Include does) and load / adjust / store at the target's DECLARED
      width, so it wraps like the type and leaves its neighbours alone.  A
      typed pointer (which steps by its element size) is not taken here. }
    if ACall.Args.Count = 2 then
      Self.EmitExprToX0(TASTExpr(ACall.Args.Items[1]))
    else
      Self.Emit(#9'movz x0, #1');
    EmitPushX0();                                      { [step] }
    IncLVal := TAddrOfExpr.Create();
    try
      IncLVal.Line := ACall.Line;
      IncLVal.Col := ACall.Col;
      IncLVal.Expr := TASTExpr(ACall.Args.Items[0]);
      Self.EmitExprToX0(IncLVal);                      { &target }
    finally
      IncLVal.Expr := nil;   { Args[0] is owned by the call node }
      IncLVal.Free();
    end;
    EmitPopTo('x2');                                   { step }
    Self.Emit(#9'mov x9, x0');
    EmitElemLoad(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    if SameText(ACall.Name, 'Inc') then
      Self.Emit(#9'add x0, x0, x2')
    else
      Self.Emit(#9'sub x0, x0, x2');
    EmitStoreByWidth('x0', 'x9', TASTExpr(ACall.Args.Items[0]).ResolvedType);
    Exit;
  end;
  NotYet('call to ''' + ACall.Name + '''', ACall);
end;

procedure TArm64Backend.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  I: Integer;
  Arg: TASTExpr;
  K: TTypeKind;
begin
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if Arg.ResolvedType <> nil then
      K := Arg.ResolvedType.Kind
    else
      K := tyInteger;
    if (K in [tyString, tyPChar]) or (Arg is TStringLiteral) then
    begin
      Self.EmitExprToX0(Arg);
      if (K = tyString) and ArcBuiltinStrArgOwnsRef(Arg) then
      begin
        { a transient is borrowed by _SysWriteStr — dispose it by shape
          after the write (rc=1 releases; rc=0 AddRef-then-Release) }
        EmitPushX0();
        Self.Emit(#9'mov x1, x0');
        Self.Emit(#9'movz w0, #1');
        EmitCallSym('_SysWriteStr');
        EmitPopTo('x0');
        EmitStrDisposeX0(Arg);
      end
      else
      begin
        Self.Emit(#9'mov x1, x0');
        Self.Emit(#9'movz w0, #1');           { fd = stdout }
        EmitCallSym('_SysWriteStr');
      end;
    end
    else if K in [tyDouble, tySingle] then
    begin
      Self.EmitExprToD0OrConvert(Arg);
      Self.Emit(#9'movz w0, #1');
      EmitCallSym('_SysWriteDouble');
    end
    else if K = tyBoolean then
    begin
      Self.EmitExprToX0(Arg);
      Self.Emit(#9'mov w1, w0');
      Self.Emit(#9'movz w0, #1');
      EmitCallSym('_SysWriteBool');
    end
    else if K = tyInt64 then
    begin
      Self.EmitExprToX0(Arg);
      Self.Emit(#9'mov x1, x0');
      Self.Emit(#9'movz w0, #1');
      EmitCallSym('_SysWriteInt64');
    end
    else if K = tyUInt64 then
    begin
      { unsigned writer: the Integer path would print a value with the high
        bit set as a negative number }
      Self.EmitExprToX0(Arg);
      Self.Emit(#9'mov x1, x0');
      Self.Emit(#9'movz w0, #1');
      EmitCallSym('_SysWriteUInt64');
    end
    else if IsIntFam(Arg.ResolvedType) or (Arg is TIntLiteral) then
    begin
      Self.EmitExprToX0(Arg);
      { Pass the full 64-bit value: EmitExprToX0 leaves a 32-bit Integer
        SIGN-extended in x0, so a negative reads correctly as N.  `mov w1, w0`
        would zero-extend the low 32 bits into x1, printing -1 as its unsigned
        value 4294967295 (macOS arm64, 2026-07-24).  Mirrors the tyInt64 arm and
        the IntToStr path, both of which pass x0 whole. }
      Self.Emit(#9'mov x1, x0');
      Self.Emit(#9'movz w0, #1');
      EmitCallSym('_SysWriteInt');
    end
    else
      NotYet('Write/WriteLn argument of this type', Arg);
  end;
  if ANewline then
  begin
    Self.Emit(#9'movz w0, #1');
    EmitCallSym('_SysWriteNewline');
  end;
end;

procedure TArm64Backend.EmitIf(AStmt: TIfStmt);
var
  ElseL, EndL: string;
begin
  ElseL := NewLabel('else');
  EndL  := NewLabel('endif');
  Self.EmitCondToX0Flushed(AStmt.Condition);
  Self.Emit(Format(#9'cbz x0, %s', [ElseL]));
  Self.EmitStmt(AStmt.ThenStmt);
  Self.Emit(Format(#9'b %s', [EndL]));
  Self.Emit(ElseL + ':');
  if AStmt.ElseStmt <> nil then
    Self.EmitStmt(AStmt.ElseStmt);
  Self.Emit(EndL + ':');
end;

procedure TArm64Backend.EmitWhile(AStmt: TWhileStmt);
var
  TopL, EndL: string;
begin
  TopL := NewLabel('while');
  EndL := NewLabel('wend');
  Self.Emit(TopL + ':');
  Self.EmitCondToX0Flushed(AStmt.Condition);   { flush per iteration (BUG-049) }
  Self.Emit(Format(#9'cbz x0, %s', [EndL]));
  { break/continue target this loop — without the push a break inside a
    while NESTED in a for would silently bind to the outer loop }
  FBreakLbls.Add(EndL);
  FLoopExcDepth.Add(IntToStr(FExcDepth));
  FContLbls.Add(TopL);
  Self.EmitStmt(AStmt.Body);
  FContLbls.Delete(FContLbls.Count - 1);
  FBreakLbls.Delete(FBreakLbls.Count - 1);
  FLoopExcDepth.Delete(FLoopExcDepth.Count - 1);
  Self.Emit(Format(#9'b %s', [TopL]));
  Self.Emit(EndL + ':');
end;

function TArm64Backend.NewExcFrameSlot: string;
begin
  { one static 512-byte, 16-aligned frame slot per emitted try — the body
    is buffered, so lazily growing the frame here is exact (BUG-045). }
  if (FFrameSize and 15) <> 0 then
    AddLocal('__excpad_' + IntToStr(FExcSlotN), 8);
  Result := '__excf_' + IntToStr(FExcSlotN);
  FExcSlotN := FExcSlotN + 1;
  if not FFrame.ContainsKey(Result) then
    AddLocal(Result, 512);
end;

procedure TArm64Backend.EmitExcPrologue(const AFrameSlot, AExcLbl,
  ATryLbl: string);
begin
  EmitSlotAddr('x0', AFrameSlot);
  EmitCallSym('_PushExcFrame');
  EmitSlotAddr('x0', AFrameSlot);
  EmitCallSym('_blaise_setjmp');
  Self.Emit(Format(#9'cbnz w0, %s', [AExcLbl]));
  Self.Emit(ATryLbl + ':');
end;

procedure TArm64Backend.EmitExcUnwindTo(ATargetDepth: Integer);
var
  I, J: Integer;
  FinBody: TCompoundStmt;
begin
  { non-local exit (Exit/Break/Continue) crossing try regions: pop each
    frame and run try/finally bodies inline on the way out }
  for I := FExcDepth downto ATargetDepth + 1 do
  begin
    EmitCallSym('_PopExcFrame');
    if I - 1 < FFinallyBodies.Count then
    begin
      FinBody := TCompoundStmt(FFinallyBodies.Items[I - 1]);
      if FinBody <> nil then
        for J := 0 to FinBody.Stmts.Count - 1 do
          EmitStmt(TASTStmt(FinBody.Stmts.Items[J]));
    end;
  end;
end;

procedure TArm64Backend.EmitTryFinally(AStmt: TTryFinallyStmt);
var
  I, FinForN: Integer;
  FrameSlot, ExcL, TryL, EndL: string;
begin
  FrameSlot := NewExcFrameSlot();
  ExcL := NewLabel('finexc');
  TryL := NewLabel('trybody');
  EndL := NewLabel('finend');
  EmitExcPrologue(FrameSlot, ExcL, TryL);
  FExcDepth := FExcDepth + 1;
  FFinallyBodies.Add(AStmt.FinallyBody);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitCallSym('_PopExcFrame');
  FExcDepth := FExcDepth - 1;
  FFinallyBodies.Delete(FFinallyBodies.Count - 1);
  { the finally body is emitted TWICE — normal path here, exception path
    below.  Both emissions of a for-loop inside the finally must consume
    the SAME hidden __for_end slot (registration allocated only one per
    for statement).  Save the for-slot counter before the normal-path
    finally and rewind to it before the exception-path finally, so the two
    emissions reuse the same slots (they are mutually exclusive at run
    time).  Without this the second emission runs off the end of the
    registered slots — an unregistered-slot store (BUG). }
  FinForN := FForN;
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  Self.Emit(Format(#9'b %s', [EndL]));
  { exception path: capture, pop, run the finally, re-raise.  Codegen-time
    depth bookkeeping balances independently per path. }
  FExcDepth := FExcDepth + 1;
  FFinallyBodies.Add(AStmt.FinallyBody);
  Self.Emit(ExcL + ':');
  EmitCallSym('_CurrentException');
  Self.Emit(#9'str x0, [sp, #-16]!');
  EmitCallSym('_PopExcFrame');
  FExcDepth := FExcDepth - 1;
  FFinallyBodies.Delete(FFinallyBodies.Count - 1);
  FForN := FinForN;   { reuse the normal-path finally's for-slot numbers }
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  Self.Emit(#9'ldr x0, [sp], #16');
  EmitCallSym('_Reraise');
  Self.Emit(EndL + ':');
end;

procedure TArm64Backend.EmitTryExcept(AStmt: TTryExceptStmt);
var
  I, J: Integer;
  H: TExceptHandlerClause;
  FrameSlot, ExcL, TryL, EndL, BodyL, NextL: string;
begin
  FrameSlot := NewExcFrameSlot();
  ExcL := NewLabel('exch');
  TryL := NewLabel('trybody');
  EndL := NewLabel('excend');
  EmitExcPrologue(FrameSlot, ExcL, TryL);
  FExcDepth := FExcDepth + 1;
  FFinallyBodies.Add(nil);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitCallSym('_PopExcFrame');
  FExcDepth := FExcDepth - 1;
  FFinallyBodies.Delete(FFinallyBodies.Count - 1);
  Self.Emit(Format(#9'b %s', [EndL]));
  Self.Emit(ExcL + ':');
  if AStmt.Handlers.Count > 0 then
  begin
    { capture while our frame is still the top, then pop }
    EmitCallSym('_CurrentException');
    Self.Emit(#9'str x0, [sp, #-16]!');
    EmitCallSym('_PopExcFrame');
    for I := 0 to AStmt.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(AStmt.Handlers.Items[I]);
      BodyL := NewLabel('hbody');
      NextL := NewLabel('hnext');
      Self.Emit(#9'ldr x0, [sp]');
      EmitTypeinfoAddr('x1', H.TypeName);
      EmitCallSym('_IsInstance');
      Self.Emit(Format(#9'cbz w0, %s', [NextL]));
      Self.Emit(BodyL + ':');
      if H.VarName <> '' then
      begin
        { bind: retain the exception (balances the scope-exit release of
          the handler var), release any prior binding, store }
        Self.Emit(#9'ldr x0, [sp]');
        EmitCallSym('_ClassAddRef');
        EmitLoadSlot('x0', H.VarName);
        EmitCallSym('_ClassRelease');
        Self.Emit(#9'ldr x0, [sp]');
        EmitStoreSlot('x0', H.VarName);
      end;
      for J := 0 to H.Body.Stmts.Count - 1 do
        EmitStmt(TASTStmt(H.Body.Stmts.Items[J]));
      { A handler with NO variable owns disposal: the exception is created rc=0
        and only borrowed, so without a handler-var slot it would be orphaned
        (BUG-20260720-exception-object-leak).  Balanced AddRef/Release
        (0->1->0) frees it + deregisters (the pointer is still at [sp]). }
      if H.VarName = '' then
      begin
        Self.Emit(#9'ldr x0, [sp]');
        EmitCallSym('_ClassAddRef');
        Self.Emit(#9'ldr x0, [sp]');
        EmitCallSym('_ClassRelease');
      end;
      Self.Emit(#9'add sp, sp, #16');
      Self.Emit(Format(#9'b %s', [EndL]));
      Self.Emit(NextL + ':');
    end;
    if AStmt.ElseBody <> nil then
    begin
      for J := 0 to AStmt.ElseBody.Stmts.Count - 1 do
        EmitStmt(TASTStmt(AStmt.ElseBody.Stmts.Items[J]));
      { else HANDLES without a variable — dispose (re-raise path below forwards
        the borrow and must NOT dispose). }
      Self.Emit(#9'ldr x0, [sp]');
      EmitCallSym('_ClassAddRef');
      Self.Emit(#9'ldr x0, [sp]');
      EmitCallSym('_ClassRelease');
      Self.Emit(#9'add sp, sp, #16');
      Self.Emit(Format(#9'b %s', [EndL]));
    end
    else
    begin
      Self.Emit(#9'ldr x0, [sp], #16');
      EmitCallSym('_Reraise');
    end;
  end
  else
  begin
    { bare except: catch-all body.  Capture the borrowed exception BEFORE the
      frame pop, dispose it after the body (BUG-20260720-exception-object-leak). }
    EmitCallSym('_CurrentException');
    Self.Emit(#9'str x0, [sp, #-16]!');
    EmitCallSym('_PopExcFrame');
    for I := 0 to AStmt.ExceptBody.Stmts.Count - 1 do
      EmitStmt(TASTStmt(AStmt.ExceptBody.Stmts.Items[I]));
    Self.Emit(#9'ldr x0, [sp]');
    EmitCallSym('_ClassAddRef');
    Self.Emit(#9'ldr x0, [sp]');
    EmitCallSym('_ClassRelease');
    Self.Emit(#9'add sp, sp, #16');
  end;
  Self.Emit(EndL + ':');
end;

procedure TArm64Backend.EmitStaticElemAssign(AStmt: TStaticSubscriptAssign);
var
  Elem: TTypeDesc;
begin
  if AStmt.PropWriteInfo <> nil then
  begin
    { Obj[I] := V through a `default` indexed property: a setter call }
    if TPropertyInfo(AStmt.PropWriteInfo).WriteMethod = '' then
      NotYet('default-property write without a setter', AStmt);
    EmitIndexedPropWrite(TPropertyInfo(AStmt.PropWriteInfo),
      AStmt.PropOwnerType, AStmt.PropAccessorVSlot, AStmt.IndexExpr,
      AStmt.ValueExpr, AStmt);
    Exit;
  end;
  { Arr[I] := V for a plain local/global static array.  The element
    ADDRESS is computed first and parked on the stack so the value
    expression (and any ARC release call) cannot invalidate it.
    A var-param STRING / PChar subscript write is handled by the tyString /
    tyPChar branches below (they load the slot and deref once more for a var
    param), so IsVarParam is only a blocker for the aggregate-array forms. }
  if ((AStmt.BaseExpr <> nil) and
      ((AStmt.ResolvedArrayType = nil) or
       not (AStmt.ResolvedArrayType.Kind in [tyStaticArray, tyDynArray]))) or
     (AStmt.IsVarParam and
      ((AStmt.ResolvedArrayType = nil) or
       not (AStmt.ResolvedArrayType.Kind in [tyString, tyPChar,
                                             tyDynArray, tyOpenArray]))) or
     (AStmt.IsImplicitSelf and ((AStmt.ImplicitFieldInfo = nil) or
       (AStmt.ResolvedArrayType = nil) or
       not (AStmt.ResolvedArrayType.Kind in [tyDynArray, tyStaticArray]))) then
    NotYet('subscript write on this array form', AStmt);
  if (AStmt.ResolvedArrayType <> nil) and
     (AStmt.ResolvedArrayType.Kind = tyString) then
  begin
    { S[I] := ch with copy-on-write.  x19 holds the ADDRESS of the slot that
      stores the string's data pointer — a local/global slot directly, or the
      caller's variable address for a var/out param.  _StringUnique returns a
      uniquely-owned writable pointer (releasing the old one when it copies);
      store it back so the slot keeps exactly one owned reference, then storeb
      into it.  Without the COW, writing a literal-backed string would hit
      read-only memory.  Mirrors x86-64 (:16340) and QBE (:17676). }
    { byte value -> parked }
    EmitByteRhsToX0(AStmt.ValueExpr);
    EmitPushX0();                                  { [sp] = byte value }
    Self.EmitExprToX0(AStmt.IndexExpr);
    EmitPushX0();                                  { [sp] = index }
    { preserve x19 (callee-saved) across the _StringUnique call }
    Self.Emit(#9'str x19, [sp, #-16]!');
    EmitSlotAddr('x19', AStmt.ArrayName);          { x19 = &slot }
    if AStmt.IsVarParam then
      { var/out param: the slot holds the caller variable's ADDRESS; the string
        pointer lives one deref further. }
      Self.Emit(#9'ldr x19, [x19]');
    Self.Emit(#9'ldr x0, [x19]');                  { old data pointer }
    EmitCallSym('_StringUnique');               { x0 = unique writable ptr }
    Self.Emit(#9'str x0, [x19]');                  { write back to slot }
    Self.Emit(#9'mov x9, x0');                     { x9 = unique base }
    Self.Emit(#9'ldr x19, [sp], #16');             { restore x19 }
    EmitPopTo('x1');                               { index }
    Self.Emit(#9'add x9, x9, x1');
    EmitPopTo('x0');                               { byte value }
    Self.Emit(#9'strb w0, [x9]');
    Exit;
  end;
  if (AStmt.ResolvedArrayType <> nil) and
     (AStmt.ResolvedArrayType.Kind = tyPChar) then
  begin
    { P[I] := ch on a PChar: one byte at value+index.  A #0/char literal
      value is a length-1 string literal in the AST — store its byte. }
    Self.EmitExprToX0(AStmt.IndexExpr);
    EmitPushX0();
    EmitLoadSlot('x0', AStmt.ArrayName);
    EmitPopTo('x1');
    Self.Emit(#9'add x9, x0, x1');
    if (AStmt.ValueExpr is TStringLiteral) then
    begin
      if Length(TStringLiteral(AStmt.ValueExpr).Value) = 0 then
        Self.Emit(#9'movz x0, #0')
      else
        EmitIntLiteral('x0',
          OrdAt(TStringLiteral(AStmt.ValueExpr).Value, 0));
    end
    else
    begin
      { park the address — the value eval clobbers x9.  EmitByteRhsToX0 keeps
        Chr(N) as the raw ordinal; a _Chr allocation here would strb the low
        byte of the returned pointer. }
      Self.Emit(#9'str x9, [sp, #-16]!');
      EmitByteRhsToX0(AStmt.ValueExpr);
      Self.Emit(#9'ldr x9, [sp], #16');
    end;
    Self.Emit(#9'strb w0, [x9]');
    Exit;
  end;
  if (AStmt.ResolvedArrayType = nil) or
     not (AStmt.ResolvedArrayType.Kind in [tyStaticArray, tyDynArray,
                                           tyOpenArray]) then
    NotYet('subscript write on this base type', AStmt);
  if AStmt.ResolvedArrayType.Kind = tyDynArray then
    Elem := TDynArrayTypeDesc(AStmt.ResolvedArrayType).ElementType
  else if AStmt.ResolvedArrayType.Kind = tyOpenArray then
    Elem := TOpenArrayTypeDesc(AStmt.ResolvedArrayType).ElementType
  else
    Elem := TStaticArrayTypeDesc(AStmt.ResolvedArrayType).ElementType;
  Self.EmitExprToX0(AStmt.IndexExpr);
  { static array with a non-zero LowBound: rebase the index to 0 before
    scaling (BUG-050) — a[5] of array[5..9] is element 0.  Dyn arrays are
    always 0-based.  A negative low bound rebases via `add` (subtracting a
    negative) to avoid an invalid `sub #-N` immediate. }
  if (AStmt.ResolvedArrayType.Kind = tyStaticArray) and
     (TStaticArrayTypeDesc(AStmt.ResolvedArrayType).LowBound <> 0) then
  begin
    if TStaticArrayTypeDesc(AStmt.ResolvedArrayType).LowBound > 0 then
      EmitAddSubImm('sub', 'x0', 'x0',
        TStaticArrayTypeDesc(AStmt.ResolvedArrayType).LowBound)
    else
      EmitAddSubImm('add', 'x0', 'x0',
        -TStaticArrayTypeDesc(AStmt.ResolvedArrayType).LowBound);
  end;
  EmitPushX0();
  if AStmt.BaseExpr <> nil then
  begin
    { a chained / multi-dimensional write G[I][J] := V (and the desugared
      G[I, J]): BaseExpr yields the inner array -- its storage address for a
      static array, its data pointer (the value) for a dyn array }
    if AStmt.ResolvedArrayType.Kind = tyStaticArray then
      EmitArrayStorageAddr(AStmt.BaseExpr)
    else
    begin
      if ArcExprOwnsRef(AStmt.BaseExpr) then
        NotYet('subscript write through an owned transient base', AStmt);
      Self.EmitExprToX0(AStmt.BaseExpr);
    end;
  end
  else if AStmt.IsImplicitSelf then
  begin
    EmitLoadSlot('x0', 'Self');
    if AStmt.ResolvedArrayType.Kind = tyDynArray then
      { dyn-array FIELD of Self: the field slot holds a data POINTER — deref it }
      Self.Emit(Format(#9'ldr x0, [x0, #%d]',
        [TFieldInfo(AStmt.ImplicitFieldInfo).Offset]))
    else if TFieldInfo(AStmt.ImplicitFieldInfo).Offset <> 0 then
      { static-array FIELD of Self: the inline array storage IS at Self+offset
        — the base is that ADDRESS, no deref (leg 16) }
      EmitAddSubImm('add', 'x0', 'x0',
        TFieldInfo(AStmt.ImplicitFieldInfo).Offset);
  end
  else if AStmt.ResolvedArrayType.Kind = tyOpenArray then
  begin
    { an open-array parameter -- var, const or value alike -- arrives as the
      caller's element-0 pointer (the (data, high) pair ABI, never an extra
      level of indirection), so the slot value IS the base }
    if IsCaptured(AStmt.ArrayName) then
    begin
      EmitLoadSlot('x0', '_cap_' + AStmt.ArrayName);
      Self.Emit(#9'ldr x0, [x0]');
    end
    else
      EmitLoadSlot('x0', AStmt.ArrayName);
  end
  else if IsCaptured(AStmt.ArrayName) then
  begin
    { captured: '_cap_' holds the storage address (a var param's storage
      holds the caller's address, one more deref).  A dyn array's data
      pointer is the value stored there; a static array IS that storage. }
    EmitLoadSlot('x0', '_cap_' + AStmt.ArrayName);
    if AStmt.IsVarParam then
      Self.Emit(#9'ldr x0, [x0]');
    if AStmt.ResolvedArrayType.Kind = tyDynArray then
      Self.Emit(#9'ldr x0, [x0]');
  end
  else if AStmt.ResolvedArrayType.Kind = tyDynArray then
  begin
    EmitLoadSlot('x0', AStmt.ArrayName);  { data pointer value }
    { a var dyn-array parameter's slot holds the caller variable's address }
    if AStmt.IsVarParam then
      Self.Emit(#9'ldr x0, [x0]');
  end
  else
    EmitSlotAddr('x0', AStmt.ArrayName);
  EmitPopTo('x1');
  EmitIntLiteral('x2', Elem.RawSize());
  Self.Emit(#9'mul x1, x1, x2');
  Self.Emit(#9'add x0, x0, x1');
  EmitPushX0();                                { [elemaddr] }
  if Elem.Kind = tyInterface then
  begin
    { the element IS an (obj, itab) pair: the shared pair store retains the
      new obj, releases the old one and writes both halves }
    EmitIntfStoreStacked(0, AStmt.ValueExpr, Elem);
    Exit;
  end;
  if Elem.IsString() or (Elem.Kind = tyClass) then
  begin
    Self.EmitExprToX0(AStmt.ValueExpr);
    if (Elem.IsString() and not ArcExprOwnsRef(AStmt.ValueExpr)) or
       ((Elem.Kind = tyClass) and not ArcExprOwnsRef(AStmt.ValueExpr)) then
    begin
      EmitPushX0();
      if Elem.IsString() then
        EmitCallSym('_StringAddRef')
      else
        EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();                              { [addr][val] }
    Self.Emit(#9'ldr x9, [sp, #16]');
    Self.Emit(#9'ldr x0, [x9]');
    if Elem.IsString() then
      EmitCallSym('_StringRelease')
    else
      EmitCallSym('_ClassRelease');
    Self.Emit(#9'ldr x9, [sp, #16]');
    EmitPopTo('x0');
    Self.Emit(#9'str x0, [x9]');
    Self.Emit(#9'add sp, sp, #16');
    Exit;
  end;
  if Elem.Kind = tyDouble then
  begin
    Self.EmitExprToD0OrConvert(AStmt.ValueExpr);
    Self.Emit(#9'fmov x0, d0');
  end
  else if Elem.Kind = tySingle then
  begin
    Self.EmitExprToD0OrConvert(AStmt.ValueExpr);
    Self.Emit(#9'fcvt s0, d0');
    Self.Emit(#9'ldr x9, [sp], #16');
    Self.Emit(#9'str s0, [x9]');
    Exit;
  end
  else if Elem.Kind = tyRecord then
  begin
    { record element: memcpy from the source record's address — managed
      fields follow the retain-source-then-release-dest discipline.
      A record-returning CALL source has no lvalue: materialise it into the
      __rret scratch first (its +1 field refs transfer), release the dest
      element's old managed refs, then memcpy __rret -> element (no source
      retain — the transfer is exact).  Mirrors the field-store leg. }
    if IsRecordCallArg(AStmt.ValueExpr) then
    begin
      EmitRecCallToRret(AStmt.ValueExpr);   { x0 = result addr; +1 transfers }
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      Self.Emit(#9'mov x19, x0');           { the result, across the walk }
      Self.Emit(#9'ldr x22, [sp, #16]');    { the parked element address }
      if not RecretManagedClean(TRecordTypeDesc(Elem)) then
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Elem), 'x22');
      Self.Emit(#9'mov x0, x22');
      Self.Emit(#9'mov x1, x19');
      EmitIntLiteral('x2', Elem.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Self.Emit(#9'add sp, sp, #16');        { drop the element address }
      Exit;
    end;
    if not RecretManagedClean(TRecordTypeDesc(Elem)) then
    begin
      Self.Emit(#9'stp x19, x22, [sp, #-16]!');
      EmitRecAddrToX0(AStmt.ValueExpr);
      Self.Emit(#9'mov x19, x0');
      Self.Emit(#9'ldr x22, [sp, #16]');   { the parked element address }
      Self.EmitRecordFieldRetains(TRecordTypeDesc(Elem), 'x19');
      { copy site: no-zero release (BUG-20260720-managed-record-self-assign) }
      Self.EmitRecordFieldReleases(TRecordTypeDesc(Elem), 'x22', False);
      Self.Emit(#9'mov x0, x22');
      Self.Emit(#9'mov x1, x19');
      EmitIntLiteral('x2', Elem.RawSize());
      EmitCallSym('memcpy');
      Self.Emit(#9'ldp x19, x22, [sp], #16');
      Self.Emit(#9'add sp, sp, #16');      { drop the element address }
      Exit;
    end;
    EmitRecAddrToX0(AStmt.ValueExpr);
    Self.Emit(#9'mov x1, x0');
    Self.Emit(#9'ldr x0, [sp], #16');      { the parked element address }
    EmitIntLiteral('x2', Elem.RawSize());
    EmitCallSym('memcpy');
    Exit;
  end
  else if IsIntFam(Elem) or
          (Elem.Kind in [tyBoolean, tyPointer, tyPChar]) then
  begin
    { a 1-byte element is a byte store: Chr(N) must stay a raw ordinal }
    if Elem.RawSize() = 1 then
      EmitByteRhsToX0(AStmt.ValueExpr)
    else
      Self.EmitExprToX0(AStmt.ValueExpr);
  end
  else
    NotYet('array element of this type', AStmt);
  Self.Emit(#9'ldr x9, [sp], #16');
  case Elem.RawSize() of
    1: Self.Emit(#9'strb w0, [x9]');
    4: Self.Emit(#9'str w0, [x9]');
    8: Self.Emit(#9'str x0, [x9]');
  else
    NotYet('array element of this width', AStmt);
  end;
end;

procedure TArm64Backend.EmitRaise(AStmt: TRaiseStmt);
begin
  if AStmt.Expr = nil then
  begin
    { bare re-raise: the in-flight exception }
    EmitCallSym('_CurrentException');
    EmitCallSym('_Reraise');
    Exit;
  end;
  { NOTE (BUG-049): a raise operand that reads a class field off an owned
    transient (raise MakeFactory().ExcField) is NOT flushed.  The exception
    object aliases the transient's graph and ESCAPES via the exception
    machinery, so releasing the transient would free the in-flight exception
    (UAF), and AddRef-pinning to compensate leaks it after the handler.  The
    deferred base stays in its _pendrel slot (leaked, never a UAF) — the sole
    residual of BUG-049; the common contexts are all flushed and leak-free.
    Mirrors the x86-64 backend. }
  Self.EmitExprToX0(AStmt.Expr);
  EmitCallSym('_Raise');
end;

procedure TArm64Backend.EmitRepeat(AStmt: TRepeatStmt);
var
  TopL, EndL: string;
begin
  { repeat..until: body always runs once; break/continue target the
    loop's exit / condition re-test }
  TopL := NewLabel('rep');
  EndL := NewLabel('rend');
  FBreakLbls.Add(EndL);
  FLoopExcDepth.Add(IntToStr(FExcDepth));
  FContLbls.Add(TopL);
  Self.Emit(TopL + ':');
  EmitStmtList(AStmt.Body.Stmts);
  Self.EmitCondToX0Flushed(AStmt.Condition);   { flush per iteration (BUG-049) }
  Self.Emit(Format(#9'cbz x0, %s', [TopL]));
  Self.Emit(EndL + ':');
  FBreakLbls.Delete(FBreakLbls.Count - 1);
  FLoopExcDepth.Delete(FLoopExcDepth.Count - 1);
  FContLbls.Delete(FContLbls.Count - 1);
end;

procedure TArm64Backend.EmitCase(AStmt: TCaseStmt);
var
  I, J: Integer;
  Br: TCaseBranch;
  EndL, NextL, BodyL, SkipL: string;
  CaseMark: Integer;
begin
  { chained compares — selector evaluated ONCE and kept on the stack
    across the branch tests (a value expression can be a call).  Ordinal
    labels compare registers; string labels compare content via
    _StringEquals (a pointer cmp would be silently wrong). }
  EndL := NewLabel('cend');
  CaseMark := FPendingRelCount;
  Self.EmitExprToX0(AStmt.Selector);
  EmitPushX0();
  { the selector may read a field off a transient; it is now safely on the
    stack, so flush its deferred base (x0 is free).  Evaluated once (BUG-049). }
  FlushNativePendingReleases(CaseMark);
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Br := TCaseBranch(AStmt.Branches.Items[I]);
    NextL := NewLabel('cnxt');
    BodyL := NewLabel('cbody');
    for J := 0 to Br.Values.Count - 1 do
    begin
      if AStmt.IsStringCase then
      begin
        { label values are string constants by grammar — immortal, so
          the value needs no disposal }
        Self.EmitExprToX0(TASTExpr(Br.Values.Items[J]));
        Self.Emit(#9'mov x1, x0');
        Self.Emit(#9'ldr x0, [sp]');
        EmitCallSym('_StringEquals');
        Self.Emit(Format(#9'cbnz x0, %s', [BodyL]));
      end
      else if TASTExpr(Br.Values.Items[J]) is TSetRangeExpr then
      begin
        { `lo..hi:` -- an inclusive range test, ordered with the selector's
          own signedness (unsigned conditions for an unsigned selector, as
          for any comparison) }
        SkipL := NewLabel('crng');
        Self.Emit(#9'ldr x0, [sp]');
        Self.EmitExprToX0Aux(TSetRangeExpr(Br.Values.Items[J]).LowExpr);
        Self.Emit(#9'cmp x0, x1');
        if IsUnsignedIntA64(AStmt.Selector.ResolvedType) then
          Self.Emit(Format(#9'b.lo %s', [SkipL]))
        else
          Self.Emit(Format(#9'b.lt %s', [SkipL]));
        Self.EmitExprToX0Aux(TSetRangeExpr(Br.Values.Items[J]).HighExpr);
        Self.Emit(#9'cmp x0, x1');
        if IsUnsignedIntA64(AStmt.Selector.ResolvedType) then
          Self.Emit(Format(#9'b.ls %s', [BodyL]))
        else
          Self.Emit(Format(#9'b.le %s', [BodyL]));
        Self.Emit(SkipL + ':');
      end
      else
      begin
        Self.Emit(#9'ldr x0, [sp]');
        Self.EmitExprToX0Aux(TASTExpr(Br.Values.Items[J]));
        Self.Emit(#9'cmp x0, x1');
        Self.Emit(Format(#9'b.eq %s', [BodyL]));
      end;
    end;
    Self.Emit(Format(#9'b %s', [NextL]));
    Self.Emit(BodyL + ':');
    EmitStmt(Br.Stmt);
    Self.Emit(Format(#9'b %s', [EndL]));
    Self.Emit(NextL + ':');
  end;
  if AStmt.ElseStmt <> nil then
    EmitStmt(AStmt.ElseStmt);
  Self.Emit(EndL + ':');
  if AStmt.IsStringCase and ArcBuiltinStrArgOwnsRef(AStmt.Selector) then
  begin
    { transient selector (concat/call result): dispose by refcount shape
      once dispatch is done — all branch bodies rejoin at EndL with the
      selector bracket still live }
    Self.Emit(#9'ldr x0, [sp]');
    EmitStrDisposeX0(AStmt.Selector);
  end;
  Self.Emit(#9'add sp, sp, #16');   { drop the selector }
end;

procedure TArm64Backend.EmitExprToX0Aux(AExpr: TASTExpr);
begin
  { evaluate AExpr into x1 while [sp] holds a live value: literal/const
    values only (case branch values are literals by grammar) }
  if AExpr is TIntLiteral then
  begin
    EmitIntLiteral('x1', TIntLiteral(AExpr).Value);
    Exit;
  end;
  if (AExpr is TIdentExpr) and TIdentExpr(AExpr).IsConstant then
  begin
    EmitIntLiteral('x1', TIdentExpr(AExpr).ConstValue);
    Exit;
  end;
  if (AExpr is TFuncCallExpr) and
     SameText(TFuncCallExpr(AExpr).Name, 'Ord') and
     (TFuncCallExpr(AExpr).Args.Count = 1) then
  begin
    { Ord(x) as a case value is compile-time foldable: a one-char
      literal folds to its byte, a constant ident to its value }
    if (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]) is TStringLiteral)
       and (Length(TStringLiteral(
         TFuncCallExpr(AExpr).Args.Items[0]).Value) = 1) then
    begin
      EmitIntLiteral('x1', StrAt(TStringLiteral(
        TFuncCallExpr(AExpr).Args.Items[0]).Value, 0));
      Exit;
    end;
    if (TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]) is TIdentExpr) and
       TIdentExpr(TFuncCallExpr(AExpr).Args.Items[0]).IsConstant then
    begin
      EmitIntLiteral('x1', TIdentExpr(
        TFuncCallExpr(AExpr).Args.Items[0]).ConstValue);
      Exit;
    end;
    if TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]) is TIntLiteral then
    begin
      EmitIntLiteral('x1', TIntLiteral(
        TFuncCallExpr(AExpr).Args.Items[0]).Value);
      Exit;
    end;
  end;
  { any other constant label (e.g. a negative literal, -5, which parses as a
    unary minus): evaluate it normally into x1, then restore the selector,
    which the contract above keeps live at [sp] }
  Self.EmitExprToX0(AExpr);
  Self.Emit(#9'mov x1, x0');
  Self.Emit(#9'ldr x0, [sp]');
end;

procedure TArm64Backend.EmitFor(AStmt: TForStmt);
var
  TopL, EndL, ContL: string;
  EndSlot: string;
  ForMark: Integer;
begin
  { the pre-pass registered one hidden end slot per for statement, consumed
    here in the same walk order }
  EndSlot := '__for_end_' + IntToStr(FForN);
  FForN := FForN + 1;
  TopL  := NewLabel('for');
  EndL  := NewLabel('fend');
  ContL := NewLabel('fcont');
  ForMark := FPendingRelCount;
  Self.EmitExprToX0(AStmt.StartExpr);
  EmitStoreSlot('x0', AStmt.VarName);
  Self.EmitExprToX0(AStmt.EndExpr);      { bound evaluated ONCE }
  EmitStoreSlot('x0', EndSlot);
  { start/end bounds may read a field off a transient; both are now stored to
    slots (x0 free), so flush their deferred bases once — the per-iteration
    test only RELOADS the slots, so a single flush suffices (BUG-049). }
  FlushNativePendingReleases(ForMark);
  Self.Emit(TopL + ':');
  EmitLoadSlot('x0', AStmt.VarName);
  EmitLoadSlot('x1', EndSlot);
  Self.Emit(#9'cmp x0, x1');
  if AStmt.IsDownTo then
    Self.Emit(Format(#9'b.lt %s', [EndL]))
  else
    Self.Emit(Format(#9'b.gt %s', [EndL]));
  FBreakLbls.Add(EndL);
  FLoopExcDepth.Add(IntToStr(FExcDepth));
  FContLbls.Add(ContL);
  Self.EmitStmt(AStmt.Body);
  FContLbls.Delete(FContLbls.Count - 1);
  FBreakLbls.Delete(FBreakLbls.Count - 1);
  FLoopExcDepth.Delete(FLoopExcDepth.Count - 1);
  Self.Emit(ContL + ':');
  EmitLoadSlot('x0', AStmt.VarName);
  if AStmt.IsDownTo then
    Self.Emit(#9'sub x0, x0, #1')
  else
    Self.Emit(#9'add x0, x0, #1');
  EmitStoreSlot('x0', AStmt.VarName);
  Self.Emit(Format(#9'b %s', [TopL]));
  Self.Emit(EndL + ':');
end;

procedure TArm64Backend.EmitForInAssignX0(AStmt: TForInStmt; AOwned: Boolean);
begin
  { assign the value in x0 to the loop variable.  Managed loop vars run
    the retain/release discipline: a BORROWED element value (array/string/
    set paths) is retained before it replaces the old binding; an OWNED
    value (enumerator Current getter result, +1) transfers straight in —
    an extra AddRef there would leak one ref per iteration. }
  if (AStmt.ResolvedVarType <> nil) and
     (AStmt.ResolvedVarType.IsString() or
      (AStmt.ResolvedVarType.Kind = tyClass)) then
  begin
    EmitPushX0();
    if not AOwned then
    begin
      if AStmt.ResolvedVarType.IsString() then
        EmitCallSym('_StringAddRef')
      else
        EmitCallSym('_ClassAddRef');
    end;
    EmitLoadSlot('x0', AStmt.VarName);
    if AStmt.ResolvedVarType.IsString() then
      EmitCallSym('_StringRelease')
    else
      EmitCallSym('_ClassRelease');
    EmitPopTo('x0');
    EmitStoreSlot('x0', AStmt.VarName);
    Exit;
  end;
  EmitStoreSlot('x0', AStmt.VarName);
end;

procedure TArm64Backend.EmitForInAssignAddr(AStmt: TForInStmt;
  AOwned: Boolean);
begin
  { x0 = the ADDRESS of the incoming record / interface value }
  if AStmt.ResolvedVarType.Kind = tyInterface then
  begin
    { the (obj, itab) pair: retain a borrowed obj, release the old binding,
      store both halves }
    Self.Emit(#9'ldp x0, x1, [x0]');
    if not AOwned then
    begin
      Self.Emit(#9'stp x0, x1, [sp, #-16]!');
      EmitCallSym('_ClassAddRef');
      Self.Emit(#9'ldp x0, x1, [sp], #16');
    end;
    Self.Emit(#9'stp x0, x1, [sp, #-16]!');
    EmitLoadSlot('x0', AStmt.VarName);
    EmitCallSym('_ClassRelease');
    Self.Emit(#9'ldp x0, x1, [sp], #16');
    EmitStoreSlot('x0', AStmt.VarName);
    EmitStoreSlot('x1', AStmt.VarName + '_itab');
    Exit;
  end;
  { a record: the record-assignment discipline -- retain a borrowed
    source's managed fields, release the loop variable's old ones, copy.
    Callee-saved x19/x22 hold the two addresses across the walk calls. }
  Self.Emit(#9'stp x19, x22, [sp, #-16]!');
  Self.Emit(#9'mov x19, x0');
  EmitSlotAddr('x22', AStmt.VarName);
  if AggHasManaged(AStmt.ResolvedVarType) then
  begin
    if not AOwned then
      Self.EmitRecordFieldRetains(TRecordTypeDesc(AStmt.ResolvedVarType), 'x19');
    Self.EmitRecordFieldReleases(TRecordTypeDesc(AStmt.ResolvedVarType),
      'x22', False);
  end;
  Self.Emit(#9'mov x0, x22');
  Self.Emit(#9'mov x1, x19');
  EmitIntLiteral('x2', AStmt.ResolvedVarType.RawSize());
  EmitCallSym('memcpy');
  Self.Emit(#9'ldp x19, x22, [sp], #16');
end;

procedure TArm64Backend.EmitForIn(AStmt: TForInStmt);
var
  IsAgg: Boolean;
  Tmp: string;
  Shape: Integer;
  CondL, NextL, EndL, NilLenL: string;
  Elem: TTypeDesc;
  ESz: Integer;
  GetE, MN, Cur: TMethodDecl;
  EmptyArgs: TObjectList;
begin
  if (AStmt.ResolvedVarType <> nil) and
     (AStmt.ResolvedVarType.Kind in [tyRecord, tyInterface]) and
     IsCaptured(AStmt.VarName) then
    NotYet('captured for-in loop variable of this type', AStmt);
  IsAgg := (AStmt.ResolvedVarType <> nil) and
           (AStmt.ResolvedVarType.Kind in [tyRecord, tyInterface]);
  CondL := NewLabel('ficond');
  NextL := NewLabel('finext');
  EndL := NewLabel('fiend');

  if AStmt.IsArrayIter or AStmt.IsDynArrayIter then
  begin
    { array iteration: idx runs low..high (static) / 0..len-1 (dynamic);
      element address = base + (idx - low) * elemsize.  The collection
      must be a plain ident — matches the subscript emitters. }
    if not (AStmt.CollExpr is TIdentExpr) then
      NotYet('for-in over this array expression', AStmt);
    if TIdentExpr(AStmt.CollExpr).ParamMode = pmVar then
      NotYet('for-in over a var array parameter', AStmt);
    if AStmt.IsArrayIter then
      Elem := TStaticArrayTypeDesc(AStmt.CollExpr.ResolvedType).ElementType
    else
      Elem := TDynArrayTypeDesc(AStmt.CollExpr.ResolvedType).ElementType;
    if (Elem = nil) or
       (not (Elem.Kind in [tyRecord, tyInterface]) and (Elem.RawSize() > 8)) then
      NotYet('for-in over aggregate elements', AStmt);
    ESz := Elem.RawSize();
    if AStmt.IsArrayIter then
      EmitIntLiteral('x0', AStmt.ArrayLow)
    else
      Self.Emit(#9'movz x0, #0');
    EmitStoreSlot('x0', AStmt.IdxVarName);
    Self.Emit(CondL + ':');
    if AStmt.IsArrayIter then
    begin
      EmitLoadSlot('x0', AStmt.IdxVarName);
      EmitIntLiteral('x1', AStmt.ArrayHigh);
      Self.Emit(#9'cmp x0, x1');
      Self.Emit(Format(#9'b.gt %s', [EndL]));
    end
    else
    begin
      { length re-read every pass — the body may SetLength }
      EmitLoadSlot('x0', TIdentExpr(AStmt.CollExpr).Name);
      EmitCallSym('_DynArrayLength');
      Self.Emit(#9'mov x1, x0');
      EmitLoadSlot('x0', AStmt.IdxVarName);
      Self.Emit(#9'cmp x0, x1');
      Self.Emit(Format(#9'b.ge %s', [EndL]));
    end;
    if AStmt.IsArrayIter then
      EmitSlotAddr('x0', TIdentExpr(AStmt.CollExpr).Name)
    else
      EmitLoadSlot('x0', TIdentExpr(AStmt.CollExpr).Name);
    EmitLoadSlot('x1', AStmt.IdxVarName);
    if AStmt.IsArrayIter and (AStmt.ArrayLow <> 0) then
    begin
      EmitIntLiteral('x2', AStmt.ArrayLow);
      Self.Emit(#9'sub x1, x1, x2');
    end;
    EmitIntLiteral('x2', ESz);
    Self.Emit(#9'mul x1, x1, x2');
    Self.Emit(#9'add x0, x0, x1');
    if IsAgg then
      { a record / interface element is copied from its address; the
        element stays the array's, so the copy retains }
      EmitForInAssignAddr(AStmt, False)
    else
    begin
      EmitElemLoad(Elem);
      EmitForInAssignX0(AStmt, False);
    end;
    FBreakLbls.Add(EndL);
    FLoopExcDepth.Add(IntToStr(FExcDepth));
    FContLbls.Add(NextL);
    Self.EmitStmt(AStmt.Body);
    FContLbls.Delete(FContLbls.Count - 1);
    FBreakLbls.Delete(FBreakLbls.Count - 1);
    FLoopExcDepth.Delete(FLoopExcDepth.Count - 1);
    Self.Emit(NextL + ':');
    EmitLoadSlot('x0', AStmt.IdxVarName);
    Self.Emit(#9'add x0, x0, #1');
    EmitStoreSlot('x0', AStmt.IdxVarName);
    Self.Emit(Format(#9'b %s', [CondL]));
    Self.Emit(EndL + ':');
    Exit;
  end;

  if AStmt.IsStringIter or AStmt.IsCodePointIter then
  begin
    { string iteration: length lives 8 bytes below the data pointer.
      Byte mode loads one byte per pass; codepoint mode calls
      _Utf8DecodeAt (packed result: low 32 = codepoint, high 32 = byte
      advance) and steps by the advance. }
    if ArcBuiltinStrArgOwnsRef(AStmt.CollExpr) then
      NotYet('for-in over a transient string', AStmt);
    Self.Emit(#9'movz x0, #0');
    EmitStoreSlot('x0', AStmt.IdxVarName);
    Self.Emit(CondL + ':');
    Self.EmitExprToX0(AStmt.CollExpr);
    { length lives at [ptr-8]; a nil (empty) string must read as length 0,
      not fault on [nil-8] — see EmitStrLen. }
    NilLenL := NewLabel('flen0');
    Self.Emit(Format(#9'cbz x0, %s', [NilLenL]));
    Self.Emit(#9'ldur w1, [x0, #-8]');
    Self.Emit(Format(#9'b %s_done', [NilLenL]));
    Self.Emit(NilLenL + ':');
    Self.Emit(#9'movz x1, #0');
    Self.Emit(NilLenL + '_done:');
    EmitLoadSlot('x0', AStmt.IdxVarName);
    Self.Emit(#9'cmp x0, x1');
    Self.Emit(Format(#9'b.ge %s', [EndL]));
    Self.EmitExprToX0(AStmt.CollExpr);
    if AStmt.IsCodePointIter then
    begin
      EmitLoadSlot('x1', AStmt.IdxVarName);
      EmitCallSym('_Utf8DecodeAt');
      EmitPushX0();
      Self.Emit(#9'lsr x0, x0, #32');
      EmitStoreSlot('x0', AStmt.AdvVarName);
      EmitPopTo('x0');
      Self.Emit(#9'sxtw x0, w0');
    end
    else
    begin
      EmitLoadSlot('x1', AStmt.IdxVarName);
      Self.Emit(#9'add x0, x0, x1');
      Self.Emit(#9'ldrb w0, [x0]');
    end;
    EmitForInAssignX0(AStmt, False);
    FBreakLbls.Add(EndL);
    FLoopExcDepth.Add(IntToStr(FExcDepth));
    FContLbls.Add(NextL);
    Self.EmitStmt(AStmt.Body);
    FContLbls.Delete(FContLbls.Count - 1);
    FBreakLbls.Delete(FBreakLbls.Count - 1);
    FLoopExcDepth.Delete(FLoopExcDepth.Count - 1);
    Self.Emit(NextL + ':');
    EmitLoadSlot('x0', AStmt.IdxVarName);
    if AStmt.IsCodePointIter then
    begin
      EmitLoadSlot('x1', AStmt.AdvVarName);
      Self.Emit(#9'add x0, x0, x1');
    end
    else
      Self.Emit(#9'add x0, x0, #1');
    EmitStoreSlot('x0', AStmt.IdxVarName);
    Self.Emit(Format(#9'b %s', [CondL]));
    Self.Emit(EndL + ':');
    Exit;
  end;

  if AStmt.IsSetIter then
  begin
    { set iteration: evaluate the mask ONCE into its synthetic slot, then
      walk bit positions 0..BitCount-1 and run the body for each set bit }
    if AStmt.SetIsJumbo then
      NotYet('for-in over a jumbo set', AStmt);
    Self.EmitExprToX0(AStmt.CollExpr);
    EmitStoreSlot('x0', AStmt.SetMaskVarName);
    Self.Emit(#9'movz x0, #0');
    EmitStoreSlot('x0', AStmt.IdxVarName);
    Self.Emit(CondL + ':');
    EmitLoadSlot('x0', AStmt.IdxVarName);
    EmitIntLiteral('x1', AStmt.SetBitCount);
    Self.Emit(#9'cmp x0, x1');
    Self.Emit(Format(#9'b.ge %s', [EndL]));
    EmitLoadSlot('x0', AStmt.SetMaskVarName);
    EmitLoadSlot('x1', AStmt.IdxVarName);
    Self.Emit(#9'lsr x0, x0, x1');
    Self.Emit(#9'movz x2, #1');
    Self.Emit(#9'and x0, x0, x2');
    Self.Emit(Format(#9'cbz x0, %s', [NextL]));
    EmitLoadSlot('x0', AStmt.IdxVarName);
    EmitForInAssignX0(AStmt, False);
    FBreakLbls.Add(EndL);
    FLoopExcDepth.Add(IntToStr(FExcDepth));
    FContLbls.Add(NextL);
    Self.EmitStmt(AStmt.Body);
    FContLbls.Delete(FContLbls.Count - 1);
    FBreakLbls.Delete(FBreakLbls.Count - 1);
    FLoopExcDepth.Delete(FLoopExcDepth.Count - 1);
    Self.Emit(NextL + ':');
    EmitLoadSlot('x0', AStmt.IdxVarName);
    Self.Emit(#9'add x0, x0, #1');
    EmitStoreSlot('x0', AStmt.IdxVarName);
    Self.Emit(Format(#9'b %s', [CondL]));
    Self.Emit(EndL + ':');
    Exit;
  end;

  { class enumerator protocol: GetEnumerator -> owned enumerator object;
    while MoveNext do LoopVar := Current.  The enumerator TRANSFERS into
    its synthetic slot (the getter result is +1; the slot's scope-exit
    release balances it — an AddRef here would leak one enumerator per
    loop). }
  GetE := TMethodDecl(AStmt.GetEnumDecl);
  MN := TMethodDecl(AStmt.MoveNextDecl);
  Cur := TMethodDecl(AStmt.CurrentDecl);
  if (GetE = nil) or (MN = nil) or (Cur = nil) then
    NotYet('for-in over this collection', AStmt);
  if (AStmt.ResolvedVarType <> nil) and
     (AStmt.ResolvedVarType.Kind in [tyDouble, tySingle]) then
    NotYet('float-typed enumerator Current', AStmt);
  if ArcExprOwnsRef(AStmt.CollExpr) then
    NotYet('for-in over an owned transient collection', AStmt);
  EmptyArgs := TObjectList.Create(False);
  try
    Self.EmitExprToX0(AStmt.CollExpr);
    EmitMethodCallCommon(GetE, 'GetEnumerator', EmptyArgs);
    EmitPushX0();
    EmitLoadSlot('x0', AStmt.EnumVarName);
    EmitCallSym('_ClassRelease');
    EmitPopTo('x0');
    EmitStoreSlot('x0', AStmt.EnumVarName);
    Self.Emit(CondL + ':');
    EmitLoadSlot('x0', AStmt.EnumVarName);
    EmitMethodCallCommon(MN, 'MoveNext', EmptyArgs);
    Self.Emit(Format(#9'cbz x0, %s', [EndL]));
    if IsAgg then
    begin
      { a record / interface Current comes back through x8 (or x0:x1 for a
        small record) into a per-site scratch, OWNED, and moves into the
        loop variable without a retain }
      Tmp := '__ficur_' + IntToStr(FJArgN);
      FJArgN := FJArgN + 1;
      if not FFrame.ContainsKey(Tmp) then
        AddLocal(Tmp, AStmt.ResolvedVarType.RawSize());
      Shape := 0;
      if AStmt.ResolvedVarType.Kind = tyRecord then
        Shape := RecReturnShape(TRecordTypeDesc(AStmt.ResolvedVarType));
      if (Shape >= 100) then
        NotYet('for-in over an HFA-record enumerator', AStmt);
      EmitLoadSlot('x0', AStmt.EnumVarName);
      EmitPushX0();
      if Shape = 0 then
        EmitCall(Cur, Cur.Name, EmptyArgs, Tmp, True, Cur.VTableSlot)
      else
      begin
        EmitCall(Cur, Cur.Name, EmptyArgs, '', True, Cur.VTableSlot);
        EmitSlotAddr('x9', Tmp);
        Self.Emit(#9'str x0, [x9]');
        if Shape = 2 then
          Self.Emit(#9'str x1, [x9, #8]');
      end;
      EmitSlotAddr('x0', Tmp);
      EmitForInAssignAddr(AStmt, True);
    end
    else
    begin
      EmitLoadSlot('x0', AStmt.EnumVarName);
      EmitMethodCallCommon(Cur, Cur.Name, EmptyArgs);
      EmitForInAssignX0(AStmt, True);
    end;
    FBreakLbls.Add(EndL);
    FLoopExcDepth.Add(IntToStr(FExcDepth));
    FContLbls.Add(CondL);
    Self.EmitStmt(AStmt.Body);
    FContLbls.Delete(FContLbls.Count - 1);
    FBreakLbls.Delete(FBreakLbls.Count - 1);
    FLoopExcDepth.Delete(FLoopExcDepth.Count - 1);
    Self.Emit(Format(#9'b %s', [CondL]));
    Self.Emit(EndL + ':');
  finally
    EmptyArgs.Free();
  end;
end;

procedure TArm64Backend.EmitBuiltinStrCall1(AArg: TASTExpr;
  const ASym: string);
begin
  { one-string-arg RTL builtin: evaluate, call, and dispose a transient
    argument BY SHAPE after the call (the result register is parked
    across the release) — the day-one rule from
    docs/arc-string-transient-handover.adoc }
  Self.EmitExprToX0(AArg);
  if ArcBuiltinStrArgOwnsRef(AArg) then
  begin
    { An rc=0 UNOWNED transient must be PINNED before the call
      (BUG-20260725-arm64-const-str-param-alias): a builtin that stores its
      const parameter into a local runs a legitimate retain-then-exit-release
      cycle on it, and at rc=0 that cycle reaches zero and frees OUR buffer
      mid-call — the post-call dispose then hit a reused block.  With the pin
      the callee's cycle is 1->2->1 and the single bare Release below disposes
      it exactly once.  Same rule as the closure-call and property-setter
      paths. }
    EmitOwnedStrTransientPin(AArg);
    EmitPushX0();                         { [arg] }
    EmitCallSym(ASym);
    EmitPushX0();                         { [arg][result] }
    Self.Emit(#9'ldr x0, [sp, #16]');
    if ArcExprIsUnownedStrTransient(AArg) then
      { pinned above: one bare release takes it 1 -> 0 }
      EmitCallSym('_StringRelease')
    else
      EmitStrDisposeX0(AArg);
    EmitPopTo('x0');
    Self.Emit(#9'add sp, sp, #16');
    Exit;
  end;
  EmitCallSym(ASym);
end;

procedure TArm64Backend.EmitRecCallDispatch(AExpr: TASTExpr;
  const ADest: string; ASretSpOff: Integer);
var
  ME: TMethodCallExpr;
  MD: TMethodDecl;
begin
  { record-returning call in an assignment: one dispatcher for free
    functions AND method receivers, so every return shape shares the
    same caller-side store logic }
  if AExpr is TMethodCallExpr then
  begin
    ME := TMethodCallExpr(AExpr);
    MD := TMethodDecl(ME.ResolvedMethod);
    if ME.IsStaticCall or MD.IsStatic then
    begin
      EmitCall(MD, ME.Name, ME.Args, ADest, False, VIRT_NONE, ASretSpOff);
      Exit;
    end;
    if MD.IsRecordMethod then
    begin
      { a RECORD method's Self is the record's ADDRESS, never its contents
        (the EmitMethodCallExpr rule).  Loading the slot passed the record's
        first 8 bytes as Self -- Self.Group(I).Value inside a record method
        (text.regex's TMatch) handed Group the FGroups data pointer. }
      if ME.ObjExpr = nil then
        EmitRecordBaseAddr('x0', ME.ObjectName, ME.IsVarParam)
      else if IsRecordCallArg(ME.ObjExpr) then
      begin
        if AggHasManaged(ME.ObjExpr.ResolvedType) then
          NotYet('record method call on a managed record call result', AExpr);
        EmitRecCallToRret(ME.ObjExpr)
      end
      else
        EmitRecAddrToX0(ME.ObjExpr);
    end
    else if ME.ObjExpr <> nil then
    begin
      if ArcExprOwnsRef(ME.ObjExpr) then
        NotYet('record call on an owned transient receiver', AExpr);
      Self.EmitExprToX0(ME.ObjExpr);
    end
    else
    begin
      EmitLoadSlot('x0', ME.ObjectName);
      if ME.IsVarParam then
        Self.Emit(#9'ldr x0, [x0]');
    end;
    EmitPushX0();
    { No adjustment for the receiver push: EmitCall's pop walk consumes it
      (ASelfPushed), so by the time x8 is set sp is back to this level. }
    EmitCall(MD, ME.Name, ME.Args, ADest, True, MD.VTableSlot, ASretSpOff);
    Exit;
  end;
  { A bare method call on implicit Self that returns a record (P := Make;) is a
    TFuncCallExpr with IsImplicitSelfMethod — it needs the SAME receiver setup a
    method call does (x0 := Self, pushed for EmitCall's method convention).  The
    scalar implicit-Self path (EmitExprToX0) rejects aggregate returns and sends
    them here, so without this the record-return free-function fallthrough below
    called the method with NO Self — ComputeLayout()/Make() ran with Self=nil and
    faulted on the first field read (macOS arm64, 2026-07-24, Mach-O exe layout). }
  if (AExpr is TFuncCallExpr) and TFuncCallExpr(AExpr).IsImplicitSelfMethod and
     (TFuncCallExpr(AExpr).ResolvedDecl <> nil) then
  begin
    MD := TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl);
    EmitLoadSlot('x0', 'Self');
    EmitPushX0();
    EmitCall(MD, TFuncCallExpr(AExpr).Name, TFuncCallExpr(AExpr).Args,
      ADest, True, MD.VTableSlot, ASretSpOff);
    Exit;
  end;
  EmitCall(TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl),
    TFuncCallExpr(AExpr).Name, TFuncCallExpr(AExpr).Args, ADest,
    False, VIRT_NONE, ASretSpOff);
end;

procedure TArm64Backend.EmitFormatCall(AArgs: TObjectList);
var
  I, FmtCount, TotalSize: Integer;
  Arg: TASTExpr;
  Elems: TObjectList;
  IsIntArg: Boolean;
begin
  { Format(Fmt, [a, b, ...]) → _StringFormatN(fmt, block, count).
    Block layout mirrors x86-64: 16-byte entries, tag at +0 (0 = int,
    1 = string/pointer, 2 = raw binary64 float bits), value at +8.
    Elements are BORROWED — same convention as the x86 lowering. }
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
    { the _high companion must be a slot of the CURRENT frame; a captured
      array-of-const param does not forward it (parity with x86-64) }
    if not IsLocal(TIdentExpr(AArgs.Items[1]).Name + '_high') then
      NotYet('Format over a captured array-of-const parameter',
        TASTExpr(AArgs.Items[1]));
    Self.EmitExprToX0(TASTExpr(AArgs.Items[0]));   { fmt }
    EmitPushX0();                                   { [fmt] }
    Self.EmitExprToX0(TASTExpr(AArgs.Items[1]));   { data ptr }
    Self.Emit(#9'mov x1, x0');
    EmitLoadSlot('x2', TIdentExpr(AArgs.Items[1]).Name + '_high');
    Self.Emit(#9'add x2, x2, #1');                  { count = high + 1 }
    EmitPopTo('x0');                                { fmt }
    EmitCallSym('_StringFormatVarRecs');
    Exit;
  end;
  { the elements: a bracket literal's (Format(F, [A, B])), or the bare
    variadic arguments themselves (Format(F, A, B)) -- the same block either
    way.  Elems is a non-owning view. }
  Elems := TObjectList.Create(False);
  try
  if (AArgs.Count = 2) and (TASTExpr(AArgs.Items[1]) is TArrayLiteralExpr) then
  begin
    for I := 0 to TArrayLiteralExpr(AArgs.Items[1]).Elements.Count - 1 do
      Elems.Add(TArrayLiteralExpr(AArgs.Items[1]).Elements.Items[I]);
  end
  else
    for I := 1 to AArgs.Count - 1 do
      Elems.Add(AArgs.Items[I]);
  FmtCount := Elems.Count;
  Self.EmitExprToX0(TASTExpr(AArgs.Items[0]));
  EmitPushX0();                              { [fmt] — parked to the end }
  if FmtCount = 0 then
  begin
    Self.Emit(#9'ldr x0, [sp]');
    Self.Emit(#9'movz x1, #0');
    Self.Emit(#9'movz x2, #0');
    EmitCallSym('_StringFormatN');
    if ArcBuiltinStrArgOwnsRef(TASTExpr(AArgs.Items[0])) then
    begin
      EmitPushX0();                          { [fmt][result] }
      Self.Emit(#9'ldr x0, [sp, #16]');
      EmitStrDisposeX0(TASTExpr(AArgs.Items[0]));
      EmitPopTo('x0');
    end;
    Self.Emit(#9'add sp, sp, #16');          { drop the fmt slot }
    Exit;
  end;
  TotalSize := ((FmtCount * 16) + 15) and (-16);
  EmitAddSubImm('sub', 'sp', 'sp', TotalSize);
  for I := 0 to FmtCount - 1 do
  begin
    Arg := TASTExpr(Elems.Items[I]);
    if (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind in [tyDouble, tySingle]) then
    begin
      { float: tag 2, value = the raw binary64 bit pattern }
      Self.EmitExprToD0OrConvert(Arg);
      Self.Emit(#9'fmov x0, d0');
      Self.Emit(Format(#9'str x0, [sp, #%d]', [I * 16 + 8]));
      Self.Emit(#9'movz x9, #2');
      Self.Emit(Format(#9'str x9, [sp, #%d]', [I * 16]));
      Continue;
    end;
    IsIntArg := (Arg.ResolvedType = nil) or
      (Arg.ResolvedType.Kind in [tyInteger, tyBoolean, tyByte, tyUInt32,
                                 tyInt64, tyUInt64, tySmallInt, tyWord,
                                 tyEnum]);
    Self.EmitExprToX0(Arg);
    Self.Emit(Format(#9'str x0, [sp, #%d]', [I * 16 + 8]));
    if IsIntArg then
      Self.Emit(#9'movz x9, #0')
    else
      Self.Emit(#9'movz x9, #1');
    Self.Emit(Format(#9'str x9, [sp, #%d]', [I * 16]));
  end;
  Self.Emit(Format(#9'ldr x0, [sp, #%d]', [TotalSize]));  { parked fmt }
  Self.Emit(#9'mov x1, sp');
  EmitIntLiteral('x2', FmtCount);
  EmitCallSym('_StringFormatN');
  { transient disposal by shape: the block still holds every element
    pointer and the fmt sits above it — park the result, sweep, restore }
  EmitPushX0();                              { [fmt][block][result] }
  for I := 0 to FmtCount - 1 do
  begin
    Arg := TASTExpr(Elems.Items[I]);
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyString)
       and ArcBuiltinStrArgOwnsRef(Arg) then
    begin
      Self.Emit(Format(#9'ldr x0, [sp, #%d]', [16 + I * 16 + 8]));
      EmitStrDisposeX0(Arg);
    end;
  end;
  if ArcBuiltinStrArgOwnsRef(TASTExpr(AArgs.Items[0])) then
  begin
    Self.Emit(Format(#9'ldr x0, [sp, #%d]', [16 + TotalSize]));
    EmitStrDisposeX0(TASTExpr(AArgs.Items[0]));
  end;
  EmitPopTo('x0');
  EmitAddSubImm('add', 'sp', 'sp', TotalSize);
  Self.Emit(#9'add sp, sp, #16');            { drop the fmt slot }
  finally
    Elems.Free();
  end;
end;

procedure TArm64Backend.EmitBuiltinStrCall2(AArg0, AArg1: TASTExpr;
  const ASym: string);
begin
  { two-arg twin: BOTH operands stay parked across the call so either
    transient can be disposed by shape afterwards (the concat emitter's
    slot scheme) }
  Self.EmitExprToX0(AArg0);
  EmitPushX0();                           { [a0] }
  Self.EmitExprToX0(AArg1);
  EmitPushX0();                           { [a0][a1] }
  Self.Emit(#9'ldr x1, [sp]');
  Self.Emit(#9'ldr x0, [sp, #16]');
  EmitCallSym(ASym);
  if ArcBuiltinStrArgOwnsRef(AArg0) or ArcBuiltinStrArgOwnsRef(AArg1) then
  begin
    EmitPushX0();                         { [a0][a1][result] }
    if ArcBuiltinStrArgOwnsRef(AArg1) then
    begin
      Self.Emit(#9'ldr x0, [sp, #16]');
      EmitStrDisposeX0(AArg1);
    end;
    if ArcBuiltinStrArgOwnsRef(AArg0) then
    begin
      Self.Emit(#9'ldr x0, [sp, #32]');
      EmitStrDisposeX0(AArg0);
    end;
    EmitPopTo('x0');
  end;
  Self.Emit(#9'add sp, sp, #32');
end;

procedure TArm64Backend.EmitNarrowX0(AType: TTypeDesc);
begin
  { normalise x0 to AType's width: truncate + re-extend so the 64-bit
    register value matches the target type's domain }
  if AType = nil then Exit;
  case AType.Kind of
    tyInteger, tyEnum: Self.Emit(#9'sxtw x0, w0');
    tyUInt32:  Self.Emit(#9'mov w0, w0');
    tyByte:
    begin
      Self.Emit(#9'lsl x0, x0, #56');
      Self.Emit(#9'lsr x0, x0, #56');
    end;
    tyWord:
    begin
      Self.Emit(#9'lsl x0, x0, #48');
      Self.Emit(#9'lsr x0, x0, #48');
    end;
    tySmallInt:
    begin
      Self.Emit(#9'lsl x0, x0, #48');
      Self.Emit(#9'asr x0, x0, #48');
    end;
    tyBoolean:
    begin
      Self.Emit(#9'cmp x0, #0');
      Self.Emit(#9'cset x0, ne');
    end;
  else
    { 64-bit integers, enums, pointer-like and class kinds pass through }
  end;
end;

procedure TArm64Backend.EmitPointerWrite(AStmt: TPointerWriteStmt);
var
  NB: Integer;
  Owned: Boolean;
begin
  { P^ := V.  Value first, then pointer — evaluating the value cannot
    invalidate a parked pointer, and an ARC release of the old pointee
    happens only after the new value holds its own reference (a self-
    assign through the pointer stays safe). }
  if AStmt.BaseTy = nil then
    NotYet('pointer write with unresolved base type', AStmt);
  { String, class and dynamic-array pointees share one retain/release shape —
    a single refcounted word — differing only in the RTL entry points. }
  if AStmt.BaseTy.IsString() or (AStmt.BaseTy.Kind = tyClass) or
     (AStmt.BaseTy.Kind = tyDynArray) then
  begin
    Self.EmitExprToX0(AStmt.ValExpr);
    if not ArcExprOwnsRef(AStmt.ValExpr) then
    begin
      EmitPushX0();
      if AStmt.BaseTy.IsString() then
        EmitCallSym('_StringAddRef')
      else if AStmt.BaseTy.Kind = tyDynArray then
        EmitCallSym('_DynArrayAddRef')
      else
        EmitCallSym('_ClassAddRef');
      EmitPopTo('x0');
    end;
    EmitPushX0();                          { [val] }
    Self.EmitExprToX0(AStmt.PtrExpr);
    EmitPushX0();                          { [val][ptr] }
    Self.Emit(#9'ldr x0, [x0]');
    if AStmt.BaseTy.IsString() then
      EmitCallSym('_StringRelease')
    else if AStmt.BaseTy.Kind = tyDynArray then
      EmitCallSym('_DynArrayRelease')
    else
      EmitCallSym('_ClassRelease');
    Self.Emit(#9'ldr x9, [sp]');
    Self.Emit(#9'ldr x0, [sp, #16]');
    Self.Emit(#9'str x0, [x9]');
    Self.Emit(#9'add sp, sp, #32');
    Exit;
  end;
  { Interface pointee: a 16-byte fat pointer (obj at +0, itab at +8).  The
    x86-64 backend delegates this to EmitInterfaceToFieldSlotsAt; arm64 has no
    address-based fat-pointer store helper yet (its interface handling is all
    named-slot based), so fail loud rather than emit a half-store that writes
    the obj word and leaves the itab stale. }
  if AStmt.BaseTy.Kind = tyInterface then
  begin
    { P^ := Intf: the pointee is an (obj, itab) pair -- the shared pair
      store retains the new obj, releases the old and writes both halves }
    Self.EmitExprToX0(AStmt.PtrExpr);
    EmitPushX0();
    EmitIntfStoreStacked(0, AStmt.ValExpr, AStmt.BaseTy);
    Exit;
  end;
  if AStmt.BaseTy.Kind in [tyDouble, tySingle] then
  begin
    Self.EmitExprToD0OrConvert(AStmt.ValExpr);
    Self.Emit(#9'str d0, [sp, #-16]!');
    Self.EmitExprToX0(AStmt.PtrExpr);
    Self.Emit(#9'ldr d0, [sp], #16');
    if AStmt.BaseTy.Kind = tySingle then
    begin
      Self.Emit(#9'fcvt s0, d0');
      Self.Emit(#9'str s0, [x0]');
    end
    else
      Self.Emit(#9'str d0, [x0]');
    Exit;
  end;
  if IsJumboSetType(AStmt.BaseTy) then
  begin
    { P^ := <jumbo set>: copy the bitmap.  A literal value lowers sp for its
      buffer, so the parked pointer is read above it. }
    Self.EmitExprToX0(AStmt.PtrExpr);
    EmitPushX0();
    NB := JumboSetLiteralBytes(AStmt.ValExpr);
    Self.EmitExprToX0(AStmt.ValExpr);
    Self.Emit(#9'mov x1, x0');
    Self.Emit(Format(#9'ldr x0, [sp, #%d]', [NB]));
    EmitIntLiteral('x2', AStmt.BaseTy.RawSize());
    EmitCallSym('memcpy');
    EmitAddSubImm('add', 'sp', 'sp', NB + 16);
    Exit;
  end;
  if (AStmt.BaseTy.Kind = tyRecord) or
     ((AStmt.BaseTy.Kind = tyStaticArray) and
      not AggHasManaged(AStmt.BaseTy)) then
  begin
    { P^ := R (TList<TRec>.Add's Dest^ := Value): the x86-64 record-copy
      discipline -- retain the source's managed fields, release the
      destination's old ones (no-zero, so P^ := P^ stays exact), memcpy.  A
      record-returning call is materialised first and its +1 references
      TRANSFER, so it is not retained again.  The two addresses live in
      callee-saved x19/x22 across the walk calls. }
    Self.EmitExprToX0(AStmt.PtrExpr);
    EmitPushX0();                                  { [ptr] }
    Self.Emit(#9'stp x19, x22, [sp, #-16]!');
    Owned := IsRecordCallArg(AStmt.ValExpr);
    if Owned then
      EmitRecCallToRret(AStmt.ValExpr)            { x0 = __rret }
    else
      EmitRecAddrToX0(AStmt.ValExpr);
    Self.Emit(#9'mov x19, x0');
    Self.Emit(#9'ldr x22, [sp, #16]');
    if (AStmt.BaseTy.Kind = tyRecord) and AggHasManaged(AStmt.BaseTy) then
    begin
      if not Owned then
        Self.EmitRecordFieldRetains(TRecordTypeDesc(AStmt.BaseTy), 'x19');
      Self.EmitRecordFieldReleases(TRecordTypeDesc(AStmt.BaseTy), 'x22',
        False);
    end;
    Self.Emit(#9'mov x0, x22');
    Self.Emit(#9'mov x1, x19');
    EmitIntLiteral('x2', AStmt.BaseTy.RawSize());
    EmitCallSym('memcpy');
    Self.Emit(#9'ldp x19, x22, [sp], #16');
    Self.Emit(#9'add sp, sp, #16');                { drop the pointer }
    Exit;
  end;
  if AStmt.BaseTy.Kind = tyStaticArray then
    NotYet('pointer write of a managed static array', AStmt);
  Self.EmitExprToX0(AStmt.ValExpr);
  EmitPushX0();
  Self.EmitExprToX0(AStmt.PtrExpr);
  Self.Emit(#9'mov x9, x0');
  EmitPopTo('x0');
  case AStmt.BaseTy.RawSize() of
    1: Self.Emit(#9'strb w0, [x9]');
    2: Self.Emit(#9'strh w0, [x9]');
    4: Self.Emit(#9'str w0, [x9]');
    8: Self.Emit(#9'str x0, [x9]');
  else
    NotYet('pointer write of this width', AStmt);
  end;
end;

procedure TArm64Backend.EmitExit(AStmt: TExitStmt);
begin
  if AStmt.ResultAssign <> nil then
    Self.EmitStmt(AStmt.ResultAssign)
  else if AStmt.Value <> nil then
    NotYet('exit with a value in this position', AStmt);
  { leaving through try regions runs their finally bodies on the way out }
  EmitExcUnwindTo(0);
  Self.Emit(Format(#9'b %s', [FExitLabel]));
end;

{ ---- routines ------------------------------------------------------------ }

function TArm64Backend.DarwinSym(const AName: string): string;
begin
  { see the declaration — unconditional on Darwin, no classification }
  if FTarget.OS = osMacOS then
    Result := '_' + AName
  else
    Result := AName;
end;

procedure TArm64Backend.EmitCallSym(const AName: string);
begin
  Self.Emit(#9'bl ' + DarwinSym(AName));
end;

function TArm64Backend.SecRodata: string;
begin
  if FTarget.OS = osMacOS then
    Result := '.section __TEXT,__const'
  else
    Result := '.section .rodata';
end;

function TArm64Backend.SecData: string;
begin
  if FTarget.OS = osMacOS then
    Result := '.section __DATA,__data'
  else
    Result := '.section .data';
end;

procedure TArm64Backend.EmitWeakDef(const ASym: string);
begin
  if FTarget.OS = osMacOS then
  begin
    { both, and in this order — see the declaration }
    Self.Emit('.globl ' + ASym);
    Self.Emit('.weak_definition ' + ASym);
  end
  else
    Self.Emit('.weak ' + ASym);
end;

procedure TArm64Backend.EmitGloblDef(const ASym: string);
begin
  { '.globl' is spelled the same on ELF and Mach-O }
  Self.Emit('.globl ' + ASym);
end;

function TArm64Backend.SecBss: string;
begin
  { __DATA,__bss takes plain labels + .zero under clang — verified; it does not
    need Mach-O's .zerofill form. }
  if FTarget.OS = osMacOS then
    Result := '.section __DATA,__bss'
  else
    Result := '.section .bss';
end;

function TArm64Backend.TypeinfoSym(const ABase: string): string;
begin
  Result := DarwinSym('typeinfo_' + ABase);
end;

function TArm64Backend.VtableSym(const ABase: string): string;
begin
  Result := DarwinSym('vtable_' + ABase);
end;

function TArm64Backend.ImpllistSym(const ABase: string): string;
begin
  Result := DarwinSym('impllist_' + ABase);
end;

function TArm64Backend.FieldCleanupSym(const ABase: string): string;
begin
  { '_FieldCleanup_X' is the base name; on Darwin it becomes
    __FieldCleanup_X, which is what QBE emits for the same table }
  Result := DarwinSym('_FieldCleanup_' + ABase);
end;

function TArm64Backend.RoutineSym(ADecl: TMethodDecl;
  const AName: string): string;
begin
  if (ADecl <> nil) and ADecl.IsExternal and (ADecl.ExternalName <> '') then
    { an external name takes the prefix like any other: 'getpid' -> _getpid is
      libSystem's real symbol, and '_StringAddRef' -> __StringAddRef matches the
      definition another RTL unit emits for it }
    Result := DarwinSym(ADecl.ExternalName)
  else if (ADecl <> nil) and (ADecl.ResolvedQbeName <> '') then
    Result := DarwinSym(CodegenMangle(ADecl.ResolvedQbeName))
  else if ADecl <> nil then
    Result := DarwinSym(CodegenMangle(ADecl.Name))
  else
    Result := DarwinSym(CodegenMangle(AName));
end;

function TArm64Backend.ItabBaseName(const AName: string): string;
begin
  { an interface variable's itab half ('X_itab') is no symbol of its own:
    it belongs to -- and resolves through -- the variable X }
  Result := AName;
  if (Length(AName) > 5) and
     (Copy(AName, Length(AName) - 5, 5) = '_itab') then
    Result := Copy(AName, 0, Length(AName) - 5);
end;

function TArm64Backend.IsSymTableVar(const AName: string): Boolean;
var
  Sym: TSymbol;
begin
  { a variable the symbol table knows -- a cross-unit global defined in a
    dependency's object; an itab half counts as its variable }
  Result := False;
  if FSymTable = nil then Exit;
  Sym := FSymTable.Lookup(ItabBaseName(AName));
  Result := (Sym <> nil) and (Sym.Kind = skVariable);
end;

function TArm64Backend.GlobalSym(const AName: string): string;
var
  Sym: TSymbol;
  Owner, Base: string;
begin
  { Owner resolution mirrors TX86_64Backend.GlobalSymName: an exported
    unit var carries its OwningUnit in the symbol table; an implementation-
    private one is invisible to Lookup and only ever referenced from its
    own unit, so the emitting unit is the owner.  The program name (and
    unmangled RTL units, via MangleUnitPrefix) map to a bare name. }
  Result := AName;
  Owner := '';
  Base := ItabBaseName(AName);
  if FSymTable <> nil then
  begin
    Sym := FSymTable.Lookup(Base);
    if (Sym <> nil) and (Sym.Kind = skVariable) and (Sym.OwningUnit <> '') then
      Owner := Sym.OwningUnit;
  end;
  if (Owner = '') and (FModuleVarNames.IndexOf(Base) >= 0) then
    Owner := FCurrentUnitName;
  if Owner = '' then Exit;
  if (FProgramName <> '') and SameText(Owner, FProgramName) then Exit;
  Result := MangleUnitPrefix(Owner) + AName;
end;

procedure TArm64Backend.RegisterGlobalInit(const ASym: string; AVD: TVarDecl);
var
  SAT: TStaticArrayTypeDesc;
  ElemDir, Lines, ElemSym: string;
  J: Integer;
begin
  { Integer, float, string and static-array initialisers become .data
    entries; const-expression initialisers stay honest holes. }
  if AVD.InitConst.ConstParts <> nil then
    NotYet('initialised global of this form', AVD);
  if AVD.InitConst.IsArrayConst then
  begin
    if (AVD.ResolvedType = nil) or
       (AVD.ResolvedType.Kind <> tyStaticArray) then
      NotYet('initialised global of this form', AVD);
    { multi-dim const arrays are nested static-array types: the directive
      is governed by the INNERMOST scalar element and the flat row-major
      element list already matches the contiguous layout }
    SAT := TStaticArrayTypeDesc(AVD.ResolvedType);
    while (SAT.ElementType <> nil) and
          (SAT.ElementType.Kind = tyStaticArray) do
      SAT := TStaticArrayTypeDesc(SAT.ElementType);
    if SAT.ElementType = nil then
      NotYet('initialised global of this form', AVD);
    Lines := '';
    if SAT.ElementType.Kind = tyString then
    begin
      { each element points at its own immortal blob — .quad takes a bare
        symbol only (no addend arithmetic), so the _d label sits AT the
        element's data, same scheme as scalar string globals }
      for J := 0 to AVD.InitConst.ArrayElements.Count - 1 do
      begin
        ElemSym := Format('%s_e%d', [ASym, J]);
        FGlobalStrInits.Add(ElemSym);
        FGlobalStrVals.Add(AVD.InitConst.ArrayElements.Strings[J]);
        if J > 0 then Lines := Lines + #10;
        Lines := Lines + Format(#9'.quad __gi_%s_d', [ElemSym]);
      end;
      FGlobalInits.Add(ASym, Lines);
      Exit;
    end;
    case SAT.ElementType.Kind of
      tyByte, tyBoolean: ElemDir := #9'.byte ';
      tySmallInt, tyWord: ElemDir := #9'.hword ';
      tyInt64, tyUInt64, tyPointer, tyPChar: ElemDir := #9'.quad ';
      tyDouble: ElemDir := #9'.double ';
      tySingle: ElemDir := #9'.float ';
    else
      ElemDir := #9'.word ';
    end;
    for J := 0 to AVD.InitConst.ArrayElements.Count - 1 do
    begin
      if J > 0 then Lines := Lines + #10;
      Lines := Lines + ElemDir + AVD.InitConst.ArrayElements.Strings[J];
    end;
    FGlobalInits.Add(ASym, Lines);
    Exit;
  end;
  if AVD.InitConst.IsString then
  begin
    { the global points at an immortal blob emitted beside the .data
      entry; program-exit _StringRelease is a no-op on refcnt -1 }
    FGlobalStrInits.Add(ASym);
    FGlobalStrVals.Add(AVD.InitConst.StrVal);
    FGlobalInits.Add(ASym, Format(#9'.quad __gi_%s_d', [ASym]));
    Exit;
  end;
  if AVD.InitConst.IsFloat then
    FGlobalInits.Add(ASym, #9'.double ' + AVD.InitConst.StrVal)
  else
    FGlobalInits.Add(ASym, Format(#9'.quad %d', [AVD.InitConst.IntVal]));
end;

procedure TArm64Backend.EmitSmallSetLiteral(AExpr: TArrayLiteralExpr);
var
  Mask: Int64;
  I: Integer;
  Elem: TASTExpr;
  HasRuntime: Boolean;
begin
  { small set (<= 64 members): compile-time members fold into an
    immediate mask; runtime members OR their bit in afterwards }
  Mask := 0;
  HasRuntime := False;
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    Elem := TASTExpr(AExpr.Elements.Items[I]);
    if Elem is TIntLiteral then
      Mask := Mask or (Int64(1) shl TIntLiteral(Elem).Value)
    else if (Elem is TIdentExpr) and TIdentExpr(Elem).IsConstant then
      Mask := Mask or (Int64(1) shl TIdentExpr(Elem).ConstValue)
    else
      HasRuntime := True;
  end;
  EmitIntLiteral('x0', Mask);
  if not HasRuntime then Exit;
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    Elem := TASTExpr(AExpr.Elements.Items[I]);
    if (Elem is TIntLiteral) or
       ((Elem is TIdentExpr) and TIdentExpr(Elem).IsConstant) then
      Continue;
    EmitPushX0();
    Self.EmitExprToX0(Elem);
    Self.Emit(#9'mov x1, x0');
    EmitPopTo('x0');
    Self.Emit(#9'movz x2, #1');
    Self.Emit(#9'lsl x2, x2, x1');
    Self.Emit(#9'orr x0, x0, x2');
  end;
end;

procedure TArm64Backend.EmitJumboSetOp(ABE: TBinaryExpr);
var
  NBytes, NL, NR: Integer;
  ARef: string;
begin
  { Jumbo set operators.  A jumbo set VALUE is its bitmap ADDRESS (in x0), so
    both operands evaluate to pointers and every operator is an RTL call.

    The two operand evaluations must not clobber each other, and either may
    itself lower sp (a jumbo LITERAL operand materialises a stack buffer and
    leaves sp lowered — see EmitJumboSetLiteral's contract).  So the LEFT
    address is parked on the stack across the right-hand evaluation, exactly
    as the membership path does -- and, like that path, it is read back from
    ABOVE a right-hand literal's buffer ([sp, #NR]), not popped from [sp],
    which would take the literal's first bitmap word as the left address.
    Both literal buffers stay live until the RTL call returns and are then
    released together with the parked slot. }
  NBytes := TSetTypeDesc(ABE.Left.ResolvedType).RawByteSize();
  NL := JumboSetLiteralBytes(ABE.Left);
  NR := JumboSetLiteralBytes(ABE.Right);

  Self.EmitExprToX0(ABE.Left);
  EmitPushX0();                         { park A across the right eval }
  Self.EmitExprToX0(ABE.Right);         { x0 = B }
  { with no right-hand literal the parked A is on top: pop it (the common
    shape, no separate sp adjustment); otherwise read it above the literal }
  if NR = 0 then
    ARef := '[sp], #16'
  else
    ARef := Format('[sp, #%d]', [NR]);

  if ABE.Op in [boEQ, boNE] then
  begin
    Self.Emit(#9'mov x1, x0');          { B }
    Self.Emit(#9'ldr x0, ' + ARef);     { A }
    EmitIntLiteral('x2', NBytes);
    EmitCallSym('_SetEqual');
    if ABE.Op = boNE then
      Self.Emit(#9'eor x0, x0, #1');
  end
  else if ABE.Op in [boLE, boGE] then
  begin
    { _SetSubset(A, B) tests "A is a subset of B".  For >= the operands swap. }
    if ABE.Op = boLE then
    begin
      Self.Emit(#9'mov x1, x0');        { B }
      Self.Emit(#9'ldr x0, ' + ARef);   { A }
    end
    else
      { A becomes the B-arg; x0 (the right operand) is the A-arg }
      Self.Emit(#9'ldr x1, ' + ARef);
    EmitIntLiteral('x2', NBytes);
    EmitCallSym('_SetSubset');
  end
  else
  begin
    { Union / intersection / difference produce a NEW bitmap, so they need a
      destination buffer.  That buffer is a FIXED x29-relative FRAME slot
      (_jset_scratch), NOT a fresh sp-lowering the way a literal does.

      This distinction is the whole design, and getting it wrong is a stack
      leak: an OPERATOR can sit inside a loop, and `sub sp` per evaluation
      never gets an `add sp` back — measured at 16 bytes per iteration before
      this was changed to a frame slot, i.e. 1.6 MB over a 100k-iteration
      loop, ending in a stack overflow.  A frame slot is allocated once per
      frame and reused, so a loop costs nothing.  It also sidesteps
      sp-relative addressing entirely, which is what the __strtrans park-slot
      comment in ReservePendRelSlots warns about. }
    Self.Emit(#9'mov x2, x0');          { B }
    Self.Emit(#9'ldr x1, ' + ARef);     { A }
    EmitSlotAddr('x0', '_jset_scratch');  { Dest — stable, x29-relative }
    EmitIntLiteral('x3', NBytes);
    case ABE.Op of
      boAdd: EmitCallSym('_SetUnion');
      boMul: EmitCallSym('_SetInter');
      boSub: EmitCallSym('_SetDiff');
    end;
    EmitSlotAddr('x0', '_jset_scratch');  { the result bitmap's address }
  end;
  { drop the right literal's buffer, the parked A (unless it was popped)
    and the left literal's buffer (x0 holds the result, untouched) }
  if NR > 0 then
    EmitAddSubImm('add', 'sp', 'sp', NR + 16 + NL)
  else if NL > 0 then
    EmitAddSubImm('add', 'sp', 'sp', NL);
end;

procedure TArm64Backend.EmitJumboSetLiteral(AExpr: TArrayLiteralExpr);
var
  I, NBytes: Integer;
  Elem: TASTExpr;
begin
  { jumbo set literal (>64 members): materialise the bitmap in a fresh
    16-byte-aligned stack buffer at [sp], memset 0, then _SetInclude each
    member's ordinal.  On return x0 = the bitmap address and sp has been
    LOWERED by NBytes — the CALLER owns the buffer and MUST restore sp
    (add sp, sp, #NBytes) once it has consumed the address.  This keeps
    the buffer alive across the membership/assignment read without leaking
    the frame.  Element evaluation must not itself move sp permanently
    (guaranteed: EmitExprToX0 balances its own brackets). }
  NBytes := (TSetTypeDesc(AExpr.ResolvedType).RawByteSize() + 15)
            and (not 15);
  EmitAddSubImm('sub', 'sp', 'sp', NBytes);
  Self.Emit(#9'mov x0, sp');
  Self.Emit(#9'movz x1, #0');
  EmitIntLiteral('x2', NBytes);
  EmitCallSym('memset');
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    Elem := TASTExpr(AExpr.Elements.Items[I]);
    Self.EmitExprToX0(Elem);       { ordinal in x0 }
    Self.Emit(#9'mov x1, x0');
    Self.Emit(#9'mov x0, sp');     { bitmap address (sp unmoved by eval) }
    EmitCallSym('_SetInclude');
  end;
  Self.Emit(#9'mov x0, sp');       { return the bitmap address }
end;

function TArm64Backend.IsJumboSetType(AType: TTypeDesc): Boolean;
begin
  Result := (AType is TSetTypeDesc) and TSetTypeDesc(AType).IsJumbo();
end;

function TArm64Backend.JumboSetLiteralBytes(AExpr: TASTExpr): Integer;
begin
  { the sp delta EmitJumboSetLiteral consumed, for the caller's restore }
  Result := 0;
  if (AExpr is TArrayLiteralExpr) and (AExpr.ResolvedType <> nil) and
     (AExpr.ResolvedType.Kind = tySet) and
     TSetTypeDesc(AExpr.ResolvedType).IsJumbo() then
    Result := (TSetTypeDesc(AExpr.ResolvedType).RawByteSize() + 15)
              and (not 15);
end;

procedure TArm64Backend.EmitStaticElemAddr(ASub: TStringSubscriptExpr);
var
  ESz: Integer;
begin
  { x0 := &base[index].  The base must be a plain local/global array
    identifier or an array CONST (semantic hands us its data label);
    chained/field bases stay NotYet. }
  ESz := TStaticArrayTypeDesc(
    ASub.StrExpr.ResolvedType).ElementType.RawSize();
  if not (ASub.StrExpr is TIdentExpr) or
     (TIdentExpr(ASub.StrExpr).ParamMode = pmVar) then
  begin
    { any other base -- an element of an outer array (G[I][J], the
      desugared G[I, J]), an array field, P^, a var array parameter: the
      base is the inner array's storage address }
    Self.EmitExprToX0(ASub.IndexExpr);
    if TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType).LowBound > 0 then
      EmitAddSubImm('sub', 'x0', 'x0',
        TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType).LowBound)
    else if TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType).LowBound < 0 then
      EmitAddSubImm('add', 'x0', 'x0',
        -TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType).LowBound);
    EmitPushX0();
    EmitArrayStorageAddr(ASub.StrExpr);
    EmitPopTo('x1');
    EmitIntLiteral('x2', ESz);
    Self.Emit(#9'mul x1, x1, x2');
    Self.Emit(#9'add x0, x0, x1');
    Exit;
  end;
  Self.EmitExprToX0(ASub.IndexExpr);
  { const arrays are 1-low sometimes (array[1..12]) — the semantic pass
    keeps the declared bounds, so subtract the low bound }
  if TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType).LowBound <> 0 then
  begin
    EmitIntLiteral('x1',
      TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType).LowBound);
    Self.Emit(#9'sub x0, x0, x1');
  end;
  EmitPushX0();
  if TIdentExpr(ASub.StrExpr).ConstArraySymbol <> '' then
  begin
    Self.Emit(Format(#9'adrp x0, %s@PAGE',
      [CodegenMangle(TIdentExpr(ASub.StrExpr).ConstArraySymbol)]));
    Self.Emit(Format(#9'add x0, x0, %s@PAGEOFF',
      [CodegenMangle(TIdentExpr(ASub.StrExpr).ConstArraySymbol)]));
  end
  else if TIdentExpr(ASub.StrExpr).IsImplicitSelf and
          (TIdentExpr(ASub.StrExpr).ImplicitFieldInfo <> nil) then
    { static-array FIELD of Self: the inline array storage is at Self+offset —
      EmitRecIdentAddr yields that address (no deref), like leg 14 (leg 16) }
    EmitRecIdentAddr('x0', TIdentExpr(ASub.StrExpr))
  else
    EmitSlotAddr('x0', TIdentExpr(ASub.StrExpr).Name);
  EmitPopTo('x1');
  EmitIntLiteral('x2', ESz);
  Self.Emit(#9'mul x1, x1, x2');
  Self.Emit(#9'add x0, x0, x1');
end;

procedure TArm64Backend.EmitArrayStorageAddr(AExpr: TASTExpr);
var
  Sub: TStringSubscriptExpr;
begin
  if AExpr is TIdentExpr then
  begin
    if TIdentExpr(AExpr).ConstArraySymbol <> '' then
    begin
      Self.Emit(Format(#9'adrp x0, %s@PAGE',
        [CodegenMangle(TIdentExpr(AExpr).ConstArraySymbol)]));
      Self.Emit(Format(#9'add x0, x0, %s@PAGEOFF',
        [CodegenMangle(TIdentExpr(AExpr).ConstArraySymbol)]));
    end
    else
      { frame/global slot, Self field, captured or var parameter }
      EmitRecIdentAddr('x0', TIdentExpr(AExpr));
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) then
  begin
    { an inner array that is itself an element: its storage IS the
      element's address }
    Sub := TStringSubscriptExpr(AExpr);
    case Sub.StrExpr.ResolvedType.Kind of
      tyStaticArray: EmitStaticElemAddr(Sub);
      tyDynArray, tyOpenArray: EmitDynElemAddr(Sub);
    else
      NotYet('array storage through this subscript base', AExpr);
    end;
    Exit;
  end;
  if AExpr is TFieldAccessExpr then
  begin
    EmitRecFieldAddrToX0(TFieldAccessExpr(AExpr));
    Exit;
  end;
  if AExpr is TDerefExpr then
  begin
    Self.EmitExprToX0(TDerefExpr(AExpr).Expr);
    Exit;
  end;
  NotYet('array storage of this expression', AExpr);
end;

procedure TArm64Backend.EmitDynElemAddr(ASub: TStringSubscriptExpr);
var
  ESz: Integer;
begin
  { x0 := dataptr + index*elemsize — the base VALUE is the element-0
    pointer (dyn-array header sits below it; an open-array param slot
    holds the caller's data pointer directly) }
  if ASub.StrExpr.ResolvedType.Kind = tyOpenArray then
    ESz := TOpenArrayTypeDesc(
      ASub.StrExpr.ResolvedType).ElementType.RawSize()
  else
    ESz := TDynArrayTypeDesc(
      ASub.StrExpr.ResolvedType).ElementType.RawSize();
  if not (ASub.StrExpr is TIdentExpr) then
  begin
    { a dyn array reached through an expression (an element of an outer
      array, a field): its VALUE is the data pointer -- a borrow, so an
      owned transient base would need a release }
    if ArcExprOwnsRef(ASub.StrExpr) then
      NotYet('subscript on an owned transient dyn array', ASub);
    Self.EmitExprToX0(ASub.IndexExpr);
    EmitPushX0();
    Self.EmitExprToX0(ASub.StrExpr);
    EmitPopTo('x1');
    EmitIntLiteral('x2', ESz);
    Self.Emit(#9'mul x1, x1, x2');
    Self.Emit(#9'add x0, x0, x1');
    Exit;
  end;
  Self.EmitExprToX0(ASub.IndexExpr);
  EmitPushX0();
  if TIdentExpr(ASub.StrExpr).IsImplicitSelf and
     (TIdentExpr(ASub.StrExpr).ImplicitFieldInfo <> nil) then
  begin
    { dyn-array FIELD of Self: the data pointer sits at Self + offset }
    EmitLoadSlot('x0', 'Self');
    Self.Emit(Format(#9'ldr x0, [x0, #%d]',
      [TFieldInfo(TIdentExpr(ASub.StrExpr).ImplicitFieldInfo).Offset]));
  end
  else if IsCaptured(TIdentExpr(ASub.StrExpr).Name) then
  begin
    { captured: '_cap_' holds the storage address (a var param's storage
      holds the caller's address, one more deref); the data pointer is the
      value stored there }
    EmitLoadSlot('x0', '_cap_' + TIdentExpr(ASub.StrExpr).Name);
    if (TIdentExpr(ASub.StrExpr).ParamMode = pmVar) and
       (ASub.StrExpr.ResolvedType.Kind <> tyOpenArray) then
      Self.Emit(#9'ldr x0, [x0]');
    Self.Emit(#9'ldr x0, [x0]');
  end
  else
  begin
    EmitLoadSlot('x0', TIdentExpr(ASub.StrExpr).Name);
    { a var dyn-array parameter's slot holds the caller variable's address;
      a var OPEN array is still the plain (data, high) pair -- its slot
      already holds the element-0 pointer }
    if (TIdentExpr(ASub.StrExpr).ParamMode = pmVar) and
       (ASub.StrExpr.ResolvedType.Kind <> tyOpenArray) then
      Self.Emit(#9'ldr x0, [x0]');
  end;
  EmitPopTo('x1');
  EmitIntLiteral('x2', ESz);
  Self.Emit(#9'mul x1, x1, x2');
  Self.Emit(#9'add x0, x0, x1');
end;

procedure TArm64Backend.EmitFieldElemAddr(AFAE: TFieldAccessExpr);
var
  ESz, LowB: Integer;
begin
  { x0 := address of AFAE (an array-typed field element: Obj.Arr[I]).
    Mirrors x86-64 @Rec.Arr[I] (:9765-9827).  First materialise the record/
    instance BASE into x0, then add the field offset, then add the scaled
    (low-bound-adjusted) index.  A CLASS base must be DEREFED to the instance
    pointer BEFORE adding the field offset (the QBE trap: adding the offset to
    the slot address yields a garbage pointer). }
  if AFAE.FieldInfo = nil then
    NotYet('address of an array-field element with no field info', AFAE);
  { --- base into x0 --- }
  if (AFAE.Base <> nil) and (AFAE.Base.ResolvedType <> nil) and
     (AFAE.Base.ResolvedType.Kind = tyRecord) then
    { a RECORD-valued chained base (c.N.A[I] -- a record field of a class,
      O.Ora[X].Arr[C] -- a record element): its ADDRESS }
    EmitRecAddrToX0(AFAE.Base)
  else if AFAE.Base <> nil then
    Self.EmitExprToX0(AFAE.Base)                 { chained receiver }
  else if AFAE.IsImplicitSelf then
  begin
    { Self, stepped across the intermediate field (FInner.Arr[I]):
      EmitImplicitBaseStep already DEREFERENCES a class-typed intermediate.
      A further `ldr` for IsClassAccess loaded the instance's vtable word as
      the base, so @FInner.Arr[1] / FInner.Arr[1] read garbage silently --
      EmitRecFieldAddrToX0 composes the same shape without it. }
    EmitLoadSlot('x0', 'Self');
    EmitImplicitBaseStep('x0', TFieldInfo(AFAE.ImplicitBaseInfo));
  end
  else if AFAE.IsClassAccess then
  begin
    { the instance POINTER lives in the field's owner slot (captured -> _cap_,
      var-param -> extra deref); EmitCapturedBase handles both, else bare load }
    if not EmitCapturedBase('x0', AFAE.RecordName, True, AFAE.IsVarParam) then
    begin
      EmitLoadSlot('x0', AFAE.RecordName);
      if AFAE.IsVarParam then
        Self.Emit(#9'ldr x0, [x0]');   { var-param class: slot -> instance }
    end;
  end
  else
    { TRUE var record → deref slot to caller addr; by-value/local/global record
      → EmitSlotAddr (the '__pptr_' discriminator keeps a by-value param off the
      double-deref path). }
    EmitRecordBaseAddr('x0', AFAE.RecordName, AFAE.IsVarParam);
  { --- add field offset --- }
  if AFAE.FieldInfo.Offset <> 0 then
    EmitAddSubImm('add', 'x0', 'x0', AFAE.FieldInfo.Offset);
  { --- scale + add index (park base across index eval, which may clobber x0) --- }
  if AFAE.FieldInfo.TypeDesc.Kind = tyStaticArray then
  begin
    ESz := TStaticArrayTypeDesc(AFAE.FieldInfo.TypeDesc).ElementType.RawSize();
    LowB := TStaticArrayTypeDesc(AFAE.FieldInfo.TypeDesc).LowBound;
  end
  else if AFAE.FieldInfo.TypeDesc.Kind = tyDynArray then
  begin
    Self.Emit(#9'ldr x0, [x0]');   { dyn-array field: deref the data pointer }
    ESz := TDynArrayTypeDesc(AFAE.FieldInfo.TypeDesc).ElementType.RawSize();
    LowB := 0;
  end
  else if AFAE.FieldInfo.TypeDesc.Kind = tyOpenArray then
  begin
    Self.Emit(#9'ldr x0, [x0]');
    ESz := TOpenArrayTypeDesc(AFAE.FieldInfo.TypeDesc).ElementType.RawSize();
    LowB := 0;
  end
  else
    NotYet('address of a non-array field element', AFAE);
  EmitPushX0();                                    { park base }
  Self.EmitExprToX0(AFAE.PropIndexExpr);           { index -> x0 }
  if LowB <> 0 then
  begin
    EmitIntLiteral('x1', LowB);
    Self.Emit(#9'sub x0, x0, x1');
  end;
  EmitIntLiteral('x2', ESz);
  Self.Emit(#9'mul x0, x0, x2');
  EmitPopTo('x1');                                 { base }
  Self.Emit(#9'add x0, x0, x1');
end;

procedure TArm64Backend.EmitElemLoad(AElem: TTypeDesc);
begin
  { load the element at [x0] into x0, width by element kind.  Signed
    2-byte loads need ldrsh (no assembler encoding yet) — NotYet. }
  if AElem = nil then NotYet('unresolved element type', nil);
  case AElem.RawSize() of
    1: Self.Emit(#9'ldrb w0, [x0]');
    2:
    begin
      Self.Emit(#9'ldrh w0, [x0]');
      { no ldrsh in the internal assembler: sign-extend a SmallInt with the
        shift pair, as EmitNormaliseNarrowSlot does (a Word or a 2-byte set
        bitmask stays zero-extended) }
      if AElem.Kind = tySmallInt then
      begin
        Self.Emit(#9'lsl x0, x0, #48');
        Self.Emit(#9'asr x0, x0, #48');
      end;
    end;
    4:
      if (AElem.Kind = tyUInt32) or (AElem.Kind = tySet) then
        { unsigned / bitmask: zero-extend (a sign-extended set with bit 31
          set would compare unequal to the same set built in a register) }
        Self.Emit(#9'ldr w0, [x0]')
      else if AElem.Kind = tySingle then
        Self.Emit(#9'ldr w0, [x0]')
      else
        Self.Emit(#9'ldrsw x0, [x0]');
    8: Self.Emit(#9'ldr x0, [x0]');
    16:
      if AElem.Kind = tyInterface then
        { an interface value in a scalar context (I <> nil, Assigned) is its
          obj half; the itab rides along in x1 for a pair consumer }
        Self.Emit(#9'ldp x0, x1, [x0]')
      else
        NotYet(Format('array element of this width (%d bytes, %s)',
          [AElem.RawSize(), AElem.Name]), nil);
  else
    NotYet(Format('array element of this width (%d bytes, %s)',
      [AElem.RawSize(), AElem.Name]), nil);
  end;
end;

function TArm64Backend.AggHasManaged(AType: TTypeDesc): Boolean;
begin
  { Delegates to the shared ARC content walk (records: any managed field
    INCLUDING static-array-of-managed fields since BUG-017; static arrays:
    managed content at any nesting depth).  The previous local version used
    RecretManagedClean, which at the time ignored static-array fields — that
    would let the retain-side walks (record copy / param entry) retain
    elements this gate then never released.  (RecretManagedClean has since
    grown a tyStaticArray arm delegating to this same walk —
    BUG-20260721-recretclean-static-array-of-managed — so the two now agree;
    the delegation here is kept for the direct any-type entry point.) }
  Result := ArcTypeHasManagedContent(AType) and
            (AType.Kind in [tyRecord, tyStaticArray]);
end;

function TArm64Backend.RecReturnShape(ARec: TRecordTypeDesc): Integer;
var
  I, NDoubles: Integer;
  F: TFieldInfo;
  AllDouble: Boolean;
begin
  { HFA check first: up to four Double fields return in d0..d(N-1) —
    AAPCS64's homogeneous float aggregate rule.  (Single-member HFAs are
    rejected with the rest of Single support.) }
  AllDouble := ARec.Fields.Count > 0;
  NDoubles := 0;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if (F.TypeDesc = nil) or (F.TypeDesc.Kind <> tyDouble) then
      AllDouble := False
    else
      NDoubles := NDoubles + 1;
  end;
  if AllDouble and (NDoubles <= 4) then
  begin
    Result := 100 + NDoubles;
    Exit;
  end;
  case Self.ClassifyRecordReturn(ARec) of
    rcSret: Result := 0;
    rcInt1: Result := 1;
  else
    { rcInt2 / rcIntSSE / rcSSEInt / rcSSE2: any non-HFA composite of at
      most 16 bytes returns as a MEMORY IMAGE in x0:x1 on AAPCS64 (no
      per-eightbyte class split like System V). }
    Result := 2;
  end;
end;

procedure TArm64Backend.RegisterForSlots(AStmt: TASTStmt);
var
  I: Integer;
begin
  if AStmt = nil then Exit;
  if AStmt is TCompoundStmt then
  begin
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      RegisterForSlots(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TForStmt then
  begin
    AddLocal('__for_end_' + IntToStr(FForN), 8);
    FForN := FForN + 1;
    RegisterForSlots(TForStmt(AStmt).Body);
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    RegisterForSlots(TIfStmt(AStmt).ThenStmt);
    RegisterForSlots(TIfStmt(AStmt).ElseStmt);
    Exit;
  end;
  if AStmt is TWhileStmt then
  begin
    RegisterForSlots(TWhileStmt(AStmt).Body);
    Exit;
  end;
  if AStmt is TRepeatStmt then
  begin
    for I := 0 to TRepeatStmt(AStmt).Body.Stmts.Count - 1 do
      RegisterForSlots(TASTStmt(TRepeatStmt(AStmt).Body.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      RegisterForSlots(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt);
    RegisterForSlots(TCaseStmt(AStmt).ElseStmt);
    Exit;
  end;
  if AStmt is TForInStmt then
  begin
    RegisterForSlots(TForInStmt(AStmt).Body);
    Exit;
  end;
  { try bodies can hold for statements too — skipping them here would
    pair registration and emission on DIFFERENT walk orders and make two
    loops share one hidden end slot (silent wrong code, not a NotYet) }
  if AStmt is TTryFinallyStmt then
  begin
    RegisterForSlots(TTryFinallyStmt(AStmt).TryBody);
    RegisterForSlots(TTryFinallyStmt(AStmt).FinallyBody);
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    RegisterForSlots(TTryExceptStmt(AStmt).TryBody);
    for I := 0 to TTryExceptStmt(AStmt).Handlers.Count - 1 do
      RegisterForSlots(TExceptHandlerClause(
        TTryExceptStmt(AStmt).Handlers.Items[I]).Body);
    RegisterForSlots(TTryExceptStmt(AStmt).ElseBody);
    RegisterForSlots(TTryExceptStmt(AStmt).ExceptBody);
  end;
end;

function TArm64Backend.MaxManagedRecRet(AStmt: TASTStmt): Integer;
var
  I, N: Integer;
  Elem: TTypeDesc;
begin
  { largest RawSize among managed-record-returning call assignments — the
    caller routes those through a __rret scratch so the LHS's old field
    refs can be released AFTER the callee produced the fresh value }
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TAssignment then
  begin
    if (TAssignment(AStmt).ResolvedLhsType <> nil) and
       (TAssignment(AStmt).ResolvedLhsType.Kind = tyRecord) and
       ((TAssignment(AStmt).Expr is TFuncCallExpr) or
        (TAssignment(AStmt).Expr is TMethodCallExpr)) and
       (not RecretManagedClean(
          TRecordTypeDesc(TAssignment(AStmt).ResolvedLhsType)) or
        (TAssignment(AStmt).ImplicitSelfField <> nil)) then
      Result := TAssignment(AStmt).ResolvedLhsType.RawSize();
    Exit;
  end;
  if AStmt is TFieldAssignment then
  begin
    { Rec.Field := <record-returning call> sret's the call into __rret then
      memcpies into the field — size __rret to the field's record type }
    if (TFieldAssignment(AStmt).FieldInfo <> nil) and
       (TFieldAssignment(AStmt).FieldInfo.TypeDesc <> nil) and
       (TFieldAssignment(AStmt).FieldInfo.TypeDesc.Kind = tyRecord) and
       IsRecordCallArg(TFieldAssignment(AStmt).Expr) then
      Result := TFieldAssignment(AStmt).FieldInfo.TypeDesc.RawSize();
    Exit;
  end;
  if AStmt is TStaticSubscriptAssign then
  begin
    { Arr[I] := <record-returning call> sret's the call into __rret then
      memcpies into the element — size __rret to the element's record type }
    if (TStaticSubscriptAssign(AStmt).ResolvedArrayType <> nil) and
       (TStaticSubscriptAssign(AStmt).ResolvedArrayType.Kind in
         [tyStaticArray, tyDynArray]) and
       IsRecordCallArg(TStaticSubscriptAssign(AStmt).ValueExpr) then
    begin
      if TStaticSubscriptAssign(AStmt).ResolvedArrayType.Kind =
           tyStaticArray then
        Elem := TStaticArrayTypeDesc(
          TStaticSubscriptAssign(AStmt).ResolvedArrayType).ElementType
      else
        Elem := TDynArrayTypeDesc(
          TStaticSubscriptAssign(AStmt).ResolvedArrayType).ElementType;
      if (Elem <> nil) and (Elem.Kind = tyRecord) then
        Result := Elem.RawSize();
    end;
    Exit;
  end;
  if AStmt is TCompoundStmt then
  begin
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
    begin
      N := MaxManagedRecRet(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]));
      if N > Result then Result := N;
    end;
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    Result := MaxManagedRecRet(TIfStmt(AStmt).ThenStmt);
    N := MaxManagedRecRet(TIfStmt(AStmt).ElseStmt);
    if N > Result then Result := N;
    Exit;
  end;
  if AStmt is TWhileStmt then
    Result := MaxManagedRecRet(TWhileStmt(AStmt).Body)
  else if AStmt is TForStmt then
    Result := MaxManagedRecRet(TForStmt(AStmt).Body)
  else if AStmt is TRepeatStmt then
  begin
    for I := 0 to TRepeatStmt(AStmt).Body.Stmts.Count - 1 do
    begin
      N := MaxManagedRecRet(TASTStmt(TRepeatStmt(AStmt).Body.Stmts.Items[I]));
      if N > Result then Result := N;
    end;
  end
  else if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
    begin
      N := MaxManagedRecRet(
        TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt);
      if N > Result then Result := N;
    end;
    N := MaxManagedRecRet(TCaseStmt(AStmt).ElseStmt);
    if N > Result then Result := N;
  end
  else if AStmt is TForInStmt then
    Result := MaxManagedRecRet(TForInStmt(AStmt).Body)
  else if AStmt is TTryFinallyStmt then
  begin
    { an undersized __rret for an assignment inside a try body would be a
      silent buffer overflow, not a NotYet — walk try bodies too }
    Result := MaxManagedRecRet(TTryFinallyStmt(AStmt).TryBody);
    N := MaxManagedRecRet(TTryFinallyStmt(AStmt).FinallyBody);
    if N > Result then Result := N;
  end
  else if AStmt is TTryExceptStmt then
  begin
    Result := MaxManagedRecRet(TTryExceptStmt(AStmt).TryBody);
    for I := 0 to TTryExceptStmt(AStmt).Handlers.Count - 1 do
    begin
      N := MaxManagedRecRet(TExceptHandlerClause(
        TTryExceptStmt(AStmt).Handlers.Items[I]).Body);
      if N > Result then Result := N;
    end;
    N := MaxManagedRecRet(TTryExceptStmt(AStmt).ElseBody);
    if N > Result then Result := N;
    N := MaxManagedRecRet(TTryExceptStmt(AStmt).ExceptBody);
    if N > Result then Result := N;
  end;
end;

procedure TArm64Backend.RegisterFrameSlots(ADecl: TMethodDecl; ABody: TBlock);
var
  I, J: Integer;
  VD: TVarDecl;
  Par: TMethodParam;
begin
  FFrame.Clear();
  FFrameSize := 0;
  FStrLocals.Clear();
  FRecLocals.Clear();
  FByValRecParams.Clear();
  FObjLocals.Clear();
  FWeakLocals.Clear();
  FIntfLocals.Clear();
  FDynLocals.Clear();
  FRefLocals.Clear();
  if ADecl <> nil then
  begin
    { Captured outer-scope vars (leg 17): each gets a pointer-size '_cap_<Name>'
      slot holding &<Name>, filled from a hidden leading register param in the
      prologue.  A nested routine that captured the enclosing METHOD's Self also
      gets a REAL 'Self' slot (BUG-008 parity), filled by loading through
      _cap_Self, so every hardcoded implicit-Self path works unchanged.
      Mirrors x86-64 BuildFrame (:5502-5516). }
    if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
    begin
      for I := 0 to ADecl.CapturedVars.Count - 1 do
        AddLocal('_cap_' + ADecl.CapturedVars.Strings[I], 8);
      if (ADecl.OwnerTypeName = '') and
         (ADecl.CapturedVars.IndexOf('Self') >= 0) then
        AddLocal('Self', 8);
    end;
    if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
      AddLocal('Self', 8);
    { Anonymous-method capture (Phase 2/3): the env base slot plus one
      '_cap_<Name>' pointer slot per name promoted into the env record --
      EmitEnvPrologue fills them.  The promoted locals keep their ordinary,
      now dead, slots (zero-init and the scope-exit release see nil there);
      every real access redirects through IsCaptured.  A thunk lifted from a
      method gets a REAL Self slot, filled from the env.  Mirrors x86-64. }
    if ADecl.EnvCaptured <> nil then
    begin
      AddLocal('__envp', 8);
      for I := 0 to ADecl.EnvCaptured.Count - 1 do
        if not IsLocal('_cap_' + ADecl.EnvCaptured.Strings[I]) then
          AddLocal('_cap_' + ADecl.EnvCaptured.Strings[I], 8);
      if ADecl.IsAnonThunk and (ADecl.EnvCaptured.IndexOf('Self') >= 0) and
         not IsLocal('Self') then
        AddLocal('Self', 8);
    end;
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      Par := TMethodParam(ADecl.Params.Items[I]);
      if Par.IsOpenArray then
      begin
        { open array (incl. 'array of const' = open array of TVarRec): the
          (data ptr, high index) pair is two 8-byte slots.  Elements are read
          through the pointer; the callee BORROWS the caller's storage (x86
          parity — no copy, no ARC on the slots).  TVarRec elements have a
          16-byte stride, which the subscript path derives from the record
          type, so no const-specific param setup is needed. }
        AddLocal(Par.ParamName, 8);
        AddLocal(Par.ParamName + '_high', 8);
        Continue;
      end;
      if Par.IsVarParam then
      begin
        { var/out param: the 8-byte slot holds the caller's ADDRESS.
          Record pointees are supported FIELD-WISE (assign/read deref the
          slot); whole-record stores into one stay NotYet.  A var CLASS
          pointee aliases the caller's class variable — reads deref twice
          (slot -> caller var -> instance), stores run ARC through the
          slot (release old, store new). }
        if not (IsIntFam(Par.ResolvedType) or
                ((Par.ResolvedType <> nil) and
                 (Par.ResolvedType.Kind in [tyDouble, tyString, tyRecord,
                                            tyClass, tyDynArray,
                                            tyPointer, tyPChar,
                                            tyMetaClass, tyInterface]))) then
          NotYet('var parameter ''' + Par.ParamName + ''' of this type', ADecl);
        AddLocal(Par.ParamName, 8);
        Continue;
      end;
      if (Par.ResolvedType <> nil) and
         (Par.ResolvedType.Kind = tyInterface) then
      begin
        { fat pointer: two int-class registers (obj, itab).  A BY-VALUE
          interface param is the callee's co-owning copy — retained in the
          prologue, obj half released at exit; const params borrow. }
        AddIntfLocal(Par.ParamName);
        if not Par.IsConstParam then
          FIntfLocals.Add(Par.ParamName);
        Continue;
      end;
      if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyRecord) then
      begin
        AddLocal(Par.ParamName, Par.ResolvedType.RawSize());
        FRecLocals.AddObject(Par.ParamName, Par.ResolvedType);
        { A true var/out param already Continue'd above, so every record param
          reaching here is BY VALUE — record that explicitly.  The semantic pass
          marks them all IsVarParam=True, and only a shape-0 param gets the
          '__pptr_' slot, so this list is what tells a field read/write that the
          slot holds the value inline rather than the caller's address. }
        FByValRecParams.Add(Par.ParamName);
        if RecReturnShape(TRecordTypeDesc(Par.ResolvedType)) = 0 then
          { >16B records arrive as a pointer; park it until the
            prologue memcpy pass copies the bytes into our own slot }
          AddLocal('__pptr_' + Par.ParamName, 8);
      end
      else if IsMethodPtrType(Par.ResolvedType) then
      begin
        { closure / method-pointer param: a 16-byte fat value (Code, Env/Self).
          It arrives as a POINTER to the caller's fat value in ONE integer
          register (the jumbo-set / record-by-pointer convention); the prologue
          memcpy pass copies the 16 bytes into our own slot via the '__pptr_'
          companion.  BORROW — a by-value closure param does not retain the env
          (matches x86-64/QBE), so it is NOT registered in FRefLocals. }
        AddLocal(Par.ParamName, 16);
        AddLocal('__pptr_' + Par.ParamName, 8);
      end
      else if (Par.ResolvedType is TSetTypeDesc) and
              TSetTypeDesc(Par.ResolvedType).IsJumbo() then
      begin
        { by-value JUMBO set param: an inline bitmap, passed by pointer like a
          closure (the caller snapshots it) and copied into our own slot by
          the prologue's pass 2, so writes in the callee stay local }
        AddLocal(Par.ParamName, Par.ResolvedType.RawSize());
        AddLocal('__pptr_' + Par.ParamName, 8);
      end
      else
      begin
        { a by-value CLASS param is one pointer; the callee holds its own
          reference to it (retained in the prologue, released at exit -- the
          caller keeps its own).  A PLAIN procedural param is one code
          pointer. }
        { A small set is a one-register bitmask and arrives like an integer;
          a JUMBO set has its own byte-array ABI and stays a hole — the same
          split the local-var and call-argument gates make. }
        if not (IsIntFam(Par.ResolvedType) or
                ((Par.ResolvedType <> nil) and
                 (Par.ResolvedType.Kind in [tyDouble, tySingle, tyString,
                                            tyClass, tyProcedural,
                                            tyPointer, tyPChar, tyDynArray,
                                            tyMetaClass]))
                or ((Par.ResolvedType <> nil) and
                    (Par.ResolvedType.Kind = tySet) and
                    not TSetTypeDesc(Par.ResolvedType).IsJumbo())) then
          NotYet('parameter ''' + Par.ParamName + ''' of this type', ADecl);
        AddLocal(Par.ParamName, 8);
        { a BY-VALUE string param is the callee's own copy: retained in the
          prologue, released with the string locals at scope exit.  A const
          string param is a borrow — no retain, no release. }
        if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyString)
           and not Par.IsConstParam then
          FStrLocals.Add(Par.ParamName);
        { a BY-VALUE dyn-array param is likewise the callee's own co-owning
          reference (both are 8-byte ref-counted pointers): retain it in the
          prologue and release it with the dyn-array locals at scope exit.  A
          const dyn-array param borrows — no ARC.  (x86-64/QBE currently omit
          this retain for by-value dyn-array params — a latent under-retain gap
          logged separately; arm64 does it correctly.) }
        if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyDynArray)
           and not Par.IsConstParam then
          FDynLocals.Add(Par.ParamName);
        { a BY-VALUE class param is the callee's own reference too (retained
          in the prologue -- see the retain loop for why) }
        if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyClass)
           and not Par.IsConstParam then
          FObjLocals.Add(Par.ParamName);
      end;
    end;
    if ADecl.ResolvedReturnType <> nil then
    begin
      if ADecl.ResolvedReturnType.Kind = tyRecord then
      begin
        { the field refs a record Result holds TRANSFER to the caller —
          Result deliberately stays out of the FRecLocals release walk }
        AddLocal('Result', ADecl.ResolvedReturnType.RawSize());
        if RecReturnShape(TRecordTypeDesc(ADecl.ResolvedReturnType)) = 0 then
          AddLocal('__sret', 8);   { the incoming x8 destination pointer }
      end
      else if IsMethodPtrType(ADecl.ResolvedReturnType) then
      begin
        { closure / method-pointer result: a 16-byte (Code, Env) Result,
          copied to the caller's x8 buffer at return.  Result stays out of
          the ref-local release walk: its Env reference TRANSFERS to the
          caller, exactly as an interface result's obj half does. }
        AddLocal('Result', 16);
        AddLocal('__sret', 8);
      end
      else if ADecl.ResolvedReturnType.Kind = tyInterface then
      begin
        { fat-pointer result: written to the caller's 16-byte x8 buffer
          at return; the +1 on the obj half transfers to the caller }
        AddIntfLocal('Result');
        AddLocal('__sret', 8);
      end
      else if IsJumboSetType(ADecl.ResolvedReturnType) then
      begin
        { a jumbo-set result: an inline bitmap Result, copied to the caller's
          x8 buffer at return (the large-record sret convention) }
        AddLocal('Result', ADecl.ResolvedReturnType.RawSize());
        AddLocal('__sret', 8);
      end
      else if not (IsIntFam(ADecl.ResolvedReturnType) or
                   (ADecl.ResolvedReturnType.Kind in [tyDouble, tySingle]) or
                   (ADecl.ResolvedReturnType.Kind in [tyString, tyClass,
                                                      tyPointer, tyPChar,
                                                      tyDynArray,
                                                      tyMetaClass]) or
                   { a small set is a one-register bitmask, returned in x0
                     like an integer (the zero-initialised 8-byte Result
                     slot keeps the bytes above its width clear) }
                   IsSmallSetType(ADecl.ResolvedReturnType)) then
        NotYet('function result of this type', ADecl)
      else
        { a string/class/dyn-array Result is a plain 8-byte pointer slot.
          It is deliberately NOT in FStrLocals/FObjLocals/FDynLocals: the +1
          it holds transfers to the caller at return (ArcExprOwnsRef treats
          call results as owned), so the scope-exit release must skip it.
          Nil-inited (5977) and returned via the generic x0 load (6085). }
        AddLocal('Result', 8);
    end;
  end;
  for I := 0 to ABody.Decls.Count - 1 do
  begin
    VD := TVarDecl(ABody.Decls.Items[I]);
    if not (IsIntFam(VD.ResolvedType) or
            ((VD.ResolvedType <> nil) and
             (VD.ResolvedType.Kind in [tyDouble, tySingle, tyString,
                                       tyRecord, tyClass, tyInterface,
                                       tyMetaClass, tyStaticArray,
                                       tyDynArray, tySet, tyPointer,
                                       tyPChar, tyProcedural]))) then
      NotYet('local variable of this type', VD);
    { A JUMBO set (> 64 members) is an inline byte-array bitmap, so its slot is
      sized from RawSize() -- see the jumbo arm below; it does NOT fall out of
      the generic 8-byte default.  The operations on it go through the _Set*
      RTL helpers. }
    for J := 0 to VD.Names.Count - 1 do
    begin
      if VD.ResolvedType.Kind in [tyRecord, tyStaticArray] then
      begin
        { managed fields/elements are fine: zero-init nils them, the
          base-class ARC walks handle the scope-exit release }
        AddLocal(VD.Names.Strings[J], VD.ResolvedType.RawSize());
        FRecLocals.AddObject(VD.Names.Strings[J], VD.ResolvedType);
      end
      else if IsMethodPtrType(VD.ResolvedType) then
        { closure / method-pointer local: a 16-byte fat value (Code, Env). }
        AddLocal(VD.Names.Strings[J], 16)
      else if VD.ResolvedType.Kind = tyInterface then
        AddIntfLocal(VD.Names.Strings[J])
      else if (VD.ResolvedType is TSetTypeDesc) and
              TSetTypeDesc(VD.ResolvedType).IsJumbo() then
        { a JUMBO set local holds its whole bitmap.  It used to fall to the
          8-byte default, so a 16-byte bitmap copied into the slot at x29-8
          overwrote the saved frame pointer }
        AddLocal(VD.Names.Strings[J], VD.ResolvedType.RawSize())
      else
        AddLocal(VD.Names.Strings[J], 8);
      if VD.ResolvedType.Kind = tyString then
        FStrLocals.Add(VD.Names.Strings[J]);
      { a 'reference to' closure local co-owns its Env — release it at scope
        exit (arkRefEnv); a method-pointer's Data half is a borrowed receiver. }
      if (VD.ResolvedType.Kind = tyProcedural) and
         TProceduralTypeDesc(VD.ResolvedType).IsReference then
        FRefLocals.Add(VD.Names.Strings[J]);
      if (VD.ResolvedType.Kind = tyClass) and not VD.IsWeak then
        FObjLocals.Add(VD.Names.Strings[J]);
      if VD.ResolvedType.Kind = tyDynArray then
        FDynLocals.Add(VD.Names.Strings[J]);
      if VD.ResolvedType.Kind = tyInterface then
      begin
        { fat pointer: split obj/itab slots; the obj half co-owns the
          backing instance (weak slots hold no ref — not released) }
        if not VD.IsWeak then
          FIntfLocals.Add(VD.Names.Strings[J]);
      end;
      { a weak slot holds no reference but IS registered in the weak table:
        it must be deregistered before the frame dies, or freeing the target
        later nils a dead stack slot }
      if VD.IsWeak and (VD.ResolvedType.Kind in [tyClass, tyInterface]) then
        FWeakLocals.Add(VD.Names.Strings[J]);
    end;
  end;
  { 16-byte scratch for interface-returning calls (sret target).  Always
    reserved — cheap, and avoids a body pre-scan. }
  AddLocal('__iret', 16);
  { __rret: scratch for record-returning calls whose result is consumed
    without an lvalue — the managed-record-assign path (sized by
    MaxManagedRecRet) AND record-call field reads (HostTarget().OS, sized
    to 16 for the register-return shapes; a >16B field-read-on-call is a
    guarded hole).  Always reserve at least 16 — cheap, avoids an
    expression pre-scan for the field-read case. }
  J := 16;
  for I := 0 to ABody.Stmts.Count - 1 do
    if MaxManagedRecRet(TASTStmt(ABody.Stmts.Items[I])) > J then
      J := MaxManagedRecRet(TASTStmt(ABody.Stmts.Items[I]));
  AddLocal('__rret', J);
  ReservePendRelSlots();   { BUG-048: statement-scoped deferred class releases }
  for I := 0 to ABody.Stmts.Count - 1 do
    RegisterForSlots(TASTStmt(ABody.Stmts.Items[I]));
end;

procedure TArm64Backend.EmitFunctionDef(ADecl: TMethodDecl;
  AWeakBind: Boolean);
var
  I, J, K, FIdx: Integer;
  SPOff, SPSz: Integer;
  SavedAsm, BodyBuf: TStringBuilder;
  FrameAligned: Integer;
  Sym: string;
  RecShape, ParShape: Integer;
  Par: TMethodParam;
begin
  Sym := RoutineSym(ADecl, ADecl.Name);
  { nostackframe: the body is an inline-asm block that owns the entire
    frame (prologue, args-from-registers, ret).  No compiler prologue/
    epilogue, no frame registration, no param spill, no ARC — the
    verbatim block only. }
  { RTL-owned routines bind WEAK (GH #180): a whole-program-per-unit
    build inlines dependency bodies into every importing object, so two
    objects may define the same bare RTL symbol — weak copies collapse
    at link.  _main stays strong: it is the LC_MAIN entry. }
  if (ADecl.OwningUnit <> '') and IsUnmangledUnit(ADecl.OwningUnit) and
     (Sym <> DarwinSym('main')) then
    AWeakBind := True;
  if ADecl.NoStackFrame then
  begin
    Self.Emit('');
    if AWeakBind then
      EmitWeakDef(Sym)
    else
      EmitGloblDef(Sym);
    Self.Emit(Sym + ':');
    EmitStmtList(ADecl.Body.Stmts);
    Exit;
  end;
  { Emit nested routines declared inside this body FIRST, as sibling
    top-level symbols mangled OuterName_InnerName (leg 17).  This runs
    before any of THIS routine's frame state is built, and each recursive
    call fully saves/restores the per-routine slot state at its own
    boundaries, so the outer emission that follows is unaffected.  The
    recursion handles multi-level nesting.  FCapturedVars is saved across
    the loop and re-pointed at THIS routine's own captures for the body
    emission below.  Mirrors x86-64 EmitFunctionDef (:20800-20812/:20841). }
  if ADecl.Body <> nil then
  begin
    for I := 0 to ADecl.Body.ProcDecls.Count - 1 do
    begin
      if TMethodDecl(ADecl.Body.ProcDecls.Items[I]).Body = nil then
        Continue;
      { Prefix the nested name with the outer routine's RESOLVED symbol, not
        its bare name (BUG-20260720-method-nested-proc-mangle): a method
        TFoo.DoIt has ResolvedQbeName 'TFoo_DoIt', so its nested Inner becomes
        'TFoo_DoIt_Inner' — distinct from TBar.DoIt's Inner — and a multi-level
        chain composes to 'L1_L2_L3' because the parent's ResolvedQbeName is
        already set when its children are derived.  Un-mangled name-space; the
        platform prefix is applied downstream at label emission. }
      if ADecl.ResolvedQbeName <> '' then
        TMethodDecl(ADecl.Body.ProcDecls.Items[I]).ResolvedQbeName :=
          ADecl.ResolvedQbeName + '_' +
          TMethodDecl(ADecl.Body.ProcDecls.Items[I]).Name
      else
        TMethodDecl(ADecl.Body.ProcDecls.Items[I]).ResolvedQbeName :=
          ADecl.Name + '_' + TMethodDecl(ADecl.Body.ProcDecls.Items[I]).Name;
      Self.EmitFunctionDef(
        TMethodDecl(ADecl.Body.ProcDecls.Items[I]), AWeakBind);
    end;
  end;
  FCapturedVars := ADecl.CapturedVars;
  FCurEnvCaptured := ADecl.EnvCaptured;
  if (ADecl.BlockEnvTypes <> nil) or (ADecl.BlockEnvCaptured <> nil) then
    NotYet('closure capture of a block-scoped variable', ADecl);
  if ADecl.EnvCaptured <> nil then
  begin
    { the routine's own nested-routine captures plus its env captures: both
      redirect through '_cap_<Name>' }
    FEnvCaps.Clear();
    if ADecl.CapturedVars <> nil then
      FEnvCaps.AddStrings(ADecl.CapturedVars);
    FEnvCaps.AddStrings(ADecl.EnvCaptured);
    FCapturedVars := FEnvCaps;
  end;
  FIsFunction := ADecl.ResolvedReturnType <> nil;
  FResultFloat := FIsFunction and
    (ADecl.ResolvedReturnType.Kind = tyDouble);
  FResultSingle := FIsFunction and
    (ADecl.ResolvedReturnType.Kind = tySingle);
  RecShape := -1;
  if FIsFunction and (ADecl.ResolvedReturnType.Kind = tyRecord) then
    RecShape := RecReturnShape(TRecordTypeDesc(ADecl.ResolvedReturnType));
  if FIsFunction and ((ADecl.ResolvedReturnType.Kind = tyInterface) or
                      IsMethodPtrType(ADecl.ResolvedReturnType) or
                      IsJumboSetType(ADecl.ResolvedReturnType)) then
    RecShape := 0;   { interface, closure and jumbo-set results use the x8
                       sret path }
  FExitLabel := NewLabel('rexit');
  FForN := 0;
  RegisterFrameSlots(ADecl, ADecl.Body);
  FForN := 0;   { reset so EmitFor consumes slots in registration order }
  FrameAligned := (FFrameSize + 15) and (not 15);

  Self.Emit('');
  if AWeakBind then
    EmitWeakDef(Sym)
  else
    EmitGloblDef(Sym);
  Self.Emit(Sym + ':');
  Self.Emit(#9'stp x29, x30, [sp, #-16]!');
  Self.Emit(#9'mov x29, sp');
  { the rest is buffered so try statements can lazily grow the frame —
    the frame-reserve sub is written with the FINAL size (BUG-045 lesson:
    never pre-count exception frames from source) }
  SavedAsm := FAsm;
  BodyBuf := TStringBuilder.Create();
  FAsm := BodyBuf;
  FExcDepth := 0;
  FExcSlotN := 0;
  FFinallyBodies.Clear();
  FLoopExcDepth.Clear();
  { spill register args to their slots.  Integer and float parameters
    consume INDEPENDENT register sequences (x0.. / d0..) per AAPCS64;
    floats hop through x9 so the slot store machinery stays uniform. }
  J := 0;      { int register index }
  FIdx := 0;   { float register index }
  SPOff := 0;  { caller outgoing-area offset for stack params }
  { Captured-var pointer params arrive FIRST in x0.. (leg 17): spill each into
    its '_cap_<Name>' slot, then a captured method Self is loaded through
    _cap_Self into the real 'Self' slot.  Captures precede sret/Self/normal
    params, shifting them right — mirrors x86-64 EmitFunctionCore (:21005-21025).
    A leg-17 nested routine never also has fewer than 8 captures+params spilling
    past x7 in the compiler's own source; guard it if that ever changes. }
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
  begin
    for I := 0 to ADecl.CapturedVars.Count - 1 do
    begin
      if J >= 8 then
        NotYet('captured var spilling past x7', ADecl);
      EmitStoreSlot('x' + IntToStr(J),
        '_cap_' + ADecl.CapturedVars.Strings[I]);
      Inc(J);
    end;
    if (ADecl.OwnerTypeName = '') and
       (ADecl.CapturedVars.IndexOf('Self') >= 0) then
    begin
      { _cap_Self holds &(enclosing method's Self slot) — deref to the
        receiver and store into this frame's real Self slot }
      EmitLoadSlot('x9', '_cap_Self');
      Self.Emit(#9'ldr x0, [x9]');
      EmitStoreSlot('x0', 'Self');
    end;
  end;
  if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
  begin
    { method: Self arrives after any captures }
    EmitStoreSlot('x' + IntToStr(J), 'Self');
    Inc(J);
  end;
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsOpenArray then
    begin
      { open array: two consecutive int-class values (data ptr, high) —
        each half falls back to the caller's outgoing area independently,
        mirroring the scalar walk (both halves are always 8 bytes) }
      for K := 0 to 1 do
      begin
        if J >= 8 then
        begin
          SPOff := AlignTo(SPOff, 8);
          Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
          if K = 0 then
            EmitStoreSlot('x9', Par.ParamName)
          else
            EmitStoreSlot('x9', Par.ParamName + '_high');
          SPOff := SPOff + 8;
        end
        else
        begin
          if K = 0 then
            EmitStoreSlot('x' + IntToStr(J), Par.ParamName)
          else
            EmitStoreSlot('x' + IntToStr(J), Par.ParamName + '_high');
          J := J + 1;
        end;
      end;
    end
    else if Par.IsVarParam then
    begin
      { var/out param: one x register carrying the caller's address }
      if J >= 8 then
      begin
        SPOff := AlignTo(SPOff, 8);
        Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
        EmitStoreSlot('x9', Par.ParamName);
        SPOff := SPOff + 8;
      end
      else
      begin
        EmitStoreSlot('x' + IntToStr(J), Par.ParamName);
        J := J + 1;
      end;
    end
    else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyRecord) then
    begin
      ParShape := RecReturnShape(TRecordTypeDesc(Par.ResolvedType));
      case ParShape of
        0:
        begin
          { >16B: pointer in one x reg — park it, copy bytes in pass 2.  When
            the int bank is full the caller passed the pointer on the stack
            (leg 29); read it from the outgoing area.  Pass 2 is unchanged: it
            memcpys from '__pptr_' regardless of how the pointer arrived. }
          if J >= 8 then
          begin
            SPOff := AlignTo(SPOff, 8);
            Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
            EmitStoreSlot('x9', '__pptr_' + Par.ParamName);
            SPOff := SPOff + 8;
          end
          else
          begin
            EmitStoreSlot('x' + IntToStr(J), '__pptr_' + Par.ParamName);
            J := J + 1;
          end;
        end;
        1:
        begin
          { <=8B record: one x reg holding the packed value (leg 29 overflow) }
          if J >= 8 then
          begin
            SPOff := AlignTo(SPOff, 8);
            Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
            EmitStoreSlot('x9', Par.ParamName);
            SPOff := SPOff + 8;
          end
          else
          begin
            EmitStoreSlot('x' + IntToStr(J), Par.ParamName);
            J := J + 1;
          end;
        end;
        2:
        begin
          { 9..16B record: two consecutive eightbytes.  AAPCS64 does not split
            an aggregate across registers and the stack — if it does not fit
            entirely in the remaining int registers it goes wholly on the stack
            (leg 29). }
          if J >= 7 then
          begin
            SPOff := AlignTo(SPOff, 8);
            EmitSlotAddr('x9', Par.ParamName);
            Self.Emit(Format(#9'ldr x10, [x29, #%d]', [16 + SPOff]));
            Self.Emit(#9'str x10, [x9]');
            Self.Emit(Format(#9'ldr x10, [x29, #%d]', [16 + SPOff + 8]));
            Self.Emit(#9'str x10, [x9, #8]');
            SPOff := SPOff + 16;
          end
          else
          begin
            EmitStoreSlot('x' + IntToStr(J), Par.ParamName);
            EmitSlotAddr('x9', Par.ParamName);
            Self.Emit(Format(#9'str x%d, [x9, #8]', [J + 1]));
            J := J + 2;
          end;
        end;
      else
        { HFA of (ParShape - 100) Doubles in d(FIdx).. — spills wholly to the
          stack when the fp bank cannot hold every lane (leg 29) }
        if FIdx + (ParShape - 100) > 8 then
        begin
          SPOff := AlignTo(SPOff, 8);
          EmitSlotAddr('x9', Par.ParamName);
          for K := 0 to (ParShape - 100) - 1 do
          begin
            Self.Emit(Format(#9'ldr x10, [x29, #%d]', [16 + SPOff + K * 8]));
            Self.Emit(Format(#9'str x10, [x9, #%d]', [K * 8]));
          end;
          SPOff := SPOff + (ParShape - 100) * 8;
        end
        else
        begin
          EmitSlotAddr('x9', Par.ParamName);
          for K := 0 to (ParShape - 100) - 1 do
            Self.Emit(Format(#9'str d%d, [x9, #%d]', [FIdx + K, K * 8]));
          FIdx := FIdx + (ParShape - 100);
        end;
      end;
    end
    else if (Par.ResolvedType <> nil) and
            (Par.ResolvedType.Kind = tyInterface) then
    begin
      { fat pointer in two consecutive x registers; spills as two eightbytes
        when the int bank cannot hold both (leg 29) }
      if J >= 7 then
      begin
        SPOff := AlignTo(SPOff, 8);
        Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
        EmitStoreSlot('x9', Par.ParamName);
        Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff + 8]));
        EmitStoreSlot('x9', Par.ParamName + '_itab');
        SPOff := SPOff + 16;
      end
      else
      begin
        EmitStoreSlot('x' + IntToStr(J), Par.ParamName);
        EmitStoreSlot('x' + IntToStr(J + 1), Par.ParamName + '_itab');
        J := J + 2;
      end;
    end
    else if (Par.ResolvedType <> nil) and
            (Par.ResolvedType.Kind = tyDouble) then
    begin
      if FIdx >= 8 then
      begin
        SPOff := AlignTo(SPOff, 8);
        Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
        EmitStoreSlot('x9', Par.ParamName);
        SPOff := SPOff + 8;
      end
      else
      begin
        Self.Emit(Format(#9'fmov x9, d%d', [FIdx]));
        EmitStoreSlot('x9', Par.ParamName);
        FIdx := FIdx + 1;
      end;
    end
    else if (Par.ResolvedType <> nil) and
            (Par.ResolvedType.Kind = tySingle) then
    begin
      { Single arrives in s(FIdx); its slot holds the 4-byte value.  On overflow
        (leg 29) the caller pushed it through the float path as a PROMOTED
        DOUBLE (fmov x0, d0 of the widened value — see the IsFloatExpr push
        arm), occupying an 8-byte stack slot.  So the callee reads the 8-byte
        double from the outgoing area, narrows it back to Single with fcvt, and
        stores the 4-byte value — the two sides must agree on the double
        encoding, not a raw 32-bit single. }
      if FIdx >= 8 then
      begin
        SPOff := AlignTo(SPOff, 8);
        Self.Emit(Format(#9'ldr d0, [x29, #%d]', [16 + SPOff]));
        Self.Emit(#9'fcvt s0, d0');
        EmitSlotAddr('x10', Par.ParamName);
        Self.Emit(#9'str s0, [x10]');
        SPOff := SPOff + 8;
      end
      else
      begin
        EmitSlotAddr('x9', Par.ParamName);
        Self.Emit(Format(#9'str s%d, [x9]', [FIdx]));
        FIdx := FIdx + 1;
      end;
    end
    else if IsMethodPtrType(Par.ResolvedType) or
            ((Par.ResolvedType is TSetTypeDesc) and
             TSetTypeDesc(Par.ResolvedType).IsJumbo()) then
    begin
      { closure / method-pointer param: a POINTER to the caller's 16-byte fat
        value arrives in one x reg (or on the stack when the int bank is full);
        park it in '__pptr_' — pass 2 memcpys the 16 bytes into our slot.
        A by-value jumbo set arrives the same way (its whole bitmap). }
      if J >= 8 then
      begin
        SPOff := AlignTo(SPOff, 8);
        Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
        EmitStoreSlot('x9', '__pptr_' + Par.ParamName);
        SPOff := SPOff + 8;
      end
      else
      begin
        EmitStoreSlot('x' + IntToStr(J), '__pptr_' + Par.ParamName);
        J := J + 1;
      end;
    end
    else
    begin
      if J >= 8 then
      begin
        SPSz := StackParamSize(Par);
        SPOff := AlignTo(SPOff, SPSz);
        if SPSz = 4 then
          Self.Emit(Format(#9'ldr w9, [x29, #%d]', [16 + SPOff]))
        else
          Self.Emit(Format(#9'ldr x9, [x29, #%d]', [16 + SPOff]));
        EmitStoreSlot('x9', Par.ParamName);
        SPOff := SPOff + SPSz;
      end
      else
      begin
        EmitStoreSlot('x' + IntToStr(J), Par.ParamName);
        J := J + 1;
      end;
    end;
  end;
  { sret: park the incoming x8 destination pointer in its hidden slot }
  if RecShape = 0 then
    EmitStoreSlot('x8', '__sret');
  { BY-VALUE string params: retain the callee's copy (the caller keeps its
    own reference).  Runs after every register is parked — _StringAddRef
    clobbers the caller-saved argument registers.

    A var/out param must be excluded as firmly as a const one.  Its slot holds
    the ADDRESS of the caller's variable, not a value, so retaining it does not
    merely over-retain — it hands _StringAddRef a pointer-to-a-pointer and the
    atomic refcount increment lands on unrelated memory.  On device that
    increment corrupted a global holding a TStringList pointer, which then
    crashed on the next use (macOS arm64, 2026-07-23).  The record-param retain
    loop just above already excludes var/out; these three never did.  The
    scope-exit RELEASE side is already safe: the frame-setup loop returns early
    for a var param, so it is never registered in FStrLocals/FIntfLocals/
    FDynLocals. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if (Par.ResolvedType = nil) or Par.IsConstParam or Par.IsVarParam then
      Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      EmitLoadSlot('x0', Par.ParamName);
      EmitCallSym('_StringAddRef');
    end;
    if Par.ResolvedType.Kind = tyInterface then
    begin
      EmitLoadSlot('x0', Par.ParamName);
      EmitCallSym('_ClassAddRef');
    end;
    { by-value CLASS param: the callee's own reference, exactly like a
      by-value string.  It used to be a pure borrow, but an assignment to the
      parameter (A := A.Next -- legal Pascal) runs the ordinary
      release-old / retain-new store, which released the CALLER's reference:
      the caller's object was freed mid-call and later double-freed, with no
      diagnostic.  Retained here, released with the class locals at exit, so
      the convention stays balanced inside the callee and the caller is
      unchanged. }
    if Par.ResolvedType.Kind = tyClass then
    begin
      EmitLoadSlot('x0', Par.ParamName);
      EmitCallSym('_ClassAddRef');
    end;
    { by-value dyn-array param: co-owning copy — retain here, released with the
      dyn-array locals at scope exit (registered in FDynLocals above). }
    if Par.ResolvedType.Kind = tyDynArray then
    begin
      EmitLoadSlot('x0', Par.ParamName);
      EmitCallSym('_DynArrayAddRef');
    end;
  end;
  { pass 2: copy the bytes of every pointer-passed record param into its
    own slot.  This runs only after every register is parked, because the
    memcpy call clobbers the caller-saved argument registers. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    { A VAR/OUT record param is NOT copied — the caller keeps ownership and
      only its ADDRESS is passed (spilled to Par.ParamName, no __pptr_ slot).
      The register loop's IsVarParam arm registers just the address slot, so a
      var-param record must be skipped here too, else this loads a
      never-registered '__pptr_<Name>' (BUG-20260720-arm64-managed-record-param
      for the var-param form). }
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyRecord) and
       (not Par.IsVarParam) and
       (RecReturnShape(TRecordTypeDesc(Par.ResolvedType)) = 0) then
    begin
      EmitSlotAddr('x0', Par.ParamName);
      EmitLoadSlot('x1', '__pptr_' + Par.ParamName);
      EmitIntLiteral('x2', Par.ResolvedType.RawSize());
      EmitCallSym('memcpy');
    end
    else if (Par.ResolvedType is TSetTypeDesc) and
            TSetTypeDesc(Par.ResolvedType).IsJumbo() and
            (not Par.IsVarParam) then
    begin
      { by-value jumbo set: copy the caller's bitmap into our own slot }
      EmitSlotAddr('x0', Par.ParamName);
      EmitLoadSlot('x1', '__pptr_' + Par.ParamName);
      EmitIntLiteral('x2', Par.ResolvedType.RawSize());
      EmitCallSym('memcpy');
    end
    else if IsMethodPtrType(Par.ResolvedType) and (not Par.IsVarParam) then
    begin
      { closure / method-pointer param: copy the 16-byte fat value from the
        caller's block (address parked in '__pptr_') into our own slot. }
      EmitLoadSlot('x1', '__pptr_' + Par.ParamName);
      Self.Emit(#9'ldp x9, x10, [x1]');
      EmitSlotAddr('x0', Par.ParamName);
      Self.Emit(#9'stp x9, x10, [x0]');
    end;
  end;
  { pass 3: by-value record params with managed fields — the callee owns its
    copy, so retain every managed field (walk anchored on callee-saved x19).

    This MUST run AFTER pass 2's memcpy, not before it.  It used to be emitted
    up with the sret parking, which meant the retains read the callee's slot
    while it still held uninitialised stack bytes: _StringAddRef was handed
    whatever garbage lay at each managed field offset, and the atomic increment
    landed on unrelated memory.  With a record big enough to reach into live
    frame data the garbage was a .text address and the increment faulted
    outright (BUG-20260725-arm64-record-param-retain-before-copy — every one of
    the 8 remaining on-device crash suites bottomed out here, via the x86_64
    assembler's `const AParsed: TParsedLine`). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyRecord) and
       not Par.IsVarParam and
       not RecretManagedClean(TRecordTypeDesc(Par.ResolvedType)) then
    begin
      Self.Emit(#9'str x19, [sp, #-16]!');
      EmitSlotAddr('x19', Par.ParamName);
      Self.EmitRecordFieldRetains(TRecordTypeDesc(Par.ResolvedType), 'x19');
      Self.Emit(#9'ldr x19, [sp], #16');
    end;
  end;
  { zero-initialise Result and every declared local (language rule: ALL
    variables are zero-initialised) }
  if FIsFunction and (ADecl.ResolvedReturnType.Kind = tyInterface) then
  begin
    EmitStoreSlot('xzr', 'Result');
    EmitStoreSlot('xzr', 'Result_itab');
  end
  else if FIsFunction and IsMethodPtrType(ADecl.ResolvedReturnType) then
  begin
    EmitSlotAddr('x0', 'Result');
    Self.Emit(#9'stp xzr, xzr, [x0]');
  end
  else if FIsFunction and (RecShape >= 0) then
  begin
    EmitSlotAddr('x0', 'Result');
    Self.Emit(#9'movz w1, #0');
    EmitIntLiteral('x2', ADecl.ResolvedReturnType.RawSize());
    EmitCallSym('memset');
  end
  else if FIsFunction then
    EmitStoreSlot('xzr', 'Result');
  for I := 0 to ADecl.Body.Decls.Count - 1 do
    for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
    begin
      if (TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind in
          [tyRecord, tyStaticArray]) or
         ((TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType is TSetTypeDesc) and
          TSetTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).IsJumbo()) then
      begin
        { aggregates (and a jumbo set's bitmap) zero-initialise their whole
          storage }
        EmitSlotAddr('x0',
          TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J]);
        Self.Emit(#9'movz w1, #0');
        EmitIntLiteral('x2',
          TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.RawSize());
        EmitCallSym('memset');
      end
      else if IsMethodPtrType(
                TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType) then
      begin
        { closure / method-pointer local: zero BOTH halves of the 16-byte fat
          value (Code at +0, Env/Data at +8) — a nil Env is a no-op for the
          scope-exit release. }
        EmitSlotAddr('x0',
          TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J]);
        Self.Emit(#9'stp xzr, xzr, [x0]');
      end
      else
        EmitStoreSlot('xzr',
          TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J]);
    end;

  if ADecl.EnvCaptured <> nil then
    EmitEnvPrologue(ADecl);

  EmitStmtList(ADecl.Body.Stmts);

  Self.Emit(FExitLabel + ':');
  { The enclosing frame drops its strong reference to the closure env; the
    env lives on iff an escaped closure still holds it.  A thunk BORROWS its
    env from the fat value it was called through -- no release. }
  if (ADecl.EnvCaptured <> nil) and not ADecl.IsAnonThunk then
  begin
    EmitLoadSlot('x0', '__envp');
    EmitCallSym('_ClassRelease');
  end;
  { release string locals at scope exit (Exit statements land here too) }
  for I := 0 to FStrLocals.Count - 1 do
  begin
    EmitLoadSlot('x0', FStrLocals.Strings[I]);
    EmitCallSym('_StringRelease');
  end;
  { release class-typed locals (borrowed Self is NOT in FObjLocals) }
  for I := 0 to FObjLocals.Count - 1 do
  begin
    EmitLoadSlot('x0', FObjLocals.Strings[I]);
    EmitCallSym('_ClassRelease');
  end;
  { deregister [Weak] locals (their obj slot) from the weak table }
  for I := 0 to FWeakLocals.Count - 1 do
  begin
    EmitSlotAddr('x0', FWeakLocals.Strings[I]);
    EmitCallSym('_WeakClear');
  end;
  { release the obj half of interface locals }
  for I := 0 to FIntfLocals.Count - 1 do
  begin
    EmitLoadSlot('x0', FIntfLocals.Strings[I]);
    EmitCallSym('_ClassRelease');
  end;
  for I := 0 to FDynLocals.Count - 1 do
  begin
    EmitLoadSlot('x0', FDynLocals.Strings[I]);
    EmitCallSym('_DynArrayRelease');
  end;
  { release the Env half of 'reference to' closure locals (arkRefEnv): load the
    slot address, read the Env pointer at +8, _ClassRelease it (nil-safe, so a
    capture-free closure is a no-op). }
  for I := 0 to FRefLocals.Count - 1 do
  begin
    EmitSlotAddr('x0', FRefLocals.Strings[I]);
    Self.Emit(#9'ldr x0, [x0, #8]');
    EmitCallSym('_ClassRelease');
  end;
  { release the managed fields of record locals — the base-class walk needs
    a callee-saved base register across its release calls }
  for I := 0 to FRecLocals.Count - 1 do
    if AggHasManaged(TTypeDesc(FRecLocals.Objects[I])) then
    begin
      Self.Emit(#9'str x19, [sp, #-16]!');
      EmitSlotAddr('x19', FRecLocals.Strings[I]);
      Self.EmitManagedReleaseAt(TTypeDesc(FRecLocals.Objects[I]),
        'x19', False);
      Self.Emit(#9'ldr x19, [sp], #16');
    end;
  if FIsFunction and (RecShape >= 0) and
     (ADecl.ResolvedReturnType.Kind = tyRecord) then
  begin
    case RecShape of
      0:
      begin
        { sret: copy Result into the caller's x8 buffer }
        EmitLoadSlot('x0', '__sret');
        EmitPushX0();
        EmitSlotAddr('x0', 'Result');
        Self.Emit(#9'mov x1, x0');
        EmitPopTo('x0');
        EmitIntLiteral('x2', ADecl.ResolvedReturnType.RawSize());
        EmitCallSym('memcpy');
      end;
      1:
      begin
        EmitSlotAddr('x9', 'Result');
        Self.Emit(#9'ldr x0, [x9]');
      end;
      2:
      begin
        EmitSlotAddr('x9', 'Result');
        Self.Emit(#9'ldr x0, [x9]');
        Self.Emit(#9'ldr x1, [x9, #8]');
      end;
    else
      begin
        { HFA: N doubles in d0..d(N-1) }
        EmitSlotAddr('x9', 'Result');
        for I := 0 to (RecShape - 100) - 1 do
          Self.Emit(Format(#9'ldr d%d, [x9, #%d]', [I, I * 8]));
      end;
    end;
  end
  else if FIsFunction and IsJumboSetType(ADecl.ResolvedReturnType) then
  begin
    { the whole bitmap to the caller's buffer }
    EmitLoadSlot('x0', '__sret');
    EmitPushX0();
    EmitSlotAddr('x1', 'Result');
    EmitPopTo('x0');
    EmitIntLiteral('x2', ADecl.ResolvedReturnType.RawSize());
    EmitCallSym('memcpy');
  end
  else if FIsFunction and IsMethodPtrType(ADecl.ResolvedReturnType) then
  begin
    { both words to the caller's buffer; the Env reference moves with them }
    EmitLoadSlot('x9', '__sret');
    EmitSlotAddr('x1', 'Result');
    Self.Emit(#9'ldp x10, x11, [x1]');
    Self.Emit(#9'stp x10, x11, [x9]');
  end
  else if FIsFunction and
          (ADecl.ResolvedReturnType.Kind = tyInterface) then
  begin
    EmitLoadSlot('x9', '__sret');
    EmitLoadSlot('x0', 'Result');
    Self.Emit(#9'str x0, [x9]');
    EmitLoadSlot('x0', 'Result_itab');
    Self.Emit(#9'str x0, [x9, #8]');
  end
  else if FIsFunction and FResultSingle then
  begin
    { Single results return in s0 — the slot holds the 4-byte value }
    EmitSlotAddr('x9', 'Result');
    Self.Emit(#9'ldr s0, [x9]');
  end
  else if FIsFunction then
  begin
    EmitLoadSlot('x0', 'Result');
    if FResultFloat then
      Self.Emit(#9'fmov d0, x0');   { Double results return in d0 }
  end;
  Self.Emit(#9'mov sp, x29');
  Self.Emit(#9'ldp x29, x30, [sp], #16');
  Self.Emit(#9'ret');
  FAsm := SavedAsm;
  FrameAligned := (FFrameSize + 15) and (not 15);
  if FrameAligned > 0 then
    EmitAddSubImm('sub', 'sp', 'sp', FrameAligned);
  FAsm.Append(BodyBuf.ToString());
  BodyBuf.Free();
  if (ADecl.EnvCaptured <> nil) and not ADecl.IsAnonThunk then
    EmitEnvCleanupFn(TRecordTypeDesc(ADecl.EnvType));
  FFrame.Clear();
  FFrameSize := 0;
  FCapturedVars := nil;   { leg 17: end the capture window for this routine }
  FCurEnvCaptured := nil;
end;

function TArm64Backend.StackArgSize(AArg: TASTExpr): Integer;
begin
  { Apple packs stack args to natural size, with the C default promotions
    for variadic args: sub-int widths promote to 4, floats to 8. }
  Result := 8;
  if (AArg.ResolvedType <> nil) and IsIntFam(AArg.ResolvedType) then
  begin
    Result := AArg.ResolvedType.RawSize();
    if Result < 4 then Result := 4;
    if Result > 8 then Result := 8;
  end;
end;

function TArm64Backend.StackParamSize(APar: TMethodParam): Integer;
begin
  { natural size for a FIXED param passed on the stack.  Floats stay 8
    (a deliberate simplification also applied on the callee side —
    a fixed Single stack param occupies 8 bytes here, matching both
    ends of every Blaise-internal call). }
  Result := 8;
  if APar.IsVarParam then Exit;
  if IsIntFam(APar.ResolvedType) then
  begin
    Result := APar.ResolvedType.RawSize();
    if Result < 4 then Result := 4;
    if Result > 8 then Result := 8;
  end;
end;

function TArm64Backend.AlignTo(AValue, AAlign: Integer): Integer;
begin
  Result := (AValue + AAlign - 1) and (not (AAlign - 1));
end;

function TArm64Backend.IsRecordCallArg(AArg: TASTExpr): Boolean;
begin
  { a record-typed argument whose VALUE is produced by a call — it has no
    lvalue slot, so it must be materialised into a scratch buffer before
    it can be passed by value.  Constructors do not return records. }
  Result := (AArg.ResolvedType <> nil) and
            (AArg.ResolvedType.Kind = tyRecord) and
            (((AArg is TFuncCallExpr) and
              (TFuncCallExpr(AArg).ResolvedDecl <> nil)) or
             ((AArg is TMethodCallExpr) and
              (TMethodCallExpr(AArg).ResolvedMethod <> nil) and
              not TMethodCallExpr(AArg).IsConstructorCall));
end;

function TArm64Backend.ComputeStackArgArea(ADecl: TMethodDecl;
  AArgs: TObjectList; ASelfPushed: Boolean): Integer;
var
  LB, TB, RB: Integer;
begin
  Result := ComputeStackArgAreaEx(ADecl, AArgs, ASelfPushed, LB, TB, RB);
end;

function TArm64Backend.ComputeStackArgAreaEx(ADecl: TMethodDecl;
  AArgs: TObjectList; ASelfPushed: Boolean; out ALitBase: Integer;
  out ATransBase: Integer; out ARecBase: Integer): Integer;
var
  I, NInt, NFloat, Off, Sz, Trans, Lit, ESz, Rec: Integer;
  Arg: TASTExpr;
begin
  { dry-run of the classification walk in EmitCall — must stay in
    lockstep with it }
  NInt := 0;
  NFloat := 0;
  Trans := 0;
  Lit := 0;
  Rec := 0;
  if ASelfPushed then NInt := 1;
  { leg 17: captured-var pointer args occupy leading integer registers before
    the normal args — count them here or the register-vs-stack decision below
    drifts from EmitCall by CapturedVars.Count, under-reserving the outgoing
    stack area (mirrors x86-64 :18220-18221). }
  if (ADecl <> nil) and (ADecl.CapturedVars <> nil) then
    NInt := NInt + ADecl.CapturedVars.Count;
  Off := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if (I < ADecl.Params.Count) and
       TMethodParam(ADecl.Params.Items[I]).IsOpenArray then
    begin
      { (ptr, high) pair — two int registers; a literal arg additionally
        reserves its element block in the literal park area }
      if Arg is TArrayLiteralExpr then
      begin
        ESz := TOpenArrayTypeDesc(
          TMethodParam(ADecl.Params.Items[I]).ResolvedType)
          .ElementType.RawSize();
        Lit := Lit +
          AlignTo(TArrayLiteralExpr(Arg).Elements.Count * ESz, 8);
      end;
      NInt := NInt + 2;
      Continue;
    end;
    { string transients get a release slot after the call when the CALLER
      must dispose them: rc=1 always (the callee pair nets to zero); rc=0
      only for const params (no callee pair — the caller pins).  A by-value
      rc=0 arg is freed by the callee's entry-retain/exit-release pair; a
      caller-side dispose would double-free.  A BORROWED aliasable source to a
      formal string param also parks (shape 'P': pin AddRef before / release
      after).  MUST stay in lockstep with the string-arg block in EmitCall. }
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyString) then
    begin
      if ArcExprOwnsRef(Arg) then
        Inc(Trans)
      else if ArcExprIsUnownedStrTransient(Arg) and
              (I < ADecl.Params.Count) and
              TMethodParam(ADecl.Params.Items[I]).IsConstParam then
        Inc(Trans)
      else if (I < ADecl.Params.Count) and
              Self.IsPinnedBorrowedStrArg(Arg,
                Self.ParamsHaveVarString(ADecl.Params)) then
        Inc(Trans);
    end;
    { an owned CLASS transient (call-result argument) parks for one
      post-call release — the callee only borrows it }
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyClass) and
       ArcExprOwnsRef(Arg) then
      Inc(Trans);
    if (I < ADecl.Params.Count) and
       TMethodParam(ADecl.Params.Items[I]).IsVarParam then
    begin
      if NInt >= 8 then
      begin
        { 9th+ var arg spills its address — mirror the EmitCall walk }
        Off := AlignTo(Off, 8);
        Off := Off + 8;
      end
      else
        Inc(NInt);
      Continue;
    end;
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyRecord) then
    begin
      { a record-CALL arg additionally reserves a scratch buffer in the RecBase
        region (materialised there before its slot is pushed).  Overflow (leg
        29): AAPCS64 does not split an aggregate across registers and the stack
        — if the whole record does not fit in the remaining int/fp registers it
        goes wholly on the stack.  Must stay in lockstep with EmitCall. }
      if IsRecordCallArg(Arg) then
        Rec := Rec + AlignTo(Arg.ResolvedType.RawSize(), 16);
      case RecReturnShape(TRecordTypeDesc(Arg.ResolvedType)) of
        0, 1:
          if NInt >= 8 then Off := AlignTo(Off, 8) + 8
          else Inc(NInt);
        2:
          if NInt >= 7 then Off := AlignTo(Off, 8) + 16
          else NInt := NInt + 2;
      else
        if NFloat + (RecReturnShape(TRecordTypeDesc(Arg.ResolvedType)) - 100) > 8 then
          Off := AlignTo(Off, 8) +
            (RecReturnShape(TRecordTypeDesc(Arg.ResolvedType)) - 100) * 8
        else
          NFloat := NFloat +
            (RecReturnShape(TRecordTypeDesc(Arg.ResolvedType)) - 100);
      end;
      Continue;
    end;
    if IsIntfArg(ADecl, I, Arg) then
    begin
      if NInt >= 7 then Off := AlignTo(Off, 8) + 16
      else NInt := NInt + 2;
      Continue;
    end;
    if IsFloatExpr(Arg) then
    begin
      if (ADecl.IsVarArgs and (I >= ADecl.Params.Count)) or (NFloat >= 8) then
      begin
        Off := AlignTo(Off, 8) + 8;
      end
      else
        Inc(NFloat);
      Continue;
    end;
    { everything else travels int-class }
    if (ADecl.IsVarArgs and (I >= ADecl.Params.Count)) or (NInt >= 8) then
    begin
      if I < ADecl.Params.Count then
        Sz := StackParamSize(TMethodParam(ADecl.Params.Items[I]))
      else
        Sz := StackArgSize(Arg);
      Off := AlignTo(Off, Sz) + Sz;
    end
    else
      Inc(NInt);
  end;
  ALitBase := AlignTo(Off, 8);
  ATransBase := ALitBase + Lit;
  ARecBase := AlignTo(ATransBase + Trans * 8, 16);
  Result := AlignTo(ARecBase + Rec, 16);
end;

procedure TArm64Backend.DecodeMemArg(const AEntry: string;
  out AOff, ASize: Integer);
var
  P: Integer;
begin
  { entry shape: m<offset>_<size> }
  P := Pos('_', AEntry);
  AOff := StrToInt(Copy(AEntry, 1, P - 1));
  ASize := StrToInt(Copy(AEntry, P + 1, Length(AEntry) - P - 1));
end;

{ True when float argument AIdx travels in an s register.  The PARAMETER's
  type decides, not the argument's: a double literal passed to a Single
  parameter must be narrowed, and a Single value passed to a Double parameter
  must stay widened in a d register.  Arguments beyond the declared
  parameters (variadic) fall back to their own type. }
function FloatArgIsSingle(ADecl: TMethodDecl; AIdx: Integer;
  AArg: TASTExpr): Boolean;
var
  PT: TTypeDesc;
begin
  if AIdx < ADecl.Params.Count then
    PT := TMethodParam(ADecl.Params.Items[AIdx]).ResolvedType
  else
    PT := AArg.ResolvedType;
  Result := (PT <> nil) and (PT.Kind = tySingle);
end;

procedure TArm64Backend.EmitCall(ADecl: TMethodDecl; const AName: string;
  AArgs: TObjectList; const ASretDest: string;
  ASelfPushed: Boolean; AVirtSlot: Integer; ASretSpOff: Integer);
var
  I, K, Shape: Integer;
  Arg: TASTExpr;
  NInt, NFloat: Integer;
  PopRegs: TStringList;
  Reg: string;
  StackOff, StackArea, ASz: Integer;
  TransBase, TransN: Integer;
  TransShapes: string;
  IsVariadicArg: Boolean;
  LitBase, LitOff, ESz, N: Integer;
  RecBase, RecOff: Integer;
  NarrowFix: Boolean;
  JTmp: string;
  JNB: Integer;
  IndSlot: string;
  IntfT: TTypeDesc;
begin
  { an indirect call's target slot, captured now -- a closure call among the
    arguments re-sets FIndirectSlot for itself }
  IndSlot := '';
  if AVirtSlot = VIRT_INDIRECT then
    IndSlot := FIndirectSlot;
  NInt := 0;
  NFloat := 0;
  StackOff := 0;
  if ADecl = nil then
    NotYet('call to unresolved routine ''' + AName + '''', nil);
  { a method receiver was pushed by the caller BEFORE this call: it is the
    first int-class value, popped last into x0 }
  if ASelfPushed then
    NInt := 1;
  { Outgoing stack-arg area: args past the register files, and ALL
    variadic anonymous args (Apple divergence — Linux AAPCS64 would
    continue the register sequence).  Apple packs stack args to natural
    size with the C default promotions; the area is allocated BEFORE the
    argument pushes so its offsets stay fixed during the pop walk. }
  StackArea := ComputeStackArgAreaEx(ADecl, AArgs, ASelfPushed, LitBase,
    TransBase, RecBase);
  TransN := 0;
  TransShapes := '';
  LitOff := 0;
  RecOff := 0;
  if StackArea > 0 then
  begin
    { The outgoing area must sit BELOW every pushed eval slot, because the pop
      walk pops a contiguous LIFO run and the memory-class / transient offsets
      are all measured from sp with those slots still pushed.

      A method receiver, though, was already pushed by our CALLER (ASelfPushed)
      — before we got here.  Reserving underneath it would leave the area
      wedged BETWEEN Self and the argument pushes, so the final pop would read
      the reserved gap instead of Self, and the transient stash offset would
      land on Self's slot and clobber it.  That is exactly what happened for
      `Result.Add(GDrivers[I].Name())`: Add got raw stack content as Self
      (macOS arm64 on-device crash, 2026-07-23) — a nested call returning an
      ARC'd string is what makes the area non-zero in the first place.

      Re-seat the receiver: pop it, reserve, push it back.  The run is then
      contiguous again and every existing offset stays correct. }
    if ASelfPushed then
      EmitPopTo('x9');
    EmitAddSubImm('sub', 'sp', 'sp', StackArea);
    if ASelfPushed then
      Self.Emit(#9'str x9, [sp, #-16]!');
  end;
  { Evaluate args left-to-right onto the stack (calls inside an argument
    cannot clobber earlier args), floats as their 8-byte bit pattern.
    Integer and float args consume INDEPENDENT register sequences
    (x0.. / d0..) per AAPCS64.  Each pushed 8-byte value records its
    final register up front; the pop walk restores in reverse order. }
  PopRegs := TStringList.Create();
  try
    if ASelfPushed then
      PopRegs.Add('x0');
    { Nested-routine capture args (leg 17): prepend one pointer arg per var the
      callee captures, BEFORE the normal args, so they occupy the leading
      integer registers (x0..).  For each captured name — if it is itself
      captured in THIS (caller) frame, forward the caller's '_cap_' pointer;
      else if a caller local, take its slot address; else a global address.
      A captured method Self forwards the caller's Self address.  Mirrors x86-64
      EmitCall (:18243-18264). }
    if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
    begin
      if ASelfPushed then
        NotYet('capture args on a receiver call', nil);
      for I := 0 to ADecl.CapturedVars.Count - 1 do
      begin
        if NInt >= 8 then
          NotYet('capture argument spilling to the stack', nil);
        if IsCaptured(ADecl.CapturedVars.Strings[I]) then
          EmitLoadSlot('x0', '_cap_' + ADecl.CapturedVars.Strings[I])
        else if SameText(ADecl.CapturedVars.Strings[I], 'Self') then
          EmitSlotAddr('x0', 'Self')
        else
          EmitSlotAddr('x0', ADecl.CapturedVars.Strings[I]);
        EmitPushX0();
        PopRegs.Add('x' + IntToStr(NInt));
        Inc(NInt);
      end;
    end;
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      if (I < ADecl.Params.Count) and
         TMethodParam(ADecl.Params.Items[I]).IsOpenArray then
      begin
        { open array: push (data ptr, high) as two int-class values }
        if NInt >= 7 then
          NotYet('open-array arguments spilling to the stack', Arg);
        if Arg is TArrayLiteralExpr then
        begin
          { materialise the element block in the pre-reserved literal
            park area.  The block's address is ABSOLUTE (sp moves as
            later args push, the block does not), computed against the
            CURRENT sp: park base sits PopRegs.Count*16 above it. }
          ESz := TOpenArrayTypeDesc(
            TMethodParam(ADecl.Params.Items[I]).ResolvedType)
            .ElementType.RawSize();
          N := TArrayLiteralExpr(Arg).Elements.Count;
          if TArrayLiteralExpr(Arg).IsConstArray then
          begin
            { 'array of const': each element is a 16-byte TVarRec (VType byte
              at +0, VValue at +8).  Borrow semantics — strings/objects stored
              without an AddRef; a double is heap-boxed (a PDouble in the slot)
              since it does not fit the integer value slot.  Mirrors x86-64
              EmitConstArrayLiteral. }
            for K := 0 to N - 1 do
              EmitConstArrayElemToVarRec(
                TASTExpr(TArrayLiteralExpr(Arg).Elements.Items[K]),
                PopRegs.Count * 16 + LitBase + LitOff + K * 16);
          end
          else
          for K := 0 to N - 1 do
          begin
            if ArcExprOwnsRef(
                 TASTExpr(TArrayLiteralExpr(Arg).Elements.Items[K])) then
              NotYet('owned transient in an open-array literal', Arg);
            Self.EmitExprToX0(
              TASTExpr(TArrayLiteralExpr(Arg).Elements.Items[K]));
            EmitAddSubImm('add', 'x9', 'sp',
              PopRegs.Count * 16 + LitBase + LitOff + K * ESz);
            case ESz of
              1: Self.Emit(#9'strb w0, [x9]');
              2: Self.Emit(#9'strh w0, [x9]');
              4: Self.Emit(#9'str w0, [x9]');
            else
              Self.Emit(#9'str x0, [x9]');
            end;
          end;
          EmitAddSubImm('add', 'x0', 'sp',
            PopRegs.Count * 16 + LitBase + LitOff);
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt));
          EmitIntLiteral('x0', N - 1);
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt + 1));
          LitOff := LitOff + AlignTo(N * ESz, 8);
        end
        else if (Arg is TIdentExpr) and (Arg.ResolvedType <> nil) and
                (Arg.ResolvedType.Kind = tyStaticArray) then
        begin
          { static array: base address + compile-time high (0-rebased) }
          if TIdentExpr(Arg).ConstArraySymbol <> '' then
          begin
            Self.Emit(Format(#9'adrp x0, %s@PAGE',
              [CodegenMangle(TIdentExpr(Arg).ConstArraySymbol)]));
            Self.Emit(Format(#9'add x0, x0, %s@PAGEOFF',
              [CodegenMangle(TIdentExpr(Arg).ConstArraySymbol)]));
          end
          else
            EmitSlotAddr('x0', TIdentExpr(Arg).Name);
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt));
          EmitIntLiteral('x0',
            TStaticArrayTypeDesc(Arg.ResolvedType).HighBound -
            TStaticArrayTypeDesc(Arg.ResolvedType).LowBound);
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt + 1));
        end
        else if (Arg.ResolvedType <> nil) and
                (Arg.ResolvedType.Kind = tyDynArray) then
        begin
          { dyn array coerced to open array: data ptr + (length - 1) }
          Self.EmitExprToX0(Arg);
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt));
          Self.Emit(#9'ldr x0, [sp]');
          EmitCallSym('_DynArrayLength');
          Self.Emit(#9'sub x0, x0, #1');
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt + 1));
        end
        else if (Arg is TIdentExpr) and (Arg.ResolvedType <> nil) and
                (Arg.ResolvedType.Kind = tyOpenArray) then
        begin
          { forwarding an open-array param: both slots pass through }
          EmitLoadSlot('x0', TIdentExpr(Arg).Name);
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt));
          EmitLoadSlot('x0', TIdentExpr(Arg).Name + '_high');
          EmitPushX0();
          PopRegs.Add('x' + IntToStr(NInt + 1));
        end
        else
          NotYet('open-array argument from this expression', Arg);
        NInt := NInt + 2;
      end
      else if (I < ADecl.Params.Count) and
         TMethodParam(ADecl.Params.Items[I]).IsVarParam then
      begin
        { var/out param: pass the lvalue's address.  A var param handed
          straight through to another var param forwards the address it
          already holds; a field lvalue (CD.Field) passes the field's
          address computed from its owning record/instance. }
        EmitVarArgAddrToX0(Arg);
        EmitPushX0();
        if NInt >= 8 then
        begin
          { 9th+ var arg: the address goes to the outgoing stack area —
            the callee prologue reads it from [x29, #16+off] }
          StackOff := AlignTo(StackOff, 8);
          PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
          StackOff := StackOff + 8;
        end
        else
        begin
          PopRegs.Add('x' + IntToStr(NInt));
          Inc(NInt);
        end;
      end
      else if (Arg.ResolvedType <> nil) and
         (Arg.ResolvedType.Kind = tyRecord) then
      begin
        Shape := RecReturnShape(TRecordTypeDesc(Arg.ResolvedType));
        { a C callee: the shapes below already follow AAPCS64 for an
          all-integer record of at most 16 bytes (x registers, memory image)
          and a flat Double HFA (d registers).  A Single or mixed float
          record would need s registers, and a larger one a private copy
          the callee may scribble on -- not lowered yet. }
        if ADecl.IsExternal and not ((Shape >= 100) or
           (Self.ClassifyRecordReturn(TRecordTypeDesc(Arg.ResolvedType)) in
             [rcInt1, rcInt2])) then
          NotYet('a record argument of this shape (floating-point fields, ' +
            'or larger than 16 bytes) to an external routine', Arg);
        if IsRecordCallArg(Arg) then
        begin
          { record-CALL argument (Foo(MakeRec(x))): the value has no lvalue
            slot.  Materialise it into a scratch buffer in the RecBase
            region — a fixed sp-relative home BELOW the arg-push slots, so
            the nested call's stack traffic and the later arg pushes cannot
            collide with it.  Register-returned shapes (1/2/HFA) store their
            result into the buffer; shape 0 (>16B, x8/memory return) needs
            an x8 destination address and stays an honest hole for now. }
          if Shape = 0 then
          begin
            { >16B return: the callee writes through x8, so hand it THIS
              buffer as its indirect-result destination, then pass the
              buffer's ADDRESS as the argument — the same >16B argument
              convention the lvalue case below uses.  Offsets are measured
              before this argument's own push, exactly like the register-
              returned shapes further down.  Mirrors x86-64's akRecCall
              hoist, which likewise materialises the sret buffer in the
              region below the argument slots. }
            EmitRecCallDispatch(Arg, '',
              PopRegs.Count * 16 + RecBase + RecOff);
            EmitAddSubImm('add', 'x0', 'sp',
              PopRegs.Count * 16 + RecBase + RecOff);
            EmitPushX0();
            if NInt >= 8 then
            begin
              StackOff := AlignTo(StackOff, 8);
              PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
              StackOff := StackOff + 8;
            end
            else
            begin
              PopRegs.Add('x' + IntToStr(NInt));
              Inc(NInt);
            end;
            RecOff := RecOff + AlignTo(Arg.ResolvedType.RawSize(), 16);
            Continue;
          end;
          EmitRecCallDispatch(Arg, '');   { result in x0 / x0:x1 / d0.. }
          { buffer address: sp + (still-pushed eval slots) + RecBase + off }
          EmitAddSubImm('add', 'x9', 'sp',
            PopRegs.Count * 16 + RecBase + RecOff);
          case Shape of
            1: Self.Emit(#9'str x0, [x9]');
            2:
            begin
              Self.Emit(#9'str x0, [x9]');
              Self.Emit(#9'str x1, [x9, #8]');
            end;
          else
            for K := 0 to (Shape - 100) - 1 do
              Self.Emit(Format(#9'str d%d, [x9, #%d]', [K, K * 8]));
          end;
          { now push the buffer's contents per shape, exactly like an
            lvalue record — the buffer address is re-derived each time
            because intervening pushes move sp but not the buffer }
          case Shape of
            1:
            begin
              EmitAddSubImm('add', 'x0', 'sp',
                PopRegs.Count * 16 + RecBase + RecOff);
              Self.Emit(#9'ldr x0, [x0]');
              EmitPushX0();
              if NInt >= 8 then
              begin
                StackOff := AlignTo(StackOff, 8);
                PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
                StackOff := StackOff + 8;
              end
              else
              begin
                PopRegs.Add('x' + IntToStr(NInt));
                Inc(NInt);
              end;
            end;
            2:
            begin
              if NInt >= 7 then
              begin
                EmitAddSubImm('add', 'x9', 'sp',
                  PopRegs.Count * 16 + RecBase + RecOff);
                StackOff := AlignTo(StackOff, 8);
                Self.Emit(#9'ldr x0, [x9]');
                EmitPushX0();
                PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
                StackOff := StackOff + 8;
                EmitAddSubImm('add', 'x9', 'sp',
                  (PopRegs.Count) * 16 + RecBase + RecOff);
                Self.Emit(#9'ldr x0, [x9, #8]');
                EmitPushX0();
                PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
                StackOff := StackOff + 8;
              end
              else
              begin
                EmitAddSubImm('add', 'x9', 'sp',
                  PopRegs.Count * 16 + RecBase + RecOff);
                Self.Emit(#9'ldr x0, [x9]');
                EmitPushX0();
                PopRegs.Add('x' + IntToStr(NInt));
                EmitAddSubImm('add', 'x9', 'sp',
                  (PopRegs.Count) * 16 + RecBase + RecOff);
                Self.Emit(#9'ldr x0, [x9, #8]');
                EmitPushX0();
                PopRegs.Add('x' + IntToStr(NInt + 1));
                NInt := NInt + 2;
              end;
            end;
          else
            if NFloat + (Shape - 100) > 8 then
              for K := 0 to (Shape - 100) - 1 do
              begin
                EmitAddSubImm('add', 'x9', 'sp',
                  PopRegs.Count * 16 + RecBase + RecOff);
                StackOff := AlignTo(StackOff, 8);
                Self.Emit(Format(#9'ldr x0, [x9, #%d]', [K * 8]));
                EmitPushX0();
                PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
                StackOff := StackOff + 8;
              end
            else
            begin
              for K := 0 to (Shape - 100) - 1 do
              begin
                EmitAddSubImm('add', 'x9', 'sp',
                  PopRegs.Count * 16 + RecBase + RecOff);
                Self.Emit(Format(#9'ldr x0, [x9, #%d]', [K * 8]));
                EmitPushX0();
                PopRegs.Add('d' + IntToStr(NFloat + K));
              end;
              NFloat := NFloat + (Shape - 100);
            end;
          end;
          RecOff := RecOff + AlignTo(Arg.ResolvedType.RawSize(), 16);
        end
        else
        case Shape of
          0:
          begin
            { >16B: pass the lvalue address (the callee memcpies into its own
              slot at entry).  EmitRecAddrToX0 handles ident/subscript/field
              lvalues uniformly — Specs[I] included.  Overflow (leg 29): the
              address travels in an 8-byte stack slot. }
            EmitRecAddrToX0(Arg);
            EmitPushX0();
            if NInt >= 8 then
            begin
              StackOff := AlignTo(StackOff, 8);
              PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
              StackOff := StackOff + 8;
            end
            else
            begin
              PopRegs.Add('x' + IntToStr(NInt));
              Inc(NInt);
            end;
          end;
          1:
          begin
            EmitRecAddrToX0(Arg);
            Self.Emit(#9'ldr x0, [x0]');
            EmitPushX0();
            if NInt >= 8 then
            begin
              StackOff := AlignTo(StackOff, 8);
              PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
              StackOff := StackOff + 8;
            end
            else
            begin
              PopRegs.Add('x' + IntToStr(NInt));
              Inc(NInt);
            end;
          end;
          2:
          begin
            EmitRecAddrToX0(Arg);
            Self.Emit(#9'mov x9, x0');
            if NInt >= 7 then
            begin
              { whole 16B aggregate on the stack — two eightbytes }
              StackOff := AlignTo(StackOff, 8);
              Self.Emit(#9'ldr x0, [x9]');
              EmitPushX0();
              PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
              StackOff := StackOff + 8;
              Self.Emit(#9'ldr x0, [x9, #8]');
              EmitPushX0();
              PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
              StackOff := StackOff + 8;
            end
            else
            begin
              Self.Emit(#9'ldr x0, [x9]');
              EmitPushX0();
              PopRegs.Add('x' + IntToStr(NInt));
              Self.Emit(#9'ldr x0, [x9, #8]');
              EmitPushX0();
              PopRegs.Add('x' + IntToStr(NInt + 1));
              NInt := NInt + 2;
            end;
          end;
        else
          { HFA of (Shape - 100) Doubles in d(NFloat).. — address computed
            once into x9 (a subscript index is not re-evaluated).  Overflow
            (leg 29): all lanes travel as consecutive 8-byte stack slots. }
          EmitRecAddrToX0(Arg);
          Self.Emit(#9'mov x9, x0');
          if NFloat + (Shape - 100) > 8 then
            for K := 0 to (Shape - 100) - 1 do
            begin
              StackOff := AlignTo(StackOff, 8);
              Self.Emit(Format(#9'ldr x0, [x9, #%d]', [K * 8]));
              EmitPushX0();
              PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
              StackOff := StackOff + 8;
            end
          else
          begin
            for K := 0 to (Shape - 100) - 1 do
            begin
              Self.Emit(Format(#9'ldr x0, [x9, #%d]', [K * 8]));
              EmitPushX0();
              PopRegs.Add('d' + IntToStr(NFloat + K));
            end;
            NFloat := NFloat + (Shape - 100);
          end;
        end;
      end
      else if IsIntfArg(ADecl, I, Arg) then
      begin
        { fat pointer: obj + itab in two consecutive int registers.
          The callee makes its own co-owning copy (by-value retains in
          the prologue), so the caller passes a borrow. }
        { any interface source (variable, field, element, P^, call result,
          class narrowing) through the shared pair lowering.  An OWNED obj
          half (a call result) is parked for one post-call release, the
          class-transient rule (shape 'C'); a borrowed one is passed as is. }
        if I < ADecl.Params.Count then
          IntfT := TMethodParam(ADecl.Params.Items[I]).ResolvedType
        else
          IntfT := Arg.ResolvedType;
        if EmitIntfPairToX0X1(Arg, IntfT) then
        begin
          if TransN >= STRTRANS_SLOTS then
            NotYet('more than 8 owned transient args in one call', Arg);
          Self.Emit(#9'str x1, [sp, #-16]!');
          EmitStoreSlot('x0', Format('__strtrans_%d', [TransN]));
          Self.Emit(#9'ldr x1, [sp], #16');
          TransShapes := TransShapes + 'C';
          Inc(TransN);
        end;
        { obj then itab, matching the PopRegs order (pops run in reverse) }
        EmitPushX0();
        Self.Emit(#9'str x1, [sp, #-16]!');
        if NInt >= 7 then
        begin
          { whole fat pointer on the stack — obj then itab, two eightbytes }
          StackOff := AlignTo(StackOff, 8);
          PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
          StackOff := StackOff + 8;
          PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
          StackOff := StackOff + 8;
        end
        else
        begin
          PopRegs.Add('x' + IntToStr(NInt));
          PopRegs.Add('x' + IntToStr(NInt + 1));
          NInt := NInt + 2;
        end;
      end
      else if (Arg.ResolvedType <> nil) and
              (Arg.ResolvedType.Kind = tyString) then
      begin
        { the callee owns its copy (by-value params retain in the callee
          prologue; const params borrow), so the caller passes a BORROWED
          pointer.  Caller-side disposal by shape: rc=1 parks for ONE
          post-call release (also for const params); rc=0 parks only for
          const params (pin: AddRef+Release) — a by-value rc=0 arg is
          freed by the callee pair and must NOT be touched again.

          A BORROWED aliasable source (a const/by-value/var param read, a
          global, an implicit-Self field, or a captured local) handed to a
          formal string param must be PINNED: _StringAddRef BEFORE the call,
          _StringRelease AFTER (shape 'P').  Without the pin the callee's
          by-value entry-retain/exit-release pair could drop the borrowed
          source one too many and free it mid-call — the macOS arm64
          FFrame.TryGetValue(const AName) over-release cascade, 2026-07-24.
          x86-64 (ConstStrShape) and QBE (ConstArgMode) both pin this case;
          arm64 previously did not.  A variadic string arg (no formal param)
          has no callee retain/release pair, so it is never pinned. }
        Self.EmitExprToX0(Arg);
        EmitPushX0();
        if ArcExprOwnsRef(Arg) then
        begin
          if TransN >= STRTRANS_SLOTS then
            NotYet('more than 8 owned string transient args in one call', Arg);
          EmitStoreSlot('x0', Format('__strtrans_%d', [TransN]));
          TransShapes := TransShapes + '1';
          Inc(TransN);
        end
        else if ArcExprIsUnownedStrTransient(Arg) and
                (I < ADecl.Params.Count) and
                TMethodParam(ADecl.Params.Items[I]).IsConstParam then
        begin
          if TransN >= STRTRANS_SLOTS then
            NotYet('more than 8 owned string transient args in one call', Arg);
          EmitStoreSlot('x0', Format('__strtrans_%d', [TransN]));
          { PIN NOW, before the call (BUG-20260725-arm64-const-str-param-alias).
            A callee that stores its const parameter into a local retains it and
            releases that local at scope exit; at rc=0 the cycle reaches zero
            and frees OUR transient mid-call, so the old post-call AddRef+Release
            operated on a freed, reused block ("_StringRelease corrupted header"
            from sysutils.ExpandFileName's `Base := APath`).  Pinned, the callee
            cycles 1 -> 2 -> 1 and the bare release after the call disposes it
            exactly once — the same rule shapes 'P', the closure call and the
            property setter already follow. }
          EmitCallSym('_StringAddRef');
          TransShapes := TransShapes + '0';
          Inc(TransN);
        end
        else if (I < ADecl.Params.Count) and
                Self.IsPinnedBorrowedStrArg(Arg,
                  Self.ParamsHaveVarString(ADecl.Params)) then
        begin
          if TransN >= STRTRANS_SLOTS then
            NotYet('more than 8 owned string transient args in one call', Arg);
          EmitStoreSlot('x0', Format('__strtrans_%d', [TransN]));
          { pin NOW (value still in x0), before the call consumes it }
          EmitCallSym('_StringAddRef');
          TransShapes := TransShapes + 'P';
          Inc(TransN);
        end;
        if (ADecl.IsVarArgs and (I >= ADecl.Params.Count)) or (NInt >= 8) then
        begin
          StackOff := AlignTo(StackOff, 8);
          PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
          StackOff := StackOff + 8;
        end
        else
        begin
          PopRegs.Add('x' + IntToStr(NInt));
          Inc(NInt);
        end;
      end
      else if IsFloatExpr(Arg) then
      begin
        IsVariadicArg := ADecl.IsVarArgs and (I >= ADecl.Params.Count);
        Self.EmitExprToD0(Arg);
        Self.Emit(#9'fmov x0, d0');
        EmitPushX0();
        if IsVariadicArg or (NFloat >= 8) then
        begin
          { variadic floats promote to double (8 bytes) }
          StackOff := AlignTo(StackOff, 8);
          PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
          StackOff := StackOff + 8;
        end
        else if FloatArgIsSingle(ADecl, I, Arg) then
        begin
          PopRegs.Add('s' + IntToStr(NFloat));
          Inc(NFloat);
        end
        else
        begin
          PopRegs.Add('d' + IntToStr(NFloat));
          Inc(NFloat);
        end;
      end
      else if (Arg.ResolvedType is TSetTypeDesc) and
              TSetTypeDesc(Arg.ResolvedType).IsJumbo() then
      begin
        { by-value JUMBO set arg: pass the ADDRESS of a bitmap in ONE integer
          register; the callee copies it (prologue pass 2).  The value is
          snapshotted into a per-site frame slot first: a literal lowers sp
          (which would break this push/pop bracket) and an operator result
          lives in the shared _jset_scratch (which a second jumbo arg in the
          same call would overwrite). }
        JTmp := '__jarg_' + IntToStr(FJArgN);
        FJArgN := FJArgN + 1;
        if not FFrame.ContainsKey(JTmp) then
          AddLocal(JTmp, Arg.ResolvedType.RawSize());
        JNB := JumboSetLiteralBytes(Arg);
        Self.EmitExprToX0(Arg);                  { source bitmap address }
        Self.Emit(#9'mov x1, x0');
        EmitSlotAddr('x0', JTmp);
        EmitIntLiteral('x2', Arg.ResolvedType.RawSize());
        EmitCallSym('memcpy');
        if JNB > 0 then
          EmitAddSubImm('add', 'sp', 'sp', JNB); { drop the literal buffer }
        EmitSlotAddr('x0', JTmp);
        EmitPushX0();
        if (ADecl.IsVarArgs and (I >= ADecl.Params.Count)) or (NInt >= 8) then
        begin
          StackOff := AlignTo(StackOff, 8);
          PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
          StackOff := StackOff + 8;
        end
        else
        begin
          PopRegs.Add('x' + IntToStr(NInt));
          Inc(NInt);
        end;
      end
      else if IsMethodPtrType(Arg.ResolvedType) then
      begin
        { closure / method-pointer arg: pass the ADDRESS of the 16-byte fat
          value in ONE integer register; the callee copies it (prologue pass 2).
          A literal materialises into its hidden value slot first
          (EmitAnonValueToSlot yields the slot address in x0); a plain closure
          variable yields its own slot address. }
        IsVariadicArg := ADecl.IsVarArgs and (I >= ADecl.Params.Count);
        if Arg is TAnonMethodExpr then
          EmitAnonValueToSlot(TAnonMethodExpr(Arg))
        else if (Arg is TIdentExpr) and
                (not TIdentExpr(Arg).IsImplicitSelf) and
                (not Self.IsCaptured(TIdentExpr(Arg).Name)) then
          EmitSlotAddr('x0', TIdentExpr(Arg).Name)
        else
          Self.EmitExprToX0(Arg);
        EmitPushX0();
        if IsVariadicArg or (NInt >= 8) then
        begin
          StackOff := AlignTo(StackOff, 8);
          PopRegs.Add(Format('m%d_%d', [StackOff, 8]));
          StackOff := StackOff + 8;
        end
        else
        begin
          PopRegs.Add('x' + IntToStr(NInt));
          Inc(NInt);
        end;
      end
      else if IsIntFam(Arg.ResolvedType) or (Arg is TIntLiteral) or
              (Arg is TNilLiteral) or
              ((Arg.ResolvedType <> nil) and
               (Arg.ResolvedType.Kind in [tyPChar, tyPointer,
                                          tyClass, tyProcedural, tyDynArray,
                                          tyMetaClass])) or
              { A small set is a bitmask that lives in ONE integer register,
                so it passes exactly like an integer (IsUnsignedIntA64 already
                classes it unsigned).  A JUMBO set is a byte-array bitmap with
                its own ABI and is still a hole — the same split the local-var
                gate makes.  Without this, any call taking a set argument was
                unreachable on arm64 (e.g. AssertRunsOn(AllBackends, ...) in
                cp.test.e2e.base, which blocked the whole e2e test runner). }
              ((Arg.ResolvedType <> nil) and
               (Arg.ResolvedType.Kind = tySet) and
               not TSetTypeDesc(Arg.ResolvedType).IsJumbo()) then
      begin
        { A dyn-array argument is an 8-byte ref-counted data pointer.  The callee
          owns its copy (a by-value dyn-array param retains in the prologue; a
          const param borrows), so the caller passes a BORROWED pointer — the
          same single-register pass as a class/pointer arg.  (An owned-transient
          dyn-array arg — a function returning a dyn-array passed straight to a
          call — would need post-call disposal like the string path; not yet
          exercised, so kept simple.)  A fat proc (method-ptr / closure) is
          handled by the IsMethodPtrType arm above; only a PLAIN proc pointer
          reaches here. }
        IsVariadicArg := ADecl.IsVarArgs and (I >= ADecl.Params.Count);
        Self.EmitExprToX0(Arg);
        EmitPushX0();
        if (Arg.ResolvedType <> nil) and
           (Arg.ResolvedType.Kind = tyClass) and ArcExprOwnsRef(Arg) then
        begin
          { owned class transient: the callee borrows it — park the +1
            for one post-call release (shape 'C') }
          if TransN >= STRTRANS_SLOTS then
            NotYet('more than 8 owned transient args in one call', Arg);
          EmitStoreSlot('x0', Format('__strtrans_%d', [TransN]));
          TransShapes := TransShapes + 'C';
          Inc(TransN);
        end;
        if IsVariadicArg or (NInt >= 8) then
        begin
          if I < ADecl.Params.Count then
            ASz := StackParamSize(TMethodParam(ADecl.Params.Items[I]))
          else
            ASz := StackArgSize(Arg);
          StackOff := AlignTo(StackOff, ASz);
          PopRegs.Add(Format('m%d_%d', [StackOff, ASz]));
          StackOff := StackOff + ASz;
        end
        else
        begin
          PopRegs.Add('x' + IntToStr(NInt));
          Inc(NInt);
        end;
      end
      else
        NotYet('call argument of this type', Arg);
    end;
    { pop last-pushed-first into each value's pre-assigned register }
    for I := PopRegs.Count - 1 downto 0 do
    begin
      Reg := PopRegs.Strings[I];
      if Copy(Reg, 0, 1) = 'm' then
      begin
        { memory-class arg: the outgoing area sits ABOVE the still-pushed
          eval slots — I of them remain (16 bytes each) at pop time }
        EmitPopTo('x9');
        DecodeMemArg(Reg, StackOff, ASz);
        if ASz = 4 then
          Self.Emit(Format(#9'str w9, [sp, #%d]', [I * 16 + StackOff]))
        else
          Self.Emit(Format(#9'str x9, [sp, #%d]', [I * 16 + StackOff]));
      end
      else if Copy(Reg, 0, 1) = 'd' then
      begin
        EmitPopTo('x9');
        Self.Emit(Format(#9'fmov %s, x9', [Reg]));
      end
      else if Copy(Reg, 0, 1) = 's' then
      begin
        { Single arg: the stacked value is the DOUBLE bit pattern —
          rebuild d(N) and narrow into s(N) (same register, legal) }
        EmitPopTo('x9');
        Self.Emit(Format(#9'fmov d%s, x9', [Copy(Reg, 1, Length(Reg) - 1)]));
        Self.Emit(Format(#9'fcvt %s, d%s',
          [Reg, Copy(Reg, 1, Length(Reg) - 1)]));
      end
      else
        EmitPopTo(Reg);
    end;
  finally
    PopRegs.Free();
  end;
  if ASretDest <> '' then
    { record sret: the callee writes through x8 (set AFTER the arg pops —
      nothing below clobbers it before the call) }
    EmitSlotAddr('x8', ASretDest)
  else if ASretSpOff >= 0 then
    { same, for a caller scratch buffer that has no slot name: the offset was
      measured at OUR entry, and our outgoing-arg area is still subtracted
      here (the pop walk above restored only the eval slots), so add it back. }
    EmitAddSubImm('add', 'x8', 'sp', ASretSpOff + StackArea);
  if AVirtSlot = VIRT_INDIRECT then
  begin
    { through the procedural value's code word (EmitFatPtrCall) }
    EmitLoadSlot('x10', IndSlot);
    Self.Emit(#9'ldr x9, [x10]');
    Self.Emit(#9'blr x9');
  end
  else if AVirtSlot >= 0 then
  begin
    { virtual dispatch: vtable at instance[0]; slot 0 is the typeinfo
      back-pointer, so method slots start at +8 }
    Self.Emit(#9'ldr x9, [x0]');
    Self.Emit(Format(#9'ldr x9, [x9, #%d]', [(AVirtSlot + 1) * 8]));
    Self.Emit(#9'blr x9');
  end
  else
    Self.Emit(Format(#9'bl %s', [RoutineSym(ADecl, AName)]));
  { C ABI boundary: a C function returning a 32-bit int leaves the value
    in w0 ONLY — bits 32-63 of x0 are UNDEFINED per AAPCS64.  Blaise
    code consumes full x0, so normalise an external's sub-64-bit result
    to its declared width here.  Intermittent by nature (the garbage
    depends on the libSystem build and code path) — open()/stat() on the
    M1 misread as negative/huge; SMOKE_MAC_FILEIO_HANDOVER.md has the
    interposer proof.  Internal Blaise calls stay untouched: both sides
    are ours and already 64-bit-clean. }
  if (ADecl <> nil) and ADecl.IsExternal and
     (ADecl.ResolvedReturnType <> nil) and
     (ADecl.ResolvedReturnType.RawSize() < 8) then
    EmitNarrowX0(ADecl.ResolvedReturnType);
  { Re-widen the slot of every NARROW variable we passed by var/out.  The callee
    stored only the declared width — it must, since the target could be a 4-byte
    record field — but a variable's SLOT is 8 bytes and is read 64-bit, so its
    upper bytes are now stale.  Same family as the external-result narrowing just
    above: a value that is correct at its own width but wrong when widened.
    Only a plain slot needs it: a var-param forward holds an ADDRESS, a captured
    var lives behind '_cap_', and an implicit-Self field is not a slot at all —
    those three are exactly the cases EmitRecIdentAddr routes away from
    EmitSlotAddr (BUG-20260726-arm64-varparam-slot-not-rewidened). }
  NarrowFix := False;
  for I := 0 to AArgs.Count - 1 do
    if (I < ADecl.Params.Count) and
       TMethodParam(ADecl.Params.Items[I]).IsVarParam then
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      if IsRewidenableVarSlot(Arg) then
        NarrowFix := True;
    end;
  if NarrowFix then
  begin
    EmitPushX0();                     { the call result must survive this }
    for I := 0 to AArgs.Count - 1 do
      if (I < ADecl.Params.Count) and
         TMethodParam(ADecl.Params.Items[I]).IsVarParam then
      begin
        Arg := TASTExpr(AArgs.Items[I]);
        if IsRewidenableVarSlot(Arg) then
          EmitNormaliseNarrowSlot(TIdentExpr(Arg).Name, Arg.ResolvedType);
      end;
    EmitPopTo('x0');
  end;
  if TransN > 0 then
  begin
    { the call result must survive the releases -- ALL of its registers: a
      two-eightbyte record comes back in x0:x1 and an HFA in d0..d3.  Saving
      only x0/d0 let the release call clobber x1, so B := F(S + ...) with a
      16-byte record result got a garbage second half (TUuid.Parse with an
      owned-transient string argument). }
    Self.Emit(#9'stp x0, x1, [sp, #-16]!');
    Self.Emit(#9'stp d0, d1, [sp, #-16]!');
    Self.Emit(#9'stp d2, d3, [sp, #-16]!');
    for I := 0 to TransN - 1 do
    begin
      { reload from the x29-relative park slot — stable across the arg pushes,
        the pop-walk, and the two result-preserving pushes above (the old
        sp-relative offset drifted with all three and freed the wrong string). }
      EmitLoadSlot('x0', Format('__strtrans_%d', [I]));
      if Copy(TransShapes, I, 1) = 'C' then
      begin
        { owned class transient: one release drops the borrowed +1 }
        EmitCallSym('_ClassRelease');
        Continue;
      end;
      { shapes '0' and 'P' both had their _StringAddRef emitted BEFORE the
        call, so this bare release just balances it.  Shape '1' (rc=1 owned
        transient) also lands here for its single release. }
      EmitCallSym('_StringRelease');
    end;
    Self.Emit(#9'ldp d2, d3, [sp], #16');
    Self.Emit(#9'ldp d0, d1, [sp], #16');
    Self.Emit(#9'ldp x0, x1, [sp], #16');
  end;
  if StackArea > 0 then
    EmitAddSubImm('add', 'sp', 'sp', StackArea);
end;

{ ---- data sections ------------------------------------------------------- }

procedure TArm64Backend.EmitStrLitSection;
var
  I, Len: Integer;
begin
  if FStrLits.Count = 0 then Exit;
  Self.Emit(SecRodata());
  for I := 0 to FStrLits.Count - 1 do
  begin
    Len := Length(FStrLits.Strings[I]);
    Self.Emit('.balign 4');
    Self.Emit(Format('__s%d:', [I]));
    Self.Emit(#9'.word -1');                    { refcnt = immortal }
    Self.Emit(Format(#9'.word %d', [Len]));     { length }
    Self.Emit(Format(#9'.word %d', [Len]));     { capacity }
    if Len > 0 then
      Self.Emit(Format(#9'.ascii "%s"', [AsmEscape(FStrLits.Strings[I])]));
    Self.Emit(#9'.byte 0');
  end;
end;

procedure TArm64Backend.EmitFloatLitSection;
var
  I: Integer;
begin
  if FFloatLits.Count = 0 then Exit;
  Self.Emit(SecRodata());
  for I := 0 to FFloatLits.Count - 1 do
  begin
    Self.Emit('.balign 8');
    Self.Emit(Format('__d%d:', [I]));
    Self.Emit(Format(#9'.double %s', [FFloatLits.Strings[I]]));
  end;
end;

procedure TArm64Backend.EmitGlobalsSection;
var
  I, J: Integer;
  Directive: string;
  AnyBss, AnyData: Boolean;
begin
  if FGlobalNames.Count = 0 then Exit;
  AnyBss := False;
  AnyData := False;
  for I := 0 to FGlobalNames.Count - 1 do
    if FGlobalInits.ContainsKey(FGlobalNames.Strings[I]) then
      AnyData := True
    else
      AnyBss := True;
  if AnyBss then
  begin
    Self.Emit(SecBss());
    for I := 0 to FGlobalNames.Count - 1 do
    begin
      if FGlobalInits.ContainsKey(FGlobalNames.Strings[I]) then Continue;
      Self.Emit('.balign 8');
      if FGlobalWeak.IndexOf(FGlobalNames.Strings[I]) >= 0 then
        EmitWeakDef('_g_' + FGlobalNames.Strings[I])
      else
        EmitGloblDef('_g_' + FGlobalNames.Strings[I]);
      Self.Emit(Format('_g_%s:', [FGlobalNames.Strings[I]]));
      if FGlobalSize.TryGetValue(FGlobalNames.Strings[I], J) then
        Self.Emit(Format(#9'.zero %d', [J]))
      else
        Self.Emit(#9'.zero 8');
    end;
  end;
  if AnyData then
  begin
    Self.Emit(SecData());
    for I := 0 to FGlobalNames.Count - 1 do
    begin
      if not FGlobalInits.TryGetValue(FGlobalNames.Strings[I], Directive) then
        Continue;
      Self.Emit('.balign 8');
      if FGlobalWeak.IndexOf(FGlobalNames.Strings[I]) >= 0 then
        EmitWeakDef('_g_' + FGlobalNames.Strings[I])
      else
        EmitGloblDef('_g_' + FGlobalNames.Strings[I]);
      Self.Emit(Format('_g_%s:', [FGlobalNames.Strings[I]]));
      Self.Emit(Directive);
    end;
  end;
  if FGlobalStrInits.Count > 0 then
  begin
    { immortal blobs for string-initialised globals: refcnt -1, length,
      capacity, bytes, NUL — the __gi_<sym>_d label sits AT the data so
      the .data pointer needs no symbol arithmetic }
    Self.Emit(SecRodata());
    for I := 0 to FGlobalStrInits.Count - 1 do
    begin
      Self.Emit('.balign 4');
      Self.Emit(Format('__gi_%s_h:', [FGlobalStrInits.Strings[I]]));
      Self.Emit(#9'.word -1');
      Self.Emit(Format(#9'.word %d', [Length(FGlobalStrVals.Strings[I])]));
      Self.Emit(Format(#9'.word %d', [Length(FGlobalStrVals.Strings[I])]));
      Self.Emit(Format('__gi_%s_d:', [FGlobalStrInits.Strings[I]]));
      if Length(FGlobalStrVals.Strings[I]) > 0 then
        Self.Emit(Format(#9'.ascii "%s"',
          [AsmEscape(FGlobalStrVals.Strings[I])]));
      Self.Emit(#9'.byte 0');
    end;
  end;
end;

{ ---- classes ------------------------------------------------------------- }

function TArm64Backend.ClassPrefixOwner(const AOwner: string): string;
begin
  { mirror of TCodeGenQBE.ClassUnitPrefixOwner: the program name and the
    unmangled RTL units keep bare class symbols }
  Result := '';
  if AOwner = '' then Exit;
  if (FProgramName <> '') and SameText(AOwner, FProgramName) then Exit;
  if SameText(AOwner, 'System') then Exit;
  if (Length(AOwner) >= 4) and SameText(Copy(AOwner, 0, 4), 'rtl.') then Exit;
  if (Length(AOwner) >= 7) and SameText(Copy(AOwner, 0, 7), 'blaise_') then Exit;
  Result := CodegenMangle(AOwner) + '_';
end;

function TArm64Backend.PropAccessorSym(const AOwnerType,
  AMethod: string): string;
var
  D: TTypeDesc;
  Pfx: string;
begin
  { mirror of TCodeGenQBE.PropAccessorTarget's direct-call arm }
  Pfx := '';
  if FSymTable <> nil then
  begin
    D := FSymTable.FindType(AOwnerType);
    { The prefix must be spelled exactly as the method DEFINITION's name is:
      that comes from the semantic pass's MangleUnitPrefix, which turns a
      DOTTED unit's dots into underscores ('async.fibers' -> 'async_fibers_').
      ClassPrefixOwner keeps the dot (right for typeinfo / class-name
      symbols, wrong here), so the getter reference dangled -- the Mach-O
      linker bound it to libSystem and dyld aborted at launch
      (TTimerHeap.Count in the fiber scheduler).  ClassPrefixOwner still
      decides WHETHER a prefix applies (program / System / RTL units: none). }
    if (D <> nil) and (ClassPrefixOwner(D.OwningUnit) <> '') then
      Pfx := MangleUnitPrefix(D.OwningUnit);
  end;
  Result := DarwinSym(Pfx + CodegenMangle(AOwnerType) + '_' +
    CodegenMangle(AMethod));
end;

procedure TArm64Backend.EmitTypeinfoAddr(const AReg, ATypeName: string);
var
  Sym: string;
begin
  { single source of truth for the typeinfo symbol (TypeinfoSymFor): prefixed
    for a plain class/interface, bare for a generic instance — so this reference
    always matches the definition and the impllist (LINK-1). }
  Sym := TypeinfoSymFor(ATypeName);
  Self.Emit(Format(#9'adrp %s, %s@PAGE', [AReg, Sym]));
  Self.Emit(Format(#9'add %s, %s, %s@PAGEOFF', [AReg, AReg, Sym]));
end;

function TArm64Backend.IntfItabSym(const AClassName,
  AIntfName: string): string;
var
  D: TTypeDesc;
  Pfx: string;
begin
  { A GENERIC INSTANCE's itab is ALWAYS bare (like ClassSym / impllist) — its
    OwningUnit is the analysing compilation, not stable across units, so a
    unit prefix would give the emission site and the use site DIFFERENT itab
    names and defeat the weak cross-unit dedup (BUG-004).  Keep it bare so the
    weak itab matches the bare impllist and the H:=B assignment reference. }
  if Pos('<', AClassName) >= 0 then
    Exit(DarwinSym('itab_' + CodegenMangle(AClassName) + '_' +
      CodegenMangle(AIntfName)));
  Pfx := '';
  if FSymTable <> nil then
  begin
    D := FSymTable.FindType(AClassName);
    if D <> nil then
      Pfx := ClassPrefixOwner(D.OwningUnit);
  end;
  Result := DarwinSym('itab_' + Pfx + CodegenMangle(AClassName) + '_' +
    CodegenMangle(AIntfName));
end;

function TArm64Backend.ClassSym(ATD: TTypeDecl): string;
var
  D: TRecordTypeDesc;
begin
  { generic instances are ALWAYS bare — the same instance is materialised
    by every compilation that touches it, so its symbols must be
    unit-independent (emitted weak; the linker dedups — BUG-004) }
  if Pos('<', ATD.Name) >= 0 then
    Exit(CodegenMangle(ATD.Name));
  D := ClassDescOf(ATD);
  Result := ClassPrefixOwner(D.OwningUnit) + CodegenMangle(ATD.Name);
end;

function TArm64Backend.ClassDescOf(ATD: TTypeDecl): TRecordTypeDesc;
var
  D: TTypeDesc;
begin
  D := TTypeDesc(ATD.ResolvedDesc);
  if (D = nil) and (FSymTable <> nil) then
    D := FSymTable.FindType(ATD.Name);
  if (D = nil) or not (D is TRecordTypeDesc) then
    NotYet('unresolved class ''' + ATD.Name + '''', nil);
  Result := TRecordTypeDesc(D);
end;

procedure TArm64Backend.EmitClassCleanupFns;
var
  I: Integer;
  TD: TTypeDecl;
  RT, Walk: TRecordTypeDesc;
  Sym: string;
begin
  { _FieldCleanup_<T>(self): invoked by _ClassRelease at refcount zero.
    Calls the nearest user Destroy in the chain once, then releases the
    managed fields (inherited fields are merged into this class's list
    by the semantic pass, so one walk covers everything). }
  Self.Emit('');
  EmitWeakDef(FieldCleanupSym('TObject'));
  Self.Emit(FieldCleanupSym('TObject') + ':');
  Self.Emit(#9'ret');
  Self.Emit('');
  EmitWeakDef(FieldCleanupSym('TCustomAttribute'));
  Self.Emit(FieldCleanupSym('TCustomAttribute') + ':');
  Self.Emit(#9'ret');
  for I := 0 to FClassDecls.Count - 1 do
  begin
    TD := TTypeDecl(FClassDecls.Items[I]);
    RT := ClassDescOf(TD);
    Sym := FieldCleanupSym(ClassSym(TD));
    Self.Emit('');
    if (Pos('<', TD.Name) >= 0) or
       IsUnmangledUnit(ClassDescOf(TD).OwningUnit) then
      EmitWeakDef(Sym)
    else
      EmitGloblDef(Sym);
    Self.Emit(Sym + ':');
    Self.Emit(#9'stp x29, x30, [sp, #-16]!');
    Self.Emit(#9'mov x29, sp');
    Self.Emit(#9'str x19, [sp, #-16]!');
    Self.Emit(#9'mov x19, x0');
    Walk := RT;
    while Walk <> nil do
    begin
      if Walk.HasDestroyMethod then
      begin
        if Walk.DestroyResolvedQbeName <> '' then
          Self.Emit(Format(#9'bl %s',
            [DarwinSym(CodegenMangle(Walk.DestroyResolvedQbeName))]))
        else
          Self.Emit(Format(#9'bl %s',
            [DarwinSym(CodegenMangle(Walk.Name) + '_Destroy')]));
        Break;
      end;
      Walk := Walk.Parent;
    end;
    Self.EmitRecordFieldReleases(RT, 'x19');
    Self.Emit(#9'ldr x19, [sp], #16');
    { Re-anchor sp from the frame pointer before restoring the pair, like
      every other epilogue the backend emits.  The pushes here are balanced
      today, so this is not a live bug — but it was the one epilogue shape
      that would load GARBAGE INTO x29 if the release walk above ever left sp
      displaced, and a corrupted x29 is exactly the failure that cost a
      round to find (2026-07-23).  Cheap insurance. }
    Self.Emit(#9'mov sp, x29');
    Self.Emit(#9'ldp x29, x30, [sp], #16');
    Self.Emit(#9'ret');
  end;
end;

procedure TArm64Backend.EmitArrayConstData(ABlock: TBlock);
var
  I, J, K: Integer;
  CD: TConstDecl;
  Decl: TMethodDecl;
  Lbl, Dir: string;

  procedure EmitOne(ACD: TConstDecl; const ALbl: string);
  var
    E: Integer;
  begin
    { A unit's INTERFACE-section const is referenced from other separately-
      compiled .o files under incremental compilation and must be exported;
      an implementation- or program-level const is never referenced across
      a .o boundary and stays local (its mangled label is only unique within
      one compile — see NewArrayConstLabel). }
    if ACD.IsExportedConst then
      Self.Emit(Format('.globl %s', [ALbl]));
    { jumbo-set byte blobs share this pass }
    if (ACD.ConstSetBytes <> nil) and (ACD.ConstSetBytes.Count > 0) then
    begin
      Self.Emit(SecRodata());
      Self.Emit('.balign 8');
      Self.Emit(ALbl + ':');
      for E := 0 to ACD.ConstSetBytes.Count - 1 do
        Self.Emit(Format(#9'.byte %s', [ACD.ConstSetBytes.Strings[E]]));
      Exit;
    end;
    if not ACD.IsArrayConst then Exit;
    if (ACD.ArrayElements = nil) or (ACD.ArrayElements.Count = 0) then Exit;
    if SameText(ACD.ArrayElemType, 'string') then
    begin
      { per-element immortal blobs, label-at-data (.quad takes bare
        symbols only) — same scheme as string-initialised globals.
        The POINTER TABLE goes to .data: dyld must rebase each entry
        (PIE), and rebases in a read-only segment are impossible —
        the Mach-O linker rejects them.  The character blobs are
        pointer-free and stay in .rodata. }
      Self.Emit(SecData());
      Self.Emit('.balign 8');
      Self.Emit(ALbl + ':');
      for E := 0 to ACD.ArrayElements.Count - 1 do
        Self.Emit(Format(#9'.quad __bce_%s_%d', [ALbl, E]));
      Self.Emit(SecRodata());
      for E := 0 to ACD.ArrayElements.Count - 1 do
      begin
        Self.Emit('.balign 4');
        Self.Emit(Format('__bce_%s_%d_h:', [ALbl, E]));
        Self.Emit(#9'.word -1');
        Self.Emit(Format(#9'.word %d',
          [Length(ACD.ArrayElements.Strings[E])]));
        Self.Emit(Format(#9'.word %d',
          [Length(ACD.ArrayElements.Strings[E])]));
        Self.Emit(Format('__bce_%s_%d:', [ALbl, E]));
        if Length(ACD.ArrayElements.Strings[E]) > 0 then
          Self.Emit(Format(#9'.ascii "%s"',
            [AsmEscape(ACD.ArrayElements.Strings[E])]));
        Self.Emit(#9'.byte 0');
      end;
      Exit;
    end;
    Self.Emit(SecRodata());
    Self.Emit('.balign 8');
    Self.Emit(ALbl + ':');
    if SameText(ACD.ArrayElemType, 'Byte') or
       SameText(ACD.ArrayElemType, 'Boolean') then
      Dir := #9'.byte '
    else if SameText(ACD.ArrayElemType, 'SmallInt') or
            SameText(ACD.ArrayElemType, 'Word') then
      Dir := #9'.hword '
    else if SameText(ACD.ArrayElemType, 'Int64') or
            SameText(ACD.ArrayElemType, 'UInt64') then
      Dir := #9'.quad '
    else if SameText(ACD.ArrayElemType, 'Double') then
      Dir := #9'.double '
    else if SameText(ACD.ArrayElemType, 'Single') then
      Dir := #9'.float '
    else
      Dir := #9'.word ';
    for E := 0 to ACD.ArrayElements.Count - 1 do
      Self.Emit(Dir + ACD.ArrayElements.Strings[E]);
  end;

begin
  { array-typed (and jumbo-set) constants become .rodata blobs so subscripts
    resolve their ConstArraySymbol labels.  Covers block-level consts and
    local consts inside routine bodies. }
  if ABlock = nil then Exit;
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    if CD.ResolvedQbeName <> '' then
      Lbl := CodegenMangle(CD.ResolvedQbeName)
    else if CD.ResolvedSetQbeName <> '' then
      Lbl := CodegenMangle(CD.ResolvedSetQbeName)
    else
      Lbl := CodegenMangle(CD.Name);
    EmitOne(CD, Lbl);
  end;
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if Decl.Body = nil then Continue;
    for J := 0 to Decl.Body.ConstDecls.Count - 1 do
    begin
      CD := TConstDecl(Decl.Body.ConstDecls.Items[J]);
      if CD.ResolvedQbeName <> '' then
        Lbl := CodegenMangle(CD.ResolvedQbeName)
      else if CD.ResolvedSetQbeName <> '' then
        Lbl := CodegenMangle(CD.ResolvedSetQbeName)
      else
        Lbl := CodegenMangle(CD.Name);
      EmitOne(CD, Lbl);
    end;
  end;
  { class-method bodies carry local consts too — walk THIS block's class
    decls (not FClassDecls, which spans blocks and would double-emit) }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    if not (TTypeDecl(ABlock.TypeDecls.Items[I]).Def is TClassTypeDef) then
      Continue;
    for J := 0 to TClassTypeDef(
      TTypeDecl(ABlock.TypeDecls.Items[I]).Def).Methods.Count - 1 do
    begin
      Decl := TMethodDecl(TClassTypeDef(
        TTypeDecl(ABlock.TypeDecls.Items[I]).Def).Methods.Items[J]);
      if Decl.Body = nil then Continue;
      for K := 0 to Decl.Body.ConstDecls.Count - 1 do
      begin
        CD := TConstDecl(Decl.Body.ConstDecls.Items[K]);
        if CD.ResolvedQbeName <> '' then
          Lbl := CodegenMangle(CD.ResolvedQbeName)
        else if CD.ResolvedSetQbeName <> '' then
          Lbl := CodegenMangle(CD.ResolvedSetQbeName)
        else
          Lbl := CodegenMangle(CD.Name);
        EmitOne(CD, Lbl);
      end;
    end;
  end;
end;

function TArm64Backend.TypeinfoSymFor(const ATypeName: string): string;
var
  D: TTypeDesc;
  Pfx: string;
  I: Integer;
begin
  { typeinfo symbol for a class/interface NAME — the SINGLE source of truth for
    both the definition and every reference (so they always agree; a mismatch
    dangles at link and breaks Supports/is/as identity at runtime).  Mirrors
    x86-64 IntfTypeInfoName: a GENERIC INSTANCE (name carries '<') is bare
    (weak, dedup'd cross-unit), a plain class/interface is owning-unit prefixed. }
  if Pos('<', ATypeName) >= 0 then
    Exit(TypeinfoSym(CodegenMangle(ATypeName)));
  Pfx := '';
  if FSymTable <> nil then
  begin
    D := FSymTable.FindType(ATypeName);
    if D <> nil then
      Pfx := ClassPrefixOwner(D.OwningUnit);
  end;
  if Pfx = '' then
    { FindType cannot see a class declared in a unit's IMPLEMENTATION
      section, so its owning-unit prefix came back empty and the reference
      was emitted BARE while EmitClassMetaSections defined the symbol through
      ClassSym — i.e. prefixed.  The two disagreed and the reference dangled
      (page reference to undefined symbol typeinfo_<Class>, e.g. every
      RegisterTest of an implementation-section test class).  FClassDecls is
      the authoritative list of the classes being emitted, so resolve through
      the SAME ClassSym the definition uses. }
    for I := 0 to FClassDecls.Count - 1 do
      if SameText(TTypeDecl(FClassDecls.Items[I]).Name, ATypeName) then
        Exit(TypeinfoSym(ClassSym(TTypeDecl(FClassDecls.Items[I]))));
  Result := TypeinfoSym(Pfx + CodegenMangle(ATypeName));
end;

procedure TArm64Backend.EmitAttrTables(ACD: TClassTypeDef;
  const ACSym: string; out AAttrsRef, AMethAttrsRef: string);
var
  J, K, N, Count: Integer;
  AU: TAttributeUse;
  MD: TMethodDecl;
begin
  { attrs_<C>: count then (attr typeinfo, factory thunk) pairs;
    methattrs_<C>: count then (method name, attr typeinfo, thunk) triples
    for PUBLISHED methods.  Emitted into .data (the entries carry
    relocations); the method-name blobs go to .rodata first so the
    tables' .quad runs are not interleaved. }
  AAttrsRef := '0';
  AMethAttrsRef := '0';

  Count := 0;
  for J := 0 to ACD.AttrUses.Count - 1 do
    if TAttributeUse(ACD.AttrUses.Items[J]).ThunkDecl <> nil then
      Count := Count + 1;
  if Count > 0 then
  begin
    Self.Emit(SecData());
    Self.Emit('.balign 8');
    Self.Emit(Format('attrs_%s:', [ACSym]));
    Self.Emit(Format(#9'.quad %d', [Count]));
    for J := 0 to ACD.AttrUses.Count - 1 do
    begin
      AU := TAttributeUse(ACD.AttrUses.Items[J]);
      if AU.ThunkDecl = nil then Continue;
      Self.Emit(Format(#9'.quad %s', [TypeinfoSymFor(AU.ResolvedClassName)]));
      Self.Emit(Format(#9'.quad %s',
        [RoutineSym(TMethodDecl(AU.ThunkDecl), '')]));
    end;
    AAttrsRef := 'attrs_' + ACSym;
  end;

  Count := 0;
  for J := 0 to ACD.Methods.Count - 1 do
  begin
    MD := TMethodDecl(ACD.Methods.Items[J]);
    if not MD.IsPublished then Continue;
    for K := 0 to MD.AttrUses.Count - 1 do
      if TAttributeUse(MD.AttrUses.Items[K]).ThunkDecl <> nil then
        Count := Count + 1;
  end;
  if Count = 0 then Exit;
  { per-entry method-name blobs — the label sits AT the data (bare-symbol
    .quad, same scheme as string globals), prefixed by the class symbol
    so repeated method names across classes cannot collide }
  Self.Emit(SecRodata());
  N := 0;
  for J := 0 to ACD.Methods.Count - 1 do
  begin
    MD := TMethodDecl(ACD.Methods.Items[J]);
    if not MD.IsPublished then Continue;
    for K := 0 to MD.AttrUses.Count - 1 do
    begin
      if TAttributeUse(MD.AttrUses.Items[K]).ThunkDecl = nil then Continue;
      Self.Emit('.balign 4');
      Self.Emit(Format('__ma_%s_%d_h:', [ACSym, N]));
      Self.Emit(#9'.word -1');
      Self.Emit(Format(#9'.word %d', [Length(MD.Name)]));
      Self.Emit(Format(#9'.word %d', [Length(MD.Name)]));
      Self.Emit(Format('__ma_%s_%d:', [ACSym, N]));
      Self.Emit(Format(#9'.ascii "%s"', [MD.Name]));
      Self.Emit(#9'.byte 0');
      N := N + 1;
    end;
  end;
  Self.Emit(SecData());
  Self.Emit('.balign 8');
  Self.Emit(Format('methattrs_%s:', [ACSym]));
  Self.Emit(Format(#9'.quad %d', [Count]));
  N := 0;
  for J := 0 to ACD.Methods.Count - 1 do
  begin
    MD := TMethodDecl(ACD.Methods.Items[J]);
    if not MD.IsPublished then Continue;
    for K := 0 to MD.AttrUses.Count - 1 do
    begin
      AU := TAttributeUse(MD.AttrUses.Items[K]);
      if AU.ThunkDecl = nil then Continue;
      Self.Emit(Format(#9'.quad __ma_%s_%d', [ACSym, N]));
      Self.Emit(Format(#9'.quad %s', [TypeinfoSymFor(AU.ResolvedClassName)]));
      Self.Emit(Format(#9'.quad %s',
        [RoutineSym(TMethodDecl(AU.ThunkDecl), '')]));
      N := N + 1;
    end;
  end;
  AMethAttrsRef := 'methattrs_' + ACSym;
end;

{ Param-signature string for a published method: one character per parameter,
  matching the encoding the testing framework's typed [TestCase] dispatch
  expects.  Mirrors the x86-64 and QBE backends' MethodParamSig (each backend
  keeps its own copy today). }
function Arm64MethodParamSig(AMD: TMethodDecl): string;
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

procedure TArm64Backend.EmitMethodsTable(ACD: TClassTypeDef;
  const ACSym: string; out AMethodsRef: string);
var
  J, N, Count: Integer;
  MD:  TMethodDecl;
  Sig: string;
begin
  { The published-method table _MethodAddress walks (typeinfo[3]):
      methods[0]  = count (Int64)
      methods[1+] = (name-data-ptr, code-ptr, param-sig-data-ptr or 0)
    The name/sig blobs go to .rodata FIRST so the table's .quad run is not
    interleaved, and each label sits AT the data (bare-symbol .quad) — the
    same scheme as the attribute tables' __ma_ blobs above.  Without this
    table arm64 emitted 0 here, so MethodAddress could never resolve a
    published method and the testing framework's dispatch was dead. }
  AMethodsRef := '0';
  Count := 0;
  for J := 0 to ACD.Methods.Count - 1 do
    if TMethodDecl(ACD.Methods.Items[J]).IsPublished then
      Count := Count + 1;
  if Count = 0 then Exit;

  Self.Emit(SecRodata());
  N := 0;
  for J := 0 to ACD.Methods.Count - 1 do
  begin
    MD := TMethodDecl(ACD.Methods.Items[J]);
    if not MD.IsPublished then Continue;
    Self.Emit('.balign 4');
    Self.Emit(Format('__pm_%s_%d_h:', [ACSym, N]));
    Self.Emit(#9'.word -1');
    Self.Emit(Format(#9'.word %d', [Length(MD.Name)]));
    Self.Emit(Format(#9'.word %d', [Length(MD.Name)]));
    Self.Emit(Format('__pm_%s_%d:', [ACSym, N]));
    Self.Emit(Format(#9'.ascii "%s"', [MD.Name]));
    Self.Emit(#9'.byte 0');
    Sig := Arm64MethodParamSig(MD);
    if Sig <> '' then
    begin
      Self.Emit('.balign 4');
      Self.Emit(Format('__ps_%s_%d_h:', [ACSym, N]));
      Self.Emit(#9'.word -1');
      Self.Emit(Format(#9'.word %d', [Length(Sig)]));
      Self.Emit(Format(#9'.word %d', [Length(Sig)]));
      Self.Emit(Format('__ps_%s_%d:', [ACSym, N]));
      Self.Emit(Format(#9'.ascii "%s"', [Sig]));
      Self.Emit(#9'.byte 0');
    end;
    N := N + 1;
  end;

  Self.Emit(SecData());
  Self.Emit('.balign 8');
  Self.Emit(Format('methods_%s:', [ACSym]));
  Self.Emit(Format(#9'.quad %d', [Count]));
  N := 0;
  for J := 0 to ACD.Methods.Count - 1 do
  begin
    MD := TMethodDecl(ACD.Methods.Items[J]);
    if not MD.IsPublished then Continue;
    Self.Emit(Format(#9'.quad __pm_%s_%d', [ACSym, N]));
    Self.Emit(Format(#9'.quad %s', [RoutineSym(MD, '')]));
    if Arm64MethodParamSig(MD) <> '' then
      Self.Emit(Format(#9'.quad __ps_%s_%d', [ACSym, N]))
    else
      Self.Emit(#9'.quad 0');
    N := N + 1;
  end;
  AMethodsRef := 'methods_' + ACSym;
end;

procedure TArm64Backend.EmitClassMetaSections;
var
  I, S: Integer;
  TD: TTypeDecl;
  RT: TRecordTypeDesc;
  E: TVTableEntry;
  Sym, ParentRef, AttrsRef, MethAttrsRef, MethodsRef: string;
begin
  { TObject stubs once per program: root typeinfo, a vtable carrying the
    built-in virtuals, and the class-name blob.  TObject_Destroy /
    TObject_ToString resolve from the RTL at link time. }
  Self.Emit('');
  Self.Emit(SecRodata());
  Self.Emit('.balign 4');
  Self.Emit('__cn_TObject_h:');
  Self.Emit(#9'.word -1');
  Self.Emit(#9'.word 7');
  Self.Emit(#9'.word 7');
  Self.Emit('__cn_TObject:');
  Self.Emit(#9'.ascii "TObject"');
  Self.Emit(#9'.byte 0');
  Self.Emit(SecData());
  Self.Emit('.balign 8');
  EmitWeakDef(TypeinfoSym('TObject'));
  Self.Emit(TypeinfoSym('TObject') + ':');
  Self.Emit(#9'.quad 0');                       { parent }
  Self.Emit(#9'.quad 0');                       { impllist }
  Self.Emit(#9'.quad __cn_TObject');            { class name }
  Self.Emit(#9'.quad 0');                       { published methods }
  Self.Emit(#9'.quad 8');                       { instance size: vptr }
  Self.Emit(Format(#9'.quad %s', [FieldCleanupSym('TObject')]));
  Self.Emit(Format(#9'.quad %s', [VtableSym('TObject')]));
  Self.Emit(#9'.quad 0');                       { class attrs }
  Self.Emit(#9'.quad 0');                       { method attrs }
  EmitWeakDef(VtableSym('TObject'));
  Self.Emit(VtableSym('TObject') + ':');
  Self.Emit(Format(#9'.quad %s', [TypeinfoSym('TObject')]));
  { RTL method labels: RoutineSym prefixes the DEFINITION on Darwin, so these
    references must go through DarwinSym too or the vtable slot dangles }
  Self.Emit(Format(#9'.quad %s', [DarwinSym('TObject_Destroy')]));
  Self.Emit(Format(#9'.quad %s', [DarwinSym('TObject_ToString')]));

  { TCustomAttribute base stubs: attribute classes declare it as their
    parent, so the typeinfo chain needs a real symbol here }
  Self.Emit(SecRodata());
  Self.Emit('.balign 4');
  Self.Emit('__cn_TCustomAttribute_h:');
  Self.Emit(#9'.word -1');
  Self.Emit(#9'.word 16');
  Self.Emit(#9'.word 16');
  Self.Emit('__cn_TCustomAttribute:');
  Self.Emit(#9'.ascii "TCustomAttribute"');
  Self.Emit(#9'.byte 0');
  Self.Emit(SecData());
  Self.Emit('.balign 8');
  EmitWeakDef(TypeinfoSym('TCustomAttribute'));
  Self.Emit(TypeinfoSym('TCustomAttribute') + ':');
  Self.Emit(Format(#9'.quad %s', [TypeinfoSym('TObject')]));
  Self.Emit(#9'.quad 0');
  Self.Emit(#9'.quad __cn_TCustomAttribute');
  Self.Emit(#9'.quad 0');
  Self.Emit(#9'.quad 8');
  Self.Emit(Format(#9'.quad %s', [FieldCleanupSym('TCustomAttribute')]));
  Self.Emit(Format(#9'.quad %s', [VtableSym('TCustomAttribute')]));
  Self.Emit(#9'.quad 0');
  Self.Emit(#9'.quad 0');
  EmitWeakDef(VtableSym('TCustomAttribute'));
  Self.Emit(VtableSym('TCustomAttribute') + ':');
  Self.Emit(Format(#9'.quad %s', [TypeinfoSym('TCustomAttribute')]));
  Self.Emit(Format(#9'.quad %s', [DarwinSym('TObject_Destroy')]));
  Self.Emit(Format(#9'.quad %s', [DarwinSym('TObject_ToString')]));

  for I := 0 to FClassDecls.Count - 1 do
  begin
    TD := TTypeDecl(FClassDecls.Items[I]);
    RT := ClassDescOf(TD);
    Sym := ClassSym(TD);
    Self.Emit(SecRodata());
    Self.Emit('.balign 4');
    Self.Emit(Format('__cn_%s_h:', [Sym]));
    Self.Emit(#9'.word -1');
    Self.Emit(Format(#9'.word %d', [Length(TD.Name)]));
    Self.Emit(Format(#9'.word %d', [Length(TD.Name)]));
    Self.Emit(Format('__cn_%s:', [Sym]));
    Self.Emit(Format(#9'.ascii "%s"', [TD.Name]));
    Self.Emit(#9'.byte 0');
    if (RT.Parent <> nil) and (RT.Parent.Name <> 'TObject') then
      ParentRef := TypeinfoSym(ClassPrefixOwner(RT.Parent.OwningUnit) +
        CodegenMangle(RT.Parent.Name))
    else
      ParentRef := TypeinfoSym('TObject');
    EmitAttrTables(TClassTypeDef(TD.Def), Sym, AttrsRef, MethAttrsRef);
    EmitMethodsTable(TClassTypeDef(TD.Def), Sym, MethodsRef);
    Self.Emit(SecData());
    Self.Emit('.balign 8');
    if (Pos('<', TD.Name) >= 0) or
       IsUnmangledUnit(ClassDescOf(TD).OwningUnit) then
      EmitWeakDef(TypeinfoSym(Sym))
    else
      EmitGloblDef(TypeinfoSym(Sym));
    Self.Emit(TypeinfoSym(Sym) + ':');
    Self.Emit(Format(#9'.quad %s', [ParentRef]));
    if ClassImplementsAny(TD) then
      Self.Emit(Format(#9'.quad %s', [ImpllistSym(Sym)]))
    else
      Self.Emit(#9'.quad 0');
    Self.Emit(Format(#9'.quad __cn_%s', [Sym]));
    Self.Emit(Format(#9'.quad %s', [MethodsRef]));   { published methods }
    { INSTANCE size — the number of bytes ClassCreate allocates and zero-fills
      for one object, i.e. vptr + every field (TotalSize, unpadded for a class
      to match FPC/Delphi InstanceSize).  NOT RawSize(): for a tyClass that
      returns 8, the width of a REFERENCE to the object, so every class was
      allocated at 8 bytes and every field past the vptr read/wrote unmapped
      heap.  x86-64 has always emitted TotalSize() here. }
    Self.Emit(Format(#9'.quad %d', [RT.TotalSize()]));
    Self.Emit(Format(#9'.quad %s', [FieldCleanupSym(Sym)]));
    Self.Emit(Format(#9'.quad %s', [VtableSym(Sym)]));
    Self.Emit(Format(#9'.quad %s', [AttrsRef]));
    Self.Emit(Format(#9'.quad %s', [MethAttrsRef]));
    if (Pos('<', TD.Name) >= 0) or
       IsUnmangledUnit(ClassDescOf(TD).OwningUnit) then
      EmitWeakDef(VtableSym(Sym))
    else
      EmitGloblDef(VtableSym(Sym));
    Self.Emit(VtableSym(Sym) + ':');
    Self.Emit(Format(#9'.quad %s', [TypeinfoSym(Sym)]));
    for S := 0 to RT.VTableCount() - 1 do
    begin
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        Self.Emit(#9'.quad ' + DarwinSym('_AbstractMethodError'))
      else if (Length(E.ImplName) > 0) and
              (StrAt(E.ImplName, 0) = Ord('$')) then
        { ImplName is a QBE label and may carry the $ sigil }
        Self.Emit(Format(#9'.quad %s',
          [DarwinSym(CodegenMangle(StrCopyTail(E.ImplName, 1)))]))
      else
        Self.Emit(Format(#9'.quad %s', [DarwinSym(CodegenMangle(E.ImplName))]));
    end;
  end;
end;

function TArm64Backend.IsIntfArg(ADecl: TMethodDecl; AIndex: Integer;
  AArg: TASTExpr): Boolean;
begin
  { an argument travels as an (obj, itab) pair when its value is an
    interface OR the by-value parameter it binds is one: a CLASS value
    passed to an interface parameter (H.Bind(TC.Create())) is narrowed at
    the call -- passing just the instance pointer left the callee's itab
    half as whatever the next register held }
  Result := (AArg.ResolvedType <> nil) and
            (AArg.ResolvedType.Kind = tyInterface);
  if (not Result) and (AIndex < ADecl.Params.Count) and
     not TMethodParam(ADecl.Params.Items[AIndex]).IsVarParam and
     (TMethodParam(ADecl.Params.Items[AIndex]).ResolvedType <> nil) and
     (TMethodParam(ADecl.Params.Items[AIndex]).ResolvedType.Kind = tyInterface) and
     (AArg.ResolvedType <> nil) and
     (AArg.ResolvedType.Kind in [tyClass, tyPointer]) then
    Result := True;
end;

procedure TArm64Backend.EmitVarArgAddrToX0(Arg: TASTExpr);
begin
  { x0 := the address a var/out parameter receives for the lvalue Arg }
  if (Arg is TIdentExpr) and (Arg.ResolvedType <> nil) and
     (Arg.ResolvedType.Kind = tyInterface) and
     not IsLocal(TIdentExpr(Arg).Name) and
     (TIdentExpr(Arg).ParamMode <> pmVar) and
     not TIdentExpr(Arg).IsImplicitSelf then
    { a global interface's halves are two separate symbols, so the
      pair has no single address to hand over }
    NotYet('var argument from a global interface variable', Arg)
  else if Arg is TIdentExpr then
    { EmitRecIdentAddr handles all three: a var-param forward (slot
      holds the caller's address), an implicit-Self FIELD (Self + field
      offset — the leg-14 case, e.g. LkAddStr(var ..., FDynStrTab)), and
      a plain local/global slot.  Mirrors x86-64 EmitVarArgAddrToRax. }
    EmitRecIdentAddr('x0', TIdentExpr(Arg))
  else if (Arg is TFieldAccessExpr) and
          (TFieldAccessExpr(Arg).FieldInfo <> nil) then
  begin
    if ArcExprOwnsRef(TFieldAccessExpr(Arg).Base) then
      NotYet('var field argument on an owned transient base', Arg);
    EmitRecFieldAddrToX0(TFieldAccessExpr(Arg));
  end
  else if (Arg is TStringSubscriptExpr) and
          (TStringSubscriptExpr(Arg).StrExpr.ResolvedType <> nil) and
          (TStringSubscriptExpr(Arg).StrExpr.ResolvedType.Kind = tyStaticArray) then
    { an array element: the address the element read would load from }
    EmitStaticElemAddr(TStringSubscriptExpr(Arg))
  else if (Arg is TStringSubscriptExpr) and
          (TStringSubscriptExpr(Arg).StrExpr.ResolvedType <> nil) and
          (TStringSubscriptExpr(Arg).StrExpr.ResolvedType.Kind in
            [tyDynArray, tyOpenArray]) then
    EmitDynElemAddr(TStringSubscriptExpr(Arg))
  else if Arg is TDerefExpr then
    { P^: the variable a pointer designates lives at the pointer's value }
    Self.EmitExprToX0(TDerefExpr(Arg).Expr)
  else
    NotYet('var argument from this expression', Arg);
end;

procedure TArm64Backend.EmitIntfDispatch(const AVarName: string;
  AIntf: TInterfaceTypeDesc; AIdx: Integer; AArgs: TObjectList;
  AObjExpr: TASTExpr; AVarParam: Boolean; AImplicitBase: TFieldInfo;
  const ASret: string);
var
  I: Integer;
  Arg: TASTExpr;
  Decl: TMethodDecl;
  Par: TMethodParam;
  Slot, RecvSlot: string;
  Owned: Boolean;
  NInt, NFloat: Integer;
begin
  { itab dispatch through the ordinary call path, like a closure call
    (EmitFatPtrCall): the interface type records each method's var/out flags
    but not its parameter types, so the synthesised declaration types each
    parameter by its ARGUMENT (x86-64's itab dispatch classifies the same
    way -- the semantic pass does not yet check interface-call arguments
    against the declared parameters; see the BUGS.md entry).  EmitCall then
    lowers every argument class it knows -- doubles in d registers, records
    by shape, interfaces as pairs, closures, var/out addresses, owned
    transients released after the call, stack overflow past 8 registers.

    The receiver pair is evaluated FIRST: the obj half becomes Self (pushed,
    ASelfPushed) and the ADDRESS of the method's itab slot is parked in a
    per-site frame slot for VIRT_INDIRECT, which branches through the word
    there.  ASret names a frame scratch the callee fills through x8. }
  { Stack-passed arguments need the DECLARED parameter types: Apple's arm64
    ABI packs stack arguments at their natural size, so an Integer literal
    classified by its own type would be written as 4 bytes where an Int64
    parameter reads 8.  The interface type does not carry parameter types
    yet (BUG-20261004-intf-call-args-unchecked), so a call that would spill
    stays an honest hole; register-passed arguments are unaffected. }
  NInt := 1;                                    { Self }
  NFloat := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if AIntf.MethodParamIsVar(AIdx, I) then
      Inc(NInt)
    else if (Arg.ResolvedType <> nil) and
            (Arg.ResolvedType.Kind = tyInterface) then
      NInt := NInt + 2
    else if (Arg.ResolvedType <> nil) and
            (Arg.ResolvedType.Kind = tyRecord) then
    begin
      case RecReturnShape(TRecordTypeDesc(Arg.ResolvedType)) of
        0, 1: Inc(NInt);
        2: NInt := NInt + 2;
      else
        NFloat := NFloat + RecReturnShape(TRecordTypeDesc(Arg.ResolvedType)) - 100;
      end;
    end
    else if IsFloatExpr(Arg) then
      Inc(NFloat)
    else
      Inc(NInt);
  end;
  if (NInt > 8) or (NFloat > 8) then
    NotYet('interface call with stack-passed arguments', AObjExpr);
  Owned := EmitIntfRecvPair(AVarName, AObjExpr, AVarParam, AImplicitBase,
    AObjExpr);
  Slot := '__icall_' + IntToStr(FJArgN);
  FJArgN := FJArgN + 1;
  if not FFrame.ContainsKey(Slot) then
    AddLocal(Slot, 8);
  if AIdx <> 0 then
    EmitAddSubImm('add', 'x1', 'x1', AIdx * 8);
  EmitStoreSlot('x1', Slot);                    { &itab[AIdx] }
  RecvSlot := '';
  if Owned then
  begin
    { an owned receiver (a call result) outlives the call in its own slot
      and is released once afterwards }
    RecvSlot := '__irecv_' + IntToStr(FJArgN);
    FJArgN := FJArgN + 1;
    if not FFrame.ContainsKey(RecvSlot) then
      AddLocal(RecvSlot, 8);
    EmitStoreSlot('x0', RecvSlot);
  end;
  EmitPushX0();                                 { the receiver obj = Self }
  Decl := TMethodDecl.Create();
  try
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      Par := TMethodParam.Create();
      Par.ParamName := 'A' + IntToStr(I);
      Par.ResolvedType := Arg.ResolvedType;
      if (Par.ResolvedType = nil) and (Arg is TIntLiteral) then
        Par.ResolvedType := FSymTable.TypeInt64;
      Par.IsVarParam := AIntf.MethodParamIsVar(AIdx, I);
      Decl.Params.Add(Par);
    end;
    FIndirectSlot := Slot;
    EmitCall(Decl, '', AArgs, ASret, True, VIRT_INDIRECT);
  finally
    Decl.Free();
  end;
  if RecvSlot <> '' then
  begin
    { keep every result register across the release }
    Self.Emit(#9'stp x0, x1, [sp, #-16]!');
    Self.Emit(#9'stp d0, d1, [sp, #-16]!');
    Self.Emit(#9'stp d2, d3, [sp, #-16]!');
    EmitLoadSlot('x0', RecvSlot);
    EmitCallSym('_ClassRelease');
    Self.Emit(#9'ldp d2, d3, [sp], #16');
    Self.Emit(#9'ldp d0, d1, [sp], #16');
    Self.Emit(#9'ldp x0, x1, [sp], #16');
  end;
end;

procedure TArm64Backend.EmitIntfMetaSections;
var
  I, J, K: Integer;
  ITD, TD: TTypeDecl;
  ID: TInterfaceTypeDesc;
  Intfs: TObjectList;                    { collected TInterfaceTypeDesc; not owned }
  ClassRT, RTWalk: TRecordTypeDesc;
  IntfWalk: TInterfaceTypeDesc;
  Sym, ISym: string;
  IsGen: Boolean;
  IsBareVis: Boolean;
  GII: TGenericInterfaceInstance;
  IDesc: TTypeDesc;
begin
  if (FIntfDecls.Count = 0) and (FClassDecls.Count = 0) and
     (FGenericIntfInstances.Count = 0) then Exit;
  Self.Emit(SecData());
  { interface typeinfo: the address IS the identity token }
  for I := 0 to FIntfDecls.Count - 1 do
  begin
    ITD := TTypeDecl(FIntfDecls.Items[I]);
    { Define the typeinfo under the SAME owning-unit-prefixed symbol that every
      reference (impllist, Supports/is/as via EmitTypeinfoAddr) computes through
      TypeinfoSymFor — a bare definition here dangled the prefixed references at
      link (LINK-1: typeinfo_Streams_IReaderFrom).  A unit-mangled owner keeps
      it .globl; an unmangled RTL unit's copy binds weak so per-object copies
      collapse (GH #174 parity). }
    ISym := TypeinfoSymFor(ITD.Name);
    IDesc := TTypeDesc(ITD.ResolvedDesc);
    if (IDesc = nil) and (FSymTable <> nil) then
      IDesc := FSymTable.FindType(ITD.Name);
    Self.Emit('.balign 8');
    if (IDesc <> nil) and IsUnmangledUnit(IDesc.OwningUnit) then
      EmitWeakDef(ISym)
    else
      EmitGloblDef(ISym);
    Self.Emit(Format('%s:', [ISym]));
    Self.Emit(#9'.quad 0');
  end;
  { typeinfo for generic INTERFACE instances (IComparer<Integer> etc): emitted
    WEAK (bare-named) so any object materialising the same instance carries a
    copy the linker dedups (BUG-004), mirroring x86-64/QBE.  Same 1-quad layout
    as a normal interface — the address is the identity token (leg 41). }
  for I := 0 to FGenericIntfInstances.Count - 1 do
  begin
    GII := TGenericInterfaceInstance(FGenericIntfInstances.Items[I]);
    { mangled — a NESTED generic argument leaves inner '<'/'>' in InstName,
      while references resolve through the mangler; see the x86-64 path for
      the full rationale. }
    Sym := TypeinfoSym(CodegenMangle(GII.InstName));
    Self.Emit('.balign 8');
    EmitWeakDef(Sym);
    Self.Emit(Sym + ':');
    Self.Emit(#9'.quad 0');
  end;
  { itab + impllist per implementing class.  DESCRIPTOR-driven (mirrors
    x86-64/QBE): the implemented-interface set is collected over TWO nested
    dimensions of the resolved type graph — (1) up the CLASS ancestor chain via
    RT.Parent (crosses unit boundaries, unlike a name lookup in FClassDecls;
    BUG-052 F3), and (2) for each implemented interface, up its OWN ancestor
    chain via IntfWalk.Parent (so a base interface of an implemented derived
    interface gets its own itab + impllist entry; BUG-052 F4).  Each collected
    interface — including each inherited base — gets a SEPARATE itab; a base's
    itab is the leading prefix of the derived's (same impl pointers). }
  for I := 0 to FClassDecls.Count - 1 do
  begin
    TD := TTypeDecl(FClassDecls.Items[I]);
    ClassRT := ClassDescOf(TD);
    Intfs := TObjectList.Create(False);   { not owned — descriptors live in the graph }
    try
      RTWalk := ClassRT;
      while RTWalk <> nil do
      begin
        for J := 0 to RTWalk.ImplementsCount() - 1 do
        begin
          IntfWalk := RTWalk.ImplementsIntfAt(J);
          while IntfWalk <> nil do
          begin
            if Intfs.IndexOf(IntfWalk) < 0 then
              Intfs.Add(IntfWalk);
            IntfWalk := IntfWalk.Parent;
          end;
        end;
        RTWalk := RTWalk.Parent;
      end;
      if Intfs.Count = 0 then Continue;
      Sym := ClassSym(TD);
      { A GENERIC INSTANCE (name carries '<') is materialised by every unit
        that touches it, so its itab + impllist must be WEAK bare symbols so
        the linker dedups the copies (BUG-004) — matching how typeinfo/vtable
        are already weak-bound for generics and the x86-64/QBE generic loops. }
      IsGen := Pos('<', TD.Name) >= 0;
      { Visibility of the itab + impllist definitions (LINK-2):
        * generic instance — WEAK bare, deduped across the many objects that
          materialise it (BUG-004);
        * a class in an UNMANGLED RTL unit (System/rtl.*/runtime.*) — also WEAK,
          because such a class's symbols are bare and re-emitted by every object
          that touches it, so a strong .globl would collide (GH #174 parity,
          matching the typeinfo def above and x86-64's BareClass rule);
        * an ordinary class — GLOBL, so the definition in the class's own object
          is visible to an interface assignment / Supports in ANOTHER object
          (without this the cross-object reference dangles at link — LINK-2). }
      IsBareVis := IsGen
        or ((ClassRT <> nil) and IsUnmangledUnit(ClassRT.OwningUnit));
      for J := 0 to Intfs.Count - 1 do
      begin
        ID := TInterfaceTypeDesc(Intfs.Items[J]);
        { a GENERIC INTERFACE instance's typeinfo is now emitted weak by the
          FGenericIntfInstances loop above, so the impllist's typeinfo_<inst>
          reference resolves (leg 41) — no longer an honest hole. }
        ISym := IntfItabSym(TD.Name, ID.Name);
        Self.Emit('.balign 8');
        if IsBareVis then
          EmitWeakDef(ISym)
        else
          EmitGloblDef(ISym);
        Self.Emit(Format('%s:', [ISym]));
        for K := 0 to ID.MethodCount() - 1 do
        begin
          { an ABSTRACT interface method (no implementation) points at the
            abort stub; otherwise the vtable-slot ImplName (correct across
            units and for generic-instance clones). }
          if IsAbstractClassMethod(ClassRT, ID.MethodName(K)) then
            Self.Emit(#9'.quad ' + DarwinSym('_AbstractMethodError'))
          else
            Self.Emit(Format(#9'.quad %s',
              [ItabMethodRefArm64(ClassRT, TD, ID.MethodName(K))]));
        end;
      end;
      Self.Emit('.balign 8');
      { Same visibility rule as the itab above (IsBareVis): weak for a generic
        instance or an unmangled-RTL-unit class, globl for an ordinary class so
        a cross-object Supports / interface-assignment reference resolves. }
      if IsBareVis then
        EmitWeakDef(ImpllistSym(Sym))
      else
        EmitGloblDef(ImpllistSym(Sym));
      Self.Emit(ImpllistSym(Sym) + ':');
      for J := 0 to Intfs.Count - 1 do
      begin
        ID := TInterfaceTypeDesc(Intfs.Items[J]);
        { the SAME symbol the typeinfo is DEFINED under (TypeinfoSymFor) — a bare
          CodegenMangle here mismatched a prefixed definition/reference (LINK-1). }
        Self.Emit(Format(#9'.quad %s', [TypeinfoSymFor(ID.Name)]));
        Self.Emit(Format(#9'.quad %s', [IntfItabSym(TD.Name, ID.Name)]));
      end;
      Self.Emit(#9'.quad 0');
    finally
      Intfs.Free();
    end;
  end;
end;

function TArm64Backend.ClassImplementsAny(ATD: TTypeDecl): Boolean;
var
  J: Integer;
  Walk: TClassTypeDef;
  WalkName: string;
begin
  Result := False;
  Walk := TClassTypeDef(ATD.Def);
  WalkName := ATD.Name;
  while Walk <> nil do
  begin
    if Walk.ImplementsNames.Count > 0 then
    begin
      Result := True;
      Exit;
    end;
    WalkName := Walk.ParentName;
    Walk := nil;
    for J := 0 to FClassDecls.Count - 1 do
      if SameText(TTypeDecl(FClassDecls.Items[J]).Name, WalkName) then
      begin
        Walk := TClassTypeDef(TTypeDecl(FClassDecls.Items[J]).Def);
        Break;
      end;
  end;
end;

function TArm64Backend.FindClassMethodImpl(ATD: TTypeDecl;
  const AName: string): TMethodDecl;
var
  J, K: Integer;
  Walk: TClassTypeDef;
  WalkName: string;
  MD: TMethodDecl;
begin
  { walk the ancestor chain for the nearest implementation }
  Result := nil;
  Walk := TClassTypeDef(ATD.Def);
  WalkName := ATD.Name;
  while Walk <> nil do
  begin
    for K := 0 to Walk.Methods.Count - 1 do
    begin
      MD := TMethodDecl(Walk.Methods.Items[K]);
      if SameText(MD.Name, AName) and (MD.Body <> nil) then
      begin
        Result := MD;
        Exit;
      end;
    end;
    WalkName := Walk.ParentName;
    Walk := nil;
    for J := 0 to FClassDecls.Count - 1 do
      if SameText(TTypeDecl(FClassDecls.Items[J]).Name, WalkName) then
      begin
        Walk := TClassTypeDef(TTypeDecl(FClassDecls.Items[J]).Def);
        Break;
      end;
  end;
end;

function TArm64Backend.IsAbstractClassMethod(AClassRT: TRecordTypeDesc;
  const AMethName: string): Boolean;
var
  Slot: Integer;
begin
  Result := False;
  if AClassRT = nil then Exit;
  Slot := AClassRT.FindVTableSlot(AMethName);
  if Slot < 0 then Exit;
  Result := AClassRT.VTableEntryAt(Slot).IsAbstract;
end;

function TArm64Backend.ItabMethodRefArm64(AClassRT: TRecordTypeDesc;
  ATD: TTypeDecl; const AMethName: string): string;
var
  Slot: Integer;
  E: TVTableEntry;
  Impl: TMethodDecl;
  AncRT: TRecordTypeDesc;
  Sym: string;
begin
  { Prefer the vtable slot's ImplName — it is the fully-qualified label of the
    nearest implementation, correct for a method INHERITED from a (possibly
    cross-unit) ancestor and for a generic-instance clone (CopyVTableFrom
    carries the ImplName down across units).  The QBE ImplName may carry a '$'
    sigil to strip. }
  if AClassRT <> nil then
  begin
    Slot := AClassRT.FindVTableSlot(AMethName);
    if Slot >= 0 then
    begin
      E := AClassRT.VTableEntryAt(Slot);
      if (E <> nil) and (E.ImplName <> '') then
      begin
        if StrAt(E.ImplName, 0) = 36 then   { 36 = '$' }
          Exit(DarwinSym(CodegenMangle(StrCopyTail(E.ImplName, 1))))
        else
          Exit(DarwinSym(CodegenMangle(E.ImplName)));
      end;
    end;
  end;
  { No vtable slot (a non-virtual interface method): fall back to the AST class
    chain for the nearest declaring class + its instance-mangled symbol.  A nil
    result means the implementation is not in this compilation (a non-virtual
    method inherited from a cross-unit ancestor, or an external method with no
    body) — bind it to a bare name would dangle or mis-bind to an unrelated
    global, so keep it an honest error (matching the pre-rewrite behaviour). }
  Impl := FindClassMethodImpl(ATD, AMethName);
  if Impl <> nil then
    Exit(RoutineSym(Impl, AMethName));
  { Not in this compilation's AST -- the declaring ancestor is in another unit.
    Climb the descriptor chain: Parent is populated across units and
    AddMethodSym records every method's emitted symbol, including non-virtual
    ones that have no vtable slot.  First hit is the nearest declarer.  This
    replaces the blanket NotYet below for the case it explicitly called out
    ("a non-virtual method inherited from a cross-unit ancestor"). }
  AncRT := AClassRT;
  while AncRT <> nil do
  begin
    Sym := AncRT.FindMethodSym(AMethName);
    if Sym <> '' then
      Exit(DarwinSym(CodegenMangle(Sym)));
    AncRT := AncRT.Parent;
  end;
  NotYet('implementation of interface method ''' + AMethName + '''', nil);
  Result := '';
end;

procedure TArm64Backend.EmitMethodCallCommon(AMethod: TMethodDecl;
  const AName: string; AArgs: TObjectList);
begin
  { receiver is in x0 — push it (EmitCall pops it back into x0 last) }
  EmitPushX0();
  EmitCall(AMethod, AName, AArgs, '', True, AMethod.VTableSlot);
end;

procedure TArm64Backend.EmitMethodCallOnExpr(AMethod: TMethodDecl;
  const AName: string; AArgs: TObjectList; AObjExpr: TASTExpr);
var
  Owned: Boolean;
  Sz: Integer;
begin
  if AMethod.IsRecordMethod and (AObjExpr.ResolvedType <> nil) and
     (AObjExpr.ResolvedType.Kind = tyRecord) and
     ((AObjExpr is TFuncCallExpr) or (AObjExpr is TMethodCallExpr)) then
  begin
    { a record VALUE returned by a call is the receiver
      (TUuid.RandomUuid().ToBytes()).  A record method's Self is an ADDRESS,
      so the result is materialised and copied into a stack temp that lives
      across the call -- __rret itself may be reused while the arguments
      evaluate.  A managed record's temp would also need its fields
      released afterwards; that stays an honest hole. }
    if AggHasManaged(AObjExpr.ResolvedType) then
      NotYet('method call on a managed record call result', AObjExpr);
    Sz := (AObjExpr.ResolvedType.RawSize() + 15) and (not 15);
    EmitRecCallToRret(AObjExpr);           { x0 = __rret }
    EmitAddSubImm('sub', 'sp', 'sp', Sz);
    Self.Emit(#9'mov x1, x0');
    Self.Emit(#9'mov x0, sp');
    EmitIntLiteral('x2', AObjExpr.ResolvedType.RawSize());
    EmitCallSym('memcpy');
    Self.Emit(#9'mov x0, sp');
    EmitPushX0();                          { the receiver EmitCall pops }
    EmitCall(AMethod, AName, AArgs, '', True, AMethod.VTableSlot);
    EmitAddSubImm('add', 'sp', 'sp', Sz);  { drop the temp }
    Exit;
  end;
  { chained receiver: the object pointer is the value of AObjExpr.  An
    OWNED +1 receiver (Create()/call result) is kept in a stack slot
    across the call and released afterwards — the transient must outlive
    the method invocation. }
  Owned := ArcExprOwnsRef(AObjExpr);
  Self.EmitExprToX0(AObjExpr);
  if Owned then
    EmitPushX0();               { copy for the post-call release }
  EmitPushX0();                 { the receiver EmitCall pops into x0 }
  EmitCall(AMethod, AName, AArgs, '', True, AMethod.VTableSlot);
  if Owned then
  begin
    EmitPushX0();               { park the result }
    Self.Emit(#9'ldr x0, [sp, #16]');
    EmitCallSym('_ClassRelease');
    EmitPopTo('x0');
    Self.Emit(#9'add sp, sp, #16');   { drop the receiver copy }
  end;
end;

procedure TArm64Backend.EmitMethodCallStmt(AStmt: TMethodCallStmt);
var
  MD: TMethodDecl;
  PT: TProceduralTypeDesc;
begin
  if AStmt.IsProcFieldCall then
  begin
    { Obj.Handler(args); / FInner.Handler(args); -- a call THROUGH a
      procedural-typed field (BUG-20260922) }
    if (AStmt.ProcFieldInfo = nil) or
       not (AStmt.ProcFieldInfo.TypeDesc is TProceduralTypeDesc) then
      NotYet('procedural-field call on this field', AStmt);
    PT := TProceduralTypeDesc(AStmt.ProcFieldInfo.TypeDesc);
    if AStmt.IsImplicitSelf and (AStmt.ImplicitBaseInfo <> nil) then
    begin
      { FInner.Handler(args) inside a method: Self -> the FInner base (a
        class value or a record address), then the field
        (BUG-20260923-implicit-field-procfield-stmt) }
      EmitLoadSlot('x0', 'Self');
      EmitImplicitBaseStep('x0', AStmt.ImplicitBaseInfo);
      if AStmt.ProcFieldInfo.Offset <> 0 then
        EmitAddSubImm('add', 'x0', 'x0', AStmt.ProcFieldInfo.Offset);
      EmitFatPtrCall('x0', PT, AStmt.Args, IsMethodPtrType(PT));
    end
    else
      EmitProcFieldCall(AStmt.ObjectName, AStmt.ObjExpr, AStmt.IsVarParam,
        False, AStmt.ResolvedClassType, AStmt.ProcFieldInfo, AStmt.Args, AStmt);
    EmitDiscardedProcResult(PT);
    Exit;
  end;
  if AStmt.IsImplicitSelf and (AStmt.ImplicitBaseInfo <> nil) and
     (TMethodDecl(AStmt.ResolvedMethod) = nil) and
     SameText(AStmt.Name, 'Free') and (AStmt.Args.Count = 0) then
  begin
    { FField.Free(): release through the field's address and NIL it —
      the same stale-alias rule as the local-slot Free }
    EmitLoadSlot('x0', 'Self');
    if AStmt.ImplicitBaseInfo.Offset <> 0 then
      EmitAddSubImm('add', 'x0', 'x0', AStmt.ImplicitBaseInfo.Offset);
    EmitPushX0();
    Self.Emit(#9'ldr x0, [x0]');
    EmitCallSym('_ClassRelease');
    EmitPopTo('x9');
    Self.Emit(#9'str xzr, [x9]');
    Exit;
  end;
  if AStmt.IsImplicitSelf and (AStmt.ImplicitBaseInfo <> nil) and
     not AStmt.IsConstructorCall and (AStmt.ResolvedMethod <> nil) and
     ((AStmt.ResolvedClassType = nil) or
      (AStmt.ResolvedClassType.Kind <> tyInterface)) then
  begin
    { method call on a class-typed FIELD of Self: FLexer.Next() —
      the receiver is loaded through Self at the field's offset }
    if (AStmt.ResolvedReturnTypeDesc <> nil) and
       IsAggregateReturn(AStmt.ResolvedReturnTypeDesc) then
      NotYet('discarded aggregate-returning field-method call', AStmt);
    EmitLoadSlot('x0', 'Self');
    Self.Emit(Format(#9'ldr x0, [x0, #%d]',
      [AStmt.ImplicitBaseInfo.Offset]));
    EmitMethodCallCommon(TMethodDecl(AStmt.ResolvedMethod), AStmt.Name,
      AStmt.Args);
    if AStmt.ResolvedReturnTypeDesc <> nil then
    begin
      if AStmt.ResolvedReturnTypeDesc.Kind = tyString then
        EmitCallSym('_StringRelease')
      else if AStmt.ResolvedReturnTypeDesc.Kind = tyClass then
        EmitCallSym('_ClassRelease')
      else if AStmt.ResolvedReturnTypeDesc.Kind = tyDynArray then
        EmitCallSym('_DynArrayRelease');
    end;
    Exit;
  end;
  if (AStmt.ResolvedClassType <> nil) and
     (AStmt.ResolvedClassType.Kind = tyInterface) and
     not AStmt.IsConstructorCall and
     ((AStmt.ObjectName <> '') or (AStmt.ObjExpr <> nil)) then
  begin
    { itab dispatch on an interface-typed receiver: a named variable, a var
      parameter, a field of Self (FIntf.M()), or a receiver expression }
    if AStmt.IsImplicitSelf and (AStmt.ImplicitBaseInfo = nil) then
      NotYet('interface dispatch on this receiver form', AStmt);
    if (AStmt.ResolvedReturnTypeDesc <> nil) and
       IsAggregateReturn(AStmt.ResolvedReturnTypeDesc) then
    begin
      { a discarded interface result still uses the x8 sret contract; the
        owned obj half is dropped straight away }
      if AStmt.ResolvedReturnTypeDesc.Kind <> tyInterface then
        NotYet('discarded aggregate-returning interface call', AStmt);
      EmitIntfDispatch(AStmt.ObjectName,
        TInterfaceTypeDesc(AStmt.ResolvedClassType),
        TInterfaceTypeDesc(AStmt.ResolvedClassType).MethodIndex(AStmt.Name),
        AStmt.Args, AStmt.ObjExpr, AStmt.IsVarParam, AStmt.ImplicitBaseInfo,
        '__iret');
      EmitLoadSlot('x0', '__iret');
      EmitCallSym('_ClassRelease');
      Exit;
    end;
    EmitIntfDispatch(AStmt.ObjectName,
      TInterfaceTypeDesc(AStmt.ResolvedClassType),
      TInterfaceTypeDesc(AStmt.ResolvedClassType).MethodIndex(AStmt.Name),
      AStmt.Args, AStmt.ObjExpr, AStmt.IsVarParam, AStmt.ImplicitBaseInfo);
    if (AStmt.ResolvedReturnTypeDesc <> nil) and
       (AStmt.ResolvedReturnTypeDesc.Kind = tyClass) then
      EmitCallSym('_ClassRelease');
    if (AStmt.ResolvedReturnTypeDesc <> nil) and
       (AStmt.ResolvedReturnTypeDesc.Kind = tyString) then
      EmitCallSym('_StringRelease');
    Exit;
  end;
  if AStmt.IsConstructorCall and AStmt.IsMetaclassDispatch and
     (AStmt.ObjExpr = nil) and (AStmt.ObjectName <> '') then
  begin
    { Cls.Create(args); with the result discarded: _ClassCreate hands back
      the instance at +1, the constructor runs for its side effects (through
      the NEW instance's vtable when virtual), and nothing holds the
      reference, so it is released straight away (x86-64 parity). }
    EmitLoadSlot('x0', AStmt.ObjectName);
    EmitCallSym('_ClassCreate');
    MD := TMethodDecl(AStmt.ResolvedMethod);
    if MD <> nil then
    begin
      EmitPushX0();
      EmitMethodCallCommon(MD, 'Create', AStmt.Args);
      EmitPopTo('x0');
    end;
    EmitCallSym('_ClassRelease');
    Exit;
  end;
  if AStmt.IsConstructorCall or AStmt.IsImplicitSelf or
     ((AStmt.ObjectName = '') and (AStmt.ObjExpr = nil)
      and not AStmt.IsStaticCall) then
    NotYet('this method-call form', AStmt);
  if (TMethodDecl(AStmt.ResolvedMethod) = nil) and
     SameText(AStmt.Name, 'Free') and (AStmt.Args.Count = 0) then
  begin
    { Obj.Free(): release AND nil the slot — a stale pointer left here
      aliases the next same-size allocation and the following ARC store
      double-releases it (QBE/x86 parity: both nil the slot) }
    if AStmt.ObjExpr is TFieldAccessExpr then
    begin
      { X.Field.Free(): release AND nil through the field's address }
      if TFieldAccessExpr(AStmt.ObjExpr).FieldInfo = nil then
        NotYet('Free on this receiver form', AStmt);
      if TFieldAccessExpr(AStmt.ObjExpr).Base <> nil then
      begin
        { chained receiver: the base expression yields the instance }
        if ArcExprOwnsRef(TFieldAccessExpr(AStmt.ObjExpr).Base) then
          NotYet('Free through an owned transient base', AStmt);
        Self.EmitExprToX0(TFieldAccessExpr(AStmt.ObjExpr).Base);
        Self.Emit(#9'mov x9, x0');
      end
      else if TFieldAccessExpr(AStmt.ObjExpr).IsImplicitSelf then
        EmitLoadSlot('x9', 'Self')
      else if TFieldAccessExpr(AStmt.ObjExpr).IsClassAccess then
      begin
        EmitLoadSlot('x9', TFieldAccessExpr(AStmt.ObjExpr).RecordName);
        if TFieldAccessExpr(AStmt.ObjExpr).IsVarParam then
          Self.Emit(#9'ldr x9, [x9]');
      end
      else
        EmitRecordBaseAddr('x9', TFieldAccessExpr(AStmt.ObjExpr).RecordName,
          TFieldAccessExpr(AStmt.ObjExpr).IsVarParam);
      if TFieldAccessExpr(AStmt.ObjExpr).FieldInfo.Offset <> 0 then
        EmitAddSubImm('add', 'x9', 'x9',
          TFieldAccessExpr(AStmt.ObjExpr).FieldInfo.Offset);
      Self.Emit(#9'mov x0, x9');
      EmitPushX0();
      Self.Emit(#9'ldr x0, [x0]');
      EmitCallSym('_ClassRelease');
      EmitPopTo('x9');
      Self.Emit(#9'str xzr, [x9]');
      Exit;
    end;
    if ArcIsArrayElemSlot(AStmt.ObjExpr) then
    begin
      { array-element receiver (A[I].Free()): release AND nil the element
        slot — parity with the QBE/x86-64 lowerings.  A stale element
        pointer double-frees when the scope-exit ARC walk releases the
        array's elements again (BUG-016). }
      case TStringSubscriptExpr(AStmt.ObjExpr).StrExpr.ResolvedType.Kind of
        tyStaticArray:
          EmitStaticElemAddr(TStringSubscriptExpr(AStmt.ObjExpr));
      else
        EmitDynElemAddr(TStringSubscriptExpr(AStmt.ObjExpr));
      end;
      EmitPushX0();
      Self.Emit(#9'ldr x0, [x0]');
      EmitCallSym('_ClassRelease');
      EmitPopTo('x9');
      Self.Emit(#9'str xzr, [x9]');
      Exit;
    end;
    if AStmt.ObjExpr <> nil then
    begin
      { general-expression receiver (Sections.Get(I).Free()): the receiver
        is an owned +1 temporary — ArcExprOwnsRef is True for any
        non-constructor method-call result — so Free is a single balanced
        release with no slot to nil (mirrors the x86-64 general branch). }
      Self.EmitExprToX0(AStmt.ObjExpr);
      EmitCallSym('_ClassRelease');
      Exit;
    end;
    if AStmt.IsImplicitSelf then
      NotYet('Free on this receiver form', AStmt);
    if AStmt.IsVarParam then
    begin
      { the slot holds the caller's ADDRESS: free through it, nil it }
      EmitLoadSlot('x0', AStmt.ObjectName);
      EmitPushX0();
      Self.Emit(#9'ldr x0, [x0]');
      EmitCallSym('_ClassRelease');
      EmitPopTo('x9');
      Self.Emit(#9'str xzr, [x9]');
      Exit;
    end;
    EmitLoadSlot('x0', AStmt.ObjectName);
    EmitCallSym('_ClassRelease');
    Self.Emit(#9'movz x0, #0');
    EmitStoreSlot('x0', AStmt.ObjectName);
    Exit;
  end;
  MD := TMethodDecl(AStmt.ResolvedMethod);
  if MD = nil then
    NotYet('unresolved method ''' + AStmt.Name + '''', AStmt);
  if AStmt.IsStaticCall or MD.IsStatic then
  begin
    EmitCall(MD, AStmt.Name, AStmt.Args);
    Exit;
  end;
  if (AStmt.ResolvedReturnTypeDesc <> nil) and
     IsAggregateReturn(AStmt.ResolvedReturnTypeDesc) then
    NotYet('discarded aggregate-returning method call', AStmt);
  if AStmt.ObjExpr <> nil then
    EmitMethodCallOnExpr(MD, AStmt.Name, AStmt.Args, AStmt.ObjExpr)
  else
  begin
    if MD.IsRecordMethod then
      { Self is the record's ADDRESS — see the expression-call twin below. }
      EmitRecordBaseAddr('x0', AStmt.ObjectName, AStmt.IsVarParam)
    else if not EmitCapturedBase('x0', AStmt.ObjectName, True, AStmt.IsVarParam) then
    begin
      EmitLoadSlot('x0', AStmt.ObjectName);
      if AStmt.IsVarParam then
        Self.Emit(#9'ldr x0, [x0]');
    end;
    EmitMethodCallCommon(MD, AStmt.Name, AStmt.Args);
  end;
  { a discarded owned result (class-typed) must be released }
  if (AStmt.ResolvedReturnTypeDesc <> nil) and
     (AStmt.ResolvedReturnTypeDesc.Kind = tyClass) then
    EmitCallSym('_ClassRelease');
  if (AStmt.ResolvedReturnTypeDesc <> nil) and
     (AStmt.ResolvedReturnTypeDesc.Kind = tyString) then
    EmitCallSym('_StringRelease');
end;

procedure TArm64Backend.EmitRaiseInvalidCast;
begin
  if (FSymTable <> nil) and (FSymTable.Lookup('EInvalidCast') <> nil) then
    EmitCallSym('SysUtils__RaiseInvalidCast')
  else
    EmitCallSym('_Raise_InvalidCast');
end;

{ ClassCreate(Cls, args...): construction from a metaclass VALUE.  The
  same lowering as Cls.Create(args) (the IsMetaclassDispatch arm of
  EmitMethodCallExpr): _ClassCreate(typeinfo) allocates, installs the vtable
  and returns the owned +1; the constructor uSemantic resolved on the base
  class then runs on the new instance, dispatching through ITS vtable when
  virtual (EmitMethodCallCommon keys on the VTableSlot), so a derived
  override runs.  No resolved Create means the implicit default ctor. }
procedure TArm64Backend.EmitClassCreate(AExpr: TFuncCallExpr);
var
  CtorArgs: TObjectList;
  I: Integer;
begin
  Self.EmitExprToX0(TASTExpr(AExpr.Args.Items[0]));
  EmitCallSym('_ClassCreate');
  if AExpr.ResolvedDecl = nil then
    Exit;
  CtorArgs := TObjectList.Create(False);
  try
    for I := 1 to AExpr.Args.Count - 1 do
      CtorArgs.Add(AExpr.Args.Items[I]);
    EmitPushX0();               { keep the result across the ctor call }
    EmitMethodCallCommon(TMethodDecl(AExpr.ResolvedDecl), 'Create', CtorArgs);
    EmitPopTo('x0');
  finally
    CtorArgs.Free();
  end;
end;

procedure TArm64Backend.EmitMethodCallExpr(AExpr: TMethodCallExpr);
var
  MD: TMethodDecl;
  TD: TTypeDecl;
  I: Integer;
  Sym: string;
begin
  if AExpr.IsConstructorCall then
  begin
    { TFoo.Create(args): _ClassCreate(typeinfo) allocates, installs the
      vtable and takes the +1; a declared constructor body then runs as a
      plain method on the new instance.  A metaclass receiver loads the
      typeinfo VALUE from its variable — _ClassCreate reads size/cleanup/
      vtable from it at runtime, and a virtual constructor dispatches
      through the NEW INSTANCE's vtable (EmitMethodCallCommon keys on the
      ctor's VTableSlot). }
    if AExpr.IsMetaclassDispatch then
    begin
      EmitLoadSlot('x0', AExpr.ObjectName);
      EmitCallSym('_ClassCreate');
      MD := TMethodDecl(AExpr.ResolvedMethod);
      { a resolved ctor is CALLED even when Body = nil — imported unit
        interfaces carry declaration stubs; the body lives in the
        owning unit's object }
      if MD <> nil then
      begin
        EmitPushX0();
        EmitMethodCallCommon(MD, 'Create', AExpr.Args);
        EmitPopTo('x0');
      end;
      { MD = nil here means a parameterless ctor with no user body (the
        implicit default constructor).  An undeclared Create* variant WITH
        args never reaches codegen — the semantic pass desugars CreateFmt
        and rejects any other arg-bearing undeclared ctor (BUG-046 fix). }
      Exit;
    end;
    Sym := '';
    for I := 0 to FClassDecls.Count - 1 do
    begin
      TD := TTypeDecl(FClassDecls.Items[I]);
      if SameText(TD.Name, AExpr.ObjectName) then
      begin
        Sym := ClassSym(TD);
        Break;
      end;
    end;
    if (Sym = '') and (AExpr.ResolvedClassType is TRecordTypeDesc) then
    begin
      { class declared in ANOTHER unit (or later in this one with no
        local decl entry): mangle from the resolved desc — the owning
        unit's own emission defines the typeinfo/vtable symbols }
      if Pos('<', TRecordTypeDesc(AExpr.ResolvedClassType).Name) >= 0 then
        Sym := CodegenMangle(TRecordTypeDesc(AExpr.ResolvedClassType).Name)
      else
        Sym := ClassPrefixOwner(
          TRecordTypeDesc(AExpr.ResolvedClassType).OwningUnit) +
          CodegenMangle(TRecordTypeDesc(AExpr.ResolvedClassType).Name);
    end;
    if Sym = '' then
      NotYet('constructor for class ''' + AExpr.ObjectName + '''', AExpr);
    { Allocate at refcount ZERO, mirroring x86-64 (:10604): _ClassAlloc does
      NOT take a reference, and the vtable is installed here.  _ClassCreate
      must NOT be used on this path — it ends with _ClassAddRef, and the
      SHARED ArcExprOwnsRef deliberately reports a constructor call as NOT
      owning, so the assignment site adds the one reference itself.  Calling
      _ClassCreate here left every instance one reference above zero: nothing
      was ever freed and no destructor ever ran (arm64 leaked every object it
      constructed). }
    if AExpr.ResolvedClassType is TRecordTypeDesc then
      EmitIntLiteral('x0',
        TRecordTypeDesc(AExpr.ResolvedClassType).TotalSize())
    else
      NotYet('constructor for class ''' + AExpr.ObjectName +
        ''' with no resolved class type', AExpr);
    Self.Emit(Format(#9'adrp x1, %s@PAGE', [FieldCleanupSym(Sym)]));
    Self.Emit(Format(#9'add x1, x1, %s@PAGEOFF', [FieldCleanupSym(Sym)]));
    EmitCallSym('_ClassAlloc');
    if TRecordTypeDesc(AExpr.ResolvedClassType).HasVTable() then
    begin
      Self.Emit(Format(#9'adrp x9, %s@PAGE', [VtableSym(Sym)]));
      Self.Emit(Format(#9'add x9, x9, %s@PAGEOFF', [VtableSym(Sym)]));
      Self.Emit(#9'str x9, [x0]');
    end;
    MD := TMethodDecl(AExpr.ResolvedMethod);
    { called even when Body = nil — imported unit interfaces carry
      declaration stubs; the body lives in the owning unit's object }
    if MD <> nil then
    begin
      EmitPushX0();               { keep the result across the ctor call }
      EmitMethodCallCommon(MD, 'Create', AExpr.Args);
      EmitPopTo('x0');
    end;
    { MD = nil here means a parameterless ctor with no user body (the
      implicit default constructor).  An undeclared Create* variant WITH
      args never reaches codegen — the semantic pass desugars CreateFmt
      and rejects any other arg-bearing undeclared ctor (BUG-046 fix). }
    Exit;
  end;
  if AExpr.IsBuiltinToString then
  begin
    { built-in TObject.ToString: always-virtual through vtable slot 1
      (offset 16 past the typeinfo back-pointer).  Returns an owned +1
      string. }
    if (AExpr.ObjExpr <> nil) or (AExpr.ObjectName = '') then
      NotYet('ToString on this receiver form', AExpr);
    EmitLoadSlot('x0', AExpr.ObjectName);
    if AExpr.IsVarParam then
      Self.Emit(#9'ldr x0, [x0]');
    Self.Emit(#9'ldr x9, [x0]');
    Self.Emit(#9'ldr x9, [x9, #16]');
    Self.Emit(#9'blr x9');
    Exit;
  end;
  if AExpr.IsBuiltinInheritsFrom then
  begin
    { _InheritsFrom(child_ti, parent_ti): the receiver is a class
      instance (typeinfo from vtable[0]) or a metaclass variable }
    if (AExpr.ObjExpr <> nil) or AExpr.IsVarParam or
       (AExpr.ObjectName = '') then
      NotYet('InheritsFrom on this receiver form', AExpr);
    Self.EmitExprToX0(TASTExpr(AExpr.Args.Items[0]));
    EmitPushX0();
    EmitLoadSlot('x0', AExpr.ObjectName);
    if (AExpr.ResolvedClassType <> nil) and
       (AExpr.ResolvedClassType.Kind = tyClass) then
    begin
      Self.Emit(#9'ldr x0, [x0]');    { vtable }
      Self.Emit(#9'ldr x0, [x0]');    { slot 0 = typeinfo }
    end;
    EmitPopTo('x1');
    EmitCallSym('_InheritsFrom');
    Exit;
  end;
  if AExpr.IsProcFieldCall then
  begin
    { Obj.Handler(args) in expression position (BUG-20260922); the result
      is left in x0 / d0 by the indirect call }
    EmitProcFieldCall(AExpr.ObjectName, AExpr.ObjExpr, AExpr.IsVarParam,
      False, AExpr.ResolvedClassType, AExpr.ProcFieldInfo, AExpr.Args, AExpr);
    Exit;
  end;
  if AExpr.IsMetaclassDispatch or
     ((AExpr.ObjectName = '') and (AExpr.ObjExpr = nil)
      and not AExpr.IsStaticCall) then
    NotYet('this method-call form', AExpr);
  if (AExpr.ResolvedClassType <> nil) and
     (AExpr.ResolvedClassType.Kind = tyInterface) then
  begin
    if (AExpr.ResolvedType <> nil) and
       IsAggregateReturn(AExpr.ResolvedType) then
      NotYet('aggregate-returning interface call', AExpr);
    EmitIntfDispatch(AExpr.ObjectName,
      TInterfaceTypeDesc(AExpr.ResolvedClassType),
      TInterfaceTypeDesc(AExpr.ResolvedClassType).MethodIndex(AExpr.Name),
      AExpr.Args, AExpr.ObjExpr, AExpr.IsVarParam);
    Exit;
  end;
  MD := TMethodDecl(AExpr.ResolvedMethod);
  if MD = nil then
    NotYet('unresolved method ''' + AExpr.Name + '''', AExpr);
  if AExpr.IsStaticCall or MD.IsStatic then
  begin
    { static (class-level) call: no Self, plain call to the mangled name }
    EmitCall(MD, AExpr.Name, AExpr.Args);
    Exit;
  end;
  if AExpr.ObjExpr <> nil then
  begin
    EmitMethodCallOnExpr(MD, AExpr.Name, AExpr.Args, AExpr.ObjExpr);
    Exit;
  end;
  if MD.IsRecordMethod then
    { A record is a VALUE, so Self is its ADDRESS — never its contents.  Loading
      the slot here would pass the record's first 8 bytes as if they were a
      pointer.  EmitRecordBaseAddr also handles the one exception: a true
      var/out receiver whose slot ALREADY holds the caller's address is loaded
      rather than address-taken again. }
    EmitRecordBaseAddr('x0', AExpr.ObjectName, AExpr.IsVarParam)
  else if not EmitCapturedBase('x0', AExpr.ObjectName, True, AExpr.IsVarParam) then
  begin
    EmitLoadSlot('x0', AExpr.ObjectName);
    if AExpr.IsVarParam then
      Self.Emit(#9'ldr x0, [x0]');
  end;
  EmitMethodCallCommon(MD, AExpr.Name, AExpr.Args);
end;

{ ---- program / unit ------------------------------------------------------ }

procedure TArm64Backend.EmitProgram(AProg: TProgram);
var
  I, J: Integer;
  VD:   TVarDecl;
  Decl: TMethodDecl;
  FrameAligned: Integer;
  TDcl: TTypeDecl;
  CDef: TClassTypeDef;
  RDef: TRecordTypeDef;
  GRDef: TRecordTypeDef;
  GI: TGenericInstance;
  SavedAsm, BodyBuf: TStringBuilder;
begin
  FProgramName := AProg.Name;
  FCurrentUnitName := '';
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TDcl := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if TDcl.Def is TClassTypeDef then
      FClassDecls.Add(TDcl)
    else if TDcl.Def is TInterfaceTypeDef then
      FIntfDecls.Add(TDcl)
    else if (TDcl.Def is TTypeAliasDef) or (TDcl.Def is TEnumTypeDef) or
            (TDcl.Def is TSetTypeDef) or (TDcl.Def is TProceduralTypeDef) or
            (TDcl.Def is TGenericTypeDef) or
            (TDcl.Def is TGenericInterfaceDef) or
            (TDcl.Def is TGenericRecordDef) or
            (TDcl.Def is TGenericProcDef) then
      { declaration-only: aliases (incl. 'class of'), enums, sets and
        procedural types need no emission; generic TEMPLATES emit nothing
        either — their INSTANCES arrive monomorphised via the
        GenericInstances lists }
    else if not (TDcl.Def is TRecordTypeDef) then
      NotYet('non-record type declarations', nil)
    else if TRecordTypeDef(TDcl.Def).Methods.Count > 0 then
      { A record with methods: collect it so the bodies emit with the class
        bodies below.  The record itself needs no metadata — no typeinfo, no
        vtable — because record methods are statically bound. }
      FRecordDecls.Add(TDcl);
  end;

  { Program-level variables become globals (int-family only for now). }
  for I := 0 to AProg.Block.Decls.Count - 1 do
  begin
    VD := TVarDecl(AProg.Block.Decls.Items[I]);
    if not (IsIntFam(VD.ResolvedType) or
            ((VD.ResolvedType <> nil) and
             (VD.ResolvedType.Kind in [tyDouble, tySingle, tyString,
                                       tyRecord, tyClass, tyInterface,
                                       tyMetaClass, tyStaticArray,
                                       tyDynArray, tySet,
                                       tyPointer, tyPChar, tyProcedural]))) then
      NotYet('program variable of this type', VD);
    { A JUMBO set (> 64 members) is an inline byte-array bitmap, so its slot is
      sized from RawSize() -- see the jumbo arm below; it does NOT fall out of
      the generic 8-byte default.  The operations on it go through the _Set*
      RTL helpers. }
    for J := 0 to VD.Names.Count - 1 do
    begin
      FGlobalNames.Add(VD.Names.Strings[J]);
      { a closure / method-pointer global is a 16-byte fat value (Code, Env). }
      if IsMethodPtrType(VD.ResolvedType) then
        FGlobalSize.Add(VD.Names.Strings[J], 16);
      if VD.InitConst <> nil then
        RegisterGlobalInit(VD.Names.Strings[J], VD);
      if VD.ResolvedType.Kind = tyString then
        FStrGlobals.Add(VD.Names.Strings[J]);
      if (VD.ResolvedType.Kind = tyClass) and not VD.IsWeak then
        FObjGlobals.Add(VD.Names.Strings[J]);
      if VD.ResolvedType.Kind = tyDynArray then
        FDynGlobals.Add(VD.Names.Strings[J]);
      { a 'reference to' closure global co-owns its Env — release at program
        exit (arkRefEnv). }
      if (VD.ResolvedType.Kind = tyProcedural) and
         TProceduralTypeDesc(VD.ResolvedType).IsReference then
        FRefGlobals.Add(VD.Names.Strings[J]);
      if VD.ResolvedType.Kind = tyInterface then
      begin
        FGlobalNames.Add(VD.Names.Strings[J] + '_itab');
        FGlobalSize.Add(VD.Names.Strings[J] + '_itab', 8);
        if not VD.IsWeak then
          FIntfGlobals.Add(VD.Names.Strings[J]);
      end;
      if VD.IsThreadVar then
      begin
        { threadvars get a Mach-O TLV descriptor; unmanaged scalar kinds
          and static arrays of them (per-thread ARC teardown is its own
          problem, so managed kinds stay NotYet) }
        if not (IsIntFam(VD.ResolvedType) or
                (VD.ResolvedType.Kind in [tyDouble, tyPointer, tyPChar,
                                          tyClass]) or
                ((VD.ResolvedType.Kind = tyStaticArray) and
                 not AggHasManaged(VD.ResolvedType))) then
          NotYet('threadvar of this type', VD);
        if VD.InitConst <> nil then
          NotYet('initialised threadvar', VD);
        FTlvGlobals.Add(VD.Names.Strings[J]);
        if VD.ResolvedType.Kind = tyStaticArray then
          FTlvSize.Items[VD.Names.Strings[J]] :=
            VD.ResolvedType.RawSize()
        else
          FTlvSize.Items[VD.Names.Strings[J]] := 8;
        { not an ordinary global: no _g_ bss entry }
        FGlobalNames.Delete(FGlobalNames.Count - 1);
      end;
      if VD.ResolvedType.Kind in [tyRecord, tyStaticArray] then
      begin
        FRecGlobals.AddObject(VD.Names.Strings[J], VD.ResolvedType);
        FGlobalSize.Add(VD.Names.Strings[J], VD.ResolvedType.RawSize());
      end
      else if (VD.ResolvedType is TSetTypeDesc) and
              TSetTypeDesc(VD.ResolvedType).IsJumbo() then
        { a JUMBO set is an inline byte bitmap; RawSize is already rounded
          to 8.  The generic 8 below let Include/_SetInclude write past the
          global into the next one. }
        FGlobalSize.Add(VD.Names.Strings[J], VD.ResolvedType.RawSize())
      else if not IsMethodPtrType(VD.ResolvedType) then
        { a closure / method-pointer global was sized 16 above; this generic
          8 used to overwrite it, so the Env half spilled into the NEXT
          global (it zeroed _g_GRtlPlatform and the next WriteLn crashed) }
        FGlobalSize.Add(VD.Names.Strings[J], 8);
    end;
  end;

  { Generic RECORD instances need no registration here — a record carries no
    typeinfo and no vtable, so unlike a generic CLASS instance there is nothing
    to wrap in a synthetic TTypeDecl.  Their method bodies emit with the other
    instance walks in the .text pass below. }

  { generic CLASS instances: wrap each monomorphised clone in a synthetic
    TTypeDecl so it flows through the ordinary class machinery (methods,
    metadata, cleanup, constructor lookup).  All instance symbols emit
    WEAK with bare names — see ClassSym. }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    { instances that implement interfaces flow through the ordinary class
      machinery too — EmitIntfMetaSections weak-binds their itab + impllist
      (leg 15); the method pointers bind to the clone's own bodies. }
    TDcl := TTypeDecl.Create();
    TDcl.Name := GI.TypeName;
    TDcl.Def := GI.ClassDef;
    TDcl.ResolvedDesc := GI.TypeDesc;
    FGenericDecls.Add(TDcl);
    FClassDecls.Add(TDcl);
  end;

  { Generic INTERFACE instances (IComparer<Integer> etc): collect them so
    EmitIntfMetaSections can emit their weak typeinfo — the itab/impllist of a
    class implementing them references typeinfo_<inst> (leg 41). }
  for I := 0 to AProg.GenericIntfInstances.Count - 1 do
    FGenericIntfInstances.Add(AProg.GenericIntfInstances.Items[I]);

  Self.Emit('.text');

  { Standalone procedures/functions before $main. }
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls.Items[I]);
    if Decl.OwnerTypeName <> '' then Continue;   { method stubs: bodies below }
    if Decl.TypeParams <> nil then Continue;     { generic templates }
    if Decl.Body = nil then Continue;            { forward decls }
    if Decl.IsExternal then Continue;            { externals: call-site only }
    EmitFunctionDef(Decl);
  end;

  { Generic function instances: concrete monomorphised bodies, weak-bound
    like every other instance symbol. }
  for I := 0 to AProg.GenericFuncInstances.Count - 1 do
    EmitFunctionDef(
      TGenericFuncInstance(AProg.GenericFuncInstances.Items[I]).MethodDecl,
      True);

  { Generic RECORD instances: each monomorphised clone's method bodies.  A
    record instance needs no typeinfo or vtable, so unlike a generic CLASS
    instance there is no wrapper to build — the bodies emit directly, weak-bound
    so two units instantiating the same specialisation collapse to one
    definition rather than colliding. }
  for I := 0 to AProg.GenericRecordInstances.Count - 1 do
  begin
    GRDef := TGenericRecordInstance(
               AProg.GenericRecordInstances.Items[I]).RecordDef;
    for J := 0 to GRDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GRDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      EmitFunctionDef(Decl, True);
    end;
  end;

  { Generic METHOD instances (leg 37): a method with its own <T> monomorphised
    at a call site.  Its MethodDecl is a fully concrete method (mangled name via
    ResolvedQbeName, OwnerTypeName set), so it emits exactly like a generic
    function instance — weak-bound for cross-unit dedup. }
  for I := 0 to AProg.GenericMethodInstances.Count - 1 do
    if TGenericMethodInstance(
         AProg.GenericMethodInstances.Items[I]).MethodDecl.Body <> nil then
      EmitFunctionDef(
        TGenericMethodInstance(AProg.GenericMethodInstances.Items[I]).MethodDecl,
        True);

  { Class method bodies (LinkClassMethodImpls placed them on the class
    defs), then the ARC field-cleanup functions.  Skip any unit class already
    emitted by EmitUnit in its own context — re-emitting here (program context,
    FCurrentUnitName='') would mis-resolve impl-section unit globals and emit a
    duplicate method label (leg 39).  Generic-instance wrappers and the
    program's own classes are NOT in FUnitEmittedClasses, so they still emit. }
  for I := 0 to FClassDecls.Count - 1 do
  begin
    if FUnitEmittedClasses.IndexOf(TTypeDecl(FClassDecls.Items[I])) >= 0 then
      Continue;
    CDef := TClassTypeDef(TTypeDecl(FClassDecls.Items[I]).Def);
    for J := 0 to CDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(CDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      { A generic method TEMPLATE (its own <T>) is not concrete code — skip it,
        like the standalone-func skip above; its monomorphised instances are
        emitted from GenericMethodInstances (leg 37). }
      if Decl.TypeParams <> nil then Continue;
      EmitFunctionDef(Decl,
        Pos('<', TTypeDecl(FClassDecls.Items[I]).Name) >= 0);
    end;
  end;

  { Record method bodies.  Identical to the class walk above — a record method
    is an ordinary function (statically bound, no vtable slot); only its Self
    differs, and that is handled at the CALL site, where the receiver's ADDRESS
    is passed rather than its value. }
  for I := 0 to FRecordDecls.Count - 1 do
  begin
    RDef := TRecordTypeDef(TTypeDecl(FRecordDecls.Items[I]).Def);
    for J := 0 to RDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(RDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;      { forward/interface-only decl }
      if Decl.TypeParams <> nil then Continue; { generic template, not code }
      EmitFunctionDef(Decl,
        Pos('<', TTypeDecl(FRecordDecls.Items[I]).Name) >= 0);
    end;
  end;
  EmitClassCleanupFns();

  { _main's frame holds only the hidden for-loop bound slots (program vars
    are globals). }
  FIsFunction := False;
  FExitLabel := NewLabel('mainexit');
  FFrame.Clear();
  FFrameSize := 0;
  FForN := 0;
  AddLocal('__iret', 16);   { interface-returning call scratch }
  { __rret: always >= 16 (register-shape record-call field reads); larger
    if a managed-record assignment needs it }
  J := 16;
  for I := 0 to AProg.Block.Stmts.Count - 1 do
    if MaxManagedRecRet(TASTStmt(AProg.Block.Stmts.Items[I])) > J then
      J := MaxManagedRecRet(TASTStmt(AProg.Block.Stmts.Items[I]));
  AddLocal('__rret', J);
  ReservePendRelSlots();   { BUG-048: statement-scoped deferred class releases }
  for I := 0 to AProg.Block.Stmts.Count - 1 do
    RegisterForSlots(TASTStmt(AProg.Block.Stmts.Items[I]));
  FForN := 0;
  FrameAligned := (FFrameSize + 15) and (not 15);

  Self.Emit('');
  EmitGloblDef(DarwinSym('main'));
  Self.Emit('_main:');
  { Prologue: fp/lr pair + frame chain — ALWAYS (Darwin unwind).  argc/argv
    arrive in x0/x1 and pass straight through to _SetArgs, which must run
    before _BlaiseInit (that clobbers the argument registers).  The body is
    buffered so try statements can lazily grow the frame (see
    EmitFunctionDef). }
  Self.Emit(#9'stp x29, x30, [sp, #-16]!');
  Self.Emit(#9'mov x29, sp');
  SavedAsm := FAsm;
  BodyBuf := TStringBuilder.Create();
  FAsm := BodyBuf;
  FExcDepth := 0;
  FExcSlotN := 0;
  FFinallyBodies.Clear();
  FLoopExcDepth.Clear();
  EmitCallSym('_SetArgs');
  EmitCallSym('_BlaiseInit');
  { unit initialization sections, in dependency (append) order }
  for I := 0 to FUnitInits.Count - 1 do
    Self.Emit(Format(#9'bl %s', [FUnitInits.Strings[I]]));

  EmitStmtList(AProg.Block.Stmts);

  Self.Emit(FExitLabel + ':');
  { unit finalization sections, REVERSE dependency order, before the
    global releases (finalizers may still touch their unit's globals) }
  for I := FUnitFinals.Count - 1 downto 0 do
    Self.Emit(Format(#9'bl %s', [FUnitFinals.Strings[I]]));
  { release string globals before returning (ARC parity with x86-64's
    program-exit global release) }
  for I := 0 to FStrGlobals.Count - 1 do
  begin
    EmitLoadSlot('x0', FStrGlobals.Strings[I]);
    EmitCallSym('_StringRelease');
  end;
  for I := 0 to FRecGlobals.Count - 1 do
    if AggHasManaged(TTypeDesc(FRecGlobals.Objects[I])) then
    begin
      Self.Emit(#9'str x19, [sp, #-16]!');
      EmitSlotAddr('x19', FRecGlobals.Strings[I]);
      Self.EmitManagedReleaseAt(TTypeDesc(FRecGlobals.Objects[I]),
        'x19', False);
      Self.Emit(#9'ldr x19, [sp], #16');
    end;
  for I := 0 to FObjGlobals.Count - 1 do
  begin
    EmitLoadSlot('x0', FObjGlobals.Strings[I]);
    EmitCallSym('_ClassRelease');
  end;
  for I := 0 to FIntfGlobals.Count - 1 do
  begin
    EmitLoadSlot('x0', FIntfGlobals.Strings[I]);
    EmitCallSym('_ClassRelease');
  end;
  for I := 0 to FDynGlobals.Count - 1 do
  begin
    EmitLoadSlot('x0', FDynGlobals.Strings[I]);
    EmitCallSym('_DynArrayRelease');
  end;
  { release the Env half of 'reference to' closure globals (arkRefEnv) }
  for I := 0 to FRefGlobals.Count - 1 do
  begin
    EmitSlotAddr('x0', FRefGlobals.Strings[I]);
    Self.Emit(#9'ldr x0, [x0, #8]');
    EmitCallSym('_ClassRelease');
  end;
  Self.Emit(#9'movz w0, #0');
  Self.Emit(#9'mov sp, x29');
  Self.Emit(#9'ldp x29, x30, [sp], #16');
  Self.Emit(#9'ret');
  FAsm := SavedAsm;
  FrameAligned := (FFrameSize + 15) and (not 15);
  if FrameAligned > 0 then
    EmitAddSubImm('sub', 'sp', 'sp', FrameAligned);
  FAsm.Append(BodyBuf.ToString());
  BodyBuf.Free();

  EmitArrayConstData(AProg.Block);
  EmitStrLitSection();
  EmitFloatLitSection();
  EmitGlobalsSection();
  if FClassDecls.Count > 0 then
    EmitClassMetaSections();
  EmitIntfMetaSections();
  EmitTlvSections();
end;

procedure TArm64Backend.EmitTlvSections;
var
  I, Sz: Integer;
begin
  if FTlvGlobals.Count = 0 then Exit;
  { per-thread storage: zerofill in __thread_bss, sized per variable }
  Self.Emit('.section __DATA,__thread_bss');
  for I := 0 to FTlvGlobals.Count - 1 do
  begin
    if not FTlvSize.TryGetValue(FTlvGlobals.Strings[I], Sz) then
      Sz := 8;
    Self.Emit('.balign 8');
    { threadvars follow the same GH #174 collapse rule as plain globals —
      per-unit objects may each carry a copy of an RTL threadvar, and the
      copies MUST collapse to one (separate TLS slots would be wrong) }
    if FGlobalWeak.IndexOf('__tlv_' + FTlvGlobals.Strings[I]) >= 0 then
      EmitWeakDef('_ts_' + FTlvGlobals.Strings[I])
    else
      EmitGloblDef('_ts_' + FTlvGlobals.Strings[I]);
    Self.Emit(Format('_ts_%s:', [FTlvGlobals.Strings[I]]));
    Self.Emit(Format(#9'.zero %d', [Sz]));
  end;
  { TLV descriptors: three quads — thunk, key, storage.  The thunk names dyld's
    bootstrap whose C name is _tlv_bootstrap, so the emitted symbol is
    __tlv_bootstrap (DarwinSym) — the same spelling dyld exports.  dyld rewrites
    the descriptor at load; the access sequence calls through it. }
  Self.Emit('.section __DATA,__thread_vars');
  for I := 0 to FTlvGlobals.Count - 1 do
  begin
    Self.Emit('.balign 8');
    if FGlobalWeak.IndexOf('__tlv_' + FTlvGlobals.Strings[I]) >= 0 then
      EmitWeakDef('_tv_' + FTlvGlobals.Strings[I])
    else
      EmitGloblDef('_tv_' + FTlvGlobals.Strings[I]);
    Self.Emit(Format('_tv_%s:', [FTlvGlobals.Strings[I]]));
    Self.Emit(#9'.quad ' + DarwinSym('_tlv_bootstrap'));
    Self.Emit(#9'.quad 0');
    Self.Emit(Format(#9'.quad _ts_%s', [FTlvGlobals.Strings[I]]));
  end;
end;

procedure TArm64Backend.EmitUnit(AUnit: TUnit);
var
  I, J: Integer;
  Decl: TMethodDecl;
  UTD: TTypeDecl;
  GI: TGenericInstance;
  GICDef: TClassTypeDef;
  URGDef: TRecordTypeDef;
  SavedUnit: string;

  procedure CheckTypeSubset(ATypeDecls: TObjectList);
  var
    K, M: Integer;
    UDcl: TTypeDecl;
    UDef: TClassTypeDef;
    URDef: TRecordTypeDef;
    MDcl: TMethodDecl;
  begin
    { pass 1: REGISTER every class/interface decl before any method body
      is emitted — a body may reference a class declared later in the
      same unit (constructor sites resolve through FClassDecls) }
    for K := 0 to ATypeDecls.Count - 1 do
    begin
      UDcl := TTypeDecl(ATypeDecls.Items[K]);
      if UDcl.Def is TClassTypeDef then
        FClassDecls.Add(UDcl)
      else if UDcl.Def is TInterfaceTypeDef then
        FIntfDecls.Add(UDcl);
    end;
    for K := 0 to ATypeDecls.Count - 1 do
    begin
      UDcl := TTypeDecl(ATypeDecls.Items[K]);
      if UDcl.Def is TClassTypeDef then
      begin
        UDef := TClassTypeDef(UDcl.Def);
        { record that this unit class's method bodies are emitted HERE (in unit
          context) so EmitProgram's FClassDecls walk skips them (leg 39). }
        FUnitEmittedClasses.Add(UDcl);
        for M := 0 to UDef.Methods.Count - 1 do
        begin
          MDcl := TMethodDecl(UDef.Methods.Items[M]);
          if MDcl.Body = nil then Continue;
          { generic method template — not concrete code; instances emitted from
            GenericMethodInstances below (leg 37) }
          if MDcl.TypeParams <> nil then Continue;
          EmitFunctionDef(MDcl);
        end;
        Continue;
      end;
      if UDcl.Def is TInterfaceTypeDef then
        { registered in pass 1; typeinfo arrives via EmitIntfMetaSections }
        Continue;
      if (UDcl.Def is TTypeAliasDef) or (UDcl.Def is TEnumTypeDef) or
         (UDcl.Def is TSetTypeDef) or (UDcl.Def is TProceduralTypeDef) or
         (UDcl.Def is TGenericTypeDef) or
         (UDcl.Def is TGenericInterfaceDef) or
         (UDcl.Def is TGenericRecordDef) or
         (UDcl.Def is TGenericProcDef) then
        { declaration-only, same set the program path accepts }
      else if not (UDcl.Def is TRecordTypeDef) then
        NotYet('non-record type declarations in unit ' + AUnit.Name, nil)
      else if TRecordTypeDef(UDcl.Def).Methods.Count > 0 then
      begin
        { Emit the record's method bodies HERE, in this unit's context, exactly
          as the class branch above does — a record method is an ordinary
          statically-bound function.  Emitting in unit context matters for the
          same reason it does for classes: the program-context walk would
          mis-resolve implementation-section unit globals (leg 39). }
        URDef := TRecordTypeDef(UDcl.Def);
        for M := 0 to URDef.Methods.Count - 1 do
        begin
          MDcl := TMethodDecl(URDef.Methods.Items[M]);
          if MDcl.Body = nil then Continue;
          if MDcl.TypeParams <> nil then Continue;
          EmitFunctionDef(MDcl);
        end;
      end;
    end;
  end;

begin
  { Same deliberately-incremental subset as EmitProgram: routines and
    record types lower; everything else stays an honest hole.  Cross-unit
    call sites need nothing here — RoutineSym mangles through the
    semantic pass's ResolvedQbeName on both the definition and the call. }
  FCurrentUnitName := AUnit.Name;
  RegisterUnitVars(AUnit.IntfBlock);
  RegisterUnitVars(AUnit.ImplBlock);
  Self.Emit('.text');
  CheckTypeSubset(AUnit.IntfBlock.TypeDecls);
  CheckTypeSubset(AUnit.ImplBlock.TypeDecls);
  { Generic RECORD instances declared in this unit: emit their method bodies
    here, in unit context, exactly as the program path does.  No wrapper decl
    is built — a record instance has no typeinfo and no vtable — and the bodies
    are weak-bound so duplicates across units collapse at link time. }
  for I := 0 to AUnit.GenericRecordInstances.Count - 1 do
  begin
    URGDef := TGenericRecordInstance(
                AUnit.GenericRecordInstances.Items[I]).RecordDef;
    for J := 0 to URGDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(URGDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      EmitFunctionDef(Decl, True);
    end;
  end;
  for I := 0 to AUnit.GenericInstances.Count - 1 do
  begin
    { interface-implementing instances flow through too — their itab +
      impllist are weak-bound in EmitIntfMetaSections (leg 15). }
    UTD := TTypeDecl.Create();
    UTD.Name := TGenericInstance(AUnit.GenericInstances.Items[I]).TypeName;
    UTD.Def := TGenericInstance(AUnit.GenericInstances.Items[I]).ClassDef;
    UTD.ResolvedDesc :=
      TGenericInstance(AUnit.GenericInstances.Items[I]).TypeDesc;
    FGenericDecls.Add(UTD);
    FClassDecls.Add(UTD);
    { This unit emits these instance bodies itself, further down (the
      AUnit.GenericInstances EmitFunctionDef walk).  Register the wrapper so
      EmitProgram's FClassDecls walk skips it — exactly the leg-39 guard used
      for a unit's ordinary classes.  Without this, a whole-program build emits
      the body TWICE into ONE assembly unit and the internal assembler rejects
      the duplicate label (e.g. TListEnumerator_String_Create for any program
      that `uses Classes`).  Weak linkage does not help here: it collapses
      duplicates across OBJECTS, not within a single object. }
    FUnitEmittedClasses.Add(UTD);
  end;
  { generic INTERFACE instances from this unit — weak typeinfo, like the program
    path (leg 41).  Omitting this leaves a unit-scoped instance's typeinfo
    dangling at link. }
  for I := 0 to AUnit.GenericIntfInstances.Count - 1 do
    FGenericIntfInstances.Add(AUnit.GenericIntfInstances.Items[I]);
  for I := 0 to AUnit.GenericFuncInstances.Count - 1 do
    EmitFunctionDef(
      TGenericFuncInstance(AUnit.GenericFuncInstances.Items[I]).MethodDecl,
      True);
  { generic METHOD instances (leg 37) — weak-bound like the func instances }
  for I := 0 to AUnit.GenericMethodInstances.Count - 1 do
    if TGenericMethodInstance(
         AUnit.GenericMethodInstances.Items[I]).MethodDecl.Body <> nil then
      EmitFunctionDef(
        TGenericMethodInstance(AUnit.GenericMethodInstances.Items[I]).MethodDecl,
        True);

  Self.Emit('.text');

  { Generic CLASS instance method bodies (leg 43).  A unit that materialises
    TList<TMoSymbol>, TDictionary<string,Integer>, etc. must emit those clones'
    method bodies in its own object — weak-bound (bare name) so the linker
    dedups the copies across every object that materialises the same instance
    (BUG-004).  Without this the vtable/itab .quad references (emitted by
    FinalizeEmit's metadata pass) point at symbols nothing defines and the
    link binds them from libSystem → dyld abort at launch (GH #189-class link
    gap; x86-64 does this in EmitClassMethods).  The clone's Line fields refer
    to the DECLARING unit, so swap FCurrentUnitName to DefUnitName for correct
    allocation-site tracking, exactly like x86-64. }
  SavedUnit := FCurrentUnitName;
  for I := 0 to AUnit.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AUnit.GenericInstances.Items[I]);
    if GI.DefUnitName <> '' then
      FCurrentUnitName := GI.DefUnitName
    else
      FCurrentUnitName := SavedUnit;
    GICDef := TClassTypeDef(GI.ClassDef);
    for J := 0 to GICDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GICDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      if Decl.TypeParams <> nil then Continue;   { generic-method template }
      EmitFunctionDef(Decl, True);               { weak: bare generic-instance name }
    end;
  end;
  FCurrentUnitName := SavedUnit;

  for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
    if Decl.OwnerTypeName <> '' then Continue;   { method stubs — types NotYet above }
    if Decl.TypeParams <> nil then Continue;     { generic templates }
    if Decl.Body = nil then Continue;            { forward decls }
    if Decl.IsExternal then Continue;            { externals: call-site only }
    EmitFunctionDef(Decl);
  end;

  { Initialization section: a parameterless <unit>_init routine that _main
    calls (in dependency order) right after _BlaiseInit.  Finalization
    becomes <unit>_final, called at program exit in REVERSE order —
    genuinely invoked, unlike the x86 emit-but-never-call shape. }
  if (AUnit.InitStmts <> nil) and (AUnit.InitStmts.Count > 0) then
    EmitUnitInit(AUnit);
  if (AUnit.FinalStmts <> nil) and (AUnit.FinalStmts.Count > 0) then
    EmitUnitSection(AUnit, AUnit.FinalStmts,
      DarwinSym(CodegenMangle(AUnit.Name) + '_final'), FUnitFinals);
  EmitArrayConstData(AUnit.IntfBlock);
  EmitArrayConstData(AUnit.ImplBlock);
  FCurrentUnitName := '';
end;

procedure TArm64Backend.EmitUnitInit(AUnit: TUnit);
begin
  EmitUnitSection(AUnit, AUnit.InitStmts,
    DarwinSym(CodegenMangle(AUnit.Name) + '_init'), FUnitInits);
end;

procedure TArm64Backend.NoteDepInitUnit(const AUnitName: string;
  AHasInit: Boolean);
begin
  { Separate compilation: the dep's <Unit>_init lives in the dep's own object,
    so EmitUnit never ran here to register it.  Record the mangled name so
    EmitProgram's _main still calls it — the mangling must match EmitUnitInit's
    DarwinSym(CodegenMangle(AUnit.Name) + '_init') exactly. }
  if AHasInit then
    FUnitInits.Add(DarwinSym(CodegenMangle(AUnitName) + '_init'));
end;

procedure TArm64Backend.NoteDepFiniUnit(const AUnitName: string;
  AHasFini: Boolean);
begin
  { Teardown twin: _main calls the finals in reverse registration order.

    DELIBERATELY NOT WIRED UP YET.  AHasFini comes from the shared
    UnitNeedsFini predicate, which is True for a unit with a finalization
    section OR with managed (ARC) module globals.  arm64's EmitUnit currently
    emits <Unit>_final ONLY for a real finalization section — it has no
    managed-global release walk (x86-64 emits one inside its <Unit>_fini).
    Registering the name here regardless would make _main call a symbol the
    arm64 backend never defines, and the link fails on exactly the units whose
    only teardown need is managed globals.

    The missing managed-global teardown is a pre-existing arm64 LEAK, tracked
    separately (BUG-20260723-arm64-unit-managed-global-teardown) — not a
    correctness regression, and out of scope for the init-call fix above.
    When that walk lands, register the name here on the same predicate
    EmitUnit uses so the two cannot drift. }
end;

procedure TArm64Backend.EmitUnitSection(AUnit: TUnit; AStmts: TObjectList;
  const ASym: string; ARegistry: TStringList);
var
  I, J: Integer;
  FrameAligned: Integer;
  SavedAsm, BodyBuf: TStringBuilder;
begin
  ARegistry.Add(ASym);
  FIsFunction := False;
  FResultFloat := False;
  FResultSingle := False;
  FExitLabel := NewLabel('usectexit');
  FFrame.Clear();
  FFrameSize := 0;
  FStrLocals.Clear();
  FRecLocals.Clear();
  FByValRecParams.Clear();
  FObjLocals.Clear();
  FWeakLocals.Clear();
  FIntfLocals.Clear();
  FForN := 0;
  AddLocal('__iret', 16);
  { __rret: always >= 16 (register-shape record-call field reads) }
  J := 16;
  for I := 0 to AStmts.Count - 1 do
    if MaxManagedRecRet(TASTStmt(AStmts.Items[I])) > J then
      J := MaxManagedRecRet(TASTStmt(AStmts.Items[I]));
  AddLocal('__rret', J);
  ReservePendRelSlots();   { BUG-048: statement-scoped deferred class releases }
  for I := 0 to AStmts.Count - 1 do
    RegisterForSlots(TASTStmt(AStmts.Items[I]));
  FForN := 0;
  FrameAligned := (FFrameSize + 15) and (not 15);
  Self.Emit('');
  EmitGloblDef(ASym);
  Self.Emit(ASym + ':');
  Self.Emit(#9'stp x29, x30, [sp, #-16]!');
  Self.Emit(#9'mov x29, sp');
  SavedAsm := FAsm;
  BodyBuf := TStringBuilder.Create();
  FAsm := BodyBuf;
  FExcDepth := 0;
  FExcSlotN := 0;
  FFinallyBodies.Clear();
  FLoopExcDepth.Clear();
  EmitStmtList(AStmts);
  Self.Emit(FExitLabel + ':');
  Self.Emit(#9'mov sp, x29');
  Self.Emit(#9'ldp x29, x30, [sp], #16');
  Self.Emit(#9'ret');
  FAsm := SavedAsm;
  FrameAligned := (FFrameSize + 15) and (not 15);
  if FrameAligned > 0 then
    EmitAddSubImm('sub', 'sp', 'sp', FrameAligned);
  FAsm.Append(BodyBuf.ToString());
  BodyBuf.Free();
  FFrame.Clear();
  FFrameSize := 0;
end;

procedure TArm64Backend.RegisterUnitVars(ABlock: TBlock);
var
  I, J: Integer;
  VD: TVarDecl;
  N: string;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    VD := TVarDecl(ABlock.Decls.Items[I]);
    if not (IsIntFam(VD.ResolvedType) or
            ((VD.ResolvedType <> nil) and
             (VD.ResolvedType.Kind in [tyDouble, tySingle, tyString,
                                       tyRecord, tyClass, tyInterface,
                                       tyMetaClass, tyStaticArray,
                                       tyDynArray, tySet,
                                       tyPointer, tyPChar,
                                       tyProcedural]))) then
      NotYet('unit variable of this type', VD);
    { A JUMBO set (> 64 members) is an inline byte-array bitmap, so its slot is
      sized from RawSize() -- see the jumbo arm below; it does NOT fall out of
      the generic 8-byte default.  The operations on it go through the _Set*
      RTL helpers. }

    for J := 0 to VD.Names.Count - 1 do
    begin
      FModuleVarNames.Add(VD.Names.Strings[J]);
      { register under the owning-unit-prefixed symbol so same-named vars
        in different units (or the program) cannot collide }
      N := GlobalSym(VD.Names.Strings[J]);
      FGlobalNames.Add(N);
      { an RTL-unit global carries a bare symbol every inlining object
        re-defines — weak binding lets the copies collapse (GH #174) }
      if (FCurrentUnitName <> '') and IsUnmangledUnit(FCurrentUnitName) then
        FGlobalWeak.Add(N);
      if VD.InitConst <> nil then
        RegisterGlobalInit(N, VD);
      if VD.IsThreadVar then
      begin
        { unmanaged scalar kinds and static arrays of them — per-thread
          ARC teardown is its own problem, so managed kinds stay NotYet }
        if not (IsIntFam(VD.ResolvedType) or
                (VD.ResolvedType.Kind in [tyDouble, tyPointer, tyPChar,
                                          tyClass]) or
                ((VD.ResolvedType.Kind = tyStaticArray) and
                 not AggHasManaged(VD.ResolvedType))) then
          NotYet('threadvar of this type', VD);
        if VD.InitConst <> nil then
          NotYet('initialised threadvar', VD);
        FTlvGlobals.Add(N);
        if (FCurrentUnitName <> '') and
           IsUnmangledUnit(FCurrentUnitName) then
          FGlobalWeak.Add('__tlv_' + N);
        if VD.ResolvedType.Kind = tyStaticArray then
          FTlvSize.Items[N] := VD.ResolvedType.RawSize()
        else
          FTlvSize.Items[N] := 8;
        FGlobalNames.Delete(FGlobalNames.Count - 1);
        FGlobalSize.Remove(N);
      end;
      if VD.ResolvedType.Kind = tyString then
        FStrGlobals.Add(N);
      if (VD.ResolvedType.Kind = tyClass) and not VD.IsWeak then
        FObjGlobals.Add(N);
      if VD.ResolvedType.Kind = tyDynArray then
        FDynGlobals.Add(N);
      if VD.ResolvedType.Kind = tyInterface then
      begin
        FGlobalNames.Add(N + '_itab');
        FGlobalSize.Add(N + '_itab', 8);
        if not VD.IsWeak then
          FIntfGlobals.Add(N);
      end;
      if VD.ResolvedType.Kind in [tyRecord, tyStaticArray] then
      begin
        if VD.ResolvedType.Kind = tyRecord then
          FRecGlobals.AddObject(N, VD.ResolvedType);
        FGlobalSize.Add(N, VD.ResolvedType.RawSize());
      end
      else if IsMethodPtrType(VD.ResolvedType) then
        FGlobalSize.Add(N, 16)    { closure / method-pointer: Code + Env }
      else if (VD.ResolvedType is TSetTypeDesc) and
              TSetTypeDesc(VD.ResolvedType).IsJumbo() then
        FGlobalSize.Add(N, VD.ResolvedType.RawSize())   { inline bitmap }
      else
        FGlobalSize.Add(N, 8);
    end;
  end;
end;

procedure TArm64Backend.FinalizeEmit;
begin
  { unit-as-top compiles (separate compilation) emit their data sections
    here — EmitProgram has its own inline tail.  Without this a unit
    object DEFINES none of its globals/literals/metadata/cleanup fns and
    every cross-object reference dangles at link (or worse: the Mach-O
    linker's underscore rule turns a missing _FieldCleanup_X into a
    phantom libSystem import). }
  Self.Emit('.text');
  if FClassDecls.Count > 0 then
    EmitClassCleanupFns();
  EmitStrLitSection();
  EmitFloatLitSection();
  EmitGlobalsSection();
  if FClassDecls.Count > 0 then
    EmitClassMetaSections();
  EmitIntfMetaSections();
  EmitTlvSections();
end;

{ ---- ARC walk primitives ------------------------------------------------- }

function TArm64Backend.ArcNestedBaseReg: string;
begin
  Result := 'x20';
end;

procedure TArm64Backend.ArcPushNestedBase(AOffset: Integer;
  const ABaseReg: string);
begin
  { Save the nested-base scratch as a full 16-byte slot (sp alignment holds
    across the recursion's runtime calls), then derive parent+offset. }
  Self.Emit(#9'str x20, [sp, #-16]!');
  if AOffset > 0 then
    Self.Emit(Format(#9'add x20, %s, #%d', [ABaseReg, AOffset]))
  else
    Self.Emit(Format(#9'mov x20, %s', [ABaseReg]));
end;

procedure TArm64Backend.ArcPopNestedBase;
begin
  Self.Emit(#9'ldr x20, [sp], #16');
end;

procedure TArm64Backend.EmitWeakClearAt(AOffset: Integer;
  const ABaseReg: string);
begin
  if AOffset > 0 then
    Self.Emit(Format(#9'add x0, %s, #%d', [ABaseReg, AOffset]))
  else
    Self.Emit(Format(#9'mov x0, %s', [ABaseReg]));
  EmitCallSym('_WeakClear');
end;

procedure TArm64Backend.EmitReleaseSlotAt(AType: TTypeDesc; AOffset: Integer;
  const ABaseReg: string; AZero: Boolean);
begin
  Self.Emit(Format(#9'ldr x0, [%s, #%d]', [ABaseReg, AOffset]));
  if AType.IsString() then
    EmitCallSym('_StringRelease')
  else if AType.Kind = tyDynArray then
    EmitCallSym('_DynArrayRelease')
  else
    { tyClass and tyInterface release the obj slot via _ClassRelease }
    EmitCallSym('_ClassRelease');
  if AZero then
    Self.Emit(Format(#9'str xzr, [%s, #%d]', [ABaseReg, AOffset]));
end;

procedure TArm64Backend.EmitRetainSlotAt(AType: TTypeDesc; AOffset: Integer;
  const ABaseReg: string);
begin
  Self.Emit(Format(#9'ldr x0, [%s, #%d]', [ABaseReg, AOffset]));
  if AType.IsString() then
    EmitCallSym('_StringAddRef')
  else if AType.Kind = tyDynArray then
    EmitCallSym('_DynArrayAddRef')
  else
    EmitCallSym('_ClassAddRef');
end;

procedure TArm64Backend.ArcEnterArrayWalk(const ABaseReg: string);
begin
  { x21 anchors the array base, x20 derives each element — saved as a PAIR
    so sp stays 16-aligned at the per-element release/retain calls. }
  Self.Emit(#9'stp x21, x20, [sp, #-16]!');
  Self.Emit(Format(#9'mov x21, %s', [ABaseReg]));
end;

procedure TArm64Backend.ArcArrayElemAddr(AByteOffset: Integer);
begin
  { The element offset is unbounded — an array of 6000 managed elements walks
    past 48000 bytes — but an add-immediate encodes only 12 bits.  Go through
    EmitAddSubImm, which materialises anything over 4095 via x16, instead of
    emitting a raw `add #imm` that the assembler then rejects outright
    ("add/sub immediate out of range: 4096", 2026-07-23). }
  if AByteOffset > 0 then
    EmitAddSubImm('add', 'x20', 'x21', AByteOffset)
  else
    Self.Emit(#9'mov x20, x21');
end;

function TArm64Backend.ArcArrayElemReg: string;
begin
  Result := 'x20';
end;

procedure TArm64Backend.ArcLeaveArrayWalk;
begin
  Self.Emit(#9'ldp x21, x20, [sp], #16');
end;

end.
