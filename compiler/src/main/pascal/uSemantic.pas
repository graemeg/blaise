{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uSemantic;

// Semantic analysis pass — walks the AST produced by uParser and:
//   1. Resolves record/class type declarations and registers them in the symbol table.
//   2. Indexes class methods for dispatch lookup.
//   3. Analyses method bodies with Self and explicit params in scope.
//   4. Resolves every identifier to a TSymbol in the symbol table.
//   5. Infers and annotates every expression node with ResolvedType.
//   6. Type-checks assignments, field assignments, and method calls.
//   7. Validates procedure/function calls.
//   8. Raises ESemanticError with source position on any violation.

interface

uses
  SysUtils, Classes, contnrs, uAST, uSymbolTable, uStrCompat,
  uUnitInterface, uLexer, uParser;

type
  ESemanticError = class(Exception);

  { One entry in the enum-member reverse index: the enum type a member
    belongs to, the member's ordinal value, and a monotonic declaration
    rank (higher = declared later, wins the context-free ambiguity
    fallback).  Owned by TSemanticAnalyser.FEnumMemberRefs. }
  TEnumMemberRef = class
    EnumDesc: TEnumTypeDesc;
    Ordinal:  Int64;
    Order:    Integer;
  end;

  TSemanticAnalyser = class(TUsesChainProvider)
  private
    FTable:                TSymbolTable;
    FProg:                 TProgram;      { current program being analysed; set in Analyse }
    FCurrentUnit:          TUnit;        { current unit being analysed; nil during program analysis }
    FMethodIndex:          TStringList;  { 'TypeName.MethodName' → TMethodDecl (not owned) }
    FProcIndex:            TStringList;  { 'ProcName' → TMethodDecl (not owned) }
    { Overload groups: same keys as FProcIndex/FMethodIndex, but each entry's
      Object is a TObjectList(False) holding EVERY decl registered under that
      key, in insertion order.  Lets per-call-site overload resolution fetch
      all candidates with one hashed IndexOf instead of a full scan of the
      index (which was O(calls × decls)).  Kept in sync by the Register*
      helpers and ReplaceProcIndexObject. }
    FProcGroups:           TStringList;  { 'ProcName' → TObjectList of TMethodDecl }
    FMethodGroups:         TStringList;  { 'Type.Method' → TObjectList of TMethodDecl }
    { Owns the group lists.  TStringList.Objects holds raw (non-retained)
      pointers, so a group whose only strong reference were a local would be
      released at the creating routine's exit (TObjectList.Add retains its
      items; TStringList.AddObject does not).  Every group created by
      AddGroupEntry is also added here, which retains it for the analyser's
      lifetime; the destructor frees this list, releasing the groups. }
    FGroupKeepAlive:       TObjectList;
    { Generic instances created while no program/unit is being analysed —
      i.e. when ImportUnitInterface triggers FindTypeOrInstantiate to resolve
      a cached iface's generic-instance field type (e.g. 'TList<TFoo>') before
      Analyse/AnalyseUnit has set FProg/FCurrentUnit.  Holding them here (non-
      owning) avoids a nil-deref on FProg.GenericInstances.Add; FlushPending
      GenericInstances moves them into the real owner once analysis begins so
      codegen still emits the instance's methods. }
    FPendingGenericInstances:       TObjectList; { TGenericInstance — not owned }
    { True while analysing a nested routine declared inside a METHOD body:
      the enclosing method's Self is capturable like any other outer name
      (BUG-008) — CollectCaptures lists it in the outer-vars set and the
      hidden by-pointer capture params thread it into the nested routine. }
    FInNestedOfMethod: Boolean;
    FPendingGenericRecordInstances: TObjectList; { TGenericRecordInstance — not owned }
    FPendingGenericIntfInstances:   TObjectList; { TGenericInterfaceInstance — not owned }
    FGenericFuncTemplates: TStringList;  { base name → TMethodDecl template (not owned) }
    FPendingAnonDecls:    TObjectList;   { non-owning — lifted anonymous-method
                                           thunks awaiting registration + body
                                           analysis; drained in module scope by
                                           DrainPendingAnonDecls after the
                                           enclosing bodies complete }
    FEnvTypeCount:        Integer;       { per-compilation counter for
                                            synthetic '__env_<n>' records }
    FAnonMethodCount:     Integer;       { per-compilation counter for
                                           '__closure_<n>' thunk names }
    FGenericMethodTemplates: TStringList; { 'OwnerType.Method' → TMethodDecl template (not owned) — generic methods with method-level <T> }
    FLoopDepth:            Integer;      { depth of enclosing while/for — Break only legal if > 0 }
    FScopeDepth:           Integer;      { mirrors FTable scope depth; used to detect main-level globals }
    FCurrentClass:         TRecordTypeDesc;  { class being analysed (set in AnalyseMethodDecl) }
    FCurrentBlockFirstSite: TObject;         { TVarDeclStmt — first block-scoped
                                               var declaration of the compound
                                               statement currently being analysed
                                               (the block's env alloc site);
                                               saved/restored per compound }
    FCurrentMethodDecl:    TMethodDecl;      { instance-method body being analysed
                                               (set in AnalyseMethodDecl alongside
                                               FCurrentClass) — the enclosing frame
                                               for anonymous-method capture inside
                                               methods (Phase 3) }
    FCurrentMethodOwner:   TRecordTypeDesc;  { declaring type of the method body
                                               currently being analysed — set for
                                               BOTH instance and STATIC methods.
                                               Unlike FCurrentClass (nil inside a
                                               static body so implicit-Self refs
                                               fail), this is used only by member-
                                               visibility checks so a strict-private
                                               member is reachable from its own
                                               type's static methods too. }
    { Type-parameter names in scope while analysing an instantiated generic
      body (T, K, V, ...).  These are registered as skType aliases (T=Integer)
      so the body resolves, but they are NOT user-declared types, so a local
      variable may legitimately share a name with one (var t: T).  The
      shadow-a-type-name check skips names found here. }
    FActiveTypeParams:     TStringList;
    FForInLoopVars:        TStringList;  { stack of active for-in loop-variable names (nested loops
                                           push/pop); a write to one of these is diagnosed — the
                                           mutation goes to a per-iteration copy and is discarded }
    FWarnings:             TStringList;  { non-fatal diagnostics collected during analysis; each is
                                           also written to StdErr as it is raised (see SemanticWarning) }
    FCurrentLocalBlock:    TBlock;       { block currently being stmt-analysed; for-in injects synthetic TVarDecl here }
    FForInCounter:         Integer;      { counter for generating unique __forin_N variable names }
    FArrayConstCounter:    Integer;      { counter for generating unique array-const data labels }
    FAnonEnumCounter:      Integer;      { counter for unique anonymous-enum type names (inline 'set of (a,b,c)') }
    FCurrentUnitName:      string;       { name of the unit/program currently being analysed }
    FMethodOwnerHint:      string;       { receiver owning-unit hint for the NEXT
                                           ResolveMethodOverload call, consumed and
                                           cleared at its start.  Disambiguates a
                                           method on a cross-unit same-named type to
                                           the receiver's actual unit.  A field, not
                                           a parameter, to keep ResolveMethodOverload
                                           within the 6-register call ABI. }
    FCurrentEnclosingDecl: TMethodDecl;  { the innermost standalone proc/func currently being analysed;
                                           nil at program level.  Used to set EnclosingDecl on nested procs. }
    FUnitIfaces:           TStringList;  { owned list (case-insensitive) — keys are unit
                                           names, Objects[I] is the TUnitInterface (NOT
                                           owned by the analyser; .bif ifaces are owned by
                                           Loader.PrebuiltIfaces, source-built ifaces by
                                           UnitIfaces in Blaise.pas).  Registered alongside
                                           ImportUnitInterface and after AnalyseUnitForExport
                                           so per-unit lookups can find an iface by name. }
    FUnitSymbols:          TStringList;  { owned (case-insensitive); keys are
                                           'UnitName' + #1 + 'SymbolName'; Objects[I] is
                                           a TSymbol (NOT owned — the canonical TSymbol
                                           is owned by FTable today, mirrored here as a
                                           direct per-unit index.  Used by the chain
                                           walker so retrieval doesn't need to filter
                                           a flat global by OwningUnit.  Sentinel
                                           character #1 keeps the key unambiguous even
                                           when a unit name contains a colon (rare). }
    FCurrentUsesChain:     TStringList;  { owned — uses-chain visible to FCurrentUnitName.
                                           Index 0 is the implicit System unit; entries 1..N-1
                                           come from the analysed program/unit's UsedUnits in
                                           source order.  Lookup walks this list right-to-left
                                           ("last in uses wins"); System is the final fallback.
                                           Empty during pure import phases. }
    FEnumMemberIndex:      TStringList;  { owned (case-insensitive, dupAccept) — reverse
                                           index of enum member names.  Strings[I] is a
                                           member name, Objects[I] a TEnumMemberRef giving
                                           its enum type + ordinal + declaration order.
                                           A name may appear more than once (the same
                                           member name in several enums); resolution
                                           picks by context, uniqueness, or last-wins.
                                           Replaces the old bare skConstant registration
                                           — enum members are no longer flat globals. }
    FEnumMemberRefs:       TObjectList;  { owns the TEnumMemberRef holders pointed at by
                                           FEnumMemberIndex.Objects (TStringList does not
                                           own its Objects). }
    FEnumOrderCounter:     Integer;      { monotonic rank stamped on each member as it is
                                           registered; higher = declared later = wins the
                                           context-free ambiguity fallback. }

    { Add ADecl to FProcIndex under key AName, auto-tagging
      ADecl.OwningUnit from FCurrentUnitName if not already set.
      Wraps the seven free-routine registration sites so a future
      chain-aware filter can read OwningUnit off any FProcIndex
      entry. }
    procedure RegisterProcDecl(const AName: string; ADecl: TMethodDecl);

    { Like FProcIndex.IndexOf, but only matches a forward decl whose OwningUnit
      is AUnitName.  FProcIndex is global across all compiled units, so a bare
      IndexOf can return a same-named decl from an imported unit. }
    function IndexOfProcInUnit(const AName, AUnitName: string): Integer;

    { The emitted/imported link symbol for a standalone routine: the
      `external name` for an external binding (defaulting to the Pascal name),
      else ResolvedQbeName (bare name for unmangled RTL units) or the name. }
    function EffectiveLinkName(A: TMethodDecl): string;

    { True when A and B denote the SAME underlying link symbol with the same
      arity, where AT LEAST one side is an external binding.  Covers two units
      each declaring `external name 'strlen'` AND a binding (`external name
      '_BlaiseGetMem'`) targeting a real function exported by an unmangled RTL
      unit.  Used to collapse false "ambiguous overload" / "duplicate
      identifier" errors in the multi-unit flat-merge. }
    function SameLinkSymbol(A, B: TMethodDecl): Boolean;

    { True when A and B are two declarations of the SAME external C function —
      both external, same effective link name, same arity.  Used to collapse the
      false "ambiguous overload" that arises when two units each privately
      declare e.g. `external name 'strlen'`. }
    function SameExternalDecl(A, B: TMethodDecl): Boolean;

    { True when every candidate in AList collapses to the same link symbol as
      the first (per SameLinkSymbol).  Used when arg scoring is unavailable
      (zero-arity early path). }
    function AllSameExternalDecl(AList: TObjectList): Boolean;

    { True when the global scope already holds a symbol that denotes the SAME
      external C function as ANew — e.g. two units each declaring
      `function _BlaiseGetMem(...): Pointer; external name '_BlaiseGetMem';`.
      Such a re-declaration is benign (one underlying symbol), not a genuine
      duplicate identifier.  Returns False for anything but matching externals. }
    function BenignDuplicateExternal(ANew: TMethodDecl): Boolean;

    { Overload-group plumbing (see FProcGroups/FMethodGroups).  Every
      FProcIndex/FMethodIndex AddObject must go through the Add*GroupEntry
      sibling so the groups stay complete; FProcIndex.Objects[] rewrites go
      through ReplaceProcIndexObject so the group sees the swap. }
    procedure AddGroupEntry(AGroups: TStringList; const AKey: string;
                            ADecl: TMethodDecl);
    function  GroupOf(AGroups: TStringList; const AKey: string): TObjectList;
    procedure ReplaceProcIndexObject(AIdx: Integer; ANew: TMethodDecl);

    { Populates FCurrentUsesChain from a program/unit's UsedUnits list.
      Pure plumbing — no behavior change today; consumed by uses-chain
      lookup in a later step. }
    procedure BuildUsesChain(AUsedUnits: TStringList);

    { Generic type instantiation: resolves 'TBox<Integer>' on demand. }
    function  FindTypeOrInstantiate(const AName: string): TTypeDesc;

    { Resolves a parameter's type, handling both plain types and open arrays.
      For IsOpenArray params, creates and registers a TOpenArrayTypeDesc. }
    function  ResolveParamType(APar: TMethodParam;
                ALoc: Integer; ACol: Integer): TTypeDesc;
    function  InstantiateGeneric(const ATypeName: string): TRecordTypeDesc;
    function  InstantiateGenericRecord(const ATypeName: string): TRecordTypeDesc;
    function  InstantiateGenericInterface(const ATypeName: string): TInterfaceTypeDesc;
    { Generic procedural-type instantiation: resolves 'TGetter<Integer>' on
      demand from a TGenericProcDef template.  Pure type metadata — defines a
      TProceduralTypeDesc symbol, emits nothing. }
    function  InstantiateGenericProcType(const ATypeName: string): TProceduralTypeDesc;
    function  SubstTypeParam(const ATypeName: string;
                AParamNames, AArgs: TStringList): string;

    { Resolves scope-bound type params inside a generic type name such as
      'TGenEnum<T>' when 'T' is bound in the current scope as a skType symbol.
      Returns the canonical name (e.g. 'TGenEnum<Integer>') suitable for
      FindTypeOrInstantiate. Has no effect on names without '<'. }
    function  ResolveScopeBoundTypeParams(const ATypeName: string): string;

    { Canonicalises the type arguments of a generic instantiation name by
      resolving each argument through any alias chain to its underlying type's
      canonical name.  'TList<TIntAlias>' (where TIntAlias = Integer) becomes
      'TList<Integer>', so an instantiation using a transparent type alias and
      one using the alias's underlying type share a single identity.  Has no
      effect on names without '<' or on arguments that are unresolved type
      parameters. }
    function  CanonGenericArgs(const ATypeName: string): string;

    { Generic function instantiation: resolves 'Identity<Integer>' on demand. }
    function  InstantiateGenericFunc(const AInstName: string): TMethodDecl;
    { Generic method instantiation: resolves 'Pick<Integer>' on an owner class
      on demand, preserving the implicit Self.  Returns the monomorphised
      TMethodDecl (with ResolvedQbeName set), or nil if not a generic method. }
    function  InstantiateGenericMethod(const AOwnerType, AInstName: string): TMethodDecl;

    procedure AnalyseBlock(ABlock: TBlock; AIsProgramTop: Boolean = False);
    procedure AnalyseConstDecls(ABlock: TBlock);
    { Resolve a set-valued const decl (IsSet): fold the member bitmask into
      CD.IntVal and register the const symbol with its tySet type. }
    procedure AnalyseSetConstDecl(ACD: TConstDecl);
    function  ResolveSetMemberOrd(const AMember: string; ACD: TConstDecl;
                                  var AEnumDesc: TEnumTypeDesc): Integer;
    procedure AnalyseArrayConstDecls(ABlock: TBlock);
    { Build the (possibly nested) static-array type for a range-indexed array
      const and validate that the flat row-major element count matches the
      product of the dimension sizes.  Single-dimension constants build one
      TStaticArrayTypeDesc as before; multi-dimensional ones build the nested
      array[d0] of array[d1] of ... of Elem chain. }
    function BuildConstArrayType(ACD: TConstDecl;
      AElemTD: TTypeDesc): TStaticArrayTypeDesc;
    { Mint a unique, link-safe QBE data-label for an array const.  The source
      name is kept for lookups; this mangled label is what codegen emits and
      references so identically-named consts in different scopes (and consts
      inside the RTL) never collide at link time. }
    function  NewArrayConstLabel(const AName: string): string;
    function  FoldConstBitOpExpr(ATokens: TStringList;
                                 ALine, ACol: Integer): Int64;
    { Fold a compile-time integer constant expression AST (literals, named
      constants, and the integer binary/unary operators with the precedence
      already encoded in the tree shape) to its Int64 value.  Named-constant
      references are resolved against the symbol table, so this must run after
      the referenced consts are declared. }
    function  EvalConstIntExpr(AExpr: TASTExpr; ALine, ACol: Integer): Int64;
    function  EvalConstFloatExpr(AExpr: TASTExpr; ALine, ACol: Integer): string;
    function  IsFloatConstExpr(AExpr: TASTExpr): Boolean;
    function  ResolveArrayBound(const ABoundText: string): Integer;
    function  ResolveSubrangeSetType(const ASubrange: string): TSetTypeDesc;
    function  ResolveConstArrayElem(const AElem: string; AElemType: TTypeDesc;
                                    ALine, ACol: Integer): string;
    procedure AnalyseTypeDecls(ABlock: TBlock);
    procedure LinkClassMethodImpls(ABlock: TBlock);
    procedure LinkGenericClassMethodImpls(ABlock: TBlock);
    procedure CheckClassMethodsImplemented(ABlock: TBlock);
    procedure RepairEarlyGenericInstances;
    { Move any generic instances parked at import time (FProg/FCurrentUnit
      both nil) into the now-current program or unit, so codegen emits their
      method bodies.  Called at the start of Analyse / AnalyseUnit. }
    procedure FlushPendingGenericInstances;
    procedure AnalyseMethodBodies(ABlock: TBlock);
    procedure AnalyseMethodDecl(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure AnalyseStandaloneDecls(ABlock: TBlock);
    procedure AnalyseStandaloneBodies(ABlock: TBlock);
    procedure AnalyseStandaloneDecl(ADecl: TMethodDecl);
    procedure CollectCaptures(ADecl: TMethodDecl; AOuterDecl: TMethodDecl);
    { Add AName to ADecl.CapturedVars if it names an enclosing variable
      (member of AOuterVars) not already recorded. }
    procedure MaybeCaptureName(ADecl: TMethodDecl; AOuterVars: TStringList;
                               const AName: string);
    { Inlining: after bodies are analysed, mark each TMethodDecl whose body
      qualifies for codegen-side inlining.  Conservative: primitive params
      + return + locals only; no try/loops/raise/nested defs; small body.
      See docs/inlining-design.adoc. }
    procedure MarkInlineCandidates(ABlock: TBlock);
    function  IsInlineEligible(ADecl: TMethodDecl): Boolean;
    function  StmtRejectsInline(AStmt: TASTStmt;
                                 const ASelfDecl: TMethodDecl;
                                 var AStmtCount: Integer): Boolean;
    function  ExprRejectsInline(AExpr: TASTExpr;
                                 const ASelfDecl: TMethodDecl): Boolean;
    function  AssignmentTargetsParameter(const AName: string;
                                          const ADecl: TMethodDecl): Boolean;
    procedure AnalyseVarDecls(ABlock: TBlock);
    procedure AnalyseVarInitializer(ADecl: TVarDecl);
    function  SynthAnonEnum(const AMemberList: string): TEnumTypeDesc;
    procedure AnalyseStmts(ABlock: TBlock);
    procedure AnalyseStmt(AStmt: TASTStmt);
    procedure AnalyseAssignment(AAssign: TAssignment);
    procedure AnalyseFieldAssignment(AAssign: TFieldAssignment);
    function  TryAnalyseFieldElemWrite(AAssign: TFieldAssignment;
      AFldInfo: TFieldInfo): Boolean;
    function  TryLowerDefaultPropertyWrite(AAssign: TFieldAssignment;
      AMemberType: TTypeDesc): Boolean;
    function  FloatBuiltinArgType(const AName: string; AArgType: TTypeDesc;
      ALine, ACol: Integer): TTypeDesc;
    procedure AnalyseProcCall(ACall: TProcCall);
    { Phase A/B overload resolution.  Walks FProcIndex collecting all
      decls whose name matches AName (case-insensitive); filters by
      arity; for the survivors, scores per-argument compatibility
      using AArgs (each TASTExpr already analysed, ResolvedType set);
      returns the highest-scoring candidate.  Raises ESemanticError on
      "no matching overload" or ambiguous ties.  AArgs may be nil for
      a pure arity probe (used when args are not yet analysed). }
    function  ResolveStandaloneOverload(const AName: string;
      AArity: Integer; AArgs: TObjectList;
      ALine, ACol: Integer): TMethodDecl;
    { Class-method overload resolution.  Walks the inheritance chain
      starting at ATypeName, collecting candidates whose method name
      matches AMethodName.  Filters by arity, scores by argument type
      (Phase B rules), returns the best match.  Raises ESemanticError
      on no-match or ambiguity.  AArgs may be nil to fall back to
      first-name-match (used by paths that need the decl before args
      are analysed, e.g. zero-arg lookups). }
    function  ResolveMethodOverload(const ATypeName, AMethodName: string;
      AArgs: TObjectList; ALine, ACol: Integer): TMethodDecl;
    { Score a pre-gathered arity-matched candidate list against AArgs and
      apply the tie-breakers (highest summed score, then fewer defaulted
      slots, then more exact matches).  Shared by ResolveMethodOverload and
      ResolveOperatorOverload: the two differ ONLY in how candidates are
      gathered (a single inheritance chain vs the union of both operand
      types' chains); scoring must stay identical and in one place.
      Returns nil when nothing scores; AAmbiguous is set when two or more
      candidates tie exactly. }
    function  PickBestCandidate(ACandidates, AArgs: TObjectList;
                out AAmbiguous: Boolean): TMethodDecl;
    { Operator-overload resolution.  Gathers `class operator` candidates of
      the given kind from BOTH operand types' inheritance chains (de-duped by
      node identity), then scores them with PickBestCandidate.  Returns nil
      when the operand types declare no such operator. }
    function  ResolveOperatorOverload(AKind: TOperatorKind;
      ALType, ARType: TTypeDesc; AArgs: TObjectList;
      ALine, ACol: Integer): TMethodDecl;
    { Append every `class operator` of AKind declared on ATypeName or an
      ancestor to ACandidates, skipping nodes already present. }
    procedure GatherOperatorCandidates(const ATypeName: string;
      AKind: TOperatorKind; ACandidates: TObjectList);
    { Operator fallback for AnalyseBinaryExpr.  Runs only after every built-in
      rule has declined and at least one operand is a record or class.  On a
      match the binary expression is LOWERED: a TMethodCallExpr calling the
      resolved static operator is synthesised, takes ownership of Left/Right
      (moved into its Args) and is stored in ABin.LoweredCall.  Codegen then
      emits an ordinary method call, so record sret returns, managed-field ARC
      and the calling convention are inherited rather than reimplemented per
      backend.  Returns the result type, or nil when no operator applies (the
      caller then raises its normal built-in error). }
    function  TryLowerOperator(ABin: TBinaryExpr;
      ALType, ARType: TTypeDesc): TTypeDesc;
    { AnalyseExpr for a slot the CALLER owns.  When analysis lowered an
      overloaded operator, the TBinaryExpr wrapper is dropped and the slot is
      rebound to the synthesised call, so every downstream consumer — codegen
      included — sees a plain TMethodCallExpr.  This matters because the
      record/sret/ARC machinery keys on NODE CLASS (`Asgn.Expr is
      TMethodCallExpr`, EmitRecordCallSretAt's dispatch, ...), not on a flag:
      a TBinaryExpr in those slots would match none of it.  Use this wherever
      an expression slot can hold a record- or class-valued expression. }
    function  AnalyseExprSlot(var ASlot: TASTExpr): TTypeDesc;
    { Rebind ASlot if it is a lowered TBinaryExpr; no-op otherwise. }
    procedure UnwrapLoweredOperator(var ASlot: TASTExpr);
    { AnalyseExprSlot for an element of an owned expression list (argument
      lists, array literals): the list slot cannot be passed as `var`. }
    function  AnalyseListSlot(AList: TObjectList; AIdx: Integer): TTypeDesc;
    { Type-code suffix for a single parameter.  Phase B mangling. }
    function  MangleTypeCode(AType: TTypeDesc; AVarParam: Boolean): string;
    { Full mangled signature for a TMethodDecl: '$<code1><code2>…'.
      Empty parameter list yields '$' (lone dollar). }
    function  MangleParamSig(ADecl: TMethodDecl): string;
    { Per-arg compatibility: 2 = exact, 1 = widening, 0 = no match. }
    function  ArgMatchScore(AParam: TTypeDesc; AArg: TTypeDesc;
                AArgExpr: TASTExpr = nil): Integer;
    { Shared enum of a bracket literal's elements, or nil (see impl). }
    function  SetLiteralBaseEnum(AExpr: TArrayLiteralExpr): TTypeDesc;
    { Re-type set-literal args to their `set of` param type post-overload. }
    procedure RetypeSetLiteralArgs(AArgs: TObjectList; AMDecl: TMethodDecl);
    procedure AnalyseMethodCall(ACall: TMethodCallStmt);
    { Resolve the return type of an interface method for a statement-position
      itab dispatch; nil for procedures.  Codegen uses this to give discarded
      sret-convention returns a throwaway buffer. }
    function  ResolveIntfMethodReturn(AIntf: TInterfaceTypeDesc;
      const AMethName: string): TTypeDesc;
    procedure AnalyseInheritedCall(ACall: TInheritedCallStmt);
    function  AnalyseInheritedCallExpr(ACall: TInheritedCallExpr): TTypeDesc;
    { True when AExpr is a valid actual for a var/out parameter (an addressable
      l-value): a variable, a field access, a pointer deref, or an array
      element subscript a[i]. }
    function  IsVarArgLValue(AExpr: TASTExpr): Boolean;
    { BUG-001: warn when a bare for-in loop variable is passed where the callee
      mutates it by reference (var/out parameter, Inc/Dec, SetLength, ...) —
      the mutation writes the per-iteration copy and never reaches the
      collection element.  Call at each site that accepts a by-ref actual. }
    procedure WarnIfVarArgIsForInLoopVar(AExpr: TASTExpr);
    { Enforce the lvalue constraint on every var/out actual of a resolved method
      call, and emit the BUG-001 for-in warning for each.  Method-call paths
      (unlike standalone-proc calls) historically skipped IsVarArgLValue, so a
      non-lvalue (e.g. a function-call result) passed to a var parameter slipped
      through the semantic pass and crashed codegen with 'var/out argument must
      be a variable or field' (BUG-011).  Call after AppendDefaultArgs. }
    procedure ValidateVarArgsExtras(AArgs: TObjectList; AMDecl: TMethodDecl;
      const AName: string; ALine, ACol: Integer);
    procedure ValidateMethodVarArgs(AArgs: TObjectList; AMDecl: TMethodDecl;
      const AName: string; ALine, ACol: Integer);
    { Interface-dispatch arm of the same check: no TMethodDecl is available at
      an interface call site, but the descriptor records per-param var flags,
      which is enough to enforce the lvalue constraint (types are not
      validated at interface-dispatch sites — Phase 3 limitation). }
    procedure ValidateIntfMethodVarArgs(AArgs: TObjectList;
      AIntf: TInterfaceTypeDesc; const AName: string; ALine, ACol: Integer);
    procedure AnalyseCaseStmt(AStmt: TCaseStmt);
    function  AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
    function  AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
    function  AnalyseIndirectFuncCallExpr(AExpr: TIndirectFuncCallExpr): TTypeDesc;
    function  AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
    function  AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
    function  AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
    function  TryLowerDefaultPropertyIndex(AAccess: TFieldAccessExpr;
      APropInfo: TPropertyInfo): TTypeDesc;
    function  AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
    function  AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;
    function  AnalyseSupportsExpr(AExpr: TSupportsExpr): TTypeDesc;
    function  AnalyseDerefExpr(AExpr: TDerefExpr): TTypeDesc;
    function  AnalyseAddrOfExpr(AExpr: TAddrOfExpr): TTypeDesc;
    { Phase 6: inside a generic instantiation's body analysis, rewrite the
      active type-param names (T -> Integer) in an anonymous-method literal's
      declaration BEFORE lifting.  The lifted thunk is analysed later by
      DrainPendingAnonDecls in module scope, where the instantiation's
      type-param bindings are gone — so the names must be made concrete now.
      Covers params, return type, body-level var declarations and
      block-scoped var statements; nested anonymous literals inside the
      body are deferred (consistent with the env-chaining deferral). }
    procedure SubstActiveTypeParamsInAnonDecl(ADecl: TMethodDecl);
    procedure SubstTypeParamsInStmt(AStmt: TASTStmt;
                                    ANames, AArgs: TStringList);
    procedure SubstTypeParamsInStmts(AStmts: TObjectList;
                                     ANames, AArgs: TStringList);
    { Phase 9a: fill an arrow lambda's untyped parameters and return type
      from a known target 'reference to' type, and desugar its single-
      expression body ('Result := E' for function targets, a call statement
      for procedure targets).  No-op for non-arrow literals or when the
      arrow was already inferred. }
    procedure InferArrowFromTarget(AExpr: TASTExpr; ATarget: TTypeDesc);
    { Phase 9b: argument-position lambda inference.  A '->' lambda argument
      is DEFERRED during the pre-resolution argument pass (it cannot be
      typed bottom-up), scored by SHAPE during overload resolution, and
      analysed after the winning candidate's parameter types are known. }
    function  IsPendingArrow(AExpr: TASTExpr): Boolean;
    procedure AnalyseArgOrDeferArrow(AExpr: TASTExpr);
    { AnalyseArgOrDeferArrow for an owned argument-list slot: rebinds the slot
      when the argument was a lowered overloaded operator. }
    procedure AnalyseArgSlot(AList: TObjectList; AIdx: Integer);
    procedure ResolveDeferredArrowArgs(AArgs: TObjectList; AMDecl: TMethodDecl);
    function  AnalyseAnonMethodExpr(AExpr: TAnonMethodExpr): TTypeDesc;
    procedure AnalyseVarDeclStmt(AStmt: TVarDeclStmt);
    procedure PromoteAnonCaptures(AThunk: TMethodDecl);
    procedure DrainPendingAnonDecls(ABlock: TBlock);
    procedure CoerceRoutineToClosure(AAssign: TAssignment);
    procedure ResolveProceduralTypeDef(ATD: TTypeDecl);
    function  AnalyseStringSubscriptExpr(AExpr: TStringSubscriptExpr): TTypeDesc;
    function  AnalyseArrayLiteralExpr(AExpr: TArrayLiteralExpr): TTypeDesc;
    function  AnalyseSetLiteralExpr(AExpr: TArrayLiteralExpr; ASetType: TSetTypeDesc): TTypeDesc;
    { Expand [lo..hi] range elements of a set literal into individual member
      idents (issue #105).  Constant ascending ranges only. }
    procedure ExpandSetRanges(AExpr: TArrayLiteralExpr; ABaseEnum: TEnumTypeDesc);
    procedure ExpandOrdinalSetRanges(AExpr: TArrayLiteralExpr; ASetType: TSetTypeDesc);
    function  SetRangeBoundOrdinal(ABound: TASTExpr; ABaseEnum: TEnumTypeDesc;
                                   const AWhich: string): Integer;
    { Width (in bits) needed for the anonymous set type of an 'X in [a,b,c]'
      literal: largest listed member ordinal + 1 when every element is a
      compile-time enum constant; otherwise the full base-enum member count
      (conservative).  Keeps low-ordinal membership tests off the jumbo path. }
    function  SetLiteralBitCount(AExpr: TArrayLiteralExpr;
                                 ABaseEnum: TEnumTypeDesc): Integer;
    procedure CoerceToCharOrd(ALit: TStringLiteral);
    procedure AnalysePointerWriteStmt(AStmt: TPointerWriteStmt);
    procedure AnalyseStaticSubscriptAssign(AStmt: TStaticSubscriptAssign);

    procedure AnalyseCompoundBody(ABody: TCompoundStmt);
    function  FindMethodDecl(const ATypeName, AMethodName: string): TMethodDecl;
    { Walks the class hierarchy from ATypeName upward and returns the name
      of the class that actually declares AMethodName.  Property accessors
      are mangled as <owner>_<method>; when a child inherits a property
      whose getter/setter lives in a parent, the call site must target the
      parent's symbol, not the child's (which never gets emitted). }
    function  PropAccessorOwner(const ATypeName, AMethodName: string): string;
    { Returns the vtable slot of property accessor AMethodName as seen from
      the static receiver type ATypeName, or -1 when the accessor is not
      virtual (a static call).  A virtual accessor must dispatch through the
      vtable so an overridden getter/setter is reached. }
    function  PropAccessorVSlot(const ATypeName, AMethodName: string): Integer;
    { Attribute helpers.  AttrMatches performs the Delphi-style suffix-drop
      lookup: [Weak] and [WeakAttribute] both resolve to the recognised
      attribute 'Weak'.  HasWeakAttribute scans an attribute list for
      any form of the Weak marker.  IsCustomAttributeClass walks the parent
      chain of a class to verify it descends from TCustomAttribute. }
    function  AttrMatches(const AAttrName, ACanonical: string): Boolean;
    function  HasWeakAttribute(AAttrs: TStringList): Boolean;
    function  HasUnretainedAttribute(AAttrs: TStringList): Boolean;
    function  IsCustomAttributeClass(const ATypeName: string): Boolean;
    procedure SynthesiseAttrThunk(AUse: TAttributeUse; const AThunkName: string);
    function  ResolveCustomAttrName(const ARawName: string): string;

    { Default-argument support.  MinArity returns the minimum number of
      arguments a call must supply: params before the first one carrying a
      DefaultValue.  TransferDefaultValues moves DefaultValue ownership from
      AFrom's params into AInto's matching params (used to forward defaults
      from an interface forward decl to its implementation).
      AnalyseDefaultValueExpr type-checks an already-attached default
      expression against the param's resolved type.
      CloneDefaultExprNode produces a fresh AST copy of a default-value
      literal/identifier so a call site can own its own argument node.
      AppendDefaultArgs fills a call's Args list from MDecl.Params for any
      missing trailing slots (Args.Count < Params.Count). }
    function  MinArity(ADecl: TMethodDecl): Integer;
    procedure TransferDefaultValues(AFrom, AInto: TMethodDecl);
    procedure AnalyseDefaultValueExpr(APar: TMethodParam;
      const AContext: string; ALine, ACol: Integer);
    function  CloneDefaultExprNode(ASrc: TASTExpr): TASTExpr;
    procedure AppendDefaultArgs(AArgs: TObjectList; ADecl: TMethodDecl;
      const AContext: string; ALine, ACol: Integer);

    procedure SemanticError(const AMsg: string; ALine, ACol: Integer);
    { Register a generic template on FTable, rejecting a same-named template
      already registered by a DIFFERENT unit (bare instance symbols would
      silently alias at link time — see TSymbolTable.RegisterGeneric). }
    procedure CheckedRegisterGeneric(ATD: TTypeDecl);
    { Emit a non-fatal diagnostic to StdErr (compilation continues).  Includes
      the source position and, when known, the current unit name — mirroring
      SemanticError's message shape. }
    procedure SemanticWarning(const AMsg: string; ALine, ACol: Integer);
    procedure CheckTypesMatch(AExpected, AActual: TTypeDesc;
      const AContext: string; ALine, ACol: Integer);
    { Returns True if AActual is AExpected or a subclass of AExpected. }
    function  IsSubtypeOf(AActual, AExpected: TTypeDesc): Boolean;
    function  InterfaceInheritsFrom(
      AActual, AExpected: TInterfaceTypeDesc): Boolean;
    { Validates a generic type parameter's constraint against a concrete type
      argument name.  Raises ESemanticError on constraint violation.
      AConstraint: '' (no constraint), 'class', 'record', or a type name. }
    procedure CheckTypeParamConstraint(const AParamName, AArgName, AConstraint,
      AContext: string);
  public
    constructor Create;
    destructor Destroy; override;
    procedure Analyse(AProg: TProgram);
    procedure AnalyseUnit(AUnit: TUnit);
    { Like AnalyseUnit but promotes interface-section symbols to the global
      scope so that subsequent Analyse(Prog) or AnalyseUnitForExport calls
      can resolve them.  Use this when compiling a unit as a dependency. }
    procedure AnalyseUnitForExport(AUnit: TUnit);
    { Read-only handle to the analyser's symbol table.  Codegen needs it
      in unit-as-top-level mode where no TProgram exists to hand it off.
      Also used by uSemanticExport.ExportUnitInterface to look up resolved
      types (e.g. for InstanceSize).  Non-owning — do not free. }
    function  GetSymbolTable: TSymbolTable;
    { Non-fatal diagnostics accumulated during analysis (see SemanticWarning).
      Each entry is also written to StdErr as it is raised.  Non-owning handle —
      do not free.  Used by tests to assert a warning was produced. }
    function  GetWarnings: TStringList;
    { Returns MangleUnitPrefix(FCurrentUnitName) when analysing a unit
      via AnalyseUnitForExport (FProg=nil), '' otherwise.  Used by
      ResolvedQbeName generation to prefix cross-unit symbol names. }
    function  CurrentUnitPrefix: string;
    { Push an imported free routine into FProcIndex (the call-site
      lookup table used by AnalyseFuncCall et al.).  Used by
      uSemanticImport when materialising symbols from a .bif —
      FTable.Define alone isn't enough because the call-site path
      goes through FProcIndex instead. }
    procedure RegisterImportedRoutine(const AName: string;
                                      ADecl: TMethodDecl);
    procedure RegisterImportedMethod(const ATypeName: string;
                                     ADecl: TMethodDecl);

    { Public entry to the on-demand type resolver used by the source
      compile path.  uSemanticImport calls this to resolve a cached
      iface's type-name string (e.g. a field type 'TList<TFoo>' or an
      'array of TFoo') that is not a plain registered symbol — the
      import path otherwise has no way to instantiate generics, so a
      generic-instance field type from a .bif fails to resolve.  Mirrors
      what AnalyseUnitForExport does for the same field in source form. }
    function  ResolveImportedTypeName(const AName: string): TTypeDesc;

    { Register a TUnitInterface in FUnitIfaces, keyed by AIface.Name.
      AIface is NOT owned — caller (Blaise.pas) retains lifetime.
      Subsequent registrations of the same name replace the entry
      (last-wins, paralleling "uses-chain last-wins").  Task #44 step 3. }
    procedure RegisterUnitIface(AIface: TUnitInterface);

    { Register a per-unit symbol mapping in FUnitSymbols.  ASym is
      NOT owned — its lifetime is managed by FTable (or whatever
      owner the caller designates).  Called by uSemanticImport
      alongside the existing Define when an iface symbol is
      materialised, and by the source-side Define wrapper for the
      unit being analysed.  Task #44 step 9. }
    procedure RegisterUnitSymbol(const AUnitName: string; ASym: TSymbol);

    { Look up a per-unit symbol by (AUnitName, ASymName).  Returns
      nil when not registered.  Used by LookupViaUsesChain to walk
      the chain without going through the flat global. }
    function FindUnitSymbol(const AUnitName, ASymName: string): TSymbol;

    { Directed lookup — "look in unit AUnit for the symbol AName".
      This is THE single entry point for every unit-qualified reference
      'Unit.Symbol' (idents, type names, statement targets): a unit
      prefix means resolve against that specific unit's exports, never
      the flat table or the uses chain.  Returns the symbol AUnit
      exports under AName (of any kind — const/var/type/routine), or nil
      when AUnit exports no such name.  Consults the per-unit cache
      first, then the unit's interface as a fallback for symbols not yet
      harvested into the cache. }
    function ResolveQualified(const AUnit, AName: string): TSymbol;

    { Define a module-scope global (interface var) with cross-unit
      last-in-uses-wins semantics, mirroring AnalyseConstDecls.  On a
      clean Define the symbol is registered in the per-unit cache; on a
      cross-unit collision the prior unit's symbol is detached (kept alive
      in the per-unit cache so a qualified Unit.Var reference still reaches
      it) and this unit's symbol is installed as the flat winner.  Same-unit
      redeclaration and module-name markers stay hard errors. }
    procedure DefineGlobalLastWins(ASym: TSymbol; ALine, ACol: Integer);

    { Define a type name with the same cross-unit last-found-wins rule as
      DefineGlobalLastWins: a collision against a type owned by a DIFFERENT
      used unit detaches the prior type (kept in the per-unit cache so a
      qualified Unit.Type reference still reaches it) and installs this unit's
      type as the flat winner; a same-unit redeclaration or a non-unit/module
      collision stays the hard 'Duplicate type name' error. }
    procedure DefineTypeLastWins(ASym: TSymbol; ATypeDecl: TTypeDecl;
                                 ALine, ACol: Integer);

    { Record one enum member in the reverse index (FEnumMemberIndex).
      Called once per member as its enum type is analysed.  Enum members
      are NOT registered as bare global symbols any more — a bare member
      name resolves through ResolveEnumMember instead. }
    procedure RegisterEnumMember(const AName: string;
                                 AEnum: TEnumTypeDesc; AOrdinal: Int64);

    { Resolve a bare enum member name to (enum type, ordinal).  Cascade:
      AExpectedType (an enum, or set-of-enum) names the enum -> that one;
      else a single candidate -> that one; else the latest-declared
      candidate (last-wins).  Returns nil when no enum has the member.
      AExpectedType may be nil (no context, e.g. Ord/const-fold). }
    function ResolveEnumMember(const AName: string;
                               AExpectedType: TTypeDesc): TEnumMemberRef;

    { Context-directed resolution of a bare enum-member identifier.  If AExpr
      is an unresolved TIdentExpr that is not a normal symbol and names a
      member of (or compatible with) AExpectedType, mark it constant in place
      and return True; the caller then reads AExpr.ResolvedType and must NOT
      call AnalyseExpr on it again.  Returns False for anything else, leaving
      AExpr untouched for the normal expression path. }
    function TryResolveBareEnumIdent(AExpr: TASTExpr;
                                     AExpectedType: TTypeDesc): Boolean;

    { Analyse AExpr, first giving a bare enum-member identifier the chance to
      resolve against AExpectedType (the known target/element/parameter type).
      Returns the expression's resolved type.  Use this anywhere an expression
      is analysed into a context whose enum type is already known. }
    function AnalyseExprHinted(AExpr: TASTExpr;
                              AExpectedType: TTypeDesc): TTypeDesc;

    { How many enums declare a member of this name.  >1 means a bare,
      context-free reference is ambiguous and must be qualified. }
    function EnumMemberCandidateCount(const AName: string): Integer;

    { Comma-separated names of every enum that declares a member AName, in
      declaration order — used to spell out an ambiguity in diagnostics. }
    function EnumMemberOwners(const AName: string): string;

    { Enum hint for a bare member passed as call argument APos to a routine
      named AName with AArity actuals.  Walks the overload candidates and,
      among those whose parameter at APos is an enum (or set-of-enum) that
      actually declares AMember, returns that enum when exactly one distinct
      enum qualifies — so a bare shared member is steered to the only enum the
      call could accept.  Returns nil when zero or several enums qualify (the
      arg then falls to the context-free last-wins path). }
    { The enum a single parameter would accept for a bare member: the param's
      enum (or set-of-enum base) when it declares AMember and the decl can take
      AArity actuals; nil otherwise. }
    function EnumOfParamAccepting(ADecl: TMethodDecl; AArity, APos: Integer;
                                 const AMember: string): TTypeDesc;
    function EnumArgHint(const AName: string; AArity, APos: Integer;
                         const AMember: string): TTypeDesc;
    { Like EnumArgHint but walks the method overload set up the inheritance
      chain of ATypeName (mirrors ResolveMethodOverload's candidate walk). }
    function EnumMethodArgHint(const ATypeName, AMethodName: string;
                               AArity, APos: Integer;
                               const AMember: string): TTypeDesc;
    { True if AArg is a bare identifier that names an enum member and is not a
      real symbol — i.e. a candidate for context-directed enum resolution. }
    function BareEnumArgCandidate(AArg: TASTExpr): Boolean;

    { Pre-pass over a call's actuals: pin any bare, context-free enum-member
      argument to the enum its target routine expects at that position, before
      the args are analysed bottom-up.  Lets Foo(meVal) reach the meVal of
      Foo's parameter enum even when meVal is shared by several enums, and
      keeps the no-warning path for an otherwise-ambiguous bare member. }
    procedure HintBareEnumArgs(const AName: string; AArgs: TObjectList);
    { As HintBareEnumArgs, for a method call on a receiver of type ATypeName. }
    procedure HintBareEnumMethodArgs(const ATypeName, AMethodName: string;
                                     AArgs: TObjectList);

    { Reserve a module name in the current scope (issue #84).  Defines
      an skModule marker so any same-scope declaration of that name
      fails the normal duplicate check, matching FPC/Delphi.  A failed
      Define (name already taken — e.g. a unit listed twice in uses)
      is silently ignored. }
    procedure DefineModuleName(const AName: string);

    { Look up a registered TUnitInterface by unit name.  Returns nil
      if not registered.  Case-insensitive. }
    function FindUnitIface(const AUnitName: string): TUnitInterface;

    { Visibility filter — single chokepoint for both unqualified
      uses-chain lookup and qualified class-member access.  Task #44
      step 4.

      AFromUnit  — name of the unit currently being analysed
                   (FCurrentUnitName).  Used by future private (Pascal
                   "unit is the privacy boundary") logic.
      AFromClass — the class whose method body the lookup is happening
                   inside, or nil for free-routine / unit-level code.
                   Used by future protected logic to walk ParentClass
                   up to ASym's declaring class.

      Stub returns True unconditionally — private/protected modifiers
      don't exist on Blaise class members yet.  When they land, this
      seam plugs in without changing call sites.

      Critical correctness note (see project_per_unit_visibility.md):
        - For *unqualified* lookups, False means skip-and-keep-walking
          the uses chain — "wasn't this unit's Foo".
        - For *qualified* member access (obj.Foo), False is a hard
          error at the resolution site — "Foo is not accessible from
          here", NOT a fall-through. }
    function IsVisibleFromUnit(ASym: TSymbol;
                               const AFromUnit: string;
                               AFromClass: TRecordTypeDesc): Boolean; overload;

    { String-flavor overload — at member-access sites we typically
      have an owning-unit string but no TSymbol (e.g. a TMethodDecl /
      TFieldInfo).  Same semantics as the TSymbol form.  Task #44
      step 6. }
    function IsVisibleFromUnit(const AMemberOwningUnit: string;
                               const AFromUnit: string;
                               AFromClass: TRecordTypeDesc): Boolean; overload;

    { Hard-error wrapper for qualified member access (`obj.Foo` /
      `Self.Foo` / `TypeName.Foo`).  Calls IsVisibleFromUnit; on
      False raises ESemanticError with a "not accessible" message
      at AMemberName's source location.  This is the rule from
      project_per_unit_visibility.md: an invisible *qualified*
      member is a hard error, never a fall-through.

      Today the filter returns True so this never raises; the seam
      is in place for when class members gain private/protected
      modifiers and a per-member OwningUnit. }
    procedure AssertMemberVisible(const AMemberOwningUnit: string;
                                  AClassContext: TRecordTypeDesc;
                                  const AMemberName: string;
                                  ALine, ACol: Integer);

    { Core visibility predicate.  Single source of truth applied by both
      the unqualified uses-chain probe and the qualified member-access
      asserts.  ADeclaringUnit / ADeclaringType identify where the member
      was declared; AFromClass is the class whose method body we are in
      (or nil at unit/free-routine level). }
    function MemberVisibleTo(AVisibility: TMemberVisibility;
                             const ADeclaringUnit, ADeclaringType: string;
                             const AFromUnit: string;
                             AFromClass: TRecordTypeDesc): Boolean;

    { Richer qualified-access assert that carries the member's visibility
      and declaring type.  On invisible, hard error. }
    procedure AssertMemberVisibleV(AVisibility: TMemberVisibility;
                                   const ADeclaringUnit, ADeclaringType: string;
                                   const AMemberName: string;
                                   ALine, ACol: Integer);

    { Visibility enforcement for a STATIC (class-level) variable access.  Like
      AssertMemberVisibleV but treats the current method's declaring type as the
      "from" class even inside a static method (FCurrentClass is nil there), so a
      strict-private static var stays reachable from its own type's static
      methods. }
    procedure AssertStaticVarVisible(AVisibility: TMemberVisibility;
                                     const ADeclaringUnit, ADeclaringType: string;
                                     const AMemberName: string;
                                     ALine, ACol: Integer);

    { Qualified instance/class method-call visibility enforcement.  AMDecl is
      the resolved TMethodDecl (via ResolveMethodOverload or FindMethodDecl);
      reads its Visibility / OwningUnit / OwnerTypeName.  No-op when AMDecl is
      nil.  Constructors are exempt (always reachable for instantiation). }
    procedure EnforceMethodVisible(AMDecl: TObject; ALine, ACol: Integer);

    { Uses-chain lookup for *unqualified* identifiers.  Walks
      FCurrentUsesChain right-to-left ("last in uses wins"); for
      each chain entry whose TUnitInterface advertises AName via
      HasSymbol, retrieves the canonical TSymbol from FTable and
      applies IsVisibleFromUnit (with FCurrentClass for the class
      context).  Returns the first visible hit, or nil.

      Today the flat FTable holds only one TSymbol per name (no
      conflicts are possible — semantics already error on name
      duplicates), so this acts as an order-preserving probe that
      will become load-bearing only once step 9 removes the flat
      merge.  Until then it's plumbing.  Task #44 step 5.

      Overrides TUsesChainProvider so TSymbolTable.Lookup can call
      us back through the abstract base (step 7). }
    function LookupViaUsesChain(const AName: string): TSymbol; override;
  end;

implementation

{ Float<->string conversion uses the RTL's pure-Pascal _DoubleToStr / _StrToDouble,
  NOT libc's snprintf / strtod.  snprintf is a genuinely variadic function;
  declaring it with a fixed Double parameter violates the SysV x86-64 variadic ABI
  (the %al vector-register count is left unset), so glibc may read the double from
  the wrong place and emit a wrong string (environment-dependent miscompilation of
  folded float constants — passes locally, fails in CI).  Routing both directions
  through the RTL also drops the last libc dependency in this path, so a --static
  (libc-free) build of the compiler links without strtod. }
function _StrToDouble(S: Pointer): Double; external name '_StrToDouble';
function _DoubleToStr(V: Double): string; external name '_DoubleToStr';

function RawDoubleToStr(V: Double): string;
begin
  Result := _DoubleToStr(V);
end;

function RawStrToDouble(const S: string): Double;
begin
  Result := _StrToDouble(PChar(S));
end;

function TSemanticAnalyser.GetSymbolTable: TSymbolTable;
begin
  Result := FTable;
end;

constructor TSemanticAnalyser.Create;
begin
  inherited Create();
  FTable                := TSymbolTable.Create();
  FMethodIndex          := TStringList.Create();
  FMethodIndex.CaseSensitive := False;
  FProcIndex            := TStringList.Create();
  FProcIndex.CaseSensitive := False;
  FProcGroups           := TStringList.Create();
  FProcGroups.CaseSensitive := False;
  FMethodGroups         := TStringList.Create();
  FMethodGroups.CaseSensitive := False;
  FGroupKeepAlive       := TObjectList.Create(False);
  FEnumMemberIndex      := TStringList.Create();
  FEnumMemberIndex.CaseSensitive := False;
  FEnumMemberIndex.Duplicates    := dupAccept;
  FEnumMemberRefs       := TObjectList.Create(True);  { owns the holders }
  FEnumOrderCounter     := 0;
  FGenericFuncTemplates := TStringList.Create();
  FGenericFuncTemplates.CaseSensitive := False;
  FGenericMethodTemplates := TStringList.Create();
  FGenericMethodTemplates.CaseSensitive := False;
  FCurrentUsesChain     := TStringList.Create();
  FCurrentUsesChain.CaseSensitive := False;
  FUnitIfaces           := TStringList.Create();
  FUnitIfaces.CaseSensitive := False;
  FUnitSymbols          := TStringList.Create();
  FUnitSymbols.CaseSensitive := False;
  FActiveTypeParams     := TStringList.Create();
  FActiveTypeParams.CaseSensitive := False;
  FForInLoopVars        := TStringList.Create();
  FForInLoopVars.CaseSensitive := False;
  FWarnings             := TStringList.Create();
  FPendingGenericInstances       := TObjectList.Create(False);
  FPendingGenericRecordInstances := TObjectList.Create(False);
  FPendingGenericIntfInstances   := TObjectList.Create(False);
  FPendingAnonDecls     := TObjectList.Create(False);
  FAnonMethodCount      := 0;
  FEnvTypeCount         := 0;
  FLoopDepth            := 0;
end;

destructor TSemanticAnalyser.Destroy;
begin
  FPendingGenericIntfInstances.Free();
  FPendingGenericRecordInstances.Free();
  FPendingGenericInstances.Free();
  FActiveTypeParams.Free();
  FForInLoopVars.Free();
  FWarnings.Free();
  FUnitSymbols.Free();
  FUnitIfaces.Free();
  FCurrentUsesChain.Free();
  FGenericFuncTemplates.Free();
  FGenericMethodTemplates.Free();
  { Releasing the keep-alive releases every group list; the group string
    lists themselves only hold raw pointers. }
  FGroupKeepAlive.Free();
  FEnumMemberRefs.Free();    { frees the holders }
  FEnumMemberIndex.Free();
  FProcGroups.Free();
  FMethodGroups.Free();
  FProcIndex.Free();
  FMethodIndex.Free();
  FTable.Free();
  inherited Destroy();
end;

procedure TSemanticAnalyser.SemanticError(const AMsg: string; ALine, ACol: Integer);
begin
  if FCurrentUnitName <> '' then
    raise ESemanticError.Create(Format('%s at line %d col %d in %s', [AMsg, ALine, ACol, FCurrentUnitName]))
  else
    raise ESemanticError.Create(Format('%s at line %d col %d', [AMsg, ALine, ACol]));
end;

procedure TSemanticAnalyser.CheckedRegisterGeneric(ATD: TTypeDecl);
var
  CurUnit, PrevUnit: string;
begin
  if FCurrentUnitName <> '' then
    CurUnit := FCurrentUnitName
  else
    CurUnit := '<program>';
  PrevUnit := FTable.RegisterGeneric(ATD.Name, ATD.Def, CurUnit);
  if PrevUnit <> '' then
    SemanticError(GenericCollisionMsg('Generic type', ATD.Name, PrevUnit, CurUnit),
      ATD.Line, ATD.Col);
end;

procedure TSemanticAnalyser.SemanticWarning(const AMsg: string; ALine, ACol: Integer);
var
  Full: string;
begin
  if FCurrentUnitName <> '' then
    Full := Format('Warning: %s at line %d col %d in %s',
      [AMsg, ALine, ACol, FCurrentUnitName])
  else
    Full := Format('Warning: %s at line %d col %d', [AMsg, ALine, ACol]);
  FWarnings.Add(Full);
  WriteLn(StdErr, Full);
end;

function TSemanticAnalyser.GetWarnings: TStringList;
begin
  Result := FWarnings;
end;

procedure TSemanticAnalyser.RegisterEnumMember(const AName: string;
                                               AEnum: TEnumTypeDesc; AOrdinal: Int64);
var
  Ref: TEnumMemberRef;
begin
  Ref          := TEnumMemberRef.Create();
  Ref.EnumDesc := AEnum;
  Ref.Ordinal  := AOrdinal;
  Inc(FEnumOrderCounter);
  Ref.Order    := FEnumOrderCounter;
  FEnumMemberRefs.Add(Ref);                  { owns Ref }
  FEnumMemberIndex.AddObject(AName, Ref);    { non-owning view, dupAccept }
end;

function TSemanticAnalyser.ResolveEnumMember(const AName: string;
                                             AExpectedType: TTypeDesc): TEnumMemberRef;
var
  I:        Integer;
  Ref:      TEnumMemberRef;
  Best:     TEnumMemberRef;
  Count:    Integer;
  WantEnum: TEnumTypeDesc;
begin
  Result := nil;
  { An expected set-of-enum context narrows to its element enum. }
  WantEnum := nil;
  if AExpectedType <> nil then
  begin
    if AExpectedType is TEnumTypeDesc then
      WantEnum := TEnumTypeDesc(AExpectedType)
    else if (AExpectedType is TSetTypeDesc) and
            (TSetTypeDesc(AExpectedType).BaseType is TEnumTypeDesc) then
      WantEnum := TEnumTypeDesc(TSetTypeDesc(AExpectedType).BaseType);
  end;

  Best  := nil;
  Count := 0;
  for I := 0 to FEnumMemberIndex.Count - 1 do
  begin
    if not SameText(FEnumMemberIndex.Strings[I], AName) then Continue;
    Ref := TEnumMemberRef(FEnumMemberIndex.Objects[I]);
    { Context hit: an enum the caller asked for wins outright. }
    if (WantEnum <> nil) and (Ref.EnumDesc = WantEnum) then
      Exit(Ref);
    Inc(Count);
    { Track the latest-declared candidate for the context-free fallback. }
    if (Best = nil) or (Ref.Order > Best.Order) then
      Best := Ref;
  end;

  if Count = 0 then Exit(nil);   { no enum has this member }
  { One candidate -> unambiguous; many -> last-declared wins. }
  Result := Best;
end;

function TSemanticAnalyser.TryResolveBareEnumIdent(AExpr: TASTExpr;
                                                   AExpectedType: TTypeDesc): Boolean;
var
  Ref: TEnumMemberRef;
begin
  Result := False;
  if not (AExpr is TIdentExpr) then Exit;
  { Already resolved (e.g. a set range expanded into constant members). }
  if TIdentExpr(AExpr).IsConstant then Exit;
  { A real symbol of that name always wins — do not shadow it with an enum. }
  if FTable.Lookup(TIdentExpr(AExpr).Name) <> nil then Exit;
  Ref := ResolveEnumMember(TIdentExpr(AExpr).Name, AExpectedType);
  if Ref = nil then Exit;
  TIdentExpr(AExpr).IsConstant   := True;
  TIdentExpr(AExpr).ConstValue   := Ref.Ordinal;
  TIdentExpr(AExpr).ResolvedType := Ref.EnumDesc;
  AExpr.ResolvedType             := Ref.EnumDesc;
  Result := True;
end;

function TSemanticAnalyser.AnalyseExprHinted(AExpr: TASTExpr;
                                            AExpectedType: TTypeDesc): TTypeDesc;
begin
  { A bracket set literal ([] or [a, b]) has no set type of its own — it must
    take one from the assignment target.  The plain-variable and qualified-field
    assignment paths already pass the LHS set type to AnalyseSetLiteralExpr; the
    array-element / pointer-write paths route through this hinted helper, so
    supply the same treatment here so `Arr[I] := [a, b]` (and dynamic / multi-
    dim / implicit-Self / open-array element writes, and PtrToSet^ := [..]) type
    against the expected set.  BUG-20260720-set-array-elem-dest. }
  if (AExpectedType <> nil) and (AExpectedType.Kind = tySet) and
     (AExpr is TArrayLiteralExpr) then
    Result := AnalyseSetLiteralExpr(TArrayLiteralExpr(AExpr),
                TSetTypeDesc(AExpectedType))
  else if TryResolveBareEnumIdent(AExpr, AExpectedType) then
    Result := AExpr.ResolvedType
  else
    Result := AnalyseExpr(AExpr);
end;

function TSemanticAnalyser.EnumMemberCandidateCount(const AName: string): Integer;
var
  I: Integer;
begin
  Result := 0;
  for I := 0 to FEnumMemberIndex.Count - 1 do
    if SameText(FEnumMemberIndex.Strings[I], AName) then
      Inc(Result);
end;

function TSemanticAnalyser.EnumMemberOwners(const AName: string): string;
var
  I:   Integer;
  Ref: TEnumMemberRef;
begin
  Result := '';
  for I := 0 to FEnumMemberIndex.Count - 1 do
    if SameText(FEnumMemberIndex.Strings[I], AName) then
    begin
      Ref := TEnumMemberRef(FEnumMemberIndex.Objects[I]);
      if Result <> '' then
        Result := Result + ', ';
      Result := Result + Ref.EnumDesc.Name;
    end;
end;

function TSemanticAnalyser.EnumOfParamAccepting(ADecl: TMethodDecl;
  AArity, APos: Integer; const AMember: string): TTypeDesc;
var
  Par:  TMethodParam;
  PT:   TTypeDesc;
  Enum: TEnumTypeDesc;
  M:    Integer;
begin
  Result := nil;
  if (ADecl = nil) or (APos < 0) or (APos >= ADecl.Params.Count) then Exit;
  { An overload that cannot take this many actuals is not a candidate. }
  if ADecl.Params.Count < AArity then Exit;
  Par := TMethodParam(ADecl.Params.Items[APos]);
  PT  := Par.ResolvedType;
  if PT = nil then Exit;
  if PT is TEnumTypeDesc then
    Enum := TEnumTypeDesc(PT)
  else if (PT is TSetTypeDesc) and
          (TSetTypeDesc(PT).BaseType is TEnumTypeDesc) then
    Enum := TEnumTypeDesc(TSetTypeDesc(PT).BaseType)
  else
    Exit;
  { Only an enum that actually declares the bare member can accept it. }
  for M := 0 to Enum.Members.Count - 1 do
    if SameText(Enum.Members.Strings[M], AMember) then
      Exit(Enum);
end;

function TSemanticAnalyser.EnumArgHint(const AName: string;
  AArity, APos: Integer; const AMember: string): TTypeDesc;
var
  I:     Integer;
  Enum:  TTypeDesc;
  Found: TTypeDesc;
begin
  Result := nil;
  Found  := nil;
  for I := 0 to FProcIndex.Count - 1 do
  begin
    if not SameText(FProcIndex.Strings[I], AName) then Continue;
    Enum := EnumOfParamAccepting(TMethodDecl(FProcIndex.Objects[I]),
      AArity, APos, AMember);
    if Enum = nil then Continue;
    if Found = nil then
      Found := Enum
    else if Found <> Enum then
      Exit(nil);   { several enums could accept it — not a unique hint }
  end;
  Result := Found;
end;

function TSemanticAnalyser.EnumMethodArgHint(const ATypeName, AMethodName: string;
  AArity, APos: Integer; const AMember: string): TTypeDesc;
var
  CurrName: string;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
  Grp:      TObjectList;
  K:        Integer;
  Cand:     TMethodDecl;
  Enum:     TTypeDesc;
  Found:    TTypeDesc;
  SawHiding: Boolean;
begin
  Result   := nil;
  Found    := nil;
  CurrName := ATypeName;
  { Walk the inheritance chain exactly as ResolveMethodOverload does: a
    non-`overload` method at a level hides inherited same-named methods. }
  while CurrName <> '' do
  begin
    Grp := GroupOf(FMethodGroups, CurrName + '.' + AMethodName);
    SawHiding := False;
    if Grp <> nil then
      for K := 0 to Grp.Count - 1 do
      begin
        Cand := TMethodDecl(Grp.Items[K]);
        if not Cand.IsOverload then SawHiding := True;
        Enum := EnumOfParamAccepting(Cand, AArity, APos, AMember);
        if Enum <> nil then
        begin
          if Found = nil then
            Found := Enum
          else if Found <> Enum then
            Exit(nil);
        end;
      end;
    if SawHiding then Break;
    Sym := FTable.Lookup(CurrName);
    if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
    begin
      RT := TRecordTypeDesc(Sym.TypeDesc);
      if RT.Parent <> nil then CurrName := RT.Parent.Name else Break;
    end
    else
      Break;
  end;
  Result := Found;
end;

function TSemanticAnalyser.BareEnumArgCandidate(AArg: TASTExpr): Boolean;
begin
  Result := False;
  if not (AArg is TIdentExpr) then Exit;
  if TIdentExpr(AArg).IsConstant then Exit;
  { A real symbol of that name always wins. }
  if FTable.Lookup(TIdentExpr(AArg).Name) <> nil then Exit;
  { Only worth steering when the name is a known enum member. }
  Result := EnumMemberCandidateCount(TIdentExpr(AArg).Name) > 0;
end;

procedure TSemanticAnalyser.HintBareEnumArgs(const AName: string;
  AArgs: TObjectList);
var
  I:    Integer;
  Arg:  TASTExpr;
  Hint: TTypeDesc;
begin
  if AArgs = nil then Exit;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if not BareEnumArgCandidate(Arg) then Continue;
    Hint := EnumArgHint(AName, AArgs.Count, I, TIdentExpr(Arg).Name);
    if Hint <> nil then
      TryResolveBareEnumIdent(Arg, Hint);
  end;
end;

procedure TSemanticAnalyser.HintBareEnumMethodArgs(const ATypeName,
  AMethodName: string; AArgs: TObjectList);
var
  I:    Integer;
  Arg:  TASTExpr;
  Hint: TTypeDesc;
begin
  if AArgs = nil then Exit;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if not BareEnumArgCandidate(Arg) then Continue;
    Hint := EnumMethodArgHint(ATypeName, AMethodName, AArgs.Count, I,
      TIdentExpr(Arg).Name);
    if Hint <> nil then
      TryResolveBareEnumIdent(Arg, Hint);
  end;
end;

function TSemanticAnalyser.AttrMatches(const AAttrName, ACanonical: string): Boolean;
{ An attribute name matches a canonical form if it equals the canonical
  name case-insensitively, or if it equals <canonical>Attribute (the
  Delphi suffix convention).  This lets [Weak] and [WeakAttribute]
  resolve to the same compiler-recognised attribute. }
var
  Suffix: string;
begin
  if SameText(AAttrName, ACanonical) then
  begin
    Exit(True);
  end;
  Suffix := ACanonical + 'Attribute';
  Result := SameText(AAttrName, Suffix);
end;

function TSemanticAnalyser.HasWeakAttribute(AAttrs: TStringList): Boolean;
var
  I: Integer;
begin
  if AAttrs = nil then
  begin
    Exit(False);
  end;
  for I := 0 to AAttrs.Count - 1 do
    if AttrMatches(AAttrs.Strings[I], 'Weak') then
    begin
      Exit(True);
    end;
  Result := False;
end;

function TSemanticAnalyser.HasUnretainedAttribute(AAttrs: TStringList): Boolean;
var
  I: Integer;
begin
  if AAttrs = nil then
  begin
    Exit(False);
  end;
  for I := 0 to AAttrs.Count - 1 do
    if AttrMatches(AAttrs.Strings[I], 'Unretained') then
    begin
      Exit(True);
    end;
  Result := False;
end;

function TSemanticAnalyser.IsCustomAttributeClass(const ATypeName: string): Boolean;
var
  Sym:  TSymbol;
  RT:   TRecordTypeDesc;
  Walk: TRecordTypeDesc;
begin
  Result := False;
  Sym := FTable.Lookup(ATypeName);
  if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then Exit;
  RT := TRecordTypeDesc(Sym.TypeDesc);
  if RT.Kind <> tyClass then Exit;
  Walk := RT;
  while Walk <> nil do
  begin
    if SameText(Walk.Name, 'TCustomAttribute') then
    begin
      Exit(True);
    end;
    Walk := Walk.Parent;
  end;
end;

function TSemanticAnalyser.ResolveCustomAttrName(const ARawName: string): string;
{ Apply Delphi suffix convention: try 'Name' then 'NameAttribute'. Returns the
  resolved class name that descends from TCustomAttribute, or '' if not found. }
var
  Sym: TSymbol;
begin
  Result := '';
  Sym := FTable.Lookup(ARawName);
  if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) and
     IsCustomAttributeClass(ARawName) then
  begin
    Exit(ARawName);
  end;
  Sym := FTable.Lookup(ARawName + 'Attribute');
  if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) and
     IsCustomAttributeClass(ARawName + 'Attribute') then
    Result := ARawName + 'Attribute';
end;

procedure TSemanticAnalyser.SynthesiseAttrThunk(AUse: TAttributeUse;
  const AThunkName: string);
{ Synthesise the parameterless factory function ('thunk') for one resolved
  attribute application:

    function <AThunkName>: TObject;
    begin
      Result := <ResolvedClassName>.Create(<attribute args>);
    end;

  and append it to the enclosing module's standalone-proc list — the program
  block, or the unit's IMPLEMENTATION block (impl-only: thunks are private
  emission artefacts referenced from the typeinfo attrs tables, never
  exported through the BIF).  AnalyseStandaloneDecls runs after
  AnalyseTypeDecls in both the program and unit flows, so the thunk is
  registered, type-checked (constructor overload resolution validates the
  attribute arguments, with errors pointing at the attribute's source
  position) and emitted by both backends like any ordinary function.
  Idempotent via AUse.ThunkDecl. }
var
  Sink: TBlock;
  MD:   TMethodDecl;
  Asn:  TAssignment;
  Call: TMethodCallExpr;
  I:    Integer;
begin
  if AUse.ThunkDecl <> nil then Exit;
  if FCurrentUnit <> nil then
    Sink := FCurrentUnit.ImplBlock
  else if FProg <> nil then
    Sink := FProg.Block
  else
    Exit;
  Call := TMethodCallExpr.Create();
  Call.Line       := AUse.Line;
  Call.Col        := AUse.Col;
  Call.ObjectName := AUse.ResolvedClassName;
  Call.Name       := 'Create';
  for I := 0 to AUse.Args.Count - 1 do
    Call.Args.Add(CloneExpr(TASTExpr(AUse.Args.Items[I])));
  Asn := TAssignment.Create();
  Asn.Line := AUse.Line;
  Asn.Col  := AUse.Col;
  Asn.Name := 'Result';
  Asn.Expr := Call;
  MD := TMethodDecl.Create();
  MD.Line           := AUse.Line;
  MD.Col            := AUse.Col;
  MD.Name           := AThunkName;
  MD.ReturnTypeName := 'TObject';
  MD.IsImplOnly     := FCurrentUnit <> nil;
  MD.Body           := TBlock.Create();
  MD.Body.Stmts.Add(Asn);
  Sink.ProcDecls.Add(MD);
  AUse.ThunkDecl := MD;
end;

procedure TSemanticAnalyser.CheckTypeParamConstraint(
  const AParamName, AArgName, AConstraint, AContext: string);
var
  ArgType:     TTypeDesc;
  ConstrType:  TTypeDesc;
  RT:          TRecordTypeDesc;
  I:           Integer;
  Implements:  Boolean;
begin
  if AConstraint = '' then Exit;

  ArgType := FTable.FindType(AArgName);
  if ArgType = nil then
    raise ESemanticError.Create(Format(
      'Unknown type ''%s'' for type parameter ''%s'' in %s',
      [AArgName, AParamName, AContext]));

  if SameText(AConstraint, 'class') then
  begin
    if ArgType.Kind <> tyClass then
      raise ESemanticError.Create(Format(
        'Type ''%s'' does not satisfy constraint ''%s: class'' in %s',
        [AArgName, AParamName, AContext]));
    Exit;
  end;

  if SameText(AConstraint, 'record') then
  begin
    if not (ArgType.Kind in [tyRecord, tyInteger, tyInt64, tyUInt32, tyUInt64,
                             tySmallInt, tyWord, tyByte, tyBoolean, tyString,
                             tyPointer]) then
      raise ESemanticError.Create(Format(
        'Type ''%s'' does not satisfy constraint ''%s: record'' in %s',
        [AArgName, AParamName, AContext]));
    Exit;
  end;

  { Named constraint: T : SomeType.  Concrete type must BE that type or —
    for classes/interfaces — inherit from / implement it. }
  ConstrType := FTable.FindType(AConstraint);
  if ConstrType = nil then
    raise ESemanticError.Create(Format(
      'Unknown constraint type ''%s'' for type parameter ''%s'' in %s',
      [AConstraint, AParamName, AContext]));

  if ArgType = ConstrType then Exit;

  if (ConstrType.Kind = tyClass) and (ArgType.Kind = tyClass) then
  begin
    if IsSubtypeOf(ArgType, ConstrType) then Exit;
    raise ESemanticError.Create(Format(
      'Type ''%s'' does not inherit from ''%s'' (constraint ''%s: %s'') in %s',
      [AArgName, AConstraint, AParamName, AConstraint, AContext]));
  end;

  if (ConstrType.Kind = tyInterface) and (ArgType.Kind = tyClass) then
  begin
    RT := TRecordTypeDesc(ArgType);
    Implements := False;
    for I := 0 to RT.ImplementsCount() - 1 do
      if RT.ImplementsIntfAt(I) = ConstrType then
      begin
        Implements := True;
        Break;
      end;
    if not Implements then
      raise ESemanticError.Create(Format(
        'Type ''%s'' does not implement ''%s'' (constraint ''%s: %s'') in %s',
        [AArgName, AConstraint, AParamName, AConstraint, AContext]));
    Exit;
  end;

  raise ESemanticError.Create(Format(
    'Type ''%s'' does not satisfy constraint ''%s: %s'' in %s',
    [AArgName, AParamName, AConstraint, AContext]));
end;

function TSemanticAnalyser.IsSubtypeOf(AActual, AExpected: TTypeDesc): Boolean;
var
  Walk: TRecordTypeDesc;
begin
  Result := AActual = AExpected;
  if Result then Exit;
  if (AActual = nil) or (AExpected = nil) then Exit;
  if (AActual.Kind <> tyClass) or (AExpected.Kind <> tyClass) then Exit;
  Walk := TRecordTypeDesc(AActual).Parent;
  while Walk <> nil do
  begin
    if Walk = AExpected then
    begin
      Exit(True);
    end;
    Walk := Walk.Parent;
  end;
end;

function TSemanticAnalyser.InterfaceInheritsFrom(
  AActual, AExpected: TInterfaceTypeDesc): Boolean;
{ True when AActual is, or transitively inherits from, AExpected — i.e. an
  AActual value is assignable where AExpected is required.  Walks the
  TInterfaceTypeDesc.Parent chain (IDog = interface(IAnimal) -> Parent). }
var
  Walk: TInterfaceTypeDesc;
begin
  Walk := AActual;
  while Walk <> nil do
  begin
    if Walk = AExpected then Exit(True);
    Walk := Walk.Parent;
  end;
  Result := False;
end;

procedure TSemanticAnalyser.CheckTypesMatch(AExpected, AActual: TTypeDesc;
  const AContext: string; ALine, ACol: Integer);
var
  RT:   TRecordTypeDesc;
  Walk: TRecordTypeDesc;
  I:    Integer;
begin
  if AExpected = AActual then
    Exit;
  { A nil actual type means the right-hand expression could not be typed —
    e.g. a bare empty set literal '[]' used outside a set context.  Report it
    rather than dereferencing nil (segfault). }
  if AActual = nil then
    SemanticError(Format('Expression has no value type in %s', [AContext]),
      ALine, ACol);
  if AExpected = nil then
    Exit;
  { nil is compatible with any class, interface, pointer, PChar, or string type }
  if (AActual.Kind = tyNil) and (AExpected.Kind in [tyClass, tyInterface, tyPointer, tyPChar, tyString, tyProcedural]) then
    Exit;
  { Two pointer types are compatible when:
      - either is untyped (Pointer), or
      - both are typed pointers to the same base type }
  if (AExpected.Kind = tyPointer) and (AActual.Kind = tyPointer) then
  begin
    if (TPointerTypeDesc(AExpected).BaseType = nil) or
       (TPointerTypeDesc(AActual).BaseType = nil) or
       (TPointerTypeDesc(AExpected).BaseType = TPointerTypeDesc(AActual).BaseType) then
      Exit;
  end;
  { Metaclass-of-TBase accepts metaclass-of-TDerived (TDerived is-a TBase). }
  if (AExpected.Kind = tyMetaClass) and (AActual.Kind = tyMetaClass) then
  begin
    if (TMetaClassTypeDesc(AExpected).BaseClass = TMetaClassTypeDesc(AActual).BaseClass) or
       IsSubtypeOf(TMetaClassTypeDesc(AActual).BaseClass,
                   TMetaClassTypeDesc(AExpected).BaseClass) then
      Exit;
  end;
  { Untyped Pointer ↔ metaclass: a class identifier passes through any
    'Pointer' parameter (used heavily by punit.AssertEquals(Pointer)). }
  if (AExpected.Kind = tyPointer) and (AActual.Kind = tyMetaClass) and
     (TPointerTypeDesc(AExpected).BaseType = nil) then
    Exit;
  if (AActual.Kind = tyPointer) and (AExpected.Kind = tyMetaClass) and
     (TPointerTypeDesc(AActual).BaseType = nil) then
    Exit;
  { enum ↔ enum (same type) already handled by = check above;
    enum ↔ integer: allow assignment between enum and integer types }
  if (AExpected.Kind = tyEnum) and AActual.IsNumeric() then Exit;
  if (AActual.Kind  = tyEnum) and AExpected.IsNumeric() then Exit;
  { set ↔ set: two set types over the same base enum are the same type, even
    when one is a named alias (TBackendSet) and the other anonymous
    (set of TBackend) — set values are structural, not nominal. }
  if (AExpected.Kind = tySet) and (AActual.Kind = tySet) and
     (TSetTypeDesc(AExpected).BaseType = TSetTypeDesc(AActual).BaseType) then
    Exit;
  { Numeric widening: allow within the integer family, within the float family
    (Single ↔ Double), and integer → float (implicit widening, same as
    Delphi/FPC).  Float → integer still requires explicit Trunc/Round.
    Exception: Int64 ↔ UInt64 requires an explicit cast since the same
    bit pattern means different values across the sign boundary. }
  if AExpected.IsFloat() and AActual.IsFloat() then Exit;
  if AExpected.IsFloat() and AActual.IsNumeric() and (not AActual.IsFloat()) then Exit;
  if AExpected.IsNumeric() and AActual.IsNumeric()
     and (not AExpected.IsFloat()) and (not AActual.IsFloat()) then
  begin
    if not (((AExpected.Kind = tyInt64)  and (AActual.Kind = tyUInt64)) or
            ((AExpected.Kind = tyUInt64) and (AActual.Kind = tyInt64))) then
      Exit;
  end;
  { subtype assignment: TDerived → TBase is allowed }
  if IsSubtypeOf(AActual, AExpected) then
    Exit;
  { TObject accepts any class — universal base class }
  if (AExpected.Kind = tyClass) and (AExpected.Name = 'TObject') and
     (AActual.Kind = tyClass) then
    Exit;
  { interface → base interface: IDerived is assignable to IBase when IBase is
    on IDerived's parent chain (IDog = interface(IAnimal) -> IDog is-a IAnimal). }
  if (AExpected.Kind = tyInterface) and (AActual.Kind = tyInterface) then
    if InterfaceInheritsFrom(TInterfaceTypeDesc(AActual),
                             TInterfaceTypeDesc(AExpected)) then
      Exit;
  { class → interface: allowed when the class — or ANY of its ancestors —
    implements that interface (or a descendant of it: implementing IDog also
    satisfies IAnimal).  A descendant inherits its parent's interface
    implementations, so the whole parent chain must be scanned, not just the
    class's own ImplementsList (issue #130 bug3). }
  if (AExpected.Kind = tyInterface) and (AActual.Kind = tyClass) then
  begin
    Walk := TRecordTypeDesc(AActual);
    while Walk <> nil do
    begin
      for I := 0 to Walk.ImplementsCount() - 1 do
        if (Walk.ImplementsIntfAt(I) = AExpected) or
           ((Walk.ImplementsIntfAt(I) is TInterfaceTypeDesc) and
            InterfaceInheritsFrom(TInterfaceTypeDesc(Walk.ImplementsIntfAt(I)),
                                  TInterfaceTypeDesc(AExpected))) then
          Exit;
      Walk := Walk.Parent;
    end;
  end;
  { Untyped pointer accepts any class/interface/string/PChar reference and vice-versa }
  if (AExpected.Kind = tyPointer) and
     (TPointerTypeDesc(AExpected).BaseType = nil) and
     (AActual.Kind in [tyClass, tyInterface, tyString, tyPointer, tyPChar]) then
    Exit;
  if (AActual.Kind = tyPointer) and
     (TPointerTypeDesc(AActual).BaseType = nil) and
     (AExpected.Kind in [tyClass, tyInterface, tyString, tyPointer, tyPChar]) then
    Exit;
  { PChar is compatible with PChar }
  if (AExpected.Kind = tyPChar) and (AActual.Kind = tyPChar) then Exit;
  { Open-array forwarding: both must be tyOpenArray with the same element type }
  if (AExpected.Kind = tyOpenArray) and (AActual.Kind = tyOpenArray) then
  begin
    if TOpenArrayTypeDesc(AExpected).ElementType =
       TOpenArrayTypeDesc(AActual).ElementType then
      Exit;
  end;
  { Static array coerced to open-array: element types must match }
  if (AExpected.Kind = tyOpenArray) and (AActual.Kind = tyStaticArray) then
  begin
    if TOpenArrayTypeDesc(AExpected).ElementType =
       TStaticArrayTypeDesc(AActual).ElementType then
      Exit;
  end;
  { Dynamic array coerced to open-array: element types must match.  A dynamic
    array's data + length give the (ptr, high) pair an open-array param
    expects, so `S(dyn)` where S(a: array of T) is valid. }
  if (AExpected.Kind = tyOpenArray) and (AActual.Kind = tyDynArray) then
  begin
    if TOpenArrayTypeDesc(AExpected).ElementType =
       TDynArrayTypeDesc(AActual).ElementType then
      Exit;
  end;
  { Procedural-type assignability: signatures must match (return type,
    parameter count, parameter types, parameter modes). }
  if (AExpected.Kind = tyProcedural) and (AActual.Kind = tyProcedural) then
  begin
    if TProceduralTypeDesc(AExpected).IsCompatibleWith(
         TProceduralTypeDesc(AActual)) then
      Exit;
  end;
  SemanticError(
    Format('Type mismatch in %s: expected ''%s'' but got ''%s''',
      [AContext, AExpected.Name, AActual.Name]),
    ALine, ACol);
end;

function TSemanticAnalyser.CurrentUnitPrefix: string;
begin
  { Program-scope routines (compiled via Analyse(AProg) with FProg
    non-nil) keep their bare names — they aren't shared across
    compilation units.  Unit-scope routines (AnalyseUnitForExport,
    FProg = nil) get the unit prefix via MangleUnitPrefix's
    allowlist semantics. }
  if FProg <> nil then
    Result := ''
  else
    Result := MangleUnitPrefix(FCurrentUnitName);
end;

procedure TSemanticAnalyser.AddGroupEntry(AGroups: TStringList;
  const AKey: string; ADecl: TMethodDecl);
var
  GIdx: Integer;
  Grp:  TObjectList;
begin
  GIdx := AGroups.IndexOf(AKey);
  if GIdx < 0 then
  begin
    Grp := TObjectList.Create(False);
    AGroups.AddObject(AKey, Grp);
    FGroupKeepAlive.Add(Grp);
  end
  else
    Grp := TObjectList(AGroups.Objects[GIdx]);
  Grp.Add(ADecl);
end;

function TSemanticAnalyser.GroupOf(AGroups: TStringList;
  const AKey: string): TObjectList;
var
  GIdx: Integer;
begin
  GIdx := AGroups.IndexOf(AKey);
  if GIdx >= 0 then
    Result := TObjectList(AGroups.Objects[GIdx])
  else
    Result := nil;
end;

procedure TSemanticAnalyser.ReplaceProcIndexObject(AIdx: Integer;
  ANew: TMethodDecl);
var
  Old: TMethodDecl;
  Grp: TObjectList;
  K:   Integer;
begin
  Old := TMethodDecl(FProcIndex.Objects[AIdx]);
  FProcIndex.Objects[AIdx] := ANew;
  Grp := GroupOf(FProcGroups, FProcIndex.Strings[AIdx]);
  if Grp <> nil then
  begin
    K := Grp.IndexOf(Old);
    if K >= 0 then
      Grp.Items[K] := ANew;
  end;
end;

procedure TSemanticAnalyser.RegisterProcDecl(const AName: string; ADecl: TMethodDecl);
begin
  if (ADecl.OwningUnit = '') and (FCurrentUnitName <> '') then
    ADecl.OwningUnit := FCurrentUnitName;
  FProcIndex.AddObject(AName, ADecl);
  AddGroupEntry(FProcGroups, AName, ADecl);
end;

function TSemanticAnalyser.IndexOfProcInUnit(const AName, AUnitName: string): Integer;
var
  I: Integer;
begin
  for I := 0 to FProcIndex.Count - 1 do
    if SameText(FProcIndex.Strings[I], AName) and
       SameText(TMethodDecl(FProcIndex.Objects[I]).OwningUnit, AUnitName) then
      Exit(I);
  Result := -1;
end;

function TSemanticAnalyser.EffectiveLinkName(A: TMethodDecl): string;
begin
  if A = nil then
  begin
    Result := '';
    Exit;
  end;
  if A.IsExternal then
  begin
    { External binding: link symbol is the `external name`, else Pascal name. }
    if A.ExternalName <> '' then Result := A.ExternalName
    else                         Result := A.Name;
  end
  else
  begin
    { Real routine: emitted symbol is ResolvedQbeName when set (bare name for
      unmangled RTL units blaise_*/rtl.*), else the Pascal name. }
    if A.ResolvedQbeName <> '' then Result := A.ResolvedQbeName
    else                            Result := A.Name;
  end;
end;

function TSemanticAnalyser.SameLinkSymbol(A, B: TMethodDecl): Boolean;
begin
  Result := False;
  if (A = nil) or (B = nil) then Exit;
  { At least one side must be an external binding — two distinct real routines
    that merely share a name are a genuine clash, not the same symbol. }
  if not (A.IsExternal or B.IsExternal) then Exit;
  if A.Params.Count <> B.Params.Count then Exit;
  Result := SameText(Self.EffectiveLinkName(A), Self.EffectiveLinkName(B));
end;

function TSemanticAnalyser.SameExternalDecl(A, B: TMethodDecl): Boolean;
begin
  Result := False;
  if (A = nil) or (B = nil) then Exit;
  if not (A.IsExternal and B.IsExternal) then Exit;
  Result := Self.SameLinkSymbol(A, B);
end;

function TSemanticAnalyser.AllSameExternalDecl(AList: TObjectList): Boolean;
var
  I:     Integer;
  First: TMethodDecl;
begin
  Result := False;
  if (AList = nil) or (AList.Count < 2) then Exit;
  First := TMethodDecl(AList.Items[0]);
  for I := 1 to AList.Count - 1 do
    if not Self.SameLinkSymbol(First, TMethodDecl(AList.Items[I])) then
      Exit;
  Result := True;
end;

function TSemanticAnalyser.BenignDuplicateExternal(ANew: TMethodDecl): Boolean;
var
  Existing:  TSymbol;
begin
  Result := False;
  if ANew = nil then Exit;
  { Only an external binding can benignly duplicate an existing symbol. }
  if not ANew.IsExternal then Exit;
  { The clash was detected in the global scope (interface symbols define at
    scope depth 1), so resolve the colliding symbol there directly — the
    uses-chain Lookup could otherwise return a shadowing symbol from a
    different scope. }
  Existing := FTable.GlobalScope().LookupLocal(ANew.Name);
  if Existing = nil then Exit;
  if not (Existing.Kind in [skProcedure, skFunction]) then Exit;
  if Existing.Decl = nil then Exit;
  { Same underlying link symbol — e.g. an `external name '_BlaiseGetMem'`
    binding targeting the real _BlaiseGetMem exported by blaise_mem. }
  Result := Self.SameLinkSymbol(TMethodDecl(Existing.Decl), ANew);
end;

procedure TSemanticAnalyser.BuildUsesChain(AUsedUnits: TStringList);
var
  I: Integer;
begin
  FCurrentUsesChain.Clear();
  { Implicit `System` is always the first entry in every unit's
    effective uses chain (Pascal "Uses System(hidden), Classes;"
    rule).  User code never has to write it; it sits at the bottom
    of the right-to-left walk, so any user-supplied unit that
    re-exports a System name shadows it.  TSymbolTable's
    RegisterBuiltins also defines a small set of compiler intrinsics
    directly in global scope — those remain reachable as the final
    fallback after the chain.

    Skip the prepend when the unit being analysed IS System — a unit
    cannot use itself.  FCurrentUnitName is set by Analyse/
    AnalyseUnitForExport just before BuildUsesChain runs. }
  if not SameText(FCurrentUnitName, 'System') then
    FCurrentUsesChain.Add('System');
  if AUsedUnits = nil then Exit;
  for I := 0 to AUsedUnits.Count - 1 do
    { Defensive: a user `uses System` (case-insensitive) is the same
      as the implicit one — skip the dup so right-to-left doesn't
      shadow itself.  TStringList is CaseSensitive=False so IndexOf
      handles it. }
    if FCurrentUsesChain.IndexOf(AUsedUnits.Strings[I]) < 0 then
      FCurrentUsesChain.Add(AUsedUnits.Strings[I]);
end;

procedure TSemanticAnalyser.Analyse(AProg: TProgram);
var
  I: Integer;
begin
  FProg := AProg;
  FlushPendingGenericInstances();
  FCurrentUnitName := AProg.Name;
  BuildUsesChain(AProg.UsedUnits);
  FTable.UsesChainProvider := Self;
  { Tag program-level globals with the program's name so layer-3
    lookup (current compilation's own symbols) finds them ahead of
    a use'd unit's same-named export. }
  FTable.DefineOwningUnit := AProg.Name;
  { The program's own name and the names of directly used units are
    reserved identifiers — no top-level declaration may redeclare
    them (issue #84, matching FPC/Delphi). }
  DefineModuleName(AProg.Name);
  for I := 0 to AProg.UsedUnits.Count - 1 do
    DefineModuleName(AProg.UsedUnits.Strings[I]);
  AnalyseBlock(AProg.Block, True);
  { Transfer symbol table ownership to the program so that TTypeDesc
    objects (referenced by ResolvedType pointers on AST nodes) outlive
    this analyser. }
  AProg.SymbolTable := FTable;
  FTable := nil;
end;

procedure TSemanticAnalyser.AnalyseUnit(AUnit: TUnit);
var
  I, J:     Integer;
  MDecl:    TMethodDecl;
  ImplDecl: TMethodDecl;
  ImplIdx:  Integer;
  Par:      TMethodParam;
  ParType:  TTypeDesc;
  Sym:      TSymbol;
begin
  FCurrentUnitName := AUnit.Name;
  FCurrentUnit := AUnit;
  FlushPendingGenericInstances();
  FTable.PushScope();
  try
    { The unit's own name and the names of directly used units are
      reserved identifiers — no interface or implementation decl may
      redeclare them (issue #84, matching FPC/Delphi). }
    DefineModuleName(AUnit.Name);
    for I := 0 to AUnit.UsedUnits.Count - 1 do
      DefineModuleName(AUnit.UsedUnits.Strings[I]);
    for I := 0 to AUnit.ImplUsedUnits.Count - 1 do
      DefineModuleName(AUnit.ImplUsedUnits.Strings[I]);

    { Resolve interface type and constant declarations. }
    AnalyseConstDecls(AUnit.IntfBlock);
    AnalyseTypeDecls(AUnit.IntfBlock);
    AnalyseArrayConstDecls(AUnit.IntfBlock);

    { Generic class templates must receive their impl-section method bodies
      *before* any FindTypeOrInstantiate call can clone an instance, or the
      instance is born with nil bodies and codegen emits no function for it. }
    LinkGenericClassMethodImpls(AUnit.ImplBlock);
    RepairEarlyGenericInstances();

    { Register interface-section global variables — visible to impl bodies. }
    for I := 0 to AUnit.IntfBlock.Decls.Count - 1 do
    begin
      MDecl := nil;  { reuse var below }
      ParType := FindTypeOrInstantiate(TVarDecl(AUnit.IntfBlock.Decls.Items[I]).TypeName);
      if ParType = nil then
        SemanticError(
          Format('Unknown type ''%s''',
            [TVarDecl(AUnit.IntfBlock.Decls.Items[I]).TypeName]),
          TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Line,
          TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Col);
      TVarDecl(AUnit.IntfBlock.Decls.Items[I]).ResolvedType := ParType;
      TVarDecl(AUnit.IntfBlock.Decls.Items[I]).IsGlobal := True;
      for J := 0 to TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Names.Count - 1 do
      begin
        Sym := TSymbol.Create(
          TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Names.Strings[J],
          skVariable, ParType);
        Sym.IsGlobal    := True;
        Sym.IsThreadVar := TVarDecl(AUnit.IntfBlock.Decls.Items[I]).IsThreadVar;
        if not FTable.Define(Sym) then
        begin
          Sym.Free();
          SemanticError(Format('Duplicate identifier ''%s''',
            [TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Names.Strings[J]]),
            TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Line,
            TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Col);
        end;
      end;
      if TVarDecl(AUnit.IntfBlock.Decls.Items[I]).InitConst <> nil then
        Self.AnalyseVarInitializer(TVarDecl(AUnit.IntfBlock.Decls.Items[I]));
    end;

    { Register interface forward declaration signatures }
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);

      { Generic free routines: skip param/return resolution and
        global-symbol registration; the impl-side AnalyseStandaloneDecl
        registers the template for on-demand instantiation. }
      if MDecl.TypeParams <> nil then
        Continue;

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par              := TMethodParam(MDecl.Params.Items[J]);
        Par.ResolvedType := ResolveParamType(Par, MDecl.Line, MDecl.Col);
      end;

      if MDecl.ReturnTypeName <> '' then
      begin
        ParType := FindTypeOrInstantiate(MDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for ''%s''',
              [MDecl.ReturnTypeName, MDecl.Name]),
            MDecl.Line, MDecl.Col);
        MDecl.ResolvedReturnType := ParType;
      end;

      { Compute mangled QBE name for overloaded forward decls. }
      if MDecl.IsOverload then
        MDecl.ResolvedQbeName := CurrentUnitPrefix() + MDecl.Name + '$' + MangleParamSig(MDecl)
      else
        MDecl.ResolvedQbeName := CurrentUnitPrefix() + MDecl.Name;

      RegisterProcDecl(MDecl.Name, MDecl);

      if MDecl.ReturnTypeName <> '' then
        Sym := TSymbol.Create(MDecl.Name, skFunction, MDecl.ResolvedReturnType)
      else
        Sym := TSymbol.Create(MDecl.Name, skProcedure, nil);
      Sym.IsOverload := MDecl.IsOverload;
      Sym.Decl       := MDecl;
      if not FTable.Define(Sym) then
      begin
        Sym.Free();
        { Two units may each export the same external C binding (e.g.
          `external name '_BlaiseGetMem'`).  The flat-merge shares one
          global scope, so the second Define collides — but it denotes ONE
          underlying symbol, not a real duplicate.  Tolerate it; otherwise
          report the genuine clash. }
        if not BenignDuplicateExternal(MDecl) then
          SemanticError(Format('Duplicate identifier ''%s''', [MDecl.Name]),
            MDecl.Line, MDecl.Col);
      end;
    end;

    { Process implementation-section const + type declarations before
      walking proc bodies, so that impl-only types and consts are in
      scope when their referencing routines are analysed. }
    AnalyseConstDecls(AUnit.ImplBlock);
    AnalyseTypeDecls(AUnit.ImplBlock);
    AnalyseArrayConstDecls(AUnit.ImplBlock);

    { Register impl-section global variables. }
    for I := 0 to AUnit.ImplBlock.Decls.Count - 1 do
    begin
      ParType := FindTypeOrInstantiate(TVarDecl(AUnit.ImplBlock.Decls.Items[I]).TypeName);
      if ParType = nil then
        SemanticError(
          Format('Unknown type ''%s''',
            [TVarDecl(AUnit.ImplBlock.Decls.Items[I]).TypeName]),
          TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Line,
          TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Col);
      TVarDecl(AUnit.ImplBlock.Decls.Items[I]).ResolvedType := ParType;
      TVarDecl(AUnit.ImplBlock.Decls.Items[I]).IsGlobal := True;
      for J := 0 to TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Names.Count - 1 do
      begin
        Sym := TSymbol.Create(
          TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Names.Strings[J],
          skVariable, ParType);
        Sym.IsGlobal    := True;
        Sym.IsThreadVar := TVarDecl(AUnit.ImplBlock.Decls.Items[I]).IsThreadVar;
        if not FTable.Define(Sym) then
        begin
          Sym.Free();
          SemanticError(Format('Duplicate identifier ''%s''',
            [TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Names.Strings[J]]),
            TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Line,
            TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Col);
        end;
      end;
      if TVarDecl(AUnit.ImplBlock.Decls.Items[I]).InitConst <> nil then
        Self.AnalyseVarInitializer(TVarDecl(AUnit.ImplBlock.Decls.Items[I]));
    end;

    { Process implementation declarations — skip generic class method impls
      (OwnerTypeName + OwnerTypeParams set); they are handled below. }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if (ImplDecl.OwnerTypeName <> '') and (ImplDecl.OwnerTypeParams <> nil) then
        Continue;
      { Generic free routine impls — handled via AnalyseStandaloneDecl /
        FGenericFuncTemplates; their param types only resolve at
        instantiation time. }
      if (ImplDecl.OwnerTypeName = '') and (ImplDecl.TypeParams <> nil) then
        Continue;

      for J := 0 to ImplDecl.Params.Count - 1 do
      begin
        Par              := TMethodParam(ImplDecl.Params.Items[J]);
        Par.ResolvedType := ResolveParamType(Par, ImplDecl.Line, ImplDecl.Col);
      end;

      if ImplDecl.ReturnTypeName <> '' then
      begin
        ParType := FindTypeOrInstantiate(ImplDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for ''%s''',
              [ImplDecl.ReturnTypeName, ImplDecl.Name]),
            ImplDecl.Line, ImplDecl.Col);
        ImplDecl.ResolvedReturnType := ParType;
      end;

      { Match impl to forward by signature.
        When any forward decl with this name is overloaded (or when the impl
        itself is marked overload), use mangled-signature matching so that each
        overload variant pairs with the correct forward decl.  This handles the
        common pattern where the interface marks each overload but the
        implementation body omits the 'overload' keyword. }
      { An impl-section routine may only pair with a forward decl from its OWN
        unit.  FProcIndex is global across all compiled units, so an unqualified
        IndexOf would match an identically-named forward decl from an imported
        unit — including the common case of two units that each privately declare
        the same `external name '...'` C function.  When that happened the second
        unit's routine was treated as an impl of the first unit's decl and was
        never defined into its own scope, so calls to it reported "Undeclared
        function".  Restrict every match to the current unit. }
      ImplIdx := -1;
      if ImplDecl.IsOverload then
      begin
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             SameText(TMethodDecl(FProcIndex.Objects[J]).OwningUnit, FCurrentUnitName) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
      end
      else
      begin
        { Check if any forward decl with this name is overloaded.
          If so, use signature matching even without 'overload' on the impl. }
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             SameText(TMethodDecl(FProcIndex.Objects[J]).OwningUnit, FCurrentUnitName) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
        if ImplIdx < 0 then
          ImplIdx := IndexOfProcInUnit(ImplDecl.Name, FCurrentUnitName);
      end;

      if ImplIdx >= 0 then
      begin
        { Matched an interface forward decl — verify param count }
        MDecl := TMethodDecl(FProcIndex.Objects[ImplIdx]);
        if MDecl.Params.Count <> ImplDecl.Params.Count then
          SemanticError(
            Format('Signature mismatch for ''%s'': interface has %d params, implementation has %d',
              [ImplDecl.Name, MDecl.Params.Count, ImplDecl.Params.Count]),
            ImplDecl.Line, ImplDecl.Col);
        { Carry mangling forward, then update the index entry.  The impl decl
          must inherit the forward decl's OwningUnit so the later
          IndexOfProcInUnit "has no implementation" check still finds it. }
        ImplDecl.ResolvedQbeName := MDecl.ResolvedQbeName;
        ImplDecl.IsOverload      := MDecl.IsOverload;
        ImplDecl.OwningUnit      := MDecl.OwningUnit;
        TransferDefaultValues(MDecl, ImplDecl);
        ReplaceProcIndexObject(ImplIdx, ImplDecl);
      end
      else
      begin
        { Impl-only declaration — register symbol and index it }
        ImplDecl.IsImplOnly := True;
        if ImplDecl.IsOverload then
          ImplDecl.ResolvedQbeName := CurrentUnitPrefix() + ImplDecl.Name + '$' + MangleParamSig(ImplDecl)
        else
          ImplDecl.ResolvedQbeName := CurrentUnitPrefix() + ImplDecl.Name;
        RegisterProcDecl(ImplDecl.Name, ImplDecl);
        if ImplDecl.ReturnTypeName <> '' then
          Sym := TSymbol.Create(ImplDecl.Name, skFunction, ImplDecl.ResolvedReturnType)
        else
          Sym := TSymbol.Create(ImplDecl.Name, skProcedure, nil);
        Sym.IsOverload := ImplDecl.IsOverload;
        Sym.Decl       := ImplDecl;
        if not FTable.Define(Sym) then
        begin
          Sym.Free();
          SemanticError(Format('Duplicate identifier ''%s''', [ImplDecl.Name]),
            ImplDecl.Line, ImplDecl.Col);
        end;
      end;
    end;

    { Generic class method body linking already happened above, before any
      potential instantiation. }

    { Verify every interface declaration has a matching implementation }
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl   := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
      if MDecl.IsExternal then Continue;
      { Generic free routines live in FGenericFuncTemplates, not FProcIndex —
        their impl is checked by AnalyseStandaloneDecl. }
      if MDecl.TypeParams <> nil then Continue;
      ImplIdx := IndexOfProcInUnit(MDecl.Name, FCurrentUnitName);
      if (ImplIdx < 0) or
         (TMethodDecl(FProcIndex.Objects[ImplIdx]).Body = nil) then
        SemanticError(
          Format('Interface function ''%s'' has no implementation', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
    end;

    { Analyse standalone implementation bodies (skip generic class method
      impls and generic free routines — both defer body analysis to
      instantiation time). }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if (ImplDecl.OwnerTypeName <> '') and (ImplDecl.OwnerTypeParams <> nil) then
        Continue;
      if (ImplDecl.OwnerTypeName = '') and (ImplDecl.TypeParams <> nil) then
        Continue;
      AnalyseStandaloneDecl(ImplDecl);
    end;

    { After all unit-impl bodies are analysed, mark inline candidates. }
    MarkInlineCandidates(AUnit.ImplBlock);

    { Analyse initialization/finalization section statements at unit scope. }
    if AUnit.InitStmts <> nil then
      for I := 0 to AUnit.InitStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.InitStmts.Items[I]));
    if AUnit.FinalStmts <> nil then
      for I := 0 to AUnit.FinalStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.FinalStmts.Items[I]));

    { Register + analyse anonymous-method thunks lifted during the body
      passes above.  Must run at unit scope (inside this try) so thunk
      bodies still see unit globals, and before codegen walks
      ImplBlock.ProcDecls. }
    DrainPendingAnonDecls(AUnit.ImplBlock);
  finally
    FTable.PopScope();
  end;
  AUnit.SymbolTable := FTable;
  FTable := nil;
  FCurrentUnit := nil;
end;

procedure TSemanticAnalyser.AnalyseUnitForExport(AUnit: TUnit);
var
  I, J:     Integer;
  MDecl:    TMethodDecl;
  ImplDecl: TMethodDecl;
  ImplIdx:  Integer;
  Par:      TMethodParam;
  ParType:  TTypeDesc;
  Sym:      TSymbol;
  VDecl:    TVarDecl;
begin
  FCurrentUnitName := AUnit.Name;
  FCurrentUnit := AUnit;
  FlushPendingGenericInstances();
  BuildUsesChain(AUnit.UsedUnits);
  FTable.UsesChainProvider := Self;
  { Auto-tag every global Define within this unit's analysis with the
    unit name — populates TSymbol.OwningUnit for the source-compiled-
    dep path, paralleling uSemanticImport for the .bif-loaded path.
    Consumed by codegen's unit-prefix mangling and by per-unit
    visibility.  Cleared at the end. }
  FTable.DefineOwningUnit := AUnit.Name;
  { --- Interface section ------------------------------------------------
    No scope is pushed here: all FTable.Define calls go to the global scope,
    making these symbols visible to callers of this unit. }

  AnalyseConstDecls(AUnit.IntfBlock);
  AnalyseTypeDecls(AUnit.IntfBlock);
  AnalyseArrayConstDecls(AUnit.IntfBlock);

  { Transfer impl-section bodies to generic class templates *before* any
    instantiation can happen.  Generic instances clone the template's
    Methods.Body at instantiation time, so if the body is still nil,
    the cloned instance method is born without a body and codegen emits
    no function — leaving call sites referencing an undefined symbol. }
  LinkGenericClassMethodImpls(AUnit.ImplBlock);
  RepairEarlyGenericInstances();

  { Register interface-section global variables.  Marked IsGlobal so
    codegen emits them as data-segment slots rather than stack allocs;
    visible to callers of this unit. }
  for I := 0 to AUnit.IntfBlock.Decls.Count - 1 do
  begin
    VDecl := TVarDecl(AUnit.IntfBlock.Decls.Items[I]);
    ParType := FindTypeOrInstantiate(VDecl.TypeName);
    if ParType = nil then
      SemanticError(Format('Unknown type ''%s''', [VDecl.TypeName]),
        VDecl.Line, VDecl.Col);
    VDecl.ResolvedType := ParType;
    VDecl.IsGlobal := True;
    for J := 0 to VDecl.Names.Count - 1 do
    begin
      Sym := TSymbol.Create(VDecl.Names.Strings[J], skVariable, ParType);
      Sym.IsGlobal    := True;
      Sym.IsThreadVar := VDecl.IsThreadVar;
      DefineGlobalLastWins(Sym, VDecl.Line, VDecl.Col);
    end;
  end;

  { Register interface forward declarations for standalone procs/funcs.
    Must happen before AnalyseMethodBodies so class method bodies can call
    them (e.g. TStringList.SetText calls SplitIntoList). }
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    MDecl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);

    { Generic free routines: defer param/return resolution to
      instantiation time and skip global symbol registration —
      the template is registered through FGenericFuncTemplates by
      AnalyseStandaloneDecl on the impl side. }
    if MDecl.TypeParams <> nil then
      Continue;

    for J := 0 to MDecl.Params.Count - 1 do
    begin
      Par              := TMethodParam(MDecl.Params.Items[J]);
      Par.ResolvedType := ResolveParamType(Par, MDecl.Line, MDecl.Col);
    end;

    if MDecl.ReturnTypeName <> '' then
    begin
      ParType := FindTypeOrInstantiate(MDecl.ReturnTypeName);
      if ParType = nil then
        SemanticError(
          Format('Unknown return type ''%s'' for ''%s''',
            [MDecl.ReturnTypeName, MDecl.Name]),
          MDecl.Line, MDecl.Col);
      MDecl.ResolvedReturnType := ParType;
    end;

    if MDecl.IsOverload then
      MDecl.ResolvedQbeName := CurrentUnitPrefix() + MDecl.Name + '$' + MangleParamSig(MDecl)
    else
      MDecl.ResolvedQbeName := CurrentUnitPrefix() + MDecl.Name;

    RegisterProcDecl(MDecl.Name, MDecl);

    if MDecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(MDecl.Name, skFunction, MDecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(MDecl.Name, skProcedure, nil);
    Sym.IsOverload := MDecl.IsOverload;
    Sym.Decl       := MDecl;
    if not FTable.Define(Sym) then
    begin
      Sym.Free();
      { Same-external collapse — see the note on the parallel AnalyseUnit
        path: two units exporting the same `external name 'X'` binding share
        one underlying symbol, so a Define collision there is benign. }
      if not BenignDuplicateExternal(MDecl) then
        SemanticError(Format('Duplicate identifier ''%s''', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
    end;
  end;

  { Register impl-section TYPE declarations BEFORE linking class method bodies,
    so a class declared in the implementation section has its methods registered
    in FMethodGroups when LinkClassMethodImpls looks them up (otherwise every
    impl-section class method reports "not declared in class").

    These are registered in the GLOBAL scope (not the pushed impl scope below)
    so the type symbols survive to codegen — EmitClassSection / EmitUnit walk
    the AST TypeDecls but ClassUnitPrefix's symbol Lookup must still find the
    class to derive its unit-qualified _FieldCleanup/vtable/typeinfo names.
    Marking them IsImplPrivate (DefineImplPrivate context) keeps them visible
    only to THIS unit: Lookup suppresses them while any other unit is analysed,
    so they do not leak into unrelated units through the flat global scope.
    The unit's own bodies still resolve them via layer 3 (owner = current
    unit); code generation resolves them by setting the emitted unit as the
    table's viewing context.

    Only TYPES are hoisted.  Impl-section consts stay in the pushed scope below
    (layer-1 visible to the unit's own bodies, never global, so they never need
    suppression); LinkClassMethodImpls needs only the types.  An impl-section
    type that sizes itself on an impl-section const is not currently supported
    and would report "Unknown type" — no codebase unit relies on it. }
  FTable.DefineImplPrivate := True;
  try
    AnalyseTypeDecls(AUnit.ImplBlock);
  finally
    FTable.DefineImplPrivate := False;
  end;

  { Link class method bodies from ImplBlock to the class type method decls
    registered by AnalyseTypeDecls.  Generic-class linking happened earlier
    so instances can clone bodies at instantiation time. }
  LinkClassMethodImpls(AUnit.ImplBlock);

  { A concrete class method declared in either section must have an
    implementation in the impl section (see CheckClassMethodsImplemented). }
  CheckClassMethodsImplemented(AUnit.IntfBlock);
  CheckClassMethodsImplemented(AUnit.ImplBlock);

  { --- Implementation section -------------------------------------------
    Push a scope so impl-only standalone symbols don't leak globally.
    Class method bodies are analysed inside this scope so they can call
    impl-only helpers (e.g. TStringList.SetText -> SplitIntoList).
    (Impl-section type decls were already processed above.) }
  FTable.PushScope();
  try
    { Register impl-section consts + global variables.  Consts stay in this
      pushed scope (layer-1 visible to the unit's own bodies); globals are
      marked IsGlobal so codegen emits them as data-segment slots. }
    AnalyseConstDecls(AUnit.ImplBlock);
    AnalyseArrayConstDecls(AUnit.ImplBlock);
    for I := 0 to AUnit.ImplBlock.Decls.Count - 1 do
    begin
      VDecl := TVarDecl(AUnit.ImplBlock.Decls.Items[I]);
      ParType := FindTypeOrInstantiate(VDecl.TypeName);
      if ParType = nil then
        SemanticError(Format('Unknown type ''%s''', [VDecl.TypeName]), VDecl.Line, VDecl.Col);
      VDecl.ResolvedType := ParType;
      VDecl.IsGlobal := True;
      for J := 0 to VDecl.Names.Count - 1 do
      begin
        Sym := TSymbol.Create(VDecl.Names.Strings[J], skVariable, ParType);
        Sym.IsGlobal    := True;
        Sym.IsThreadVar := VDecl.IsThreadVar;
        if not FTable.Define(Sym) then
        begin
          Sym.Free();
          SemanticError(Format('Duplicate identifier ''%s''', [VDecl.Names.Strings[J]]), VDecl.Line, VDecl.Col);
        end;
      end;
    end;

    { Register impl decls, skipping class method impls (already linked above) }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if ImplDecl.OwnerTypeName <> '' then Continue;  { class method — already handled }
      { Generic free routines defer all param/return resolution to
        instantiation time; AnalyseStandaloneDecl below registers
        the template. }
      if ImplDecl.TypeParams <> nil then Continue;

      for J := 0 to ImplDecl.Params.Count - 1 do
      begin
        Par              := TMethodParam(ImplDecl.Params.Items[J]);
        Par.ResolvedType := ResolveParamType(Par, ImplDecl.Line, ImplDecl.Col);
      end;

      if ImplDecl.ReturnTypeName <> '' then
      begin
        ParType := FindTypeOrInstantiate(ImplDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for ''%s''',
              [ImplDecl.ReturnTypeName, ImplDecl.Name]),
            ImplDecl.Line, ImplDecl.Col);
        ImplDecl.ResolvedReturnType := ParType;
      end;

      { Match impl to forward by signature.
        When any forward decl with this name is overloaded (or when the impl
        itself is marked overload), use mangled-signature matching so that
        each overload variant pairs with the correct forward decl.
        This covers the common Pascal pattern where the interface marks each
        overload with the 'overload' keyword but the implementation section
        repeats the body without re-stating 'overload'. }
      { Impl pairs only with a forward decl from its OWN unit — see the matching
        comment in AnalyseUnit.  FProcIndex is global across units. }
      ImplIdx := -1;
      if ImplDecl.IsOverload then
      begin
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             SameText(TMethodDecl(FProcIndex.Objects[J]).OwningUnit, FCurrentUnitName) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
      end
      else
      begin
        { Check if any forward decl with this name is overloaded.
          If so, use signature matching even though the impl lacks 'overload'. }
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             SameText(TMethodDecl(FProcIndex.Objects[J]).OwningUnit, FCurrentUnitName) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
        if ImplIdx < 0 then
          ImplIdx := IndexOfProcInUnit(ImplDecl.Name, FCurrentUnitName);
      end;

      if ImplIdx >= 0 then
      begin
        { Matches an interface forward decl — verify param count and update index }
        MDecl := TMethodDecl(FProcIndex.Objects[ImplIdx]);
        if MDecl.Params.Count <> ImplDecl.Params.Count then
          SemanticError(
            Format('Signature mismatch for ''%s'': interface has %d params, implementation has %d',
              [ImplDecl.Name, MDecl.Params.Count, ImplDecl.Params.Count]),
            ImplDecl.Line, ImplDecl.Col);
        ImplDecl.ResolvedQbeName := MDecl.ResolvedQbeName;
        ImplDecl.IsOverload      := MDecl.IsOverload;
        ImplDecl.OwningUnit      := MDecl.OwningUnit;
        TransferDefaultValues(MDecl, ImplDecl);
        ReplaceProcIndexObject(ImplIdx, ImplDecl);
      end
      else
      begin
        { Impl-only declaration — register in impl scope (does not persist) }
        ImplDecl.IsImplOnly := True;
        if ImplDecl.IsOverload then
          ImplDecl.ResolvedQbeName := CurrentUnitPrefix() + ImplDecl.Name + '$' + MangleParamSig(ImplDecl)
        else
          ImplDecl.ResolvedQbeName := CurrentUnitPrefix() + ImplDecl.Name;
        RegisterProcDecl(ImplDecl.Name, ImplDecl);
        if ImplDecl.ReturnTypeName <> '' then
          Sym := TSymbol.Create(ImplDecl.Name, skFunction, ImplDecl.ResolvedReturnType)
        else
          Sym := TSymbol.Create(ImplDecl.Name, skProcedure, nil);
        Sym.IsOverload := ImplDecl.IsOverload;
        Sym.Decl       := ImplDecl;
        if not FTable.Define(Sym) then
        begin
          Sym.Free();
          SemanticError(Format('Duplicate identifier ''%s''', [ImplDecl.Name]),
            ImplDecl.Line, ImplDecl.Col);
        end;
      end;
    end;

    { Analyse class method bodies — impl-only helpers now visible above.
      ImplBlock is analysed too so a class declared in the implementation
      section has its method bodies type-checked (otherwise field/param
      references inside them carry no ResolvedType and codegen aborts with
      "no resolved type"). }
    AnalyseMethodBodies(AUnit.IntfBlock);
    AnalyseMethodBodies(AUnit.ImplBlock);

    { Verify every interface declaration has a matching implementation }
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl   := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
      if MDecl.IsExternal then Continue;
      { Generic free routines: impl lives in FGenericFuncTemplates. }
      if MDecl.TypeParams <> nil then Continue;
      ImplIdx := IndexOfProcInUnit(MDecl.Name, FCurrentUnitName);
      if (ImplIdx < 0) or
         (TMethodDecl(FProcIndex.Objects[ImplIdx]).Body = nil) then
        SemanticError(
          Format('Interface function ''%s'' has no implementation', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
    end;

    { Analyse standalone implementation bodies (skip class method impls
      and generic free routines, whose bodies only re-type-check at
      instantiation time). }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if ImplDecl.OwnerTypeName <> '' then Continue;
      if ImplDecl.TypeParams <> nil then Continue;
      AnalyseStandaloneDecl(ImplDecl);
    end;

    { After all unit-impl bodies are analysed, mark inline candidates. }
    MarkInlineCandidates(AUnit.ImplBlock);

    { Analyse initialization/finalization section statements at unit scope. }
    if AUnit.InitStmts <> nil then
      for I := 0 to AUnit.InitStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.InitStmts.Items[I]));
    if AUnit.FinalStmts <> nil then
      for I := 0 to AUnit.FinalStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.FinalStmts.Items[I]));

    { Register + analyse anonymous-method thunks lifted during the body
      passes above.  Must run at unit scope (inside this try) so thunk
      bodies still see unit globals, and before codegen walks
      ImplBlock.ProcDecls. }
    DrainPendingAnonDecls(AUnit.ImplBlock);
  finally
    FTable.PopScope();
  end;
  FCurrentUnit := nil;
  FTable.DefineOwningUnit := '';
end;

procedure TSemanticAnalyser.RegisterImportedRoutine(const AName: string;
                                                    ADecl: TMethodDecl);
begin
  { ADecl.OwningUnit is set by the caller (uSemanticImport) to the
    iface's unit name before we get here; don't overwrite with
    FCurrentUnitName since the analyser may not be mid-analysis. }
  FProcIndex.AddObject(AName, ADecl);
  AddGroupEntry(FProcGroups, AName, ADecl);
end;

procedure TSemanticAnalyser.RegisterImportedMethod(const ATypeName: string;
                                                    ADecl: TMethodDecl);
begin
  FMethodIndex.AddObject(ATypeName + '.' + ADecl.Name, ADecl);
  AddGroupEntry(FMethodGroups, ATypeName + '.' + ADecl.Name, ADecl);
end;

function TSemanticAnalyser.ResolveImportedTypeName(const AName: string): TTypeDesc;
begin
  Result := Self.FindTypeOrInstantiate(AName);
end;

procedure TSemanticAnalyser.RegisterUnitIface(AIface: TUnitInterface);
var
  Idx, I:  Integer;
  Scope:   TScope;
  Sym:     TSymbol;
begin
  if AIface = nil then Exit;
  Idx := FUnitIfaces.IndexOf(AIface.Name);
  if Idx >= 0 then
    FUnitIfaces.Objects[Idx] := AIface
  else
    FUnitIfaces.AddObject(AIface.Name, AIface);

  { Absorb the symbols this unit Define'd into FTable's global scope
    into the per-unit cache.  Lets LookupViaUsesChain do a direct
    keyed retrieval without filtering the flat global by OwningUnit.
    Walks each global-scope symbol once and grabs the ones whose
    OwningUnit matches AIface.Name. }
  if FTable = nil then Exit;
  Scope := FTable.GlobalScope();
  for I := 0 to Scope.SymbolCount() - 1 do
  begin
    Sym := Scope.SymbolAt(I);
    if (Sym <> nil) and SameText(Sym.OwningUnit, AIface.Name) then
      RegisterUnitSymbol(AIface.Name, Sym);
  end;
end;

function TSemanticAnalyser.FindUnitIface(const AUnitName: string): TUnitInterface;
var
  Idx: Integer;
begin
  Idx := FUnitIfaces.IndexOf(AUnitName);
  if Idx >= 0 then
    Result := TUnitInterface(FUnitIfaces.Objects[Idx])
  else
    Result := nil;
end;

procedure TSemanticAnalyser.DefineModuleName(const AName: string);
var
  Sym: TSymbol;
begin
  if AName = '' then Exit;
  Sym := TSymbol.Create(AName, skModule, nil);
  if not FTable.Define(Sym) then
    Sym.Free();  { name already taken — keep the existing symbol }
end;

procedure TSemanticAnalyser.RegisterUnitSymbol(const AUnitName: string;
                                               ASym: TSymbol);
var
  Key: string;
  Idx: Integer;
begin
  if (AUnitName = '') or (ASym = nil) then Exit;
  Key := AUnitName + #1 + ASym.Name;
  Idx := FUnitSymbols.IndexOf(Key);
  if Idx >= 0 then
    FUnitSymbols.Objects[Idx] := ASym
  else
    FUnitSymbols.AddObject(Key, ASym);
end;

function TSemanticAnalyser.FindUnitSymbol(const AUnitName,
                                          ASymName: string): TSymbol;
var
  Idx: Integer;
begin
  Idx := FUnitSymbols.IndexOf(AUnitName + #1 + ASymName);
  if Idx >= 0 then
    Result := TSymbol(FUnitSymbols.Objects[Idx])
  else
    Result := nil;
end;

function TSemanticAnalyser.ResolveQualified(const AUnit,
                                            AName: string): TSymbol;
begin
  Result := nil;
  if (AUnit = '') or (FTable = nil) then Exit;

  { 1. Per-unit cache: direct keyed retrieval — the symbol AUnit defined.
       This is what disambiguates two units exporting the same name (a
       collision winner is evicted from the flat table but kept here). }
  Result := FindUnitSymbol(AUnit, AName);
  if Result <> nil then Exit;

  { 2. Flat-table fallback: covers paths/harnesses that populate the flat
       global but not the per-unit cache (the cache is only filled by the
       driver's RegisterUnitIface loop; the in-process test harness skips
       it).  Accept the symbol unless it demonstrably belongs to a DIFFERENT
       unit — same leniency as the LookupViaUsesChain fallback: an empty
       OwningUnit is treated as a match, a non-empty mismatch is rejected. }
  FTable.BypassUsesChain := True;
  try
    Result := FTable.Lookup(AName);
  finally
    FTable.BypassUsesChain := False;
  end;
  if (Result <> nil) and (Result.OwningUnit <> '')
     and not SameText(Result.OwningUnit, AUnit) then
    Result := nil;
end;

function TSemanticAnalyser.LookupViaUsesChain(const AName: string): TSymbol;
var
  I:        Integer;
  UnitName: string;
  Iface:    TUnitInterface;
  Sym:      TSymbol;
begin
  Result := nil;
  if FTable = nil then Exit;
  { Right-to-left walk = "last in uses wins". }
  FTable.BypassUsesChain := True;
  try
    for I := FCurrentUsesChain.Count - 1 downto 0 do
    begin
      UnitName := FCurrentUsesChain.Strings[I];

      { Prefer the per-unit symbol cache — direct keyed lookup, no
        flat-global filtering needed.  Populated by uSemanticImport
        when materialising iface symbols. }
      Sym := FindUnitSymbol(UnitName, AName);

      { Fallback: probe the iface's HasSymbol and the flat FTable.
        Covers entries the per-unit cache hasn't seen yet (e.g.
        symbols defined by the unit currently mid-analysis whose
        AnalyseUnitForExport hasn't completed its Register*-equivalent
        path). }
      if Sym = nil then
      begin
        Iface := FindUnitIface(UnitName);
        if (Iface <> nil) and Iface.HasSymbol(AName) then
        begin
          Sym := FTable.Lookup(AName);
          if (Sym <> nil) and (Sym.OwningUnit <> '')
             and not SameText(Sym.OwningUnit, UnitName) then
            Sym := nil;
        end;
      end;

      if Sym = nil then Continue;

      if IsVisibleFromUnit(Sym, FCurrentUnitName, FCurrentClass) then
      begin
        Result := Sym;
        Exit;
      end;
    end;
  finally
    FTable.BypassUsesChain := False;
  end;
end;

function TSemanticAnalyser.IsVisibleFromUnit(ASym: TSymbol;
                                             const AFromUnit: string;
                                             AFromClass: TRecordTypeDesc): Boolean;
begin
  { Free (non-member) symbols default to public — the symbol carries no
    per-member visibility, so the uses-chain probe never rejects on this
    path.  Class/record member visibility is enforced at the qualified- and
    unqualified-member access sites via MemberVisibleTo / AssertMemberVisibleV. }
  Result := True;
end;

function TSemanticAnalyser.IsVisibleFromUnit(const AMemberOwningUnit: string;
                                             const AFromUnit: string;
                                             AFromClass: TRecordTypeDesc): Boolean;
begin
  { String-flavor — same rationale as the TSymbol form. }
  Result := True;
end;

function TSemanticAnalyser.MemberVisibleTo(AVisibility: TMemberVisibility;
                                           const ADeclaringUnit, ADeclaringType: string;
                                           const AFromUnit: string;
                                           AFromClass: TRecordTypeDesc): Boolean;
var
  C: TRecordTypeDesc;
begin
  case AVisibility of
    mvPublic, mvPublished:
      Result := True;

    mvPrivate:
      { Unit-scoped: visible to any code in the declaring unit.  A member
        whose declaring unit is unknown (empty) is treated as same-unit —
        program-scope types and pre-visibility imports must not be locked out. }
      Result := (ADeclaringUnit = '') or SameText(ADeclaringUnit, AFromUnit);

    mvProtected:
      begin
        { Same unit OR AFromClass is the declaring type or a descendant of it. }
        Result := (ADeclaringUnit = '') or SameText(ADeclaringUnit, AFromUnit);
        if not Result then
        begin
          C := AFromClass;
          while C <> nil do
          begin
            if SameText(C.Name, ADeclaringType) then
            begin
              Result := True;
              Break;
            end;
            C := C.Parent;
          end;
        end;
      end;

    mvStrictPrivate:
      { Visible only from the declaring TYPE's own methods. }
      Result := (AFromClass <> nil) and SameText(AFromClass.Name, ADeclaringType);

    mvStrictProtected:
      begin
        { Declaring type or any descendant's methods, regardless of unit. }
        Result := False;
        C := AFromClass;
        while C <> nil do
        begin
          if SameText(C.Name, ADeclaringType) then
          begin
            Result := True;
            Break;
          end;
          C := C.Parent;
        end;
      end;
  else
    Result := True;
  end;
end;

procedure TSemanticAnalyser.AssertMemberVisible(const AMemberOwningUnit: string;
                                                AClassContext: TRecordTypeDesc;
                                                const AMemberName: string;
                                                ALine, ACol: Integer);
begin
  { Legacy unit-only assert — no per-member visibility available here, so it
    never rejects.  Retained for call sites that lack the descriptor; the
    visibility-bearing AssertMemberVisibleV does the real enforcement. }
  if not IsVisibleFromUnit(AMemberOwningUnit, FCurrentUnitName, AClassContext) then
    SemanticError(
      Format('Identifier ''%s'' is not accessible from this context',
        [AMemberName]),
      ALine, ACol);
end;

procedure TSemanticAnalyser.EnforceMethodVisible(AMDecl: TObject;
                                                 ALine, ACol: Integer);
var
  M: TMethodDecl;
begin
  if AMDecl = nil then Exit;
  M := TMethodDecl(AMDecl);
  { A constructor is always reachable (you must be able to instantiate the
    type); enforcing visibility on Create would block legitimate construction. }
  if SameText(M.Name, 'Create') then Exit;
  AssertMemberVisibleV(M.Visibility, M.OwningUnit, M.OwnerTypeName,
                       M.Name, ALine, ACol);
end;

procedure TSemanticAnalyser.AssertMemberVisibleV(AVisibility: TMemberVisibility;
                                                 const ADeclaringUnit, ADeclaringType: string;
                                                 const AMemberName: string;
                                                 ALine, ACol: Integer);
begin
  if not MemberVisibleTo(AVisibility, ADeclaringUnit, ADeclaringType,
                         FCurrentUnitName, FCurrentClass) then
    SemanticError(
      Format('''%s'' is not accessible from here', [AMemberName]),
      ALine, ACol);
end;

procedure TSemanticAnalyser.AssertStaticVarVisible(AVisibility: TMemberVisibility;
                                                   const ADeclaringUnit, ADeclaringType: string;
                                                   const AMemberName: string;
                                                   ALine, ACol: Integer);
var
  FromClass: TRecordTypeDesc;
begin
  { Static-var access uses the declaring type of the CURRENT METHOD as the
    "from" class, so a strict-private static var is reachable from its own
    type's STATIC methods too (those leave FCurrentClass nil to suppress
    implicit Self, but FCurrentMethodOwner still names the owner). }
  if FCurrentClass <> nil then
    FromClass := FCurrentClass
  else
    FromClass := FCurrentMethodOwner;
  if not MemberVisibleTo(AVisibility, ADeclaringUnit, ADeclaringType,
                         FCurrentUnitName, FromClass) then
    SemanticError(
      Format('''%s'' is not accessible from here', [AMemberName]),
      ALine, ACol);
end;

procedure TSemanticAnalyser.LinkClassMethodImpls(ABlock: TBlock);
var
  I, J, K:  Integer;
  Decl:     TMethodDecl;
  Key:      string;
  CD:       TMethodDecl;
  Match:    TMethodDecl;
  Grp:      TObjectList;
  ImplSig:  string;
  Par:      TMethodParam;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if Decl.OwnerTypeName = '' then Continue;
    if Decl.OwnerTypeParams <> nil then Continue;  { generic owner — handled by LinkGenericClassMethodImpls }

    { Out-of-line generic METHOD impl (function TUtil.Pick<T>(...)): its params
      reference the method's own <T>, so they cannot be resolved here.  Find the
      in-class generic-method template by Owner.Method and transfer the body
      onto it so InstantiateGenericMethod clones a complete template. }
    if Decl.TypeParams <> nil then
    begin
      Key := Decl.OwnerTypeName + '.' + Decl.Name;
      K   := FGenericMethodTemplates.IndexOf(Key);
      if K < 0 then
        SemanticError(
          Format('Generic method ''%s'' is not declared in class ''%s''',
            [Decl.Name, Decl.OwnerTypeName]),
          Decl.Line, Decl.Col);
      Match := TMethodDecl(FGenericMethodTemplates.Objects[K]);
      if Match.Body <> nil then
        SemanticError(
          Format('Generic method ''%s.%s'' already has an inline body',
            [Decl.OwnerTypeName, Decl.Name]),
          Decl.Line, Decl.Col);
      Match.Body := Decl.Body;
      Decl.Body  := nil;
      Continue;
    end;

    { Resolve impl param types so we can compute its signature for matching. }
    for J := 0 to Decl.Params.Count - 1 do
    begin
      Par              := TMethodParam(Decl.Params.Items[J]);
      Par.ResolvedType := ResolveParamType(Par, Decl.Line, Decl.Col);
    end;
    ImplSig := MangleParamSig(Decl);

    Key   := Decl.OwnerTypeName + '.' + Decl.Name;
    Match := nil;
    Grp   := GroupOf(FMethodGroups, Key);
    if Grp <> nil then
    begin
      { Prefer a declaration owned by the unit whose impl body this is: with
        cross-unit type last-wins the group can also hold a same-named method
        on another used unit's same-named type. }
      for K := 0 to Grp.Count - 1 do
      begin
        CD := TMethodDecl(Grp.Items[K]);
        if (CD.OwningUnit <> '') and (FCurrentUnitName <> '') and
           not SameText(CD.OwningUnit, FCurrentUnitName) then
          Continue;
        if CD.IsOverload then
        begin
          if MangleParamSig(CD) = ImplSig then
          begin
            Match := CD;
            Break;
          end;
        end
        else
        begin
          { Non-overloaded: first (and only) match wins }
          Match := CD;
          Break;
        end;
      end;
      { Fallback: no declaration is owned by the current unit — e.g. a generic
        instance whose template (and method decls) live in another unit.  Match
        by signature regardless of owner, preserving the pre-last-wins behaviour. }
      if Match = nil then
        for K := 0 to Grp.Count - 1 do
        begin
          CD := TMethodDecl(Grp.Items[K]);
          if CD.IsOverload then
          begin
            if MangleParamSig(CD) = ImplSig then
            begin
              Match := CD;
              Break;
            end;
          end
          else
          begin
            Match := CD;
            Break;
          end;
        end;
    end;
    if Match = nil then
      SemanticError(
        Format('Method ''%s'' is not declared in class ''%s''',
          [Decl.Name, Decl.OwnerTypeName]),
        Decl.Line, Decl.Col);
    if Match.Body <> nil then
      SemanticError(
        Format('Method ''%s.%s'' already has an inline body',
          [Decl.OwnerTypeName, Decl.Name]),
        Decl.Line, Decl.Col);
    { Transfer the body; after this, AnalyseMethodBodies will find and analyse it }
    Match.Body := Decl.Body;
    Decl.Body  := nil;
  end;
end;

{ Diagnose class methods that were declared but never implemented.  Must run
  AFTER LinkClassMethodImpls has transferred every matching implementation body
  onto its class method declaration: a concrete (non-abstract, non-external)
  method whose Body is still nil has no implementation, so codegen would emit a
  call to a symbol that is never defined and the program fails at link/load
  time with `undefined symbol: <Class>_<Method>`.  A declared concrete method
  is a promise of an implementation; diagnose the broken promise up front. }
procedure TSemanticAnalyser.CheckClassMethodsImplemented(ABlock: TBlock);
var
  I, J:  Integer;
  TD:    TTypeDecl;
  CD:    TClassTypeDef;
  MDecl: TMethodDecl;
begin
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    CD := TClassTypeDef(TD.Def);
    { A bare forward declaration carries no members; the completing full
      declaration is a separate TypeDecl and is checked on its own. }
    if CD.IsForward then Continue;
    for J := 0 to CD.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(CD.Methods.Items[J]);
      { Abstract methods intentionally have no body; external methods are
        satisfied by a foreign symbol; a generic method template
        (TypeParams <> nil) has its body cloned per instantiation. }
      if MDecl.IsAbstract or MDecl.IsExternal then Continue;
      if MDecl.TypeParams <> nil then Continue;
      if MDecl.Body = nil then
        SemanticError(
          Format('Method ''%s.%s'' declared but not implemented',
            [TD.Name, MDecl.Name]),
          MDecl.Line, MDecl.Col);
    end;
  end;
end;

procedure TSemanticAnalyser.LinkGenericClassMethodImpls(ABlock: TBlock);
var
  I, J: Integer;
  Decl: TMethodDecl;
  GenObj: TObject;
  Methods: TObjectList;
  MDecl: TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if (Decl.OwnerTypeName = '') or (Decl.OwnerTypeParams = nil) then
      Continue;
    { Locate the generic template — may be a class or a record }
    GenObj := FTable.FindGeneric(Decl.OwnerTypeName);
    if GenObj is TGenericTypeDef then
      Methods := TGenericTypeDef(GenObj).ClassDef.Methods
    else if GenObj is TGenericRecordDef then
      Methods := TGenericRecordDef(GenObj).RecordDef.Methods
    else
      begin
        SemanticError(
          Format('Generic type ''%s'' not found for method ''%s''',
            [Decl.OwnerTypeName, Decl.Name]),
          Decl.Line, Decl.Col);
        Methods := nil;
      end;
    if Methods = nil then
      Continue;
    { Find the matching forward declaration in the template }
    MDecl := nil;
    for J := 0 to Methods.Count - 1 do
      if SameText(TMethodDecl(Methods.Items[J]).Name, Decl.Name) then
      begin
        MDecl := TMethodDecl(Methods.Items[J]);
        Break;
      end;
    if MDecl = nil then
      SemanticError(
        Format('Method ''%s'' is not declared in generic type ''%s''',
          [Decl.Name, Decl.OwnerTypeName]),
        Decl.Line, Decl.Col);
    if MDecl.Body <> nil then
      SemanticError(
        Format('Method ''%s.%s'' already has a body',
          [Decl.OwnerTypeName, Decl.Name]),
        Decl.Line, Decl.Col);
    MDecl.Body := Decl.Body;
    Decl.Body  := nil;
  end;
end;

procedure TSemanticAnalyser.FlushPendingGenericInstances;
var
  I: Integer;
begin
  if FCurrentUnit <> nil then
  begin
    for I := 0 to FPendingGenericInstances.Count - 1 do
      FCurrentUnit.GenericInstances.Add(FPendingGenericInstances.Items[I]);
    for I := 0 to FPendingGenericRecordInstances.Count - 1 do
      FCurrentUnit.GenericRecordInstances.Add(
        FPendingGenericRecordInstances.Items[I]);
    for I := 0 to FPendingGenericIntfInstances.Count - 1 do
      FCurrentUnit.GenericIntfInstances.Add(
        FPendingGenericIntfInstances.Items[I]);
  end
  else if FProg <> nil then
  begin
    for I := 0 to FPendingGenericInstances.Count - 1 do
      FProg.GenericInstances.Add(FPendingGenericInstances.Items[I]);
    for I := 0 to FPendingGenericRecordInstances.Count - 1 do
      FProg.GenericRecordInstances.Add(
        FPendingGenericRecordInstances.Items[I]);
    for I := 0 to FPendingGenericIntfInstances.Count - 1 do
      FProg.GenericIntfInstances.Add(
        FPendingGenericIntfInstances.Items[I]);
  end
  else
    Exit;
  FPendingGenericInstances.Clear();
  FPendingGenericRecordInstances.Clear();
  FPendingGenericIntfInstances.Clear();
end;

procedure TSemanticAnalyser.RepairEarlyGenericInstances;
var
  Instances: TObjectList;
  I, J, K, MIdx: Integer;
  GRI:       TGenericRecordInstance;
  GI:        TGenericInstance;
  InstMDecl: TMethodDecl;
  TmplMDecl: TMethodDecl;
  BaseName:  string;
  ArgsStr:   string;
  BracPos:   Integer;
  GenObj:    TObject;
  TmplMethods: TObjectList;
  Args:      TStringList;
  ParamNames: TStringList;
  ConcrType: TTypeDesc;
  Sym:       TSymbol;
  RT:        TRecordTypeDesc;
  RepairedIndices: TStringList;
begin
  Instances := nil;
  if FCurrentUnit <> nil then
    Instances := FCurrentUnit.GenericRecordInstances
  else if FProg <> nil then
    Instances := FProg.GenericRecordInstances;
  if Instances <> nil then
  begin
    for I := 0 to Instances.Count - 1 do
    begin
      GRI := TGenericRecordInstance(Instances.Items[I]);
      BracPos := StrPos('<', GRI.TypeName);
      if BracPos < 0 then Continue;
      BaseName := StrHead(GRI.TypeName, BracPos);
      GenObj := FTable.FindGeneric(BaseName);
      if not (GenObj is TGenericRecordDef) then Continue;
      TmplMethods := TGenericRecordDef(GenObj).RecordDef.Methods;
      RepairedIndices := TStringList.Create();
      try
        for J := 0 to GRI.RecordDef.Methods.Count - 1 do
        begin
          InstMDecl := TMethodDecl(GRI.RecordDef.Methods.Items[J]);
          if InstMDecl.Body <> nil then
            Continue;
          TmplMDecl := nil;
          for K := 0 to TmplMethods.Count - 1 do
            if SameText(TMethodDecl(TmplMethods.Items[K]).Name, InstMDecl.Name) then
            begin
              TmplMDecl := TMethodDecl(TmplMethods.Items[K]);
              Break;
            end;
          if (TmplMDecl <> nil) and (TmplMDecl.Body <> nil) then
          begin
            InstMDecl.Body := CloneBlock(TmplMDecl.Body);
            InstMDecl.OwnBody := True;
            RepairedIndices.Add(IntToStr(J));
          end;
        end;
        if RepairedIndices.Count > 0 then
        begin
          ArgsStr := StrCopyFrom(GRI.TypeName, StrPos('<', GRI.TypeName) + 1,
            Length(GRI.TypeName) - StrPos('<', GRI.TypeName) - 2);
          Args := TStringList.Create();
          try
            while ArgsStr <> '' do
            begin
              BracPos := StrPos(',', ArgsStr);
              if BracPos >= 0 then
              begin
                Args.Add(Trim(StrHead(ArgsStr, BracPos)));
                ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
              end
              else
              begin
                Args.Add(Trim(ArgsStr));
                ArgsStr := '';
              end;
            end;
            ParamNames := TGenericRecordDef(FTable.FindGeneric(BaseName)).ParamNames;
            RT := TRecordTypeDesc(GRI.TypeDesc);
            FTable.PushScope();
            for K := 0 to ParamNames.Count - 1 do
              FActiveTypeParams.Add(ParamNames.Strings[K]);
            try
              for K := 0 to ParamNames.Count - 1 do
              begin
                ConcrType := FindTypeOrInstantiate(Args.Strings[K]);
                if ConcrType <> nil then
                begin
                  Sym := TSymbol.Create(ParamNames.Strings[K], skType, ConcrType);
                  FTable.Define(Sym);
                end;
              end;
              for J := 0 to RepairedIndices.Count - 1 do
              begin
                MIdx := StrToInt(RepairedIndices.Strings[J]);
                InstMDecl := TMethodDecl(GRI.RecordDef.Methods.Items[MIdx]);
                if InstMDecl.Body <> nil then
                  AnalyseMethodDecl(InstMDecl, RT);
              end;
            finally
              for K := 0 to ParamNames.Count - 1 do
                FActiveTypeParams.Delete(FActiveTypeParams.Count - 1);
              FTable.PopScope();
            end;
          finally
            Args.Free();
          end;
        end;
      finally
        RepairedIndices.Free();
      end;
    end;
  end;

  Instances := nil;
  if FCurrentUnit <> nil then
    Instances := FCurrentUnit.GenericInstances
  else if FProg <> nil then
    Instances := FProg.GenericInstances;
  if Instances <> nil then
  begin
    for I := 0 to Instances.Count - 1 do
    begin
      GI := TGenericInstance(Instances.Items[I]);
      BracPos := StrPos('<', GI.TypeName);
      if BracPos < 0 then Continue;
      BaseName := StrHead(GI.TypeName, BracPos);
      GenObj := FTable.FindGeneric(BaseName);
      if not (GenObj is TGenericTypeDef) then Continue;
      TmplMethods := TGenericTypeDef(GenObj).ClassDef.Methods;
      RepairedIndices := TStringList.Create();
      try
        for J := 0 to GI.ClassDef.Methods.Count - 1 do
        begin
          InstMDecl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
          if InstMDecl.Body <> nil then
            Continue;
          TmplMDecl := nil;
          for K := 0 to TmplMethods.Count - 1 do
            if SameText(TMethodDecl(TmplMethods.Items[K]).Name, InstMDecl.Name) then
            begin
              TmplMDecl := TMethodDecl(TmplMethods.Items[K]);
              Break;
            end;
          if (TmplMDecl <> nil) and (TmplMDecl.Body <> nil) then
          begin
            InstMDecl.Body := CloneBlock(TmplMDecl.Body);
            InstMDecl.OwnBody := True;
            RepairedIndices.Add(IntToStr(J));
          end;
        end;
        if RepairedIndices.Count > 0 then
        begin
          ArgsStr := StrCopyFrom(GI.TypeName, StrPos('<', GI.TypeName) + 1,
            Length(GI.TypeName) - StrPos('<', GI.TypeName) - 2);
          Args := TStringList.Create();
          try
            while ArgsStr <> '' do
            begin
              BracPos := StrPos(',', ArgsStr);
              if BracPos >= 0 then
              begin
                Args.Add(Trim(StrHead(ArgsStr, BracPos)));
                ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
              end
              else
              begin
                Args.Add(Trim(ArgsStr));
                ArgsStr := '';
              end;
            end;
            ParamNames := TGenericTypeDef(FTable.FindGeneric(BaseName)).ParamNames;
            RT := TRecordTypeDesc(GI.TypeDesc);
            FTable.PushScope();
            for K := 0 to ParamNames.Count - 1 do
              FActiveTypeParams.Add(ParamNames.Strings[K]);
            try
              for K := 0 to ParamNames.Count - 1 do
              begin
                ConcrType := FindTypeOrInstantiate(Args.Strings[K]);
                if ConcrType <> nil then
                begin
                  Sym := TSymbol.Create(ParamNames.Strings[K], skType, ConcrType);
                  FTable.Define(Sym);
                end;
              end;
              for J := 0 to RepairedIndices.Count - 1 do
              begin
                MIdx := StrToInt(RepairedIndices.Strings[J]);
                InstMDecl := TMethodDecl(GI.ClassDef.Methods.Items[MIdx]);
                if InstMDecl.Body <> nil then
                  AnalyseMethodDecl(InstMDecl, RT);
              end;
            finally
              for K := 0 to ParamNames.Count - 1 do
                FActiveTypeParams.Delete(FActiveTypeParams.Count - 1);
              FTable.PopScope();
            end;
          finally
            Args.Free();
          end;
        end;
      finally
        RepairedIndices.Free();
      end;
    end;
  end;
end;

function TSemanticAnalyser.ResolveScopeBoundTypeParams(const ATypeName: string): string;
var
  BrOpen, BrClose, I: Integer;
  BasePart, ArgsPart, OutArgs, Arg: string;
  ArgList: TStringList;
  Sym: TSymbol;
begin
  Result  := ATypeName;
  BrOpen  := StrPos('<', ATypeName);
  if BrOpen < 0 then Exit;
  BrClose  := Length(ATypeName);
  BasePart := StrHead(ATypeName, BrOpen);
  ArgsPart := StrCopyFrom(ATypeName, BrOpen + 1, BrClose - BrOpen - 2);
  ArgList  := TStringList.Create();
  try
    while ArgsPart <> '' do
    begin
      I := StrPos(',', ArgsPart);
      if I >= 0 then
      begin
        ArgList.Add(Trim(StrHead(ArgsPart, I)));
        ArgsPart := Trim(StrCopyTail(ArgsPart, I + 1));
      end
      else
      begin
        ArgList.Add(Trim(ArgsPart));
        ArgsPart := '';
      end;
    end;
    OutArgs := '';
    for I := 0 to ArgList.Count - 1 do
    begin
      Arg := ArgList.Strings[I];
      { If this arg is a bare ident bound as skType in the current scope,
        replace it with the concrete type name. }
      Sym := FTable.Lookup(Arg);
      if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) then
        Arg := Sym.TypeDesc.Name;
      if OutArgs = '' then
        OutArgs := Arg
      else
        OutArgs := OutArgs + ',' + Arg;
    end;
  finally
    ArgList.Free();
  end;
  Result := BasePart + '<' + OutArgs + '>';
end;

function TSemanticAnalyser.CanonGenericArgs(const ATypeName: string): string;
var
  BrOpen, BrClose, I: Integer;
  BasePart, ArgsPart, OutArgs, Arg: string;
  ArgList: TStringList;
  ArgType: TTypeDesc;
begin
  Result  := ATypeName;
  BrOpen  := StrPos('<', ATypeName);
  if BrOpen < 0 then Exit;
  BrClose  := Length(ATypeName);  { closing '>' is always the last char }
  BasePart := StrHead(ATypeName, BrOpen);
  ArgsPart := StrCopyFrom(ATypeName, BrOpen + 1, BrClose - BrOpen - 2);
  ArgList  := TStringList.Create();
  try
    while ArgsPart <> '' do
    begin
      I := StrPos(',', ArgsPart);
      if I >= 0 then
      begin
        ArgList.Add(Trim(StrHead(ArgsPart, I)));
        ArgsPart := Trim(StrCopyTail(ArgsPart, I + 1));
      end
      else
      begin
        ArgList.Add(Trim(ArgsPart));
        ArgsPart := '';
      end;
    end;
    OutArgs := '';
    for I := 0 to ArgList.Count - 1 do
    begin
      Arg := ArgList.Strings[I];
      { Resolve the argument to its underlying type and use that type's
        canonical name.  A transparent type alias (type TIntAlias = Integer)
        shares the underlying type's descriptor, so its .Name is the
        canonical 'Integer' — collapsing 'Foo<TIntAlias>' and 'Foo<Integer>'
        onto one instantiation.  Leave the argument untouched when it does not
        resolve (e.g. an in-scope generic type parameter T) so substitution
        still applies later. }
      ArgType := FindTypeOrInstantiate(Arg);
      if (ArgType <> nil) and (ArgType.Name <> '') and
         (not SameText(ArgType.Name, Arg)) then
        Arg := ArgType.Name;
      if OutArgs = '' then
        OutArgs := Arg
      else
        OutArgs := OutArgs + ',' + Arg;
    end;
  finally
    ArgList.Free();
  end;
  Result := BasePart + '<' + OutArgs + '>';
end;

function TSemanticAnalyser.SynthAnonEnum(const AMemberList: string): TEnumTypeDesc;
{ Synthesise (or reuse) an enum type from an inline member list encoded as
  '(a,b,c)'.  Members become skConstant symbols, exactly as a named enum's do.
  If the members are already defined (the same inline enum resolved earlier, or
  a clashing identifier), the existing enum is reused when it matches, otherwise
  a duplicate-identifier error is raised — mirroring named-enum semantics. }
var
  Inner:   string;
  Members: TStringList;
  EnumName: string;
  Cand:    TEnumTypeDesc;
  Matches: Boolean;
  K, CPos, IxI: Integer;
begin
  { Strip the surrounding parentheses and split on commas. }
  Inner := AMemberList;
  if (Length(Inner) >= 2) and (StrAt(Inner, 0) = Ord('(')) then
    Inner := StrCopyFrom(Inner, 1, Length(Inner) - 2);
  Members := TStringList.Create();
  try
    while Inner <> '' do
    begin
      CPos := StrPos(',', Inner);
      if CPos < 0 then
      begin
        Members.Add(Inner);
        Inner := '';
      end
      else
      begin
        Members.Add(StrHead(Inner, CPos));
        Inner := StrCopyTail(Inner, CPos + 1);
      end;
    end;
    if Members.Count = 0 then
      SemanticError('Empty anonymous enumeration in set type', 0, 0);
    if Members.Count > 256 then
      SemanticError(Format(
        'Anonymous enumeration has %d members; set types support at most 256',
        [Members.Count]), 0, 0);
    { Reuse an already-synthesised identical enum: scan the reverse index for an
      enum (named or anonymous) whose member list matches exactly, so the same
      inline `set of (a,b,c)` written twice yields one compatible set type.
      Sharing a member name with an unrelated enum is no longer a collision. }
    for IxI := 0 to FEnumMemberIndex.Count - 1 do
    begin
      if not SameText(FEnumMemberIndex.Strings[IxI], Members.Strings[0]) then
        Continue;
      Cand := TEnumMemberRef(FEnumMemberIndex.Objects[IxI]).EnumDesc;
      if Cand.Members.Count <> Members.Count then Continue;
      Matches := True;
      for K := 0 to Members.Count - 1 do
        if not SameText(Cand.Members.Strings[K], Members.Strings[K]) then
        begin
          Matches := False;
          Break;
        end;
      if Matches then
        Exit(Cand);
    end;
    Inc(FAnonEnumCounter);
    EnumName := Format('$anonenum_%d', [FAnonEnumCounter]);
    Result := FTable.NewEnumType(EnumName);
    for K := 0 to Members.Count - 1 do
    begin
      { Inline anon enums carry no explicit-ordinal syntax (the encoded list is
        just names), so the ordinal is the position K. }
      Result.AddMember(Members.Strings[K], K);
      RegisterEnumMember(Members.Strings[K], Result, K);
    end;
    FTable.DefineGlobal(TSymbol.Create(EnumName, skType, Result));
  finally
    Members.Free();
  end;
end;

function TSemanticAnalyser.FindTypeOrInstantiate(const AName: string): TTypeDesc;
var
  BaseName: string;
  BaseType: TTypeDesc;
  PT:       TPointerTypeDesc;
  Sym:      TSymbol;
  DDotPos, RBrPos, OfPos: Integer;
  LStr, HStr, ElemName, IdxName: string;
  CanonName: string;
  LVal, HVal: Integer;
  IdxTD: TTypeDesc;
  EnumDesc: TEnumTypeDesc;
  SAT: TStaticArrayTypeDesc;
  DAT: TDynArrayTypeDesc;
  I, LtPos, DotPos: Integer;
begin
  { Unit-qualified type 'Unit.TypeName' — resolve against that specific unit's
    own exports FIRST, before the flat FindType below (which strips the
    qualifier and binds the tail through the uses chain, i.e. to the cross-unit
    last-wins winner).  Only short-circuits on a directed hit; a miss (the
    common single-definition case, or a dotted stdlib qualifier the per-unit
    cache has not harvested) falls through to the existing resolution. }
  LtPos := StrPos('<', AName);
  if LtPos < 0 then LtPos := Length(AName);
  DotPos := -1;
  for I := 0 to LtPos - 1 do
    if StrAt(AName, I) = Ord('.') then DotPos := I;
  if DotPos >= 0 then
  begin
    Sym := ResolveQualified(Copy(AName, 0, DotPos),
                            StrCopyTail(AName, DotPos + 1));
    if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) then
      Exit(Sym.TypeDesc);
  end;
  Result := FTable.FindType(AName);
  if Result <> nil then Exit;
  { Dynamic array: 'array of TypeName' — create on demand.  Key cache by
    the canonical element-type name so 'array of T' under T=String and
    T=TObject do not collide. }
  if (Length(AName) > 9) and (StrHead(AName, 9) = 'array of ') then
  begin
    ElemName := StrCopyTail(AName, 9);
    BaseType := FindTypeOrInstantiate(ElemName);
    if BaseType <> nil then
    begin
      CanonName := 'array of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        DAT := FTable.NewDynArrayType(BaseType);
        Sym := TSymbol.Create(CanonName, skType, DAT);
        FTable.DefineGlobal(Sym);
        Result := DAT;
      end;
    end;
    Exit;
  end;
  { Ordinal-indexed static array: 'array[@TEnum] of TypeName'.  A single bare
    ordinal marker only — an enum-typed multi-dim dimension is encoded as a
    range 'array[@L:TEnum..@H:TEnum]' (GH #182) and must fall through to the
    range-indexed 'array[L..H]' branch below.  The '..'-absence test is scoped
    to the INDEX brackets (StrHead up to the first ']'), because the ELEMENT
    type may legitimately contain '..' — e.g. 'array[@TEnum] of array[0..1]',
    the nested form, must still take THIS single-dim ordinal branch. }
  if (Length(AName) > 8) and (StrHead(AName, 7) = 'array[@') and
     (StrPos('..', StrHead(AName, StrPos(']', AName))) < 0) then
  begin
    RBrPos   := StrPos(']', AName);
    OfPos    := StrPos(' of ', AName);
    IdxName  := StrCopyFrom(AName, 7, RBrPos - 7);
    ElemName := StrCopyTail(AName, OfPos + 4);
    IdxTD    := FTable.FindType(IdxName);
    BaseType := FindTypeOrInstantiate(ElemName);
    if (IdxTD <> nil) and (IdxTD.Kind = tyEnum) and (not IdxTD.IsSubrange) and
       (BaseType <> nil) then
    begin
      { A full enum index (array[TEnum] of T) spans 0..N-1.  An ENUM-SUBRANGE
        index (IsSubrange) is NOT full-range — it falls through to the subrange
        branch below, which uses the subrange's own ordinal bounds (GH #182). }
      EnumDesc := TEnumTypeDesc(IdxTD);
      HVal     := EnumDesc.Members.Count - 1;
      CanonName := Format('array[0..%d] of %s', [HVal, BaseType.Name]);
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        SAT := FTable.NewStaticArrayType(BaseType, 0, HVal);
        Sym := TSymbol.Create(CanonName, skType, SAT);
        FTable.DefineGlobal(Sym);
        Result := SAT;
      end;
    end
    else if (IdxTD <> nil) and (IdxTD.Kind = tyBoolean) and (BaseType <> nil) then
    begin
      { Boolean index (array[Boolean] of T): a 2-element ordinal indexed by
        False (0) and True (1).  Fold to array[0..1] of T, parallel to the
        enum branch (GH #181). }
      CanonName := Format('array[0..1] of %s', [BaseType.Name]);
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        SAT := FTable.NewStaticArrayType(BaseType, 0, 1);
        Sym := TSymbol.Create(CanonName, skType, SAT);
        FTable.DefineGlobal(Sym);
        Result := SAT;
      end;
    end
    else if (IdxTD <> nil) and IdxTD.IsSubrange and (BaseType <> nil) then
    begin
      { Named integer subrange index (type TIdx = lo..hi; array[TIdx] of T):
        the subrange supplies the index range; fold to array[lo..hi] of T,
        exactly parallel to the enum branch's array[0..N-1]. }
      LVal := IdxTD.SubrangeLow;
      HVal := IdxTD.SubrangeHigh;
      CanonName := Format('array[%d..%d] of %s', [LVal, HVal, BaseType.Name]);
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        SAT := FTable.NewStaticArrayType(BaseType, LVal, HVal);
        Sym := TSymbol.Create(CanonName, skType, SAT);
        FTable.DefineGlobal(Sym);
        Result := SAT;
      end;
    end
    else if IdxTD = nil then
      SemanticError(Format('Unknown index type ''%s''', [IdxName]), 0, 0)
    else if (IdxTD.Kind <> tyEnum) and (IdxTD.Kind <> tyBoolean) and
            (not IdxTD.IsSubrange) then
      SemanticError(Format(
        '''%s'' is not a valid array index type (expected an enumeration, '
        + 'Boolean, or an integer subrange)', [IdxName]), 0, 0);
    Exit;
  end;
  { Range-indexed static array: 'array[L..H] of TypeName' — create on demand.
    L and H may be integer literals, named constants, or constant
    expressions (e.g. N-1).  ResolveArrayBound folds them to integers. }
  if (Length(AName) > 6) and (StrHead(AName, 6) = 'array[') then
  begin
    DDotPos  := StrPos('..', AName);
    RBrPos   := StrPos(']', AName);
    OfPos    := StrPos(' of ', AName);
    LStr     := StrCopyFrom(AName, 6, DDotPos - 6);
    HStr     := StrCopyFrom(AName, DDotPos + 2, RBrPos - DDotPos - 2);
    ElemName := StrCopyTail(AName, OfPos + 4);
    BaseType := FindTypeOrInstantiate(ElemName);
    if BaseType <> nil then
    begin
      LVal := ResolveArrayBound(LStr);
      HVal := ResolveArrayBound(HStr);
      CanonName := Format('array[%d..%d] of %s', [LVal, HVal, BaseType.Name]);
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        SAT := FTable.NewStaticArrayType(BaseType, LVal, HVal);
        Sym := TSymbol.Create(CanonName, skType, SAT);
        FTable.DefineGlobal(Sym);
        Result := SAT;
      end;
    end;
    Exit;
  end;
  { Typed pointer: '^TypeName' — create on demand.  When TypeName resolves
    to a concrete type (e.g. T → String inside a generic method body), key
    the cache by the canonical '^String' rather than the unsubstituted
    '^T' — otherwise a second instantiation that binds T to a different
    concrete type re-uses the stale '^T' → '^String' entry. }
  if (Length(AName) > 1) and (StrAt(AName, 0) = Ord('^')) then
  begin
    BaseName := StrCopyTail(AName, 1);
    BaseType := FindTypeOrInstantiate(BaseName);
    if BaseType <> nil then
    begin
      CanonName := '^' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        PT  := FTable.NewPointerType(CanonName, BaseType);
        Sym := TSymbol.Create(CanonName, skType, PT);
        FTable.DefineGlobal(Sym);
        Result := PT;
      end;
    end;
    Exit;
  end;
  { Metaclass: 'class of TypeName' — create on demand. }
  if (Length(AName) > 9) and (StrHead(AName, 9) = 'class of ') then
  begin
    BaseName := StrCopyTail(AName, 9);
    BaseType := FindTypeOrInstantiate(BaseName);
    if (BaseType <> nil) and (BaseType.Kind = tyClass) then
    begin
      CanonName := 'class of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        Sym := TSymbol.Create(CanonName, skType,
          FTable.NewMetaClassType(CanonName, BaseType));
        FTable.DefineGlobal(Sym);
        Result := Sym.TypeDesc;
      end;
    end;
    Exit;
  end;
  { Inline set type: 'set of TypeName' — create on demand.  The element type
    must be an enum (up to 256 members) or a small ordinal type (Byte,
    Boolean).  The canonical name 'set of <Base>' matches the inferred-set-
    constant path, so identical inline and named sets share one descriptor
    (set types compare structurally regardless). }
  if (Length(AName) > 7) and (StrHead(AName, 7) = 'set of ') then
  begin
    BaseName := StrCopyTail(AName, 7);
    { Integer-subrange base type 'set of lo..hi' (e.g. set of 0..255).  Like
      Delphi/FPC, the element ordinals are the integer values themselves and the
      type is capped at 256 elements (ordinals 0..255).  Resolve and validate
      the bounds, then build an ordinal set sized by the high bound — reusing the
      same Byte-set machinery (bits 0..hi). }
    if StrPos('..', BaseName) >= 0 then
    begin
      Result := Self.ResolveSubrangeSetType(BaseName);
      Exit;
    end;
    { Anonymous enum element 'set of (a,b,c)' — synthesise the enum from the
      encoded member list; otherwise resolve a named element type. }
    if (BaseName <> '') and (StrAt(BaseName, 0) = Ord('(')) then
      BaseType := Self.SynthAnonEnum(BaseName)
    else
      BaseType := FindTypeOrInstantiate(BaseName);
    if (BaseType <> nil) and (BaseType.Kind = tyEnum) then
    begin
      if TEnumTypeDesc(BaseType).Members.Count > 256 then
        SemanticError(Format(
          'Enumeration ''%s'' has %d members; set types support at most 256',
          [BaseType.Name, TEnumTypeDesc(BaseType).Members.Count]), 0, 0);
      CanonName := 'set of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        Result := FTable.NewSetType(CanonName, TEnumTypeDesc(BaseType));
        FTable.DefineGlobal(TSymbol.Create(CanonName, skType, Result));
      end;
    end
    else if (BaseType <> nil) and (BaseType.Kind = tyByte) then
    begin
      CanonName := 'set of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        Result := FTable.NewOrdinalSetType(CanonName, BaseType, 256);
        FTable.DefineGlobal(TSymbol.Create(CanonName, skType, Result));
      end;
    end
    else if (BaseType <> nil) and (BaseType.Kind = tyBoolean) then
    begin
      CanonName := 'set of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        Result := FTable.NewOrdinalSetType(CanonName, BaseType, 2);
        FTable.DefineGlobal(TSymbol.Create(CanonName, skType, Result));
      end;
    end
    else if BaseType <> nil then
      SemanticError(Format(
        'Set base type ''%s'' must be an enumeration, Byte, or Boolean',
        [BaseType.Name]), 0, 0);
    Exit;
  end;
  { Qualified type name 'UnitName.TypeName' — the unit qualifier may itself be
    dotted (System.SysUtils.TFormatSettings).  A type is a single identifier,
    so strip everything up to the final '.' that precedes any generic '<...>'
    argument list and resolve the tail via the normal uses chain (the qualifier
    names the unit, already loaded by the 'uses' clause).  A qualified generic
    instance (Unit.TList<Integer>) reduces to the bare 'TList<Integer>', which
    the generic branch above instantiates. }
  LtPos := StrPos('<', AName);
  if LtPos < 0 then
    LtPos := Length(AName);
  DotPos := -1;
  for I := 0 to LtPos - 1 do
    if StrAt(AName, I) = Ord('.') then
      DotPos := I;
  if DotPos >= 0 then
  begin
    { Unit-qualified type 'Unit.TypeName' — directed lookup against that
      unit's own exports first, so two units declaring the same type name
      are disambiguated.  Falls back to bare-tail resolution via the uses
      chain when that unit's per-unit cache has no such type (covers dotted
      stdlib qualifiers like System.SysUtils.TFoo whose iface key differs
      from the dotted prefix, and qualified generic instances). }
    Sym := ResolveQualified(Copy(AName, 0, DotPos),
                            StrCopyTail(AName, DotPos + 1));
    if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) then
      Exit(Sym.TypeDesc);
    Result := FindTypeOrInstantiate(StrCopyTail(AName, DotPos + 1));
    Exit;
  end;
  if StrPos('<', AName) >= 0 then
  begin
    { Canonicalise type-alias arguments to their underlying type's name so a
      generic instantiated with a transparent alias (Foo<TIntAlias>) shares one
      identity with the underlying-type form (Foo<Integer>).  Re-check the
      table under the canonical name before instantiating. }
    CanonName := CanonGenericArgs(AName);
    if not SameText(CanonName, AName) then
    begin
      Result := FTable.FindType(CanonName);
      if Result <> nil then Exit;
    end;
    Result := InstantiateGeneric(CanonName);
    if Result = nil then
      Result := InstantiateGenericRecord(CanonName);
    if Result = nil then
      Result := InstantiateGenericInterface(CanonName);
    if Result = nil then
      Result := InstantiateGenericProcType(CanonName);
  end;
end;

function TSemanticAnalyser.ResolveParamType(APar: TMethodParam;
  ALoc: Integer; ACol: Integer): TTypeDesc;
var
  ElemType: TTypeDesc;
begin
  if APar.IsOpenArray then
  begin
    ElemType := FindTypeOrInstantiate(APar.TypeName);
    if ElemType = nil then
      SemanticError(
        Format('Unknown element type ''%s'' in open-array parameter ''%s''',
          [APar.TypeName, APar.ParamName]),
        ALoc, ACol);
    Result := FTable.NewOpenArrayType(ElemType);
  end
  else
  begin
    Result := FindTypeOrInstantiate(APar.TypeName);
    if Result = nil then
      SemanticError(
        Format('Unknown type ''%s'' for parameter ''%s''',
          [APar.TypeName, APar.ParamName]),
        ALoc, ACol);
  end;
end;

function TSemanticAnalyser.SubstTypeParam(const ATypeName: string;
  AParamNames, AArgs: TStringList): string;
var
  I, BrOpen, BrClose: Integer;
  BasePart, ArgsPart, OutArgs, Arg: string;
  ArgList: TStringList;
begin
  Result := ATypeName;
  { Direct match: T → Integer }
  for I := 0 to AParamNames.Count - 1 do
    if SameText(Result, AParamNames.Strings[I]) then
    begin
      Exit(AArgs.Strings[I]);
    end;
  { Prefix caret: ^T → ^Integer, ^^T → ^^Integer, etc. }
  if (Length(Result) > 0) and (StrAt(Result, 0) = Ord('^')) then
  begin
    Exit('^' + Self.SubstTypeParam(StrCopyTail(Result, 1), AParamNames, AArgs));
  end;
  { Generic instantiation: SomeName<T,...> — substitute each type argument }
  BrOpen := StrPos('<', Result);
  if BrOpen >= 0 then
  begin
    BrClose  := Length(Result);  { closing '>' is always the last char }
    BasePart := StrHead(Result, BrOpen);
    ArgsPart := StrCopyFrom(Result, BrOpen + 1, BrClose - BrOpen - 2);
    ArgList  := TStringList.Create();
    try
      while ArgsPart <> '' do
      begin
        I := StrPos(',', ArgsPart);
        if I >= 0 then
        begin
          ArgList.Add(Trim(StrHead(ArgsPart, I)));
          ArgsPart := Trim(StrCopyTail(ArgsPart, I + 1));
        end
        else
        begin
          ArgList.Add(Trim(ArgsPart));
          ArgsPart := '';
        end;
      end;
      OutArgs := '';
      for I := 0 to ArgList.Count - 1 do
      begin
        Arg := Self.SubstTypeParam(ArgList.Strings[I], AParamNames, AArgs);
        if OutArgs = '' then
          OutArgs := Arg
        else
          OutArgs := OutArgs + ',' + Arg;
      end;
    finally
      ArgList.Free();
    end;
    Result := BasePart + '<' + OutArgs + '>';
  end;
end;

function TSemanticAnalyser.InstantiateGeneric(const ATypeName: string): TRecordTypeDesc;
var
  BracPos:  Integer;
  BaseName: string;
  ArgsStr:  string;
  Args:     TStringList;
  Templ:    TGenericTypeDef;
  ClonedCD: TClassTypeDef;
  I, J, K:  Integer;
  FDecl:    TFieldDecl;
  NewFDecl: TFieldDecl;
  MDecl:    TMethodDecl;
  NewMDecl: TMethodDecl;
  Par:      TMethodParam;
  NewPar:   TMethodParam;
  PDecl:    TPropertyDecl;
  NewPDecl: TPropertyDecl;
  Sym:      TSymbol;
  Key:      string;
  FldType:  TTypeDesc;
  FldName:  string;
  ParType:  TTypeDesc;
  PropType: TTypeDesc;
  PropInfo: TPropertyInfo;
  RT:       TRecordTypeDesc;
  GI:        TGenericInstance;
  Subst:     string;
  ConcrType: TTypeDesc;
  IntfDesc:  TInterfaceTypeDesc;
  ParentSym: TSymbol;
  ParentRT:  TRecordTypeDesc;
  FldInfo:   TFieldInfo;
  DeferBodies: Boolean;
begin
  Result := nil;
  { No program/unit context yet (ImportUnitInterface resolving a cached
    iface's generic-instance field type).  Build the type descriptor +
    fields now, but leave method bodies nil and park the instance — once
    Analyse/AnalyseUnit sets a context, RepairEarlyGenericInstances clones
    and analyses the bodies.  Analysing them here would deref nil FProg/
    FCurrentUnit deep in the body walk. }
  DeferBodies := (FProg = nil) and (FCurrentUnit = nil);

  { Parse 'BaseName<Arg1,Arg2>' }
  BracPos := StrPos('<', ATypeName);
  if BracPos < 0 then Exit;
  BaseName := StrHead(ATypeName, BracPos);
  ArgsStr  := StrCopyFrom(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 2);

  Args := TStringList.Create();
  try
    while ArgsStr <> '' do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    { Bail if the template exists but is a generic interface, not a class }
    if not (FTable.FindGeneric(BaseName) is TGenericTypeDef) then Exit;
    Templ := TGenericTypeDef(FTable.FindGeneric(BaseName));
    if Templ = nil then Exit;
    if Args.Count <> Templ.ParamNames.Count then Exit;

    { Validate each type argument against its declared constraint. }
    for I := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (I < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Strings[I], Args.Strings[I],
          Templ.ParamConstraints.Strings[I],
          Format('instantiation ''%s''', [ATypeName]));

    { Create the concrete class type descriptor — defined globally so the
      symbol survives scope pops and is visible after analysis completes. }
    RT  := FTable.NewClassType(ATypeName);
    Sym := TSymbol.Create(ATypeName, skType, RT);
    FTable.DefineGlobal(Sym);

    { Build substituted clone of the class definition }
    ClonedCD            := TClassTypeDef.Create();
    ClonedCD.ParentName := SubstTypeParam(Templ.ClassDef.ParentName, Templ.ParamNames, Args);
    { The first heritage entry (class(X)) is parsed into ParentName regardless of
      whether X is a class or an interface.  If it resolves to an interface —
      generic (IFoo<T>) or plain (IVal) — move it to ImplementsNames so the
      implements-wiring pass calls AddImplements on RT; otherwise it stays as the
      parent class.  Earlier this only handled the generic ('<') case, so a
      generic class implementing a NON-generic interface (TBox<T> = class(IVal))
      lost its interface and could not be assigned to an interface variable. }
    if ClonedCD.ParentName <> '' then
    begin
      FldType := FindTypeOrInstantiate(ClonedCD.ParentName);
      if (FldType <> nil) and (FldType.Kind = tyInterface) then
      begin
        ClonedCD.ImplementsNames.Insert(0, ClonedCD.ParentName);
        ClonedCD.ParentName := '';
      end;
    end;
    for I := 0 to Templ.ClassDef.ImplementsNames.Count - 1 do
      ClonedCD.ImplementsNames.Add(
        SubstTypeParam(Templ.ClassDef.ImplementsNames.Strings[I], Templ.ParamNames, Args));

    { Clone fields with type-param substitution (handles ^T → ^Integer etc.) }
    for I := 0 to Templ.ClassDef.Fields.Count - 1 do
    begin
      FDecl    := TFieldDecl(Templ.ClassDef.Fields.Items[I]);
      NewFDecl := TFieldDecl.Create();
      for J := 0 to FDecl.Names.Count - 1 do
        NewFDecl.Names.Add(FDecl.Names.Strings[J]);
      NewFDecl.TypeName := SubstTypeParam(FDecl.TypeName, Templ.ParamNames, Args);
      NewFDecl.Visibility := FDecl.Visibility;
      ClonedCD.Fields.Add(NewFDecl);
    end;

    { Clone method declarations.  Body is deep-cloned so each generic
      instance has its own AST nodes for semantic re-analysis; without this
      the Resolved* annotations on the shared body would carry whichever
      instance was analysed last, causing call targets in instance N's
      method body to resolve against instance M's class. }
    for I := 0 to Templ.ClassDef.Methods.Count - 1 do
    begin
      MDecl            := TMethodDecl(Templ.ClassDef.Methods.Items[I]);
      NewMDecl         := TMethodDecl.Create();
      NewMDecl.Name          := MDecl.Name;
      NewMDecl.OwnerTypeName := ATypeName;
      NewMDecl.IsVirtual     := MDecl.IsVirtual;
      NewMDecl.IsOverride    := MDecl.IsOverride;
      NewMDecl.Visibility    := MDecl.Visibility;
      { A generic METHOD on a generic class (TBox<T>.MapTo<R>) keeps its own
        type-parameter list through class instantiation — the class's T is
        substituted here, the method's R only when a call site instantiates
        via InstantiateGenericMethod (Phase 10 gate). }
      if MDecl.TypeParams <> nil then
      begin
        NewMDecl.TypeParams := TStringList.Create();
        NewMDecl.TypeParams.AddStrings(MDecl.TypeParams);
      end;
      if (MDecl.Body <> nil) and (not DeferBodies) then
      begin
        NewMDecl.Body    := CloneBlock(MDecl.Body);
        NewMDecl.OwnBody := True;
      end
      else
      begin
        { Body left nil — either the template is signature-only, or we are
          deferring body analysis to RepairEarlyGenericInstances (which only
          repairs methods whose Body is still nil). }
        NewMDecl.Body    := nil;
        NewMDecl.OwnBody := False;
      end;

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par    := TMethodParam(MDecl.Params.Items[J]);
        NewPar := TMethodParam.Create();
        NewPar.ParamName  := Par.ParamName;
        { Every passing-mode flag must survive monomorphisation — dropping
          IsConstParam made `const AKey: K` a BY-VALUE param, so the callee
          retained/released a key it only borrows.  For a refcount-0
          transient argument that pair frees the caller's string. }
        NewPar.IsVarParam   := Par.IsVarParam;
        NewPar.IsConstParam := Par.IsConstParam;
        NewPar.IsOutParam   := Par.IsOutParam;
        NewPar.IsOpenArray  := Par.IsOpenArray;
        NewPar.HasDefault   := Par.HasDefault;
        NewPar.DefaultValue := CloneExpr(Par.DefaultValue);
        NewPar.TypeName   := SubstTypeParam(Par.TypeName, Templ.ParamNames, Args);
        NewMDecl.Params.Add(NewPar);
      end;

      NewMDecl.ReturnTypeName :=
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args);

      ClonedCD.Methods.Add(NewMDecl);
    end;

    { Clone property declarations with type-param substitution }
    for I := 0 to Templ.ClassDef.Properties.Count - 1 do
    begin
      PDecl    := TPropertyDecl(Templ.ClassDef.Properties.Items[I]);
      NewPDecl := TPropertyDecl.Create();
      NewPDecl.Name           := PDecl.Name;
      NewPDecl.TypeName       := SubstTypeParam(PDecl.TypeName, Templ.ParamNames, Args);
      NewPDecl.ReadName       := PDecl.ReadName;
      NewPDecl.WriteName      := PDecl.WriteName;
      NewPDecl.IndexParamName := PDecl.IndexParamName;
      NewPDecl.IndexTypeName  := SubstTypeParam(PDecl.IndexTypeName, Templ.ParamNames, Args);
      NewPDecl.IsDefault      := PDecl.IsDefault;
      NewPDecl.Visibility     := PDecl.Visibility;
      ClonedCD.Properties.Add(NewPDecl);
    end;

    { Wire up parent class so the generic instance is a first-class class:
      - inherits parent fields (FindField walks them after AddField copies)
      - inherits parent vtable slots (Destroy/ToString from TObject, etc.)
      - has a valid RT.Parent chain (FindProperty/FindMethodDecl walk it)
      Mirrors the regular class resolution path in AnalyseProgramTypes.
      If no explicit parent name, implicitly inherit from TObject. }
    if ClonedCD.ParentName <> '' then
    begin
      ParentSym := FTable.Lookup(ClonedCD.ParentName);
      if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
      begin
        ParentRT  := TRecordTypeDesc(ParentSym.TypeDesc);
        RT.Parent := ParentRT;
        RT.CopyVTableFrom(ParentRT);
        for K := 0 to ParentRT.Fields.Count - 1 do
        begin
          FldInfo := TFieldInfo(ParentRT.Fields.Items[K]);
          RT.AddField(FldInfo.Name, FldInfo.TypeDesc);
          RT.FindField(FldInfo.Name).IsUnretained := FldInfo.IsUnretained;
          RT.FindField(FldInfo.Name).IsWeak       := FldInfo.IsWeak;
          RT.FindField(FldInfo.Name).Visibility    := FldInfo.Visibility;
          RT.FindField(FldInfo.Name).DeclaringUnit := FldInfo.DeclaringUnit;
          RT.FindField(FldInfo.Name).DeclaringType := FldInfo.DeclaringType;
        end;
      end;
    end
    else if not SameText(ATypeName, 'TObject') then
    begin
      ParentSym := FTable.Lookup('TObject');
      if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
      begin
        ParentRT  := TRecordTypeDesc(ParentSym.TypeDesc);
        RT.Parent := ParentRT;
        RT.CopyVTableFrom(ParentRT);
      end;
    end;

    { Pre-pass: vtable slots (before fields so vptr is counted in offsets).
      Generic-instance symbols are ALWAYS bare (no unit prefix): the same
      instance can be materialised by any compilation process, so its symbols
      must be process- and unit-independent.  Per-unit codegen emits them as
      WEAK symbols so multiple objects may carry the copy and the linker
      dedups (BUGS.md BUG-004). }
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods.Items[J]);
      if NewMDecl.TypeParams <> nil then Continue;  { generic method — no slot }
      if NewMDecl.IsVirtual then
        RT.AddVTableSlot(NewMDecl.Name, '$' + ATypeName + '_' + NewMDecl.Name)
      else if NewMDecl.IsOverride then
        RT.OverrideVTableSlot(
          RT.FindVTableSlot(NewMDecl.Name),
          '$' + ATypeName + '_' + NewMDecl.Name)
      else if (SameText(NewMDecl.Name, 'Create') or
               (StrPos('Create', NewMDecl.Name) = 0)) and
              (not NewMDecl.IsVirtual) and (not NewMDecl.IsOverride) then
      begin
        if RT.FindVTableSlot(NewMDecl.Name) >= 0 then
          RT.OverrideVTableSlot(RT.FindVTableSlot(NewMDecl.Name),
            '$' + ATypeName + '_' + NewMDecl.Name)
        else
          RT.AddVTableSlot(NewMDecl.Name, '$' + ATypeName + '_' + NewMDecl.Name);
      end;
    end;

    { Resolve fields }
    for J := 0 to ClonedCD.Fields.Count - 1 do
    begin
      NewFDecl := TFieldDecl(ClonedCD.Fields.Items[J]);
      FldType  := FindTypeOrInstantiate(NewFDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field in ''%s''', [NewFDecl.TypeName, ATypeName]),
          0, 0);
      NewFDecl.ResolvedType := FldType;
      for K := 0 to NewFDecl.Names.Count - 1 do
      begin
        FldName := NewFDecl.Names.Strings[K];
        RT.AddField(FldName, FldType);
        RT.FindField(FldName).Visibility    := NewFDecl.Visibility;
        RT.FindField(FldName).DeclaringUnit := FCurrentUnitName;
        RT.FindField(FldName).DeclaringType := ATypeName;
      end;
    end;

    { Resolve method signatures and index them }
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods.Items[J]);
      { A generic method's signature references its OWN type params (R) —
        resolution happens per call-site instantiation; AnalyseMethodDecl
        registers the template below. }
      if NewMDecl.TypeParams <> nil then Continue;
      Key      := ATypeName + '.' + NewMDecl.Name;
      FMethodIndex.AddObject(Key, NewMDecl);
      AddGroupEntry(FMethodGroups, Key, NewMDecl);
      { Pin the QBE symbol now so the def and call sites agree.  The
        instance's type symbol inherits OwningUnit from the analysing
        compilation (program/unit name) via DefineGlobal's auto-tag;
        the emit name itself is BARE — never unit-prefixed — because the
        same instance is materialised independently by every compilation
        process that touches it, and all of them must agree on one symbol
        (per-unit codegen emits it WEAK so the linker dedups; BUG-004). }
      NewMDecl.OwningUnit     := Sym.OwningUnit;
      NewMDecl.ResolvedQbeName := ATypeName + '_' + NewMDecl.Name;
      if SameText(NewMDecl.Name, 'Destroy') then
      begin
        RT.HasDestroyMethod := True;
        { Pin the destructor's emit name to the same prefix the method def
          uses, so $_FieldCleanup_<T> calls the symbol that actually exists.
          Without this the cleanup falls back to ClassUnitPrefix(), which can
          disagree with the method's ResolvedQbeName for program-scope
          generics and produce an undefined-reference link error. }
        if NewMDecl.Params.Count = 0 then
          RT.DestroyResolvedQbeName := NewMDecl.ResolvedQbeName;
      end;

      if NewMDecl.IsVirtual or NewMDecl.IsOverride or
         (SameText(NewMDecl.Name, 'Create') or (StrPos('Create', NewMDecl.Name) = 0)) then
        NewMDecl.VTableSlot := RT.FindVTableSlot(NewMDecl.Name);

      for K := 0 to NewMDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(NewMDecl.Params.Items[K]);
        ParType := FindTypeOrInstantiate(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for param ''%s'' in ''%s''',
              [Par.TypeName, Par.ParamName, ATypeName]),
            0, 0);
        Par.ResolvedType := ParType;
      end;

      if NewMDecl.ReturnTypeName <> '' then
      begin
        ParType := FindTypeOrInstantiate(NewMDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for method ''%s'' in ''%s''',
              [NewMDecl.ReturnTypeName, NewMDecl.Name, ATypeName]),
            0, 0);
        NewMDecl.ResolvedReturnType := ParType;
      end;
    end;

    { Resolve property declarations — type-param already substituted in clone pass }
    for J := 0 to ClonedCD.Properties.Count - 1 do
    begin
      NewPDecl := TPropertyDecl(ClonedCD.Properties.Items[J]);
      PropType := FindTypeOrInstantiate(NewPDecl.TypeName);
      if PropType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for property ''%s'' in ''%s''',
            [NewPDecl.TypeName, NewPDecl.Name, ATypeName]),
          0, 0);
      PropInfo := TPropertyInfo.Create();
      PropInfo.Name := NewPDecl.Name;
      PropInfo.TypeDesc := PropType;
      if NewPDecl.ReadName <> '' then
      begin
        if RT.FindField(NewPDecl.ReadName) <> nil then
          PropInfo.ReadField := NewPDecl.ReadName
        else
          PropInfo.ReadMethod := NewPDecl.ReadName;
      end;
      if NewPDecl.WriteName <> '' then
      begin
        if RT.FindField(NewPDecl.WriteName) <> nil then
          PropInfo.WriteField := NewPDecl.WriteName
        else
          PropInfo.WriteMethod := NewPDecl.WriteName;
      end;
      PropInfo.IndexParamName := NewPDecl.IndexParamName;
      if NewPDecl.IndexTypeName <> '' then
        PropInfo.IndexTypeDesc := FindTypeOrInstantiate(NewPDecl.IndexTypeName);
      PropInfo.IsDefault := NewPDecl.IsDefault;
      PropInfo.IsStatic := NewPDecl.IsStatic;
      PropInfo.Visibility    := NewPDecl.Visibility;
      PropInfo.DeclaringUnit := FCurrentUnitName;
      PropInfo.DeclaringType := ATypeName;
      RT.AddProperty(PropInfo);
    end;

    { Analyse method bodies with concrete types in scope.
      Push type-param bindings (T=Integer etc.) so that SizeOf(T) and
      local var declarations like 'var P: ^T' resolve to concrete types. }
    FTable.PushScope();
    for K := 0 to Templ.ParamNames.Count - 1 do
      FActiveTypeParams.Add(Templ.ParamNames.Strings[K]);
    try
      for K := 0 to Templ.ParamNames.Count - 1 do
      begin
        ConcrType := FindTypeOrInstantiate(Args.Strings[K]);
        if ConcrType <> nil then
        begin
          Sym := TSymbol.Create(Templ.ParamNames.Strings[K], skType, ConcrType);
          FTable.Define(Sym);
        end;
      end;
      for J := 0 to ClonedCD.Methods.Count - 1 do
      begin
        NewMDecl := TMethodDecl(ClonedCD.Methods.Items[J]);
        if NewMDecl.Body <> nil then
          AnalyseMethodDecl(NewMDecl, RT);
      end;
    finally
      for K := 0 to Templ.ParamNames.Count - 1 do
        FActiveTypeParams.Delete(FActiveTypeParams.Count - 1);
      FTable.PopScope();
    end;

    { Wire up implements: for each interface name in the cloned definition,
      find or instantiate the interface and call AddImplements on RT so that
      type-compatibility checks (class → interface assignment) work. }
    for J := 0 to ClonedCD.ImplementsNames.Count - 1 do
    begin
      Key      := ClonedCD.ImplementsNames.Strings[J];
      IntfDesc := TInterfaceTypeDesc(FindTypeOrInstantiate(Key));
      if IntfDesc <> nil then
        RT.AddImplements(IntfDesc);
    end;

    GI := TGenericInstance.Create();
    GI.TypeName := ATypeName;
    GI.ClassDef := ClonedCD;
    GI.TypeDesc := RT;
    GI.DefUnitName := Templ.DefUnitName;
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericInstances.Add(GI)
    else if FProg <> nil then
      FProg.GenericInstances.Add(GI)
    else
      { Instantiated during ImportUnitInterface, before Analyse/AnalyseUnit
        has set a program/unit owner.  Park it; FlushPendingGenericInstances
        hands it to the real owner once analysis starts. }
      FPendingGenericInstances.Add(GI);

    Result := RT;
  finally
    Args.Free();
  end;
end;

function TSemanticAnalyser.InstantiateGenericRecord(const ATypeName: string): TRecordTypeDesc;
var
  BracPos:  Integer;
  BaseName: string;
  ArgsStr:  string;
  Args:     TStringList;
  Templ:    TGenericRecordDef;
  ClonedRD: TRecordTypeDef;
  I, J, K:  Integer;
  FDecl:    TFieldDecl;
  NewFDecl: TFieldDecl;
  MDecl:    TMethodDecl;
  NewMDecl: TMethodDecl;
  Par:      TMethodParam;
  NewPar:   TMethodParam;
  Sym:      TSymbol;
  Key:      string;
  FldType:  TTypeDesc;
  FldName:  string;
  ParType:  TTypeDesc;
  RT:       TRecordTypeDesc;
  GRI:      TGenericRecordInstance;
  ConcrType: TTypeDesc;
  DeferBodies: Boolean;
begin
  Result := nil;
  { See InstantiateGeneric — defer body clone+analysis when there is no
    program/unit context (import-time resolution of a cached field type).
    RepairEarlyGenericInstances re-clones and analyses the bodies later. }
  DeferBodies := (FProg = nil) and (FCurrentUnit = nil);

  BracPos := StrPos('<', ATypeName);
  if BracPos < 0 then Exit;
  BaseName := StrHead(ATypeName, BracPos);
  ArgsStr  := StrCopyFrom(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 2);

  Args := TStringList.Create();
  try
    while ArgsStr <> '' do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    if not (FTable.FindGeneric(BaseName) is TGenericRecordDef) then Exit;
    Templ := TGenericRecordDef(FTable.FindGeneric(BaseName));
    if Templ = nil then Exit;
    if Args.Count <> Templ.ParamNames.Count then Exit;

    for I := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (I < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Strings[I], Args.Strings[I],
          Templ.ParamConstraints.Strings[I],
          Format('instantiation ''%s''', [ATypeName]));

    RT  := FTable.NewRecordType(ATypeName);
    Sym := TSymbol.Create(ATypeName, skType, RT);
    FTable.DefineGlobal(Sym);

    ClonedRD := TRecordTypeDef.Create();
    ClonedRD.IsPacked := Templ.RecordDef.IsPacked;

    for I := 0 to Templ.RecordDef.Fields.Count - 1 do
    begin
      FDecl    := TFieldDecl(Templ.RecordDef.Fields.Items[I]);
      NewFDecl := TFieldDecl.Create();
      for J := 0 to FDecl.Names.Count - 1 do
        NewFDecl.Names.Add(FDecl.Names.Strings[J]);
      NewFDecl.TypeName := SubstTypeParam(FDecl.TypeName, Templ.ParamNames, Args);
      NewFDecl.Visibility := FDecl.Visibility;
      ClonedRD.Fields.Add(NewFDecl);
    end;

    for I := 0 to Templ.RecordDef.Methods.Count - 1 do
    begin
      MDecl            := TMethodDecl(Templ.RecordDef.Methods.Items[I]);
      NewMDecl         := TMethodDecl.Create();
      NewMDecl.Name          := MDecl.Name;
      NewMDecl.OwnerTypeName := ATypeName;
      NewMDecl.IsRecordMethod := True;
      NewMDecl.Visibility    := MDecl.Visibility;
      if (MDecl.Body <> nil) and (not DeferBodies) then
      begin
        NewMDecl.Body    := CloneBlock(MDecl.Body);
        NewMDecl.OwnBody := True;
      end
      else
      begin
        { Body left nil — signature-only template, or deferred to
          RepairEarlyGenericInstances (import-time, no program context). }
        NewMDecl.Body    := nil;
        NewMDecl.OwnBody := False;
      end;

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par    := TMethodParam(MDecl.Params.Items[J]);
        NewPar := TMethodParam.Create();
        NewPar.ParamName  := Par.ParamName;
        { See the class path above — all passing-mode flags must be carried. }
        NewPar.IsVarParam   := Par.IsVarParam;
        NewPar.IsConstParam := Par.IsConstParam;
        NewPar.IsOutParam   := Par.IsOutParam;
        NewPar.IsOpenArray  := Par.IsOpenArray;
        NewPar.HasDefault   := Par.HasDefault;
        NewPar.DefaultValue := CloneExpr(Par.DefaultValue);
        NewPar.TypeName   := SubstTypeParam(Par.TypeName, Templ.ParamNames, Args);
        NewMDecl.Params.Add(NewPar);
      end;

      NewMDecl.ReturnTypeName :=
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args);

      ClonedRD.Methods.Add(NewMDecl);
    end;

    for J := 0 to ClonedRD.Fields.Count - 1 do
    begin
      NewFDecl := TFieldDecl(ClonedRD.Fields.Items[J]);
      FldType  := FindTypeOrInstantiate(NewFDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field in ''%s''', [NewFDecl.TypeName, ATypeName]),
          0, 0);
      NewFDecl.ResolvedType := FldType;
      for K := 0 to NewFDecl.Names.Count - 1 do
      begin
        FldName := NewFDecl.Names.Strings[K];
        RT.AddField(FldName, FldType);
        RT.FindField(FldName).Visibility    := NewFDecl.Visibility;
        RT.FindField(FldName).DeclaringUnit := FCurrentUnitName;
        RT.FindField(FldName).DeclaringType := ATypeName;
      end;
    end;

    for J := 0 to ClonedRD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedRD.Methods.Items[J]);
      Key      := ATypeName + '.' + NewMDecl.Name;
      FMethodIndex.AddObject(Key, NewMDecl);
      AddGroupEntry(FMethodGroups, Key, NewMDecl);
      NewMDecl.OwningUnit      := Sym.OwningUnit;
      { Bare, like class instances — see InstantiateGeneric (BUG-004). }
      NewMDecl.ResolvedQbeName := ATypeName + '_' + NewMDecl.Name;

      for K := 0 to NewMDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(NewMDecl.Params.Items[K]);
        ParType := FindTypeOrInstantiate(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for param ''%s'' in ''%s''',
              [Par.TypeName, Par.ParamName, ATypeName]),
            0, 0);
        Par.ResolvedType := ParType;
      end;

      if NewMDecl.ReturnTypeName <> '' then
      begin
        ParType := FindTypeOrInstantiate(NewMDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for method ''%s'' in ''%s''',
              [NewMDecl.ReturnTypeName, NewMDecl.Name, ATypeName]),
            0, 0);
        NewMDecl.ResolvedReturnType := ParType;
      end;
    end;

    FTable.PushScope();
    for K := 0 to Templ.ParamNames.Count - 1 do
      FActiveTypeParams.Add(Templ.ParamNames.Strings[K]);
    try
      for K := 0 to Templ.ParamNames.Count - 1 do
      begin
        ConcrType := FindTypeOrInstantiate(Args.Strings[K]);
        if ConcrType <> nil then
        begin
          Sym := TSymbol.Create(Templ.ParamNames.Strings[K], skType, ConcrType);
          FTable.Define(Sym);
        end;
      end;
      for J := 0 to ClonedRD.Methods.Count - 1 do
      begin
        NewMDecl := TMethodDecl(ClonedRD.Methods.Items[J]);
        if NewMDecl.Body <> nil then
          AnalyseMethodDecl(NewMDecl, RT);
      end;
    finally
      for K := 0 to Templ.ParamNames.Count - 1 do
        FActiveTypeParams.Delete(FActiveTypeParams.Count - 1);
      FTable.PopScope();
    end;

    GRI           := TGenericRecordInstance.Create();
    GRI.TypeName  := ATypeName;
    GRI.RecordDef := ClonedRD;
    GRI.TypeDesc  := RT;
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericRecordInstances.Add(GRI)
    else if FProg <> nil then
      FProg.GenericRecordInstances.Add(GRI)
    else
      FPendingGenericRecordInstances.Add(GRI);

    Result := RT;
  finally
    Args.Free();
  end;
end;

function TSemanticAnalyser.InstantiateGenericInterface(const ATypeName: string): TInterfaceTypeDesc;
var
  BracPos:     Integer;
  BaseName:    string;
  ArgsStr:     string;
  Args:        TStringList;
  Templ:       TGenericInterfaceDef;
  TemplObj:    TObject;
  I, K:        Integer;
  MDecl:       TMethodDecl;
  Par:         TMethodParam;
  Sym:         TSymbol;
  GII:         TGenericInterfaceInstance;
  MangledName: string;
  VarFlags:    string;
begin
  Result := nil;

  BracPos := StrPos('<', ATypeName);
  if BracPos < 0 then Exit;
  BaseName := StrHead(ATypeName, BracPos);
  ArgsStr  := StrCopyFrom(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 2);

  Args := TStringList.Create();
  try
    while ArgsStr <> '' do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    TemplObj := FTable.FindGeneric(BaseName);
    if (TemplObj = nil) or not (TemplObj is TGenericInterfaceDef) then Exit;
    Templ := TGenericInterfaceDef(TemplObj);
    if Args.Count <> Templ.ParamNames.Count then Exit;

    for I := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (I < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Strings[I], Args.Strings[I],
          Templ.ParamConstraints.Strings[I],
          Format('interface instantiation ''%s''', [ATypeName]));

    { Check if already instantiated }
    Sym := FTable.Lookup(ATypeName);
    if (Sym <> nil) and (Sym.TypeDesc is TInterfaceTypeDesc) then
    begin
      Exit(TInterfaceTypeDesc(Sym.TypeDesc));
    end;

    { Build mangled name: IEqualityComparer<Integer> → IEqualityComparer_Integer }
    MangledName := BaseName;
    for I := 0 to Args.Count - 1 do
      MangledName := MangledName + '_' + Args.Strings[I];

    { Create the concrete interface type descriptor }
    Result := FTable.NewInterfaceType(ATypeName);
    Sym    := TSymbol.Create(ATypeName, skType, Result);
    FTable.DefineGlobal(Sym);

    { Register interface method names with substituted return types + var-param flags }
    for I := 0 to Templ.IntfDef.Methods.Count - 1 do
    begin
      MDecl    := TMethodDecl(Templ.IntfDef.Methods.Items[I]);
      VarFlags := '';
      for K := 0 to MDecl.Params.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[K]);
        if K > 0 then VarFlags := VarFlags + ',';
        if Par.IsVarParam then VarFlags := VarFlags + '1'
                          else VarFlags := VarFlags + '0';
      end;
      Result.AddMethod(MDecl.Name,
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args),
        VarFlags);
    end;

    { Register the instantiation for codegen }
    GII          := TGenericInterfaceInstance.Create();
    GII.InstName := MangledName;
    GII.IntfDef  := nil;
    GII.TypeDesc := Result;
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericIntfInstances.Add(GII)
    else if FProg <> nil then
      FProg.GenericIntfInstances.Add(GII)
    else
      FPendingGenericIntfInstances.Add(GII);
  finally
    Args.Free();
  end;
end;

function TSemanticAnalyser.InstantiateGenericProcType(
  const ATypeName: string): TProceduralTypeDesc;
var
  BracPos:  Integer;
  BaseName: string;
  ArgsStr:  string;
  Args:     TStringList;
  Templ:    TGenericProcDef;
  ProcDesc: TProceduralTypeDesc;
  Sym:      TSymbol;
  K:        Integer;
  MParam:   TMethodParam;
  ProcParam: TProcParamInfo;
  SubstName: string;
  SubstType: TTypeDesc;
begin
  Result := nil;

  { Parse 'BaseName<Arg1,Arg2>' }
  BracPos := StrPos('<', ATypeName);
  if BracPos < 0 then Exit;
  BaseName := StrHead(ATypeName, BracPos);
  ArgsStr  := StrCopyFrom(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 2);

  if not (FTable.FindGeneric(BaseName) is TGenericProcDef) then Exit;
  Templ := TGenericProcDef(FTable.FindGeneric(BaseName));

  Args := TStringList.Create();
  try
    while ArgsStr <> '' do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;
    if Args.Count <> Templ.ParamNames.Count then Exit;

    for K := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (K < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Strings[K], Args.Strings[K],
          Templ.ParamConstraints.Strings[K],
          Format('instantiation ''%s''', [ATypeName]));

    { Build the concrete procedural descriptor.  Param and return type names
      are substituted, then resolved via FindTypeOrInstantiate so nested
      generic arguments (TGetter<TList<Integer>>) instantiate on demand. }
    ProcDesc := FTable.NewProceduralType(ATypeName);
    ProcDesc.IsMethodPtr := Templ.ProcDef.IsMethodPtr;
    ProcDesc.IsReference := Templ.ProcDef.IsReference;
    for K := 0 to Templ.ProcDef.Params.Count - 1 do
    begin
      MParam    := TMethodParam(Templ.ProcDef.Params.Items[K]);
      SubstName := SubstTypeParam(MParam.TypeName, Templ.ParamNames, Args);
      SubstType := FindTypeOrInstantiate(SubstName);
      if SubstType = nil then
        SemanticError(Format(
          'Unknown parameter type ''%s'' in generic procedural type ''%s''',
          [SubstName, ATypeName]), Templ.Line, Templ.Col);
      ProcParam := TProcParamInfo.Create();
      ProcParam.Name         := MParam.ParamName;
      ProcParam.TypeDesc     := SubstType;
      ProcParam.IsVarParam   := MParam.IsVarParam;
      ProcParam.IsConstParam := MParam.IsConstParam;
      ProcDesc.Params.Add(ProcParam);
    end;
    if Templ.ProcDef.IsFunction then
    begin
      SubstName := SubstTypeParam(Templ.ProcDef.ReturnTypeName,
                                  Templ.ParamNames, Args);
      SubstType := FindTypeOrInstantiate(SubstName);
      if SubstType = nil then
        SemanticError(Format(
          'Unknown return type ''%s'' in generic procedural type ''%s''',
          [SubstName, ATypeName]), Templ.Line, Templ.Col);
      ProcDesc.ReturnType := SubstType;
    end;

    Sym := TSymbol.Create(ATypeName, skType, ProcDesc);
    FTable.DefineGlobal(Sym);
    Result := ProcDesc;
  finally
    Args.Free();
  end;
end;

function TSemanticAnalyser.InstantiateGenericFunc(const AInstName: string): TMethodDecl;
var
  BracPos:     Integer;
  BaseName:    string;
  ArgsStr:     string;
  Args:        TStringList;
  Templ:       TMethodDecl;
  TemplIdx:    Integer;
  NewMDecl:    TMethodDecl;
  NewPar:      TMethodParam;
  OldPar:      TMethodParam;
  ParTypeName: string;
  RetTypeName: string;
  SubstType:   TTypeDesc;
  I, J:        Integer;
  Sym:         TSymbol;
  GFI:         TGenericFuncInstance;
begin
  Result := nil;

  { Parse 'Identity<Integer>' → BaseName='Identity', ArgsStr='Integer' }
  BracPos := StrPos('<', AInstName);
  if BracPos < 0 then Exit;

  BaseName := StrHead(AInstName, BracPos);
  ArgsStr  := StrCopyFrom(AInstName, BracPos + 1, Length(AInstName) - BracPos - 2);

  { Check both the in-unit template index and any imported templates
    registered through the symbol table.  Imports landed via
    uSemanticImport.RegisterUnitInterface populate FTable; in-unit
    AnalyseStandaloneDecl populates both. }
  TemplIdx := FGenericFuncTemplates.IndexOf(BaseName);
  if TemplIdx >= 0 then
    Templ := TMethodDecl(FGenericFuncTemplates.Objects[TemplIdx])
  else
    Templ := TMethodDecl(FTable.FindGenericRoutine(BaseName));
  if Templ = nil then Exit;  { not a known generic function template }

  Args := TStringList.Create();
  try
    while Length(ArgsStr) > 0 do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    if Args.Count <> Templ.TypeParams.Count then
      SemanticError(
        Format('Generic function ''%s'' expects %d type parameter(s) but got %d',
          [BaseName, Templ.TypeParams.Count, Args.Count]),
        0, 0);

    { Validate each type argument against the template's declared constraints. }
    for I := 0 to Args.Count - 1 do
      if (Templ.TypeParamConstraints <> nil) and
         (I < Templ.TypeParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.TypeParams.Strings[I], Args.Strings[I],
          Templ.TypeParamConstraints.Strings[I],
          Format('generic function ''%s''', [AInstName]));

    NewMDecl         := TMethodDecl.Create();
    NewMDecl.Name    := AInstName;
    { Deep-clone the template body so each instance has its own analysed
      AST.  Sharing would leave Resolved* annotations from the last
      instance on the body, miscompiling earlier instances. }
    if Templ.Body <> nil then
    begin
      NewMDecl.Body    := CloneBlock(Templ.Body);
      NewMDecl.OwnBody := True;
      { Substitute the type parameter in the body's local var declarations
        (e.g. `var v: T` -> `var v: Integer`).  Signature substitution
        (params + return) is done below, but a local of type T would
        otherwise reach AnalyseStandaloneDecl with T still unresolved. }
      for I := 0 to NewMDecl.Body.Decls.Count - 1 do
        TVarDecl(NewMDecl.Body.Decls.Items[I]).TypeName :=
          Self.SubstTypeParam(TVarDecl(NewMDecl.Body.Decls.Items[I]).TypeName,
            Templ.TypeParams, Args);
    end
    else
    begin
      NewMDecl.Body    := nil;
      NewMDecl.OwnBody := False;
    end;

    { Substitute return type }
    { Nested-aware substitution: type params may appear INSIDE generic
      arguments (TSel<Integer, R> at R = string) — a whole-name compare
      misses them (the Phase-10 gate failure). }
    RetTypeName := Self.SubstTypeParam(Templ.ReturnTypeName,
      Templ.TypeParams, Args);
    NewMDecl.ReturnTypeName := RetTypeName;
    if RetTypeName <> '' then
    begin
      SubstType := FindTypeOrInstantiate(RetTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' in generic function instance ''%s''',
          [RetTypeName, AInstName]), 0, 0);
      NewMDecl.ResolvedReturnType := SubstType;
    end;

    { Clone params with substituted types }
    for I := 0 to Templ.Params.Count - 1 do
    begin
      OldPar           := TMethodParam(Templ.Params.Items[I]);
      NewPar           := TMethodParam.Create();
      NewPar.ParamName  := OldPar.ParamName;
      { All passing-mode flags must survive monomorphisation — see the
        generic-class path in InstantiateGeneric. }
      NewPar.IsVarParam   := OldPar.IsVarParam;
      NewPar.IsConstParam := OldPar.IsConstParam;
      NewPar.IsOutParam   := OldPar.IsOutParam;
      NewPar.IsOpenArray  := OldPar.IsOpenArray;
      NewPar.HasDefault   := OldPar.HasDefault;
      NewPar.DefaultValue := CloneExpr(OldPar.DefaultValue);
      ParTypeName := Self.SubstTypeParam(OldPar.TypeName,
        Templ.TypeParams, Args);
      NewPar.TypeName := ParTypeName;
      SubstType := FindTypeOrInstantiate(ParTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' for parameter ''%s'' in ''%s''',
          [ParTypeName, NewPar.ParamName, AInstName]), 0, 0);
      NewPar.ResolvedType := SubstType;
      NewMDecl.Params.Add(NewPar);
    end;

    { Analyse the shared body with concrete types in scope }
    AnalyseStandaloneDecl(NewMDecl);

    { Register in proc index and global symbol table }
    RegisterProcDecl(AInstName, NewMDecl);
    if NewMDecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(AInstName, skFunction, NewMDecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(AInstName, skProcedure, nil);
    FTable.DefineGlobal(Sym);

    { Store for codegen }
    GFI            := TGenericFuncInstance.Create();
    GFI.InstName   := AInstName;
    GFI.MethodDecl := NewMDecl;
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericFuncInstances.Add(GFI)
    else
      FProg.GenericFuncInstances.Add(GFI);

    Result := NewMDecl;
  finally
    Args.Free();
  end;
end;

function TSemanticAnalyser.InstantiateGenericMethod(
  const AOwnerType, AInstName: string): TMethodDecl;
{ AInstName is the method name with type args, e.g. 'Pick<Integer>'.  Mirrors
  InstantiateGenericFunc but preserves the implicit Self: the instance is
  analysed as a method of AOwnerType and emitted as <Owner>_<Inst>. }
var
  BaseName:    string;
  ArgsStr:     string;
  TemplIdx:    Integer;
  BracPos:     Integer;
  Templ:       TMethodDecl;
  Args:        TStringList;
  NewMDecl:    TMethodDecl;
  NewPar:      TMethodParam;
  OldPar:      TMethodParam;
  ParTypeName: string;
  RetTypeName: string;
  SubstType:   TTypeDesc;
  OwnerSym:    TSymbol;
  OwnerRT:     TRecordTypeDesc;
  GMI:         TGenericMethodInstance;
  I, J:        Integer;
begin
  Result := nil;
  BracPos := StrPos('<', AInstName);
  if BracPos < 0 then Exit;
  BaseName := StrHead(AInstName, BracPos);
  ArgsStr  := StrCopyFrom(AInstName, BracPos + 1, Length(AInstName) - BracPos - 2);

  TemplIdx := FGenericMethodTemplates.IndexOf(AOwnerType + '.' + BaseName);
  if TemplIdx < 0 then Exit;  { not a known generic method on this owner }
  Templ := TMethodDecl(FGenericMethodTemplates.Objects[TemplIdx]);

  OwnerSym := FTable.Lookup(AOwnerType);
  if (OwnerSym = nil) or not (OwnerSym.TypeDesc is TRecordTypeDesc) then Exit;
  OwnerRT := TRecordTypeDesc(OwnerSym.TypeDesc);

  { Idempotent: a second call site with the same type args reuses the existing
    instance rather than emitting a duplicate symbol. }
  if FCurrentUnit <> nil then
  begin
    for I := 0 to FCurrentUnit.GenericMethodInstances.Count - 1 do
    begin
      GMI := TGenericMethodInstance(FCurrentUnit.GenericMethodInstances.Items[I]);
      if SameText(GMI.OwnerType, AOwnerType) and SameText(GMI.InstName, AInstName) then
        Exit(GMI.MethodDecl);
    end;
  end
  else
    for I := 0 to FProg.GenericMethodInstances.Count - 1 do
    begin
      GMI := TGenericMethodInstance(FProg.GenericMethodInstances.Items[I]);
      if SameText(GMI.OwnerType, AOwnerType) and SameText(GMI.InstName, AInstName) then
        Exit(GMI.MethodDecl);
    end;

  Args := TStringList.Create();
  try
    while Length(ArgsStr) > 0 do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    if Args.Count <> Templ.TypeParams.Count then
      SemanticError(
        Format('Generic method ''%s.%s'' expects %d type parameter(s) but got %d',
          [AOwnerType, BaseName, Templ.TypeParams.Count, Args.Count]),
        0, 0);
    for I := 0 to Args.Count - 1 do
      if (Templ.TypeParamConstraints <> nil) and
         (I < Templ.TypeParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.TypeParams.Strings[I], Args.Strings[I],
          Templ.TypeParamConstraints.Strings[I],
          Format('generic method ''%s.%s''', [AOwnerType, BaseName]));

    NewMDecl              := TMethodDecl.Create();
    NewMDecl.Name         := AInstName;
    NewMDecl.OwnerTypeName := AOwnerType;
    NewMDecl.IsRecordMethod := Templ.IsRecordMethod;
    { Mangled symbol: <Owner>_<Method><args> -> QBEMangle drops the <>
      and joins with '_', e.g. TUtil_Pick_Integer.  Bare (no unit prefix):
      monomorphised on demand by any consumer, deduped by weak linkage in
      per-unit mode — same rule as class instances (BUG-004). }
    NewMDecl.ResolvedQbeName := AOwnerType + '_' + AInstName;

    if Templ.Body <> nil then
    begin
      NewMDecl.Body    := CloneBlock(Templ.Body);
      NewMDecl.OwnBody := True;
      for I := 0 to NewMDecl.Body.Decls.Count - 1 do
        TVarDecl(NewMDecl.Body.Decls.Items[I]).TypeName :=
          Self.SubstTypeParam(TVarDecl(NewMDecl.Body.Decls.Items[I]).TypeName,
            Templ.TypeParams, Args);
    end
    else
    begin
      NewMDecl.Body    := nil;
      NewMDecl.OwnBody := False;
    end;

    { Nested-aware substitution: type params may appear INSIDE generic
      arguments (TSel<Integer, R> at R = string) — a whole-name compare
      misses them (the Phase-10 gate failure). }
    RetTypeName := Self.SubstTypeParam(Templ.ReturnTypeName,
      Templ.TypeParams, Args);
    NewMDecl.ReturnTypeName := RetTypeName;
    if RetTypeName <> '' then
    begin
      SubstType := FindTypeOrInstantiate(RetTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' in generic method instance ''%s.%s''',
          [RetTypeName, AOwnerType, AInstName]), 0, 0);
      NewMDecl.ResolvedReturnType := SubstType;
    end;

    for I := 0 to Templ.Params.Count - 1 do
    begin
      OldPar            := TMethodParam(Templ.Params.Items[I]);
      NewPar            := TMethodParam.Create();
      NewPar.ParamName  := OldPar.ParamName;
      { All passing-mode flags must survive monomorphisation — see the
        generic-class path in InstantiateGeneric. }
      NewPar.IsVarParam   := OldPar.IsVarParam;
      NewPar.IsConstParam := OldPar.IsConstParam;
      NewPar.IsOutParam   := OldPar.IsOutParam;
      NewPar.IsOpenArray  := OldPar.IsOpenArray;
      NewPar.HasDefault   := OldPar.HasDefault;
      NewPar.DefaultValue := CloneExpr(OldPar.DefaultValue);
      ParTypeName := Self.SubstTypeParam(OldPar.TypeName,
        Templ.TypeParams, Args);
      NewPar.TypeName := ParTypeName;
      SubstType := FindTypeOrInstantiate(ParTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' for parameter ''%s'' in ''%s.%s''',
          [ParTypeName, NewPar.ParamName, AOwnerType, AInstName]), 0, 0);
      NewPar.ResolvedType := SubstType;
      NewMDecl.Params.Add(NewPar);
    end;

    { Analyse the body with Self (the owner) and concrete types in scope.
      The method's OWN type params (R) are bound as scoped type aliases so
      body references like TList<R>.Create() canonicalise to the concrete
      instantiation — mirrors InstantiateGeneric's body-analysis block. }
    FTable.PushScope();
    for I := 0 to Templ.TypeParams.Count - 1 do
      FActiveTypeParams.Add(Templ.TypeParams.Strings[I]);
    try
      for I := 0 to Templ.TypeParams.Count - 1 do
      begin
        SubstType := FindTypeOrInstantiate(Args.Strings[I]);
        if SubstType <> nil then
          FTable.Define(TSymbol.Create(Templ.TypeParams.Strings[I],
            skType, SubstType));
      end;
      AnalyseMethodDecl(NewMDecl, OwnerRT);
    finally
      for I := 0 to Templ.TypeParams.Count - 1 do
        FActiveTypeParams.Delete(FActiveTypeParams.Count - 1);
      FTable.PopScope();
    end;

    GMI            := TGenericMethodInstance.Create();
    GMI.OwnerType  := AOwnerType;
    GMI.InstName   := AInstName;
    GMI.MethodDecl := NewMDecl;
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericMethodInstances.Add(GMI)
    else
      FProg.GenericMethodInstances.Add(GMI);

    Result := NewMDecl;
  finally
    Args.Free();
  end;
end;

procedure TSemanticAnalyser.AnalyseBlock(ABlock: TBlock; AIsProgramTop: Boolean = False);
var
  I: Integer;
begin
  { Type declarations are registered in the outer scope so they remain visible
    after the block scope is popped — needed for var declarations and the
    transferred symbol table used by codegen. }
  AnalyseConstDecls(ABlock);
  AnalyseTypeDecls(ABlock);
  AnalyseArrayConstDecls(ABlock);
  { Link standalone TTypeName.MethodName implementations to their class method
    declarations, transferring the body so AnalyseMethodBodies can process it. }
  LinkClassMethodImpls(ABlock);
  LinkGenericClassMethodImpls(ABlock);
  CheckClassMethodsImplemented(ABlock);
  RepairEarlyGenericInstances();
  { Register standalone proc/func signatures before class method bodies so that
    methods can call free functions declared in the same block. }
  AnalyseStandaloneDecls(ABlock);
  FTable.PushScope();
  Inc(FScopeDepth);
  try
    { The program's top-level block gets its own pushed scope, so the
      module-name markers planted in the global scope by Analyse() are
      one level down and would not block program-level var decls.
      Re-plant them in this scope (issue #84). }
    if AIsProgramTop and (FProg <> nil) then
    begin
      DefineModuleName(FProg.Name);
      for I := 0 to FProg.UsedUnits.Count - 1 do
        DefineModuleName(FProg.UsedUnits.Strings[I]);
    end;
    { Register var declarations before method bodies so that class methods can
      resolve identifiers that refer to program-level globals (issue #43).
      The same applies inside nested function/procedure blocks: locals must be
      in scope before any method body declared in this block is analysed. }
    AnalyseVarDecls(ABlock);
    AnalyseMethodBodies(ABlock);
    AnalyseStandaloneBodies(ABlock);
    AnalyseStmts(ABlock);
    { Register + analyse anonymous-method thunks lifted during the body
      passes above.  Program-top only: nested AnalyseBlock calls (routine
      bodies) must NOT drain, or thunk bodies would be analysed with the
      enclosing routine's locals still in scope and an unsupported capture
      would silently type-check. }
    if AIsProgramTop then
      DrainPendingAnonDecls(ABlock);
    { After all bodies are analysed, mark inline candidates so codegen can
      decide whether to emit a call or inline the body at each call site. }
    MarkInlineCandidates(ABlock);
  finally
    Dec(FScopeDepth);
    FTable.PopScope();
  end;
end;

{ Fold a deferred const bit-op expression to an Int64.  ATokens is the
  alternating operand/operator list built by the parser:

    Tokens[0,2,4,...]  operands; Objects[i] = nil → literal,
                                 Objects[i] <> nil → ident reference
    Tokens[1,3,5,...]  operator names: 'or'/'and'/'xor'/'shl'/'shr'

  Idents must resolve to integer-typed constants in the current scope.
  Left-to-right associativity (no precedence between bit ops). }
function TSemanticAnalyser.FoldConstBitOpExpr(ATokens: TStringList;
                                              ALine, ACol: Integer): Int64;
var
  I:       Integer;
  Op:      string;
  Operand: Int64;
  RefSym:  TSymbol;
begin
  Result := 0;
  if (ATokens = nil) or (ATokens.Count = 0) then Exit;
  I := 0;
  while I < ATokens.Count do
  begin
    if ATokens.Objects[I] = TObject(1) then
    begin
      RefSym := FTable.Lookup(ATokens.Get(I));
      if (RefSym = nil) or (RefSym.Kind <> skConstant) then
      begin
        SemanticError(Format('Undeclared constant ''%s''', [ATokens.Get(I)]),
                      ALine, ACol);
        Exit;
      end;
      Operand := RefSym.ConstValue;
    end
    else
      Operand := StrToInt64(ATokens.Get(I));
    if I = 0 then
      Result := Operand
    else
    begin
      Op := ATokens.Get(I - 1);
      if      Op = 'or'  then Result := Result or  Operand
      else if Op = 'and' then Result := Result and Operand
      else if Op = 'xor' then Result := Result xor Operand
      else if Op = 'shl' then Result := Result shl Operand
      else if Op = 'shr' then Result := Result shr Operand
      else
        SemanticError(Format('Unsupported const bit-op ''%s''', [Op]),
                      ALine, ACol);
    end;
    Inc(I, 2);
  end;
end;

function TSemanticAnalyser.EvalConstIntExpr(AExpr: TASTExpr;
                                            ALine, ACol: Integer): Int64;
var
  Bin:     TBinaryExpr;
  IdSym:   TSymbol;
  EnumRef: TEnumMemberRef;
  L, R:    Int64;
begin
  Result := 0;
  if AExpr = nil then Exit;

  if AExpr is TIntLiteral then
    Exit(TIntLiteral(AExpr).Value);

  if AExpr is TIdentExpr then
  begin
    { Named-constant reference; also resolves True/False to 1/0. }
    if SameText(TIdentExpr(AExpr).Name, 'True') then Exit(1);
    if SameText(TIdentExpr(AExpr).Name, 'False') then Exit(0);
    IdSym := FTable.Lookup(TIdentExpr(AExpr).Name);
    if (IdSym = nil) or (IdSym.Kind <> skConstant) then
    begin
      { Bare enum member used in a constant expression (e.g. an array
        bound or set range).  No type context here: a member declared by a
        single enum resolves; one shared by several is ambiguous and must be
        qualified (TEnum.Member). }
      EnumRef := ResolveEnumMember(TIdentExpr(AExpr).Name, nil);
      if EnumRef <> nil then
      begin
        if EnumMemberCandidateCount(TIdentExpr(AExpr).Name) > 1 then
          SemanticError(Format(
            'cannot determine which enum ''%s'' refers to: it is declared by ' +
            '%s, and there is no type context here to choose. Qualify it as ' +
            '<EnumType>.%s',
            [TIdentExpr(AExpr).Name, EnumMemberOwners(TIdentExpr(AExpr).Name),
             TIdentExpr(AExpr).Name]),
            ALine, ACol);
        Exit(EnumRef.Ordinal);
      end;
      SemanticError(Format(
        'Constant expression references ''%s'', which is not a constant',
        [TIdentExpr(AExpr).Name]), ALine, ACol);
      Exit;
    end;
    Exit(IdSym.ConstValue);
  end;

  if AExpr is TNotExpr then
    Exit(not EvalConstIntExpr(TNotExpr(AExpr).Expr, ALine, ACol));

  if AExpr is TBinaryExpr then
  begin
    Bin := TBinaryExpr(AExpr);
    L := EvalConstIntExpr(Bin.Left,  ALine, ACol);
    R := EvalConstIntExpr(Bin.Right, ALine, ACol);
    case Bin.Op of
      boAdd: Exit(L + R);
      boSub: Exit(L - R);
      boMul: Exit(L * R);
      boDiv:
        begin
          if R = 0 then
          begin
            SemanticError('Division by zero in constant expression', ALine, ACol);
            Exit;
          end;
          Exit(L div R);
        end;
      boMod:
        begin
          if R = 0 then
          begin
            SemanticError('Division by zero in constant expression', ALine, ACol);
            Exit;
          end;
          Exit(L mod R);
        end;
      boAnd: Exit(L and R);
      boOr:  Exit(L or R);
      boXor: Exit(L xor R);
      boShl: Exit(L shl R);
      boShr, boSar: Exit(L shr R);
    else
      SemanticError(
        'Unsupported operator in integer constant expression', ALine, ACol);
      Exit;
    end;
  end;

  SemanticError(
    'Constant expression is not a compile-time integer', ALine, ACol);
end;

function TSemanticAnalyser.IsFloatConstExpr(AExpr: TASTExpr): Boolean;
var
  Bin: TBinaryExpr;
  Sym: TSymbol;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr is TFloatLiteral then
    Exit(True);
  if AExpr is TIdentExpr then
  begin
    Sym := FTable.Lookup(TIdentExpr(AExpr).Name);
    if (Sym <> nil) and (Sym.Kind = skConstant) and
       (Sym.TypeDesc <> nil) and Sym.TypeDesc.IsFloat() then
      Exit(True);
    Exit;
  end;
  if AExpr is TBinaryExpr then
  begin
    Bin := TBinaryExpr(AExpr);
    if Bin.Op = boSlash then
      Exit(True);
    if IsFloatConstExpr(Bin.Left) or IsFloatConstExpr(Bin.Right) then
      Exit(True);
  end;
end;

function TSemanticAnalyser.EvalConstFloatExpr(AExpr: TASTExpr;
                                               ALine, ACol: Integer): string;
var
  Bin:   TBinaryExpr;
  IdSym: TSymbol;
  L, R:  Double;
  LStr:  string;
  RStr:  string;
begin
  Result := '0';
  if AExpr = nil then Exit;

  if AExpr is TFloatLiteral then
    Exit(TFloatLiteral(AExpr).Value);

  if AExpr is TIntLiteral then
    Exit(IntToStr(TIntLiteral(AExpr).Value));

  if AExpr is TIdentExpr then
  begin
    IdSym := FTable.Lookup(TIdentExpr(AExpr).Name);
    if (IdSym = nil) or (IdSym.Kind <> skConstant) then
    begin
      SemanticError(Format(
        'Constant expression references ''%s'', which is not a constant',
        [TIdentExpr(AExpr).Name]), ALine, ACol);
      Exit;
    end;
    if (IdSym.TypeDesc <> nil) and IdSym.TypeDesc.IsFloat() then
      Exit(IdSym.ConstString)
    else
      Exit(IntToStr(IdSym.ConstValue));
  end;

  if AExpr is TBinaryExpr then
  begin
    Bin  := TBinaryExpr(AExpr);
    LStr := EvalConstFloatExpr(Bin.Left,  ALine, ACol);
    RStr := EvalConstFloatExpr(Bin.Right, ALine, ACol);
    L    := RawStrToDouble(LStr);
    R    := RawStrToDouble(RStr);
    case Bin.Op of
      boAdd: L := L + R;
      boSub: L := L - R;
      boMul: L := L * R;
      boSlash, boDiv:
        begin
          if R = 0.0 then
          begin
            SemanticError('Division by zero in constant expression', ALine, ACol);
            Exit;
          end;
          L := L / R;
        end;
    else
      SemanticError(
        'Unsupported operator in floating-point constant expression', ALine, ACol);
      Exit;
    end;
    Exit(RawDoubleToStr(L));
  end;

  SemanticError(
    'Constant expression is not a compile-time float', ALine, ACol);
end;

function IsPlainInt(const S: string): Boolean;
var
  I, Start: Integer;
begin
  Result := False;
  if Length(S) = 0 then Exit;
  if S[0] = '-' then
    Start := 1
  else
    Start := 0;
  if Start >= Length(S) then Exit;
  for I := Start to Length(S) - 1 do
    if (S[I] < '0') or (S[I] > '9') then Exit;
  Result := True;
end;

function TSemanticAnalyser.ResolveArrayBound(const ABoundText: string): Integer;
var
  Src: string;
  Lx: TLexer;
  Px: TParser;
  Prog: TProgram;
  CD: TConstDecl;
  Expr: TASTExpr;
  Sym: TSymbol;
  EnumRef: TEnumMemberRef;
begin
  if IsPlainInt(ABoundText) then
    Exit(Integer(StrToInt(ABoundText)));
  { Enum-type dimension markers (see ReadConstArrayDim): '@L:TEnum' / '@H:TEnum'
    are the low / high bounds of an enum-typed array dimension.  A FULL enum
    spans 0..Members.Count-1; an ENUM-SUBRANGE type (TSub = a..b) spans its own
    ordinal bounds SubrangeLow..SubrangeHigh — so the low is NOT always 0
    (GH #182).  The bare '@TEnum' form (legacy high-only encoding) is still
    accepted for backward compatibility. }
  if (Length(ABoundText) >= 3) and (Copy(ABoundText, 0, 3) = '@L:') then
  begin
    Sym := FTable.Lookup(Copy(ABoundText, 3, Length(ABoundText) - 3));
    if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) and
       (Sym.TypeDesc.Kind = tyEnum) then
    begin
      if TEnumTypeDesc(Sym.TypeDesc).IsSubrange then
        Exit(Integer(TEnumTypeDesc(Sym.TypeDesc).SubrangeLow));
      Exit(0);
    end;
    SemanticError(Format('Unknown enum type ''%s'' in array dimension',
      [Copy(ABoundText, 3, Length(ABoundText) - 3)]), 0, 0);
  end;
  if (Length(ABoundText) >= 3) and (Copy(ABoundText, 0, 3) = '@H:') then
  begin
    Sym := FTable.Lookup(Copy(ABoundText, 3, Length(ABoundText) - 3));
    if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) and
       (Sym.TypeDesc.Kind = tyEnum) then
    begin
      if TEnumTypeDesc(Sym.TypeDesc).IsSubrange then
        Exit(Integer(TEnumTypeDesc(Sym.TypeDesc).SubrangeHigh));
      Exit(TEnumTypeDesc(Sym.TypeDesc).Members.Count - 1);
    end;
    SemanticError(Format('Unknown enum type ''%s'' in array dimension',
      [Copy(ABoundText, 3, Length(ABoundText) - 3)]), 0, 0);
  end;
  if (Length(ABoundText) > 0) and (ABoundText[0] = '@') then
  begin
    Sym := FTable.Lookup(Copy(ABoundText, 1, Length(ABoundText) - 1));
    if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) and
       (Sym.TypeDesc.Kind = tyEnum) then
    begin
      if TEnumTypeDesc(Sym.TypeDesc).IsSubrange then
        Exit(Integer(TEnumTypeDesc(Sym.TypeDesc).SubrangeHigh));
      Exit(TEnumTypeDesc(Sym.TypeDesc).Members.Count - 1);
    end;
    SemanticError(Format('Unknown enum type ''%s'' in array dimension',
      [Copy(ABoundText, 1, Length(ABoundText) - 1)]), 0, 0);
  end;
  Sym := FTable.Lookup(ABoundText);
  if (Sym <> nil) and (Sym.Kind = skConstant) then
    Exit(Integer(Sym.ConstValue));
  { Enum-member bound: an INLINE enum-subrange array index —
    array[ptWhitePawn..ptKing] — supplies its bounds as bare enum-member
    names, which live in the reverse enum-member index, NOT the main symbol
    table (so the skConstant probe above misses them).  Resolve the member's
    ordinal.  A NAMED enum-subrange type (TSub = a..b) already works because
    it is built via the subrange-type path; this closes the inline form
    (GH #182 follow-up). }
  EnumRef := ResolveEnumMember(ABoundText, nil);
  if EnumRef <> nil then
  begin
    { An AMBIGUOUS member name (declared by more than one enum) has no type
      context here to disambiguate, and last-declared-wins would silently
      pick a wrong ordinal → a wrong array extent.  Reject it, mirroring the
      EvalConstIntExpr precedent — but suggest a NAMED subrange type, since
      a qualified 'TEnum.Member' does not parse in bound position. }
    if EnumMemberCandidateCount(ABoundText) > 1 then
      SemanticError(Format(
        'cannot determine which enum ''%s'' refers to as an array bound: it ' +
        'is declared by %s, and there is no type context here to choose. ' +
        'Declare a named subrange type (type TSub = Lo..Hi) and index by that',
        [ABoundText, EnumMemberOwners(ABoundText)]), 0, 0);
    Exit(Integer(EnumRef.Ordinal));
  end;
  Src := 'program _ab; const _ab_val = ' + ABoundText + '; begin end.';
  Lx := TLexer.Create(Src);
  Px := TParser.Create(Lx);
  try
    Prog := Px.Parse();
    try
      if Prog.Block.ConstDecls.Count = 0 then
        raise ESemanticError.Create(
          Format('Cannot resolve array bound ''%s''', [ABoundText]));
      CD := TConstDecl(Prog.Block.ConstDecls.Items[0]);
      if CD.IntValueExpr <> nil then
      begin
        Expr := CD.IntValueExpr;
        Result := Integer(EvalConstIntExpr(Expr, 0, 0));
      end
      else if CD.IntExprTokens <> nil then
        Result := Integer(FoldConstBitOpExpr(CD.IntExprTokens, 0, 0))
      else
        raise ESemanticError.Create(
          Format('Cannot resolve array bound ''%s''', [ABoundText]));
    finally
      Prog.Free();
    end;
  finally
    Px.Free();
    Lx.Free();
  end;
end;

function TSemanticAnalyser.ResolveSubrangeSetType(const ASubrange: string): TSetTypeDesc;
{ Resolve a 'set of lo..hi' integer-subrange set type, e.g. 'set of 0..255'.
  Element ordinals are the integer values themselves; like Delphi/FPC the type is
  capped at 256 elements (ordinals 0..255).  The bitmap is sized by the high
  bound (bits 0..hi), reusing the Byte-backed ordinal-set machinery — a low bound
  > 0 simply leaves the lower bits unused, matching FPC. }
var
  DDotPos, Lo, Hi: Integer;
  LStr, HStr, CanonName: string;
begin
  DDotPos := StrPos('..', ASubrange);
  LStr := StrCopyFrom(ASubrange, 0, DDotPos);
  HStr := StrCopyTail(ASubrange, DDotPos + 2);
  Lo := ResolveArrayBound(LStr);
  Hi := ResolveArrayBound(HStr);
  if Lo < 0 then
    SemanticError(Format(
      'Set subrange ''%s'': lower bound must be >= 0', [ASubrange]), 0, 0);
  if Hi > 255 then
    SemanticError(Format(
      'Set subrange ''%s'': upper bound must be <= 255 (a set has at most 256 ' +
      'elements)', [ASubrange]), 0, 0);
  if Hi < Lo then
    SemanticError(Format(
      'Set subrange ''%s'' is descending', [ASubrange]), 0, 0);
  CanonName := Format('set of %d..%d', [Lo, Hi]);
  Result := TSetTypeDesc(FTable.FindType(CanonName));
  if Result = nil then
  begin
    Result := FTable.NewOrdinalSetType(CanonName, FTable.TypeByte, Hi + 1);
    FTable.DefineGlobal(TSymbol.Create(CanonName, skType, Result));
  end;
end;

function TSemanticAnalyser.ResolveConstArrayElem(const AElem: string;
  AElemType: TTypeDesc; ALine, ACol: Integer): string;
{ Resolve one array-const element to the numeric string codegen needs.  The
  parser stores identifiers verbatim because it does not yet know the element
  type; with the type now known, fold bare identifiers — Boolean True/False,
  enum members, and named integer/boolean constants — to their ordinal value.
  Numeric and float literals (and already-folded integers) pass through. }
var
  Sym:     TSymbol;
  EnumRef: TEnumMemberRef;
  RadixVal: Int64;
  RadixIsU: Boolean;
begin
  Result := AElem;
  if AElem = '' then Exit;
  { Radix-prefixed integer literal — $hex, %binary, &octal (with optional
    leading sign).  The lexer keeps the prefixed form in the token text, but
    the rest of the const-array pipeline (codegen, OPDF) expects a plain
    decimal string.  Fold through ParseIntOrUInt64Literal, the same tolerant
    parser the scalar typed-const path uses (issue #133), so a sign-bit bit
    pattern like $8080808080808080 is accepted here too (issue #159): the
    folded decimal is the signed rendering of the same 64-bit image. }
  if (AElem[0] = '$') or (AElem[0] = '%') or (AElem[0] = '&') then
  begin
    ParseIntOrUInt64Literal(AElem, RadixVal, RadixIsU);
    Exit(IntToStr(RadixVal));
  end;
  if (Length(AElem) > 1) and (AElem[0] = '-') and
     ((AElem[1] = '$') or (AElem[1] = '%') or (AElem[1] = '&')) then
    Exit(IntToStr(-ParseIntLiteral(StrCopyTail(AElem, 1))));
  { Already a numeric literal (int, negative int, or float) — leave as is. }
  if IsPlainInt(AElem) then Exit;
  if (AElem[0] >= '0') and (AElem[0] <= '9') then Exit;
  if (AElem[0] = '-') or (AElem[0] = '+') or (AElem[0] = '.') then Exit;
  { Boolean literals. }
  if SameText(AElem, 'True') then Exit('1');
  if SameText(AElem, 'False') then Exit('0');
  { Named constant carrying its value in ConstValue. }
  Sym := FTable.Lookup(AElem);
  if (Sym <> nil) and (Sym.Kind = skConstant) then
    Exit(IntToStr(Sym.ConstValue));
  { Bare enum member (no longer a global symbol) — resolve via the reverse
    index, using the array's element type as context when it is an enum. }
  EnumRef := ResolveEnumMember(AElem, AElemType);
  if EnumRef <> nil then
    Exit(IntToStr(EnumRef.Ordinal));
  { Unresolved identifier in a numeric/boolean/enum array — a real error;
    leaving it would emit an undefined symbol reference at link time. }
  SemanticError(Format(
    'Cannot resolve array-const element ''%s'' to a constant value', [AElem]),
    ALine, ACol);
end;

function TSemanticAnalyser.ResolveSetMemberOrd(const AMember: string;
  ACD: TConstDecl; var AEnumDesc: TEnumTypeDesc): Integer;
{ Resolve one set-constant member (an integer literal, an enum constant, or a
  named integer constant) to its ordinal.  Enum members must all share one base
  enum, tracked through AEnumDesc; integer members do not set it (the set's base
  type then comes from the declared TypeName, e.g. set of Byte). }
var
  Sym: TSymbol;
  Ref: TEnumMemberRef;
begin
  if IsPlainInt(AMember) then
    Exit(Integer(StrToInt(AMember)));
  { A named integer/ordinal constant (enum members are no longer symbols). }
  Sym := FTable.Lookup(AMember);
  if (Sym <> nil) and (Sym.Kind = skConstant) then
    Exit(Integer(Sym.ConstValue));
  { Bare enum member via the reverse index.  The first enum member seen pins
    the set's base enum; later members resolve against it (so an ambiguous
    name follows the set), and a member outside it is a genuine mix error. }
  Ref := ResolveEnumMember(AMember, AEnumDesc);
  if Ref = nil then
  begin
    SemanticError(Format(
      'Set constant ''%s'' member ''%s'' is not a constant value',
      [ACD.Name, AMember]), ACD.Line, ACD.Col);
    Exit(0);
  end;
  if AEnumDesc = nil then
    AEnumDesc := Ref.EnumDesc
  else if Ref.EnumDesc <> AEnumDesc then
    SemanticError(Format(
      'Set constant ''%s'' mixes members of ''%s'' and ''%s''',
      [ACD.Name, AEnumDesc.Name, Ref.EnumDesc.Name]), ACD.Line, ACD.Col);
  Result := Integer(Ref.Ordinal);
end;

procedure TSemanticAnalyser.AnalyseSetConstDecl(ACD: TConstDecl);
var
  I:         Integer;
  Mask:      Int64;
  MemName:   string;
  MemSym:    TSymbol;
  EnumDesc:  TEnumTypeDesc;
  SetDesc:   TSetTypeDesc;
  DeclTD:    TTypeDesc;
  CanonName: string;
  ExistTD:   TTypeDesc;
  Sym:       TSymbol;
  Ords:      TStringList;
  Ord, BIdx, NB, BVal: Integer;
  DotPos, Lo, Hi: Integer;
  LoStr, HiStr: string;
begin
  Mask     := 0;
  EnumDesc := nil;
  Ords     := TStringList.Create();

  { Resolve each member to an enum constant; record its ordinal and pin down
    the shared base enum.  The bitmask (small set) or byte bitmap (jumbo set)
    is built AFTER the set type is known, so we never `shl` by an ordinal >= 64
    (undefined) before we know whether the set is jumbo. }
  for I := 0 to ACD.SetElements.Count - 1 do
  begin
    MemName := ACD.SetElements.Strings[I];
    DotPos  := Pos('..', MemName);
    if DotPos >= 0 then
    begin
      { Inclusive range lo..hi — resolve both endpoints to ordinals and add
        every value in between. }
      LoStr := Copy(MemName, 0, DotPos);
      HiStr := Copy(MemName, DotPos + 2, Length(MemName) - DotPos - 2);
      Lo := Self.ResolveSetMemberOrd(LoStr, ACD, EnumDesc);
      Hi := Self.ResolveSetMemberOrd(HiStr, ACD, EnumDesc);
      if Hi < Lo then
        SemanticError(Format(
          'Set constant ''%s'' range %s..%s is descending', [ACD.Name, LoStr, HiStr]),
          ACD.Line, ACD.Col);
      for Ord := Lo to Hi do
        Ords.Add(IntToStr(Ord));
    end
    else
      Ords.Add(IntToStr(Self.ResolveSetMemberOrd(MemName, ACD, EnumDesc)));
  end;

  { Determine the set type descriptor. }
  if ACD.TypeName <> '' then
  begin
    { Declared set type: const X: TSomeSet = [...].  Must be a set, and its
      base enum must match the members. }
    DeclTD := FTable.FindType(ACD.TypeName);
    if (DeclTD = nil) or (DeclTD.Kind <> tySet) then
    begin
      SemanticError(Format(
        'Type ''%s'' in set constant ''%s'' is not a set type',
        [ACD.TypeName, ACD.Name]), ACD.Line, ACD.Col);
      Exit;
    end;
    SetDesc := TSetTypeDesc(DeclTD);
    if (EnumDesc <> nil) and (SetDesc.BaseType <> EnumDesc) then
    begin
      SemanticError(Format(
        'Set constant ''%s'' members are ''%s'' but type ''%s'' is set of ''%s''',
        [ACD.Name, EnumDesc.Name, ACD.TypeName, SetDesc.BaseType.Name]),
        ACD.Line, ACD.Col);
      Exit;
    end;
  end
  else if EnumDesc <> nil then
  begin
    if EnumDesc.Members.Count > 256 then
      SemanticError(
        Format('Enumeration ''%s'' has %d members; set types support at most 256',
          [EnumDesc.Name, EnumDesc.Members.Count]),
        ACD.Line, ACD.Col);
    { Inferred set type: find or create the canonical 'set of <Enum>'. }
    CanonName := 'set of ' + EnumDesc.Name;
    ExistTD   := FTable.FindType(CanonName);
    if (ExistTD <> nil) and (ExistTD.Kind = tySet) then
      SetDesc := TSetTypeDesc(ExistTD)
    else
    begin
      SetDesc := FTable.NewSetType(CanonName, EnumDesc);
      FTable.DefineGlobal(TSymbol.Create(CanonName, skType, SetDesc));
    end;
  end
  else
  begin
    { Empty set with no type annotation: nothing to infer the base enum from. }
    SemanticError(Format(
      'Empty set constant ''%s'' needs an explicit set type (const %s: TSet = [])',
      [ACD.Name, ACD.Name]), ACD.Line, ACD.Col);
    Exit;
  end;

  Sym := TSymbol.Create(ACD.Name, skConstant, SetDesc);
  if SetDesc.IsJumbo() then
  begin
    { Jumbo set const: build a byte-array bitmap; the mask can't fit in Int64. }
    NB := SetDesc.RawByteSize();
    ACD.ConstSetBytes := TStringList.Create();
    for I := 0 to NB - 1 do
      ACD.ConstSetBytes.Add('0');
    for I := 0 to Ords.Count - 1 do
    begin
      Ord  := StrToInt(Ords.Strings[I]);
      BIdx := Ord shr 3;
      BVal := StrToInt(ACD.ConstSetBytes.Strings[BIdx]) or (1 shl (Ord and 7));
      ACD.ConstSetBytes.Put(BIdx, IntToStr(BVal));
    end;
    Sym.ConstSetBytes := TStringList.Create();
    for I := 0 to ACD.ConstSetBytes.Count - 1 do
      Sym.ConstSetBytes.Add(ACD.ConstSetBytes.Strings[I]);
    { Mangled, file-local data label for the bitmap blob (mirrors array
      consts), shared by the decl and the symbol so reads resolve to it. }
    if ACD.ResolvedSetQbeName = '' then
      ACD.ResolvedSetQbeName := Self.NewArrayConstLabel(ACD.Name);
    Sym.ConstSetQbe := ACD.ResolvedSetQbeName;
    ACD.IntVal     := 0;
    Sym.ConstValue := 0;
  end
  else
  begin
    { Small set: pack into the Int64 bitmask (existing fast path). }
    for I := 0 to Ords.Count - 1 do
      Mask := Mask or (Int64(1) shl StrToInt(Ords.Strings[I]));
    ACD.IntVal     := Mask;
    Sym.ConstValue := Mask;
  end;
  if not FTable.Define(Sym) then
    Sym.Free();   { duplicate — cross-unit shadowing tolerated, like scalar consts }
end;

procedure TSemanticAnalyser.AnalyseConstDecls(ABlock: TBlock);
var
  I, J:   Integer;
  CD:     TConstDecl;
  Sym:    TSymbol;
  RefSym: TSymbol;
  Prev:   TSymbol;
  TD:     TTypeDesc;
  Resolved: string;
  IsSameBlockDup: Boolean;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    if CD.IsArrayConst then Continue;  { handled by AnalyseArrayConstDecls }

    if CD.IsString and (CD.ConstParts <> nil) then
    begin
      Resolved := '';
      for J := 0 to CD.ConstParts.Count - 1 do
      begin
        if CD.ConstParts.Objects[J] <> nil then
        begin
          RefSym := FTable.Lookup(CD.ConstParts[J]);
          if (RefSym <> nil) and (RefSym.Kind = skConstant) then
            Resolved := Resolved + RefSym.ConstString
          else
            SemanticError(Format('Undeclared constant ''%s''', [CD.ConstParts[J]]),
                          CD.Line, CD.Col);
        end
        else
          Resolved := Resolved + CD.ConstParts[J];
      end;
      CD.StrVal := Resolved;
    end;
    { Deferred bit-op expression: fold now using the already-defined
      named-constant values in scope. }
    if CD.IntExprTokens <> nil then
      CD.IntVal := FoldConstBitOpExpr(CD.IntExprTokens, CD.Line, CD.Col);
    if (CD.IntValueExpr <> nil) and IsFloatConstExpr(CD.IntValueExpr) then
    begin
      CD.StrVal  := EvalConstFloatExpr(CD.IntValueExpr, CD.Line, CD.Col);
      CD.IsFloat := True;
      CD.IsString := False;
    end
    else if CD.IntValueExpr <> nil then
      CD.IntVal := EvalConstIntExpr(CD.IntValueExpr, CD.Line, CD.Col);
    { Set-valued constants reference enum members, which are not registered
      until AnalyseTypeDecls runs — so they are resolved in the second pass
      (AnalyseArrayConstDecls), like array consts. }
    if CD.IsSet then Continue;
    if CD.TypeName <> '' then
    begin
      TD := FTable.FindType(CD.TypeName);
      if TD = nil then
        SemanticError(Format('Unknown type ''%s'' in typed constant ''%s''',
          [CD.TypeName, CD.Name]), CD.Line, CD.Col);
      if (not CD.IsFloat) and (not CD.IsString) and
         (TD <> nil) and (TD.Kind in [tyDouble, tySingle]) then
      begin
        CD.StrVal  := IntToStr(CD.IntVal);
        CD.IsFloat := True;
      end;
    end
    else if CD.IsString then
      TD := FTable.TypeString
    else if CD.IsFloat then
      TD := FTable.TypeDouble
    { Untyped integer constant: pick the width by magnitude so a value that does
      not fit in 32 bits is NOT silently truncated to Integer (issue #133).  A
      UInt64-range bit pattern (above High(Int64)) types as UInt64; a value
      outside the signed 32-bit range types as Int64; otherwise Integer. }
    else if CD.IsUInt64 then
      TD := FTable.TypeUInt64
    else if (CD.IntVal > 2147483647) or (CD.IntVal < -2147483648) then
      TD := FTable.TypeInt64
    else
      TD := FTable.TypeInteger;
    Sym              := TSymbol.Create(CD.Name, skConstant, TD);
    Sym.ConstValue   := CD.IntVal;
    Sym.ConstString  := CD.StrVal;
    if not FTable.Define(Sym) then
    begin
      { A module-name marker blocking the Define is always a hard error
        (issue #84). }
      RefSym := FTable.CurrentScope.LookupLocal(CD.Name);
      if (RefSym <> nil) and (RefSym.Kind = skModule) then
      begin
        Sym.Free();
        SemanticError(Format('Duplicate identifier ''%s''', [CD.Name]),
          CD.Line, CD.Col);
      end;
      { Same-block duplicate (the unit declares the name twice itself) is a
        hard error. }
      IsSameBlockDup := False;
      for J := 0 to I - 1 do
        if SameText(TConstDecl(ABlock.ConstDecls.Items[J]).Name, CD.Name) then
        begin
          IsSameBlockDup := True;
          Break;
        end;
      if IsSameBlockDup then
      begin
        Sym.Free();
        SemanticError(Format('Duplicate identifier ''%s''', [CD.Name]), CD.Line, CD.Col);
      end;
      { Cross-unit collision: last-in-uses wins.  Detach the prior unit's
        const and stash it in the per-unit cache so a qualified reference
        (Unit.Const) can still reach the shadowed value; install this unit's
        const as the flat winner.  Mirrors RegisterConsts on the prebuilt-
        import path so source-loaded and prebuilt deps behave identically. }
      Prev := FTable.ExtractLocal(CD.Name);
      if (Prev <> nil) and (Prev.OwningUnit <> '') then
        RegisterUnitSymbol(Prev.OwningUnit, Prev);
      FTable.Define(Sym);
    end;
    { Register every interface const in the per-unit cache keyed by its owning
      unit, so a qualified reference resolves against the declaring unit's own
      value regardless of which unit won the bare (flat) slot. }
    if Sym.OwningUnit <> '' then
      RegisterUnitSymbol(Sym.OwningUnit, Sym);
  end;
end;

procedure TSemanticAnalyser.DefineGlobalLastWins(ASym: TSymbol;
  ALine, ACol: Integer);
var
  RefSym: TSymbol;
  Prev:   TSymbol;
begin
  if not FTable.Define(ASym) then
  begin
    RefSym := FTable.CurrentScope.LookupLocal(ASym.Name);
    { A module-name marker (issue #84), a non-unit symbol (builtin /
      program-scope, OwningUnit = ''), or a same-unit redeclaration
      blocking the Define is a hard error — only a genuine cross-unit
      collision (two used units exporting the same name) gets last-wins. }
    if (RefSym = nil) or (RefSym.Kind = skModule) or
       (RefSym.OwningUnit = '') or
       SameText(RefSym.OwningUnit, ASym.OwningUnit) then
    begin
      ASym.Free();
      SemanticError(Format('Duplicate identifier ''%s''', [ASym.Name]),
        ALine, ACol);
      Exit;
    end;
    { Cross-unit collision: last-in-uses wins.  Detach the prior unit's
      var and stash it in the per-unit cache so a qualified reference
      (Unit.Var) can still reach the shadowed slot; install this unit's
      var as the flat winner.  Mirrors AnalyseConstDecls and RegisterVars. }
    Prev := FTable.ExtractLocal(ASym.Name);
    if (Prev <> nil) and (Prev.OwningUnit <> '') then
      RegisterUnitSymbol(Prev.OwningUnit, Prev);
    FTable.Define(ASym);
  end;
  { Register every interface var in the per-unit cache keyed by its owning
    unit, so a qualified reference resolves against the declaring unit's own
    slot regardless of which unit won the bare (flat) slot. }
  if ASym.OwningUnit <> '' then
    RegisterUnitSymbol(ASym.OwningUnit, ASym);
end;

procedure TSemanticAnalyser.DefineTypeLastWins(ASym: TSymbol;
  ATypeDecl: TTypeDecl; ALine, ACol: Integer);
var
  RefSym: TSymbol;
  Prev:   TSymbol;
  AName:  string;
begin
  AName := ATypeDecl.Name;
  { Record the descriptor created for THIS decl so codegen can emit this unit's
    own type even after a same-named type from another used unit wins the flat
    slot (extracted below). }
  ATypeDecl.ResolvedDesc := ASym.TypeDesc;
  if not FTable.Define(ASym) then
  begin
    RefSym := FTable.CurrentScope.LookupLocal(AName);
    { Only a genuine cross-unit collision (two used units exporting the same
      type name) gets last-wins; a module marker, a non-unit symbol, or a
      same-unit redeclaration stays a hard error. }
    if (RefSym = nil) or (RefSym.Kind = skModule) or
       (RefSym.OwningUnit = '') or
       SameText(RefSym.OwningUnit, ASym.OwningUnit) then
    begin
      ASym.Free();
      SemanticError(Format('Duplicate type name ''%s''', [AName]), ALine, ACol);
      Exit;
    end;
    { Detach the prior unit's type and stash it in the per-unit cache so a
      qualified reference (Unit.Type) still resolves against it; install this
      unit's type as the flat winner. }
    Prev := FTable.ExtractLocal(AName);
    if (Prev <> nil) and (Prev.OwningUnit <> '') then
      RegisterUnitSymbol(Prev.OwningUnit, Prev);
    FTable.Define(ASym);
  end;
  { Register every type in the per-unit cache keyed by its owning unit, so a
    qualified reference resolves against the declaring unit regardless of which
    unit won the bare (flat) slot. }
  if ASym.OwningUnit <> '' then
    RegisterUnitSymbol(ASym.OwningUnit, ASym);
end;

function TSemanticAnalyser.NewArrayConstLabel(const AName: string): string;
begin
  Inc(FArrayConstCounter);
  Result := Format('__bac_%d_%s', [FArrayConstCounter, AName]);
end;

function TSemanticAnalyser.BuildConstArrayType(ACD: TConstDecl;
  AElemTD: TTypeDesc): TStaticArrayTypeDesc;
var
  D, Lo, Hi: Integer;
  Expected:  Integer;
  Inner:     TTypeDesc;
begin
  { Multi-dimensional: build the nested type innermost-first and require the
    flat element count to equal the product of all dimension extents. }
  if (ACD.ArrayDimLows <> nil) and (ACD.ArrayDimLows.Count > 1) then
  begin
    Expected := 1;
    for D := 0 to ACD.ArrayDimLows.Count - 1 do
    begin
      Lo := ResolveArrayBound(ACD.ArrayDimLows.Strings[D]);
      Hi := ResolveArrayBound(ACD.ArrayDimHighs.Strings[D]);
      Expected := Expected * (Hi - Lo + 1);
    end;
    if ACD.ArrayElements.Count <> Expected then
      SemanticError(Format(
        'Array const ''%s'' has %d element(s) but its dimensions need %d',
        [ACD.Name, ACD.ArrayElements.Count, Expected]),
        ACD.Line, ACD.Col);
    Inner := AElemTD;
    for D := ACD.ArrayDimLows.Count - 1 downto 0 do
    begin
      Lo := ResolveArrayBound(ACD.ArrayDimLows.Strings[D]);
      Hi := ResolveArrayBound(ACD.ArrayDimHighs.Strings[D]);
      Inner := FTable.NewStaticArrayType(Inner, Lo, Hi);
    end;
    Result := TStaticArrayTypeDesc(Inner);
    Exit;
  end;
  { Single dimension — resolve from dim lists (parser stores raw text). }
  if (ACD.ArrayDimLows <> nil) and (ACD.ArrayDimLows.Count = 1) then
  begin
    ACD.ArrayLowBound  := ResolveArrayBound(ACD.ArrayDimLows.Strings[0]);
    ACD.ArrayHighBound := ResolveArrayBound(ACD.ArrayDimHighs.Strings[0]);
  end;
  Expected := ACD.ArrayHighBound - ACD.ArrayLowBound + 1;
  if ACD.ArrayElements.Count <> Expected then
    SemanticError(Format(
      'Array const ''%s'' has %d element(s) but range [%d..%d] needs %d',
      [ACD.Name, ACD.ArrayElements.Count, ACD.ArrayLowBound,
       ACD.ArrayHighBound, Expected]),
      ACD.Line, ACD.Col);
  Result := FTable.NewStaticArrayType(AElemTD, ACD.ArrayLowBound,
    ACD.ArrayHighBound);
end;

procedure TSemanticAnalyser.AnalyseArrayConstDecls(ABlock: TBlock);
{ Second-pass constant analysis for array-typed constants.
  Called after AnalyseTypeDecls so that enum index types are in scope. }
var
  I, J:     Integer;
  CD:       TConstDecl;
  Sym:      TSymbol;
  RefSym:   TSymbol;
  ElemTD:   TTypeDesc;
  IdxTD:    TTypeDesc;
  ArrTD:    TStaticArrayTypeDesc;
  EnumDesc: TEnumTypeDesc;
  Expected: Integer;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    { Set-valued constants are resolved here too — enum members are now in
      scope (AnalyseTypeDecls ran before this pass). }
    if CD.IsSet then
    begin
      AnalyseSetConstDecl(CD);
      Continue;
    end;
    if not CD.IsArrayConst then Continue;
    if (CD.ArrayElemType = '') and (CD.TypeName <> '') then
    begin
      ElemTD := FTable.FindType(CD.TypeName);
      if ElemTD = nil then
        SemanticError(Format('Unknown type ''%s'' in typed constant ''%s''',
          [CD.TypeName, CD.Name]), CD.Line, CD.Col);
      if ElemTD.Kind <> tyStaticArray then
        SemanticError(Format('Type ''%s'' is not a static array in typed constant ''%s''',
          [CD.TypeName, CD.Name]), CD.Line, CD.Col);
      ArrTD := TStaticArrayTypeDesc(ElemTD);
      Expected := ArrTD.HighBound - ArrTD.LowBound + 1;
      if CD.ArrayElements.Count <> Expected then
        SemanticError(Format(
          'Array const ''%s'' has %d element(s) but type ''%s'' expects %d',
          [CD.Name, CD.ArrayElements.Count, CD.TypeName, Expected]),
          CD.Line, CD.Col);
    end
    else
    begin
      ElemTD := FTable.FindType(CD.ArrayElemType);
      if ElemTD = nil then
        SemanticError(Format('Unknown element type ''%s'' in array const ''%s''',
          [CD.ArrayElemType, CD.Name]), CD.Line, CD.Col);
      if CD.ArrayIsRangeIndexed then
        ArrTD := Self.BuildConstArrayType(CD, ElemTD)
      else
      begin
        IdxTD := FTable.FindType(CD.ArrayIndexType);
        if IdxTD = nil then
          SemanticError(Format('Unknown index type ''%s'' in array const ''%s''',
            [CD.ArrayIndexType, CD.Name]), CD.Line, CD.Col);
        if IdxTD.Kind <> tyEnum then
          SemanticError(Format('Array const index type must be an enum, got ''%s''',
            [IdxTD.Name]), CD.Line, CD.Col);
        EnumDesc := TEnumTypeDesc(IdxTD);
        { An enum-SUBRANGE index (TTurn = East..South) spans only its own
          ordinal bounds — the descriptor copies the base enum's members, so
          Members.Count is the FULL enum width (GH #182 follow-up).  The
          array's bounds are the subrange ordinals, so element reads index
          relative to SubrangeLow. }
        if EnumDesc.IsSubrange then
          Expected := EnumDesc.SubrangeHigh - EnumDesc.SubrangeLow + 1
        else
          Expected := EnumDesc.Members.Count;
        if CD.ArrayElements.Count <> Expected then
          SemanticError(Format(
            'Array const ''%s'' has %d element(s) but index type ''%s'' has %d member(s)',
            [CD.Name, CD.ArrayElements.Count, CD.ArrayIndexType, Expected]),
            CD.Line, CD.Col);
        if EnumDesc.IsSubrange then
          ArrTD := FTable.NewStaticArrayType(ElemTD,
            EnumDesc.SubrangeLow, EnumDesc.SubrangeHigh)
        else
          ArrTD := FTable.NewStaticArrayType(ElemTD, 0, Expected - 1);
      end;
    end;
    { Fold any deferred bit-op expressions into their final integer
      strings in ArrayElements before publishing to the symbol. }
    if CD.ArrayElementParts <> nil then
      for J := 0 to CD.ArrayElementParts.Count - 1 do
        if (CD.ArrayElementParts.Items[J] <> nil) and
           (J < CD.ArrayElements.Count) then
          CD.ArrayElements.Put(J, IntToStr(FoldConstBitOpExpr(
            TStringList(CD.ArrayElementParts.Items[J]), CD.Line, CD.Col)));
    { Resolve bare-identifier elements to their numeric values so codegen emits
      integer constants, not symbol references.  The parser stores identifiers
      verbatim (it does not know the element type yet); here ElemTD is known.
      Covers Boolean literals (False/True -> 0/1), enum members (-> ordinal),
      and named integer/boolean constants. }
    if (ElemTD <> nil) and
       ((ElemTD.Kind in [tyBoolean, tyEnum]) or
        (ElemTD.IsNumeric() and not (ElemTD.Kind in [tyDouble, tySingle]))) then
      for J := 0 to CD.ArrayElements.Count - 1 do
        CD.ArrayElements.Put(J,
          Self.ResolveConstArrayElem(CD.ArrayElements[J], ElemTD,
                                     CD.Line, CD.Col));
    if CD.ResolvedQbeName = '' then
      CD.ResolvedQbeName := Self.NewArrayConstLabel(CD.Name);
    Sym := TSymbol.Create(CD.Name, skConstant, ArrTD);
    Sym.IsGlobal := True;
    Sym.ConstArrayQbe := CD.ResolvedQbeName;
    Sym.ConstArray := TStringList.Create();
    for J := 0 to CD.ArrayElements.Count - 1 do
      Sym.ConstArray.Add(CD.ArrayElements[J]);
    if not FTable.Define(Sym) then
    begin
      Sym.Free();
      { A module-name marker blocking the Define is a hard error
        (issue #84); other clashes keep the silent-skip tolerance. }
      RefSym := FTable.CurrentScope.LookupLocal(CD.Name);
      if (RefSym <> nil) and (RefSym.Kind = skModule) then
        SemanticError(Format('Duplicate identifier ''%s''', [CD.Name]),
          CD.Line, CD.Col);
    end;
  end;
end;

{ Return AName in the casing of the matching method declaration, or AName
  unchanged when no declaration matches.  Property accessor names must use
  the method's declared casing — emitted method symbols are case-sensitive
  at link time, while Pascal name resolution is not. }
function DeclaredMethodCase(AMethods: TObjectList; const AName: string): string;
var
  I: Integer;
begin
  Result := AName;
  if AMethods = nil then Exit;
  for I := 0 to AMethods.Count - 1 do
    if SameText(TMethodDecl(AMethods.Items[I]).Name, AName) then
      Exit(TMethodDecl(AMethods.Items[I]).Name);
end;

procedure TSemanticAnalyser.AnalyseTypeDecls(ABlock: TBlock);
var
  I, J, K:    Integer;
  L:          Integer;
  TD:         TTypeDecl;
  FieldList:  TObjectList;
  MethodList: TObjectList;
  Grp:        TObjectList;
  FDecl:      TFieldDecl;
  ClassVarEmit: string;
  MDecl:      TMethodDecl;
  Par:        TMethodParam;
  ParType:    TTypeDesc;
  RT:         TRecordTypeDesc;
  ParentRT:   TRecordTypeDesc;
  ParentSym:  TSymbol;
  GenParentDesc: TTypeDesc;
  FldType:    TTypeDesc;
  FldName:    string;
  Sym:        TSymbol;
  Key:        string;
  FldInfo:    TFieldInfo;
  IntfDesc:   TInterfaceTypeDesc;
  IntfName:   string;
  IntfSym:    TSymbol;
  ITD:        TInterfaceTypeDef;
  PropDecl:   TPropertyDecl;
  PropInfo:   TPropertyInfo;
  PropType:   TTypeDesc;
  EnumDesc:   TEnumTypeDesc;
  EnumDef:    TEnumTypeDef;
  SubEnum:    TEnumTypeDesc;
  LowRef:     TEnumMemberRef;
  HighRef:    TEnumMemberRef;
  SetDesc:    TSetTypeDesc;
  SetSubDesc: TSetTypeDesc;
  SetDef:     TSetTypeDef;
  AttrIdx:    Integer;
  RawAttr:    string;
  Resolved:   string;
  AttrUse:    TAttributeUse;
  BaseSym:    TSymbol;
  MName:      string;
  Slot:       Integer;
  CD:         TConstDecl;
  AliasDef:   TTypeAliasDef;
  AliasName:  string;
  AliasDesc:  TTypeDesc;
  BaseName:   string;
  BaseType:   TTypeDesc;
  MangledKey: string;
  VarFlags:   string;
  ElemTD:     TTypeDesc;
  IdxTD:      TTypeDesc;
  ArrTD:      TStaticArrayTypeDesc;
  Expected:   Integer;
  ForwardDecls: TStringList;  { names of bare forward class/interface decls still
                               awaiting their completing full declaration }
  FwdIdx:     Integer;
  FwdType:    TTypeDesc;
begin
  { Forward declarations (`TFoo = class;` / `IFoo = interface;`) register a
    placeholder type in pass 1 and are completed by a later full declaration of
    the same name in this scope.  Track the pending ones so a never-completed
    forward is reported as an error. }
  ForwardDecls := TStringList.Create();
  ForwardDecls.CaseSensitive := False;
  { Pass 1 — register all type symbols with empty descriptors.
    This allows self-referential field types to resolve in pass 2. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TRecordTypeDef then
    begin
      RT := FTable.NewRecordType(TD.Name);
      RT.IsPacked := TRecordTypeDef(TD.Def).IsPacked;
    end
    else if TD.Def is TClassTypeDef then
    begin
      if TClassTypeDef(TD.Def).IsForward then
      begin
        { Forward class: register a placeholder class type so intervening
          declarations can name it.  A name already in the table — including a
          prior forward — is a redeclaration. }
        if FTable.Lookup(TD.Name) <> nil then
        begin
          if ForwardDecls.IndexOf(TD.Name) >= 0 then
            SemanticError(Format('Duplicate forward type declaration ''%s''',
              [TD.Name]), TD.Line, TD.Col)
          else
            SemanticError(Format('Duplicate type name ''%s''', [TD.Name]),
              TD.Line, TD.Col);
        end;
        Sym := TSymbol.Create(TD.Name, skType, FTable.NewClassType(TD.Name));
        FTable.Define(Sym);
        ForwardDecls.AddObject(TD.Name, TD);
        Continue;
      end;
      { Full class declaration completing a pending forward: reuse the
        placeholder descriptor (pass 2 re-derives it by name) — skip the
        re-registration below. }
      FwdIdx := ForwardDecls.IndexOf(TD.Name);
      if FwdIdx >= 0 then
      begin
        { The placeholder was registered under the forward declaration's name
          spelling.  Adopt the completing declaration's spelling on the shared
          descriptor so it matches the TTypeDecl the codegen keys a class's
          storage symbols (_FieldCleanup / typeinfo / vtable) on.  Without this
          a case-only difference between the two spellings (e.g. `TState = class;`
          then `Tstate = class ... end;`) leaves instantiation sites — which read
          the descriptor Name — referencing `_FieldCleanup_TState` while the
          definition is emitted under `_FieldCleanup_Tstate`, an undefined-symbol
          link failure. }
        FwdType := FTable.FindType(TD.Name);
        if FwdType <> nil then
          FwdType.Name := TD.Name;
        ForwardDecls.Delete(FwdIdx);
        Continue;
      end;
      RT := FTable.NewClassType(TD.Name);
    end
    else if TD.Def is TGenericTypeDef then
    begin
      { Register as template — no concrete type symbol; instantiated on demand.
        Record the declaring unit so allocation sites inside cloned method
        bodies are attributed to the template's source, not the instantiator. }
      TGenericTypeDef(TD.Def).DefUnitName := FCurrentUnitName;
      CheckedRegisterGeneric(TD);
      Continue;
    end
    else if TD.Def is TGenericRecordDef then
    begin
      CheckedRegisterGeneric(TD);
      Continue;
    end
    else if TD.Def is TGenericInterfaceDef then
    begin
      { Register as template — instantiated on demand when used as type name }
      CheckedRegisterGeneric(TD);
      Continue;
    end
    else if TD.Def is TGenericProcDef then
    begin
      { Register as template — instantiated on demand when used as type name.
        A monomorphised procedural type is pure metadata (no code emission),
        so there is no instance list. }
      CheckedRegisterGeneric(TD);
      Continue;
    end
    else if TD.Def is TInterfaceTypeDef then
    begin
      if TInterfaceTypeDef(TD.Def).IsForward then
      begin
        { Forward interface: placeholder, completed later in scope. }
        if FTable.Lookup(TD.Name) <> nil then
        begin
          if ForwardDecls.IndexOf(TD.Name) >= 0 then
            SemanticError(Format('Duplicate forward type declaration ''%s''',
              [TD.Name]), TD.Line, TD.Col)
          else
            SemanticError(Format('Duplicate type name ''%s''', [TD.Name]),
              TD.Line, TD.Col);
        end;
        Sym := TSymbol.Create(TD.Name, skType, FTable.NewInterfaceType(TD.Name));
        FTable.Define(Sym);
        ForwardDecls.AddObject(TD.Name, TD);
        Continue;
      end;
      { Full interface completing a pending forward: reuse the placeholder. }
      FwdIdx := ForwardDecls.IndexOf(TD.Name);
      if FwdIdx >= 0 then
      begin
        ForwardDecls.Delete(FwdIdx);
        Continue;
      end;
      IntfDesc := FTable.NewInterfaceType(TD.Name);
      Sym      := TSymbol.Create(TD.Name, skType, IntfDesc);
      DefineTypeLastWins(Sym, TD, TD.Line, TD.Col);
      Continue;
    end
    else if TD.Def is TEnumTypeDef then
    begin
      { Enum type: register the type, and record each member in the reverse
        index keyed by name.  Members are NOT registered as bare global
        skConstants — a bare member name resolves through ResolveEnumMember
        (by context type, uniqueness, or last-wins), so two enums in scope
        may legitimately share a member name without colliding. }
      EnumDef  := TEnumTypeDef(TD.Def);
      EnumDesc := FTable.NewEnumType(TD.Name);
      for K := 0 to EnumDef.Members.Count - 1 do
      begin
        MName := EnumDef.Members.Strings[K];
        { Carry the explicit ordinal onto the descriptor so High/Low fold
          from the real max/min (BUG-20260720-enum-explicit-ordinal-highlow). }
        EnumDesc.AddMember(MName, EnumDef.OrdinalAt(K));
        RegisterEnumMember(MName, EnumDesc, EnumDef.OrdinalAt(K));
      end;
      Sym := TSymbol.Create(TD.Name, skType, EnumDesc);
      DefineTypeLastWins(Sym, TD, TD.Line, TD.Col);
      Continue;
    end
    else if TD.Def is TSetTypeDef then
    begin
      SetDef   := TSetTypeDef(TD.Def);
      { Integer-subrange base type ('lo..hi', e.g. set of 0..255): build an
        ordinal set sized by the high bound (validated 0..255), bound to this
        type's name. }
      if StrPos('..', SetDef.BaseTypeName) >= 0 then
      begin
        SetSubDesc := Self.ResolveSubrangeSetType(SetDef.BaseTypeName);
        SetDesc := FTable.NewOrdinalSetType(TD.Name, SetSubDesc.BaseType,
                                            SetSubDesc.BitCount);
        Sym := TSymbol.Create(TD.Name, skType, SetDesc);
        DefineTypeLastWins(Sym, TD, TD.Line, TD.Col);
        Continue;
      end;
      BaseSym  := FTable.Lookup(SetDef.BaseTypeName);
      if (BaseSym = nil) or (BaseSym.Kind <> skType) then
        SemanticError(
          Format('Set base type ''%s'' is not a known type', [SetDef.BaseTypeName]),
          TD.Line, TD.Col);
      if BaseSym.TypeDesc is TEnumTypeDesc then
      begin
        if TEnumTypeDesc(BaseSym.TypeDesc).Members.Count > 256 then
          SemanticError(
            Format('Enumeration ''%s'' has %d members; set types support at most 256',
              [SetDef.BaseTypeName, TEnumTypeDesc(BaseSym.TypeDesc).Members.Count]),
            TD.Line, TD.Col);
        SetDesc := FTable.NewSetType(TD.Name, TEnumTypeDesc(BaseSym.TypeDesc));
      end
      else if BaseSym.TypeDesc.Kind = tyByte then
        SetDesc := FTable.NewOrdinalSetType(TD.Name, BaseSym.TypeDesc, 256)
      else if BaseSym.TypeDesc.Kind = tyBoolean then
        SetDesc := FTable.NewOrdinalSetType(TD.Name, BaseSym.TypeDesc, 2)
      else
      begin
        SemanticError(
          Format('Set base type ''%s'' must be an enumeration, Byte, or Boolean',
            [SetDef.BaseTypeName]),
          TD.Line, TD.Col);
        SetDesc := nil;
      end;
      Sym := TSymbol.Create(TD.Name, skType, SetDesc);
      DefineTypeLastWins(Sym, TD, TD.Line, TD.Col);
      Continue;
    end
    else if TD.Def is TProceduralTypeDef then
    begin
      { Procedural type: register an empty TProceduralTypeDesc; param/return
        resolution happens in pass 2. }
      Sym := TSymbol.Create(TD.Name, skType,
                            FTable.NewProceduralType(TD.Name));
      DefineTypeLastWins(Sym, TD, TD.Line, TD.Col);
      Continue;
    end
    else if TD.Def is TTypeAliasDef then
    begin
      { Type alias or pointer alias: resolve the named type and register
        a new symbol pointing at either the base type (simple alias) or
        a fresh TPointerTypeDesc (pointer alias '^T'). }
      AliasDef  := TTypeAliasDef(TD.Def);
      AliasName := AliasDef.TypeName;
      if (Length(AliasName) > 0) and (StrAt(AliasName, 0) = Ord('^')) then
      begin
        { Pointer alias: ^BaseName — base may not be registered yet
          (forward reference); leave BaseType nil for now (untyped
          pointer semantics — safe for punit's usage pattern). }
        BaseName := StrCopyTail(AliasName, 1);
        BaseSym  := FTable.Lookup(BaseName);
        BaseType := nil;
        if (BaseSym <> nil) and (BaseSym.Kind = skType) then
          BaseType := BaseSym.TypeDesc;
        AliasDesc := FTable.NewPointerType(TD.Name, BaseType);
      end
      else if (Length(AliasName) > 9) and (StrHead(AliasName, 9) = 'class of ') then
      begin
        { Metaclass alias: 'class of TFoo'.  Route through the standard
          on-demand instantiation path so the underlying class type is
          resolved consistently with other 'class of TFoo' references. }
        AliasDesc := FindTypeOrInstantiate(AliasName);
        if AliasDesc = nil then
        begin
          SemanticError(
            Format('Unknown class type in metaclass alias ''%s''', [AliasName]),
            TD.Line, TD.Col);
          Continue;
        end;
      end
      else if AliasDef.IsSubrange and (AliasDef.SubrangeLowName <> '') then
      begin
        { Enum-member subrange: type TSub = zwei..drei;  Resolve both member
          names to a common enum and its member ordinals, then build a DISTINCT
          enum descriptor (with the base enum's members copied, so every
          tyEnum-cast path stays valid) carrying IsSubrange + the ordinal bounds
          — the array-index resolver and the High/Low fold read them (GH #182). }
        LowRef := ResolveEnumMember(AliasDef.SubrangeLowName, nil);
        HighRef := ResolveEnumMember(AliasDef.SubrangeHighName, nil);
        if (LowRef = nil) or (HighRef = nil) then
        begin
          SemanticError(Format(
            'Unknown enum member in subrange ''%s..%s''',
            [AliasDef.SubrangeLowName, AliasDef.SubrangeHighName]), TD.Line, TD.Col);
          Continue;
        end;
        if LowRef.EnumDesc <> HighRef.EnumDesc then
        begin
          SemanticError(Format(
            'Subrange bounds ''%s'' and ''%s'' are from different enum types',
            [AliasDef.SubrangeLowName, AliasDef.SubrangeHighName]), TD.Line, TD.Col);
          Continue;
        end;
        if HighRef.Ordinal < LowRef.Ordinal then
        begin
          SemanticError(Format('Subrange ''%s..%s'' is descending',
            [AliasDef.SubrangeLowName, AliasDef.SubrangeHighName]), TD.Line, TD.Col);
          Continue;
        end;
        SubEnum := FTable.NewEnumType(TD.Name);
        for K := 0 to LowRef.EnumDesc.Members.Count - 1 do
          SubEnum.AddMember(LowRef.EnumDesc.Members.Strings[K],
            LowRef.EnumDesc.OrdinalAt(K));
        SubEnum.IsSubrange := True;
        SubEnum.SubrangeLow := LowRef.Ordinal;
        SubEnum.SubrangeHigh := HighRef.Ordinal;
        AliasDesc := SubEnum;
      end
      else if AliasDef.IsSubrange then
      begin
        { Named integer subrange: type TIdx = lo..hi;  AliasName is the
          narrowest fitting standard integer type (e.g. 'Byte').  Create a
          DISTINCT descriptor that copies the underlying int's Kind (so layout,
          QBE type, IsNumeric/IsOrdinal and assignment all treat it as that
          int), but carries IsSubrange + the lo..hi bounds so the array-index
          resolver can fold array[TIdx] -> array[lo..hi]. }
        BaseSym := FTable.Lookup(AliasName);
        if (BaseSym = nil) or (BaseSym.Kind <> skType) or (BaseSym.TypeDesc = nil) then
        begin
          SemanticError(Format('Unknown base type ''%s'' for subrange', [AliasName]),
            TD.Line, TD.Col);
          Continue;
        end;
        AliasDesc := FTable.NewType(BaseSym.TypeDesc.Kind, TD.Name);
        AliasDesc.IsSubrange := True;
        AliasDesc.SubrangeLow := AliasDef.SubrangeLow;
        AliasDesc.SubrangeHigh := AliasDef.SubrangeHigh;
      end
      else
      begin
        { Simple alias or constructed alias (array[L..H] of T, etc.).
          Try direct lookup first; fall through to FindTypeOrInstantiate
          for names the symbol table doesn't hold yet (e.g. array types
          that are created on demand). }
        BaseSym := FTable.Lookup(AliasName);
        if (BaseSym <> nil) and (BaseSym.Kind = skType) then
          AliasDesc := BaseSym.TypeDesc
        else
        begin
          AliasDesc := FindTypeOrInstantiate(AliasName);
          if AliasDesc = nil then
          begin
            SemanticError(Format('Unknown type ''%s'' in type alias', [AliasName]),
              TD.Line, TD.Col);
            Continue;
          end;
        end;
      end;
      Sym := TSymbol.Create(TD.Name, skType, AliasDesc);
      DefineTypeLastWins(Sym, TD, TD.Line, TD.Col);
      Continue;
    end
    else
    begin
      SemanticError('Only record, class, interface, enum, set, procedural, or type alias definitions are supported',
        TD.Line, TD.Col);
      Continue;
    end;
    Sym := TSymbol.Create(TD.Name, skType, RT);
    DefineTypeLastWins(Sym, TD, TD.Line, TD.Col);
  end;

  { Pass 2 — resolve parent, fields, and method signatures for each type. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);

    { Generic templates, enum, set, and type alias need no pass-2 processing }
    if TD.Def is TGenericTypeDef then Continue;
    if TD.Def is TGenericRecordDef then Continue;
    if TD.Def is TGenericInterfaceDef then Continue;
    if TD.Def is TGenericProcDef then Continue;
    if TD.Def is TEnumTypeDef then Continue;
    if TD.Def is TSetTypeDef then Continue;
    if TD.Def is TTypeAliasDef then Continue;

    { Forward stub: the completing full declaration (same name, later) carries
      the body and does all pass-2 work. }
    if (TD.Def is TClassTypeDef) and TClassTypeDef(TD.Def).IsForward then Continue;
    if (TD.Def is TInterfaceTypeDef) and TInterfaceTypeDef(TD.Def).IsForward then Continue;

    { Procedural types: resolve param + return types now that all
      type names are registered. }
    if TD.Def is TProceduralTypeDef then
    begin
      ResolveProceduralTypeDef(TD);
      Continue;
    end;

    { Interface types: register methods and resolve optional parent }
    if TD.Def is TInterfaceTypeDef then
    begin
      ITD      := TInterfaceTypeDef(TD.Def);
      IntfSym  := FTable.Lookup(TD.Name);
      IntfDesc := TInterfaceTypeDesc(IntfSym.TypeDesc);
      if ITD.ParentName <> '' then
      begin
        Sym := FTable.Lookup(ITD.ParentName);
        if (Sym = nil) or not (Sym.TypeDesc is TInterfaceTypeDesc) then
          SemanticError(
            Format('Unknown parent interface ''%s'' for ''%s''',
              [ITD.ParentName, TD.Name]),
            TD.Line, TD.Col);
        IntfDesc.Parent := TInterfaceTypeDesc(Sym.TypeDesc);
        { Inherit parent methods (propagate var-param flags too) }
        for J := 0 to IntfDesc.Parent.MethodCount() - 1 do
          IntfDesc.AddMethod(IntfDesc.Parent.MethodName(J),
            IntfDesc.Parent.MethodReturnTypeName(J),
            IntfDesc.Parent.MethodParamVarFlagsStr(J));
      end;
      for J := 0 to ITD.Methods.Count - 1 do
      begin
        MDecl    := TMethodDecl(ITD.Methods.Items[J]);
        VarFlags := '';
        for K := 0 to MDecl.Params.Count - 1 do
        begin
          Par := TMethodParam(MDecl.Params.Items[K]);
          if K > 0 then VarFlags := VarFlags + ',';
          if Par.IsVarParam then VarFlags := VarFlags + '1'
                            else VarFlags := VarFlags + '0';
        end;
        IntfDesc.AddMethod(MDecl.Name, MDecl.ReturnTypeName, VarFlags);
      end;
      { Register interface properties.  Accessors must be methods of the
        interface itself (or an inherited one) — interfaces have no fields,
        so field-backed accessors cannot exist. }
      for J := 0 to ITD.Properties.Count - 1 do
      begin
        PropDecl := TPropertyDecl(ITD.Properties.Items[J]);
        if IntfDesc.FindProperty(PropDecl.Name) <> nil then Continue;
        if (PropDecl.ReadName <> '') and
           not IntfDesc.HasMethod(PropDecl.ReadName) then
          SemanticError(Format(
            'Interface property ''%s.%s'': read accessor ''%s'' is not a method of the interface',
            [TD.Name, PropDecl.Name, PropDecl.ReadName]), TD.Line, TD.Col);
        if (PropDecl.WriteName <> '') and
           not IntfDesc.HasMethod(PropDecl.WriteName) then
          SemanticError(Format(
            'Interface property ''%s.%s'': write accessor ''%s'' is not a method of the interface',
            [TD.Name, PropDecl.Name, PropDecl.WriteName]), TD.Line, TD.Col);
        PropInfo := TPropertyInfo.Create();
        PropInfo.Name := PropDecl.Name;
        PropInfo.TypeDesc := FindTypeOrInstantiate(PropDecl.TypeName);
        if PropInfo.TypeDesc = nil then
        begin
          PropInfo.Free();
          SemanticError(Format(
            'Unknown type ''%s'' for interface property ''%s.%s''',
            [PropDecl.TypeName, TD.Name, PropDecl.Name]), TD.Line, TD.Col);
        end;
        { Canonical method casing — link-time symbols are case-sensitive. }
        if PropDecl.ReadName <> '' then
          PropInfo.ReadMethod :=
            IntfDesc.MethodName(IntfDesc.MethodIndex(PropDecl.ReadName));
        if PropDecl.WriteName <> '' then
          PropInfo.WriteMethod :=
            IntfDesc.MethodName(IntfDesc.MethodIndex(PropDecl.WriteName));
        IntfDesc.AddProperty(PropInfo);
      end;
      Continue;
    end;

    Sym := FTable.Lookup(TD.Name);
    RT  := TRecordTypeDesc(Sym.TypeDesc);

    if TD.Def is TRecordTypeDef then
    begin
      FieldList  := TRecordTypeDef(TD.Def).Fields;
      MethodList := TRecordTypeDef(TD.Def).Methods;
      { Resolve param and return types for record methods. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Items[J]);
          MDecl.IsRecordMethod := True;
          for K := 0 to MDecl.Params.Count - 1 do
          begin
            Par              := TMethodParam(MDecl.Params.Items[K]);
            Par.ResolvedType := ResolveParamType(Par, MDecl.Line, MDecl.Col);
          end;
          if MDecl.ReturnTypeName <> '' then
          begin
            ParType := FindTypeOrInstantiate(MDecl.ReturnTypeName);
            if ParType = nil then
              SemanticError(
                Format('Unknown return type ''%s'' for method ''%s''',
                  [MDecl.ReturnTypeName, MDecl.Name]),
                MDecl.Line, MDecl.Col);
            MDecl.ResolvedReturnType := ParType;
          end;
        end;
    end
    else
    begin
      FieldList  := TClassTypeDef(TD.Def).Fields;
      MethodList := TClassTypeDef(TD.Def).Methods;

      { Resolve class-level custom attributes.  Each raw name is matched
        using the Delphi suffix convention: [Threaded] resolves to
        ThreadedAttribute if that class descends from TCustomAttribute.
        [Weak] is a compiler intrinsic and is skipped here. }
      for AttrIdx := 0 to TClassTypeDef(TD.Def).Attributes.Count - 1 do
      begin
        RawAttr := TClassTypeDef(TD.Def).Attributes.Strings[AttrIdx];
        if AttrMatches(RawAttr, 'Weak') then Continue;
        Resolved := ResolveCustomAttrName(RawAttr);
        if Resolved = '' then
          SemanticError(
            Format('Unknown attribute ''%s'': no class ''%s'' or ''%sAttribute'' ' +
                   'descending from TCustomAttribute found',
                   [RawAttr, RawAttr, RawAttr]),
            TD.Line, TD.Col)
        else
          RT.AddClassAttribute(Resolved);
      end;
      { Reify class-level attribute applications: resolve each captured
        TAttributeUse and synthesise its factory thunk.  Unknown names were
        already rejected by the name loop above, so a '' resolution here can
        only be the skipped [Weak] intrinsic. }
      for AttrIdx := 0 to TClassTypeDef(TD.Def).AttrUses.Count - 1 do
      begin
        AttrUse := TAttributeUse(TClassTypeDef(TD.Def).AttrUses.Items[AttrIdx]);
        Resolved := ResolveCustomAttrName(AttrUse.Name);
        if Resolved = '' then Continue;
        AttrUse.ResolvedClassName := Resolved;
        SynthesiseAttrThunk(AttrUse,
          '__attr_' + TD.Name + '_c' + IntToStr(AttrIdx));
      end;

      { Copy inherited fields and vtable from parent class first.
        The parser may store a generic interface name (e.g. IFoo<T>) as ParentName
        when no explicit class parent was specified — detect this and treat it as
        an implements entry instead. }
      if TClassTypeDef(TD.Def).ParentName <> '' then
      begin
        ParentSym := nil;
        { A generic name as the first heritage entry (class(TBox<Integer>) or
          class(IFoo<T>)) must be instantiated, then classified: a generic
          CLASS instance is the parent class, a generic INTERFACE instance is
          an implements entry.  Earlier this assumed interface unconditionally,
          so inheriting from a generic class was rejected as an unknown
          interface. }
        if StrPos('<', TClassTypeDef(TD.Def).ParentName) >= 0 then
        begin
          GenParentDesc := FindTypeOrInstantiate(TClassTypeDef(TD.Def).ParentName);
          if (GenParentDesc <> nil) and
             (GenParentDesc is TInterfaceTypeDesc) then
          begin
            { Generic interface — move to the implements list. }
            TClassTypeDef(TD.Def).ImplementsNames.Insert(
              0, TClassTypeDef(TD.Def).ParentName);
            TClassTypeDef(TD.Def).ParentName := '';
          end;
          { Otherwise (generic class instance, or unresolved) leave it as the
            ParentName for the class-parent resolution below. }
        end;
        if TClassTypeDef(TD.Def).ParentName <> '' then
        begin
          { Resolve through the type machinery (not a literal FTable.Lookup) so
            a unit-qualified ancestor 'Unit.TParent' binds to that unit's type
            and disambiguates a same-named class in another unit.
            FindTypeOrInstantiate handles both bare and dotted names. }
          GenParentDesc := FindTypeOrInstantiate(TClassTypeDef(TD.Def).ParentName);
          { If the first name in class(...) is an interface, not a class,
            treat it as an implements entry — TObject becomes the implicit parent. }
          if (GenParentDesc <> nil) and (GenParentDesc is TInterfaceTypeDesc) then
          begin
            TClassTypeDef(TD.Def).ImplementsNames.Insert(
              0, TClassTypeDef(TD.Def).ParentName);
            TClassTypeDef(TD.Def).ParentName := '';
          end
          else
          begin
            if (GenParentDesc = nil) or not (GenParentDesc is TRecordTypeDesc) then
              SemanticError(
                Format('Unknown parent class ''%s'' for ''%s''',
                  [TClassTypeDef(TD.Def).ParentName, TD.Name]),
                TD.Line, TD.Col);
            ParentRT     := TRecordTypeDesc(GenParentDesc);
            RT.Parent    := ParentRT;
            RT.CopyVTableFrom(ParentRT);
            for K := 0 to ParentRT.Fields.Count - 1 do
            begin
              FldInfo := TFieldInfo(ParentRT.Fields.Items[K]);
              RT.AddField(FldInfo.Name, FldInfo.TypeDesc);
              RT.FindField(FldInfo.Name).IsUnretained := FldInfo.IsUnretained;
              RT.FindField(FldInfo.Name).IsWeak       := FldInfo.IsWeak;
              { An inherited field keeps the ANCESTOR's visibility + declaring
                origin — protected/strict checks must resolve against where the
                field was actually declared, not the subclass that copied it. }
              RT.FindField(FldInfo.Name).Visibility    := FldInfo.Visibility;
              RT.FindField(FldInfo.Name).DeclaringUnit := FldInfo.DeclaringUnit;
              RT.FindField(FldInfo.Name).DeclaringType := FldInfo.DeclaringType;
            end;
          end;
        end;
      end;

      { If no explicit parent was specified (and this class is not TObject itself),
        implicitly inherit from TObject: copy its vtable so the vptr slot is
        present and field offsets start after the 8-byte pointer, and set
        RT.Parent so that typeinfo carries the correct parent chain for
        is/as/InheritsFrom checks. }
      if (TClassTypeDef(TD.Def).ParentName = '') and (TD.Name <> 'TObject') then
      begin
        ParentSym := FTable.Lookup('TObject');
        if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
        begin
          ParentRT := TRecordTypeDesc(ParentSym.TypeDesc);
          RT.CopyVTableFrom(ParentRT);
          RT.Parent := ParentRT;
        end;
      end;

      { Pre-resolve param and return types for class methods so that MangleParamSig
        can compute overloaded keys correctly in the vtable pre-pass below. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Items[J]);
          { Generic method (method-level <T>): params/return reference the
            method's own type params, unknown until a call site instantiates it.
            Register the template keyed by OwnerType.Method and skip resolution. }
          if MDecl.TypeParams <> nil then
          begin
            MDecl.OwnerTypeName := RT.Name;
            if FGenericMethodTemplates.IndexOf(RT.Name + '.' + MDecl.Name) < 0 then
              FGenericMethodTemplates.AddObject(RT.Name + '.' + MDecl.Name, MDecl);
            Continue;
          end;
          for K := 0 to MDecl.Params.Count - 1 do
          begin
            Par              := TMethodParam(MDecl.Params.Items[K]);
            Par.ResolvedType := ResolveParamType(Par, MDecl.Line, MDecl.Col);
          end;
          if MDecl.ReturnTypeName <> '' then
          begin
            ParType := FindTypeOrInstantiate(MDecl.ReturnTypeName);
            if ParType = nil then
              SemanticError(
                Format('Unknown return type ''%s'' for method ''%s''',
                  [MDecl.ReturnTypeName, MDecl.Name]),
                MDecl.Line, MDecl.Col);
            MDecl.ResolvedReturnType := ParType;
          end;
        end;

      { Pre-pass: register vtable slots for virtual/override methods BEFORE
        adding own fields, so that field offsets correctly account for the vptr.
        Each (name, parameter-signature) pair gets its own slot — overloaded
        virtual methods are independently dispatched. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Items[J]);
          { Generic-method templates take no vtable slot — they cannot be
            virtual (each instantiation is a distinct monomorphised body). }
          if MDecl.TypeParams <> nil then Continue;
          MangledKey := MDecl.Name;
          if MDecl.IsOverload then
            MangledKey := MangledKey + '$' + MangleParamSig(MDecl);
          if MDecl.IsVirtual then
          begin
            Slot := RT.AddVTableSlot(MangledKey, '$' + CurrentUnitPrefix() + TD.Name + '_' + MangledKey);
            if MDecl.IsAbstract then
            begin
              RT.VTableEntryAt(Slot).IsAbstract := True;
              RT.HasAbstractMethods := True;
            end;
          end
          else if MDecl.IsOverride then
          begin
            Slot := RT.FindVTableSlot(MangledKey);
            if Slot < 0 then
            begin
              ParentSym := FTable.Lookup('TObject');
              if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
              begin
                ParentRT := TRecordTypeDesc(ParentSym.TypeDesc);
                if ParentRT.FindVTableSlot(MangledKey) >= 0 then
                begin
                  RT.CopyVTableFrom(ParentRT);
                  if RT.Parent = nil then
                    RT.Parent := ParentRT;
                  Slot := RT.FindVTableSlot(MangledKey);
                end;
              end;
            end;
            RT.OverrideVTableSlot(Slot, '$' + CurrentUnitPrefix() + TD.Name + '_' + MangledKey);
            { Override clears the abstract flag on the inherited slot }
            if Slot >= 0 then
              RT.VTableEntryAt(Slot).IsAbstract := False;
          end
          else if (SameText(MDecl.Name, 'Create') or
                   (StrPos('Create', MDecl.Name) = 0)) and
                  (not MDecl.IsVirtual) and (not MDecl.IsOverride) then
          begin
            Slot := RT.FindVTableSlot(MangledKey);
            if Slot >= 0 then
              RT.OverrideVTableSlot(Slot, '$' + CurrentUnitPrefix() + TD.Name + '_' + MangledKey)
            else
              RT.AddVTableSlot(MangledKey, '$' + CurrentUnitPrefix() + TD.Name + '_' + MangledKey);
          end;
        end;
    end;

    { After building this class's vtable, check if any abstract slots remain
      (inherited but not overridden). If so, mark the class as abstract. }
    if RT <> nil then
    begin
      for J := 0 to RT.VTableCount() - 1 do
        if RT.VTableEntryAt(J).IsAbstract then
        begin
          RT.HasAbstractMethods := True;
          Break;
        end;
    end;

    { Resolve own field declarations (offsets now include vptr if HasVTable) }
    for J := 0 to FieldList.Count - 1 do
    begin
      FDecl   := TFieldDecl(FieldList.Items[J]);
      FldType := FindTypeOrInstantiate(FDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field', [FDecl.TypeName]),
          FDecl.Line, FDecl.Col);
      FDecl.ResolvedType := FldType;
      { Resolve [Weak] on fields.  Same type constraint as local vars. }
      if HasWeakAttribute(FDecl.Attributes) then
      begin
        if not ((FldType.Kind = tyClass) or (FldType.Kind = tyInterface)) then
          SemanticError(
            Format('[Weak] can only be applied to class or interface ' +
                   'fields, not ''%s''', [FDecl.TypeName]),
            FDecl.Line, FDecl.Col);
        FDecl.IsWeak := True;
      end;
      { Resolve [Unretained] on fields — a non-owning reference with no ARC
        and no weak registry.  Same class/interface constraint as [Weak]. }
      if HasUnretainedAttribute(FDecl.Attributes) then
      begin
        if not ((FldType.Kind = tyClass) or (FldType.Kind = tyInterface)) then
          SemanticError(
            Format('[Unretained] can only be applied to class or interface ' +
                   'fields, not ''%s''', [FDecl.TypeName]),
            FDecl.Line, FDecl.Col);
        if FDecl.IsWeak then
          SemanticError(
            '[Weak] and [Unretained] are mutually exclusive',
            FDecl.Line, FDecl.Col);
        FDecl.IsUnretained := True;
      end;
      for K := 0 to FDecl.Names.Count - 1 do
      begin
        FldName := FDecl.Names.Strings[K];
        if FDecl.IsClassVar then
        begin
          { STATIC (class-level) variable: not an instance field — do NOT call
            AddField (that would advance the instance layout).  Register a single
            shared global instead, under a mangled emit label, reachable by both
            the bare name (inside methods) and the qualified 'TFoo.Name' form.
            Class-, interface-, string-, and dynamic-array-typed static vars are
            supported: a single shared pointer slot, zero-initialised to nil,
            with assignment through the normal managed-global store ARC (retain
            new / release old) and a program-exit release dispatched by type
            (BUG-20260720-static-var-string-unsupported lifted the string/
            dynarray restriction — the store and read paths were already type-
            generic; native teardown already dispatched by type, and QBE's
            EmitStaticVarReleases gained string/dynarray arms). }
          ClassVarEmit := CurrentUnitPrefix() + TD.Name + '_' + FldName;
          { Single source of truth for codegen: stash the mangled label on the
            field decl (used by both backends to emit the data slot, even for a
            read-only static var that no assignment auto-registers). }
          if FDecl.Names.Count = 1 then
            FDecl.ClassVarEmitName := ClassVarEmit;
          { Bare name — usable unqualified inside the class's own methods. }
          Sym := TSymbol.Create(FldName, skVariable, FldType);
          Sym.IsGlobal       := True;
          Sym.IsClassVar     := True;
          Sym.GlobalEmitName := ClassVarEmit;
          Sym.Visibility     := FDecl.Visibility;
          Sym.OwnerTypeName  := TD.Name;
          if not FTable.Define(Sym) then Sym.Free();
          { Qualified name — usable as TFoo.Name from anywhere. }
          Sym := TSymbol.Create(TD.Name + '.' + FldName, skVariable, FldType);
          Sym.IsGlobal       := True;
          Sym.IsClassVar     := True;
          Sym.GlobalEmitName := ClassVarEmit;
          Sym.Visibility     := FDecl.Visibility;
          Sym.OwnerTypeName  := TD.Name;
          if not FTable.Define(Sym) then Sym.Free();
        end
        else
        begin
          RT.AddField(FldName, FldType);
          { Propagate the weak/unretained flags to the just-added field info so
            codegen and the field cleanup emitter can consult them without
            walking back to the AST. }
          if FDecl.IsWeak then
            RT.FindField(FldName).IsWeak := True;
          if FDecl.IsUnretained then
            RT.FindField(FldName).IsUnretained := True;
          { Carry visibility + declaring origin so member-access checks can be
            applied without re-walking the AST.  DeclaringType is this class
            (the one that declares the field); inherited fields copy the
            ancestor's metadata at the copy site above. }
          RT.FindField(FldName).Visibility    := FDecl.Visibility;
          RT.FindField(FldName).DeclaringUnit := FCurrentUnitName;
          RT.FindField(FldName).DeclaringType := TD.Name;
        end;
      end;
    end;

    { Index class methods, record VTableSlot on MDecl, resolve param/return types }
    if MethodList <> nil then
      for J := 0 to MethodList.Count - 1 do
      begin
        MDecl               := TMethodDecl(MethodList.Items[J]);
        MDecl.OwnerTypeName := TD.Name;
        { Stamp the declaring unit so member-visibility (private/protected) can
          enforce the unit privacy boundary.  Only set when empty so a value
          carried from an imported .bif is not overwritten. }
        if MDecl.OwningUnit = '' then
          MDecl.OwningUnit := FCurrentUnitName;

        { Compute mangled key and ResolvedQbeName for overloaded methods.
          Non-overloaded methods keep their plain name throughout. }
        MangledKey := MDecl.Name;
        if MDecl.IsOverload then
          MangledKey := MangledKey + '$' + MangleParamSig(MDecl);
        MDecl.ResolvedQbeName := CurrentUnitPrefix() + TD.Name + '_' + MangledKey;

        { Resolve method-level custom attributes and reify them.  The name
          must resolve to a TCustomAttribute descendant (the [Weak] field
          intrinsic is meaningless on a method and errors as unknown).
          Factory thunks are synthesised for PUBLISHED methods only — those
          are the methods with entries in the typeinfo method-attrs table;
          attributes on non-published methods are validated but carry no
          runtime representation. }
        for AttrIdx := 0 to MDecl.AttrUses.Count - 1 do
        begin
          AttrUse  := TAttributeUse(MDecl.AttrUses.Items[AttrIdx]);
          Resolved := ResolveCustomAttrName(AttrUse.Name);
          if Resolved = '' then
            SemanticError(
              Format('Unknown attribute ''%s'' on method ''%s.%s'': no class ' +
                     '''%s'' or ''%sAttribute'' descending from ' +
                     'TCustomAttribute found',
                     [AttrUse.Name, TD.Name, MDecl.Name,
                      AttrUse.Name, AttrUse.Name]),
              AttrUse.Line, AttrUse.Col);
          AttrUse.ResolvedClassName := Resolved;
          if MDecl.IsPublished then
            SynthesiseAttrThunk(AttrUse,
              '__attr_' + TD.Name + '_m' + IntToStr(J) + '_' + IntToStr(AttrIdx));
        end;

        { Reject duplicate-without-overload at registration time.  Walk
          existing FMethodIndex entries for this (TypeName.Name) — if
          any sibling has IsOverload=False or the new MDecl lacks
          IsOverload, this is a duplicate-identifier error. }
        if (MDecl.OwningUnit = '') and (FCurrentUnitName <> '') then
          MDecl.OwningUnit := FCurrentUnitName;
        Key := TD.Name + '.' + MDecl.Name;
        Grp := GroupOf(FMethodGroups, Key);
        if Grp <> nil then
          for K := 0 to Grp.Count - 1 do
          begin
            { A same-named method on a same-named type owned by a DIFFERENT
              used unit is a distinct method (it carries its own unit-prefixed
              ResolvedQbeName), not a missing-overload duplicate — the two
              types coexist under cross-unit last-wins. }
            if not SameText(TMethodDecl(Grp.Items[K]).OwningUnit,
                            MDecl.OwningUnit) then
              Continue;
            if (not MDecl.IsOverload) or
               (not TMethodDecl(Grp.Items[K]).IsOverload) then
              SemanticError(
                Format('Duplicate method ''%s.%s'' (missing ''overload'' directive?)',
                  [TD.Name, MDecl.Name]),
                MDecl.Line, MDecl.Col);
          end;
        FMethodIndex.AddObject(Key, MDecl);
        AddGroupEntry(FMethodGroups, Key, MDecl);
        if SameText(MDecl.Name, 'Destroy') then
        begin
          RT.HasDestroyMethod := True;
          { Stash the resolved emit name of the no-arg Destroy so ARC
            field cleanup calls the symbol that was actually emitted.
            Critical when Destroy is overloaded — the bare
            '<Class>_Destroy' label is never written in that case. }
          if (MDecl.Params.Count = 0) and (RT.DestroyResolvedQbeName = '') then
            RT.DestroyResolvedQbeName := MDecl.ResolvedQbeName;
        end;

        { Retrieve the vtable slot assigned in the pre-pass above.
          Constructors get implicit vtable slots (metaclass dispatch). }
        if MDecl.IsVirtual or MDecl.IsOverride or
           (SameText(MDecl.Name, 'Create') or (StrPos('Create', MDecl.Name) = 0)) then
        begin
          MDecl.VTableSlot := RT.FindVTableSlot(MangledKey);
          if MDecl.IsOverride and (MDecl.VTableSlot < 0) then
            SemanticError(
              Format('Method ''%s'' marked override but no matching virtual base method found',
                [MDecl.Name]),
              MDecl.Line, MDecl.Col);
        end;
      end;

    { Resolve property declarations }
    if TD.Def is TClassTypeDef then
      for J := 0 to TClassTypeDef(TD.Def).Properties.Count - 1 do
      begin
        PropDecl := TPropertyDecl(TClassTypeDef(TD.Def).Properties.Items[J]);
        PropType := FTable.FindType(PropDecl.TypeName);
        if PropType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for property ''%s''',
              [PropDecl.TypeName, PropDecl.Name]),
            PropDecl.Line, PropDecl.Col);
        PropInfo := TPropertyInfo.Create();
        PropInfo.Name := PropDecl.Name;
        PropInfo.TypeDesc := PropType;
        if PropDecl.ReadName <> '' then
        begin
          if RT.FindField(PropDecl.ReadName) <> nil then
            PropInfo.ReadField := PropDecl.ReadName
          else
            PropInfo.ReadMethod := DeclaredMethodCase(
              TClassTypeDef(TD.Def).Methods, PropDecl.ReadName);
        end;
        if PropDecl.WriteName <> '' then
        begin
          if RT.FindField(PropDecl.WriteName) <> nil then
            PropInfo.WriteField := PropDecl.WriteName
          else
            PropInfo.WriteMethod := DeclaredMethodCase(
              TClassTypeDef(TD.Def).Methods, PropDecl.WriteName);
        end;
        PropInfo.IndexParamName := PropDecl.IndexParamName;
        if PropDecl.IndexTypeName <> '' then
          PropInfo.IndexTypeDesc := FTable.FindType(PropDecl.IndexTypeName);
        PropInfo.IsDefault := PropDecl.IsDefault;
        PropInfo.IsStatic := PropDecl.IsStatic;
        PropInfo.Visibility    := PropDecl.Visibility;
        PropInfo.DeclaringUnit := FCurrentUnitName;
        PropInfo.DeclaringType := TD.Name;
        RT.AddProperty(PropInfo);
      end;

    { Register class-level constants in the global scope — accessible both
      unqualified (MaxItems) and qualified (TFoo.MaxItems) }
    if TD.Def is TClassTypeDef then
      for J := 0 to TClassTypeDef(TD.Def).ConstDecls.Count - 1 do
      begin
        CD := TConstDecl(TClassTypeDef(TD.Def).ConstDecls.Items[J]);
        if CD.IsArrayConst then
        begin
          ElemTD := FTable.FindType(CD.ArrayElemType);
          if ElemTD = nil then
            SemanticError(Format('Unknown element type ''%s'' in class array const ''%s''',
              [CD.ArrayElemType, CD.Name]), CD.Line, CD.Col);
          if CD.ArrayIsRangeIndexed then
            ArrTD := Self.BuildConstArrayType(CD, ElemTD)
          else
          begin
            IdxTD := FTable.FindType(CD.ArrayIndexType);
            if IdxTD = nil then
              SemanticError(Format('Unknown index type ''%s'' in class array const ''%s''',
                [CD.ArrayIndexType, CD.Name]), CD.Line, CD.Col);
            if IdxTD.Kind <> tyEnum then
              SemanticError(Format('Class array const index must be an enum, got ''%s''',
                [IdxTD.Name]), CD.Line, CD.Col);
            EnumDesc := TEnumTypeDesc(IdxTD);
            { Enum-subrange index: span + bounds come from the subrange
              ordinals, not the full base enum (GH #182 follow-up) — same
              rule as the unit-level array-const arm. }
            if EnumDesc.IsSubrange then
              Expected := EnumDesc.SubrangeHigh - EnumDesc.SubrangeLow + 1
            else
              Expected := EnumDesc.Members.Count;
            if CD.ArrayElements.Count <> Expected then
              SemanticError(Format(
                'Class array const ''%s'' has %d element(s) but index type ''%s'' has %d member(s)',
                [CD.Name, CD.ArrayElements.Count, CD.ArrayIndexType, Expected]),
                CD.Line, CD.Col);
            if EnumDesc.IsSubrange then
              ArrTD := FTable.NewStaticArrayType(ElemTD,
                EnumDesc.SubrangeLow, EnumDesc.SubrangeHigh)
            else
              ArrTD := FTable.NewStaticArrayType(ElemTD, 0, Expected - 1);
          end;
          Sym := TSymbol.Create(CD.Name, skConstant, ArrTD);
          Sym.IsGlobal := True;
          Sym.ConstArray := TStringList.Create();
          for K := 0 to CD.ArrayElements.Count - 1 do
            Sym.ConstArray.Add(CD.ArrayElements[K]);
          if not FTable.Define(Sym) then
            Sym.Free();
          Sym := TSymbol.Create(TD.Name + '.' + CD.Name, skConstant, ArrTD);
          Sym.IsGlobal := True;
          Sym.ConstArray := TStringList.Create();
          for K := 0 to CD.ArrayElements.Count - 1 do
            Sym.ConstArray.Add(CD.ArrayElements[K]);
          if not FTable.Define(Sym) then
            Sym.Free();
        end
        else
        begin
          if CD.IsString then
            ParType := FTable.TypeString
          else
            ParType := FTable.TypeInteger;
          { Unqualified name — usable inside class methods without prefix }
          Sym := TSymbol.Create(CD.Name, skConstant, ParType);
          Sym.ConstValue  := CD.IntVal;
          Sym.ConstString := CD.StrVal;
          if not FTable.Define(Sym) then
            Sym.Free();
          { Qualified name — usable as TFoo.MaxItems from anywhere }
          Sym := TSymbol.Create(TD.Name + '.' + CD.Name, skConstant, ParType);
          Sym.ConstValue  := CD.IntVal;
          Sym.ConstString := CD.StrVal;
          if not FTable.Define(Sym) then
            Sym.Free();
        end;
      end;

    { Verify class implements all methods of each declared interface }
    if TD.Def is TClassTypeDef then
      for L := 0 to TClassTypeDef(TD.Def).ImplementsNames.Count - 1 do
      begin
        IntfName := TClassTypeDef(TD.Def).ImplementsNames.Strings[L];
        IntfSym  := FTable.Lookup(IntfName);
        if IntfSym = nil then
        begin
          { May be a generic interface — try instantiation }
          IntfDesc := TInterfaceTypeDesc(FindTypeOrInstantiate(IntfName));
          if IntfDesc = nil then
            SemanticError(
              Format('Unknown interface ''%s'' in implements list of ''%s''',
                [IntfName, TD.Name]),
              TD.Line, TD.Col);
          IntfSym := FTable.Lookup(IntfName);
        end;
        if (IntfSym = nil) or not (IntfSym.TypeDesc is TInterfaceTypeDesc) then
          SemanticError(
            Format('Unknown interface ''%s'' in implements list of ''%s''',
              [IntfName, TD.Name]),
            TD.Line, TD.Col);
        IntfDesc := TInterfaceTypeDesc(IntfSym.TypeDesc);
        RT.AddImplements(IntfDesc);
        for J := 0 to IntfDesc.MethodCount() - 1 do
        begin
          Key := IntfDesc.MethodName(J);
          if RT.FindField(Key) = nil then
          begin
            { Check method exists in class — search method list }
            MDecl := nil;
            if TD.Def is TClassTypeDef then
              for K := 0 to TClassTypeDef(TD.Def).Methods.Count - 1 do
                if SameText(TMethodDecl(TClassTypeDef(TD.Def).Methods.Items[K]).Name, Key) then
                begin
                  MDecl := TMethodDecl(TClassTypeDef(TD.Def).Methods.Items[K]);
                  Break;
                end;
            if MDecl = nil then
              SemanticError(
                Format('Class ''%s'' does not implement method ''%s'' from interface ''%s''',
                  [TD.Name, Key, IntfName]),
                TD.Line, TD.Col);
          end;
        end;
      end;
  end;

  { Pass 3 — resolve forward-referenced pointer aliases.
    A pointer type 'PFoo = ^TFoo' may have been processed before TFoo was
    registered; its TPointerTypeDesc.BaseType is nil.  Now that all types
    are in the symbol table, fill in the missing base types. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if not (TD.Def is TTypeAliasDef) then Continue;
    AliasDef  := TTypeAliasDef(TD.Def);
    AliasName := AliasDef.TypeName;
    if (Length(AliasName) = 0) or (StrAt(AliasName, 0) <> Ord('^')) then Continue;
    BaseName := StrCopyTail(AliasName, 1);
    BaseSym  := FTable.Lookup(TD.Name);
    if (BaseSym = nil) or not (BaseSym.TypeDesc is TPointerTypeDesc) then Continue;
    if TPointerTypeDesc(BaseSym.TypeDesc).BaseType <> nil then Continue;
    { Base was unresolved in Pass 1 — try again now }
    Sym := FTable.Lookup(BaseName);
    if (Sym <> nil) and (Sym.Kind = skType) then
      TPointerTypeDesc(BaseSym.TypeDesc).BaseType := Sym.TypeDesc;
  end;

  { A forward declaration never completed in this scope is an error. }
  if ForwardDecls.Count > 0 then
  begin
    TD := TTypeDecl(ForwardDecls.Objects[0]);
    SemanticError(Format('Forward type not resolved ''%s''',
      [ForwardDecls.Strings[0]]), TD.Line, TD.Col);
  end;

  { Drop the now-redundant forward stubs from the AST so later phases (codegen
    iterates ABlock.TypeDecls) never see two declarations of the same type. }
  for I := ABlock.TypeDecls.Count - 1 downto 0 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if ((TD.Def is TClassTypeDef) and TClassTypeDef(TD.Def).IsForward) or
       ((TD.Def is TInterfaceTypeDef) and TInterfaceTypeDef(TD.Def).IsForward) then
      ABlock.TypeDecls.Delete(I);
  end;

  ForwardDecls.Free();
end;

procedure TSemanticAnalyser.AnalyseMethodBodies(ABlock: TBlock);
var
  I, J:    Integer;
  TD:      TTypeDecl;
  CD:      TClassTypeDef;
  RD:      TRecordTypeDef;
  RT:      TRecordTypeDesc;
  Sym:     TSymbol;
  Methods: TObjectList;
begin
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
    begin
      CD  := TClassTypeDef(TD.Def);
      Sym := FTable.Lookup(TD.Name);
      if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then
        Continue;
      RT      := TRecordTypeDesc(Sym.TypeDesc);
      Methods := CD.Methods;
    end
    else if TD.Def is TRecordTypeDef then
    begin
      RD  := TRecordTypeDef(TD.Def);
      Sym := FTable.Lookup(TD.Name);
      if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then
        Continue;
      RT      := TRecordTypeDesc(Sym.TypeDesc);
      Methods := RD.Methods;
    end
    else
      Continue;
    for J := 0 to Methods.Count - 1 do
      AnalyseMethodDecl(TMethodDecl(Methods.Items[J]), RT);
  end;
end;

procedure TSemanticAnalyser.AnalyseMethodDecl(
  AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
var
  I:          Integer;
  Par:        TMethodParam;
  Sym:        TSymbol;
  SavedClass: TRecordTypeDesc;
  SavedMethodOwner: TRecordTypeDesc;
  SavedMethodDecl: TMethodDecl;
  SavedEnclosing: TMethodDecl;
  TKey:       string;
begin
  { Generic method (method-level <T>): its params/body reference the method's
    own type parameters, which are not in scope until a call site instantiates
    it.  Register the template keyed by OwnerType.Method and defer analysis to
    InstantiateGenericMethod.  (A method of a generic CLASS uses OwnerTypeParams,
    not TypeParams, and is NOT skipped here.) }
  if AMethod.TypeParams <> nil then
  begin
    TKey := AClassType.Name + '.' + AMethod.Name;
    if FGenericMethodTemplates.IndexOf(TKey) < 0 then
      FGenericMethodTemplates.AddObject(TKey, AMethod);
    AMethod.OwnerTypeName := AClassType.Name;
    Exit;
  end;
  SavedClass    := FCurrentClass;
  SavedMethodOwner := FCurrentMethodOwner;
  SavedMethodDecl := FCurrentMethodDecl;
  SavedEnclosing := FCurrentEnclosingDecl;
  FCurrentMethodDecl := AMethod;
  { Nested routines declared in this method's body record the method as
    their EnclosingDecl (mirrors AnalyseStandaloneDecl) — the call-site
    nested-proc resolution keys off it (BUG-008). }
  FCurrentEnclosingDecl := AMethod;
  { A STATIC (class-level) method has no instance receiver.  Leave FCurrentClass
    at its saved value (do NOT bind it to AClassType) so that an implicit
    instance-member reference inside the body resolves as an undeclared
    identifier rather than silently binding to a non-existent Self.  Static
    members of the same type remain reachable through their registered bare
    global symbols. }
  if not AMethod.IsStatic then
    FCurrentClass := AClassType;
  { Visibility context: the declaring type of THIS method body, set for static
    and instance methods alike, so a strict-private member is reachable from its
    own type's methods regardless of static-ness. }
  FCurrentMethodOwner := AClassType;
  FTable.PushScope();
  Inc(FScopeDepth);
  try
    { Record methods receive the record by pointer (like a var param); class
      methods receive the object pointer as a value.  Declaring Self as
      skVarParameter for records makes the codegen dereference it correctly.
      A static method receives NO Self. }
    if not AMethod.IsStatic then
    begin
      if AMethod.IsRecordMethod then
        Sym := TSymbol.Create('Self', skVarParameter, AClassType)
      else
        Sym := TSymbol.Create('Self', skVariable, AClassType);
      FTable.Define(Sym);
    end;

    { For function methods, define Result as a writable variable }
    if AMethod.ResolvedReturnType <> nil then
    begin
      Sym := TSymbol.Create('Result', skVariable, AMethod.ResolvedReturnType);
      FTable.Define(Sym);
    end;

    { Define explicit parameters }
    for I := 0 to AMethod.Params.Count - 1 do
    begin
      Par := TMethodParam(AMethod.Params.Items[I]);
      if Par.ResolvedType = nil then
        SemanticError(
          Format('Parameter ''%s'' has unresolved type', [Par.ParamName]),
          AMethod.Line, AMethod.Col);
      if Par.IsVarParam then
        Sym := TSymbol.Create(Par.ParamName, skVarParameter, Par.ResolvedType)
      else
        Sym := TSymbol.Create(Par.ParamName, skParameter, Par.ResolvedType);
      if not FTable.Define(Sym) then
      begin
        Sym.Free();
        SemanticError(
          Format('Duplicate parameter name ''%s''', [Par.ParamName]),
          AMethod.Line, AMethod.Col);
      end;
    end;

    { Abstract methods must not have a body }
    if AMethod.IsAbstract and (AMethod.Body <> nil) then
      SemanticError(
        Format('Abstract method ''%s'' must not have an implementation',
          [AMethod.Name]),
        AMethod.Line, AMethod.Col);

    { Analyse the method body block (pushes its own inner scope) }
    if (AMethod.Body <> nil) and not AMethod.IsAbstract then
      AnalyseBlock(AMethod.Body);
  finally
    Dec(FScopeDepth);
    FTable.PopScope();
    FCurrentClass := SavedClass;
    FCurrentEnclosingDecl := SavedEnclosing;
    FCurrentMethodOwner := SavedMethodOwner;
    FCurrentMethodDecl := SavedMethodDecl;
  end;
end;

function TSemanticAnalyser.FindMethodDecl(
  const ATypeName, AMethodName: string): TMethodDecl;
var
  CurrName: string;
  Idx, K:   Integer;
  Key:      string;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
  OwnerUnit: string;
  Grp:      TObjectList;
begin
  CurrName := ATypeName;
  while CurrName <> '' do
  begin
    Key := CurrName + '.' + AMethodName;
    Idx := FMethodIndex.IndexOf(Key);
    if Idx >= 0 then
    begin
      Result := TMethodDecl(FMethodIndex.Objects[Idx]);
      { Visibility is NOT enforced here: FindMethodDecl is also used to resolve
        property getters/setters, Free/Create existence probes, and inherited
        lookups, where the access is legitimate regardless of the member's
        declared visibility.  Enforcement happens at the user-written call /
        member-access sites (EnforceMethodVisible / AssertMemberVisibleV). }
      { Cross-unit last-wins: two used units may export a same-named type, so
        the group holds both their methods under one key.  FMethodIndex returns
        the first-registered, which may belong to the OTHER unit; bind instead
        to the method on the type that actually resolved (its owning unit). }
      OwnerUnit := '';
      Sym := FTable.Lookup(CurrName);
      if Sym <> nil then OwnerUnit := Sym.OwningUnit;
      if (OwnerUnit <> '') and not SameText(Result.OwningUnit, OwnerUnit) then
      begin
        Grp := GroupOf(FMethodGroups, Key);
        if Grp <> nil then
          for K := 0 to Grp.Count - 1 do
            if SameText(TMethodDecl(Grp.Items[K]).OwningUnit, OwnerUnit) then
            begin
              Result := TMethodDecl(Grp.Items[K]);
              Break;
            end;
      end;
      Exit;
    end;
    { Walk to parent }
    Sym := FTable.Lookup(CurrName);
    if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
    begin
      RT := TRecordTypeDesc(Sym.TypeDesc);
      if RT.Parent <> nil then
        CurrName := RT.Parent.Name
      else
        Break;
    end
    else
      Break;
  end;
  Result := nil;
end;

function TSemanticAnalyser.PropAccessorOwner(
  const ATypeName, AMethodName: string): string;
{ See the interface-section comment.  Mirrors the chain walk in
  FindMethodDecl; falls back to ATypeName when no declaring class is found
  (e.g. abstract/forward) so the non-inherited case is unchanged. }
var
  CurrName: string;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
begin
  CurrName := ATypeName;
  while CurrName <> '' do
  begin
    if FMethodIndex.IndexOf(CurrName + '.' + AMethodName) >= 0 then
      Exit(CurrName);
    Sym := FTable.Lookup(CurrName);
    if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
    begin
      RT := TRecordTypeDesc(Sym.TypeDesc);
      if RT.Parent <> nil then
        CurrName := RT.Parent.Name
      else
        Break;
    end
    else
      Break;
  end;
  Result := ATypeName;
end;

function TSemanticAnalyser.PropAccessorVSlot(
  const ATypeName, AMethodName: string): Integer;
var
  TDesc: TTypeDesc;
begin
  Result := -1;
  TDesc := FTable.FindType(ATypeName);
  if TDesc is TRecordTypeDesc then
    Result := TRecordTypeDesc(TDesc).FindVTableSlot(AMethodName);
end;

function TSemanticAnalyser.ResolveMethodOverload(
  const ATypeName, AMethodName: string;
  AArgs: TObjectList; ALine, ACol: Integer): TMethodDecl;
var
  CurrName:    string;
  Sym:         TSymbol;
  RT:          TRecordTypeDesc;
  Key:         string;
  OwnerHint:   string;
  Cand:        TMethodDecl;
  Grp:         TObjectList;
  ArityMatch:  TObjectList;
  K:           Integer;
  Best:        TMethodDecl;
  Ambiguous:   Boolean;
  TotalCnt:    Integer;
  Arity:       Integer;
  SawHiding:   Boolean;
begin
  Result    := nil;
  { Consume the one-shot receiver owner hint set by the caller. }
  OwnerHint := FMethodOwnerHint;
  FMethodOwnerHint := '';
  if AArgs <> nil then Arity := AArgs.Count else Arity := -1;
  TotalCnt  := 0;
  ArityMatch := TObjectList.Create(False);
  try
    CurrName := ATypeName;
    while CurrName <> '' do
    begin
      Key := CurrName + '.' + AMethodName;
      Grp := GroupOf(FMethodGroups, Key);
      SawHiding := False;
      if Grp <> nil then
        for K := 0 to Grp.Count - 1 do
        begin
          Cand := TMethodDecl(Grp.Items[K]);
          { Cross-unit last-wins: at the receiver's OWN type level the group can
            also hold a same-named method on another used unit's same-named type.
            Bind to the receiver's actual unit (the hint) — a name re-lookup
            would pick the flat-table winner instead. }
          if (OwnerHint <> '') and SameText(CurrName, ATypeName) and
             (Cand.OwningUnit <> '') and
             not SameText(Cand.OwningUnit, OwnerHint) then
            Continue;
          Inc(TotalCnt);
          { A method declared WITHOUT `overload` hides all inherited methods of
            the same name — once seen at this (more-derived) level, the parent
            chain is not consulted.  Methods WITH `overload` merge with the
            inherited overload set, so the walk continues to the parent. }
          if not Cand.IsOverload then SawHiding := True;
          if (Arity < 0) or
             ((Arity >= MinArity(Cand)) and (Arity <= Cand.Params.Count)) then
            ArityMatch.Add(Cand);
        end;
      { Delphi overload semantics: derived `overload` methods MERGE with the
        inherited overload set (walk continues), but a non-`overload` method at
        this level hides the inherited ones (stop).  Stop too once any class in
        the chain actually declares the name without `overload`. }
      if SawHiding then Break;
      Sym := FTable.Lookup(CurrName);
      if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
      begin
        RT := TRecordTypeDesc(Sym.TypeDesc);
        if RT.Parent <> nil then
          CurrName := RT.Parent.Name
        else
          Break;
      end
      else
        Break;
    end;

    if TotalCnt = 0 then Exit;  { caller treats nil as "no method on class" }

    if ArityMatch.Count = 0 then
      SemanticError(
        Format('No matching overload for ''%s.%s'' with %d argument(s)',
          [ATypeName, AMethodName, Arity]),
        ALine, ACol);

    if (AArgs = nil) or (Arity = 0) then
    begin
      if ArityMatch.Count = 1 then
      begin
        Exit(TMethodDecl(ArityMatch.Items[0]));
      end;
      Exit;  { ambiguous-by-arity-only — caller must score with args }
    end;

    Best := Self.PickBestCandidate(ArityMatch, AArgs, Ambiguous);

    if Best = nil then
      SemanticError(
        Format('No matching overload for ''%s.%s'' with %d argument(s)',
          [ATypeName, AMethodName, Arity]),
        ALine, ACol);
    if Ambiguous then
      SemanticError(
        Format('Ambiguous overload of ''%s.%s'' — multiple candidates match equally',
          [ATypeName, AMethodName]),
        ALine, ACol);
    Result := Best;
  finally
    ArityMatch.Free();
  end;
end;

{ Scoring + tie-breaking, shared by ordinary method-overload resolution and
  operator-overload resolution (see the declaration comment).  ACandidates
  must already be filtered to the right arity. }
function TSemanticAnalyser.PickBestCandidate(ACandidates, AArgs: TObjectList;
  out AAmbiguous: Boolean): TMethodDecl;
var
  J, K:      Integer;
  Arity:     Integer;
  Cand:      TMethodDecl;
  Par:       TMethodParam;
  Arg:       TASTExpr;
  Score:     Integer;
  ArgScore:  Integer;
  BestScore: Integer;
  BestCount: Integer;
  Best:      TMethodDecl;
  ExactNew:  Integer;
  ExactBest: Integer;
  S1, S2:    Integer;
begin
  AAmbiguous := False;
  Result     := nil;
  Arity      := AArgs.Count;
  BestScore  := -1;
  BestCount  := 0;
  Best       := nil;
  for K := 0 to ACandidates.Count - 1 do
  begin
    Cand  := TMethodDecl(ACandidates.Items[K]);
    Score := 0;
    for J := 0 to Arity - 1 do
    begin
      Par      := TMethodParam(Cand.Params.Items[J]);
      Arg      := TASTExpr(AArgs.Items[J]);
      ArgScore := ArgMatchScore(Par.ResolvedType, Arg.ResolvedType, Arg);
      if ArgScore = 0 then
      begin
        Score := -1;
        Break;
      end;
      Score := Score + ArgScore;
    end;
    if Score < 0 then Continue;
    { Primary tie-break: prefer fewer defaulted slots. }
    Score := (Score * 16) - (Cand.Params.Count - Arity);
    if Score > BestScore then
    begin
      BestScore := Score;
      BestCount := 1;
      Best      := Cand;
    end
    else if Score = BestScore then
    begin
      { Secondary tie-break: count exact matches (score=2) per argument.
        More exact matches = better candidate. }
      ExactNew  := 0;
      ExactBest := 0;
      for J := 0 to Arity - 1 do
      begin
        S1 := ArgMatchScore(TMethodParam(Cand.Params.Items[J]).ResolvedType,
                            TASTExpr(AArgs.Items[J]).ResolvedType,
                            TASTExpr(AArgs.Items[J]));
        S2 := ArgMatchScore(TMethodParam(Best.Params.Items[J]).ResolvedType,
                            TASTExpr(AArgs.Items[J]).ResolvedType,
                            TASTExpr(AArgs.Items[J]));
        if S1 = 2 then Inc(ExactNew);
        if S2 = 2 then Inc(ExactBest);
      end;
      if ExactNew > ExactBest then
      begin
        Best      := Cand;
        BestCount := 1;
      end
      else if ExactNew = ExactBest then
        Inc(BestCount);
      { ExactNew < ExactBest: keep current Best, don't increment BestCount }
    end;
  end;
  if BestScore < 0 then Exit;
  AAmbiguous := BestCount > 1;
  Result     := Best;
end;

procedure TSemanticAnalyser.GatherOperatorCandidates(const ATypeName: string;
  AKind: TOperatorKind; ACandidates: TObjectList);
var
  CurrName: string;
  Key:      string;
  Grp:      TObjectList;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
  Cand:     TMethodDecl;
  I, K:     Integer;
  Dup:      Boolean;
begin
  CurrName := ATypeName;
  while CurrName <> '' do
  begin
    Key := CurrName + '.' + OperatorKindName(AKind);
    Grp := GroupOf(FMethodGroups, Key);
    if Grp <> nil then
      for K := 0 to Grp.Count - 1 do
      begin
        Cand := TMethodDecl(Grp.Items[K]);
        if not (Cand.IsOperator and (Cand.OperatorKind = AKind)) then Continue;
        if Cand.Params.Count <> OperatorKindArity(AKind) then Continue;
        { De-dup by node identity: a same-type binary operator is reachable
          from both operand types. }
        Dup := False;
        for I := 0 to ACandidates.Count - 1 do
          if TObject(ACandidates.Items[I]) = TObject(Cand) then
          begin
            Dup := True;
            Break;
          end;
        if not Dup then ACandidates.Add(Cand);
      end;
    { Walk the inheritance chain — an operator declared on a base record or
      class applies to its descendants. }
    Sym := FTable.Lookup(CurrName);
    if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
    begin
      RT := TRecordTypeDesc(Sym.TypeDesc);
      if RT.Parent <> nil then
        CurrName := RT.Parent.Name
      else
        Break;
    end
    else
      Break;
  end;
end;

function TSemanticAnalyser.ResolveOperatorOverload(AKind: TOperatorKind;
  ALType, ARType: TTypeDesc; AArgs: TObjectList;
  ALine, ACol: Integer): TMethodDecl;
var
  Cands:     TObjectList;
  Ambiguous: Boolean;
  LName:     string;
  RName:     string;
begin
  Result := nil;
  if AKind = okNone then Exit;
  if ALType <> nil then LName := ALType.Name else LName := '<nil>';
  if ARType <> nil then RName := ARType.Name else RName := '<nil>';
  Cands := TObjectList.Create(False);
  try
    if (ALType <> nil) and (ALType.Kind in [tyRecord, tyClass]) then
      Self.GatherOperatorCandidates(ALType.Name, AKind, Cands);
    if (ARType <> nil) and (ARType.Kind in [tyRecord, tyClass]) and
       ((ALType = nil) or not SameText(ALType.Name, ARType.Name)) then
      Self.GatherOperatorCandidates(ARType.Name, AKind, Cands);
    if Cands.Count = 0 then Exit;
    Result := Self.PickBestCandidate(Cands, AArgs, Ambiguous);
    if Ambiguous then
      SemanticError(
        Format('Ambiguous operator ''%s'' for ''%s'' and ''%s'' — multiple candidates match equally',
          [OperatorKindName(AKind), LName, RName]),
        ALine, ACol);
  finally
    Cands.Free();
  end;
end;

procedure TSemanticAnalyser.UnwrapLoweredOperator(var ASlot: TASTExpr);
var
  Bin:  TBinaryExpr;
  Call: TASTExpr;
begin
  if not (ASlot is TBinaryExpr) then Exit;
  Bin := TBinaryExpr(ASlot);
  if Bin.LoweredCall = nil then Exit;
  Call := Bin.LoweredCall;
  Bin.LoweredCall := nil;   { ownership moves to the slot }
  ASlot := Call;
  Bin.Free();
end;

function TSemanticAnalyser.AnalyseExprSlot(var ASlot: TASTExpr): TTypeDesc;
begin
  Result := AnalyseExpr(ASlot);
  Self.UnwrapLoweredOperator(ASlot);
end;

function TSemanticAnalyser.AnalyseListSlot(AList: TObjectList;
  AIdx: Integer): TTypeDesc;
var
  Slot: TASTExpr;
begin
  Slot   := TASTExpr(AList.Items[AIdx]);
  Result := AnalyseExpr(Slot);
  Self.UnwrapLoweredOperator(Slot);
  AList.Items[AIdx] := Slot;
end;

function TSemanticAnalyser.TryLowerOperator(ABin: TBinaryExpr;
  ALType, ARType: TTypeDesc): TTypeDesc;
var
  Kind:  TOperatorKind;
  Args:  TObjectList;
  MDecl: TMethodDecl;
  Call:  TMethodCallExpr;
begin
  Result := nil;
  if ABin.LoweredCall <> nil then
  begin
    { Already lowered (a re-analysed generic body may revisit the node). }
    Exit(ABin.LoweredCall.ResolvedType);
  end;
  Kind := BinaryOpToOperatorKind(ABin.Op);
  if Kind = okNone then Exit;
  { Only record / class operands can carry operators. }
  if not (((ALType <> nil) and (ALType.Kind in [tyRecord, tyClass])) or
          ((ARType <> nil) and (ARType.Kind in [tyRecord, tyClass]))) then Exit;

  { Score against the already-analysed operand expressions. }
  Args := TObjectList.Create(False);
  try
    Args.Add(ABin.Left);
    Args.Add(ABin.Right);
    MDecl := Self.ResolveOperatorOverload(Kind, ALType, ARType, Args,
      ABin.Line, ABin.Col);
  finally
    Args.Free();
  end;
  if MDecl = nil then Exit;

  { Lower to `OwnerType.OperatorName(Left, Right)`.  Analysing the synthesised
    node re-runs the ordinary static-method-call path, which fills
    ResolvedMethod / IsStaticCall / ResolvedType and performs the usual
    argument checks — no call-shape logic is duplicated here. }
  Call            := TMethodCallExpr.Create();
  Call.Line       := ABin.Line;
  Call.Col        := ABin.Col;
  Call.ObjectName := MDecl.OwnerTypeName;
  Call.Name       := MDecl.Name;
  Call.Args.Add(ABin.Left);
  Call.Args.Add(ABin.Right);
  { Ownership of both operands moves into the call's arg list. }
  ABin.Left  := nil;
  ABin.Right := nil;
  ABin.LoweredCall     := Call;
  ABin.ResolvedOperator := MDecl;
  Result := AnalyseExpr(Call);
  ABin.ResolvedType := Result;
end;

procedure TSemanticAnalyser.AnalyseStandaloneDecls(ABlock: TBlock);
var
  I, J:    Integer;
  ADecl:   TMethodDecl;
  Par:     TMethodParam;
  ParType: TTypeDesc;
  RetType: TTypeDesc;
  Sym:     TSymbol;
  CurUnit:  string;
  PrevUnit: string;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    { Class method implementations have their body transferred; skip them here }
    if ADecl.OwnerTypeName <> '' then Continue;
    { Generic function templates — registered for on-demand instantiation.
      Mirrored on FTable so imported units (uSemanticImport) can share
      the same lookup surface as in-unit templates. }
    if ADecl.TypeParams <> nil then
    begin
      FGenericFuncTemplates.AddObject(ADecl.Name, ADecl);
      if FCurrentUnitName <> '' then
        CurUnit := FCurrentUnitName
      else
        CurUnit := '<program>';
      PrevUnit := FTable.RegisterGenericRoutine(ADecl.Name, ADecl, CurUnit);
      if PrevUnit <> '' then
        SemanticError(
          GenericCollisionMsg('Generic routine', ADecl.Name, PrevUnit, CurUnit),
          ADecl.Line, ADecl.Col);
      Continue;
    end;

    { Resolve parameter types }
    for J := 0 to ADecl.Params.Count - 1 do
    begin
      Par              := TMethodParam(ADecl.Params.Items[J]);
      Par.ResolvedType := ResolveParamType(Par, ADecl.Line, ADecl.Col);
    end;

    { Resolve return type for functions }
    if ADecl.ReturnTypeName <> '' then
    begin
      RetType := FindTypeOrInstantiate(ADecl.ReturnTypeName);
      if RetType = nil then
        SemanticError(
          Format('Unknown return type ''%s'' for function ''%s''',
            [ADecl.ReturnTypeName, ADecl.Name]),
          ADecl.Line, ADecl.Col);
      ADecl.ResolvedReturnType := RetType;
    end;

    { If an earlier forward declaration exists, update the index to point to
      this implementation and skip re-registering the symbol.  Overloaded
      decls bypass this — each overload is independent. }
    if not ADecl.IsOverload then
    begin
      J := FProcIndex.IndexOf(ADecl.Name);
      if (J >= 0) and (TMethodDecl(FProcIndex.Objects[J]).Body = nil) and
         (not TMethodDecl(FProcIndex.Objects[J]).IsOverload) then
      begin
        ReplaceProcIndexObject(J, ADecl);
        Continue;
      end;
    end;

    { Compute the QBE-emit name.  Phase B: overloads get a type-code
      suffix ('$<codes>'); non-overloaded decls keep their plain name. }
    if ADecl.IsOverload then
      ADecl.ResolvedQbeName := ADecl.Name + '$' + MangleParamSig(ADecl)
    else
      ADecl.ResolvedQbeName := ADecl.Name;

    { Index for call resolution — overloaded names appear multiple times.
      Nested procs (those inside another routine's body) are resolved via the
      scoped symbol table only; adding them to the global FProcIndex would
      make same-named nested procs in different outer routines appear as
      ambiguous overloads of each other.  A proc is nested when it sits
      inside a standalone routine (FCurrentEnclosingDecl set) OR inside a
      method body (FCurrentMethodOwner set) — both cases must be excluded
      from the global index. }
    if (FCurrentEnclosingDecl = nil) and (FCurrentMethodOwner = nil) then
      RegisterProcDecl(ADecl.Name, ADecl);

    { Register in symbol table }
    if ADecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(ADecl.Name, skFunction, ADecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(ADecl.Name, skProcedure, nil);
    Sym.IsOverload := ADecl.IsOverload;
    Sym.Decl       := ADecl;

    if not FTable.Define(Sym) then
    begin
      Sym.Free();
      SemanticError(
        Format('Duplicate identifier ''%s''', [ADecl.Name]),
        ADecl.Line, ADecl.Col);
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseStandaloneDecl(ADecl: TMethodDecl);
var
  I:           Integer;
  Par:         TMethodParam;
  Sym:         TSymbol;
  SavedEncl:   TMethodDecl;
  SavedClass:  TRecordTypeDesc;
  SavedOwner:  TRecordTypeDesc;
  SelfFld:     TFieldInfo;
begin
  ADecl.EnclosingDecl := FCurrentEnclosingDecl;
  SavedEncl := FCurrentEnclosingDecl;
  SavedClass := FCurrentClass;
  SavedOwner := FCurrentMethodOwner;
  FCurrentEnclosingDecl := ADecl;
  { Anonymous-method thunk lifted from an instance-method body (Phase 3):
    re-establish the owning class as the implicit-Self context so bare
    member references in the body resolve exactly as they did in the
    method.  The class is recoverable from the env record's 'Self' field. }
  if ADecl.IsAnonThunk and (ADecl.EnvCaptured <> nil) and
     (ADecl.EnvCaptured.IndexOf('Self') >= 0) and (ADecl.EnvType <> nil) then
  begin
    SelfFld := TRecordTypeDesc(ADecl.EnvType).FindField('Self');
    if (SelfFld <> nil) and (SelfFld.TypeDesc is TRecordTypeDesc) then
    begin
      FCurrentClass       := TRecordTypeDesc(SelfFld.TypeDesc);
      FCurrentMethodOwner := TRecordTypeDesc(SelfFld.TypeDesc);
    end;
  end;
  FTable.PushScope();
  Inc(FScopeDepth);
  try
    { Define Result for functions }
    if ADecl.ResolvedReturnType <> nil then
    begin
      Sym := TSymbol.Create('Result', skVariable, ADecl.ResolvedReturnType);
      FTable.Define(Sym);
    end;

    { Define explicit parameters }
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      Par := TMethodParam(ADecl.Params.Items[I]);
      if Par.IsVarParam then
        Sym := TSymbol.Create(Par.ParamName, skVarParameter, Par.ResolvedType)
      else
        Sym := TSymbol.Create(Par.ParamName, skParameter, Par.ResolvedType);
      if not FTable.Define(Sym) then
      begin
        Sym.Free();
        SemanticError(
          Format('Duplicate parameter name ''%s''', [Par.ParamName]),
          ADecl.Line, ADecl.Col);
      end;
    end;

    { Anonymous-method thunk (Phase 2): the captured enclosing names live in
      the heap env record reached through the hidden '__env' parameter.
      Define each as an ordinary local symbol typed from its env field so the
      module-scope body analysis resolves it; codegen redirects the accesses
      through __env by name (TMethodDecl.EnvCaptured). }
    if ADecl.IsAnonThunk and (ADecl.EnvCaptured <> nil) then
      for I := 0 to ADecl.EnvCaptured.Count - 1 do
      begin
        Sym := TSymbol.Create(ADecl.EnvCaptured.Strings[I], skVariable,
          TRecordTypeDesc(ADecl.EnvType).FindField(
            ADecl.EnvCaptured.Strings[I]).TypeDesc);
        FTable.Define(Sym);
      end;

    if ADecl.IsVarArgs and not ADecl.IsExternal then
      SemanticError(
        Format('''%s'': varargs is only valid on external declarations',
          [ADecl.Name]),
        ADecl.Line, ADecl.Col);
    if ADecl.IsVarArgs and ADecl.IsOverload then
      SemanticError(
        Format('''%s'': varargs cannot be combined with overload',
          [ADecl.Name]),
        ADecl.Line, ADecl.Col);
    if (not ADecl.IsExternal) and (ADecl.Body <> nil) then
    begin
      AnalyseBlock(ADecl.Body);
      { After analysing the body, determine which outer-scope variables are
        captured by any nested proc declared inside this one. }
      if ADecl.EnclosingDecl <> nil then
        CollectCaptures(ADecl, ADecl.EnclosingDecl);
    end;
  finally
    Dec(FScopeDepth);
    FTable.PopScope();
    FCurrentEnclosingDecl := SavedEncl;
    FCurrentClass := SavedClass;
    FCurrentMethodOwner := SavedOwner;
  end;
end;

procedure TSemanticAnalyser.AnalyseStandaloneBodies(ABlock: TBlock);
var
  I:     Integer;
  ADecl: TMethodDecl;
  SavedClass:       TRecordTypeDesc;
  SavedMethodOwner: TRecordTypeDesc;
  SavedMethodDecl:  TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    { Class method implementations have their body transferred; skip them here }
    if ADecl.OwnerTypeName <> '' then Continue;
    { Generic templates are instantiated on demand — skip until first call }
    if ADecl.TypeParams <> nil then Continue;
    { Forward declarations have no body; the later impl handles analysis }
    if ADecl.Body = nil then Continue;
    { A nested routine declared inside a METHOD body captures the method's
      Self like any other outer variable (BUG-008): the class context stays
      SET so 'Self' and implicit member access resolve against the enclosing
      class, and CollectCaptures threads Self through the hidden by-pointer
      capture params.  Only FCurrentMethodDecl is cleared — the nested
      routine is emitted as a standalone function, not a method body. }
    if FCurrentMethodDecl <> nil then
    begin
      SavedClass       := FCurrentClass;
      SavedMethodOwner := FCurrentMethodOwner;
      SavedMethodDecl  := FCurrentMethodDecl;
      FCurrentMethodDecl  := nil;
      FInNestedOfMethod   := True;
      try
        AnalyseStandaloneDecl(ADecl);
      finally
        FCurrentClass       := SavedClass;
        FCurrentMethodOwner := SavedMethodOwner;
        FCurrentMethodDecl  := SavedMethodDecl;
        FInNestedOfMethod   := False;
      end;
    end
    else
      AnalyseStandaloneDecl(ADecl);
  end;
end;

procedure TSemanticAnalyser.MaybeCaptureName(ADecl: TMethodDecl;
  AOuterVars: TStringList; const AName: string);
begin
  if AName = '' then Exit;
  if AOuterVars.IndexOf(AName) < 0 then Exit;
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.IndexOf(AName) >= 0) then
    Exit;
  if ADecl.CapturedVars = nil then
    ADecl.CapturedVars := TStringList.Create();
  ADecl.CapturedVars.Add(AName);
end;

procedure TSemanticAnalyser.CollectCaptures(ADecl: TMethodDecl; AOuterDecl: TMethodDecl);
{ Walk ADecl's body statements/expressions to find every reference to a variable
  belonging to the enclosing proc AOuterDecl — its locals AND its parameters
  (a `var` record parameter captured by a nested proc is the case that broke
  before).  Each such name is "captured": ADecl receives an implicit hidden
  var-by-pointer parameter, and the call site passes the variable's address. }
var
  OuterVars: TStringList;
  I, J, K:   Integer;
  VDecl:     TVarDecl;
  VName:     string;
  TodoExprs: TObjectList;
  TodoStmts: TObjectList;
  CurExpr:   TASTExpr;
  CurStmt:   TASTStmt;
  ChainDecl: TMethodDecl;
begin
  if ADecl.Body = nil then Exit;
  if AOuterDecl = nil then Exit;

  OuterVars := TStringList.Create();
  TodoExprs := TObjectList.Create(False);
  TodoStmts := TObjectList.Create(False);
  try
    { Build the set of enclosing names by walking the WHOLE enclosing-scope
      chain — the immediate parent AND every grandparent up to the top-level
      proc (BUG-20260720-grandparent-capture).  A routine nested three or more
      levels deep may reference a variable owned two-or-more levels up; that
      name must be capturable here so it enters CapturedVars, and the existing
      bottom-up child-fold then propagates it up through every intermediate
      level (each level analysed after its children).  The walk is
      innermost-first and every add is guarded by IndexOf < 0, so a name owned
      by a NEARER level wins — a grandparent var shadowed by an intermediate
      level's own local/param is correctly excluded. }
    ChainDecl := AOuterDecl;
    while ChainDecl <> nil do
    begin
      { this level's local var decls ... }
      if ChainDecl.Body <> nil then
        for I := 0 to ChainDecl.Body.Decls.Count - 1 do
        begin
          VDecl := TVarDecl(ChainDecl.Body.Decls.Items[I]);
          for J := 0 to VDecl.Names.Count - 1 do
          begin
            VName := VDecl.Names.Strings[J];
            if OuterVars.IndexOf(VName) < 0 then
              OuterVars.Add(VName);
          end;
        end;
      { ... and this level's PARAMETERS (value, var, out — all capturable;
        a captured var-param carries a pointer, handled by codegen). }
      for I := 0 to ChainDecl.Params.Count - 1 do
      begin
        VName := TMethodParam(ChainDecl.Params.Items[I]).ParamName;
        if OuterVars.IndexOf(VName) < 0 then
          OuterVars.Add(VName);
      end;
      ChainDecl := ChainDecl.EnclosingDecl;
    end;
    { Nested-of-method: the enclosing method's Self is capturable like any
      other outer name (BUG-008).  It is an implicit parameter, so it never
      appears in the local/param sets above — list it explicitly.  Implicit
      member references (bare fields, bare method calls) count as Self uses;
      the walker registers those below via the IsImplicitSelf annotations. }
    if FInNestedOfMethod then
    begin
      OuterVars.Add('Self');
      { Transitive Self plumbing: a nested-of-nested routine that captured
        Self needs THIS routine to receive and forward the Self pointer,
        even when this body never touches Self itself.  (The inner decls
        were analysed — and their captures collected — before this call.) }
      for I := 0 to ADecl.Body.ProcDecls.Count - 1 do
        if (TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars <> nil) and
           (TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars.IndexOf('Self') >= 0) then
          MaybeCaptureName(ADecl, OuterVars, 'Self');
    end;
    { A name that ADecl DECLARES as its own local var or parameter SHADOWS the
      enclosing var of the same name — a reference resolves to ADecl's own slot,
      NOT a capture.  Remove such names from OuterVars so MaybeCaptureName never
      adds them to CapturedVars (BUG-20260720-nested-shadow-local).  Case-
      insensitive (Pascal identifiers are), and Self is never a declared local
      so it is unaffected. }
    if ADecl.Body <> nil then
      for I := 0 to ADecl.Body.Decls.Count - 1 do
      begin
        VDecl := TVarDecl(ADecl.Body.Decls.Items[I]);
        for J := 0 to VDecl.Names.Count - 1 do
        begin
          VName := VDecl.Names.Strings[J];
          for K := OuterVars.Count - 1 downto 0 do
            if SameText(OuterVars.Strings[K], VName) then
              OuterVars.Delete(K);
        end;
      end;
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      VName := TMethodParam(ADecl.Params.Items[I]).ParamName;
      for K := OuterVars.Count - 1 downto 0 do
        if SameText(OuterVars.Strings[K], VName) then
          OuterVars.Delete(K);
    end;
    if OuterVars.Count = 0 then Exit;

    { Seed work-list with all statements in the inner body }
    for I := 0 to ADecl.Body.Stmts.Count - 1 do
      TodoStmts.Add(ADecl.Body.Stmts.Items[I]);

    { Iterative BFS over stmts, pushing child exprs/stmts onto the work-lists }
    while (TodoStmts.Count > 0) or (TodoExprs.Count > 0) do
    begin
      { Process one stmt }
      while TodoStmts.Count > 0 do
      begin
        CurStmt := TASTStmt(TodoStmts.Items[TodoStmts.Count - 1]);
        TodoStmts.Delete(TodoStmts.Count - 1);
        if CurStmt = nil then Continue;

        if CurStmt is TAssignment then
        begin
          { LHS name — check if it's an outer var (direct assign).  An
            implicit-Self field write is a use of the method's Self. }
          if TAssignment(CurStmt).ImplicitSelfField = nil then
            MaybeCaptureName(ADecl, OuterVars, TAssignment(CurStmt).Name)
          else
            MaybeCaptureName(ADecl, OuterVars, 'Self');
          TodoExprs.Add(TAssignment(CurStmt).Expr);
        end
        else if CurStmt is TFieldAssignment then
        begin
          { 'R.Field := ...' — the receiver R may be an outer var/var-param.
            Implicit-Self writes (RecordName names a field of Self) resolve
            through Self — that is a Self use (BUG-008). }
          if not TFieldAssignment(CurStmt).IsImplicitSelf then
            MaybeCaptureName(ADecl, OuterVars, TFieldAssignment(CurStmt).RecordName)
          else
            MaybeCaptureName(ADecl, OuterVars, 'Self');
          TodoExprs.Add(TFieldAssignment(CurStmt).ObjExpr);
          TodoExprs.Add(TFieldAssignment(CurStmt).PropIndexExpr);
          TodoExprs.Add(TFieldAssignment(CurStmt).Expr);
        end
        else if CurStmt is TStaticSubscriptAssign then
        begin
          { 'A[i] := ...' — the array A may be an outer var/var-param.
            Implicit-Self array writes resolve through Self. }
          if not TStaticSubscriptAssign(CurStmt).IsImplicitSelf then
            MaybeCaptureName(ADecl, OuterVars, TStaticSubscriptAssign(CurStmt).ArrayName)
          else
            MaybeCaptureName(ADecl, OuterVars, 'Self');
          TodoExprs.Add(TStaticSubscriptAssign(CurStmt).BaseExpr);
          TodoExprs.Add(TStaticSubscriptAssign(CurStmt).IndexExpr);
          TodoExprs.Add(TStaticSubscriptAssign(CurStmt).ValueExpr);
        end
        else if CurStmt is TProcCall then
        begin
          { A bare call that resolved to a method of the enclosing class is
            an implicit Self.Method() dispatch. }
          if TProcCall(CurStmt).IsImplicitSelfMethod then
            MaybeCaptureName(ADecl, OuterVars, 'Self');
          { A call to a SIBLING nested routine forwards the callee's captured
            outer variables by address, so the CALLER must capture them too —
            even when its own body never references them (BUG-031).  Only
            names that belong to the shared enclosing scope fold in (the
            OuterVars filter inside MaybeCaptureName).  Siblings are analysed
            in declaration order, so the callee's capture set is final here. }
          if (TProcCall(CurStmt).ResolvedDecl <> nil) and
             (TProcCall(CurStmt).ResolvedDecl is TMethodDecl) and
             (TMethodDecl(TProcCall(CurStmt).ResolvedDecl).EnclosingDecl <> nil) and
             (TMethodDecl(TProcCall(CurStmt).ResolvedDecl).CapturedVars <> nil) then
            for J := 0 to TMethodDecl(TProcCall(CurStmt).ResolvedDecl)
                            .CapturedVars.Count - 1 do
              MaybeCaptureName(ADecl, OuterVars,
                TMethodDecl(TProcCall(CurStmt).ResolvedDecl)
                  .CapturedVars.Strings[J]);
          for J := 0 to TProcCall(CurStmt).Args.Count - 1 do
            TodoExprs.Add(TProcCall(CurStmt).Args.Items[J]);
        end
        else if CurStmt is TMethodCallStmt then
        begin
          { The RECEIVER is a name reference too — without this a nested
            routine calling a method on a captured outer object (or on the
            enclosing method's Self) never registered the capture and read
            a garbage frame slot. }
          if TMethodCallStmt(CurStmt).IsImplicitSelf then
            MaybeCaptureName(ADecl, OuterVars, 'Self');
          MaybeCaptureName(ADecl, OuterVars, TMethodCallStmt(CurStmt).ObjectName);
          if TMethodCallStmt(CurStmt).ObjExpr <> nil then
            TodoExprs.Add(TMethodCallStmt(CurStmt).ObjExpr);
          for J := 0 to TMethodCallStmt(CurStmt).Args.Count - 1 do
            TodoExprs.Add(TMethodCallStmt(CurStmt).Args.Items[J]);
        end
        else if CurStmt is TIfStmt then
        begin
          TodoExprs.Add(TIfStmt(CurStmt).Condition);
          TodoStmts.Add(TIfStmt(CurStmt).ThenStmt);
          TodoStmts.Add(TIfStmt(CurStmt).ElseStmt);
        end
        else if CurStmt is TWhileStmt then
        begin
          TodoExprs.Add(TWhileStmt(CurStmt).Condition);
          TodoStmts.Add(TWhileStmt(CurStmt).Body);
        end
        else if CurStmt is TRepeatStmt then
        begin
          for J := 0 to TRepeatStmt(CurStmt).Body.Stmts.Count - 1 do
            TodoStmts.Add(TRepeatStmt(CurStmt).Body.Stmts.Items[J]);
          TodoExprs.Add(TRepeatStmt(CurStmt).Condition);
        end
        else if CurStmt is TForStmt then
        begin
          MaybeCaptureName(ADecl, OuterVars, TForStmt(CurStmt).VarName);
          TodoExprs.Add(TForStmt(CurStmt).StartExpr);
          TodoExprs.Add(TForStmt(CurStmt).EndExpr);
          TodoStmts.Add(TForStmt(CurStmt).Body);
        end
        else if CurStmt is TCompoundStmt then
        begin
          for J := 0 to TCompoundStmt(CurStmt).Stmts.Count - 1 do
            TodoStmts.Add(TCompoundStmt(CurStmt).Stmts.Items[J]);
        end
        else if CurStmt is TTryFinallyStmt then
        begin
          TodoStmts.Add(TTryFinallyStmt(CurStmt).TryBody);
          TodoStmts.Add(TTryFinallyStmt(CurStmt).FinallyBody);
        end
        else if CurStmt is TTryExceptStmt then
        begin
          TodoStmts.Add(TTryExceptStmt(CurStmt).TryBody);
          TodoStmts.Add(TTryExceptStmt(CurStmt).ExceptBody);
          TodoStmts.Add(TTryExceptStmt(CurStmt).ElseBody);
          if TTryExceptStmt(CurStmt).Handlers <> nil then
            for J := 0 to TTryExceptStmt(CurStmt).Handlers.Count - 1 do
              TodoStmts.Add(
                TExceptHandlerClause(TTryExceptStmt(CurStmt).Handlers.Items[J]).Body);
        end
        else if CurStmt is TRaiseStmt then
          TodoExprs.Add(TRaiseStmt(CurStmt).Expr)
        else if CurStmt is TExitStmt then
          TodoExprs.Add(TExitStmt(CurStmt).Value)
        else if CurStmt is TCaseStmt then
        begin
          TodoExprs.Add(TCaseStmt(CurStmt).Selector);
          TodoStmts.Add(TCaseStmt(CurStmt).ElseStmt);
          for J := 0 to TCaseStmt(CurStmt).Branches.Count - 1 do
            TodoStmts.Add(TCaseBranch(TCaseStmt(CurStmt).Branches.Items[J]).Stmt);
        end
        else if CurStmt is TForInStmt then
        begin
          MaybeCaptureName(ADecl, OuterVars, TForInStmt(CurStmt).VarName);
          TodoExprs.Add(TForInStmt(CurStmt).CollExpr);
          TodoStmts.Add(TForInStmt(CurStmt).Body);
        end
        else if CurStmt is TPointerWriteStmt then
        begin
          TodoExprs.Add(TPointerWriteStmt(CurStmt).PtrExpr);
          TodoExprs.Add(TPointerWriteStmt(CurStmt).ValExpr);
        end
        else if CurStmt is TInheritedCallStmt then
        begin
          { 'inherited M(...)' dispatches on the method's Self. }
          MaybeCaptureName(ADecl, OuterVars, 'Self');
          for J := 0 to TInheritedCallStmt(CurStmt).Args.Count - 1 do
            TodoExprs.Add(TInheritedCallStmt(CurStmt).Args.Items[J]);
        end
        else if CurStmt is TVarDeclStmt then
        begin
          { Block-scoped 'var X := Expr' — the initialiser may reference
            outer vars (or Self).  The analysed form holds it in the
            synthesised InitAssign. }
          TodoExprs.Add(TVarDeclStmt(CurStmt).InitExpr);
          TodoStmts.Add(TVarDeclStmt(CurStmt).InitAssign);
        end
      end;

      { Process one expr }
      if TodoExprs.Count > 0 then
      begin
        CurExpr := TASTExpr(TodoExprs.Items[TodoExprs.Count - 1]);
        TodoExprs.Delete(TodoExprs.Count - 1);
        if CurExpr = nil then Continue;

        if CurExpr is TIdentExpr then
        begin
          { A bare ident that resolved as an implicit Self member (field
            read or zero-arg method call) is a use of the method's Self. }
          if TIdentExpr(CurExpr).IsImplicitSelf or
             TIdentExpr(CurExpr).IsImplicitSelfMethod then
            MaybeCaptureName(ADecl, OuterVars, 'Self')
          else
            MaybeCaptureName(ADecl, OuterVars, TIdentExpr(CurExpr).Name);
        end
        else if CurExpr is TFieldAccessExpr then
        begin
          { 'R.Field' read — the base R may be an outer var/var-param.  When the
            base is a sub-expression (chain), descend; when it is a bare name,
            capture it.  Implicit-Self reads resolve through Self. }
          if TFieldAccessExpr(CurExpr).Base <> nil then
            TodoExprs.Add(TFieldAccessExpr(CurExpr).Base)
          else if TFieldAccessExpr(CurExpr).IsImplicitSelf then
            MaybeCaptureName(ADecl, OuterVars, 'Self')
          else
            MaybeCaptureName(ADecl, OuterVars, TFieldAccessExpr(CurExpr).RecordName);
          TodoExprs.Add(TFieldAccessExpr(CurExpr).PropIndexExpr);
        end
        else if CurExpr is TStringSubscriptExpr then
        begin
          TodoExprs.Add(TStringSubscriptExpr(CurExpr).StrExpr);
          TodoExprs.Add(TStringSubscriptExpr(CurExpr).IndexExpr);
        end
        else if CurExpr is TBinaryExpr then
        begin
          TodoExprs.Add(TBinaryExpr(CurExpr).Left);
          TodoExprs.Add(TBinaryExpr(CurExpr).Right);
        end
        else if CurExpr is TNotExpr then
          TodoExprs.Add(TNotExpr(CurExpr).Expr)
        else if CurExpr is TFuncCallExpr then
        begin
          { A bare function call that resolved to a method of the enclosing
            class dispatches on the method's Self. }
          if TFuncCallExpr(CurExpr).IsImplicitSelfMethod then
            MaybeCaptureName(ADecl, OuterVars, 'Self');
          { Sibling nested-routine call: fold the callee's captures into the
            caller (BUG-031) — see the TProcCall branch. }
          if (TFuncCallExpr(CurExpr).ResolvedDecl <> nil) and
             (TFuncCallExpr(CurExpr).ResolvedDecl is TMethodDecl) and
             (TMethodDecl(TFuncCallExpr(CurExpr).ResolvedDecl).EnclosingDecl <> nil) and
             (TMethodDecl(TFuncCallExpr(CurExpr).ResolvedDecl).CapturedVars <> nil) then
            for J := 0 to TMethodDecl(TFuncCallExpr(CurExpr).ResolvedDecl)
                            .CapturedVars.Count - 1 do
              MaybeCaptureName(ADecl, OuterVars,
                TMethodDecl(TFuncCallExpr(CurExpr).ResolvedDecl)
                  .CapturedVars.Strings[J]);
          for J := 0 to TFuncCallExpr(CurExpr).Args.Count - 1 do
            TodoExprs.Add(TFuncCallExpr(CurExpr).Args.Items[J]);
        end
        else if CurExpr is TMethodCallExpr then
        begin
          { The receiver of 'Obj.M()' in expression position may be an outer
            var — or the enclosing method's Self. }
          MaybeCaptureName(ADecl, OuterVars, TMethodCallExpr(CurExpr).ObjectName);
          if TMethodCallExpr(CurExpr).ObjExpr <> nil then
            TodoExprs.Add(TMethodCallExpr(CurExpr).ObjExpr);
          for J := 0 to TMethodCallExpr(CurExpr).Args.Count - 1 do
            TodoExprs.Add(TMethodCallExpr(CurExpr).Args.Items[J]);
        end
        else if CurExpr is TArrayLiteralExpr then
        begin
          for J := 0 to TArrayLiteralExpr(CurExpr).Elements.Count - 1 do
            TodoExprs.Add(TArrayLiteralExpr(CurExpr).Elements.Items[J]);
        end
        else if CurExpr is TIsExpr then
          TodoExprs.Add(TIsExpr(CurExpr).Obj)
        else if CurExpr is TAsExpr then
          TodoExprs.Add(TAsExpr(CurExpr).Obj)
        else if CurExpr is TSupportsExpr then
          TodoExprs.Add(TSupportsExpr(CurExpr).Obj)
        else if CurExpr is TDerefExpr then
          TodoExprs.Add(TDerefExpr(CurExpr).Expr)
        else if CurExpr is TAddrOfExpr then
          TodoExprs.Add(TAddrOfExpr(CurExpr).Expr)
        else if CurExpr is TIndirectFuncCallExpr then
        begin
          TodoExprs.Add(TIndirectFuncCallExpr(CurExpr).CalleeExpr);
          for J := 0 to TIndirectFuncCallExpr(CurExpr).Args.Count - 1 do
            TodoExprs.Add(TIndirectFuncCallExpr(CurExpr).Args.Items[J]);
        end
        else if CurExpr is TInheritedCallExpr then
        begin
          { 'inherited F(...)' in expression position dispatches on Self. }
          MaybeCaptureName(ADecl, OuterVars, 'Self');
          for J := 0 to TInheritedCallExpr(CurExpr).Args.Count - 1 do
            TodoExprs.Add(TInheritedCallExpr(CurExpr).Args.Items[J]);
        end;
      end;
    end;
  finally
    OuterVars.Free();
    TodoExprs.Free();
    TodoStmts.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Inlining: eligibility analyser                                       }
{ ------------------------------------------------------------------ }
{ A function is inlinable when all of:                                 }
{   - has a body (not external, not forward)                           }
{   - not a method on a class or record                                }
{   - not generic (TypeParams = nil)                                   }
{   - has no var-params, open-array params, interface params, or       }
{     record-by-value params                                           }
{   - return type is nil (procedure) or a primitive scalar fitting     }
{     in a register (no record/string/class returns)                   }
{   - body has no try/except/finally, no raise, no loops, no nested    }
{     function/method calls that are themselves recursive, and no      }
{     references to the function itself (no self-recursion)            }
{   - body has at most a small number of statements                    }
{                                                                      }
{ Implementation: walks Body.Stmts and the parameter/return type list. }
{ Used by codegen — see docs/inlining-design.adoc.                     }

function TSemanticAnalyser.AssignmentTargetsParameter(const AName: string;
                                                       const ADecl: TMethodDecl): Boolean;
var
  I: Integer;
begin
  Result := False;
  if ADecl = nil then Exit;
  for I := 0 to ADecl.Params.Count - 1 do
    if SameText(TMethodParam(ADecl.Params.Items[I]).ParamName, AName) then
    begin
      Exit(True);
    end;
end;

function TSemanticAnalyser.ExprRejectsInline(AExpr: TASTExpr;
                                              const ASelfDecl: TMethodDecl): Boolean;
var
  FC:  TFuncCallExpr;
  Bin: TBinaryExpr;
  I:   Integer;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    { Self-recursion makes inlining unbounded. }
    if FC.ResolvedDecl = ASelfDecl then begin Result := True; Exit; end;
    for I := 0 to FC.Args.Count - 1 do
      if ExprRejectsInline(TASTExpr(FC.Args.Items[I]), ASelfDecl) then
        begin Result := True; Exit; end;
    Exit;
  end;
  if AExpr is TMethodCallExpr then begin Result := True; Exit; end;
  if AExpr is TBinaryExpr then
  begin
    Bin := TBinaryExpr(AExpr);
    if ExprRejectsInline(Bin.Left, ASelfDecl) then begin Result := True; Exit; end;
    if ExprRejectsInline(Bin.Right, ASelfDecl) then begin Result := True; Exit; end;
    Exit;
  end;
  if AExpr is TNotExpr then
  begin
    Exit(ExprRejectsInline(TNotExpr(AExpr).Expr, ASelfDecl));
  end;
end;

function TSemanticAnalyser.StmtRejectsInline(AStmt: TASTStmt;
                                              const ASelfDecl: TMethodDecl;
                                              var AStmtCount: Integer): Boolean;
var
  I, J: Integer;
  Cmp:  TCompoundStmt;
  Asg:  TAssignment;
  Ifs:  TIfStmt;
  Cs:   TCaseStmt;
  Br:   TCaseBranch;
begin
  Result := True;
  if AStmt = nil then begin Result := False; Exit; end;

  { Hard rejects: loops, try, raise, method calls, nested calls we can't trace. }
  if (AStmt is TWhileStmt) or
     (AStmt is TRepeatStmt) or
     (AStmt is TForStmt) or
     (AStmt is TForInStmt) or
     (AStmt is TTryFinallyStmt) or
     (AStmt is TTryExceptStmt) or
     (AStmt is TRaiseStmt) or
     (AStmt is TBreakStmt) or
     (AStmt is TContinueStmt) or
     (AStmt is TMethodCallStmt) or
     (AStmt is TInheritedCallStmt) or
     (AStmt is TPointerWriteStmt) or
     (AStmt is TFieldAssignment) or
     (AStmt is TStaticSubscriptAssign) then
    Exit;

  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      if StmtRejectsInline(TASTStmt(Cmp.Stmts.Items[I]), ASelfDecl, AStmtCount) then
        Exit;
    Exit(False);
  end;

  if AStmt is TExitStmt then
  begin
    Inc(AStmtCount);
    Exit(False);
  end;

  if AStmt is TIfStmt then
  begin
    Ifs := TIfStmt(AStmt);
    Inc(AStmtCount);
    if ExprRejectsInline(Ifs.Condition, ASelfDecl) then Exit;
    if StmtRejectsInline(Ifs.ThenStmt, ASelfDecl, AStmtCount) then Exit;
    if (Ifs.ElseStmt <> nil) and
       StmtRejectsInline(Ifs.ElseStmt, ASelfDecl, AStmtCount) then Exit;
    Exit(False);
  end;

  if AStmt is TAssignment then
  begin
    Asg := TAssignment(AStmt);
    Inc(AStmtCount);
    if ExprRejectsInline(Asg.Expr, ASelfDecl) then Exit;
    { Assignment to a parameter requires updating the caller-side temp,
      which the simple inliner does not support.  Reject. }
    if AssignmentTargetsParameter(Asg.Name, ASelfDecl) then Exit;
    Exit(False);
  end;

  if AStmt is TProcCall then
  begin
    Inc(AStmtCount);
    { Calls to other functions inside an inline candidate are allowed as long
      as they are not the function itself.  The codegen will emit them as
      regular calls or inline them in turn. }
    if TProcCall(AStmt).ResolvedDecl = ASelfDecl then Exit;
    for I := 0 to TProcCall(AStmt).Args.Count - 1 do
      if ExprRejectsInline(TASTExpr(TProcCall(AStmt).Args.Items[I]), ASelfDecl) then
        Exit;
    Exit(False);
  end;

  if AStmt is TCaseStmt then
  begin
    Cs := TCaseStmt(AStmt);
    Inc(AStmtCount);
    if ExprRejectsInline(Cs.Selector, ASelfDecl) then Exit;
    for I := 0 to Cs.Branches.Count - 1 do
    begin
      Br := TCaseBranch(Cs.Branches.Items[I]);
      for J := 0 to Br.Values.Count - 1 do
        if ExprRejectsInline(TASTExpr(Br.Values.Items[J]), ASelfDecl) then Exit;
      if StmtRejectsInline(Br.Stmt, ASelfDecl, AStmtCount) then Exit;
    end;
    if (Cs.ElseStmt <> nil) and
       StmtRejectsInline(Cs.ElseStmt, ASelfDecl, AStmtCount) then Exit;
    Exit(False);
  end;

  { Unknown statement form: reject conservatively. }
end;

function TSemanticAnalyser.IsInlineEligible(ADecl: TMethodDecl): Boolean;
const
  MAX_STMTS = 24;
var
  I:   Integer;
  Par: TMethodParam;
  K:   TTypeKind;
  Cnt: Integer;
begin
  Result := False;
  if ADecl = nil then Exit;
  if ADecl.IsExternal then Exit;
  if ADecl.Body = nil then Exit;
  if ADecl.OwnerTypeName <> '' then Exit;       { class/record method — phase 2 }
  if ADecl.TypeParams <> nil then Exit;         { generic template }
  if ADecl.VTableSlot >= 0 then Exit;           { virtual dispatch }
  if ADecl.IsVirtual or ADecl.IsAbstract then Exit;

  { Return type: nil (procedure) or primitive scalar only. }
  if ADecl.ResolvedReturnType <> nil then
  begin
    K := ADecl.ResolvedReturnType.Kind;
    if not (K in [tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
                  tyInt64, tyUInt64, tySmallInt, tyWord,
                  tyDouble, tySingle, tyPointer, tyPChar]) then
      Exit;
  end;

  { Parameters: only primitive by-value. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray then Exit;
    if Par.ResolvedType = nil then Exit;
    K := Par.ResolvedType.Kind;
    if not (K in [tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
                  tyInt64, tyUInt64, tySmallInt, tyWord,
                  tyDouble, tySingle, tyPointer, tyPChar]) then
      Exit;
  end;

  { No local variables (phase 1 keeps it simple — only the implicit Result). }
  if (ADecl.Body.Decls <> nil) and (ADecl.Body.Decls.Count > 0) then Exit;
  if (ADecl.Body.TypeDecls <> nil) and (ADecl.Body.TypeDecls.Count > 0) then Exit;
  if (ADecl.Body.ConstDecls <> nil) and (ADecl.Body.ConstDecls.Count > 0) then Exit;
  if (ADecl.Body.ProcDecls <> nil) and (ADecl.Body.ProcDecls.Count > 0) then Exit;

  { Walk body statements, counting and checking. }
  Cnt := 0;
  for I := 0 to ADecl.Body.Stmts.Count - 1 do
  begin
    if StmtRejectsInline(TASTStmt(ADecl.Body.Stmts.Items[I]), ADecl, Cnt) then Exit;
    if Cnt > MAX_STMTS then Exit;
  end;

  Result := True;
end;

procedure TSemanticAnalyser.MarkInlineCandidates(ABlock: TBlock);
var
  I:     Integer;
  ADecl: TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    ADecl.IsInlineCandidate := IsInlineEligible(ADecl);
  end;
end;

procedure TSemanticAnalyser.AnalyseVarDecls(ABlock: TBlock);
var
  I, J, K: Integer;
  Decl:    TVarDecl;
  Typ:     TTypeDesc;
  VarName: string;
  Sym:     TSymbol;
  EnumShadowSym: TSymbol;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Items[I]);

    Typ := FindTypeOrInstantiate(Decl.TypeName);
    if Typ = nil then
      SemanticError(
        Format('Unknown type ''%s''', [Decl.TypeName]),
        Decl.Line, Decl.Col);

    Decl.ResolvedType := Typ;

    { Resolve [Weak].  Only reference types carry strong refcounts, so
      weakness is meaningful only on classes and interfaces.  Rejecting
      it elsewhere catches misuse at the declaration site rather than
      later when the user wonders why the attribute had no effect. }
    if HasWeakAttribute(Decl.Attributes) then
    begin
      if not ((Typ.Kind = tyClass) or (Typ.Kind = tyInterface)) then
        SemanticError(
          Format('[Weak] can only be applied to class or interface types, ' +
                 'not ''%s''', [Decl.TypeName]),
          Decl.Line, Decl.Col);
      Decl.IsWeak := True;
    end;

    { Depth 2 = inside the top-level program block — these are global variables. }
    Decl.IsGlobal := (FScopeDepth = 1);  { depth 1 = main program block (global scope) }
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Strings[J];
      { Consts from the same block live in the immediately enclosing scope
        (AnalyseBlock pushes a new scope before calling AnalyseVarDecls, so
        FTable.Define cannot see same-block consts).  Scan the block's own
        ConstDecls list so we catch only same-block clashes, not legitimate
        shadowing of outer-scope or unit-imported consts. }
      for K := 0 to ABlock.ConstDecls.Count - 1 do
        if SameText(TConstDecl(ABlock.ConstDecls.Items[K]).Name, VarName) then
          SemanticError(
            Format('Duplicate identifier ''%s''', [VarName]),
            Decl.Line, Decl.Col);
      { A variable may not share a name with any visible type — built-in,
        same-block, outer-scope, or imported (issue #102).  Pascal is
        case-insensitive, so `type Iface` and `var iface` are the same
        identifier; allowing both silently shadows the type and is a
        common source of confusion.  Stricter than FPC mode objfpc, which
        permits shadowing built-in/outer types; Blaise rejects the whole
        class.  (Same-scope type-vs-var is otherwise invisible to
        FTable.Define because types live in the enclosing scope while
        var decls are registered one scope deeper.) }
      { A generic type PARAMETER in scope (registered as a T=Integer alias
        while an instantiated body is analysed) is not a user-declared type
        the programmer is shadowing — a local `var t: T` is legitimate.  Only
        flag a clash with a genuine visible type. }
      if (FTable.FindType(VarName) <> nil) and
         (FActiveTypeParams.IndexOf(VarName) < 0) then
        SemanticError(
          Format('Duplicate identifier ''%s'' — a type with this name is ' +
                 'already visible', [VarName]),
          Decl.Line, Decl.Col);
      { A variable may not share a name with a visible ENUM MEMBER (case-
        insensitive).  Shadowing it silently retargets the member in a set
        literal `[A, c, D]` to the variable — which is not a constant, so QBE
        errors cryptically and native miscompiles the bitmask.  Reject it, in
        the same spirit as the type-name rule above. }
      EnumShadowSym := FTable.Lookup(VarName);
      if (EnumShadowSym <> nil) and (EnumShadowSym.Kind = skConstant) and
         (EnumShadowSym.TypeDesc <> nil) and
         (EnumShadowSym.TypeDesc.Kind = tyEnum) then
        SemanticError(
          Format('Duplicate identifier ''%s'' — an enum member with this name ' +
                 'is already visible', [VarName]),
          Decl.Line, Decl.Col);
      if Decl.IsThreadVar and not Decl.IsGlobal then
        SemanticError('threadvar is only allowed at unit or program scope',
          Decl.Line, Decl.Col);
      Sym := TSymbol.Create(VarName, skVariable, Typ);
      Sym.IsWeak      := Decl.IsWeak;
      Sym.IsGlobal    := Decl.IsGlobal;
      Sym.IsThreadVar := Decl.IsThreadVar;
      if not FTable.Define(Sym) then
      begin
        Sym.Free();
        SemanticError(
          Format('Duplicate identifier ''%s''', [VarName]),
          Decl.Line, Decl.Col);
      end;
    end;
    if Decl.InitConst <> nil then
      Self.AnalyseVarInitializer(Decl);
  end;
end;

{ Analyse and fold a variable initialiser (var G: T = value).  The initialiser
  is carried as a TConstDecl (Decl.InitConst) reusing the const value pipeline.
  Scalar/string values are folded and type-checked against the declared type;
  array values derive their element type and bounds from the declared static
  array type, fold their elements, and mint a data label.  Record initialisers
  are not yet supported (no record-const machinery). }
procedure TSemanticAnalyser.AnalyseVarInitializer(ADecl: TVarDecl);
var
  CD:     TConstDecl;
  Typ:    TTypeDesc;
  SAT:    TStaticArrayTypeDesc;
  J:      Integer;
begin
  CD  := ADecl.InitConst;
  Typ := ADecl.ResolvedType;
  if Typ = nil then Exit;

  { Initialisers are only meaningful for global storage — locals are zeroed and
    assigned in the body.  Initialised locals could be supported later (emit the
    assignment at scope entry); reject for now to keep the data-section path the
    single source of truth. }
  if not ADecl.IsGlobal then
    SemanticError(
      'Variable initialisers are only supported on global variables',
      CD.Line, CD.Col);

  { Aggregate (array) initialiser: derive element type + bounds from the
    declared static array type, then drive the array-const folding. }
  if CD.IsArrayConst then
  begin
    if Typ.Kind <> tyStaticArray then
      SemanticError(Format(
        'Parenthesised initialiser requires a static array type, not ''%s''',
        [ADecl.TypeName]), CD.Line, CD.Col);
    SAT := TStaticArrayTypeDesc(Typ);
    if SAT.ElementType.Kind = tyStaticArray then
      SemanticError(
        'Initialisers for multi-dimensional arrays are not yet supported',
        CD.Line, CD.Col);
    CD.ArrayElemType := SAT.ElementType.Name;
    CD.ArrayLowBound := SAT.LowBound;
    CD.ArrayHighBound := SAT.HighBound;
    CD.ArrayIsRangeIndexed := True;
    if CD.ArrayElements.Count <> (SAT.HighBound - SAT.LowBound + 1) then
      SemanticError(Format(
        'Initialiser for ''%s'' has %d element(s) but the array needs %d',
        [ADecl.Names.Strings[0], CD.ArrayElements.Count,
         SAT.HighBound - SAT.LowBound + 1]), CD.Line, CD.Col);
    { Fold any deferred bit-op element expressions to integer strings. }
    if CD.ArrayElementParts <> nil then
      for J := 0 to CD.ArrayElementParts.Count - 1 do
        if (CD.ArrayElementParts.Items[J] <> nil) and
           (J < CD.ArrayElements.Count) then
          CD.ArrayElements.Put(J, IntToStr(FoldConstBitOpExpr(
            TStringList(CD.ArrayElementParts.Items[J]), CD.Line, CD.Col)));
    if CD.ResolvedQbeName = '' then
      CD.ResolvedQbeName := Self.NewArrayConstLabel(CD.Name);
    Exit;
  end;

  if Typ.Kind = tyRecord then
    SemanticError(
      'Record variable initialisers are not yet supported',
      CD.Line, CD.Col);

  { Set initialiser: not yet supported on variables (AnalyseSetConstDecl also
    defines a const symbol, which would clash with the variable symbol).  Use a
    named set constant for now. }
  if CD.IsSet then
    SemanticError(
      'Set variable initialisers are not yet supported; use a named constant',
      CD.Line, CD.Col);

  { Scalar / string initialiser. }
  if CD.IsString and (CD.ConstParts <> nil) then
    SemanticError(
      'Named-constant string initialisers are not yet supported on variables',
      CD.Line, CD.Col);
  if CD.IntExprTokens <> nil then
    CD.IntVal := FoldConstBitOpExpr(CD.IntExprTokens, CD.Line, CD.Col);
  if (CD.IntValueExpr <> nil) and IsFloatConstExpr(CD.IntValueExpr) then
  begin
    CD.StrVal  := EvalConstFloatExpr(CD.IntValueExpr, CD.Line, CD.Col);
    CD.IsFloat := True;
    CD.IsString := False;
  end
  else if CD.IntValueExpr <> nil then
    CD.IntVal := EvalConstIntExpr(CD.IntValueExpr, CD.Line, CD.Col);
  if (not CD.IsFloat) and (not CD.IsString) and
     (Typ.Kind in [tyDouble, tySingle]) then
  begin
    CD.StrVal  := IntToStr(CD.IntVal);
    CD.IsFloat := True;
  end;

  { Type compatibility check between the folded value kind and the declared
    type — catches 'var N: Integer = ''text''' and similar. }
  if CD.IsString then
  begin
    if not Typ.IsString() then
      SemanticError(Format(
        'String initialiser is incompatible with type ''%s''', [ADecl.TypeName]),
        CD.Line, CD.Col);
  end
  else if CD.IsFloat then
  begin
    if not (Typ.Kind in [tyDouble, tySingle]) then
      SemanticError(Format(
        'Real initialiser is incompatible with type ''%s''', [ADecl.TypeName]),
        CD.Line, CD.Col);
  end
  else
  begin
    { Integer/boolean/enum-ordinal initialiser. }
    if not (Typ.IsNumeric() or (Typ.Kind in [tyBoolean, tyEnum,
            tyPointer, tyPChar])) then
      SemanticError(Format(
        'Numeric initialiser is incompatible with type ''%s''', [ADecl.TypeName]),
        CD.Line, CD.Col);
  end;
end;

procedure TSemanticAnalyser.AnalyseCompoundBody(ABody: TCompoundStmt);
var
  I: Integer;
begin
  for I := 0 to ABody.Stmts.Count - 1 do
    AnalyseStmt(TASTStmt(ABody.Stmts.Items[I]));
end;

procedure TSemanticAnalyser.AnalyseStmts(ABlock: TBlock);
var
  I:         Integer;
  PrevBlock: TBlock;
begin
  PrevBlock := FCurrentLocalBlock;
  FCurrentLocalBlock := ABlock;
  try
    for I := 0 to ABlock.Stmts.Count - 1 do
      AnalyseStmt(TASTStmt(ABlock.Stmts.Items[I]));
  finally
    FCurrentLocalBlock := PrevBlock;
  end;
end;

procedure TSemanticAnalyser.AnalyseStmt(AStmt: TASTStmt);
var
  IfS:    TIfStmt;
  CmpS:   TCompoundStmt;
  SavedBlockSite: TObject;
  ForS:   TForStmt;
  ForInS: TForInStmt;
  WS:     TWhileStmt;
  RS:     TRepeatStmt;
  TFS:    TTryFinallyStmt;
  TES:    TTryExceptStmt;
  H:      TExceptHandlerClause;
  RaiseS: TRaiseStmt;
  I:         Integer;
  CondType:  TTypeDesc;
  VarSym:    TSymbol;
  StartType: TTypeDesc;
  EndType:   TTypeDesc;
  ResultSym:  TSymbol;
  ExitAssign: TAssignment;
  CollType:     TTypeDesc;
  CollRT:       TRecordTypeDesc;
  GetEnumDecl:  TMethodDecl;
  EnumType:     TTypeDesc;
  EnumRT:       TRecordTypeDesc;
  MNDecl:       TMethodDecl;
  CurProp:      TPropertyInfo;
  CurDecl:      TMethodDecl;
  ElemType:     TTypeDesc;
  SynthDecl:    TVarDecl;
  WalkRT:       TRecordTypeDesc;
  K:            Integer;
  L:            Integer;
  DupLocal:     Boolean;
begin
  { Inline-assembler block: opaque to the front end — its content is assembly,
    not Pascal, so no statement/type/ARC analysis runs over it. }
  if AStmt is TAsmStmt then
    Exit;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    VarSym := FTable.Lookup(ForS.VarName);
    if VarSym = nil then
      SemanticError(
        Format('Undeclared loop variable ''%s''', [ForS.VarName]),
        ForS.Line, ForS.Col);
    ForS.VarName  := VarSym.Name;  { normalise to declared casing }
    ForS.IsGlobal := (VarSym <> nil) and VarSym.IsGlobal;
    if VarSym.Kind <> skVariable then
      SemanticError(
        Format('''%s'' is not a variable', [ForS.VarName]),
        ForS.Line, ForS.Col);
    if not VarSym.TypeDesc.IsOrdinal() then
      SemanticError(
        Format('Loop variable ''%s'' must be an ordinal type, got ''%s''',
          [ForS.VarName, VarSym.TypeDesc.Name]),
        ForS.Line, ForS.Col);
    { A bare enum-member bound is steered to the loop variable's enum. }
    if TryResolveBareEnumIdent(ForS.StartExpr, VarSym.TypeDesc) then
      StartType := ForS.StartExpr.ResolvedType
    else
      StartType := Self.AnalyseExprSlot(ForS.StartExpr);
    CheckTypesMatch(VarSym.TypeDesc, StartType,
      'for-loop start expression', ForS.Line, ForS.Col);
    if TryResolveBareEnumIdent(ForS.EndExpr, VarSym.TypeDesc) then
      EndType := ForS.EndExpr.ResolvedType
    else
      EndType := Self.AnalyseExprSlot(ForS.EndExpr);
    CheckTypesMatch(VarSym.TypeDesc, EndType,
      'for-loop end expression', ForS.Line, ForS.Col);
    Inc(FLoopDepth);
    try
      AnalyseStmt(ForS.Body);
    finally
      Dec(FLoopDepth);
    end;
  end
  else if AStmt is TForInStmt then
  begin
    ForInS := TForInStmt(AStmt);

    { 1. Analyse the collection expression }
    CollType := Self.AnalyseExprSlot(ForInS.CollExpr);
    if CollType = nil then
      SemanticError('for-in collection has unknown type',
        ForInS.Line, ForInS.Col);

    if CollType.Kind = tyStaticArray then
    begin
      { ---- Static array iteration path ---- }
      ElemType := TStaticArrayTypeDesc(CollType).ElementType;

      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarName := VarSym.Name;  { normalise to declared casing }
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      CheckTypesMatch(VarSym.TypeDesc, ElemType,
        'for-in loop variable', ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal    := VarSym.IsGlobal;
      ForInS.IsArrayIter    := True;
      ForInS.ResolvedVarType := ElemType;
      ForInS.ArrayLow  := TStaticArrayTypeDesc(CollType).LowBound;
      ForInS.ArrayHigh := TStaticArrayTypeDesc(CollType).HighBound;

      { Inject synthetic index slot __idx_N (Integer) }
      ForInS.IdxVarName := '__idx_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create();
        SynthDecl.Names.Add(ForInS.IdxVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else if CollType.Kind = tyClass then
    begin
      { ---- Class enumerator protocol path ---- }
      CollRT := TRecordTypeDesc(CollType);

      GetEnumDecl := FindMethodDecl(CollRT.Name, 'GetEnumerator');
      if GetEnumDecl = nil then
        SemanticError(
          Format('class ''%s'' does not have a GetEnumerator method',
            [CollRT.Name]),
          ForInS.Line, ForInS.Col);

      EnumType := GetEnumDecl.ResolvedReturnType;
      if (EnumType = nil) or (EnumType.Kind <> tyClass) then
        SemanticError(
          Format('GetEnumerator on ''%s'' must return a class type',
            [CollRT.Name]),
          ForInS.Line, ForInS.Col);
      EnumRT := TRecordTypeDesc(EnumType);

      MNDecl := FindMethodDecl(EnumRT.Name, 'MoveNext');
      if MNDecl = nil then
        SemanticError(
          Format('enumerator class ''%s'' does not have a MoveNext method',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);
      if (MNDecl.ResolvedReturnType = nil) or
         (MNDecl.ResolvedReturnType.Kind <> tyBoolean) then
        SemanticError(
          Format('MoveNext on enumerator ''%s'' must return Boolean',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);

      CurProp := nil;
      WalkRT  := EnumRT;
      while (WalkRT <> nil) and (CurProp = nil) do
      begin
        CurProp := WalkRT.FindProperty('Current');
        WalkRT  := WalkRT.Parent;
      end;
      if CurProp = nil then
        SemanticError(
          Format('enumerator class ''%s'' does not have a Current property',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);
      if CurProp.ReadMethod = '' then
        SemanticError(
          Format('Current property on ''%s'' must have a method-backed getter',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);

      CurDecl := FindMethodDecl(EnumRT.Name, CurProp.ReadMethod);
      if CurDecl = nil then
        SemanticError(
          Format('getter ''%s'' for Current on ''%s'' not found',
            [CurProp.ReadMethod, EnumRT.Name]),
          ForInS.Line, ForInS.Col);
      ElemType := CurDecl.ResolvedReturnType;

      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarName := VarSym.Name;  { normalise to declared casing }
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      CheckTypesMatch(VarSym.TypeDesc, ElemType,
        'for-in loop variable', ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal := VarSym.IsGlobal;

      ForInS.ResolvedVarType      := ElemType;
      ForInS.ResolvedEnumTypeName := EnumRT.Name;
      ForInS.GetEnumDecl          := GetEnumDecl;
      ForInS.MoveNextDecl         := MNDecl;
      ForInS.CurrentDecl          := CurDecl;

      ForInS.EnumVarName := '__forin_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create();
        SynthDecl.Names.Add(ForInS.EnumVarName);
        SynthDecl.TypeName    := EnumRT.Name;
        SynthDecl.ResolvedType := EnumType;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else if CollType.Kind = tyString then
    begin
      { ---- String iteration path ---- }
      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if (VarSym.TypeDesc.Kind <> tyByte) and
         (VarSym.TypeDesc.Kind <> tyInteger) then
        SemanticError(
          Format('for-in over string: loop variable ''%s'' must be Byte or Integer',
            [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal := VarSym.IsGlobal;
      if VarSym.TypeDesc.Kind = tyByte then
      begin
        ForInS.IsStringIter    := True;
        ForInS.ResolvedVarType := FTable.TypeByte;
      end
      else
      begin
        ForInS.IsCodePointIter := True;
        ForInS.ResolvedVarType := FTable.TypeInteger;
      end;

      ForInS.IdxVarName := '__idx_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create();
        SynthDecl.Names.Add(ForInS.IdxVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
      if ForInS.IsCodePointIter then
      begin
        ForInS.AdvVarName := '__adv_' + IntToStr(FForInCounter - 1);
        if FCurrentLocalBlock <> nil then
        begin
          SynthDecl := TVarDecl.Create();
          SynthDecl.Names.Add(ForInS.AdvVarName);
          SynthDecl.TypeName    := 'Integer';
          SynthDecl.ResolvedType := FTable.TypeInteger;
          SynthDecl.IsGlobal    := False;
          FCurrentLocalBlock.Decls.Add(SynthDecl);
        end;
      end;
    end
    else if CollType.Kind = tySet then
    begin
      { ---- Set iteration path ---- }
      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ElemType := TSetTypeDesc(CollType).BaseType;
      { Loop variable must be the same enum type as the set's base type,
        or any numeric type (ordinal compatibility). Reject non-ordinal types. }
      if not VarSym.TypeDesc.IsOrdinal() then
        SemanticError(
          Format('for-in over set: loop variable ''%s'' must be an ordinal type',
            [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal    := VarSym.IsGlobal;
      ForInS.IsSetIter      := True;
      ForInS.ResolvedVarType := ElemType;
      ForInS.SetBitCount    := TSetTypeDesc(CollType).BitCount;
      ForInS.SetIsJumbo     := TSetTypeDesc(CollType).IsJumbo();

      { Inject synthetic mask slot for the evaluated set value }
      ForInS.SetMaskVarName := '__setmask_' + IntToStr(FForInCounter);
      { Inject synthetic index slot (Integer) for the bit position }
      ForInS.IdxVarName := '__idx_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create();
        SynthDecl.Names.Add(ForInS.SetMaskVarName);
        if ForInS.SetIsJumbo then
        begin
          { Jumbo: the slot holds the set's ADDRESS (pointer-sized), not a mask;
            membership is tested per-ordinal via the _SetIn RTL helper. }
          SynthDecl.TypeName    := 'Int64';
          SynthDecl.ResolvedType := FTable.TypeInt64;
        end
        else if TSetTypeDesc(CollType).BitCount > 32 then
        begin
          SynthDecl.TypeName    := 'Int64';
          SynthDecl.ResolvedType := FTable.TypeInt64;
        end
        else
        begin
          SynthDecl.TypeName    := 'Integer';
          SynthDecl.ResolvedType := FTable.TypeInteger;
        end;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);

        SynthDecl := TVarDecl.Create();
        SynthDecl.Names.Add(ForInS.IdxVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else if CollType.Kind = tyDynArray then
    begin
      { ---- Dynamic array iteration path ---- }
      ElemType := TDynArrayTypeDesc(CollType).ElementType;

      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarName := VarSym.Name;
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      CheckTypesMatch(VarSym.TypeDesc, ElemType,
        'for-in loop variable', ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal    := VarSym.IsGlobal;
      ForInS.IsDynArrayIter := True;
      ForInS.ResolvedVarType := ElemType;

      { Inject synthetic index slot __idx_N (Integer) }
      ForInS.IdxVarName := '__idx_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create();
        SynthDecl.Names.Add(ForInS.IdxVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else
      SemanticError(
        'for-in collection must be a class instance, static array, dynamic array, string, or set',
        ForInS.Line, ForInS.Col);

    Inc(FLoopDepth);
    { Track the loop variable so a write to it inside the body is diagnosed
      (BUG-001): the mutation goes to a per-iteration copy and is discarded.
      Nested for-in loops push/pop, so an inner loop's variable does not mask
      an outer one. }
    FForInLoopVars.Add(ForInS.VarName);
    try
      AnalyseStmt(ForInS.Body);
    finally
      FForInLoopVars.Delete(FForInLoopVars.Count - 1);
      Dec(FLoopDepth);
    end;
  end
  else if AStmt is TWhileStmt then
  begin
    WS := TWhileStmt(AStmt);
    CondType := Self.AnalyseExprSlot(WS.Condition);
    if CondType.Kind <> tyBoolean then
      SemanticError(
        Format('while condition must be Boolean, got ''%s''', [CondType.Name]),
        AStmt.Line, AStmt.Col);
    Inc(FLoopDepth);
    try
      AnalyseStmt(WS.Body);
    finally
      Dec(FLoopDepth);
    end;
  end
  else if AStmt is TRepeatStmt then
  begin
    RS := TRepeatStmt(AStmt);
    Inc(FLoopDepth);
    try
      AnalyseCompoundBody(RS.Body);
    finally
      Dec(FLoopDepth);
    end;
    CondType := Self.AnalyseExprSlot(RS.Condition);
    if CondType.Kind <> tyBoolean then
      SemanticError(
        Format('repeat condition must be Boolean, got ''%s''', [CondType.Name]),
        AStmt.Line, AStmt.Col);
  end
  else if AStmt is TExitStmt then
  begin
    { A bare 'exit' is valid in any method or the main program block.  The
      Exit(X) shorthand assigns X to Result, so it is only valid inside a
      function (where Result is in scope).  Rewrite it into a synthesised
      'Result := X' (analysed like any assignment, so it inherits all the
      type-check / widening / ARC handling) that codegen emits before the
      exit jump. }
    if TExitStmt(AStmt).Value <> nil then
    begin
      ResultSym := FTable.Lookup('Result');
      if (ResultSym = nil) or (ResultSym.Kind <> skVariable) then
        SemanticError(
          '''Exit(Value)'' is only valid inside a function',
          AStmt.Line, AStmt.Col);
      ExitAssign      := TAssignment.Create();
      ExitAssign.Line := AStmt.Line;
      ExitAssign.Col  := AStmt.Col;
      ExitAssign.Name := 'Result';
      ExitAssign.Expr := TExitStmt(AStmt).Value;
      TExitStmt(AStmt).Value := nil;   { ownership moves into the assignment }
      AnalyseStmt(ExitAssign);          { fills ResolvedLhsType + checks types }
      TExitStmt(AStmt).ResultAssign := ExitAssign;
    end;
  end
  else if AStmt is TBreakStmt then
  begin
    if FLoopDepth = 0 then
      SemanticError('''break'' is not inside a loop', AStmt.Line, AStmt.Col);
  end
  else if AStmt is TContinueStmt then
  begin
    if FLoopDepth = 0 then
      SemanticError('''continue'' is not inside a loop', AStmt.Line, AStmt.Col);
  end
  else if AStmt is TIfStmt then
  begin
    IfS      := TIfStmt(AStmt);
    CondType := Self.AnalyseExprSlot(IfS.Condition);
    if CondType.Kind <> tyBoolean then
      SemanticError(
        Format('if condition must be Boolean, got ''%s''', [CondType.Name]),
        IfS.Line, IfS.Col);
    AnalyseStmt(IfS.ThenStmt);
    if IfS.ElseStmt <> nil then
      AnalyseStmt(IfS.ElseStmt);
  end
  else if AStmt is TCompoundStmt then
  begin
    { Each begin..end block is a lexical scope for block-scoped 'var'
      declarations (Phase 4): names declared inside are popped at the end,
      and the block is a fresh env-alloc-site frame. }
    CmpS := TCompoundStmt(AStmt);
    SavedBlockSite := FCurrentBlockFirstSite;
    FCurrentBlockFirstSite := nil;
    FTable.PushScope();
    try
      for I := 0 to CmpS.Stmts.Count - 1 do
        AnalyseStmt(TASTStmt(CmpS.Stmts.Items[I]));
    finally
      FTable.PopScope();
      FCurrentBlockFirstSite := SavedBlockSite;
    end;
  end
  else if AStmt is TVarDeclStmt then
    AnalyseVarDeclStmt(TVarDeclStmt(AStmt))
  else if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    AnalyseCompoundBody(TFS.TryBody);
    AnalyseCompoundBody(TFS.FinallyBody);
  end
  else if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    AnalyseCompoundBody(TES.TryBody);
    if TES.Handlers.Count > 0 then
    begin
      for I := 0 to TES.Handlers.Count - 1 do
      begin
        H := TExceptHandlerClause(TES.Handlers[I]);
        CondType := FindTypeOrInstantiate(H.TypeName);
        if CondType = nil then
          SemanticError(
            Format('Unknown exception type ''%s''', [H.TypeName]),
            AStmt.Line, AStmt.Col);
        if CondType.Kind <> tyClass then
          SemanticError(
            Format('Exception handler type must be a class, got ''%s''', [H.TypeName]),
            AStmt.Line, AStmt.Col);
        if H.VarName <> '' then
        begin
          { Inject a synthetic local so EmitVarAllocs allocates a stack slot.
            One slot per DISTINCT name: multiple `on E:` clauses (and nested
            try-excepts) share it — injecting per clause double-allocated the
            slot and emitted one epilogue release per duplicate, driving the
            bound exception's refcount negative. }
          if FCurrentLocalBlock <> nil then
          begin
            DupLocal := False;
            for K := 0 to FCurrentLocalBlock.Decls.Count - 1 do
              if TObject(FCurrentLocalBlock.Decls.Items[K]) is TVarDecl then
                for L := 0 to TVarDecl(FCurrentLocalBlock.Decls.Items[K]).Names.Count - 1 do
                  if SameText(TVarDecl(FCurrentLocalBlock.Decls.Items[K]).Names.Strings[L],
                              H.VarName) then
                    DupLocal := True;
            if not DupLocal then
            begin
              SynthDecl := TVarDecl.Create();
              SynthDecl.Names.Add(H.VarName);
              SynthDecl.TypeName    := H.TypeName;
              SynthDecl.ResolvedType := CondType;
              SynthDecl.IsGlobal    := False;
              FCurrentLocalBlock.Decls.Add(SynthDecl);
            end;
          end;
          FTable.PushScope();
          try
            VarSym := TSymbol.Create(H.VarName, skVariable, CondType);
            if not FTable.Define(VarSym) then
              VarSym.Free();
            AnalyseCompoundBody(H.Body);
          finally
            FTable.PopScope();
          end;
        end
        else
          AnalyseCompoundBody(H.Body);
      end;
      if TES.ElseBody <> nil then
        AnalyseCompoundBody(TES.ElseBody);
    end
    else
      AnalyseCompoundBody(TES.ExceptBody);
  end
  else if AStmt is TRaiseStmt then
  begin
    RaiseS := TRaiseStmt(AStmt);
    if RaiseS.Expr <> nil then
    begin
      CondType := Self.AnalyseExprSlot(RaiseS.Expr);
      if CondType.Kind <> tyClass then
        SemanticError(
          Format('raise expression must be a class instance, got ''%s''',
            [CondType.Name]),
          AStmt.Line, AStmt.Col);
    end;
  end
  else if AStmt is TFieldAssignment then
    AnalyseFieldAssignment(TFieldAssignment(AStmt))
  else if AStmt is TAssignment then
    AnalyseAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    AnalyseMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TInheritedCallStmt then
    AnalyseInheritedCall(TInheritedCallStmt(AStmt))
  else if AStmt is TPointerWriteStmt then
    AnalysePointerWriteStmt(TPointerWriteStmt(AStmt))
  else if AStmt is TStaticSubscriptAssign then
    AnalyseStaticSubscriptAssign(TStaticSubscriptAssign(AStmt))
  else if AStmt is TProcCall then
    AnalyseProcCall(TProcCall(AStmt))
  else if AStmt is TCaseStmt then
    AnalyseCaseStmt(TCaseStmt(AStmt));
end;

function TSemanticAnalyser.ResolveIntfMethodReturn(AIntf: TInterfaceTypeDesc;
  const AMethName: string): TTypeDesc;
var
  RetName: string;
begin
  Result := nil;
  RetName := AIntf.MethodReturnTypeName(AIntf.MethodIndex(AMethName));
  if RetName <> '' then
    Result := FindTypeOrInstantiate(RetName);
end;

procedure TSemanticAnalyser.AnalyseMethodCall(ACall: TMethodCallStmt);
var
  ObjSym:  TSymbol;
  RT:      TRecordTypeDesc;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  I:       Integer;
  ObjType: TTypeDesc;
  FldInfo: TFieldInfo;
begin
  { Call on a receiver expression: AProg.UsedUnits.Add(UName) }
  if ACall.ObjExpr <> nil then
  begin
    ObjType := Self.AnalyseExprSlot(ACall.ObjExpr);
    if not (ObjType.Kind in [tyClass, tyInterface]) then
      SemanticError(
        Format('Receiver of ''.%s'' must be a class or interface', [ACall.Name]),
        ACall.Line, ACall.Col);
    { Interface-typed receiver expression (e.g. a non-Self interface field:
      H.S.Note();) — dispatch through the itab, mirroring the implicit-Self
      interface path below.  Codegen resolves obj/itab from the receiver
      expression's fat pointer. }
    if ObjType.Kind = tyInterface then
    begin
      if not TInterfaceTypeDesc(ObjType).HasMethod(ACall.Name) then
        SemanticError(
          Format('Interface ''%s'' has no method ''%s''',
            [ObjType.Name, ACall.Name]),
          ACall.Line, ACall.Col);
      for I := 0 to ACall.Args.Count - 1 do
        Self.AnalyseListSlot(ACall.Args, I);
      ValidateIntfMethodVarArgs(ACall.Args, TInterfaceTypeDesc(ObjType),
        ACall.Name, ACall.Line, ACall.Col);
      ACall.ResolvedClassType := ObjType;
      ACall.ResolvedMethod    := nil;
      ACall.ResolvedReturnTypeDesc :=
        ResolveIntfMethodReturn(TInterfaceTypeDesc(ObjType), ACall.Name);
      Exit;
    end;
    RT := TRecordTypeDesc(ObjType);
    if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) and
       (FindMethodDecl(RT.Name, 'Free') = nil) then
    begin
      ACall.ResolvedClassType := RT;
      ACall.ResolvedMethod    := nil;
      Exit;
    end;
    HintBareEnumMethodArgs(RT.Name, ACall.Name, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
      Self.AnalyseArgSlot(ACall.Args, I);
    MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
      ACall.Line, ACall.Col);
    ResolveDeferredArrowArgs(ACall.Args, MDecl);
    if MDecl = nil then
    begin
      FldInfo := RT.FindField(ACall.Name);
      if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
         (FldInfo.TypeDesc.Kind = tyProcedural) then
      begin
        ACall.IsProcFieldCall   := True;
        ACall.ProcFieldInfo     := FldInfo;
        ACall.ResolvedProcType  := FldInfo.TypeDesc;
        ACall.ResolvedClassType := RT;
        ACall.ResolvedMethod    := nil;
        Exit;
      end;
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
        ACall.Line, ACall.Col);
    end;
    { Set-literal args: see BUG-20260722-native-set-literal-arg. }
    RetypeSetLiteralArgs(ACall.Args, MDecl);
    AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
    ValidateMethodVarArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := MDecl;
    if (MDecl.ResolvedReturnType <> nil) and
       (MDecl.ResolvedReturnType.Kind = tyRecord) then
      ACall.ResolvedReturnTypeDesc := MDecl.ResolvedReturnType;
    Exit;
  end;

  ObjSym := FTable.Lookup(ACall.ObjectName);
  { TypeName.StaticMethod() — a static (type-level) method called through the
    CLASS or RECORD name in statement position.  Resolve the method on the
    type; it must be declared static.  Lowered with NO Self.  (Records took
    this path late: TUuid.Parse(...) as a discarded statement used to fail
    with "'TUuid' is not a variable" — expression position already worked.) }
  if (ObjSym <> nil) and (ObjSym.Kind = skType) and (ObjSym.TypeDesc <> nil) and
     (ObjSym.TypeDesc.Kind in [tyClass, tyRecord]) then
  begin
    RT := TRecordTypeDesc(ObjSym.TypeDesc);
    for I := 0 to ACall.Args.Count - 1 do
      Self.AnalyseArgSlot(ACall.Args, I);
    MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
      ACall.Line, ACall.Col);
    ResolveDeferredArrowArgs(ACall.Args, MDecl);
    if MDecl = nil then
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
        ACall.Line, ACall.Col);
    if not MDecl.IsStatic then
      SemanticError(
        Format('''%s.%s'' is not a static method — call it on an instance',
          [RT.Name, ACall.Name]),
        ACall.Line, ACall.Col);
    { Set-literal args: see BUG-20260722-native-set-literal-arg. }
    RetypeSetLiteralArgs(ACall.Args, MDecl);
    AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
    ValidateMethodVarArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
    EnforceMethodVisible(MDecl, ACall.Line, ACall.Col);
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := MDecl;
    ACall.IsStaticCall      := True;
    if (MDecl.ResolvedReturnType <> nil) and
       (MDecl.ResolvedReturnType.Kind = tyRecord) then
      ACall.ResolvedReturnTypeDesc := MDecl.ResolvedReturnType;
    Exit;
  end;
  { Inside a method, class fields shadow same-named globals.  Try the
    implicit Self.Field path when there is no match (ObjSym=nil) OR when
    the only match is a global variable that a class field should shadow. }
  if (FCurrentClass <> nil) and
     ((ObjSym = nil) or ObjSym.IsGlobal) then
  begin
    ACall.ImplicitBaseInfo :=
      FCurrentClass.FindField(ACall.ObjectName);
    if (ACall.ImplicitBaseInfo <> nil) and
       (ACall.ImplicitBaseInfo.TypeDesc.Kind in [tyClass, tyInterface, tyRecord]) then
    begin
      ACall.IsImplicitSelf := True;
      { Interface field: dispatch via vtable, same semantics as the
        non-implicit path at the "ObjSym.TypeDesc.Kind = tyInterface" block. }
      if ACall.ImplicitBaseInfo.TypeDesc.Kind = tyInterface then
      begin
        if not TInterfaceTypeDesc(ACall.ImplicitBaseInfo.TypeDesc).HasMethod(ACall.Name) then
          SemanticError(
            Format('Interface ''%s'' has no method ''%s''',
              [ACall.ImplicitBaseInfo.TypeDesc.Name, ACall.Name]),
            ACall.Line, ACall.Col);
        for I := 0 to ACall.Args.Count - 1 do
          Self.AnalyseListSlot(ACall.Args, I);
        ValidateIntfMethodVarArgs(ACall.Args,
          TInterfaceTypeDesc(ACall.ImplicitBaseInfo.TypeDesc),
          ACall.Name, ACall.Line, ACall.Col);
        ACall.ResolvedClassType := ACall.ImplicitBaseInfo.TypeDesc;
        ACall.ResolvedMethod    := nil;
        ACall.ResolvedReturnTypeDesc := ResolveIntfMethodReturn(
          TInterfaceTypeDesc(ACall.ImplicitBaseInfo.TypeDesc), ACall.Name);
        Exit;
      end;
      RT := TRecordTypeDesc(ACall.ImplicitBaseInfo.TypeDesc);
      if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) and
         (FindMethodDecl(RT.Name, 'Free') = nil) then
      begin
        ACall.ResolvedClassType := RT;
        ACall.ResolvedMethod    := nil;
        Exit;
      end;
      HintBareEnumMethodArgs(RT.Name, ACall.Name, ACall.Args);
      for I := 0 to ACall.Args.Count - 1 do
        Self.AnalyseArgSlot(ACall.Args, I);
      MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
        ACall.Line, ACall.Col);
      ResolveDeferredArrowArgs(ACall.Args, MDecl);
      if MDecl = nil then
        SemanticError(
          Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
          ACall.Line, ACall.Col);
      { Type bracket set literals against the resolved params — the args were
        analysed unhinted for overload resolution, leaving open-array types
        native codegen rejects (BUG-20260722-native-set-literal-arg). }
      RetypeSetLiteralArgs(ACall.Args, MDecl);
      AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
      ValidateMethodVarArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
      ACall.ResolvedClassType := RT;
      ACall.ResolvedMethod    := MDecl;
      if (MDecl.ResolvedReturnType <> nil) and
         (MDecl.ResolvedReturnType.Kind = tyRecord) then
        ACall.ResolvedReturnTypeDesc := MDecl.ResolvedReturnType;
      Exit;
    end;
  end;
  if ObjSym = nil then
  begin
    SemanticError(
      Format('Undeclared variable ''%s''', [ACall.ObjectName]),
      ACall.Line, ACall.Col);
  end;
  ACall.ObjectName := ObjSym.Name;  { normalise to declared casing }
  if not (ObjSym.Kind in [skVariable, skParameter, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [ACall.ObjectName]),
      ACall.Line, ACall.Col);
  { Metaclass-var constructor dispatch in statement position. }
  if (ObjSym.TypeDesc.Kind = tyMetaClass) and
     (SameText(ACall.Name, 'Create') or (StrPos('Create', ACall.Name) = 0)) then
  begin
    RT := TRecordTypeDesc(TMetaClassTypeDesc(ObjSym.TypeDesc).BaseClass);
    HintBareEnumMethodArgs(RT.Name, ACall.Name, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
      Self.AnalyseArgSlot(ACall.Args, I);
    MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
      ACall.Line, ACall.Col);
    ResolveDeferredArrowArgs(ACall.Args, MDecl);
    if MDecl = nil then
      MDecl := FindMethodDecl(RT.Name, ACall.Name);
    ValidateMethodVarArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
    ACall.ResolvedClassType   := RT;
    ACall.ResolvedMethod      := MDecl;
    ACall.IsConstructorCall   := True;
    ACall.IsMetaclassDispatch := True;
    ACall.IsGlobal            := ObjSym.IsGlobal;
    ACall.IsVarParam          := (ObjSym.Kind = skVarParameter);
    Exit;
  end;

  if not (ObjSym.TypeDesc.Kind in [tyClass, tyInterface, tyRecord]) then
    SemanticError(
      Format('''%s'' is not a class, interface, or record variable', [ACall.ObjectName]),
      ACall.Line, ACall.Col);

  { Interface method call: look up method in interface type descriptor }
  if ObjSym.TypeDesc.Kind = tyInterface then
  begin
    if not TInterfaceTypeDesc(ObjSym.TypeDesc).HasMethod(ACall.Name) then
      SemanticError(
        Format('Interface ''%s'' has no method ''%s''',
          [ObjSym.TypeDesc.Name, ACall.Name]),
        ACall.Line, ACall.Col);
    { Resolve arg expressions so codegen has ResolvedType on every node.
      We don't have concrete param signatures at interface-dispatch sites
      (Phase 3 limitation), so we can't validate types — but expressions
      still need to be analysed so e.g. `@Buf[0]` annotates the
      TStringSubscriptExpr's StrExpr.ResolvedType.  Without this,
      EmitAddrOfExpr crashes on a nil ResolvedType when emitting the
      argument. }
    for I := 0 to ACall.Args.Count - 1 do
      Self.AnalyseListSlot(ACall.Args, I);
    ValidateIntfMethodVarArgs(ACall.Args, TInterfaceTypeDesc(ObjSym.TypeDesc),
      ACall.Name, ACall.Line, ACall.Col);
    ACall.ResolvedClassType := ObjSym.TypeDesc;
    ACall.ResolvedMethod    := nil;  { nil = interface dispatch, not class dispatch }
    ACall.IsGlobal          := ObjSym.IsGlobal;
    ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
    ACall.ResolvedReturnTypeDesc := ResolveIntfMethodReturn(
      TInterfaceTypeDesc(ObjSym.TypeDesc), ACall.Name);
    Exit;
  end;

  RT := TRecordTypeDesc(ObjSym.TypeDesc);
  { Free is a built-in: if Self <> nil then free(Self). No user-defined method needed. }
  if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) and
     (FindMethodDecl(RT.Name, 'Free') = nil) then
  begin
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := nil;
    ACall.IsGlobal          := ObjSym.IsGlobal;
    ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
    Exit;
  end;

  HintBareEnumMethodArgs(RT.Name, ACall.Name, ACall.Args);
  for I := 0 to ACall.Args.Count - 1 do
    Self.AnalyseArgSlot(ACall.Args, I);

  { Direct invocation of a procedural-typed field (e.g. an event-handler
    field): F.Handler; or F.Handler();.  Resolve this before reporting a
    missing method so the call dispatches through the (Code, Data) pair
    stored in the field, mirroring the indirect-call path used for a
    procedural-typed local variable. }
  FldInfo := RT.FindField(ACall.Name);
  if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
     (FldInfo.TypeDesc.Kind = tyProcedural) and
     (FindMethodDecl(RT.Name, ACall.Name) = nil) then
  begin
    ACall.IsProcFieldCall   := True;
    ACall.ProcFieldInfo     := FldInfo;
    ACall.ResolvedProcType  := FldInfo.TypeDesc;
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := nil;
    ACall.IsGlobal          := ObjSym.IsGlobal;
    ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
    Exit;
  end;

  MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
    ACall.Line, ACall.Col);
  if MDecl = nil then
    SemanticError(
      Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
      ACall.Line, ACall.Col);
  ResolveDeferredArrowArgs(ACall.Args, MDecl);

  { Type bracket set literals against the resolved params — the args were
    analysed unhinted for overload resolution, leaving open-array types
    native codegen rejects (BUG-20260722-native-set-literal-arg). }
  RetypeSetLiteralArgs(ACall.Args, MDecl);
  AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
  ValidateMethodVarArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
  EnforceMethodVisible(MDecl, ACall.Line, ACall.Col);
  ACall.ResolvedClassType := RT;
  ACall.ResolvedMethod    := MDecl;
  ACall.IsGlobal          := ObjSym.IsGlobal;
  ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
  if (MDecl.ResolvedReturnType <> nil) and
     (MDecl.ResolvedReturnType.Kind = tyRecord) then
    ACall.ResolvedReturnTypeDesc := MDecl.ResolvedReturnType;
end;

{ If AExpr is a diamond constructor call (RecordName ends with '<>'), replace
  the sentinel with the full concrete type name from ALhsType.  This implements
  the diamond operator: TFoo<> infers all type arguments from the LHS. }
procedure ResolveDiamond(AExpr: TASTExpr; ALhsType: TTypeDesc);
var
  TypeName: string;
  BaseName: string;
  BrPos: Integer;
begin
  if ALhsType = nil then Exit;
  if AExpr is TFieldAccessExpr then
    TypeName := TFieldAccessExpr(AExpr).RecordName
  else if AExpr is TMethodCallExpr then
    TypeName := TMethodCallExpr(AExpr).ObjectName
  else
    Exit;
  if (Length(TypeName) < 3) or
     (StrCopyTail(TypeName, Length(TypeName) - 2) <> '<>') then Exit;
  BaseName := StrHead(TypeName, Length(TypeName) - 2);
  BrPos := StrPos('<', ALhsType.Name);
  if (ALhsType.Kind = tyClass) and
     (BrPos >= 0) and
     SameText(StrHead(ALhsType.Name, BrPos), BaseName) then
  begin
    if AExpr is TFieldAccessExpr then
      TFieldAccessExpr(AExpr).RecordName := ALhsType.Name
    else
      TMethodCallExpr(AExpr).ObjectName := ALhsType.Name;
  end;
end;

procedure TSemanticAnalyser.AnalyseAssignment(AAssign: TAssignment);
var
  VarSym:  TSymbol;
  FldInfo: TFieldInfo;
  ExprType: TTypeDesc;
begin
  VarSym := FTable.Lookup(AAssign.Name);
  { BUG-001: assigning to a for-in loop variable writes a per-iteration COPY
    that never reaches the collection element — almost always a mistake.
    Standard Pascal (FPC/Delphi) treats for-in as read-only, so the behaviour
    is correct; warn so the discarded write is not silent.  The name is only in
    FForInLoopVars while inside that loop's body, and it holds the resolved
    loop-variable name, so a match here IS the loop variable (a program-level
    for-in variable is still a discarded write). }
  if (FForInLoopVars.IndexOf(AAssign.Name) >= 0) and
     (VarSym <> nil) and (VarSym.Kind = skVariable) then
    SemanticWarning(
      Format('assignment to for-in loop variable ''%s'' is discarded (the loop '
        + 'variable is a per-iteration copy) — use an indexed ''for'' loop to '
        + 'mutate the collection', [AAssign.Name]),
      AAssign.Line, AAssign.Col);
  { Inside a method, class fields shadow same-named globals.  Mirror the
    priority of the expression read path (see TIdentExpr handling): try the
    class field when there is no local/param match (VarSym=nil) OR when the
    only match found is a global variable that the field should shadow. }
  if (FCurrentClass <> nil) and
     ((VarSym = nil) or VarSym.IsGlobal) then
  begin
    FldInfo := FCurrentClass.FindField(AAssign.Name);
    if FldInfo <> nil then
    begin
      AAssign.ImplicitSelfField := FldInfo;
      AAssign.ResolvedLhsType   := FldInfo.TypeDesc;
      InferArrowFromTarget(AAssign.Expr, FldInfo.TypeDesc);
      ResolveDiamond(AAssign.Expr, FldInfo.TypeDesc);
      { Set-literal RHS into a tySet field via the bare (implicit-Self) form:
        analyse with the field's set type as context, exactly as the plain
        variable and qualified 'obj.Field' paths do.  Without this an empty
        '[]' has no element type of its own and stays untyped, so the
        CheckTypesMatch below reports "Expression has no value type" for the
        valid 'Field := []'.  Affects every set type, not just jumbo ones. }
      if (FldInfo.TypeDesc <> nil) and (FldInfo.TypeDesc.Kind = tySet) and
         (AAssign.Expr is TArrayLiteralExpr) then
      begin
        AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
          TSetTypeDesc(FldInfo.TypeDesc));
        Exit;
      end;
      { Bare enum member on the RHS resolves against the field's type. }
      if TryResolveBareEnumIdent(AAssign.Expr, FldInfo.TypeDesc) then
        ExprType := AAssign.Expr.ResolvedType
      else
        ExprType := Self.AnalyseExprSlot(AAssign.Expr);
      CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
      Exit;
    end;
  end;
  if VarSym = nil then
  begin
    SemanticError(
      Format('Undeclared variable ''%s''', [AAssign.Name]),
      AAssign.Line, AAssign.Col);
  end;
  if not (VarSym.Kind in [skVariable, skVarParameter, skParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.Name]),
      AAssign.Line, AAssign.Col);

  AAssign.Name            := VarSym.Name;  { normalise to declared casing }
  { Static (class-level) var: the assignment target is the single shared global
    emitted under the mangled GlobalEmitName, so the LHS name must be that label
    (matches the read path in AnalyseIdentExpr).  Enforce member visibility on
    the bare form too: a strict-private static var is reachable only from its
    declaring type's own methods, so writing it from another type, or from the
    unit initialization/finalization section (FCurrentClass = nil), is rejected. }
  if VarSym.IsClassVar and (VarSym.GlobalEmitName <> '') then
  begin
    AssertStaticVarVisible(VarSym.Visibility, VarSym.OwningUnit,
                           VarSym.OwnerTypeName, VarSym.Name,
                         AAssign.Line, AAssign.Col);
    AAssign.Name := VarSym.GlobalEmitName;
  end;
  AAssign.IsVarParam      := (VarSym.Kind = skVarParameter);
  AAssign.ResolvedLhsType := VarSym.TypeDesc;
  AAssign.IsWeakLhs       := VarSym.IsWeak;
  AAssign.IsGlobal        := VarSym.IsGlobal;
  AAssign.IsThreadVar     := VarSym.IsThreadVar;
  { Owning unit of a module-scope global target, so the store address is
    mangled with the unit that won resolution — keeps a bare write to a
    cross-unit last-wins var hitting the same slot a bare read sees.  A static
    class/record var's name is its already fully-mangled GlobalEmitName, so flag
    it pre-mangled to keep codegen's module-var prefixing from double-applying. }
  if VarSym.IsGlobal and (VarSym.Kind = skVariable) then
  begin
    if VarSym.IsClassVar then
      AAssign.ResolvedOwnerUnit := PreMangledGlobalOwner
    else
      AAssign.ResolvedOwnerUnit := VarSym.OwningUnit;
  end;

  ResolveDiamond(AAssign.Expr, VarSym.TypeDesc);
  { Phase 9a: a '->' lambda RHS takes its parameter/return types from the
    LHS variable's 'reference to' type. }
  InferArrowFromTarget(AAssign.Expr, VarSym.TypeDesc);

  { '@Routine' assigned to a 'reference to' variable coerces via a
    forwarding adapter literal. }
  if (VarSym.TypeDesc <> nil) and (VarSym.TypeDesc.Kind = tyProcedural) and
     TProceduralTypeDesc(VarSym.TypeDesc).IsReference then
    CoerceRoutineToClosure(AAssign);

  { Set-literal assignment: [elem, ...] on RHS when LHS is a set type }
  if (VarSym.TypeDesc.Kind = tySet) and (AAssign.Expr is TArrayLiteralExpr) then
  begin
    AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
      TSetTypeDesc(VarSym.TypeDesc));
    Exit;
  end;
  { An empty bracket literal [] assigned to a non-set LHS has no inferable
    type (it deferred to a nil ResolvedType); only a set target gives it
    meaning.  Reject cleanly rather than passing nil to CheckTypesMatch. }
  if (AAssign.Expr is TArrayLiteralExpr) and
     (TArrayLiteralExpr(AAssign.Expr).Elements.Count = 0) then
    SemanticError(Format(
      'Empty set literal ''[]'' cannot be assigned to non-set variable ''%s'' of type ''%s''',
      [AAssign.Name, VarSym.TypeDesc.Name]), AAssign.Line, AAssign.Col);

  { Bare enum member on the RHS resolves against the variable's type, so a
    member name shared by several enums picks the one the LHS expects. }
  if TryResolveBareEnumIdent(AAssign.Expr, VarSym.TypeDesc) then
    ExprType := AAssign.Expr.ResolvedType
  else
    ExprType := Self.AnalyseExprSlot(AAssign.Expr);
  { Method-pointer → 'reference to' coercion (Phase 3): an 'of object'
    value of matching callable signature becomes a closure whose Env is
    the strong-retained receiver (uniform closure ABI: code(env, args) is
    the method call itself).  Accepted for @Obj.M and method-pointer
    variables alike; codegen keys off the RHS shape/type. }
  if (VarSym.TypeDesc <> nil) and (VarSym.TypeDesc.Kind = tyProcedural) and
     TProceduralTypeDesc(VarSym.TypeDesc).IsReference and
     (ExprType <> nil) and (ExprType.Kind = tyProcedural) and
     TProceduralTypeDesc(ExprType).IsMethodPtr and
     TProceduralTypeDesc(VarSym.TypeDesc).SignatureMatches(
       TProceduralTypeDesc(ExprType)) then
    Exit;
  CheckTypesMatch(VarSym.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
end;

procedure TSemanticAnalyser.AnalyseInheritedCall(ACall: TInheritedCallStmt);
var
  ParentType: TRecordTypeDesc;
  MDecl:      TMethodDecl;
  ArgType:    TTypeDesc;
  Par:        TMethodParam;
  I:          Integer;
begin
  if FCurrentClass = nil then
    SemanticError('''inherited'' used outside a method body',
      ACall.Line, ACall.Col);

  if FCurrentClass.Parent = nil then
  begin
    { No explicit parent — implicit TObject. inherited Create/Destroy are no-ops. }
    if SameText(ACall.Name, 'Create') or SameText(ACall.Name, 'Destroy') then
    begin
      ACall.ResolvedParentType := nil;
      ACall.ResolvedMethod     := nil;
      Exit;
    end;
    SemanticError(
      Format('Class ''%s'' has no parent; ''inherited'' is not valid',
        [FCurrentClass.Name]),
      ACall.Line, ACall.Col);
  end;

  ParentType := FCurrentClass.Parent;

  { TObject is the builtin root class — inherited Create/Destroy are no-ops }
  if SameText(ParentType.Name, 'TObject') then
  begin
    ACall.ResolvedParentType := ParentType;
    ACall.ResolvedMethod     := nil;
    Exit;
  end;

  MDecl := FindMethodDecl(ParentType.Name, ACall.Name);
  if MDecl = nil then
  begin
    { Constructor/destructor chaining: if the parent doesn't explicitly declare
      Create or Destroy, the call chains up to TObject (a no-op in ARC). }
    if SameText(ACall.Name, 'Create') or SameText(ACall.Name, 'Destroy') then
    begin
      ACall.ResolvedParentType := ParentType;
      ACall.ResolvedMethod     := nil;
      Exit;
    end;
    SemanticError(
      Format('Parent class ''%s'' has no method ''%s''',
        [ParentType.Name, ACall.Name]),
      ACall.Line, ACall.Col);
  end;

  if ACall.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d',
        [ParentType.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
      ACall.Line, ACall.Col);

  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MDecl.Params.Items[I]);
    { Bracket set literal: type against the param's set type — see the
      method-call arms (BUG-20260722-native-set-literal-arg). }
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tySet) and
       (TASTExpr(ACall.Args.Items[I]) is TArrayLiteralExpr) then
      ArgType := AnalyseSetLiteralExpr(
        TArrayLiteralExpr(ACall.Args.Items[I]),
        TSetTypeDesc(Par.ResolvedType))
    else
      ArgType := Self.AnalyseListSlot(ACall.Args, I);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of inherited ''%s''', [I + 1, ACall.Name]),
      ACall.Line, ACall.Col);
  end;
  ValidateMethodVarArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);

  ACall.ResolvedParentType := ParentType;
  ACall.ResolvedMethod     := MDecl;
end;

function TSemanticAnalyser.IsVarArgLValue(AExpr: TASTExpr): Boolean;
var
  BaseKind: TTypeKind;
begin
  if (AExpr is TIdentExpr) or (AExpr is TFieldAccessExpr) or
     (AExpr is TDerefExpr) then
    Exit(True);
  { Array element a[i] (a TStringSubscriptExpr over an array base) is a
    valid var/out actual.  String / PChar subscripts yield a char by value,
    not a standalone addressable element, so they are not accepted. }
  if AExpr is TStringSubscriptExpr then
  begin
    if (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType = nil) then
      Exit(False);
    BaseKind := TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind;
    Exit(BaseKind in [tyStaticArray, tyDynArray, tyOpenArray]);
  end;
  Result := False;
end;

procedure TSemanticAnalyser.WarnIfVarArgIsForInLoopVar(AExpr: TASTExpr);
var
  Sym: TSymbol;
begin
  { BUG-001, by-ref arm: passing a for-in loop variable to a var/out parameter
    (or a mutating built-in such as Inc/SetLength) writes the per-iteration
    copy, so the mutation never reaches the collection element.  Mirrors the
    direct-assignment diagnostic in AnalyseAssignment.  Only the bare-ident
    form is diagnosed here; a field of a record loop variable passed by ref
    is covered by neither arm yet (documented follow-up). }
  if not (AExpr is TIdentExpr) then
    Exit;
  if FForInLoopVars.IndexOf(TIdentExpr(AExpr).Name) < 0 then
    Exit;
  Sym := FTable.Lookup(TIdentExpr(AExpr).Name);
  if (Sym <> nil) and (Sym.Kind = skVariable) then
    SemanticWarning(
      Format('by-ref mutation of for-in loop variable ''%s'' is discarded '
        + '(the loop variable is a per-iteration copy) — use an indexed '
        + '''for'' loop to mutate the collection', [TIdentExpr(AExpr).Name]),
      AExpr.Line, AExpr.Col);
end;

procedure TSemanticAnalyser.ValidateMethodVarArgs(AArgs: TObjectList;
  AMDecl: TMethodDecl; const AName: string; ALine, ACol: Integer);
var
  I: Integer;
  Par: TMethodParam;
begin
  if AMDecl = nil then
    Exit;
  { Only validate the explicit parameters that received an actual — variadic
    defaults were appended already, but an omitted trailing param has no arg. }
  for I := 0 to AArgs.Count - 1 do
  begin
    if I >= AMDecl.Params.Count then
      Break;
    Par := TMethodParam(AMDecl.Params.Items[I]);
    if Par.IsVarParam then
    begin
      if not IsVarArgLValue(TASTExpr(AArgs.Items[I])) then
        SemanticError(
          Format('var argument %d of ''%s'' must be a variable', [I + 1, AName]),
          ALine, ACol);
      WarnIfVarArgIsForInLoopVar(TASTExpr(AArgs.Items[I]));
    end;
  end;
end;

procedure TSemanticAnalyser.ValidateIntfMethodVarArgs(AArgs: TObjectList;
  AIntf: TInterfaceTypeDesc; const AName: string; ALine, ACol: Integer);
var
  I: Integer;
  MIdx: Integer;
begin
  if AIntf = nil then
    Exit;
  MIdx := AIntf.MethodIndex(AName);
  if MIdx < 0 then
    Exit;
  for I := 0 to AArgs.Count - 1 do
  begin
    if AIntf.MethodParamIsVar(MIdx, I) then
    begin
      if not IsVarArgLValue(TASTExpr(AArgs.Items[I])) then
        SemanticError(
          Format('var argument %d of ''%s'' must be a variable', [I + 1, AName]),
          ALine, ACol);
      WarnIfVarArgIsForInLoopVar(TASTExpr(AArgs.Items[I]));
    end;
  end;
end;

function TSemanticAnalyser.AnalyseInheritedCallExpr(
  ACall: TInheritedCallExpr): TTypeDesc;
var
  ParentType: TRecordTypeDesc;
  MDecl:      TMethodDecl;
  ArgType:    TTypeDesc;
  Par:        TMethodParam;
  I:          Integer;
begin
  { Mirrors AnalyseInheritedCall (the statement form) but the call is used as
    a VALUE, so the parent method must be a function (non-void return) and the
    result type becomes this expression's ResolvedType. }
  if FCurrentClass = nil then
    SemanticError('''inherited'' used outside a method body',
      ACall.Line, ACall.Col);
  if FCurrentClass.Parent = nil then
    SemanticError(
      Format('Class ''%s'' has no parent; ''inherited'' is not valid',
        [FCurrentClass.Name]),
      ACall.Line, ACall.Col);

  ParentType := FCurrentClass.Parent;
  MDecl := FindMethodDecl(ParentType.Name, ACall.Name);
  if MDecl = nil then
    SemanticError(
      Format('Parent class ''%s'' has no method ''%s''',
        [ParentType.Name, ACall.Name]),
      ACall.Line, ACall.Col);

  if (MDecl.ResolvedReturnType = nil) or
     (MDecl.ResolvedReturnType.Kind = tyVoid) then
    SemanticError(
      Format('inherited ''%s'' is a procedure and has no value',
        [ACall.Name]),
      ACall.Line, ACall.Col);

  if ACall.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d',
        [ParentType.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
      ACall.Line, ACall.Col);

  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MDecl.Params.Items[I]);
    { Bracket set literal: type against the param's set type — see the
      method-call arms (BUG-20260722-native-set-literal-arg). }
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tySet) and
       (TASTExpr(ACall.Args.Items[I]) is TArrayLiteralExpr) then
      ArgType := AnalyseSetLiteralExpr(
        TArrayLiteralExpr(ACall.Args.Items[I]),
        TSetTypeDesc(Par.ResolvedType))
    else
      ArgType := Self.AnalyseListSlot(ACall.Args, I);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of inherited ''%s''', [I + 1, ACall.Name]),
      ACall.Line, ACall.Col);
  end;
  ValidateMethodVarArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);

  ACall.ResolvedParentType := ParentType;
  ACall.ResolvedMethod     := MDecl;
  ACall.ResolvedType       := MDecl.ResolvedReturnType;
  Result                   := MDecl.ResolvedReturnType;
end;

{ Effective float type of a float-builtin argument: float types pass
  through unchanged; integer-family arguments implicitly widen to Double
  (FPC/Delphi semantics, consistent with Blaise's int→float assignment
  rule).  Anything else is an error. }
function TSemanticAnalyser.FloatBuiltinArgType(const AName: string;
  AArgType: TTypeDesc; ALine, ACol: Integer): TTypeDesc;
begin
  if AArgType.IsFloat() then
    Exit(AArgType);
  if AArgType.Kind in [tyInteger, tyInt64, tyUInt32, tyUInt64,
                       tySmallInt, tyWord, tyByte] then
    Exit(FTable.TypeDouble);
  SemanticError(
    Format('%s requires a numeric argument, got ''%s''',
      [AName, AArgType.Name]),
    ALine, ACol);
  Result := nil;
end;

{ Element write into an array-typed FIELD: Receiver.Field[Index] := Value.
  The parser stores the subscript in PropIndexExpr (the same slot used for
  indexed property writes); when Field resolves to a real array field the
  subscript is an ELEMENT index — the RHS must match the element type, not
  the array type.  Returns False when there is no subscript to interpret;
  errors out when a subscript is applied to a non-array field. }
function TSemanticAnalyser.TryAnalyseFieldElemWrite(AAssign: TFieldAssignment;
  AFldInfo: TFieldInfo): Boolean;
var
  ElemT:    TTypeDesc;
  IdxType:  TTypeDesc;
  ExprType: TTypeDesc;
begin
  Result := False;
  if AAssign.PropIndexExpr = nil then
    Exit;
  if AFldInfo.TypeDesc.Kind = tyDynArray then
    ElemT := TDynArrayTypeDesc(AFldInfo.TypeDesc).ElementType
  else if AFldInfo.TypeDesc.Kind = tyStaticArray then
    ElemT := TStaticArrayTypeDesc(AFldInfo.TypeDesc).ElementType
  else
  begin
    { A class field carrying a default array property: the subscript is a write
      through that default property, Recv.Field[I] := V → (Recv.Field).Default[I]
      := V.  Otherwise the subscript is meaningless on this field. }
    if TryLowerDefaultPropertyWrite(AAssign, AFldInfo.TypeDesc) then
    begin
      Result := True;
      Exit;
    end;
    SemanticError(
      Format('Field ''%s'' is not an array — cannot assign to a subscript',
        [AAssign.FieldName]),
      AAssign.Line, AAssign.Col);
    Exit;
  end;
  IdxType := Self.AnalyseExprSlot(AAssign.PropIndexExpr);
  if not IdxType.IsArrayIndex() then
    SemanticError('Array index must be an ordinal type', AAssign.Line, AAssign.Col);
  { Hint a bracket set literal against the element set type — a plain-variable
    array element write already does this (AnalyseExprHinted), but the
    field-array element destination (R.Arr[0] := [3, 200]) went through the
    unhinted slot analysis and kept the open-array type, so it failed the
    match (BUG-20260722-jumbo-field-array-elem symptom 4). }
  ExprType := Self.AnalyseExprHinted(AAssign.Expr, ElemT);
  CheckTypesMatch(ElemT, ExprType,
    Format('''%s'' element', [AAssign.FieldName]), AAssign.Line, AAssign.Col);
  AAssign.IsElemWrite := True;
  Result := True;
end;

{ Write through a default array property on a member result:
  Recv.Member[idx] := V where Member (a field or property) yields a class that
  carries a writable `default` indexed property — lower to
  (Recv.Member).Default[idx] := V.  Reads the member into an inner object
  expression (the new ObjExpr receiver) and re-targets the assignment at the
  default property's setter.  Class members only (a record getter result is a
  by-value temp, so a write through it would be discarded).  Returns False when
  no lowering applies (no trailing index, not a class, or no writable default
  property), leaving the caller to handle the member as before. }
function TSemanticAnalyser.TryLowerDefaultPropertyWrite(
  AAssign: TFieldAssignment; AMemberType: TTypeDesc): Boolean;
var
  DefProp: TPropertyInfo;
  DefRT:   TRecordTypeDesc;
  Inner:   TFieldAccessExpr;
  IdxType: TTypeDesc;
  ValType: TTypeDesc;
begin
  Result := False;
  if AAssign.PropIndexExpr = nil then
    Exit;
  if (AMemberType = nil) or (AMemberType.Kind <> tyClass) then
    Exit;
  DefRT   := TRecordTypeDesc(AMemberType);
  DefProp := DefRT.FindDefaultProperty();
  if (DefProp = nil) or (DefProp.WriteMethod = '') then
    Exit;
  { Inner = the member read (the getter / field access), the receiver of the
    setter call.  Carries the original receiver (RecordName form, or the ObjExpr
    receiver if one was already present). }
  Inner := TFieldAccessExpr.Create();
  Inner.Line       := AAssign.Line;
  Inner.Col        := AAssign.Col;
  Inner.Base       := AAssign.ObjExpr;     { transfer (nil for the RecordName form) }
  Inner.RecordName := AAssign.RecordName;
  Inner.FieldName  := AAssign.FieldName;
  AnalyseExpr(Inner);
  { Re-target the assignment at the default property setter on that result. }
  AAssign.ObjExpr           := Inner;
  AAssign.RecordName        := '';
  AAssign.FieldName         := DefProp.Name;
  AAssign.PropWriteInfo     := DefProp;
  AAssign.PropOwnerType     := PropAccessorOwner(DefRT.Name, DefProp.WriteMethod);
  AAssign.PropAccessorVSlot := PropAccessorVSlot(DefRT.Name, DefProp.WriteMethod);
  IdxType := Self.AnalyseExprSlot(AAssign.PropIndexExpr);
  if DefProp.IndexTypeDesc <> nil then
    CheckTypesMatch(DefProp.IndexTypeDesc, IdxType, 'default property index',
      AAssign.Line, AAssign.Col);
  ValType := Self.AnalyseExprSlot(AAssign.Expr);
  CheckTypesMatch(DefProp.TypeDesc, ValType, 'default property assignment',
    AAssign.Line, AAssign.Col);
  Result := True;
end;

procedure TSemanticAnalyser.AnalyseFieldAssignment(AAssign: TFieldAssignment);
var
  RecSym:   TSymbol;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  BaseInfo: TFieldInfo;
  BaseType: TTypeDesc;
  PropInfo: TPropertyInfo;
  ExprType: TTypeDesc;
  ObjType:  TTypeDesc;
  IntfDesc: TInterfaceTypeDesc;
  VarSym:   TSymbol;
  BaseE:    TASTExpr;
begin
  { ObjExpr path: receiver is an arbitrary expression (e.g. typecast result) }
  if AAssign.ObjExpr <> nil then
  begin
    ObjType := Self.AnalyseExprSlot(AAssign.ObjExpr);
    if not (ObjType.Kind in [tyRecord, tyClass]) then
      SemanticError(
        Format('Field assignment: expression is not a record or class (got %s)',
          [ObjType.Name]),
        AAssign.Line, AAssign.Col);
    { BUG-001, deep-path arm: 'R.Inner.Field := x' where every link from the
      root identifier to the receiver is a value RECORD writes the loop
      variable's per-iteration copy — discarded.  Any class link in the chain
      (or a non-record root) means the write reaches a live heap object, so
      the walk stops there and no warning is issued. }
    if ObjType.Kind = tyRecord then
    begin
      BaseE := AAssign.ObjExpr;
      while (BaseE is TFieldAccessExpr) and
            (BaseE.ResolvedType <> nil) and
            (BaseE.ResolvedType.Kind = tyRecord) do
        BaseE := TFieldAccessExpr(BaseE).Base;
      if (BaseE is TIdentExpr) and
         (FForInLoopVars.IndexOf(TIdentExpr(BaseE).Name) >= 0) then
      begin
        VarSym := FTable.Lookup(TIdentExpr(BaseE).Name);
        if (VarSym <> nil) and (VarSym.Kind = skVariable) and
           (VarSym.TypeDesc <> nil) and (VarSym.TypeDesc.Kind = tyRecord) then
          SemanticWarning(
            Format('write to field ''%s'' of for-in loop variable ''%s'' is '
              + 'discarded (the loop variable is a per-iteration copy) — use '
              + 'an indexed ''for'' loop to mutate the collection',
              [AAssign.FieldName, TIdentExpr(BaseE).Name]),
            AAssign.Line, AAssign.Col);
      end;
    end;
    RT      := TRecordTypeDesc(ObjType);
    FldInfo := RT.FindField(AAssign.FieldName);
    if FldInfo = nil then
    begin
      PropInfo := RT.FindProperty(AAssign.FieldName);
      if PropInfo <> nil then
        AssertMemberVisibleV(PropInfo.Visibility, PropInfo.DeclaringUnit,
                             PropInfo.DeclaringType, AAssign.FieldName,
                             AAssign.Line, AAssign.Col);
      if (PropInfo <> nil) and (PropInfo.WriteField <> '') then
      begin
        AAssign.FieldName := PropInfo.WriteField;
        FldInfo           := RT.FindField(PropInfo.WriteField);
      end
      else
        SemanticError(
          Format('Type ''%s'' has no field ''%s''', [ObjType.Name, AAssign.FieldName]),
          AAssign.Line, AAssign.Col);
    end
    else
      AssertMemberVisibleV(FldInfo.Visibility, FldInfo.DeclaringUnit,
                           FldInfo.DeclaringType, AAssign.FieldName,
                           AAssign.Line, AAssign.Col);
    AAssign.IsClassAccess := ObjType.Kind = tyClass;
    AAssign.FieldInfo     := FldInfo;
    if TryAnalyseFieldElemWrite(AAssign, FldInfo) then
      Exit;
    { Set-literal RHS into a tySet field — analyse with set context. }
    if (FldInfo.TypeDesc.Kind = tySet) and (AAssign.Expr is TArrayLiteralExpr) then
    begin
      AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
        TSetTypeDesc(FldInfo.TypeDesc));
      Exit;
    end;
    { Phase 9a: a '->' lambda RHS takes its types from the field's
      'reference to' type. }
    InferArrowFromTarget(AAssign.Expr, FldInfo.TypeDesc);
    ExprType := Self.AnalyseExprSlot(AAssign.Expr);
    CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
      AAssign.Line, AAssign.Col);
    Exit;
  end;
  RecSym := FTable.Lookup(AAssign.RecordName);
  { BUG-001: a field write through a for-in loop variable whose element type is
    a RECORD (a per-iteration value copy) is discarded — it never reaches the
    collection element.  A for-in over an array/list of CLASS references binds
    the loop variable to the live object, so 'obj.Field := x' DOES mutate it;
    only warn for value-copy (record) loop variables. }
  if (FForInLoopVars.IndexOf(AAssign.RecordName) >= 0) and
     (RecSym <> nil) and
     (RecSym.TypeDesc <> nil) and (RecSym.TypeDesc.Kind = tyRecord) then
    SemanticWarning(
      Format('write to field ''%s'' of for-in loop variable ''%s'' is discarded '
        + '(the loop variable is a per-iteration copy) — use an indexed ''for'' '
        + 'loop to mutate the collection', [AAssign.FieldName, AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  if RecSym = nil then
  begin
    { Implicit Self.Field.Subfield — RecordName is a field of current class }
    if FCurrentClass <> nil then
    begin
      BaseInfo := FCurrentClass.FindField(AAssign.RecordName);
      if (BaseInfo <> nil) and
         (BaseInfo.TypeDesc.Kind in [tyRecord, tyClass]) then
      begin
        AAssign.IsImplicitSelf   := True;
        AAssign.ImplicitBaseInfo := BaseInfo;
        AAssign.IsClassAccess    := BaseInfo.TypeDesc.Kind = tyClass;
        BaseType := BaseInfo.TypeDesc;
        RT       := TRecordTypeDesc(BaseType);
        FldInfo  := RT.FindField(AAssign.FieldName);
        if FldInfo = nil then
        begin
          PropInfo := RT.FindProperty(AAssign.FieldName);
          if (PropInfo <> nil) and (PropInfo.WriteField <> '') then
          begin
            AAssign.FieldName := PropInfo.WriteField;
            FldInfo           := RT.FindField(PropInfo.WriteField);
          end
          else if (PropInfo <> nil) and (PropInfo.WriteMethod <> '') then
          begin
            { Method-backed write (includes indexed properties) }
            if PropInfo.IndexParamName <> '' then
            begin
              if AAssign.PropIndexExpr = nil then
                SemanticError(
                  Format('Indexed property ''%s'' requires an index expression',
                    [AAssign.FieldName]),
                  AAssign.Line, AAssign.Col);
              Self.AnalyseExprSlot(AAssign.PropIndexExpr);
            end;
            AAssign.PropWriteInfo := PropInfo;
            AAssign.PropOwnerType :=
              PropAccessorOwner(RT.Name, PropInfo.WriteMethod);
            AAssign.PropAccessorVSlot :=
              PropAccessorVSlot(RT.Name, PropInfo.WriteMethod);
            ExprType := Self.AnalyseExprSlot(AAssign.Expr);
            CheckTypesMatch(PropInfo.TypeDesc, ExprType, 'property assignment',
              AAssign.Line, AAssign.Col);
            Exit;
          end
          else
            SemanticError(
              Format('Type ''%s'' has no field ''%s''',
                [AAssign.RecordName, AAssign.FieldName]),
              AAssign.Line, AAssign.Col);
        end;
        AAssign.FieldInfo := FldInfo;
        if TryAnalyseFieldElemWrite(AAssign, FldInfo) then
          Exit;
        ExprType := Self.AnalyseExprSlot(AAssign.Expr);
        CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
          AAssign.Line, AAssign.Col);
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  end;
  { Qualified STATIC (class-level) variable write: 'TFoo.StaticVar := V'.
    RecordName is a class/record TYPE, not a variable; the static var was
    registered under the combined key 'TFoo.StaticVar'.  Enforce member
    visibility (a strict/private static var written from another type is
    rejected with a "not accessible" diagnostic), then mark the node so codegen
    lowers it as a plain store to the shared global slot — identical to the bare
    'StaticVar := V' form a static method writes. }
  if RecSym.Kind = skType then
  begin
    VarSym := FTable.Lookup(AAssign.RecordName + '.' + AAssign.FieldName);
    if (VarSym <> nil) and (VarSym.Kind = skVariable) and VarSym.IsClassVar then
    begin
      AssertStaticVarVisible(VarSym.Visibility, VarSym.OwningUnit,
                             VarSym.OwnerTypeName, AAssign.FieldName,
                           AAssign.Line, AAssign.Col);
      AAssign.IsClassVarWrite  := True;
      AAssign.ClassVarEmitName := VarSym.GlobalEmitName;
      AAssign.ClassVarLhsType  := VarSym.TypeDesc;
      AAssign.IsGlobal         := True;
      if (VarSym.TypeDesc.Kind = tySet) and (AAssign.Expr is TArrayLiteralExpr) then
      begin
        AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
          TSetTypeDesc(VarSym.TypeDesc));
        Exit;
      end;
      ResolveDiamond(AAssign.Expr, VarSym.TypeDesc);
      ExprType := Self.AnalyseExprSlot(AAssign.Expr);
      CheckTypesMatch(VarSym.TypeDesc, ExprType, 'static var assignment',
        AAssign.Line, AAssign.Col);
      Exit;
    end;
  end;
  if not (RecSym.Kind in [skVariable, skParameter, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  { Interface property write: I.Prop := V lowers to the setter dispatched
    through the itab.  FieldName is rewritten to the setter method name;
    codegen reads IntfWriteDesc to emit the indirect call. }
  if RecSym.TypeDesc.Kind = tyInterface then
  begin
    IntfDesc := TInterfaceTypeDesc(RecSym.TypeDesc);
    PropInfo := IntfDesc.FindProperty(AAssign.FieldName);
    if PropInfo = nil then
      SemanticError(
        Format('Interface ''%s'' has no property ''%s''',
          [IntfDesc.Name, AAssign.FieldName]),
        AAssign.Line, AAssign.Col);
    if PropInfo.WriteMethod = '' then
      SemanticError(
        Format('Interface property ''%s.%s'' is read-only',
          [IntfDesc.Name, AAssign.FieldName]),
        AAssign.Line, AAssign.Col);
    AAssign.RecordName    := RecSym.Name;  { normalise to declared casing }
    AAssign.FieldName     := PropInfo.WriteMethod;
    AAssign.IntfWriteDesc := IntfDesc;
    AAssign.IsGlobal      := RecSym.IsGlobal;
    AAssign.IsVarParam    := RecSym.Kind = skVarParameter;
    if TryResolveBareEnumIdent(AAssign.Expr, PropInfo.TypeDesc) then
      ExprType := AAssign.Expr.ResolvedType
    else
      ExprType := Self.AnalyseExprSlot(AAssign.Expr);
    CheckTypesMatch(PropInfo.TypeDesc, ExprType, 'property assignment',
      AAssign.Line, AAssign.Col);
    Exit;
  end;
  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);

  AAssign.RecordName    := RecSym.Name;  { normalise to declared casing }
  AAssign.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAssign.IsGlobal      := RecSym.IsGlobal;
  { Treat value record/array params as by-reference at QBE ABI level. }
  AAssign.IsVarParam    :=
    (RecSym.Kind = skVarParameter) or
    ((RecSym.Kind = skParameter) and (RecSym.TypeDesc <> nil) and
     (RecSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAssign.FieldName);
  if FldInfo = nil then
  begin
    { Check if this is a property write }
    PropInfo := RT.FindProperty(AAssign.FieldName);
    if PropInfo <> nil then
    begin
      AssertMemberVisibleV(PropInfo.Visibility, PropInfo.DeclaringUnit,
                           PropInfo.DeclaringType, AAssign.FieldName,
                           AAssign.Line, AAssign.Col);
      if PropInfo.WriteField <> '' then
      begin
        { Field-backed write: redirect to the backing field }
        AAssign.FieldName := PropInfo.WriteField;
        FldInfo           := RT.FindField(PropInfo.WriteField);
      end
      else if PropInfo.WriteMethod <> '' then
      begin
        { Method-backed write (includes indexed properties) }
        if PropInfo.IndexParamName <> '' then
        begin
          if AAssign.PropIndexExpr = nil then
            SemanticError(
              Format('Indexed property ''%s'' requires an index expression',
                [AAssign.FieldName]),
              AAssign.Line, AAssign.Col);
          Self.AnalyseExprSlot(AAssign.PropIndexExpr);
        end;
        AAssign.PropWriteInfo := PropInfo;
        AAssign.PropOwnerType :=
          PropAccessorOwner(RT.Name, PropInfo.WriteMethod);
        AAssign.PropAccessorVSlot :=
          PropAccessorVSlot(RT.Name, PropInfo.WriteMethod);
        ExprType := Self.AnalyseExprSlot(AAssign.Expr);
        CheckTypesMatch(PropInfo.TypeDesc, ExprType, 'property assignment',
          AAssign.Line, AAssign.Col);
        Exit;
      end
      else if TryLowerDefaultPropertyWrite(AAssign, PropInfo.TypeDesc) then
        Exit
      else
        SemanticError(
          Format('Property ''%s'' is read-only', [AAssign.FieldName]),
          AAssign.Line, AAssign.Col);
    end
    else
      SemanticError(
        Format('''%s'' (of type ''%s'') has no field ''%s''',
          [AAssign.RecordName, RT.Name, AAssign.FieldName]),
        AAssign.Line, AAssign.Col);
  end
  else
    { Field write via variable.Field — enforce visibility. }
    AssertMemberVisibleV(FldInfo.Visibility, FldInfo.DeclaringUnit,
                         FldInfo.DeclaringType, AAssign.FieldName,
                         AAssign.Line, AAssign.Col);

  AAssign.FieldInfo := FldInfo;
  if TryAnalyseFieldElemWrite(AAssign, FldInfo) then
    Exit;
  { Set-literal RHS into a tySet field — analyse with set context. }
  if (FldInfo.TypeDesc.Kind = tySet) and (AAssign.Expr is TArrayLiteralExpr) then
  begin
    AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
      TSetTypeDesc(FldInfo.TypeDesc));
    Exit;
  end;
  if TryResolveBareEnumIdent(AAssign.Expr, FldInfo.TypeDesc) then
    ExprType := AAssign.Expr.ResolvedType
  else
    ExprType := Self.AnalyseExprSlot(AAssign.Expr);
  CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
    AAssign.Line, AAssign.Col);
end;

function TSemanticAnalyser.MangleTypeCode(AType: TTypeDesc;
  AVarParam: Boolean): string;
var
  Base: string;
  PT:   TPointerTypeDesc;
begin
  if AType = nil then
  begin
    Exit('?');
  end;
  case AType.Kind of
    tyInteger:  Base := 'i';
    tyInt64:    Base := 'l';
    tyUInt32:   Base := 'u';
    tyUInt64:   Base := 'Q';
    tySmallInt: Base := 'h';
    tyWord:     Base := 'H';
    tyByte:     Base := 'y';
    tyBoolean:  Base := 'b';
    tyDouble:   Base := 'd';
    tySingle:   Base := 's';
    tyString:   Base := 'S';
    tyPChar:    Base := 'C';
    tyEnum:     Base := 'E' + AType.Name;
    tyRecord:   Base := 'R' + AType.Name;
    tyClass:    Base := 'K' + AType.Name;
    tyInterface:Base := 'I' + AType.Name;
    tyPointer:
      begin
        PT := TPointerTypeDesc(AType);
        if (PT.BaseType = nil) then
          Base := 'p'
        else
          Base := '^' + MangleTypeCode(PT.BaseType, False);
      end;
    tyOpenArray: Base := 'A' + MangleTypeCode(
                          TOpenArrayTypeDesc(AType).ElementType, False);
    tySet:       Base := 'T' + AType.Name;
    tyProcedural:Base := 'F' + AType.Name;
  else
    Base := '?';
  end;
  if AVarParam then
    Result := '@' + Base
  else
    Result := Base;
end;

function TSemanticAnalyser.MangleParamSig(ADecl: TMethodDecl): string;
var
  I:   Integer;
  Par: TMethodParam;
begin
  Result := '';
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par    := TMethodParam(ADecl.Params.Items[I]);
    Result := Result + MangleTypeCode(Par.ResolvedType, Par.IsVarParam);
  end;
end;

function TSemanticAnalyser.MinArity(ADecl: TMethodDecl): Integer;
var
  I: Integer;
begin
  for I := 0 to ADecl.Params.Count - 1 do
    if (TMethodParam(ADecl.Params.Items[I]).DefaultValue <> nil) or
       (TMethodParam(ADecl.Params.Items[I]).HasDefault) then
    begin
      Exit(I);
    end;
  Result := ADecl.Params.Count;
end;

procedure TSemanticAnalyser.TransferDefaultValues(AFrom, AInto: TMethodDecl);
var
  I:    Integer;
  PSrc: TMethodParam;
  PDst: TMethodParam;
begin
  if (AFrom = nil) or (AInto = nil) then Exit;
  if AFrom.Params.Count <> AInto.Params.Count then Exit;
  for I := 0 to AFrom.Params.Count - 1 do
  begin
    PSrc := TMethodParam(AFrom.Params.Items[I]);
    PDst := TMethodParam(AInto.Params.Items[I]);
    if (PSrc.DefaultValue <> nil) and (PDst.DefaultValue = nil) then
      { Clone rather than move: the source is the interface forward decl,
        which uSemanticExport later serialises into the unit's .bif.  Moving
        (nil-ing PSrc) stripped the default from the exported signature, so a
        caller in a SEPARATE compilation that loaded the unit from its cached
        .bif could not omit the defaulted trailing arguments.  Both decls now
        keep their own copy. }
      PDst.DefaultValue := CloneExpr(PSrc.DefaultValue);
  end;
end;

procedure TSemanticAnalyser.AnalyseDefaultValueExpr(APar: TMethodParam;
  const AContext: string; ALine, ACol: Integer);
var
  T: TTypeDesc;
begin
  if APar.DefaultValue = nil then Exit;
  if APar.DefaultValue.ResolvedType <> nil then Exit;  { already analysed }
  if not ((APar.DefaultValue is TIntLiteral)    or
          (APar.DefaultValue is TFloatLiteral)  or
          (APar.DefaultValue is TStringLiteral) or
          (APar.DefaultValue is TNilLiteral)    or
          (APar.DefaultValue is TIdentExpr)) then
    SemanticError(
      Format('Default value for parameter ''%s'' must be a literal or named constant',
        [APar.ParamName]),
      ALine, ACol);
  T := Self.AnalyseExprSlot(APar.DefaultValue);
  if APar.DefaultValue is TIdentExpr then
    if not TIdentExpr(APar.DefaultValue).IsConstant then
      SemanticError(
        Format('Default value for parameter ''%s'' must be a constant expression',
          [APar.ParamName]),
        ALine, ACol);
  CheckTypesMatch(APar.ResolvedType, T,
    Format('default value of parameter ''%s'' (%s)', [APar.ParamName, AContext]),
    ALine, ACol);
end;

function TSemanticAnalyser.CloneDefaultExprNode(ASrc: TASTExpr): TASTExpr;
var
  ILit: TIntLiteral;
  FLit: TFloatLiteral;
  SLit: TStringLiteral;
  Ident: TIdentExpr;
  SrcId: TIdentExpr;
begin
  Result := nil;
  if ASrc = nil then Exit;
  if ASrc is TIntLiteral then
  begin
    ILit       := TIntLiteral.Create();
    ILit.Value := TIntLiteral(ASrc).Value;
    ILit.Line  := ASrc.Line;
    ILit.Col   := ASrc.Col;
    ILit.ResolvedType := ASrc.ResolvedType;
    Result := ILit;
  end
  else if ASrc is TFloatLiteral then
  begin
    FLit       := TFloatLiteral.Create();
    FLit.Value := TFloatLiteral(ASrc).Value;
    FLit.Line  := ASrc.Line;
    FLit.Col   := ASrc.Col;
    FLit.ResolvedType := ASrc.ResolvedType;
    Result := FLit;
  end
  else if ASrc is TStringLiteral then
  begin
    SLit       := TStringLiteral.Create();
    SLit.Value := TStringLiteral(ASrc).Value;
    SLit.IsCharCoerce := TStringLiteral(ASrc).IsCharCoerce;
    SLit.CharOrdValue := TStringLiteral(ASrc).CharOrdValue;
    SLit.Line  := ASrc.Line;
    SLit.Col   := ASrc.Col;
    SLit.ResolvedType := ASrc.ResolvedType;
    Result := SLit;
  end
  else if ASrc is TNilLiteral then
  begin
    Result      := TNilLiteral.Create();
    Result.Line := ASrc.Line;
    Result.Col  := ASrc.Col;
    Result.ResolvedType := ASrc.ResolvedType;
  end
  else if ASrc is TIdentExpr then
  begin
    SrcId  := TIdentExpr(ASrc);
    Ident  := TIdentExpr.Create();
    Ident.Name        := SrcId.Name;
    Ident.IsConstant  := SrcId.IsConstant;
    Ident.ConstValue  := SrcId.ConstValue;
    Ident.ConstString := SrcId.ConstString;
    Ident.Line        := SrcId.Line;
    Ident.Col         := SrcId.Col;
    Ident.ResolvedType := SrcId.ResolvedType;
    Result := Ident;
  end
  else
    SemanticError(
      'Internal: unsupported default-value AST node — only literals and named constants allowed',
      ASrc.Line, ASrc.Col);
end;

{ Extra arguments to a 'varargs' external (beyond its fixed parameter
  list) must be C-passable: integers, floats, pointers, PChar, nil.
  Two deliberate errors guide the caller: a Blaise string needs an
  explicit PChar() borrow, and a Single needs promotion to Double
  (C's default argument promotions — the callee reads a double). }
procedure TSemanticAnalyser.ValidateVarArgsExtras(AArgs: TObjectList;
  AMDecl: TMethodDecl; const AName: string; ALine, ACol: Integer);
var
  I: Integer;
  T: TTypeDesc;
begin
  if AArgs.Count <= AMDecl.Params.Count then Exit;
  for I := AMDecl.Params.Count to AArgs.Count - 1 do
  begin
    T := TASTExpr(AArgs.Items[I]).ResolvedType;
    if T = nil then
      SemanticError(
        Format('varargs argument %d of ''%s'' has no type', [I + 1, AName]),
        ALine, ACol);
    case T.Kind of
      tyInteger, tyInt64, tyUInt32, tyUInt64, tySmallInt, tyWord, tyByte,
      tyBoolean, tyEnum, tyDouble, tyPChar, tyPointer, tyNil: ;
      tySingle:
        SemanticError(
          Format('varargs argument %d of ''%s'': C promotes float to ' +
            'double — pass Double(...) explicitly', [I + 1, AName]),
          ALine, ACol);
      tyString:
        SemanticError(
          Format('varargs argument %d of ''%s'': a Blaise string cannot ' +
            'cross a C varargs boundary — pass PChar(...)', [I + 1, AName]),
          ALine, ACol);
      else
        SemanticError(
          Format('varargs argument %d of ''%s'': type ''%s'' cannot be ' +
            'passed to a C variadic function', [I + 1, AName, T.Name]),
          ALine, ACol);
    end;
  end;
end;

procedure TSemanticAnalyser.AppendDefaultArgs(AArgs: TObjectList;
  ADecl: TMethodDecl; const AContext: string; ALine, ACol: Integer);
var
  I:        Integer;
  Par:      TMethodParam;
  CloneEx:  TASTExpr;
begin
  if ADecl = nil then Exit;
  for I := AArgs.Count to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.DefaultValue = nil then
      SemanticError(
        Format('No default value for parameter ''%s'' of ''%s''',
          [Par.ParamName, AContext]),
        ALine, ACol);
    AnalyseDefaultValueExpr(Par, AContext, ALine, ACol);
    CloneEx := CloneDefaultExprNode(Par.DefaultValue);
    AArgs.Add(CloneEx);
  end;
end;

{ After overload resolution: any bracket-literal argument matched against a
  `set of` parameter is a set constructor, but it was analysed without set
  context (so its ResolvedType is an open-array, not the set).  Re-point each
  such argument's ResolvedType at the parameter's set type so codegen emits a
  bitmask (EmitArrayLiteralExpr dispatches on ResolvedType.Kind = tySet). }
procedure TSemanticAnalyser.RetypeSetLiteralArgs(AArgs: TObjectList;
  AMDecl: TMethodDecl);
var
  I:   Integer;
  Par: TMethodParam;
  Arg: TASTExpr;
  N:   Integer;
begin
  N := AArgs.Count;
  if AMDecl.Params.Count < N then
    N := AMDecl.Params.Count;
  for I := 0 to N - 1 do
  begin
    Par := TMethodParam(AMDecl.Params.Items[I]);
    Arg := TASTExpr(AArgs.Items[I]);
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tySet) and
       (Arg is TArrayLiteralExpr) then
      Arg.ResolvedType := Par.ResolvedType;
    { Bracket literal bound to an 'array of const' formal: mark it so codegen
      boxes each element into a TVarRec, and pin its type to the formal's
      array-of-TVarRec (the homogeneous case was typed 'array of <T>'). }
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyOpenArray) and
       (TOpenArrayTypeDesc(Par.ResolvedType).ElementType <> nil) and
       SameText(TOpenArrayTypeDesc(Par.ResolvedType).ElementType.Name, 'TVarRec') and
       (Arg is TArrayLiteralExpr) then
    begin
      TArrayLiteralExpr(Arg).IsConstArray := True;
      Arg.ResolvedType := Par.ResolvedType;
    end;
    { Empty bracket literal [] bound to a plain open-array formal: pin its type
      to the formal so codegen emits a zero-length open array (data=nil, high=-1)
      of the right element type.  The untyped [] would otherwise reach codegen
      with no ResolvedType. }
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyOpenArray) and
       (Arg is TArrayLiteralExpr) and
       (TArrayLiteralExpr(Arg).Elements.Count = 0) and
       (Arg.ResolvedType = nil) then
      Arg.ResolvedType := Par.ResolvedType;
  end;
end;

{ If every element of the bracket literal is an enum constant of one shared
  enum, return that enum descriptor; otherwise nil.  Used to recognise a set
  constructor [a, b] passed where a `set of <enum>` is expected.  An empty
  literal returns nil (the caller treats [] as matching any set). }
function TSemanticAnalyser.SetLiteralBaseEnum(AExpr: TArrayLiteralExpr): TTypeDesc;
var
  I:    Integer;
  Elem: TASTExpr;
  Ref:  TEnumMemberRef;
begin
  Result := nil;
  if AExpr.Elements.Count = 0 then Exit;
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    Elem := TASTExpr(AExpr.Elements.Items[I]);
    if not (Elem is TIdentExpr) then
      Exit(nil);
    { Resolve each element against the enum pinned by the first one, so a
      member name shared by several enums follows the rest of the literal. }
    Ref := ResolveEnumMember(TIdentExpr(Elem).Name, Result);
    if Ref = nil then
      Exit(nil);
    if Result = nil then
      Result := Ref.EnumDesc
    else if Ref.EnumDesc <> Result then
    begin
      Result := nil;   { mixed enums — not a clean set constructor }
      Exit;
    end;
  end;
end;

function TSemanticAnalyser.ArgMatchScore(AParam: TTypeDesc;
  AArg: TTypeDesc; AArgExpr: TASTExpr): Integer;
begin
  Result := 0;
  if AParam = nil then Exit;
  { Phase 9b: a deferred '->' lambda argument has no ResolvedType yet —
    score it by SHAPE: it matches exactly one kind of parameter, a
    'reference to' type with the same parameter count.  The body is
    analysed only after the winning candidate supplies the types. }
  if (AArgExpr is TAnonMethodExpr) and TAnonMethodExpr(AArgExpr).IsArrow and
     (AArgExpr.ResolvedType = nil) then
  begin
    if (AParam.Kind = tyProcedural) and
       TProceduralTypeDesc(AParam).IsReference and
       (TProceduralTypeDesc(AParam).Params.Count =
        TAnonMethodExpr(AArgExpr).Decl.Params.Count) then
      Result := 2;
    Exit;
  end;
  { A bracket literal [a, b] against a `set of <enum>` parameter is a set
    constructor, even though (lacking set context) it was analysed as an
    open-array — or, for the empty literal [], left untyped.  Match it here,
    before the nil-arg bail, so [] also matches.  AnalyseProcCall re-types the
    argument to the set type before codegen so the bitmask is emitted.  Checked
    first because an empty-literal arg has no ResolvedType. }
  if (AParam.Kind = tySet) and (AArgExpr is TArrayLiteralExpr) then
  begin
    if TArrayLiteralExpr(AArgExpr).Elements.Count = 0 then
      Result := 2
    else if TSetTypeDesc(AParam).BaseType.Kind in [tyByte, tyBoolean] then
      Result := 2
    else if TSetTypeDesc(AParam).BaseType =
            SetLiteralBaseEnum(TArrayLiteralExpr(AArgExpr)) then
      Result := 2;
    Exit;
  end;
  { An 'array of const' formal (open array of TVarRec) accepts any bracket
    literal — homogeneous or heterogeneous.  Matched here before the generic
    open-array rules so a heterogeneous literal (typed 'array of TVarRec') and
    a homogeneous one ('array of Integer') both bind, and the empty literal []
    (nil arg type) binds too. }
  if (AParam.Kind = tyOpenArray) and
     (TOpenArrayTypeDesc(AParam).ElementType <> nil) and
     SameText(TOpenArrayTypeDesc(AParam).ElementType.Name, 'TVarRec') and
     (AArgExpr is TArrayLiteralExpr) then
  begin
    Result := 2;
    Exit;
  end;
  { An EMPTY bracket literal [] passed to a plain open-array parameter (array of
    T) is a valid empty open array of any element type — it has no elements to
    infer a type from, so AnalyseArrayLiteralExpr left it untyped (nil).  Match
    it here, before the nil-arg bail; AnalyseProcCall re-types it to the formal's
    open-array type so codegen emits a zero-length (data=nil, high=-1) array. }
  if (AParam.Kind = tyOpenArray) and (AArgExpr is TArrayLiteralExpr) and
     (TArrayLiteralExpr(AArgExpr).Elements.Count = 0) then
  begin
    Result := 2;
    Exit;
  end;
  if AArg = nil then Exit;
  { Integer literal (untyped constant) matches any integer type exactly —
    mirrors Pascal's treatment of untyped integer constants.  Floating-point
    params score 1 (widening) so an Integer overload beats a Double overload
    when both are candidates. }
  if (AArgExpr is TIntLiteral) and AParam.IsNumeric() then
  begin
    if AParam.Kind in [tyInteger, tyInt64, tyUInt32, tyUInt64,
                       tySmallInt, tyWord, tyByte] then
      Result := 2
    else
      Result := 1;  { Double, Single — widening }
    Exit;
  end;
  if AParam = AArg then
  begin
    Result := 2;  { exact match — same descriptor instance }
    Exit;
  end;
  { Same-kind, same-name, structurally identical types count as exact —
    catches multiple TOpenArrayTypeDesc instances over the same element. }
  if (AParam.Kind = tyOpenArray) and (AArg.Kind = tyOpenArray) and
     (TOpenArrayTypeDesc(AParam).ElementType =
      TOpenArrayTypeDesc(AArg).ElementType) then
  begin
    Exit(2);
  end;
  { Static array coerced to open-array: widening match (score 1) }
  if (AParam.Kind = tyOpenArray) and (AArg.Kind = tyStaticArray) and
     (TOpenArrayTypeDesc(AParam).ElementType =
      TStaticArrayTypeDesc(AArg).ElementType) then
  begin
    Exit(1);
  end;
  { Dynamic array coerced to open-array: widening match (score 1).  A dynamic
    array passes its (data ptr, high) to an open-array formal. }
  if (AParam.Kind = tyOpenArray) and (AArg.Kind = tyDynArray) and
     (TOpenArrayTypeDesc(AParam).ElementType =
      TDynArrayTypeDesc(AArg).ElementType) then
  begin
    Exit(1);
  end;
  { Same numeric kind = exact match (same kind, just possibly different
    descriptor instance). }
  if AParam.IsNumeric() and AArg.IsNumeric() and (AParam.Kind = AArg.Kind) then
  begin
    Exit(2);
  end;
  { Numeric widening: both numerics, kinds differ.  Captures
    Integer→Int64, Integer→Double, Single→Double, Byte→Integer, etc. }
  if AParam.IsNumeric() and AArg.IsNumeric() then
  begin
    Exit(1);
  end;
  { Fall-through: probe full assignability via CheckTypesMatch.  This
    covers nil-literal, class subtypes, untyped-Pointer compatibility,
    enum/integer crossover, procedural-type signature compatibility,
    and similar.  Cost 1 (widening). }
  try
    CheckTypesMatch(AParam, AArg, '', 0, 0);
    Result := 1;
  except
    on E: ESemanticError do
      Result := 0;
  end;
end;

function TSemanticAnalyser.ResolveStandaloneOverload(const AName: string;
  AArity: Integer; AArgs: TObjectList; ALine, ACol: Integer): TMethodDecl;
var
  I, J:        Integer;
  Cand:        TMethodDecl;
  Grp:         TObjectList;
  ArityMatch:  TObjectList;
  Score:       Integer;
  ArgScore:    Integer;
  Par:         TMethodParam;
  Arg:         TASTExpr;
  BestScore:   Integer;
  BestCount:   Integer;
  Best:        TMethodDecl;
  TotalCnt:    Integer;
  ExactNew:    Integer;
  ExactBest:   Integer;
  S1, S2:      Integer;
  FixedN:      Integer;
  DefaultedN:  Integer;
begin
  Result    := nil;
  TotalCnt  := 0;
  ArityMatch := TObjectList.Create(False);
  try
    Grp := GroupOf(FProcGroups, AName);
    if Grp <> nil then
      for I := 0 to Grp.Count - 1 do
      begin
        Cand := TMethodDecl(Grp.Items[I]);
        { Impl-only (implementation-section) routines are PRIVATE to their
          unit.  When several units each declare a same-named private helper
          (e.g. DiagAbort in both blaise_arc and blaise_exc), only the one
          owned by the unit currently being analysed is a valid candidate —
          the others are not visible here and must not count toward
          ambiguity.  Routines exported from an interface (IsImplOnly=False)
          remain globally visible as before. }
        if Cand.IsImplOnly and (Cand.OwningUnit <> '') and
           (FCurrentUnitName <> '') and
           not SameText(Cand.OwningUnit, FCurrentUnitName) then
          Continue;
        Inc(TotalCnt);
        { A varargs external accepts any argument count >= its fixed
          parameter list (the extras are the C '...' part). }
        if (AArity >= MinArity(Cand)) and
           ((AArity <= Cand.Params.Count) or
            (Cand.IsVarArgs and (AArity > Cand.Params.Count))) then
          ArityMatch.Add(Cand);
      end;

    if TotalCnt = 0 then Exit;  { caller treats as "no decl found" }

    if ArityMatch.Count = 0 then
      SemanticError(
        Format('No matching overload for ''%s'' with %d argument(s)',
          [AName, AArity]),
        ALine, ACol);

    { With no args supplied, accept the unique arity match — used by
      callers that haven't analysed their args yet.  Ambiguity is then
      caught when the caller re-resolves with arg types. }
    if (AArgs = nil) or (AArity = 0) then
    begin
      if ArityMatch.Count = 1 then
      begin
        Exit(TMethodDecl(ArityMatch.Items[0]));
      end;
      { Two units may each privately declare the SAME external C function
        (e.g. a parameterless `external name 'abort'`).  Both land in the
        global overload group with identical arity, but they denote ONE
        function — not an ambiguous overload.  Collapse the duplicates: if
        every arity match is the same external decl as the first, accept it
        rather than erroring.  Mirrors the arg-scoring collapse below. }
      if AllSameExternalDecl(ArityMatch) then
        Exit(TMethodDecl(ArityMatch.Items[0]));
      { zero-arg ambiguity is impossible for non-external decls — same name
        + zero params would have been rejected by the symbol-table chain,
        but be defensive. }
      if AArity = 0 then
        SemanticError(
          Format('Ambiguous overload of ''%s''', [AName]),
          ALine, ACol);
      { Multiple arity matches but no args to score with — keep nil. }
      Exit;
    end;

    BestScore := -1;
    BestCount := 0;
    Best      := nil;
    for I := 0 to ArityMatch.Count - 1 do
    begin
      Cand  := TMethodDecl(ArityMatch.Items[I]);
      Score := 0;
      { Varargs extras beyond the fixed parameters are not scored —
        they have no declared type to score against. }
      FixedN := AArity;
      if Cand.Params.Count < FixedN then FixedN := Cand.Params.Count;
      for J := 0 to FixedN - 1 do
      begin
        Par      := TMethodParam(Cand.Params.Items[J]);
        Arg      := TASTExpr(AArgs.Items[J]);
        ArgScore := ArgMatchScore(Par.ResolvedType, Arg.ResolvedType, Arg);
        if ArgScore = 0 then
        begin
          Score := -1;  { drop this candidate }
          Break;
        end;
        Score := Score + ArgScore;
      end;
      if Score < 0 then Continue;
      { Tie-break: prefer the candidate that needs the fewest defaulted
        parameters — i.e. Params.Count closest to AArity.  Score in the
        high bits, defaulting penalty in the low bits.  Each defaulted
        slot subtracts 1 from the composite score. }
      DefaultedN := Cand.Params.Count - AArity;
      if DefaultedN < 0 then DefaultedN := 0;   { varargs extras, not defaults }
      Score := (Score * 16) - DefaultedN;
      if Score > BestScore then
      begin
        BestScore := Score;
        BestCount := 1;
        Best      := Cand;
      end
      else if Score = BestScore then
      begin
        { Secondary tie-break: count exact matches (ArgMatchScore=2).
          More exact matches = better candidate. }
        ExactNew  := 0;
        ExactBest := 0;
        FixedN := AArity;
        if Cand.Params.Count < FixedN then FixedN := Cand.Params.Count;
        if Best.Params.Count < FixedN then FixedN := Best.Params.Count;
        for J := 0 to FixedN - 1 do
        begin
          S1 := ArgMatchScore(TMethodParam(Cand.Params.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]));
          S2 := ArgMatchScore(TMethodParam(Best.Params.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]));
          if S1 = 2 then Inc(ExactNew);
          if S2 = 2 then Inc(ExactBest);
        end;
        if ExactNew > ExactBest then
        begin
          Best      := Cand;
          BestCount := 1;
        end
        else if ExactNew = ExactBest then
        begin
          { Two candidates may denote the SAME underlying link symbol: two
            units each declaring `external name 'strlen'`, or an
            `external name '_BlaiseGetMem'` binding alongside the real
            _BlaiseGetMem exported by blaise_mem.  They score identically but
            are ONE function — not an ambiguous overload.  Collapse instead of
            erroring. }
          if not SameLinkSymbol(Cand, Best) then
            Inc(BestCount);
        end;
      end;
    end;

    if BestScore < 0 then
      SemanticError(
        Format('No matching overload for ''%s'' with %d argument(s)',
          [AName, AArity]),
        ALine, ACol);
    if BestCount > 1 then
      SemanticError(
        Format('Ambiguous overload of ''%s'' — multiple candidates match equally',
          [AName]),
        ALine, ACol);
    Result := Best;
  finally
    ArityMatch.Free();
  end;
end;

procedure TSemanticAnalyser.AnalyseProcCall(ACall: TProcCall);
var
  Sym:     TSymbol;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  Idx:     Integer;
  I:       Integer;
  PT:      TProceduralTypeDesc;
  PPar:    TProcParamInfo;
  FldInfo: TFieldInfo;
begin
  { Resolution order matches Delphi/FPC:
      1. Local variables / parameters / var-parameters — a `var Run:
         TRunMethod` shadows an inherited method of the same name
         (called via the variable, not the method).
      2. Implicit Self.member (incl. inherited via class chain) —
         shadows a unit-level proc of the same name.  Was the bug:
         a `uses strutils` in scope used to bind unqualified
         CountOccurrences inside a class method to strutils's
         version, even when the enclosing class declared its own.
      3. Unit-level proc / function (program-level or uses-clause). }
  Sym := FTable.Lookup(ACall.Name);
  { Only a LOCAL variable/parameter shadows the implicit-Self method — a
    PROGRAM-LEVEL global of the same (case-insensitive) name must not: the
    class scope sits between locals and the unit scope (BUG-037; same rule
    the ident-expression path applies to class fields vs globals). }
  if (FCurrentClass <> nil) and
     ((Sym = nil) or
      (Sym.IsGlobal) or
      not (Sym.Kind in [skVariable, skParameter, skVarParameter])) then
  begin
    MDecl := FindMethodDecl(FCurrentClass.Name, ACall.Name);
    if MDecl <> nil then
    begin
      { Analyse args first so overload resolution can score by type
        ('->' lambda args are deferred and scored by shape — Phase 9b). }
      HintBareEnumMethodArgs(FCurrentClass.Name, ACall.Name, ACall.Args);
      for I := 0 to ACall.Args.Count - 1 do
        Self.AnalyseArgSlot(ACall.Args, I);
      { Use overload resolution so the correct variant is chosen when
        multiple overloads exist (e.g. AssertEquals(string,string,string)
        vs AssertEquals(string,Integer,Integer)). }
      MDecl := ResolveMethodOverload(FCurrentClass.Name, ACall.Name,
        ACall.Args, ACall.Line, ACall.Col);
      if MDecl = nil then
        SemanticError(
          Format('No matching overload for ''%s.%s'' with %d argument(s)',
            [FCurrentClass.Name, ACall.Name, ACall.Args.Count]),
          ACall.Line, ACall.Col);
      ResolveDeferredArrowArgs(ACall.Args, MDecl);
      { Validate only var-param arguments (non-var compatibility was
        verified by the overload scorer). }
      for I := 0 to ACall.Args.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[I]);
        if Par.IsVarParam then
        begin
          if not IsVarArgLValue(TASTExpr(ACall.Args.Items[I])) then
            SemanticError(
              Format('var argument %d of ''%s'' must be a variable',
                [I + 1, ACall.Name]),
              ACall.Line, ACall.Col);
          ArgType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('var argument %d of ''%s''', [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
          WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[I]));
        end;
      end;
      { Set-literal args: see BUG-20260722-native-set-literal-arg. }
      RetypeSetLiteralArgs(ACall.Args, MDecl);
      AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
      ACall.ResolvedDecl         := MDecl;
      ACall.IsImplicitSelfMethod := True;
      Exit;
    end;
    { No method of that name — an unqualified procedural-typed field of the
      current class (implicit Self.Field) dispatches through its stored
      pointer, mirroring the explicit Self.Field() path. }
    FldInfo := FCurrentClass.FindField(ACall.Name);
    if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
       (FldInfo.TypeDesc.Kind = tyProcedural) then
    begin
      PT := TProceduralTypeDesc(FldInfo.TypeDesc);
      if ACall.Args.Count <> PT.Params.Count then
        SemanticError(Format(
          'Indirect call ''%s'' expects %d argument(s), got %d',
          [ACall.Name, PT.Params.Count, ACall.Args.Count]),
          ACall.Line, ACall.Col);
      for I := 0 to ACall.Args.Count - 1 do
      begin
        PPar    := TProcParamInfo(PT.Params.Items[I]);
        ArgType := AnalyseExprHinted(TASTExpr(ACall.Args.Items[I]), PPar.TypeDesc);
        if PPar.IsVarParam and
           not IsVarArgLValue(TASTExpr(ACall.Args.Items[I])) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable',
              [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
        if PPar.IsVarParam then
          WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[I]));
        CheckTypesMatch(PPar.TypeDesc, ArgType,
          Format('argument %d of ''%s''', [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      end;
      ACall.IsProcFieldCall  := True;
      ACall.ProcFieldInfo    := FldInfo;
      ACall.ResolvedProcType := FldInfo.TypeDesc;
      Exit;
    end;
  end;
  { Try on-demand instantiation of a generic function }
  if StrPos('<', ACall.Name) >= 0 then
  begin
    InstantiateGenericFunc(ACall.Name);
    Sym := FTable.Lookup(ACall.Name);
  end;
  if Sym = nil then
    SemanticError(
      Format('Undeclared procedure ''%s''', [ACall.Name]),
      ACall.Line, ACall.Col);
  ACall.Name := Sym.Name;  { normalise to declared casing }
  { Indirect call through a procedural-typed variable used as a statement:
    e.g. 'MyHandler(Arg1, Arg2)' where MyHandler is 'var MyHandler: TMyProc'. }
  if (Sym.Kind in [skVariable, skParameter, skVarParameter]) and
     (Sym.TypeDesc <> nil) and (Sym.TypeDesc.Kind = tyProcedural) then
  begin
    ACall.IsIndirectCall       := True;
    ACall.IndirectCallIsGlobal := Sym.IsGlobal;
    ACall.ResolvedProcType     := Sym.TypeDesc;
    PT := TProceduralTypeDesc(Sym.TypeDesc);
    if ACall.Args.Count <> PT.Params.Count then
      SemanticError(Format(
        'Indirect call ''%s'' expects %d argument(s), got %d',
        [ACall.Name, PT.Params.Count, ACall.Args.Count]),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      PPar    := TProcParamInfo(PT.Params.Items[I]);
      ArgType := AnalyseExprHinted(TASTExpr(ACall.Args.Items[I]), PPar.TypeDesc);
      { Var-param actual must be an L-value; check before the type match
        so the diagnostic matches the regular-call path. }
      if PPar.IsVarParam and
         not IsVarArgLValue(TASTExpr(ACall.Args.Items[I])) then
        SemanticError(
          Format('var argument %d of ''%s'' must be a variable',
            [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      if PPar.IsVarParam then
        WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[I]));
      CheckTypesMatch(PPar.TypeDesc, ArgType,
        Format('argument %d of ''%s''', [I + 1, ACall.Name]),
        ACall.Line, ACall.Col);
    end;
    Exit;
  end;

  if not (Sym.Kind in [skProcedure, skFunction]) then
    SemanticError(
      Format('''%s'' is not a procedure or function', [ACall.Name]),
      ACall.Line, ACall.Col);

  { Nested proc: found in scope but not in FProcIndex (nested procs are
    excluded from the global index to prevent same-name clashes across
    different outer procs).  Resolve directly from the symbol's Decl. }
  if (Sym.Kind in [skProcedure, skFunction]) and
     (Sym.Decl <> nil) and
     (TMethodDecl(Sym.Decl).EnclosingDecl <> nil) then
  begin
    MDecl := TMethodDecl(Sym.Decl);
    if ACall.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Nested procedure ''%s'' expects %d argument(s), got %d',
          [ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
      Self.AnalyseArgSlot(ACall.Args, I);
    ResolveDeferredArrowArgs(ACall.Args, MDecl);
    ACall.ResolvedDecl := MDecl;
    Exit;
  end;

  { For user-defined procs/funcs, validate arg count and types.
    Phase B: analyse all args FIRST so overload resolution can score
    them by type, then re-validate the chosen overload's parameter
    modes (var/out arguments). }
  Idx := FProcIndex.IndexOf(ACall.Name);
  if Idx >= 0 then
  begin
    { Steer a bare shared enum member to the enum this proc expects before
      bottom-up analysis pins it by last-wins. }
    HintBareEnumArgs(ACall.Name, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
      Self.AnalyseArgSlot(ACall.Args, I);

    MDecl := ResolveStandaloneOverload(ACall.Name, ACall.Args.Count,
      ACall.Args, ACall.Line, ACall.Col);
    ResolveDeferredArrowArgs(ACall.Args, MDecl);
    if MDecl = nil then
      SemanticError(
        Format('No matching overload for ''%s'' with %d argument(s)',
          [ACall.Name, ACall.Args.Count]),
        ACall.Line, ACall.Col);

    for I := 0 to ACall.Args.Count - 1 do
    begin
      if I >= MDecl.Params.Count then Break;   { varargs extras }
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        { Var argument must be an L-value: simple ident, field access,
          pointer-deref-then-field (P^.F), or pointer deref (P^). }
        if not IsVarArgLValue(TASTExpr(ACall.Args.Items[I])) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable',
              [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
        WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[I]));
        ArgType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('var argument %d of ''%s''', [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      end;
      { Non-var argument compatibility was verified by overload scoring;
        no second CheckTypesMatch needed here. }
    end;
    RetypeSetLiteralArgs(ACall.Args, MDecl);
    if MDecl.IsVarArgs then
      ValidateVarArgsExtras(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
    AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
    ACall.ResolvedDecl := MDecl;
  end
  else
  begin
    { GetMem / ReallocMem are FUNCTIONS in Blaise (BUG-035): the classic
      Delphi/FPC procedure forms — GetMem(P, N), ReallocMem(P, N) — are
      deliberately not supported, and calling either in statement position
      always discards the pointer it returns.  Reject here so neither
      backend ever sees the call (the QBE backend raised a generic
      'Unknown procedure'; the native backend dereferenced the nil
      ResolvedDecl and crashed the compiler). }
    if SameText(ACall.Name, 'GetMem') or SameText(ACall.Name, 'ReallocMem') then
      SemanticError(
        Format('''%s'' is a function — assign its result, e.g. P := %s(...)',
          [ACall.Name, ACall.Name]),
        ACall.Line, ACall.Col);
    { FreeMem takes exactly one argument; the Delphi FreeMem(P, Size) form
      is not supported (the allocator's block header knows the size). }
    if SameText(ACall.Name, 'FreeMem') and (ACall.Args.Count <> 1) then
      SemanticError('FreeMem requires exactly 1 argument',
        ACall.Line, ACall.Col);
    { Inc(x) / Inc(x, n) / Dec(x) / Dec(x, n) — in-place add/sub }
    if SameText(ACall.Name, 'Inc') or SameText(ACall.Name, 'Dec') then
    begin
      if (ACall.Args.Count < 1) or (ACall.Args.Count > 2) then
        SemanticError(
          Format('''%s'' requires 1 or 2 arguments', [ACall.Name]),
          ACall.Line, ACall.Col);
      Self.AnalyseListSlot(ACall.Args, 0);
      WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[0]));
      if ACall.Args.Count = 2 then
        Self.AnalyseListSlot(ACall.Args, 1);
    end
    else
    { Include(S, elem) / Exclude(S, elem): validate arg count and types }
    if SameText(ACall.Name, 'Include') or SameText(ACall.Name, 'Exclude') then
    begin
      if ACall.Args.Count <> 2 then
        SemanticError(
          Format('''%s'' requires exactly 2 arguments', [ACall.Name]),
          ACall.Line, ACall.Col);
      ArgType := Self.AnalyseListSlot(ACall.Args, 0);
      if ArgType.Kind <> tySet then
        SemanticError(
          Format('First argument of ''%s'' must be a set variable, got ''%s''',
            [ACall.Name, ArgType.Name]),
          ACall.Line, ACall.Col);
      WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[0]));
      if ACall.Args.Count >= 2 then
      begin
        ArgType := Self.AnalyseListSlot(ACall.Args, 1);
        if TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind = tySet then
        begin
          if TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).BaseType.Kind
             in [tyByte, tyBoolean] then
          begin
            { Ordinal-base set: accept a numeric ordinal, and a Boolean operand
              for a Boolean-base set (Include(s, True)). }
            if not (ArgType.IsNumeric() or
                    ((TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).BaseType.Kind = tyBoolean) and
                     (ArgType.Kind = tyBoolean))) then
              SemanticError(
                Format('Second argument of ''%s'' must be ordinal for ''set of %s'', got ''%s''',
                  [ACall.Name,
                   TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).BaseType.Name,
                   ArgType.Name]),
                ACall.Line, ACall.Col);
          end
          else if ArgType <> TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).BaseType then
            SemanticError(
              Format('Second argument of ''%s'' must be type ''%s'', got ''%s''',
                [ACall.Name,
                 TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).BaseType.Name,
                 ArgType.Name]),
              ACall.Line, ACall.Col);
        end;
      end;
    end
    else
    if SameText(ACall.Name, 'Delete') then
    begin
      { Delete(var S: string; Idx, Count: Integer) — string mutator. }
      if ACall.Args.Count <> 3 then
        SemanticError('Delete requires exactly 3 arguments',
          ACall.Line, ACall.Col);
      ArgType := Self.AnalyseListSlot(ACall.Args, 0);
      if (ArgType = nil) or (ArgType.Kind <> tyString) then
        SemanticError('First argument of ''Delete'' must be a string variable',
          ACall.Line, ACall.Col);
      if not ((TASTExpr(ACall.Args.Items[0]) is TIdentExpr) or
              (TASTExpr(ACall.Args.Items[0]) is TFieldAccessExpr)) then
        SemanticError('First argument of ''Delete'' must be an assignable string',
          ACall.Line, ACall.Col);
      WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[0]));
      Self.AnalyseListSlot(ACall.Args, 1);
      Self.AnalyseListSlot(ACall.Args, 2);
    end
    else
    if SameText(ACall.Name, 'SetLength') then
    begin
      { SetLength(var S: string; N: Integer) — string truncate/grow.
        SetLength(var A: array of T; N: Integer) — dynamic array resize. }
      if ACall.Args.Count <> 2 then
        SemanticError('SetLength requires exactly 2 arguments',
          ACall.Line, ACall.Col);
      ArgType := Self.AnalyseListSlot(ACall.Args, 0);
      if (ArgType = nil) or not (ArgType.Kind in [tyString, tyDynArray]) then
        SemanticError('First argument of ''SetLength'' must be a string or dynamic array variable',
          ACall.Line, ACall.Col);
      { Accept any addressable l-value: a variable, a field, a pointer deref,
        or an array element — the last enables 2-D dynamic arrays
        (SetLength(m[i], n) resizes the inner array). }
      if not IsVarArgLValue(TASTExpr(ACall.Args.Items[0])) then
        SemanticError('First argument of ''SetLength'' must be an assignable variable',
          ACall.Line, ACall.Col);
      WarnIfVarArgIsForInLoopVar(TASTExpr(ACall.Args.Items[0]));
      Self.AnalyseListSlot(ACall.Args, 1);
    end
    else
    if SameText(ACall.Name, 'Sleep') then
    begin
      if ACall.Args.Count <> 1 then
        SemanticError('Sleep requires exactly 1 argument', ACall.Line, ACall.Col);
      Self.AnalyseListSlot(ACall.Args, 0);
    end
    else
    begin
      { Other built-ins (WriteLn/Write/etc.) — analyse args, then for
        Write/WriteLn specifically reject types that have no text representation. }
      for I := 0 to ACall.Args.Count - 1 do
      begin
        ArgType := Self.AnalyseListSlot(ACall.Args, I);
        if SameText(ACall.Name, 'WriteLn') or SameText(ACall.Name, 'Write') then
        begin
          if (ArgType = nil) or (ArgType.Kind = tyVoid) then
            SemanticError(
              Format('Cannot pass a procedure call result (no return value) to ''%s''',
                [ACall.Name]),
              TASTExpr(ACall.Args.Items[I]).Line,
              TASTExpr(ACall.Args.Items[I]).Col)
          else if ArgType.Kind in [tyProcedural, tyRecord, tyClass, tyInterface,
                                   tyMetaClass, tyStaticArray, tyDynArray,
                                   tyOpenArray, tyPointer, tyNil] then
            SemanticError(
              Format('Cannot pass a value of type ''%s'' to ''%s''',
                [ArgType.Name, ACall.Name]),
              TASTExpr(ACall.Args.Items[I]).Line,
              TASTExpr(ACall.Args.Items[I]).Col);
        end;
      end;
    end;
  end;
end;

function TSemanticAnalyser.AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
var
  Sym:     TSymbol;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  Idx:     Integer;
  I:       Integer;
  PT:      TProceduralTypeDesc;
  PPar:    TProcParamInfo;
  FldInfo: TFieldInfo;
begin
  { HasClassAttribute(AClass, AAttrClass): Boolean — runtime query of the custom
    attribute RTTI stored in slot 7 of the class's typeinfo.  Both arguments
    must be metaclass expressions (bare class names).  Lowers to a call to
    $_HasClassAttribute(l typeinfo_class, l typeinfo_attr). }
  if SameText(AExpr.Name, 'HasClassAttribute') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('HasClassAttribute requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    if (TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil) or
       not (TASTExpr(AExpr.Args.Items[0]).ResolvedType.Kind in [tyClass, tyMetaClass]) then
      SemanticError('HasClassAttribute: first argument must be a class type reference',
        AExpr.Line, AExpr.Col);
    if (TASTExpr(AExpr.Args.Items[1]).ResolvedType = nil) or
       not (TASTExpr(AExpr.Args.Items[1]).ResolvedType.Kind in [tyClass, tyMetaClass]) then
      SemanticError('HasClassAttribute: second argument must be an attribute class reference',
        AExpr.Line, AExpr.Col);
    AExpr.IsBuiltinHasClassAttr := True;
    AExpr.ResolvedType := FTable.TypeBoolean;
    Exit(AExpr.ResolvedType);
  end;

  { Attribute-RTTI builtins over the reified attribute tables in typeinfo
    (class attrs at slot 7 as (typeinfo, thunk) pairs; method attrs at slot 8
    as (name, typeinfo, thunk) triples):

      GetClassAttribute(AClass, AAttrClass): TObject
      HasMethodAttribute(AClass, AMethodName, AAttrClass): Boolean
      GetMethodAttribute(AClass, AMethodName, AAttrClass): TObject
      MethodAttributeCount(AClass, AMethodName): Integer
      GetMethodAttributeAt(AClass, AMethodName, AIndex): TObject

    Class arguments are metaclass expressions lowering to typeinfo pointers;
    method names are ordinary strings compared against the published-method
    name entries.  The Get* forms construct a FRESH attribute instance on
    every call by invoking the stored factory thunk (nil when absent);
    callers narrow the TObject result with 'is'/'as'.  Each lowers to the
    same-named runtime helper prefixed '_'. }
  if SameText(AExpr.Name, 'GetClassAttribute') or
     SameText(AExpr.Name, 'HasMethodAttribute') or
     SameText(AExpr.Name, 'GetMethodAttribute') or
     SameText(AExpr.Name, 'MethodAttributeCount') or
     SameText(AExpr.Name, 'GetMethodAttributeAt') then
  begin
    if SameText(AExpr.Name, 'GetClassAttribute') or
       SameText(AExpr.Name, 'MethodAttributeCount') then
      Idx := 2
    else
      Idx := 3;
    if AExpr.Args.Count <> Idx then
      SemanticError(Format('%s requires exactly %d arguments',
        [AExpr.Name, Idx]), AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    { Arg 0 is always the queried class. }
    if (TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil) or
       not (TASTExpr(AExpr.Args.Items[0]).ResolvedType.Kind in [tyClass, tyMetaClass]) then
      SemanticError(AExpr.Name + ': first argument must be a class type reference',
        AExpr.Line, AExpr.Col);
    if SameText(AExpr.Name, 'GetClassAttribute') then
    begin
      if (TASTExpr(AExpr.Args.Items[1]).ResolvedType = nil) or
         not (TASTExpr(AExpr.Args.Items[1]).ResolvedType.Kind in [tyClass, tyMetaClass]) then
        SemanticError(AExpr.Name + ': second argument must be an attribute class reference',
          AExpr.Line, AExpr.Col);
    end
    else
    begin
      { Method-attr forms: arg 1 is the method name string. }
      if (TASTExpr(AExpr.Args.Items[1]).ResolvedType = nil) or
         (TASTExpr(AExpr.Args.Items[1]).ResolvedType.Kind <> tyString) then
        SemanticError(AExpr.Name + ': second argument must be a method name string',
          AExpr.Line, AExpr.Col);
      if SameText(AExpr.Name, 'HasMethodAttribute') or
         SameText(AExpr.Name, 'GetMethodAttribute') then
      begin
        if (TASTExpr(AExpr.Args.Items[2]).ResolvedType = nil) or
           not (TASTExpr(AExpr.Args.Items[2]).ResolvedType.Kind in [tyClass, tyMetaClass]) then
          SemanticError(AExpr.Name + ': third argument must be an attribute class reference',
            AExpr.Line, AExpr.Col);
      end
      else if SameText(AExpr.Name, 'GetMethodAttributeAt') then
      begin
        if (TASTExpr(AExpr.Args.Items[2]).ResolvedType = nil) or
           not (TASTExpr(AExpr.Args.Items[2]).ResolvedType.Kind in
                [tyInteger, tyInt64, tyByte, tySmallInt, tyWord, tyUInt32]) then
          SemanticError(AExpr.Name + ': third argument must be an integer index',
            AExpr.Line, AExpr.Col);
      end;
    end;
    { Canonical spelling — codegen appends this to '_' to name the runtime
      helper symbol, so the user's (case-insensitive) spelling must not
      leak through. }
    if SameText(AExpr.Name, 'GetClassAttribute') then
      AExpr.AttrRTTIBuiltin := 'GetClassAttribute'
    else if SameText(AExpr.Name, 'HasMethodAttribute') then
      AExpr.AttrRTTIBuiltin := 'HasMethodAttribute'
    else if SameText(AExpr.Name, 'GetMethodAttribute') then
      AExpr.AttrRTTIBuiltin := 'GetMethodAttribute'
    else if SameText(AExpr.Name, 'MethodAttributeCount') then
      AExpr.AttrRTTIBuiltin := 'MethodAttributeCount'
    else
      AExpr.AttrRTTIBuiltin := 'GetMethodAttributeAt';
    if SameText(AExpr.Name, 'HasMethodAttribute') then
      AExpr.ResolvedType := FTable.TypeBoolean
    else if SameText(AExpr.Name, 'MethodAttributeCount') then
      AExpr.ResolvedType := FTable.TypeInteger
    else
    begin
      AExpr.ResolvedType := FTable.FindType('TObject');
      if AExpr.ResolvedType = nil then
        SemanticError(AExpr.Name + ': TObject type not available', AExpr.Line, AExpr.Col);
    end;
    Exit(AExpr.ResolvedType);
  end;

  { SizeOf(TypeName) or SizeOf(expression) — compile-time byte size,
    returns Integer.  The codegen reads Args[0].ResolvedType.ByteSize and
    emits a literal, so the argument is never evaluated at runtime. }
  if SameText(AExpr.Name, 'SizeOf') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('SizeOf requires exactly one argument', AExpr.Line, AExpr.Col);
    Sym := nil;
    if AExpr.Args.Items[0] is TIdentExpr then
      Sym := FTable.Lookup(TIdentExpr(AExpr.Args.Items[0]).Name);
    if (Sym <> nil) and (Sym.Kind = skType) then
      TIdentExpr(AExpr.Args.Items[0]).ResolvedType := Sym.TypeDesc
    else
      Self.AnalyseListSlot(AExpr.Args, 0);
    if TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil then
      SemanticError('SizeOf argument must be a type or typed expression',
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'PChar') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('PChar requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    if not (ArgType.Kind in [tyString, tyPChar, tyPointer]) then
      SemanticError(
        Format('PChar cast requires a string, PChar, or Pointer expression, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypePChar;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Pointer(intOrPtrExpr) — reinterpret any integer or pointer value as
    an untyped Pointer.  Integer sources are treated as raw addresses (no
    sign-extension guarantee beyond what the source type provides). }
  if SameText(AExpr.Name, 'Pointer') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Pointer cast requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    if not (ArgType.Kind in [tyInteger, tyInt64, tyUInt64, tyUInt32, tyByte,
                              tySmallInt, tyWord, tyPointer, tyPChar, tyString,
                              tyClass, tyMetaClass, tyProcedural, tyNil]) then
      SemanticError(
        Format('Pointer cast requires an integer, pointer, or class expression, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypePointer;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { PtrUInt(intOrPtrExpr) — reinterpret any integer or pointer value as
    a pointer-sized unsigned integer (UInt64 on 64-bit targets).  The
    primary use is arithmetic on pointer values without signed overflow. }
  if SameText(AExpr.Name, 'PtrUInt') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('PtrUInt cast requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    if not (ArgType.Kind in [tyInteger, tyInt64, tyUInt64, tyUInt32, tyByte,
                              tySmallInt, tyWord, tyPointer, tyPChar, tyString,
                              tyClass, tyNil]) then
      SemanticError(
        Format('PtrUInt cast requires an integer, pointer, or class expression, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeUInt64;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'string') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('string() requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    if ArgType.Kind <> tyPChar then
      SemanticError(
        Format('string() cast requires a PChar expression, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'High') or SameText(AExpr.Name, 'Low') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument',
        AExpr.Line, AExpr.Col);
    { Accept either a type-name identifier (e.g. High(Integer)) or a typed
      expression (e.g. High(SomeVar)).  For type-name form, record the type
      on the argument node so codegen can read ResolvedType directly. }
    Sym := nil;
    if AExpr.Args.Items[0] is TIdentExpr then
      Sym := FTable.Lookup(TIdentExpr(AExpr.Args.Items[0]).Name);
    if (Sym <> nil) and (Sym.Kind = skType) then
    begin
      ArgType := Sym.TypeDesc;
      TIdentExpr(AExpr.Args.Items[0]).ResolvedType := ArgType;
    end
    else
      ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    if ArgType = nil then
      SemanticError(AExpr.Name + ' argument has no resolved type',
        AExpr.Line, AExpr.Col);
    if ArgType.IsFloat() then
      SemanticError(AExpr.Name +
        ' is not defined for floating-point types; use MaxDouble/MinDouble or Math.Infinity',
        AExpr.Line, AExpr.Col);
    if ArgType.Kind in [tyOpenArray, tyStaticArray, tyDynArray, tyString] then
    begin
      { Index-bound form: result is Integer (existing behaviour). }
      Result := FTable.TypeInteger;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    if ArgType.IsOrdinal() then
    begin
      { Ordinal-bound form: result type is the argument's own type. }
      Result := ArgType;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    SemanticError(AExpr.Name +
      ' argument must be an ordinal type, array, or string',
      AExpr.Line, AExpr.Col);
  end;

  { Succ(x)/Pred(x): the next/previous value of an ordinal (enum or integer
    family).  Result keeps the argument's type, so Succ(enum) is still that
    enum.  Codegen lowers to +1 / -1 on the ordinal value.  Handled here,
    before the symbol lookup, since these are builtins with no symbol. }
  if SameText(AExpr.Name, 'Succ') or SameText(AExpr.Name, 'Pred') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('%s requires exactly 1 argument', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
    Result := Self.AnalyseListSlot(AExpr.Args, 0);
    if (Result = nil) or
       not ((Result.Kind = tyEnum) or Result.IsNumeric()) then
      SemanticError(
        Format('%s requires an ordinal (enum or integer) argument', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Resolution order: see AnalyseProcCall for the matching pattern.
    Local vars/parameters win over implicit-Self method, which wins
    over unit-level. }
  Sym := FTable.Lookup(AExpr.Name);
  { A program-level global does not shadow an implicit-Self method — see
    the matching note in AnalyseProcCall (BUG-037). }
  if (FCurrentClass <> nil) and
     ((Sym = nil) or
      (Sym.IsGlobal) or
      not (Sym.Kind in [skVariable, skParameter, skVarParameter])) then
  begin
    MDecl := FindMethodDecl(FCurrentClass.Name, AExpr.Name);
    if MDecl <> nil then
    begin
      { Analyse args first so overload resolution can score by type
        ('->' lambda args are deferred and scored by shape — Phase 9b). }
      HintBareEnumMethodArgs(FCurrentClass.Name, AExpr.Name, AExpr.Args);
      for I := 0 to AExpr.Args.Count - 1 do
        Self.AnalyseArgSlot(AExpr.Args, I);
      MDecl := ResolveMethodOverload(FCurrentClass.Name, AExpr.Name,
        AExpr.Args, AExpr.Line, AExpr.Col);
      if MDecl = nil then
        SemanticError(
          Format('No matching overload for ''%s.%s'' with %d argument(s)',
            [FCurrentClass.Name, AExpr.Name, AExpr.Args.Count]),
          AExpr.Line, AExpr.Col);
      ResolveDeferredArrowArgs(AExpr.Args, MDecl);
      for I := 0 to AExpr.Args.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[I]);
        if Par.IsVarParam then
        begin
          if not IsVarArgLValue(TASTExpr(AExpr.Args.Items[I])) then
            SemanticError(
              Format('var argument %d of ''%s'' must be a variable',
                [I + 1, AExpr.Name]),
              AExpr.Line, AExpr.Col);
          ArgType := TASTExpr(AExpr.Args.Items[I]).ResolvedType;
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('var argument %d of ''%s''', [I + 1, AExpr.Name]),
            AExpr.Line, AExpr.Col);
          WarnIfVarArgIsForInLoopVar(TASTExpr(AExpr.Args.Items[I]));
        end;
      end;
      { Set-literal args: see BUG-20260722-native-set-literal-arg. }
      RetypeSetLiteralArgs(AExpr.Args, MDecl);
      AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
      AExpr.ResolvedDecl         := MDecl;
      AExpr.IsImplicitSelfMethod := True;
      Result := MDecl.ResolvedReturnType;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    { No method of that name — an unqualified procedural-typed field of the
      current class (implicit Self.Field) called as an expression dispatches
      through its stored pointer and yields the signature's return type. }
    FldInfo := FCurrentClass.FindField(AExpr.Name);
    if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
       (FldInfo.TypeDesc.Kind = tyProcedural) then
    begin
      PT := TProceduralTypeDesc(FldInfo.TypeDesc);
      if AExpr.Args.Count <> PT.Params.Count then
        SemanticError(Format(
          'Indirect call ''%s'' expects %d argument(s), got %d',
          [AExpr.Name, PT.Params.Count, AExpr.Args.Count]),
          AExpr.Line, AExpr.Col);
      for I := 0 to AExpr.Args.Count - 1 do
      begin
        PPar    := TProcParamInfo(PT.Params.Items[I]);
        ArgType := AnalyseExprHinted(TASTExpr(AExpr.Args.Items[I]), PPar.TypeDesc);
        if PPar.IsVarParam and
           not IsVarArgLValue(TASTExpr(AExpr.Args.Items[I])) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable',
              [I + 1, AExpr.Name]),
            AExpr.Line, AExpr.Col);
        if PPar.IsVarParam then
          WarnIfVarArgIsForInLoopVar(TASTExpr(AExpr.Args.Items[I]));
        CheckTypesMatch(PPar.TypeDesc, ArgType,
          Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      end;
      AExpr.IsProcFieldCall  := True;
      AExpr.ProcFieldInfo    := FldInfo;
      AExpr.ResolvedProcType := FldInfo.TypeDesc;
      Result := PT.ReturnType;
      AExpr.ResolvedType := Result;
      Exit;
    end;
  end;
  { Try on-demand instantiation of a generic function }
  if StrPos('<', AExpr.Name) >= 0 then
  begin
    InstantiateGenericFunc(AExpr.Name);
    Sym := FTable.Lookup(AExpr.Name);
  end;
  if Sym = nil then
    SemanticError(
      Format('Undeclared function ''%s''', [AExpr.Name]),
      AExpr.Line, AExpr.Col);
  AExpr.Name := Sym.Name;  { normalise to declared casing }
  { Type cast: TypeName(Expr) — single-argument call to a type name }
  if Sym.Kind = skType then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(
        Format('Type cast ''%s'' expects exactly one argument', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    { Byte(','), Word('A'), ...: an integer cast of a string LITERAL
      means the character code (Ord semantics).  Without this fold the
      backends reinterpret the literal's pointer — silent garbage.
      CoerceToCharOrd rejects literals that are not exactly one byte. }
    if (Sym.TypeDesc <> nil) and
       (Sym.TypeDesc.Kind in [tyInteger, tyInt64, tyUInt32, tyUInt64,
                              tySmallInt, tyWord, tyByte]) and
       (TASTExpr(AExpr.Args.Items[0]) is TStringLiteral) then
      CoerceToCharOrd(TStringLiteral(AExpr.Args.Items[0]));
    Result := Sym.TypeDesc;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Indirect call through a procedural-typed variable: F() where F is
    declared 'var F: TIntFn'.  The call dispatches through the function
    pointer stored in F. }
  if (Sym.Kind in [skVariable, skParameter, skVarParameter]) and
     (Sym.TypeDesc <> nil) and (Sym.TypeDesc.Kind = tyProcedural) then
  begin
    AExpr.IsIndirectCall       := True;
    AExpr.IndirectCallIsGlobal := Sym.IsGlobal;
    AExpr.ResolvedProcType     := Sym.TypeDesc;
    { Validate arg count + types against the signature. }
    PT := TProceduralTypeDesc(Sym.TypeDesc);
    if AExpr.Args.Count <> PT.Params.Count then
      SemanticError(Format(
        'Indirect call ''%s'' expects %d argument(s), got %d',
        [AExpr.Name, PT.Params.Count, AExpr.Args.Count]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
    begin
      PPar    := TProcParamInfo(PT.Params.Items[I]);
      ArgType := AnalyseExprHinted(TASTExpr(AExpr.Args.Items[I]), PPar.TypeDesc);
      if PPar.IsVarParam and
         not IsVarArgLValue(TASTExpr(AExpr.Args.Items[I])) then
        SemanticError(
          Format('var argument %d of ''%s'' must be a variable',
            [I + 1, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      if PPar.IsVarParam then
        WarnIfVarArgIsForInLoopVar(TASTExpr(AExpr.Args.Items[I]));
      CheckTypesMatch(PPar.TypeDesc, ArgType,
        Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    end;
    Result := PT.ReturnType;
    if Result = nil then
      Result := FTable.TypeVoid;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if Sym.Kind <> skFunction then
    SemanticError(
      Format('''%s'' is not a function', [AExpr.Name]),
      AExpr.Line, AExpr.Col);

  { Built-in memory functions: GetMem / ReallocMem.  Arity-checked here
    (BUG-035): a wrong-arity call used to sail through to the backends,
    where no intrinsic case matched and the fall-through misfired. }
  if SameText(AExpr.Name, 'GetMem') or SameText(AExpr.Name, 'ReallocMem') then
  begin
    if SameText(AExpr.Name, 'GetMem') and (AExpr.Args.Count <> 1) then
      SemanticError('GetMem requires exactly 1 argument (the byte count)',
        AExpr.Line, AExpr.Col);
    if SameText(AExpr.Name, 'ReallocMem') and (AExpr.Args.Count <> 2) then
      SemanticError(
        'ReallocMem requires exactly 2 arguments (pointer, new byte count)',
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    Result := FTable.TypePointer;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Built-in string functions — validate arg count and first-arg type,
    then set return type.  These call RTL functions at runtime. }
  if SameText(AExpr.Name, 'Length') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Length requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    if not (ArgType.Kind in [tyString, tyOpenArray, tyStaticArray, tyDynArray]) then
      SemanticError('Length argument must be a string or array', AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Pos') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('Pos requires exactly two arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'PosEx') then
  begin
    if AExpr.Args.Count <> 3 then
      SemanticError('PosEx requires exactly three arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Self.AnalyseListSlot(AExpr.Args, 2);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Copy') then
  begin
    if AExpr.Args.Count <> 3 then
      SemanticError('Copy requires exactly three arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Self.AnalyseListSlot(AExpr.Args, 2);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'UpperCase') or SameText(AExpr.Name, 'LowerCase')
     or SameText(AExpr.Name, 'Trim') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'SameText') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('SameText requires exactly two arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'IntToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('IntToStr requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Assigned') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Assigned requires exactly one argument',
        AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    if (ArgType = nil) or
       not (ArgType.Kind in [tyPointer, tyPChar, tyClass, tyInterface,
                             tyString, tyProcedural]) then
      SemanticError(
        Format('Assigned requires a pointer/class/interface/proc argument, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Int64ToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Int64ToStr requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'UInt64ToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('UInt64ToStr requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'DoubleToStr') or SameText(AExpr.Name, 'SingleToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'StrToDouble') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('StrToDouble requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeDouble;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Abs') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Abs requires exactly one argument', AExpr.Line, AExpr.Col);
    Result := Self.AnalyseListSlot(AExpr.Args, 0);
    if not Result.IsNumeric() then
      SemanticError(Format('Abs requires a numeric argument, got ''%s''', [Result.Name]),
        AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;  { return type matches argument type }
    Exit;
  end;

  { Math builtins — Sqrt, Ceil, Floor, Round, Trunc, Ln, Log2, Log10,
    Power, Sin, Cos, Tan, ArcTan, ArcTan2, IsNaN, IsInfinite.
    These are implemented as compiler builtins rather than RTL functions
    so that the codegen can emit dtosi/stosi for the float→integer
    conversions (Ceil/Floor/Round/Trunc) and can dispatch to the *f
    variants for Single arguments on the trig functions.
    Integer-family arguments are accepted and implicitly widened to
    Double (FloatBuiltinArgType) — matching FPC/Delphi and Blaise's own
    implicit int→float assignment rule.
    Min and Max are implemented in pure Pascal in math.pas because they
    are handled correctly by normal overload resolution. }

  if SameText(AExpr.Name, 'Sqrt') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Sqrt requires exactly one argument', AExpr.Line, AExpr.Col);
    Result := Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FloatBuiltinArgType(AExpr.Name, Result, AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Ceil') or SameText(AExpr.Name, 'Floor') or
     SameText(AExpr.Name, 'Round') or SameText(AExpr.Name, 'Trunc') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    FloatBuiltinArgType(AExpr.Name, ArgType, AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Ln') or SameText(AExpr.Name, 'Log2') or
     SameText(AExpr.Name, 'Log10') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    FloatBuiltinArgType(AExpr.Name, ArgType, AExpr.Line, AExpr.Col);
    Result := FTable.TypeDouble;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Power') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('Power requires exactly two arguments', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    FloatBuiltinArgType(AExpr.Name, ArgType, AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 1);
    FloatBuiltinArgType(AExpr.Name, ArgType, AExpr.Line, AExpr.Col);
    Result := FTable.TypeDouble;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Sin') or SameText(AExpr.Name, 'Cos') or
     SameText(AExpr.Name, 'Tan') or SameText(AExpr.Name, 'ArcTan') or
     SameText(AExpr.Name, 'ArcSin') or SameText(AExpr.Name, 'ArcCos') or
     SameText(AExpr.Name, 'Sinh') or SameText(AExpr.Name, 'Cosh') or
     SameText(AExpr.Name, 'Tanh') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    Result := Self.AnalyseListSlot(AExpr.Args, 0);
    { Return type matches argument type — Single→Single, Double→Double,
      integer→Double. }
    Result := FloatBuiltinArgType(AExpr.Name, Result, AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ArcTan2') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('ArcTan2 requires exactly two arguments', AExpr.Line, AExpr.Col);
    Result := Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FloatBuiltinArgType(AExpr.Name, Result, AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 1);
    FloatBuiltinArgType(AExpr.Name, ArgType, AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;  { return type matches first argument type }
    Exit;
  end;

  if SameText(AExpr.Name, 'IsNaN') or SameText(AExpr.Name, 'IsInfinite') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := Self.AnalyseListSlot(AExpr.Args, 0);
    FloatBuiltinArgType(AExpr.Name, ArgType, AExpr.Line, AExpr.Col);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'StrToInt') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('StrToInt requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { MethodAddress(Obj, Name): walks the object's typeinfo chain looking for
    a published method named 'Name'.  Returns nil when not found.  Used by
    blaise.testing's RegisterTest path to dispatch test methods by name. }
  if SameText(AExpr.Name, 'MethodAddress') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('MethodAddress requires exactly two arguments (Obj, Name)',
        AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    if (TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil) or
       (TASTExpr(AExpr.Args.Items[0]).ResolvedType.Kind <> tyClass) then
      SemanticError('MethodAddress: first argument must be a class instance',
        AExpr.Line, AExpr.Col);
    if (TASTExpr(AExpr.Args.Items[1]).ResolvedType = nil) or
       (TASTExpr(AExpr.Args.Items[1]).ResolvedType.Kind <> tyString) then
      SemanticError('MethodAddress: second argument must be a string',
        AExpr.Line, AExpr.Col);
    Result := FTable.TypePointer;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'StrToInt64') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('StrToInt64 requires exactly one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeInt64;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { ClassCreate(Cls, ...args): runtime construction from a metaclass.
    Resolves the constructor on Cls.BaseClass with the supplied args
    and stores the TMethodDecl on AExpr.ResolvedDecl.  Codegen lowers
    this to '%p = call $_ClassCreate(l <classvalue>); call $T_Create(l %p, args...)'.
    Result type is the BaseClass — assigning to a 'var T: TFoo' is
    well-typed when Cls: class of TFoo. }
  if SameText(AExpr.Name, 'ClassCreate') then
  begin
    if AExpr.Args.Count < 1 then
      SemanticError('ClassCreate requires a metaclass as the first argument',
        AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    if (TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil) or
       (TASTExpr(AExpr.Args.Items[0]).ResolvedType.Kind <> tyMetaClass) then
      SemanticError('ClassCreate: first argument must be a metaclass (class of T) value',
        AExpr.Line, AExpr.Col);
    { Analyse remaining args before resolving the constructor — argument
      types feed FindMethodDecl when we add overload resolution; for v0
      we look up 'Create' by name and trust uniqueness. }
    for I := 1 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    Result := TMetaClassTypeDesc(TASTExpr(AExpr.Args.Items[0]).ResolvedType).BaseClass;
    AExpr.ResolvedType := Result;
    AExpr.ResolvedDecl := FindMethodDecl(Result.Name, 'Create');
    Exit;
  end;

  if SameText(AExpr.Name, 'Format') then
  begin
    if AExpr.Args.Count < 1 then
      SemanticError('Format requires at least one argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    { When the second arg is an array literal (Pascal 'array of const' notation),
      analyse each element individually — types need not be homogeneous. }
    if (AExpr.Args.Count = 2) and (AExpr.Args.Items[1] is TArrayLiteralExpr) then
    begin
      for I := 0 to TArrayLiteralExpr(AExpr.Args.Items[1]).Elements.Count - 1 do
        AnalyseExpr(TASTExpr(TArrayLiteralExpr(AExpr.Args.Items[1]).Elements.Items[I]));
      TArrayLiteralExpr(AExpr.Args.Items[1]).ResolvedType := FTable.TypeString;
    end
    else
      for I := 1 to AExpr.Args.Count - 1 do
        Self.AnalyseListSlot(AExpr.Args, I);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'OrdAt') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('OrdAt requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Ord') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Ord requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Chr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Chr requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'UpCase') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('UpCase requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'CompareStr') or SameText(AExpr.Name, 'CompareText') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError(AExpr.Name + ' requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { CLI arguments }
  if SameText(AExpr.Name, 'ParamCount') or
     SameText(AExpr.Name, 'GetProcessID') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError(Format('''%s'' takes no arguments', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'GetTempDir') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('GetTempDir takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'GetCurrentDir') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('GetCurrentDir() takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'GetTempFileName') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('GetTempFileName requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ParamStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ParamStr requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { File I/O functions }
  if SameText(AExpr.Name, 'ReadFile') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ReadFile requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'FileExists') or
     SameText(AExpr.Name, 'DirectoryExists') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'FileAge') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('FileAge requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeInt64;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ForceDirectories') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ForceDirectories requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Environment and process functions }
  if SameText(AExpr.Name, 'GetEnvVar') or
     SameText(AExpr.Name, 'GetEnvironmentVariable') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Exec') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Exec requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { File path manipulation }
  if SameText(AExpr.Name, 'ChangeFileExt') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('ChangeFileExt requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ExtractFileName') or
     SameText(AExpr.Name, 'ExtractFilePath') or
     SameText(AExpr.Name, 'ExtractFileDir') or
     SameText(AExpr.Name, 'ExtractFileExt') or
     SameText(AExpr.Name, 'IncludeTrailingPathDelimiter') or
     SameText(AExpr.Name, 'ExcludeTrailingPathDelimiter') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'RenameFile') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('RenameFile requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Self.AnalyseListSlot(AExpr.Args, 1);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'SetCurrentDir') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('SetCurrentDir requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Process management built-ins }
  if SameText(AExpr.Name, 'ProcessCreate') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('ProcessCreate takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypePointer;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ProcessRunning') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ProcessRunning requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ProcessReadOutput') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ProcessReadOutput requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ProcessExitCode') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ProcessExitCode requires exactly 1 argument', AExpr.Line, AExpr.Col);
    Self.AnalyseListSlot(AExpr.Args, 0);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Scoped nested routine: a function declared inside another routine's body
    is registered in the symbol table only, never in the global FProcIndex /
    FProcGroups (so same-named nested procs in sibling outer routines do not
    collide as ambiguous overloads).  When the call name misses the global
    index but the scoped Sym carries its backing decl, resolve directly
    against that single decl rather than the overload group. }
  if (FProcIndex.IndexOf(AExpr.Name) < 0) and (Sym <> nil) and
     (Sym.Decl <> nil) and (Sym.Decl is TMethodDecl) then
  begin
    MDecl := TMethodDecl(Sym.Decl);
    HintBareEnumArgs(AExpr.Name, AExpr.Args);
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    if (AExpr.Args.Count < MinArity(MDecl)) or
       (AExpr.Args.Count > MDecl.Params.Count) then
      SemanticError(
        Format('''%s'' expects %d argument(s), got %d',
          [AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        if not IsVarArgLValue(TASTExpr(AExpr.Args.Items[I])) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable',
              [I + 1, AExpr.Name]),
            AExpr.Line, AExpr.Col);
        ArgType := TASTExpr(AExpr.Args.Items[I]).ResolvedType;
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('var argument %d of ''%s''', [I + 1, AExpr.Name]),
          AExpr.Line, AExpr.Col);
        WarnIfVarArgIsForInLoopVar(TASTExpr(AExpr.Args.Items[I]));
      end;
    end;
    RetypeSetLiteralArgs(AExpr.Args, MDecl);
    AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    AExpr.ResolvedDecl := MDecl;
    Result := MDecl.ResolvedReturnType;
    Exit;
  end;

  Idx := FProcIndex.IndexOf(AExpr.Name);
  if Idx < 0 then
    SemanticError(
      Format('Cannot find declaration for function ''%s''', [AExpr.Name]),
      AExpr.Line, AExpr.Col);

  { Phase B: analyse args first, then score overloads by argument type.
    A bare shared enum member is first steered to the enum the target expects
    at its position, so the right ordinal is pinned before bottom-up analysis. }
  HintBareEnumArgs(AExpr.Name, AExpr.Args);
  for I := 0 to AExpr.Args.Count - 1 do
    Self.AnalyseArgSlot(AExpr.Args, I);

  MDecl := ResolveStandaloneOverload(AExpr.Name, AExpr.Args.Count,
    AExpr.Args, AExpr.Line, AExpr.Col);
  if MDecl = nil then
    SemanticError(
      Format('No matching overload for ''%s'' with %d argument(s)',
        [AExpr.Name, AExpr.Args.Count]),
      AExpr.Line, AExpr.Col);
  ResolveDeferredArrowArgs(AExpr.Args, MDecl);

  { Var-param actuals must be L-values with exactly matching types — mirrors
    the statement form (AnalyseProcCall); the expression form skipped this,
    so a non-lvalue slipped through to codegen (BUG-011). }
  for I := 0 to AExpr.Args.Count - 1 do
  begin
    if I >= MDecl.Params.Count then Break;   { varargs extras }
    Par := TMethodParam(MDecl.Params.Items[I]);
    if Par.IsVarParam then
    begin
      if not IsVarArgLValue(TASTExpr(AExpr.Args.Items[I])) then
        SemanticError(
          Format('var argument %d of ''%s'' must be a variable',
            [I + 1, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      WarnIfVarArgIsForInLoopVar(TASTExpr(AExpr.Args.Items[I]));
      ArgType := TASTExpr(AExpr.Args.Items[I]).ResolvedType;
      CheckTypesMatch(Par.ResolvedType, ArgType,
        Format('var argument %d of ''%s''', [I + 1, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    end;
  end;

  RetypeSetLiteralArgs(AExpr.Args, MDecl);
  if MDecl.IsVarArgs then
    ValidateVarArgsExtras(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
  AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
  AExpr.ResolvedDecl := MDecl;
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
var
  ObjSym:   TSymbol;
  RT:       TRecordTypeDesc;
  MDecl:    TMethodDecl;
  Par:      TMethodParam;
  ArgType:  TTypeDesc;
  I:        Integer;
  IntfDesc: TInterfaceTypeDesc;
  ObjType:  TTypeDesc;
  ResolvedObjName: string;
  FldInfo: TFieldInfo;
  FmtCall: TFuncCallExpr;
begin
  { Call on an arbitrary expression (e.g. TCast(x).Method(y)) }
  if AExpr.ObjExpr <> nil then
  begin
    ObjType := Self.AnalyseExprSlot(AExpr.ObjExpr);

    { Built-in InheritsFrom on a Pointer/metaclass/class ObjExpr receiver. }
    if SameText(AExpr.Name, 'InheritsFrom') and (AExpr.Args.Count = 1) and
       (ObjType.Kind in [tyPointer, tyMetaClass, tyClass]) then
    begin
      Self.AnalyseListSlot(AExpr.Args, 0);
      AExpr.IsBuiltinInheritsFrom := True;
      Result := FTable.TypeBoolean;
      AExpr.ResolvedType := Result;
      Exit;
    end;

    if not (ObjType.Kind in [tyClass, tyInterface, tyRecord]) then
      SemanticError(
        Format('Receiver of ''.%s'' must be a class, interface, or record', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
    if ObjType.Kind = tyInterface then
    begin
      IntfDesc := TInterfaceTypeDesc(ObjType);
      if not IntfDesc.HasMethod(AExpr.Name) then
        SemanticError(
          Format('Interface ''%s'' has no method ''%s''',
            [ObjType.Name, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      for I := 0 to AExpr.Args.Count - 1 do
        Self.AnalyseListSlot(AExpr.Args, I);
      ValidateIntfMethodVarArgs(AExpr.Args, IntfDesc,
        AExpr.Name, AExpr.Line, AExpr.Col);
      AExpr.ResolvedClassType := ObjType;
      AExpr.ResolvedMethod    := nil;
      Result := FindTypeOrInstantiate(
        IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
      if Result = nil then Result := FTable.TypeInteger;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    RT := TRecordTypeDesc(ObjType);
    { Analyse args first so overload resolution can score by type
      ('->' lambda args are deferred and scored by shape — Phase 9b). }
    HintBareEnumMethodArgs(RT.Name, AExpr.Name, AExpr.Args);
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseArgSlot(AExpr.Args, I);
    { Built-in TObject.ToString: virtual dispatch via vtable slot 1.
      Only applies to class receivers — record methods named ToString are
      resolved normally and dispatched statically. }
    if SameText(AExpr.Name, 'ToString') and (AExpr.Args.Count = 0) and
       (ObjType.Kind = tyClass) then
    begin
      AExpr.ResolvedClassType := RT;
      AExpr.ResolvedMethod    := nil;
      AExpr.IsBuiltinToString := True;
      Result := FTable.TypeString;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    FMethodOwnerHint := RT.OwningUnit;
      MDecl := ResolveMethodOverload(RT.Name, AExpr.Name, AExpr.Args,
        AExpr.Line, AExpr.Col);
    if MDecl = nil then
    begin
      FldInfo := RT.FindField(AExpr.Name);
      if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
         (FldInfo.TypeDesc.Kind = tyProcedural) then
      begin
        AExpr.IsProcFieldCall   := True;
        AExpr.ProcFieldInfo     := FldInfo;
        AExpr.ResolvedProcType  := FldInfo.TypeDesc;
        AExpr.ResolvedClassType := RT;
        AExpr.ResolvedMethod    := nil;
        { Calling a function-pointer field yields the field signature's return
          type — not nil — so the call can be used as an expression. }
        AExpr.ResolvedType      := TProceduralTypeDesc(FldInfo.TypeDesc).ReturnType;
        Result                  := AExpr.ResolvedType;
        Exit;
      end;
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    end;
    ResolveDeferredArrowArgs(AExpr.Args, MDecl);
    AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    ValidateMethodVarArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    AExpr.ResolvedClassType := RT;
    AExpr.ResolvedMethod    := MDecl;
    Result := MDecl.ResolvedReturnType;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { A unit-qualified receiver type 'Unit.Type.Method' resolves against that
    specific unit's exports (directed lookup), so a constructor on a cross-unit
    same-named type binds to the named unit rather than the flat last-wins
    winner.  Falls back to the normal lookup on a miss. }
  ObjSym := nil;
  if AExpr.QualifierUnit <> '' then
    ObjSym := ResolveQualified(AExpr.QualifierUnit, AExpr.ObjectName);
  if ObjSym = nil then
    ObjSym := FTable.Lookup(AExpr.ObjectName);
  { If the name contains '<' and wasn't found, resolve scope-bound type params
    (e.g. 'TListEnumerator<T>' → 'TListEnumerator<Integer>' when T=Integer is
    in scope) and trigger on-demand instantiation.  Mirrors the field-access
    path so that 'TGen<T>.Create(args)' resolves inside a generic method body.

    The shared method body means we must NOT mutate AExpr.ObjectName — a
    second instantiation with a different concrete arg would then see the
    first instance's resolved name and skip its own substitution. }
  if (ObjSym = nil) and (StrPos('<', AExpr.ObjectName) >= 0) then
  begin
    ResolvedObjName := ResolveScopeBoundTypeParams(AExpr.ObjectName);
    FindTypeOrInstantiate(ResolvedObjName);
    ObjSym := FTable.Lookup(ResolvedObjName);
  end;
  if ObjSym = nil then
  begin
    { Implicit Self.Field.Method — ObjectName is a field of current class.
      Synthesise a receiver expression that reads the field. }
    if FCurrentClass <> nil then
    begin
      ObjType := nil;
      ObjSym  := nil;
      begin
        { Attempt field lookup and rewrite AExpr.ObjExpr to read Self.Field }
        AExpr.ObjExpr := TIdentExpr.Create();
        TIdentExpr(AExpr.ObjExpr).Name := AExpr.ObjectName;
        TIdentExpr(AExpr.ObjExpr).Line := AExpr.Line;
        TIdentExpr(AExpr.ObjExpr).Col  := AExpr.Col;
        try
          ObjType := Self.AnalyseExprSlot(AExpr.ObjExpr);
        except
          AExpr.ObjExpr := nil;
          SemanticError(
            Format('Undeclared identifier ''%s''', [AExpr.ObjectName]),
            AExpr.Line, AExpr.Col);
        end;
      end;
      if (ObjType = nil) or not (ObjType.Kind in [tyClass, tyInterface]) then
      begin
        AExpr.ObjExpr := nil;
        SemanticError(
          Format('Undeclared identifier ''%s''', [AExpr.ObjectName]),
          AExpr.Line, AExpr.Col);
      end;
      AExpr.ObjectName := '';
      if ObjType.Kind = tyInterface then
      begin
        IntfDesc := TInterfaceTypeDesc(ObjType);
        if not IntfDesc.HasMethod(AExpr.Name) then
          SemanticError(
            Format('Interface ''%s'' has no method ''%s''',
              [ObjType.Name, AExpr.Name]),
            AExpr.Line, AExpr.Col);
        for I := 0 to AExpr.Args.Count - 1 do
          Self.AnalyseListSlot(AExpr.Args, I);
        ValidateIntfMethodVarArgs(AExpr.Args, IntfDesc,
          AExpr.Name, AExpr.Line, AExpr.Col);
        AExpr.ResolvedClassType := ObjType;
        AExpr.ResolvedMethod    := nil;
        Result := FindTypeOrInstantiate(
          IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
        if Result = nil then Result := FTable.TypeInteger;
        AExpr.ResolvedType := Result;
        Exit;
      end;
      RT := TRecordTypeDesc(ObjType);
      { Analyse args first so overload resolution can score by type. }
      HintBareEnumMethodArgs(RT.Name, AExpr.Name, AExpr.Args);
      for I := 0 to AExpr.Args.Count - 1 do
        Self.AnalyseListSlot(AExpr.Args, I);
      FMethodOwnerHint := RT.OwningUnit;
        MDecl := ResolveMethodOverload(RT.Name, AExpr.Name, AExpr.Args,
          AExpr.Line, AExpr.Col);
      if MDecl = nil then
      begin
        FldInfo := RT.FindField(AExpr.Name);
        if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
           (FldInfo.TypeDesc.Kind = tyProcedural) then
        begin
          AExpr.IsProcFieldCall   := True;
          AExpr.ProcFieldInfo     := FldInfo;
          AExpr.ResolvedProcType  := FldInfo.TypeDesc;
          AExpr.ResolvedClassType := RT;
          AExpr.ResolvedMethod    := nil;
          { Function-pointer field call yields the signature's return type. }
          AExpr.ResolvedType      := TProceduralTypeDesc(FldInfo.TypeDesc).ReturnType;
          Result                  := AExpr.ResolvedType;
          Exit;
        end;
        SemanticError(
          Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      end;
      AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
      { Validate var/out-param arguments (type compatibility scored by
        overload resolver; only lvalue constraint needs rechecking). }
      for I := 0 to AExpr.Args.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[I]);
        if Par.IsVarParam then
        begin
          if not IsVarArgLValue(TASTExpr(AExpr.Args.Items[I])) then
            SemanticError(
              Format('var argument %d of ''%s'' must be a variable',
                [I + 1, AExpr.Name]),
              AExpr.Line, AExpr.Col);
          ArgType := TASTExpr(AExpr.Args.Items[I]).ResolvedType;
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('var argument %d of ''%s''', [I + 1, AExpr.Name]),
            AExpr.Line, AExpr.Col);
          WarnIfVarArgIsForInLoopVar(TASTExpr(AExpr.Args.Items[I]));
        end;
      end;
      AExpr.ResolvedClassType := RT;
      AExpr.ResolvedMethod    := MDecl;
      Result := MDecl.ResolvedReturnType;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    SemanticError(
      Format('Undeclared identifier ''%s''', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);
  end;

  { Normalise casing on the AST node ONLY when the lookup matched the
    original name case-insensitively.  When the symbol came in via
    scope-bound type-param substitution (e.g. AExpr.ObjectName was
    'TFoo<T>' and we resolved it to 'TFoo<String>'), keep the AST
    name as the template form so a second instantiation that binds T
    to a different concrete type re-runs the same substitution.  The
    resolved name is captured in ResolvedClassType for codegen. }
  if SameText(ObjSym.Name, AExpr.ObjectName) then
    AExpr.ObjectName := ObjSym.Name;

  { TypeName.StaticFunction(args) in expression position — a static (class-level)
    method reached through the class name.  Must be declared static; lowered with
    NO Self.  Checked before the Create-constructor branch so a non-Create static
    method resolves here rather than falling through to "is not a variable". }
  if (ObjSym.Kind = skType) and (ObjSym.TypeDesc <> nil) and
     (ObjSym.TypeDesc.Kind in [tyClass, tyRecord]) and
     not (SameText(AExpr.Name, 'Create') or (StrPos('Create', AExpr.Name) = 0)) then
  begin
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    MDecl := ResolveMethodOverload(ObjSym.Name, AExpr.Name, AExpr.Args,
      AExpr.Line, AExpr.Col);
    if MDecl = nil then
      MDecl := FindMethodDecl(ObjSym.Name, AExpr.Name);
    if MDecl = nil then
      SemanticError(
        Format('Type ''%s'' has no method ''%s''', [ObjSym.Name, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    if not MDecl.IsStatic then
      SemanticError(
        Format('''%s.%s'' is not a static method — call it on an instance',
          [ObjSym.Name, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    { Set-literal args: see BUG-20260722-native-set-literal-arg. }
    RetypeSetLiteralArgs(AExpr.Args, MDecl);
    AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    ValidateMethodVarArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    EnforceMethodVisible(MDecl, AExpr.Line, AExpr.Col);
    AExpr.ResolvedMethod    := MDecl;
    AExpr.ResolvedClassType := ObjSym.TypeDesc;
    AExpr.IsStaticCall      := True;
    Result := MDecl.ResolvedReturnType;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Constructor call with args: TypeName.Create(arg1, arg2, ...) or any
    method on a class type starting with Create (e.g. CreateFmt). }
  if (ObjSym.Kind = skType) and
     (SameText(AExpr.Name, 'Create') or
      (StrPos('Create', AExpr.Name) = 0)) then
  begin
    if ObjSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot construct non-class type ''%s''', [ObjSym.Name]),
        AExpr.Line, AExpr.Col);
    if TRecordTypeDesc(ObjSym.TypeDesc).HasAbstractMethods then
      SemanticError(
        Format('Cannot instantiate abstract class ''%s''', [ObjSym.Name]),
        AExpr.Line, AExpr.Col);
    HintBareEnumMethodArgs(ObjSym.Name, AExpr.Name, AExpr.Args);
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    { Try to find a user-defined constructor method for type checking.
      Use overload resolution so the correct variant is chosen when multiple
      constructors with the same name (e.g. Create) are declared.  Look up
      on the resolved class name (ObjSym.Name) so generic instances pick
      the right concrete method set. }
    MDecl := ResolveMethodOverload(ObjSym.Name, AExpr.Name,
      AExpr.Args, AExpr.Line, AExpr.Col);
    if MDecl = nil then
      MDecl := FindMethodDecl(ObjSym.Name, AExpr.Name);
    { CreateFmt(fmt, [args]) with no declared CreateFmt method desugars to
      Create(Format(fmt, [args])): move the two args into a synthesized
      Format call and re-resolve as a plain Create.  Without this the args
      were silently DROPPED — the raised exception had an empty message
      (BUG-046).  Only the bracket-literal form desugars; a forwarded
      'array of const' param cannot (Format needs the literal). }
    if (MDecl = nil) and SameText(AExpr.Name, 'CreateFmt') and
       (AExpr.Args.Count = 2) and
       (AExpr.Args.Items[1] is TArrayLiteralExpr) then
    begin
      FmtCall := TFuncCallExpr.Create();
      FmtCall.Name := 'Format';
      FmtCall.Line := AExpr.Line;
      FmtCall.Col  := AExpr.Col;
      FmtCall.Args.Add(AExpr.Args.Extract(AExpr.Args.Items[0]));
      FmtCall.Args.Add(AExpr.Args.Extract(AExpr.Args.Items[0]));
      AExpr.Args.Add(FmtCall);   { AExpr.Args now holds just the Format call }
      AExpr.Name := 'Create';
      { the args were analysed as CreateFmt's args, but the synthesized
        Format node is new — analyse it so its string ResolvedType is set
        before overload resolution matches it against Create(string) }
      AnalyseExpr(FmtCall);
      MDecl := ResolveMethodOverload(ObjSym.Name, 'Create',
        AExpr.Args, AExpr.Line, AExpr.Col);
      if MDecl = nil then
        MDecl := FindMethodDecl(ObjSym.Name, 'Create');
    end;
    { Any remaining undeclared Create* variant WITH args is an error — a
      silent arg-drop (as CreateFmt did before the desugar above) is never
      correct.  A parameterless Create* on a class with no user ctor is
      still fine (the implicit default constructor). }
    if (MDecl = nil) and (AExpr.Args.Count > 0) then
      SemanticError(
        Format('No constructor ''%s'' declared on ''%s'' — its arguments ' +
               'would be silently discarded', [AExpr.Name, ObjSym.Name]),
        AExpr.Line, AExpr.Col);
    if MDecl <> nil then
    begin
      { Re-type a bracket-literal argument bound to a `set of` parameter to that
        parameter's set type, exactly as the free-proc / function-call paths do.
        Without this the literal keeps the open-array type it was analysed with
        (no set context at analysis time), and codegen rejects it as an
        unsupported array literal in constructor-argument position. }
      RetypeSetLiteralArgs(AExpr.Args, MDecl);
      AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    end;
    ValidateMethodVarArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    AExpr.ResolvedMethod    := MDecl;
    AExpr.ResolvedClassType := ObjSym.TypeDesc;
    AExpr.IsConstructorCall := True;
    Exit(ObjSym.TypeDesc);
  end;

  if not (ObjSym.Kind in [skVariable, skParameter, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);

  { Built-in InheritsFrom on a Pointer/metaclass receiver.
    Called as AClass.InheritsFrom(BClass) where both sides are typeinfo
    pointers (i.e. TClass = Pointer, or class-of-T metaclass).
    Also handles a tyClass receiver (instance) for uniform usage. }
  if SameText(AExpr.Name, 'InheritsFrom') and (AExpr.Args.Count = 1) and
     (ObjSym.TypeDesc.Kind in [tyPointer, tyMetaClass, tyClass]) then
  begin
    Self.AnalyseListSlot(AExpr.Args, 0);
    AExpr.IsBuiltinInheritsFrom := True;
    AExpr.IsGlobal  := ObjSym.IsGlobal;
    AExpr.IsVarParam :=
      (ObjSym.Kind = skVarParameter) or
      ((ObjSym.Kind = skParameter) and (ObjSym.TypeDesc <> nil) and
       (ObjSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Metaclass-var constructor dispatch: C.Create(args) where C is a
    metaclass variable.  Resolve against the BaseClass and flag for
    indirect ctor dispatch via vtable at codegen time. }
  if (ObjSym.TypeDesc.Kind = tyMetaClass) and
     (SameText(AExpr.Name, 'Create') or (StrPos('Create', AExpr.Name) = 0)) then
  begin
    RT := TRecordTypeDesc(TMetaClassTypeDesc(ObjSym.TypeDesc).BaseClass);
    HintBareEnumMethodArgs(RT.Name, AExpr.Name, AExpr.Args);
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    MDecl := ResolveMethodOverload(RT.Name, AExpr.Name,
      AExpr.Args, AExpr.Line, AExpr.Col);
    if MDecl = nil then
      MDecl := FindMethodDecl(RT.Name, AExpr.Name);
    if MDecl <> nil then
    begin
      RetypeSetLiteralArgs(AExpr.Args, MDecl);
      AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    end;
    ValidateMethodVarArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    AExpr.ResolvedMethod      := MDecl;
    AExpr.ResolvedClassType   := RT;
    AExpr.IsConstructorCall   := True;
    AExpr.IsMetaclassDispatch := True;
    AExpr.IsGlobal            := ObjSym.IsGlobal;
    AExpr.IsVarParam          := (ObjSym.Kind = skVarParameter);
    Exit(RT);
  end;

  if not (ObjSym.TypeDesc.Kind in [tyClass, tyInterface, tyRecord]) then
    SemanticError(
      Format('''%s'' is not a class, interface, or record variable', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);

  { Interface method call expression: dispatch through itab }
  if ObjSym.TypeDesc.Kind = tyInterface then
  begin
    IntfDesc := TInterfaceTypeDesc(ObjSym.TypeDesc);
    if not IntfDesc.HasMethod(AExpr.Name) then
      SemanticError(
        Format('Interface ''%s'' has no method ''%s''',
          [ObjSym.TypeDesc.Name, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      Self.AnalyseListSlot(AExpr.Args, I);
    ValidateIntfMethodVarArgs(AExpr.Args, IntfDesc,
      AExpr.Name, AExpr.Line, AExpr.Col);
    AExpr.ResolvedClassType := ObjSym.TypeDesc;
    AExpr.ResolvedMethod    := nil;  { nil = interface dispatch }
    AExpr.IsGlobal          := ObjSym.IsGlobal;
    AExpr.IsVarParam        :=
      (ObjSym.Kind = skVarParameter) or
      ((ObjSym.Kind = skParameter) and (ObjSym.TypeDesc <> nil) and
       (ObjSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));
    { Look up return type from interface method descriptor }
    Result := FindTypeOrInstantiate(
      IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
    if Result = nil then
      Result := FTable.TypeInteger;  { fallback for void/unknown }
    AExpr.ResolvedType := Result;
    Exit;
  end;

  RT    := TRecordTypeDesc(ObjSym.TypeDesc);
  { Overload-aware resolution: pick the variant matching the argument list
    (merging overloads across the inheritance chain).  Args must be analysed
    first so ResolveMethodOverload can score against their resolved types
    ('->' lambda args are deferred and scored by shape — Phase 9b).
    Fall back to a plain chain lookup for the no-overload / single case. }
  for I := 0 to AExpr.Args.Count - 1 do
    Self.AnalyseArgSlot(AExpr.Args, I);
  { Generic method call obj.Pick<Integer>(...): the parser folded the explicit
    type args into AExpr.Name.  Instantiate the monomorphised method and use it
    directly (it is not part of the overload set). }
  if StrPos('<', AExpr.Name) >= 0 then
  begin
    MDecl := InstantiateGenericMethod(RT.Name, AExpr.Name);
    if MDecl = nil then
      SemanticError(Format('Class ''%s'' has no generic method ''%s''',
        [RT.Name, AExpr.Name]), AExpr.Line, AExpr.Col);
    { Validate the call arguments against the monomorphised signature — the
      instance body was analysed, but the call site's args still need checking
      (unlike the overload path, this path bypasses ResolveMethodOverload). }
    if AExpr.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Method ''%s.%s'' expects %d argument(s) but got %d',
          [RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
        AExpr.Line, AExpr.Col);
    ResolveDeferredArrowArgs(AExpr.Args, MDecl);
    { Set-literal args: see BUG-20260722-native-set-literal-arg. }
    RetypeSetLiteralArgs(AExpr.Args, MDecl);
    for I := 0 to AExpr.Args.Count - 1 do
      CheckTypesMatch(TMethodParam(MDecl.Params.Items[I]).ResolvedType,
        TASTExpr(AExpr.Args.Items[I]).ResolvedType,
        Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    ValidateMethodVarArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    AExpr.ResolvedClassType := RT;
    AExpr.ResolvedMethod    := MDecl;
    AExpr.IsGlobal          := ObjSym.IsGlobal;
    AExpr.IsVarParam        :=
      (ObjSym.Kind = skVarParameter) or
      ((ObjSym.Kind = skParameter) and (ObjSym.TypeDesc <> nil) and
       (ObjSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));
    Result := MDecl.ResolvedReturnType;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  FMethodOwnerHint := RT.OwningUnit;
    MDecl := ResolveMethodOverload(RT.Name, AExpr.Name, AExpr.Args,
      AExpr.Line, AExpr.Col);
  if MDecl = nil then
    MDecl := FindMethodDecl(RT.Name, AExpr.Name);
  ResolveDeferredArrowArgs(AExpr.Args, MDecl);
  { Built-in TObject.ToString: virtual dispatch yielding string.
    Every class inherits this from TObject (vtable slot 1). }
  if (MDecl = nil) and SameText(AExpr.Name, 'ToString') and (AExpr.Args.Count = 0) and
     (ObjSym.TypeDesc.Kind = tyClass) then
  begin
    AExpr.ResolvedClassType := RT;
    AExpr.ResolvedMethod    := nil;
    AExpr.IsBuiltinToString := True;
    AExpr.IsGlobal          := ObjSym.IsGlobal;
    AExpr.IsVarParam        :=
      (ObjSym.Kind = skVarParameter) or
      ((ObjSym.Kind = skParameter) and (ObjSym.TypeDesc <> nil) and
       (ObjSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  if MDecl = nil then
  begin
    FldInfo := RT.FindField(AExpr.Name);
    if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
       (FldInfo.TypeDesc.Kind = tyProcedural) then
    begin
      AExpr.IsProcFieldCall   := True;
      AExpr.ProcFieldInfo     := FldInfo;
      AExpr.ResolvedProcType  := FldInfo.TypeDesc;
      AExpr.ResolvedClassType := RT;
      AExpr.ResolvedMethod    := nil;
      AExpr.IsGlobal          := ObjSym.IsGlobal;
      AExpr.IsVarParam        :=
        (ObjSym.Kind = skVarParameter) or
        ((ObjSym.Kind = skParameter) and (ObjSym.TypeDesc <> nil) and
         (ObjSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));
      { Function-pointer field call yields the signature's return type. }
      AExpr.ResolvedType      := TProceduralTypeDesc(FldInfo.TypeDesc).ReturnType;
      Result                  := AExpr.ResolvedType;
      Exit;
    end;
    SemanticError(
      Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
      AExpr.Line, AExpr.Col);
  end;
  if MDecl.ResolvedReturnType = nil then
    SemanticError(
      Format('Method ''%s.%s'' is a procedure (no return value)',
        [RT.Name, AExpr.Name]),
      AExpr.Line, AExpr.Col);

  if AExpr.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d',
        [RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
      AExpr.Line, AExpr.Col);

  for I := 0 to AExpr.Args.Count - 1 do
  begin
    Par := TMethodParam(MDecl.Params.Items[I]);
    { A bracket set literal has no set type of its own — type it against the
      param's set type, exactly as the free-proc / function-call paths do
      (RetypeSetLiteralArgs).  Analysing it unhinted leaves an open-array
      type that fails the match here and is rejected by native codegen
      (BUG-20260722-native-set-literal-arg). }
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tySet) and
       (TASTExpr(AExpr.Args.Items[I]) is TArrayLiteralExpr) then
      ArgType := AnalyseSetLiteralExpr(
        TArrayLiteralExpr(AExpr.Args.Items[I]),
        TSetTypeDesc(Par.ResolvedType))
    else
      ArgType := Self.AnalyseListSlot(AExpr.Args, I);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
      AExpr.Line, AExpr.Col);
  end;
  ValidateMethodVarArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);

  EnforceMethodVisible(MDecl, AExpr.Line, AExpr.Col);
  AExpr.ResolvedClassType := RT;
  AExpr.ResolvedMethod    := MDecl;
  AExpr.IsGlobal          := ObjSym.IsGlobal;
  AExpr.IsVarParam        :=
    (ObjSym.Kind = skVarParameter) or
    ((ObjSym.Kind = skParameter) and (ObjSym.TypeDesc <> nil) and
     (ObjSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
var
  Sym:       TSymbol;
  FldInfo:   TFieldInfo;
  PropInfo:  TPropertyInfo;
  EnumRef:   TEnumMemberRef;
begin
  if AExpr is TNilLiteral then
    Result := FTable.TypeNil
  else if AExpr is TIntLiteral then
    if TIntLiteral(AExpr).IsUInt64 then
      Result := FTable.TypeUInt64
    else if (TIntLiteral(AExpr).Value < -2147483648) or
            (TIntLiteral(AExpr).Value > 2147483647) then
      Result := FTable.TypeInt64
    else
      Result := FTable.TypeInteger
  else if AExpr is TFloatLiteral then
    Result := FTable.TypeDouble   { float literals default to Double }
  else if AExpr is TStringLiteral then
    Result := FTable.TypeString
  else if AExpr is TIdentExpr then
  begin
    { Already resolved to a constant (e.g. a bare enum member pinned in place
      by a context-directed site such as an assignment, case label or 'in'
      operand).  Re-returning the type keeps resolution idempotent and avoids
      a spurious second ambiguity warning. }
    if TIdentExpr(AExpr).IsConstant and (AExpr.ResolvedType <> nil) then
      Exit(AExpr.ResolvedType);
    { Unit-qualified reference 'Unit.Symbol' (parser preserved the unit in
      QualifierUnit).  Resolve via the directed-lookup primitive against
      that specific unit's exports: a same-named symbol in another used
      unit cannot shadow it, the uses-chain last-wins rule does not apply,
      and an explicit qualifier is never shadowed by a class field.  An
      absent member is a hard error at the qualification site.  No const/
      var/type special-casing here — it falls through to the shared symbol
      normalisation below, dispatched on Sym.Kind like any other symbol. }
    if TIdentExpr(AExpr).QualifierUnit <> '' then
    begin
      Sym := ResolveQualified(TIdentExpr(AExpr).QualifierUnit,
                              TIdentExpr(AExpr).Name);
      if Sym = nil then
        SemanticError(Format(
          'Identifier ''%s'' not declared in unit ''%s''',
          [TIdentExpr(AExpr).Name, TIdentExpr(AExpr).QualifierUnit]),
          AExpr.Line, AExpr.Col);
    end
    else
    begin
    { Resolution order (matches AnalyseProcCall / AnalyseFuncCall):
      local vars/params > implicit Self.member > unit-level.  Without
      this priority, a bare identifier inside a method binds to the
      same-named unit-level symbol even when the enclosing class has
      a field / zero-arg method / property of that name.
      Also try class fields when Sym is a global variable — a class field
      with the same name must shadow a program-level global. }
    Sym := FTable.Lookup(TIdentExpr(AExpr).Name);
    if (FCurrentClass <> nil) and
       ((Sym = nil) or
        (Sym.IsGlobal) or
        not (Sym.Kind in [skVariable, skParameter, skVarParameter])) then
    begin
      FldInfo := FCurrentClass.FindField(TIdentExpr(AExpr).Name);
      if FldInfo <> nil then
      begin
        TIdentExpr(AExpr).IsImplicitSelf    := True;
        TIdentExpr(AExpr).ImplicitFieldInfo := FldInfo;
        Result := FldInfo.TypeDesc;
        AExpr.ResolvedType := Result;
        Exit;
      end;
      { Bare zero-arg method reference — error: mandatory () required }
      if FindMethodDecl(FCurrentClass.Name, TIdentExpr(AExpr).Name) <> nil then
        SemanticError(
          Format('Bare reference to ''%s'' requires () for a call',
            [TIdentExpr(AExpr).Name]),
          AExpr.Line, AExpr.Col);
      { Property of current class, method-backed: rewrite to the read method }
      PropInfo := FCurrentClass.FindProperty(TIdentExpr(AExpr).Name);
      if PropInfo <> nil then
      begin
        if PropInfo.ReadMethod <> '' then
        begin
          TIdentExpr(AExpr).ImplicitMethodDecl :=
            FindMethodDecl(FCurrentClass.Name, PropInfo.ReadMethod);
          if TIdentExpr(AExpr).ImplicitMethodDecl <> nil then
          begin
            TIdentExpr(AExpr).IsImplicitSelfMethod := True;
            TIdentExpr(AExpr).Name := PropInfo.ReadMethod;
            Result := PropInfo.TypeDesc;
            AExpr.ResolvedType := Result;
            Exit;
          end;
        end
        else if PropInfo.ReadField <> '' then
        begin
          FldInfo := FCurrentClass.FindField(PropInfo.ReadField);
          if FldInfo <> nil then
          begin
            TIdentExpr(AExpr).IsImplicitSelf    := True;
            TIdentExpr(AExpr).ImplicitFieldInfo := FldInfo;
            Result := FldInfo.TypeDesc;
            AExpr.ResolvedType := Result;
            Exit;
          end;
        end;
      end;
    end;
    if Sym = nil then
    begin
      { Not a normal symbol — try a bare enum member.  No expected-type
        context flows into the generic expression path, so this resolves a
        member declared by a single enum directly; a member shared by several
        enums is ambiguous here and is rejected — qualify it (TEnum.Member).
        Context-sensitive sites (assignment, case, call args, set elements,
        for bounds) inject a hint before reaching here. }
      EnumRef := ResolveEnumMember(TIdentExpr(AExpr).Name, nil);
      if EnumRef <> nil then
      begin
        if EnumMemberCandidateCount(TIdentExpr(AExpr).Name) > 1 then
          SemanticError(Format(
            'cannot determine which enum ''%s'' refers to: it is declared by ' +
            '%s, and there is no type context here to choose. Qualify it as ' +
            '<EnumType>.%s',
            [TIdentExpr(AExpr).Name, EnumMemberOwners(TIdentExpr(AExpr).Name),
             TIdentExpr(AExpr).Name]),
            AExpr.Line, AExpr.Col);
        TIdentExpr(AExpr).IsConstant := True;
        TIdentExpr(AExpr).ConstValue := EnumRef.Ordinal;
        Result := EnumRef.EnumDesc;
        AExpr.ResolvedType := Result;
        Exit;
      end;
      SemanticError(
        Format('Undeclared identifier ''%s''', [TIdentExpr(AExpr).Name]),
        AExpr.Line, AExpr.Col);
    end;
    end;  { end else: unqualified resolution (qualified set Sym above) }
    { Var-params and value-record/array params are both passed by reference at
      the QBE ABI level: the local slot holds a pointer, not the aggregate
      bytes.  Codegen must dereference the slot before reading fields. }
    TIdentExpr(AExpr).Name      := Sym.Name;  { normalise to declared casing }
    { A static (class-level) variable resolves to a single shared global whose
      emit label is the mangled GlobalEmitName, distinct from the lookup key
      ('FInstance' or 'TFoo.FInstance' both reach the one slot).  Rewrite the
      node's emitted name to that label so codegen lowers $TFoo_FInstance.
      Enforce member visibility on the bare form: a strict-private static var is
      reachable only from its declaring type's own methods (FCurrentClass = the
      declaring type), not from another type or the unit init/final section. }
    if Sym.IsClassVar and (Sym.GlobalEmitName <> '') then
    begin
      AssertStaticVarVisible(Sym.Visibility, Sym.OwningUnit,
                             Sym.OwnerTypeName, Sym.Name,
                           AExpr.Line, AExpr.Col);
      TIdentExpr(AExpr).Name := Sym.GlobalEmitName;
    end;
    if Sym.Kind = skVarParameter then
      TIdentExpr(AExpr).ParamMode := pmVar
    else if (Sym.Kind = skParameter) and (Sym.TypeDesc <> nil) and
            (Sym.TypeDesc.Kind = tyRecord) then
      TIdentExpr(AExpr).ParamMode := pmRecordValue
    else if (Sym.Kind = skParameter) and (Sym.TypeDesc <> nil) and
            (Sym.TypeDesc.Kind = tyStaticArray) then
      TIdentExpr(AExpr).ParamMode := pmStaticArrayValue
    else if (Sym.Kind = skParameter) and (Sym.TypeDesc <> nil) and
            (Sym.TypeDesc.Kind = tySet) and TSetTypeDesc(Sym.TypeDesc).IsJumbo() then
      TIdentExpr(AExpr).ParamMode := pmJumboSetValue
    else
      TIdentExpr(AExpr).ParamMode := pmNone;
    TIdentExpr(AExpr).IsGlobal    := Sym.IsGlobal;
    TIdentExpr(AExpr).IsThreadVar := Sym.IsThreadVar;
    { Record the owning unit of a module-scope global so codegen mangles
      the storage symbol with the unit that actually won resolution (the
      uses-chain last-wins winner for a bare ref, the named unit for a
      qualified ref).  Without this, two used units exporting the same var
      name both resolve to one slot. }
    if Sym.IsGlobal and (Sym.Kind = skVariable) then
    begin
      { A static class/record var's Name was rewritten above to its already
        fully-mangled GlobalEmitName (Unit_Class_Field); flag it so codegen's
        module-var prefixing does not double-apply.  Plain module globals carry
        their owning unit for owner-based mangling. }
      if Sym.IsClassVar then
        TIdentExpr(AExpr).ResolvedOwnerUnit := PreMangledGlobalOwner
      else
        TIdentExpr(AExpr).ResolvedOwnerUnit := Sym.OwningUnit;
    end;
    if Sym.Kind = skConstant then
    begin
      TIdentExpr(AExpr).IsConstant  := True;
      TIdentExpr(AExpr).ConstValue  := Sym.ConstValue;
      TIdentExpr(AExpr).ConstString := Sym.ConstString;
    end;
    { Array const referenced bare: codegen must use the mangled data-label,
      not $Name, to avoid link collisions. }
    if (Sym.ConstArray <> nil) and (Sym.ConstArrayQbe <> '') then
      TIdentExpr(AExpr).ConstArraySymbol := Sym.ConstArrayQbe;
    { Jumbo set const referenced bare: same mangled-label mechanism — the read
      resolves to the bitmap blob's address via the aggregate-read path. }
    if (Sym.ConstSetBytes <> nil) and (Sym.ConstSetQbe <> '') then
      TIdentExpr(AExpr).ConstArraySymbol := Sym.ConstSetQbe;
    { Bare class type identifier used as a value: metaclass reference.
      The result type is 'class of TFoo'; codegen emits the typeinfo
      address.  Compatibility with untyped Pointer (so 'Pointer(EError)'
      casts and 'AClass: Pointer' parameters keep working) is handled
      in CheckTypesMatch. }
    if (Sym.Kind = skType) and (Sym.TypeDesc <> nil) and
       (Sym.TypeDesc.Kind = tyClass) then
    begin
      TIdentExpr(AExpr).IsMetaclassRef := True;
      Result := FindTypeOrInstantiate('class of ' + Sym.TypeDesc.Name);
      if Result = nil then Result := FTable.TypePointer;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    if (Sym.Kind in [skFunction, skProcedure]) then
    begin
      if (FCurrentEnclosingDecl = nil) or
         (not SameText(FCurrentEnclosingDecl.Name, TIdentExpr(AExpr).Name)) then
        SemanticError(
          Format('Bare reference to ''%s'' requires () for a call',
            [TIdentExpr(AExpr).Name]),
          AExpr.Line, AExpr.Col);
    end;
    Result := Sym.TypeDesc;
  end
  else if AExpr is TIndirectFuncCallExpr then
    Result := AnalyseIndirectFuncCallExpr(TIndirectFuncCallExpr(AExpr))
  else if AExpr is TFuncCallExpr then
    Result := AnalyseFuncCallExpr(TFuncCallExpr(AExpr))
  else if AExpr is TMethodCallExpr then
    Result := AnalyseMethodCallExpr(TMethodCallExpr(AExpr))
  else if AExpr is TFieldAccessExpr then
    Result := AnalyseFieldAccess(TFieldAccessExpr(AExpr))
  else if AExpr is TBinaryExpr then
    Result := AnalyseBinaryExpr(TBinaryExpr(AExpr))
  else if AExpr is TIsExpr then
    Result := AnalyseIsExpr(TIsExpr(AExpr))
  else if AExpr is TInheritedCallExpr then
    Result := AnalyseInheritedCallExpr(TInheritedCallExpr(AExpr))
  else if AExpr is TAsExpr then
    Result := AnalyseAsExpr(TAsExpr(AExpr))
  else if AExpr is TSupportsExpr then
    Result := AnalyseSupportsExpr(TSupportsExpr(AExpr))
  else if AExpr is TDerefExpr then
    Result := AnalyseDerefExpr(TDerefExpr(AExpr))
  else if AExpr is TAddrOfExpr then
    Result := AnalyseAddrOfExpr(TAddrOfExpr(AExpr))
  else if AExpr is TAnonMethodExpr then
    Result := AnalyseAnonMethodExpr(TAnonMethodExpr(AExpr))
  else if AExpr is TStringSubscriptExpr then
    Result := AnalyseStringSubscriptExpr(TStringSubscriptExpr(AExpr))
  else if AExpr is TArrayLiteralExpr then
    Result := AnalyseArrayLiteralExpr(TArrayLiteralExpr(AExpr))
  else if AExpr is TNotExpr then
  begin
    Result := AnalyseExpr(TNotExpr(AExpr).Expr);
    if Result.Kind = tyBoolean then
      Result := FTable.TypeBoolean
    else if Result.IsNumeric() and not Result.IsFloat() then
    begin
      if Result.Kind = tyUInt64 then
        Result := FTable.TypeUInt64
      else if Result.Kind = tyInt64 then
        Result := FTable.TypeInt64
      else
        Result := FTable.TypeInteger;
    end
    else
      SemanticError(
        Format('''not'' requires a Boolean or integer operand, got ''%s''', [Result.Name]),
        AExpr.Line, AExpr.Col);
  end
  else
    SemanticError('Unknown expression node', AExpr.Line, AExpr.Col);

  AExpr.ResolvedType := Result;
end;

{ Default array property on a property-read result.  The parser folds the
  trailing '[idx]' of 'Recv.Prop[idx]' into AAccess.PropIndexExpr, so when Prop
  is a (non-indexed) property whose type has a `default` indexed property, the
  read above would resolve Recv.Prop and drop the index.  Rewrite it as
  '(Recv.Prop).Default[idx]': move the property read into a fresh inner
  field-access (the getter, no index) and re-point AAccess at the default
  property, then re-analyse — which lands on the chained indexed-property path.
  Returns the resolved element type, or nil when no lowering applies (the
  caller then handles Prop as before).  APropInfo is the already-resolved read
  property. }
function TSemanticAnalyser.TryLowerDefaultPropertyIndex(
  AAccess: TFieldAccessExpr; APropInfo: TPropertyInfo): TTypeDesc;
var
  Inner:   TFieldAccessExpr;
  DefProp: TPropertyInfo;
begin
  Result := nil;
  if (APropInfo.IndexParamName <> '') or (AAccess.PropIndexExpr = nil) then
    Exit;
  if not (APropInfo.TypeDesc.Kind in [tyRecord, tyClass]) then
    Exit;
  DefProp := TRecordTypeDesc(APropInfo.TypeDesc).FindDefaultProperty();
  if (DefProp = nil) or (DefProp.ReadMethod = '') then
    Exit;
  { Inner = the property getter without the index; carries the receiver. }
  Inner := TFieldAccessExpr.Create();
  Inner.Line       := AAccess.Line;
  Inner.Col        := AAccess.Col;
  Inner.Base       := AAccess.Base;        { transfer ownership (may be nil) }
  Inner.RecordName := AAccess.RecordName;
  Inner.FieldName  := AAccess.FieldName;
  { Re-point AAccess at the default property on that getter result; the
    PropIndexExpr ('[idx]') is left in place as its index. }
  AAccess.Base       := Inner;
  AAccess.RecordName := '';
  AAccess.FieldName  := DefProp.Name;
  Result := AnalyseFieldAccess(AAccess);
end;

function TSemanticAnalyser.AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
var
  RecSym:   TSymbol;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  PropInfo: TPropertyInfo;
  BaseType: TTypeDesc;
  IntfDesc: TInterfaceTypeDesc;
  MDecl:    TMethodDecl;
  EnumOrd:  Integer;
begin
  { Chained access: A.B.C — base is another expression whose type must be
    a record or class.  Leaf lookup uses Base.ResolvedType; RecordName path
    (no Base) is used only for the simple IDENT.IDENT form. }
  if AAccess.Base <> nil then
  begin
    BaseType := Self.AnalyseExprSlot(AAccess.Base);
    { Metaclass base: 'TypeName.StaticVar' or 'TypeName.StaticProp' arriving as
      a chained access (Base is the bare class-name ident resolving to
      'class of TypeName') rather than the simple RecordName form.  This is how
      the parser shapes a qualified static-var/property used as the BASE of a
      further chain on an l-value, e.g. 'TFoo.GObj.V := x' or 'TFoo.GObj.M()'.
      Resolve it exactly like the RecordName static-var/static-prop read below,
      so the result type feeds the outer chain. }
    if BaseType.Kind = tyMetaClass then
    begin
      RT  := TRecordTypeDesc(TMetaClassTypeDesc(BaseType).BaseClass);
      Sym := FTable.Lookup(RT.Name + '.' + AAccess.FieldName);
      if (Sym <> nil) and (Sym.Kind = skVariable) and Sym.IsClassVar then
      begin
        AssertStaticVarVisible(Sym.Visibility, Sym.OwningUnit,
                               Sym.OwnerTypeName, AAccess.FieldName,
                               AAccess.Line, AAccess.Col);
        AAccess.IsClassVarRead   := True;
        AAccess.IsGlobal         := True;
        AAccess.ClassVarEmitName := Sym.GlobalEmitName;
        AAccess.ResolvedType     := Sym.TypeDesc;
        Exit(Sym.TypeDesc);
      end;
      PropInfo := RT.FindProperty(AAccess.FieldName);
      if (PropInfo <> nil) and PropInfo.IsStatic then
      begin
        if PropInfo.ReadMethod = '' then
          SemanticError(
            Format('Static property ''%s.%s'' has no readable static getter',
              [RT.Name, AAccess.FieldName]),
            AAccess.Line, AAccess.Col);
        MDecl := FindMethodDecl(RT.Name, PropInfo.ReadMethod);
        if (MDecl = nil) or not MDecl.IsStatic then
          SemanticError(
            Format('Static property ''%s.%s'' getter ''%s'' is not a static method',
              [RT.Name, AAccess.FieldName, PropInfo.ReadMethod]),
            AAccess.Line, AAccess.Col);
        AAccess.IsStaticPropGet   := True;
        AAccess.ResolvedMethod    := MDecl;
        AAccess.ResolvedClassType := BaseType;
        AAccess.ResolvedType      := MDecl.ResolvedReturnType;
        Exit(MDecl.ResolvedReturnType);
      end;
      SemanticError(
        Format('Unknown static member ''%s'' on type ''%s''',
          [AAccess.FieldName, RT.Name]),
        AAccess.Line, AAccess.Col);
    end;
    if not (BaseType.Kind in [tyRecord, tyClass]) then
      SemanticError(
        Format('Field access ''.%s'' requires a record or class base, got ''%s''',
          [AAccess.FieldName, BaseType.Name]),
        AAccess.Line, AAccess.Col);
    AAccess.IsClassAccess := BaseType.Kind = tyClass;
    { Built-in class intrinsics available on any class instance }
    if SameText(AAccess.FieldName, 'ClassName') and (BaseType.Kind = tyClass) then
    begin
      AAccess.IsClassNameAccess := True;
      AAccess.ResolvedType := FTable.TypeString;
      Exit(FTable.TypeString);
    end;
    if SameText(AAccess.FieldName, 'ClassType') and (BaseType.Kind = tyClass) then
    begin
      AAccess.IsClassTypeAccess := True;
      AAccess.ResolvedType := FTable.TypePointer;  { TClass = Pointer for now }
      Exit(FTable.TypePointer);
    end;
    RT      := TRecordTypeDesc(BaseType);
    FldInfo := RT.FindField(AAccess.FieldName);
    if FldInfo = nil then
    begin
      PropInfo := RT.FindProperty(AAccess.FieldName);
      if PropInfo <> nil then
        AssertMemberVisibleV(PropInfo.Visibility, PropInfo.DeclaringUnit,
                             PropInfo.DeclaringType, AAccess.FieldName,
                             AAccess.Line, AAccess.Col);
      if (PropInfo <> nil) and (PropInfo.ReadField <> '') then
      begin
        Result := TryLowerDefaultPropertyIndex(AAccess, PropInfo);
        if Result <> nil then
          Exit;
        AAccess.FieldName := PropInfo.ReadField;
        AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
        AAccess.BackingFieldRedirect := True;
        Exit(PropInfo.TypeDesc);
      end;
      { Method-backed property (including indexed: the parser attaches the
        '[idx]' to AAccess.PropIndexExpr when it parses 'Base.Prop[idx]'). }
      if (PropInfo <> nil) and (PropInfo.ReadMethod <> '') then
      begin
        Result := TryLowerDefaultPropertyIndex(AAccess, PropInfo);
        if Result <> nil then
          Exit;
        if PropInfo.IndexParamName <> '' then
        begin
          if AAccess.PropIndexExpr = nil then
            SemanticError(
              Format('Indexed property ''%s'' requires an index expression',
                [AAccess.FieldName]),
              AAccess.Line, AAccess.Col);
          Self.AnalyseExprSlot(AAccess.PropIndexExpr);
        end;
        AAccess.PropRead := PropInfo;
        AAccess.PropOwnerType :=
          PropAccessorOwner(RT.Name, PropInfo.ReadMethod);
        AAccess.PropAccessorVSlot :=
          PropAccessorVSlot(RT.Name, PropInfo.ReadMethod);
        AAccess.PropReadDecl := FindMethodDecl(RT.Name, PropInfo.ReadMethod);
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
        Exit;
      end;
      { Zero-arg method call via field access: Obj.Method (no parens) — error }
      if FindMethodDecl(RT.Name, AAccess.FieldName) <> nil then
        SemanticError(
          Format('Bare reference to ''%s'' requires () for a call',
            [AAccess.FieldName]),
          AAccess.Line, AAccess.Col);
      { Built-in TObject.ToString: must use () }
      if SameText(AAccess.FieldName, 'ToString') and
         (BaseType.Kind = tyClass) then
        SemanticError(
          Format('Bare reference to ''%s'' requires () for a call',
            [AAccess.FieldName]),
          AAccess.Line, AAccess.Col);
      { Class-level constant (scalar or array): look up ClassName.ConstName }
      Sym := FTable.Lookup(BaseType.Name + '.' + AAccess.FieldName);
      if (Sym <> nil) and (Sym.Kind = skConstant) then
      begin
        AAccess.IsConstant := True;
        AAccess.ConstValue := Sym.ConstValue;
        AAccess.ConstString := Sym.ConstString;
        if Sym.ConstArray <> nil then
        begin
          AAccess.ConstArraySymbol := BaseType.Name + '_' + AAccess.FieldName;
          AAccess.ConstArrayType := Sym.TypeDesc;
        end;
        AAccess.ResolvedType := Sym.TypeDesc;
        Exit(Sym.TypeDesc);
      end;
      SemanticError(
        Format('Type ''%s'' has no field ''%s''',
          [BaseType.Name, AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    end;
    { Field found via qualified access (Base.Field) — enforce visibility unless
      this node is a property→backing-field redirect already checked. }
    if not AAccess.BackingFieldRedirect then
      AssertMemberVisibleV(FldInfo.Visibility, FldInfo.DeclaringUnit,
                           FldInfo.DeclaringType, AAccess.FieldName,
                           AAccess.Line, AAccess.Col);
    AAccess.FieldInfo := FldInfo;
    Result := FldInfo.TypeDesc;
    if AAccess.PropIndexExpr <> nil then
    begin
      { Subscript on a string field: Rec.Field[N] — emit char access. }
      if FldInfo.TypeDesc.IsString() then
      begin
        Self.AnalyseExprSlot(AAccess.PropIndexExpr);
        AAccess.IsCharAccess := True;
        Result := FTable.TypeInteger;
        AAccess.ResolvedType := Result;
      end
      { Subscript on a class field: Rec.Field[I] — use the field type's indexed property. }
      else if FldInfo.TypeDesc.Kind in [tyRecord, tyClass] then
      begin
        PropInfo := TRecordTypeDesc(FldInfo.TypeDesc).FindIndexedProperty();
        if PropInfo <> nil then
        begin
          Self.AnalyseExprSlot(AAccess.PropIndexExpr);
          AAccess.PropRead      := PropInfo;
          AAccess.PropOwnerType := PropAccessorOwner(
            TRecordTypeDesc(FldInfo.TypeDesc).Name, PropInfo.ReadMethod);
          AAccess.PropAccessorVSlot := PropAccessorVSlot(
            TRecordTypeDesc(FldInfo.TypeDesc).Name, PropInfo.ReadMethod);
          Result := PropInfo.TypeDesc;
          AAccess.ResolvedType := Result;
        end;
      end
      else if FldInfo.TypeDesc.Kind = tyDynArray then
      begin
        Self.AnalyseExprSlot(AAccess.PropIndexExpr);
        AAccess.IsArrayAccess := True;
        Result := TDynArrayTypeDesc(FldInfo.TypeDesc).ElementType;
        AAccess.ResolvedType := Result;
      end
      else if FldInfo.TypeDesc.Kind = tyStaticArray then
      begin
        Self.AnalyseExprSlot(AAccess.PropIndexExpr);
        AAccess.IsArrayAccess := True;
        Result := TStaticArrayTypeDesc(FldInfo.TypeDesc).ElementType;
        AAccess.ResolvedType := Result;
      end
      else if FldInfo.TypeDesc.Kind = tyOpenArray then
      begin
        Self.AnalyseExprSlot(AAccess.PropIndexExpr);
        AAccess.IsArrayAccess := True;
        Result := TOpenArrayTypeDesc(FldInfo.TypeDesc).ElementType;
        AAccess.ResolvedType := Result;
      end;
    end;
    Exit;
  end;

  { A unit-qualified base type 'Unit.TEnum.Member' / 'Unit.TFoo.StaticVar'
    resolves the base against that specific unit's exports (directed lookup), so
    it binds to the named unit rather than the flat cross-unit last-wins winner.
    Falls back to the normal lookup on a miss. }
  RecSym := nil;
  if AAccess.QualifierUnit <> '' then
    RecSym := ResolveQualified(AAccess.QualifierUnit, AAccess.RecordName);
  if RecSym = nil then
    RecSym := FTable.Lookup(AAccess.RecordName);
  { If the name contains '<' and wasn't found, resolve scope-bound type params
    (e.g. 'TGenEnum<T>' → 'TGenEnum<Integer>' when T=Integer is in scope)
    and update AAccess.RecordName so codegen sees the concrete instantiation. }
  if (RecSym = nil) and (StrPos('<', AAccess.RecordName) >= 0) then
  begin
    AAccess.RecordName := ResolveScopeBoundTypeParams(AAccess.RecordName);
    FindTypeOrInstantiate(AAccess.RecordName);
    RecSym := FTable.Lookup(AAccess.RecordName);
  end;
  if RecSym = nil then
  begin
    { Implicit Self.RecordName.FieldName — RecordName is a field of current class }
    if FCurrentClass <> nil then
    begin
      FldInfo := FCurrentClass.FindField(AAccess.RecordName);
      if (FldInfo <> nil) and
         (FldInfo.TypeDesc.Kind in [tyRecord, tyClass]) then
      begin
        AAccess.IsImplicitSelf   := True;
        AAccess.ImplicitBaseInfo := FldInfo;
        AAccess.IsClassAccess    := FldInfo.TypeDesc.Kind = tyClass;
        RT := TRecordTypeDesc(FldInfo.TypeDesc);
        AAccess.FieldInfo := RT.FindField(AAccess.FieldName);
        if AAccess.FieldInfo = nil then
        begin
          { Field-backed property on the implicit-Self field's type }
          PropInfo := RT.FindProperty(AAccess.FieldName);
          if PropInfo <> nil then
          begin
            if PropInfo.ReadField <> '' then
            begin
              Result := TryLowerDefaultPropertyIndex(AAccess, PropInfo);
              if Result <> nil then
                Exit;
              AAccess.FieldName := PropInfo.ReadField;
              AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
              Result := PropInfo.TypeDesc;
              AAccess.ResolvedType := Result;
              Exit;
            end
            else if PropInfo.ReadMethod <> '' then
            begin
              { Method-backed read (includes indexed properties) }
              Result := TryLowerDefaultPropertyIndex(AAccess, PropInfo);
              if Result <> nil then
                Exit;
              if PropInfo.IndexParamName <> '' then
              begin
                if AAccess.PropIndexExpr = nil then
                  SemanticError(
                    Format('Indexed property ''%s'' requires an index expression',
                      [AAccess.FieldName]),
                    AAccess.Line, AAccess.Col);
                Self.AnalyseExprSlot(AAccess.PropIndexExpr);
              end;
              AAccess.PropRead := PropInfo;
              AAccess.PropOwnerType :=
                PropAccessorOwner(RT.Name, PropInfo.ReadMethod);
              AAccess.PropAccessorVSlot :=
                PropAccessorVSlot(RT.Name, PropInfo.ReadMethod);
              Result := PropInfo.TypeDesc;
              AAccess.ResolvedType := Result;
              Exit;
            end;
          end;
          { Zero-arg method on the implicit-Self field — error: mandatory () }
          if FindMethodDecl(RT.Name, AAccess.FieldName) <> nil then
            SemanticError(
              Format('Bare reference to ''%s'' requires () for a call',
                [AAccess.FieldName]),
              AAccess.Line, AAccess.Col);
          SemanticError(
            Format('Type ''%s'' has no field ''%s''',
              [AAccess.RecordName, AAccess.FieldName]),
            AAccess.Line, AAccess.Col);
        end;
        Result := AAccess.FieldInfo.TypeDesc;
        if AAccess.PropIndexExpr <> nil then
        begin
          if AAccess.FieldInfo.TypeDesc.IsString() then
          begin
            Self.AnalyseExprSlot(AAccess.PropIndexExpr);
            AAccess.IsCharAccess := True;
            Result := FTable.TypeInteger;
            AAccess.ResolvedType := Result;
          end
          else if AAccess.FieldInfo.TypeDesc.Kind in [tyRecord, tyClass] then
          begin
            PropInfo := TRecordTypeDesc(AAccess.FieldInfo.TypeDesc).FindIndexedProperty();
            if PropInfo <> nil then
            begin
              Self.AnalyseExprSlot(AAccess.PropIndexExpr);
              AAccess.PropRead      := PropInfo;
              AAccess.PropOwnerType := PropAccessorOwner(
                TRecordTypeDesc(AAccess.FieldInfo.TypeDesc).Name,
                PropInfo.ReadMethod);
              AAccess.PropAccessorVSlot := PropAccessorVSlot(
                TRecordTypeDesc(AAccess.FieldInfo.TypeDesc).Name,
                PropInfo.ReadMethod);
              Result := PropInfo.TypeDesc;
              AAccess.ResolvedType := Result;
            end;
          end
          else if AAccess.FieldInfo.TypeDesc.Kind = tyDynArray then
          begin
            Self.AnalyseExprSlot(AAccess.PropIndexExpr);
            AAccess.IsArrayAccess := True;
            Result := TDynArrayTypeDesc(AAccess.FieldInfo.TypeDesc).ElementType;
            AAccess.ResolvedType := Result;
          end
          else if AAccess.FieldInfo.TypeDesc.Kind = tyStaticArray then
          begin
            Self.AnalyseExprSlot(AAccess.PropIndexExpr);
            AAccess.IsArrayAccess := True;
            Result := TStaticArrayTypeDesc(AAccess.FieldInfo.TypeDesc).ElementType;
            AAccess.ResolvedType := Result;
          end
          else if AAccess.FieldInfo.TypeDesc.Kind = tyOpenArray then
          begin
            Self.AnalyseExprSlot(AAccess.PropIndexExpr);
            AAccess.IsArrayAccess := True;
            Result := TOpenArrayTypeDesc(AAccess.FieldInfo.TypeDesc).ElementType;
            AAccess.ResolvedType := Result;
          end;
        end;
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared identifier ''%s''', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);
  end;

  AAccess.RecordName := RecSym.Name;  { normalise to declared casing }

  { Type-qualified enum member: TMyEnum.meValue.  Resolve the member straight
    from the named enum's own member list, so the reference is unambiguous even
    when another enum in scope declares a member of the same name (the bare name
    resolves to whichever enum claimed the global slot; the qualified form
    always names this one). }
  if (RecSym.Kind = skType) and (RecSym.TypeDesc <> nil) and
     (RecSym.TypeDesc.Kind = tyEnum) then
  begin
    EnumOrd := TEnumTypeDesc(RecSym.TypeDesc).OrdinalOf(AAccess.FieldName);
    if EnumOrd < 0 then
      SemanticError(
        Format('Enum ''%s'' has no member ''%s''',
          [AAccess.RecordName, AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    AAccess.IsConstant   := True;
    AAccess.ConstValue   := EnumOrd;
    AAccess.ResolvedType := RecSym.TypeDesc;
    Exit(RecSym.TypeDesc);
  end;

  { Constructor call: TypeName.Create }
  if RecSym.Kind = skType then
  begin
    if RecSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot call constructor on non-class type ''%s''',
          [AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    if not SameText(AAccess.FieldName, 'Create') then
    begin
      { Check for a class-level constant registered as TypeName.ConstName }
      Sym := FTable.Lookup(AAccess.RecordName + '.' + AAccess.FieldName);
      if (Sym <> nil) and (Sym.Kind = skConstant) then
      begin
        AAccess.IsConstant  := True;
        AAccess.ConstValue  := Sym.ConstValue;
        AAccess.ConstString := Sym.ConstString;
        if Sym.ConstArray <> nil then
        begin
          AAccess.ConstArraySymbol := AAccess.RecordName + '_' + AAccess.FieldName;
          AAccess.ConstArrayType := Sym.TypeDesc;
          if AAccess.PropIndexExpr <> nil then
          begin
            Self.AnalyseExprSlot(AAccess.PropIndexExpr);
            AAccess.ResolvedType := TStaticArrayTypeDesc(Sym.TypeDesc).ElementType;
            Exit(AAccess.ResolvedType);
          end;
        end;
        AAccess.ResolvedType := Sym.TypeDesc;
        Exit(Sym.TypeDesc);
      end;
      { Static (class-level) variable read: TypeName.StaticVar.  The qualified
        symbol carries the mangled GlobalEmitName; rewrite the access to a plain
        global read of that label (codegen lowers it like a global ident).
        Enforce member visibility — a strict/private static var read through the
        qualified form from a context that may not see it is rejected. }
      if (Sym <> nil) and (Sym.Kind = skVariable) and Sym.IsClassVar then
      begin
        AssertStaticVarVisible(Sym.Visibility, Sym.OwningUnit,
                               Sym.OwnerTypeName, AAccess.FieldName,
                             AAccess.Line, AAccess.Col);
        AAccess.IsClassVarRead := True;
        AAccess.IsGlobal       := True;
        AAccess.ClassVarEmitName := Sym.GlobalEmitName;
        AAccess.ResolvedType   := Sym.TypeDesc;
        Exit(Sym.TypeDesc);
      end;
      { Static property read: TypeName.StaticProp.  Resolve to its (static)
        getter and lower as a static getter call.  Only method-backed static
        getters are supported (a field-backed static property would resolve to
        the static var directly). }
      PropInfo := TRecordTypeDesc(RecSym.TypeDesc).FindProperty(AAccess.FieldName);
      if (PropInfo <> nil) and PropInfo.IsStatic then
      begin
        if PropInfo.ReadMethod = '' then
          SemanticError(
            Format('Static property ''%s.%s'' has no readable static getter',
              [AAccess.RecordName, AAccess.FieldName]),
            AAccess.Line, AAccess.Col);
        MDecl := FindMethodDecl(TRecordTypeDesc(RecSym.TypeDesc).Name, PropInfo.ReadMethod);
        if (MDecl = nil) or not MDecl.IsStatic then
          SemanticError(
            Format('Static property ''%s.%s'' getter ''%s'' is not a static method',
              [AAccess.RecordName, AAccess.FieldName, PropInfo.ReadMethod]),
            AAccess.Line, AAccess.Col);
        AAccess.IsStaticPropGet := True;
        AAccess.ResolvedMethod  := MDecl;
        AAccess.ResolvedClassType := RecSym.TypeDesc;
        AAccess.ResolvedType    := MDecl.ResolvedReturnType;
        Exit(MDecl.ResolvedReturnType);
      end;
      SemanticError(
        Format('Unknown class method ''%s'' on type ''%s''',
          [AAccess.FieldName, AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    end;
    if TRecordTypeDesc(RecSym.TypeDesc).HasAbstractMethods then
      SemanticError(
        Format('Cannot instantiate abstract class ''%s''', [AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    AAccess.IsConstructorCall := True;
    AAccess.ResolvedMethod    := FindMethodDecl(TRecordTypeDesc(RecSym.TypeDesc).Name, 'Create');
    Exit(RecSym.TypeDesc);
  end;

  { Field access on variable or parameter }
  if not (RecSym.Kind in [skVariable, skParameter, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable or type', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  { Interface variable: method call through itab (expression context) }
  if RecSym.TypeDesc.Kind = tyInterface then
  begin
    IntfDesc := TInterfaceTypeDesc(RecSym.TypeDesc);
    if not IntfDesc.HasMethod(AAccess.FieldName) then
    begin
      { Property read: lower to the getter — pure sugar over the
        zero-argument interface method dispatch below. }
      PropInfo := IntfDesc.FindProperty(AAccess.FieldName);
      if PropInfo = nil then
        SemanticError(
          Format('Interface ''%s'' has no method or property ''%s''',
            [IntfDesc.Name, AAccess.FieldName]),
          AAccess.Line, AAccess.Col);
      if PropInfo.ReadMethod = '' then
        SemanticError(
          Format('Interface property ''%s.%s'' is write-only',
            [IntfDesc.Name, AAccess.FieldName]),
          AAccess.Line, AAccess.Col);
      AAccess.FieldName := PropInfo.ReadMethod;
    end;
    AAccess.IsInterfaceCall  := True;
    AAccess.ResolvedClassType := IntfDesc;
    AAccess.IsGlobal         := RecSym.IsGlobal;
    AAccess.IsVarParam       := (RecSym.Kind = skVarParameter);
    Result := FindTypeOrInstantiate(
      IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AAccess.FieldName)));
    if Result = nil then
      Result := FTable.TypeInteger;
    AAccess.ResolvedType := Result;
    Exit;
  end;

  { Metaclass variable: a bare 'C.Create' / 'C.Method' (no parens) reaching
    field-access analysis is a constructor/method call written without the
    mandatory parentheses — the parenthesised form is a TMethodCallExpr and
    never lands here.  Emit the parens diagnostic rather than the misleading
    'is not a record or class' error. }
  if RecSym.TypeDesc.Kind = tyMetaClass then
  begin
    RT := TRecordTypeDesc(TMetaClassTypeDesc(RecSym.TypeDesc).BaseClass);
    if (RT <> nil) and
       (SameText(AAccess.FieldName, 'Create') or
        (FindMethodDecl(RT.Name, AAccess.FieldName) <> nil)) then
      SemanticError(
        Format('Bare reference to ''%s'' requires () for a call',
          [AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    SemanticError(
      Format('Metaclass ''%s'' has no method ''%s''',
        [RecSym.TypeDesc.Name, AAccess.FieldName]),
      AAccess.Line, AAccess.Col);
  end;

  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  AAccess.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAccess.IsGlobal      := RecSym.IsGlobal;
  { Records and static arrays are always passed by reference at the QBE ABI
    level — the param slot holds a pointer.  Mark both var-params and value
    aggregate params so codegen dereferences the slot. }
  AAccess.IsVarParam    :=
    (RecSym.Kind = skVarParameter) or
    ((RecSym.Kind = skParameter) and (RecSym.TypeDesc <> nil) and
     (RecSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));

  { Built-in class intrinsics }
  if SameText(AAccess.FieldName, 'ClassName') and (RecSym.TypeDesc.Kind = tyClass) then
  begin
    AAccess.IsClassNameAccess := True;
    AAccess.ResolvedType := FTable.TypeString;
    Exit(FTable.TypeString);
  end;
  if SameText(AAccess.FieldName, 'ClassType') and (RecSym.TypeDesc.Kind = tyClass) then
  begin
    AAccess.IsClassTypeAccess := True;
    AAccess.ResolvedType := FTable.TypePointer;
    Exit(FTable.TypePointer);
  end;

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAccess.FieldName);
  if FldInfo = nil then
  begin
    { Zero-arg method call via field access: Obj.Method (no parens) — error }
    if FindMethodDecl(RT.Name, AAccess.FieldName) <> nil then
      SemanticError(
        Format('Bare reference to ''%s'' requires () for a call',
          [AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    { Built-in TObject.ToString: virtual dispatch yielding string. }
    if SameText(AAccess.FieldName, 'ToString') and
       (RecSym.TypeDesc.Kind = tyClass) then
      SemanticError(
        Format('Bare reference to ''%s'' requires () for a call',
          [AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    { Check if this is a property access }
    PropInfo := RT.FindProperty(AAccess.FieldName);
    if PropInfo <> nil then
    begin
      AssertMemberVisibleV(PropInfo.Visibility, PropInfo.DeclaringUnit,
                           PropInfo.DeclaringType, AAccess.FieldName,
                           AAccess.Line, AAccess.Col);
      if PropInfo.ReadField <> '' then
      begin
        { Field-backed read: redirect to the backing field }
        Result := TryLowerDefaultPropertyIndex(AAccess, PropInfo);
        if Result <> nil then
          Exit;
        AAccess.FieldName := PropInfo.ReadField;
        AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
        AAccess.BackingFieldRedirect := True;
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
        Exit;
      end
      else if PropInfo.ReadMethod <> '' then
      begin
        { Method-backed read (includes indexed properties) }
        Result := TryLowerDefaultPropertyIndex(AAccess, PropInfo);
        if Result <> nil then
          Exit;
        if PropInfo.IndexParamName <> '' then
        begin
          if AAccess.PropIndexExpr = nil then
            SemanticError(
              Format('Indexed property ''%s'' requires an index expression',
                [AAccess.FieldName]),
              AAccess.Line, AAccess.Col);
          Self.AnalyseExprSlot(AAccess.PropIndexExpr);
        end;
        AAccess.PropRead := PropInfo;
        AAccess.PropOwnerType :=
          PropAccessorOwner(RT.Name, PropInfo.ReadMethod);
        AAccess.PropAccessorVSlot :=
          PropAccessorVSlot(RT.Name, PropInfo.ReadMethod);
        AAccess.PropReadDecl := FindMethodDecl(RT.Name, PropInfo.ReadMethod);
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
        Exit;
      end;
    end;
    { Class-level constant (scalar or array) via instance: T.Const }
    Sym := FTable.Lookup(RT.Name + '.' + AAccess.FieldName);
    if (Sym <> nil) and (Sym.Kind = skConstant) then
    begin
      AAccess.IsConstant := True;
      AAccess.ConstValue := Sym.ConstValue;
      AAccess.ConstString := Sym.ConstString;
      if Sym.ConstArray <> nil then
      begin
        AAccess.ConstArraySymbol := RT.Name + '_' + AAccess.FieldName;
        AAccess.ConstArrayType := Sym.TypeDesc;
        if AAccess.PropIndexExpr <> nil then
        begin
          Self.AnalyseExprSlot(AAccess.PropIndexExpr);
          AAccess.ResolvedType := TStaticArrayTypeDesc(Sym.TypeDesc).ElementType;
          Exit(AAccess.ResolvedType);
        end;
      end;
      AAccess.ResolvedType := Sym.TypeDesc;
      Exit(Sym.TypeDesc);
    end;
    SemanticError(
      Format('''%s'' (of type ''%s'') has no field ''%s''',
        [AAccess.RecordName, RT.Name, AAccess.FieldName]),
      AAccess.Line, AAccess.Col);
  end;

  { Field found via variable.Field qualified access — enforce visibility unless
    this node is a property→backing-field redirect already checked. }
  if not AAccess.BackingFieldRedirect then
    AssertMemberVisibleV(FldInfo.Visibility, FldInfo.DeclaringUnit,
                         FldInfo.DeclaringType, AAccess.FieldName,
                         AAccess.Line, AAccess.Col);
  AAccess.FieldInfo := FldInfo;
  Result := FldInfo.TypeDesc;
  if AAccess.PropIndexExpr <> nil then
  begin
    if FldInfo.TypeDesc.IsString() then
    begin
      Self.AnalyseExprSlot(AAccess.PropIndexExpr);
      AAccess.IsCharAccess := True;
      Result := FTable.TypeInteger;
      AAccess.ResolvedType := Result;
    end
    else if FldInfo.TypeDesc.Kind in [tyRecord, tyClass] then
    begin
      PropInfo := TRecordTypeDesc(FldInfo.TypeDesc).FindIndexedProperty();
      if PropInfo <> nil then
      begin
        Self.AnalyseExprSlot(AAccess.PropIndexExpr);
        AAccess.PropRead      := PropInfo;
        AAccess.PropOwnerType := PropAccessorOwner(
          TRecordTypeDesc(FldInfo.TypeDesc).Name, PropInfo.ReadMethod);
        AAccess.PropAccessorVSlot := PropAccessorVSlot(
          TRecordTypeDesc(FldInfo.TypeDesc).Name, PropInfo.ReadMethod);
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
      end;
    end
    else if FldInfo.TypeDesc.Kind = tyDynArray then
    begin
      Self.AnalyseExprSlot(AAccess.PropIndexExpr);
      AAccess.IsArrayAccess := True;
      Result := TDynArrayTypeDesc(FldInfo.TypeDesc).ElementType;
      AAccess.ResolvedType := Result;
    end
    else if FldInfo.TypeDesc.Kind = tyStaticArray then
    begin
      Self.AnalyseExprSlot(AAccess.PropIndexExpr);
      AAccess.IsArrayAccess := True;
      Result := TStaticArrayTypeDesc(FldInfo.TypeDesc).ElementType;
      AAccess.ResolvedType := Result;
    end
    else if FldInfo.TypeDesc.Kind = tyOpenArray then
    begin
      Self.AnalyseExprSlot(AAccess.PropIndexExpr);
      AAccess.IsArrayAccess := True;
      Result := TOpenArrayTypeDesc(FldInfo.TypeDesc).ElementType;
      AAccess.ResolvedType := Result;
    end;
  end;
end;

function TSemanticAnalyser.AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
var
  LType, RType: TTypeDesc;
  TmpSet: TSetTypeDesc;
  OpType: TTypeDesc;
begin
  { Set membership with a bare enum-member left operand and a real set (not a
    literal) on the right: the set's element type disambiguates the member, so
    resolve the right first and pin the left against it.  Done before the eager
    analysis below, which would otherwise pick a context-free last-wins
    candidate (and warn) for a shared member name. }
  if (ABin.Op = boIn) and (ABin.Left is TIdentExpr) and
     not TIdentExpr(ABin.Left).IsConstant and
     not (ABin.Right is TArrayLiteralExpr) then
  begin
    RType := Self.AnalyseExprSlot(ABin.Right);
    if (RType <> nil) and (RType.Kind = tySet) then
      TryResolveBareEnumIdent(ABin.Left, TSetTypeDesc(RType).BaseType);
    LType := Self.AnalyseExprSlot(ABin.Left);
  end
  else
  begin
    { Slot form: a nested operator expression (A + B + C) is lowered in place,
      so the outer node sees a plain call where its operand used to be. }
    LType := Self.AnalyseExprSlot(ABin.Left);
    RType := Self.AnalyseExprSlot(ABin.Right);
  end;

  { Set membership: elem in SetVar — left is base enum, right is set type }
  if ABin.Op = boIn then
  begin
    { Coerce array literal [a, b, c] to an anonymous set type when the left
      operand is an enum — handles the common 'x in [A, B, C]' idiom.
      Size the anonymous set by the largest ORDINAL actually listed (when all
      elements are compile-time enum constants), not the full enum's member
      count.  This keeps 'Kind in [low members]' on the fast <=64-bit register
      path even when the base enum has more than 64 members, and only widens to
      a jumbo set when a listed member's ordinal is itself >= 64.  Elements that
      are not constant fall back to the full enum size (conservative). }
    if (ABin.Right is TArrayLiteralExpr) and (LType.Kind = tyEnum) then
    begin
      TmpSet := FTable.NewSetType('', TEnumTypeDesc(LType));
      RType := AnalyseSetLiteralExpr(TArrayLiteralExpr(ABin.Right), TmpSet);
      TmpSet.BitCount := SetLiteralBitCount(TArrayLiteralExpr(ABin.Right),
        TEnumTypeDesc(LType));
    end;
    if RType.Kind <> tySet then
      SemanticError(
        Format('Right operand of ''in'' must be a set type, got ''%s''', [RType.Name]),
        ABin.Line, ABin.Col);
    if TSetTypeDesc(RType).BaseType.Kind in [tyByte, tyBoolean] then
    begin
      { Ordinal-base set (Byte/Boolean or an integer subrange): the left operand
        is the element ordinal.  Accept a numeric operand, and — for a Boolean
        base — a Boolean operand (True/False), since `True in s` is the natural
        form.  Both lower to the operand's ordinal. }
      if not (LType.IsNumeric() or
              ((TSetTypeDesc(RType).BaseType.Kind = tyBoolean) and
               (LType.Kind = tyBoolean))) then
        SemanticError(
          Format('Left operand of ''in'' must be %s for ''set of %s'', got ''%s''',
            ['ordinal', TSetTypeDesc(RType).BaseType.Name, LType.Name]),
          ABin.Line, ABin.Col);
    end
    else if LType <> TSetTypeDesc(RType).BaseType then
      SemanticError(
        Format('Left operand of ''in'' must be type ''%s'', got ''%s''',
          [TSetTypeDesc(RType).BaseType.Name, LType.Name]),
        ABin.Line, ABin.Col);
    Result := FTable.TypeBoolean;
    ABin.ResolvedType := Result;
    Exit;
  end;

  { Set arithmetic and equality: coerce array literals [...] or empty []
    to the set type of the other operand.  AnalyseArrayLiteralExpr returns nil
    for [] (no element type to infer) and tyOpenArray for [a, b, c]. }
  if (LType <> nil) and (LType.Kind = tySet) and
     (ABin.Right is TArrayLiteralExpr) and
     ((RType = nil) or (RType.Kind = tyOpenArray)) then
    RType := AnalyseSetLiteralExpr(TArrayLiteralExpr(ABin.Right),
                                   TSetTypeDesc(LType));
  if (RType <> nil) and (RType.Kind = tySet) and
     (ABin.Left is TArrayLiteralExpr) and
     ((LType = nil) or (LType.Kind = tyOpenArray)) then
    LType := AnalyseSetLiteralExpr(TArrayLiteralExpr(ABin.Left),
                                   TSetTypeDesc(RType));
  if ((LType <> nil) and (LType.Kind = tySet)) or
     ((RType <> nil) and (RType.Kind = tySet)) then
  begin
    if (LType = nil) or (LType.Kind <> tySet) then
      SemanticError(
        Format('Left operand of ''%s'' must be a set type',
          [BinaryOpName(ABin.Op)]),
        ABin.Line, ABin.Col);
    if (RType = nil) or (RType.Kind <> tySet) then
      SemanticError(
        Format('Right operand of ''%s'' must be a set type',
          [BinaryOpName(ABin.Op)]),
        ABin.Line, ABin.Col);
    if LType <> RType then
      SemanticError(
        Format('Incompatible set types in ''%s'': ''%s'' vs ''%s''',
          [BinaryOpName(ABin.Op), LType.Name, RType.Name]),
        ABin.Line, ABin.Col);
    if ABin.Op in [boEQ, boNE, boLE, boGE] then
      { = <> equality; <= subset; >= superset — all yield Boolean. }
      Result := FTable.TypeBoolean
    else if ABin.Op in [boAdd, boSub, boMul] then
      Result := LType
    else
      SemanticError(
        Format('Operator ''%s'' is not defined for set types', [BinaryOpName(ABin.Op)]),
        ABin.Line, ABin.Col);
    ABin.ResolvedType := Result;
    Exit;
  end;

  { Logical AND / OR / XOR — both operands must be Boolean or both numeric. }
  if ABin.Op in [boAnd, boOr, boXor] then
  begin
    { Bitwise or/and for integer types }
    if LType.IsNumeric() and RType.IsNumeric() then
    begin
      if ((LType.Kind = tyInt64) and (RType.Kind = tyUInt64)) or
         ((LType.Kind = tyUInt64) and (RType.Kind = tyInt64)) then
        SemanticError(
          Format('Cannot mix signed Int64 and UInt64 in ''%s'' '
                 + 'without an explicit cast', [BinaryOpName(ABin.Op)]),
          ABin.Line, ABin.Col);
      if (LType.Kind = tyUInt64) or (RType.Kind = tyUInt64) then
        Result := FTable.TypeUInt64
      else if (LType.Kind = tyInt64) or (RType.Kind = tyInt64) then
        Result := FTable.TypeInt64
      else
        Result := FTable.TypeInteger;
      Exit;
    end;
    if LType.Kind <> tyBoolean then
      SemanticError(
        Format('Left operand of ''%s'' must be Boolean, got ''%s''',
          [BinaryOpName(ABin.Op), LType.Name]),
        ABin.Line, ABin.Col);
    if RType.Kind <> tyBoolean then
      SemanticError(
        Format('Right operand of ''%s'' must be Boolean, got ''%s''',
          [BinaryOpName(ABin.Op), RType.Name]),
        ABin.Line, ABin.Col);
    Exit(FTable.TypeBoolean);
  end;

  if IsComparisonOp(ABin.Op) then
  begin
    { Char literal coercion: S[N] = '-' — subscript yields Integer; coerce the literal }
    if (LType.Kind = tyInteger) and (ABin.Right is TStringLiteral) then
    begin
      CoerceToCharOrd(TStringLiteral(ABin.Right));
      RType := ABin.Right.ResolvedType;
    end
    else if (RType.Kind = tyInteger) and (ABin.Left is TStringLiteral) then
    begin
      CoerceToCharOrd(TStringLiteral(ABin.Left));
      LType := ABin.Left.ResolvedType;
    end;
    { nil can be compared with class, interface, pointer, or PChar types }
    if not (
      (LType = RType) or
      { Float comparisons: Single/Double are compatible with each other }
      (LType.IsFloat() and RType.IsFloat()) or
      { Integer/float mixing in comparisons is allowed (integer promotes) }
      (LType.IsFloat() and RType.IsNumeric()) or
      (RType.IsFloat() and LType.IsNumeric()) or
      ((LType.Kind = tyNil) and (RType.Kind in [tyClass, tyInterface, tyPointer, tyPChar])) or
      ((RType.Kind = tyNil) and (LType.Kind in [tyClass, tyInterface, tyPointer, tyPChar])) or
      ((LType.Kind = tyPointer) and (RType.Kind = tyPointer)) or
      { Class comparisons: allow subtype on either side }
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       (IsSubtypeOf(LType, RType) or IsSubtypeOf(RType, LType))) or
      { TObject is universal base class }
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       ((LType.Name = 'TObject') or (RType.Name = 'TObject'))) or
      { Metaclass comparisons: any two metaclass-typed values compare
        as pointer identity. }
      ((LType.Kind = tyMetaClass) and (RType.Kind = tyMetaClass)) or
      ((LType.Kind = tyMetaClass) and (RType.Kind in [tyPointer, tyNil])) or
      ((RType.Kind = tyMetaClass) and (LType.Kind in [tyPointer, tyNil]))
    ) then
      CheckTypesMatch(LType, RType,
        Format('comparison ''%s''', [BinaryOpName(ABin.Op)]),
        ABin.Line, ABin.Col);
    Result := FTable.TypeBoolean;
  end
  else
  begin
    { String concatenation: s1 + s2 → string }
    if (ABin.Op = boAdd) and LType.IsString() and RType.IsString() then
    begin
      Exit(FTable.TypeString);
    end;

    { Pointer arithmetic: Pointer/PChar + Integer or Integer + Pointer → same type }
    if (ABin.Op in [boAdd, boSub]) and (LType.Kind in [tyPointer, tyPChar]) and RType.IsNumeric() then
    begin
      Exit(LType);
    end;
    if (ABin.Op = boAdd) and LType.IsNumeric() and (RType.Kind in [tyPointer, tyPChar]) then
    begin
      Exit(RType);
    end;

    { Shift operators: result has the left operand's type; right is the shift amount }
    if ABin.Op in [boShl, boShr, boSar] then
    begin
      if not LType.IsNumeric() then
        SemanticError(
          Format('Left operand of ''%s'' must be numeric, got ''%s''',
            [BinaryOpName(ABin.Op), LType.Name]),
          ABin.Line, ABin.Col);
      if not RType.IsNumeric() then
        SemanticError(
          Format('Shift amount of ''%s'' must be numeric, got ''%s''',
            [BinaryOpName(ABin.Op), RType.Name]),
          ABin.Line, ABin.Col);
      Result := LType;
      ABin.ResolvedType := Result;
      Exit;
    end;

    { Operator overloading — the FALLBACK.  Every built-in rule above Exits on
      a match, so reaching here means no built-in applies; `string + string`,
      `Integer + Integer`, set algebra, pointer arithmetic and the shifts are
      structurally unreachable from this point and therefore always win.
      Only now do we look for a user-declared `class operator`.  See
      docs/language-rationale.adoc, "Operator Overloading". }
    OpType := Self.TryLowerOperator(ABin, LType, RType);
    if OpType <> nil then
      Exit(OpType);

    if not LType.IsNumeric() then
      SemanticError(
        Format('Left operand of ''%s'' must be numeric, got ''%s''',
          [BinaryOpName(ABin.Op), LType.Name]),
        ABin.Line, ABin.Col);
    if not RType.IsNumeric() then
      SemanticError(
        Format('Right operand of ''%s'' must be numeric, got ''%s''',
          [BinaryOpName(ABin.Op), RType.Name]),
        ABin.Line, ABin.Col);
    { `div` is integer division; reject float operands. }
    if (ABin.Op = boDiv) and (LType.IsFloat() or RType.IsFloat()) then
      SemanticError(
        '''div'' requires integer operands; use ''/'' for real division',
        ABin.Line, ABin.Col);
    { `/` is real division: always yields a float, even with Integer operands.
      Result is Single when both operands are Single, Double otherwise. }
    if ABin.Op = boSlash then
    begin
      if (LType.Kind = tySingle) and (RType.Kind = tySingle) then
        Result := FTable.TypeSingle
      else
        Result := FTable.TypeDouble;
    end
    { Float promotion: if either side is float, result is float.
      Double wins over Single; any integer mixed with float promotes to Double. }
    else if LType.IsFloat() or RType.IsFloat() then
    begin
      if (LType.Kind = tyDouble) or (RType.Kind = tyDouble) or
         (not LType.IsFloat()) or (not RType.IsFloat()) then
        Result := FTable.TypeDouble
      else
        Result := FTable.TypeSingle;  { Single op Single → Single }
    end
    else
    begin
      CheckTypesMatch(LType, RType, 'binary expression', ABin.Line, ABin.Col);
      { Int64 / UInt64 wins over narrower integer types so codegen emits
        l-typed instructions and the high bits are preserved.  Signed and
        unsigned 64-bit types cannot be mixed without an explicit cast. }
      if ((LType.Kind = tyInt64) and (RType.Kind = tyUInt64)) or
         ((LType.Kind = tyUInt64) and (RType.Kind = tyInt64)) then
        SemanticError(
          'Cannot mix signed Int64 and UInt64 in arithmetic without '
          + 'an explicit cast', ABin.Line, ABin.Col);
      if (LType.Kind = tyUInt64) or (RType.Kind = tyUInt64) then
        Result := FTable.TypeUInt64
      else if (LType.Kind = tyInt64) or (RType.Kind = tyInt64) then
        Result := FTable.TypeInt64
      else
        Result := LType;
    end;
  end;
end;

function TSemanticAnalyser.AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
var
  ObjType:    TTypeDesc;
  TargetType: TTypeDesc;
begin
  ObjType := Self.AnalyseExprSlot(AExpr.Obj);
  { Allow untyped Pointer on left — GetObject/Get return Pointer, used with 'is' }
  if not ((ObjType.Kind = tyClass) or (ObjType.Kind = tyPointer) or
          (ObjType.Kind = tyInterface)) then
    SemanticError(
      Format('''is'' requires a class instance on the left, got ''%s''',
        [ObjType.Name]),
      AExpr.Line, AExpr.Col);

  TargetType := FTable.FindType(AExpr.TypeName);
  if (TargetType = nil) or
     ((TargetType.Kind <> tyClass) and (TargetType.Kind <> tyInterface)) then
    SemanticError(
      Format('''is'' requires a class or interface type name on the right, got ''%s''',
        [AExpr.TypeName]),
      AExpr.Line, AExpr.Col);

  AExpr.ResolvedTargetType := TargetType;
  Result := FTable.TypeBoolean;
end;

function TSemanticAnalyser.AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;
var
  ObjType:    TTypeDesc;
  TargetType: TTypeDesc;
begin
  ObjType := Self.AnalyseExprSlot(AExpr.Obj);
  if ObjType.Kind <> tyClass then
    SemanticError(
      Format('''as'' requires a class instance on the left, got ''%s''',
        [ObjType.Name]),
      AExpr.Line, AExpr.Col);

  TargetType := FTable.FindType(AExpr.TypeName);
  if (TargetType = nil) or
     ((TargetType.Kind <> tyClass) and (TargetType.Kind <> tyInterface)) then
    SemanticError(
      Format('''as'' requires a class or interface type name on the right, got ''%s''',
        [AExpr.TypeName]),
      AExpr.Line, AExpr.Col);

  Result := TargetType;
end;

function TSemanticAnalyser.AnalyseSupportsExpr(AExpr: TSupportsExpr): TTypeDesc;
var
  ObjType:   TTypeDesc;
  IntfType:  TTypeDesc;
  OutSym:    TSymbol;
begin
  ObjType := Self.AnalyseExprSlot(AExpr.Obj);
  if not (ObjType.Kind in [tyClass, tyInterface, tyPointer]) then
    SemanticError(
      Format('Supports() requires a class or interface instance as first argument, got ''%s''',
        [ObjType.Name]),
      AExpr.Line, AExpr.Col);

  IntfType := FTable.FindType(AExpr.IntfTypeName);
  if (IntfType = nil) or (IntfType.Kind <> tyInterface) then
    SemanticError(
      Format('Supports() second argument must be an interface type name, got ''%s''',
        [AExpr.IntfTypeName]),
      AExpr.Line, AExpr.Col);

  AExpr.ResolvedIntfType := IntfType;

  if AExpr.OutVarName <> '' then
  begin
    OutSym := FTable.Lookup(AExpr.OutVarName);
    if (OutSym = nil) or (OutSym.TypeDesc = nil) or
       (OutSym.TypeDesc.Kind <> tyInterface) then
      SemanticError(
        Format('Supports() third argument must be an interface-typed variable, got ''%s''',
          [AExpr.OutVarName]),
        AExpr.Line, AExpr.Col);
    AExpr.OutVarName     := OutSym.Name;  { normalise to declared casing }
    AExpr.OutVarIsGlobal := OutSym.IsGlobal;
  end;

  Result := FTable.TypeBoolean;
  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseDerefExpr(AExpr: TDerefExpr): TTypeDesc;
var
  PtrType: TTypeDesc;
begin
  PtrType := Self.AnalyseExprSlot(AExpr.Expr);
  if PtrType.Kind <> tyPointer then
    SemanticError(
      Format('Dereference operator ''%s^'' requires a pointer type',
        [PtrType.Name]),
      AExpr.Line, AExpr.Col);
  if TPointerTypeDesc(PtrType).BaseType = nil then
    SemanticError(
      'Cannot dereference untyped ''Pointer'' — use a typed pointer (e.g. ^Integer)',
      AExpr.Line, AExpr.Col);
  Result := TPointerTypeDesc(PtrType).BaseType;
end;

procedure TSemanticAnalyser.SubstTypeParamsInStmt(AStmt: TASTStmt;
                                                  ANames, AArgs: TStringList);
begin
  if AStmt = nil then Exit;
  if (AStmt is TVarDeclStmt) and (TVarDeclStmt(AStmt).Decl <> nil) then
    TVarDeclStmt(AStmt).Decl.TypeName :=
      SubstTypeParam(TVarDeclStmt(AStmt).Decl.TypeName, ANames, AArgs)
  else if AStmt is TCompoundStmt then
    SubstTypeParamsInStmts(TCompoundStmt(AStmt).Stmts, ANames, AArgs)
  else if AStmt is TIfStmt then
  begin
    SubstTypeParamsInStmt(TIfStmt(AStmt).ThenStmt, ANames, AArgs);
    SubstTypeParamsInStmt(TIfStmt(AStmt).ElseStmt, ANames, AArgs);
  end
  else if AStmt is TWhileStmt then
    SubstTypeParamsInStmt(TWhileStmt(AStmt).Body, ANames, AArgs)
  else if AStmt is TForStmt then
    SubstTypeParamsInStmt(TForStmt(AStmt).Body, ANames, AArgs);
end;

procedure TSemanticAnalyser.SubstTypeParamsInStmts(AStmts: TObjectList;
                                                   ANames, AArgs: TStringList);
var
  I: Integer;
begin
  if AStmts = nil then Exit;
  for I := 0 to AStmts.Count - 1 do
    SubstTypeParamsInStmt(TASTStmt(AStmts.Items[I]), ANames, AArgs);
end;

procedure TSemanticAnalyser.SubstActiveTypeParamsInAnonDecl(ADecl: TMethodDecl);
var
  K:      Integer;
  Names:  TStringList;
  Args:   TStringList;
  Sym:    TSymbol;
  Par:    TMethodParam;
  VD:     TVarDecl;
begin
  if (ADecl = nil) or (FActiveTypeParams.Count = 0) then Exit;
  Names := TStringList.Create();
  Args  := TStringList.Create();
  try
    for K := 0 to FActiveTypeParams.Count - 1 do
    begin
      Sym := FTable.Lookup(FActiveTypeParams.Strings[K]);
      if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) then
      begin
        Names.Add(FActiveTypeParams.Strings[K]);
        Args.Add(Sym.TypeDesc.Name);
      end;
    end;
    if Names.Count = 0 then Exit;

    for K := 0 to ADecl.Params.Count - 1 do
    begin
      Par := TMethodParam(ADecl.Params.Items[K]);
      Par.TypeName := SubstTypeParam(Par.TypeName, Names, Args);
    end;
    ADecl.ReturnTypeName := SubstTypeParam(ADecl.ReturnTypeName, Names, Args);
    if ADecl.Body <> nil then
    begin
      for K := 0 to ADecl.Body.Decls.Count - 1 do
      begin
        VD := TVarDecl(ADecl.Body.Decls.Items[K]);
        VD.TypeName := SubstTypeParam(VD.TypeName, Names, Args);
      end;
      SubstTypeParamsInStmts(ADecl.Body.Stmts, Names, Args);
    end;
  finally
    Names.Free();
    Args.Free();
  end;
end;

function TSemanticAnalyser.IsPendingArrow(AExpr: TASTExpr): Boolean;
begin
  Result := (AExpr is TAnonMethodExpr) and TAnonMethodExpr(AExpr).IsArrow and
            (AExpr.ResolvedType = nil);
end;

procedure TSemanticAnalyser.AnalyseArgSlot(AList: TObjectList; AIdx: Integer);
var
  Slot: TASTExpr;
begin
  Slot := TASTExpr(AList.Items[AIdx]);
  Self.AnalyseArgOrDeferArrow(Slot);
  Self.UnwrapLoweredOperator(Slot);
  AList.Items[AIdx] := Slot;
end;

procedure TSemanticAnalyser.AnalyseArgOrDeferArrow(AExpr: TASTExpr);
begin
  if not IsPendingArrow(AExpr) then
    AnalyseExpr(AExpr);
end;

procedure TSemanticAnalyser.ResolveDeferredArrowArgs(AArgs: TObjectList;
  AMDecl: TMethodDecl);
var
  I:   Integer;
  Par: TMethodParam;
begin
  if AMDecl = nil then Exit;
  for I := 0 to AArgs.Count - 1 do
    if IsPendingArrow(TASTExpr(AArgs.Items[I])) and
       (I < AMDecl.Params.Count) then
    begin
      Par := TMethodParam(AMDecl.Params.Items[I]);
      InferArrowFromTarget(TASTExpr(AArgs.Items[I]), Par.ResolvedType);
      AnalyseExpr(TASTExpr(AArgs.Items[I]));
    end;
end;

procedure TSemanticAnalyser.InferArrowFromTarget(AExpr: TASTExpr;
  ATarget: TTypeDesc);
var
  AME:   TAnonMethodExpr;
  PT:    TProceduralTypeDesc;
  Par:   TMethodParam;
  PInfo: TProcParamInfo;
  Blk:   TBlock;
  Asn:   TAssignment;
  PC:    TProcCall;
  MCS:   TMethodCallStmt;
  FCE:   TFuncCallExpr;
  MCE:   TMethodCallExpr;
  I:     Integer;
begin
  if not (AExpr is TAnonMethodExpr) then Exit;
  AME := TAnonMethodExpr(AExpr);
  if not AME.IsArrow then Exit;
  if AME.ResolvedType <> nil then Exit;   { already analysed }

  if (ATarget = nil) or (ATarget.Kind <> tyProcedural) or
     (not TProceduralTypeDesc(ATarget).IsReference) then
    SemanticError(
      'Cannot infer the type of a ''->'' lambda here — the target must be ' +
      'a named ''reference to'' type (use a full function/procedure literal ' +
      'with explicit types instead)',
      AME.Line, AME.Col);
  PT := TProceduralTypeDesc(ATarget);

  if AME.Decl.Params.Count <> PT.Params.Count then
    SemanticError(Format(
      '''->'' lambda has %d parameter(s) but the target type expects %d',
      [AME.Decl.Params.Count, PT.Params.Count]), AME.Line, AME.Col);

  for I := 0 to AME.Decl.Params.Count - 1 do
  begin
    Par   := TMethodParam(AME.Decl.Params.Items[I]);
    PInfo := TProcParamInfo(PT.Params.Items[I]);
    if Par.TypeName = '' then
    begin
      Par.TypeName     := PInfo.TypeDesc.Name;
      Par.ResolvedType := PInfo.TypeDesc;
      Par.IsVarParam   := PInfo.IsVarParam;
      Par.IsConstParam := PInfo.IsConstParam;
    end;
  end;

  { Single-expression body: desugar now that function-vs-procedure is known. }
  if AME.ArrowExpr <> nil then
  begin
    Blk := TBlock.Create();
    if PT.ReturnType <> nil then
    begin
      Asn := TAssignment.Create();
      Asn.Line := AME.ArrowExpr.Line;
      Asn.Col  := AME.ArrowExpr.Col;
      Asn.Name := 'Result';
      Asn.Expr := AME.ArrowExpr;
      Blk.Stmts.Add(Asn);
    end
    else if AME.ArrowExpr is TFuncCallExpr then
    begin
      { Procedure target with a call body: re-shape the parsed call
        expression into a call statement (ownership of the args moves). }
      FCE := TFuncCallExpr(AME.ArrowExpr);
      PC  := TProcCall.Create();
      PC.Line := FCE.Line;
      PC.Col  := FCE.Col;
      PC.Name := FCE.Name;
      while FCE.Args.Count > 0 do
      begin
        PC.Args.Add(FCE.Args.Items[0]);
        FCE.Args.Delete(0);
      end;
      Blk.Stmts.Add(PC);
      AME.ArrowExpr.Free();
    end
    else if AME.ArrowExpr is TMethodCallExpr then
    begin
      MCE := TMethodCallExpr(AME.ArrowExpr);
      MCS := TMethodCallStmt.Create();
      MCS.Line := MCE.Line;
      MCS.Col  := MCE.Col;
      MCS.ObjectName := MCE.ObjectName;
      MCS.Name       := MCE.Name;
      MCS.ObjExpr    := MCE.ObjExpr;
      MCE.ObjExpr    := nil;
      while MCE.Args.Count > 0 do
      begin
        MCS.Args.Add(MCE.Args.Items[0]);
        MCE.Args.Delete(0);
      end;
      Blk.Stmts.Add(MCS);
      AME.ArrowExpr.Free();
    end
    else
      SemanticError(
        'A ''->'' lambda for a procedure target must have a call body or ' +
        'a begin..end block', AME.Line, AME.Col);
    AME.ArrowExpr := nil;
    AME.Decl.Body := Blk;
    AME.Decl.OwnBody := True;
  end;

  if PT.ReturnType <> nil then
    AME.Decl.ReturnTypeName := PT.ReturnType.Name;

  AME.IsArrow := False;   { inferred — analyse as an ordinary literal }
end;

function TSemanticAnalyser.AnalyseAnonMethodExpr(AExpr: TAnonMethodExpr): TTypeDesc;
{ Anonymous procedure/function literal (docs/anonymous-methods-design.adoc,
  Phase 1: capture-free).  Two products:

  1. The literal's structural signature: an unnamed TProceduralTypeDesc with
     IsReference = True built from the declared params and return type.
     CheckTypesMatch then accepts the literal against any identically-shaped
     named 'reference to' type via IsCompatibleWith — no target-typing needed
     because the literal is fully typed by the grammar.

  2. The lifted thunk: a hidden module-level routine '__closure_<n>' with the
     uniform closure ABI — the environment pointer arrives as a hidden
     '__env: Pointer' FIRST parameter (unused by capture-free bodies; the
     call site always passes the fat value's Env half).  The thunk shares
     the literal's Body (OwnBody = False) and is queued on
     FPendingAnonDecls; DrainPendingAnonDecls registers and analyses it in
     MODULE scope after the enclosing bodies complete, so a body that
     references an enclosing local fails with a clear undeclared-variable
     error instead of silently miscompiling — capture promotion is Phase 2. }
var
  ProcDesc:  TProceduralTypeDesc;
  MD:        TMethodDecl;
  Par:       TMethodParam;
  EnvPar:    TMethodParam;
  ProcParam: TProcParamInfo;
  ValVD:     TVarDecl;
  I:         Integer;
begin
  if AExpr.ResolvedType <> nil then Exit(AExpr.ResolvedType);  { idempotent }

  { Phase 9a: an arrow lambda that reaches full analysis without a target
    (no assignment/field/var-init context supplied one) cannot be typed. }
  if AExpr.IsArrow then
    SemanticError(
      'Cannot infer the type of a ''->'' lambda here — assign it to a ' +
      '''reference to''-typed variable/field first, or use a full ' +
      'function/procedure literal with explicit types',
      AExpr.Line, AExpr.Col);

  { Phase 6: make type-param names concrete while the instantiation's
    bindings are still in scope (the lifted thunk is analysed later in
    module scope, where they are gone). }
  SubstActiveTypeParamsInAnonDecl(AExpr.Decl);

  ProcDesc := FTable.NewProceduralType('');
  ProcDesc.IsReference := True;
  for I := 0 to AExpr.Decl.Params.Count - 1 do
  begin
    Par := TMethodParam(AExpr.Decl.Params.Items[I]);
    Par.ResolvedType := ResolveParamType(Par, AExpr.Line, AExpr.Col);
    ProcParam := TProcParamInfo.Create();
    ProcParam.Name         := Par.ParamName;
    ProcParam.TypeDesc     := Par.ResolvedType;
    ProcParam.IsVarParam   := Par.IsVarParam;
    ProcParam.IsConstParam := Par.IsConstParam;
    ProcDesc.Params.Add(ProcParam);
  end;
  if AExpr.Decl.ReturnTypeName <> '' then
  begin
    ProcDesc.ReturnType := FindTypeOrInstantiate(AExpr.Decl.ReturnTypeName);
    if ProcDesc.ReturnType = nil then
      SemanticError(Format(
        'Unknown return type ''%s'' in anonymous method',
        [AExpr.Decl.ReturnTypeName]), AExpr.Line, AExpr.Col);
  end;

  if AExpr.LiftedDecl = nil then
  begin
    FAnonMethodCount := FAnonMethodCount + 1;
    MD := TMethodDecl.Create();
    MD.Line := AExpr.Line;
    MD.Col  := AExpr.Col;
    MD.Name := '__closure_' + IntToStr(FAnonMethodCount);
    MD.ReturnTypeName := AExpr.Decl.ReturnTypeName;
    EnvPar := TMethodParam.Create();
    EnvPar.ParamName := '__env';
    EnvPar.TypeName  := 'Pointer';
    MD.Params.Add(EnvPar);
    for I := 0 to AExpr.Decl.Params.Count - 1 do
      MD.Params.Add(CloneMethodParam(TMethodParam(AExpr.Decl.Params.Items[I])));
    MD.Body       := AExpr.Decl.Body;
    MD.OwnBody    := False;     { the literal's Decl keeps ownership }
    MD.IsImplOnly := FCurrentUnit <> nil;
    AExpr.LiftedName := MD.Name;
    AExpr.LiftedDecl := MD;
    MD.IsAnonThunk := True;
    { Hidden VALUE slot for argument-position materialisation: a 16-byte
      local of this literal's reference type in the enclosing frame.  The
      native backend builds the fat value here when the literal is consumed
      as a call argument; the slot participates in the ordinary zero-init
      and reference-local scope-exit release passes, so its env reference
      is balanced without a bespoke cleanup path. }
    AExpr.ValueSlotName := '__anonv_' + IntToStr(FAnonMethodCount);
    ValVD := TVarDecl.Create();
    ValVD.Names.Add(AExpr.ValueSlotName);
    ValVD.TypeName := '';
    ValVD.ResolvedType := ProcDesc;
    if FCurrentEnclosingDecl <> nil then
      FCurrentEnclosingDecl.Body.Decls.Add(ValVD)
    else if FCurrentMethodDecl <> nil then
      FCurrentMethodDecl.Body.Decls.Add(ValVD)
    else if (FProg <> nil) and (FProg.Block <> nil) then
      FProg.Block.Decls.Add(ValVD)
    else if (FCurrentUnit <> nil) and (FCurrentUnit.ImplBlock <> nil) then
      FCurrentUnit.ImplBlock.Decls.Add(ValVD)
    else
      ValVD.Free();
    { Phase 5: [Weak name] capture-modifier list.  v1 supports [Weak Self]
      only — the cycle-breaking case (closure stored in its own receiver).
      Validated and applied during capture promotion below. }
    if AExpr.WeakCaptures <> nil then
    begin
      { Directly inside a method body FCurrentEnclosingDecl is now the
        method itself (recorded for nested-routine resolution, BUG-008) —
        only a DIFFERENT enclosing frame (nested routine, standalone proc)
        disqualifies [Weak]. }
      if (FCurrentEnclosingDecl <> nil) and
         (FCurrentEnclosingDecl <> FCurrentMethodDecl) then
        SemanticError('[Weak] capture is only supported for Self inside ' +
          'an instance method body', AExpr.Line, AExpr.Col);
      for I := 0 to AExpr.WeakCaptures.Count - 1 do
        if not SameText(AExpr.WeakCaptures.Strings[I], 'Self') then
          SemanticError(Format('[Weak] capture of ''%s'' is not yet ' +
            'supported — only [Weak Self] (weak capture of ordinary ' +
            'variables is a later extension)',
            [AExpr.WeakCaptures.Strings[I]]), AExpr.Line, AExpr.Col);
      MD.WantsWeakSelf := True;
    end;
    FPendingAnonDecls.Add(MD);
    { Phase 2/3: capture promotion.  Runs NOW, while the enclosing frame's
      scope is live, so captured names can be typed from their symbols.
      Standalone routines (Phase 2) and instance-method bodies (Phase 3 —
      Self is captured conservatively) are supported; record methods are
      not (the receiver is a caller-frame record, not an ARC instance). }
    if FCurrentEnclosingDecl <> nil then
      PromoteAnonCaptures(MD)
    else if (FCurrentMethodDecl <> nil) and (FCurrentClass <> nil) and
            (not FCurrentMethodDecl.IsRecordMethod) then
      PromoteAnonCaptures(MD);
  end;

  AExpr.ResolvedType := ProcDesc;
  Result := ProcDesc;
end;

procedure TSemanticAnalyser.AnalyseVarDeclStmt(AStmt: TVarDeclStmt);
{ Block-scoped 'var Name: Type [:= Expr]' statement (Phase 4).  The name is
  defined in the CURRENT scope (pushed by the enclosing compound statement,
  popped at its end).  Storage is a frame slot: the decl MOVES into the
  enclosing routine's Body.Decls.  The optional initialiser becomes a
  synthesised assignment (InitAssign) emitted each time the statement
  executes; when the variable is captured, the block allocates a FRESH env
  per execution at the first such declaration (the env-alloc site). }
var
  Frame: TMethodDecl;
  Name:  string;
  T:     TTypeDesc;
  Sym:   TSymbol;
  Asn:   TAssignment;
begin
  Frame := FCurrentEnclosingDecl;
  if Frame = nil then Frame := FCurrentMethodDecl;
  if Frame = nil then
    SemanticError('Block-scoped ''var'' is only allowed inside a routine ' +
      'or method body', AStmt.Line, AStmt.Col);
  Name := AStmt.Decl.Names.Strings[0];
  Sym := FTable.Lookup(Name);
  if (Sym <> nil) and (not Sym.IsGlobal) then
    SemanticError(Format('Duplicate identifier ''%s'' — a block-scoped ' +
      'var may not shadow an existing local', [Name]), AStmt.Line, AStmt.Col);
  T := FindTypeOrInstantiate(AStmt.Decl.TypeName);
  if T = nil then
    SemanticError(Format('Unknown type ''%s''', [AStmt.Decl.TypeName]),
      AStmt.Line, AStmt.Col);
  AStmt.Decl.ResolvedType := T;
  if AStmt.DeclOwned then
  begin
    Frame.Body.Decls.Add(AStmt.Decl);
    AStmt.DeclOwned := False;
  end;
  { This statement is the block's env-alloc site if it is the FIRST block
    var of the current compound. }
  if FCurrentBlockFirstSite = nil then
    FCurrentBlockFirstSite := AStmt;
  Sym := TSymbol.Create(Name, skVariable, T);
  Sym.BlockSite := FCurrentBlockFirstSite;
  FTable.Define(Sym);
  if (AStmt.InitExpr <> nil) and (AStmt.InitAssign = nil) then
  begin
    Asn := TAssignment.Create();
    Asn.Line := AStmt.Line;
    Asn.Col  := AStmt.Col;
    Asn.Name := Name;
    Asn.Expr := AStmt.InitExpr;
    AStmt.InitExpr := nil;   { ownership moves to the assignment }
    AStmt.InitAssign := Asn;
  end;
  if AStmt.InitAssign <> nil then
    AnalyseStmt(AStmt.InitAssign);
end;

procedure TSemanticAnalyser.PromoteAnonCaptures(AThunk: TMethodDecl);
{ Phase 2 of docs/anonymous-methods-design.adoc: determine which enclosing
  locals/params the literal's body references, promote them into ONE shared
  heap environment record per enclosing frame (TRecordTypeDesc '__env_<n>'
  — field offsets, alignment and ARC cleanup come free from the record
  machinery), and record the capture facts on both decls:

    enclosing.EnvCaptured / EnvType — fields of the env the frame allocates
    thunk.EnvCaptured / EnvType     — names the body reads via '__env'

  Codegen redirects accesses by name (the '_cap_' mechanism generalised);
  no AST rewriting.  Reuses the nested-proc capture walker CollectCaptures,
  which deposits into CapturedVars — the result is MOVED to EnvCaptured so
  the hidden-var-param nested-proc codegen path never sees it. }
var
  Encl:  TMethodDecl;
  Env:   TRecordTypeDesc;
  Name:  string;
  Sym:   TSymbol;
  Par:   TMethodParam;
  VDecl: TVarDecl;
  Own:   Boolean;
  InMethod: Boolean;
  SelfJustAdded: Boolean;
  BlockSite: TObject;
  HasFrameNames: Boolean;
  Site:  TVarDeclStmt;
  I, J:  Integer;
begin
  Encl := FCurrentEnclosingDecl;
  InMethod := False;
  if Encl = nil then
  begin
    { Phase 3: the enclosing frame is an instance-method body. }
    Encl := FCurrentMethodDecl;
    InMethod := True;
  end
  else if (FCurrentMethodDecl <> nil) and (Encl = FCurrentMethodDecl) then
    { AnalyseMethodDecl records the method as FCurrentEnclosingDecl so its
      NESTED ROUTINES resolve (BUG-008) — a literal directly inside the
      method body is still the InMethod case (conservative Self capture). }
    InMethod := True;
  if Encl.IsAnonThunk then
    SemanticError('Capturing variables of an enclosing anonymous method ' +
      'is not yet supported (nested closure environments are a later phase)',
      AThunk.Line, AThunk.Col);

  CollectCaptures(AThunk, Encl);
  { An anonymous method inside a CLASSIC NESTED ROUTINE of a method cannot
    capture Self yet: the nested routine holds Self behind a hidden by-
    pointer capture param (BUG-008), and the env-fill machinery has no path
    from that to a heap env field.  Reject cleanly rather than miscompile. }
  if (not InMethod) and FInNestedOfMethod and
     (AThunk.CapturedVars <> nil) and
     (AThunk.CapturedVars.IndexOf('Self') >= 0) then
    SemanticError('Self cannot be captured by an anonymous method declared ' +
      'inside a nested routine of a method', AThunk.Line, AThunk.Col);
  if (AThunk.CapturedVars = nil) and (not InMethod) then Exit;

  { Drop names shadowed by the literal's own params or locals — the walker
    only checks the OUTER name set, not the literal's own declarations. }
  if AThunk.CapturedVars <> nil then
    for I := AThunk.CapturedVars.Count - 1 downto 0 do
    begin
      Name := AThunk.CapturedVars.Strings[I];
      Own := False;
      for J := 0 to AThunk.Params.Count - 1 do
        if SameText(TMethodParam(AThunk.Params.Items[J]).ParamName, Name) then
          Own := True;
      if AThunk.Body <> nil then
        for J := 0 to AThunk.Body.Decls.Count - 1 do
        begin
          VDecl := TVarDecl(AThunk.Body.Decls.Items[J]);
          if VDecl.Names.IndexOf(Name) >= 0 then Own := True;
        end;
      if Own then AThunk.CapturedVars.Delete(I);
    end;
  { Classify captures: BLOCK-SCOPED names (declared by a 'var' statement,
    Phase 4) belong to their declaring block's per-execution env; all other
    names belong to the routine-level frame env.  v1 supports ONE scope per
    closure — mixing block-scoped and routine-level (or Self) captures in a
    single literal needs environment chaining, which is deferred. }
  BlockSite := nil;
  HasFrameNames := False;
  if AThunk.CapturedVars <> nil then
    for I := 0 to AThunk.CapturedVars.Count - 1 do
    begin
      Sym := FTable.Lookup(AThunk.CapturedVars.Strings[I]);
      if (Sym <> nil) and (Sym.BlockSite <> nil) then
      begin
        if (BlockSite <> nil) and (BlockSite <> Sym.BlockSite) then
          SemanticError('Capturing block-scoped variables from different ' +
            'blocks in one anonymous method is not yet supported',
            AThunk.Line, AThunk.Col);
        BlockSite := Sym.BlockSite;
      end
      else
        HasFrameNames := True;
    end;
  if (BlockSite <> nil) and HasFrameNames then
    SemanticError('Capturing both block-scoped and routine-level variables ' +
      'in one anonymous method is not yet supported — move the routine-level ' +
      'value into a block-scoped var', AThunk.Line, AThunk.Col);

  if BlockSite <> nil then
  begin
    { Per-execution BLOCK env: created/extended on the alloc-site stmt. }
    Site := TVarDeclStmt(BlockSite);
    if Site.EnvType = nil then
    begin
      FEnvTypeCount := FEnvTypeCount + 1;
      Site.EnvType := FTable.NewRecordType(
        CurrentUnitPrefix() + '__env_' + IntToStr(FEnvTypeCount));
      Site.IsEnvAllocSite := True;
      if Encl.BlockEnvTypes = nil then
        Encl.BlockEnvTypes := TObjectList.Create(False);
      Site.EnvSlotName := '__envp_b' + IntToStr(Encl.BlockEnvTypes.Count);
      Encl.BlockEnvTypes.Add(Site.EnvType);
    end;
    Env := TRecordTypeDesc(Site.EnvType);
    if Encl.BlockEnvCaptured = nil then
      Encl.BlockEnvCaptured := TStringList.Create();
    for I := 0 to AThunk.CapturedVars.Count - 1 do
    begin
      Name := AThunk.CapturedVars.Strings[I];
      if Env.FindField(Name) = nil then
      begin
        Sym := FTable.Lookup(Name);
        if (Sym = nil) or (Sym.TypeDesc = nil) then
          SemanticError(Format('Cannot resolve captured variable ''%s''',
            [Name]), AThunk.Line, AThunk.Col);
        Env.AddField(Name, Sym.TypeDesc);
      end;
      if Encl.BlockEnvCaptured.IndexOf(Name) < 0 then
        Encl.BlockEnvCaptured.Add(Name);
    end;
    AThunk.EnvCaptured := AThunk.CapturedVars;
    AThunk.CapturedVars := nil;
    AThunk.EnvType := Env;
    AThunk.EnvSlotName := Site.EnvSlotName;
    Exit;
  end;

  { Inside an instance method, Self is captured CONSERVATIVELY (whether or
    not the body names it): implicit member access cannot be detected
    syntactically before analysis, and the cost is one env field.  This
    also matches the strong-retain lifetime rule — a callback keeps its
    receiver alive.  (The [Weak] escape is Phase 5.) }
  if InMethod then
  begin
    if AThunk.CapturedVars = nil then
      AThunk.CapturedVars := TStringList.Create();
    if AThunk.CapturedVars.IndexOf('Self') < 0 then
      AThunk.CapturedVars.Add('Self');
  end;
  if AThunk.CapturedVars = nil then Exit;
  if AThunk.CapturedVars.Count = 0 then
  begin
    AThunk.CapturedVars.Free();
    AThunk.CapturedVars := nil;
    Exit;
  end;

  { v1 restriction: a var/out parameter's storage belongs to the CALLER
    frame; capturing its address in an escaping closure dangles.  Escape
    analysis is deferred — reject with a clear diagnostic (design doc,
    Risks).  Capture a local copy instead. }
  for I := 0 to AThunk.CapturedVars.Count - 1 do
  begin
    Name := AThunk.CapturedVars.Strings[I];
    for J := 0 to Encl.Params.Count - 1 do
    begin
      Par := TMethodParam(Encl.Params.Items[J]);
      if SameText(Par.ParamName, Name) and Par.IsVarParam then
        SemanticError(Format('Cannot capture var/out parameter ''%s'' in ' +
          'an anonymous method — capture a local copy instead', [Name]),
          AThunk.Line, AThunk.Col);
    end;
  end;

  { Build (or extend) the enclosing frame's shared env record. }
  if Encl.EnvCaptured = nil then
  begin
    Encl.EnvCaptured := TStringList.Create();
    FEnvTypeCount := FEnvTypeCount + 1;
    Encl.EnvType := FTable.NewRecordType(
      CurrentUnitPrefix() + '__env_' + IntToStr(FEnvTypeCount));
  end;
  Env := TRecordTypeDesc(Encl.EnvType);

  SelfJustAdded := False;
  for I := 0 to AThunk.CapturedVars.Count - 1 do
  begin
    Name := AThunk.CapturedVars.Strings[I];
    if Encl.EnvCaptured.IndexOf(Name) < 0 then
    begin
      Sym := FTable.Lookup(Name);
      if (Sym = nil) or (Sym.TypeDesc = nil) then
        SemanticError(Format('Cannot resolve captured variable ''%s''',
          [Name]), AThunk.Line, AThunk.Col);
      Env.AddField(Name, Sym.TypeDesc);
      Encl.EnvCaptured.Add(Name);
      if Name = 'Self' then SelfJustAdded := True;
    end;
  end;

  { Phase 5: [Weak Self] — mark the shared env's Self field weak so it is
    stored via the weak registry, auto-nil'd when the receiver dies, and
    skipped by the env cleanup (both behaviours come free from the [Weak]
    class-field machinery).  The field is SHARED by every literal in the
    frame, so all of them must agree on its weakness. }
  if Env.FindField('Self') <> nil then
  begin
    if SelfJustAdded then
      Env.FindField('Self').IsWeak := AThunk.WantsWeakSelf
    else if Env.FindField('Self').IsWeak <> AThunk.WantsWeakSelf then
      SemanticError('Conflicting Self capture: every anonymous method in ' +
        'one frame must agree on [Weak Self] (the env''s Self field is ' +
        'shared)', AThunk.Line, AThunk.Col);
  end;

  { Hand the capture list to the env channel; CapturedVars must stay nil so
    the nested-proc hidden-param path ignores the thunk. }
  AThunk.EnvCaptured := AThunk.CapturedVars;
  AThunk.CapturedVars := nil;
  AThunk.EnvType := Env;
end;

procedure TSemanticAnalyser.DrainPendingAnonDecls(ABlock: TBlock);
{ Register and analyse every lifted anonymous-method thunk queued during
  body analysis.  Runs in MODULE scope (the enclosing routine's locals are
  no longer visible — see AnalyseAnonMethodExpr).  Appends each thunk to
  ABlock.ProcDecls so both backends emit it like any standalone routine.
  A while-loop because a literal nested inside another literal's body
  queues further thunks during AnalyseStandaloneDecl. }
var
  MD:      TMethodDecl;
  Par:     TMethodParam;
  RetType: TTypeDesc;
  I:       Integer;
begin
  while FPendingAnonDecls.Count > 0 do
  begin
    MD := TMethodDecl(FPendingAnonDecls.Get(0));
    FPendingAnonDecls.Delete(0);
    { The signature facts AnalyseStandaloneDecls would have computed. }
    for I := 0 to MD.Params.Count - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Par.ResolvedType := ResolveParamType(Par, MD.Line, MD.Col);
    end;
    if MD.ReturnTypeName <> '' then
    begin
      RetType := FindTypeOrInstantiate(MD.ReturnTypeName);
      if RetType = nil then
        SemanticError(Format(
          'Unknown return type ''%s'' in anonymous method',
          [MD.ReturnTypeName]), MD.Line, MD.Col);
      MD.ResolvedReturnType := RetType;
    end;
    MD.ResolvedQbeName := CurrentUnitPrefix() + MD.Name;
    ABlock.ProcDecls.Add(MD);
    AnalyseStandaloneDecl(MD);
  end;
end;

procedure TSemanticAnalyser.CoerceRoutineToClosure(AAssign: TAssignment);
{ '@Routine' assigned to a 'reference to' variable: desugar the RHS into a
  capture-free anonymous-method literal that forwards to the routine — the
  design's "adapter thunk" (docs/anonymous-methods-design.adoc,
  Conversions).  The literal then flows through AnalyseAnonMethodExpr and
  ordinary codegen, so both backends get the adapter for free and the
  signature is validated by the forwarding call + CheckTypesMatch.
  Method-pointer coercion (strong-retained receiver) is a later phase.
  Callers guard: LHS type is tyProcedural with IsReference. }
var
  Sym:     TSymbol;
  MD:      TMethodDecl;
  AME:     TAnonMethodExpr;
  NewDecl: TMethodDecl;
  FCall:   TFuncCallExpr;
  PCall:   TProcCall;
  Asn:     TAssignment;
  Idn:     TIdentExpr;
  Par:     TMethodParam;
  I:       Integer;
begin
  if not (AAssign.Expr is TAddrOfExpr) then Exit;
  if not (TAddrOfExpr(AAssign.Expr).Expr is TIdentExpr) then Exit;
  Sym := FTable.Lookup(TIdentExpr(TAddrOfExpr(AAssign.Expr).Expr).Name);
  if (Sym = nil) or not (Sym.Kind in [skFunction, skProcedure]) then Exit;
  if Sym.Decl = nil then Exit;
  MD := TMethodDecl(Sym.Decl);

  AME      := TAnonMethodExpr.Create();
  AME.Line := AAssign.Line;
  AME.Col  := AAssign.Col;
  NewDecl  := TMethodDecl.Create();
  NewDecl.Line := AAssign.Line;
  NewDecl.Col  := AAssign.Col;
  NewDecl.ReturnTypeName := MD.ReturnTypeName;
  for I := 0 to MD.Params.Count - 1 do
    NewDecl.Params.Add(CloneMethodParam(TMethodParam(MD.Params.Items[I])));
  NewDecl.Body := TBlock.Create();
  if MD.ReturnTypeName <> '' then
  begin
    FCall := TFuncCallExpr.Create();
    FCall.Line := AAssign.Line;
    FCall.Col  := AAssign.Col;
    FCall.Name := MD.Name;
    for I := 0 to MD.Params.Count - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Idn := TIdentExpr.Create();
      Idn.Line := AAssign.Line;
      Idn.Col  := AAssign.Col;
      Idn.Name := Par.ParamName;
      FCall.Args.Add(Idn);
    end;
    Asn := TAssignment.Create();
    Asn.Line := AAssign.Line;
    Asn.Col  := AAssign.Col;
    Asn.Name := 'Result';
    Asn.Expr := FCall;
    NewDecl.Body.Stmts.Add(Asn);
  end
  else
  begin
    PCall := TProcCall.Create();
    PCall.Line := AAssign.Line;
    PCall.Col  := AAssign.Col;
    PCall.Name := MD.Name;
    for I := 0 to MD.Params.Count - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Idn := TIdentExpr.Create();
      Idn.Line := AAssign.Line;
      Idn.Col  := AAssign.Col;
      Idn.Name := Par.ParamName;
      PCall.Args.Add(Idn);
    end;
    NewDecl.Body.Stmts.Add(PCall);
  end;
  AME.Decl := NewDecl;
  AAssign.Expr.Free();
  AAssign.Expr := AME;
end;

function TSemanticAnalyser.AnalyseAddrOfExpr(AExpr: TAddrOfExpr): TTypeDesc;
var
  InnerType: TTypeDesc;
  PtrName: string;
  PT: TPointerTypeDesc;
  Sym, FSym: TSymbol;
  IdentExpr: TIdentExpr;
  FldExpr: TFieldAccessExpr;
  ProcDesc: TProceduralTypeDesc;
  ProcParam: TProcParamInfo;
  MD: TMethodDecl;
  MParam: TMethodParam;
  BaseType: TTypeDesc;
  Idx, K: Integer;
begin
  { @FuncName / @ProcName — if the inner is a bare identifier that
    resolves to a standalone function or procedure, build a procedural
    type matching the function's signature and return it.  This must run
    before AnalyseExpr, which would treat a zero-arg function reference
    as an implicit call. }
  if AExpr.Expr is TIdentExpr then
  begin
    IdentExpr := TIdentExpr(AExpr.Expr);
    FSym := FTable.Lookup(IdentExpr.Name);
    if (FSym <> nil) and (FSym.Kind in [skFunction, skProcedure]) then
    begin
      { Prefer the SCOPED symbol's own backing decl over a bare-name lookup in
        the global FProcIndex: when two units each declare a same-named file-
        local routine (e.g. two test units both defining ServerFiber), the
        FProcIndex bare-name IndexOf returns the FIRST match, so @ServerFiber
        in one unit would resolve to the OTHER unit's mangled symbol (an
        undefined cross-object reference under separate compilation). FSym.Decl
        already points at the correctly-scoped routine. }
      MD := nil;
      if FSym.Decl <> nil then
        MD := TMethodDecl(FSym.Decl);
      if MD = nil then
      begin
        Idx := FProcIndex.IndexOf(IdentExpr.Name);
        if Idx < 0 then
          SemanticError(Format('Internal: function ''%s'' not in proc index',
            [IdentExpr.Name]), AExpr.Line, AExpr.Col);
        MD := TMethodDecl(FProcIndex.Objects[Idx]);
      end;
      ProcDesc := FTable.NewProceduralType('');
      for K := 0 to MD.Params.Count - 1 do
      begin
        MParam := TMethodParam(MD.Params.Items[K]);
        ProcParam := TProcParamInfo.Create();
        ProcParam.Name         := MParam.ParamName;
        ProcParam.TypeDesc     := MParam.ResolvedType;
        ProcParam.IsVarParam   := MParam.IsVarParam;
        ProcParam.IsConstParam := MParam.IsConstParam;
        ProcDesc.Params.Add(ProcParam);
      end;
      ProcDesc.ReturnType := MD.ResolvedReturnType;  { nil for procedure }
      Result := ProcDesc;
      IdentExpr.ResolvedType := ProcDesc;
      { Stash the resolved decl on the address-of node so codegen can
        read MD.ResolvedQbeName directly — keeps the mangled label
        out of TIdentExpr and lets a future patch evolve the mangling
        without touching every reference site. }
      AExpr.ResolvedFreeRoutine := MD;
      AExpr.ResolvedType := Result;
      Exit;
    end;
  end;

  { @Obj.MethodName — method pointer construction.  The inner expression is a
    TFieldAccessExpr whose base is a class instance and whose field name
    resolves to a method on that class.  Build a method-pointer type
    (IsMethodPtr = True) that pairs the method code with the object pointer.
    Two forms: Obj.Method (RecordName set, Base=nil) and Expr.Method (Base set). }
  if AExpr.Expr is TFieldAccessExpr then
  begin
    FldExpr  := TFieldAccessExpr(AExpr.Expr);
    { Determine base type from either RecordName or Base expression }
    if FldExpr.Base = nil then
    begin
      { Simple form: @VarName.MethodName — look up VarName }
      Sym := FTable.Lookup(FldExpr.RecordName);
      if (Sym <> nil) and
         (Sym.Kind in [skVariable, skParameter, skVarParameter]) and
         (Sym.TypeDesc <> nil) and (Sym.TypeDesc.Kind = tyClass) then
        BaseType := Sym.TypeDesc
      else
        BaseType := nil;
      if BaseType <> nil then
      begin
        FldExpr.RecordName := Sym.Name;  { normalise to declared casing }
        FldExpr.IsGlobal := Sym.IsGlobal;
      end;
    end
    else
      BaseType := Self.AnalyseExprSlot(FldExpr.Base);
    if (BaseType <> nil) and (BaseType.Kind = tyClass) then
    begin
      MD := FindMethodDecl(TRecordTypeDesc(BaseType).Name, FldExpr.FieldName);
      if MD <> nil then
      begin
        FldExpr.IsClassAccess  := True;
        FldExpr.IsMethodCall   := False;  { @Obj.M is not a call }
        FldExpr.ResolvedMethod := MD;
        ProcDesc := FTable.NewProceduralType('');
        ProcDesc.IsMethodPtr := True;
        for K := 0 to MD.Params.Count - 1 do
        begin
          MParam := TMethodParam(MD.Params.Items[K]);
          ProcParam := TProcParamInfo.Create();
          ProcParam.Name         := MParam.ParamName;
          ProcParam.TypeDesc     := MParam.ResolvedType;
          ProcParam.IsVarParam   := MParam.IsVarParam;
          ProcParam.IsConstParam := MParam.IsConstParam;
          ProcDesc.Params.Add(ProcParam);
        end;
        ProcDesc.ReturnType := MD.ResolvedReturnType;
        FldExpr.ResolvedType := ProcDesc;
        AExpr.ResolvedType   := ProcDesc;
        Exit(ProcDesc);
      end;
    end;
  end;
  InnerType := Self.AnalyseExprSlot(AExpr.Expr);
  PtrName := '^' + InnerType.Name;
  Result := FindTypeOrInstantiate(PtrName);
  if Result = nil then
  begin
    PT := FTable.NewPointerType(PtrName, InnerType);
    Sym := TSymbol.Create(PtrName, skType, PT);
    FTable.DefineGlobal(Sym);
    Result := PT;
  end;
  AExpr.ResolvedType := Result;
end;

procedure TSemanticAnalyser.ResolveProceduralTypeDef(ATD: TTypeDecl);
var
  Def: TProceduralTypeDef;
  ProcDesc: TProceduralTypeDesc;
  Sym: TSymbol;
  K: Integer;
  MParam: TMethodParam;
  ProcParam: TProcParamInfo;
  TSym: TSymbol;
begin
  Def := TProceduralTypeDef(ATD.Def);
  Sym := FTable.Lookup(ATD.Name);
  if (Sym = nil) or not (Sym.TypeDesc is TProceduralTypeDesc) then
    SemanticError(Format('Internal: procedural type ''%s'' not registered',
      [ATD.Name]), ATD.Line, ATD.Col);
  ProcDesc := TProceduralTypeDesc(Sym.TypeDesc);
  ProcDesc.IsMethodPtr := Def.IsMethodPtr;
  ProcDesc.IsReference := Def.IsReference;
  for K := 0 to Def.Params.Count - 1 do
  begin
    MParam := TMethodParam(Def.Params.Items[K]);
    TSym   := FTable.Lookup(MParam.TypeName);
    if (TSym = nil) or (TSym.Kind <> skType) then
      SemanticError(Format(
        'Unknown parameter type ''%s'' in procedural type ''%s''',
        [MParam.TypeName, ATD.Name]), ATD.Line, ATD.Col);
    MParam.ResolvedType := TSym.TypeDesc;
    ProcParam := TProcParamInfo.Create();
    ProcParam.Name         := MParam.ParamName;
    ProcParam.TypeDesc     := TSym.TypeDesc;
    ProcParam.IsVarParam   := MParam.IsVarParam;
    ProcParam.IsConstParam := MParam.IsConstParam;
    ProcDesc.Params.Add(ProcParam);
  end;
  if Def.IsFunction then
  begin
    TSym := FTable.Lookup(Def.ReturnTypeName);
    if (TSym = nil) or (TSym.Kind <> skType) then
      SemanticError(Format(
        'Unknown return type ''%s'' in procedural type ''%s''',
        [Def.ReturnTypeName, ATD.Name]), ATD.Line, ATD.Col);
    ProcDesc.ReturnType := TSym.TypeDesc;
  end;
end;

function TSemanticAnalyser.AnalyseStringSubscriptExpr(AExpr: TStringSubscriptExpr): TTypeDesc;
var
  StrType, IdxType: TTypeDesc;
  FldAccess: TFieldAccessExpr;
  DefProp:   TPropertyInfo;
  DefFA:     TFieldAccessExpr;
begin
  { Idempotency guard: this node rewrites itself in place on the default-property
    and indexed-property paths (StrExpr is swapped for a synthesised field-access,
    IndexExpr is cleared).  A second analysis of an already-resolved node would
    re-walk the mutated children and recurse without bound — which happens when a
    typecast operand is itself a default-property subscript, e.g.
    TStringList(OL[0])[1] (the outer subscript re-analyses its typecast base,
    which re-analyses the inner OL[0]).  Once resolved, return the cached type. }
  if AExpr.ResolvedType <> nil then
    Exit(AExpr.ResolvedType);
  StrType := Self.AnalyseExprSlot(AExpr.StrExpr);
  { Indexed property read: Obj.Prop[I] where Prop is a method-backed indexed property }
  if AExpr.StrExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr.StrExpr);
    if (FldAccess.PropRead <> nil) and (FldAccess.PropRead.IndexParamName <> '') then
    begin
      IdxType := Self.AnalyseExprSlot(AExpr.IndexExpr);
      FldAccess.PropIndexExpr := AExpr.IndexExpr;
      AExpr.IndexExpr := nil;
      Result := FldAccess.PropRead.TypeDesc;
      AExpr.ResolvedType := Result;
      Exit;
    end;
  end;
  { Static array element access: A[I] where A is a static array local }
  if StrType.Kind = tyStaticArray then
  begin
    IdxType := Self.AnalyseExprSlot(AExpr.IndexExpr);
    if not IdxType.IsArrayIndex() then
      SemanticError(
        Format('Static array index must be an ordinal type, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := TStaticArrayTypeDesc(StrType).ElementType;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  { Open-array element access: A[I] where A is an open-array parameter }
  if StrType.Kind = tyOpenArray then
  begin
    IdxType := Self.AnalyseExprSlot(AExpr.IndexExpr);
    if not IdxType.IsNumeric() then
      SemanticError(
        Format('Open-array index must be numeric, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := TOpenArrayTypeDesc(StrType).ElementType;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  { Dynamic array element access: A[I] — 0-based, returns element type }
  if StrType.Kind = tyDynArray then
  begin
    IdxType := Self.AnalyseExprSlot(AExpr.IndexExpr);
    if not IdxType.IsNumeric() then
      SemanticError(
        Format('Dynamic array index must be numeric, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := TDynArrayTypeDesc(StrType).ElementType;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  { PChar byte access: P[I] — 0-based, reads one byte as Integer }
  if StrType.Kind = tyPChar then
  begin
    IdxType := Self.AnalyseExprSlot(AExpr.IndexExpr);
    if not IdxType.IsNumeric() then
      SemanticError(
        Format('PChar subscript index must be numeric, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  { Default array property: Obj[I] on a class/record with a `default` indexed
    property is sugar for Obj.<DefaultProp>[I].  Synthesise the field-access for
    the default property's getter, analyse it (which sets PropRead / owner /
    vtable slot), and reuse the indexed-property-read path above. }
  if (StrType.Kind in [tyClass, tyRecord]) then
  begin
    DefProp := TRecordTypeDesc(StrType).FindDefaultProperty();
    if (DefProp <> nil) and (DefProp.ReadMethod <> '') then
    begin
      DefFA := TFieldAccessExpr.Create();
      DefFA.Line := AExpr.Line;
      DefFA.Col  := AExpr.Col;
      DefFA.Base := AExpr.StrExpr;     { transfer ownership of the receiver expr }
      DefFA.FieldName := DefProp.Name;
      { Attach the index BEFORE analysis — the indexed-property field-access
        path expects PropIndexExpr to be present. }
      DefFA.PropIndexExpr := AExpr.IndexExpr;
      AExpr.IndexExpr := nil;
      AExpr.StrExpr := DefFA;          { StrExpr now owns DefFA }
      AnalyseExpr(DefFA);              { sets DefFA.PropRead / PropOwnerType / VSlot }
      Result := DefProp.TypeDesc;
      AExpr.ResolvedType := Result;
      Exit;
    end;
  end;
  if not StrType.IsString() then
    SemanticError(
      Format('String subscript ''[]'' requires a string expression, got ''%s''',
        [StrType.Name]),
      AExpr.Line, AExpr.Col);
  IdxType := Self.AnalyseExprSlot(AExpr.IndexExpr);
  if not IdxType.IsNumeric() then
    SemanticError(
      Format('String subscript index must be numeric, got ''%s''', [IdxType.Name]),
      AExpr.Line, AExpr.Col);
  Result := FTable.TypeInteger;
  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseIndirectFuncCallExpr(AExpr: TIndirectFuncCallExpr): TTypeDesc;
var
  CalleeType: TTypeDesc;
  ProcDesc:   TProceduralTypeDesc;
  I:          Integer;
begin
  CalleeType := Self.AnalyseExprSlot(AExpr.CalleeExpr);
  if (CalleeType = nil) or (CalleeType.Kind <> tyProcedural) then
  begin
    SemanticError(
      'Expression is not callable — expected procedural type',
      AExpr.Line, AExpr.Col);
    Exit(FTable.TypeInteger);
  end;
  ProcDesc := TProceduralTypeDesc(CalleeType);
  AExpr.ResolvedProcType := ProcDesc;
  for I := 0 to AExpr.Args.Count - 1 do
    Self.AnalyseListSlot(AExpr.Args, I);
  if ProcDesc.ReturnType <> nil then
    Result := ProcDesc.ReturnType
  else
    Result := FTable.TypeInteger;
  AExpr.ResolvedType := Result;
end;

procedure TSemanticAnalyser.CoerceToCharOrd(ALit: TStringLiteral);
begin
  if Length(ALit.Value) <> 1 then
    SemanticError(
      Format('String literal ''%s'' is %d bytes and cannot coerce to Byte; ' +
        'use a single ASCII character (U+0000..U+007F)',
        [ALit.Value, Length(ALit.Value)]),
      ALit.Line, ALit.Col);
  ALit.IsCharCoerce := True;
  ALit.CharOrdValue := StrAt(ALit.Value, 0);
  ALit.ResolvedType := FTable.TypeInteger;
end;

procedure TSemanticAnalyser.AnalyseCaseStmt(AStmt: TCaseStmt);
var
  SelType:  TTypeDesc;
  Branch:   TCaseBranch;
  ValType:  TTypeDesc;
  I, J:     Integer;
begin
  SelType := Self.AnalyseExprSlot(AStmt.Selector);
  AStmt.IsStringCase := SelType.IsString();
  if not (SelType.IsOrdinal() or AStmt.IsStringCase) then
    SemanticError(
      Format('case selector must be ordinal or string type, got ''%s''',
        [SelType.Name]),
      AStmt.Line, AStmt.Col);
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Branch := TCaseBranch(AStmt.Branches.Items[I]);
    for J := 0 to Branch.Values.Count - 1 do
    begin
      if TASTExpr(Branch.Values.Items[J]) is TSetRangeExpr then
      begin
        { Range label lo..hi — both bounds must match the selector type. }
        if AStmt.IsStringCase then
          SemanticError('case range labels are not allowed for a string selector',
            AStmt.Line, AStmt.Col);
        if not TryResolveBareEnumIdent(TSetRangeExpr(Branch.Values.Items[J]).LowExpr, SelType) then
          ValType := AnalyseExpr(TSetRangeExpr(Branch.Values.Items[J]).LowExpr)
        else
          ValType := TSetRangeExpr(Branch.Values.Items[J]).LowExpr.ResolvedType;
        CheckTypesMatch(SelType, ValType, 'case range low', AStmt.Line, AStmt.Col);
        if not TryResolveBareEnumIdent(TSetRangeExpr(Branch.Values.Items[J]).HighExpr, SelType) then
          ValType := AnalyseExpr(TSetRangeExpr(Branch.Values.Items[J]).HighExpr)
        else
          ValType := TSetRangeExpr(Branch.Values.Items[J]).HighExpr.ResolvedType;
        CheckTypesMatch(SelType, ValType, 'case range high', AStmt.Line, AStmt.Col);
      end
      else
      begin
        { A bare enum member label resolves against the selector's type. }
        if TryResolveBareEnumIdent(TASTExpr(Branch.Values.Items[J]), SelType) then
          ValType := TASTExpr(Branch.Values.Items[J]).ResolvedType
        else
          ValType := AnalyseExpr(TASTExpr(Branch.Values.Items[J]));
        CheckTypesMatch(SelType, ValType, 'case value', AStmt.Line, AStmt.Col);
      end;
    end;
    AnalyseStmt(Branch.Stmt);
  end;
  if AStmt.ElseStmt <> nil then
    AnalyseStmt(AStmt.ElseStmt);
end;

procedure TSemanticAnalyser.AnalysePointerWriteStmt(AStmt: TPointerWriteStmt);
var
  PtrType: TTypeDesc;
  ValType: TTypeDesc;
begin
  PtrType := Self.AnalyseExprSlot(AStmt.PtrExpr);
  if PtrType.Kind <> tyPointer then
    SemanticError(
      Format('Pointer write requires a pointer type, got ''%s''', [PtrType.Name]),
      AStmt.Line, AStmt.Col);
  if TPointerTypeDesc(PtrType).BaseType = nil then
    SemanticError(
      'Cannot write through untyped ''Pointer'' — use a typed pointer (e.g. ^Integer)',
      AStmt.Line, AStmt.Col);
  AStmt.BaseTy := TPointerTypeDesc(PtrType).BaseType;
  ValType := AnalyseExprHinted(AStmt.ValExpr, AStmt.BaseTy);
  CheckTypesMatch(AStmt.BaseTy, ValType, 'pointer write', AStmt.Line, AStmt.Col);
end;

procedure TSemanticAnalyser.AnalyseStaticSubscriptAssign(AStmt: TStaticSubscriptAssign);
var
  Sym:      TSymbol;
  ArrType:  TStaticArrayTypeDesc;
  IdxType:  TTypeDesc;
  ValType:  TTypeDesc;
  BaseInfo: TFieldInfo;
  ElemT:    TTypeDesc;
  DefProp:  TPropertyInfo;
begin
  { Chained / multi-dimensional element write: BaseExpr yields the inner
    array (A[I][J] := V, lowered from A[I, J] := V or written directly).
    The element being written is the IndexExpr-th element of BaseExpr's
    static-array result. }
  if AStmt.BaseExpr <> nil then
  begin
    AStmt.ResolvedArrayType := Self.AnalyseExprSlot(AStmt.BaseExpr);
    if (AStmt.ResolvedArrayType = nil) or
       not (AStmt.ResolvedArrayType.Kind in [tyStaticArray, tyDynArray]) then
      SemanticError(
        'Multi-dimensional subscript base must be a static or dynamic array',
        AStmt.Line, AStmt.Col);
    if AStmt.ResolvedArrayType.Kind = tyDynArray then
      ElemT := TDynArrayTypeDesc(AStmt.ResolvedArrayType).ElementType
    else
      ElemT := TStaticArrayTypeDesc(AStmt.ResolvedArrayType).ElementType;
    IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
    if not IdxType.IsArrayIndex() then
      SemanticError('Array index must be an ordinal type', AStmt.Line, AStmt.Col);
    ValType := AnalyseExprHinted(AStmt.ValueExpr, ElemT);
    CheckTypesMatch(ElemT, ValType,
      Format('''%s'' element', [AStmt.ArrayName]), AStmt.Line, AStmt.Col);
    Exit;
  end;
  Sym := FTable.Lookup(AStmt.ArrayName);
  if Sym = nil then
  begin
    { Implicit Self.Field[I] := V — ArrayName is an array-typed field of the
      current class. }
    if FCurrentClass <> nil then
    begin
      BaseInfo := FCurrentClass.FindField(AStmt.ArrayName);
      if (BaseInfo <> nil) and
         (BaseInfo.TypeDesc <> nil) and
         (BaseInfo.TypeDesc.Kind in [tyDynArray, tyStaticArray]) then
      begin
        AStmt.IsImplicitSelf    := True;
        AStmt.ImplicitFieldInfo := BaseInfo;
        AStmt.ResolvedArrayType := BaseInfo.TypeDesc;
        if BaseInfo.TypeDesc.Kind = tyDynArray then
          ElemT := TDynArrayTypeDesc(BaseInfo.TypeDesc).ElementType
        else
          ElemT := TStaticArrayTypeDesc(BaseInfo.TypeDesc).ElementType;
        IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
        if not IdxType.IsArrayIndex() then
          SemanticError('Array index must be an ordinal type', AStmt.Line, AStmt.Col);
        ValType := AnalyseExprHinted(AStmt.ValueExpr, ElemT);
        CheckTypesMatch(ElemT, ValType,
          Format('''%s'' element', [AStmt.ArrayName]), AStmt.Line, AStmt.Col);
        Exit;
      end;
      { Implicit Self.Field[I] := V where Field is a class with a writable
        default array property — lower to its setter on the field's object. }
      if (BaseInfo <> nil) and (BaseInfo.TypeDesc <> nil) and
         (BaseInfo.TypeDesc.Kind = tyClass) then
      begin
        DefProp := TRecordTypeDesc(BaseInfo.TypeDesc).FindDefaultProperty();
        if (DefProp <> nil) and (DefProp.WriteMethod <> '') then
        begin
          AStmt.IsImplicitSelf    := True;
          AStmt.ImplicitFieldInfo := BaseInfo;
          AStmt.PropWriteInfo     := DefProp;
          AStmt.PropOwnerType     := PropAccessorOwner(
            TRecordTypeDesc(BaseInfo.TypeDesc).Name, DefProp.WriteMethod);
          AStmt.PropAccessorVSlot := PropAccessorVSlot(
            TRecordTypeDesc(BaseInfo.TypeDesc).Name, DefProp.WriteMethod);
          IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
          if DefProp.IndexTypeDesc <> nil then
            CheckTypesMatch(DefProp.IndexTypeDesc, IdxType, 'default property index',
              AStmt.Line, AStmt.Col);
          ValType := AnalyseExprHinted(AStmt.ValueExpr, DefProp.TypeDesc);
          CheckTypesMatch(DefProp.TypeDesc, ValType, 'default property assignment',
            AStmt.Line, AStmt.Col);
          Exit;
        end;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', [AStmt.ArrayName]),
      AStmt.Line, AStmt.Col);
  end;
  AStmt.ArrayName := Sym.Name;  { normalise to declared casing }
  { Default array property write: Obj[I] := V where Obj's class/record has a
    `default` indexed property with a setter — lower to a setter call. }
  if Sym.TypeDesc.Kind in [tyClass, tyRecord] then
  begin
    DefProp := TRecordTypeDesc(Sym.TypeDesc).FindDefaultProperty();
    if (DefProp <> nil) and (DefProp.WriteMethod <> '') then
    begin
      AStmt.IsGlobal   := Sym.IsGlobal;
      AStmt.IsVarParam := Sym.Kind = skVarParameter;
      AStmt.PropWriteInfo := DefProp;
      AStmt.PropOwnerType :=
        PropAccessorOwner(TRecordTypeDesc(Sym.TypeDesc).Name, DefProp.WriteMethod);
      AStmt.PropAccessorVSlot :=
        PropAccessorVSlot(TRecordTypeDesc(Sym.TypeDesc).Name, DefProp.WriteMethod);
      IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
      if (DefProp.IndexTypeDesc <> nil) then
        CheckTypesMatch(DefProp.IndexTypeDesc, IdxType, 'default property index',
          AStmt.Line, AStmt.Col);
      ValType := AnalyseExprHinted(AStmt.ValueExpr, DefProp.TypeDesc);
      CheckTypesMatch(DefProp.TypeDesc, ValType, 'default property assignment',
        AStmt.Line, AStmt.Col);
      Exit;
    end;
  end;
  { PChar subscript write: P[I] := Integer — storeb at ptr + I }
  if Sym.TypeDesc.Kind = tyPChar then
  begin
    AStmt.IsGlobal := Sym.IsGlobal;
    AStmt.IsVarParam := Sym.Kind = skVarParameter;
    AStmt.ResolvedArrayType := FTable.TypePChar;
    IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
    if not IdxType.IsNumeric() then
      SemanticError('PChar subscript index must be numeric', AStmt.Line, AStmt.Col);
    Self.AnalyseExprSlot(AStmt.ValueExpr);
    Exit;
  end;
  { String subscript write: S[I] := <byte> — storeb at data_ptr + I.
    Blaise strings are mutable 0-based UTF-8 byte buffers (data-pointer
    convention, see docs/language-rationale.adoc), so an in-place byte write
    is a single storeb with no header skip — the symmetric counterpart of the
    S[I] read.  The value is a byte ordinal (string subscripts read/write
    Byte-as-Integer; there is no Char type). }
  if Sym.TypeDesc.Kind = tyString then
  begin
    AStmt.IsGlobal := Sym.IsGlobal;
    AStmt.IsVarParam := Sym.Kind = skVarParameter;
    AStmt.ResolvedArrayType := FTable.TypeString;
    IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
    if not IdxType.IsNumeric() then
      SemanticError('String subscript index must be numeric',
        AStmt.Line, AStmt.Col);
    { The RHS is a single byte.  Accept a numeric ordinal, or the
      Char-shaped forms the language uses in place of a Char type: Chr(n)
      and single-character string literals (the codegen's byte-RHS path
      stores their first byte).  Mirrors the read side, where S[I] yields a
      byte ordinal. }
    ValType := Self.AnalyseExprSlot(AStmt.ValueExpr);
    if not (ValType.IsNumeric() or (ValType.Kind = tyString)) then
      SemanticError(
        'String element assignment requires a byte, Chr(...), or ' +
        'single-character value', AStmt.Line, AStmt.Col);
    Exit;
  end;
  { Dynamic array subscript write: A[I] := V }
  if Sym.TypeDesc.Kind = tyDynArray then
  begin
    AStmt.IsGlobal          := Sym.IsGlobal;
    AStmt.IsVarParam        := Sym.Kind = skVarParameter;
    AStmt.ResolvedArrayType := Sym.TypeDesc;
    IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
    if not IdxType.IsNumeric() then
      SemanticError('Dynamic array index must be numeric', AStmt.Line, AStmt.Col);
    ValType := AnalyseExprHinted(AStmt.ValueExpr,
      TDynArrayTypeDesc(Sym.TypeDesc).ElementType);
    CheckTypesMatch(TDynArrayTypeDesc(Sym.TypeDesc).ElementType, ValType,
      Format('''%s'' element', [AStmt.ArrayName]), AStmt.Line, AStmt.Col);
    Exit;
  end;
  { Open-array parameter subscript write: a[I] := V.  An open-array param is a
    (data ptr, high) pair; an element write needs a var/out param so the pointer
    refers to the caller's storage.  A `const` open array is read-only and
    rejected.  (issue #130 bug5) }
  if Sym.TypeDesc.Kind = tyOpenArray then
  begin
    if Sym.Kind <> skVarParameter then
      SemanticError(Format(
        'cannot assign to an element of ''%s'': a const open-array parameter ' +
        'is read-only (declare it ''var'')', [AStmt.ArrayName]),
        AStmt.Line, AStmt.Col);
    AStmt.IsGlobal          := False;
    AStmt.IsVarParam        := True;
    AStmt.ResolvedArrayType := Sym.TypeDesc;
    IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
    if not IdxType.IsNumeric() then
      SemanticError('Open array index must be numeric', AStmt.Line, AStmt.Col);
    ValType := AnalyseExprHinted(AStmt.ValueExpr,
      TOpenArrayTypeDesc(Sym.TypeDesc).ElementType);
    CheckTypesMatch(TOpenArrayTypeDesc(Sym.TypeDesc).ElementType, ValType,
      Format('''%s'' element', [AStmt.ArrayName]), AStmt.Line, AStmt.Col);
    Exit;
  end;
  if Sym.TypeDesc.Kind <> tyStaticArray then
    SemanticError(
      Format('''%s'' is not a static array or dynamic array', [AStmt.ArrayName]),
      AStmt.Line, AStmt.Col);
  ArrType := TStaticArrayTypeDesc(Sym.TypeDesc);
  AStmt.IsGlobal := Sym.IsGlobal;
  AStmt.IsVarParam := Sym.Kind = skVarParameter;
  AStmt.ResolvedArrayType := ArrType;
  IdxType := Self.AnalyseExprSlot(AStmt.IndexExpr);
  if not IdxType.IsArrayIndex() then
    SemanticError('Array index must be an ordinal type', AStmt.Line, AStmt.Col);
  ValType := AnalyseExprHinted(AStmt.ValueExpr, ArrType.ElementType);
  CheckTypesMatch(ArrType.ElementType, ValType,
    Format('''%s'' element', [AStmt.ArrayName]), AStmt.Line, AStmt.Col);
end;

function TSemanticAnalyser.AnalyseArrayLiteralExpr(AExpr: TArrayLiteralExpr): TTypeDesc;
var
  ElemType: TTypeDesc;
  ActType:  TTypeDesc;
  I:        Integer;
begin
  { An empty literal [] has no element type to infer.  It is only valid in a
    context that supplies the target type — a set assignment (handled before
    this is reached) or a set-typed argument (resolved by RetypeSetLiteralArgs
    after overload resolution).  Defer here (nil type, no error) rather than
    rejecting outright; an [] that never gets a context surfaces later as an
    unresolved-type use. }
  if AExpr.Elements.Count = 0 then
  begin
    AExpr.ResolvedType := nil;
    Exit(nil);
  end;
  ElemType := Self.AnalyseListSlot(AExpr.Elements, 0);
  for I := 1 to AExpr.Elements.Count - 1 do
  begin
    ActType := Self.AnalyseListSlot(AExpr.Elements, I);
    if (ActType <> ElemType) and not AExpr.IsConstArray then
    begin
      { A heterogeneous bracket literal is only valid as an 'array of const'
        argument.  Rather than rejecting it here, type it as 'array of TVarRec'
        and flag it; overload resolution then matches it against an
        array-of-const formal (or fails with 'no matching overload' if none
        exists), and codegen boxes each element into a TVarRec. }
      AExpr.IsConstArray := True;
    end;
  end;
  if AExpr.IsConstArray then
    Result := FTable.NewOpenArrayType(FTable.FindType('TVarRec'))
  else
    Result := FTable.NewOpenArrayType(ElemType);
  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.SetLiteralBitCount(AExpr: TArrayLiteralExpr;
  ABaseEnum: TEnumTypeDesc): Integer;
var
  I, MaxOrd: Integer;
  Elem: TASTExpr;
begin
  MaxOrd := -1;
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    Elem := TASTExpr(AExpr.Elements.Items[I]);
    { Only compile-time enum constants have a known ordinal.  Any non-constant
      element forces the conservative full-enum width. }
    if (Elem is TIdentExpr) and TIdentExpr(Elem).IsConstant then
    begin
      if TIdentExpr(Elem).ConstValue > MaxOrd then
        MaxOrd := TIdentExpr(Elem).ConstValue;
    end
    else
      Exit(ABaseEnum.Members.Count);
  end;
  { Empty literal -> width 1 (a single zero byte fits any small set). }
  if MaxOrd < 0 then
    Result := 1
  else
    Result := MaxOrd + 1;
end;

function TSemanticAnalyser.SetRangeBoundOrdinal(ABound: TASTExpr;
  ABaseEnum: TEnumTypeDesc; const AWhich: string): Integer;
{ Resolve a set-range bound (lo or hi) to a compile-time ordinal of the
  base enum.  Rejects non-constant and wrong-type bounds.  Issue #105. }
var
  BType: TTypeDesc;
begin
  { Resolve a bare enum-member bound against the base enum so a member name
    shared by several enums binds to this set's enum, not last-wins. }
  if TryResolveBareEnumIdent(ABound, ABaseEnum) then
    BType := ABound.ResolvedType
  else
    BType := AnalyseExpr(ABound);
  if BType <> ABaseEnum then
    SemanticError(
      Format('Set range %s bound has type ''%s''; expected ''%s''',
        [AWhich, BType.Name, ABaseEnum.Name]),
      ABound.Line, ABound.Col);
  if not ((ABound is TIdentExpr) and TIdentExpr(ABound).IsConstant) then
    SemanticError(
      Format('Set range %s bound ''%s'' is not a constant',
        [AWhich, TIdentExpr(ABound).Name]),
      ABound.Line, ABound.Col);
  Result := TIdentExpr(ABound).ConstValue;
end;

procedure TSemanticAnalyser.ExpandSetRanges(AExpr: TArrayLiteralExpr;
  ABaseEnum: TEnumTypeDesc);
{ Replace every TSetRangeExpr element [lo..hi] with the individual member
  idents lo, lo+1, ..., hi.  Constant ascending ranges only; a reversed
  range is a compile-time error (not a silent empty set).  Runs before the
  element validation loop so the rest of the pipeline only ever sees plain
  member idents.  Issue #105. }
var
  I, J:      Integer;
  Elem:      TASTExpr;
  Range:     TSetRangeExpr;
  LoOrd:     Integer;
  HiOrd:     Integer;
  NewList:   TObjectList;
  MemberId:  TIdentExpr;
begin
  { Quick scan — nothing to do if there are no ranges. }
  J := -1;
  for I := 0 to AExpr.Elements.Count - 1 do
    if TASTExpr(AExpr.Elements.Items[I]) is TSetRangeExpr then
    begin
      J := I;
      Break;
    end;
  if J < 0 then Exit;

  if ABaseEnum = nil then
    SemanticError('Set range requires an enumeration base type',
      AExpr.Line, AExpr.Col);

  { Build a fresh element list, expanding ranges into members.  NewList does
    NOT own its items — ownership of plain elements transfers from the old
    list, and the generated member idents are handed to it too; the swap
    below frees the old list (with the consumed ranges) without touching the
    surviving plain elements. }
  NewList := TObjectList.Create(False);
  try
    for I := 0 to AExpr.Elements.Count - 1 do
    begin
      Elem := TASTExpr(AExpr.Elements.Items[I]);
      if not (Elem is TSetRangeExpr) then
      begin
        NewList.Add(Elem);
        Continue;
      end;
      Range := TSetRangeExpr(Elem);
      LoOrd := SetRangeBoundOrdinal(Range.LowExpr,  ABaseEnum, 'low');
      HiOrd := SetRangeBoundOrdinal(Range.HighExpr, ABaseEnum, 'high');
      if HiOrd < LoOrd then
        SemanticError(
          Format('Set range is reversed (low ordinal %d > high ordinal %d) — ' +
                 'an empty range is almost always a mistake; use [] for an ' +
                 'empty set', [LoOrd, HiOrd]),
          Range.Line, Range.Col);
      for J := LoOrd to HiOrd do
      begin
        MemberId            := TIdentExpr.Create();
        MemberId.Line       := Range.Line;
        MemberId.Col        := Range.Col;
        MemberId.Name       := ABaseEnum.Members.Strings[J];
        MemberId.IsConstant := True;
        MemberId.ConstValue := J;
        MemberId.ResolvedType := ABaseEnum;
        NewList.Add(MemberId);
      end;
    end;
    { Transfer expanded elements into a new owning list and swap.  The old
      Elements list owns its items; detach the survivors first so freeing it
      only disposes the consumed TSetRangeExpr nodes. }
    for I := AExpr.Elements.Count - 1 downto 0 do
      if not (TASTExpr(AExpr.Elements.Items[I]) is TSetRangeExpr) then
        AExpr.Elements.Extract(AExpr.Elements.Items[I]);
    AExpr.Elements.Clear();   { frees the remaining TSetRangeExpr nodes }
    for I := 0 to NewList.Count - 1 do
      AExpr.Elements.Add(NewList.Items[I]);
  finally
    NewList.Free();
  end;
end;

procedure TSemanticAnalyser.ExpandOrdinalSetRanges(AExpr: TArrayLiteralExpr;
  ASetType: TSetTypeDesc);
var
  I, J:      Integer;
  Elem:      TASTExpr;
  Range:     TSetRangeExpr;
  LoVal:     Int64;
  HiVal:     Int64;
  NewList:   TObjectList;
  Lit:       TIntLiteral;
  HasRanges: Boolean;
begin
  HasRanges := False;
  for I := 0 to AExpr.Elements.Count - 1 do
    if TASTExpr(AExpr.Elements.Items[I]) is TSetRangeExpr then
    begin
      HasRanges := True;
      Break;
    end;
  if not HasRanges then Exit;

  NewList := TObjectList.Create(False);
  try
    for I := 0 to AExpr.Elements.Count - 1 do
    begin
      Elem := TASTExpr(AExpr.Elements.Items[I]);
      if not (Elem is TSetRangeExpr) then
      begin
        NewList.Add(Elem);
        Continue;
      end;
      Range := TSetRangeExpr(Elem);
      LoVal := EvalConstIntExpr(Range.LowExpr, Range.Line, Range.Col);
      HiVal := EvalConstIntExpr(Range.HighExpr, Range.Line, Range.Col);
      if HiVal < LoVal then
        SemanticError(
          Format('Set range is reversed (%d > %d)', [LoVal, HiVal]),
          Range.Line, Range.Col);
      if (LoVal < 0) or (HiVal >= ASetType.BitCount) then
        SemanticError(
          Format('Set range %d..%d out of bounds (0..%d)',
            [LoVal, HiVal, ASetType.BitCount - 1]),
          Range.Line, Range.Col);
      for J := LoVal to HiVal do
      begin
        Lit := TIntLiteral.Create();
        Lit.Line := Range.Line;
        Lit.Col := Range.Col;
        Lit.Value := J;
        Lit.ResolvedType := ASetType.BaseType;
        NewList.Add(Lit);
      end;
    end;
    for I := AExpr.Elements.Count - 1 downto 0 do
      if not (TASTExpr(AExpr.Elements.Items[I]) is TSetRangeExpr) then
        AExpr.Elements.Extract(AExpr.Elements.Items[I]);
    AExpr.Elements.Clear();
    for I := 0 to NewList.Count - 1 do
      AExpr.Elements.Add(NewList.Items[I]);
  finally
    NewList.Free();
  end;
end;

function TSemanticAnalyser.AnalyseSetLiteralExpr(AExpr: TArrayLiteralExpr;
  ASetType: TSetTypeDesc): TTypeDesc;
var
  ElemType: TTypeDesc;
  I:        Integer;
  IsOrdBase: Boolean;
begin
  IsOrdBase := ASetType.BaseType.Kind in [tyByte, tyBoolean];
  if ASetType.BaseType is TEnumTypeDesc then
    ExpandSetRanges(AExpr, TEnumTypeDesc(ASetType.BaseType))
  else if IsOrdBase then
    ExpandOrdinalSetRanges(AExpr, ASetType)
  else
    ExpandSetRanges(AExpr, nil);
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    { A bare enum member element resolves against the set's element type, so a
      member name shared by several enums picks this set's enum. }
    if TryResolveBareEnumIdent(TASTExpr(AExpr.Elements.Items[I]), ASetType.BaseType) then
      ElemType := TASTExpr(AExpr.Elements.Items[I]).ResolvedType
    else
      ElemType := Self.AnalyseListSlot(AExpr.Elements, I);
    if IsOrdBase then
    begin
      if (not ElemType.IsNumeric()) and (ElemType <> ASetType.BaseType) then
        SemanticError(
          Format('Set literal element %d has type ''%s''; expected ''%s'' or integer',
            [I + 1, ElemType.Name, ASetType.BaseType.Name]),
          AExpr.Line, AExpr.Col);
    end
    else if ElemType <> ASetType.BaseType then
      SemanticError(
        Format('Set literal element %d has type ''%s''; expected ''%s''',
          [I + 1, ElemType.Name, ASetType.BaseType.Name]),
        AExpr.Line, AExpr.Col);
  end;
  AExpr.ResolvedType := ASetType;
  Result := ASetType;
end;

end.
