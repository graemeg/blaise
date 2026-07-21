{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.sepcompile;

{ End-to-end separate-compilation gate.

  Drives the headline feature through the actual blaise binary rather
  than the in-process pipeline used by the other E2E suites:

    1. blaise --source Dep.pas --output Dep.o
         -> ELF .o with .blaise.iface embedded
    2. Dep.pas removed from disk
    3. blaise --source UseDep.pas --output use_dep --unit-path <dir-with-Dep.o>
         -> compiler picks up Dep.o via auto-discovery, reads the iface
            out of the embedded section, links the program
    4. ./use_dep
         -> prints the expected output

  Covers both free routines (where only the call site needs the iface)
  and generic classes (where the consumer instantiates the template
  using bodies carried in the .blaise.iface — no source TUnit
  required). }

interface

uses
  classes, sysutils, process, blaise.testing,
  cp.test.e2e.base;

type
  TSepCompileTests = class(TE2ETestCase)
  private
    procedure RunRecordMethodsAndClosuresWarmCache(const ABackend: string);
    procedure RunWarmSetLibProgram(const ATag, AProgSrc, AExpected: string);
  protected
    procedure SetUp; override;
  private
    function  BlaisePath(): string;
    function  RunBlaise(const AArgs: array of string;
                        out AStdout: string): Integer;
    function  RunBinary(const AExe: string; out AStdout: string): Integer;
    { Run an arbitrary tool (ar, cc, nm, …) capturing its stdout. }
    function  RunProc(const AExe: string; const AArgs: array of string;
                      out AStdout: string): Integer;
    { Assert ASym is present in nm output ANm but not as a strong (T/D) local
      definition — the GH #174 archive-collision guard. }
    procedure AssertNotStrongDef(const ANm, ASym, AWhere: string);
  published
    { Regression (BUG-042 Gap 1): a Linux program using the async reactor must
      link and run under --static.  The reactor binds epoll_create1/epoll_ctl/
      epoll_wait/eventfd via `external name`; on the dynamic path libc provides
      them, but the freestanding static leaf (runtime.syscall.linux) had no
      definitions, so --static died with `undefined reference to epoll_ctl`.
      Linux-only (the static syscall leaf is Linux x86-64). }
    procedure TestStaticAsyncReactor_LinksAndRuns;
    procedure TestFreeRoutine_RoundTrip_WithoutSource;
    procedure TestGenericClass_RoundTrip_WithoutSource;
    procedure TestUninstantiatedGenericFunc_InUnit_Compiles;
    procedure TestDuplicateExternalAcrossUnits_Compiles;
    procedure TestNativeIncremental_MultiUnitClass_Compiles;
    procedure TestNativeNoIncremental_MultiUnitClass_Compiles;
    { Regression (GH #174): a class declared in an UNMANGLED unit (rtl.*/
      runtime.*/System) has BARE typeinfo/vtable/_FieldCleanup symbols, and a
      unit-level global of such a unit has a bare data symbol.  Under
      --no-incremental every object that references the class / inlines the unit
      re-DEFINES those bare symbols; two such objects archived together then
      collide at link with a multiple-definition error.  The fix emits the
      definitions WEAK so the copies collapse.  This test compiles two rtl.*
      leaf units (each using a shared rtl.* base unit) standalone with
      --no-incremental, archives all three, and links a driver that pulls BOTH
      leaves — the link must succeed and the program run. }
    procedure TestNoIncremental_UnmangledUnitClass_ArchiveLinks;
    { Regression: a class declared in a unit's IMPLEMENTATION section (not its
      interface) was rejected at compile and never had its method bodies /
      typeinfo / vtable / _FieldCleanup emitted — both backends' unit-emission
      loops only walked IntfBlock.TypeDecls.  The fix registers impl-section
      types unit-private, analyses their method bodies, and emits them
      alongside IntfBlock ones. }
    procedure TestNativeImplSectionClass_Compiles;
    procedure TestQBEImplSectionClass_Compiles;
    { Regression: an IMPLEMENTATION-section class referenced as a METACLASS value
      (class-of / `TFoo` used as a value) in the unit's OWN initialization block.
      Per-unit codegen left DefineOwningUnit pointing at a dependency unit by the
      time the init block was emitted, so the impl-section class symbol was
      suppressed by Lookup's cross-unit-leak guard and the metaclass ref mangled
      to a bare, undefined typeinfo symbol -> link-time garbage -> SIGSEGV.
      Both backends. }
    procedure TestNativeImplSectionMetaclassInInit_Runs;
    procedure TestQBEImplSectionMetaclassInInit_Runs;
    { Regression: a class declared in unit A's IMPLEMENTATION section must NOT
      be visible to an unrelated unit B that never `uses` A — it previously
      leaked through the flat global scope. }
    procedure TestImplSectionClass_DoesNotLeakCrossUnit;
    { Regression: compiling a UNIT (unit-mode, top source is a `unit`) that
      USES another unit, with the default incremental path, segfaulted — the
      incremental worker setup read Prog.SymbolTable, but in unit-mode Prog is
      nil (the table comes from the semantic pass).  This is the exact path the
      runtime Makefile drives (every RTL unit is compiled `--source X.pas
      --output X.o`), so it broke `make` in runtime/. }
    procedure TestNativeIncremental_UnitUsesUnit_Compiles;
    { Regression: a Double field read via implicit Self (Result := FFloat
      inside a method) compiled in unit-mode (.o) emitted `movsd FFloat(%rip)`
      — a load from a global symbol named after the field instead of from
      Self+offset — producing an undefined `FFloat` symbol.  The store path was
      already correct; only the read was broken, and only in per-unit codegen
      (whole-program builds resolved it as a field offset). }
    procedure TestNativeIncremental_FloatFieldRead_InUnit;
    { Regression: a unit that USES another unit only in its IMPLEMENTATION
      section.  On a clean build all units are parsed, so the impl-only
      dependency's object is linked.  But on an incremental REBUILD, the
      consuming unit is loaded from its cached .o/.bif — and the .bif only
      recorded the INTERFACE uses, so the impl-only dependency was never
      loaded and its .o was dropped from the link → undefined symbol at
      run time.  This is exactly what broke a second `pasbuild test-compile`
      (the compiler rebuilt itself incrementally into a populated cache and
      lost ~880 KB of impl-only-dependency code). }
    procedure TestIncrementalRebuild_ImplOnlyUses_LinksDependency;
    { Regression (BUG-20260720-unit-iface-static-array-bif-roundtrip): a unit
      INTERFACE var of an anonymous array type — `array[0..2] of string` or
      `array of string` — broke the warm rebuild.  The .bif stored the type as
      `$builtin.array[0..2] of string` and the importer split on the LAST dot
      (the `..` range), mangling the type to `2] of string`; and RegisterVars
      resolved with FindType-only, which cannot instantiate an anonymous array. }
    procedure TestIncrementalRebuild_UnitIfaceAnonArrayVar;
    { Regression: a non-virtual constructor named 'Create' receives an
      implicit vtable slot (metaclass dispatch through a class-of
      reference).  The source-side semantic pass added that slot, but the
      cached-.bif importer (uSemanticImport.RegisterClassMethod) only added
      slots for virtual/override methods — so a descendant class compiled
      against a CACHED base unit built a vtable that omitted the Create slot
      and shifted every later virtual method up.  A Cls.Create call then
      dispatched through the wrong vtable slot (it hit the method that fell
      into Create's old index), so the constructor body never ran and the
      object's fields stayed nil.  This crashed the stdlib JSON test suite
      when its TTestCase base came from target/units. }
    procedure TestIncrementalRebuild_VirtualCtorVtableSlot;
    { Regression (bugs.txt warm --unit-cache): a leaf class inherits a method
      from a GRANDPARENT class that lives in a different cached unit.  On a
      warm rebuild the leaf unit recompiles from source while its ancestors
      load from cached .bif ifaces.  A cross-unit parent is serialised in the
      .bif with its unit qualifier (e.g. `base.TBase`); the importer resolved
      the parent with a bare Lookup that missed the qualified name, leaving the
      intermediate class's Parent pointer nil — so the leaf's inherited-method
      walk dead-ended and reported "Undeclared procedure". }
    procedure TestIncrementalRebuild_QualifiedGrandparentMethod;
    { Regression (warm --unit-cache set-of-enum literal): the cached-.bif
      importer registered an enum's members as symbols but never populated the
      analyser's enum-member reverse index (FEnumMemberIndex).  ArgMatchScore
      is the one argument-matching path with no target type in hand: it must
      INFER a bracket literal's base enum from its elements, via
      SetLiteralBaseEnum -> ResolveEnumMember, which reads ONLY that index.
      Warm, the index was empty, so [oA] scored 0 against a `set of TOpt`
      parameter and the call was rejected with "No matching overload".  Cold
      builds passed because the source-visible path does register members. }
    procedure TestIncrementalRebuild_SetLiteralArg_EnumBase;
    procedure TestIncrementalRebuild_SetLiteralArg_OverloadedEnumBase;
    { The other two ArgMatchScore set arms — empty literal and a Byte-based
      set — never consulted the reverse index and passed warm even before the
      fix.  Locked in here so the index fix cannot regress them. }
    procedure TestIncrementalRebuild_SetLiteralArg_EmptyAndByteBase;
    { Two enums in a cached unit sharing a member name.  The source-visible
      path deliberately does NOT define enum members as bare global skConstant
      symbols (so names may be shared and resolved by context); the importer
      used to, which made a warm build hard-error where a cold build compiled. }
    procedure TestIncrementalRebuild_SharedEnumMemberName_Warm;
    { The same asymmetry seen through a BARE member reference rather than a
      set literal.  The importer's global skConstant for a shared name shadowed
      the reverse-index lookup (TryResolveBareEnumIdent bails to a real symbol
      of that name), so a warm build bound `S := cShared` to the FIRST enum's
      member and silently assigned the wrong ordinal — 1 instead of 3.  Wrong
      code, not a diagnostic, which is why this needs an execution check. }
    procedure TestIncrementalRebuild_SharedEnumMemberName_BareRef_Warm;
    procedure TestDebugOpdf_PerUnitSection_InDependencyObject;
    { Regression (F1-followup cross-unit static members): a class with `static`
      members — a static var, a static method, and a static const — declared in
      one unit and used through the COMPILED .bif boundary from another unit.
      The wire format already encoded the static facts, but the export clone
      dropped TFieldDecl.IsClassVar/ClassVarEmitName, TMethodDecl.IsStatic and
      TPropertyDecl.IsStatic before encoding; the importer ignored them and the
      decoded ConstDecls; and TRoutineSig carried no IsStatic field at all.  So
      a cross-unit TReg.Next() failed with "is not a static method", a static
      var did not register as a shared global, and TReg.Tag did not resolve.
      Driving through --unit-cache exercises the real .bif write+read path on
      both backends. }
    procedure TestStaticMembers_CrossUnit_QBE;
    procedure TestStaticMembers_CrossUnit_Native;
    { Regression (BUG-043 follow-ons, IFACE v13): RECORD methods vanished
      entirely from the cached interface (records never exported/imported
      their method sigs), an imported record method lost the record-receiver
      convention (IsRecordMethod), and a 'reference to' procedural type lost
      its closure flag on import (anon-method args then failed overload
      scoring).  One warm-cache round trip covers all three, per backend. }
    procedure TestRecordMethodsAndClosures_WarmCache_Native;
    procedure TestRecordMethodsAndClosures_WarmCache_QBE;
    { Regression: two units EACH declaring a same-named unit-level `var` (and a
      same-named `threadvar`) must emit DISTINCT global symbols on the native
      backend (ua_GVal / ub_GVal), not one colliding bare `GVal`.  The native
      backend previously emitted and referenced module globals under their BARE
      name, so the internal linker silently merged the two units' slots (a shared-
      storage hazard) and the EXTERNAL linker rejected the build with "multiple
      definition of GVal".  The fix makes native honour the owning unit for module
      globals, mirroring the QBE backend.  Built with `--linker external` so a
      regression re-surfaces as a hard link failure, and the printed values prove
      the two slots are genuinely independent. }
    procedure TestSameNamedModuleVar_AcrossUnits_ExternalLink_Native;
    procedure TestSameNamedModuleVar_AcrossUnits_QBE;
    { Regression (BUGS.md BUG-004): generic-instance symbols were mangled from
      FOUR inconsistent sources — the instantiating unit's prefix (source
      instantiation), bare (instantiated during .bif import), Sym.OwningUnit
      (name-based codegen refs, poisoned to the re-exporting unit by import),
      and forced-bare (desc-based refs).  A consumer unit compiled in a multi-
      unit --unit-cache process could reference a copy under a prefix nobody
      ever emitted (e.g. Xml_Types_TOrderedDictionary_string_string_SetItem in
      the stdlib TestRunner) — the link succeeded lazily and the loader failed
      at run time with an undefined symbol.  The fix mangles ALL generic-
      instance symbols BARE at every site and emits them as WEAK symbols in
      per-unit mode so any number of objects may carry the (identical) copy and
      the linker dedups.  The scenario: uprovider instantiates TReg<Integer> in
      cache1's process; ureexport carries it as an interface field; a second
      process (cache2) compiles two consumers where the first-compiled one
      inherits the pending instance and the second references it through the
      default-property setter (the name-based path that read the poisoned
      OwningUnit). }
    procedure TestGenericInstance_CrossUnitCache_DefaultPropSetter_Runs;
    { Phase 6 (anonymous methods x generics): a generic class whose method
      body contains a closure literal, exported through the .bif generic-body
      template and monomorphised by a consumer that has no access to the
      source.  Covers the TAnonMethodExpr round-trip inside EncodeBlock and
      the per-instantiation thunk/env regeneration at the import site. }
    procedure TestGenericBodyClosure_RoundTrip_WithoutSource;
    { Colliding generic declarations: generic-instance symbols are mangled
      BARE (no unit prefix) and emitted WEAK so the linker folds the copies
      that multiple units materialise of the SAME instance (the BUG-004
      COMDAT model).  The flip side: two DIFFERENT generics with the same
      base name declared in two different units produce byte-identical
      instance symbols (e.g. TBox_Integer) and the linker would silently
      keep one and drop the other.  The front end cannot represent that
      case either (the template registry is keyed by bare base name), so
      it must be REJECTED with a diagnostic naming both units — at source
      analysis and on the cached-.bif import path alike. }
    procedure TestCollidingGenerics_TwoSourceUnits_Rejected;
    procedure TestCollidingGenerics_CachedIface_Rejected;
    { NOTE: drives the cached-.bif path only — a cross-unit generic FUNCTION
      call cannot resolve on the whole-program source path at all (BUGS.md
      BUG-034); extend to the source path when that gap is fixed. }
    procedure TestCollidingGenericRoutines_CachedIface_Rejected;
  end;

implementation

procedure TSepCompileTests.SetUp;
begin
  inherited SetUp();
  { BUG-019: every method in this class compiles with '--unit-path FScratch',
    so a dependency unit (.pas/.bif/.o) written by a PRIOR method into the
    SHARED scratch dir could be resolved instead of this test's own — the
    cause of the rare full-run-only failure of
    TestDuplicateExternalAcrossUnits_Compiles. Give each test its OWN scratch
    subdirectory (keyed on the test method name) so unit resolution only ever
    sees files this test wrote. Non-destructive and race-free — no shared
    directory to clean between tests. }
  SetUpScratch('compiler/target/test-e2e-sepcompile/' + TestName)
end;

function TSepCompileTests.BlaisePath(): string;
var
  ProjectRoot: string;
begin
  ProjectRoot := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if ProjectRoot <> '' then
    Result := IncludeTrailingPathDelimiter(ProjectRoot) + 'compiler/target/blaise'
  else
    Result := ExtractFilePath(ParamStr(0)) + 'blaise'
end;

function TSepCompileTests.RunBlaise(const AArgs: array of string;
                                    out AStdout: string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := BlaisePath();
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TSepCompileTests.RunBinary(const AExe: string;
                                    out AStdout: string): Integer;
var
  Proc:  TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

procedure TSepCompileTests.TestFreeRoutine_RoundTrip_WithoutSource;
const
  DepSrc =
    '''
    unit MyDep;
    interface
    function Triple(N: Integer): Integer;
    implementation
    function Triple(N: Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 1 to 3 do Result := Result + N
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseMyDep;
    uses MyDep;
    begin
      WriteLn('Triple(7) = ', Triple(7))
    end.
    ''';
var
  DepPas, DepObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas  := FScratch + '/MyDep.pas';
  DepObj  := FScratch + '/MyDep.o';
  ProgPas := FScratch + '/use_mydep.pas';
  ProgBin := FScratch + '/use_mydep';

  { Step 1: build the dep into an .o with embedded .blaise.iface. }
  WriteFile(DepPas, DepSrc);
  Rc := RunBlaise(['--source', DepPas, '--output', DepObj], Captured);
  AssertEquals('blaise(MyDep) exit code', 0, Rc);
  AssertTrue('MyDep.o exists', FileExists(DepObj));

  { Step 2: hide the source so the consumer cannot reach it. }
  DeleteFile(DepPas);
  AssertFalse('MyDep.pas hidden', FileExists(DepPas));

  { Step 3: compile the consumer.  The loader's auto-discovery walks
    the unit path looking for a sibling <unit>.o with an embedded
    iface; the call site for Triple is resolved from that iface and
    the .o is linked into the final binary. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_mydep) exit code', 0, Rc);
  AssertTrue('use_mydep exists', FileExists(ProgBin));

  { Step 4: run the program. }
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_mydep exit code', 0, Rc);
  AssertEquals('use_mydep stdout', 'Triple(7) = 21' + #10, Captured)
end;

procedure TSepCompileTests.TestGenericClass_RoundTrip_WithoutSource;
const
  DepSrc =
    '''
    unit MyContainers;
    interface
    type
      TBox<T> = class
      private
        FValue: T;
      public
        constructor Create(AValue: T);
        function Get: T;
      end;
    implementation
    constructor TBox<T>.Create(AValue: T);
    begin
      FValue := AValue
    end;
    function TBox<T>.Get: T;
    begin
      Result := FValue
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseBox;
    uses MyContainers;
    var B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create(42);
      WriteLn('Box = ', B.Get());
      B.Free()
    end.
    ''';
var
  DepPas, DepObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas  := FScratch + '/MyContainers.pas';
  DepObj  := FScratch + '/MyContainers.o';
  ProgPas := FScratch + '/use_box.pas';
  ProgBin := FScratch + '/use_box';

  { Step 1: compile the generic-bearing unit to an .o with embedded
    iface.  The .bif must carry enough of the generic template body
    (statements + types) for the consumer to instantiate TBox<Integer>
    without ever reading MyContainers.pas back. }
  WriteFile(DepPas, DepSrc);
  Rc := RunBlaise(['--source', DepPas, '--output', DepObj], Captured);
  AssertEquals('blaise(MyContainers) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('MyContainers.o exists', FileExists(DepObj));

  { Step 2: hide the source. }
  DeleteFile(DepPas);
  AssertFalse('MyContainers.pas hidden', FileExists(DepPas));

  { Step 3: instantiate the generic in a consumer with only the .o
    visible.  Codegen has to clone the template body, substitute the
    Integer type argument, and emit a fresh TBox_Integer_* family —
    all sourced from the imported iface, not from the (absent) TUnit. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_box) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('use_box exists', FileExists(ProgBin));

  { Step 4: run the program. }
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_box exit code', 0, Rc);
  AssertEquals('use_box stdout', 'Box = 42' + #10, Captured)
end;

{ Regression for issue #107: a generic FUNCTION declared in a unit but never
  instantiated was code-generated as a template, whose `T`-typed locals have
  no resolved type — codegen raised "Variable 'MaxValue' has no resolved type
  — semantic pass required".  EmitStandaloneDefs skipped templates, but the
  unit-emission path (GenerateUnit/AppendUnit → EmitFuncDef) did not.  The
  unit must compile to an .o even when nothing uses the generic. }
procedure TSepCompileTests.TestUninstantiatedGenericFunc_InUnit_Compiles;
const
  DepSrc =
    '''
    unit MyMaxUnit;
    interface
    function Doubled(N: Integer): Integer;
    function FindMaxValue<T>(arr: array of T): T;
    implementation
    function Doubled(N: Integer): Integer;
    begin
      Result := N * 2
    end;
    function FindMaxValue<T>(arr: array of T): T;
    var
      MaxValue: T;
      x: UInt64;
    begin
      x := Low(arr);
      MaxValue := arr[0];
      while x <= High(arr) do
      begin
        if arr[x] > MaxValue then
          MaxValue := arr[x];
        Inc(x)
      end;
      Result := MaxValue
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseMyMax;
    uses MyMaxUnit;
    begin
      { Use only the non-generic routine — the generic stays uninstantiated. }
      WriteLn('Doubled(21) = ', Doubled(21))
    end.
    ''';
var
  DepPas, DepObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas  := FScratch + '/MyMaxUnit.pas';
  DepObj  := FScratch + '/MyMaxUnit.o';
  ProgPas := FScratch + '/use_mymax.pas';
  ProgBin := FScratch + '/use_mymax';

  { Step 1: compile the unit.  The uninstantiated generic template must be
    skipped by codegen — this is the step that previously crashed. }
  WriteFile(DepPas, DepSrc);
  Rc := RunBlaise(['--source', DepPas, '--output', DepObj], Captured);
  AssertEquals('blaise(MyMaxUnit) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('MyMaxUnit.o exists', FileExists(DepObj));

  { Step 2: a consumer that never instantiates the generic links and runs. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_mymax) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('use_mymax exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_mymax exit code', 0, Rc);
  AssertEquals('use_mymax stdout', 'Doubled(21) = 42' + #10, Captured)
end;

{ Two units that each privately declare the SAME C function via
  `external name '...'` must both resolve calls to it.  Regression for a
  cross-unit clash in impl-only proc matching: the per-unit forward-decl
  fallback (FProcIndex.IndexOf) ignored unit ownership, so the second unit's
  external matched the FIRST unit's already-indexed decl and was never defined
  into its own scope -> "Undeclared function" at the call site. }
procedure TSepCompileTests.TestDuplicateExternalAcrossUnits_Compiles;
const
  UnitASrc =
    '''
    unit DupExtA;
    interface
    function LenA(const S: string): Integer;
    implementation
    function _strlenA(S: Pointer): Int64; external name 'strlen';
    function LenA(const S: string): Integer;
    begin
      Result := Integer(_strlenA(PChar(S)))
    end;
    end.
    ''';
  UnitBSrc =
    '''
    unit DupExtB;
    interface
    function LenB(const S: string): Integer;
    implementation
    function _strlenA(S: Pointer): Int64; external name 'strlen';
    function LenB(const S: string): Integer;
    begin
      Result := Integer(_strlenA(PChar(S)))
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseDupExt;
    uses DupExtA, DupExtB;
    begin
      WriteLn(LenA('abc') + LenB('defgh'))
    end.
    ''';
var
  APas, BPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  APas    := FScratch + '/DupExtA.pas';
  BPas    := FScratch + '/DupExtB.pas';
  ProgPas := FScratch + '/use_dupext.pas';
  ProgBin := FScratch + '/use_dupext';

  WriteFile(APas, UnitASrc);
  WriteFile(BPas, UnitBSrc);
  WriteFile(ProgPas, ProgSrc);

  { Single invocation: both units are picked up off the unit path and
    compiled alongside the program. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_dupext) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('use_dupext exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_dupext exit code', 0, Rc);
  AssertEquals('use_dupext stdout', '8' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeIncremental_MultiUnitClass_Compiles;
{ Incremental compilation (per-unit .o + embedded .bif) is the DEFAULT on the
  native backend (as it is on QBE).  Compile a program using a unit that
  declares a class (exercises the system-def suppression + global
  typeinfo_TObject and per-unit string literals in the unit object) WITHOUT any
  --incremental flag — the default path must produce a working binary and leave
  a per-unit .o behind. }
const
  UnitSrc =
    '''
    unit ShapesU;
    interface
    type
      TShape = class
        Name: string;
        function Describe: string;
      end;
    implementation
    function TShape.Describe: string;
    begin Result := 'shape:' + Name end;
    end.
    ''';
  ProgSrc =
    '''
    program UseShapes;
    uses ShapesU;
    var S: TShape;
    begin
      S := TShape.Create();
      S.Name := 'box';
      WriteLn(S.Describe());
      S.Free()
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin, UnitObj: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ShapesU.pas';
  ProgPas := FScratch + '/use_shapes.pas';
  ProgBin := FScratch + '/use_shapes';
  { Incremental writes the per-unit .o next to the output with a lowercased
    unit name (see UnitOPath in Blaise.pas). }
  UnitObj := FScratch + '/shapesu.o';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);
  DeleteFile(UnitObj);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_shapes) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_shapes exists', FileExists(ProgBin));
  AssertTrue('per-unit ShapesU.o cached', FileExists(UnitObj));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_shapes exit code', 0, Rc);
  AssertEquals('use_shapes stdout', 'shape:box' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeNoIncremental_MultiUnitClass_Compiles;
{ --no-incremental opts out of the default per-unit .o emission: the same
  multi-unit-class program must still compile and run as a single whole-program
  object, and NO per-unit .o is left behind. }
const
  UnitSrc =
    '''
    unit ShapesU;
    interface
    type
      TShape = class
        Name: string;
        function Describe: string;
      end;
    implementation
    function TShape.Describe: string;
    begin Result := 'shape:' + Name end;
    end.
    ''';
  ProgSrc =
    '''
    program UseShapes;
    uses ShapesU;
    var S: TShape;
    begin
      S := TShape.Create();
      S.Name := 'box';
      WriteLn(S.Describe());
      S.Free()
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin, UnitObj: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ShapesU.pas';
  ProgPas := FScratch + '/use_shapes_ni.pas';
  ProgBin := FScratch + '/use_shapes_ni';
  UnitObj := FScratch + '/shapesu.o';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);
  DeleteFile(UnitObj);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native', '--no-incremental',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_shapes_ni) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_shapes_ni exists', FileExists(ProgBin));
  AssertFalse('no per-unit ShapesU.o with --no-incremental', FileExists(UnitObj));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_shapes_ni exit code', 0, Rc);
  AssertEquals('use_shapes_ni stdout', 'shape:box' + #10, Captured)
end;

function TSepCompileTests.RunProc(const AExe: string;
  const AArgs: array of string; out AStdout: string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

procedure TSepCompileTests.AssertNotStrongDef(const ANm, ASym, AWhere: string);
{ nm prints one line '<addr> <bind> <name>' per symbol: 'T'/'D' = strong
  text/data def (the GH #174 collision), 'W'/'V' = weak def (the fix), 'U' =
  external reference.  The bare base-class symbol re-defined by a leaf object
  must not be strong; weak or extern is fine.  (Blaise Pos is 0-based and
  returns -1 when not found.) }
begin
  { Present at all — a trailing-newline exact match so a prefix (e.g.
    typeinfo_TGh174Base) is not matched by a search for a shorter name. }
  AssertTrue(ASym + ' present in ' + AWhere,
    Pos(' ' + ASym + #10, ANm + #10) >= 0);
  { Neither strong-text (' T ') nor strong-data (' D ') binding for it. }
  AssertTrue(ASym + ' must not be a strong text def in ' + AWhere +
    ' — GH #174', Pos(' T ' + ASym + #10, ANm + #10) < 0);
  AssertTrue(ASym + ' must not be a strong data def in ' + AWhere +
    ' — GH #174', Pos(' D ' + ASym + #10, ANm + #10) < 0)
end;

procedure TSepCompileTests.TestNoIncremental_UnmangledUnitClass_ArchiveLinks;
{ GH #174: two rtl.* leaf units, each USING a shared rtl.* base unit that
  declares a class + a unit global, are each compiled STANDALONE with
  --no-incremental (the runtime/Makefile archive-producer path).  Because the
  base unit is unmangled its class typeinfo/vtable/_FieldCleanup and its global
  are BARE, and every inlining object re-DEFINES them.  Before the fix each such
  definition was STRONG (a gas .globl), so archiving the two leaves and linking
  a puller that pulls BOTH failed with 'multiple definition of
  typeinfo_TGh174Base' / GGh174.  The fix emits them WEAK; nm must show 'W'/'V'
  (weak), never 'T'/'D' (strong), for the base class's symbols and global in the
  leaf objects.  Asserting the binding directly (rather than driving a full
  archive link) isolates THIS defect from the orthogonal fact that a
  --no-incremental object also inlines its runtime.* deps. }
const
  { The base is ABSTRACT and published and implements an interface, so it emits
    the FULL set of bare per-class symbols a referencing object re-defines —
    typeinfo/vtable/_FieldCleanup/methods/itab/impllist — plus a bare unit
    global, while emitting NO concrete method body of its own (Kind is abstract;
    the override lives in each leaf).  Every one of those definitions must be
    weak.  (A concrete base method body is a separate, still-latent case not
    exercised here: no RTL class today declares one.) }
  BaseSrc =
    '''
    unit rtl.gh174base;
    interface
    type
      IGh174 = interface
        function Kind: string;
      end;
      TGh174Base = class(IGh174)
        Tag: Integer;
      published
        function Kind: string; virtual; abstract;
      end;
    var GGh174: TGh174Base;
    implementation
    end.
    ''';
  LeafASrc =
    '''
    unit rtl.gh174a;
    interface
    uses rtl.gh174base;
    function MakeGh174A: TGh174Base;
    implementation
    type TGh174A = class(TGh174Base) function Kind: string; override; end;
    function TGh174A.Kind: string; begin Result := 'A' end;
    function MakeGh174A: TGh174Base; begin Result := TGh174A.Create() end;
    end.
    ''';
  LeafBSrc =
    '''
    unit rtl.gh174b;
    interface
    uses rtl.gh174base;
    function MakeGh174B: TGh174Base;
    implementation
    type TGh174B = class(TGh174Base) function Kind: string; override; end;
    function TGh174B.Kind: string; begin Result := 'B' end;
    function MakeGh174B: TGh174Base; begin Result := TGh174B.Create() end;
    end.
    ''';

var
  BasePas, LeafAPas, LeafBPas: string;
  BaseObj, LeafAObj, LeafBObj: string;
  Captured, NmA, NmB: string;
  Rc: Integer;
begin
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  BasePas  := FScratch + '/rtl.gh174base.pas';
  LeafAPas := FScratch + '/rtl.gh174a.pas';
  LeafBPas := FScratch + '/rtl.gh174b.pas';
  { Objects go in a subdir that is NOT on --unit-path, so each leaf INLINES the
    base unit from source (--no-incremental) rather than auto-discovering a
    prebuilt base.o and importing it externally — matching runtime/Makefile,
    whose .o outputs land in target/ while --unit-path points at the sources.
    This is what makes every leaf re-define the bare base symbols. }
  ForceDirectories(FScratch + '/obj');
  BaseObj  := FScratch + '/obj/rtl.gh174base.o';
  LeafAObj := FScratch + '/obj/rtl.gh174a.o';
  LeafBObj := FScratch + '/obj/rtl.gh174b.o';

  WriteFile(BasePas, BaseSrc);
  WriteFile(LeafAPas, LeafASrc);
  WriteFile(LeafBPas, LeafBSrc);

  { Compile each unit STANDALONE with --no-incremental + native/internal — the
    exact recipe runtime/Makefile uses to build blaise_rtl.a members. }
  Rc := RunBlaise(['--source', BasePas, '--output', BaseObj,
                   '--backend', 'native', '--assembler', 'internal',
                   '--no-incremental', '--unit-path', FScratch], Captured);
  AssertEquals('compile base (out: ' + Captured + ')', 0, Rc);
  Rc := RunBlaise(['--source', LeafAPas, '--output', LeafAObj,
                   '--backend', 'native', '--assembler', 'internal',
                   '--no-incremental', '--unit-path', FScratch], Captured);
  AssertEquals('compile leaf A (out: ' + Captured + ')', 0, Rc);
  Rc := RunBlaise(['--source', LeafBPas, '--output', LeafBObj,
                   '--backend', 'native', '--assembler', 'internal',
                   '--no-incremental', '--unit-path', FScratch], Captured);
  AssertEquals('compile leaf B (out: ' + Captured + ')', 0, Rc);

  { Both leaf objects inline the base unit, so each re-defines the base class's
    bare symbols and the bare global.  None of these may be a STRONG local
    definition, or two members collide when archived + both pulled. }
  Rc := RunProc('nm', [LeafAObj], NmA);
  AssertEquals('nm leaf A', 0, Rc);
  Rc := RunProc('nm', [LeafBObj], NmB);
  AssertEquals('nm leaf B', 0, Rc);

  AssertNotStrongDef(NmA, 'typeinfo_TGh174Base', 'leaf A');
  AssertNotStrongDef(NmA, 'vtable_TGh174Base', 'leaf A');
  AssertNotStrongDef(NmA, '_FieldCleanup_TGh174Base', 'leaf A');
  AssertNotStrongDef(NmA, 'methods_TGh174Base', 'leaf A');
  AssertNotStrongDef(NmA, 'itab_TGh174Base_IGh174', 'leaf A');
  AssertNotStrongDef(NmA, 'impllist_TGh174Base', 'leaf A');
  AssertNotStrongDef(NmA, 'typeinfo_IGh174', 'leaf A');
  AssertNotStrongDef(NmA, 'GGh174', 'leaf A');
  AssertNotStrongDef(NmB, 'typeinfo_TGh174Base', 'leaf B');
  AssertNotStrongDef(NmB, 'vtable_TGh174Base', 'leaf B');
  AssertNotStrongDef(NmB, '_FieldCleanup_TGh174Base', 'leaf B');
  AssertNotStrongDef(NmB, 'methods_TGh174Base', 'leaf B');
  AssertNotStrongDef(NmB, 'itab_TGh174Base_IGh174', 'leaf B');
  AssertNotStrongDef(NmB, 'impllist_TGh174Base', 'leaf B');
  AssertNotStrongDef(NmB, 'typeinfo_IGh174', 'leaf B');
  AssertNotStrongDef(NmB, 'GGh174', 'leaf B')
end;

procedure TSepCompileTests.TestNativeImplSectionClass_Compiles;
{ A class declared entirely in a unit's IMPLEMENTATION section, used by an
  interface-exported routine of that unit.  The unit object must emit the
  class's method bodies, typeinfo, vtable and _FieldCleanup so the call site
  links.  Native default (incremental) path. }
const
  UnitSrc =
    '''
    unit ImplCls;
    interface
    function MakeAndGet: Integer;
    implementation
    type
      TFoo = class
        FX: Integer;
        constructor Create(AX: Integer);
        function GetX: Integer;
      end;
    constructor TFoo.Create(AX: Integer);
    begin FX := AX end;
    function TFoo.GetX: Integer;
    begin Result := FX end;
    function MakeAndGet: Integer;
    var F: TFoo;
    begin
      F := TFoo.Create(7);
      Result := F.GetX();
      F.Free()
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseImplCls;
    uses ImplCls;
    begin
      WriteLn(MakeAndGet())
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ImplCls.pas';
  ProgPas := FScratch + '/use_implcls.pas';
  ProgBin := FScratch + '/use_implcls';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_implcls) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_implcls exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_implcls exit code', 0, Rc);
  AssertEquals('use_implcls stdout', '7' + #10, Captured)
end;

procedure TSepCompileTests.TestQBEImplSectionClass_Compiles;
{ Same as TestNativeImplSectionClass_Compiles but forces the QBE backend —
  the QBE unit-emission loop (AppendUnit) must also walk ImplBlock classes. }
const
  UnitSrc =
    '''
    unit ImplClsQ;
    interface
    function MakeAndGet: Integer;
    implementation
    type
      TFoo = class
        FX: Integer;
        constructor Create(AX: Integer);
        function GetX: Integer;
      end;
    constructor TFoo.Create(AX: Integer);
    begin FX := AX end;
    function TFoo.GetX: Integer;
    begin Result := FX end;
    function MakeAndGet: Integer;
    var F: TFoo;
    begin
      F := TFoo.Create(7);
      Result := F.GetX();
      F.Free()
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseImplClsQ;
    uses ImplClsQ;
    begin
      WriteLn(MakeAndGet())
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ImplClsQ.pas';
  ProgPas := FScratch + '/use_implclsq.pas';
  ProgBin := FScratch + '/use_implclsq';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'qbe',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_implclsq) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_implclsq exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_implclsq exit code', 0, Rc);
  AssertEquals('use_implclsq stdout', '7' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeImplSectionMetaclassInInit_Runs;
{ The unit's INITIALIZATION block references an impl-section class as a metaclass
  value (assigns the class to a `class of` global).  Before the
  DefineOwningUnit re-assertion fix, per-unit codegen emitted that metaclass ref
  under a bare, undefined `typeinfo_<TFoo>` symbol, linking to garbage and
  crashing at runtime.  Native (default) path. }
const
  UnitSrc =
    '''
    unit ImplMetaN;
    interface
    function MakeViaMeta: Integer;
    implementation
    type
      TFoo = class
        FX: Integer;
        constructor Create;
        function GetX: Integer;
      end;
      TFooClass = class of TFoo;
    var
      GCls: TFooClass;
    constructor TFoo.Create;
    begin FX := 42 end;
    function TFoo.GetX: Integer;
    begin Result := FX end;
    function MakeViaMeta: Integer;
    var F: TFoo;
    begin
      F := GCls.Create();
      Result := F.GetX();
      F.Free()
    end;
    initialization
      GCls := TFoo;
    end.
    ''';
  ProgSrc =
    '''
    program UseImplMetaN;
    uses ImplMetaN;
    begin
      WriteLn(MakeViaMeta())
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ImplMetaN.pas';
  ProgPas := FScratch + '/use_implmetan.pas';
  ProgBin := FScratch + '/use_implmetan';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_implmetan) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_implmetan exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_implmetan exit code', 0, Rc);
  AssertEquals('use_implmetan stdout', '42' + #10, Captured)
end;

procedure TSepCompileTests.TestQBEImplSectionMetaclassInInit_Runs;
{ Same as TestNativeImplSectionMetaclassInInit_Runs but forces the QBE backend. }
const
  UnitSrc =
    '''
    unit ImplMetaQ;
    interface
    function MakeViaMeta: Integer;
    implementation
    type
      TFoo = class
        FX: Integer;
        constructor Create;
        function GetX: Integer;
      end;
      TFooClass = class of TFoo;
    var
      GCls: TFooClass;
    constructor TFoo.Create;
    begin FX := 42 end;
    function TFoo.GetX: Integer;
    begin Result := FX end;
    function MakeViaMeta: Integer;
    var F: TFoo;
    begin
      F := GCls.Create();
      Result := F.GetX();
      F.Free()
    end;
    initialization
      GCls := TFoo;
    end.
    ''';
  ProgSrc =
    '''
    program UseImplMetaQ;
    uses ImplMetaQ;
    begin
      WriteLn(MakeViaMeta())
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ImplMetaQ.pas';
  ProgPas := FScratch + '/use_implmetaq.pas';
  ProgBin := FScratch + '/use_implmetaq';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'qbe',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_implmetaq) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_implmetaq exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_implmetaq exit code', 0, Rc);
  AssertEquals('use_implmetaq stdout', '42' + #10, Captured)
end;

procedure TSepCompileTests.TestImplSectionClass_DoesNotLeakCrossUnit;
{ A class declared in unit A's IMPLEMENTATION section is private to A.  A second
  unit B that never `uses` A must NOT see it — referencing it must be a compile
  error, not a silent success via the flat global scope.  (Both A and B sit on
  the same unit path, so before the fix B resolved A's impl class by leak.) }
const
  UnitASrc =
    '''
    unit LeakA;
    interface
    procedure Noop;
    implementation
    type
      TPrivate = class
        V: Integer;
      end;
    procedure Noop; begin end;
    end.
    ''';
  UnitBSrc =
    '''
    unit LeakB;
    interface
    function Use: Integer;
    implementation
    function Use: Integer;
    var X: TPrivate;       // LeakB does NOT use LeakA — must be unknown
    begin
      X := TPrivate.Create();
      Result := X.V;
      X.Free()
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseLeak;
    uses LeakA, LeakB;
    begin
      WriteLn(Use())
    end.
    ''';
var
  UnitAPas, UnitBPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitAPas := FScratch + '/LeakA.pas';
  UnitBPas := FScratch + '/LeakB.pas';
  ProgPas  := FScratch + '/use_leak.pas';
  ProgBin  := FScratch + '/use_leak';

  WriteFile(UnitAPas, UnitASrc);
  WriteFile(UnitBPas, UnitBSrc);
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertTrue('compile must FAIL (impl-section class is unit-private), out: '
             + Captured, Rc <> 0);
  AssertTrue('error names the unknown type TPrivate, out: ' + Captured,
             Pos('TPrivate', Captured) >= 0)
end;

procedure TSepCompileTests.TestNativeIncremental_UnitUsesUnit_Compiles;
{ Compile a UNIT that uses another unit, in unit-mode (--source <unit>.pas
  --output <unit>.o), via the default incremental path.  This is the runtime
  Makefile's exact invocation and used to segfault (nil Prog.SymbolTable in the
  incremental worker setup).  A program that uses the compiled unit must then
  build and run, proving the per-unit object is correct. }
const
  BaseSrc =
    '''
    unit BaseU;
    interface
    type TFoo = record A: Integer; end;
    function MakeFoo(N: Integer): TFoo;
    implementation
    function MakeFoo(N: Integer): TFoo;
    begin Result.A := N end;
    end.
    ''';
  DerivedSrc =
    '''
    unit DerivedU;
    interface
    uses BaseU;
    function Doubled(N: Integer): Integer;
    implementation
    function Doubled(N: Integer): Integer;
    var F: TFoo;
    begin F := MakeFoo(N); Result := F.A * 2 end;
    end.
    ''';
  ProgSrc =
    '''
    program UseDerived;
    uses DerivedU;
    begin
      WriteLn(Doubled(21))
    end.
    ''';
var
  BasePas, DerivedPas, DerivedObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  BasePas    := FScratch + '/BaseU.pas';
  DerivedPas := FScratch + '/DerivedU.pas';
  DerivedObj := FScratch + '/derivedu.o';
  ProgPas    := FScratch + '/use_derived.pas';
  ProgBin    := FScratch + '/use_derived';

  WriteFile(BasePas, BaseSrc);
  WriteFile(DerivedPas, DerivedSrc);
  DeleteFile(DerivedObj);

  { Unit-mode incremental compile: this is the call that crashed. }
  Rc := RunBlaise(['--source', DerivedPas, '--output', DerivedObj,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(DerivedU unit) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('DerivedU.o exists', FileExists(DerivedObj));

  { The emitted unit object must be usable: build + run a program over it. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_derived) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_derived exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_derived exit code', 0, Rc);
  AssertEquals('use_derived stdout', '42' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeIncremental_FloatFieldRead_InUnit;
const
  UnitSrc =
    '''
    unit NumU;
    interface
    type
      TNum = class
        FFloat: Double;
        procedure SetF(v: Double);
        function GetF: Double;
      end;
    implementation
    procedure TNum.SetF(v: Double); begin FFloat := v; end;
    function TNum.GetF: Double; begin Result := FFloat; end;
    end.
    ''';
  ProgSrc =
    '''
    program UseNum;
    uses NumU;
    var N: TNum;
    begin
      N := TNum.Create();
      N.SetF(3.5);
      WriteLn(N.GetF());
      N.Free()
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/NumU.pas';
  ProgPas := FScratch + '/use_num.pas';
  ProgBin := FScratch + '/use_num';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);

  { Incremental (per-unit .o) is the default; NumU is compiled to numu.o, whose
    GetF must read FFloat from Self+offset, not a global symbol. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_num) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_num exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_num exit code', 0, Rc);
  AssertEquals('use_num stdout', '3.5' + #10, Captured)
end;

procedure TSepCompileTests.TestIncrementalRebuild_ImplOnlyUses_LinksDependency;
const
  HelperSrc =
    '''
    unit HelperU;
    interface
    function HelperVal: Integer;
    implementation
    function HelperVal: Integer;
    begin Result := 42 end;
    end.
    ''';
  { MidU uses HelperU only in its IMPLEMENTATION section — HelperU does not
    appear in MidU's interface, so MidU's .bif must still record it as an
    implementation-section dependency. }
  MidSrc =
    '''
    unit MidU;
    interface
    function MidVal: Integer;
    implementation
    uses HelperU;
    function MidVal: Integer;
    begin Result := HelperVal() + 1 end;
    end.
    ''';
  ProgSrc =
    '''
    program UseMid;
    uses MidU;
    begin
      WriteLn(MidVal())
    end.
    ''';
var
  HelperPas, MidPas, ProgPas, ProgBin, CacheDir: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  HelperPas := FScratch + '/HelperU.pas';
  MidPas    := FScratch + '/MidU.pas';
  ProgPas   := FScratch + '/use_mid.pas';
  ProgBin   := FScratch + '/use_mid';
  CacheDir  := FScratch + '/units-impl';

  WriteFile(HelperPas, HelperSrc);
  WriteFile(MidPas, MidSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  { Build 1 (clean cache): every unit is parsed from source, so HelperU's
    object is linked.  This populates the cache with .o/.bif for MidU and
    HelperU. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  AssertEquals('build1 stdout', '43' + #10, Captured);

  { Build 2 (populated cache): MidU is now loaded from its cached iface.
    The loader must still pull in HelperU (MidU's impl-only dependency) and
    link helperu.o — otherwise the link drops it and the program aborts at
    run time with an undefined symbol. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_mid exists after rebuild', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code (impl-only dep must be linked)', 0, Rc);
  AssertEquals('build2 stdout', '43' + #10, Captured)
end;

procedure TSepCompileTests.TestIncrementalRebuild_UnitIfaceAnonArrayVar;
const
  StaticLibSrc =
    '''
    unit SArrLib;
    interface
    var UA: array[0..2] of string;
    implementation
    end.
    ''';
  DynLibSrc =
    '''
    unit DArrLib;
    interface
    var DA: array of string;
    implementation
    end.
    ''';
  StaticProgSrc =
    '''
    program UseSArr;
    uses SArrLib;
    begin UA[0] := 'hi'; WriteLn(UA[0]) end.
    ''';
  DynProgSrc =
    '''
    program UseDArr;
    uses DArrLib;
    begin SetLength(DA, 2); DA[1] := 'dyn'; WriteLn(DA[1]) end.
    ''';

  procedure RunWarmRebuild(const AUnitName, AUnitSrc, AProgName, AProgSrc,
                           AExpected: string);
  var
    UnitPas, ProgPas, ProgBin, CacheDir, Captured: string;
    Rc: Integer;
  begin
    UnitPas  := FScratch + '/' + AUnitName + '.pas';
    ProgPas  := FScratch + '/' + AProgName + '.pas';
    ProgBin  := FScratch + '/' + AProgName;
    CacheDir := FScratch + '/cache-' + AUnitName;
    WriteFile(UnitPas, AUnitSrc);
    WriteFile(ProgPas, AProgSrc);
    ForceDirectories(CacheDir);
    { Build 1 (clean cache): unit parsed from source. }
    Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                     '--unit-cache', CacheDir,
                     '--unit-path', FScratch], Captured);
    AssertEquals(AUnitName + ' build1 exit (out: ' + Captured + ')', 0, Rc);
    { Build 2 (warm): unit imported from its cached .bif — the round-trip that
      used to fail with EImportError. }
    Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                     '--unit-cache', CacheDir,
                     '--unit-path', FScratch], Captured);
    AssertEquals(AUnitName + ' build2 (warm) exit (out: ' + Captured + ')', 0, Rc);
    Rc := RunBinary(ProgBin, Captured);
    AssertEquals(AUnitName + ' warm run exit', 0, Rc);
    AssertEquals(AUnitName + ' warm stdout', AExpected + #10, Captured);
  end;

begin
  if not ToolchainAvailable() then
  begin Fail('toolchain missing'); Exit end;
  if not FileExists(BlaisePath()) then
  begin Fail('blaise binary missing'); Exit end;
  RunWarmRebuild('SArrLib', StaticLibSrc, 'UseSArr', StaticProgSrc, 'hi');
  RunWarmRebuild('DArrLib', DynLibSrc, 'UseDArr', DynProgSrc, 'dyn');
end;

procedure TSepCompileTests.TestIncrementalRebuild_QualifiedGrandparentMethod;
const
  { Three-level chain mirroring TAssert->TTestCase->TE2ETestCase.  Greet is
    defined on the grandparent TBase.  CRITICAL: the grandparent unit has a
    DOTTED name (chain.base) — the trigger for this bug.  A cross-unit parent
    is serialised in the .bif as `Unit.Type`; when the unit is dotted
    (chain.base.TBase) the decoder must split at the LAST dot.  Splitting at
    the first dot yielded type='base.TBase', so the cached parent could not be
    relinked and the leaf's inherited-method walk dead-ended. }
  BaseSrc =
    '''
    unit chain.base;
    interface
    type
      TBase = class
        function Greet: Integer;
      end;
    implementation
    function TBase.Greet: Integer;
    begin Result := 7 end;
    end.
    ''';
  { TMid's parent TBase lives in the dotted unit chain.base, so chain.mid's
    .bif serialises the parent qualified as `chain.base.TBase`. }
  MidSrc =
    '''
    unit chain.mid;
    interface
    uses chain.base;
    type
      TMid = class(TBase)
        function MidOnly: Integer;
      end;
    implementation
    function TMid.MidOnly: Integer;
    begin Result := 1 end;
    end.
    ''';
  { Leaf unit: TLeaf inherits Greet from TBase via TMid (two cached units up).
    The marker comment is edited between builds to force a recompile-from-
    source of THIS unit while chain.base/chain.mid stay cached. }
  LeafSrc =
    '''
    unit chain.leaf;
    interface
    uses chain.mid;
    type
      TLeaf = class(TMid)
        function Run: Integer;
      end;
    implementation
    { rev 1 }
    function TLeaf.Run: Integer;
    begin Result := Greet() + MidOnly() end;
    end.
    ''';
  LeafSrc2 =
    '''
    unit chain.leaf;
    interface
    uses chain.mid;
    type
      TLeaf = class(TMid)
        function Run: Integer;
      end;
    implementation
    { rev 2 — edited to force recompile from source }
    function TLeaf.Run: Integer;
    begin Result := Greet() + MidOnly() end;
    end.
    ''';
  ProgSrc =
    '''
    program UseLeaf;
    uses chain.leaf;
    var L: TLeaf;
    begin
      L := TLeaf.Create();
      WriteLn(L.Run());
      L.Free()
    end.
    ''';
var
  BasePas, MidPas, LeafPas, ProgPas, ProgBin, CacheDir: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  BasePas  := FScratch + '/chain.base.pas';
  MidPas   := FScratch + '/chain.mid.pas';
  LeafPas  := FScratch + '/chain.leaf.pas';
  ProgPas  := FScratch + '/use_leaf.pas';
  ProgBin  := FScratch + '/use_leaf';
  CacheDir := FScratch + '/units-qgp';

  WriteFile(BasePas, BaseSrc);
  WriteFile(MidPas, MidSrc);
  WriteFile(LeafPas, LeafSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  { Build 1 (clean cache): all units from source; populates the cache. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  AssertEquals('build1 stdout', '8' + #10, Captured);

  { Edit the LEAF unit's content so build 2 recompiles it FROM SOURCE while
    BaseU and MidU load from their cached .bif/.o.  The inherited Greet (on
    the cached grandparent TBase) must still resolve through MidU's
    qualified parent link. }
  WriteFile(LeafPas, LeafSrc2);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code — grandparent method must resolve (out: '
    + Captured + ')', 0, Rc);
  AssertTrue('use_leaf exists after rebuild', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code', 0, Rc);
  AssertEquals('build2 stdout', '8' + #10, Captured)
end;

{ Regression for the cached-unit virtual-constructor vtable-slot bug.

  BaseU declares a class with a non-virtual constructor Create (which still
  takes a vtable slot for class-of dispatch) FOLLOWED by a virtual method
  Tag.  A descendant TDerived overrides Tag, and the program creates the
  instance through a class-of reference (Cls.Create) so the constructor is
  reached via the vtable.  Create sets FValue := 7; if the cached import
  drops Create's vtable slot, Cls.Create dispatches into Tag's slot instead,
  FValue stays 0, and the program prints '0' rather than '7'. }
procedure TSepCompileTests.TestIncrementalRebuild_VirtualCtorVtableSlot;
const
  BaseSrc =
    '''
    unit BaseU;
    interface
    type
      TBase = class(TObject)
      private
        FValue: Integer;
      public
        constructor Create;
        function Tag: Integer; virtual;
        property Value: Integer read FValue;
      end;
      TBaseClass = class of TBase;
    implementation
    constructor TBase.Create;
    begin
      inherited Create();
      Self.FValue := 7
    end;
    function TBase.Tag: Integer;
    begin
      Result := 100
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseBase;
    uses BaseU;
    var
      Cls: TBaseClass;
      Obj: TBase;
    begin
      Cls := TBase;
      Obj := Cls.Create();
      WriteLn(Obj.Value)
    end.
    ''';
var
  BasePas, ProgPas, ProgBin, CacheDir, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  BasePas  := FScratch + '/BaseU.pas';
  ProgPas  := FScratch + '/use_base.pas';
  ProgBin  := FScratch + '/use_base';
  CacheDir := FScratch + '/units-vctor';

  WriteFile(BasePas, BaseSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  { Build 1 (clean cache): BaseU is parsed from source.  Populates the
    cache with BaseU's .o/.bif. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  AssertEquals('build1 stdout (ctor ran)', '7' + #10, Captured);

  { Build 2 (populated cache): BaseU is loaded from its cached .bif.  The
    importer must re-create the Create vtable slot so Cls.Create dispatches
    to the constructor and FValue is set to 7. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_base exists after rebuild', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code', 0, Rc);
  AssertEquals('build2 stdout (cached ctor slot)', '7' + #10, Captured)
end;

{ Compile AProgSrc twice into the SAME unit cache alongside a shared SetLib
  unit (a set-of-enum type, a Byte-based set type, a plain non-overloaded
  taker, and an overloaded pair), and assert both builds succeed and print
  AExpected.  A cold-only test cannot see the bug — the second build is the
  one that imports SetLib from its .bif. }
procedure TSepCompileTests.RunWarmSetLibProgram(const ATag, AProgSrc,
  AExpected: string);
const
  SetLibSrc =
    '''
    unit SetLib;
    interface
    type
      TOpt = (oA, oB, oC);
      TOpts = set of TOpt;
      TByteSet = set of Byte;
    function PlainEnum(const O: TOpts): Integer;
    function CountBytes(const B: TByteSet): Integer;
    function Pick(const O: TOpts): Integer; overload;
    function Pick(const O: TOpts; AExtra: Integer): Integer; overload;
    implementation
    function PlainEnum(const O: TOpts): Integer;
    var
      E: TOpt;
    begin
      Result := 0;
      for E := oA to oC do
        if E in O then Inc(Result)
    end;
    function CountBytes(const B: TByteSet): Integer;
    var
      I: Integer;
    begin
      Result := 0;
      for I := 0 to 255 do
        if I in B then Inc(Result)
    end;
    function Pick(const O: TOpts): Integer;
    begin
      Result := 1
    end;
    function Pick(const O: TOpts; AExtra: Integer): Integer;
    begin
      Result := 2 + AExtra
    end;
    end.
    ''';
var
  LibPas, ProgPas, ProgBin, CacheDir, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  LibPas   := FScratch + '/SetLib.pas';
  ProgPas  := FScratch + '/use_setlib_' + ATag + '.pas';
  ProgBin  := FScratch + '/use_setlib_' + ATag;
  CacheDir := FScratch + '/units-setlit-' + ATag;

  WriteFile(LibPas, SetLibSrc);
  WriteFile(ProgPas, AProgSrc);
  ForceDirectories(CacheDir);

  { Build 1 (clean cache): SetLib is parsed from source. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  AssertEquals('build1 stdout', AExpected, Captured);

  { Build 2 (populated cache): SetLib is imported from its cached .bif. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code', 0, Rc);
  AssertEquals('build2 stdout (cached enum members)', AExpected, Captured)
end;

procedure TSepCompileTests.TestIncrementalRebuild_SetLiteralArg_EnumBase;
const
  ProgSrc =
    '''
    program UseSetLib;
    uses SetLib;
    begin
      WriteLn(PlainEnum([oA]));
      WriteLn(PlainEnum([oA, oC]))
    end.
    ''';
begin
  RunWarmSetLibProgram('plain', ProgSrc, '1' + #10 + '2' + #10)
end;

procedure TSepCompileTests.TestIncrementalRebuild_SetLiteralArg_OverloadedEnumBase;
const
  ProgSrc =
    '''
    program UseSetLibOvl;
    uses SetLib;
    begin
      WriteLn(Pick([oB]));
      WriteLn(Pick([oB], 5))
    end.
    ''';
begin
  { 1 = the 1-arg overload, 7 = the 2-arg overload (2 + 5). }
  RunWarmSetLibProgram('ovl', ProgSrc, '1' + #10 + '7' + #10)
end;

procedure TSepCompileTests.TestIncrementalRebuild_SetLiteralArg_EmptyAndByteBase;
const
  ProgSrc =
    '''
    program UseSetLibEmpty;
    uses SetLib;
    begin
      WriteLn(PlainEnum([]));
      WriteLn(CountBytes([]));
      WriteLn(CountBytes([3, 9, 200]))
    end.
    ''';
begin
  RunWarmSetLibProgram('empty', ProgSrc, '0' + #10 + '0' + #10 + '3' + #10)
end;

procedure TSepCompileTests.TestIncrementalRebuild_SharedEnumMemberName_Warm;
const
  DualSrc =
    '''
    unit DualEnum;
    interface
    type
      TColour = (cRed, cShared, cBlue);
      TShape = (sBox, sShared, sDot);
      TColours = set of TColour;
      TShapes = set of TShape;
    function CountColours(const C: TColours): Integer;
    function CountShapes(const S: TShapes): Integer;
    implementation
    function CountColours(const C: TColours): Integer;
    var
      E: TColour;
    begin
      Result := 0;
      for E := cRed to cBlue do
        if E in C then Inc(Result)
    end;
    function CountShapes(const S: TShapes): Integer;
    var
      E: TShape;
    begin
      Result := 0;
      for E := sBox to sDot do
        if E in S then Inc(Result)
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseDualEnum;
    uses DualEnum;
    begin
      WriteLn(CountColours([cRed, cShared]));
      WriteLn(CountShapes([sShared, sDot]))
    end.
    ''';
var
  LibPas, ProgPas, ProgBin, CacheDir, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  LibPas   := FScratch + '/DualEnum.pas';
  ProgPas  := FScratch + '/use_dualenum.pas';
  ProgBin  := FScratch + '/use_dualenum';
  CacheDir := FScratch + '/units-dualenum';

  WriteFile(LibPas, DualSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  AssertEquals('build1 stdout', '2' + #10 + '2' + #10, Captured);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code', 0, Rc);
  AssertEquals('build2 stdout (shared member name)', '2' + #10 + '2' + #10, Captured)
end;

procedure TSepCompileTests.TestIncrementalRebuild_SharedEnumMemberName_BareRef_Warm;
const
  DualSrc =
    '''
    unit BareDual;
    interface
    type
      TColour = (cRed, cShared, cBlue);
      TShape = (sBox, sMid, sPad, cShared);
    implementation
    end.
    ''';
  ProgSrc =
    '''
    program UseBareDual;
    uses BareDual;
    var
      S: TShape;
    begin
      S := cShared;
      WriteLn(Ord(S))
    end.
    ''';
var
  LibPas, ProgPas, ProgBin, CacheDir, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  LibPas   := FScratch + '/BareDual.pas';
  ProgPas  := FScratch + '/use_baredual.pas';
  ProgBin  := FScratch + '/use_baredual';
  CacheDir := FScratch + '/units-baredual';

  WriteFile(LibPas, DualSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  { The declared type TShape narrows the shared name to its own member. }
  AssertEquals('build1 stdout (Ord(TShape.cShared))', '3' + #10, Captured);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code', 0, Rc);
  AssertEquals('build2 stdout (cached shared name, same ordinal)',
               '3' + #10, Captured)
end;

procedure TSepCompileTests.TestDebugOpdf_PerUnitSection_InDependencyObject;
const
  DepSrc =
    '''
    unit OpdfDep;
    interface
    procedure Greet(const AName: string);
    implementation
    procedure Greet(const AName: string);
    var
      Total: Integer;
      Msg: string;
    begin
      Total := 0;
      Msg := 'Hello, ';
      Msg := Msg + AName;
      Total := Total + 1;
      WriteLn(Msg);
      Total := Total + 1;
      WriteLn('Count is ', Total)
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseOpdfDep;
    uses OpdfDep;
    begin
      Greet('World')
    end.
    ''';
var
  DepPas, ProgPas, ProgBin, CacheDir, DepObj: string;
  Captured, ObjOut: string;
  Rc: Integer;
  Proc: TProcess;
  Chunk: string;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas   := FScratch + '/OpdfDep.pas';
  ProgPas  := FScratch + '/use_opdfdep.pas';
  ProgBin  := FScratch + '/use_opdfdep';
  CacheDir := FScratch + '/units-opdf';
  DepObj   := CacheDir + '/opdfdep.o';

  WriteFile(DepPas, DepSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  { Default (incremental) native build with --debug-opdf: the dependency
    unit is compiled to its own .o in the cache dir.  With per-unit OPDF the
    worker embeds a self-contained .opdf section into that .o so pdr can break
    inside OpdfDep.Greet.  Before this feature only the program object carried
    OPDF, so the dependency .o had no .opdf section. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native', '--debug-opdf',
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(--debug-opdf) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_opdfdep exists', FileExists(ProgBin));
  AssertTrue('dependency object exists at ' + DepObj, FileExists(DepObj));

  { The unit .o must carry an .opdf section (objdump -h shows it). }
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := 'objdump';
    Proc.Parameters.Add('-h');
    Proc.Parameters.Add(DepObj);
    Proc.Execute();
    ObjOut := '';
    repeat
      Chunk := Proc.ReadOutput();
      ObjOut := ObjOut + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit()
  finally
    Proc.Free()
  end;
  AssertTrue('dependency .o has an .opdf section (objdump -h)',
    Pos('.opdf', ObjOut) >= 0);

  { The program still runs correctly. }
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_opdfdep exit code', 0, Rc);
  AssertEquals('use_opdfdep stdout', 'Hello, World' + #10 + 'Count is 2' + #10,
    Captured)
end;

{ Shared source for the two cross-unit static-member tests below.  RegModU
  declares a class with all three static member forms; the consuming program
  reaches them across the compiled .bif boundary. }
const
  StaticRegModSrc =
    '''
    unit RegModU;
    interface
    type
      TReg = class
      private static var
        FCount: Integer;
      public
        static function Next: Integer;
        { Static property whose getter is a static method: exercises
          TPropertyDecl.IsStatic surviving the .bif round-trip (a non-static
          import would dispatch with a bogus Self). }
        static property Counter: Integer read Next;
      public static const
        Tag = 7;
      end;
    implementation
    static function TReg.Next: Integer;
    begin
      FCount := FCount + 1;
      Result := FCount;
    end;
    end.
    ''';
  StaticRegProgSrc =
    '''
    program UseReg;
    uses RegModU;
    begin
      WriteLn(TReg.Next());
      WriteLn(TReg.Next());
      WriteLn(TReg.Counter);
      WriteLn(TReg.Tag)
    end.
    ''';

const
  RecClosUnitSrc =
    '''
    unit recclos;
    interface
    type
      TVal = record
        X: Integer;
        static function Make(A: Integer): TVal;
        function Doubled: Integer;
      end;
      TStep = reference to procedure;
      TWalker = class
      public
        procedure Walk(AMsg: string; AStep: TStep); overload;
        procedure Walk(AStep: TStep); overload;
      end;
    implementation
    static function TVal.Make(A: Integer): TVal;
    begin
      Result.X := A
    end;
    function TVal.Doubled: Integer;
    begin
      Result := X * 2
    end;
    procedure TWalker.Walk(AMsg: string; AStep: TStep);
    begin
      WriteLn(AMsg);
      AStep()
    end;
    procedure TWalker.Walk(AStep: TStep);
    begin
      AStep()
    end;
    end.
    ''';
  RecClosProgSrc =
    '''
    program userec;
    uses recclos;
    var
      V: TVal;
      W: TWalker;
    begin
      V := TVal.Make(21);
      W := TWalker.Create();
      W.Walk('go', procedure begin WriteLn(V.Doubled()) end)
    end.
    ''';

procedure TSepCompileTests.RunRecordMethodsAndClosuresWarmCache(
  const ABackend: string);
var
  UnitPas, ProgPas, ProgBin, CacheDir: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  UnitPas  := FScratch + '/recclos.pas';
  ProgPas  := FScratch + '/userec_' + ABackend + '.pas';
  ProgBin  := FScratch + '/userec_' + ABackend;
  CacheDir := FScratch + '/units-recclos-' + ABackend;
  WriteFile(UnitPas, RecClosUnitSrc);
  WriteFile(ProgPas, RecClosProgSrc);
  ForceDirectories(CacheDir);

  { Build 1: cold cache — everything from source. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', ABackend,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('cold build exit (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('cold run exit', 0, Rc);
  AssertEquals('cold stdout', 'go' + #10 + '42' + #10, Captured);

  { Build 2: warm cache — recclos loads from its .bif; the record's static
    and instance methods and the reference-to overloads must all resolve. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', ABackend,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('warm build exit (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('warm run exit', 0, Rc);
  AssertEquals('warm stdout', 'go' + #10 + '42' + #10, Captured)
end;

procedure TSepCompileTests.TestRecordMethodsAndClosures_WarmCache_Native;
begin
  Self.RunRecordMethodsAndClosuresWarmCache('native');
end;

procedure TSepCompileTests.TestRecordMethodsAndClosures_WarmCache_QBE;
begin
  Self.RunRecordMethodsAndClosuresWarmCache('qbe');
end;

procedure TSepCompileTests.TestStaticMembers_CrossUnit_QBE;
var
  UnitPas, ProgPas, ProgBin, CacheDir: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas  := FScratch + '/RegModU.pas';
  ProgPas  := FScratch + '/use_reg_qbe.pas';
  ProgBin  := FScratch + '/use_reg_qbe';
  CacheDir := FScratch + '/units-static-qbe';

  WriteFile(UnitPas, StaticRegModSrc);
  WriteFile(ProgPas, StaticRegProgSrc);
  ForceDirectories(CacheDir);

  { Build 1 (clean cache): RegModU compiled from source, .o/.bif cached. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'qbe',
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('qbe build1 exit (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('qbe build1 run exit', 0, Rc);
  AssertEquals('qbe build1 stdout', '1' + #10 + '2' + #10 + '3' + #10 + '7' + #10, Captured);

  { Build 2 (warm cache): RegModU loaded purely from its cached .bif — the
    static facts must survive the .bif round-trip. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'qbe',
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('qbe build2 exit (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('qbe build2 run exit', 0, Rc);
  AssertEquals('qbe build2 stdout', '1' + #10 + '2' + #10 + '3' + #10 + '7' + #10, Captured)
end;

procedure TSepCompileTests.TestStaticMembers_CrossUnit_Native;
var
  UnitPas, ProgPas, ProgBin, CacheDir: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas  := FScratch + '/RegModU.pas';
  ProgPas  := FScratch + '/use_reg_native.pas';
  ProgBin  := FScratch + '/use_reg_native';
  CacheDir := FScratch + '/units-static-native';

  WriteFile(UnitPas, StaticRegModSrc);
  WriteFile(ProgPas, StaticRegProgSrc);
  ForceDirectories(CacheDir);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('native build1 exit (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('native build1 run exit', 0, Rc);
  AssertEquals('native build1 stdout', '1' + #10 + '2' + #10 + '3' + #10 + '7' + #10, Captured);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('native build2 exit (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('native build2 run exit', 0, Rc);
  AssertEquals('native build2 stdout', '1' + #10 + '2' + #10 + '3' + #10 + '7' + #10, Captured)
end;

procedure TSepCompileTests.TestSameNamedModuleVar_AcrossUnits_ExternalLink_Native;
{ ua and ub each declare `var GVal: Integer` AND `threadvar GTls: Integer`.  On
  the native backend these must become ua_GVal/ub_GVal and ua_GTls/ub_GTls, not a
  single colliding GVal/GTls — proved by building with the EXTERNAL linker (which
  hard-fails on a duplicate definition) and by the program printing all four
  independent values. }
const
  UnitASrc =
    '''
    unit uaMV;
    interface
    procedure SetA(X: Integer);
    function GetA: Integer;
    procedure SetTlsA(X: Integer);
    function GetTlsA: Integer;
    implementation
    var GVal: Integer;
    threadvar GTls: Integer;
    procedure SetA(X: Integer); begin GVal := X; end;
    function GetA: Integer; begin Result := GVal; end;
    procedure SetTlsA(X: Integer); begin GTls := X; end;
    function GetTlsA: Integer; begin Result := GTls; end;
    end.
    ''';
  UnitBSrc =
    '''
    unit ubMV;
    interface
    procedure SetB(X: Integer);
    function GetB: Integer;
    procedure SetTlsB(X: Integer);
    function GetTlsB: Integer;
    implementation
    var GVal: Integer;
    threadvar GTls: Integer;
    procedure SetB(X: Integer); begin GVal := X; end;
    function GetB: Integer; begin Result := GVal; end;
    procedure SetTlsB(X: Integer); begin GTls := X; end;
    function GetTlsB: Integer; begin Result := GTls; end;
    end.
    ''';
  ProgSrc =
    '''
    program useMV;
    uses uaMV, ubMV;
    begin
      SetA(11); SetB(22);
      SetTlsA(33); SetTlsB(44);
      WriteLn(GetA());
      WriteLn(GetB());
      WriteLn(GetTlsA());
      WriteLn(GetTlsB());
    end.
    ''';
var
  UnitAPas, UnitBPas, ProgPas, ProgBin, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitAPas := FScratch + '/uaMV.pas';
  UnitBPas := FScratch + '/ubMV.pas';
  ProgPas  := FScratch + '/use_mv_native.pas';
  ProgBin  := FScratch + '/use_mv_native';

  WriteFile(UnitAPas, UnitASrc);
  WriteFile(UnitBPas, UnitBSrc);
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native', '--linker', 'external',
                   '--unit-path', FScratch], Captured);
  AssertEquals('native external link exit (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_mv_native exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_mv_native run exit', 0, Rc);
  AssertEquals('use_mv_native stdout',
    '11' + #10 + '22' + #10 + '33' + #10 + '44' + #10, Captured)
end;

procedure TSepCompileTests.TestSameNamedModuleVar_AcrossUnits_QBE;
{ Same two-units-same-named-var shape on the QBE backend (module var only — the
  QBE cross-unit threadvar TLS-reference path is a separate, pre-existing gap).
  QBE already mangled module vars by owner; this pins that it keeps working and
  that the two slots stay independent. }
const
  UnitASrc =
    '''
    unit uaMVq;
    interface
    procedure SetA(X: Integer);
    function GetA: Integer;
    implementation
    var GVal: Integer;
    procedure SetA(X: Integer); begin GVal := X; end;
    function GetA: Integer; begin Result := GVal; end;
    end.
    ''';
  UnitBSrc =
    '''
    unit ubMVq;
    interface
    procedure SetB(X: Integer);
    function GetB: Integer;
    implementation
    var GVal: Integer;
    procedure SetB(X: Integer); begin GVal := X; end;
    function GetB: Integer; begin Result := GVal; end;
    end.
    ''';
  ProgSrc =
    '''
    program useMVq;
    uses uaMVq, ubMVq;
    begin
      SetA(11); SetB(22);
      WriteLn(GetA());
      WriteLn(GetB());
    end.
    ''';
var
  UnitAPas, UnitBPas, ProgPas, ProgBin, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitAPas := FScratch + '/uaMVq.pas';
  UnitBPas := FScratch + '/ubMVq.pas';
  ProgPas  := FScratch + '/use_mv_qbe.pas';
  ProgBin  := FScratch + '/use_mv_qbe';

  WriteFile(UnitAPas, UnitASrc);
  WriteFile(UnitBPas, UnitBSrc);
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'qbe',
                   '--unit-path', FScratch], Captured);
  AssertEquals('qbe build exit (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_mv_qbe exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_mv_qbe run exit', 0, Rc);
  AssertEquals('use_mv_qbe stdout', '11' + #10 + '22' + #10, Captured)
end;

procedure TSepCompileTests.TestGenericInstance_CrossUnitCache_DefaultPropSetter_Runs;
const
  GenSrc =
    '''
    unit ugenBP;
    interface
    type
      TReg<T> = class
      private
        FVal: T;
        function GetItem(AKey: Integer): T;
        procedure SetItem(AKey: Integer; AVal: T);
      public
        procedure Put(AVal: T);
        function Get(): T;
        property Items[AKey: Integer]: T read GetItem write SetItem; default;
      end;
    implementation
    function TReg<T>.GetItem(AKey: Integer): T;
    begin
      Result := FVal
    end;
    procedure TReg<T>.SetItem(AKey: Integer; AVal: T);
    begin
      FVal := AVal
    end;
    procedure TReg<T>.Put(AVal: T);
    begin
      FVal := AVal
    end;
    function TReg<T>.Get(): T;
    begin
      Result := FVal
    end;
    end.
    ''';
  ProviderSrc =
    '''
    unit uproviderBP;
    interface
    uses ugenBP;
    function ProvideReg(): TReg<Integer>;
    implementation
    function ProvideReg(): TReg<Integer>;
    begin
      Result := TReg<Integer>.Create();
      Result[0] := 5
    end;
    end.
    ''';
  ReexportSrc =
    '''
    unit ureexportBP;
    interface
    uses ugenBP;
    type
      THolder = class
      public
        FReg: TReg<Integer>;
        constructor Create();
      end;
    implementation
    constructor THolder.Create();
    begin
      FReg := TReg<Integer>.Create()
    end;
    end.
    ''';
  Prog1Src =
    '''
    program prog1bp;
    uses ugenBP, uproviderBP, ureexportBP;
    var H: THolder;
    begin
      H := THolder.Create();
      H.FReg.Put(ProvideReg().Get());
      WriteLn(H.FReg.Get())
    end.
    ''';
  Consumer1Src =
    '''
    unit uconsumer1BP;
    interface
    uses ugenBP, ureexportBP;
    function ReadHolder(AH: THolder): Integer;
    implementation
    function ReadHolder(AH: THolder): Integer;
    begin
      Result := AH.FReg.Get()
    end;
    end.
    ''';
  Consumer2Src =
    '''
    unit uconsumer2BP;
    interface
    uses ugenBP, ureexportBP;
    procedure WriteHolder(AH: THolder; AVal: Integer);
    implementation
    procedure WriteHolder(AH: THolder; AVal: Integer);
    begin
      AH.FReg[0] := AVal
    end;
    end.
    ''';
  Prog2Src =
    '''
    program prog2bp;
    uses ugenBP, ureexportBP, uconsumer1BP, uconsumer2BP;
    var H: THolder;
    begin
      H := THolder.Create();
      WriteHolder(H, 42);
      WriteLn(ReadHolder(H))
    end.
    ''';
var
  GenPas, ProviderPas, ReexportPas: string;
  Consumer1Pas, Consumer2Pas: string;
  Prog1Pas, Prog2Pas, Prog1Bin, Prog2Bin: string;
  Cache1, Cache2: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  GenPas       := FScratch + '/ugenBP.pas';
  ProviderPas  := FScratch + '/uproviderBP.pas';
  ReexportPas  := FScratch + '/ureexportBP.pas';
  Consumer1Pas := FScratch + '/uconsumer1BP.pas';
  Consumer2Pas := FScratch + '/uconsumer2BP.pas';
  Prog1Pas     := FScratch + '/prog1bp.pas';
  Prog2Pas     := FScratch + '/prog2bp.pas';
  Prog1Bin     := FScratch + '/prog1bp';
  Prog2Bin     := FScratch + '/prog2bp';
  Cache1       := FScratch + '/cache1bp';
  Cache2       := FScratch + '/cache2bp';

  WriteFile(GenPas, GenSrc);
  WriteFile(ProviderPas, ProviderSrc);
  WriteFile(ReexportPas, ReexportSrc);
  WriteFile(Consumer1Pas, Consumer1Src);
  WriteFile(Consumer2Pas, Consumer2Src);
  WriteFile(Prog1Pas, Prog1Src);
  WriteFile(Prog2Pas, Prog2Src);
  ForceDirectories(Cache1);
  ForceDirectories(Cache2);

  { Process 1: populate cache1 with uprovider/ureexport compiled from source
    (uprovider's compile is where TReg<Integer> is first instantiated). }
  Rc := RunBlaise(['--source', Prog1Pas, '--output', Prog1Bin,
                   '--unit-cache', Cache1,
                   '--unit-path', FScratch], Captured);
  AssertEquals('prog1 build exit (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(Prog1Bin, Captured);
  AssertEquals('prog1 run exit', 0, Rc);
  AssertEquals('prog1 stdout', '5' + #10, Captured);

  { Hide the cached units' sources so process 2 must import their .bifs. }
  DeleteFile(GenPas);
  DeleteFile(ProviderPas);
  DeleteFile(ReexportPas);

  { Process 2: fresh cache, consumers compiled from source against cache1's
    .bifs.  uconsumer1 (compiled first) inherits the import-time pending
    instance; uconsumer2's default-property write must reference a SetItem
    copy that actually exists in some linked object. }
  Rc := RunBlaise(['--source', Prog2Pas, '--output', Prog2Bin,
                   '--unit-cache', Cache2,
                   '--unit-path', Cache1,
                   '--unit-path', FScratch], Captured);
  AssertEquals('prog2 build exit (out: ' + Captured + ')', 0, Rc);
  AssertTrue('prog2 exists', FileExists(Prog2Bin));

  { The historical failure mode is a LAZY link: the build succeeds and the
    dynamic loader aborts at run time with
    "undefined symbol: ureexportBP_TReg_Integer_SetItem". }
  Rc := RunBinary(Prog2Bin, Captured);
  AssertEquals('prog2 run exit (loader must resolve all instance symbols)',
    0, Rc);
  AssertEquals('prog2 stdout', '42' + #10, Captured)
end;

procedure TSepCompileTests.TestGenericBodyClosure_RoundTrip_WithoutSource;
const
  DepSrc =
    '''
    unit uclosgen;
    interface
    type
      TGetter<T> = reference to function(): T;
      TBox<T> = class
      public
        FVal: T;
        function Make(): TGetter<T>;
      end;
    implementation
    function TBox<T>.Make(): TGetter<T>;
    begin
      Result := function(): T
        begin
          Result := FVal
        end;
    end;
    end.
    ''';
  ProgSrc =
    '''
    program useclos;
    uses uclosgen;
    var
      BI: TBox<Integer>;
      BS: TBox<string>;
      GI: TGetter<Integer>;
      GS: TGetter<string>;
    begin
      BI := TBox<Integer>.Create();
      BI.FVal := 41;
      BS := TBox<string>.Create();
      BS.FVal := 'boxed';
      GI := BI.Make();
      GS := BS.Make();
      BS := nil;
      WriteLn(GI() + 1);
      WriteLn(GS())
    end.
    ''';
var
  DepPas, DepObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas  := FScratch + '/uclosgen.pas';
  DepObj  := FScratch + '/uclosgen.o';
  ProgPas := FScratch + '/useclos.pas';
  ProgBin := FScratch + '/useclos';

  WriteFile(DepPas, DepSrc);
  Rc := RunBlaise(['--source', DepPas, '--output', DepObj], Captured);
  AssertEquals('blaise(uclosgen) exit (out: ' + Captured + ')', 0, Rc);

  DeleteFile(DepPas);
  AssertFalse('uclosgen.pas hidden', FileExists(DepPas));

  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(useclos) exit (out: ' + Captured + ')', 0, Rc);

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('useclos run exit', 0, Rc);
  AssertEquals('useclos stdout', '42' + #10 + 'boxed' + #10, Captured)
end;

procedure TSepCompileTests.TestCollidingGenerics_TwoSourceUnits_Rejected;
const
  UnitASrc =
    '''
    unit GdupA;
    interface
    type
      TBox<T> = class
      public
        FValue: T;
      end;
    function MakeA(): Integer;
    implementation
    function MakeA(): Integer;
    var B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.FValue := 41;
      Result := B.FValue;
      B.Free()
    end;
    end.
    ''';
  UnitBSrc =
    '''
    unit GdupB;
    interface
    type
      TBox<T> = class
      public
        FTag: Integer;
        FValue: T;
      end;
    function MakeB(): Integer;
    implementation
    function MakeB(): Integer;
    var B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.FValue := 1;
      Result := B.FValue;
      B.Free()
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseDup;
    uses GdupA, GdupB;
    begin
      WriteLn(MakeA() + MakeB())
    end.
    ''';
var
  ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  WriteFile(FScratch + '/GdupA.pas', UnitASrc);
  WriteFile(FScratch + '/GdupB.pas', UnitBSrc);
  ProgPas := FScratch + '/use_dup.pas';
  ProgBin := FScratch + '/use_dup';
  WriteFile(ProgPas, ProgSrc);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertTrue('compile must FAIL (colliding generic TBox), out: ' + Captured,
             Rc <> 0);
  AssertTrue('error names the colliding generic, out: ' + Captured,
             Pos('TBox', Captured) >= 0);
  AssertTrue('error says declared in both, out: ' + Captured,
             Pos('is declared in both', Captured) >= 0);
  AssertTrue('error names unit GdupA, out: ' + Captured,
             Pos('GdupA', Captured) >= 0);
  AssertTrue('error names unit GdupB, out: ' + Captured,
             Pos('GdupB', Captured) >= 0)
end;

procedure TSepCompileTests.TestCollidingGenerics_CachedIface_Rejected;
{ Same collision, but each unit is first compiled to its own .o (each is
  fine in isolation) and the sources are hidden — the consumer build sees
  only the cached .bif ifaces, so the conflict must be caught on the
  uSemanticImport registration path, not the source-analysis one. }
const
  UnitASrc =
    '''
    unit GcacA;
    interface
    type
      TBox<T> = class
      public
        FValue: T;
      end;
    function MakeA(): Integer;
    implementation
    function MakeA(): Integer;
    var B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.FValue := 41;
      Result := B.FValue;
      B.Free()
    end;
    end.
    ''';
  UnitBSrc =
    '''
    unit GcacB;
    interface
    type
      TBox<T> = class
      public
        FTag: Integer;
        FValue: T;
      end;
    function MakeB(): Integer;
    implementation
    function MakeB(): Integer;
    var B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.FValue := 1;
      Result := B.FValue;
      B.Free()
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseCac;
    uses GcacA, GcacB;
    begin
      WriteLn(MakeA() + MakeB())
    end.
    ''';
var
  UnitAPas, UnitBPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitAPas := FScratch + '/GcacA.pas';
  UnitBPas := FScratch + '/GcacB.pas';
  ProgPas  := FScratch + '/use_cac.pas';
  ProgBin  := FScratch + '/use_cac';

  WriteFile(UnitAPas, UnitASrc);
  Rc := RunBlaise(['--source', UnitAPas,
                   '--output', FScratch + '/GcacA.o'], Captured);
  AssertEquals('blaise(GcacA) exit code 0' + #10 + Captured, 0, Rc);
  WriteFile(UnitBPas, UnitBSrc);
  Rc := RunBlaise(['--source', UnitBPas,
                   '--output', FScratch + '/GcacB.o'], Captured);
  AssertEquals('blaise(GcacB) exit code 0' + #10 + Captured, 0, Rc);

  DeleteFile(UnitAPas);
  DeleteFile(UnitBPas);

  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertTrue('compile must FAIL (colliding cached generic TBox), out: '
             + Captured, Rc <> 0);
  AssertTrue('error names the colliding generic, out: ' + Captured,
             Pos('TBox', Captured) >= 0);
  AssertTrue('error says declared in both, out: ' + Captured,
             Pos('is declared in both', Captured) >= 0)
end;

procedure TSepCompileTests.TestCollidingGenericRoutines_CachedIface_Rejected;
const
  UnitASrc =
    '''
    unit GfnA;
    interface
    function Pick<T>(AVal: T): T;
    implementation
    function Pick<T>(AVal: T): T;
    begin
      Result := AVal
    end;
    end.
    ''';
  UnitBSrc =
    '''
    unit GfnB;
    interface
    function Pick<T>(AVal: T): T;
    implementation
    function Pick<T>(AVal: T): T;
    begin
      Result := AVal
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseFn;
    uses GfnA, GfnB;
    begin
      WriteLn(Pick<Integer>(7))
    end.
    ''';
var
  UnitAPas, UnitBPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitAPas := FScratch + '/GfnA.pas';
  UnitBPas := FScratch + '/GfnB.pas';
  ProgPas  := FScratch + '/use_fn.pas';
  ProgBin  := FScratch + '/use_fn';

  WriteFile(UnitAPas, UnitASrc);
  Rc := RunBlaise(['--source', UnitAPas,
                   '--output', FScratch + '/GfnA.o'], Captured);
  AssertEquals('blaise(GfnA) exit code 0' + #10 + Captured, 0, Rc);
  WriteFile(UnitBPas, UnitBSrc);
  Rc := RunBlaise(['--source', UnitBPas,
                   '--output', FScratch + '/GfnB.o'], Captured);
  AssertEquals('blaise(GfnB) exit code 0' + #10 + Captured, 0, Rc);

  DeleteFile(UnitAPas);
  DeleteFile(UnitBPas);

  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertTrue('compile must FAIL (colliding generic routine Pick), out: '
             + Captured, Rc <> 0);
  AssertTrue('error names the colliding routine, out: ' + Captured,
             Pos('Pick', Captured) >= 0);
  AssertTrue('error says declared in both, out: ' + Captured,
             Pos('is declared in both', Captured) >= 0)
end;

procedure TSepCompileTests.TestStaticAsyncReactor_LinksAndRuns;
{$IFDEF LINUX}
const
  ProgSrc =
    '''
    program staticepoll;
    uses async.fibers;
    procedure Work(AArg: Pointer);
    begin
      FiberSleep(1);
      WriteLn('OK')
    end;
    begin
      SpawnFiber(@Work, nil);
      RunScheduler();
      WriteLn('DONE')
    end.
    ''';
var
  ProgPas, ProgBin, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  if not FileExists(BlaisePath()) then begin Ignore('blaise binary missing'); Exit; end;

  ProgPas := FScratch + '/staticepoll.pas';
  ProgBin := FScratch + '/staticepoll';
  WriteFile(ProgPas, ProgSrc);

  { Compile + link --static.  Before BUG-042 Gap 1 this died with an internal
    linker error: undefined reference to epoll_ctl / eventfd. }
  Rc := RunBlaise(['--source', ProgPas, '--backend', 'native', '--static',
                   '--output', ProgBin,
                   '--unit-path', ProjectRoot() + 'compiler/src/main/pascal',
                   '--unit-path', ProjectRoot() + 'stdlib/src/main/pascal'],
                  Captured);
  AssertEquals('static compile+link exit code, out: ' + Captured, 0, Rc);
  AssertTrue('static binary exists', FileExists(ProgBin));

  { It must actually run (drives epoll_wait + eventfd through the reactor). }
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('static binary exit code', 0, Rc);
  AssertEquals('static binary stdout', 'OK' + #10 + 'DONE' + #10, Captured);
end;
{$ELSE}
begin
  Ignore('static async reactor is Linux-only');
end;
{$ENDIF}

initialization
  RegisterTest(TSepCompileTests);

end.
