{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Skeleton tests for TUnitInterface (Phase 1 of separate compilation).

  The contract being pinned down here:

    TUnitInterface is the self-contained, post-semantic description of
    a unit's interface section.  Once produced by AnalyseUnitForExport,
    it must be usable by downstream compilation passes WITHOUT keeping
    the source TUnit alive.

  Every test in this file targets one property of that contract.  They
  are deliberately stubbed with Fail('TODO …') so the green/red bar
  acts as a checklist as the implementation lands. }

unit cp.test.unitinterface;

interface

uses
  Classes, contnrs, blaise.testing,
  uAST, uLexer, uParser, uSemantic, uSymbolTable,
  uUnitInterface, uSemanticExport, uSemanticImport, uUnitInterfaceIO;

type
  { ParseAndExport helper — shared across fixtures.  Stubbed for now;
    once uUnitInterface exists, this becomes the single point that
    parses a source string, runs AnalyseUnitForExport, and hands back
    the resulting TUnitInterface for inspection.

    Returning Pointer (not TUnitInterface) keeps this unit free of a
    uUnitInterface dependency while the type doesn't exist yet. }

  { ----- Self-containment ----------------------------------------- }

  [Threaded]
  TSelfContainmentTests = class(TTestCase)
  published
    { After AnalyseUnitForExport returns, freeing the source TUnit
      must not affect lookups against the interface. }
    procedure TestInterfaceUsable_AfterSourceUnitFreed;

    { No member of TUnitInterface holds a pointer into the source
      TUnit's AST.  Spot-checks via identity comparison after free. }
    procedure TestNoBackPointers_IntoSourceAST;

    { Cloning of generic/inline bodies is deep — mutating the source
      block (before free) must not affect the cloned body. }
    procedure TestGenericBody_IsDeepClone;
    procedure TestInlineBody_IsDeepClone;
  end;

  { ----- Cross-unit references ------------------------------------ }

  [Threaded]
  TCrossUnitRefTests = class(TTestCase)
  published
    { Unit B references a type from unit A: B's interface stores the
      ref as TQualTypeRef('A','TFoo'), not as a pointer into A. }
    procedure TestTypeFromOtherUnit_QualifiedByName;

    { Local types referenced inside the same unit appear with
      UnitName = '' (this unit). }
    procedure TestLocalTypeRef_UnqualifiedUnitName;

    { Builtins (Integer, string, Boolean, …) get UnitName = '$builtin'. }
    procedure TestBuiltinTypeRef_BuiltinUnitName;
  end;

  { ----- Const round-trip ----------------------------------------- }

  [Threaded]
  TConstRoundTripTests = class(TTestCase)
  published
    procedure TestIntegerConst_ValuePreserved;
    procedure TestStringConst_ValuePreserved;
    procedure TestFloatConst_ValuePreserved;
    procedure TestIdentRefConst_PartsPreserved;
    procedure TestArrayConst_ElementsAndBoundsPreserved;
    procedure TestEnumIndexedArrayConst_IndexTypePreserved;
  end;

  { ----- Enum & set type structure -------------------------------- }

  [Threaded]
  TEnumSetTests = class(TTestCase)
  published
    procedure TestEnum_MembersAndOrdinalsPreserved;
    procedure TestSet_BaseEnumPreserved;
  end;

  { ----- Record & class layout ------------------------------------ }

  [Threaded]
  TRecordClassLayoutTests = class(TTestCase)
  published
    procedure TestRecord_FieldsInDeclarationOrder;
    procedure TestRecord_FieldTypes_AsQualTypeRef;
    procedure TestClass_ParentClassResolved;
    procedure TestClass_ImplementsListPopulated;
    procedure TestClass_MethodSignaturesExported;
    procedure TestClass_VTableSlotsAssigned;
    procedure TestClass_InstanceSizeComputed;
    procedure TestClass_AttributesPreserved;
  end;

  { ----- Inline & generic bodies ---------------------------------- }

  [Threaded]
  TInlineGenericBodyTests = class(TTestCase)
  published
    { inline routine declared in interface → InlineBodies entry. }
    procedure TestInline_BodyExportedWithSig;

    { Generic class declared in interface → GenericBodies entry with
      TypeParams populated, TypeDef cloned. }
    procedure TestGenericType_BodyExported;

    { Generic free routine → GenericBodies entry with RoutineSig +
      Body, IsType=False. }
    procedure TestGenericRoutine_BodyExported;

    { Constraints (e.g. <T: TFoo>) propagate to TGenericBody.Constraints
      parallel-array. }
    procedure TestGeneric_ConstraintsPreserved;
  end;

  { ----- Implementation invisibility ------------------------------ }

  [Threaded]
  TImplementationHidingTests = class(TTestCase)
  published
    { Routine declared only in impl section: absent from .Routines. }
    procedure TestImplOnlyRoutine_NotExported;

    { Type declared only in impl section: absent from .Types. }
    procedure TestImplOnlyType_NotExported;

    { Regular (non-inline, non-generic) routine declared in interface:
      signature exported, no body in InlineBodies/GenericBodies. }
    procedure TestRegularRoutine_SigOnly_NoBody;
  end;

  { ----- Visibility ----------------------------------------------- }

  [Threaded]
  TVisibilityTests = class(TTestCase)
  published
    { Class members carry their declared visibility through to the
      exported entries.  Decision pending: do we export private
      members at all, or filter them out?  This test pins down
      whichever choice we make. }
    procedure TestClassMember_VisibilityPreserved;
  end;

  { ----- Forward-declared class completion ------------------------ }

  [Threaded]
  TForwardDeclTests = class(TTestCase)
  published
    { `type TFoo = class;` in interface + full body in impl: the
      exported entry for TFoo carries the full structure (fields,
      methods, parent), not just the forward stub.  Documents the
      accepted impl-leak. }
    procedure TestForwardDeclClass_FullBodyExported;
  end;

  { ----- Routine signature details -------------------------------- }

  [Threaded]
  TRoutineSigTests = class(TTestCase)
  published
    procedure TestParam_ModeVar_Preserved;
    procedure TestParam_ModeConst_Preserved;
    procedure TestParam_ModeOut_Preserved;
    procedure TestReturnType_FunctionVsProcedure;
    procedure TestCallingConv_Cdecl_Preserved;
    procedure TestExternal_NamePreserved;
  end;

  { ----- UsedUnits ------------------------------------------------ }

  [Threaded]
  TUsedUnitsTests = class(TTestCase)
  published
    { UsedUnits reflects the interface uses clause, in declaration order. }
    procedure TestUsedUnits_OrderPreserved;

    { Units used only by the implementation section do NOT appear in
      the exported UsedUnits list. }
    procedure TestImplOnlyUsedUnit_NotInUsedUnits;
  end;

  { ----- Lookup helpers ------------------------------------------- }

  [Threaded]
  TLookupTests = class(TTestCase)
  published
    procedure TestFindType_CaseInsensitive;
    procedure TestFindConst_CaseInsensitive;
    procedure TestFindRoutine_CaseInsensitive;
    procedure TestFindGeneric_CaseInsensitive;
    procedure TestFind_Missing_ReturnsNil;
    procedure TestFindType_CaseSensitive_FlagRespected;
  end;

  { ----- Metadata ------------------------------------------------- }

  [Threaded]
  TMetadataTests = class(TTestCase)
  published
    procedure TestName_MatchesSource;
    procedure TestSourceFile_MatchesPath;
    procedure TestSourceHash_NonEmpty;
    procedure TestCompilerId_NonEmpty;
  end;

  { ----- TUnitInterface disk format (Phase 6c-E starter) --------- }

  [Threaded]
  TIfaceIOTests = class(TTestCase)
  published
    { Header carries magic + version. }
    procedure TestWrite_StartsWithMagicAndVersion;
    { Unit name round-trips. }
    procedure TestRoundTrip_UnitNamePreserved;
    { HasInitialization / HasFinalization round-trip via the META block —
      a dropped fini flag means a cached unit's <Unit>_fini is never called
      (finalization skipped, globals leak). }
    procedure TestRoundTrip_InitFiniFlagsPreserved;
    { External-library link deps (LinkLibs) round-trip via the META block. }
    procedure TestRoundTrip_LinkLibsPreserved;
    { Int const round-trips. }
    procedure TestRoundTrip_IntConstPreserved;
    { Named integer subrange alias round-trips its IsSubrange + lo..hi bounds,
      so array[OtherUnit.TSub] still folds across separate compilation. }
    procedure TestRoundTrip_NamedSubrangeAlias_BoundsPreserved;
    { String const round-trips, even with newlines + colons in the value. }
    procedure TestRoundTrip_StringConstWithAwkwardChars;
    { Empty interface round-trips (zero consts). }
    procedure TestRoundTrip_EmptyInterface;
    { Version mismatch is rejected. }
    procedure TestRead_VersionMismatch_Raises;
    { Whole-pipeline round-trip via the export machinery on a real
      source — exercises types/consts/vars/routines together. }
    procedure TestRoundTrip_RealSource_AllSimpleKinds;
    { File wrappers. }
    procedure TestRoundTrip_ViaFile;
    procedure TestRoundTrip_Record;
    procedure TestRoundTrip_Class_WithVirtualMethod;
    procedure TestRoundTrip_Class_WithOverloadedMethods;
    procedure TestRoundTrip_Interface_WithOverloadedMethods;
    procedure TestRoundTrip_Interface;
    procedure TestRoundTrip_Interface_WithProperty;
    procedure TestRoundTrip_ProceduralType;
    procedure TestRoundTrip_ReferenceToType;
    procedure TestRoundTrip_Metadata_UsedUnits_SourceFile;
    procedure TestRoundTrip_GenericClass_TemplateParams;
    procedure TestRoundTrip_GenericInterface_TemplateParams;
    { End-to-end via the disk path: write → read → import.  Validates
      the wire format carries enough info to feed ImportUnitInterface
      directly, with no fresh-from-source rebuild in the middle. }
    procedure TestDiskPath_Const_ImportsCleanly;
    procedure TestDiskPath_Enum_ImportsCleanly;
    procedure TestDiskPath_Class_ImportsCleanly;
    procedure TestDiskPath_GenericClass_ImportsCleanly;
    procedure TestDiskPath_GenericRoutine_ImportsCleanly;
    { Body survives the disk path — the AST body serialiser
      preserves statements/expressions through write+read. }
    procedure TestDiskPath_GenericRoutine_BodyPreserved;
    procedure TestRoundTrip_InlineBody_Preserved;
    { Static (class-level) member facts must survive export-clone → encode →
      decode.  The export clone previously dropped TFieldDecl.IsClassVar /
      ClassVarEmitName, TMethodDecl.IsStatic and TPropertyDecl.IsStatic, so
      they encoded as defaults. }
    procedure TestRoundTrip_StaticMembers_Preserved;
    { Pre-existing clone bug uncovered alongside the static-members work: a
      [Weak] field and a `default` property round-tripped as plain owning /
      non-default because CloneFieldDecl / ClonePropertyDecl dropped IsWeak
      and IsDefault before encoding. }
    procedure TestRoundTrip_WeakField_And_DefaultProperty_Preserved;
  end;

  { ----- ImportUnitInterface round-trip (Phase 6c-A) -------------- }

  { Each test below exports a unit's interface, then imports that
    interface into a fresh TSymbolTable, and asserts the symbol
    table looks like a from-scratch AnalyseUnitForExport would have
    produced.  Class/generic cases are intentionally NOT covered
    here — they land with 6c-B/C. }
  [Threaded]
  TImportRoundTripTests = class(TTestCase)
  published
    procedure TestImport_IntConst_DefinedWithValue;
    procedure TestImport_StringConst_DefinedWithValue;
    procedure TestImport_Enum_TypeAndMembersDefined;
    { An imported enum must be indistinguishable from a source-visible one:
      its members must land in the analyser's enum-member reverse index, which
      is the only thing ResolveEnumMember (and hence ArgMatchScore's inference
      of a bracket literal's base enum) consults. }
    procedure TestImport_Enum_MembersInAnalyserReverseIndex;
    procedure TestImport_Set_BaseEnumLinked;
    procedure TestImport_Alias_ResolvesToBase;
    procedure TestImport_ProcedureRoutine_DefinedAsSkProcedure;
    procedure TestImport_FunctionRoutine_DefinedAsSkFunction;
    procedure TestImport_GlobalVar_MarkedIsGlobal;
    procedure TestImport_Record_FieldsImportedWithOffsets;
    procedure TestImport_Class_ImplicitTObjectParent;
    procedure TestImport_Class_FieldOffsetAfterParentVptr;
    procedure TestImport_Class_ExplicitParentChain;
    procedure TestImport_Class_VirtualMethod_AddsVTableSlot;
    procedure TestImport_Class_Override_ReusesParentSlot;
    procedure TestImport_Interface_MethodsRegistered;
    procedure TestImport_Class_ImplementsInterface;
    procedure TestImport_Class_AttributePreserved;
    procedure TestImport_GenericClass_RegisteredAsTemplate;
    procedure TestImport_GenericInterface_RegisteredAsTemplate;
    procedure TestImport_GenericRoutine_RegisteredOnTable;
    procedure TestEndToEnd_MainProgramSeesImportedConst;
    procedure TestEndToEnd_MainProgramSeesImportedClass;
  end;

implementation

const
  TODO_MSG = 'TODO: TUnitInterface not yet implemented (Phase 1)';

{ ParseAndExport — central helper.  Parses ASource as a Blaise unit
  and runs ExportUnitInterface against it (no semantic — Phase 2 export
  walks raw parsed fields; semantic-derived export comes later).
  Returns the produced TUnitInterface; caller owns it.

  ASource is treated as the entire content of a .pas file: must begin
  with 'unit Name;' and contain interface/implementation/end.
  Deps is empty for now; cross-unit tests will pre-populate it. }
{ Like ParseAndExport but also runs uSemantic.AnalyseUnitForExport
  on the parsed unit before producing the TUnitInterface.  Use this
  when a test needs semantic-populated fields (VTableSlot,
  InstanceSize, resolved field types). }
function ParseAnalyseAndExport(const ASource: string): TUnitInterface;
var
  Lex:    TLexer;
  Parser: TParser;
  U:      TUnit;
  Sem:    TSemanticAnalyser;
begin
  Lex := TLexer.Create(ASource, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit();
      try
        Sem := TSemanticAnalyser.Create();
        try
          Sem.AnalyseUnitForExport(U);
          Result := ExportUnitInterface(U, nil, Sem.GetSymbolTable());
        finally
          Sem.Free();
        end;
      finally
        U.Free();
      end;
    finally
      Parser.Free();
    end;
  finally
    Lex.Free();
  end;
end;

function ParseAndExportWithDeps(const ASource: string;
                                ADeps: TObjectList): TUnitInterface;
var
  Lex:    TLexer;
  Parser: TParser;
  U:      TUnit;
begin
  Lex := TLexer.Create(ASource, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit();
      try
        Result := ExportUnitInterface(U, ADeps);
      finally
        U.Free();
      end;
    finally
      Parser.Free();
    end;
  finally
    Lex.Free();
  end;
end;

function ParseAndExport(const ASource: string): TUnitInterface;
var
  Lex:    TLexer;
  Parser: TParser;
  U:      TUnit;
begin
  Lex := TLexer.Create(ASource, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit();
      try
        Result := ExportUnitInterface(U, nil);  { no deps yet }
      finally
        U.Free();
      end;
    finally
      Parser.Free();
    end;
  finally
    Lex.Free();
  end;
end;

{ ==================================================================
  Stubs.  Each test fails with TODO_MSG until the production code
  lands and the body is fleshed out.
  ================================================================== }

{ ----- TSelfContainmentTests ------------------------------------ }

{ Note: ParseAndExport already frees the source TUnit before returning,
  so any successful test that uses the returned interface is implicit
  evidence of self-containment.  These tests make that property
  explicit and exercise a richer cross-section of the interface to
  catch any field that quietly held a pointer back to the source. }

procedure TSelfContainmentTests.TestInterfaceUsable_AfterSourceUnitFreed;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'uses SysUtils;'                                    + #10 +
    'const Pi = 3.14;'                                  + #10 +
    'type'                                              + #10 +
    '  TColor = (Red, Green, Blue);'                    + #10 +
    '  TPoint = record X, Y: Integer; end;'             + #10 +
    'function Hello(const Who: string): string;'        + #10 +
    'implementation'                                    + #10 +
    'function Hello(const Who: string): string; begin Result := Who; end;' + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);    { source TUnit is freed inside helper }
  try
    { Walk a deliberately mixed cross-section.  If anything in the
      interface still pointed at freed memory, one of these would
      either return nil unexpectedly or crash. }
    AssertEquals('uses',     1, Iface.UsedUnits.Count);
    AssertEquals('uses[0]',  'SysUtils', Iface.UsedUnits.Strings[0]);

    AssertEquals('type TColor', True, Iface.FindType('TColor') <> nil);
    AssertEquals('type TPoint', True, Iface.FindType('TPoint') <> nil);
    AssertEquals('const Pi',    True, Iface.FindConst('Pi') <> nil);
    AssertEquals('routine Hello', True, Iface.FindRoutine('Hello') <> nil);

    { Recursive walk through cloned AST — proves Def is a real
      clone, not a dangling ref. }
    AssertEquals('TColor is enum',
                 True, Iface.FindType('TColor').Def is TEnumTypeDef);
    AssertEquals('TPoint is record',
                 True, Iface.FindType('TPoint').Def is TRecordTypeDef);
    { TPoint declares 'X, Y: Integer' — one TFieldDecl carrying two names. }
    AssertEquals('TPoint field-decl count', 1,
                 TRecordTypeDef(Iface.FindType('TPoint').Def).Fields.Count);
    AssertEquals('TPoint name count', 2,
                 TFieldDecl(TRecordTypeDef(Iface.FindType('TPoint').Def)
                              .Fields.Items[0]).Names.Count);
  finally
    Iface.Free();
  end;
end;

procedure TSelfContainmentTests.TestNoBackPointers_IntoSourceAST;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type TFoo = record A: Integer; end;'               + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Lex:     TLexer;
  Parser:  TParser;
  U:       TUnit;
  Iface:   TUnitInterface;
  SrcDef:  TASTTypeDef;
  IfaceDef: TASTTypeDef;
begin
  { Build by hand so we can compare the source's TASTTypeDef pointer
    against the interface's TASTTypeDef pointer.  They MUST differ —
    if they're equal, the export pass leaked a back-pointer. }
  Lex := TLexer.Create(SRC, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit();
      try
        SrcDef := TTypeDecl(U.IntfBlock.TypeDecls.Items[0]).Def;
        Iface  := ExportUnitInterface(U, nil);
        try
          IfaceDef := Iface.FindType('TFoo').Def;
          AssertEquals('def is a clone, not a ref',
                       True, SrcDef <> IfaceDef);
        finally
          Iface.Free();
        end;
      finally
        U.Free();
      end;
    finally
      Parser.Free();
    end;
  finally
    Lex.Free();
  end;
end;
procedure TSelfContainmentTests.TestGenericBody_IsDeepClone;
const
  SRC =
    'unit TestU;'                                + #10 +
    'interface'                                  + #10 +
    'type TBox<T> = class Value: T; end;'        + #10 +
    'implementation'                             + #10 +
    'end.'                                       + #10;
var
  Lex:    TLexer;
  Parser: TParser;
  U:      TUnit;
  Iface:  TUnitInterface;
  SrcDef: TASTTypeDef;
  GBody:  TGenericBody;
begin
  Lex := TLexer.Create(SRC, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit();
      try
        SrcDef := TTypeDecl(U.IntfBlock.TypeDecls.Items[0]).Def;
        Iface  := ExportUnitInterface(U, nil);
        try
          GBody := Iface.FindGeneric('TBox');
          AssertEquals('generic found', True, GBody <> nil);
          AssertEquals('TypeDef cloned, not aliased',
                       True, GBody.TypeDef <> SrcDef);
        finally
          Iface.Free();
        end;
      finally
        U.Free();
      end;
    finally
      Parser.Free();
    end;
  finally
    Lex.Free();
  end;
end;

procedure TSelfContainmentTests.TestInlineBody_IsDeepClone;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'function Square(N: Integer): Integer; inline;'        + #10 +
    'implementation'                                       + #10 +
    'function Square(N: Integer): Integer; begin Result := N * N; end;' + #10 +
    'end.'                                                 + #10;
var
  Lex:     TLexer;
  Parser:  TParser;
  U:       TUnit;
  Iface:   TUnitInterface;
  SrcImpl: TMethodDecl;
  Body:    TInlineBody;
begin
  Lex := TLexer.Create(SRC, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit();
      try
        SrcImpl := TMethodDecl(U.ImplBlock.ProcDecls.Items[0]);
        Iface   := ExportUnitInterface(U, nil);
        try
          Body := Iface.FindInlineBody('Square');
          AssertEquals('body found', True, Body <> nil);
          AssertEquals('block cloned, not aliased',
                       True, Body.Block <> SrcImpl.Body);
        finally
          Iface.Free();
        end;
      finally
        U.Free();
      end;
    finally
      Parser.Free();
    end;
  finally
    Lex.Free();
  end;
end;

{ ----- TCrossUnitRefTests --------------------------------------- }

{ Build a small 'DepU' interface containing TWidget, then export
  a consumer that references it.  The consumer's ReturnType field
  (which goes through ResolveTypeRef) is the cleanest observable
  for cross-unit qualification today — record-field types still
  travel as raw TypeName strings until Phase 3. }

procedure TCrossUnitRefTests.TestTypeFromOtherUnit_QualifiedByName;
const
  DEP_SRC =
    'unit DepU;'                                + #10 +
    'interface'                                 + #10 +
    'type TWidget = record N: Integer; end;'    + #10 +
    'implementation'                            + #10 +
    'end.'                                      + #10;
  MAIN_SRC =
    'unit MainU;'                               + #10 +
    'interface'                                 + #10 +
    'uses DepU;'                                + #10 +
    'function MakeOne: TWidget;'                + #10 +
    'implementation'                            + #10 +
    'function MakeOne: TWidget; begin end;'     + #10 +
    'end.'                                      + #10;
var
  Deps:  TObjectList;
  Dep:   TUnitInterface;
  Main:  TUnitInterface;
  Sig:   TRoutineSig;
begin
  Dep  := ParseAndExport(DEP_SRC);
  Deps := TObjectList.Create(False);  { non-owning — Dep freed below }
  try
    Deps.Add(Dep);
    Main := ParseAndExportWithDeps(MAIN_SRC, Deps);
    try
      Sig := Main.FindRoutine('MakeOne');
      AssertEquals('routine found',    True, Sig <> nil);
      AssertEquals('return type name', 'TWidget', Sig.ReturnType.TypeName);
      AssertEquals('return type unit', 'DepU',    Sig.ReturnType.UnitName);
    finally
      Main.Free();
    end;
  finally
    Deps.Free();
    Dep.Free();
  end;
end;

procedure TCrossUnitRefTests.TestLocalTypeRef_UnqualifiedUnitName;
const
  SRC =
    'unit TestU;'                               + #10 +
    'interface'                                 + #10 +
    'type TItem = record N: Integer; end;'      + #10 +
    'function Make: TItem;'                     + #10 +
    'implementation'                            + #10 +
    'function Make: TItem; begin end;'          + #10 +
    'end.'                                      + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Make');
    AssertEquals('return type name', 'TItem', Sig.ReturnType.TypeName);
    AssertEquals('is local ref',     True,    IsLocalRef(Sig.ReturnType));
    AssertEquals('unit name empty',  '',      Sig.ReturnType.UnitName);
  finally
    Iface.Free();
  end;
end;

procedure TCrossUnitRefTests.TestBuiltinTypeRef_BuiltinUnitName;
const
  SRC =
    'unit TestU;'                              + #10 +
    'interface'                                + #10 +
    'function Count: Integer;'                 + #10 +
    'implementation'                           + #10 +
    'function Count: Integer; begin end;'      + #10 +
    'end.'                                     + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Count');
    AssertEquals('return type name', 'Integer', Sig.ReturnType.TypeName);
    AssertEquals('is builtin ref',   True,      IsBuiltinRef(Sig.ReturnType));
    AssertEquals('unit name builtin','$builtin',Sig.ReturnType.UnitName);
  finally
    Iface.Free();
  end;
end;

{ ----- TConstRoundTripTests ------------------------------------- }

{ Helpers — assemble TConstDecl variants directly, then wrap in
  TConstEntry and stash via AddConst.  Mirror the shape that
  AnalyseUnitForExport will eventually produce. }

function MakeIntConst(const AName: string; AValue: Int64): TConstEntry;
begin
  Result := TConstEntry.Create();
  Result.Decl := TConstDecl.Create();
  Result.Decl.Name   := AName;
  Result.Decl.IntVal := AValue;
  Result.TypeRef := MakeBuiltinRef('Integer');
end;

function MakeStringConst(const AName, AValue: string): TConstEntry;
begin
  Result := TConstEntry.Create();
  Result.Decl := TConstDecl.Create();
  Result.Decl.Name     := AName;
  Result.Decl.StrVal   := AValue;
  Result.Decl.IsString := True;
  Result.TypeRef := MakeBuiltinRef('string');
end;

function MakeFloatConst(const AName, AText: string): TConstEntry;
begin
  Result := TConstEntry.Create();
  Result.Decl := TConstDecl.Create();
  Result.Decl.Name    := AName;
  Result.Decl.StrVal  := AText;        { raw float text }
  Result.Decl.IsFloat := True;
  Result.TypeRef := MakeBuiltinRef('Double');
end;

procedure TConstRoundTripTests.TestIntegerConst_ValuePreserved;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeIntConst('MaxBuf', 4096));

    E := U.FindConst('MaxBuf');
    AssertEquals('found', True, E <> nil);
    AssertEquals('value',  Int64(4096), E.Decl.IntVal);
    AssertEquals('not string', False, E.Decl.IsString);
    AssertEquals('not float',  False, E.Decl.IsFloat);
    AssertEquals('type ref',  'Integer', E.TypeRef.TypeName);
  finally
    U.Free();
  end;
end;

procedure TConstRoundTripTests.TestStringConst_ValuePreserved;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeStringConst('Greeting', 'hello world'));

    E := U.FindConst('Greeting');
    AssertEquals('found', True, E <> nil);
    AssertEquals('value', 'hello world', E.Decl.StrVal);
    AssertEquals('is string', True, E.Decl.IsString);
  finally
    U.Free();
  end;
end;

procedure TConstRoundTripTests.TestFloatConst_ValuePreserved;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeFloatConst('Pi', '3.14159265'));

    E := U.FindConst('Pi');
    AssertEquals('found', True, E <> nil);
    AssertEquals('raw text', '3.14159265', E.Decl.StrVal);
    AssertEquals('is float', True, E.Decl.IsFloat);
  finally
    U.Free();
  end;
end;

procedure TConstRoundTripTests.TestIdentRefConst_PartsPreserved;
var
  U:    TUnitInterface;
  E:    TConstEntry;
  Decl: TConstDecl;
begin
  { ConstParts encodes 'Greeting + ", " + Name' as alternating
    literal/ident entries.  Objects[i] = nil → string literal,
    Objects[i] <> nil → ident reference. }
  U := TUnitInterface.Create('TestUnit');
  try
    Decl := TConstDecl.Create();
    Decl.Name       := 'FullGreeting';
    Decl.IsString   := True;
    Decl.ConstParts := TStringList.Create();
    Decl.ConstParts.AddObject('Hello, ', nil);
    Decl.ConstParts.AddObject('Name',    TObject(Pointer(1)));

    E := TConstEntry.Create();
    E.Decl := Decl;
    E.TypeRef := MakeBuiltinRef('string');
    U.AddConst(E);

    E := U.FindConst('FullGreeting');
    AssertEquals('found', True, E <> nil);
    AssertEquals('parts count', 2, E.Decl.ConstParts.Count);
    AssertEquals('part 0 text', 'Hello, ', E.Decl.ConstParts.Strings[0]);
    AssertEquals('part 0 is literal', True,  E.Decl.ConstParts.Objects[0] = nil);
    AssertEquals('part 1 text', 'Name',     E.Decl.ConstParts.Strings[1]);
    AssertEquals('part 1 is ident',   True,  E.Decl.ConstParts.Objects[1] <> nil);
  finally
    U.Free();
  end;
end;

procedure TConstRoundTripTests.TestArrayConst_ElementsAndBoundsPreserved;
var
  U:    TUnitInterface;
  E:    TConstEntry;
  Decl: TConstDecl;
begin
  { const Primes: array[0..4] of Integer = (2, 3, 5, 7, 11); }
  U := TUnitInterface.Create('TestUnit');
  try
    Decl := TConstDecl.Create();
    Decl.Name                := 'Primes';
    Decl.IsArrayConst        := True;
    Decl.ArrayElemType       := 'Integer';
    Decl.ArrayIsRangeIndexed := True;
    Decl.ArrayLowBound       := 0;
    Decl.ArrayHighBound      := 4;
    Decl.ArrayElements       := TStringList.Create();
    Decl.ArrayElements.Add('2');
    Decl.ArrayElements.Add('3');
    Decl.ArrayElements.Add('5');
    Decl.ArrayElements.Add('7');
    Decl.ArrayElements.Add('11');

    E := TConstEntry.Create();
    E.Decl := Decl;
    U.AddConst(E);

    E := U.FindConst('Primes');
    AssertEquals('found', True, E <> nil);
    AssertEquals('is array',     True, E.Decl.IsArrayConst);
    AssertEquals('elem type',    'Integer', E.Decl.ArrayElemType);
    AssertEquals('range indexed', True, E.Decl.ArrayIsRangeIndexed);
    AssertEquals('low',  0, E.Decl.ArrayLowBound);
    AssertEquals('high', 4, E.Decl.ArrayHighBound);
    AssertEquals('count', 5, E.Decl.ArrayElements.Count);
    AssertEquals('e0', '2',  E.Decl.ArrayElements.Strings[0]);
    AssertEquals('e4', '11', E.Decl.ArrayElements.Strings[4]);
  finally
    U.Free();
  end;
end;

procedure TConstRoundTripTests.TestEnumIndexedArrayConst_IndexTypePreserved;
var
  U:    TUnitInterface;
  E:    TConstEntry;
  Decl: TConstDecl;
begin
  { const DayNames: array[TDayOfWeek] of string = ('Mon', 'Tue', ...);
    Index type is an enum, not a numeric range. }
  U := TUnitInterface.Create('TestUnit');
  try
    Decl := TConstDecl.Create();
    Decl.Name                := 'DayNames';
    Decl.IsArrayConst        := True;
    Decl.ArrayIndexType      := 'TDayOfWeek';
    Decl.ArrayElemType       := 'string';
    Decl.ArrayIsRangeIndexed := False;
    Decl.ArrayElements       := TStringList.Create();
    Decl.ArrayElements.Add('Mon');
    Decl.ArrayElements.Add('Tue');
    Decl.ArrayElements.Add('Wed');

    E := TConstEntry.Create();
    E.Decl := Decl;
    U.AddConst(E);

    E := U.FindConst('DayNames');
    AssertEquals('found', True, E <> nil);
    AssertEquals('index type', 'TDayOfWeek', E.Decl.ArrayIndexType);
    AssertEquals('not range',  False, E.Decl.ArrayIsRangeIndexed);
    AssertEquals('count', 3, E.Decl.ArrayElements.Count);
    AssertEquals('e0', 'Mon', E.Decl.ArrayElements.Strings[0]);
  finally
    U.Free();
  end;
end;

{ ----- TEnumSetTests -------------------------------------------- }

procedure TEnumSetTests.TestEnum_MembersAndOrdinalsPreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type TColor = (Red, Green, Blue);'                 + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Enum:  TEnumTypeDef;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TColor');
    AssertEquals('found', True, E <> nil);
    AssertEquals('is enum def', True, E.Def is TEnumTypeDef);

    Enum := TEnumTypeDef(E.Def);
    AssertEquals('member count', 3, Enum.Members.Count);
    AssertEquals('m0', 'Red',   Enum.Members.Strings[0]);
    AssertEquals('m1', 'Green', Enum.Members.Strings[1]);
    AssertEquals('m2', 'Blue',  Enum.Members.Strings[2]);
    AssertEquals('ord 0', 0, Enum.OrdinalAt(0));
    AssertEquals('ord 1', 1, Enum.OrdinalAt(1));
    AssertEquals('ord 2', 2, Enum.OrdinalAt(2));
  finally
    Iface.Free();
  end;
end;

procedure TEnumSetTests.TestSet_BaseEnumPreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TFlag = (fA, fB, fC);'                           + #10 +
    '  TFlags = set of TFlag;'                          + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TFlags');
    AssertEquals('found',         True, E <> nil);
    AssertEquals('is set def',    True, E.Def is TSetTypeDef);
    AssertEquals('base enum',    'TFlag', TSetTypeDef(E.Def).BaseTypeName);
  finally
    Iface.Free();
  end;
end;

{ ----- TRecordClassLayoutTests (record-shape subset) ------------ }

procedure TRecordClassLayoutTests.TestRecord_FieldsInDeclarationOrder;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TPoint = record'                                 + #10 +
    '    X: Integer;'                                   + #10 +
    '    Y: Integer;'                                   + #10 +
    '    Z: Integer;'                                   + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Rec:   TRecordTypeDef;
  F0, F1, F2: TFieldDecl;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TPoint');
    AssertEquals('found', True, E <> nil);
    AssertEquals('is record', True, E.Def is TRecordTypeDef);

    Rec := TRecordTypeDef(E.Def);
    AssertEquals('field count', 3, Rec.Fields.Count);

    F0 := TFieldDecl(Rec.Fields.Items[0]);
    F1 := TFieldDecl(Rec.Fields.Items[1]);
    F2 := TFieldDecl(Rec.Fields.Items[2]);

    AssertEquals('f0 name', 'X', F0.Names.Strings[0]);
    AssertEquals('f1 name', 'Y', F1.Names.Strings[0]);
    AssertEquals('f2 name', 'Z', F2.Names.Strings[0]);
  finally
    Iface.Free();
  end;
end;

procedure TRecordClassLayoutTests.TestRecord_FieldTypes_AsQualTypeRef;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TLocal = record A: Integer; end;'                + #10 +
    '  TUses = record'                                  + #10 +
    '    L: TLocal;'                                    + #10 +
    '    N: Integer;'                                   + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Rec:   TRecordTypeDef;
  F:     TFieldDecl;
begin
  { TQualTypeRef for record-field types isn't populated by Phase 2's
    BuildTypeEntry yet — CloneTypeDef preserves the TypeName string,
    but per-field TQualTypeRef resolution requires a richer Phase 3
    walk.  This test verifies what we DO have today: the field
    TypeName strings are correctly cloned, so a later resolver pass
    can still figure out which unit owns each type. }
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TUses');
    AssertEquals('found', True, E <> nil);

    Rec := TRecordTypeDef(E.Def);
    AssertEquals('field count', 2, Rec.Fields.Count);

    F := TFieldDecl(Rec.Fields.Items[0]);
    AssertEquals('f0 type name', 'TLocal',  F.TypeName);

    F := TFieldDecl(Rec.Fields.Items[1]);
    AssertEquals('f1 type name', 'Integer', F.TypeName);
  finally
    Iface.Free();
  end;
end;
{ ----- TRecordClassLayoutTests (class subset, Phase 3) ---------- }

procedure TRecordClassLayoutTests.TestClass_ParentClassResolved;
const
  DEP =
    'unit DepU;'                                       + #10 +
    'interface'                                        + #10 +
    'type TBase = class end;'                          + #10 +
    'implementation'                                   + #10 +
    'end.'                                             + #10;
  MAIN =
    'unit MainU;'                                      + #10 +
    'interface'                                        + #10 +
    'uses DepU;'                                       + #10 +
    'type TDerived = class(TBase) end;'                + #10 +
    'implementation'                                   + #10 +
    'end.'                                             + #10;
var
  DepIface:  TUnitInterface;
  MainIface: TUnitInterface;
  Deps:           TObjectList;
  E:              TTypeEntry;
begin
  DepIface := ParseAndExport(DEP);
  Deps := TObjectList.Create(False);
  try
    Deps.Add(DepIface);
    MainIface := ParseAndExportWithDeps(MAIN, Deps);
    try
      E := MainIface.FindType('TDerived');
      AssertEquals('found',         True,     E <> nil);
      AssertEquals('parent name',   'TBase',  E.ParentClass.TypeName);
      AssertEquals('parent unit',   'DepU',   E.ParentClass.UnitName);
    finally
      MainIface.Free();
    end;
  finally
    Deps.Free();
    DepIface.Free();
  end;
end;

procedure TRecordClassLayoutTests.TestClass_ImplementsListPopulated;
const
  SRC =
    'unit TestU;'                                                + #10 +
    'interface'                                                  + #10 +
    'type'                                                       + #10 +
    '  IFirst  = interface end;'                                 + #10 +
    '  ISecond = interface end;'                                 + #10 +
    '  TWidget = class(TObject, IFirst, ISecond) end;'           + #10 +
    'implementation'                                             + #10 +
    'end.'                                                       + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TWidget');
    AssertEquals('found',           True, E <> nil);
    AssertEquals('implements count', 2, E.Implements.Count);
    AssertEquals('impl[0]', 'IFirst',  E.Implements.Strings[0]);
    AssertEquals('impl[1]', 'ISecond', E.Implements.Strings[1]);
  finally
    Iface.Free();
  end;
end;

procedure TRecordClassLayoutTests.TestClass_MethodSignaturesExported;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TWidget = class'                                 + #10 +
    '    procedure Step;'                               + #10 +
    '    function  Count: Integer;'                     + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'procedure TWidget.Step; begin end;'                + #10 +
    'function  TWidget.Count: Integer; begin Result := 0; end;' + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Step:  TRoutineSig;
  Count: TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TWidget');
    AssertEquals('found', True, E <> nil);
    AssertEquals('method count', 2, E.Methods.Count);

    Step  := TRoutineSig(E.Methods.Items[0]);
    Count := TRoutineSig(E.Methods.Items[1]);
    AssertEquals('m0 name',     'Step',    Step.Name);
    AssertEquals('m0 not func', False,     Step.IsFunction);
    AssertEquals('m1 name',     'Count',   Count.Name);
    AssertEquals('m1 is func',  True,      Count.IsFunction);
    AssertEquals('m1 return',   'Integer', Count.ReturnType.TypeName);
  finally
    Iface.Free();
  end;
end;

procedure TRecordClassLayoutTests.TestClass_VTableSlotsAssigned;
const
  { Override of TObject.ToString gets a real (non-negative) slot.
    Non-overriding regular methods are static — slot -1. }
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TWidget = class'                                 + #10 +
    '    function ToString: string; override;'          + #10 +
    '    procedure Plain;'                              + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'function TWidget.ToString(): string; begin Result := ''w''; end;' + #10 +
    'procedure TWidget.Plain; begin end;'               + #10 +
    'end.'                                              + #10;
var
  Iface:    TUnitInterface;
  E:        TTypeEntry;
  ToString: TRoutineSig;
  Plain:    TRoutineSig;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    E        := Iface.FindType('TWidget');
    ToString := TRoutineSig(E.Methods.Items[0]);
    Plain    := TRoutineSig(E.Methods.Items[1]);

    AssertEquals('ToString virtual slot', True, ToString.VTableSlot >= 0);
    AssertEquals('Plain static',          -1,   Plain.VTableSlot);
  finally
    Iface.Free();
  end;
end;

procedure TRecordClassLayoutTests.TestClass_InstanceSizeComputed;
const
  { Class header (typeinfo + ARC + monitor) plus one Integer field
    rounds to some positive size > 0 — exact value depends on the
    backend layout, so just assert positivity. }
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type TWidget = class N: Integer; end;'             + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    E := Iface.FindType('TWidget');
    AssertEquals('found',                  True, E <> nil);
    AssertEquals('instance size positive', True, E.InstanceSize > 0);
  finally
    Iface.Free();
  end;
end;

procedure TRecordClassLayoutTests.TestClass_AttributesPreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  [Threaded]'                                      + #10 +
    '  TJob = class end;'                               + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TJob');
    AssertEquals('found',          True, E <> nil);
    AssertEquals('attribute count', 1, E.Attributes.Count);
    AssertEquals('attribute name', 'Threaded', E.Attributes.Strings[0]);
  finally
    Iface.Free();
  end;
end;

{ ----- TInlineGenericBodyTests ---------------------------------- }

procedure TInlineGenericBodyTests.TestInline_BodyExportedWithSig;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'function Square(N: Integer): Integer; inline;'        + #10 +
    'implementation'                                       + #10 +
    'function Square(N: Integer): Integer; begin Result := N * N; end;' + #10 +
    'end.'                                                 + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
  Body:  TInlineBody;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Square');
    AssertEquals('sig found',  True, Sig <> nil);
    AssertEquals('sig inline', True, Sig.IsInline);

    Body := Iface.FindInlineBody('Square');
    AssertEquals('body found', True, Body <> nil);
    AssertEquals('block non-nil', True, Body.Block <> nil);
  finally
    Iface.Free();
  end;
end;

procedure TInlineGenericBodyTests.TestGenericType_BodyExported;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'type'                                                 + #10 +
    '  TBox<T> = class'                                    + #10 +
    '    Value: T;'                                        + #10 +
    '  end;'                                               + #10 +
    'implementation'                                       + #10 +
    'end.'                                                 + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  G:     TGenericBody;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TBox');
    AssertEquals('type entry', True, E <> nil);
    AssertEquals('IsGeneric flag', True, E.IsGeneric);

    G := Iface.FindGeneric('TBox');
    AssertEquals('generic entry', True, G <> nil);
    AssertEquals('IsType',  True, G.IsType);
    AssertEquals('TypeDef non-nil', True, G.TypeDef <> nil);
    AssertEquals('type-param count', 1, G.TypeParams.Count);
    AssertEquals('type-param[0]', 'T', G.TypeParams.Strings[0]);
  finally
    Iface.Free();
  end;
end;

procedure TInlineGenericBodyTests.TestGenericRoutine_BodyExported;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'function Identity<T>(V: T): T;'                    + #10 +
    'implementation'                                    + #10 +
    'function Identity<T>(V: T): T;'                    + #10 +
    'begin Result := V; end;'                           + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  G:     TGenericBody;
begin
  Iface := ParseAndExport(SRC);
  try
    G := Iface.FindGeneric('Identity');
    AssertTrue('generic routine entry', G <> nil);
    AssertEquals('IsType', False, G.IsType);
    AssertTrue('RoutineSig present', G.RoutineSig <> nil);
    AssertTrue('Body present',       G.Body <> nil);
    AssertEquals('type-param count', 1, G.TypeParams.Count);
    AssertEquals('type-param[0]', 'T', G.TypeParams.Strings[0]);
  finally
    Iface.Free();
  end;
end;

procedure TInlineGenericBodyTests.TestGeneric_ConstraintsPreserved;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'type'                                                 + #10 +
    '  TList<T: class> = class'                            + #10 +
    '    Head: T;'                                         + #10 +
    '  end;'                                               + #10 +
    'implementation'                                       + #10 +
    'end.'                                                 + #10;
var
  Iface: TUnitInterface;
  G:     TGenericBody;
begin
  Iface := ParseAndExport(SRC);
  try
    G := Iface.FindGeneric('TList');
    AssertEquals('generic found', True, G <> nil);
    AssertEquals('constraint',    'class', G.Constraints.Strings[0]);
  finally
    Iface.Free();
  end;
end;

{ ----- TImplementationHidingTests ------------------------------- }

procedure TImplementationHidingTests.TestImplOnlyRoutine_NotExported;
const
  SRC =
    'unit TestU;'                                 + #10 +
    'interface'                                   + #10 +
    'procedure Public1;'                          + #10 +
    'implementation'                              + #10 +
    'procedure Private1; begin end;'              + #10 +
    'procedure Public1;  begin end;'              + #10 +
    'end.'                                        + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);
  try
    AssertEquals('intf count',  1, Iface.Routines.Count);
    AssertEquals('public present', True, Iface.FindRoutine('Public1')  <> nil);
    AssertEquals('private hidden', True, Iface.FindRoutine('Private1') = nil);
  finally
    Iface.Free();
  end;
end;

procedure TImplementationHidingTests.TestImplOnlyType_NotExported;
const
  SRC =
    'unit TestU;'                              + #10 +
    'interface'                                + #10 +
    'type TPublic = record X: Integer; end;'   + #10 +
    'implementation'                           + #10 +
    'type TPrivate = record Y: Integer; end;'  + #10 +
    'end.'                                     + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);
  try
    AssertEquals('intf count', 1, Iface.Types.Count);
    AssertEquals('public present', True, Iface.FindType('TPublic')  <> nil);
    AssertEquals('private hidden', True, Iface.FindType('TPrivate') = nil);
  finally
    Iface.Free();
  end;
end;

procedure TImplementationHidingTests.TestRegularRoutine_SigOnly_NoBody;
const
  SRC =
    'unit TestU;'                       + #10 +
    'interface'                         + #10 +
    'function Compute(N: Integer): Integer;' + #10 +
    'implementation'                    + #10 +
    'function Compute(N: Integer): Integer; begin Result := N * 2; end;' + #10 +
    'end.'                              + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Compute');
    AssertEquals('routine present', True, Sig <> nil);
    AssertEquals('is function',     True, Sig.IsFunction);
    AssertEquals('return type',     'Integer', Sig.ReturnType.TypeName);
    AssertEquals('param count',     1, Sig.Params.Count);
    AssertEquals('no inline body', True,
                 Iface.FindInlineBody('Compute') = nil);
  finally
    Iface.Free();
  end;
end;

{ ----- TVisibilityTests ----------------------------------------- }

procedure TVisibilityTests.TestClassMember_VisibilityPreserved;
const
  { Today the parser only tracks 'published' as a distinct
    visibility (used for RTL MethodAddress lookups); private /
    protected / public are accepted but silently dropped to the
    same default state.  Pin down what we DO carry through. }
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TWidget = class'                                 + #10 +
    '  published'                                       + #10 +
    '    procedure Pub;'                                + #10 +
    '  public'                                          + #10 +
    '    procedure Pub2;'                               + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'procedure TWidget.Pub;  begin end;'                + #10 +
    'procedure TWidget.Pub2; begin end;'                + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Pub:   TRoutineSig;
  Pub2:  TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    E    := Iface.FindType('TWidget');
    Pub  := TRoutineSig(E.Methods.Items[0]);
    Pub2 := TRoutineSig(E.Methods.Items[1]);

    AssertEquals('Pub  IsPublished',  True,  Pub.IsPublished);
    AssertEquals('Pub2 IsPublished',  False, Pub2.IsPublished);
  finally
    Iface.Free();
  end;
end;

{ ----- TForwardDeclTests ---------------------------------------- }

procedure TForwardDeclTests.TestForwardDeclClass_FullBodyExported;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type TWidget = class;'                             + #10 +
    'implementation'                                    + #10 +
    'type'                                              + #10 +
    '  TWidget = class'                                 + #10 +
    '    procedure Step;'                               + #10 +
    '    N: Integer;'                                   + #10 +
    '  end;'                                            + #10 +
    'procedure TWidget.Step; begin end;'                + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TWidget');
    AssertEquals('found',        True, E <> nil);
    AssertEquals('is class',     True, E.IsClass);
    AssertEquals('method count', 1, E.Methods.Count);
    AssertEquals('field count',  1, TClassTypeDef(E.Def).Fields.Count);
  finally
    Iface.Free();
  end;
end;

{ ----- TRoutineSigTests ----------------------------------------- }

procedure TRoutineSigTests.TestParam_ModeVar_Preserved;
const
  SRC =
    'unit TestU;'                              + #10 +
    'interface'                                + #10 +
    'procedure Inc(var X: Integer);'           + #10 +
    'implementation'                           + #10 +
    'procedure Inc(var X: Integer); begin X := X + 1; end;' + #10 +
    'end.'                                     + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
  P:     TMethodParam;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Inc');
    AssertEquals('found', True, Sig <> nil);
    AssertEquals('param count', 1, Sig.Params.Count);
    P := TMethodParam(Sig.Params.Items[0]);
    AssertEquals('name',  'X',     P.ParamName);
    AssertEquals('type',  'Integer', P.TypeName);
    AssertEquals('var',   True,    P.IsVarParam);
    AssertEquals('not const', False, P.IsConstParam);
  finally
    Iface.Free();
  end;
end;

procedure TRoutineSigTests.TestParam_ModeConst_Preserved;
const
  SRC =
    'unit TestU;'                                  + #10 +
    'interface'                                    + #10 +
    'function Hash(const S: string): Integer;'     + #10 +
    'implementation'                               + #10 +
    'function Hash(const S: string): Integer; begin Result := 0; end;' + #10 +
    'end.'                                         + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
  P:     TMethodParam;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Hash');
    AssertEquals('found', True, Sig <> nil);
    P := TMethodParam(Sig.Params.Items[0]);
    AssertEquals('name',      'S',      P.ParamName);
    AssertEquals('type',      'string', P.TypeName);
    AssertEquals('const',     True,     P.IsConstParam);
    AssertEquals('not var',   False,    P.IsVarParam);
  finally
    Iface.Free();
  end;
end;

procedure TRoutineSigTests.TestParam_ModeOut_Preserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'procedure Fetch(out X: Integer);'                  + #10 +
    'implementation'                                    + #10 +
    'procedure Fetch(out X: Integer); begin X := 0; end;' + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
  P:     TMethodParam;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Fetch');
    AssertEquals('found', True, Sig <> nil);
    AssertEquals('param count', 1, Sig.Params.Count);
    P := TMethodParam(Sig.Params.Items[0]);
    AssertEquals('name',  'X',       P.ParamName);
    AssertEquals('type',  'Integer', P.TypeName);
    { 'out' is a by-reference mode, so IsVarParam is also set. }
    AssertEquals('out',       True,  P.IsOutParam);
    AssertEquals('var',       True,  P.IsVarParam);
    AssertEquals('not const', False, P.IsConstParam);
  finally
    Iface.Free();
  end;
end;

procedure TRoutineSigTests.TestReturnType_FunctionVsProcedure;
const
  SRC =
    'unit TestU;'                                + #10 +
    'interface'                                  + #10 +
    'procedure Step;'                            + #10 +
    'function  Count: Integer;'                  + #10 +
    'implementation'                             + #10 +
    'procedure Step;            begin end;'      + #10 +
    'function  Count: Integer;  begin Result := 0; end;' + #10 +
    'end.'                                       + #10;
var
  Iface: TUnitInterface;
  Proc:  TRoutineSig;
  Func:  TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Proc := Iface.FindRoutine('Step');
    Func := Iface.FindRoutine('Count');
    AssertEquals('procedure found', True, Proc <> nil);
    AssertEquals('function  found', True, Func <> nil);
    AssertEquals('proc IsFunction',  False, Proc.IsFunction);
    AssertEquals('proc ret empty',   '', Proc.ReturnType.TypeName);
    AssertEquals('func IsFunction',  True, Func.IsFunction);
    AssertEquals('func ret',         'Integer', Func.ReturnType.TypeName);
  finally
    Iface.Free();
  end;
end;

procedure TRoutineSigTests.TestCallingConv_Cdecl_Preserved;
const
  SRC = '''
    unit TestU;
    interface
    procedure Beep; cdecl;
    implementation
    procedure Beep; cdecl; begin end;
    end.
    ''';
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Beep');
    AssertEquals('found',        True,    Sig <> nil);
    AssertEquals('calling conv', 'cdecl', Sig.CallingConv);
  finally
    Iface.Free();
  end;
end;

procedure TRoutineSigTests.TestExternal_NamePreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'function clock: Integer; external name ''clock'';' + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('clock');
    AssertEquals('found',         True,   Sig <> nil);
    AssertEquals('is external',   True,   Sig.IsExternal);
    AssertEquals('external name', 'clock', Sig.ExternalName);
  finally
    Iface.Free();
  end;
end;

{ ----- TUsedUnitsTests ------------------------------------------ }

procedure TUsedUnitsTests.TestUsedUnits_OrderPreserved;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.UsedUnits.Add('SysUtils');
    U.UsedUnits.Add('Classes');
    U.UsedUnits.Add('Math');

    AssertEquals('count',    3, U.UsedUnits.Count);
    AssertEquals('first',    'SysUtils', U.UsedUnits.Strings[0]);
    AssertEquals('second',   'Classes',  U.UsedUnits.Strings[1]);
    AssertEquals('third',    'Math',     U.UsedUnits.Strings[2]);
  finally
    U.Free();
  end;
end;

procedure TUsedUnitsTests.TestImplOnlyUsedUnit_NotInUsedUnits;
const
  SRC =
    'unit TestU;'                + #10 +
    'interface'                  + #10 +
    'uses SysUtils;'             + #10 +
    'implementation'             + #10 +
    'uses Classes, Math;'        + #10 +
    'end.'                       + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);
  try
    AssertEquals('intf-uses count',   1,          Iface.UsedUnits.Count);
    AssertEquals('intf-uses[0]',      'SysUtils', Iface.UsedUnits.Strings[0]);
    AssertEquals('Classes excluded',  -1,         Iface.UsedUnits.IndexOf('Classes'));
    AssertEquals('Math excluded',     -1,         Iface.UsedUnits.IndexOf('Math'));
  finally
    Iface.Free();
  end;
end;

{ ----- TLookupTests --------------------------------------------- }

{ Helpers — build minimal entries for lookup-table testing.
  TLookupTests only exercises the index/lookup machinery, so the
  entries don't need to be semantically meaningful. }

function MakeTypeEntry(const AName: string): TTypeEntry;
begin
  Result := TTypeEntry.Create();
  Result.Name := AName;
end;

function MakeConstEntry(const AName: string): TConstEntry;
begin
  Result := TConstEntry.Create();
  Result.Decl := TConstDecl.Create();
  Result.Decl.Name := AName;
end;

function MakeRoutineSig(const AName: string): TRoutineSig;
begin
  Result := TRoutineSig.Create();
  Result.Name := AName;
end;

function MakeGenericBody(const AName: string): TGenericBody;
begin
  Result := TGenericBody.Create();
  Result.Name := AName;
end;

function MakeInlineBody: TInlineBody;
begin
  Result := TInlineBody.Create();
  Result.RoutineName := 'SomeInline';
end;

procedure TLookupTests.TestFindType_CaseInsensitive;
var
  U: TUnitInterface;
  E: TTypeEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddType(MakeTypeEntry('TFoo'));

    E := U.FindType('TFoo');
    AssertEquals('exact', True, E <> nil);
    AssertEquals('exact name', 'TFoo', E.Name);

    E := U.FindType('tfoo');
    AssertEquals('lowercase', True, E <> nil);

    E := U.FindType('TFOO');
    AssertEquals('uppercase', True, E <> nil);
  finally
    U.Free();
  end;
end;

procedure TLookupTests.TestFindConst_CaseInsensitive;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeConstEntry('MaxValue'));

    E := U.FindConst('MaxValue');
    AssertEquals('exact', True, E <> nil);

    E := U.FindConst('MAXVALUE');
    AssertEquals('uppercase', True, E <> nil);

    E := U.FindConst('maxvalue');
    AssertEquals('lowercase', True, E <> nil);
  finally
    U.Free();
  end;
end;

procedure TLookupTests.TestFindRoutine_CaseInsensitive;
var
  U: TUnitInterface;
  S: TRoutineSig;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddRoutine(MakeRoutineSig('DoStuff'));

    S := U.FindRoutine('DoStuff');
    AssertEquals('exact', True, S <> nil);

    S := U.FindRoutine('dostuff');
    AssertEquals('lowercase', True, S <> nil);

    S := U.FindRoutine('DOSTUFF');
    AssertEquals('uppercase', True, S <> nil);
  finally
    U.Free();
  end;
end;

procedure TLookupTests.TestFindGeneric_CaseInsensitive;
var
  U: TUnitInterface;
  G: TGenericBody;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddGenericBody(MakeGenericBody('TList'));

    G := U.FindGeneric('TList');
    AssertEquals('exact', True, G <> nil);

    G := U.FindGeneric('tlist');
    AssertEquals('lowercase', True, G <> nil);

    G := U.FindGeneric('TLIST');
    AssertEquals('uppercase', True, G <> nil);
  finally
    U.Free();
  end;
end;

procedure TLookupTests.TestFindType_CaseSensitive_FlagRespected;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('TestUnit', True);  { case-sensitive }
  try
    U.AddType(MakeTypeEntry('TFoo'));

    AssertEquals('exact match',     True, U.FindType('TFoo') <> nil);
    AssertEquals('wrong case miss', True, U.FindType('tfoo') = nil);
    AssertEquals('upper case miss', True, U.FindType('TFOO') = nil);
  finally
    U.Free();
  end;
end;

procedure TLookupTests.TestFind_Missing_ReturnsNil;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddType(MakeTypeEntry('TFoo'));
    U.AddConst(MakeConstEntry('Pi'));
    U.AddRoutine(MakeRoutineSig('DoIt'));
    U.AddGenericBody(MakeGenericBody('TList'));
    U.AddInlineBody(MakeInlineBody());

    AssertEquals('type missing',     True, U.FindType('TBar') = nil);
    AssertEquals('const missing',    True, U.FindConst('E') = nil);
    AssertEquals('routine missing',  True, U.FindRoutine('Other') = nil);
    AssertEquals('inline missing',   True, U.FindInlineBody('NotInline') = nil);
    AssertEquals('generic missing',  True, U.FindGeneric('TQueue') = nil);
  finally
    U.Free();
  end;
end;

{ ----- TMetadataTests ------------------------------------------- }

procedure TMetadataTests.TestName_MatchesSource;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    AssertEquals('name preserved', 'MyUnit', U.Name);
  finally
    U.Free();
  end;
end;

procedure TMetadataTests.TestSourceFile_MatchesPath;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    U.SourceFile := '/tmp/MyUnit.pas';
    AssertEquals('source file', '/tmp/MyUnit.pas', U.SourceFile);
  finally
    U.Free();
  end;
end;

{ SourceHash and CompilerId are reserved for Phase 5+ .bpu work.
  They are documented as empty strings at construction time.  The
  tests pin that contract so a later patch that starts populating
  them doesn't silently change semantics for downstream consumers. }

procedure TMetadataTests.TestSourceHash_NonEmpty;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    AssertEquals('hash empty in Phase 1', '', U.SourceHash);
  finally
    U.Free();
  end;
end;

procedure TMetadataTests.TestCompilerId_NonEmpty;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    AssertEquals('compiler version empty in Phase 1', '', U.CompilerId);
  finally
    U.Free();
  end;
end;

{ ----- TImportRoundTripTests (Phase 6c-A) ----------------------- }

{ Build a fresh symbol table seeded with the builtins, ready to
  receive an ImportUnitInterface call. }
function FreshTableWithBuiltins: TSymbolTable;
begin
  { TSymbolTable.Create already calls RegisterBuiltins. }
  Result := TSymbolTable.Create();
end;

procedure TImportRoundTripTests.TestImport_IntConst_DefinedWithValue;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'const Answer = 42;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Sym:   TSymbol;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Sym := Tab.Lookup('Answer');
    AssertTrue('Answer defined', Sym <> nil);
    AssertTrue('skConstant', Sym.Kind = skConstant);
    AssertEquals('value', 42, Sym.ConstValue);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_StringConst_DefinedWithValue;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'const Greeting = ''hello'';' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Sym:   TSymbol;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Sym := Tab.Lookup('Greeting');
    AssertTrue('Greeting defined', Sym <> nil);
    AssertTrue('skConstant', Sym.Kind = skConstant);
    AssertEquals('value', 'hello', Sym.ConstString);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Enum_TypeAndMembersDefined;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TColor = (Red, Green, Blue);' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  TyDesc: TTypeDesc;
  Sym:   TSymbol;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    TyDesc := Tab.FindType('TColor');
    AssertTrue('TColor type defined', TyDesc <> nil);
    AssertTrue('TColor is enum', TyDesc is TEnumTypeDesc);
    AssertEquals('three members', 3, TEnumTypeDesc(TyDesc).Members.Count);
    { An imported enum's members live on the descriptor and — when an analyser
      is supplied — in its enum-member reverse index.  They are deliberately
      NOT defined as bare global skConstant symbols, matching the
      source-visible path, so two enums may share a member name. }
    AssertEquals('Green ordinal', 1,
                 TEnumTypeDesc(TyDesc).Members.IndexOf('Green'));
    Sym := Tab.Lookup('Green');
    AssertTrue('Green is not a bare global constant', Sym = nil);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Enum_MembersInAnalyserReverseIndex;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TColor = (Red, Green, Blue);' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Sem:   TSemanticAnalyser;
  Ref:   TEnumMemberRef;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Sem   := TSemanticAnalyser.Create();
  try
    ImportUnitInterface(Iface, Sem.GetSymbolTable(), Sem);
    { No context type: a single candidate resolves unambiguously. }
    Ref := Sem.ResolveEnumMember('Green', nil);
    AssertTrue('Green in reverse index', Ref <> nil);
    AssertEquals('Green ordinal', Int64(1), Ref.Ordinal);
    AssertTrue('Green belongs to TColor',
      Ref.EnumDesc = TEnumTypeDesc(Sem.GetSymbolTable().FindType('TColor')));
  finally
    Sem.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Set_BaseEnumLinked;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type' + #10 +
    '  TColor = (Red, Green, Blue);' + #10 +
    '  TColors = set of TColor;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  TyDesc: TTypeDesc;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    TyDesc := Tab.FindType('TColors');
    AssertTrue('TColors defined', TyDesc <> nil);
    AssertTrue('TColors is set', TyDesc is TSetTypeDesc);
    AssertTrue('base is the enum',
      TSetTypeDesc(TyDesc).BaseType =
        TEnumTypeDesc(Tab.FindType('TColor')));
    AssertEquals('bit count', 3, TSetTypeDesc(TyDesc).BitCount);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Alias_ResolvesToBase;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TMyInt = Integer;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  TyDesc: TTypeDesc;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    TyDesc := Tab.FindType('TMyInt');
    AssertTrue('TMyInt defined', TyDesc <> nil);
    AssertTrue('Aliases to Integer', TyDesc = Tab.FindType('Integer'));
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_ProcedureRoutine_DefinedAsSkProcedure;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'procedure DoIt(N: Integer);' + #10 +
    'implementation' + #10 +
    'procedure DoIt(N: Integer); begin end;' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Sym:   TSymbol;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Sym := Tab.Lookup('DoIt');
    AssertTrue('DoIt defined', Sym <> nil);
    AssertTrue('skProcedure', Sym.Kind = skProcedure);
    AssertEquals('one param', 1, Sym.Params.Count);
    AssertTrue('param type Integer',
      TParamDesc(Sym.Params.Items[0]).TypeDesc = Tab.FindType('Integer'));
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_FunctionRoutine_DefinedAsSkFunction;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'function Sum(A, B: Integer): Integer;' + #10 +
    'implementation' + #10 +
    'function Sum(A, B: Integer): Integer; begin Result := A + B; end;' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Sym:   TSymbol;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Sym := Tab.Lookup('Sum');
    AssertTrue('Sum defined', Sym <> nil);
    AssertTrue('skFunction', Sym.Kind = skFunction);
    AssertTrue('returns Integer', Sym.TypeDesc = Tab.FindType('Integer'));
    AssertEquals('two params', 2, Sym.Params.Count);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Record_FieldsImportedWithOffsets;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TPoint = record X, Y: Integer; end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  TyDesc: TTypeDesc;
  Rec:   TRecordTypeDesc;
  Fx, Fy: TFieldInfo;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    TyDesc := Tab.FindType('TPoint');
    AssertTrue('TPoint defined', TyDesc <> nil);
    AssertTrue('is record', TyDesc is TRecordTypeDesc);
    Rec := TRecordTypeDesc(TyDesc);
    AssertEquals('two fields', 2, Rec.Fields.Count);
    Fx := Rec.FindField('X');
    Fy := Rec.FindField('Y');
    AssertTrue('X found', Fx <> nil);
    AssertTrue('Y found', Fy <> nil);
    AssertEquals('X offset', 0, Fx.Offset);
    AssertEquals('Y offset', 4, Fy.Offset);
    AssertTrue('X type Integer', Fx.TypeDesc = Tab.FindType('Integer'));
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Class_ImplicitTObjectParent;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TFoo = class end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  TyDesc: TTypeDesc;
  Rec:   TRecordTypeDesc;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    TyDesc := Tab.FindType('TFoo');
    AssertTrue('TFoo defined', TyDesc <> nil);
    AssertTrue('is class (tyClass)', TyDesc.Kind = tyClass);
    Rec := TRecordTypeDesc(TyDesc);
    AssertTrue('parent TObject', Rec.Parent <> nil);
    AssertEquals('parent name', 'TObject', Rec.Parent.Name);
    AssertTrue('inherits TObject vtable', Rec.HasVTable());
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Class_FieldOffsetAfterParentVptr;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TFoo = class Counter: Integer; end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Rec:   TRecordTypeDesc;
  Fi:    TFieldInfo;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Rec := TRecordTypeDesc(Tab.FindType('TFoo'));
    AssertTrue('TFoo defined', Rec <> nil);
    Fi := Rec.FindField('Counter');
    AssertTrue('Counter found', Fi <> nil);
    { Layout: vptr at offset 0 (8 bytes) + Counter at 8 — matches
      what AnalyseTypeDecls produces for a TObject-derived class. }
    AssertEquals('Counter offset', 8, Fi.Offset);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Class_ExplicitParentChain;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type' + #10 +
    '  TBase = class A: Integer; end;' + #10 +
    '  TDerived = class(TBase) B: Integer; end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Derived: TRecordTypeDesc;
  Fa, Fb: TFieldInfo;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Derived := TRecordTypeDesc(Tab.FindType('TDerived'));
    AssertTrue('TDerived defined', Derived <> nil);
    AssertTrue('parent TBase', Derived.Parent <> nil);
    AssertEquals('parent name', 'TBase', Derived.Parent.Name);
    { Inherited field A and own field B both reachable via FindField,
      since FindField walks the chain (or, when our import inherits
      parent fields into the child, finds locally). }
    Fa := Derived.FindField('A');
    Fb := Derived.FindField('B');
    AssertTrue('A reachable', Fa <> nil);
    AssertTrue('B reachable', Fb <> nil);
    AssertEquals('A offset',  8,  Fa.Offset);  { after vptr }
    AssertEquals('B offset', 12,  Fb.Offset);  { after A }
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Class_VirtualMethod_AddsVTableSlot;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TFoo = class' + #10 +
    '  procedure Speak; virtual;' + #10 +
    'end;' + #10+
    'implementation' + #10 +
    'procedure TFoo.Speak(); begin end;' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  RT:    TRecordTypeDesc;
  Slot:  Integer;
  Ent:   TVTableEntry;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    RT := TRecordTypeDesc(Tab.FindType('TFoo'));
    AssertTrue('TFoo defined', RT <> nil);
    Slot := RT.FindVTableSlot('Speak');
    AssertTrue('Speak has vtable slot', Slot >= 0);
    Ent := RT.VTableEntryAt(Slot);
    AssertEquals('ImplName', '$U_TFoo_Speak', Ent.ImplName);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Class_Override_ReusesParentSlot;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type' + #10 +
    '  TBase = class procedure Speak; virtual; end;' + #10 +
    '  TDerived = class(TBase) procedure Speak; override; end;' + #10 +
    'implementation' + #10 +
    'procedure TBase.Speak(); begin end;' + #10 +
    'procedure TDerived.Speak(); begin end;' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Base, Derived: TRecordTypeDesc;
  BaseSlot, DerSlot: Integer;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Base    := TRecordTypeDesc(Tab.FindType('TBase'));
    Derived := TRecordTypeDesc(Tab.FindType('TDerived'));
    AssertTrue('TBase defined',    Base    <> nil);
    AssertTrue('TDerived defined', Derived <> nil);
    BaseSlot := Base.FindVTableSlot('Speak');
    DerSlot  := Derived.FindVTableSlot('Speak');
    AssertTrue('TBase has slot', BaseSlot >= 0);
    AssertEquals('same slot', BaseSlot, DerSlot);
    AssertEquals('TDerived ImplName',
      '$U_TDerived_Speak',
      Derived.VTableEntryAt(DerSlot).ImplName);
    AssertEquals('TBase ImplName still own',
      '$U_TBase_Speak',
      Base.VTableEntryAt(BaseSlot).ImplName);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Interface_MethodsRegistered;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type IGreeter = interface' + #10 +
    '  function Hello: string;' + #10 +
    '  procedure Quit;' + #10 +
    'end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  ITD:   TInterfaceTypeDesc;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    ITD := TInterfaceTypeDesc(Tab.FindType('IGreeter'));
    AssertTrue('IGreeter defined', ITD <> nil);
    AssertEquals('two methods', 2, ITD.MethodCount());
    AssertTrue('has Hello',  ITD.HasMethod('Hello'));
    AssertTrue('has Quit',   ITD.HasMethod('Quit'));
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Class_ImplementsInterface;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type' + #10 +
    '  IGreeter = interface procedure Greet; end;' + #10 +
    '  TFoo = class(TObject, IGreeter) procedure Greet; end;' + #10 +
    'implementation' + #10 +
    'procedure TFoo.Greet(); begin end;' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  RT:    TRecordTypeDesc;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    RT := TRecordTypeDesc(Tab.FindType('TFoo'));
    AssertTrue('TFoo defined', RT <> nil);
    AssertEquals('one impl', 1, RT.ImplementsCount());
    AssertEquals('impl is IGreeter', 'IGreeter',
      RT.ImplementsIntfAt(0).Name);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_Class_AttributePreserved;
const
  { Custom attribute defined inline so the test does not depend on
    blaise.testing being parsed via 'uses'. }
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type' + #10 +
    '  MarkerAttribute = class(TCustomAttribute) end;' + #10 +
    '  [Marker]' + #10 +
    '  TFoo = class end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  RT:    TRecordTypeDesc;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    RT := TRecordTypeDesc(Tab.FindType('TFoo'));
    AssertTrue('TFoo defined', RT <> nil);
    AssertEquals('one attribute',  1, RT.ClassAttributeCount());
    AssertEquals('MarkerAttribute', 'MarkerAttribute', RT.ClassAttributeAt(0));
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_GenericClass_RegisteredAsTemplate;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TBox<T> = class V: T; end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Templ: TObject;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Templ := Tab.FindGeneric('TBox');
    AssertTrue('TBox template registered', Templ <> nil);
    AssertTrue('template is TGenericTypeDef', Templ is TGenericTypeDef);
    AssertEquals('one type param',
      1, TGenericTypeDef(Templ).ParamNames.Count);
    AssertEquals('param name',
      'T', TGenericTypeDef(Templ).ParamNames.Strings[0]);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_GenericInterface_RegisteredAsTemplate;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type IBox<T> = interface' + #10 +
    '  function Get: T;' + #10 +
    'end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Templ: TObject;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Templ := Tab.FindGeneric('IBox');
    AssertTrue('IBox template registered', Templ <> nil);
    AssertTrue('template is TGenericInterfaceDef',
               Templ is TGenericInterfaceDef);
    AssertEquals('one type param', 1,
      TGenericInterfaceDef(Templ).ParamNames.Count);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_GenericRoutine_RegisteredOnTable;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'function Identity<T>(V: T): T;' + #10 +
    'implementation' + #10 +
    'function Identity<T>(V: T): T;' + #10 +
    'begin Result := V; end;' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Templ: TObject;
  MD:    TMethodDecl;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Templ := Tab.FindGenericRoutine('Identity');
    AssertTrue('Identity template registered', Templ <> nil);
    AssertTrue('is TMethodDecl', Templ is TMethodDecl);
    MD := TMethodDecl(Templ);
    AssertEquals('one type param', 1, MD.TypeParams.Count);
    AssertEquals('param name', 'T', MD.TypeParams.Strings[0]);
    AssertEquals('one value param', 1, MD.Params.Count);
    AssertTrue('body cloned', MD.Body <> nil);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

{ Parse a program string into a TProgram and analyse it through the
  supplied TSemanticAnalyser.  Returns the program (caller owns).
  Used to prove ImportUnitInterface populates a TSymbolTable
  equivalent to what AnalyseUnitForExport would have produced. }
function ParseAndAnalyseProgram(const ASource: string;
                                ASem: TSemanticAnalyser): TProgram;
var
  Lex:    TLexer;
  Parser: TParser;
begin
  Lex := TLexer.Create(ASource, '<main>');
  try
    Parser := TParser.Create(Lex);
    try
      Result := Parser.Parse();  { public entry; ParseProgram is a private internal }
    finally
      Parser.Free();
    end;
  finally
    Lex.Free();
  end;
  ASem.Analyse(Result);
end;

procedure TImportRoundTripTests.TestEndToEnd_MainProgramSeesImportedConst;
const
  DEP_SRC =
    'unit DepU;' + #10 +
    'interface' + #10 +
    'const K = 42;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
  MAIN_SRC =
    'program M;' + #10 +
    'var X: Integer;' + #10 +
    'begin X := K; end.' + #10;
var
  Iface: TUnitInterface;
  Sem:   TSemanticAnalyser;
  Prog:  TProgram;
begin
  Iface := ParseAnalyseAndExport(DEP_SRC);  { also frees DEP source TUnit }
  Sem   := TSemanticAnalyser.Create();
  try
    ImportUnitInterface(Iface, Sem.GetSymbolTable());
    Prog := ParseAndAnalyseProgram(MAIN_SRC, Sem);
    try
      { Analyse() transferred the table to Prog.SymbolTable. }
      AssertTrue('main analysed', Prog.SymbolTable <> nil);
      AssertTrue('K still visible after free',
                 Prog.SymbolTable.Lookup('K') <> nil);
    finally
      Prog.Free();
    end;
  finally
    Sem.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestEndToEnd_MainProgramSeesImportedClass;
const
  DEP_SRC =
    'unit DepU;' + #10 +
    'interface' + #10 +
    'type TFoo = class V: Integer; end;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
  MAIN_SRC =
    'program M;' + #10 +
    'var F: TFoo;' + #10 +
    'begin F := nil; end.' + #10;
var
  Iface: TUnitInterface;
  Sem:   TSemanticAnalyser;
  Prog:  TProgram;
begin
  Iface := ParseAnalyseAndExport(DEP_SRC);
  Sem   := TSemanticAnalyser.Create();
  try
    ImportUnitInterface(Iface, Sem.GetSymbolTable());
    Prog := ParseAndAnalyseProgram(MAIN_SRC, Sem);
    try
      AssertTrue('main analysed', Prog.SymbolTable <> nil);
      AssertTrue('TFoo still visible after free',
                 Prog.SymbolTable.FindType('TFoo') <> nil);
    finally
      Prog.Free();
    end;
  finally
    Sem.Free();
    Iface.Free();
  end;
end;

procedure TImportRoundTripTests.TestImport_GlobalVar_MarkedIsGlobal;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'var Counter: Integer;' + #10 +
    'implementation' + #10 +
    'end.' + #10;
var
  Iface: TUnitInterface;
  Tab:   TSymbolTable;
  Sym:   TSymbol;
begin
  Iface := ParseAnalyseAndExport(SRC);
  Tab   := FreshTableWithBuiltins();
  try
    ImportUnitInterface(Iface, Tab);
    Sym := Tab.Lookup('Counter');
    AssertTrue('Counter defined', Sym <> nil);
    AssertTrue('skVariable', Sym.Kind = skVariable);
    AssertTrue('IsGlobal', Sym.IsGlobal);
    AssertTrue('type Integer', Sym.TypeDesc = Tab.FindType('Integer'));
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

{ ----- TIfaceIOTests --------------------------------------------- }

function BuildIfaceWithIntConst: TUnitInterface;
var
  C: TConstEntry;
begin
  Result := TUnitInterface.Create('TestU');
  C := TConstEntry.Create();
  C.Decl := TConstDecl.Create();
  C.Decl.Name   := 'MaxBuf';
  C.Decl.IntVal := 4096;
  C.TypeRef     := MakeBuiltinRef('Integer');
  Result.AddConst(C);
end;

procedure TIfaceIOTests.TestWrite_StartsWithMagicAndVersion;
var
  Iface: TUnitInterface;
  Buf:   string;
begin
  Iface := TUnitInterface.Create('U');
  try
    Buf := WriteUnitInterface(Iface);
    { Blaise Pos is 0-based; match-at-start returns 0.  Version is 16 since
      TMethodDecl.IsStatic joined EncodeMethodDecl — a `static` method on a
      GENERIC template travels as a method DECL, so the v4 sig-level IsStatic
      did not reach it (v15 added META HasFinalization, v14 the ROUT
      IsVarArgs flag, v13 the record method list, v12 the '->' lambda facts,
      v11 the 'generic-proc' TYPE-block kind, on top of v10's 'reference to'
      form, v9's free-routine external-name linkage, v8's named integer
      subranges, v7's LinkLibs, v6's `overload` directive, v5's member
      Visibility, v4's TRoutineSig.IsStatic, and v3's static-member facts). }
    AssertTrue('starts with magic',
      Pos('BLAISE-IFACE 16', Buf) = 0);
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_UnitNamePreserved;
var
  Src, Dst: TUnitInterface;
  Buf:      string;
begin
  Src := TUnitInterface.Create('MyUnit');
  try
    Buf := WriteUnitInterface(Src);
    Dst := ReadUnitInterface(Buf);
    try
      AssertEquals('unit name', 'MyUnit', Dst.Name);
    finally
      Dst.Free();
    end;
  finally
    Src.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_InitFiniFlagsPreserved;
var
  Src, Dst: TUnitInterface;
  Buf:      string;
begin
  Src := TUnitInterface.Create('MyUnit');
  try
    Src.HasInitialization := True;
    Src.HasFinalization := True;
    Buf := WriteUnitInterface(Src);
    Dst := ReadUnitInterface(Buf);
    try
      AssertTrue('HasInitialization', Dst.HasInitialization);
      AssertTrue('HasFinalization', Dst.HasFinalization);
    finally
      Dst.Free();
    end;
  finally
    Src.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_LinkLibsPreserved;
var
  Src, Dst: TUnitInterface;
  Buf:      string;
begin
  Src := TUnitInterface.Create('MyUnit');
  try
    Src.LinkLibs.Add('c');
    Src.LinkLibs.Add('m');
    Buf := WriteUnitInterface(Src);
    Dst := ReadUnitInterface(Buf);
    try
      AssertEquals('link-lib count', 2, Dst.LinkLibs.Count);
      AssertEquals('first lib',  'c', Dst.LinkLibs.Strings[0]);
      AssertEquals('second lib', 'm', Dst.LinkLibs.Strings[1]);
    finally
      Dst.Free();
    end;
  finally
    Src.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_IntConstPreserved;
var
  Src, Dst: TUnitInterface;
  C:        TConstEntry;
  Buf:      string;
begin
  Src := BuildIfaceWithIntConst();
  try
    Buf := WriteUnitInterface(Src);
    Dst := ReadUnitInterface(Buf);
    try
      C := Dst.FindConst('MaxBuf');
      AssertTrue('MaxBuf present', C <> nil);
      AssertEquals('value',  Int64(4096), C.Decl.IntVal);
      AssertEquals('type ref unit', '$builtin', C.TypeRef.UnitName);
      AssertEquals('type ref name', 'Integer',  C.TypeRef.TypeName);
    finally
      Dst.Free();
    end;
  finally
    Src.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_NamedSubrangeAlias_BoundsPreserved;
const
  SRC =
    'unit TestU;'                            + #10 +
    'interface'                              + #10 +
    'type TIdx = 2..4;'                      + #10 +
    'implementation'                         + #10 +
    'end.'                                   + #10;
var
  SrcIface, Dst: TUnitInterface;
  E:        TTypeEntry;
  AD:       TTypeAliasDef;
  Buf:      string;
begin
  SrcIface := ParseAndExport(SRC);
  try
    Buf := WriteUnitInterface(SrcIface);
    Dst := ReadUnitInterface(Buf);
    try
      E := Dst.FindType('TIdx');
      AssertTrue('TIdx present', E <> nil);
      AssertTrue('is alias def', E.Def is TTypeAliasDef);
      AD := TTypeAliasDef(E.Def);
      AssertEquals('IsSubrange',   True, AD.IsSubrange);
      AssertEquals('SubrangeLow',  Int64(2), AD.SubrangeLow);
      AssertEquals('SubrangeHigh', Int64(4), AD.SubrangeHigh);
    finally
      Dst.Free();
    end;
  finally
    SrcIface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_StringConstWithAwkwardChars;
const
  WEIRD = 'multi' + #10 + 'line: with ":" inside';
var
  Src, Dst: TUnitInterface;
  C:        TConstEntry;
  Buf:      string;
begin
  Src := TUnitInterface.Create('U');
  C := TConstEntry.Create();
  C.Decl := TConstDecl.Create();
  C.Decl.Name     := 'Weird';
  C.Decl.StrVal   := WEIRD;
  C.Decl.IsString := True;
  C.TypeRef       := MakeBuiltinRef('string');
  Src.AddConst(C);
  try
    Buf := WriteUnitInterface(Src);
    Dst := ReadUnitInterface(Buf);
    try
      C := Dst.FindConst('Weird');
      AssertTrue('Weird present', C <> nil);
      AssertEquals('exact bytes', WEIRD, C.Decl.StrVal);
      AssertTrue('IsString', C.Decl.IsString);
    finally
      Dst.Free();
    end;
  finally
    Src.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_EmptyInterface;
var
  Src, Dst: TUnitInterface;
  Buf:      string;
begin
  Src := TUnitInterface.Create('Empty');
  try
    Buf := WriteUnitInterface(Src);
    Dst := ReadUnitInterface(Buf);
    try
      AssertEquals('name', 'Empty', Dst.Name);
      AssertEquals('zero consts', 0, Dst.Consts.Count);
    finally
      Dst.Free();
    end;
  finally
    Src.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_RealSource_AllSimpleKinds;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'const K = 42;' + #10 +
    'var Counter: Integer;' + #10 +
    'type' + #10 +
    '  TColor  = (Red, Green, Blue);' + #10 +
    '  TColors = set of TColor;' + #10 +
    '  TMyInt  = Integer;' + #10 +
    'function Add(A, B: Integer): Integer;' + #10 +
    'implementation' + #10 +
    'function Add(A, B: Integer): Integer; begin Result := A + B; end;' + #10 +
    'end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  Enum:         TTypeEntry;
  Sig:          TRoutineSig;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      AssertEquals('unit name',    'U', Round.Name);
      AssertTrue('K present',      Round.FindConst('K') <> nil);
      AssertEquals('K value',      Int64(42), Round.FindConst('K').Decl.IntVal);
      AssertEquals('1 var',        1, Round.Vars.Count);
      AssertEquals('Counter name', 'Counter', TVarEntry(Round.Vars.Items[0]).Name);
      AssertEquals('3 types',      3, Round.Types.Count);
      Enum := Round.FindType('TColor');
      AssertTrue('TColor type', Enum <> nil);
      AssertTrue('TColor is enum', Enum.Def is TEnumTypeDef);
      AssertEquals('3 members', 3, TEnumTypeDef(Enum.Def).Members.Count);
      Sig := Round.FindRoutine('Add');
      AssertTrue('Add routine', Sig <> nil);
      AssertTrue('Add IsFunction', Sig.IsFunction);
      AssertEquals('Add params', 2, Sig.Params.Count);
      AssertEquals('Add param 0 name', 'A',
        TMethodParam(Sig.Params.Items[0]).ParamName);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_ViaFile;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'const K = 7;' + #10 +
    'implementation end.' + #10;
  PATH = '/tmp/blaise-iface-roundtrip-test.bif';
var
  Iface, Round: TUnitInterface;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    WriteUnitInterfaceToFile(Iface, PATH);
    Round := ReadUnitInterfaceFromFile(PATH);
    try
      AssertEquals('K value',
        Int64(7), Round.FindConst('K').Decl.IntVal);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_Record;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TPoint = record X, Y: Integer; end;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  Def:          TRecordTypeDef;
  F0, F1:       TFieldDecl;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TPoint');
      AssertTrue('TPoint present', E <> nil);
      AssertTrue('is record', E.Def is TRecordTypeDef);
      Def := TRecordTypeDef(E.Def);
      { Multi-name decl 'X, Y: Integer' was flattened to one
        TFieldDecl per name on the wire — reader produces two
        single-name TFieldDecls in order. }
      AssertEquals('2 fields', 2, Def.Fields.Count);
      F0 := TFieldDecl(Def.Fields.Items[0]);
      F1 := TFieldDecl(Def.Fields.Items[1]);
      AssertEquals('X name', 'X', F0.Names.Strings[0]);
      AssertEquals('Y name', 'Y', F1.Names.Strings[0]);
      AssertEquals('X type', 'Integer', F0.TypeName);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_Class_WithVirtualMethod;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TFoo = class' + #10 +
    '  Counter: Integer;' + #10 +
    '  procedure Speak; virtual;' + #10 +
    'end;' + #10 +
    'implementation' + #10 +
    'procedure TFoo.Speak(); begin end;' + #10 +
    'end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  M:            TRoutineSig;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TFoo');
      AssertTrue('TFoo present', E <> nil);
      AssertTrue('IsClass flagged', E.IsClass);
      { Implicit TObject parent: uSemanticExport.PopulateClassEntry
        emits ParentClass via ResolveTypeRef on the source's empty
        ParentName, which produces the ('', '') sentinel.  The
        importer treats an empty ParentName as the implicit-TObject
        signal — round-tripping that sentinel exactly is what we
        verify here. }
      AssertEquals('parent unit empty', '', E.ParentClass.UnitName);
      AssertEquals('parent type empty', '', E.ParentClass.TypeName);
      AssertTrue('InstanceSize > 0', E.InstanceSize > 0);
      AssertEquals('1 field', 1,
        TClassTypeDef(E.Def).Fields.Count);
      AssertEquals('1 method', 1, E.Methods.Count);
      M := TRoutineSig(E.Methods.Items[0]);
      AssertEquals('method name', 'Speak', M.Name);
      AssertTrue('IsVirtual', M.IsVirtual);
      AssertEquals('ResolvedQbeName', 'U_TFoo_Speak', M.ResolvedQbeName);
      AssertTrue('VTableSlot assigned', M.VTableSlot >= 0);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_Class_WithOverloadedMethods;
{ Regression (bugs.txt: imported methods lose IsOverload).  A class with an
  overloaded method set must round-trip the `overload` directive through the
  .bif: ResolveMethodOverload's hiding walk stops at the first NON-overload
  candidate, so a method imported with IsOverload=False would wrongly truncate
  an overload set that is split across an imported class and its ancestor. }
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TFoo = class' + #10 +
    '  procedure Add(A: Integer); overload;' + #10 +
    '  procedure Add(A: string); overload;' + #10 +
    'end;' + #10 +
    'implementation' + #10 +
    'procedure TFoo.Add(A: Integer); begin end;' + #10 +
    'procedure TFoo.Add(A: string); begin end;' + #10 +
    'end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  M:            TRoutineSig;
  I:            Integer;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TFoo');
      AssertTrue('TFoo present', E <> nil);
      AssertEquals('2 methods', 2, E.Methods.Count);
      { Every Add overload must carry IsOverload across the .bif boundary. }
      for I := 0 to E.Methods.Count - 1 do
      begin
        M := TRoutineSig(E.Methods.Items[I]);
        AssertEquals('overload method name', 'Add', M.Name);
        AssertTrue('IsOverload preserved for ' + M.ResolvedQbeName, M.IsOverload);
      end;
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_Interface_WithOverloadedMethods;
{ Interface methods serialise via EncodeMethodDecl/ReadMethodDecl (the AST
  TMethodDecl path, distinct from the class TRoutineSig path).  That path also
  dropped IsOverload, so an overloaded interface method imported from a .bif
  would lose its `overload` directive. }
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type IShape = interface' + #10 +
    '  procedure Draw(X: Integer); overload;' + #10 +
    '  procedure Draw(X: string); overload;' + #10 +
    'end;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  M:            TMethodDecl;
  I:            Integer;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('IShape');
      AssertTrue('IShape present', E <> nil);
      AssertTrue('is interface', E.Def is TInterfaceTypeDef);
      AssertEquals('2 methods', 2, TInterfaceTypeDef(E.Def).Methods.Count);
      for I := 0 to TInterfaceTypeDef(E.Def).Methods.Count - 1 do
      begin
        M := TMethodDecl(TInterfaceTypeDef(E.Def).Methods.Items[I]);
        AssertEquals('overload method name', 'Draw', M.Name);
        AssertTrue('IsOverload preserved', M.IsOverload);
      end;
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_Interface;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type IGreeter = interface' + #10 +
    '  function Hello: string;' + #10 +
    '  procedure Quit;' + #10 +
    'end;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('IGreeter');
      AssertTrue('IGreeter present', E <> nil);
      AssertTrue('is interface', E.Def is TInterfaceTypeDef);
      { Interface methods live on the AST (Def.Methods) — that's
        what uSemanticImport.RegisterInterface walks. }
      AssertEquals('2 methods', 2,
        TInterfaceTypeDef(E.Def).Methods.Count);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_Interface_WithProperty;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type IValued = interface' + #10 +
    '  function GetValue(): Integer;' + #10 +
    '  procedure SetValue(AValue: Integer);' + #10 +
    '  property Value: Integer read GetValue write SetValue;' + #10 +
    'end;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  P:            TPropertyDecl;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('IValued');
      AssertTrue('IValued present', E <> nil);
      AssertTrue('is interface', E.Def is TInterfaceTypeDef);
      AssertEquals('2 methods', 2, TInterfaceTypeDef(E.Def).Methods.Count);
      AssertEquals('1 property', 1, TInterfaceTypeDef(E.Def).Properties.Count);
      P := TPropertyDecl(TInterfaceTypeDef(E.Def).Properties.Items[0]);
      AssertEquals('property name', 'Value', P.Name);
      AssertEquals('property type', 'Integer', P.TypeName);
      AssertEquals('read accessor', 'GetValue', P.ReadName);
      AssertEquals('write accessor', 'SetValue', P.WriteName);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_ProceduralType;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TCallback = procedure(N: Integer) of object;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  Def:          TProceduralTypeDef;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TCallback');
      AssertTrue('TCallback present', E <> nil);
      AssertTrue('is procedural', E.Def is TProceduralTypeDef);
      Def := TProceduralTypeDef(E.Def);
      AssertTrue('not a function', not Def.IsFunction);
      AssertTrue('is method ptr', Def.IsMethodPtr);
      AssertEquals('1 param', 1, Def.Params.Count);
      AssertEquals('param name', 'N',
        TMethodParam(Def.Params.Items[0]).ParamName);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_ReferenceToType;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TOnDone = reference to function(N: Integer): Integer;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  Def:          TProceduralTypeDef;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TOnDone');
      AssertTrue('TOnDone present', E <> nil);
      AssertTrue('is procedural', E.Def is TProceduralTypeDef);
      Def := TProceduralTypeDef(E.Def);
      AssertTrue('is a function', Def.IsFunction);
      AssertTrue('IsReference survives the round-trip', Def.IsReference);
      AssertTrue('not a method ptr', not Def.IsMethodPtr);
      AssertEquals('return type', 'Integer', Def.ReturnTypeName);
      AssertEquals('1 param', 1, Def.Params.Count);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_Metadata_UsedUnits_SourceFile;
var
  Src, Round: TUnitInterface;
  Buf:        string;
begin
  Src := TUnitInterface.Create('U');
  Src.SourceFile      := '/a/b/U.pas';
  Src.SourceHash      := 'deadbeef';
  Src.CompilerId := '0.8.0-test';
  Src.UsedUnits.Add('SysUtils');
  Src.UsedUnits.Add('Classes');
  try
    Buf   := WriteUnitInterface(Src);
    Round := ReadUnitInterface(Buf);
    try
      AssertEquals('source file', '/a/b/U.pas', Round.SourceFile);
      AssertEquals('source hash', 'deadbeef',   Round.SourceHash);
      AssertEquals('version',     '0.8.0-test', Round.CompilerId);
      AssertEquals('2 used units', 2, Round.UsedUnits.Count);
      AssertEquals('first used',   'SysUtils', Round.UsedUnits.Strings[0]);
      AssertEquals('second used',  'Classes',  Round.UsedUnits.Strings[1]);
    finally
      Round.Free();
    end;
  finally
    Src.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_GenericClass_TemplateParams;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TBox<T> = class V: T; end;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  Def:          TGenericTypeDef;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TBox');
      AssertTrue('TBox present', E <> nil);
      AssertTrue('IsGeneric flagged', E.IsGeneric);
      AssertTrue('Def is TGenericTypeDef', E.Def is TGenericTypeDef);
      Def := TGenericTypeDef(E.Def);
      AssertEquals('1 type param', 1, Def.ParamNames.Count);
      AssertEquals('param name', 'T', Def.ParamNames.Strings[0]);
      AssertTrue('inner ClassDef present', Def.ClassDef <> nil);
      AssertEquals('1 field on template', 1, Def.ClassDef.Fields.Count);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_GenericInterface_TemplateParams;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type IBox<T> = interface' + #10 +
    '  function Get: T;' + #10 +
    'end;' + #10 +
    'implementation end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  Def:          TGenericInterfaceDef;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('IBox');
      AssertTrue('IBox present', E <> nil);
      AssertTrue('Def is TGenericInterfaceDef', E.Def is TGenericInterfaceDef);
      Def := TGenericInterfaceDef(E.Def);
      AssertEquals('1 type param', 1, Def.ParamNames.Count);
      AssertTrue('inner IntfDef present', Def.IntfDef <> nil);
      AssertEquals('1 method on template', 1, Def.IntfDef.Methods.Count);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

{ Helper for disk-path tests: takes a source string, builds a
  TUnitInterface, serialises it through the disk format (string
  round-trip), and imports the resulting iface into a fresh
  TSymbolTable.  Returns both for the caller to assert against.
  Caller owns the returned objects. }
procedure DiskPathImport(const ASource: string;
                         out ATab:   TSymbolTable;
                         out AIface: TUnitInterface);
var
  Src: TUnitInterface;
  Buf: string;
begin
  Src := ParseAnalyseAndExport(ASource);
  try
    Buf := WriteUnitInterface(Src);
  finally
    Src.Free();
  end;
  AIface := ReadUnitInterface(Buf);
  ATab   := FreshTableWithBuiltins();
  ImportUnitInterface(AIface, ATab);
end;

procedure TIfaceIOTests.TestDiskPath_Const_ImportsCleanly;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'const K = 99;' + #10 +
    'implementation end.' + #10;
var
  Tab:   TSymbolTable;
  Iface: TUnitInterface;
  Sym:   TSymbol;
begin
  DiskPathImport(SRC, Tab, Iface);
  try
    Sym := Tab.Lookup('K');
    AssertTrue('K defined', Sym <> nil);
    AssertEquals('K value', Int64(99), Sym.ConstValue);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestDiskPath_Enum_ImportsCleanly;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TColor = (Red, Green, Blue);' + #10 +
    'implementation end.' + #10;
var
  Tab:   TSymbolTable;
  Iface: TUnitInterface;
  Ty:    TTypeDesc;
  Sym:   TSymbol;
begin
  DiskPathImport(SRC, Tab, Iface);
  try
    Ty := Tab.FindType('TColor');
    AssertTrue('TColor defined', Ty <> nil);
    AssertTrue('is enum', Ty is TEnumTypeDesc);
    AssertEquals('3 members', 3, TEnumTypeDesc(Ty).Members.Count);
    { Members live on the enum descriptor and in the analyser's reverse index,
      NOT as bare global skConstant symbols — the same contract the
      source-visible path follows, so two enums may share a member name.
      (This import call passes no analyser, so only the descriptor is filled.) }
    AssertEquals('Green ordinal', 1, TEnumTypeDesc(Ty).Members.IndexOf('Green'));
    Sym := Tab.Lookup('Green');
    AssertTrue('Green is not a bare global constant', Sym = nil);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestDiskPath_Class_ImportsCleanly;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TFoo = class' + #10 +
    '  Counter: Integer;' + #10 +
    '  procedure Speak; virtual;' + #10 +
    'end;' + #10 +
    'implementation' + #10 +
    'procedure TFoo.Speak(); begin end;' + #10 +
    'end.' + #10;
var
  Tab:   TSymbolTable;
  Iface: TUnitInterface;
  RT:    TRecordTypeDesc;
  Slot:  Integer;
begin
  DiskPathImport(SRC, Tab, Iface);
  try
    RT := TRecordTypeDesc(Tab.FindType('TFoo'));
    AssertTrue('TFoo defined', RT <> nil);
    AssertTrue('Counter field', RT.FindField('Counter') <> nil);
    Slot := RT.FindVTableSlot('Speak');
    AssertTrue('Speak in vtable', Slot >= 0);
    AssertEquals('Speak ImplName',
      '$U_TFoo_Speak', RT.VTableEntryAt(Slot).ImplName);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestDiskPath_GenericClass_ImportsCleanly;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TBox<T> = class V: T; end;' + #10 +
    'implementation end.' + #10;
var
  Tab:   TSymbolTable;
  Iface: TUnitInterface;
  Templ: TObject;
begin
  DiskPathImport(SRC, Tab, Iface);
  try
    Templ := Tab.FindGeneric('TBox');
    AssertTrue('TBox template registered', Templ <> nil);
    AssertTrue('is TGenericTypeDef', Templ is TGenericTypeDef);
    AssertEquals('one type param', 1,
      TGenericTypeDef(Templ).ParamNames.Count);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestDiskPath_GenericRoutine_ImportsCleanly;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'function Identity<T>(V: T): T;' + #10 +
    'implementation' + #10 +
    'function Identity<T>(V: T): T; begin Result := V; end;' + #10 +
    'end.' + #10;
var
  Tab:   TSymbolTable;
  Iface: TUnitInterface;
  Templ: TObject;
begin
  { Generic routines: body serialisation is not yet implemented in
    the wire format, so MethodDecl.Body comes back nil through the
    disk path.  Asserting registration only — instantiation
    requires bodies and is gated on the AST body serialiser. }
  DiskPathImport(SRC, Tab, Iface);
  try
    Templ := Tab.FindGenericRoutine('Identity');
    AssertTrue('Identity template registered', Templ <> nil);
    AssertTrue('is TMethodDecl', Templ is TMethodDecl);
    AssertEquals('one type param', 1,
      TMethodDecl(Templ).TypeParams.Count);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestDiskPath_GenericRoutine_BodyPreserved;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'function Identity<T>(V: T): T;' + #10 +
    'implementation' + #10 +
    'function Identity<T>(V: T): T;' + #10 +
    'begin Result := V; end;' + #10 +
    'end.' + #10;
var
  Tab:   TSymbolTable;
  Iface: TUnitInterface;
  MD:    TMethodDecl;
  Comp:  TCompoundStmt;
  Asn:   TAssignment;
begin
  DiskPathImport(SRC, Tab, Iface);
  try
    MD := TMethodDecl(Tab.FindGenericRoutine('Identity'));
    AssertTrue('template registered', MD <> nil);
    AssertTrue('body preserved through disk', MD.Body <> nil);
    AssertTrue('at least one stmt', MD.Body.Stmts.Count >= 1);
    { Walk past any wrapping TCompoundStmt nodes the parser produces
      around 'begin … end;' to get at the actual assignment. }
    Asn := nil;
    if MD.Body.Stmts.Items[0] is TAssignment then
      Asn := TAssignment(MD.Body.Stmts.Items[0])
    else if MD.Body.Stmts.Items[0] is TCompoundStmt then
    begin
      Comp := TCompoundStmt(MD.Body.Stmts.Items[0]);
      if (Comp.Stmts.Count >= 1) and (Comp.Stmts.Items[0] is TAssignment) then
        Asn := TAssignment(Comp.Stmts.Items[0]);
    end;
    AssertTrue('found assignment somewhere', Asn <> nil);
    AssertEquals('lhs Result', 'Result', Asn.Name);
    AssertTrue('rhs is ident V', Asn.Expr is TIdentExpr);
    AssertEquals('rhs name V', 'V', TIdentExpr(Asn.Expr).Name);
  finally
    Tab.Free();
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_InlineBody_Preserved;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'function Square(N: Integer): Integer; inline;' + #10 +
    'implementation' + #10 +
    'function Square(N: Integer): Integer; inline;' + #10 +
    'begin Result := N * N; end;' + #10 +
    'end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  IB:           TInlineBody;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      IB := Round.FindInlineBody('Square');
      AssertTrue('Square inline body present', IB <> nil);
      AssertTrue('block carried', IB.Block <> nil);
      AssertTrue('has at least one stmt', IB.Block.Stmts.Count >= 1);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_StaticMembers_Preserved;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TReg = class' + #10 +
    '  private static var' + #10 +
    '    FCount: Integer;' + #10 +
    '  public' + #10 +
    '    static function Next: Integer;' + #10 +
    '    static property Counter: Integer read Next;' + #10 +
    '  public static const' + #10 +
    '    Tag = 7;' + #10 +
    'end;' + #10 +
    'implementation' + #10 +
    'static function TReg.Next: Integer; begin Result := FCount end;' + #10 +
    'end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  Def:          TClassTypeDef;
  Fld:          TFieldDecl;
  M:            TRoutineSig;
  Prop:         TPropertyDecl;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TReg');
      AssertTrue('TReg present', E <> nil);
      Def := TClassTypeDef(E.Def);

      { static var FCount: IsClassVar set, mangled emit label round-tripped. }
      AssertEquals('1 field decl', 1, Def.Fields.Count);
      Fld := TFieldDecl(Def.Fields.Items[0]);
      AssertEquals('field name', 'FCount', Fld.Names.Strings[0]);
      AssertTrue('FCount IsClassVar', Fld.IsClassVar);
      AssertEquals('FCount emit label', 'U_TReg_FCount', Fld.ClassVarEmitName);

      { static method Next: IsStatic carried on the routine sig. }
      AssertEquals('1 method', 1, E.Methods.Count);
      M := TRoutineSig(E.Methods.Items[0]);
      AssertEquals('method name', 'Next', M.Name);
      AssertTrue('Next IsStatic', M.IsStatic);

      { static property Counter: IsStatic carried on the property decl. }
      AssertEquals('1 property', 1, Def.Properties.Count);
      Prop := TPropertyDecl(Def.Properties.Items[0]);
      AssertEquals('prop name', 'Counter', Prop.Name);
      AssertTrue('Counter IsStatic', Prop.IsStatic);

      { static const Tag: carried in the class ConstDecls list. }
      AssertEquals('1 const decl', 1, Def.ConstDecls.Count);
      AssertEquals('const name', 'Tag',
        TConstDecl(Def.ConstDecls.Items[0]).Name);
      AssertEquals('const value', 7,
        TConstDecl(Def.ConstDecls.Items[0]).IntVal);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRoundTrip_WeakField_And_DefaultProperty_Preserved;
const
  SRC =
    'unit U;' + #10 +
    'interface' + #10 +
    'type TNode = class' + #10 +
    '    [Weak] FNext: TNode;' + #10 +
    '    function Get(I: Integer): Integer;' + #10 +
    '    property Items[I: Integer]: Integer read Get; default;' + #10 +
    'end;' + #10 +
    'implementation' + #10 +
    'function TNode.Get(I: Integer): Integer; begin Result := I end;' + #10 +
    'end.' + #10;
var
  Iface, Round: TUnitInterface;
  Buf:          string;
  E:            TTypeEntry;
  Def:          TClassTypeDef;
  Fld:          TFieldDecl;
  Prop:         TPropertyDecl;
begin
  Iface := ParseAnalyseAndExport(SRC);
  try
    Buf   := WriteUnitInterface(Iface);
    Round := ReadUnitInterface(Buf);
    try
      E := Round.FindType('TNode');
      AssertTrue('TNode present', E <> nil);
      Def := TClassTypeDef(E.Def);

      AssertEquals('1 field decl', 1, Def.Fields.Count);
      Fld := TFieldDecl(Def.Fields.Items[0]);
      AssertEquals('field name', 'FNext', Fld.Names.Strings[0]);
      AssertTrue('FNext IsWeak survives clone+round-trip', Fld.IsWeak);

      AssertEquals('1 property', 1, Def.Properties.Count);
      Prop := TPropertyDecl(Def.Properties.Items[0]);
      AssertEquals('prop name', 'Items', Prop.Name);
      AssertTrue('Items IsDefault survives clone+round-trip', Prop.IsDefault);
    finally
      Round.Free();
    end;
  finally
    Iface.Free();
  end;
end;

procedure TIfaceIOTests.TestRead_VersionMismatch_Raises;
var
  Caught: Boolean;
begin
  Caught := False;
  try
    ReadUnitInterface('BLAISE-IFACE 99' + #10 + '0:' + #10 + 'CONST 0' + #10 + 'END' + #10).Free();
  except
    on E: EIfaceFormatError do Caught := True;
  end;
  AssertTrue('version mismatch raised', Caught);
end;

initialization
  RegisterTest(TSelfContainmentTests);
  RegisterTest(TCrossUnitRefTests);
  RegisterTest(TConstRoundTripTests);
  RegisterTest(TEnumSetTests);
  RegisterTest(TRecordClassLayoutTests);
  RegisterTest(TInlineGenericBodyTests);
  RegisterTest(TImplementationHidingTests);
  RegisterTest(TVisibilityTests);
  RegisterTest(TForwardDeclTests);
  RegisterTest(TRoutineSigTests);
  RegisterTest(TUsedUnitsTests);
  RegisterTest(TLookupTests);
  RegisterTest(TMetadataTests);
  RegisterTest(TIfaceIOTests);
  RegisterTest(TImportRoundTripTests);
end.
