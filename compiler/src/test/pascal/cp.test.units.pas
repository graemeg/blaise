{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.units;

{ Tests for unit interface/implementation: parsing, semantic analysis,
  and code generation. Cross-unit 'uses' loading is out of scope here. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uUnitLoader, cp.test.harness;

type
  TUnitTests = class(TTestCase)
  private
    function  ParseUnit(const ASrc: string): TUnit;
    function  AnalyseUnit(const ASrc: string): TUnit;
    procedure AnalyseUnitExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Unit_Keyword;
    procedure TestLexer_Interface_Keyword;
    procedure TestLexer_Implementation_Keyword;

    { ------------------------------------------------------------------ }
    { Parser — structure                                                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_Unit_IsNotProgram;
    procedure TestParse_Unit_Name;
    procedure TestParse_Unit_IntfHasForwardDecls;
    procedure TestParse_Unit_ForwardDeclHasNilBody;
    procedure TestParse_Unit_ImplHasFullBodies;
    procedure TestParse_Unit_ImplBodyIsNotNil;
    { Nested procedure as the FIRST item in an impl routine's body must not be
      mistaken for a second top-level decl (impl-section parser).  Andrew's
      fix 82e770ac. }
    procedure TestParse_Unit_ImplNestedProcFirst_SingleDecl;
    procedure TestParse_Unit_ImplNestedProcFirst_HasBody;
    procedure TestParse_Unit_IntfTypeDecl;
    procedure TestParse_Unit_ForwardDeclParamCount;
    procedure TestParse_Unit_MultipleForwardDecls;
    { Issue #172: the legacy Turbo Pascal unit-initialization form
      `implementation ... begin ... end.` is deliberately unsupported.
      Blaise requires an explicit `initialization` section.  A bare
      `begin` block at unit-body position must give a clear, actionable
      error, not the raw `Expected 'end' but got 'begin'`. }
    procedure TestParse_Unit_LegacyBeginBody_Rejected;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Unit_OK;
    procedure TestSemantic_Unit_WithType_OK;
    { Qualified type name 'System.Integer' resolves to the builtin. }
    procedure TestSemantic_Unit_QualifiedType_OK;
    procedure TestSemantic_Unit_ImplBodyUsesIntfType;
    procedure TestSemantic_Unit_SignatureMismatch_ParamCount_RaisesError;
    procedure TestSemantic_Unit_MissingImpl_RaisesError;
    procedure TestSemantic_Unit_ImplOnlyDecl_OK;
    { Module names are reserved identifiers (issue #84): a unit's own
      name cannot be redeclared by interface or implementation decls;
      routine-local scopes may still shadow it. }
    procedure TestSemantic_UnitName_RedeclaredAsIntfVar_RaisesError;
    procedure TestSemantic_UnitName_RedeclaredAsImplVar_RaisesError;
    procedure TestSemantic_UnitName_LocalShadow_OK;

    { Interface-section global variable is registered and visible to
      implementation-section function bodies. }
    procedure TestSemantic_Unit_IntfVarVisibleInImpl;
    { Implementation-section type declarations are processed (e.g.
      enum types declared after the 'implementation' keyword can be
      used to type subsequent var declarations). }
    procedure TestSemantic_Unit_ImplTypeDecl;
    { Forward decl with 'overload' directive parses and analyses. }
    procedure TestSemantic_Unit_ForwardOverload_OK;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Unit_NoMainFunction;
    procedure TestCodegen_Unit_ExportsInterfaceRoutinesOnly;

    { ------------------------------------------------------------------ }
    { Unit loader                                                          }
    { ------------------------------------------------------------------ }
    { Missing unit with no search paths must raise EUnitNotFound, not
      silently succeed (regression for issue #31). }
    procedure TestUnitLoader_MissingUnit_NoSearchPaths_RaisesError;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TUnitTests.ParseUnit(const ASrc: string): TUnit;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit();
  finally
    P.Free(); L.Free();
  end;
end;

function TUnitTests.AnalyseUnit(const ASrc: string): TUnit;
var A: TSemanticAnalyser;
begin
  Result := ParseUnit(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.AnalyseUnit(Result);
  finally
    A.Free();
  end;
end;

procedure TUnitTests.AnalyseUnitExpectError(const ASrc: string);
var U: TUnit;
begin
  try
    U := AnalyseUnit(ASrc);
    U.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcUnitFuncs =
    '''
        unit MathUtils;
        interface
        function Add(A, B: Integer): Integer;
        function Mul(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        function Mul(A, B: Integer): Integer;
        begin
          Result := A * B
        end;
        end.
        ''';

  SrcUnitWithType =
    '''
        unit Shapes;
        interface
        type
          TBox = record
            W: Integer;
            H: Integer;
          end;
        function Area(W, H: Integer): Integer;
        implementation
        function Area(W, H: Integer): Integer;
        begin
          Result := W * H
        end;
        end.
        ''';

  SrcUnitImplOnly =
    '''
        unit Internals;
        interface
        function Pub(X: Integer): Integer;
        implementation
        function Helper(X: Integer): Integer;
        begin
          Result := X + 1
        end;
        function Pub(X: Integer): Integer;
        begin
          Result := Helper(X)
        end;
        end.
        ''';

  { Implementation-section routine whose body leads with a nested procedure
    declaration (no preceding var/const/type).  The outer routine must parse
    as a single decl WITH a body, not split into two bodyless decls. }
  SrcUnitNestedProcFirst =
    '''
        unit Nested;
        interface
        function Outer(N: Integer): Integer;
        implementation
        function Outer(N: Integer): Integer;
          function Inner(X: Integer): Integer;
          begin
            Result := X + 1
          end;
        var
          T: Integer;
        begin
          T := Inner(N);
          Result := T
        end;
        end.
        ''';

  { Qualified type names resolve by their final dotted component through the
    uses chain.  'System.Integer' needs no cross-unit load — System is
    implicit and Integer is builtin — so it self-containedly exercises the
    qualifier-stripping type resolver. }
  SrcUnitQualifiedType =
    '''
        unit QualT;
        interface
        function Twice(N: System.Integer): System.Integer;
        implementation
        function Twice(N: System.Integer): System.Integer;
        begin
          Result := N * 2
        end;
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestLexer_Unit_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('unit');
  try
    T := L.Next();
    AssertEquals('unit token', Ord(tkUnit), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TUnitTests.TestLexer_Interface_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('interface');
  try
    T := L.Next();
    AssertEquals('interface token', Ord(tkIntf), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TUnitTests.TestLexer_Implementation_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('implementation');
  try
    T := L.Next();
    AssertEquals('implementation token', Ord(tkImplementation), Ord(T.Kind));
  finally L.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestParse_Unit_IsNotProgram;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertNotNull('TUnit returned', U);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_Name;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertEquals('unit name is MathUtils', 'MathUtils', U.Name);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_IntfHasForwardDecls;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertEquals('intf has 2 forward decls', 2, U.IntfBlock.ProcDecls.Count);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_ForwardDeclHasNilBody;
var U: TUnit; MD: TMethodDecl;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    MD := TMethodDecl(U.IntfBlock.ProcDecls[0]);
    AssertNull('forward decl body is nil', MD.Body);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_ImplHasFullBodies;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertEquals('impl has 2 full decls', 2, U.ImplBlock.ProcDecls.Count);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_ImplBodyIsNotNil;
var U: TUnit; MD: TMethodDecl;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    MD := TMethodDecl(U.ImplBlock.ProcDecls[0]);
    AssertNotNull('impl body is not nil', MD.Body);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_ImplNestedProcFirst_SingleDecl;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitNestedProcFirst);
  try
    AssertEquals('impl has 1 decl (outer routine only)',
      1, U.ImplBlock.ProcDecls.Count);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_ImplNestedProcFirst_HasBody;
var U: TUnit; MD: TMethodDecl;
begin
  U := ParseUnit(SrcUnitNestedProcFirst);
  try
    MD := TMethodDecl(U.ImplBlock.ProcDecls[0]);
    AssertNotNull('outer routine has a body', MD.Body);
    AssertEquals('outer body holds the nested proc',
      1, MD.Body.ProcDecls.Count);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_IntfTypeDecl;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitWithType);
  try
    AssertEquals('intf has 1 type decl', 1, U.IntfBlock.TypeDecls.Count);
    AssertEquals('type name is TBox',
      'TBox', TTypeDecl(U.IntfBlock.TypeDecls[0]).Name);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_ForwardDeclParamCount;
var U: TUnit; MD: TMethodDecl;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    MD := TMethodDecl(U.IntfBlock.ProcDecls[0]);  { Add }
    AssertEquals('Add has 2 params', 2, MD.Params.Count);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_MultipleForwardDecls;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitImplOnly);
  try
    AssertEquals('intf has 1 forward decl', 1, U.IntfBlock.ProcDecls.Count);
    AssertEquals('impl has 2 full decls',   2, U.ImplBlock.ProcDecls.Count);
  finally U.Free(); end;
end;

procedure TUnitTests.TestParse_Unit_LegacyBeginBody_Rejected;
const
  SrcLegacyBegin =
    '''
    unit tunit;
    interface
    var x: Integer;
    implementation
    begin
      x := 1;
    end.
    ''';
begin
  { Issue #172: legacy Turbo Pascal unit-init form is rejected with a
    clear message pointing the user at 'initialization'. }
  try
    ParseUnit(SrcLegacyBegin).Free();
    Fail('Expected EParseError for legacy begin-body unit');
  except
    on E: EParseError do
      AssertTrue('mentions initialization',
        Pos('initialization', E.Message) >= 0);
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestSemantic_Unit_OK;
begin
  AnalyseUnit(SrcUnitFuncs).Free();
end;

procedure TUnitTests.TestSemantic_Unit_WithType_OK;
begin
  AnalyseUnit(SrcUnitWithType).Free();
end;

procedure TUnitTests.TestSemantic_Unit_QualifiedType_OK;
begin
  AnalyseUnit(SrcUnitQualifiedType).Free();
end;

procedure TUnitTests.TestSemantic_Unit_ImplBodyUsesIntfType;
begin
  { TBox is declared in interface; impl body can reference it }
  AnalyseUnit(SrcUnitWithType).Free();
end;

procedure TUnitTests.TestSemantic_Unit_SignatureMismatch_ParamCount_RaisesError;
begin
  AnalyseUnitExpectError(
    'unit Bad;' + #10 +
    'interface' + #10 +
    'function Add(A, B: Integer): Integer;' + #10 +
    'implementation' + #10 +
    'function Add(A: Integer): Integer;'         + #10 +  { wrong: 1 param }
    '''
        begin
          Result := A
        end;
        end.
        ''');
end;

procedure TUnitTests.TestSemantic_Unit_MissingImpl_RaisesError;
begin
  AnalyseUnitExpectError(
    '''
        unit Bad;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        end.
        ''');                                     { no implementation of Add }
end;

procedure TUnitTests.TestSemantic_UnitName_RedeclaredAsIntfVar_RaisesError;
begin
  AnalyseUnitExpectError(
    '''
        unit Clash;
        interface
        var Clash: Integer;
        implementation
        end.
        ''');
end;

procedure TUnitTests.TestSemantic_UnitName_RedeclaredAsImplVar_RaisesError;
begin
  AnalyseUnitExpectError(
    '''
        unit Clash;
        interface
        implementation
        var Clash: Integer;
        end.
        ''');
end;

procedure TUnitTests.TestSemantic_UnitName_LocalShadow_OK;
begin
  AnalyseUnit(
    '''
        unit Outer;
        interface
        procedure P;
        implementation
        procedure P;
        var Outer: Integer;
        begin
          Outer := 1;
        end;
        end.
        ''').Free();
end;

procedure TUnitTests.TestSemantic_Unit_ImplOnlyDecl_OK;
begin
  { Helper is impl-only; Pub calls Helper — both should resolve }
  AnalyseUnit(SrcUnitImplOnly).Free();
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestCodegen_Unit_NoMainFunction;
begin
  { A unit compiled on its own is a library object: no program entry. }
  AssertTrue('x86-64: no main', Pos(#10 + 'main:', GenUnitAsm(SrcUnitFuncs, TargetX86_64)) < 0);
  AssertTrue('arm64: no main', Pos(#10 + '_main:', GenUnitAsm(SrcUnitFuncs, TargetArm64)) < 0);
end;

procedure TUnitTests.TestCodegen_Unit_ExportsInterfaceRoutinesOnly;
var
  X86, A64: string;
begin
  { Interface routines are defined under their unit-prefixed name and
    exported for the objects that use the unit; an implementation-only
    routine is defined but, on x86-64, stays private to the unit's object.  The symbol
    binding is invisible within one program -- it decides what links. }
  X86 := GenUnitAsm(SrcUnitFuncs, TargetX86_64);
  A64 := GenUnitAsm(SrcUnitFuncs, TargetArm64);
  AssertTrue('x86-64: MathUtils_Add defined', Pos(#10 + 'MathUtils_Add:', X86) >= 0);
  AssertTrue('x86-64: MathUtils_Mul exported', Pos('.globl MathUtils_Mul', X86) >= 0);
  AssertTrue('arm64: MathUtils_Add defined', Pos(#10 + '_MathUtils_Add:', A64) >= 0);
  AssertTrue('arm64: MathUtils_Mul exported', Pos('.globl _MathUtils_Mul', A64) >= 0);
  X86 := GenUnitAsm(SrcUnitImplOnly, TargetX86_64);
  A64 := GenUnitAsm(SrcUnitImplOnly, TargetArm64);
  AssertTrue('x86-64: Internals_Pub exported', Pos('.globl Internals_Pub', X86) >= 0);
  AssertTrue('x86-64: Internals_Helper defined', Pos(#10 + 'Internals_Helper:', X86) >= 0);
  AssertTrue('x86-64: Internals_Helper not exported',
    Pos('.globl Internals_Helper', X86) < 0);
  AssertTrue('arm64: Internals_Pub exported', Pos('.globl _Internals_Pub', A64) >= 0);
  { arm64 exports every routine; the unit-prefixed name cannot collide, so
    only its definition is pinned there }
  AssertTrue('arm64: Internals_Helper defined', Pos(#10 + '_Internals_Helper:', A64) >= 0);
end;

procedure TUnitTests.TestSemantic_Unit_IntfVarVisibleInImpl;
var
  U: TUnit;
begin
  U := AnalyseUnit(
    '''
        unit U;
        interface
        var Counter: Integer;
        procedure Bump;
        implementation
        procedure Bump;
        begin Counter := Counter + 1 end;
        end.
        ''');
  U.Free();
end;

procedure TUnitTests.TestSemantic_Unit_ImplTypeDecl;
var
  U: TUnit;
begin
  U := AnalyseUnit(
    '''
        unit U;
        interface
        procedure Bump;
        implementation
        type
          TMode = (mA, mB, mC);
        var CurrentMode: TMode;
        procedure Bump;
        begin CurrentMode := mA end;
        end.
        ''');
  U.Free();
end;

procedure TUnitTests.TestSemantic_Unit_ForwardOverload_OK;
var
  U: TUnit;
begin
  U := AnalyseUnit(
    '''
        unit U;
        interface
        function Add(A, B: Integer): Integer; overload;
        function Add(A, B: Double):  Double;  overload;
        implementation
        function Add(A, B: Integer): Integer; overload;
        begin Result := A + B end;
        function Add(A, B: Double): Double; overload;
        begin Result := A + B end;
        end.
        ''');
  U.Free();
end;

procedure TUnitTests.TestUnitLoader_MissingUnit_NoSearchPaths_RaisesError;
var
  Lexer:      TLexer;
  Parser:     TParser;
  Prog:       TProgram;
  Loader:     TUnitLoader;
  SearchPaths: TStringList;
  Units:      TObjectList;
begin
  Lexer  := TLexer.Create('program nounit; uses zip, zilch, nada; begin end.');
  Parser := TParser.Create(Lexer);
  Prog   := Parser.Parse();
  try
    SearchPaths := TStringList.Create();
    try
      Loader := TUnitLoader.Create(SearchPaths);
      try
        try
          Units := Loader.LoadAll(Prog.UsedUnits);
          Units.Free();
          Fail('Expected EUnitNotFound');
        except
          on E: EUnitNotFound do ;
        end;
      finally
        Loader.Free();
      end;
    finally
      SearchPaths.Free();
    end;
  finally
    Prog.Free();
    Parser.Free();
    Lexer.Free();
  end;
end;

initialization
  RegisterTest(TUnitTests);

end.
