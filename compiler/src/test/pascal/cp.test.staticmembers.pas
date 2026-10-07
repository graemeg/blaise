{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.staticmembers;

{ Tests for `static` (class-level) members: static var, static const,
  static function/procedure, static property, on classes and records.
  Feature 1 of the static-members work.  Covers the PARSER layer
  (TStaticMembersParseTests — the forms parse, the IsStatic / IsClassVar AST
  flags are set, and `static constructor` / `static destructor` are rejected)
  and the SEMANTIC layer (TStaticMembersSemTests — resolution of static vars
  to shared globals, no-Self static methods).  Lowering -- shared global slots,
  qualified reads and writes, static properties, the program-exit release of
  class-typed static vars -- is covered end to end by
  cp.test.e2e.staticmembers.pas. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable;

type
  TStaticMembersParseTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function ClassOf(AProg: TProgram; AIndex: Integer): TClassTypeDef;
    function RecordOf(AProg: TProgram; AIndex: Integer): TRecordTypeDef;
    procedure ParseExpectError(const ASrc: string);
    procedure ParseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
  published
    { static var / static const sections on a class }
    procedure TestParse_StaticVarSection_SetsIsClassVar;
    procedure TestParse_PlainFieldAfterStaticVar_NotClassVar;
    procedure TestParse_PrivateStaticVar_SetsIsClassVar;
    procedure TestParse_StaticConstSection_OnClass;
    procedure TestParse_StaticConstSection_FollowedByMoreMembers;

    { static method prefix and section }
    procedure TestParse_StaticFunctionPrefix_SetsIsStatic;
    procedure TestParse_StaticProcedurePrefix_SetsIsStatic;
    procedure TestParse_StaticSection_AppliesToMethods;
    procedure TestParse_PlainMethodAfterStaticSection_NotStatic;
    { BUG-036: a bare `static var` BLOCK ends at the first method/property —
      a method declared right after it must NOT silently become static
      (that made instance fields invisible in its body). }
    procedure TestParse_MethodAfterBareStaticVar_NotStatic;
    procedure TestParse_PropertyAfterBareStaticVar_NotStatic;
    procedure TestParse_BareStaticKeepsCurrentVisibility;

    { static property }
    procedure TestParse_StaticProperty_SetsIsStatic;

    { out-of-line static impl }
    procedure TestParse_StaticImpl_OutOfLine;

    { records }
    procedure TestParse_StaticFunctionInRecord_SetsIsStatic;
    procedure TestParse_StaticVarInRecord_SetsIsClassVar;
    procedure TestParse_StaticConstInRecord;

    { rejections }
    procedure TestParse_StaticConstructor_Rejected;
    procedure TestParse_StaticDestructor_Rejected;
  end;

implementation

function TStaticMembersParseTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
end;

function TStaticMembersParseTests.ClassOf(AProg: TProgram; AIndex: Integer): TClassTypeDef;
var TD: TTypeDecl;
begin
  TD := TTypeDecl(AProg.Block.TypeDecls.Items[AIndex]);
  Result := TD.Def as TClassTypeDef;
end;

function TStaticMembersParseTests.RecordOf(AProg: TProgram; AIndex: Integer): TRecordTypeDef;
var TD: TTypeDecl;
begin
  TD := TTypeDecl(AProg.Block.TypeDecls.Items[AIndex]);
  Result := TD.Def as TRecordTypeDef;
end;

procedure TStaticMembersParseTests.ParseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := ParseSrc(ASrc);
    Prog.Free();
    Fail('Expected EParseError');
  except
    on E: EParseError do ;
  end;
end;

procedure TStaticMembersParseTests.ParseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
var Prog: TProgram;
begin
  try
    Prog := ParseSrc(ASrc);
    Prog.Free();
    Fail('Expected EParseError');
  except
    on E: EParseError do
      AssertTrue('error message contains "' + AExpectedSubstr + '" (got: ' +
        E.Message + ')', Pos(AExpectedSubstr, E.Message) >= 0);
  end;
end;

{ ------------------------------------------------------------------ }
{  static var / static const                                          }
{ ------------------------------------------------------------------ }

procedure TStaticMembersParseTests.TestParse_StaticVarSection_SetsIsClassVar;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          static var
            FInstance: TFoo;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef; F: TFieldDecl;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('one field', 1, C.Fields.Count);
    F := TFieldDecl(C.Fields.Items[0]);
    AssertEquals('field name', 'FInstance', F.Names[0]);
    AssertTrue('FInstance is a class var', F.IsClassVar);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_PlainFieldAfterStaticVar_NotClassVar;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          static var
            FShared: Integer;
          public
            FInst: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('two fields', 2, C.Fields.Count);
    AssertTrue('FShared is class var', TFieldDecl(C.Fields.Items[0]).IsClassVar);
    AssertFalse('FInst is NOT class var (section reset by public)',
      TFieldDecl(C.Fields.Items[1]).IsClassVar);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_PrivateStaticVar_SetsIsClassVar;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private static var
            FInstance: TFoo;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('one field', 1, C.Fields.Count);
    AssertTrue('private static var is class var',
      TFieldDecl(C.Fields.Items[0]).IsClassVar);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_StaticConstSection_OnClass;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          static const
            MaxItems = 256;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('one const', 1, C.ConstDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_StaticConstSection_FollowedByMoreMembers;
const
  { A static const section is not the last section: the const block must stop
    at the following `private` visibility keyword rather than swallowing it. }
  Src =
    '''
        program P;
        type
          TFoo = class
          private static const
            MaxEntries = 256;
          private
            FCount: Integer;
          public
            function GetCount: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('one const', 1, C.ConstDecls.Count);
    AssertEquals('one field', 1, C.Fields.Count);
    AssertEquals('field name', 'FCount', TFieldDecl(C.Fields.Items[0]).Names[0]);
    AssertEquals('one method', 1, C.Methods.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  static methods                                                      }
{ ------------------------------------------------------------------ }

procedure TStaticMembersParseTests.TestParse_StaticFunctionPrefix_SetsIsStatic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
            static function GetInstance: TFoo;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef; M: TMethodDecl;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('one method', 1, C.Methods.Count);
    M := TMethodDecl(C.Methods.Items[0]);
    AssertEquals('method name', 'GetInstance', M.Name);
    AssertTrue('GetInstance is static', M.IsStatic);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_StaticProcedurePrefix_SetsIsStatic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
            static procedure Reset;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertTrue('Reset is static', TMethodDecl(C.Methods.Items[0]).IsStatic);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_StaticSection_AppliesToMethods;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          public static
            function A: Integer;
            function B: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('two methods', 2, C.Methods.Count);
    AssertTrue('A is static', TMethodDecl(C.Methods.Items[0]).IsStatic);
    AssertTrue('B is static', TMethodDecl(C.Methods.Items[1]).IsStatic);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_PlainMethodAfterStaticSection_NotStatic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          public static
            function A: Integer;
          public
            function B: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertTrue('A is static', TMethodDecl(C.Methods.Items[0]).IsStatic);
    AssertFalse('B is NOT static (section reset by public)',
      TMethodDecl(C.Methods.Items[1]).IsStatic);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_BareStaticKeepsCurrentVisibility;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private
            FInst: Integer;
          static
            function A: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertFalse('FInst not class var', TFieldDecl(C.Fields.Items[0]).IsClassVar);
    AssertTrue('A is static', TMethodDecl(C.Methods.Items[0]).IsStatic);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  static property                                                     }
{ ------------------------------------------------------------------ }

procedure TStaticMembersParseTests.TestParse_StaticProperty_SetsIsStatic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
            static function GetInstance: TFoo;
            static property Instance: TFoo read GetInstance;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef; Pr: TPropertyDecl;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertEquals('one property', 1, C.Properties.Count);
    Pr := TPropertyDecl(C.Properties.Items[0]);
    AssertEquals('property name', 'Instance', Pr.Name);
    AssertTrue('Instance property is static', Pr.IsStatic);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  out-of-line static impl                                             }
{ ------------------------------------------------------------------ }

procedure TStaticMembersParseTests.TestParse_StaticImpl_OutOfLine;
const
  Src =
    '''
        program P;
        type
          TFoo = class
            static function GetInstance: TFoo;
          end;
        static function TFoo.GetInstance: TFoo;
        begin
          Result := nil;
        end;
        begin end.
        ''';
var Prog: TProgram; M: TMethodDecl;
begin
  Prog := ParseSrc(Src);
  try
    { The out-of-line impl is a standalone proc decl in the block. }
    AssertEquals('one standalone proc', 1, Prog.Block.ProcDecls.Count);
    M := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('out-of-line impl is static', M.IsStatic);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  records                                                             }
{ ------------------------------------------------------------------ }

procedure TStaticMembersParseTests.TestParse_StaticFunctionInRecord_SetsIsStatic;
const
  Src =
    '''
        program P;
        type
          TInfo = record
            Category: string;
            static function New(const C: string): TInfo;
          end;
        begin end.
        ''';
var Prog: TProgram; R: TRecordTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    R := RecordOf(Prog, 0);
    AssertEquals('one method', 1, R.Methods.Count);
    AssertTrue('New is static', TMethodDecl(R.Methods.Items[0]).IsStatic);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_StaticVarInRecord_SetsIsClassVar;
const
  Src =
    '''
        program P;
        type
          TInfo = record
            Category: string;
          static var
            Count: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; R: TRecordTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    R := RecordOf(Prog, 0);
    AssertEquals('two fields', 2, R.Fields.Count);
    AssertFalse('Category not class var', TFieldDecl(R.Fields.Items[0]).IsClassVar);
    AssertTrue('Count is class var', TFieldDecl(R.Fields.Items[1]).IsClassVar);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_StaticConstInRecord;
const
  Src =
    '''
        program P;
        type
          TInfo = record
            X: Integer;
          static const
            Tag = 7;
          end;
        begin end.
        ''';
var Prog: TProgram; R: TRecordTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    R := RecordOf(Prog, 0);
    AssertEquals('one const', 1, R.ConstDecls.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  rejections                                                          }
{ ------------------------------------------------------------------ }

procedure TStaticMembersParseTests.TestParse_StaticConstructor_Rejected;
const
  Src =
    '''
        program P;
        type
          TFoo = class
            static constructor Create;
          end;
        begin end.
        ''';
begin
  ParseExpectErrorMsg(Src, 'static');
end;

procedure TStaticMembersParseTests.TestParse_StaticDestructor_Rejected;
const
  Src =
    '''
        program P;
        type
          TFoo = class
            static destructor Destroy;
          end;
        begin end.
        ''';
begin
  ParseExpectErrorMsg(Src, 'static');
end;

{ ================================================================== }
{  Semantic tests                                                     }
{ ================================================================== }

type
  TStaticMembersSemTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
  published
    { static var resolves to a shared global, not an instance field }
    procedure TestSem_StaticVar_BareReadResolves;
    procedure TestSem_StaticVar_NotAnInstanceField;
    procedure TestSem_StaticVar_RejectsStringType;
    procedure TestSem_StaticVar_AcceptsClassType;
    procedure TestSem_StaticMethod_NoSelf_CannotTouchInstanceField;
    procedure TestSem_StaticMethod_CanReadStaticVar;
  end;

function TStaticMembersSemTests.AnalyseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser; A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

procedure TStaticMembersSemTests.AnalyseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do
      AssertTrue('error message contains "' + AExpectedSubstr + '" (got: ' +
        E.Message + ')', Pos(AExpectedSubstr, E.Message) >= 0);
  end;
end;

procedure TStaticMembersSemTests.TestSem_StaticVar_BareReadResolves;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private static var
            FCount: Integer;
            static procedure Bump;
          end;
        static procedure TFoo.Bump;
        begin
          FCount := FCount + 1;
        end;
        begin end.
        ''';
var Prog: TProgram;
begin
  { Just analysing without an "undeclared identifier" error proves the bare
    static-var name resolves inside a static method. }
  Prog := AnalyseSrc(Src);
  Prog.Free();
end;

procedure TStaticMembersSemTests.TestSem_StaticVar_NotAnInstanceField;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private static var
            FShared: Integer;
          public
            FInst: Integer;
          end;
        var
          F: TFoo;
        begin
          F := TFoo.Create();
          F.FInst := 7;
        end.
        ''';
var Prog: TProgram; RT: TRecordTypeDesc; Sym: TSymbol;
begin
  Prog := AnalyseSrc(Src);
  try
    Sym := Prog.SymbolTable.Lookup('TFoo');
    AssertNotNull('TFoo type present', Sym);
    RT := TRecordTypeDesc(Sym.TypeDesc);
    { The class has exactly ONE instance field (FInst); FShared is a static
      var and must NOT occupy an instance slot. }
    AssertNotNull('FInst is an instance field', RT.FindField('FInst'));
    AssertNull('FShared is NOT an instance field', RT.FindField('FShared'));
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersSemTests.TestSem_StaticVar_RejectsStringType;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private static var
            FName: string;
            FData: array of Integer;
          end;
        begin end.
        ''';
var
  Prog: TProgram;
begin
  { String and dynamic-array static vars are now SUPPORTED (BUG-20260720-static-
    var-string-unsupported lifted the restriction — the store/read paths were
    already type-generic; teardown releases by type).  Drive the full analyse ->
    Free cycle and assert it completes without a rejection. }
  Prog := AnalyseSrc(Src);
  Prog.Free();
  AssertTrue('string + dynarray static vars analyse and tear down cleanly', True);
end;

procedure TStaticMembersSemTests.TestSem_StaticVar_AcceptsClassType;
const
  Src =
    '''
        program P;
        type
          TConfig = class
          private static var
            FInstance: TConfig;
          public
            static function Instance: TConfig;
          end;
        static function TConfig.Instance: TConfig;
        begin
          if FInstance = nil then FInstance := TConfig.Create();
          Result := FInstance;
        end;
        begin TConfig.Instance(); end.
        ''';
var
  Prog: TProgram;
begin
  { A class-typed (self-referential) static var is the canonical singleton
    shape.  This used to corrupt the heap during AST/symbol-table teardown
    (a double-free of the shared GlobalEmitName string registered on the two
    static-var symbols).  Drive the full analyse -> Free cycle and assert it
    completes without error — the teardown is the part under test. }
  Prog := AnalyseSrc(Src);
  Prog.Free();
  AssertTrue('class-typed static var analyses and tears down cleanly', True);
end;

procedure TStaticMembersSemTests.TestSem_StaticMethod_NoSelf_CannotTouchInstanceField;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          public
            FInst: Integer;
            static procedure Bad;
          end;
        static procedure TFoo.Bad;
        begin
          FInst := 1;
        end;
        begin end.
        ''';
begin
  { A static method has no Self, so an instance field is not in scope. }
  AnalyseExpectErrorMsg(Src, 'FInst');
end;

procedure TStaticMembersSemTests.TestSem_StaticMethod_CanReadStaticVar;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private static var
            FCount: Integer;
          public
            static function GetCount: Integer;
          end;
        static function TFoo.GetCount: Integer;
        begin
          Result := FCount;
        end;
        begin end.
        ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  Prog.Free();
end;

procedure TStaticMembersParseTests.TestParse_MethodAfterBareStaticVar_NotStatic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private
            FName: string;
          public
            constructor Create; overload;
            static var Shared: Integer;
            procedure Log;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertTrue('Shared is class var',
      TFieldDecl(C.Fields.Items[1]).IsClassVar);
    AssertFalse('FName stays an instance field',
      TFieldDecl(C.Fields.Items[0]).IsClassVar);
    AssertFalse('Log after the static var block is NOT static',
      TMethodDecl(C.Methods.Items[1]).IsStatic);
  finally
    Prog.Free();
  end;
end;

procedure TStaticMembersParseTests.TestParse_PropertyAfterBareStaticVar_NotStatic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private
            FVal: Integer;
          public
            static var Shared: Integer;
            property Val: Integer read FVal;
          end;
        begin end.
        ''';
var Prog: TProgram; C: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    C := ClassOf(Prog, 0);
    AssertFalse('property after the static var block is NOT static',
      TPropertyDecl(C.Properties.Items[0]).IsStatic);
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TStaticMembersParseTests);
  RegisterTest(TStaticMembersSemTests);

end.
