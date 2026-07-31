{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.classes;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TClassTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestCodegen_AliasConstructor_RunsUserCtor;
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Class_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_ClassSection_Exists;
    procedure TestParse_ClassType_Name;
    procedure TestParse_ClassType_SingleField;
    procedure TestParse_ClassType_MultipleFields;
    procedure TestParse_ClassType_WithParent;
    procedure TestParse_ClassVar;
    procedure TestParse_ClassConstructorCall;
    procedure TestParse_ClassFieldAssignment;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ClassType_Registered;
    procedure TestSemantic_ClassType_IsClass;
    procedure TestSemantic_ClassVar_HasClassType;
    procedure TestSemantic_Constructor_TypeIsClass;
    procedure TestSemantic_ClassFieldAssign_OK;
    procedure TestSemantic_ClassFieldAssign_TypeMismatch_RaisesError;
    procedure TestSemantic_ClassFieldAccess_TypeIsFieldType;
    procedure TestSemantic_ClassFieldAccess_UnknownField_RaisesError;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_ClassVar_HasPointerAlloc;
    procedure TestCodegen_ClassVar_ZeroInit;
    procedure TestCodegen_Constructor_CallsClassAlloc;
    procedure TestCodegen_ClassFieldStore_LoadsPointer;
    procedure TestCodegen_ClassFieldLoad_LoadsPointer;

    { ------------------------------------------------------------------ }
    { Separate method implementations                                      }
    { ------------------------------------------------------------------ }
    procedure TestParse_SeparateImpl_ForwardDeclNoBody;
    procedure TestParse_SeparateImpl_QualifiedName;
    procedure TestSemantic_SeparateImpl_OK;
    procedure TestSemantic_MethodBody_AccessesProgramGlobal;
    procedure TestCodegen_SeparateImpl_EmitsMethod;
    procedure TestCodegen_MethodCall_CaseInsensitive;
    procedure TestCodegen_MethodBody_ReadsProgramGlobal;
    procedure TestSemantic_MethodDeclaredNotImplemented_RaisesError;
    procedure TestSemantic_AbstractMethod_NoImpl_OK;
    procedure TestSemantic_ExternalMethod_NoImpl_OK;

    { ------------------------------------------------------------------ }
    { Forward class declarations  (TFoo = class;)                          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ForwardClass_CompletedByFullDecl;
    procedure TestSemantic_ForwardClass_MutualReference;
    procedure TestSemantic_ForwardClass_Unresolved_RaisesError;
    procedure TestSemantic_ForwardClass_DoubleForward_RaisesError;
    procedure TestCodegen_ForwardClass_SingleVTable;
    procedure TestCodegen_ForwardClass_CaseDifferentSpelling_FieldCleanupConsistent;

    { ------------------------------------------------------------------ }
    { Free built-in                                                        }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Free_OK;
    procedure TestCodegen_Free_CallsClassRelease;

    { ------------------------------------------------------------------ }
    { ARC on class variables and fields                                    }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_ClassVarAssign_InsertsAddRefRelease;
    procedure TestCodegen_ClassVarAssignNil_EmitsRelease;
    procedure TestCodegen_ClassVarScopeExit_EmitsRelease;
    procedure TestCodegen_ClassFieldAssign_InsertsAddRefRelease;
    procedure TestCodegen_FieldCleanup_EmittedPerClass;
    procedure TestCodegen_FieldCleanup_ReleasesClassField;
    { Regression — a class with an overloaded Destroy emits the
      destructor as '<Class>_Destroy$...' (mangled).  The field-cleanup
      helper must call that mangled name; the bare '<Class>_Destroy'
      label is never emitted in that case, so a hard-coded call would
      leave the binary with an undefined-symbol link error. }
    procedure TestCodegen_FieldCleanup_OverloadedDestroy_CallsMangledSymbol;

    { ------------------------------------------------------------------ }
    { vtable initialisation                                                }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Constructor_NoArgs_StoresVTable;
    procedure TestCodegen_Constructor_WithArgs_StoresVTable;
    procedure TestCodegen_Constructor_WithArgs_ExactlyOneAddRef;

    { ------------------------------------------------------------------ }
    { ARC on method string parameters                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_MethodStringParam_AddRefOnEntry;
    procedure TestCodegen_MethodStringParam_ReleaseOnExit;

    { ------------------------------------------------------------------ }
    { 0-based string semantic analysis                                     }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ConstructorPrefix_CreateFmt;
    procedure TestSemantic_PointerTypeAlias;
    procedure TestSemantic_MetaclassAlias;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TClassTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TClassTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TClassTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

{ ------------------------------------------------------------------ }
{ Lexer                                                               }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestLexer_Class_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('class');
  try
    T := L.Next();
    AssertEquals('class token', Ord(tkClass), Ord(T.Kind));
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

const
  SrcSimpleClass =
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        begin end.
        ''';

procedure TClassTests.TestParse_ClassSection_Exists;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcSimpleClass);
  try
    AssertEquals('1 type decl', 1, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_ClassType_Name;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcSimpleClass);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('Type name', 'TFoo', TD.Name);
    AssertTrue('Is TClassTypeDef', TD.Def is TClassTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_ClassType_SingleField;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  Fld:  TFieldDecl;
begin
  Prog := ParseSrc(SrcSimpleClass);
  try
    CD  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('1 field', 1, CD.Fields.Count);
    Fld := TFieldDecl(CD.Fields[0]);
    AssertEquals('Field name', 'X', Fld.Names[0]);
    AssertEquals('Field type', 'Integer', Fld.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_ClassType_MultipleFields;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPerson = class
            Name: string;
            Age: Integer;
          end;
        begin end.
        ''');
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('2 fields', 2, CD.Fields.Count);
    AssertEquals('First field', 'Name', TFieldDecl(CD.Fields[0]).Names[0]);
    AssertEquals('Second field', 'Age',  TFieldDecl(CD.Fields[1]).Names[0]);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_ClassType_WithParent;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TAnimal = class
            Name: string;
          end;
          TDog = class(TAnimal)
            Breed: string;
          end;
        begin end.
        ''');
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    AssertEquals('Parent class', 'TAnimal', CD.ParentName);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_ClassVar;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin end.
        ''');
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Var name', 'F', Decl.Names[0]);
    AssertEquals('Var type', 'TFoo', Decl.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_ClassConstructorCall;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Expr:   TFieldAccessExpr;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create()
        end.
        ''');
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('Assigns to F', 'F', Assign.Name);
    AssertTrue('Expr is TMethodCallExpr', Assign.Expr is TMethodCallExpr);
    AssertEquals('Type name', 'TFoo',   TMethodCallExpr(Assign.Expr).ObjectName);
    AssertEquals('Method',    'Create', TMethodCallExpr(Assign.Expr).Name);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_ClassFieldAssignment;
var
  Prog: TProgram;
  Stmt: TFieldAssignment;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F.X := 99
        end.
        ''');
  try
    Stmt := TFieldAssignment(Prog.Block.Stmts[0]);
    AssertEquals('Record var',  'F',  Stmt.RecordName);
    AssertEquals('Field name',  'X',  Stmt.FieldName);
    AssertTrue('Expr is TIntLiteral', Stmt.Expr is TIntLiteral);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestSemantic_ClassType_Registered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcSimpleClass);
  try
    AssertNotNull('TFoo in symbol table',
      Prog.SymbolTable.FindType('TFoo'));
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_ClassType_IsClass;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcSimpleClass);
  try
    AssertEquals('TFoo is tyClass',
      Ord(tyClass),
      Ord(Prog.SymbolTable.FindType('TFoo').Kind));
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_ClassVar_HasClassType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin end.
        ''');
  try
    AssertEquals('F is tyClass',
      Ord(tyClass),
      Ord(TVarDecl(Prog.Block.Decls[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_Constructor_TypeIsClass;
var
  Prog:   TProgram;
  Assign: TAssignment;
  MC:     TMethodCallExpr;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create()
        end.
        ''');
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    MC     := TMethodCallExpr(Assign.Expr);
    AssertTrue('IsConstructorCall', MC.IsConstructorCall);
    AssertEquals('ResolvedType is tyClass',
      Ord(tyClass), Ord(MC.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_ClassFieldAssign_OK;
begin
  AnalyseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F.X := 42
        end.
        '''
  ).Free();
end;

procedure TClassTests.TestSemantic_ClassFieldAssign_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F.X := 'hello'
        end.
        ''');
end;

procedure TClassTests.TestSemantic_ClassFieldAccess_TypeIsFieldType;
var
  Prog:   TProgram;
  Access: TFieldAccessExpr;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo; N: Integer;
        begin
          N := F.X
        end.
        ''');
  try
    Access := TFieldAccessExpr(TAssignment(Prog.Block.Stmts[0]).Expr);
    AssertTrue('IsClassAccess', Access.IsClassAccess);
    AssertEquals('Field access type',
      Ord(tyInteger), Ord(Access.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_ClassFieldAccess_UnknownField_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo; N: Integer;
        begin
          N := F.Z
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ Code generation                                                     }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestCodegen_ClassVar_HasPointerAlloc;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin end.
        ''');
  { Program-level class var F is a data-section global pointer slot }
  AssertTrue('data decl for F', Pos('$F', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassVar_ZeroInit;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin end.
        ''');
  { Program-level class var F is zero-initialised via data section entry }
  AssertTrue('zero init via data section', Pos('data $F = { l 0 }', IR) > 0);
end;

procedure TClassTests.TestCodegen_Constructor_CallsClassAlloc;
var
  IR: string;
begin
  { Class instances are allocated via _ClassAlloc, which prefixes an 8-byte
    refcount header before the user pointer so every Blaise class carries the
    bookkeeping needed for ARC.  The user pointer still points at the vptr
    (offset 0); field offsets are unchanged. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create()
        end.
        ''');
  AssertTrue('calls _ClassAlloc', Pos('call $_ClassAlloc', IR) > 0);
  AssertTrue('does not call calloc directly', Pos('call $calloc', IR) < 0);
  AssertTrue('stores pointer', Pos('storel', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassFieldStore_LoadsPointer;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F.X := 42
        end.
        ''');
  { F is a program-level global — loaded via $F }
  AssertTrue('loads pointer', Pos('loadl $F', IR) > 0);
  AssertTrue('stores value',  Pos('storew', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassFieldLoad_LoadsPointer;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo; N: Integer;
        begin
          N := F.X
        end.
        ''');
  { F is a program-level global — loaded via $F }
  AssertTrue('loads pointer', Pos('loadl $F', IR) > 0);
  AssertTrue('loads field',   Pos('loadw', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Separate method implementations                                      }
{ ------------------------------------------------------------------ }

const
  SrcSeparateImpl =
    '''
        program P;
        type
          TFoo = class
            X: Integer;
            procedure SetX(AVal: Integer);
          end;
        procedure TFoo.SetX(AVal: Integer);
        begin
          Self.X := AVal
        end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.SetX(42)
        end.
        ''';

procedure TClassTests.TestParse_SeparateImpl_ForwardDeclNoBody;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcSeparateImpl);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[0]);
    AssertNull('class method forward decl has no body', MD.Body);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestParse_SeparateImpl_QualifiedName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcSeparateImpl);
  try
    { First ProcDecl in block is the standalone impl }
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('owner type name', 'TFoo', MD.OwnerTypeName);
    AssertEquals('method name', 'SetX', MD.Name);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_SeparateImpl_OK;
begin
  AnalyseSrc(SrcSeparateImpl).Free();
end;

procedure TClassTests.TestSemantic_MethodBody_AccessesProgramGlobal;
begin
  { Regression for issue #43: a class method body must be able to resolve
    program-level globals declared above the class type. }
  AnalyseSrc(
    '''
        program P;
        var gValue: Integer;
        type
          TFoo = class
            function GetValue: Integer;
          end;
        function TFoo.GetValue: Integer;
        begin
          Result := gValue
        end;
        begin end.
        ''').Free();
end;

procedure TClassTests.TestCodegen_MethodBody_ReadsProgramGlobal;
var
  IR: string;
begin
  { Regression for issue #43: method body codegen must emit a load of the
    program-level global via its $-prefixed data symbol. }
  IR := GenIR(
    '''
        program P;
        var gValue: Integer;
        type
          TFoo = class
            function GetValue: Integer;
          end;
        function TFoo.GetValue: Integer;
        begin
          Result := gValue
        end;
        begin end.
        ''');
  AssertTrue('method loads global $gValue', Pos('loadw $gValue', IR) > 0);
end;

procedure TClassTests.TestSemantic_MethodDeclaredNotImplemented_RaisesError;
begin
  { Regression for issue #161: a concrete class method that is declared but
    never implemented must be rejected at compile time.  Previously the
    program compiled and only failed at load time with
    `undefined symbol: TForward_work`. }
  AnalyseExpectError(
    '''
        program P;
        type
          TForward = class
            procedure Work;
          end;
        var F: TForward;
        begin
          F := TForward.Create();
          F.Work()
        end.
        ''');
end;

procedure TClassTests.TestSemantic_AbstractMethod_NoImpl_OK;
begin
  { An abstract method legitimately has no implementation — the missing-body
    diagnostic (issue #161) must not fire for it. }
  AnalyseSrc(
    '''
        program P;
        type
          TBase = class
            procedure Work; virtual; abstract;
          end;
        begin
        end.
        ''').Free();
end;

procedure TClassTests.TestSemantic_ExternalMethod_NoImpl_OK;
begin
  { An external method is satisfied by a foreign symbol and carries no Blaise
    body — the missing-body diagnostic (issue #161) must not fire for it. }
  AnalyseSrc(
    '''
        program P;
        type
          TWrap = class
            function Peek: Integer; external 'peek';
          end;
        begin
        end.
        ''').Free();
end;

procedure TClassTests.TestCodegen_SeparateImpl_EmitsMethod;
var IR: string;
begin
  IR := GenIR(SrcSeparateImpl);
  { The method body must appear in the IR as TFoo_SetX }
  AssertTrue('TFoo_SetX emitted', Pos('$TFoo_SetX', IR) > 0);
  { The call site must use it }
  AssertTrue('call to TFoo_SetX', Pos('call $TFoo_SetX', IR) > 0);
end;

const
  SrcMethodCaseInsensitive =
    '''
        program P;
        type
          TFoo = class
            X: Integer;
            procedure SetX(AVal: Integer);
          end;
        procedure TFoo.SetX(AVal: Integer);
        begin
          Self.X := AVal
        end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.setx(42)
        end.
        ''';

procedure TClassTests.TestCodegen_MethodCall_CaseInsensitive;
var IR: string;
begin
  IR := GenIR(SrcMethodCaseInsensitive);
  AssertTrue('call uses declared name TFoo_SetX',
    Pos('call $TFoo_SetX', IR) > 0);
  AssertTrue('no lowercase TFoo_setx in IR',
    Pos('$TFoo_setx', IR) < 0);
end;

{ ------------------------------------------------------------------ }
{ Free built-in                                                        }
{ ------------------------------------------------------------------ }

const
  SrcFree =
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.Free()
        end.
        ''';

procedure TClassTests.TestSemantic_Free_OK;
begin
  AnalyseSrc(SrcFree).Free();
end;

procedure TClassTests.TestCodegen_Free_CallsClassRelease;
var IR: string;
begin
  { Obj.Free is a sanctioned synonym for immediate release under ARC: it
    decrements the refcount (freeing the block and running the field
    cleanup fn at zero) and nil-outs the slot so the scope-exit release
    becomes a no-op. }
  IR := GenIR(SrcFree);
  AssertTrue('calls _ClassRelease',     Pos('call $_ClassRelease', IR) > 0);
  AssertTrue('nil-outs slot after Free', (Pos('storel 0, %_var_', IR) > 0) or (Pos('storel 0, $', IR) > 0));
  AssertTrue('does not call C free() directly', Pos('call $free(', IR) < 0);
end;

{ ------------------------------------------------------------------ }
{ ARC on class variables and fields                                    }
{ ------------------------------------------------------------------ }

const
  SrcArcBasic =
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create()
        end.
        ''';

  SrcArcFieldClass =
    '''
        program P;
        type
          TInner = class
            V: Integer;
          end;
          TOuter = class
            Child: TInner;
          end;
        var A, B: TOuter;
        begin
          A := TOuter.Create();
          B := TOuter.Create();
          A.Child := TInner.Create();
          B.Child := A.Child
        end.
        ''';

procedure TClassTests.TestCodegen_ClassVarAssign_InsertsAddRefRelease;
var IR: string;
begin
  IR := GenIR(SrcArcBasic);
  AssertTrue('addref on new class RHS',
    Pos('call $_ClassAddRef', IR) > 0);
  AssertTrue('release on old class LHS',
    Pos('call $_ClassRelease', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassVarAssignNil_EmitsRelease;
const
  Src = '''
      program P;
      type TFoo = class end;
      var F: TFoo;
      begin
        F := TFoo.Create();
        F := nil
      end.
      ''';
var
  IR: string;
  P1, P2, P3: Integer;
begin
  IR := GenIR(Src);
  P1 := Pos('call $_ClassRelease', IR);
  AssertTrue('1st _ClassRelease (Create assignment)', P1 > 0);
  P2 := Pos('call $_ClassRelease', Copy(IR, P1 + 20, MaxInt));
  AssertTrue('2nd _ClassRelease (F := nil must release old value)', P2 > 0);
  P3 := Pos('call $_ClassRelease', Copy(IR, P1 + 20 + P2 + 20, MaxInt));
  AssertTrue('3rd _ClassRelease (scope-exit cleanup)', P3 > 0);
end;

procedure TClassTests.TestCodegen_ClassVarScopeExit_EmitsRelease;
var IR: string;
begin
  { The variable F must be released at block exit (main_exit label).
    Emitted as part of EmitArcCleanup. }
  IR := GenIR(SrcArcBasic);
  AssertTrue('release at scope exit',
    Pos('call $_ClassRelease', IR) > 0);
  { Two releases: one from overwriting the nil slot during F := Create
    (old=nil, noop at runtime but still emitted), one at scope exit. }
  AssertTrue('at least two class releases emitted',
    (Pos('call $_ClassRelease',
         Copy(IR, Pos('call $_ClassRelease', IR) + 1, MaxInt)) > 0));
end;

procedure TClassTests.TestCodegen_ClassFieldAssign_InsertsAddRefRelease;
var IR: string;
begin
  { A.Child := TInner.Create should load old A.Child, release it, addref the
    new Inner, and store.  The insertion pattern mirrors variable ARC but
    targets a heap-field slot rather than a local. }
  IR := GenIR(SrcArcFieldClass);
  AssertTrue('class field assignment addrefs',
    Pos('call $_ClassAddRef', IR) > 0);
  AssertTrue('class field assignment releases old',
    Pos('call $_ClassRelease', IR) > 0);
end;

procedure TClassTests.TestCodegen_FieldCleanup_EmittedPerClass;
var IR: string;
begin
  IR := GenIR(SrcArcFieldClass);
  AssertTrue('cleanup fn emitted for TInner',
    Pos('function $_FieldCleanup_TInner', IR) > 0);
  AssertTrue('cleanup fn emitted for TOuter',
    Pos('function $_FieldCleanup_TOuter', IR) > 0);
end;

procedure TClassTests.TestCodegen_FieldCleanup_ReleasesClassField;
var IR, OuterBody: string;
  StartPos, EndPos: Integer;
begin
  { TOuter.Child is a TInner — its cleanup fn must release the field.
    Isolate _FieldCleanup_TOuter's body and assert a _ClassRelease appears
    inside it (not in some sibling function). }
  IR       := GenIR(SrcArcFieldClass);
  StartPos := Pos('function $_FieldCleanup_TOuter', IR);
  AssertTrue('TOuter cleanup present', StartPos > 0);
  OuterBody := Copy(IR, StartPos, MaxInt);
  EndPos   := Pos(#10 + '}', OuterBody);
  AssertTrue('TOuter cleanup has end', EndPos > 0);
  OuterBody := Copy(OuterBody, 1, EndPos);
  AssertTrue('TOuter cleanup releases class-typed field',
    Pos('call $_ClassRelease', OuterBody) > 0);
end;

procedure TClassTests.TestCodegen_FieldCleanup_OverloadedDestroy_CallsMangledSymbol;
var IR: string;
begin
  { When Destroy is overloaded, the destructor symbol is emitted with
    the overload-mangled suffix (e.g. '$TFoo_Destroy_D_').  The
    field-cleanup helper must call that same symbol; previously it
    hard-coded the bare '<Class>_Destroy' which was never emitted,
    leaving the binary with an undefined-symbol link error. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
          public
            Buf: string;
            destructor Destroy(why: Integer); overload;
            destructor Destroy; overload;
          end;
        destructor TFoo.Destroy(why: Integer); begin end;
        destructor TFoo.Destroy; begin end;
        var f: TFoo;
        begin f := TFoo.Create(); f.Free() end.
        '''
  );
  AssertTrue('Overloaded no-arg Destroy emits the mangled symbol',
    Pos('function $TFoo_Destroy_D_(', IR) > 0);
  AssertTrue('_FieldCleanup_TFoo calls the mangled destructor',
    Pos('call $TFoo_Destroy_D_(l %self)', IR) > 0);
  AssertFalse('_FieldCleanup_TFoo MUST NOT call the bare unmangled label',
    Pos('call $TFoo_Destroy(l %self)', IR) > 0);
end;

procedure TClassTests.TestCodegen_Constructor_NoArgs_StoresVTable;
var IR: string;
begin
  { TFoo.Create() (no args) — goes through TMethodCallExpr.IsConstructorCall.
    A class with a virtual method must get its vtable pointer stored at
    offset 0 immediately after _ClassAlloc. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            procedure Done; virtual;
          end;
        procedure TFoo.Done; begin end;
        var F: TFoo;
        begin
          F := TFoo.Create()
        end.
        ''');
  AssertTrue('no-arg ctor stores vtable', Pos('storel $vtable_TFoo', IR) > 0);
end;

procedure TClassTests.TestCodegen_Constructor_WithArgs_StoresVTable;
var IR: string;
begin
  { TFoo.Create(N) (args) — goes through TMethodCallExpr.IsConstructorCall.
    The vtable pointer must still be stored at offset 0 even when a
    user-defined Create method is called with arguments. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            FN: Integer;
            procedure Create(N: Integer);
            procedure Done; virtual;
          end;
        procedure TFoo.Create(N: Integer);
        begin FN := N end;
        procedure TFoo.Done; begin end;
        var F: TFoo;
        begin
          F := TFoo.Create(42)
        end.
        ''');
  AssertTrue('with-arg ctor stores vtable', Pos('storel $vtable_TFoo', IR) > 0);
end;

procedure TClassTests.TestCodegen_Constructor_WithArgs_ExactlyOneAddRef;
var
  IR: string;
  AddRefCount: Integer;
  P: Integer;
begin
  { TFoo.Create(N) must produce exactly one _ClassAddRef — from the
    assignment site.  The constructor path itself must NOT add a second. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            FN: Integer;
            constructor Create(N: Integer);
          end;
        constructor TFoo.Create(N: Integer);
        begin FN := N end;
        var F: TFoo;
        begin
          F := TFoo.Create(42)
        end.
        ''');
  AddRefCount := 0;
  P := 0;
  repeat
    P := PosEx('_ClassAddRef', IR, P);
    if P >= 0 then begin Inc(AddRefCount); Inc(P) end;
  until P < 0;
  AssertEquals('exactly one _ClassAddRef for constructor-with-args', 1, AddRefCount);
end;

{ ------------------------------------------------------------------ }
{ ARC on method string parameters                                      }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestCodegen_MethodStringParam_AddRefOnEntry;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'                              + LineEnding +
    'type'                                    + LineEnding +
    '  TFoo = class'                          + LineEnding +
    '    procedure Bar(S: string);'           + LineEnding +
    '  end;'                                  + LineEnding +
    'procedure TFoo.Bar(S: string);'          + LineEnding +
    'begin end;'                              + LineEnding +
    'begin'                                   + LineEnding +
    'end.');
  AssertTrue('method string param must AddRef on entry',
    Pos('call $_StringAddRef', IR) > 0);
end;

procedure TClassTests.TestCodegen_MethodStringParam_ReleaseOnExit;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'                              + LineEnding +
    'type'                                    + LineEnding +
    '  TFoo = class'                          + LineEnding +
    '    procedure Bar(S: string);'           + LineEnding +
    '  end;'                                  + LineEnding +
    'procedure TFoo.Bar(S: string);'          + LineEnding +
    'begin end;'                              + LineEnding +
    'begin'                                   + LineEnding +
    'end.');
  AssertTrue('method string param must Release on exit',
    Pos('call $_StringRelease', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ 0-based string semantic analysis                                     }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestSemantic_ConstructorPrefix_CreateFmt;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(
    'program P;'                                      + LineEnding +
    'type'                                            + LineEnding +
    '  TFoo = class'                                  + LineEnding +
    '    constructor CreateFmt(S: string; N: Integer);' + LineEnding +
    '  end;'                                          + LineEnding +
    'constructor TFoo.CreateFmt(S: string; N: Integer);' + LineEnding +
    'begin end;'                                      + LineEnding +
    'var F: TFoo;'                                    + LineEnding +
    'begin'                                           + LineEnding +
    '  F := TFoo.CreateFmt(''hello'', 42)'            + LineEnding +
    'end.');
  try
    AssertTrue('program parsed and analysed without error', Prog <> nil);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_PointerTypeAlias;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TFoo = class'                              + LineEnding +
    '    X: Integer;'                             + LineEnding +
    '  end;'                                      + LineEnding +
    '  PFoo = ^TFoo;'                             + LineEnding +
    'begin'                                       + LineEnding +
    'end.');
  try
    AssertTrue('pointer type alias parsed OK', Prog <> nil);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_MetaclassAlias;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TFoo = class'                              + LineEnding +
    '  end;'                                      + LineEnding +
    '  TFooClass = class of TFoo;'                + LineEnding +
    'begin'                                       + LineEnding +
    'end.');
  try
    AssertTrue('metaclass alias parsed OK', Prog <> nil);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Forward class declarations                                          }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestSemantic_ForwardClass_CompletedByFullDecl;
var
  Prog: TProgram;
begin
  { A bare `TFoo = class;` forward stub, completed by the full declaration
    later in the same type section, must not be a duplicate-type error. }
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TFoo = class;
          TFoo = class
            X: Integer;
          end;
        begin
        end.
        ''');
  try
    AssertTrue('forward class completed by full decl analyses OK', Prog <> nil);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_ForwardClass_MutualReference;
var
  Prog: TProgram;
begin
  { The point of a forward decl: a class declared between the forward and the
    full declaration can name the forward-declared type. }
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TFoo = class;
          TBar = class
            Foo: TFoo;
          end;
          TFoo = class
            Bar: TBar;
          end;
        begin
        end.
        ''');
  try
    AssertTrue('mutual class reference via forward decl analyses OK',
      Prog <> nil);
  finally
    Prog.Free();
  end;
end;

procedure TClassTests.TestSemantic_ForwardClass_Unresolved_RaisesError;
begin
  { A forward never completed in the scope is an error. }
  AnalyseExpectError(
    '''
        program P;
        type
          TFoo = class;
        begin
        end.
        ''');
end;

procedure TClassTests.TestSemantic_ForwardClass_DoubleForward_RaisesError;
begin
  { The same type may be forward-declared only once. }
  AnalyseExpectError(
    '''
        program P;
        type
          TFoo = class;
          TFoo = class;
          TFoo = class
            X: Integer;
          end;
        begin
        end.
        ''');
end;

procedure TClassTests.TestCodegen_ForwardClass_SingleVTable;
var
  IR:    string;
  Count: Integer;
  P:     Integer;
begin
  { The forward stub is dropped after semantic analysis, so codegen must emit
    the class's vtable exactly once — a second emission would be a duplicate
    data symbol and fail to link. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class;
          TFoo = class
            X: Integer;
          end;
        begin
        end.
        ''');
  Count := 0;
  P := 0;
  repeat
    P := PosEx('data $vtable_TFoo', IR, P);
    if P >= 0 then begin Inc(Count); Inc(P) end;
  until P < 0;
  AssertEquals('vtable_TFoo emitted exactly once', 1, Count);
end;

procedure TClassTests.TestCodegen_ForwardClass_CaseDifferentSpelling_FieldCleanupConsistent;
var
  IR: string;
begin
  { Regression for issue #162: when the forward declaration and its completing
    full declaration differ only in case (TState vs Tstate), the shared class
    descriptor must adopt the completing spelling so a class's _FieldCleanup is
    referenced under the same name it is defined with.  Previously the
    instantiation site read the forward spelling and referenced
    $_FieldCleanup_TState while the definition was emitted as
    $_FieldCleanup_Tstate — an undefined-symbol link failure. }
  IR := GenIR(
    '''
        program P;
        type
          TState = class;
          Tstate = class
            FName: string;
          end;
        var S: Tstate;
        begin
          S := Tstate.Create()
        end.
        ''');
  AssertTrue('_FieldCleanup defined+referenced under the completing spelling',
    Pos('$_FieldCleanup_Tstate', IR) > 0);
  AssertTrue('no dangling forward-spelling $_FieldCleanup_TState reference',
    Pos('$_FieldCleanup_TState', IR) < 0);
end;

procedure TClassTests.TestCodegen_AliasConstructor_RunsUserCtor;
var
  IR: string;
begin
  { type TAlias = TThing; TAlias.Create() must resolve THING's user
    constructor.  The lookup used to go through the SYMBOL name ('TAlias',
    no method table), silently fell back to the implicit default ctor, and
    the object came back allocated but unconstructed (found when
    reactor.tests aliased the per-OS reactor class for GH #204). }
  IR := GenIR(
    '''
        program P;
        type
          TThing = class
            X: Integer;
            constructor Create();
          end;
          TAlias = TThing;
        constructor TThing.Create();
        begin
          X := 7;
        end;
        var A: TThing;
        begin
          A := TAlias.Create()
        end.
        ''');
  AssertTrue('user ctor body called through the alias',
    Pos('call $TThing_Create', IR) > 0);
end;

initialization
  RegisterTest(TClassTests);

end.
