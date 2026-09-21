{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.records;

interface

uses
  blaise.testing, strutils,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TRecordTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer — new keywords                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Type_Keyword;
    procedure TestLexer_Record_Keyword;

    { ------------------------------------------------------------------ }
    { Parser — type section and record body                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_TypeSection_Exists;
    procedure TestParse_RecordType_Name;
    procedure TestParse_RecordType_SingleField;
    procedure TestParse_RecordType_MultipleFields;
    procedure TestParse_RecordType_MultiNameField;
    { Nested type declarations (GH #175 Stage 1) — a `type` section inside a
      record body, mirroring the class form. }
    procedure TestParse_RecordNestedType_Record;
    procedure TestParse_RecordNestedType_KeepsOuterMembers;
    procedure TestParse_RecordNestedType_TakesSectionVisibility;
    procedure TestParse_VarOfRecordType;
    procedure TestParse_FieldAssignment;
    procedure TestParse_FieldAccessInExpr;

    { ------------------------------------------------------------------ }
    { Semantic — record type resolution                                   }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_RecordType_Registered;
    procedure TestSemantic_RecordType_FieldsResolved;
    procedure TestSemantic_RecordVar_HasRecordType;
    procedure TestSemantic_FieldAssign_OK;
    procedure TestSemantic_FieldAssign_TypeMismatch_RaisesError;
    procedure TestSemantic_FieldAccess_TypeIsFieldType;
    procedure TestSemantic_FieldAccess_UnknownField_RaisesError;
    procedure TestSemantic_FieldAccess_OnNonRecord_RaisesError;

    { ------------------------------------------------------------------ }
    { Code generation                                                     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_RecordVar_HasAlloc;
    procedure TestCodegen_FieldStore_EmitsOffset;
    procedure TestCodegen_FieldLoad_EmitsOffset;
    { Real-typed literals and double sub-expressions land in the SSA
      at double width; storing them into a Single record field needs
      an explicit narrowing or the IR is type-mismatched and the
      assembler refuses to lower it. }
    procedure TestCodegen_FieldStore_DoubleLiteralToSingleField_Trunced;
    procedure TestCodegen_FieldStore_SingleSrcToDoubleField_Extended;
    procedure TestCodegen_TwoIntFields_CorrectSize;
    procedure TestCodegen_StringField_CorrectSize;

    { ------------------------------------------------------------------ }
    { Byte sizing and record packing                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_FourByteRecord_TotalSizeIs4;
    procedure TestSemantic_ByteThenInteger_AlignsInteger;
    procedure TestSemantic_ByteFieldOffsets_Are0123;
    procedure TestCodegen_SizeOfByte_Is1;
    procedure TestCodegen_SizeOfFourByteRecord_Is4;
    { Single is a 4-byte IEEE-754 float — alignment 4, not 8.  A record
      of three back-to-back Single fields totals 12 bytes, not 24. }
    procedure TestSemantic_ThreeSingleRecord_TotalSizeIs12;

    { ------------------------------------------------------------------ }
    { By-value record param ARC — managed fields                          }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_RecordByValParam_StringField_AddRefRelease;
    procedure TestCodegen_RecordByValParam_DynArrayField_AddRefRelease;
    procedure TestCodegen_RecordByValParam_ConstParam_NoARC;
    procedure TestCodegen_RecordByValArg_CallResultTemp_CleansFields;
    procedure TestCodegen_RecordByValArg_VarRef_DoesNotClean;
    procedure TestCodegen_RecordByValArg_NestedManagedField_Recurses;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TRecordTests.ParseSrc(const ASrc: string): TProgram;
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

function TRecordTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TRecordTests.GenIR(const ASrc: string): string;
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

procedure TRecordTests.AnalyseExpectError(const ASrc: string);
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

procedure TRecordTests.TestLexer_Type_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('type');
  try
    T := L.Next();
    AssertEquals('type token', Ord(tkType), Ord(T.Kind));
  finally
    L.Free();
  end;
end;

procedure TRecordTests.TestLexer_Record_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('record');
  try
    T := L.Next();
    AssertEquals('record token', Ord(tkRecord), Ord(T.Kind));
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TRecordTests.TestParse_TypeSection_Exists;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        begin end.
        ''');
  try
    AssertEquals('1 type decl', 1, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_RecordType_Name;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        begin end.
        ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    AssertEquals('Type name', 'TPoint', TD.Name);
    AssertTrue('Is TRecordTypeDef', TD.Def is TRecordTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_RecordType_SingleField;
var
  Prog: TProgram;
  Rec:  TRecordTypeDef;
  Fld:  TFieldDecl;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        begin end.
        ''');
  try
    Rec := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('1 field', 1, Rec.Fields.Count);
    Fld := TFieldDecl(Rec.Fields.Items[0]);
    AssertEquals('Field name', 'X', Fld.Names.Strings[0]);
    AssertEquals('Field type', 'Integer', Fld.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_RecordType_MultipleFields;
var
  Prog: TProgram;
  Rec:  TRecordTypeDef;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
            Y: Integer;
          end;
        begin end.
        ''');
  try
    Rec := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('2 fields', 2, Rec.Fields.Count);
    AssertEquals('First field', 'X', TFieldDecl(Rec.Fields.Items[0]).Names.Strings[0]);
    AssertEquals('Second field', 'Y', TFieldDecl(Rec.Fields.Items[1]).Names.Strings[0]);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  Nested type declarations — GH #175 Stage 1 (parser)                 }
{ ------------------------------------------------------------------ }

procedure TRecordTests.TestParse_RecordNestedType_Record;
var
  Prog: TProgram;
  Rec:  TRecordTypeDef;
  NTD:  TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TOuter = record
            type
              TInner = record
                F: Integer;
              end;
          end;
        begin end.
        ''');
  try
    Rec := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('1 nested type', 1, Rec.NestedTypeDecls.Count);
    NTD := TTypeDecl(Rec.NestedTypeDecls.Items[0]);
    AssertEquals('nested type name', 'TInner', NTD.Name);
    AssertTrue('nested def is a record', NTD.Def is TRecordTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_RecordNestedType_KeepsOuterMembers;
var
  Prog: TProgram;
  Rec:  TRecordTypeDef;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TOuter = record
            type
              TInner = record
                F: Integer;
              end;
            X: Integer;
          end;
        begin end.
        ''');
  try
    Rec := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('1 nested type', 1, Rec.NestedTypeDecls.Count);
    AssertEquals('outer field survived', 1, Rec.Fields.Count);
    AssertEquals('outer field name', 'X',
      TFieldDecl(Rec.Fields.Items[0]).Names[0]);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_RecordNestedType_TakesSectionVisibility;
var
  Prog: TProgram;
  Rec:  TRecordTypeDef;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TOuter = record
          strict private
            type
              THidden = record
                F: Integer;
              end;
          public
            type
              TShown = record
                G: Integer;
              end;
          end;
        begin end.
        ''');
  try
    Rec := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('2 nested types', 2, Rec.NestedTypeDecls.Count);
    AssertTrue('THidden is strict private',
      TTypeDecl(Rec.NestedTypeDecls.Items[0]).Visibility = mvStrictPrivate);
    AssertTrue('TShown is public',
      TTypeDecl(Rec.NestedTypeDecls.Items[1]).Visibility = mvPublic);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_RecordType_MultiNameField;
var
  Prog: TProgram;
  Rec:  TRecordTypeDef;
  Fld:  TFieldDecl;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X, Y: Integer;
          end;
        begin end.
        ''');
  try
    Rec := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('1 field group', 1, Rec.Fields.Count);
    Fld := TFieldDecl(Rec.Fields.Items[0]);
    AssertEquals('2 names', 2, Fld.Names.Count);
    AssertEquals('First',  'X', Fld.Names.Strings[0]);
    AssertEquals('Second', 'Y', Fld.Names.Strings[1]);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_VarOfRecordType;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var P: TPoint;
        begin end.
        ''');
  try
    AssertEquals('1 var', 1, Prog.Block.Decls.Count);
    Decl := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertEquals('Var name', 'P', Decl.Names.Strings[0]);
    AssertEquals('Var type', 'TPoint', Decl.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_FieldAssignment;
var
  Prog: TProgram;
  Stmt: TFieldAssignment;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint;
        begin
          Pt.X := 10
        end.
        ''');
  try
    AssertEquals('1 stmt', 1, Prog.Block.Stmts.Count);
    AssertTrue('Is TFieldAssignment',
      Prog.Block.Stmts.Items[0] is TFieldAssignment);
    Stmt := TFieldAssignment(Prog.Block.Stmts.Items[0]);
    AssertEquals('Record var', 'Pt',  Stmt.RecordName);
    AssertEquals('Field name', 'X',   Stmt.FieldName);
    AssertTrue('Expr is TIntLiteral', Stmt.Expr is TIntLiteral);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestParse_FieldAccessInExpr;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := ParseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint; N: Integer;
        begin
          N := Pt.X + 1
        end.
        ''');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertTrue('Left is TFieldAccessExpr', Bin.Left is TFieldAccessExpr);
    AssertEquals('Record', 'Pt', TFieldAccessExpr(Bin.Left).RecordName);
    AssertEquals('Field',  'X',  TFieldAccessExpr(Bin.Left).FieldName);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TRecordTests.TestSemantic_RecordType_Registered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        begin end.
        ''');
  try
    AssertNotNull('TPoint in symbol table',
      Prog.SymbolTable.FindType('TPoint'));
    AssertEquals('TPoint is tyRecord',
      Ord(tyRecord),
      Ord(Prog.SymbolTable.FindType('TPoint').Kind));
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestSemantic_RecordType_FieldsResolved;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
            Y: Integer;
          end;
        begin end.
        ''');
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TPoint'));
    AssertEquals('2 fields', 2, RT.Fields.Count);
    AssertEquals('X type',
      Ord(tyInteger), Ord(TFieldInfo(RT.Fields.Items[0]).TypeDesc.Kind));
    AssertEquals('Y type',
      Ord(tyInteger), Ord(TFieldInfo(RT.Fields.Items[1]).TypeDesc.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestSemantic_RecordVar_HasRecordType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint;
        begin end.
        ''');
  try
    AssertEquals('Var is tyRecord',
      Ord(tyRecord),
      Ord(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestSemantic_FieldAssign_OK;
begin
  AnalyseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint;
        begin
          Pt.X := 42
        end.
        '''
  ).Free();
end;

procedure TRecordTests.TestSemantic_FieldAssign_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint;
        begin
          Pt.X := 'hello'
        end.
        ''');
end;

procedure TRecordTests.TestSemantic_FieldAccess_TypeIsFieldType;
var
  Prog:   TProgram;
  Access: TFieldAccessExpr;
begin
  Prog := AnalyseSrc(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint; N: Integer;
        begin
          N := Pt.X
        end.
        ''');
  try
    Access := TFieldAccessExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Field access type',
      Ord(tyInteger), Ord(Access.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestSemantic_FieldAccess_UnknownField_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint; N: Integer;
        begin
          N := Pt.Z
        end.
        ''');
end;

procedure TRecordTests.TestSemantic_FieldAccess_OnNonRecord_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        begin
          N := N.X
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ Code generation                                                     }
{ ------------------------------------------------------------------ }

procedure TRecordTests.TestCodegen_RecordVar_HasAlloc;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint;
        begin end.
        ''');
  { Program-level record var Pt is a data-section global }
  AssertTrue('data decl for Pt', Pos('$Pt', IR) > 0);
end;

procedure TRecordTests.TestCodegen_FieldStore_EmitsOffset;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint;
        begin
          Pt.X := 10
        end.
        ''');
  AssertTrue('storew in IR', Pos('storew', IR) > 0);
end;

procedure TRecordTests.TestCodegen_FieldLoad_EmitsOffset;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TPoint = record
            X: Integer;
          end;
        var Pt: TPoint; N: Integer;
        begin
          N := Pt.X
        end.
        ''');
  AssertTrue('loadw in IR', Pos('loadw', IR) > 0);
end;

procedure TRecordTests.TestCodegen_FieldStore_DoubleLiteralToSingleField_Trunced;
var IR: string;
begin
  { Assigning a real-typed literal to a Single record field must emit a
    narrowing before the store; previously the IR contained
    'stores d_<lit>, ...' which the assembler rejected as a type
    mismatch on the operand width. }
  IR := GenIR(
    '''
        program P;
        type TRec = record v: Single; end;
        var r: TRec;
        begin r.v := 1.5 end.
        ''');
  AssertTrue('field-store narrows double literal to single (truncd)',
    Pos('truncd', IR) > 0);
  { The bug shape: a double-typed literal stored straight into the
    Single field's storage slot. }
  AssertFalse('field-store MUST NOT directly store a double into a single slot',
    Pos('stores d_', IR) > 0);
end;

procedure TRecordTests.TestCodegen_FieldStore_SingleSrcToDoubleField_Extended;
var IR: string;
begin
  { Symmetric direction: a Single value stored into a Double record
    field must be extended first.  Verifies the coercion is bidirectional
    and not just a half-fix. }
  IR := GenIR(
    '''
        program P;
        type TRec = record v: Double; end;
        var r: TRec; s: Single;
        begin s := 0.5; r.v := s end.
        ''');
  AssertTrue('field-store widens single source to double (exts)',
    Pos(' =d exts ', IR) > 0);
end;

procedure TRecordTests.TestCodegen_TwoIntFields_CorrectSize;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TRect = record
            L: Integer;
            T: Integer;
          end;
        var R: TRect;
        begin end.
        ''');
  { Two Integer fields = 8 bytes total; program-level record uses data section }
  AssertTrue('8-byte record in data section', Pos('z 8', IR) > 0);
end;

procedure TRecordTests.TestCodegen_StringField_CorrectSize;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TPerson = record
            Name: string;
          end;
        var Person: TPerson;
        begin end.
        ''');
  { One string field = 8 bytes; program-level record uses data section }
  AssertTrue('8-byte record in data section', Pos('z 8', IR) > 0);
end;

procedure TRecordTests.TestSemantic_FourByteRecord_TotalSizeIs4;
const
  Src =
    '''
        program P;
        type
          TFourBytes = record
            A: Byte;
            B: Byte;
            C: Byte;
            D: Byte;
          end;
        var R: TFourBytes;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('record of four Byte fields totals 4 bytes',
      4, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestSemantic_ByteThenInteger_AlignsInteger;
const
  Src =
    '''
        program P;
        type
          TMixed = record
            A: Byte;
            B: Integer;
          end;
        var R: TMixed;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  F:    TFieldInfo;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    F  := RT.FindField('B');
    AssertEquals('Integer after Byte aligns to offset 4', 4, F.Offset);
    AssertEquals('record total size is 8 (1 byte + 3 pad + 4)', 8, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestSemantic_ByteFieldOffsets_Are0123;
const
  Src =
    '''
        program P;
        type
          TFourBytes = record
            A: Byte;
            B: Byte;
            C: Byte;
            D: Byte;
          end;
        var R: TFourBytes;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('A at 0', 0, RT.FindField('A').Offset);
    AssertEquals('B at 1', 1, RT.FindField('B').Offset);
    AssertEquals('C at 2', 2, RT.FindField('C').Offset);
    AssertEquals('D at 3', 3, RT.FindField('D').Offset);
  finally
    Prog.Free();
  end;
end;

procedure TRecordTests.TestCodegen_SizeOfByte_Is1;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var N: Integer;
        begin
          N := SizeOf(Byte)
        end.
        ''');
  { SizeOf(Byte) should be a compile-time literal 1, not 4 }
  AssertTrue('SizeOf(Byte) emits copy 1', Pos('copy 1', IR) > 0);
  AssertFalse('SizeOf(Byte) does not emit copy 4', Pos('copy 4', IR) > 0);
end;

procedure TRecordTests.TestCodegen_SizeOfFourByteRecord_Is4;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TFourBytes = record
            A: Byte;
            B: Byte;
            C: Byte;
            D: Byte;
          end;
        var N: Integer;
        begin
          N := SizeOf(TFourBytes)
        end.
        ''');
  AssertTrue('SizeOf(TFourBytes) emits copy 4', Pos('copy 4', IR) > 0);
  AssertFalse('not 16', Pos('copy 16', IR) > 0);
end;

procedure TRecordTests.TestSemantic_ThreeSingleRecord_TotalSizeIs12;
const
  Src =
    '''
        program P;
        type
          TVec3 = record
            X: Single;
            Y: Single;
            Z: Single;
          end;
        var V: TVec3;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('record of three Single fields totals 12 bytes (4-byte align)',
      12, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ By-value record param ARC                                           }
{ ------------------------------------------------------------------ }

{ When a record with a managed (string/dynarray/interface/class) field
  is passed by value, the callee operates on QBE's materialised
  aggregate.  The callee must AddRef each managed leaf on entry and
  Release each on exit so that in-callee field reassignment's
  release-old does not free the caller's shared heap data. }
procedure TRecordTests.TestCodegen_RecordByValParam_StringField_AddRefRelease;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TR = record S: string; end;
        procedure Mut(R: TR); begin R.S := 'x'; end;
        var W: TR;
        begin W.S := ''; Mut(W) end.
        ''');
  AssertTrue('addref on entry to Mut', Pos('_StringAddRef', IR) > 0);
  AssertTrue('release on exit from Mut', Pos('_StringRelease', IR) > 0);
end;

procedure TRecordTests.TestCodegen_RecordByValParam_DynArrayField_AddRefRelease;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TIA = array of Integer;
          TR  = record A: TIA; end;
        procedure Mut(R: TR);
        var Tmp: TIA;
        begin SetLength(Tmp, 1); R.A := Tmp end;
        var W: TR;
        begin Mut(W) end.
        ''');
  AssertTrue('addref dynarray on entry to Mut',
    Pos('_DynArrayAddRef', IR) > 0);
  AssertTrue('release dynarray on exit from Mut',
    Pos('_DynArrayRelease', IR) > 0);
end;

{ const params skip the ARC retain/release pair — the caller keeps the
  object alive for the whole call.  A record by-const-value param with
  no other managed locals must therefore emit no AddRef/Release at all. }
procedure TRecordTests.TestCodegen_RecordByValParam_ConstParam_NoARC;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TR = record S: string; end;
        procedure ReadOnly(const R: TR);
        var L: Integer;
        begin L := Length(R.S) end;
        begin end.
        ''');
  { The only managed entity in the routine is R.S, and R is const, so
    no _StringAddRef should appear anywhere in the emitted IR. }
  AssertEquals('no AddRef anywhere for const record param',
    -1, Pos('_StringAddRef', IR));
end;

{ Caller-side: DoSomething(GetRec()) — the sret temporary from GetRec is
  consumed by DoSomething and not bound to a named variable.  The call
  site must release each managed leaf of the temp buffer after the call,
  otherwise the temp's heap string leaks every time the caller runs. }
procedure TRecordTests.TestCodegen_RecordByValArg_CallResultTemp_CleansFields;
var
  IR, DriverBody: string;
  StartIdx, EndIdx: Integer;
begin
  IR := GenIR(
    '''
        program P;
        type TR = record S: string; end;
        function MakeIt: TR; begin Result.S := 'x' end;
        procedure Consume(R: TR); begin end;
        procedure Driver; begin Consume(MakeIt()) end;
        begin Driver() end.
        ''');
  StartIdx := Pos('$Driver(', IR);
  AssertTrue('Driver emitted', StartIdx > 0);
  EndIdx := StartIdx;
  while (EndIdx <= Length(IR)) and (IR[EndIdx] <> '}') do Inc(EndIdx);
  DriverBody := Copy(IR, StartIdx, EndIdx - StartIdx);
  AssertTrue('Driver releases temp''s string field after Consume() call',
    Pos('_StringRelease', DriverBody) > 0);
end;

{ Caller-side, variable arg: DoSomething(W) where W is a named record
  variable.  The variable's storage belongs to the enclosing scope (and
  is cleaned up at scope exit), so the call site must NOT emit a
  per-field Release after the call — doing so would corrupt W. }
procedure TRecordTests.TestCodegen_RecordByValArg_VarRef_DoesNotClean;
var
  IR, DriverBody: string;
  StartIdx, EndIdx: Integer;
begin
  IR := GenIR(
    '''
        program P;
        type TR = record S: string; end;
        procedure Consume(R: TR); begin end;
        procedure Driver;
        var W: TR;
        begin W.S := 'x'; Consume(W) end;
        begin Driver() end.
        ''');
  StartIdx := Pos('$Driver(', IR);
  AssertTrue('Driver emitted', StartIdx > 0);
  EndIdx := StartIdx;
  while (EndIdx <= Length(IR)) and (IR[EndIdx] <> '}') do Inc(EndIdx);
  DriverBody := Copy(IR, StartIdx, EndIdx - StartIdx);
  { Two pre-existing _StringReleases: (1) release-old in W.S := 'x' and
    (2) W's scope-exit cleanup.  My call-site cleanup must NOT add a
    third for the Consume(W) call site — W is a named variable, not a
    temp.  Three Releases would indicate the call site corrupted W. }
  AssertEquals('no extra _StringRelease at variable-arg call site',
    2, CountOccurrences('_StringRelease', DriverBody));
end;

{ Nested-record-with-managed-leaf temporary: the helper recurses through
  TInner so both the outer string and the inner string get released. }
procedure TRecordTests.TestCodegen_RecordByValArg_NestedManagedField_Recurses;
var
  IR, DriverBody: string;
  StartIdx, EndIdx: Integer;
begin
  IR := GenIR(
    '''
        program P;
        type
          TInner = record N: string; end;
          TOuter = record S: string; Inner: TInner; end;
        function MakeIt: TOuter;
        begin Result.S := 'a'; Result.Inner.N := 'b' end;
        procedure Consume(R: TOuter); begin end;
        procedure Driver; begin Consume(MakeIt()) end;
        begin Driver() end.
        ''');
  StartIdx := Pos('$Driver(', IR);
  AssertTrue('Driver emitted', StartIdx > 0);
  EndIdx := StartIdx;
  while (EndIdx <= Length(IR)) and (IR[EndIdx] <> '}') do Inc(EndIdx);
  DriverBody := Copy(IR, StartIdx, EndIdx - StartIdx);
  AssertEquals('two _StringRelease — outer.S and inner.N — after Consume call',
    2, CountOccurrences('_StringRelease', DriverBody));
end;

initialization
  RegisterTest(TRecordTests);

end.
