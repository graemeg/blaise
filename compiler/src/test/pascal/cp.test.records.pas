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
  blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TRecordTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
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
    procedure TestCodegen_ConstRecordParam_NoAddRef;

    { ------------------------------------------------------------------ }
    { Byte sizing and record packing                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_FourByteRecord_TotalSizeIs4;
    procedure TestSemantic_ByteThenInteger_AlignsInteger;
    procedure TestSemantic_ByteFieldOffsets_Are0123;
    { Single is a 4-byte IEEE-754 float — alignment 4, not 8.  A record
      of three back-to-back Single fields totals 12 bytes, not 24. }
    procedure TestSemantic_ThreeSingleRecord_TotalSizeIs12;
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
{ Code generation                                                     }
{ ------------------------------------------------------------------ }

procedure TRecordTests.TestCodegen_ConstRecordParam_NoAddRef;
const
  Src = '''
    program P;
    type TR = record S: string; end;
    procedure ReadOnly(const R: TR);
    var L: Integer;
    begin
      L := Length(R.S);
      WriteLn(L)
    end;
    begin end.
    ''';
var
  I: Integer;
  Target: string;
begin
  { A const record parameter is borrowed: the callee neither retains nor
    releases its managed fields.  An extra retain/release pair would be
    balanced, so a running program cannot see it -- only the code can. }
  for I := 0 to 1 do
  begin
    if I = 0 then
      Target := TargetX86_64
    else
      Target := TargetArm64;
    AssertTrue(Target + ': no AddRef for a const record param',
      Pos('_StringAddRef', GenAsm(Src, Target)) < 0);
    AssertTrue(Target + ': no Release for a const record param',
      Pos('_StringRelease', GenAsm(Src, Target)) < 0);
  end;
end;

initialization
  RegisterTest(TRecordTests);

end.
