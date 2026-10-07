{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.dynarray;

{ Tests for dynamic array type declarations:
  parsing, semantic analysis, and QBE IR code generation.

  Dynamic arrays (array of T) are heap-allocated, reference-counted
  arrays with runtime length stored in a 2-word header before element 0.
  Layout: [refcount:4][length:4][element 0][element 1]...
  The variable slot holds a pointer to element 0 (nil = unassigned). }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TDynArrayTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_DynArray_TypeAlias_AcceptsDecl;
    procedure TestParse_DynArray_InlineVarDecl_AcceptsDecl;
    procedure TestParse_DynArray_Combined_TypeAndVar;
    procedure TestParse_DynArray_TypeName_EncodesCorrectly;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_DynArray_Kind;
    procedure TestSemantic_DynArray_ElementType_Integer;
    procedure TestSemantic_DynArray_ElementType_String;
    procedure TestSemantic_DynArray_Var_ResolvesToDynArray;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_DynArray_High_Accepted;
    procedure TestSemantic_DynArray_Low_Accepted;

    { ------------------------------------------------------------------ }
    { Record elements: a[i] := r copies; a[i].F := v assigns in place      }
    { ------------------------------------------------------------------ }
    procedure TestParse_DynArray_RecordElem_FieldAssign_Accepted;

    { ------------------------------------------------------------------ }
    { Array-typed FIELDS: r.A[i] := v writes the element, not the array    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_RecordField_DynArrayElemAssign_Accepted;
    procedure TestParse_ChainedField_DynArrayElemAssign_Accepted;
  end;

implementation

function TDynArrayTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try Result := P.Parse(); finally P.Free(); L.Free(); end;
end;

function TDynArrayTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try A.Analyse(Result); finally A.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TDynArrayTests.TestParse_DynArray_TypeAlias_AcceptsDecl;
var Prog: TProgram;
begin
  Prog := ParseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestParse_DynArray_InlineVarDecl_AcceptsDecl;
var Prog: TProgram;
begin
  Prog := ParseSrc('''
      program Prg;
      var
        A: array of Integer;
      begin
      end.
      ''');
  try
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestParse_DynArray_Combined_TypeAndVar;
var Prog: TProgram;
begin
  Prog := ParseSrc('''
      program Prg;
      type
        TStrArr = array of string;
      var
        S: TStrArr;
      begin
      end.
      ''');
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestParse_DynArray_TypeName_EncodesCorrectly;
var Prog: TProgram; TD: TTypeDecl; AD: TTypeAliasDef;
begin
  Prog := ParseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    AD := TTypeAliasDef(TD.Def);
    AssertEquals('type name encoded as array of Integer',
      'array of Integer', AD.TypeName);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TDynArrayTests.TestSemantic_DynArray_Kind;
var Prog: TProgram; Sym: TSymbol;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('TIntArr');
    AssertTrue('TIntArr symbol found', Sym <> nil);
    AssertEquals('kind is tyDynArray', Ord(tyDynArray), Ord(Sym.TypeDesc.Kind));
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestSemantic_DynArray_ElementType_Integer;
var Prog: TProgram; Sym: TSymbol; DAT: TDynArrayTypeDesc;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('TIntArr');
    DAT := TDynArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('element type is Integer', 'Integer', DAT.ElementType.Name);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestSemantic_DynArray_ElementType_String;
var Prog: TProgram; Sym: TSymbol; DAT: TDynArrayTypeDesc;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type
        TStrArr = array of string;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('TStrArr');
    DAT := TDynArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('element type is string', 'string', DAT.ElementType.Name);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestSemantic_DynArray_Var_ResolvesToDynArray;
var Prog: TProgram; VD: TVarDecl;
begin
  Prog := AnalyseSrc('''
      program Prg;
      var
        A: array of Integer;
      begin
      end.
      ''');
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertEquals('var resolved to tyDynArray',
      Ord(tyDynArray), Ord(VD.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TDynArrayTests.TestSemantic_DynArray_High_Accepted;
var Prog: TProgram;
begin
  { High() on a named dynamic array type must not raise a semantic error }
  Prog := AnalyseSrc('''
      program Prg;
      type Tar = array of Integer;
      var ar: Tar;
          i: Integer;
      begin
        i := High(ar);
      end.
      ''');
  AssertNotNil('program parsed and analysed without error', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestSemantic_DynArray_Low_Accepted;
var Prog: TProgram;
begin
  { Low() on a named dynamic array type must not raise a semantic error }
  Prog := AnalyseSrc('''
      program Prg;
      type Tar = array of Integer;
      var ar: Tar;
          i: Integer;
      begin
        i := Low(ar);
      end.
      ''');
  AssertNotNil('program parsed and analysed without error', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestParse_DynArray_RecordElem_FieldAssign_Accepted;
var Prog: TProgram;
begin
  { a[i].Field := v on the statement LHS used to raise
    "Expected ':=' but got '.'" — the subscript statement branch only
    accepted ':=' directly after ']'. }
  Prog := ParseSrc('''
      program Prg;
      type TRec = record Name: String; Number: Integer; end;
      var A: array of TRec;
      begin
        SetLength(A, 2);
        A[0].Name := 'hello';
        A[1].Number := 42;
      end.
      ''');
  AssertNotNil('program with a[i].Field := v parses', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestSemantic_RecordField_DynArrayElemAssign_Accepted;
var Prog: TProgram;
begin
  { r.A[0] := 10 used to fail semantic with "expected 'array of Integer'
    but got 'Integer'" — the subscript was treated as an indexed-property
    index and dropped from the LHS type. }
  Prog := AnalyseSrc('''
      program Prg;
      type
        TIA = array of Integer;
        TR  = record A: TIA; end;
      var r: TR;
      begin
        SetLength(r.A, 3);
        r.A[0] := 10;
      end.
      ''');
  AssertNotNil('record-field element assign analyses', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestParse_ChainedField_DynArrayElemAssign_Accepted;
var Prog: TProgram;
begin
  { c.N.A[0] := 7 used to fail parse with "Expected 'end' but got '['" —
    the chained L-value walker refused a subscript after the final field. }
  Prog := ParseSrc('''
      program Prg;
      type
        TIA    = array of Integer;
        TInner = record A: TIA; end;
        TC     = class N: TInner; end;
      var c: TC;
      begin
        c := TC.Create();
        SetLength(c.N.A, 3);
        c.N.A[0] := 7;
      end.
      ''');
  AssertNotNil('chained field element assign parses', Prog);
  Prog.Free();
end;

initialization
  RegisterTest(TDynArrayTests);

end.
