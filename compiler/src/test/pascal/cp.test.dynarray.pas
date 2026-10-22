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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TDynArrayTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { a dynamic-array literal allocates a fresh array and retains a borrowed
      managed element (an owned one moves in) }
    procedure TestCodegen_DynArrayLiteral_FreshArrayRetainsBorrowed;
    { a bracket literal assigned to a dynamic array takes the target's type;
      each element is checked against the element type }
    procedure TestSemantic_DynArrayLiteral_TypedFromTarget;
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

    { ------------------------------------------------------------------ }
    { Whole-array store through a var/out param: deref the caller's slot   }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_DynArray_VarParamStore_ReleasesThroughAddress;
    procedure TestCodegen_DynArray_SubscriptOfCallResult_ReleasesIt;

    { nil empties a dynamic array: assignment, argument, result and
      comparison; a static array still rejects nil }
    procedure TestSemantic_DynArray_NilAssignCompare_Accepted;
    procedure TestSemantic_StaticArray_NilAssign_Rejected;
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

procedure TDynArrayTests.TestCodegen_DynArray_VarParamStore_ReleasesThroughAddress;
const
  { A := B with A a var param: the slot holds the caller's ADDRESS, so the old
    array is loaded and released THROUGH it and the new one stored there.
    arm64 rejected this shape outright (not yet lowered) until GH #220's
    TDictionary<string, array of Byte> hit it. }
  Src = '''
    program P;
    type TBytes = array of Byte;
    procedure Fill(var A: TBytes; const B: TBytes);
    begin
      A := B
    end;
    var X, Y: TBytes;
    begin
      Fill(X, Y)
    end.
    ''';
begin
  AssertEquals('old value released through the var-param address', '',
    AsmMissing(Src,
      #9'movq (%rcx), %rdi' + LineEnding + #9'subq $8, %rsp' + LineEnding +
        #9'callq _DynArrayRelease',
      #9'ldr x0, [x9]' + LineEnding + #9'bl __DynArrayRelease'));
end;

procedure TDynArrayTests.TestCodegen_DynArray_SubscriptOfCallResult_ReleasesIt;
const
  { MakeArr()[1]: the call's +1 array is subscripted in place and owned by
    nobody else, so it must be released once the element is read.  x86-64
    leaked it (2 GB peak for 20000 x 100 KB); arm64 refused the shape.  Nothing
    else in this program releases a dyn array, so any release is that one. }
  Src = '''
    program P;
    type TBytes = array of Byte;
    function MakeArr(): TBytes;
    begin
      SetLength(Result, 3)
    end;
    var I: Integer;
    begin
      I := MakeArr()[1]
    end.
    ''';
begin
  AssertEquals('owned transient released after the element read', '',
    AsmMissing(Src, #9'callq _DynArrayRelease', #9'bl __DynArrayRelease'));
end;

procedure TDynArrayTests.TestSemantic_DynArrayLiteral_TypedFromTarget;
const
  SrcOk = '''
    program P;
    type TIA = array of Integer;
    var C: array of Integer; D: array of Double; M: array of TIA;
    begin
      C := [1, 2]; C := []; D := [1.5, 2]; M := [[1], [], [2, 3]];
    end.
    ''';
  SrcElem = '''
    program P;
    var C: array of Integer;
    begin
      C := [1, 'a'];
    end.
    ''';
  SrcRange = '''
    program P;
    var C: array of Integer;
    begin
      C := [1..3];
    end.
    ''';
  SrcSub = '''
    program P;
    type TSub = 1..5;
    var C: array of TSub;
    begin
      C := [2, 7];
    end.
    ''';
begin
  { DA := [1, 2] was rejected with "expected 'array of Integer' but got
    'array of Integer'" -- the literal had an anonymous type of its own
    (BUG-20261014-dynarray-literal-assignment) }
  AssertEquals('dyn-array literals accepted', '', SemanticError(SrcOk));
  AssertTrue('element type checked',
    Pos('dynamic-array literal element', SemanticError(SrcElem)) >= 0);
  AssertTrue('a range is a set form',
    Pos('only allowed in a set literal', SemanticError(SrcRange)) >= 0);
  AssertTrue('subrange element range-checked',
    Pos('out of range', SemanticError(SrcSub)) >= 0);
end;

procedure TDynArrayTests.TestCodegen_DynArrayLiteral_FreshArrayRetainsBorrowed;
const
  Src = '''
    program P;
    var S: array of string; X: string;
    begin
      X := 'x';
      S := [X];
    end.
    ''';
begin
  AssertEquals('fresh array', '',
    AsmMissing(Src, #9'callq _DynArraySetLengthM', #9'bl __DynArraySetLengthM'));
  AssertEquals('borrowed element retained', '',
    AsmMissing(Src, #9'callq _StringAddRef', #9'bl __StringAddRef'));
end;

procedure TDynArrayTests.TestSemantic_DynArray_NilAssignCompare_Accepted;
var Prog: TProgram;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type TIA = array of Integer;
      var A: TIA; B: Boolean;
      function Count(X: TIA): Integer; begin Result := Length(X) end;
      function None: TIA; begin Result := nil end;
      begin
        A := nil;
        B := (A = nil) or (nil <> A);
        Count(nil);
        A := None();
      end.
      ''');
  AssertNotNil('nil accepted for a dynamic array', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestSemantic_StaticArray_NilAssign_Rejected;
var Raised: Boolean;
begin
  Raised := False;
  try
    AnalyseSrc('program Prg; var A: array[0..2] of Integer; ' +
      'begin A := nil end.').Free();
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('nil into a static array rejected', Raised);
end;

initialization
  RegisterTest(TDynArrayTests);

end.
