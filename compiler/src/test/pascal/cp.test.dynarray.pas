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
    { BUG-20261017: F()[I] := V writes an element of the dynamic array a
      call returns (shared storage); on a static-array result it would
      change a temporary copy and is rejected }
    procedure TestSemantic_WriteThroughCallResult_DynArrayOnly;
    procedure TestCodegen_WriteThroughCallResult_ReleasesTheResult;
    { Pointer(A) is the data pointer of a dynamic-array variable, field or
      element; of a call result it would dangle and is rejected }
    procedure TestSemantic_PointerOfDynArray;
    { x86-64: the index of A[I] := F() is checked before F is called }
    procedure TestCodegen_BadIndexWrite_CheckPrecedesValue;
    { the element address of A[I] := V is taken after V (which may resize
      A) and the index checked again there, on both ISAs and for the
      record-call and interface arms }
    procedure TestCodegen_ValueFirst_ThenAddress;
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

    { ------------------------------------------------------------------ }
    { Copy / + / Concat / Delete / Insert on dynamic arrays (GH #260)     }
    { ------------------------------------------------------------------ }
    { Copy(A), Copy(A, I), Copy(A, I, N), A + B, A + [x], [x] + A and
      Concat(A, B, ...) all type as A's array type }
    procedure TestSemantic_DynArrayCopyConcat_TypeAsTheArray;
    { A + B needs one dynamic-array type on both sides }
    procedure TestSemantic_DynArrayPlus_MismatchedTypes_Rejected;
    { Delete and Insert take an assignable array; an inserted value is checked
      against the element type (or is an array of the same type) }
    procedure TestSemantic_DynArrayDeleteInsert_ArgsChecked;
    { Concat of strings is their concatenation; Concat needs one argument and
      cannot mix strings and arrays }
    procedure TestSemantic_Concat_StringsAndErrors;
    { each operation lowers to its RTL routine on both ISAs }
    procedure TestCodegen_DynArrayOps_CallTheirRtlRoutines;
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
        TIntArr = array of Int;
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
        A: array of Int;
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
        TIntArr = array of Int32;
      begin
      end.
      ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    AD := TTypeAliasDef(TD.Def);
    AssertEquals('type name encoded as array of Int',
      'array of Int32', AD.TypeName);
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
        TIntArr = array of Int;
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
        TIntArr = array of Int32;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('TIntArr');
    DAT := TDynArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('element type is Integer', 'Int32', DAT.ElementType.Name);
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
        A: array of Int;
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
      type Tar = array of Int;
      var ar: Tar;
          i: Int;
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
      type Tar = array of Int;
      var ar: Tar;
          i: Int;
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
      type TRec = record Name: String; Number: Int; end;
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
  { r.A[0] := 10 used to fail semantic with "expected 'array of Int32'
    but got 'Int32'" — the subscript was treated as an indexed-property
    index and dropped from the LHS type. }
  Prog := AnalyseSrc('''
      program Prg;
      type
        TIA = array of Int32;
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
        TIA    = array of Int;
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
    var I: Int;
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
    type TIA = array of Int32;
    var C: array of Int32; D: array of Float64; M: array of TIA;
    begin
      C := [1, 2]; C := []; D := [1.5, 2]; M := [[1], [], [2, 3]];
    end.
    ''';
  SrcElem = '''
    program P;
    var C: array of Int32;
    begin
      C := [1, 'a'];
    end.
    ''';
  SrcRange = '''
    program P;
    var C: array of Int32;
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
  { DA := [1, 2] was rejected with "expected 'array of Int32' but got
    'array of Int32'" -- the literal had an anonymous type of its own
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
      type TIA = array of Int;
      var A: TIA; B: Boolean;
      function Count(X: TIA): Int; begin Result := Length(X) end;
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
    AnalyseSrc('program Prg; var A: array[0..2] of Int; ' +
      'begin A := nil end.').Free();
  except
    on E: ESemanticError do Raised := True;
  end;
  AssertTrue('nil into a static array rejected', Raised);
end;

procedure TDynArrayTests.TestSemantic_DynArrayCopyConcat_TypeAsTheArray;
var Prog: TProgram;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type TIA = array of Int16;
      var A, B, C: TIA; X: Int16;
      begin
        C := Copy(A);
        C := Copy(A, 1);
        C := Copy(A, 1, 2);
        C := A + B;
        C := A + [X];
        C := [X, 7] + A;
        C := Concat(A, B, [X]);
        C := Concat(A);
        X := Copy(A, 0, 1)[0];
      end.
      ''');
  AssertNotNil('every array form accepted', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestSemantic_DynArrayPlus_MismatchedTypes_Rejected;
begin
  AssertTrue('different element types',
    Pos('dynamic array', SemanticError('''
      program Prg;
      var A: array of Int16; S: array of string;
      begin
        A := A + S;
      end.
      ''')) >= 0);
  AssertTrue('array plus a scalar',
    SemanticError('''
      program Prg;
      var A: array of Int16;
      begin
        A := A + 1;
      end.
      ''') <> '');
  AssertTrue('Copy result is the array type, not a string',
    SemanticError('''
      program Prg;
      var A: array of Int16; S: string;
      begin
        S := Copy(A, 0, 1);
      end.
      ''') <> '');
end;

procedure TDynArrayTests.TestSemantic_DynArrayDeleteInsert_ArgsChecked;
var Prog: TProgram;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type TIA = array of Int16;
        TRec = record F: TIA; end;
      var A, B: TIA; R: TRec; M: array of TIA; X: Int16;
      procedure Edit(var V: TIA);
      begin
        Delete(V, 0, 1);
        Insert(X, V, 0);
      end;
      begin
        Delete(A, 1, 2);
        Insert(B, A, 1);
        Insert(X, A, 0);
        Insert(5, A, 0);
        Insert([1, 2], A, 0);
        Delete(R.F, 0, 1);
        Insert(X, R.F, 0);
        SetLength(M, 1);
        Insert(X, M[0], 0);
        Delete(M[0], 0, 1);
        Edit(A);
      end.
      ''');
  AssertNotNil('every assignable target accepted', Prog);
  Prog.Free();
  AssertTrue('inserted value checked against the element type',
    SemanticError('''
      program Prg;
      var A: array of Int16;
      begin
        Insert('x', A, 0);
      end.
      ''') <> '');
  AssertTrue('Delete needs an assignable array',
    Pos('assignable', SemanticError('''
      program Prg;
      type TIA = array of Int16;
      function F: TIA; begin Result := nil end;
      begin
        Delete(F(), 0, 1);
      end.
      ''')) >= 0);
  AssertTrue('Insert needs three arguments',
    SemanticError('''
      program Prg;
      var A: array of Int16;
      begin
        Insert(1, A);
      end.
      ''') <> '');
end;

procedure TDynArrayTests.TestSemantic_Concat_StringsAndErrors;
var Prog: TProgram;
begin
  Prog := AnalyseSrc('''
      program Prg;
      var S, T: string;
      begin
        S := Concat('a', T, 'c');
        S := Concat(T);
      end.
      ''');
  AssertNotNil('string Concat accepted', Prog);
  Prog.Free();
  AssertTrue('Concat needs an argument',
    SemanticError('''
      program Prg;
      var S: string;
      begin
        S := Concat();
      end.
      ''') <> '');
  AssertTrue('Concat cannot mix strings and arrays',
    SemanticError('''
      program Prg;
      var S: string; A: array of string;
      begin
        A := Concat(A, S);
      end.
      ''') <> '');
end;

procedure TDynArrayTests.TestCodegen_DynArrayOps_CallTheirRtlRoutines;
const
  Src = '''
    program P;
    var A, B, C: array of string;
    begin
      C := Copy(A, 1, 2);
      C := A + B;
      Delete(A, 0, 1);
      Insert(B, A, 1);
    end.
    ''';
begin
  AssertEquals('Copy', '',
    AsmMissing(Src, #9'callq _DynArrayCopy', #9'bl __DynArrayCopy'));
  AssertEquals('+', '',
    AsmMissing(Src, #9'callq _DynArrayConcat', #9'bl __DynArrayConcat'));
  AssertEquals('Delete', '',
    AsmMissing(Src, #9'callq _DynArrayDelete', #9'bl __DynArrayDelete'));
  AssertEquals('Insert', '',
    AsmMissing(Src, #9'callq _DynArrayInsert', #9'bl __DynArrayInsert'));
  { a managed element passes its hook, so copies are retained }
  AssertEquals('string element hook passed', '',
    AsmMissing(Src, '_DynElemsString', '_DynElemsString'));
end;


const
  SrcWriteThroughCall = '''
    program P;
    type TArr = array of Int32;
      TObj = class A: TArr; function Items: TArr; end;
    var G: TArr; O: TObj;
    function GetArr: TArr; begin Result := G end;
    function TObj.Items: TArr; begin Result := A end;
    begin
      GetArr()[1] := 9;
      O.Items()[0] := 5
    end.
    ''';

procedure TDynArrayTests.TestSemantic_WriteThroughCallResult_DynArrayOnly;
const
  SrcStatic = '''
    program P;
    type TSA = array[0..2] of Int32;
    function GetSA: TSA; begin Result[0] := 0 end;
    begin
      GetSA()[1] := 9
    end.
    ''';
begin
  AssertEquals('a dynamic-array call result is writable', '',
    SemanticError(SrcWriteThroughCall));
  AssertEquals('a value cast of a static-array variable is its storage', '',
    SemanticError('''
      program P;
      type TSA = array[0..3] of Byte; TSB = array[0..3] of Byte;
      var B: TSB;
      begin
        TSA(B)[1] := 7
      end.
      '''));
  AssertTrue('a static-array call result is a temporary: ' +
    SemanticError(SrcStatic),
    Pos('temporary', SemanticError(SrcStatic)) >= 0);
end;

procedure TDynArrayTests.TestCodegen_WriteThroughCallResult_ReleasesTheResult;
begin
  { the call returns an owned +1 reference: x86-64 never released it (one
    leaked reference per write), arm64 stopped with an internal error }
  AssertEquals('the returned array is released after the store', '',
    AsmMissing(SrcWriteThroughCall,
      #9'movq _pendrel_0(%rip), %rdi' + #10 + #9'callq _DynArrayRelease',
      #9'bl __DynArrayRelease' + #10 + #9'stur xzr, [x29, #-'));
end;


procedure TDynArrayTests.TestSemantic_PointerOfDynArray;
const
  SrcOk = '''
    program P;
    type TRec = record A: array of Int32; end;
    var A: array of Int32; R: TRec; M: array of array of Int32; Q: Pointer;
    begin
      Q := Pointer(A); Q := Pointer(R.A); Q := Pointer(M[0])
    end.
    ''';
  SrcCall = '''
    program P;
    var A: array of Int32; Q: Pointer;
    function MkArr: array of Int32; begin Result := A end;
    begin
      Q := Pointer(MkArr())
    end.
    ''';
begin
  AssertEquals('variable, field and element accepted', '', SemanticError(SrcOk));
  AssertTrue('a call result is rejected: ' + SemanticError(SrcCall),
    Pos('needs a variable, field or element', SemanticError(SrcCall)) >= 0);
end;

procedure TDynArrayTests.TestCodegen_BadIndexWrite_CheckPrecedesValue;
const
  Src = '''
    program P;
    var IA: array of Int32; SA: array of String;
    function VI: Int32; begin Result := 1 end;
    function VS: String; begin Result := 'x' end;
    begin
      IA[5] := VI();
      SA[5] := VS()
    end.
    ''';
var
  A, Main: string;
  M: Int;
begin
  A := GenAsm(Src, TargetX86_64);
  M := Pos(#10'main:', A);
  AssertTrue('main found', M >= 0);
  Main := Copy(A, M, Length(A) - M);
  AssertTrue('the int write checks before calling VI: ' + Main,
    (Pos('callq _Raise_RangeError', Main) >= 0) and
    (Pos('callq _Raise_RangeError', Main) < Pos('callq VI', Main)));
  Main := Copy(Main, Pos('callq VI', Main), Length(Main));
  AssertTrue('the string write checks before calling VS',
    (Pos('callq _Raise_RangeError', Main) >= 0) and
    (Pos('callq _Raise_RangeError', Main) < Pos('callq VS', Main)));
end;


procedure TDynArrayTests.TestCodegen_ValueFirst_ThenAddress;
const
  Src = '''
    program P;
    type TRec = record N: Int32; S: String; end;
      IFoo = interface end;
    var IA: array of Int32; RA: array of TRec; XA: array of IFoo; F: IFoo;
    function GI: Int32; begin Result := 1 end;
    function GR: TRec; begin Result.N := 1 end;
    function GX: IFoo; begin Result := F end;
    begin
      IA[0] := GI();
      RA[0] := GR();
      XA[0] := GX()
    end.
    ''';

  procedure CheckAfter(const AAsm, ACall, ARaise, AWhat: string);
  var
    Rest: string;
    P: Int;
  begin
    P := Pos(ACall, AAsm);
    AssertTrue(AWhat + ': the value call is emitted', P >= 0);
    Rest := Copy(AAsm, P + Length(ACall), Length(AAsm));
    AssertTrue(AWhat + ': the index is checked again after the value',
      Pos(ARaise, Rest) >= 0);
  end;

var
  X86, A64: string;
begin
  X86 := GenAsm(Src, TargetX86_64);
  X86 := Copy(X86, Pos(#10'main:', X86), Length(X86));
  A64 := GenAsm(Src, TargetArm64);
  A64 := Copy(A64, Pos(#10'_main:', A64), Length(A64));
  CheckAfter(X86, 'callq GI', 'callq _Raise_RangeError', 'x86-64 Int32');
  CheckAfter(X86, 'callq GR', 'callq _Raise_RangeError', 'x86-64 record call');
  CheckAfter(X86, 'callq GX', 'callq _Raise_RangeError', 'x86-64 interface');
  CheckAfter(A64, 'bl _GI', 'bl __Raise_RangeError', 'arm64 Int32');
  CheckAfter(A64, 'bl _GR', 'bl __Raise_RangeError', 'arm64 record call');
  CheckAfter(A64, 'bl _GX', 'bl __Raise_RangeError', 'arm64 interface');
end;

initialization
  RegisterTest(TDynArrayTests);

end.
