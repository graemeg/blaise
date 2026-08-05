{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.staticarray;

{ Tests for static array declarations and element access:
  parsing, semantic analysis, and QBE IR code generation. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TStaticArrayTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_StaticArray_TypeName;
    procedure TestParse_StaticArray_SubscriptAssign_Name;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StaticArray_Kind;
    procedure TestSemantic_StaticArray_ElementType;
    procedure TestSemantic_StaticArray_Bounds;
    procedure TestSemantic_StaticArray_ByteSize;
    procedure TestSemantic_StaticArray_IntArray;
    procedure TestSemantic_StaticArray_NonZero_LowBound;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_StaticArray_AllocEmitted;
    procedure TestCodegen_StaticArray_MemsetEmitted;
    procedure TestCodegen_StaticArray_WriteEmitted;
    procedure TestCodegen_StaticArray_ReadEmitted;
    procedure TestCodegen_StaticArray_NonZero_OffsetSubtracted;
    procedure TestCodegen_StaticArray_StringWrite_EmitsARC;
    procedure TestCodegen_StaticArray_ClassWrite_EmitsARC;
    procedure TestCodegen_DynArray_StringWrite_EmitsARC;
    procedure TestCodegen_DynArray_ClassWrite_EmitsARC;

    { ------------------------------------------------------------------ }
    { Low / High                                                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StaticArray_Low_ReturnsInteger;
    procedure TestSemantic_StaticArray_High_ReturnsInteger;
    procedure TestCodegen_StaticArray_Low_EmitsLowBound;
    procedure TestCodegen_StaticArray_High_EmitsHighBound;

    { ------------------------------------------------------------------ }
    { Address-of                                                           }
    { ------------------------------------------------------------------ }
    procedure TestParse_AddrOf_NodeType;
    procedure TestSemantic_AddrOf_ReturnsPointerType;
    procedure TestSemantic_AddrOf_BaseTypeIsByte;
    procedure TestCodegen_AddrOf_NoLoad;
    procedure TestCodegen_AddrOf_AddressArithmetic;

    { ------------------------------------------------------------------ }
    { Named array type alias: type TArr = array[L..H] of T               }
    { ------------------------------------------------------------------ }
    procedure TestParse_TypeAlias_ArrayParses;
    procedure TestParse_TypeAlias_ArrayName;
    procedure TestSemantic_TypeAlias_KindIsStaticArray;
    procedure TestSemantic_TypeAlias_ElementType;
    procedure TestSemantic_TypeAlias_Bounds;
    procedure TestSemantic_TypeAlias_VarUsesAlias;
    procedure TestSemantic_TypeAlias_NonZeroBase;
    procedure TestCodegen_TypeAlias_AllocEmitted;
    procedure TestCodegen_TypeAlias_ElementSizeInAlloc;

    { ------------------------------------------------------------------ }
    { Named integer subrange as an array index type                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_NamedSubrange_IndexFoldsToBounds;
    procedure TestSemantic_NamedSubrange_NonZeroBase_IndexFoldsToBounds;

    { ------------------------------------------------------------------ }
    { Multi-dimensional arrays (comma form desugars to nested arrays)     }
    { ------------------------------------------------------------------ }
    procedure TestParse_MultiDim_CommaDecl_DesugarsToNested;
    procedure TestSemantic_MultiDim_Kind_IsStaticArray;
    procedure TestSemantic_MultiDim_ElementType_IsInnerArray;
    procedure TestSemantic_MultiDim_TotalByteSize;
    procedure TestSemantic_MultiDim_ThreeDims;
    procedure TestCodegen_MultiDim_AllocTotalSize;
    procedure TestCodegen_MultiDim_CommaWrite_EmitsRowOffset;
    procedure TestCodegen_MultiDim_ChainedWrite_SameAsComma;
    procedure TestCodegen_MultiDim_CommaRead_NestedSubscript;

    { ------------------------------------------------------------------ }
    { Function returning static array by value (issue #112)              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_ReturnStaticArray_SretParam;
    procedure TestCodegen_ReturnStaticArray_VoidReturn;

    { ------------------------------------------------------------------ }
    { Named constant array bounds (issue #109)                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_NamedConstBound_Simple;
    procedure TestSemantic_NamedConstBound_BothBounds;
    procedure TestSemantic_NamedConstBound_Expression;
    procedure TestSemantic_NamedConstBound_TypeDecl;
    procedure TestCodegen_NamedConstBound_CorrectSize;

    { ------------------------------------------------------------------ }
    { Enum-indexed var/type static arrays (issue #114)                   }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_EnumIndex_VarDecl;
    procedure TestSemantic_EnumIndex_TypeDecl;
    procedure TestSemantic_EnumIndex_Bounds;
    procedure TestCodegen_EnumIndex_AllocSize;
    { GH #181 — Boolean is a valid 2-element ordinal index type. }
    procedure TestSemantic_BooleanIndex_TypeDecl;
    procedure TestSemantic_BooleanIndex_Bounds;
    { GH #208 — the same index type in an inline typed CONSTANT. }
    procedure TestSemantic_BooleanIndex_ConstBounds;
    procedure TestSemantic_BooleanIndex_ConstWrongCount;
    procedure TestSemantic_StringIndex_RaisesTargetedError;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TStaticArrayTests.ParseSrc(const ASrc: string): TProgram;
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

function TStaticArrayTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TStaticArrayTests.GenIR(const ASrc: string): string;
var P: TProgram; CG: TCodeGenQBE;
begin
  P := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(P);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    P.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                              }
{ ------------------------------------------------------------------ }

const
  SrcByteBuf =
    '''
        program SA;
        procedure Foo;
        var Buf: array[0..7] of Byte;
        begin
          Buf[0] := 42
        end;
        begin end.
        ''';

  SrcIntArray =
    '''
        program SA;
        procedure Foo;
        var A: array[0..3] of Integer;
        begin
          A[2] := 99
        end;
        begin end.
        ''';

  SrcReadBack =
    '''
        program SA;
        function GetFirst: Integer;
        var A: array[0..3] of Integer;
        begin
          A[0] := 7;
          Result := A[0]
        end;
        begin end.
        ''';

  SrcNonZero =
    '''
        program SA;
        procedure Foo;
        var R: array[5..9] of Integer;
        begin
          R[5] := 1
        end;
        begin end.
        ''';

  SrcAddrOf =
    '''
        program SA;
        procedure Foo;
        var Buf: array[0..7] of Byte;
            P: ^Byte;
        begin
          P := @Buf[0]
        end;
        begin end.
        ''';

  SrcLowHigh =
    '''
        program SA;
        function Len: Integer;
        var A: array[3..7] of Integer;
        begin
          Result := High(A) - Low(A) + 1
        end;
        begin end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser tests                                                        }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestParse_StaticArray_TypeName;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  P := ParseSrc(SrcByteBuf);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    AssertEquals('type name encoded', 'array[0..7] of Byte', Decl.TypeName);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestParse_StaticArray_SubscriptAssign_Name;
var P: TProgram; MD: TMethodDecl; Stmt: TStaticSubscriptAssign;
begin
  P := ParseSrc(SrcByteBuf);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    AssertTrue('stmt is TStaticSubscriptAssign',
      MD.Body.Stmts[0] is TStaticSubscriptAssign);
    Stmt := TStaticSubscriptAssign(MD.Body.Stmts[0]);
    AssertEquals('array name', 'Buf', Stmt.ArrayName);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_StaticArray_Kind;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcByteBuf);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    AssertNotNull('ResolvedType set', Decl.ResolvedType);
    AssertEquals('kind is tyStaticArray',
      Ord(tyStaticArray), Ord(Decl.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_StaticArray_ElementType;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc(SrcByteBuf);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    AssertTrue('is TStaticArrayTypeDesc', Decl.ResolvedType is TStaticArrayTypeDesc);
    SAT := TStaticArrayTypeDesc(Decl.ResolvedType);
    AssertNotNull('ElementType set', SAT.ElementType);
    AssertEquals('element is tyByte', Ord(tyByte), Ord(SAT.ElementType.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_StaticArray_Bounds;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc(SrcByteBuf);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    SAT  := TStaticArrayTypeDesc(Decl.ResolvedType);
    AssertEquals('LowBound = 0', 0, SAT.LowBound);
    AssertEquals('HighBound = 7', 7, SAT.HighBound);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_StaticArray_ByteSize;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcByteBuf);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    { 8 elements × 1 byte each = 8 bytes }
    AssertEquals('ByteSize = 8', 8, Decl.ResolvedType.ByteSize());
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_StaticArray_IntArray;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcIntArray);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    { 4 elements × 4 bytes each = 16 bytes }
    AssertEquals('ByteSize = 16', 16, Decl.ResolvedType.ByteSize());
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_StaticArray_NonZero_LowBound;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc(SrcNonZero);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    SAT  := TStaticArrayTypeDesc(Decl.ResolvedType);
    AssertEquals('LowBound = 5', 5, SAT.LowBound);
    AssertEquals('HighBound = 9', 9, SAT.HighBound);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                       }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestCodegen_StaticArray_AllocEmitted;
var IR: string;
begin
  IR := GenIR(SrcByteBuf);
  { 8-byte Byte array: alloc4 alignment, 8 bytes total }
  AssertTrue('alloc4 8 emitted', Pos('alloc4 8', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_MemsetEmitted;
var IR: string;
begin
  IR := GenIR(SrcByteBuf);
  AssertTrue('memset call emitted', Pos('call $memset', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_WriteEmitted;
var IR: string;
begin
  IR := GenIR(SrcByteBuf);
  { Byte element write uses storeb }
  AssertTrue('storeb emitted', Pos('storeb', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_ReadEmitted;
var IR: string;
begin
  IR := GenIR(SrcReadBack);
  { Integer element read uses loadw }
  AssertTrue('loadw emitted', Pos('loadw', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_NonZero_OffsetSubtracted;
var IR: string;
begin
  IR := GenIR(SrcNonZero);
  { R[5] with LowBound=5: offset = (5-5)*4 = 0; sub instruction emitted }
  AssertTrue('sub for low-bound adjustment', Pos('=l sub', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_StringWrite_EmitsARC;
const
  Src =
    '''
        program P;
        var A: array[0..2] of string;
        begin
          A[0] := 'hello';
          A[0] := 'world'
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('string element write retains new value',
    Pos('call $_StringAddRef(', IR) > 0);
  AssertTrue('string element write releases old value',
    Pos('call $_StringRelease(', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_ClassWrite_EmitsARC;
const
  Src =
    '''
        program P;
        type TC = class(TObject) end;
        var A: array[0..2] of TC;
        begin
          A[0] := TC.Create();
          A[0] := TC.Create()
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('class element write retains new instance',
    Pos('call $_ClassAddRef(', IR) > 0);
  AssertTrue('class element write releases prior instance',
    Pos('call $_ClassRelease(', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_DynArray_StringWrite_EmitsARC;
const
  Src =
    '''
        program P;
        var A: array of string;
        begin
          SetLength(A, 3);
          A[0] := 'hello';
          A[0] := 'world'
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('dynarray string element write retains new value',
    Pos('call $_StringAddRef(', IR) > 0);
  AssertTrue('dynarray string element write releases old value',
    Pos('call $_StringRelease(', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_DynArray_ClassWrite_EmitsARC;
const
  Src =
    '''
        program P;
        type TC = class(TObject) end;
        var A: array of TC;
        begin
          SetLength(A, 3);
          A[0] := TC.Create();
          A[0] := TC.Create()
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('dynarray class element write retains new instance',
    Pos('call $_ClassAddRef(', IR) > 0);
  AssertTrue('dynarray class element write releases prior instance',
    Pos('call $_ClassRelease(', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Low / High tests                                                    }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_StaticArray_Low_ReturnsInteger;
var P: TProgram;
begin
  { If Low(A) on a static array fails semantic analysis an exception is raised here }
  P := AnalyseSrc(SrcLowHigh);
  try
    AssertNotNull('program analysed', P);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_StaticArray_High_ReturnsInteger;
var P: TProgram;
begin
  { If High(A) on a static array fails semantic analysis an exception is raised here }
  P := AnalyseSrc(SrcLowHigh);
  try
    AssertNotNull('program analysed', P);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_Low_EmitsLowBound;
var IR: string;
begin
  IR := GenIR(SrcLowHigh);
  { Low(A) on array[3..7] emits: copy 3 }
  AssertTrue('copy 3 for Low(A)', Pos('copy 3', IR) > 0);
end;

procedure TStaticArrayTests.TestCodegen_StaticArray_High_EmitsHighBound;
var IR: string;
begin
  IR := GenIR(SrcLowHigh);
  { High(A) on array[3..7] emits: copy 7 }
  AssertTrue('copy 7 for High(A)', Pos('copy 7', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Address-of tests                                                    }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestParse_AddrOf_NodeType;
var P: TProgram; MD: TMethodDecl; Assign: TAssignment;
begin
  P := ParseSrc(SrcAddrOf);
  try
    MD     := TMethodDecl(P.Block.ProcDecls[0]);
    Assign := TAssignment(MD.Body.Stmts[0]);
    AssertTrue('expr is TAddrOfExpr', Assign.Expr is TAddrOfExpr);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_AddrOf_ReturnsPointerType;
var P: TProgram; MD: TMethodDecl; Assign: TAssignment;
begin
  P := AnalyseSrc(SrcAddrOf);
  try
    MD     := TMethodDecl(P.Block.ProcDecls[0]);
    Assign := TAssignment(MD.Body.Stmts[0]);
    AssertNotNull('expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('@Buf[0] resolves to tyPointer',
      Ord(tyPointer), Ord(Assign.Expr.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_AddrOf_BaseTypeIsByte;
var P: TProgram; MD: TMethodDecl; Assign: TAssignment; PT: TPointerTypeDesc;
begin
  P := AnalyseSrc(SrcAddrOf);
  try
    MD     := TMethodDecl(P.Block.ProcDecls[0]);
    Assign := TAssignment(MD.Body.Stmts[0]);
    AssertTrue('is TPointerTypeDesc', Assign.Expr.ResolvedType is TPointerTypeDesc);
    PT := TPointerTypeDesc(Assign.Expr.ResolvedType);
    AssertNotNull('BaseType set', PT.BaseType);
    AssertEquals('BaseType is tyByte', Ord(tyByte), Ord(PT.BaseType.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestCodegen_AddrOf_NoLoad;
var IR: string;
begin
  IR := GenIR(SrcAddrOf);
  { @Buf[0] takes address only — no loadub should appear }
  AssertTrue('no loadub emitted', Pos('loadub', IR) < 0);
end;

procedure TStaticArrayTests.TestCodegen_AddrOf_AddressArithmetic;
var IR: string;
begin
  IR := GenIR(SrcAddrOf);
  { address is computed: base + offset using add }
  AssertTrue('=l add emitted', Pos('=l add', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Named array type alias — source constants                            }
{ ------------------------------------------------------------------ }

const
  SrcTypeAliasBasic =
    '''
        program SA;
        type
          TByteArr = array[0..7] of Byte;
        var Buf: TByteArr;
        begin
          Buf[0] := 55
        end.
        ''';

  SrcTypeAliasIntNonZero =
    '''
        program SA;
        type
          TIntRange = array[1..5] of Integer;
        var A: TIntRange;
        begin
          A[1] := 99
        end.
        ''';

  SrcTypeAliasVar =
    '''
        program SA;
        type
          TWordArr = array[0..3] of Integer;
        var W: TWordArr; X: Integer;
        begin
          W[0] := 7;
          X := W[0]
        end.
        ''';

  { Named integer subrange (0-based) used as the array index type.
    array[TIdx] of Integer must fold to array[0..2] of Integer. }
  SrcNamedSubrangeIndex =
    '''
        program SA;
        type
          TIdx = 0..2;
          TBuf = array[TIdx] of Integer;
        var A: TBuf;
        begin
          A[0] := 11
        end.
        ''';

  { Non-zero-based named integer subrange index: array[2..4]. }
  SrcNamedSubrangeIndexNonZero =
    '''
        program SA;
        type
          TIdx = 2..4;
          TBuf = array[TIdx] of Integer;
        var A: TBuf;
        begin
          A[2] := 11
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Named array type alias — tests                                       }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestParse_TypeAlias_ArrayParses;
var P: TProgram;
begin
  P := ParseSrc(SrcTypeAliasBasic);
  try
    AssertEquals('one type decl', 1, P.Block.TypeDecls.Count);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestParse_TypeAlias_ArrayName;
var P: TProgram; TD: TTypeDecl;
begin
  P := ParseSrc(SrcTypeAliasBasic);
  try
    TD := TTypeDecl(P.Block.TypeDecls.Items[0]);
    AssertEquals('type name', 'TByteArr', TD.Name);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_TypeAlias_KindIsStaticArray;
var P: TProgram; Sym: TSymbol;
begin
  P := AnalyseSrc(SrcTypeAliasBasic);
  try
    Sym := P.SymbolTable.Lookup('TByteArr');
    AssertTrue('symbol found', Sym <> nil);
    AssertEquals('kind is tyStaticArray',
      Ord(tyStaticArray), Ord(Sym.TypeDesc.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_TypeAlias_ElementType;
var P: TProgram; Sym: TSymbol; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc(SrcTypeAliasBasic);
  try
    Sym := P.SymbolTable.Lookup('TByteArr');
    AssertTrue('symbol found', Sym <> nil);
    SAT := TStaticArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('element kind is tyByte',
      Ord(tyByte), Ord(SAT.ElementType.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_TypeAlias_Bounds;
var P: TProgram; Sym: TSymbol; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc(SrcTypeAliasBasic);
  try
    Sym := P.SymbolTable.Lookup('TByteArr');
    SAT := TStaticArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('low=0',  0, SAT.LowBound);
    AssertEquals('high=7', 7, SAT.HighBound);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_TypeAlias_VarUsesAlias;
var P: TProgram; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcTypeAliasVar);
  try
    AssertTrue('at least one var decl', P.Block.Decls.Count >= 1);
    Decl := TVarDecl(P.Block.Decls.Items[0]);
    AssertEquals('var name is W', 'W', Decl.Names.Strings[0]);
    AssertTrue('ResolvedType set', Decl.ResolvedType <> nil);
    AssertEquals('var W has tyStaticArray',
      Ord(tyStaticArray), Ord(Decl.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_TypeAlias_NonZeroBase;
var P: TProgram; Sym: TSymbol; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc(SrcTypeAliasIntNonZero);
  try
    Sym := P.SymbolTable.Lookup('TIntRange');
    AssertTrue('TIntRange found', Sym <> nil);
    SAT := TStaticArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('low=1',  1, SAT.LowBound);
    AssertEquals('high=5', 5, SAT.HighBound);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestCodegen_TypeAlias_AllocEmitted;
var IR: string;
begin
  IR := GenIR(SrcTypeAliasBasic);
  { Global array is emitted as a data declaration containing the var name }
  AssertTrue('Buf appears in IR', Pos('Buf', IR) >= 0);
end;

procedure TStaticArrayTests.TestCodegen_TypeAlias_ElementSizeInAlloc;
var IR: string;
begin
  IR := GenIR(SrcTypeAliasBasic);
  // 8 bytes * 1 (Byte) = 8 bytes total; check the number 8 appears in the IR
  AssertTrue('size 8 appears in IR', Pos('8', IR) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_NamedSubrange_IndexFoldsToBounds;
var P: TProgram; Sym: TSymbol; SAT: TStaticArrayTypeDesc;
begin
  { type TIdx = 0..2; TBuf = array[TIdx] of Integer; must resolve to a static
    array with bounds 0..2, exactly as if written array[0..2]. }
  P := AnalyseSrc(SrcNamedSubrangeIndex);
  try
    Sym := P.SymbolTable.Lookup('TBuf');
    AssertTrue('TBuf found', Sym <> nil);
    AssertEquals('TBuf is static array',
      Ord(tyStaticArray), Ord(Sym.TypeDesc.Kind));
    SAT := TStaticArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('low=0',  0, SAT.LowBound);
    AssertEquals('high=2', 2, SAT.HighBound);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_NamedSubrange_NonZeroBase_IndexFoldsToBounds;
var P: TProgram; Sym: TSymbol; SAT: TStaticArrayTypeDesc;
begin
  { type TIdx = 2..4; TBuf = array[TIdx] of Integer; folds to array[2..4]. }
  P := AnalyseSrc(SrcNamedSubrangeIndexNonZero);
  try
    Sym := P.SymbolTable.Lookup('TBuf');
    AssertTrue('TBuf found', Sym <> nil);
    SAT := TStaticArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('low=2',  2, SAT.LowBound);
    AssertEquals('high=4', 4, SAT.HighBound);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Multi-dimensional arrays                                            }
{ ------------------------------------------------------------------ }

const
  SrcMultiDimComma =
    '''
        program SA;
        procedure Foo;
        var A: array[0..1, 0..2] of Integer;
        begin
          A[1, 2] := 99
        end;
        begin end.
        ''';

  SrcMultiDimChained =
    '''
        program SA;
        procedure Foo;
        var A: array[0..1] of array[0..2] of Integer;
        begin
          A[1][2] := 99
        end;
        begin end.
        ''';

  SrcMultiDimRead =
    '''
        program SA;
        function Foo: Integer;
        var A: array[0..1, 0..2] of Integer;
        begin
          Result := A[1, 2]
        end;
        begin end.
        ''';

  SrcMultiDim3D =
    '''
        program SA;
        procedure Foo;
        var A: array[0..1, 0..2, 0..3] of Integer;
        begin
          A[0, 0, 0] := 1
        end;
        begin end.
        ''';

procedure TStaticArrayTests.TestParse_MultiDim_CommaDecl_DesugarsToNested;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  { The comma form array[0..1, 0..2] of T is desugared at parse time into the
    nested type string array[0..1] of array[0..2] of T. }
  P := ParseSrc(SrcMultiDimComma);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    AssertEquals('desugared to nested array type',
      'array[0..1] of array[0..2] of Integer', Decl.TypeName);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_MultiDim_Kind_IsStaticArray;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcMultiDimComma);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    AssertTrue('outer is static array', Decl.ResolvedType is TStaticArrayTypeDesc);
    AssertEquals('outer high bound = 1', 1,
      TStaticArrayTypeDesc(Decl.ResolvedType).HighBound);
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_MultiDim_ElementType_IsInnerArray;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl; Inner: TTypeDesc;
begin
  P := AnalyseSrc(SrcMultiDimComma);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    Inner := TStaticArrayTypeDesc(Decl.ResolvedType).ElementType;
    AssertTrue('element type is itself a static array',
      Inner is TStaticArrayTypeDesc);
    AssertEquals('inner high bound = 2', 2,
      TStaticArrayTypeDesc(Inner).HighBound);
    AssertEquals('inner element is tyInteger', Ord(tyInteger),
      Ord(TStaticArrayTypeDesc(Inner).ElementType.Kind));
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_MultiDim_TotalByteSize;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcMultiDimComma);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    { 2 rows × 3 cols × 4 bytes = 24 bytes }
    AssertEquals('ByteSize = 24', 24, Decl.ResolvedType.ByteSize());
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestSemantic_MultiDim_ThreeDims;
var P: TProgram; MD: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcMultiDim3D);
  try
    MD   := TMethodDecl(P.Block.ProcDecls[0]);
    Decl := TVarDecl(MD.Body.Decls[0]);
    { 2 × 3 × 4 × 4 bytes = 96 bytes }
    AssertEquals('ByteSize = 96', 96, Decl.ResolvedType.ByteSize());
  finally P.Free(); end;
end;

procedure TStaticArrayTests.TestCodegen_MultiDim_AllocTotalSize;
var IR: string;
begin
  { The single backing allocation must cover the whole flattened block (24). }
  IR := GenIR(SrcMultiDimComma);
  AssertTrue('alloc of 24 bytes present', Pos('24', IR) >= 0);
end;

procedure TStaticArrayTests.TestCodegen_MultiDim_CommaWrite_EmitsRowOffset;
var IR: string;
begin
  { Writing A[1, 2] indexes row 1 (stride = inner size 12) then col 2
    (stride 4): both the row stride 12 and column stride 4 must appear. }
  IR := GenIR(SrcMultiDimComma);
  AssertTrue('row stride 12 present', Pos('mul', IR) >= 0);
  AssertTrue('stores the value 99', Pos('99', IR) >= 0);
end;

procedure TStaticArrayTests.TestCodegen_MultiDim_ChainedWrite_SameAsComma;
var IRComma, IRChained: string;
begin
  { The comma form and the explicit nested-chained form must produce identical
    IR — the comma form is pure sugar over the nested form. }
  IRComma   := GenIR(SrcMultiDimComma);
  IRChained := GenIR(SrcMultiDimChained);
  AssertEquals('comma form IR == chained form IR', IRComma, IRChained);
end;

procedure TStaticArrayTests.TestCodegen_MultiDim_CommaRead_NestedSubscript;
var IR: string;
begin
  { A read A[1, 2] must compute an inner-array address (a load of the final
    element off base + row offset + col offset). }
  IR := GenIR(SrcMultiDimRead);
  AssertTrue('emits a word load for the element', Pos('loadw', IR) >= 0);
end;

const
  SrcArrayReturn =
    '''
    program P;
    type TVec3 = array[0..2] of Integer;
    function MakeVec(A, B, C: Integer): TVec3;
    begin
      Result[0] := A;
      Result[1] := B;
      Result[2] := C
    end;
    var V: TVec3;
    begin
      V := MakeVec(1, 2, 3)
    end.
    ''';

procedure TStaticArrayTests.TestCodegen_ReturnStaticArray_SretParam;
var IR: string;
begin
  IR := GenIR(SrcArrayReturn);
  AssertTrue('sret hidden param', Pos('_par__sret', IR) >= 0);
end;

procedure TStaticArrayTests.TestCodegen_ReturnStaticArray_VoidReturn;
var IR: string;
begin
  IR := GenIR(SrcArrayReturn);
  AssertTrue('void return', Pos('ret', IR) >= 0);
end;

{ ------------------------------------------------------------------ }
{ Named constant array bounds (issue #109)                           }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_NamedConstBound_Simple;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    const N = 5;
    var A: array[0..N] of Integer;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    AssertTrue('resolved type', VD.ResolvedType <> nil);
    AssertTrue('is static array', VD.ResolvedType.Kind = tyStaticArray);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 0, SAT.LowBound);
    AssertEquals('high', 5, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_NamedConstBound_BothBounds;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    const Lo = 1; Hi = 10;
    var A: array[Lo..Hi] of Integer;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 1, SAT.LowBound);
    AssertEquals('high', 10, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_NamedConstBound_Expression;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    const N = 10;
    var A: array[0..N-1] of Integer;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 0, SAT.LowBound);
    AssertEquals('high', 9, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_NamedConstBound_TypeDecl;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    const MaxItems = 8;
    type TBuf = array[0..MaxItems-1] of Byte;
    var Buf: TBuf;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 0, SAT.LowBound);
    AssertEquals('high', 7, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestCodegen_NamedConstBound_CorrectSize;
var IR: string;
begin
  IR := GenIR('''
    program P;
    const N = 4;
    var A: array[0..N] of Integer;
    begin A[0] := 42 end.
    ''');
  AssertTrue('alloc for 5 ints (20 bytes)', Pos('20', IR) >= 0);
end;

{ ------------------------------------------------------------------ }
{ Enum-indexed var/type static arrays (issue #114)                   }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_EnumIndex_VarDecl;
var P: TProgram; VD: TVarDecl;
begin
  P := AnalyseSrc('''
    program P;
    type TColor = (Red, Green, Blue);
    var A: array[TColor] of Integer;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    AssertTrue('resolved type', VD.ResolvedType <> nil);
    AssertTrue('is static array', VD.ResolvedType.Kind = tyStaticArray);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_TypeDecl;
var P: TProgram; VD: TVarDecl;
begin
  P := AnalyseSrc('''
    program P;
    type TColor = (Red, Green, Blue);
    type TColorNames = array[TColor] of string;
    var Names: TColorNames;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    AssertTrue('resolved type', VD.ResolvedType <> nil);
    AssertTrue('is static array', VD.ResolvedType.Kind = tyStaticArray);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_Bounds;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    type TDir = (North, South, East, West);
    var D: array[TDir] of Integer;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 0, SAT.LowBound);
    AssertEquals('high', 3, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_BooleanIndex_TypeDecl;
var P: TProgram; VD: TVarDecl;
begin
  P := AnalyseSrc('''
    program P;
    type TFlags = array[Boolean] of string;
    var F: TFlags;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    AssertTrue('resolved type', VD.ResolvedType <> nil);
    AssertTrue('is static array', VD.ResolvedType.Kind = tyStaticArray);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_BooleanIndex_Bounds;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    var B: array[Boolean] of Integer;
    begin end.
    ''');
  try
    VD := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 0, SAT.LowBound);
    AssertEquals('high (False..True)', 1, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_BooleanIndex_ConstBounds;
var P: TProgram; Sym: TSymbol; SAT: TStaticArrayTypeDesc;
begin
  { GH #208: the INLINE form was rejected ("index type must be an enum") while
    the same constant via a named type was accepted.  Assert the folded bounds
    match the type-declaration path: array[Boolean] === array[0..1].
    TConstDecl carries no ResolvedType, so the check goes through the symbol
    the analyser publishes for the constant. }
  P := AnalyseSrc('''
    program P;
    const C: array[Boolean] of Integer = (10, 20);
    begin end.
    ''');
  try
    Sym := P.SymbolTable.Lookup('C');
    AssertTrue('constant is defined', Sym <> nil);
    AssertTrue('is a static array', Sym.TypeDesc.Kind = tyStaticArray);
    SAT := TStaticArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('low', 0, SAT.LowBound);
    AssertEquals('high (False..True)', 1, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_BooleanIndex_ConstWrongCount;
var Threw: Boolean; Msg: string;
begin
  { The count check must still fire for a Boolean index — accepting the type
    must not accept any arity. }
  Threw := False; Msg := '';
  try
    AnalyseSrc('''
      program P;
      const C: array[Boolean] of Integer = (1, 2, 3);
      begin end.
      ''');
  except
    on E: Exception do begin Threw := True; Msg := E.Message; end;
  end;
  AssertTrue('expected semantic error', Threw);
  AssertTrue('reports the arity mismatch, got: ' + Msg,
    Pos('has 3 element(s)', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_StringIndex_RaisesTargetedError;
var Threw: Boolean; Msg: string;
begin
  Threw := False; Msg := '';
  try
    AnalyseSrc('''
      program P;
      type TBad = array[string] of Integer;
      begin end.
      ''');
  except
    on E: Exception do begin Threw := True; Msg := E.Message; end;
  end;
  AssertTrue('expected semantic error', Threw);
  AssertTrue('mentions valid index types, got: ' + Msg,
    Pos('not a valid array index type', Msg) >= 0);
end;

procedure TStaticArrayTests.TestCodegen_EnumIndex_AllocSize;
var IR: string;
begin
  IR := GenIR('''
    program P;
    type TColor = (Red, Green, Blue);
    var A: array[TColor] of Integer;
    begin A[Red] := 42 end.
    ''');
  AssertTrue('alloc for 3 ints (12 bytes)', Pos('12', IR) >= 0);
end;

initialization
  RegisterTest(TStaticArrayTests);

end.
