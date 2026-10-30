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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TStaticArrayTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    { Analyses ASrc and returns the semantic error message, or '' if the
      source analysed cleanly. }
    function SemanticErrMsg(const ASrc: string): string;
  published
    { O.Rows[I] := Row on an array-of-static-array field copies the row's
      bytes (arm64 stopped with 'field array element of this type') }
    procedure TestCodegen_FieldArrayOfRows_ElementStoreCopies;
    { x86-64 by-value static-array params keep a POINTER to the callee's
      copy in their slot: an element write and a whole-array store must go
      through it (both took the slot's own address and wrote over the
      frame), and a managed copy co-owns its elements }
    procedure TestNative_ByValueArrayParam_WritesThroughPointer;
    procedure TestNative_ByValueManagedArrayParam_RetainsElements;
    { R.A := G with A a static-array field copies the bytes (x86-64 stored
      G's ADDRESS over A[0..1]) }
    procedure TestNative_StaticArrayFieldStore_CopiesBytes;
    { F := G inside a method, F a static array of strings: the element walk
      retains (x86-64 handed the array type to the RECORD walk, which read
      its descriptor as a field list -- a layout-dependent compiler crash) }
    procedure TestNative_ImplicitSelfStaticArrayStore_RetainsElements;
    { R.F := [a, b] with R a record field of Self is a SET literal ("expected
      'TSmallSet' but got 'array of TColor'") }
    procedure TestSemantic_SetLiteralIntoSelfRecordField;
    { M[I] := D on an array of dyn arrays co-owns the block (x86-64 stored
      the raw pointer -- dropping D freed what M[I] pointed at; arm64
      refused the store) }
    procedure TestNative_DynArrayElement_Retained;
    { X := O.A[I] with A an array FIELD of Doubles loads the ELEMENT (x86-64
      loaded the field's first bytes) }
    procedure TestNative_FloatArrayFieldElement_LoadsElement;
    { MakeObj().A[I] := V parses as an element write through the call }
    procedure TestParse_CallResultArrayFieldElemWrite;
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

    { ------------------------------------------------------------------ }
    { Low / High                                                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StaticArray_Low_ReturnsInteger;
    procedure TestSemantic_StaticArray_High_ReturnsInteger;

    { ------------------------------------------------------------------ }
    { Address-of                                                           }
    { ------------------------------------------------------------------ }
    procedure TestParse_AddrOf_NodeType;
    procedure TestSemantic_AddrOf_ReturnsPointerType;
    procedure TestSemantic_AddrOf_BaseTypeIsByte;

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

    { ------------------------------------------------------------------ }
    { Function returning static array by value (issue #112)              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Named constant array bounds (issue #109)                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_NamedConstBound_Simple;
    procedure TestSemantic_NamedConstBound_BothBounds;
    procedure TestSemantic_NamedConstBound_Expression;
    procedure TestSemantic_NamedConstBound_TypeDecl;

    { ------------------------------------------------------------------ }
    { Enum-indexed var/type static arrays (issue #114)                   }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_EnumIndex_VarDecl;
    procedure TestSemantic_EnumIndex_TypeDecl;
    procedure TestSemantic_EnumIndex_Bounds;
    { GH #181 — Boolean is a valid 2-element ordinal index type. }
    procedure TestSemantic_BooleanIndex_TypeDecl;
    procedure TestSemantic_BooleanIndex_Bounds;
    { GH #208 — the same index type in an inline typed CONSTANT. }
    procedure TestSemantic_BooleanIndex_ConstBounds;
    procedure TestSemantic_BooleanIndex_ConstWrongCount;
    procedure TestSemantic_StringIndex_RaisesTargetedError;
    { an 8- or 16-bit integer type indexes its whole range, as in FPC and
      Delphi; a 32-bit one is rejected (found by the ordinal matrix) }
    procedure TestSemantic_SmallIntTypeIndex_Bounds;
    procedure TestSemantic_Int32TypeIndex_Rejected;
    { a MULTI-dimensional array takes the same index types as a
      single-dimensional one: Boolean, Byte, Int8 and an integer subrange in
      any position (only enum dimensions worked: "Unknown enum type
      'boolean' in array dimension"; found probing GH #240) }
    procedure TestSemantic_MultiDim_TypeIndexes_Bounds;
    procedure TestSemantic_MultiDim_Int32Index_Rejected;
    { GH #239: an sret function's Result passed to a var parameter is the
      caller's buffer: x86-64 passed the SLOT holding that pointer, so the
      callee's write clobbered the pointer and the next Result write
      crashed.  arm64 keeps Result in a local buffer, whose address is
      right. }
    procedure TestNative_SretResultAsVarArg_PassesBuffer;

    { ------------------------------------------------------------------ }
    { BUG-20260921-const-array-index-out-of-bounds — a CONSTANT index    }
    { outside the declared bounds is a compile-time error.               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ConstIndex_Write_AboveHigh_Raises;
    procedure TestSemantic_ConstIndex_Write_Negative_Raises;
    procedure TestSemantic_ConstIndex_Read_AboveHigh_Raises;
    procedure TestSemantic_ConstIndex_Read_BelowLow_Raises;
    procedure TestSemantic_ConstIndex_NonZeroBase_BelowLow_Raises;
    procedure TestSemantic_ConstIndex_NamedConst_AboveHigh_Raises;
    procedure TestSemantic_ConstIndex_FoldedExpr_AboveHigh_Raises;
    procedure TestSemantic_ConstIndex_ErrorNamesBoundsAndIndex;
    { Controls — these must keep compiling cleanly. }
    procedure TestSemantic_ConstIndex_InRange_Accepted;
    procedure TestSemantic_ConstIndex_BoundaryLowAndHigh_Accepted;
    procedure TestSemantic_ConstIndex_NonZeroBase_InRange_Accepted;
    procedure TestSemantic_VarIndex_NotDiagnosed;
    procedure TestSemantic_ConstIndex_DynArray_NotDiagnosed;
    procedure TestSemantic_ConstIndex_Nested2D_AboveHigh_Raises;
    { A variable/parameter/field whose name collides with an enum member must
      NOT be folded as that member's ordinal — it is not a constant at all.
      Re-resolving the name inside the fold got this wrong and rejected
      legal programs; the fold now trusts uSemantic's IsConstant annotation. }
    procedure TestSemantic_EnumShadowedByGlobalVar_NotFolded;
    procedure TestSemantic_EnumShadowedByLocalVar_NotFolded;
    procedure TestSemantic_EnumShadowedByParam_NotFolded;
    procedure TestSemantic_EnumShadowedByField_NotFolded;

    { ------------------------------------------------------------------ }
    { BUG-20260922-explicit-ordinal-enum-array-bounds — an enum with     }
    { EXPLICIT ordinals indexes an array over its MIN..MAX ordinal span, }
    { not 0..Count-1 (which mis-sized the array while member indices     }
    { folded to real ordinals, landing outside it).                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_EnumIndex_ExplicitOrdinals_BoundsSpanMinMax;
    procedure TestSemantic_EnumIndex_NegativeOrdinal_BoundsSpanMinMax;
    procedure TestSemantic_EnumIndex_NonMonotonic_BoundsSpanMinMax;
    procedure TestSemantic_EnumIndex_MultiDim_OuterSpansMinMax;
    procedure TestSemantic_EnumIndex_MultiDim_InnerSpansMinMax;
    procedure TestSemantic_ConstArray_ExplicitOrdinals_NeedsSpanElements;
    procedure TestSemantic_ConstArray_ExplicitOrdinals_SpanElementsAccepted;
    procedure TestSemantic_ClassConstArray_ExplicitOrdinals_NeedsSpanElements;
    procedure TestSemantic_InitGlobal_ExplicitOrdinals_NeedsSpanElements;
    { A contiguous 0-based enum is unchanged — the overwhelmingly common
      case must produce identical bounds, and hence identical layout. }
    procedure TestSemantic_EnumIndex_ZeroBased_Unchanged;
    procedure TestSemantic_EnumIndex_PartiallyExplicit_StillZeroBased;

    { ------------------------------------------------------------------ }
    { BUG-20260922-class-const-array-index-unchecked — the constant       }
    { index range check must cover a CLASS-level const array too, not     }
    { only a unit-level one.                                              }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ClassConstArray_ConstIndex_AboveHigh_Raises;
    procedure TestSemantic_ClassConstArray_ConstIndex_Negative_Raises;
    procedure TestSemantic_ClassConstArray_ConstIndex_ViaInstance_Raises;
    procedure TestSemantic_ClassConstArray_ConstIndex_InRange_Accepted;
    procedure TestSemantic_ClassConstArray_VarIndex_NotDiagnosed;

    { ------------------------------------------------------------------ }
    { Managed static arrays (array[..] of String / interface / ...) -- P4-8 }
    { ------------------------------------------------------------------ }
    { a by-value managed array parameter: the callee's copy co-owns every
      element (retained on entry, released at exit).  arm64 had no lowering
      at all (a compile-time NotYet) }
    procedure TestCodegen_ManagedArrayByValueParam_RetainedAndReleased;
    { F.A := L, AA[I] := L, R.A := MkA(): the copy retains the source's
      elements and releases the destination's old ones (arm64: NotYet) }
    procedure TestCodegen_ManagedArrayStores_RetainAndRelease;
    { an array-of-interface element read from a const parameter indexed the
      frame instead of the array: x86-64 crashed }
    procedure TestCodegen_IntfArrayParamElement_ReadsThroughParam;
    { a closure held in an array element or behind a pointer, passed as a
      by-value closure argument, passes the element's ADDRESS (the callee
      copies 16 bytes through it); the loaded first word crashed }
    procedure TestCodegen_ClosureElementArg_PassesAddress;
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
        var A: array[0..3] of Int32;
        begin
          A[2] := 99
        end;
        begin end.
        ''';

  SrcNonZero =
    '''
        program SA;
        procedure Foo;
        var R: array[5..9] of Int;
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
        function Len: Int;
        var A: array[3..7] of Int;
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
          TIntRange = array[1..5] of Int;
        var A: TIntRange;
        begin
          A[1] := 99
        end.
        ''';

  SrcTypeAliasVar =
    '''
        program SA;
        type
          TWordArr = array[0..3] of Int;
        var W: TWordArr; X: Int;
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
          TBuf = array[TIdx] of Int;
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
          TBuf = array[TIdx] of Int;
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
        var A: array[0..1, 0..2] of Int32;
        begin
          A[1, 2] := 99
        end;
        begin end.
        ''';

  SrcMultiDim3D =
    '''
        program SA;
        procedure Foo;
        var A: array[0..1, 0..2, 0..3] of Int32;
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
      'array[0..1] of array[0..2] of Int32', Decl.TypeName);
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

const
{ ------------------------------------------------------------------ }
{ Named constant array bounds (issue #109)                           }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_NamedConstBound_Simple;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    const N = 5;
    var A: array[0..N] of Int;
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
    var A: array[Lo..Hi] of Int;
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
    var A: array[0..N-1] of Int;
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

{ ------------------------------------------------------------------ }
{ Enum-indexed var/type static arrays (issue #114)                   }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_EnumIndex_VarDecl;
var P: TProgram; VD: TVarDecl;
begin
  P := AnalyseSrc('''
    program P;
    type TColor = (Red, Green, Blue);
    var A: array[TColor] of Int;
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
    var D: array[TDir] of Int;
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
    var B: array[Boolean] of Int;
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

procedure TStaticArrayTests.TestSemantic_MultiDim_TypeIndexes_Bounds;
var P: TProgram;

  procedure CheckDecl(AIdx, ALo, AHi, AInnerLo, AInnerHi: Int;
                      const AWhat: string);
  var Outer, Inner: TStaticArrayTypeDesc;
  begin
    Outer := TStaticArrayTypeDesc(TVarDecl(P.Block.Decls.Items[AIdx]).ResolvedType);
    Inner := TStaticArrayTypeDesc(Outer.ElementType);
    AssertEquals(AWhat + ' low', ALo, Outer.LowBound);
    AssertEquals(AWhat + ' high', AHi, Outer.HighBound);
    AssertEquals(AWhat + ' inner low', AInnerLo, Inner.LowBound);
    AssertEquals(AWhat + ' inner high', AInnerHi, Inner.HighBound);
  end;

begin
  P := AnalyseSrc('''
    program P;
    type TC = (cRed, cGreen, cBlue); TMid = cGreen..cBlue; TIdx = 3..5;
    var
      A: array[Boolean, 0..1] of Int;
      B: array[0..1, Boolean] of Int;
      C: array[Byte, TC] of Byte;
      D: array[TIdx, Int8] of Byte;
      E: array[TMid, Boolean] of Int;
    begin end.
    ''');
  try
    CheckDecl(0, 0, 1, 0, 1, 'Boolean, 0..1');
    CheckDecl(1, 0, 1, 0, 1, '0..1, Boolean');
    CheckDecl(2, 0, 255, 0, 2, 'Byte, TC');
    CheckDecl(3, 3, 5, -128, 127, 'TIdx, Int8');
    CheckDecl(4, 1, 2, 0, 1, 'TMid, Boolean');
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_MultiDim_Int32Index_Rejected;
var Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A: array[Int32, 0..1] of Byte;
    begin end.
    ''');
  AssertTrue('Int32 dimension rejected: ' + Msg,
    Pos('not a valid array index type', Msg) >= 0);
  Msg := SemanticError('''
    program P;
    var A: array[0..1, TNope] of Byte;
    begin end.
    ''');
  AssertTrue('unknown dimension type named: ' + Msg,
    Pos('Unknown index type ''TNope''', Msg) >= 0);
end;

procedure TStaticArrayTests.TestNative_SretResultAsVarArg_PassesBuffer;
const
  Src = '''
    program P;
    type TArr = array[0..1] of Int32;
    procedure Clear(var A: TArr); begin A[0] := 0 end;
    function NewArr: TArr;
    begin
      Clear(Result);
      Result[0] := 7
    end;
    var R: TArr;
    begin
      R := NewArr()
    end.
    ''';
begin
  { x86-64: the slot at -8 holds the caller's buffer pointer -- load it,
    never leaq the slot; arm64: the local Result buffer at x29-8 }
  AssertEquals('Clear(Result) passes the buffer', '',
    AsmMissing(Src,
      #9'movq -8(%rbp), %rax' + #10 + #9'movq %rax, %rdi' + #10 +
        #9'callq Clear',
      #9'sub x0, x29, #8' + #10 + #9'str x0, [sp, #-16]!'));
end;

procedure TStaticArrayTests.TestSemantic_SmallIntTypeIndex_Bounds;
var P: TProgram; SAT: TStaticArrayTypeDesc;

  procedure CheckDecl(AIdx: Int; ALow, AHigh: Int; const AWhat: string);
  begin
    SAT := TStaticArrayTypeDesc(TVarDecl(P.Block.Decls.Items[AIdx]).ResolvedType);
    AssertEquals(AWhat + ' low', ALow, SAT.LowBound);
    AssertEquals(AWhat + ' high', AHigh, SAT.HighBound);
  end;

begin
  P := AnalyseSrc('''
    program P;
    var A: array[Byte] of Int32;
    var B: array[Int8] of Int32;
    var C: array[UInt16] of Byte;
    var D: array[Int16] of Byte;
    begin end.
    ''');
  try
    CheckDecl(0, 0, 255, 'Byte');
    CheckDecl(1, -128, 127, 'Int8');
    CheckDecl(2, 0, 65535, 'UInt16');
    CheckDecl(3, -32768, 32767, 'Int16');
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_Int32TypeIndex_Rejected;
begin
  AssertTrue('Int32 index rejected', Pos('not a valid array index type',
    SemanticError('''
      program P;
      var A: array[Int32] of Byte;
      begin end.
      ''')) >= 0);
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
    const C: array[Boolean] of Int32 = (10, 20);
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
      const C: array[Boolean] of Int32 = (1, 2, 3);
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
      type TBad = array[string] of Int;
      begin end.
      ''');
  except
    on E: Exception do begin Threw := True; Msg := E.Message; end;
  end;
  AssertTrue('expected semantic error', Threw);
  AssertTrue('mentions valid index types, got: ' + Msg,
    Pos('not a valid array index type', Msg) >= 0);
end;

{ ------------------------------------------------------------------ }
{ BUG-20260921-const-array-index-out-of-bounds                       }
{                                                                     }
{ When the index is a compile-time constant and the array is static,  }
{ both bounds are known, so an out-of-range index is diagnosable at   }
{ compile time.  Before the fix a positive OOB index silently wrote   }
{ past the array and a negative one segfaulted at runtime.            }
{ ------------------------------------------------------------------ }

function TStaticArrayTests.SemanticErrMsg(const ASrc: string): string;
var P: TProgram;
begin
  Result := '';
  P := nil;
  try
    try
      P := AnalyseSrc(ASrc);
    except
      on E: Exception do Result := E.Message;
    end;
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_Write_AboveHigh_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    var a: array[0..4] of Int;
    begin a[99] := 7 end.
    ''');
  AssertTrue('a[99] on array[0..4] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_Write_Negative_Raises;
var Msg: string;
begin
  { The crashing case: -3 parses as BinaryExpr(0 - 3), so the fold must
    handle it rather than only spotting a negative literal. }
  Msg := SemanticErrMsg('''
    program P;
    var a: array[0..4] of Int;
    begin a[-3] := 5 end.
    ''');
  AssertTrue('a[-3] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_Read_AboveHigh_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    var a: array[0..4] of Int; x: Int;
    begin x := a[77] end.
    ''');
  AssertTrue('read of a[77] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_Read_BelowLow_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    var a: array[0..4] of Int; x: Int;
    begin x := a[-1] end.
    ''');
  AssertTrue('read of a[-1] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_NonZeroBase_BelowLow_Raises;
var Msg: string;
begin
  { 0 is a valid index for array[0..4] but NOT for array[1..5] — the check
    must use the declared LowBound, not assume 0-based. }
  Msg := SemanticErrMsg('''
    program P;
    var a: array[1..5] of Int;
    begin a[0] := 1 end.
    ''');
  AssertTrue('a[0] on array[1..5] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_NamedConst_AboveHigh_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    const K = 9;
    var a: array[0..4] of Int;
    begin a[K] := 1 end.
    ''');
  AssertTrue('a[K] with K=9 must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_FoldedExpr_AboveHigh_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    var a: array[0..4] of Int;
    begin a[2 + 3] := 1 end.
    ''');
  AssertTrue('a[2+3] on array[0..4] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_ErrorNamesBoundsAndIndex;
var Msg: string;
begin
  { The diagnostic must state the offending index and the valid range, so
    the programmer does not have to go and look the declaration up. }
  Msg := SemanticErrMsg('''
    program P;
    var a: array[1..5] of Int;
    begin a[42] := 1 end.
    ''');
  AssertTrue('names the index 42, got: ' + Msg, Pos('42', Msg) >= 0);
  AssertTrue('names the valid range 1..5, got: ' + Msg, Pos('1..5', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_InRange_Accepted;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    var a: array[0..4] of Int;
    begin a[3] := 7 end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_BoundaryLowAndHigh_Accepted;
begin
  { Off-by-one guard: both bounds are INCLUSIVE and must be accepted. }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    var a: array[0..4] of Int;
    begin a[0] := 1; a[4] := 2 end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_NonZeroBase_InRange_Accepted;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    var a: array[1..5] of Int;
    begin a[1] := 1; a[5] := 2 end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_VarIndex_NotDiagnosed;
begin
  { A variable index is not a compile-time fact — it must NOT be rejected,
    even when the value would obviously be out of range at runtime. }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    var a: array[0..4] of Int; i: Int;
    begin i := 99; a[i] := 7 end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_DynArray_NotDiagnosed;
begin
  { A dynamic array's length is not a compile-time fact — out of scope
    of this check (see BUG-20260921-no-compile-time-range-check). }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    var d: array of Int;
    begin SetLength(d, 3); d[50] := 9 end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_ConstIndex_Nested2D_AboveHigh_Raises;
var Msg: string;
begin
  { Multi-dimensional access lowers to A[I][J]; the inner subscript's base
    is a static-array-typed expression rather than a named variable. }
  Msg := SemanticErrMsg('''
    program P;
    var m: array[0..2, 0..2] of Int;
    begin m[1, 7] := 3 end.
    ''');
  AssertTrue('m[1,7] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_EnumShadowedByGlobalVar_NotFolded;
begin
  { 'Red' here is an Integer variable, not TColor.Red — folding it to the
    ordinal 0 would wrongly report it out of bounds of array[1..5]. }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    type TColor = (Red, Green, Blue);
    var A: array[1..5] of Int; Red: Int;
    begin Red := 3; A[Red] := 1 end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_EnumShadowedByLocalVar_NotFolded;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    type TColor = (Red, Green, Blue);
    var A: array[1..5] of Int;
    procedure Fill();
    var Blue: Int;
    begin Blue := 4; A[Blue] := 1 end;
    begin Fill() end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_EnumShadowedByParam_NotFolded;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    type TColor = (Red, Green, Blue);
    var A: array[5..9] of Int;
    procedure Fill(Green: Int);
    begin A[Green] := 1 end;
    begin Fill(7) end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_EnumShadowedByField_NotFolded;
begin
  { A class FIELD is not in the symbol table at all, so a lookup-based guard
    would still mis-fold this one — the IsConstant annotation is what makes
    it correct. }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    type
      TColor = (Red, Green, Blue);
      TC = class
        Red: Int;
        A: array[1..5] of Int;
        procedure Go();
      end;
    procedure TC.Go();
    begin Red := 3; A[Red] := 1 end;
    var C: TC;
    begin C := TC.Create(); C.Go() end.
    '''));
end;

{ ------------------------------------------------------------------ }
{ BUG-20260922-explicit-ordinal-enum-array-bounds                    }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_EnumIndex_ExplicitOrdinals_BoundsSpanMinMax;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    type TColor = (Red = 5, Green = 10);
    var A: array[TColor] of Int;
    begin end.
    ''');
  try
    VD  := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low is MinOrdinal', 5, SAT.LowBound);
    AssertEquals('high is MaxOrdinal', 10, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_NegativeOrdinal_BoundsSpanMinMax;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  { A negative low bound is already supported for array[-3..2]. }
  P := AnalyseSrc('''
    program P;
    type TS = (sA = -3, sB = 2);
    var A: array[TS] of Int;
    begin end.
    ''');
  try
    VD  := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', -3, SAT.LowBound);
    AssertEquals('high', 2, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_NonMonotonic_BoundsSpanMinMax;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  { MaxOrdinal is a max over ALL members, not the last one declared. }
  P := AnalyseSrc('''
    program P;
    type TN = (nA = 10, nB = 20, nC = 15);
    var A: array[TN] of Int;
    begin end.
    ''');
  try
    VD  := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 10, SAT.LowBound);
    AssertEquals('high is the MAX, not the last', 20, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_MultiDim_OuterSpansMinMax;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    type TColor = (Red = 5, Green = 10);
    var A: array[TColor, 0..1] of Int;
    begin end.
    ''');
  try
    VD  := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('outer low', 5, SAT.LowBound);
    AssertEquals('outer high', 10, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_MultiDim_InnerSpansMinMax;
var P: TProgram; VD: TVarDecl; SAT, Inner: TStaticArrayTypeDesc;
begin
  P := AnalyseSrc('''
    program P;
    type TColor = (Red = 5, Green = 10);
    var A: array[0..1, TColor] of Int;
    begin end.
    ''');
  try
    VD    := TVarDecl(P.Block.Decls.Items[0]);
    SAT   := TStaticArrayTypeDesc(VD.ResolvedType);
    Inner := TStaticArrayTypeDesc(SAT.ElementType);
    AssertEquals('inner low', 5, Inner.LowBound);
    AssertEquals('inner high', 10, Inner.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_ConstArray_ExplicitOrdinals_NeedsSpanElements;
var Msg: string;
begin
  { USER-VISIBLE CHANGE: the initialiser is positional over the SPAN, so a
    sparse enum needs one value per ordinal slot, holes included. }
  Msg := SemanticErrMsg('''
    program P;
    type TColor = (Red = 5, Green = 10);
    const A: array[TColor] of Int32 = (1, 2);
    begin end.
    ''');
  AssertTrue('2 elements for a 6-slot span must be rejected, got: ' + Msg,
    Pos('element', Msg) >= 0);
  AssertTrue('message states the span, got: ' + Msg,
    Pos('5..10', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ConstArray_ExplicitOrdinals_SpanElementsAccepted;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    type TColor = (Red = 5, Green = 10);
    const A: array[TColor] of Int32 = (1, 0, 0, 0, 0, 2);
    begin WriteLn(A[Red]) end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_ClassConstArray_ExplicitOrdinals_NeedsSpanElements;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type
      TColor = (Red = 5, Green = 10);
      TC = class
      public
        const Names: array[TColor] of Int32 = (1, 2);
      end;
    begin end.
    ''');
  AssertTrue('class const needs span elements, got: ' + Msg,
    Pos('element', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_InitGlobal_ExplicitOrdinals_NeedsSpanElements;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TColor = (Red = 5, Green = 10);
    var A: array[TColor] of Int32 = (1, 2);
    begin end.
    ''');
  AssertTrue('global initialiser needs span elements, got: ' + Msg,
    Pos('element', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_ZeroBased_Unchanged;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  { The common case: MinOrdinal=0 and MaxOrdinal=Count-1, so the new rule
    produces identical bounds — and hence identical layout and IR. }
  P := AnalyseSrc('''
    program P;
    type TDir = (North, South, East, West);
    var D: array[TDir] of Int;
    begin end.
    ''');
  try
    VD  := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low unchanged', 0, SAT.LowBound);
    AssertEquals('high unchanged', 3, SAT.HighBound);
  finally
    P.Free();
  end;
end;

procedure TStaticArrayTests.TestSemantic_EnumIndex_PartiallyExplicit_StillZeroBased;
var P: TProgram; VD: TVarDecl; SAT: TStaticArrayTypeDesc;
begin
  { (A, B = 1, C) is still exactly 0..2 — also unchanged. }
  P := AnalyseSrc('''
    program P;
    type TP = (pA, pB = 1, pC);
    var A: array[TP] of Int;
    begin end.
    ''');
  try
    VD  := TVarDecl(P.Block.Decls.Items[0]);
    SAT := TStaticArrayTypeDesc(VD.ResolvedType);
    AssertEquals('low', 0, SAT.LowBound);
    AssertEquals('high', 2, SAT.HighBound);
  finally
    P.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ BUG-20260922-class-const-array-index-unchecked                     }
{ ------------------------------------------------------------------ }

procedure TStaticArrayTests.TestSemantic_ClassConstArray_ConstIndex_AboveHigh_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type
      TE = (eA, eB);
      TC = class
      public
        const Names: array[TE] of Int32 = (1, 2);
      end;
    begin WriteLn(TC.Names[7]) end.
    ''');
  AssertTrue('TC.Names[7] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ClassConstArray_ConstIndex_Negative_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type
      TE = (eA, eB);
      TC = class
      public
        const Names: array[TE] of Int32 = (1, 2);
      end;
    begin WriteLn(TC.Names[-3]) end.
    ''');
  AssertTrue('TC.Names[-3] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ClassConstArray_ConstIndex_ViaInstance_Raises;
var Msg: string;
begin
  { Reading the class const through an INSTANCE is a separate resolution
    arm from the bare TypeName.Const form, and had the same omission. }
  Msg := SemanticErrMsg('''
    program P;
    type
      TE = (eA, eB);
      TC = class
      public
        const Names: array[TE] of Int32 = (1, 2);
      end;
    var c: TC;
    begin c := TC.Create(); WriteLn(c.Names[9]) end.
    ''');
  AssertTrue('c.Names[9] must be rejected, got: ' + Msg,
    Pos('out of bounds', Msg) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_ClassConstArray_ConstIndex_InRange_Accepted;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    type
      TE = (eA, eB);
      TC = class
      public
        const Names: array[TE] of Int32 = (11, 22);
      end;
    begin WriteLn(TC.Names[0], ' ', TC.Names[1]) end.
    '''));
end;

procedure TStaticArrayTests.TestSemantic_ClassConstArray_VarIndex_NotDiagnosed;
begin
  { A variable index is not a compile-time fact — must not be rejected. }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
    program P;
    type
      TE = (eA, eB);
      TC = class
      public
        const Names: array[TE] of Int32 = (1, 2);
      end;
    var i: Int;
    begin i := 9; WriteLn(TC.Names[i]) end.
    '''));
end;

procedure TStaticArrayTests.TestNative_ByValueArrayParam_WritesThroughPointer;
const
  Src = '''
    program P;
    type TArr = array[0..2] of Int32;
    procedure Outer(A: TArr; B: TArr);
    begin
      A[1] := 9;
      A := B;
    end;
    var G: TArr;
    begin
      Outer(G, G);
    end.
    ''';
begin
  { x86-64: the slot at -8 holds the copy's address; arm64 keeps the copy
    inline at x29-16 }
  AssertEquals('element write through the copy', '',
    AsmMissing(Src,
      #9'movq -8(%rbp), %rcx' + #10 + #9'addq %rcx, %rax',
      #9'sub x0, x29, #16' + #10 + #9'ldr x1, [sp], #16'));
  AssertEquals('whole-array store into the copy', '',
    AsmMissing(Src,
      #9'movq -8(%rbp), %rdi' + #10 + #9'movq $12, %rdx' + #10 +
        #9'callq memcpy',
      #9'sub x0, x29, #16' + #10 + #9'movz x2, #12' + #10 + #9'bl _memcpy'));
end;

procedure TStaticArrayTests.TestNative_ByValueManagedArrayParam_RetainsElements;
const
  Src = '''
    program P;
    type TSA = array[0..1] of String;
    procedure Strs(S: TSA);
    begin
      WriteLn(S[0]);
    end;
    var G: TSA;
    begin
      Strs(G);
    end.
    ''';
var
  AsmT: string;
begin
  { x86-64 only: arm64 does not lower a managed static-array parameter yet
    (a compile-time NotYet, never silent) }
  AsmT := GenAsm(Src, TargetX86_64);
  AssertTrue('each element retained on entry',
    Pos(#9'movq -8(%rbp), %rbx' + #10 + #9'pushq %r15', AsmT) >= 0);
  AssertTrue('and released at exit',
    Pos(#9'callq _StringRelease', AsmT) >= 0);
end;

procedure TStaticArrayTests.TestNative_StaticArrayFieldStore_CopiesBytes;
const
  Src = '''
    program P;
    type
      TArr = array[0..2] of Int32;
      TRec = record N: Int32; A: TArr; end;
    var G: TArr; R: TRec;
    begin
      R.A := G;
    end.
    ''';
begin
  AssertEquals('a 12-byte copy, not an 8-byte address store', '',
    AsmMissing(Src,
      #9'movq %r15, %rdi' + #10 + #9'movq %rbx, %rsi' + #10 +
        #9'movq $12, %rdx' + #10 + #9'callq memcpy',
      #9'add x0, x0, #4' + #10 + #9'movz x2, #12' + #10 + #9'bl _memcpy'));
end;

procedure TStaticArrayTests.TestNative_ImplicitSelfStaticArrayStore_RetainsElements;
const
  Src = '''
    program P;
    type
      TSA = array[0..1] of String;
      TObj = class F: TSA; procedure Put(const G: TSA); end;
    procedure TObj.Put(const G: TSA); begin F := G end;
    begin
    end.
    ''';
begin
  AssertTrue('elements retained',
    Pos(#9'callq _StringAddRef', GenAsm(Src, TargetX86_64)) >= 0);
end;

procedure TStaticArrayTests.TestSemantic_SetLiteralIntoSelfRecordField;
var
  Prog: TProgram;
begin
  Prog := Analyse('''
    program P;
    type
      TColor = (cRed, cGreen, cBlue);
      TSmallSet = set of TColor;
      TBig = set of 0..127;
      TRec = record F: TSmallSet; B: TBig; end;
      TObj = class R: TRec; procedure Run; end;
    procedure TObj.Run; begin R.F := [cRed, cBlue]; R.B := [3, 100] end;
    begin
    end.
    ''');
  AssertNotNull('analysed', Prog);
  Prog.Free();
end;

procedure TStaticArrayTests.TestNative_DynArrayElement_Retained;
const
  Src = '''
    program P;
    type TDyn = array of Int;
    var M: array of TDyn; D: TDyn;
    begin
      M[0] := D;
    end.
    ''';
begin
  AssertEquals('retain new, release old', '',
    AsmMissing(Src,
      #9'callq _DynArrayAddRef' + #10 + #9'movq (%rsp), %rcx' + #10 +
        #9'movq (%rcx), %rdi' + #10 + #9'callq _DynArrayRelease',
      #9'bl __DynArrayAddRef' + #10 + #9'ldr x0, [sp], #16' + #10 +
        #9'str x0, [sp, #-16]!' + #10 + #9'ldr x9, [sp, #16]' + #10 +
        #9'ldr x0, [x9]' + #10 + #9'bl __DynArrayRelease'));
end;

procedure TStaticArrayTests.TestNative_FloatArrayFieldElement_LoadsElement;
const
  Src = '''
    program P;
    type TObj = class A: array[0..2] of Float64; end;
    var O: TObj; X: Float64;
    begin
      X := O.A[1];
    end.
    ''';
begin
  AssertEquals('the element is loaded', '',
    AsmMissing(Src,
      #9'addq %rcx, %rax' + #10 + #9'movq %rax, %rcx' + #10 +
        #9'movsd (%rcx), %xmm0',
      #9'add x0, x0, x1' + #10 + #9'ldr x0, [x0]' + #10 + #9'fmov d0, x0'));
end;

procedure TStaticArrayTests.TestParse_CallResultArrayFieldElemWrite;
var
  Prog: TProgram;
  FA: TFieldAssignment;
begin
  Prog := ParseSrc('''
    program P;
    begin
      MakeObj().A[1] := 5;
    end.
    ''');
  try
    AssertTrue('a field assignment', Prog.Block.Stmts[0] is TFieldAssignment);
    FA := TFieldAssignment(Prog.Block.Stmts[0]);
    AssertTrue('through the call', FA.ObjExpr is TFuncCallExpr);
    AssertNotNull('with the index', FA.PropIndexExpr);
  finally
    Prog.Free();
  end;
end;

const
  SrcManagedByVal = '''
    program P;
    type TSA = array[0..1] of String;
    procedure ByVal(A: TSA);
    begin
    end;
    var G: TSA;
    begin
      ByVal(G)
    end.
    ''';
  SrcManagedStores = '''
    program P;
    type
      TSA = array[0..1] of String;
      TRec = record A: TSA; end;
      TObj = class A: TSA; end;
    function MkA: TSA; begin Result[0] := 'x' end;
    var L: TSA; R: TRec; O: TObj; AA: array[0..1] of TSA;
    begin
      O := TObj.Create();
      R.A := L;
      O.A := L;
      AA[1] := L;
      L := MkA()
    end.
    ''';
  SrcIntfArrayParam = '''
    program P;
    type
      IFoo = interface function Get: Int; end;
      TSA = array[0..1] of IFoo;
    function Pick(const A: TSA): Int; begin Result := A[1].Get() end;
    var G: TSA;
    begin
      WriteLn(Pick(G))
    end.
    ''';

procedure TStaticArrayTests.TestCodegen_ManagedArrayByValueParam_RetainedAndReleased;
begin
  AssertEquals('the callee retains its copy and releases it at exit', '',
    AsmMissing(SrcManagedByVal,
      #9'callq _StringAddRef',
      #9'bl __StringAddRef'));
  AssertEquals('and releases it at exit', '',
    AsmMissing(SrcManagedByVal,
      #9'callq _StringRelease',
      #9'bl __StringRelease'));
end;

procedure TStaticArrayTests.TestCodegen_ManagedArrayStores_RetainAndRelease;
begin
  AssertEquals('whole-array stores walk the elements', '',
    AsmMissing(SrcManagedStores,
      #9'callq _StringAddRef'#10#9'leaq 8(%r15), %r14',
      #9'bl __StringAddRef'#10#9'add x20, x21, #8'));
end;

procedure TStaticArrayTests.TestCodegen_IntfArrayParamElement_ReadsThroughParam;
begin
  AssertEquals('the element address is computed from the parameter''s array', '',
    AsmMissing(SrcIntfArrayParam,
      #9'movq -8(%rbp), %rax'#10#9'pushq %rax'#10#9'movl $1, %eax',
      #9'mul x1, x1, x2'#10#9'add x0, x0, x1'#10#9'ldp x0, x1, [x0]'));
end;

procedure TStaticArrayTests.TestCodegen_ClosureElementArg_PassesAddress;
const
  Src = '''
    program Prg;
    type
      TF = reference to function: Int;
      TSA = array[0..1] of TF;
    function Use(E: TF): Int; begin Result := E() end;
    var L: TSA;
    begin
      WriteLn(Use(L[1]))
    end.
    ''';
begin
  AssertEquals('the element address is the argument', '',
    AsmMissing(Src,
      #9'addq %rcx, %rax'#10#9'movq %rax, %rdi'#10#9'callq Use',
      #9'add x0, x0, x1'#10#9'str x0, [sp, #-16]!'#10#9'ldr x0, [sp], #16'#10 +
        #9'bl _Use'));
end;

procedure TStaticArrayTests.TestCodegen_FieldArrayOfRows_ElementStoreCopies;
const
  Src = '''
      program P;
      type
        TRow = array[0..2] of Int;
        TObj = class
          Rows: array[0..1] of TRow;
        end;
      procedure Put(O: TObj; const R: TRow);
      begin
        O.Rows[1] := R
      end;
      begin
      end.
      ''';
begin
  AssertEquals('the row is copied in', '',
    AsmMissing(Src, 'callq memcpy', 'bl _memcpy'));
end;

initialization
  RegisterTest(TStaticArrayTests);

end.
