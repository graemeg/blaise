{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.staticarray;

{ E2E tests for static arrays: compile -> QBE -> cc -> run, assert on stdout.
  Covers inline anonymous array declarations (var A: array[L..H] of T) and
  the named array type alias form (type TArr = array[L..H] of T) introduced
  to fix the missing parser branch. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStaticArrayTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Inline anonymous declaration (regression: ensure existing behaviour holds) }
    procedure TestRun_AnonymousDecl_ReadWrite;
    procedure TestRun_AnonymousDecl_NonZeroBase;
    procedure TestRun_AnonymousDecl_LowHighLength;
    { BUG-050: a non-zero-LowBound static array WRITE must rebase the index on
      EVERY backend (the existing NonZeroBase test runs QBE-only; the native
      write path ignored the low bound). Runs on all backends. }
    procedure TestRun_NonZeroBase_Write_AllBackends;

    { Named type alias: type TArr = array[L..H] of T }
    procedure TestRun_TypeAlias_BasicReadWrite;
    procedure TestRun_TypeAlias_NonZeroBase;
    procedure TestRun_TypeAlias_AsParam_Length;
    procedure TestRun_TypeAlias_MultipleVarsShareType;
    procedure TestRun_TypeAlias_GlobalAndLocal;
    { A named integer subrange (TIdx = 0..2) used as an array index type:
      array[TIdx] of T resolves to array[0..2] of T (ordinal-indexed). }
    procedure TestRun_NamedSubrange_AsArrayIndex;
    procedure TestRun_NamedSubrange_NonZeroBase_AsArrayIndex;

    { Range-indexed const array: const X: array[L..H] of T = (...) }
    procedure TestRun_ConstArray_RangeIndexed_Strings;
    procedure TestRun_ConstArray_RangeIndexed_Integers;

    { Class-level array constants }
    procedure TestRun_ClassConstArray_RangeIndexed;
    procedure TestRun_ClassConstArray_EnumIndexed;
    { GH #182 follow-up: a class array const indexed by an enum-SUBRANGE type
      expects the subrange's member count and indexes with the subrange's
      ordinal bounds (twin of the unit-level TestRun_Subrange_OfEnum_ConstArray). }
    procedure TestRun_ClassConstArray_EnumSubrangeIndexed;

    { Dynamic array High/Low }
    procedure TestRun_DynArray_High_ReturnsLengthMinusOne;
    procedure TestRun_DynArray_Low_ReturnsZero;

    { Dynamic array for..in }
    procedure TestRun_DynArray_ForIn_IteratesAllElements;
    procedure TestRun_DynArray_ForIn_EmptyArray_NoIterations;

    { Multi-dimensional arrays — run on both backends (QBE + native) }
    procedure TestRun_MultiDim_CommaForm_ReadWrite;
    procedure TestRun_MultiDim_ChainedForm_ReadWrite;
    procedure TestRun_MultiDim_NonZeroBounds;
    procedure TestRun_MultiDim_ThreeDimensions;
    procedure TestRun_MultiDim_StringElements_ARC;
    procedure TestRun_MultiDim_MixedNotation;

    { self-cross-compile leg 16: read AND write of an element of an
      implicit-Self STATIC-array field (array[0..N] of string) — the
      FPromoVars pattern in the compiler's own native backend.  Runs on both
      backends AND asserts leak-freedom (the element store retains new /
      releases old, so a mis-emitted base would over-/under-release). }
    procedure TestRun_StaticArrayField_ImplicitSelf_ElementReadWrite;

    { Floating-point array elements — run on both backends (QBE + native).
      Regression: the dyn-array element store used storel/movq for any
      non-integer element, corrupting Double/Single stores. }
    procedure TestRun_DynArray_DoubleElement_ReadWrite;
    procedure TestRun_DynArray_SingleElement_ReadWrite;
    procedure TestRun_StaticArray_DoubleElement_ReadWrite;

    { Multi-dimensional const arrays — run on both backends (QBE + native).
      Comma and nested declaration forms; row-major value layout. }
    procedure TestRun_MultiDimConst_CommaForm_ReadsValues;
    procedure TestRun_MultiDimConst_NestedForm_ReadsValues;
    procedure TestRun_MultiDimConst_ThreeDimensions;

    { Named constant array bounds (issue #109) }
    procedure TestRun_NamedConstBound_Simple;
    procedure TestRun_NamedConstBound_Expression;
    procedure TestRun_NamedConstBound_TypeAlias;

    { Enum-indexed var/type static arrays (issue #114) }
    procedure TestRun_EnumIndex_VarDecl;
    procedure TestRun_EnumIndex_TypeDecl;
    { GH #181 — Boolean is a valid 2-element ordinal index type. }
    procedure TestRun_BooleanIndex_TypeDecl;
    procedure TestRun_BooleanIndex_VarDecl;
    { Reading a RECORD element out of a static/dynamic array — the element is a
      value used by reference (whole-record copy, field read).  arm64 leg 32
      hardened its element-read path; this guards the behaviour on QBE + native. }
    procedure TestRun_RecordElement_ReadAndCopy;
    { Reading an element of a 2-D (or deeper) array FIELD — H.FGrid[1][1] where
      FGrid: array[..] of array[..] of T.  The inner element type of the first
      subscript is tyStaticArray; the field-array element-read arms did not
      return its ADDRESS, so 8 bytes of the inner array were loaded as a
      pointer and the outer subscript dereferenced garbage — SIGSEGV on both
      backends (BUG-20260723-2d-field-array-elem-read). }
    procedure TestRun_MultiDimFieldArray_ElementRead;
  end;

implementation

const
  SrcAnonReadWrite =
    '''
    program P;
    var A: array[0..2] of Integer;
    begin
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      WriteLn(A[0]);
      WriteLn(A[1]);
      WriteLn(A[2])
    end.
    ''';

  SrcAnonNonZero =
    '''
    program P;
    var A: array[5..7] of Integer;
    begin
      A[5] := 100;
      A[6] := 200;
      A[7] := 300;
      WriteLn(A[5]);
      WriteLn(A[7])
    end.
    ''';

  SrcAnonLowHighLen =
    '''
    program P;
    var A: array[0..4] of Integer;
    begin
      WriteLn(Low(A));
      WriteLn(High(A));
      WriteLn(Length(A))
    end.
    ''';

  SrcAliasBasic =
    '''
    program P;
    type
      TTriple = array[0..2] of Integer;
    var A: TTriple;
    begin
      A[0] := 1;
      A[1] := 2;
      A[2] := 3;
      WriteLn(A[0]);
      WriteLn(A[1]);
      WriteLn(A[2])
    end.
    ''';

  SrcAliasNonZero =
    '''
    program P;
    type
      TSlice = array[3..5] of Integer;
    var S: TSlice;
    begin
      S[3] := 33;
      S[4] := 44;
      S[5] := 55;
      WriteLn(S[3]);
      WriteLn(S[5])
    end.
    ''';

  SrcAliasAsParam =
    '''
    program P;
    type
      TFive = array[0..4] of Integer;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: TFive;
    begin
      PrintLen(B)
    end.
    ''';

  SrcAliasMultiVar =
    '''
    program P;
    type
      TPair = array[0..1] of Integer;
    var X, Y: TPair;
    begin
      X[0] := 10; X[1] := 20;
      Y[0] := 30; Y[1] := 40;
      WriteLn(X[0]);
      WriteLn(Y[1])
    end.
    ''';

  SrcAliasGlobalLocal =
    '''
    program P;
    type
      TBuf = array[0..2] of Integer;
    var G: TBuf;
    procedure Fill;
    var L: TBuf;
    begin
      L[0] := 7; L[1] := 8; L[2] := 9;
      G[0] := L[0];
      G[2] := L[2]
    end;
    begin
      Fill();
      WriteLn(G[0]);
      WriteLn(G[2])
    end.
    ''';

  { A named integer subrange used as an array index type.  array[TIdx] of T,
    where TIdx = 0..2, must resolve to array[0..2] of T (ordinal-indexed,
    like array[TEnum]).  FPC compiles this; Blaise must too. }
  SrcSubrangeIndex =
    '''
    program P;
    type
      TIdx = 0..2;
      TBuf = array[TIdx] of Integer;
    var A: TBuf;
    begin
      A[0] := 11; A[1] := 22; A[2] := 33;
      WriteLn(A[0]);
      WriteLn(A[1]);
      WriteLn(A[2]);
      WriteLn(Length(A))
    end.
    ''';

  { Non-zero-based named subrange index: array[2..4] via a named subrange. }
  SrcSubrangeIndexNonZero =
    '''
    program P;
    type
      TIdx = 2..4;
      TBuf = array[TIdx] of Integer;
    var A: TBuf;
    begin
      A[2] := 100; A[3] := 200; A[4] := 300;
      WriteLn(A[2]);
      WriteLn(A[4]);
      WriteLn(Low(A));
      WriteLn(High(A))
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EStaticArrayTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-staticarray')
end;

{ ------------------------------------------------------------------ }
{ Tests — anonymous inline declarations                                }
{ ------------------------------------------------------------------ }

procedure TE2EStaticArrayTests.TestRun_AnonymousDecl_ReadWrite;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAnonReadWrite, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[0]=10', '10', Lines.Strings[0]);
    AssertEquals('A[1]=20', '20', Lines.Strings[1]);
    AssertEquals('A[2]=30', '30', Lines.Strings[2]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_AnonymousDecl_NonZeroBase;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAnonNonZero, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[5]=100', '100', Lines.Strings[0]);
    AssertEquals('A[7]=300', '300', Lines.Strings[1]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_AnonymousDecl_LowHighLength;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAnonLowHighLen, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Low=0',    '0', Lines.Strings[0]);
    AssertEquals('High=4',   '4', Lines.Strings[1]);
    AssertEquals('Length=5', '5', Lines.Strings[2]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_NonZeroBase_Write_AllBackends;
const
  Src = '''
    program P;
    var
      A: array[5..9] of Integer;
      I: Integer;
    begin
      for I := 5 to 9 do
        A[I] := I * 10;
      WriteLn(A[5], ' ', A[9])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  { A[5]=50, A[9]=90 — the write must rebase index 5→0 on every backend }
  AssertRunsOnAll(Src, '50 90' + Chr(10), 0);
end;

{ ------------------------------------------------------------------ }
{ Tests — named type alias                                             }
{ ------------------------------------------------------------------ }

procedure TE2EStaticArrayTests.TestRun_TypeAlias_BasicReadWrite;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasBasic, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[0]=1', '1', Lines.Strings[0]);
    AssertEquals('A[1]=2', '2', Lines.Strings[1]);
    AssertEquals('A[2]=3', '3', Lines.Strings[2]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_NonZeroBase;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasNonZero, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('S[3]=33', '33', Lines.Strings[0]);
    AssertEquals('S[5]=55', '55', Lines.Strings[1]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_AsParam_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasAsParam, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Length(TFive)=5', '5', Trim(Output));
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_MultipleVarsShareType;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasMultiVar, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('X[0]=10', '10', Lines.Strings[0]);
    AssertEquals('Y[1]=40', '40', Lines.Strings[1]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_GlobalAndLocal;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasGlobalLocal, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('G[0]=7', '7', Lines.Strings[0]);
    AssertEquals('G[2]=9', '9', Lines.Strings[1]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_NamedSubrange_AsArrayIndex;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcSubrangeIndex, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[0]=11', '11', Lines.Strings[0]);
    AssertEquals('A[1]=22', '22', Lines.Strings[1]);
    AssertEquals('A[2]=33', '33', Lines.Strings[2]);
    AssertEquals('Length(A)=3', '3', Lines.Strings[3]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_NamedSubrange_NonZeroBase_AsArrayIndex;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcSubrangeIndexNonZero, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[2]=100', '100', Lines.Strings[0]);
    AssertEquals('A[4]=300', '300', Lines.Strings[1]);
    AssertEquals('Low(A)=2',  '2', Lines.Strings[2]);
    AssertEquals('High(A)=4', '4', Lines.Strings[3]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_ConstArray_RangeIndexed_Strings;
const
  Src =
    '''
    program P;
    const Days: array[0..6] of string = ('Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat');
    var I: Integer;
    begin
      WriteLn(Days[0]);
      WriteLn(Days[3]);
      WriteLn(Days[6]);
      I := 5;
      WriteLn(Days[I])
    end.
    ''';
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Days[0]', 'Sun', Lines.Strings[0]);
    AssertEquals('Days[3]', 'Wed', Lines.Strings[1]);
    AssertEquals('Days[6]', 'Sat', Lines.Strings[2]);
    AssertEquals('Days[5]', 'Fri', Lines.Strings[3]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_ConstArray_RangeIndexed_Integers;
const
  Src =
    '''
    program P;
    const Primes: array[0..4] of Integer = (2, 3, 5, 7, 11);
    begin
      WriteLn(Primes[0]);
      WriteLn(Primes[2]);
      WriteLn(Primes[4])
    end.
    ''';
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Primes[0]', '2', Lines.Strings[0]);
    AssertEquals('Primes[2]', '5', Lines.Strings[1]);
    AssertEquals('Primes[4]', '11', Lines.Strings[2]);
  finally Lines.Free() end
end;

procedure TE2EStaticArrayTests.TestRun_ClassConstArray_RangeIndexed;
const
  Src =
    '''
    program P;
    type
      TMyDays = class
      public
        const Days: array[0..6] of string =
          ('Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat');
      end;
    var T: TMyDays; I: Integer;
    begin
      T := TMyDays.Create();
      WriteLn(T.Days[0]);
      WriteLn(T.Days[1]);
      I := 5;
      WriteLn(T.Days[I]);
      T.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src,
    'Sun' + Chr(10) + 'Mon' + Chr(10) + 'Fri' + Chr(10), 0);
end;

procedure TE2EStaticArrayTests.TestRun_ClassConstArray_EnumIndexed;
const
  Src =
    '''
    program P;
    type
      TColor = (Red, Green, Blue);
      TPalette = class
      public
        const Names: array[TColor] of string = ('Red', 'Green', 'Blue');
      end;
    var P2: TPalette;
    begin
      P2 := TPalette.Create();
      WriteLn(P2.Names[0]);
      WriteLn(P2.Names[2]);
      P2.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src, 'Red' + Chr(10) + 'Blue' + Chr(10), 0);
end;

procedure TE2EStaticArrayTests.TestRun_ClassConstArray_EnumSubrangeIndexed;
const
  { Distinct values pin the ordinal-bounds indexing (East = ordinal 1 maps to
    the first element).  Reads via an enum-literal index and via a variable
    index cover both the folded and runtime rebase paths. }
  Src =
    '''
    program P;
    type
      TDirection = (North, East, South, West);
      TTurn = East..South;
      THolder = class
      public
        const Names: array[TTurn] of string = ('east', 'south');
      end;
    var
      H: THolder;
      T: TTurn;
    begin
      H := THolder.Create();
      WriteLn(H.Names[East]);
      T := South;
      WriteLn(H.Names[T]);
      H.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src, 'east' + Chr(10) + 'south' + Chr(10), 0);
end;

procedure TE2EStaticArrayTests.TestRun_DynArray_High_ReturnsLengthMinusOne;
const Src =
  '''
  program P;
  type Tar = array of Integer;
  var ar: Tar;
  begin
    SetLength(ar, 15);
    WriteLn(High(ar));
  end.
  ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('High of 15-element array is 14', '14', Trim(Output));
end;

procedure TE2EStaticArrayTests.TestRun_DynArray_Low_ReturnsZero;
const Src =
  '''
  program P;
  type Tar = array of Integer;
  var ar: Tar;
  begin
    SetLength(ar, 15);
    WriteLn(Low(ar));
  end.
  ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Low of dynamic array is always 0', '0', Trim(Output));
end;

procedure TE2EStaticArrayTests.TestRun_DynArray_ForIn_IteratesAllElements;
const Src =
  '''
  program P;
  var
    da: array of Integer;
    x, i: Integer;
  begin
    SetLength(da, 4);
    da[0] := 10;
    da[1] := 20;
    da[2] := 30;
    da[3] := 40;
    for x in da do
      WriteLn(x)
  end.
  ''';
var LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '10' + LE + '20' + LE + '30' + LE + '40' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_DynArray_ForIn_EmptyArray_NoIterations;
const Src =
  '''
  program P;
  var
    da: array of Integer;
    x: Integer;
    count: Integer;
  begin
    count := 0;
    for x in da do
      Inc(count);
    WriteLn(count)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '0' + LineEnding, 0);
end;

{ ------------------------------------------------------------------ }
{ Multi-dimensional arrays — exercised on every backend                }
{ ------------------------------------------------------------------ }

procedure TE2EStaticArrayTests.TestRun_MultiDim_CommaForm_ReadWrite;
const Src =
  '''
  program P;
  var A: array[0..1, 0..2] of Integer;
      i, j: Integer;
  begin
    for i := 0 to 1 do
      for j := 0 to 2 do
        A[i, j] := (i * 10) + j;
    for i := 0 to 1 do
      for j := 0 to 2 do
        WriteLn(A[i, j])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src,
    '0' + LE + '1' + LE + '2' + LE + '10' + LE + '11' + LE + '12' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDim_ChainedForm_ReadWrite;
const Src =
  '''
  program P;
  var A: array[0..1] of array[0..2] of Integer;
  begin
    A[0][0] := 5;
    A[1][2] := 42;
    WriteLn(A[0][0]);
    WriteLn(A[1][2])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '5' + LE + '42' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDim_NonZeroBounds;
const Src =
  '''
  program P;
  var A: array[1..2, 5..7] of Integer;
      i, j: Integer;
  begin
    for i := 1 to 2 do
      for j := 5 to 7 do
        A[i, j] := (i * 100) + j;
    WriteLn(A[1, 5]);
    WriteLn(A[2, 7])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '105' + LE + '207' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDim_ThreeDimensions;
const Src =
  '''
  program P;
  var A: array[0..1, 0..1, 0..1] of Integer;
  begin
    A[0, 0, 0] := 1;
    A[1, 1, 1] := 8;
    A[0, 1, 0] := 3;
    WriteLn(A[0, 0, 0]);
    WriteLn(A[1, 1, 1]);
    WriteLn(A[0, 1, 0])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '8' + LE + '3' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDim_StringElements_ARC;
const Src =
  '''
  program P;
  var S: array[0..1, 0..1] of string;
  begin
    S[0, 0] := 'hello';
    S[1, 1] := 'world';
    WriteLn(S[0, 0]);
    WriteLn(S[1, 1])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, 'hello' + LE + 'world' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDim_MixedNotation;
const Src =
  '''
  program P;
  var A: array[0..1, 0..2] of Integer;
  begin
    A[1, 2] := 77;       { comma write }
    WriteLn(A[1][2]);    { chained read }
    A[0][1] := 33;       { chained write }
    WriteLn(A[0, 1])     { comma read }
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '77' + LE + '33' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_DynArray_DoubleElement_ReadWrite;
const Src =
  '''
  program P;
  type TArr = array of Double;
  var A: TArr;
  begin
    SetLength(A, 3);
    A[0] := 12.5;
    A[1] := -3.25;
    A[2] := 100.0;
    WriteLn(A[0]);
    WriteLn(A[1]);
    WriteLn(A[2])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '12.5' + LE + '-3.25' + LE + '100' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_DynArray_SingleElement_ReadWrite;
const Src =
  '''
  program P;
  type TArr = array of Single;
  var A: TArr;
  begin
    SetLength(A, 2);
    A[0] := 1.5;
    A[1] := 2.25;
    WriteLn(A[0]);
    WriteLn(A[1])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1.5' + LE + '2.25' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_StaticArray_DoubleElement_ReadWrite;
const Src =
  '''
  program P;
  var A: array[0..2] of Double;
  begin
    A[0] := 12.5;
    A[1] := -3.25;
    A[2] := 100.0;
    WriteLn(A[0]);
    WriteLn(A[1]);
    WriteLn(A[2])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '12.5' + LE + '-3.25' + LE + '100' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDimConst_CommaForm_ReadsValues;
const Src =
  '''
  program P;
  const M: array[0..1, 0..2] of Integer = ((1, 2, 3), (4, 5, 6));
  begin
    WriteLn(M[0, 0]);
    WriteLn(M[0, 2]);
    WriteLn(M[1, 0]);
    WriteLn(M[1, 2])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '3' + LE + '4' + LE + '6' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDimConst_NestedForm_ReadsValues;
const Src =
  '''
  program P;
  const M: array[0..1] of array[0..1] of Integer = ((10, 20), (30, 40));
  begin
    WriteLn(M[0][0]);
    WriteLn(M[0][1]);
    WriteLn(M[1][0]);
    WriteLn(M[1][1])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '10' + LE + '20' + LE + '30' + LE + '40' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDimConst_ThreeDimensions;
const Src =
  '''
  program P;
  const M: array[0..1, 0..1, 0..1] of Integer =
    (((1, 2), (3, 4)), ((5, 6), (7, 8)));
  begin
    WriteLn(M[0, 0, 0]);
    WriteLn(M[1, 0, 1]);
    WriteLn(M[1, 1, 1])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '6' + LE + '8' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_NamedConstBound_Simple;
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll('''
    program P;
    const N = 3;
    var A: array[0..N] of Integer;
    begin
      A[0] := 10; A[1] := 20; A[2] := 30; A[3] := 40;
      WriteLn(A[0]); WriteLn(A[3])
    end.
    ''', '10' + LE + '40' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_NamedConstBound_Expression;
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll('''
    program P;
    const N = 10;
    var A: array[0..N-1] of Integer;
    begin
      A[0] := 1; A[9] := 99;
      WriteLn(A[0]); WriteLn(A[9])
    end.
    ''', '1' + LE + '99' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_NamedConstBound_TypeAlias;
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll('''
    program P;
    const MaxItems = 5;
    type TBuf = array[0..MaxItems-1] of Integer;
    var B: TBuf;
    begin
      B[0] := 100; B[4] := 500;
      WriteLn(B[0]); WriteLn(B[4])
    end.
    ''', '100' + LE + '500' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_EnumIndex_VarDecl;
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll('''
    program P;
    type TColor = (Red, Green, Blue);
    var A: array[TColor] of string;
    begin
      A[Red] := 'R'; A[Green] := 'G'; A[Blue] := 'B';
      WriteLn(A[Red]); WriteLn(A[Blue])
    end.
    ''', 'R' + LE + 'B' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_EnumIndex_TypeDecl;
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll('''
    program P;
    type TDir = (North, South, East, West);
    type TDirCost = array[TDir] of Integer;
    var C: TDirCost;
    begin
      C[North] := 1; C[South] := 2; C[East] := 3; C[West] := 4;
      WriteLn(C[North]); WriteLn(C[West])
    end.
    ''', '1' + LE + '4' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_BooleanIndex_TypeDecl;
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll('''
    program P;
    type TFlags = array[Boolean] of string;
    var A: TFlags;
    begin
      A[False] := 'no'; A[True] := 'yes';
      WriteLn(A[False]); WriteLn(A[True])
    end.
    ''', 'no' + LE + 'yes' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_BooleanIndex_VarDecl;
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  { Anonymous decl + subscript by a Boolean expression, not just literals. }
  AssertRunsOnAll('''
    program P;
    var A: array[Boolean] of Integer;
    var I: Integer;
    begin
      A[False] := 10; A[True] := 20;
      for I := 0 to 3 do
        WriteLn(A[I > 1]);
    end.
    ''', '10' + LE + '10' + LE + '20' + LE + '20' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_StaticArrayField_ImplicitSelf_ElementReadWrite;
begin
  { A class with a static-array string field, written and read through methods
    (so FTab is an implicit-Self field).  This is the FPromoVars shape from the
    compiler's own native backend that leg 16 unblocks.  Leak-free on both. }
  AssertLeakFreeOnAll('''
    program P;
    type
      TThing = class
        FTab: array[0..3] of string;
        procedure Fill;
        function Get(I: Integer): string;
      end;
    procedure TThing.Fill;
    begin
      FTab[0] := 'aa';
      FTab[1] := 'bb';
      FTab[3] := 'dd'
    end;
    function TThing.Get(I: Integer): string;
    begin
      Result := FTab[I]
    end;
    var T: TThing;
    begin
      T := TThing.Create();
      T.Fill();
      WriteLn(T.Get(0));
      WriteLn(T.Get(1));
      WriteLn(T.Get(3));
      T.Free()
    end.
    ''', 'aa');
end;

procedure TE2EStaticArrayTests.TestRun_RecordElement_ReadAndCopy;
const
  Src =
    '''
    program P;
    type TR = record A, B: Integer; S: string; end;
    var arr: array[0..3] of TR; d: array of TR; r: TR;
    begin
      arr[1].A := 5; arr[1].B := 7; arr[1].S := 'hi';
      r := arr[1];
      WriteLn(r.A, ' ', arr[1].A, ' ', arr[1].B, ' ', arr[1].S);
      SetLength(d, 2);
      d[0].A := 9; d[0].S := 'yo';
      r := d[0];
      WriteLn(r.A, ' ', d[0].A, ' ', d[0].S)
    end.
    ''';
var
  LE: string;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '5 5 7 hi' + LE + '9 9 yo' + LE, 0);
end;

procedure TE2EStaticArrayTests.TestRun_MultiDimFieldArray_ElementRead;
const Src =
  '''
  program P;
  type
    TBig = set of Byte;
    THold = class
    public
      FGrid: array[0..1] of array[0..1] of Integer;
      FDeep: array[0..1] of array[0..1] of array[0..1] of Integer;
      FSets: array[0..1] of array[0..1] of TBig;
    end;
    TOuter = class
    public
      FH: THold;
    end;
  procedure Bump(var I: Integer); begin I := I + 100 end;
  var H: THold; O: TOuter;
  begin
    H := THold.Create();
    H.FGrid[0][0] := 1; H.FGrid[0][1] := 2;
    H.FGrid[1][0] := 3; H.FGrid[1][1] := 4;
    WriteLn(H.FGrid[0][0], ' ', H.FGrid[1][1]);        { 1 4 }
    Bump(H.FGrid[1][1]);                               { 2-D elem by var }
    WriteLn(H.FGrid[1][0], ' ', H.FGrid[1][1]);        { 3 104 }
    H.FDeep[1][0][1] := 42;
    WriteLn(H.FDeep[1][0][1]);                         { 42 (3-D) }
    H.FSets[0][0] := [5]; H.FSets[1][1] := [200];      { 2-D jumbo }
    if 200 in H.FSets[1][1] then WriteLn('j') else WriteLn('.');
    if 200 in H.FSets[0][0] then WriteLn('.') else WriteLn('k');
    { Chained-base arm (O.FH.FGrid — FldAccess.Base <> nil) is a separate
      code path in the QBE backend and has drifted from the leaf arm before
      (BUG-20260723-qbe-intf-nested-chain-array-elem). }
    O := TOuter.Create();
    O.FH := H;
    WriteLn(O.FH.FGrid[1][0], ' ', O.FH.FGrid[1][1])   { 3 104 (chained) }
  end.
  ''';
var LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '1 4' + LE + '3 104' + LE + '42' + LE +
    'j' + LE + 'k' + LE + '3 104' + LE, 0);
end;

initialization
  RegisterTest(TE2EStaticArrayTests);

end.
