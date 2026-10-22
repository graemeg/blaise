{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.openarray;

{ E2E tests for open-array parameters: compile -> QBE -> cc -> run, assert on
  stdout.  Covers inline array literals (sum, High/Low, Length) and the
  static-array-to-open-array coercion introduced to fix the "No matching
  overload" error when a named static-array variable is passed as an open-array
  argument. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EOpenArrayTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { an open-array LITERAL of records, interfaces, closures, method
      pointers and static arrays -- of variables and of call results -- is
      built as a temporary dynamic array: the in-frame element block stored
      one machine word per element, garbling all of them on both ISAs and
      never releasing an owned element.  Through a function, a method, a
      procedural variable and an interface dispatch }
    procedure TestRun_OpenArrayLiteral_RichElements;
    { an interface method with an open-array parameter, given a dynamic
      array, a dynamic-array call result and a literal (x86-64 passed one
      word and a garbage high, or refused the literal) }
    procedure TestRun_OpenArray_ThroughInterfaceDispatch;
    { an open array of STATIC arrays indexed twice, A[I][J] (x86-64 loaded
      the element and indexed through its first bytes) }
    procedure TestRun_OpenArray_OfStaticArrays;
    { the elements of a literal typed by its open-array formal arrive as the
      formal's element type: objects dispatch virtually, integers become floats }
    procedure TestRun_ArrayLiteralArg_TakesFormalElementType;
    { A static array produced by a GETTER -- O.AG, an indexed O.AI[7], a bare AG
      and Self.AG inside a method -- passed to an open-array parameter, const or
      by value, with managed elements too.  x86-64 sent the getter down the
      l-value address walk, which found no field ("var/out field argument has no
      resolved field info"). }
    procedure TestRun_StaticArrayGetter_AsOpenArrayArg;
    procedure TestRun_OpenArray_StringLiteral_HighAndForwarding;
    { Inline array literal call site }
    procedure TestRun_OpenArray_Sum;
    procedure TestRun_OpenArray_HighLow;
    procedure TestRun_OpenArray_Length;

    { Static array variable coerced to open-array parameter }
    procedure TestRun_StaticToOpen_Length_ZeroBase;
    procedure TestRun_StaticToOpen_Length_NonZeroBase;
    procedure TestRun_StaticToOpen_Sum;
    procedure TestRun_StaticToOpen_PassToNested;
    procedure TestRun_StaticToOpen_ConstParam_NoMutation;

    { Procedural type as open-array element }
    procedure TestRun_OpenArray_ProcType_CallEach;

    { Open-array params on METHODS and CONSTRUCTORS: the call sites must
      pass the (data, high) pair just like standalone functions. }
    procedure TestRun_OpenArray_MethodAndCtorParams;

    { Dynamic array variable coerced to open-array parameter: the call
      sites must pass (data ptr, runtime-length - 1) — high comes from
      _DynArrayLength, not a compile-time static bound. }
    procedure TestRun_DynToOpen_Sum;
    procedure TestRun_DynToOpen_HighLength;
    procedure TestRun_DynToOpen_Empty;
    procedure TestRun_DynToOpen_OfString;
    procedure TestRun_DynToOpen_PassToNested;

    { Empty bracket literal [] as an open-array argument }
    procedure TestRun_EmptyLiteral_ToOpenArray;
    procedure TestRun_EmptyLiteral_OverloadDisambiguation;

    { var open-array parameter (issue #130 bug5): element READ used to segfault
      on QBE (extra deref of the data pointer) and element WRITE was a semantic
      error / native codegen error.  A const open array stays read-only. }
    procedure TestRun_VarOpenArray_ElementRead;
    procedure TestRun_VarOpenArray_ElementWrite;
    procedure TestRun_VarOpenArray_ReadModifyWrite;
    procedure TestRun_MethodCall_SevenSlots_OpenArrayMidList;
    { BUG-20260923-addr-of-openarray-proc: a procedural type with an open-array
      (or array of const) param.  The param resolved as its ELEMENT type, @Proc
      was rejected against it, and no indirect-call path passed an open array
      as its (data, high) pair. }
    procedure TestRun_OpenArrayParam_ProcVarCalls;
    procedure TestRun_OpenArrayParam_FieldClosureMethodPtrCalls;
    { Constant-integer literals passed to Byte / Word / SmallInt / Int64 open
      arrays through plain, method and inherited calls; an exact-element
      overload still wins.  Includes GH #233's program as reported. }
    procedure TestRun_IntLiteral_ToNarrowOpenArray;
    procedure TestRun_GH233_KochTrainingString;
    { BUG-20261010-captured-open-array: nested routines (two levels, and a
      sibling call) reading the parent's open array through High / Length /
      subscript / for-in, writing a var open array, and the empty case. }
    procedure TestRun_NestedRoutine_CapturesOpenArray;
    procedure TestRun_StaticArrayExpr_ToOpenArray;
    procedure TestRun_StaticArrayParamsAndCalls_ToOpenArray;
    procedure TestRun_OpenArrayArgs_SpillToStack;
    { owned transients (string, object) inside an open-array literal are
      released after the call: x86-64 leaked every one, arm64 refused the
      literal }
    procedure TestRun_LiteralOwnedElements_ReleasedAfterCall;
    { every form of float element in an open-array literal: literals,
      operators, unary minus, and each call form -- direct, indirect (an
      element and a call result as the callee), closure, method pointer,
      procedure variable and implicit Self -- in Double and Single blocks.
      Both backends refused the literals, stored garbage for operators and
      calls (inf, -2D, 0), and arm64 refused the call forms }
    procedure TestRun_LiteralFloatElements_EveryForm;
    { a var open array through every call path: routine, procedure
      variable, record method, constructor, method (direct, method pointer,
      past the register slots) and static method.  x86-64 passed only the
      address to a method, and the call segfaulted }
    procedure TestRun_VarOpenArray_EveryCallPath;
  end;

implementation

const
  SrcOpenArraySum =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    begin
      WriteLn(Sum([1, 2, 3, 4, 5]))
    end.
    ''';

  SrcOpenArrayHighLow =
    '''
    program P;
    procedure PrintBounds(const A: array of Integer);
    begin
      WriteLn(Low(A));
      WriteLn(High(A))
    end;
    begin
      PrintBounds([10, 20, 30])
    end.
    ''';

  SrcOpenArrayLength =
    '''
    program P;
    function Count(const A: array of Integer): Integer;
    begin
      Result := Length(A)
    end;
    begin
      WriteLn(Count([10, 20, 30]))
    end.
    ''';

  SrcStaticLenZeroBase =
    '''
    program P;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: array[0..4] of Integer;
    begin
      PrintLen(B)
    end.
    ''';

  SrcStaticLenNonZero =
    '''
    program P;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: array[3..7] of Integer;
    begin
      PrintLen(B)
    end.
    ''';

  SrcStaticSum =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 10;
      B[1] := 20;
      B[2] := 30;
      WriteLn(Sum(B))
    end.
    ''';

  SrcStaticPassNested =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    procedure Process(const A: array of Integer);
    begin
      WriteLn(Sum(A))
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 5;
      B[1] := 10;
      B[2] := 15;
      Process(B)
    end.
    ''';

  SrcStaticConstRead =
    '''
    program P;
    function First(const A: array of Integer): Integer;
    begin
      Result := A[0]
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 77; B[1] := 88; B[2] := 99;
      WriteLn(First(B));
      WriteLn(Length(B))
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EOpenArrayTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-openarray')
end;

{ ------------------------------------------------------------------ }
{ Tests — inline array literals                                        }
{ ------------------------------------------------------------------ }

procedure TE2EOpenArrayTests.TestRun_OpenArray_Sum;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOpenArraySum, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Sum([1..5])=15', '15', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_OpenArray_HighLow;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOpenArrayHighLow, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Low=0',  '0', Lines.Strings[0]);
    AssertEquals('High=2', '2', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EOpenArrayTests.TestRun_OpenArray_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOpenArrayLength, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Length([10,20,30])=3', '3', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Tests — static array coerced to open-array                          }
{ ------------------------------------------------------------------ }

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_Length_ZeroBase;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticLenZeroBase, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Length(B[0..4])=5', '5', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_Length_NonZeroBase;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticLenNonZero, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Length(B[3..7])=5', '5', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_Sum;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticSum, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Sum(B[0..2])=60', '60', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_PassToNested;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticPassNested, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested sum=30', '30', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_ConstParam_NoMutation;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticConstRead, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('First(B)=77',   '77', Lines.Strings[0]);
    AssertEquals('Length(B[0..2])=3', '3', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

{ ------------------------------------------------------------------ }
{ Tests — procedural type as open-array element                      }
{ ------------------------------------------------------------------ }

const
  SrcProcTypeOpenArray =
    '''
    program P;
    type TIntFn = function: Integer;

    function ApplyAll(const Fns: array of TIntFn): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(Fns) do
        Result := Result + Fns[I]();
    end;

    function One: Integer; begin Result := 1; end;
    function Two: Integer; begin Result := 2; end;
    function Three: Integer; begin Result := 3; end;

    var A: array[0..2] of TIntFn;
    begin
      A[0] := @One;
      A[1] := @Two;
      A[2] := @Three;
      WriteLn(ApplyAll(A));
    end.
    ''';

procedure TE2EOpenArrayTests.TestRun_OpenArray_ProcType_CallEach;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeOpenArray, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1+2+3=6', '6', Trim(Output));
end;

const
  SrcOpenArrayMethodCtor = '''
    program P;
    type
      TFoo = class
        FSeed: Integer;
        constructor Create(const Init: array of Integer);
        function Sum(const A: array of Integer): Integer;
        procedure Note(const A: array of Integer);
      end;
    constructor TFoo.Create(const Init: array of Integer);
    var I: Integer;
    begin
      FSeed := 0;
      for I := 0 to High(Init) do
        FSeed := FSeed + Init[I];
    end;
    function TFoo.Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := FSeed;
      for I := 0 to High(A) do
        Result := Result + A[I];
    end;
    procedure TFoo.Note(const A: array of Integer);
    begin
      writeln(High(A) + 1);
    end;
    var
      F: TFoo;
    begin
      F := TFoo.Create([1, 2]);
      writeln(F.FSeed);
      writeln(F.Sum([10, 20, 30]));
      F.Note([5, 6, 7, 8]);
    end.
    ''';

procedure TE2EOpenArrayTests.TestRun_OpenArray_MethodAndCtorParams;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOpenArrayMethodCtor, '3' + #10 + '63' + #10 + '4' + #10, 0);
end;

{ ------------------------------------------------------------------ }
{ Tests — dynamic array coerced to open-array                         }
{ ------------------------------------------------------------------ }

const
  SrcDynSum = '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do Result := Result + A[I];
    end;
    var X: array of Integer; I: Integer;
    begin
      SetLength(X, 5);
      for I := 0 to 4 do X[I] := I + 1;
      WriteLn(Sum(X));
    end.
    ''';

  SrcDynHighLen = '''
    program P;
    procedure Report(const A: array of Integer);
    begin
      WriteLn(Length(A));
      WriteLn(High(A));
    end;
    var X: array of Integer;
    begin
      SetLength(X, 7);
      Report(X);
    end.
    ''';

  SrcDynEmpty = '''
    program P;
    function Count(const A: array of Integer): Integer;
    begin
      Result := Length(A);
    end;
    var X: array of Integer;
    begin
      SetLength(X, 0);
      WriteLn(Count(X));
    end.
    ''';

  SrcDynOfString = '''
    program P;
    function Join(const A: array of string): string;
    var I: Integer;
    begin
      Result := '';
      for I := 0 to High(A) do Result := Result + A[I];
    end;
    var X: array of string;
    begin
      SetLength(X, 3);
      X[0] := 'a'; X[1] := 'b'; X[2] := 'c';
      WriteLn(Join(X));
    end.
    ''';

  SrcDynNested = '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do Result := Result + A[I];
    end;
    procedure Process(const A: array of Integer);
    begin
      WriteLn(Sum(A));
    end;
    var X: array of Integer; I: Integer;
    begin
      SetLength(X, 4);
      for I := 0 to 3 do X[I] := (I + 1) * 10;
      Process(X);
    end.
    ''';

procedure TE2EOpenArrayTests.TestRun_DynToOpen_Sum;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynSum, '15' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_DynToOpen_HighLength;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynHighLen, '7' + #10 + '6' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_DynToOpen_Empty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynEmpty, '0' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_DynToOpen_OfString;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynOfString, 'abc' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_DynToOpen_PassToNested;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynNested, '100' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_EmptyLiteral_ToOpenArray;
{ An empty bracket literal [] passed to a plain open-array parameter — both for a
  string and an integer open array — is a valid zero-length open array.  This
  previously failed overload resolution ("No matching overload"). }
const Src = '''
    program P;
    procedure ShowS(const A: array of string);
    begin WriteLn(Length(A)) end;
    procedure ShowI(const A: array of Integer);
    var i, s: Integer;
    begin
      s := 0;
      for i := 0 to Length(A) - 1 do s := s + A[i];
      WriteLn(Length(A), ' ', s)
    end;
    begin
      ShowS([]);
      ShowS(['a', 'b']);
      ShowI([]);
      ShowI([10, 20, 30])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0' + #10 + '2' + #10 + '0 0' + #10 + '3 60' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_EmptyLiteral_OverloadDisambiguation;
{ [] selects the open-array overload over a non-array one; a non-bracket
  argument still picks the scalar overload. }
const Src = '''
    program P;
    procedure F(X: Integer); overload;
    begin WriteLn('int') end;
    procedure F(const A: array of string); overload;
    begin WriteLn('oa ', Length(A)) end;
    begin
      F([]);
      F(['x']);
      F(5)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'oa 0' + #10 + 'oa 1' + #10 + 'int' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_VarOpenArray_ElementRead;
const
  { Read-only body on a var open array — the exact issue #130 repro. }
  Src = '''
    program P;
    procedure SumVar(var a: array of Integer);
    var i, s: Integer;
    begin s := 0; for i := 0 to High(a) do s := s + a[i]; WriteLn(s) end;
    var x: array[0..2] of Integer;
    begin x[0] := 1; x[1] := 2; x[2] := 3; SumVar(x) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '6' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_VarOpenArray_ElementWrite;
const
  { Element write through a var open array mutates the caller's storage. }
  Src = '''
    program P;
    procedure Zero(var a: array of Integer);
    var i: Integer;
    begin for i := 0 to High(a) do a[i] := 0 end;
    var x: array[0..2] of Integer; i: Integer;
    begin
      x[0] := 1; x[1] := 2; x[2] := 3;
      Zero(x);
      for i := 0 to 2 do WriteLn(x[i])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0' + #10 + '0' + #10 + '0' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_VarOpenArray_ReadModifyWrite;
const
  { Read and write the same element (a[i] := a[i] * by) through a var open
    array, then read it back via a const open array. }
  Src = '''
    program P;
    procedure Scale(var a: array of Integer; by: Integer);
    var i: Integer;
    begin for i := 0 to High(a) do a[i] := a[i] * by end;
    function SumC(const a: array of Integer): Integer;
    var i: Integer;
    begin Result := 0; for i := 0 to High(a) do Result := Result + a[i] end;
    var x: array[0..3] of Integer; i: Integer;
    begin
      for i := 0 to 3 do x[i] := i + 1;
      Scale(x, 10);
      for i := 0 to 3 do WriteLn(x[i]);
      WriteLn('sum=', SumC(x))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '10' + #10 + '20' + #10 + '30' + #10 + '40' + #10 + 'sum=100' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_MethodCall_SevenSlots_OpenArrayMidList;
begin
  { 7 flat arg slots (Self + enum + string + open array ptr/high + two out
    params): the >6-slot store path used one slot per LOGICAL argument, so
    the open array's high collapsed into the next slot -- the callee read a
    garbage high and wrote its out params through wild addresses (segfault).
    Found when the e2e harness itself grew this exact signature. }
  AssertRunsOnAll(
    '''
    program P;
    type
      TBk = (bkOne, bkTwo);
      TC = class
      public
        function RunOnLibs(ABk: TBk; const ASrc: string;
                           const ALibs: array of string;
                           out AOut: string; out ACode: Integer): Boolean;
      end;
    function TC.RunOnLibs(ABk: TBk; const ASrc: string;
                          const ALibs: array of string;
                          out AOut: string; out ACode: Integer): Boolean;
    begin
      WriteLn('high=', IntToStr(High(ALibs)));
      AOut := 'out:' + ASrc;
      ACode := 42;
      Result := True;
    end;
    var
      C: TC;
      A: array[0..1] of string;
      O: string;
      Code: Integer;
    begin
      C := TC.Create();
      A[0] := 'x';
      A[1] := 'y';
      if C.RunOnLibs(bkOne, 'prog', A, O, Code) then
        WriteLn(O, ' code=', IntToStr(Code));
    end.
    ''', 'high=1' + Chr(10) + 'out:prog code=42' + Chr(10), 0);
end;

procedure TE2EOpenArrayTests.TestRun_OpenArrayParam_ProcVarCalls;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll('''
    program P;
    type
      TCnt = function(const A: array of Integer): Integer;
      TSum = function(A: array of Integer): Integer;
      TFmt = procedure(const S: string; const Args: array of const);
      TGCnt<T> = function(const A: array of T): Integer;
    function Cnt(const A: array of Integer): Integer;
    begin
      Result := Length(A)
    end;
    function Sum(A: array of Integer): Integer;
    var
      I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    procedure Fmt(const S: string; const Args: array of const);
    begin
      WriteLn(Format(S, Args))
    end;
    function Apply(F: TCnt; const A: array of Integer): Integer;
    begin
      Result := F(A)                  { proc-type PARAM, open-array passthrough }
    end;
    var
      C: TCnt;
      S: TSum;
      F: TFmt;
      G: TGCnt<Integer>;
      D: array of Integer;
      St: array[0..2] of Integer;
    begin
      C := @Cnt;
      S := @Sum;
      F := @Fmt;
      G := @Cnt;
      WriteLn(C([]));                 { empty literal }
      WriteLn(C([1, 2, 3]));          { literal }
      WriteLn(S([10, 20, 30]));       { by-value open array }
      SetLength(D, 4);
      D[0] := 1; D[1] := 2; D[2] := 3; D[3] := 4;
      WriteLn(S(D));                  { dynamic array }
      St[0] := 5; St[1] := 6; St[2] := 7;
      WriteLn(S(St));                 { static array }
      F('%d-%s', [42, 'x']);          { array of const, statement }
      WriteLn(Apply(C, [9, 9]));
      WriteLn(G([1, 2, 3, 4]))        { generic procedural type }
    end.
    ''',
    '0' + #10 + '3' + #10 + '60' + #10 + '10' + #10 + '18' + #10 +
    '42-x' + #10 + '2' + #10 + '4' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_OpenArrayParam_FieldClosureMethodPtrCalls;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll('''
    program P;
    type
      TCnt = function(const A: array of Integer): Integer;
      TShow = procedure(const A: array of Integer);
      TRefCnt = reference to function(const A: array of Integer): Integer;
      TMSum = function(const A: array of Integer): Integer of object;
      TBox = class
      public
        FC: TCnt;
        FS: TShow;
        FBase: Integer;
        function Total(const A: array of Integer): Integer;
        procedure Drv();
      end;
    function Cnt(const A: array of Integer): Integer;
    begin
      Result := Length(A)
    end;
    procedure ShowLen(const A: array of Integer);
    begin
      WriteLn('len=', Length(A))
    end;
    function TBox.Total(const A: array of Integer): Integer;
    var
      I: Integer;
    begin
      Result := FBase;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    procedure TBox.Drv();
    begin
      WriteLn(FC([7, 8]));            { implicit-Self field, expression }
      FS([6])                         { implicit-Self field, statement }
    end;
    var
      R: TRefCnt;
      M: TMSum;
      B: TBox;
      K: Integer;
    begin
      K := 100;
      R := function(const A: array of Integer): Integer
        begin
          Result := Length(A) + K
        end;
      WriteLn(R([1, 2]));             { reference to }
      B := TBox.Create();
      B.FBase := 1000;
      M := @B.Total;
      WriteLn(M([1, 2]));             { of object }
      B.FC := @Cnt;
      B.FS := @ShowLen;
      WriteLn(B.FC([1]));             { qualified field, expression }
      B.FS([4, 5]);                   { qualified field, statement }
      B.Drv();
      R := nil;
      B.Free()
    end.
    ''',
    '102' + #10 + '1003' + #10 + '1' + #10 + 'len=2' + #10 +
    '2' + #10 + 'len=1' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_OpenArray_StringLiteral_HighAndForwarding;
const
  {
    Replaces the openarray GenIR checks: a string-element literal passes its
    (data, high) pair -- High is 1 for two elements and 0 for one -- every element
    is stored, and a string open array forwarded to another routine keeps both. }
  Src = '''
    program P;
    procedure Inner(const B: array of string);
    var I: Integer;
    begin
      Write(High(B), ':');
      for I := Low(B) to High(B) do
        Write(' ', B[I]);
      WriteLn()
    end;
    procedure Outer(const A: array of string);
    begin
      WriteLn(Length(A), ' ', A[0]);
      Inner(A)
    end;
    begin
      Outer(['hello', 'world']);
      Outer(['only'])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 hello' + #10 +
    '1: hello world' + #10 +
    '1 only' + #10 +
    '0: only' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_IntLiteral_ToNarrowOpenArray;
const Src =
  '''
  program P;
  const K = 300;
  type
    TBase = class
      procedure Put(const A: array of Word); virtual;
    end;
    TKid = class(TBase)
      procedure Put(const A: array of Word); override;
    end;
  procedure TBase.Put(const A: array of Word);
  var I: Integer;
  begin
    for I := 0 to High(A) do Write(A[I], ' ');
    WriteLn()
  end;
  procedure TKid.Put(const A: array of Word);
  begin
    Write('kid ');
    inherited Put([60000, K, 1])
  end;
  procedure Bytes(const A: array of Byte);
  var I: Integer;
  begin
    for I := 0 to High(A) do Write(A[I], ' ');
    WriteLn()
  end;
  procedure Smalls(const A: array of SmallInt);
  var I: Integer;
  begin
    for I := 0 to High(A) do Write(A[I], ' ');
    WriteLn()
  end;
  procedure Bigs(const A: array of Int64);
  var I: Integer;
  begin
    for I := 0 to High(A) do Write(A[I], ' ');
    WriteLn()
  end;
  procedure Pick(const A: array of Byte); overload;
  begin
    WriteLn('byte ', Length(A))
  end;
  procedure Pick(const A: array of Integer); overload;
  begin
    WriteLn('integer ', Length(A))
  end;
  var O: TBase;
  begin
    Bytes([0, 4, 255]);
    Smalls([-5, 32000]);
    Bigs([5000000000, -1]);
    O := TKid.Create();
    O.Put([2, 3]);
    O.Free();
    Pick([1, 2])
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0 4 255 ' + #10 +
    '-5 32000 ' + #10 +
    '5000000000 -1 ' + #10 +
    'kid 60000 300 1 ' + #10 +
    'integer 2' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_GH233_KochTrainingString;
const Src =
  '''
  program it;
  type
    TkochGroup = array [0..42] of String;
  const
    cKochGroup: TkochGroup = ('K', 'M', 'R', 'S', 'U', 'A', 'P', 'T', 'L', 'O',
      'W', 'I', '.', 'N', 'J', 'E', 'F', '0', 'Y', ',',
      'V', 'G', '5', '/', 'Q', '9', 'Z', 'H', '3', '8',
      'B', '?', '4', '2', '7', 'C', '1', 'D', '6', 'X',
      '<BK>', '<SK>', '<AR>');
  var
    b, x: Byte;
    ba: array [0..15] of Byte;
  function trainingString(ACharNum: array of Byte): String;
  var
    b: Byte;
  begin
    for b in ACharNum do
      result := result + cKochGroup[b] + ' ';
  end;
  begin
    for x := 0 to 15 do
      ba[x] := x * 2;
    for b in ba do
      Write(b, ' ');
    WriteLn();
    WriteLn(trainingString(ba));
    WriteLn(trainingString([0, 40, 42]))
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0 2 4 6 8 10 12 14 16 18 20 22 24 26 28 30 ' + #10 +
    'K R U P L W . J F Y V 5 Q Z 3 B ' + #10 +
    'K <BK> <AR> ' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_NestedRoutine_CapturesOpenArray;
const Src =
  '''
  program P;
  procedure Run(const A: array of Integer; var V: array of Byte);
    procedure ShowLen;
    begin
      WriteLn('len ', Length(A), ' high ', High(A))
    end;
    procedure Inner;
    var
      I, X: Integer;
      procedure Deeper;
      var Y: Integer;
      begin
        for Y in A do Write('d', Y, ' ');
        WriteLn();
        V[0] := V[0] + 10
      end;
    begin
      for I := 0 to High(A) do Write(A[I], ' ');
      WriteLn();
      for X in A do Write('[', X, ']');
      WriteLn();
      ShowLen();
      Deeper()
    end;
  begin
    Inner()
  end;
  procedure Join(const S: array of string);
    function Glue: string;
    var T: string;
    begin
      Result := '';
      for T in S do Result := Result + T + '/'
    end;
  begin
    WriteLn(Glue())
  end;
  var B: array[0..1] of Byte;
  begin
    B[0] := 1; B[1] := 2;
    Run([1, 2, 3], B);
    WriteLn(B[0], ' ', B[1]);
    Run([], B);
    WriteLn(B[0]);
    Join(['a', 'b' + IntToStr(7)])
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1 2 3 ' + #10 +
    '[1][2][3]' + #10 +
    'len 3 high 2' + #10 +
    'd1 d2 d3 ' + #10 +
    '11 2' + #10 +
    #10 + #10 +
    'len 0 high -1' + #10 +
    #10 +
    '21' + #10 +
    'a/b7/' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_StaticArrayExpr_ToOpenArray;
const
  Src = '''
    program P;
    type
      TArr = array[0..2] of Integer;
      TC = class
        A: TArr;
        function GetA: TArr;
      end;
      TR = record A: TArr; end;
      PRec = ^TR;
    function TC.GetA: TArr; begin Result := A end;
    procedure Show(const V: array of Integer);
    var I: Integer;
    begin
      for I := 0 to High(V) do Write(V[I], ' ');
      WriteLn(High(V))
    end;
    var
      C: TC; R: TR; PQ: PRec; RS: array of TR;
      M: array[0..1] of TArr;
    begin
      C := TC.Create();
      C.A[1] := 5; R.A[2] := 9; PQ := @R;
      SetLength(RS, 2); RS[1].A[0] := 4;
      M[1][2] := 7;
      Show(C.A);
      Show(R.A);
      Show(PQ^.A);
      Show(RS[1].A);
      Show(M[1]);
      Show(C.GetA())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0 5 0 2' + #10 +
    '0 0 9 2' + #10 +
    '0 0 9 2' + #10 +
    '4 0 0 2' + #10 +
    '0 0 7 2' + #10 +
    '0 5 0 2' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_StaticArrayParamsAndCalls_ToOpenArray;
const
  Src = '''
    program se;
    type TArr = array[0..2] of Integer;
    procedure Show(const V: array of Integer);
    var I: Integer;
    begin for I := 0 to High(V) do Write(V[I], ' '); WriteLn(High(V)) end;
    function MakeA(K: Integer): TArr; begin Result[0] := K; Result[1] := 0; Result[2] := K * 2 end;
    procedure ByVar(var X: TArr); begin Show(X) end;
    procedure ByVal(X: TArr); begin Show(X) end;
    procedure ByConst(const X: TArr); begin Show(X) end;
    procedure Outer2(var P: TArr; Q: TArr);
      procedure Inner2; begin Show(P); Show(Q) end;
    begin Inner2() end;
    procedure Outer;
    var L: TArr;
      procedure Inner; begin Show(L) end;
    begin L[0] := 8; Inner() end;
    function Sum(K: Integer): Integer;
    begin Result := MakeA(K)[0] + MakeA(K)[2] end;
    var G: TArr; K: Integer;
    begin
      WriteLn(MakeA(3)[2]);
      G[1] := 6;
      ByVar(G); ByVal(G); ByConst(G);
      Outer(); Outer2(G, MakeA(7));
      for K := 1 to 2 do Show(MakeA(K));
      WriteLn(Sum(5));
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '6' + #10 +
    '0 6 0 2' + #10 + '0 6 0 2' + #10 + '0 6 0 2' + #10 +
    '8 0 0 2' + #10 +
    '0 6 0 2' + #10 + '7 0 14 2' + #10 +
    '1 0 2 2' + #10 + '2 0 4 2' + #10 +
    '15' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_OpenArrayArgs_SpillToStack;
const
  Src = '''
    program s1;
    uses SysUtils;
    function SumOA(const V: array of Integer): Integer;
    var I: Integer;
    begin Result := 0; for I := 0 to High(V) do Result := Result + V[I] end;
    function F7(A, B, C, D, E, G, H: Integer; const V: array of Integer): Integer;
    begin Result := A + B + C + D + E + G + H + SumOA(V) * 100 + High(V) * 10000 end;
    function F8(A, B, C, D, E, G, H, K: Integer; const V: array of Integer; L: Integer): Integer;
    begin Result := A + H + K + L * 1000 + SumOA(V) * 100 + High(V) * 100000 end;
    function Two(const P: array of Integer; A, B, C, D, E: Integer; const Q: array of string): string;
    var I: Integer;
    begin Result := IntToStr(SumOA(P) + A + E) + ':'; for I := 0 to High(Q) do Result := Result + Q[I] end;
    procedure ManyVar(A, B, C, D, E, G: Integer; var X: Integer; const V: array of Integer);
    begin X := SumOA(V) + G end;
    var Arr: array[0..3] of Integer; D: array of Integer; X: Integer;
    begin
      Arr[0] := 1; Arr[1] := 2; Arr[2] := 3; Arr[3] := 4;
      SetLength(D, 2); D[0] := 5; D[1] := 6;
      WriteLn(F7(1, 2, 3, 4, 5, 6, 7, Arr));
      WriteLn(F7(1, 2, 3, 4, 5, 6, 7, [9, 9]));
      WriteLn(F8(1, 2, 3, 4, 5, 6, 7, 8, D, 3));
      WriteLn(F8(1, 2, 3, 4, 5, 6, 7, 8, [1, 2, 3], 4));
      WriteLn(Two([1, 1], 1, 2, 3, 4, 5, ['a', 'b' + IntToStr(X)]));
      ManyVar(1, 2, 3, 4, 5, 6, X, Arr); WriteLn(X);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '31028' + #10 + '11828' + #10 + '104116' + #10 + '204616' + #10 +
    '8:ab0' + #10 + '16' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_LiteralOwnedElements_ReleasedAfterCall;
const
  Src = '''
    program OALits;
    uses SysUtils;
    type TTag = class N: Integer; end;
    function MkS(N: Integer): string; begin Result := 'f' + IntToStr(N) end;
    function MkT(N: Integer): TTag; begin Result := TTag.Create(); Result.N := N end;
    procedure Show(const AExe: string; const A: array of string; ATail: Integer);
    var I: Integer; Line: string;
    begin
      Line := AExe;
      for I := 0 to High(A) do Line := Line + ' ' + A[I];
      WriteLn(Line, ' ', ATail)
    end;
    function SumTags(const A: array of TTag): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do Result := Result + A[I].N
    end;
    var I: Integer;
    begin
      for I := 1 to 2 do
        Show('gcc', ['-o', MkS(I), MkS(I * 10)], 7);
      WriteLn('tags ', SumTags([MkT(1), MkT(2)]))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertLeakFreeOnAll(Src, 'gcc -o f2 f20 7');
end;

procedure TE2EOpenArrayTests.TestRun_VarOpenArray_EveryCallPath;
const
  Src = '''
    program P;
    type
      TTot = function(var A: array of Integer): Integer;
      TTotM = function(var A: array of Integer): Integer of object;
      TRec = record
        K: Integer;
        function Tot(var A: array of Integer): Integer;
      end;
      TC = class
        S: Integer;
        constructor Create(var A: array of Integer);
        function Tot(var A: array of Integer): Integer;
        function Many(P1, P2, P3, P4: Integer; var A: array of Integer;
          P5: Integer): Integer;
        static function STot(var A: array of Integer): Integer;
      end;
    function Sum(var A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do Result := Result + A[I]
    end;
    function TRec.Tot(var A: array of Integer): Integer; begin Result := Sum(A) + K end;
    constructor TC.Create(var A: array of Integer); begin S := Sum(A); A[0] := 100 end;
    function TC.Tot(var A: array of Integer): Integer; begin Result := Sum(A) end;
    function TC.Many(P1, P2, P3, P4: Integer; var A: array of Integer;
      P5: Integer): Integer;
    begin
      Result := P1 + P2 + P3 + P4 + P5 + Sum(A)
    end;
    static function TC.STot(var A: array of Integer): Integer; begin Result := Sum(A) * 2 end;
    var F: TTot; M: TTotM; R: TRec; C: TC;
      Arr: array[0..2] of Integer; D: array of Integer;
    begin
      Arr[0] := 1; Arr[1] := 2; Arr[2] := 3;
      F := @Sum; WriteLn(F(Arr));
      R.K := 10; WriteLn(R.Tot(Arr));
      C := TC.Create(Arr); WriteLn(C.S, ' ', Arr[0]);
      Arr[0] := 1;
      M := @C.Tot; WriteLn(M(Arr));
      WriteLn(C.Tot(Arr), ' ', C.Many(1, 2, 3, 4, Arr, 5), ' ', TC.STot(Arr));
      SetLength(D, 3); D[0] := 7; D[1] := 8; D[2] := 9;
      WriteLn(C.Tot(D), ' ', C.Many(0, 0, 0, 0, D, 1))
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '6' + LineEnding + '16' + LineEnding + '6 100' + LineEnding +
    '6' + LineEnding + '6 21 12' + LineEnding + '24 25' + LineEnding, 0);
end;

procedure TE2EOpenArrayTests.TestRun_LiteralFloatElements_EveryForm;
const
  Src = '''
    program P;
    type
      TFn = function(X: Double): Double;
      TFnS = function(X: Single): Single;
      TRef = reference to function(X: Double): Double;
      TRefS = reference to function(X: Single): Single;
      TMeth = function(X: Double): Double of object;
      TK = class
        function Half(X: Double): Double;
        function HalfS(X: Single): Single;
        procedure Run();
      end;
    function Sum(const A: array of Double): Double;
    var I: Integer;
    begin Result := 0; for I := 0 to High(A) do Result := Result + A[I] end;
    function SumS(const A: array of Single): Single;
    var I: Integer;
    begin Result := 0; for I := 0 to High(A) do Result := Result + A[I] end;
    function Twice(X: Double): Double; begin Result := X * 2 end;
    function TwiceS(X: Single): Single; begin Result := X * 2 end;
    function GetFn(): TFn; begin Result := @Twice end;
    function TK.Half(X: Double): Double; begin Result := X / 2 end;
    function TK.HalfS(X: Single): Single; begin Result := X / 2 end;
    procedure TK.Run();
    begin
      WriteLn('self ', Sum([Half(3), 1.0]):0:2, ' ', SumS([HalfS(3)]):0:2);
    end;
    var
      Fns: array[0..0] of TFn; FnsS: array[0..0] of TFnS;
      F: TFn; R: TRef; RS: TRefS; M: TMeth; K: TK; D: Double; S: Single;
    begin
      K := TK.Create();
      D := 1.5; S := 2.5;
      Fns[0] := @Twice; FnsS[0] := @TwiceS; F := @Twice; M := @K.Half;
      R := function(X: Double): Double begin Result := X * 3 end;
      RS := function(X: Single): Single begin Result := X * 3 end;
      WriteLn('values ', Sum([1.0, 2.0]):0:2, ' ', Sum([D, D * 2]):0:2, ' ',
        Sum([-D]):0:2, ' ', SumS([S, S + S]):0:2);
      WriteLn('direct ', Sum([Twice(D)]):0:2, ' ', SumS([TwiceS(S)]):0:2);
      WriteLn('indirect ', Sum([Fns[0](1), 1.0]):0:2, ' ',
        SumS([FnsS[0](1)]):0:2, ' ', Sum([GetFn()(2), 1.0]):0:2);
      WriteLn('closure ', Sum([R(1), 1.0]):0:2, ' ', SumS([RS(1)]):0:2, ' ',
        Sum([M(5), 1.0]):0:2);
      WriteLn('procvar ', Sum([F(1), 1.0]):0:2);
      K.Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'values 3.00 4.50 -1.50 7.50' + #10 +
    'direct 3.00 5.00' + #10 +
    'indirect 3.00 2.00 5.00' + #10 +
    'closure 4.00 3.00 3.50' + #10 +
    'procvar 3.00' + #10 +
    'self 2.50 1.50' + #10, 0);
end;

procedure TE2EOpenArrayTests.TestRun_StaticArrayGetter_AsOpenArrayArg;
const
  Src = '''
    program OA1;
    type
      TArr = array[0..3] of Integer;
      TObj = class
      private
        FArr: TArr;
        function GetArr: TArr;
        function GetArrI(I: Integer): TArr;
      public
        property AG: TArr read GetArr;
        property AI[I: Integer]: TArr read GetArrI;
        procedure Run;
      end;
    function TObj.GetArr: TArr; begin Result := FArr; Result[0] := 99; end;
    function TObj.GetArrI(I: Integer): TArr; begin Result := FArr; Result[1] := I; end;
    procedure ShowOpen(const A: array of Integer); var X: Integer; begin for X in A do Write(X, ' '); WriteLn(); end;
    procedure ShowVal(A: array of Integer); var X: Integer; begin for X in A do Write(X, ' '); WriteLn(); end;
    procedure TObj.Run; begin ShowOpen(AG); ShowOpen(Self.AG); ShowOpen(GetArr()); end;
    var O: TObj;
    begin
      O := TObj.Create(); O.FArr[3] := 3;
      ShowOpen(O.GetArr());
      ShowOpen(O.AG);
      ShowOpen(O.AI[7]);
      ShowVal(O.AG);
      O.Run();
      O.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '99 0 0 3 ' + LineEnding +
    '99 0 0 3 ' + LineEnding +
    '0 7 0 3 ' + LineEnding +
    '99 0 0 3 ' + LineEnding +
    '99 0 0 3 ' + LineEnding +
    '99 0 0 3 ' + LineEnding +
    '99 0 0 3 ' + LineEnding, 0);
end;

procedure TE2EOpenArrayTests.TestRun_ArrayLiteralArg_TakesFormalElementType;
const
  Src = '''
    program P;
    type
      TA = class
        function Name(): string; virtual;
      end;
      TB = class(TA)
        function Name(): string; override;
      end;
      TAC = class of TA;
    function TA.Name(): string;
    begin
      Result := 'A'
    end;
    function TB.Name(): string;
    begin
      Result := 'B'
    end;
    function Names(const L: array of TA): string;
    var I: Integer;
    begin
      Result := '';
      for I := 0 to High(L) do
        Result := Result + L[I].Name()
    end;
    function Sum(const L: array of Double): Double;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(L) do
        Result := Result + L[I]
    end;
    function SumS(const L: array of Single): Single;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(L) do
        Result := Result + L[I]
    end;
    function Pick(const L: array of Integer): string; overload;
    begin
      Result := 'int'
    end;
    function Pick(const L: array of Double): string; overload;
    begin
      Result := 'dbl'
    end;
    function Kinds(const L: array of TAC): string;
    var I: Integer;
    begin
      Result := '';
      for I := 0 to High(L) do
        if L[I] = TB then
          Result := Result + 'b'
        else
          Result := Result + 'a'
    end;
    var X: TA; Y: TB; I: Integer; D: Double;
    begin
      X := TA.Create();
      Y := TB.Create();
      I := 3;
      D := 0.25;
      WriteLn(Names([X, Y]), Names([Y, X, Y]), Names([Y]));
      WriteLn(Sum([1, 2.5, I, D]):0:2, ' ', SumS([1, I, 0.5]):0:2);
      WriteLn(Pick([1, 2]), Pick([1, 2.5]), Pick([I]), Pick([D]));
      WriteLn(Kinds([TB, TA, TB]))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'ABBABB' + #10 + '6.75 4.50' + #10 + 'intdblintdbl' + #10 + 'bab' + #10, 0);
end;


procedure TE2EOpenArrayTests.TestRun_OpenArrayLiteral_RichElements;
const
  Src = '''
    program P;
    type
      IFoo = interface
        function N(): Integer;
      end;
      TFoo = class(TObject, IFoo)
        FN: Integer;
        constructor Create(A: Integer);
        destructor Destroy; override;
        function N(): Integer;
      end;
      TRec = record S: string; K: Integer; end;
      TPt = record X, Y: Integer; end;
      TSA = array[0..1] of string;
      TProc = reference to function(): Integer;
      TM = procedure(A: Integer) of object;
      TObj = class
        Tag: string;
        procedure Hello(A: Integer);
        procedure Take(const A: array of TRec);
      end;
      TTaker = procedure(const A: array of TRec);
    constructor TFoo.Create(A: Integer); begin FN := A; end;
    destructor TFoo.Destroy; begin WriteLn('free ', FN); end;
    function TFoo.N(): Integer; begin Result := FN; end;
    procedure TObj.Hello(A: Integer); begin WriteLn('hello ', Tag, ' ', A); end;
    procedure TObj.Take(const A: array of TRec); begin WriteLn('meth ', A[High(A)].S); end;
    function MkI(A: Integer): IFoo; begin Result := TFoo.Create(A); end;
    function MkR(A: Integer): TRec; begin Result.S := 'r' + IntToStr(A); Result.K := A; end;
    function MkP(A: Integer): TProc; begin Result := function(): Integer begin Result := A * 2; end; end;
    function Pt(X, Y: Integer): TPt; begin Result.X := X; Result.Y := Y; end;
    procedure SI(const A: array of IFoo); var I: Integer; begin for I := 0 to High(A) do WriteLn('i ', A[I].N()); end;
    procedure SR(const A: array of TRec); var I: Integer; begin for I := 0 to High(A) do WriteLn('r ', A[I].S, ' ', A[I].K); end;
    procedure SP(const A: array of TProc); var I: Integer; begin for I := 0 to High(A) do WriteLn('p ', A[I]()); end;
    procedure SPt(const A: array of TPt); var I, T: Integer; begin T := 0; for I := 0 to High(A) do T := T + A[I].X * A[I].Y; WriteLn('pt ', T); end;
    procedure SSA(const A: array of TSA); begin WriteLn('sa ', A[1][0], A[0][1]); end;
    procedure SM(const A: array of TM); var I: Integer; begin for I := 0 to High(A) do A[I](I); end;
    procedure Plain(const A: array of TRec); begin WriteLn('proc ', A[0].S); end;
    var
      O: TObj; T: TTaker; R1: TRec; P1: TProc; X: IFoo; S1, S2: TSA;
    begin
      SI([MkI(1), MkI(2)]);
      SR([MkR(3), MkR(4)]);
      SP([MkP(5)]);
      R1 := MkR(6); P1 := MkP(7); X := MkI(8);
      SR([R1, R1]);
      SP([P1]);
      SI([X, X]);
      SPt([Pt(1, 2), Pt(3, 4)]);
      S1[0] := 'a'; S1[1] := 'b'; S2[0] := 'c'; S2[1] := 'd';
      SSA([S1, S2]);
      O := TObj.Create(); O.Tag := 'o';
      SM([@O.Hello, @O.Hello]);
      O.Take([MkR(9), MkR(10)]);
      T := @Plain;
      T([MkR(11)]);
      X := nil;
      WriteLn('end');
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  AssertRunsOnAll(Src,
    'i 1' + LE + 'i 2' + LE + 'free 1' + LE + 'free 2' + LE +
    'r r3 3' + LE + 'r r4 4' + LE + 'p 10' + LE +
    'r r6 6' + LE + 'r r6 6' + LE + 'p 14' + LE + 'i 8' + LE + 'i 8' + LE +
    'pt 14' + LE + 'sa cb' + LE + 'hello o 0' + LE + 'hello o 1' + LE +
    'meth r10' + LE + 'proc r11' + LE + 'free 8' + LE + 'end' + LE, 0);
end;

procedure TE2EOpenArrayTests.TestRun_OpenArray_ThroughInterfaceDispatch;
const
  Src = '''
    program P;
    type
      TRec = record S: string; K: Integer; end;
      ISink = interface
        procedure Take(const A: array of TRec);
        procedure TakeI(N: Integer; const A: array of Integer; M: Integer);
      end;
      TSink = class(TObject, ISink)
        procedure Take(const A: array of TRec);
        procedure TakeI(N: Integer; const A: array of Integer; M: Integer);
      end;
      THold = class
        S: ISink;
      end;
    procedure TSink.Take(const A: array of TRec); begin WriteLn('rec ', A[0].S, ' ', Length(A)); end;
    procedure TSink.TakeI(N: Integer; const A: array of Integer; M: Integer);
    var I, T: Integer;
    begin
      T := 0;
      for I := 0 to High(A) do T := T + A[I];
      WriteLn('int ', N, ' ', Length(A), ' ', T, ' ', M);
    end;
    function MkA(N: Integer): array of Integer;
    var I: Integer;
    begin
      SetLength(Result, N);
      for I := 0 to N - 1 do Result[I] := I + 1;
    end;
    var I: ISink; H: THold; D: array of TRec; DI: array of Integer;
    begin
      I := TSink.Create();
      SetLength(D, 1); D[0].S := 'x';
      I.Take(D);
      SetLength(DI, 2); DI[0] := 4; DI[1] := 5;
      I.TakeI(1, DI, 2);
      I.TakeI(3, MkA(4), 5);
      I.TakeI(6, [7, 8, 9], 10);
      H := THold.Create();
      H.S := I;
      H.S.TakeI(11, MkA(2), 12);
      H.S.Take([D[0], D[0]]);
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  AssertRunsOnAll(Src,
    'rec x 1' + LE + 'int 1 2 9 2' + LE + 'int 3 4 10 5' + LE +
    'int 6 3 24 10' + LE + 'int 11 2 3 12' + LE + 'rec x 2' + LE, 0);
end;

procedure TE2EOpenArrayTests.TestRun_OpenArray_OfStaticArrays;
const
  Src = '''
    program P;
    type
      TSI = array[0..1] of Integer;
      TSS = array[0..1] of string;
    procedure SI(const A: array of TSI); begin WriteLn('si ', A[1][0], ' ', A[0][1], ' ', Length(A)); end;
    procedure SS(const A: array of TSS); begin WriteLn('ss ', A[1][0], A[0][1]); end;
    var DI: array of TSI; DS: array of TSS; X: TSI; Y: TSS; SX: array[0..2] of TSI;
    begin
      X[0] := 1; X[1] := 2;
      SetLength(DI, 2); DI[0] := X; DI[1] := X; DI[1][0] := 7;
      SI(DI);
      SX[1][0] := 3; SX[0][1] := 4;
      SI(SX);
      Y[0] := 'a'; Y[1] := 'b';
      SetLength(DS, 2); DS[0] := Y; DS[1] := Y; DS[1][0] := 'c';
      SS(DS);
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  AssertRunsOnAll(Src, 'si 7 2 2' + LE + 'si 3 4 3' + LE + 'ss cb' + LE, 0);
end;

initialization
  RegisterTest(TE2EOpenArrayTests);

end.
