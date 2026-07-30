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

initialization
  RegisterTest(TE2EOpenArrayTests);

end.
