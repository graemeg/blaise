{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.varinit;

{ E2E tests for initialised global variables (var G: T = value): compile ->
  run, asserting stdout on every backend (QBE + native).  The IR-level tests
  live in cp.test.varinit.pas. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EVarInitTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_IntegerInit;
    procedure TestRun_StringInit;
    procedure TestRun_BooleanInit;
    procedure TestRun_RealInit;
    procedure TestRun_Int64Init;
    procedure TestRun_ArrayInit_ZeroBased;
    procedure TestRun_ArrayInit_NonZeroBased;
    procedure TestRun_MultipleInits;
    procedure TestRun_InitThenReassign;
    { set initialisers on program and unit variables: a small set, a
      64-member set, a jumbo set and the empty set hold exactly their
      members (rejected in a program; silently empty in a unit) }
    procedure TestRun_SetInit_ProgramAndUnit;
    { `= nil` on every pointer-like kind, in a program and a unit interface }
    procedure TestRun_NilInit_ProgramAndUnit;
    procedure TestRun_FloatConstFold_Parens;
    procedure TestRun_FloatConstFold_NegativeMul;
  end;

implementation

procedure TE2EVarInitTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-varinit')
end;

procedure TE2EVarInitTests.TestRun_IntegerInit;
const Src =
  '''
  program P;
  var G: Int32 = 42;
  begin
    WriteLn(G)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EVarInitTests.TestRun_StringInit;
const Src =
  '''
  program P;
  var S: string = 'hello world';
  begin
    WriteLn(S)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'hello world' + LineEnding, 0);
end;

procedure TE2EVarInitTests.TestRun_BooleanInit;
const Src =
  '''
  program P;
  var B: Boolean = True;
  begin
    if B then WriteLn('yes') else WriteLn('no')
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'yes' + LineEnding, 0);
end;

procedure TE2EVarInitTests.TestRun_RealInit;
const Src =
  '''
  program P;
  var D: Float64 = 3.5;
  begin
    WriteLn(D)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '3.5' + LineEnding, 0);
end;

procedure TE2EVarInitTests.TestRun_Int64Init;
const Src =
  '''
  program P;
  var Big: Int64 = 9999999999;
  begin
    WriteLn(Big)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '9999999999' + LineEnding, 0);
end;

procedure TE2EVarInitTests.TestRun_ArrayInit_ZeroBased;
const Src =
  '''
  program P;
  var A: array[0..2] of Int32 = (10, 20, 30);
  begin
    WriteLn(A[0]); WriteLn(A[1]); WriteLn(A[2])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2EVarInitTests.TestRun_ArrayInit_NonZeroBased;
const Src =
  '''
  program P;
  var R: array[1..3] of Int32 = (7, 8, 9);
  begin
    WriteLn(R[1]); WriteLn(R[3])
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '7' + LE + '9' + LE, 0);
end;

procedure TE2EVarInitTests.TestRun_MultipleInits;
const Src =
  '''
  program P;
  var
    A: Int32 = 1;
    B: Int32 = 2;
    C: string = 'three';
  begin
    WriteLn(A); WriteLn(B); WriteLn(C)
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '2' + LE + 'three' + LE, 0);
end;

procedure TE2EVarInitTests.TestRun_InitThenReassign;
const Src =
  '''
  program P;
  var G: Int32 = 10;
  begin
    WriteLn(G);
    G := G + 5;
    WriteLn(G)
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '10' + LE + '15' + LE, 0);
end;

{ Compile-time float-const folding crosses the codegen->run boundary here: the
  compiler folds the expression (uSemantic.RawDoubleToStr) and bakes the literal
  into the IR, then the running program prints it.  An IR-only test cannot catch
  a folding bug that depends on the host ABI — the compiler's own RawDoubleToStr
  once called libc snprintf through a fixed-arg declaration, which violates the
  SysV variadic ABI (%al unset) and mis-folded on some hosts.  These run-and-
  compare tests pin the actual folded value on every backend. }
procedure TE2EVarInitTests.TestRun_FloatConstFold_Parens;
const Src =
  '''
  program P;
  const X = (1.0 + 2.0) * 3.0;
  begin
    WriteLn(X)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '9' + LineEnding, 0);
end;

procedure TE2EVarInitTests.TestRun_FloatConstFold_NegativeMul;
const Src =
  '''
  program P;
  const X = -1.5 * 2.0;
  begin
    WriteLn(X)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '-3' + LineEnding, 0);
end;

procedure TE2EVarInitTests.TestRun_SetInit_ProgramAndUnit;
const
  UnitSrc =
    '''
    unit SetInitU;
    interface
    type
      TBig = 0..199;
      TJumbo = set of TBig;
      TWide = 0..63;
      TWideSet = set of TWide;
    var
      UJ: TJumbo = [1, 150, 199];
      UW: TWideSet = [0, 40, 63];
    implementation
    end.
    ''';
  Src =
    '''
    program P;
    uses SetInitU;
    type
      TEn = (eA, eB, eC, eD);
      TS = set of TEn;
    var
      S: TS = [eA, eC..eD];
      E: TS = [];
      J: TJumbo = [2, 100];
    var I: Int;
    begin
      WriteLn(eA in S, ' ', eB in S, ' ', eC in S, ' ', eD in S, ' ', E = []);
      WriteLn(2 in J, ' ', 3 in J, ' ', 100 in J);
      WriteLn(1 in UJ, ' ', 150 in UJ, ' ', 199 in UJ, ' ', 2 in UJ);
      WriteLn(0 in UW, ' ', 40 in UW, ' ', 63 in UW, ' ', 41 in UW);
      S := S - [eA];
      Include(UJ, 7);
      WriteLn(eA in S, ' ', 7 in UJ)
    end.
    ''';
var
  Outp: string;
  Rc: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compiles and runs',
    CompileAndRunWithUnit('SetInitU', UnitSrc, Src, Outp, Rc));
  AssertEquals('exit code', 0, Rc);
  AssertEquals('stdout',
    'True False True True True' + LineEnding +
    'True False True' + LineEnding +
    'True True True False' + LineEnding +
    'True True True False' + LineEnding +
    'False True' + LineEnding, Outp);
end;

procedure TE2EVarInitTests.TestRun_NilInit_ProgramAndUnit;
const
  UnitSrc =
    '''
    unit NilInitU;
    interface
    var
      UP: Pointer = nil;
      UO: TObject = nil;
    implementation
    var
      HiddenA: array of Int32 = nil;
    function HiddenLen: Int;
    begin
      Result := Length(HiddenA)
    end;
    end.
    ''';
  Src =
    '''
    program P;
    uses NilInitU;
    type
      TProc = procedure;
      TClassRef = class of TObject;
      IThing = interface end;
    var
      Ptr: Pointer = nil;
      O: TObject = nil;
      C: TClassRef = nil;
      F: TProc = nil;
      I: IThing = nil;
      A: array of Int32 = nil;
    begin
      WriteLn(Ptr = nil, ' ', O = nil, ' ', C = nil, ' ', Assigned(F), ' ',
        I = nil, ' ', Length(A));
      WriteLn(UP = nil, ' ', UO = nil);
      O := TObject.Create();
      SetLength(A, 3);
      WriteLn(O = nil, ' ', Length(A))
    end.
    ''';
var
  Outp: string;
  Rc: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compiles and runs',
    CompileAndRunWithUnit('NilInitU', UnitSrc, Src, Outp, Rc));
  AssertEquals('exit code', 0, Rc);
  AssertEquals('stdout',
    'True True True False True 0' + LineEnding +
    'True True' + LineEnding +
    'False 3' + LineEnding, Outp);
end;

initialization
  RegisterTest(TE2EVarInitTests);

end.
