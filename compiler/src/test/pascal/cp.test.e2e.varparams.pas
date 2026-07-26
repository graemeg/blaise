{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.varparams;

{ End-to-end tests for var/out parameters — compile + run on BOTH backends.
  Grew out of the test-hardening sweep.  Includes array-element actuals
  (a[i] passed to a var param), which semantic+codegen previously rejected. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EVarParamTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { A var/out param must be stored at the DESTINATION's declared width.
      QBE keyed the store off the RHS type, so `X := 9` with `var X: Byte`
      emitted storew and wrote 4 bytes through a 1-byte destination —
      destroying the adjacent fields.  Native/x86-64 already dispatched
      correctly (movb/movw/movl); arm64 was fixed in d5b94c86. }
    procedure TestRun_VarParam_NarrowWidths_NoAdjacentClobber;
    procedure TestRun_VarInt;
    procedure TestRun_VarSwap;
    procedure TestRun_VarString;
    procedure TestRun_OutParams;
    procedure TestRun_VarRecord;
    procedure TestRun_VarNestedCall;
    procedure TestRun_VarClassField;
    { leg 14: an implicit-Self field (bare FField inside a method, referencing
      Self.FField) passed as a var-parameter — its address is Self + offset,
      distinct from the explicit external-object c.FX form above. }
    procedure TestRun_ImplicitSelfFieldVarArg;
    { Array element as a var/out actual. }
    procedure TestRun_StaticArrayElemVarArg;
    procedure TestRun_DynArrayElemVarArg;
    procedure TestRun_SwapArrayElements;
    procedure TestRun_VarStringArrayElem;
    { Pointer dereference (P^) as a var/out actual — the address is simply
      the pointer's value.  punit passes CurrentResult^ to var params; the
      native backend previously rejected this ("var/out argument must be a
      variable or field"). }
    procedure TestRun_PointerDerefVarArg;
    { SetLength on a var-param string — resizes the caller's string through the
      slot address (arm64 leg 34; also the AddRef-the-rc0-result ARC fix). }
    procedure TestRun_SetLengthVarParamString;
  end;

implementation

const
  LE = #10;

procedure TE2EVarParamTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-varparams');
end;

const
  SrcVarInt = '''
    program Prg;
    procedure Inc2(var X: Integer); begin X := X + 2 end;
    var a: Integer;
    begin a := 10; Inc2(a); WriteLn(a) end.
    ''';

  SrcVarSwap = '''
    program Prg;
    procedure Swap(var A, B: Integer); var t: Integer; begin t := A; A := B; B := t end;
    var x, y: Integer;
    begin x := 1; y := 9; Swap(x, y); WriteLn(x, ' ', y) end.
    ''';

  SrcVarString = '''
    program Prg;
    procedure App(var S: string); begin S := S + '!' end;
    var s: string;
    begin s := 'hi'; App(s); App(s); WriteLn(s) end.
    ''';

  SrcOut = '''
    program Prg;
    procedure GetVals(out A, B: Integer); begin A := 100; B := 200 end;
    var x, y: Integer;
    begin GetVals(x, y); WriteLn(x + y) end.
    ''';

  SrcVarRecord = '''
    program Prg;
    type TP = record X, Y: Integer; end;
    procedure Bump(var R: TP); begin R.X := R.X + 1; R.Y := R.Y + 1 end;
    var r: TP;
    begin r.X := 5; r.Y := 7; Bump(r); WriteLn(r.X, ',', r.Y) end.
    ''';

  SrcVarNested = '''
    program Prg;
    procedure Inner(var X: Integer); begin X := X * 2 end;
    procedure Outer(var Y: Integer); begin Inner(Y); Inner(Y) end;
    var a: Integer;
    begin a := 3; Outer(a); WriteLn(a) end.
    ''';

  SrcVarField = '''
    program Prg;
    type TC = class FX: Integer; end;
    procedure Set5(var X: Integer); begin X := 5 end;
    var c: TC;
    begin c := TC.Create(); Set5(c.FX); WriteLn(c.FX); c.Free() end.
    ''';

  { leg 14: an implicit-Self STRING field passed as a var-param (bare FTab
    inside a method) — its address is Self + offset. }
  SrcImplicitSelfFieldVarArg = '''
    program Prg;
    procedure AppendTo(var S: string; const E: string);
    begin S := S + E end;
    type
      TThing = class
        FTab: string;
        procedure Build;
      end;
    procedure TThing.Build;
    begin
      FTab := 'a';
      AppendTo(FTab, 'bc');
      AppendTo(Self.FTab, 'd')
    end;
    var T: TThing;
    begin
      T := TThing.Create();
      T.Build();
      WriteLn(T.FTab);
      T.Free()
    end.
    ''';

  SrcStaticArrElem = '''
    program Prg;
    procedure S9(var X: Integer); begin X := 9 end;
    var a: array[0..3] of Integer;
    begin a[2] := 0; S9(a[2]); WriteLn(a[2]) end.
    ''';

  SrcDynArrElem = '''
    program Prg;
    procedure S9(var X: Integer); begin X := 9 end;
    var a: array of Integer;
    begin SetLength(a, 4); a[2] := 0; S9(a[2]); WriteLn(a[2]) end.
    ''';

  SrcSwapElems = '''
    program Prg;
    procedure Swap(var A, B: Integer); var t: Integer; begin t := A; A := B; B := t end;
    var a: array[0..3] of Integer;
    begin a[0] := 1; a[1] := 2; Swap(a[0], a[1]); WriteLn(a[0], ' ', a[1]) end.
    ''';

  SrcVarStrElem = '''
    program Prg;
    procedure App(var S: string); begin S := S + 'x' end;
    var a: array[0..1] of string;
    begin a[0] := 'q'; App(a[0]); WriteLn(a[0]) end.
    ''';

  SrcPtrDeref = '''
    program Prg;
    type
      TRec = record
        A: Integer;
        B: Integer;
      end;
      PRec = ^TRec;
    procedure FillRec(var R: TRec); begin R.A := 7; R.B := 11 end;
    procedure Set9(var X: Integer); begin X := 9 end;
    var
      Rec: TRec;
      P: PRec;
      V: Integer;
      PI: ^Integer;
    begin
      P := @Rec;
      FillRec(P^);
      WriteLn(Rec.A, ' ', Rec.B);
      V := 0;
      PI := @V;
      Set9(PI^);
      WriteLn(V)
    end.
    ''';

procedure TE2EVarParamTests.TestRun_VarParam_NarrowWidths_NoAdjacentClobber;
const
  Src = '''
    program P;
    type
      TR = record A, B, C, D: Byte; end;
      TW = record P: Word; Q: Word; end;
    procedure SB(var X: Byte); begin X := 9 end;
    procedure SW(var X: Word); begin X := 999 end;
    procedure SL(var X: Int64); begin X := 4096 end;
    var R: TR; W: TW; L: Int64; M: Int64;
    begin
      R.A := 1; R.B := 200; R.C := 201; R.D := 202;
      SB(R.A);
      WriteLn(R.A, ' ', R.B, ' ', R.C, ' ', R.D);
      W.P := 111; W.Q := 60000;
      SW(W.P);
      WriteLn(W.P, ' ', W.Q);
      { an Integer literal into a var Int64 must widen, not emit storel on a
        w-typed value (qbe rejects that outright) }
      L := 0; M := 77;
      SL(L);
      WriteLn(L, ' ', M)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '9 200 201 202' + LE + '999 60000' + LE + '4096 77' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_VarInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarInt, '12' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_VarSwap;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarSwap, '9 1' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_VarString;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarString, 'hi!!' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_OutParams;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOut, '300' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_VarRecord;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarRecord, '6,8' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_VarNestedCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarNested, '12' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_VarClassField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarField, '5' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_ImplicitSelfFieldVarArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcImplicitSelfFieldVarArg, 'abcd' + LE, 0);
  { the string field is grown through the var-param — no leak }
  AssertLeakFreeOnAll(SrcImplicitSelfFieldVarArg, 'abcd');
end;

procedure TE2EVarParamTests.TestRun_StaticArrayElemVarArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticArrElem, '9' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_DynArrayElemVarArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynArrElem, '9' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_SwapArrayElements;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSwapElems, '2 1' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_VarStringArrayElem;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarStrElem, 'qx' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_PointerDerefVarArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcPtrDeref, '7 11' + LE + '9' + LE, 0);
end;

procedure TE2EVarParamTests.TestRun_SetLengthVarParamString;
const
  Src = '''
    program Prg;
    procedure Grow(var S: string; N: Integer); begin SetLength(S, N) end;
    var s: string;
    begin
      s := 'ab';
      Grow(s, 5);
      WriteLn(Length(s))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '5' + LE, 0);
end;

initialization
  RegisterTest(TE2EVarParamTests);

end.
