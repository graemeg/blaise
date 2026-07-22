{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.jumboset;

{ E2E tests for JUMBO sets (set of an enum with >64 members): compile -> run,
  assert stdout, on BOTH backends (QBE + native) via AssertRunsOnAll.  Covers
  membership across the >64 boundary, Include/Exclude, union/intersection/
  difference, equality, for-in, value params, sret returns, and a jumbo
  constant consumed at runtime. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EJumboSetTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_IncludeMembership_AcrossBoundary;
    procedure TestRun_SetOps_UnionInterDiff;
    procedure TestRun_Equality;
    procedure TestRun_ForIn_CountsMembers;
    procedure TestRun_Param_And_Return;
    procedure TestRun_RecordField_RoundTrips;
    procedure TestRun_ClassField_RoundTrips;
    procedure TestRun_VarParam_RoundTrips;
    procedure TestRun_Constant;
    { Regression: a jumbo-set-returning call whose result is assigned back over
      a variable that is ALSO one of its arguments (s := Comp(s)).  The native
      caller memset the sret destination before evaluating the argument list,
      so the callee saw an empty set.  The distinct-destination control in the
      same program pins the non-aliasing path. }
    procedure TestRun_SelfAssignedSretReturn_NotAliased;
    { Same, with the aliased set in NON-FIRST argument position. }
    procedure TestRun_SelfAssignedSret_NonFirstArgPosition;
    { Same, where the alias is an ARGUMENT of a record-method call whose
      receiver is a different variable. }
    procedure TestRun_SelfAssignedSret_MethodArgument;
    { Jumbo-set ARRAY ELEMENTS: the element read returned the loaded first
      8 bitmap bytes instead of the element's bitmap ADDRESS, so `x in B[0]`
      and element-to-element copies dereferenced garbage — SIGSEGV on both
      backends (BUG-20260721-jumbo-set-in-array-elem). }
    procedure TestRun_JumboSet_ArrayElement_MembershipAndCopy;
    { Jumbo-set elements of a FIELD-typed array (R.Arr[0], H.FArr[0],
      H.FDyn[0], and in-method FArr[0]): the FieldAccess+ArrayAccess store
      wrote only the RHS pointer (8 of 32 bytes, aliasing) and the native
      read SIGSEGV'd; plus the set-literal-into-field-element destination was
      rejected by semantic (BUG-20260722-jumbo-field-array-elem). }
    procedure TestRun_JumboSet_FieldArrayElement;
    procedure TestRun_JumboSet_NestedFieldChainElement;
  end;

implementation

const
  LE = #10;

  { 80-member enum shared by the test programs. }
  ENUMHDR =
    '''
    type TBig = (b00,b01,b02,b03,b04,b05,b06,b07,b08,b09,b10,b11,b12,b13,b14,b15,
                 b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,
                 b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,
                 b48,b49,b50,b51,b52,b53,b54,b55,b56,b57,b58,b59,b60,b61,b62,b63,
                 b64,b65,b66,b67,b68,b69,b70,b71,b72,b73,b74,b75,b76,b77,b78,b79);
         TBigSet = set of TBig;
    ''';

procedure TE2EJumboSetTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-jumboset');
end;

procedure TE2EJumboSetTests.TestRun_IncludeMembership_AcrossBoundary;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var s: TBigSet;' + LE +
         'begin' + LE +
         '  s := [];' + LE +
         '  Include(s, b70);' + LE +
         '  Include(s, b05);' + LE +
         '  WriteLn(b70 in s);' + LE +   { True }
         '  WriteLn(b71 in s);' + LE +   { False }
         '  WriteLn(b05 in s);' + LE +   { True }
         '  Exclude(s, b70);' + LE +
         '  WriteLn(b70 in s)' + LE +    { False }
         'end.';
  AssertRunsOnAll(Src, 'True' + LE + 'False' + LE + 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_SetOps_UnionInterDiff;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var a, b, c: TBigSet;' + LE +
         'begin' + LE +
         '  a := [b05, b70];' + LE +
         '  b := [b05, b40];' + LE +
         '  c := a + b;' + LE +
         '  WriteLn(b05 in c, b40 in c, b70 in c);' + LE +  { True True True }
         '  c := a * b;' + LE +
         '  WriteLn(b05 in c, b40 in c, b70 in c);' + LE +  { True False False }
         '  c := a - b;' + LE +
         '  WriteLn(b05 in c, b70 in c)' + LE +             { False True }
         'end.';
  AssertRunsOnAll(Src,
    'TrueTrueTrue' + LE + 'TrueFalseFalse' + LE + 'FalseTrue' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_Equality;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var a, b: TBigSet;' + LE +
         'begin' + LE +
         '  a := [b70, b05];' + LE +
         '  b := [b05, b70];' + LE +
         '  WriteLn(a = b);' + LE +      { True }
         '  Include(b, b79);' + LE +
         '  WriteLn(a = b);' + LE +      { False }
         '  WriteLn(a <> b)' + LE +      { True }
         'end.';
  AssertRunsOnAll(Src, 'True' + LE + 'False' + LE + 'True' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_ForIn_CountsMembers;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var s: TBigSet; e: TBig; n: Integer;' + LE +
         'begin' + LE +
         '  s := [b05, b40, b70, b79];' + LE +
         '  n := 0;' + LE +
         '  for e in s do n := n + 1;' + LE +
         '  WriteLn(n);' + LE +          { 4 }
         '  for e in s do Write(Ord(e), '' '');' + LE +
         '  WriteLn()' + LE +
         'end.';
  AssertRunsOnAll(Src, '4' + LE + '5 40 70 79 ' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_Param_And_Return;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'function HasHigh(const x: TBigSet): Boolean;' + LE +
         'begin Result := b70 in x; end;' + LE +
         'function MakeSet: TBigSet;' + LE +
         'begin Result := [b65, b70]; end;' + LE +
         'var s: TBigSet;' + LE +
         'begin' + LE +
         '  s := [b70, b05];' + LE +
         '  WriteLn(HasHigh(s));' + LE +    { True }
         '  s := [b05];' + LE +
         '  WriteLn(HasHigh(s));' + LE +    { False }
         '  s := MakeSet();' + LE +
         '  WriteLn(b65 in s, b70 in s, b05 in s)' + LE +  { True True False }
         'end.';
  AssertRunsOnAll(Src,
    'True' + LE + 'False' + LE + 'TrueTrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_RecordField_RoundTrips;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { A jumbo set stored into a record field used to lose every member silently:
    the field received the ADDRESS of a stack scratch buffer instead of a copy
    of the bitmap. }
  Src := 'program P;' + LE + ENUMHDR + LE +
         'type TRec = record S: TBigSet; N: Integer; end;' + LE +
         'var r: TRec;' + LE +
         'begin' + LE +
         '  r.S := [];' + LE +
         '  r.S := r.S + [b05];' + LE +
         '  r.S := r.S + [b70];' + LE +
         '  r.N := 7;' + LE +
         '  WriteLn(b05 in r.S, b70 in r.S, b71 in r.S);' + LE +
         '  WriteLn(r.N)' + LE +
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueFalse' + LE + '7' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_ClassField_RoundTrips;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'type THolder = class' + LE +
         '  S: TBigSet;' + LE +
         '  procedure Fill;' + LE +
         'end;' + LE +
         'procedure THolder.Fill;' + LE +
         'begin S := S + [b65]; end;' + LE +
         'var h: THolder;' + LE +
         'begin' + LE +
         '  h := THolder.Create();' + LE +
         '  h.S := [];' + LE +
         '  h.S := h.S + [b40];' + LE +
         '  h.Fill();' + LE +
         '  WriteLn(b40 in h.S, b65 in h.S, b00 in h.S)' + LE +
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_VarParam_RoundTrips;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { Assigning through a var/out parameter must copy the bitmap into the
    caller's storage, not store a pointer into the pointer slot. }
  Src := 'program P;' + LE + ENUMHDR + LE +
         'procedure Fill(var s: TBigSet);' + LE +
         'begin' + LE +
         '  s := [];' + LE +
         '  s := s + [b05];' + LE +
         '  s := s + [b70];' + LE +
         'end;' + LE +
         'procedure FillOut(out s: TBigSet);' + LE +
         'begin s := [b79]; end;' + LE +
         'var a, b: TBigSet;' + LE +
         'begin' + LE +
         '  Fill(a);' + LE +
         '  WriteLn(b05 in a, b70 in a, b71 in a);' + LE +
         '  FillOut(b);' + LE +
         '  WriteLn(b79 in b, b05 in b)' + LE +
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueFalse' + LE + 'TrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_Constant;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'const HIGHS: TBigSet = [b65, b70, b79];' + LE +
         'var s: TBigSet;' + LE +
         'begin' + LE +
         '  s := HIGHS;' + LE +
         '  WriteLn(b65 in s, b70 in s, b79 in s, b00 in s)' + LE +  { True True True False }
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueTrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_SelfAssignedSretReturn_NotAliased;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { Comp keeps b70 (which IS in the source) and adds b03 (which is NOT).
    s := Comp(s) must observe s's live value; the trailing t := Comp(s) is the
    non-aliasing control. }
  Src := 'program P;' + LE + ENUMHDR + LE +
         'function Comp(const x: TBigSet): TBigSet;' + LE +
         'begin' + LE +
         '  Result := [];' + LE +
         '  if b70 in x then Include(Result, b70);' + LE +
         '  if b05 in x then Include(Result, b03);' + LE +
         'end;' + LE +
         'var s, t: TBigSet;' + LE +
         'begin' + LE +
         '  s := [b70, b05];' + LE +
         '  s := Comp(s);' + LE +
         '  WriteLn(b70 in s, b03 in s, b05 in s);' + LE +
         '  t := [b70, b05];' + LE +
         '  t := Comp(t);' + LE +
         '  WriteLn(b70 in t, b03 in t, b05 in t)' + LE +
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueFalse' + LE + 'TrueTrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_SelfAssignedSret_NonFirstArgPosition;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'function Pick(const n: Integer; const x: TBigSet): TBigSet;' + LE +
         'begin' + LE +
         '  Result := [];' + LE +
         '  if b70 in x then Include(Result, b70);' + LE +
         '  if n > 0 then Include(Result, b01);' + LE +
         'end;' + LE +
         'var s: TBigSet;' + LE +
         'begin' + LE +
         '  s := [b70, b05];' + LE +
         '  s := Pick(1, s);' + LE +
         '  WriteLn(b70 in s, b01 in s, b05 in s)' + LE +
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_SelfAssignedSret_MethodArgument;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { The receiver R is a different variable — the alias sits in the argument
    list only, which the old receiver-only guard never inspected. }
  Src := 'program P;' + LE + ENUMHDR + LE +
         'type TH = record' + LE +
         '  Tag: Integer;' + LE +
         '  function Comp(const x: TBigSet): TBigSet;' + LE +
         'end;' + LE +
         'function TH.Comp(const x: TBigSet): TBigSet;' + LE +
         'begin' + LE +
         '  Result := [];' + LE +
         '  if b70 in x then Include(Result, b70);' + LE +
         '  if Self.Tag > 0 then Include(Result, b02);' + LE +
         'end;' + LE +
         'var s: TBigSet;' + LE +
         '    R: TH;' + LE +
         'begin' + LE +
         '  R.Tag := 1;' + LE +
         '  s := [b70, b05];' + LE +
         '  s := R.Comp(s);' + LE +
         '  WriteLn(b70 in s, b02 in s, b05 in s)' + LE +
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_JumboSet_ArrayElement_MembershipAndCopy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program P;
    type TBig = set of Byte;
    var
      B: array[0..1] of TBig;
      D: array of TBig;
      U: TBig;
    begin
      B[0] := [5, 40, 200];
      if 200 in B[0] then WriteLn('y') else WriteLn('n');
      if 6 in B[0] then WriteLn('y') else WriteLn('n');
      B[1] := B[0];
      if 40 in B[1] then WriteLn('y') else WriteLn('n');
      SetLength(D, 1);
      D[0] := B[1];
      if 200 in D[0] then WriteLn('y') else WriteLn('n');
      { Consumers of the element ADDRESS convention: Include/Exclude on an
        element, union of two elements, equality of elements. }
      Include(B[1], 77);
      Exclude(B[1], 5);
      if (77 in B[1]) and not (5 in B[1]) then WriteLn('y') else WriteLn('n');
      U := B[0] + B[1];
      if (5 in U) and (77 in U) then WriteLn('y') else WriteLn('n');
      if B[0] = B[1] then WriteLn('y') else WriteLn('n')
    end.
    ''', 'y' + LE + 'n' + LE + 'y' + LE + 'y' + LE +
         'y' + LE + 'y' + LE + 'n' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_JumboSet_FieldArrayElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program P;
    type
      TBig = set of Byte;
      TRec = record Arr: array[0..1] of TBig; end;
      THold = class
      public
        FArr: array[0..1] of TBig;
        FDyn: array of TBig;
        function ProbeSelf(): Boolean;
      end;
    function THold.ProbeSelf(): Boolean;
    begin
      Result := 200 in FArr[0]
    end;
    var
      R: TRec;
      H: THold;
      V: TBig;
    begin
      V := [5, 40, 200];
      R.Arr[0] := V;                { record field-array elem store (memcpy) }
      R.Arr[1] := [3, 250];         { set-literal into field-array elem }
      H := THold.Create();
      H.FArr[0] := V;               { class field-array elem store }
      SetLength(H.FDyn, 2);
      H.FDyn[0] := V;               { class dyn-array field elem store }
      V := V - [200];               { mutate source — element must not alias }
      if 200 in R.Arr[0]  then WriteLn('R')  else WriteLn('r');
      if 250 in R.Arr[1]  then WriteLn('L')  else WriteLn('l');
      if 200 in H.FArr[0] then WriteLn('H')  else WriteLn('h');
      if 200 in H.FDyn[0] then WriteLn('D')  else WriteLn('d');
      if H.ProbeSelf()    then WriteLn('S')  else WriteLn('s')
    end.
    ''', 'R' + LE + 'L' + LE + 'H' + LE + 'D' + LE + 'S' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_JumboSet_NestedFieldChainElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A jumbo element of an array field reached through a NESTED record chain
    (O.B.Arr[0]) — the chained-base read arm also had to return the element
    address (QBE SIGSEGV'd on the 8-byte load; this shape was masked before
    the set-literal semantic fix that unblocked it). }
  AssertRunsOnAll('''
    program P;
    type
      TBig = set of Byte;
      TInner = record Arr: array[0..1] of TBig; end;
      TOuter = record Tag: Int64; B: TInner; end;
    var
      O: TOuter;
    begin
      O.Tag := 1;
      O.B.Arr[0] := [5, 200];
      O.B.Arr[1] := [40];
      if 200 in O.B.Arr[0] then WriteLn('a')  else WriteLn('.');
      if 40  in O.B.Arr[0] then WriteLn('.')  else WriteLn('b');
      if 40  in O.B.Arr[1] then WriteLn('c')  else WriteLn('.')
    end.
    ''', 'a' + LE + 'b' + LE + 'c' + LE, 0);
end;

initialization
  RegisterTest(TE2EJumboSetTests);

end.
