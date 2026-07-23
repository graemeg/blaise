{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.dynarray;

{ End-to-end tests for dynamic arrays — compile + run on BOTH backends.
  Grew out of the test-hardening sweep (dynarray was IR-only).  Includes
  SetLength on an array element (SetLength(m[i], n)), which enables ragged
  2-D dynamic arrays and was previously rejected. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EDynArrayTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_SetLengthFillSum;
    procedure TestRun_LengthAndHigh;
    procedure TestRun_GrowPreservesContents;
    procedure TestRun_ArrayOfString;
    procedure TestRun_ReferenceSemantics;
    procedure TestRun_ReturnByValue;
    { SetLength on an element (ragged 2-D dynamic array). }
    procedure TestRun_SetLengthOnElement_Ragged;
    procedure TestRun_SetLengthOnElement_FillViaRow;
    { Chained element WRITE m[i][j] := v on dyn-of-dyn (previously rejected
      with "Multi-dimensional subscript base must be a static array"). }
    procedure TestRun_ChainedWrite_Int2D;
    procedure TestRun_ChainedWrite_String2D;
    procedure TestRun_ChainedWrite_Int3D;
    { SetLength(dest, Length(src)) where the length sub-expression itself
      emits a call (_DynArrayLength) — must not clobber the dest pointer
      register before the resize call.  Regression for the native backend
      Result-aliases-param bug: writes to Result[i] were lost because
      SetLength resized the parameter, not Result. }
    procedure TestRun_SetLengthResultFromParamLength;
    procedure TestRun_DiffOfConstArrayParams;
    procedure TestRun_SetLengthGlobalFromGlobalLength;
    procedure TestRun_SetLengthLocalFromLocalLength;
    procedure TestRun_SetLengthFromUserFuncCall;
    { Element READ of a class dyn-array FIELD with a COMPOUND index
      (H.Bytes[R.Offset + K]): the native lowering held the data pointer in
      %rcx while EmitExprToEax evaluated the index, and a record-field or
      other rcx-using index expression clobbered the base -> garbage deref
      (segfault).  Static-array fields already push/popped the base. }
    procedure TestRun_FieldElemRead_CompoundIndex;
    { leg 27: SetLength on a dyn-array FIELD of a VAR-PARAM record — the resize
      must reach the CALLER's record (the dereferenced var-param address), so
      the caller sees the resized array after the call. }
    procedure TestRun_SetLengthOnVarParamRecordField;
    { leg 28: element write into a dyn-array FIELD of a VAR-PARAM record —
      C.Arr[I] := V must reach the CALLER's array, for both an int element and
      a managed-record element. }
    procedure TestRun_VarParamRecordArrayFieldElemWrite;
    { A dyn-array passed BY VALUE (non-const) — the callee co-owns its copy.
      The value must survive the call and the caller's array stay intact. }
    procedure TestRun_ByValueDynArrayParam;
    { SetLength on a dyn-array ELEMENT of an ARRAY FIELD — SetLength(H.FNest[I], N)
      where FNest: array[..] of array of T.  The native slot-address path dropped
      the [I] subscript and resized the wrong slot -> SIGSEGV; QBE already routed
      through the subscript-aware EmitLValueAddr (BUG-20260723-native-setlength-field-array-elem). }
    procedure TestRun_SetLengthOnArrayFieldElem;
    { Inc/Dec on a plain array-VARIABLE element (A[I], D[I]) — the native
      EmitIncDec dispatch had no TStringSubscriptExpr branch and rejected it
      with "unsupported expression form" while QBE accepted it
      (BUG-20260723-native-incdec-plain-array-elem). }
    procedure TestRun_IncDec_PlainArrayElem;
  end;

implementation

const
  LE = #10;

procedure TE2EDynArrayTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-dynarray');
end;

const
  SrcFillSum = '''
    program Prg;
    var a: array of Integer; i, sum: Integer;
    begin SetLength(a, 5); for i := 0 to 4 do a[i] := i * 2;
      sum := 0; for i := 0 to High(a) do sum := sum + a[i]; WriteLn(sum) end.
    ''';

  SrcLenHigh = '''
    program Prg;
    var a: array of Integer;
    begin SetLength(a, 7); WriteLn(Length(a), ' ', High(a)) end.
    ''';

  SrcGrow = '''
    program Prg;
    var a: array of Integer; i: Integer;
    begin SetLength(a, 3); for i := 0 to 2 do a[i] := i + 1;
      SetLength(a, 6); WriteLn(a[0], a[1], a[2], ' ', Length(a)) end.
    ''';

  SrcOfString = '''
    program Prg;
    var a: array of string; i: Integer;
    begin SetLength(a, 3); a[0] := 'x'; a[1] := 'y'; a[2] := 'z';
      for i := 0 to 2 do Write(a[i]); WriteLn() end.
    ''';

  SrcRefSem = '''
    program Prg;
    var a, b: array of Integer;
    begin SetLength(a, 3); a[0] := 7; b := a; b[0] := 99; WriteLn(a[0]) end.
    ''';

  SrcReturn = '''
    program Prg;
    type TIntArr = array of Integer;
    function MakeArr(n: Integer): TIntArr; var i: Integer; begin SetLength(Result, n); for i := 0 to n-1 do Result[i] := i end;
    var a: TIntArr;
    begin a := MakeArr(5); WriteLn(Length(a), ' ', a[4]) end.
    ''';

  SrcRagged = '''
    program Prg;
    var m: array of array of Integer;
    begin SetLength(m, 3); SetLength(m[0], 1); SetLength(m[1], 2); SetLength(m[2], 3);
      WriteLn(Length(m[0]), Length(m[1]), Length(m[2])) end.
    ''';

  SrcFillViaRow = '''
    program Prg;
    var m: array of array of Integer; row: array of Integer; i, sum: Integer;
    begin SetLength(m, 2); SetLength(m[0], 3);
      row := m[0]; for i := 0 to 2 do row[i] := i + 1;
      sum := 0; for i := 0 to 2 do sum := sum + m[0][i];
      WriteLn(sum) end.
    ''';

  SrcChainedInt2D = '''
    program Prg;
    var m: array of array of Integer; i, j: Integer;
    begin
      SetLength(m, 2); SetLength(m[0], 2); SetLength(m[1], 2);
      m[0][0] := 1; m[0][1] := 2; m[1][0] := 3; m[1][1] := 4;
      for i := 0 to 1 do for j := 0 to 1 do Write(m[i][j]);
      WriteLn()
    end.
    ''';

  SrcChainedString2D = '''
    program Prg;
    var m: array of array of string; i, j: Integer;
    begin
      SetLength(m, 2); SetLength(m[0], 2); SetLength(m[1], 2);
      m[0][0] := 'a'; m[0][1] := 'b'; m[1][0] := 'c'; m[1][1] := 'd';
      m[0][1] := 'B';
      for i := 0 to 1 do for j := 0 to 1 do Write(m[i][j]);
      WriteLn()
    end.
    ''';

  SrcChainedInt3D = '''
    program Prg;
    var c: array of array of array of Integer; i, j, k: Integer;
    begin
      SetLength(c, 2);
      for i := 0 to 1 do begin
        SetLength(c[i], 2);
        for j := 0 to 1 do SetLength(c[i][j], 2);
      end;
      for i := 0 to 1 do for j := 0 to 1 do for k := 0 to 1 do
        c[i][j][k] := i*4 + j*2 + k;
      for i := 0 to 1 do for j := 0 to 1 do for k := 0 to 1 do
        Write(c[i][j][k]);
      WriteLn()
    end.
    ''';

  { SetLength(Result, Length(A)) inside a dynarray-returning function whose
    parameter is also a dynarray.  Stores a constant 7 — output must be 7,
    not A[0] (=5).  This is the minimal native Result-aliases-param repro. }
  SrcResultFromParamLen = '''
    program Prg;
    type TA = array of UInt32;
    function F(const A, B: TA): TA;
    var I: Integer;
    begin
      SetLength(Result, Length(A));
      I := 0;
      while I < Length(A) do begin Result[I] := 7; I := I + 1 end;
    end;
    var X, Y, Z: TA;
    begin
      SetLength(X, 1); X[0] := 5;
      SetLength(Y, 1); Y[0] := 3;
      Z := F(X, Y);
      WriteLn(Z[0])
    end.
    ''';

  { The original symptom: store the difference of two indexed const-array-param
    loads.  Result[0] must be 2 (=5-3), not 5. }
  SrcDiffConstParams = '''
    program Prg;
    type TA = array of UInt32;
    function Diff(const A, B: TA): TA;
    var I: Integer;
    begin
      SetLength(Result, Length(A));
      I := 0;
      while I < Length(A) do begin Result[I] := A[I] - B[I]; I := I + 1 end;
    end;
    var R, X, Y: TA;
    begin
      SetLength(X, 1); X[0] := 5;
      SetLength(Y, 1); Y[0] := 3;
      R := Diff(X, Y);
      WriteLn(R[0])
    end.
    ''';

  { Global-array target: SetLength(G, Length(H)) at program scope exercises
    the global (%rip-relative) store-back path, not the local one. }
  SrcGlobalFromGlobalLen = '''
    program Prg;
    var G, H: array of Integer; I: Integer;
    begin
      SetLength(H, 4);
      for I := 0 to 3 do H[I] := I + 1;
      SetLength(G, Length(H));
      for I := 0 to High(G) do G[I] := 9;
      for I := 0 to High(G) do Write(G[I]);
      WriteLn()
    end.
    ''';

  { Two local arrays: SetLength(A, Length(B)) where B is a local — the length
    call must not clobber A's pointer before the resize. }
  SrcLocalFromLocalLen = '''
    program Prg;
    var A, B: array of Integer; I: Integer;
    begin
      SetLength(B, 3);
      SetLength(A, Length(B));
      for I := 0 to High(A) do A[I] := 8;
      for I := 0 to High(A) do Write(A[I]);
      WriteLn()
    end.
    ''';

  { Length expression is a user-function call (the most general rdi-clobber):
    SetLength(A, Pick()) where Pick() returns an Integer via its own call. }
  SrcFromUserFuncCall = '''
    program Prg;
    var A: array of Integer; I: Integer;
    function Pick: Integer;
    begin Result := 3 end;
    begin
      SetLength(A, Pick());
      for I := 0 to High(A) do A[I] := 6;
      for I := 0 to High(A) do Write(A[I]);
      WriteLn()
    end.
    ''';

procedure TE2EDynArrayTests.TestRun_SetLengthFillSum;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFillSum, '20' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_LengthAndHigh;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcLenHigh, '7 6' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_GrowPreservesContents;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGrow, '123 6' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_ArrayOfString;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOfString, 'xyz' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_ReferenceSemantics;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRefSem, '99' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_ReturnByValue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcReturn, '5 4' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthOnElement_Ragged;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRagged, '123' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthOnElement_FillViaRow;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFillViaRow, '6' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_ChainedWrite_Int2D;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcChainedInt2D, '1234' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_ChainedWrite_String2D;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcChainedString2D, 'aBcd' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_ChainedWrite_Int3D;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcChainedInt3D, '01234567' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthResultFromParamLength;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcResultFromParamLen, '7' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_DiffOfConstArrayParams;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDiffConstParams, '2' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthGlobalFromGlobalLength;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGlobalFromGlobalLen, '9999' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthLocalFromLocalLength;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcLocalFromLocalLen, '888' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthFromUserFuncCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFromUserFuncCall, '666' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_FieldElemRead_CompoundIndex;
const
  Src = '''
    program p;
    type
      TRec = record
        Offset: Integer;
        Pad: Int64;
      end;
      THolder = class
      public
        Bytes: array of Byte;
      end;
    var
      H: THolder;
      R: TRec;
      K: Integer;
      V: Int64;
    begin
      H := THolder.Create();
      SetLength(H.Bytes, 16);
      for K := 0 to 15 do
        H.Bytes[K] := K + 1;
      R.Offset := 4;
      V := 0;
      for K := 0 to 7 do
        V := V or (Int64(H.Bytes[R.Offset + K]) shl (K * 8));
      { bytes 5..12 little-endian }
      WriteLn(V = $0C0B0A0908070605)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthOnVarParamRecordField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Grow(var C: TCtx) does SetLength(C.Arr, N) then C.Arr[0] := 42.  The resize
    and the element write must reach the CALLER's record (through the derefed
    var-param address), so after the call Length(Ctx.Arr)=3 and Ctx.Arr[0]=42. }
  AssertRunsOnAll('''
    program Prg;
    type TCtx = record Arr: array of Integer; end;
    procedure Grow(var C: TCtx; N: Integer);
    begin SetLength(C.Arr, N); C.Arr[0] := 42 end;
    var Ctx: TCtx;
    begin
      Grow(Ctx, 3);
      WriteLn(Length(Ctx.Arr));
      WriteLn(Ctx.Arr[0])
    end.
    ''', '3' + LE + '42' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_VarParamRecordArrayFieldElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { SetInt(var C) does C.Ints[I] := V; SetRec(var C) does C.Recs[I] := R with a
    MANAGED-record element (string field).  Both writes must reach the CALLER's
    arrays through the derefed var-param address, and the managed-record store
    must retain/release correctly.  After the calls the caller sees the values. }
  AssertRunsOnAll('''
    program Prg;
    type
      TRec = record S: string; N: Integer; end;
      TCtx = record Ints: array of Integer; Recs: array of TRec; end;
    procedure SetInt(var C: TCtx; I, V: Integer);
    begin C.Ints[I] := V end;
    procedure SetRec(var C: TCtx; I: Integer; const R: TRec);
    begin C.Recs[I] := R end;
    var Ctx: TCtx; R: TRec;
    begin
      SetLength(Ctx.Ints, 3);
      SetLength(Ctx.Recs, 2);
      SetInt(Ctx, 1, 42);
      SetInt(Ctx, 2, 99);
      R.S := 'hello'; R.N := 7;
      SetRec(Ctx, 0, R);
      WriteLn(Ctx.Ints[1]);
      WriteLn(Ctx.Ints[2]);
      WriteLn(Ctx.Recs[0].S);
      WriteLn(Ctx.Recs[0].N)
    end.
    ''', '42' + LE + '99' + LE + 'hello' + LE + '7' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_ByValueDynArrayParam;
const
  Src = '''
    program P;
    type TA = array of Integer;
    function SumV(A: TA): Integer;
    var i: Integer;
    begin Result := 0; for i := 0 to Length(A) - 1 do Result := Result + A[i] end;
    var d: TA;
    begin
      SetLength(d, 3); d[0] := 1; d[1] := 2; d[2] := 3;
      WriteLn(SumV(d));
      WriteLn(Length(d))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  { SumV owns its copy (retain/release); the caller's d survives intact. }
  AssertRunsOnAll(Src, '6' + LE + '3' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLengthOnArrayFieldElem;
const
  Src = '''
    program P;
    type
      THold = class
      public
        FNest: array[0..1] of array of Integer;
        FStrs: array[0..1] of string;
        FObjs: array[0..1] of TObject;
        FDD: array of array of Integer;
      end;
    var H: THold;
    begin
      H := THold.Create();
      SetLength(H.FNest[0], 2);
      SetLength(H.FNest[1], 3);
      H.FNest[0][0] := 10; H.FNest[0][1] := 11;
      H.FNest[1][0] := 20; H.FNest[1][2] := 22;
      SetLength(H.FStrs[0], 3);
      SetLength(H.FStrs[1], 5);
      WriteLn(Length(H.FNest[0]), ' ', Length(H.FNest[1]));
      WriteLn(H.FNest[0][1], ' ', H.FNest[1][2]);
      WriteLn(Length(H.FStrs[0]), ' ', Length(H.FStrs[1]));
      SetLength(H.FDD, 2);
      SetLength(H.FDD[1], 4);
      H.FDD[1][3] := 33;
      WriteLn(Length(H.FDD[0]), ' ', Length(H.FDD[1]), ' ', H.FDD[1][3]);
      H.FObjs[1] := TObject.Create();
      H.FObjs[1].Free();
      WriteLn(H.FObjs[1] = nil)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  { SetLength must resize the element the [I] subscript selects, not the field
    base — dropping the subscript segfaulted the native backend.  Also covers
    the two sibling shapes the same slot-address tail serves: a DYN-array
    outer field (FDD — the helper's deref-then-index branch, vs FNest's
    static-array branch) and Free() on a field-array element (the third
    EmitLValueSlotAddr caller — must release AND nil the ELEMENT slot, not
    the field base). }
  AssertRunsOnAll(Src, '2 3' + LE + '11 22' + LE + '3 5' + LE +
    '0 4 33' + LE + 'True' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_IncDec_PlainArrayElem;
const
  Src = '''
    program P;
    var
      A: array[0..3] of Integer;
      D: array of Integer;
    begin
      A[0] := 5; A[1] := 40;
      Inc(A[1], 2);
      SetLength(D, 3);
      D[0] := 8; D[1] := 100;
      Inc(D[1]);
      Dec(D[1], 3);
      WriteLn(A[0], ' ', A[1], ' ', D[0], ' ', D[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  { A[0]/D[0] must stay untouched; only the [1] elements change. }
  AssertRunsOnAll(Src, '5 42 8 98' + LE, 0);
end;

initialization
  RegisterTest(TE2EDynArrayTests);

end.
