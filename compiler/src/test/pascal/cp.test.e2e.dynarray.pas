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
    { overloads distinguished only by an array or metaclass parameter type --
      distinct dynamic arrays, distinct static arrays, distinct metaclasses --
      each get their own label and each call reaches its own body }
    procedure TestRun_Overloads_OnArrayAndMetaclassTypes;
    { DA := [..] builds a fresh dynamic array: every target and element kind }
    procedure TestRun_DynArrayLiteral_EveryTargetAndElementKind;
    procedure TestRun_DynArray_AggregateElements_ReleasedWithArray;
    procedure TestRun_DynArray_ManagedElements_ReleasedWithArray;
    procedure TestRun_DynArray_BoundsElementsAddressesRecords;
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
    { Inc/Dec on a Byte/Word/SmallInt array element — both backends did a
      32-bit read-modify-write, so the carry out of a 255-valued Byte
      incremented the NEXT element and the store over-wrote up to 3 bytes past
      the element (BUG-20260723-incdec-narrow-elem-rmw).  Load/store must use
      the element's natural width. }
    procedure TestRun_IncDec_NarrowArrayElem;
    { Inc/Dec on a narrow (Byte/Word/SmallInt) GLOBAL — globals are emitted
      packed, so the native direct-ident path's 32-bit RMW carried into the
      neighbouring global (BUG-20260723-incdec-narrow-global-rmw). }
    procedure TestRun_IncDec_NarrowGlobal;
    procedure TestRun_IncDec_NarrowVarParam_StoresDeclaredWidth;
    procedure TestRun_Assign_NarrowTarget_Wraps;
    procedure TestRun_VarAndCapturedDynArray_ResizeAndWrite;
    { Inc/Dec on a PROMOTED narrow LOCAL — QBE kept the local as a bare w SSA
      temp and never masked, so Inc of a Byte 255 read back 256 instead of 0
      (BUG-20260723-incdec-promoted-narrow-local). }
    procedure TestRun_IncDec_PromotedNarrowLocal;
    { an owned dyn-array result consumed by a by-value, const or open-array
      argument, by Length / High, or discarded, drops its +1: the array's
      refcount is back to 1 afterwards (each leaked one reference -- the
      whole array -- per evaluation; BUG-20261011-owned-dynarray-arg-leak).
      The --debug tracker cannot see these: a fresh array is tracked only on
      its 0 -> 1 retain. }
    procedure TestRun_OwnedDynArrayTransients_Released;
    { A := nil releases the array (and its managed elements) and leaves it
      empty, through every storage form; nil is also an argument, a result
      and a comparison operand }
    procedure TestRun_DynArray_NilAssign_EveryForm;
    { GH #260: Copy, +, Concat, Delete and Insert on dynamic arrays, and
      Concat on strings.  The program and its expected output come from FPC
      3.2.2 (with ArrayOperators): every clamping rule for a negative or
      out-of-range index and count, literals as operands, copy-on-write for
      a shared array, and string elements.  Leak-checked. }
    procedure TestRun_DynArrayOps_MatchFPC;
    { the results hold exactly one reference and the sources keep theirs;
      owned operands (call results, literals) are released; managed
      elements are retained by every copy and released with the last one }
    procedure TestRun_DynArrayOps_RefCountsAndManagedElements;
    { Delete and Insert reach every assignable target: a var parameter, a
      record field, an implicit-Self field, an element of an array of arrays,
      a global and a captured local }
    procedure TestRun_DynArrayOps_EveryTarget;
    { Concat and Insert are builtins only when nothing of that name is in
      scope: a program's own Concat / Insert, and an implicit-Self Insert
      method, keep winning (FPC-compatibility units declare their own) }
    procedure TestRun_UserConcatAndInsert_Win;
    { SetLength on a uniquely owned array grows it in place with geometric
      headroom, so an append loop is amortised O(n): the data pointer moves
      only a handful of times, not on every append (it used to move -- a
      fresh mapping, zeroed and copied -- on every call, which made an
      append loop quadratic; Schmitty2005/morse PR 2) }
    procedure TestRun_SetLength_AppendLoop_GrowsInPlace;
    { growing a SHARED array still copies: the other holder keeps its old
      contents and length, the grown copy has the old elements and a zeroed
      tail }
    procedure TestRun_SetLength_SharedGrow_CopiesOnWrite;
    { a shrink followed by a grow in place exposes zeroed elements, never the
      stale values the shrink cut off -- unmanaged and managed elements }
    procedure TestRun_SetLength_ShrinkThenGrow_TailIsZeroed;
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
    var a: array of Int; i, sum: Int;
    begin SetLength(a, 5); for i := 0 to 4 do a[i] := i * 2;
      sum := 0; for i := 0 to High(a) do sum := sum + a[i]; WriteLn(sum) end.
    ''';

  SrcLenHigh = '''
    program Prg;
    var a: array of Int;
    begin SetLength(a, 7); WriteLn(Length(a), ' ', High(a)) end.
    ''';

  SrcGrow = '''
    program Prg;
    var a: array of Int; i: Int;
    begin SetLength(a, 3); for i := 0 to 2 do a[i] := i + 1;
      SetLength(a, 6); WriteLn(a[0], a[1], a[2], ' ', Length(a)) end.
    ''';

  SrcOfString = '''
    program Prg;
    var a: array of string; i: Int;
    begin SetLength(a, 3); a[0] := 'x'; a[1] := 'y'; a[2] := 'z';
      for i := 0 to 2 do Write(a[i]); WriteLn() end.
    ''';

  SrcRefSem = '''
    program Prg;
    var a, b: array of Int;
    begin SetLength(a, 3); a[0] := 7; b := a; b[0] := 99; WriteLn(a[0]) end.
    ''';

  SrcReturn = '''
    program Prg;
    type TIntArr = array of Int;
    function MakeArr(n: Int): TIntArr; var i: Int; begin SetLength(Result, n); for i := 0 to n-1 do Result[i] := i end;
    var a: TIntArr;
    begin a := MakeArr(5); WriteLn(Length(a), ' ', a[4]) end.
    ''';

  SrcRagged = '''
    program Prg;
    var m: array of array of Int;
    begin SetLength(m, 3); SetLength(m[0], 1); SetLength(m[1], 2); SetLength(m[2], 3);
      WriteLn(Length(m[0]), Length(m[1]), Length(m[2])) end.
    ''';

  SrcFillViaRow = '''
    program Prg;
    var m: array of array of Int; row: array of Int; i, sum: Int;
    begin SetLength(m, 2); SetLength(m[0], 3);
      row := m[0]; for i := 0 to 2 do row[i] := i + 1;
      sum := 0; for i := 0 to 2 do sum := sum + m[0][i];
      WriteLn(sum) end.
    ''';

  SrcChainedInt2D = '''
    program Prg;
    var m: array of array of Int; i, j: Int;
    begin
      SetLength(m, 2); SetLength(m[0], 2); SetLength(m[1], 2);
      m[0][0] := 1; m[0][1] := 2; m[1][0] := 3; m[1][1] := 4;
      for i := 0 to 1 do for j := 0 to 1 do Write(m[i][j]);
      WriteLn()
    end.
    ''';

  SrcChainedString2D = '''
    program Prg;
    var m: array of array of string; i, j: Int;
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
    var c: array of array of array of Int; i, j, k: Int;
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
    var I: Int;
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
    var I: Int;
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
    var G, H: array of Int; I: Int;
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
    var A, B: array of Int; I: Int;
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
    var A: array of Int; I: Int;
    function Pick: Int;
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
        Offset: Int;
        Pad: Int64;
      end;
      THolder = class
      public
        Bytes: array of Byte;
      end;
    var
      H: THolder;
      R: TRec;
      K: Int;
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
    type TCtx = record Arr: array of Int; end;
    procedure Grow(var C: TCtx; N: Int);
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
      TRec = record S: string; N: Int; end;
      TCtx = record Ints: array of Int; Recs: array of TRec; end;
    procedure SetInt(var C: TCtx; I, V: Int);
    begin C.Ints[I] := V end;
    procedure SetRec(var C: TCtx; I: Int; const R: TRec);
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
    type TA = array of Int;
    function SumV(A: TA): Int;
    var i: Int;
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
        FNest: array[0..1] of array of Int;
        FStrs: array[0..1] of string;
        FObjs: array[0..1] of TObject;
        FDD: array of array of Int;
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
      A: array[0..3] of Int;
      D: array of Int;
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

procedure TE2EDynArrayTests.TestRun_IncDec_NarrowArrayElem;
const
  Src = '''
    program Prg;
    var
      B: array[0..3] of Byte;
      W: array[0..3] of UInt16;
      SI: array[0..3] of Int16;
    begin
      B[0] := 10; B[1] := 255; B[2] := 20; B[3] := 30;
      Inc(B[1]);                { wraps to 0; B[2] must stay 20 }
      W[0] := 100; W[1] := 65535; W[2] := 200; W[3] := 300;
      Inc(W[1], 2);             { wraps to 1; W[2] must stay 200 }
      SI[0] := 100; SI[1] := -5; SI[2] := 40; SI[3] := 50;
      Inc(SI[1], 3);            { -2; neighbours untouched }
      Dec(SI[2], 50);           { -10; signed }
      WriteLn(B[0], ' ', B[1], ' ', B[2], ' ', B[3]);
      WriteLn(W[0], ' ', W[1], ' ', W[2], ' ', W[3]);
      WriteLn(SI[0], ' ', SI[1], ' ', SI[2], ' ', SI[3])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src, '10 0 20 30' + LE + '100 1 200 300' + LE +
    '100 -2 -10 50' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_IncDec_NarrowGlobal;
const
  Src = '''
    program Prg;
    var
      GA: Byte; GB: Byte; GC: Byte;
      WA: UInt16; WB: UInt16; WC: UInt16;
      GS: Int16;
    begin
      GA := 1; GB := 255; GC := 2;
      Inc(GB);              { wraps to 0; GC must stay 2, not carry to 3 }
      WA := 10; WB := 65535; WC := 20;
      Inc(WB, 2);           { wraps to 1; WC must stay 20 }
      GS := -5; Inc(GS, 3); { -2 (signed) }
      WriteLn(GA, ' ', GB, ' ', GC);
      WriteLn(WA, ' ', WB, ' ', WC);
      WriteLn(GS)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src, '1 0 2' + LE + '10 1 20' + LE + '-2' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_IncDec_NarrowVarParam_StoresDeclaredWidth;
const
  { Inc/Dec through a var parameter must load and store at the target's
    declared width.  arm64 used a 64-bit ldr/str there, so Dec on a Byte
    record field wrote 8 bytes and wiped its neighbours, and the value never
    wrapped (0 - 1 left 64-bit -1). }
  Src = '''
    program Prg;
    type
      TRec = record
        A: Byte; B: Byte; C: UInt16; D: Int16; E: Int32; F: Int32;
      end;
    procedure DecB(var X: Byte); begin Dec(X) end;
    procedure IncW(var X: UInt16); begin Inc(X, 3) end;
    procedure DecS(var X: Int16); begin Dec(X, 2) end;
    procedure IncI(var X: Int32); begin Inc(X) end;
    var R: TRec;
    begin
      R.A := 0; R.B := 7; R.C := 65534; R.D := -32767; R.E := 2147483647;
      R.F := 99;
      DecB(R.A); IncW(R.C); DecS(R.D); IncI(R.E);
      WriteLn(R.A, ' ', R.B, ' ', R.C, ' ', R.D, ' ', R.E, ' ', R.F)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src, '255 7 1 32767 -2147483648 99' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_Assign_NarrowTarget_Wraps;
const
  { A plain assignment must wrap the value to the TARGET's width and
    signedness.  arm64 stored the full 64-bit result into the 8-byte slot,
    so `G := G + 10` on a Byte holding 250 read back 260, silently. }
  Src = '''
    program Prg;
    var G: Byte; I: Int32; Wd: UInt16; S: Int16; C: UInt32;
    begin
      G := 250; G := G + 10;
      I := 2147483647; I := I + 1;
      Wd := 65535; Wd := Wd + 2;
      S := 32767; S := S + 1;
      C := 0; C := C - 1;
      WriteLn(G, ' ', I, ' ', Wd, ' ', S, ' ', C)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src, '4 -2147483648 1 -32768 4294967295' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_VarAndCapturedDynArray_ResizeAndWrite;
const
  { A dyn array reached through a var parameter or a closure capture: the
    slot holds the variable's ADDRESS (the captured local's own slot is
    dead), so SetLength, element reads and element / element-field writes
    must all go through it.  arm64 rejected the var forms, and SetLength on a
    captured array resized the dead slot.  This is the shape of the fiber
    reactors' Wait(..., var AReady: TReadyList). }
  Src = '''
    program vd;
    type
      TEntry = record Token: Int64; Events: Int; end;
      TList = array of TEntry;
      TInts = array of Int;
    procedure Fill(var A: TList; N: Int);
    var I: Int;
    begin
      if Length(A) < N then SetLength(A, N);
      for I := 0 to N - 1 do
      begin
        A[I].Token := I * 10;
        A[I].Events := I + 1;
      end;
    end;
    procedure Grow(var B: TInts);
    begin
      SetLength(B, Length(B) + 1);
      B[High(B)] := 99;
    end;
    type TProc0 = reference to procedure;
    var L: TList; X: TInts; P: TProc0; C: TInts;
    begin
      Fill(L, 3); WriteLn(Length(L), ' ', L[2].Token, ' ', L[2].Events);
      Grow(X); Grow(X); WriteLn(Length(X), ' ', X[1]);
      P := procedure begin SetLength(C, 4); C[3] := 5; end;
      P(); WriteLn(Length(C), ' ', C[3]);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertRunsOnAll(Src, '3 20 3' + LE + '2 99' + LE + '4 5' + LE, 0);
  AssertLeakFreeOnAll(Src, '4 5');
end;

procedure TE2EDynArrayTests.TestRun_IncDec_PromotedNarrowLocal;
const
  Src = '''
    program Prg;
    procedure P;
    var
      LB: Byte;
      LW: UInt16;
      LS: Int16;
      LI: Int32;
      L6: Int64;
    begin
      LB := 255; Inc(LB);        { wraps to 0 }
      WriteLn(LB);
      LB := 200; Inc(LB, 100);   { 300 mod 256 = 44 }
      WriteLn(LB);
      LB := 0; Dec(LB);          { underflows to 255 }
      WriteLn(LB);
      LW := 65535; Inc(LW);      { wraps to 0 }
      WriteLn(LW);
      LS := 32767; Inc(LS);      { overflow to -32768 }
      WriteLn(LS);
      LS := -32768; Dec(LS);     { underflow to 32767 }
      WriteLn(LS);
      LI := 2147483647; Inc(LI); { regression: Integer must NOT be narrowed }
      WriteLn(LI);
      L6 := 4294967295; Inc(L6); { regression: Int64 takes the wide arm }
      WriteLn(L6)
    end;
    begin
      P()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  { The locals are promotable (no address taken, no try), so QBE keeps them in
    SSA temps — the Inc result must still be truncated to the type's range.
    The Integer/Int64 cases guard the other direction: TruncateNarrowW must
    leave non-narrow types untouched. }
  AssertRunsOnAll(Src, '0' + LE + '44' + LE + '255' + LE + '0' + LE +
    '-32768' + LE + '32767' + LE + '-2147483648' + LE + '4294967296' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_DynArray_BoundsElementsAddressesRecords;
const
  {
    Dynamic arrays end to end: a fresh variable is empty, SetLength / Length /
    High / Low, element read and write (scaled offsets), @A[I] and
    @Holder.Items[I] addressing the element in place, a record element copied
    field by field (the copy is independent and its string retained, not the
    source's address stored), a string field written through A[I].Name, and an
    element of a dyn-array field of a record and of a class. }
  Src = '''
    program DynArrays;
    type
      TRec = record
        Name: string;
        Number: Int;
      end;
      PRec = ^TRec;
      PInt = ^Int;
      THolder = record
        Items: array of TRec;
      end;
      TIA = array of Int;
      TR = record
        A: TIA;
      end;
      TC = class
        A: TIA;
      end;
    procedure Run;
    var
      A: array of Int;
      RA: array of TRec;
      R: TRec;
      H: THolder;
      P: PRec;
      PI: PInt;
      Rec: TR;
      C: TC;
      I: Int;
    begin
      WriteLn(Length(A));
      SetLength(A, 4);
      for I := 0 to High(A) do
        A[I] := I * 10;
      WriteLn(Length(A), ' ', Low(A), ' ', High(A), ' ', A[3]);
      PI := @A[2];
      PI^ := 99;
      WriteLn(A[2]);
      SetLength(RA, 2);
      R.Name := 'first';
      R.Number := 1;
      RA[0] := R;
      R.Name := 'changed';
      WriteLn(RA[0].Name, ' ', RA[0].Number);
      RA[1].Name := 'second';
      WriteLn(RA[1].Name);
      H.Items := RA;
      P := @H.Items[1];
      P^.Number := 22;
      WriteLn(RA[1].Number);
      SetLength(Rec.A, 3);
      Rec.A[1] := 10;
      WriteLn(Rec.A[1]);
      C := TC.Create();
      SetLength(C.A, 2);
      C.A[1] := 20;
      WriteLn(C.A[1] + Rec.A[1])
    end;
    begin
      Run()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0' + LE +
    '4 0 3 30' + LE +
    '99' + LE +
    'first 1' + LE +
    'second' + LE +
    '22' + LE +
    '10' + LE +
    '30' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_DynArray_ManagedElements_ReleasedWithArray;
const
  {
    A dynamic array owns its managed elements (BUG-20261007-dynarray-managed-
    elems-never-released): strings, objects, interfaces and nested dynamic
    arrays are released when the array's last reference goes -- at SetLength(A,
    0), at scope exit and for a global at program exit -- and a shrink releases
    the dropped tail at once.  SetLength on a SHARED array is copy-on-write
    (BUG-20261004-setlength-frees-shared-dynarray): B keeps its two elements
    after SetLength(A, 1), where it used to read freed memory.  Leak-checked. }
  Src = '''
    program DynScalar;
    type
      TBox = class
        V: Int;
        constructor Create(AV: Int);
        destructor Destroy; override;
      end;
      IVal = interface
        function Get: Int;
      end;
      TVal = class(TObject, IVal)
        N: Int;
        function Get: Int;
        destructor Destroy; override;
      end;
      TStrs = array of string;
    constructor TBox.Create(AV: Int); begin V := AV end;
    destructor TBox.Destroy;
    begin
      WriteLn('box ', V, ' gone');
      inherited Destroy()
    end;
    function TVal.Get: Int; begin Result := N end;
    destructor TVal.Destroy;
    begin
      WriteLn('val ', N, ' gone');
      inherited Destroy()
    end;
    function MakeVal(AN: Int): IVal;
    var V: TVal;
    begin
      V := TVal.Create();
      V.N := AN;
      Result := V
    end;
    var GS: TStrs;
    procedure Locals;
    var
      S: TStrs; B: array of TBox; I: array of IVal; N: array of TStrs;
    begin
      SetLength(S, 2);
      S[0] := 'a' + 'b'; S[1] := 'c' + 'd';
      SetLength(B, 3);
      B[0] := TBox.Create(1); B[1] := TBox.Create(2); B[2] := TBox.Create(3);
      WriteLn('shrink');
      SetLength(B, 1);
      WriteLn('shrunk ', Length(B), ' ', B[0].V);
      SetLength(I, 1);
      I[0] := MakeVal(7);
      SetLength(N, 2);
      SetLength(N[1], 1);
      N[1][0] := 'n' + 'ested';
      WriteLn(S[1], ' ', I[0].Get(), ' ', N[1][0]);
      SetLength(B, 0);
      SetLength(I, 0);
      WriteLn('end locals')
    end;
    procedure Shared;
    var A, B: array of TBox;
    begin
      SetLength(A, 2);
      A[0] := TBox.Create(10); A[1] := TBox.Create(11);
      B := A;
      SetLength(A, 1);
      WriteLn('shared ', Length(A), ' ', Length(B), ' ', B[1].V);
      SetLength(B, 0);
      WriteLn('b cleared');
      SetLength(A, 0);
      WriteLn('a cleared')
    end;
    begin
      Locals();
      Shared();
      SetLength(GS, 1);
      GS[0] := 'glo' + 'bal';
      WriteLn(GS[0]);
      WriteLn('done')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'shrink' + LE +
    'box 2 gone' + LE +
    'box 3 gone' + LE +
    'shrunk 1 1' + LE +
    'cd 7 nested' + LE +
    'box 1 gone' + LE +
    'val 7 gone' + LE +
    'end locals' + LE +
    'shared 1 2 11' + LE +
    'box 11 gone' + LE +
    'b cleared' + LE +
    'box 10 gone' + LE +
    'a cleared' + LE +
    'global' + LE +
    'done' + LE, 0);
  AssertLeakFreeOnAll(Src, 'a cleared');
end;

procedure TE2EDynArrayTests.TestRun_DynArray_AggregateElements_ReleasedWithArray;
const
  {
    Records and static arrays with managed fields as dynamic-array elements
    are released through a per-type element hook the native backends emit:
    shrinking releases the dropped records' fields, a copy-on-write keeps the
    shared original intact, and the last reference releases everything.
    Leak-checked on the native backend (QBE emits no per-type hook). }
  Src = '''
    program DynAggregate;
    type
      TBox = class
        V: Int;
        constructor Create(AV: Int);
        destructor Destroy; override;
      end;
      TInner = record
        Names: array[0..1] of string;
      end;
      TRec = record
        S: string;
        B: TBox;
        Inner: TInner;
      end;
      TPair = array[0..1] of string;
    constructor TBox.Create(AV: Int); begin V := AV end;
    destructor TBox.Destroy;
    begin
      WriteLn('box ', V, ' gone');
      inherited Destroy()
    end;
    procedure Run;
    var R, Copy2: array of TRec; P: array of TPair; I: Int;
    begin
      SetLength(R, 3);
      for I := 0 to 2 do
      begin
        R[I].S := 'rec' + IntToStr(I);
        R[I].B := TBox.Create(I);
        R[I].Inner.Names[1] := 'in' + IntToStr(I)
      end;
      WriteLn('shrink');
      SetLength(R, 2);
      Copy2 := R;
      SetLength(R, 1);
      WriteLn(R[0].S, ' ', Copy2[1].S, ' ', Copy2[1].B.V, ' ', Copy2[1].Inner.Names[1]);
      SetLength(Copy2, 0);
      WriteLn('copy cleared');
      SetLength(P, 2);
      P[0][0] := 'p' + 'q';
      P[1][1] := 'r' + 's';
      WriteLn(P[0][0], ' ', P[1][1]);
      SetLength(R, 0);
      WriteLn('end run')
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''';
var
  RunOut: string;
  Code: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'shrink' + LE +
    'box 2 gone' + LE +
    'rec0 rec1 1 in1' + LE +
    'box 1 gone' + LE +
    'copy cleared' + LE +
    'pq rs' + LE +
    'box 0 gone' + LE +
    'end run' + LE +
    'done' + LE, 0);
  AssertTrue('native compile+run (--debug)',
    CompileAndRunWithRTLDebugOn(beNative, Src, RunOut, Code, True));
  AssertEquals('native exit 0 (output: ' + RunOut + ')', 0, Code);
  AssertTrue('native no leak report, got: ' + RunOut, Pos('leak', RunOut) < 0);
end;

procedure TE2EDynArrayTests.TestRun_OwnedDynArrayTransients_Released;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TIntArr = array of Int32;
      PInt32 = ^Int32;
    var
      G: TIntArr;
    function GetG: TIntArr;
    begin
      Result := G;
    end;
    function RC: Int32;
    begin
      Result := PInt32(Pointer(@G[0]) - 12)^;   { the header's RefCount }
    end;
    procedure UseArr(A: TIntArr); begin end;
    procedure UseConst(const A: TIntArr); begin end;
    procedure UseOpen(const A: array of Int32); begin end;
    var
      N: Int32;
    begin
      SetLength(G, 3);
      WriteLn(RC());
      UseArr(GetG());
      UseConst(GetG());
      UseOpen(GetG());
      GetG();
      N := Length(GetG()) + High(GetG());
      WriteLn(N, ' ', RC());
    end.
    ''', '1' + LE + '5 1' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_DynArrayLiteral_EveryTargetAndElementKind;
const
  SrcTargets = '''
    program P;
    type
      TIA = array of Int;
      TDA = array of Float64;
      TObj = class
        N: Int;
        constructor Create(AN: Int);
      end;
      TRec = record
        A: Int;
        S: string;
      end;
      THolder = class
        Items: TIA;
      end;
    constructor TObj.Create(AN: Int);
    begin
      N := AN;
    end;
    function MkS(I: Int): string;
    begin
      Result := 'm' + IntToStr(I);
    end;
    function SumD(D: TIA): Int;
    var I: Int;
    begin
      Result := 0;
      for I := 0 to High(D) do Result := Result + D[I];
    end;
    function Make: TIA;
    begin
      Result := [7, 8, 9];
    end;
    var
      C: array of Int;
      E: TIA;
      D: TDA;
      S: array of string;
      X: string;
      M: array of TIA;
      B: array of Byte;
      H: THolder;
      Os: array of TObj;
      R: TRec;
      Rs: array of TRec;
    begin
      C := [1, 2];
      WriteLn(Length(C), ' ', C[0], ' ', C[1]);
      C := [];
      WriteLn(Length(C));
      D := [1.5, 2];
      WriteLn(Trunc(D[0] * 10), ' ', Trunc(D[1] * 10));
      X := 'x';
      S := ['a', X, MkS(3)];
      WriteLn(S[0], S[1], S[2]);
      M := [[1, 2], [3]];
      WriteLn(Length(M), Length(M[0]), Length(M[1]), M[1][0]);
      B := [1, 255];
      WriteLn(B[0] + B[1]);
      H := THolder.Create();
      H.Items := [4, 5];
      WriteLn(H.Items[1]);
      Os := [TObj.Create(1), TObj.Create(2)];
      WriteLn(Os[1].N);
      R.A := 1;
      R.S := 'r' + X;
      Rs := [R, R];
      WriteLn(Rs[1].S, Rs[0].A);
      WriteLn(SumD([1, 2, 3]));
      E := Make();
      WriteLn(E[2]);
    end.
    ''';
  SrcElements = '''
    program P;
    type
      IThing = interface
        function Id: Int;
      end;
      TThing = class(TObject, IThing)
        FId: Int;
        constructor Create(AId: Int);
        function Id: Int;
      end;
      TIA = array of Int;
      TRec = record
        A: Int;
        S: string;
      end;
      TProc = procedure of object;
      TRunner = class
        N: Int;
        procedure Run;
      end;
    constructor TThing.Create(AId: Int);
    begin
      FId := AId;
    end;
    function TThing.Id: Int;
    begin
      Result := FId;
    end;
    procedure TRunner.Run;
    begin
      WriteLn('run ', N);
    end;
    function MkRec(I: Int): TRec;
    begin
      Result.A := I;
      Result.S := 's' + IntToStr(I);
    end;
    function Make(N: Int): TIA;
    begin
      Result := [N, N + 1];
    end;
    var
      Ints: array of IThing;
      T: IThing;
      Rs: array of TRec;
      M: array of TIA;
      Fs: array of Float32;
      Ps: array of TProc;
      R: TRunner;
      S: array of string;
      I: Int;
    begin
      T := TThing.Create(5);
      Ints := [T, TThing.Create(6)];
      WriteLn(Ints[0].Id(), Ints[1].Id());
      Rs := [MkRec(1), MkRec(2)];
      WriteLn(Rs[1].S, Rs[0].A);
      M := [Make(1), Make(10), []];
      WriteLn(M[1][1], ' ', Length(M[2]));
      Fs := [0.5, 2];
      WriteLn(Trunc(Fs[0] * 10 + Fs[1]));
      R := TRunner.Create();
      R.N := 3;
      Ps := [@R.Run];
      Ps[0]();
      for I := 1 to 3 do
        S := ['a' + IntToStr(I), 'b'];
      WriteLn(S[0], S[1]);
      S := [S[1], S[0]];
      WriteLn(S[0], S[1]);
    end.
    ''';
var
  RunOut: string;
  Code: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { targets: var, empty, Result, field, argument; elements: Integer, Double
    from an integer, borrowed / owned strings, nested literals, Byte,
    objects, records (BUG-20261014-dynarray-literal-assignment) }
  AssertRunsOnAll(SrcTargets,
    '2 1 2' + LE + '0' + LE + '15 20' + LE + 'axm3' + LE + '2213' + LE +
    '256' + LE + '5' + LE + '2' + LE + 'rx1' + LE + '6' + LE + '9' + LE, 0);
  { interfaces, record calls, owned nested arrays, Single, method pointers,
    reassignment over a live array -- and nothing leaks }
  AssertRunsOnAll(SrcElements,
    '56' + LE + 's21' + LE + '11 0' + LE + '7' + LE + 'run 3' + LE +
    'a3b' + LE + 'ba3' + LE, 0);
  AssertTrue('native compile+run (--debug)',
    CompileAndRunWithRTLDebugOn(beNative, SrcElements, RunOut, Code, True));
  AssertEquals('native exit 0 (output: ' + RunOut + ')', 0, Code);
  AssertTrue('native no leak report, got: ' + RunOut, Pos('leak', RunOut) < 0);
end;

procedure TE2EDynArrayTests.TestRun_Overloads_OnArrayAndMetaclassTypes;
const
  Src = '''
    program P;
    type
      TInts = array of Int;
      TStrs = array of string;
      TPair = array[0..1] of Int;
      TTrio = array[0..2] of Int;
      TA = class end;
      TB = class end;
      TAClass = class of TA;
      TBClass = class of TB;
    procedure F(const X: TInts); overload; begin WriteLn('ints ', Length(X)) end;
    procedure F(const X: TStrs); overload; begin WriteLn('strs ', Length(X)) end;
    procedure G(const X: TPair); overload; begin WriteLn('pair ', X[1]) end;
    procedure G(const X: TTrio); overload; begin WriteLn('trio ', X[2]) end;
    procedure H(X: TAClass); overload; begin WriteLn('a') end;
    procedure H(X: TBClass); overload; begin WriteLn('b') end;
    var I: TInts; S: TStrs; Pr: TPair; Tr: TTrio;
    begin
      SetLength(I, 2); SetLength(S, 3);
      Pr[1] := 7; Tr[2] := 9;
      F(I); F(S);
      G(Pr); G(Tr);
      H(TA); H(TB)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'ints 2' + #10 + 'strs 3' + #10 + 'pair 7' + #10 + 'trio 9' + #10 +
    'a' + #10 + 'b' + #10, 0);
end;

procedure TE2EDynArrayTests.TestRun_DynArray_NilAssign_EveryForm;
const
  Src =
    '''
    program P;
    type
      TIA = array of Int;
      TSA = array of string;
      THolder = class
        F: TSA;
      end;
      TRec = record
        R: TIA;
      end;
    var
      G: TIA;
      GS: TSA;
      H: THolder;
      Rc: TRec;
      Nested: array of TIA;

    function Count(A: TIA): Int;
    begin
      Result := Length(A)
    end;

    function MakeNil(N: Int): TIA;
    begin
      SetLength(Result, N);
      Result := nil
    end;

    procedure Clear(var A: TSA);
    begin
      A := nil
    end;

    procedure Local;
    var L: TSA;
    begin
      SetLength(L, 2);
      L[0] := 'x' + IntToStr(1);
      L := nil;
      WriteLn('local ', Length(L))
    end;

    begin
      SetLength(G, 3);
      G := nil;
      WriteLn(Length(G), ' ', G = nil, ' ', nil <> G);
      SetLength(GS, 2);
      GS[1] := 'abc' + IntToStr(2);
      Clear(GS);
      WriteLn(Length(GS));
      WriteLn(Count(nil), ' ', Length(MakeNil(4)));
      H := THolder.Create();
      SetLength(H.F, 5);
      H.F := nil;
      WriteLn(Length(H.F));
      SetLength(Rc.R, 2);
      Rc.R := nil;
      WriteLn(Length(Rc.R));
      SetLength(Nested, 2);
      SetLength(Nested[1], 3);
      Nested[1] := nil;
      WriteLn(Length(Nested[1]), ' ', Length(Nested));
      Local();
      SetLength(G, 1);
      WriteLn(G <> nil)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0 True False' + #10 + '0' + #10 + '0 0' + #10 + '0' + #10 + '0' + #10 +
    '0 2' + #10 + 'local 0' + #10 + 'True' + #10, 0);
  AssertLeakFreeOnAll(Src, 'local 0');
end;

procedure TE2EDynArrayTests.TestRun_DynArrayOps_MatchFPC;
const
  Src = '''
    program oracle;
    type TI = array of Int16; TS = array of string;
    procedure P(const Tag: string; const A: TI);
    var I: Int64;
    begin
      Write(Tag, ' [', Length(A), ']');
      for I := 0 to High(A) do Write(' ', A[I]);
      WriteLn();
    end;
    procedure PS(const Tag: string; const A: TS);
    var I: Int64;
    begin
      Write(Tag, ' [', Length(A), ']');
      for I := 0 to High(A) do Write(' ', A[I]);
      WriteLn();
    end;
    var A, B, C, E: TI; SA, SB: TS; s: string;
    begin
      A := [10, 11, 12, 13, 14];
      B := [20, 21];
      E := nil;
      P('copy-all', Copy(A));
      P('copy-from2', Copy(A, 2));
      P('copy-1-2', Copy(A, 1, 2));
      P('copy-neg-3', Copy(A, -2, 3));
      P('copy-3-99', Copy(A, 3, 99));
      P('copy-5-1', Copy(A, 5, 1));
      P('copy-9-1', Copy(A, 9, 1));
      P('copy-1-0', Copy(A, 1, 0));
      P('copy-1-neg', Copy(A, 1, -1));
      P('copy-nil', Copy(E, 0, 2));
      P('plus', A + B);
      P('plus-nil-l', E + B);
      P('plus-nil-r', A + E);
      P('plus-lit', A + [7]);
      P('lit-plus', [7, 8] + B);
      P('concat3', Concat(A, B, [99]));
      C := Copy(A); Delete(C, 1, 2); P('del-1-2', C);
      C := Copy(A); Delete(C, 3, 99); P('del-3-99', C);
      C := Copy(A); Delete(C, -1, 2); P('del-neg-2', C);
      C := Copy(A); Delete(C, 5, 1); P('del-5-1', C);
      C := Copy(A); Delete(C, 0, 0); P('del-0-0', C);
      C := Copy(A); Delete(C, 0, 5); P('del-all', C);
      C := Copy(A); Insert(B, C, 2); P('ins-arr-2', C);
      C := Copy(A); Insert(B, C, 0); P('ins-arr-0', C);
      C := Copy(A); Insert(B, C, 5); P('ins-arr-end', C);
      C := Copy(A); Insert(B, C, 99); P('ins-arr-99', C);
      C := Copy(A); Insert(B, C, -3); P('ins-arr-neg', C);
      C := Copy(A); Insert(Int16(42), C, 1); P('ins-elem-1', C);
      C := nil; Insert(Int16(42), C, 0); P('ins-elem-nil', C);
      C := Copy(A); Insert([1, 2], C, 1); P('ins-lit', C);
      C := A; Delete(C, 0, 1); P('cow-del-C', C); P('cow-del-A', A);
      C := A; Insert(Int16(1), C, 0); P('cow-ins-C', C); P('cow-ins-A', A);
      C := Copy(A); C[0] := 0; P('copy-indep-A', A);
      s := 'x';
      SA := ['a', 'b' + s, 'c'];
      SB := Copy(SA, 1, 2); PS('s-copy', SB);
      PS('s-plus', SA + SB);
      SB := SA; Delete(SB, 0, 1); PS('s-del', SB); PS('s-del-orig', SA);
      SB := SA; Insert('ins' + s, SB, 1); PS('s-ins', SB); PS('s-ins-orig', SA);
      WriteLn(Concat('ab', 'cd', s));
      WriteLn(Concat('solo'));
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'copy-all [5] 10 11 12 13 14' + LE +
    'copy-from2 [3] 12 13 14' + LE +
    'copy-1-2 [2] 11 12' + LE +
    'copy-neg-3 [1] 10' + LE +
    'copy-3-99 [2] 13 14' + LE +
    'copy-5-1 [0]' + LE +
    'copy-9-1 [0]' + LE +
    'copy-1-0 [0]' + LE +
    'copy-1-neg [0]' + LE +
    'copy-nil [0]' + LE +
    'plus [7] 10 11 12 13 14 20 21' + LE +
    'plus-nil-l [2] 20 21' + LE +
    'plus-nil-r [5] 10 11 12 13 14' + LE +
    'plus-lit [6] 10 11 12 13 14 7' + LE +
    'lit-plus [4] 7 8 20 21' + LE +
    'concat3 [8] 10 11 12 13 14 20 21 99' + LE +
    'del-1-2 [3] 10 13 14' + LE +
    'del-3-99 [3] 10 11 12' + LE +
    'del-neg-2 [5] 10 11 12 13 14' + LE +
    'del-5-1 [5] 10 11 12 13 14' + LE +
    'del-0-0 [5] 10 11 12 13 14' + LE +
    'del-all [0]' + LE +
    'ins-arr-2 [7] 10 11 20 21 12 13 14' + LE +
    'ins-arr-0 [7] 20 21 10 11 12 13 14' + LE +
    'ins-arr-end [7] 10 11 12 13 14 20 21' + LE +
    'ins-arr-99 [7] 10 11 12 13 14 20 21' + LE +
    'ins-arr-neg [7] 20 21 10 11 12 13 14' + LE +
    'ins-elem-1 [6] 10 42 11 12 13 14' + LE +
    'ins-elem-nil [1] 42' + LE +
    'ins-lit [7] 10 1 2 11 12 13 14' + LE +
    'cow-del-C [4] 11 12 13 14' + LE +
    'cow-del-A [5] 10 11 12 13 14' + LE +
    'cow-ins-C [6] 1 10 11 12 13 14' + LE +
    'cow-ins-A [5] 10 11 12 13 14' + LE +
    'copy-indep-A [5] 10 11 12 13 14' + LE +
    's-copy [2] bx c' + LE +
    's-plus [5] a bx c bx c' + LE +
    's-del [2] bx c' + LE +
    's-del-orig [3] a bx c' + LE +
    's-ins [4] a insx bx c' + LE +
    's-ins-orig [3] a bx c' + LE +
    'abcdx' + LE +
    'solo' + LE, 0);
  AssertLeakFreeOnAll(Src, 'solo');
end;

procedure TE2EDynArrayTests.TestRun_DynArrayOps_RefCountsAndManagedElements;
const
  Src = '''
    program Prg;
    type
      TIA = array of Int32;
      PInt32 = ^Int32;
      TBox = class
        V: Int;
        constructor Create(AV: Int);
        destructor Destroy; override;
      end;
      TBoxes = array of TBox;
    constructor TBox.Create(AV: Int); begin V := AV end;
    destructor TBox.Destroy;
    begin
      WriteLn('box ', V, ' gone');
      inherited Destroy()
    end;
    function RC(const A: TIA): Int32;
    begin
      Result := PInt32(Pointer(@A[0]) - 12)^;
    end;
    function Make(N: Int32): TIA;
    begin
      Result := [N, N + 1];
    end;
    procedure Ints;
    var A, B, C: TIA;
    begin
      A := [1, 2, 3];
      B := [4];
      C := A + B;
      WriteLn('plus ', RC(A), ' ', RC(B), ' ', RC(C));
      C := Copy(A, 1, 2);
      WriteLn('copy ', RC(A), ' ', RC(C));
      C := Make(5) + Make(7);
      WriteLn('owned plus ', Length(C), ' ', C[3], ' ', RC(C));
      C := Copy(Make(9), 1, 1);
      WriteLn('owned copy ', C[0], ' ', RC(C));
      C := Concat(Make(1), [0], Make(3));
      WriteLn('concat ', Length(C), ' ', RC(C));
      WriteLn('length ', Length(A + Make(1)), ' ', Copy(A, 2, 1)[0]);
      B := A;
      Delete(B, 0, 1);
      WriteLn('shared delete ', RC(A), ' ', RC(B), ' ', Length(A), ' ', Length(B));
      B := A;
      Insert(Make(8), B, 1);
      WriteLn('shared insert ', RC(A), ' ', RC(B), ' ', Length(B), ' ', B[1]);
      Insert(A, A, 1);
      WriteLn('self insert ', Length(A), ' ', A[1], ' ', A[3], ' ', RC(A));
    end;
    procedure Boxes;
    var A, B: TBoxes;
    begin
      A := [TBox.Create(1), TBox.Create(2), TBox.Create(3)];
      B := Copy(A, 1, 1) + [TBox.Create(4)];
      WriteLn('copied ', Length(B), ' ', B[0].V, ' ', B[1].V);
      Delete(A, 1, 2);
      WriteLn('deleted ', Length(A), ' ', A[0].V);
      Insert(TBox.Create(5), A, 0);
      WriteLn('inserted ', A[0].V, ' ', A[1].V);
      A := nil;
      WriteLn('a cleared');
      B := nil;
      WriteLn('b cleared');
    end;
    begin
      Ints();
      Boxes();
      WriteLn('done');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'plus 1 1 1' + LE +
    'copy 1 1' + LE +
    'owned plus 4 8 1' + LE +
    'owned copy 10 1' + LE +
    'concat 5 1' + LE +
    'length 5 3' + LE +
    'shared delete 1 1 3 2' + LE +
    'shared insert 1 1 5 8' + LE +
    'self insert 6 1 3 1' + LE +
    'copied 2 2 4' + LE +
    'box 3 gone' + LE +
    'deleted 1 1' + LE +
    'inserted 5 1' + LE +
    'box 5 gone' + LE +
    'box 1 gone' + LE +
    'a cleared' + LE +
    'box 2 gone' + LE +
    'box 4 gone' + LE +
    'b cleared' + LE +
    'done' + LE, 0);
  AssertLeakFreeOnAll(Src, 'done');
end;

procedure TE2EDynArrayTests.TestRun_DynArrayOps_EveryTarget;
const
  Src = '''
    program Prg;
    type
      TSA = array of string;
      TRec = record F: TSA; end;
      THolder = class
        Items: TSA;
        procedure Edit();
      end;
    var G: TSA;
    procedure Show(const Tag: string; const A: TSA);
    var I: Int;
    begin
      Write(Tag, ':');
      for I := 0 to High(A) do Write(' ', A[I]);
      WriteLn();
    end;
    procedure THolder.Edit();
    begin
      Insert('h' + 'x', Items, 0);
      Delete(Items, 1, 1);
    end;
    procedure ViaVar(var A: TSA);
    begin
      Insert(['v1', 'v2'], A, 1);
      Delete(A, 0, 1);
    end;
    procedure Captured;
    var L: TSA;
      procedure Inner;
      begin
        Insert('c' + 'x', L, 1);
        Delete(L, 0, 1);
      end;
    begin
      L := ['a', 'b'];
      Inner();
      Show('captured', L);
    end;
    var R: TRec; H: THolder; M: array of TSA; A: TSA;
    begin
      A := ['a', 'b', 'c'];
      ViaVar(A);
      Show('var', A);
      R.F := ['r1', 'r2'];
      Insert('r0', R.F, 0);
      Delete(R.F, 2, 1);
      Show('field', R.F);
      H := THolder.Create();
      H.Items := ['i1', 'i2'];
      H.Edit();
      Show('self', H.Items);
      H.Free();
      SetLength(M, 2);
      M[1] := ['m1'];
      Insert('m0', M[1], 0);
      Insert(M[1], M[0], 0);
      Delete(M[1], 1, 1);
      Show('elem0', M[0]);
      Show('elem1', M[1]);
      G := ['g1'];
      Insert(G + ['g2'], G, 1);
      Show('global', G);
      Captured();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'var: v1 v2 b c' + LE +
    'field: r0 r1' + LE +
    'self: hx i2' + LE +
    'elem0: m0 m1' + LE +
    'elem1: m0' + LE +
    'global: g1 g1 g2' + LE +
    'captured: cx b' + LE, 0);
  AssertLeakFreeOnAll(Src, 'captured');
end;

procedure TE2EDynArrayTests.TestRun_UserConcatAndInsert_Win;
const
  Src = '''
    program Prg;
    type
      TList2 = class
        N: Int;
        procedure Insert(AIdx, AVal, AExtra: Int);
        procedure Fill();
      end;
    procedure TList2.Insert(AIdx, AVal, AExtra: Int);
    begin
      N := AIdx + AVal + AExtra;
    end;
    procedure TList2.Fill();
    begin
      Insert(1, 2, 3);
    end;
    procedure Insert(A, B, C: Int);
    begin
      WriteLn('user insert ', A + B + C);
    end;
    function Concat(const A, B: string): string;
    begin
      Result := 'user ' + A + B;
    end;
    var L: TList2;
    begin
      Insert(1, 2, 4);
      WriteLn(Concat('x', 'y'));
      L := TList2.Create();
      L.Fill();
      WriteLn('method insert ', L.N);
      L.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'user insert 7' + LE +
    'user xy' + LE +
    'method insert 6' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLength_AppendLoop_GrowsInPlace;
const
  Src = '''
    program Prg;
    type
      TSamples = array of Int16;
    var
      A, Chunk: TSamples;
      I, J, OldLen, Moves: Int64;
      Last: Pointer;
      Sum: Int64;
    begin
      SetLength(Chunk, 1000);
      for I := 0 to High(Chunk) do
        Chunk[I] := Int16(I mod 7);
      Moves := 0;
      Last := nil;
      for J := 1 to 4000 do
      begin
        OldLen := Length(A);
        SetLength(A, OldLen + Length(Chunk));
        if Pointer(@A[0]) <> Last then
        begin
          Inc(Moves);
          Last := @A[0];
        end;
        for I := 0 to High(Chunk) do
          A[OldLen + I] := Chunk[I];
      end;
      Sum := 0;
      for I := 0 to High(A) do
        Sum := Sum + A[I];
      WriteLn(Length(A), ' ', Sum);
      WriteLn('few moves ', Moves < 100);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 4000 chunks of 0..6 repeating over 1000 elements: each chunk sums to
    2997 (142 full 0..6 cycles = 2982, plus 0..5 = 15) }
  AssertRunsOnAll(Src, '4000000 11988000' + LE + 'few moves True' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLength_SharedGrow_CopiesOnWrite;
const
  Src = '''
    program Prg;
    type
      TInts = array of Int32;
    var
      A, B: TInts;
      I: Int32;
    begin
      SetLength(A, 3000);
      for I := 0 to High(A) do
        A[I] := I + 1;
      B := A;
      SetLength(A, 6000);
      A[0] := -1;
      WriteLn(Length(B), ' ', B[0], ' ', B[2999]);
      WriteLn(Length(A), ' ', A[0], ' ', A[2999], ' ', A[3000], ' ', A[5999]);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '3000 1 3000' + LE +
    '6000 -1 3000 0 0' + LE, 0);
end;

procedure TE2EDynArrayTests.TestRun_SetLength_ShrinkThenGrow_TailIsZeroed;
const
  Src = '''
    program Prg;
    type
      TInts = array of Int32;
      TStrs = array of string;
    var
      A: TInts;
      S: TStrs;
      I: Int32;
    begin
      SetLength(A, 5000);
      for I := 0 to High(A) do
        A[I] := 7;
      SetLength(A, 10);
      SetLength(A, 5000);
      WriteLn(A[9], ' ', A[10], ' ', A[4999]);
      SetLength(A, 5);
      SetLength(A, 9);
      WriteLn(A[4], ' ', A[5], ' ', A[8]);
      SetLength(S, 600);
      for I := 0 to High(S) do
        S[I] := 'v' + IntToStr(I);
      SetLength(S, 2);
      SetLength(S, 600);
      WriteLn(S[1], ' [', S[2], '] [', S[599], ']');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '7 0 0' + LE +
    '7 0 0' + LE +
    'v1 [] []' + LE, 0);
end;

initialization
  RegisterTest(TE2EDynArrayTests);

end.
